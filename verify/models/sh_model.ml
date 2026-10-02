(* sh_model.ml
 *
 * Executable reference model of the Synrc POSIX shell, scoped to the full
 * grammar in BNF.txt (the ush src/ pipeline target), verified before manual
 * isomorphic C extraction. BTRON verify/models house style.
 *
 *   §1 tokens  §2 lexer  §3 AST/state/expansion  §4 parser  §5 interpreter
 *   §6 invariants  §7 verification suite
 *
 * Language coverage (POSIX 2.9):
 *   simple_command: assignments (prefix), argv, io_redirect (< > >> >| <& >&
 *   <> << <<- with IO_NUMBER), here-document bodies with delimiter quoting
 *   pipeline [!], and_or (&& ||, proper short-circuit), list (; NEWLINE &)
 *   compound: if/elif/else, while, until, for [in wordlist], case with
 *   glob patterns (star, question, [set]), brace groups (current env), subshells
 *   (isolated param/function space, shared file space), function definitions
 *   name() compound, redirects on compound commands
 *   expansion: $var ${var} $? $# $@ $* $N, single/double quotes, backslash
 *   escapes, field splitting on unquoted expansion, comments (#)
 *   exit status algebra: success = 0, statuses normalized mod 2^8 (POSIX
 *   2.8.2), exit as special builtin (terminates shell or its subshell)
 *
 * Deliberately outside the verified subset (documented, parser or executor
 * rejects): command substitution $(...) and backquotes, arithmetic,
 * pathname/glob file expansion, job control (& runs sequentially), shift,
 * sourced scripts, set -e/-u, aliases.
 *
 * Build & run:
 *   ocamlc -o sh_model sh_model.ml && ./sh_model
 *)

open Printf

(* ── §1 Tokens ──────────────────────────────────────────────────── *)

type kind =
  | K_WORD | K_ASSIGN | K_NL | K_I_NUM
  | K_ANDIF | K_ORIF | K_DSEMI
  | K_DLESS | K_DGREAT | K_LESSAND | K_GREATAND | K_LESSGREAT | K_DLESSDASH
  | K_CLOBBER | K_LESS | K_GREAT
  | K_IF | K_THEN | K_ELSE | K_ELIF | K_FI
  | K_DO | K_DONE | K_CASE | K_ESAC | K_WHILE
  | K_UNTIL | K_FOR | K_IN
  | K_LBRACE | K_RBRACE | K_BANG | K_LPAREN | K_RPAREN
  | K_SEMI | K_PIPE | K_AMP | K_EOF

type token = { k : kind; v : string; start : int }

exception Syntax of string
exception ExitShell of int
exception FuelExhausted

let kind_name k =
  match k with
  | K_WORD -> "WORD" | K_ASSIGN -> "ASSIGNMENT" | K_NL -> "NEWLINE"
  | K_I_NUM -> "IO_NUMBER" | K_ANDIF -> "&&" | K_ORIF -> "||" | K_DSEMI -> ";;"
  | K_DLESS -> "<<" | K_DGREAT -> ">>" | K_LESSAND -> "<&" | K_GREATAND -> ">&"
  | K_LESSGREAT -> "<>" | K_DLESSDASH -> "<<-" | K_CLOBBER -> ">|"
  | K_LESS -> "<" | K_GREAT -> ">"
  | K_IF -> "if" | K_THEN -> "then" | K_ELSE -> "else" | K_ELIF -> "elif"
  | K_FI -> "fi" | K_DO -> "do" | K_DONE -> "done" | K_CASE -> "case"
  | K_ESAC -> "esac" | K_WHILE -> "while" | K_UNTIL -> "until" | K_FOR -> "for"
  | K_IN -> "in" | K_LBRACE -> "{" | K_RBRACE -> "}" | K_BANG -> "!"
  | K_LPAREN -> "(" | K_RPAREN -> ")" | K_SEMI -> ";" | K_PIPE -> "|"
  | K_AMP -> "&" | K_EOF -> "EOF"

(* ── §2 Lexer ───────────────────────────────────────────────────── *)

let is_space c =
  c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = '\011' || c = '\012'
let is_blank c = c = ' ' || c = '\t' || c = '\r' || c = '\011' || c = '\012'
let is_digit c = c >= '0' && c <= '9'
let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
let is_alnum c = is_alpha c || is_digit c
let is_name_char c = is_alnum c || c = '_'
let is_op_delim c =
  c = ';' || c = '|' || c = '&' || c = '<' || c = '>'
  || c = '(' || c = ')' || c = '{' || c = '}'

let reserved =
  [ ("if", K_IF); ("then", K_THEN); ("else", K_ELSE); ("elif", K_ELIF)
  ; ("fi", K_FI); ("do", K_DO); ("done", K_DONE); ("case", K_CASE)
  ; ("esac", K_ESAC); ("while", K_WHILE); ("until", K_UNTIL)
  ; ("for", K_FOR); ("in", K_IN) ]

let two_char =
  [ ("&&", K_ANDIF); ("||", K_ORIF); (";;", K_DSEMI)
  ; ("<<-", K_DLESSDASH); ("<<", K_DLESS); (">>", K_DGREAT)
  ; ("<&", K_LESSAND); (">&", K_GREATAND); ("<>", K_LESSGREAT)
  ; (">|", K_CLOBBER) ]

let single =
  [ ('{', K_LBRACE); ('}', K_RBRACE); ('!', K_BANG)
  ; ('(', K_LPAREN); (')', K_RPAREN)
  ; ('<', K_LESS); ('>', K_GREAT)
  ; (';', K_SEMI); ('|', K_PIPE); ('&', K_AMP) ]

let starts_at s i p =
  let lp = String.length p in
  i + lp <= String.length s && String.sub s i lp = p

(* Word recognition, POSIX 2.3: a token is terminated by an unquoted blank,
   newline, or operator character. Quotes and backslash escapes suppress
   termination; a ${...} parameter reference keeps braces inside the word.
   The index of the first unquoted '=' is returned so the caller can classify
   the token as an assignment word (POSIX 2.9.1). *)
let scan_word src i n =
  let j = ref i in
  let eq = ref (-1) in
  let inq = ref false in (* inside '...' or "..." *)
  let inq_char = ref ' ' in
  let depth = ref 0 in (* inside ${...} *)
  let stop c =
    (not !inq) && !depth = 0 && (is_blank c || c = '\n' || is_op_delim c)
  in
  while !j < n && not (stop src.[!j]) do
    let c = src.[!j] in
    if c = '\\' && !j + 1 < n then j := !j + 2 (* escaped char cannot terminate *)
    else if !inq then begin
      if !depth = 0 && c = !inq_char then inq := false;
      incr j
    end
    else if c = '\'' || c = '"' then begin
      inq_char := c;
      inq := true;
      incr j
    end
    else begin
      if !depth > 0 then begin
        if c = '{' then incr depth
        else if c = '}' then decr depth
      end
      else if c = '=' && !eq = (-1) && !j > i then eq := !j;
      if c = '$' && !j + 1 < n && src.[!j + 1] = '{' then begin
        depth := !depth + 1;
        j := !j + 2
      end
      else incr j
    end
  done;
  (* an unterminated quote or ${ swallows the rest of the input *)
  (!j, !eq)

let tokenize (src : string) : token list =
  let toks = ref [] in
  let i = ref 0 in
  let n = String.length src in
  let emit k v st = toks := { k; v; start = st } :: !toks in
  while !i < n do
    (* blanks and comments *)
    let progress = ref true in
    while !progress && !i < n do
      progress := false;
      while !i < n && is_blank src.[!i] do
        incr i; progress := true
      done;
      if !i < n && src.[!i] = '#' then begin
        while !i < n && src.[!i] <> '\n' do
          incr i
        done;
        progress := true
      end
    done;
    if !i >= n then ()
    else if src.[!i] = '\n' then (emit K_NL "\n" !i; incr i)
    else match List.find_opt (fun (p, _) -> starts_at src !i p) two_char with
      | Some (p, k) -> emit k p !i; i := !i + String.length p
      | None ->
        match List.find_opt (fun (c, _) -> src.[!i] = c) single with
        | Some (c, k) -> emit k (String.make 1 c) !i; incr i
        | None ->
          let start = !i in
          if
            is_digit src.[!i]
            &&
            let j = ref !i in
            while !j < n && is_digit src.[!j] do
              incr j
            done;
            !j < n && (src.[!j] = '<' || src.[!j] = '>')
          then begin
            (* IO_NUMBER: digits immediately preceding an I/O operator *)
            while !i < n && is_digit src.[!i] do
              incr i
            done;
            emit K_I_NUM (String.sub src start (!i - start)) start
          end
          else begin
            (* A word is scanned in full first: only an entire word that equals
               a reserved name is a reserved token, so `in.txt' stays a word
               (POSIX 2.3 token recognition, unlike a prefix match). *)
            let (j, eq) = scan_word src !i n in
            let v = String.sub src start (j - start) in
            (match List.find_opt (fun (w, _) -> w = v) reserved with
             | Some (_, k) -> emit k v start
             | None ->
                 if eq >= 0 then emit K_ASSIGN v start
                 else emit K_WORD v start);
            i := j
          end
  done;
  emit K_EOF "" n;
  List.rev !toks

(* ── §3 AST ─────────────────────────────────────────────────────── *)

type redir_op = Less | Great | DGreat | Clobber

type redir =
  | R_file of int option * redir_op * string
  | R_dup_in of int option * string
  | R_dup_out of int option * string
  | R_rdwr of int option * string
  | R_here of int option * bool * string * bool (* io, dash, body, expand *)

type simple =
  { sm_assigns : (string * string) list
  ; sm_argv : string list
  ; sm_redirs : redir list }

type cmd =
  | Simple of simple
  | Pipeline of { pl_bang : bool; pl_stages : cmd list }
  | AndIf of cmd * cmd
  | OrIf of cmd * cmd
  | Seq of cmd * cmd
  | BraceGroup of cmd list
  | Subshell of cmd list
  | IfClause of
      { ic_cond : cmd list
      ; ic_then : cmd list
      ; ic_elifs : (cmd list * cmd list) list
      ; ic_else : cmd list option }
  | WhileClause of { wl_cond : cmd list; wl_body : cmd list }
  | UntilClause of { ul_cond : cmd list; ul_body : cmd list }
  | ForClause of
      { fc_var : string; fc_words : string list option; fc_body : cmd list }
  | CaseClause of
      { cc_word : string; cc_items : (string list * cmd list) list }
  | FunctionDef of { fd_name : string; fd_body : cmd }
  | Compound of cmd * redir list

(* ── §3b State ──────────────────────────────────────────────────── *)

type state =
  { vars : (string, string) Hashtbl.t
  ; funcs : (string, cmd) Hashtbl.t
  ; files : (string, string) Hashtbl.t
  ; env : (string, string) Hashtbl.t
  ; log : string list ref
  ; mutable params : string list
  ; mutable last_status : int
  ; mutable last_out : string
  ; mutable last_err : string
  ; mutable fuel : int }

let norm n = n land 255

let new_state ?(env = []) ?(files = []) () =
  let h kvs =
    let t = Hashtbl.create (max 4 (List.length kvs)) in
    List.iter (fun (k, v) -> Hashtbl.replace t k v) kvs;
    t
  in
  { vars = Hashtbl.create 16
  ; funcs = Hashtbl.create 8
  ; files = h files
  ; env = h env
  ; log = ref []
  ; params = []
  ; last_status = 0
  ; last_out = ""
  ; last_err = ""
  ; fuel = 1000 }

let log st s = st.log := s :: !(st.log)
let set_var st k v = Hashtbl.replace st.vars k v

(* Unbounded iteration (while/until, recursive functions) is fuel-bounded in
   the model: exhausting fuel is a checkable error rather than a hang, mirroring
   the Coq CLoop fuel parameter. *)
let decr_fuel st =
  if st.fuel <= 0 then raise FuelExhausted;
  st.fuel <- st.fuel - 1

let lookup_param st name =
  if name = "?" then string_of_int st.last_status
  else if name = "#" then string_of_int (List.length st.params)
  else if name = "@" || name = "*" then "" (* handled by expanders *)
  else if name <> "" && is_digit name.[0] then begin
    let i = (try int_of_string name with _ -> 0) in
    if i = 0 then "sh" (* $0: shell name *)
    else if i >= 1 && i <= List.length st.params then
      List.nth st.params (i - 1)
    else ""
  end
  else
    match Hashtbl.find_opt st.vars name with
    | Some v -> v
    | None -> (match Hashtbl.find_opt st.env name with Some v -> v | None -> "")

(* ── §3c Expansion: segments, splitting, ${} ───────────────────── *)

(* Segments of a raw word: (flag, text) with quotes removed and escapes
   processed per POSIX 2.2.1 quoting rules. Flag 'P' = plain (subject to
   field splitting), 'D' = double-quoted (expands but never splits),
   'S' = literal (single quotes or backslash-removed characters). *)
let mem l c = List.exists (fun x -> x = c) l

let segments raw =
  let parts = ref [] in
  let buf = Buffer.create 16 in
  let cur = ref 'P' in
  let n = String.length raw in
  let i = ref 0 in
  let flush () =
    let t = Buffer.contents buf in
    Buffer.clear buf;
    if String.length t > 0 || !cur <> 'P' then parts := (!cur, t) :: !parts
  in
  let literal () = flush (); cur := 'S' in
  while !i < n do
    (* the match must be parenthesised: otherwise the trailing incr i would be
       parsed as part of the last branch and quoted runs would not advance *)
    (let c = raw.[!i] in
     match !cur with
     | 'S' ->
        if c = '\'' then begin
          flush ();
          cur := 'P'
        end
        else Buffer.add_char buf c
    | _ -> (* P or D *)
      if c = '\\' && !i + 1 < n then begin
        let d = raw.[!i + 1] in
        if !cur = 'P' || mem [ '`'; '"'; '$'; '\\'; '\n' ] d then begin
          let back = !cur in
          literal ();
          Buffer.add_char buf d;
          flush ();
          cur := back;
          incr i
        end
        else Buffer.add_string buf "\\\\"
      end
      else if c = '\'' then begin
        flush ();
        cur := 'S'
      end
      else if c = '"' then begin
        flush ();
        cur := if !cur = 'D' then 'P' else 'D'
      end
      else Buffer.add_char buf c);
    incr i
  done;
  flush ();
  List.rev !parts

(* split a string into fields on IFS blanks (space/tab/newline) *)
let split_ifs s =
  let out = ref [] in
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    while !i < n && (s.[!i] = ' ' || s.[!i] = '\t' || s.[!i] = '\n') do
      incr i
    done;
    if !i < n then begin
      let start = !i in
      while !i < n && not (s.[!i] = ' ' || s.[!i] = '\t' || s.[!i] = '\n') do
        incr i
      done;
      out := String.sub s start (!i - start) :: !out
    end
  done;
  List.rev !out

(* Expand one segment's text (quotes already removed) into POSIX fields.
   split=true is the plain context: unquoted expansions undergo field
   splitting and an all-empty expansion contributes no field at all.
   split=false is the double-quoted context: expansions never split, and a
   literal empty expansion still yields one (empty) field. $@ is the one
   POSIX special case that splits even when quoted. Returns (fields, alive). *)
let expand_segment st ~split text =
  let n = String.length text in
  let fields = ref [] in
  let cur = Buffer.create 16 in
  let suppress = ref false in (* an empty $@ erases the whole word *)
  let at_expanded = ref false in (* $@ with params: no trailing empty field *)
  let i = ref 0 in
  let take_ref () =
    incr i;
    if !i < n && (mem [ '?'; '#'; '@'; '*'; '$'; '-'; '!'; '_' ] text.[!i])
    then begin
      let c = text.[!i] in
      incr i;
      String.make 1 c
    end
    else if !i < n && is_digit text.[!i] then begin
      (* $0..$9: one digit, no name continuation *)
      let c = text.[!i] in
      incr i;
      String.make 1 c
    end
    else if !i < n && text.[!i] = '{' then begin
      incr i;
      let b = Buffer.create 8 in
      while !i < n && text.[!i] <> '}' do
        Buffer.add_char b text.[!i];
        incr i
      done;
      if !i < n then incr i;
      Buffer.contents b
    end
    else begin
      let b = Buffer.create 8 in
      while !i < n && is_name_char text.[!i] do
        Buffer.add_char b text.[!i];
        incr i
      done;
      Buffer.contents b
    end
  in
  (* append v to the pending field, splitting it when in plain context *)
  let add_value v =
    if not split then Buffer.add_string cur v
    else
      match split_ifs v with
      | [] -> ()
      | hd :: tl ->
          Buffer.add_string cur hd;
          List.iter
            (fun f ->
              fields := !fields @ [ Buffer.contents cur ];
              Buffer.clear cur;
              Buffer.add_string cur f)
            tl
  in
  (* $@: each positional parameter becomes its own field *)
  let add_at () =
    let pending = ref (Buffer.contents cur) in
    Buffer.clear cur;
    List.iter
      (fun p ->
        let f =
          if !pending <> "" then begin
            let s = !pending in
            pending := "";
            s ^ p
          end
          else p
        in
        fields := !fields @ [ f ])
      st.params;
    if st.params = [] then begin
      suppress := true;
      Buffer.add_string cur !pending
    end
    else begin
      at_expanded := true;
      if !pending <> "" then Buffer.add_string cur !pending
    end
  in
  while !i < n do
    if
      text.[!i] = '$' && !i + 1 < n
      && (is_name_char text.[!i + 1] || text.[!i + 1] = '{'
          || mem [ '?'; '#'; '@'; '*'; '$'; '-'; '!'; '_' ] text.[!i + 1])
    then begin
      let name = take_ref () in
      match name with
      | "@" -> add_at ()
      | "*" -> add_value (String.concat " " st.params)
      | _ -> add_value (lookup_param st name)
    end
    else begin
      Buffer.add_char cur text.[!i];
      incr i
    end
  done;
  let acc = Buffer.contents cur in
  if acc <> "" || (not split && not !suppress && not !at_expanded) then
    fields := !fields @ [ acc ];
  (!fields, !fields <> [])

(* full-word expansion producing POSIX fields (unquoted expansion splits) *)
let expand_fields st raw =
  let segs = segments raw in
  let cur = Buffer.create 16 in
  let out = ref [] in
  let alive = ref false in
  List.iter
    (fun (flag, text) ->
      if flag = 'S' then begin
        Buffer.add_string cur text;
        alive := true (* quoted content survives even when empty *)
      end
      else begin
        let split = flag = 'P' in
        let (fs, a) = expand_segment st ~split text in
        if a then alive := true;
        match fs with
        | [] -> ()
        | hd :: tl ->
            Buffer.add_string cur hd;
            List.iter
              (fun f ->
                out := !out @ [ Buffer.contents cur ];
                Buffer.clear cur;
                Buffer.add_string cur f)
              tl
      end)
    segs;
  let last = Buffer.contents cur in
  if last <> "" || !alive then out := !out @ [ last ];
  !out

(* expansion without splitting (assignments, here-doc bodies, case words) *)
let expand_nosplit st raw =
  let segs = segments raw in
  String.concat ""
    (List.map
       (fun (flag, text) ->
         if flag = 'S' then text
         else
           let (fs, _) = expand_segment st ~split:false text in
           String.concat " " fs)
       segs)

(* ── §4 Parser ──────────────────────────────────────────────────── *)

(* `spans' are source ranges covered by here-document bodies. The tokenizer
   has already produced tokens for that literal text, so the parser must ignore
   them: advance() steps over any token whose start offset lies in a span. This
   keeps the rest of the here-document's first line (trailing redirects, `;')
   parseable instead of swallowing it. *)
type parser =
  { toks : token array
  ; src : string
  ; mutable pos : int
  ; mutable spans : (int * int) list }

let cur p = p.toks.(p.pos)
let at p k = (cur p).k = k

let in_span p i =
  let s = (p.toks.(i)).start in
  List.exists (fun (a, b) -> s >= a && s < b) p.spans

let advance p =
  p.pos <- p.pos + 1;
  while p.pos < Array.length p.toks && in_span p p.pos do
    p.pos <- p.pos + 1
  done

let expect p k msg =
  if not (at p k) then raise (Syntax msg);
  advance p

let skip_nl p = while at p K_NL do advance p done

let is_sep k = k = K_SEMI || k = K_NL || k = K_AMP

(* token kinds that are structural operators anywhere in a list *)
let structural =
  [ K_SEMI; K_NL; K_AMP; K_PIPE; K_ANDIF; K_ORIF; K_EOF; K_DSEMI; K_RBRACE
  ; K_RPAREN ]

(* a WORD-ish token: usable as an argument/word in command suffix position *)
let wordish k =
  k = K_WORD || k = K_IF || k = K_THEN || k = K_ELSE || k = K_ELIF
  || k = K_FI || k = K_DO || k = K_DONE || k = K_CASE || k = K_ESAC
  || k = K_WHILE || k = K_UNTIL || k = K_FOR || k = K_IN || k = K_BANG
  || k = K_LBRACE || k = K_ASSIGN

(* the first token of a simple command cannot be a reserved word used
   as a mere argument: command position dispatch handles reserved forms *)
let start_stop k =
  List.mem k structural || k = K_THEN || k = K_ELSE || k = K_ELIF
  || k = K_FI || k = K_DONE || k = K_ESAC || k = K_RBRACE || k = K_RPAREN
  || k = K_DSEMI

let rec parse_program p =
  let items = ref [] in
  skip_nl p;
  while not (at p K_EOF) do
    if is_sep (cur p).k then advance p
    else begin
      items := !items @ [ parse_and_or p ];
      if is_sep (cur p).k then advance p
      else if not (at p K_EOF) then raise (Syntax "expected separator")
    end
  done;
  !items

and parse_and_or p =
  let node = ref (parse_pipeline p) in
  while at p K_ANDIF || at p K_ORIF do
    let is_and = at p K_ANDIF in
    advance p;
    skip_nl p;
    let rhs = parse_pipeline p in
    node := if is_and then AndIf (!node, rhs) else OrIf (!node, rhs)
  done;
  !node

and parse_pipeline p =
  let bang = if at p K_BANG then (advance p; true) else false in
  if start_stop (cur p).k then raise (Syntax "empty pipeline");
  let stages = ref [ parse_command p ] in
  while at p K_PIPE do
    advance p;
    skip_nl p;
    if start_stop (cur p).k then raise (Syntax "empty pipeline stage");
    stages := !stages @ [ parse_command p ]
  done;
  Pipeline { pl_bang = bang; pl_stages = !stages }

and parse_command p =
  (* POSIX 2.9.1: compound_command redirect_line* — redirects may trail a
     compound command and apply to the whole compound. *)
  let c = parse_command_form p in
  let redirs = ref [] in
  while redir_start p do
    parse_redir_token p redirs
  done;
  if !redirs = [] then c else Compound (c, !redirs)

and parse_command_form p =
  match (cur p).k with
  | K_IF -> parse_if p
  | K_WHILE -> parse_while p
  | K_UNTIL -> parse_until p
  | K_FOR -> parse_for p
  | K_CASE -> parse_case p
  | K_LBRACE ->
      advance p;
      skip_nl p;
      let body = parse_compound_list p [ K_RBRACE ] in
      expect p K_RBRACE "expected }";
      BraceGroup body
  | K_LPAREN ->
      advance p;
      skip_nl p;
      let body = parse_compound_list p [ K_RPAREN ] in
      expect p K_RPAREN "expected )";
      Subshell body
  | K_WORD when kind_at p 1 = K_LPAREN && kind_at p 2 = K_RPAREN ->
      parse_fundef p
  | _ -> parse_simple p

and redir_op_kind k =
  k = K_LESS || k = K_GREAT || k = K_DGREAT || k = K_CLOBBER
  || k = K_LESSAND || k = K_GREATAND || k = K_LESSGREAT || k = K_DLESS
  || k = K_DLESSDASH

and redir_start p =
  let k = (cur p).k in
  redir_op_kind k
  || (k = K_I_NUM && let j = p.pos + 1 in
        j < Array.length p.toks && redir_op_kind (p.toks.(j)).k)

and parse_redir_token p redirs =
  let io =
    if at p K_I_NUM then begin
      let n = int_of_string (cur p).v in
      advance p;
      Some n
    end
    else None
  in
  let k = (cur p).k in
  if not (redir_op_kind k) then
    raise (Syntax ("unexpected redirect token " ^ kind_name k));
  if k = K_LESS || k = K_GREAT || k = K_DGREAT || k = K_CLOBBER then
    parse_file_redir p io redirs
  else if k = K_LESSAND || k = K_GREATAND || k = K_LESSGREAT then
    parse_dup_redir p io redirs
  else parse_here_redir p io redirs

and kind_at p off =
  let j = p.pos + off in
  if j < Array.length p.toks then (p.toks.(j)).k else K_EOF

and parse_compound_list p stop =
  let items = ref [] in
  skip_nl p;
  while not (List.mem (cur p).k stop) && not (at p K_EOF) do
    items := !items @ [ parse_and_or p ];
    if is_sep (cur p).k then begin
      advance p;
      skip_nl p
    end
    else if not (List.mem (cur p).k stop || at p K_EOF) then
      raise (Syntax "expected separator")
  done;
  !items

and parse_if p =
  expect p K_IF "expected if";
  skip_nl p;
  let ic_cond = parse_compound_list p [ K_THEN ] in
  expect p K_THEN "expected then";
  skip_nl p;
  let ic_then = parse_compound_list p [ K_ELSE; K_ELIF; K_FI ] in
  let ic_elifs = ref [] in
  while at p K_ELIF do
    advance p;
    skip_nl p;
    let c = parse_compound_list p [ K_THEN ] in
    expect p K_THEN "expected then (elif)";
    skip_nl p;
    let t = parse_compound_list p [ K_ELSE; K_ELIF; K_FI ] in
    ic_elifs := !ic_elifs @ [ (c, t) ]
  done;
  let ic_else =
    if at p K_ELSE then begin
      advance p;
      skip_nl p;
      Some (parse_compound_list p [ K_FI ])
    end
    else None
  in
  expect p K_FI "expected fi";
  IfClause { ic_cond; ic_then; ic_elifs = !ic_elifs; ic_else }

and parse_while p =
  expect p K_WHILE "expected while";
  skip_nl p;
  let wl_cond = parse_compound_list p [ K_DO ] in
  expect p K_DO "expected do";
  skip_nl p;
  let wl_body = parse_compound_list p [ K_DONE ] in
  expect p K_DONE "expected done";
  WhileClause { wl_cond; wl_body }

and parse_until p =
  expect p K_UNTIL "expected until";
  skip_nl p;
  let ul_cond = parse_compound_list p [ K_DO ] in
  expect p K_DO "expected do";
  skip_nl p;
  let ul_body = parse_compound_list p [ K_DONE ] in
  expect p K_DONE "expected done";
  UntilClause { ul_cond; ul_body }

and wordlist_token k = k = K_WORD || wordish k (* reserved as plain words *)

and parse_for p =
  expect p K_FOR "expected for";
  if not (at p K_WORD) then raise (Syntax "for expects name");
  let fc_var = (cur p).v in
  advance p;
  let fc_words =
    if at p K_IN then begin
      advance p;
      skip_nl p;
      let ws = ref [] in
      while wordlist_token (cur p).k && not (is_sep (cur p).k) do
        ws := !ws @ [ (cur p).v ];
        advance p
      done;
      Some !ws
    end
    else None
  in
  (* sequential separator before do_group *)
  (match (cur p).k with
   | K_SEMI | K_NL -> advance p; skip_nl p
   | K_DO -> ()
   | _ -> raise (Syntax "expected ; or newline before do"));
  expect p K_DO "expected do";
  skip_nl p;
  let fc_body = parse_compound_list p [ K_DONE ] in
  expect p K_DONE "expected done";
  ForClause { fc_var; fc_words; fc_body }

and parse_case p =
  expect p K_CASE "expected case";
  if not (wordish (cur p).k) then raise (Syntax "case expects word");
  let cc_word = (cur p).v in
  advance p;
  expect p K_IN "expected in";
  skip_nl p;
  let items = ref [] in
  while not (at p K_ESAC) && not (at p K_EOF) do
    (* optional leading ( *)
    if at p K_LPAREN then advance p;
    let pats = ref [ (cur p).v ] in
    if not (wordish (cur p).k) then raise (Syntax "case expects pattern");
    advance p;
    while at p K_PIPE do
      advance p;
      if not (wordish (cur p).k) then raise (Syntax "case expects pattern");
      pats := !pats @ [ (cur p).v ];
      advance p
    done;
    expect p K_RPAREN "expected ) in case";
    skip_nl p;
    let body = parse_compound_list p [ K_DSEMI; K_ESAC ] in
    if at p K_DSEMI then advance p;
    skip_nl p;
    items := !items @ [ (!pats, body) ]
  done;
  expect p K_ESAC "expected esac";
  CaseClause { cc_word; cc_items = !items }

and parse_fundef p =
  let fd_name = (cur p).v in
  advance p;
  expect p K_LPAREN "expected ( in function definition";
  expect p K_RPAREN "expected ) in function definition";
  skip_nl p;
  let fd_body = parse_command p in
  match fd_body with
  | Simple _ -> raise (Syntax "function body must be a compound command")
  | c -> FunctionDef { fd_name; fd_body = c }

and parse_simple p =
  let assigns = ref [] and argv = ref [] and redirs = ref [] in
  let has_item () = !argv <> [] || !assigns <> [] || !redirs <> [] in
  let cont k =
    k = K_WORD || k = K_ASSIGN || k = K_LESS || k = K_GREAT || k = K_DGREAT
    || k = K_CLOBBER || k = K_I_NUM || k = K_DLESS || k = K_DLESSDASH
    || k = K_LESSAND || k = K_GREATAND || k = K_LESSGREAT
    || (wordish k && has_item ())
  in
  while cont (cur p).k do
    match (cur p).k with
    | K_ASSIGN when !argv = [] ->
        (* assignments are cmd_prefix only (POSIX 2.9.1): before the first
           argv word they bind; after, the token is a literal argument word *)
        let v = (cur p).v in
        let eq = String.index v '=' in
        assigns :=
          !assigns
          @ [ (String.sub v 0 eq,
               String.sub v (eq + 1) (String.length v - eq - 1)) ];
        advance p
    | _ ->
      if wordish (cur p).k then begin
        argv := !argv @ [ (cur p).v ];
        advance p
      end
      else parse_redir_token p redirs
  done;
  Simple { sm_assigns = !assigns; sm_argv = !argv; sm_redirs = !redirs }

and parse_file_redir p io redirs =
  let op =
    match (cur p).k with
    | K_LESS -> Less
    | K_GREAT -> Great
    | K_DGREAT -> DGreat
    | K_CLOBBER -> Clobber
    | _ -> raise (Syntax "expected redirect operator")
  in
  advance p;
  let f = redir_word p in
  redirs := !redirs @ [ R_file (io, op, f) ]

and parse_dup_redir p io redirs =
  let k = (cur p).k in
  advance p;
  let w = redir_word p in
  let r =
    match k with
    | K_LESSAND -> R_dup_in (io, w)
    | K_GREATAND -> R_dup_out (io, w)
    | K_LESSGREAT -> R_rdwr (io, w)
    | _ -> raise (Syntax "dup operator")
  in
  redirs := !redirs @ [ r ]

and parse_here_redir p io redirs =
  let dash = at p K_DLESSDASH in
  advance p;
  let delim_raw = redir_word p in
  (* Consume the here-document body from the raw source: it starts at the
     newline ending this line and ends at the first line that equals the
     delimiter (after leading-tab stripping for <<-, POSIX 2.7.4). The
     delimiter itself is quote-stripped at parse time; variable expansion of
     the body is deferred to execution, and a quoted delimiter suppresses it. *)
  let li =
    try String.index_from p.src (cur p).start '\n'
    with Not_found -> raise (Syntax "here-document body missing")
  in
  let body_start = li + 1 in
  let has_quote ch = ch = '\'' || ch = '"' || ch = '\\' in
  let quoted =
    let n = String.length delim_raw in
    let found = ref false in
    for k = 0 to n - 1 do
      if has_quote delim_raw.[k] then found := true
    done;
    !found
  in
  let delim =
    String.concat "" (List.map snd (segments delim_raw))
  in
  let expand = not quoted in
  let rec find_end from =
    let nl =
      try String.index_from p.src from '\n'
      with Not_found -> String.length p.src
    in
    let line0 = String.sub p.src from (nl - from) in
    let line =
      if dash then
        let k = ref 0 in
        while !k < String.length line0 && line0.[!k] = '\t' do
          incr k
        done;
        String.sub line0 !k (String.length line0 - !k)
      else line0
    in
    if line = delim then from
    else if nl >= String.length p.src then
      raise (Syntax "here-document delimiter not found")
    else find_end (nl + 1)
  in
  let body_end = find_end body_start in
  let body = String.sub p.src body_start (body_end - body_start) in
  (* skip tokens until past the delimiter line *)
  let after =
    try String.index_from p.src body_end '\n'
    with Not_found -> String.length p.src
  in
  let after = min (String.length p.src) (after + 1) in
  p.spans <- (body_start, after) :: p.spans;
  if in_span p p.pos then advance p;
  redirs := !redirs @ [ R_here (io, dash, body, expand) ]

and redir_word p =
  let k = (cur p).k in
  if k = K_WORD || k = K_ASSIGN || wordish k then begin
    let v = (cur p).v in
    advance p;
    v
  end
  else raise (Syntax "expected redirect word")

and split_on s c =
  let out = ref [] in
  let buf = Buffer.create 16 in
  String.iter
    (fun ch ->
      if ch = c then begin
        out := !out @ [ Buffer.contents buf ];
        Buffer.clear buf
      end
      else Buffer.add_char buf ch)
    s;
  out := !out @ [ Buffer.contents buf ];
  !out

(* ── §5 Interpreter ─────────────────────────────────────────────── *)

type sink = { sbuf : string ref; sfile : string; sapp : bool }
type fdval = Fd_in of string | Fd_out of sink | Fd_closed

let expand st ~split raw =
  if split then expand_fields st raw else [expand_nosplit st raw]

let route st (tbl : (int, fdval) Hashtbl.t) out err =
  (* Flush redirected sinks into the file space. Sinks are deduplicated by
     buffer identity so that `>f 2>&1` writes f once, and the ordering of the
     flushes does not matter. *)
  let done_refs = ref ([] : sink list) in
  Hashtbl.iter
    (fun _ v ->
      match v with
      | Fd_out s ->
          if not (List.exists (fun s2 -> s2.sbuf == s.sbuf) !done_refs) then begin
            done_refs := s :: !done_refs;
            if s.sfile <> "" then begin
              let existing =
                match Hashtbl.find_opt st.files s.sfile with Some c -> c
                | None -> ""
              in
              let content = if s.sapp then existing ^ !(s.sbuf) else !(s.sbuf) in
              Hashtbl.replace st.files s.sfile content
            end
          end
      | _ -> ())
    tbl;
  (* The command's visible stdout/stderr are the contents of the two sinks it
     inherited; a redirection replaces the fd table entry, never the inherited
     sink, so `2>&1 > f` correctly leaves the error text on inherited stdout. *)
  (!(out.sbuf), !(err.sbuf))

(* build the fd table for a command: returns (tbl, sink1, sink2, open_fail) *)
let build_fds st base_input redirs =
  let sink1 = { sbuf = ref ""; sfile = ""; sapp = false } in
  let sink2 = { sbuf = ref ""; sfile = ""; sapp = false } in
  let tbl : (int, fdval) Hashtbl.t = Hashtbl.create 8 in
  Hashtbl.replace tbl 0 (Fd_in base_input);
  Hashtbl.replace tbl 1 (Fd_out sink1);
  Hashtbl.replace tbl 2 (Fd_out sink2);
  let failed = ref false in
  let dflt op = match op with Less -> 0 | _ -> 1 in
  (* POSIX 2.9.1: redirections are performed in order and a failure aborts the
     command, so the redirects after the failing one are not applied. *)
  List.iter
    (fun r ->
      if !failed then ()
      else match r with
      | R_file (io, op, file_raw) ->
          let fd = match io with Some n -> n | None -> dflt op in
          let file = expand_nosplit st file_raw in
          (match op with
           | Less ->
               (match Hashtbl.find_opt st.files file with
                | Some c -> Hashtbl.replace tbl fd (Fd_in c)
                | None -> failed := true)
           | Great | Clobber ->
               Hashtbl.replace tbl fd
                 (Fd_out { sbuf = ref ""; sfile = file; sapp = false })
           | DGreat ->
               Hashtbl.replace tbl fd
                 (Fd_out { sbuf = ref ""; sfile = file; sapp = true }))
      | R_dup_in (io, w_raw) ->
          let fd = match io with Some n -> n | None -> 0 in
          let w = expand_nosplit st w_raw in
          (match int_of_string_opt w with
           | Some n ->
               (match Hashtbl.find_opt tbl n with
                | Some (Fd_in c) -> Hashtbl.replace tbl fd (Fd_in c)
                | _ -> Hashtbl.replace tbl fd (Fd_in ""))
           | None ->
               if w = "-" then Hashtbl.replace tbl fd Fd_closed
               else match Hashtbl.find_opt st.files w with
                    | Some c -> Hashtbl.replace tbl fd (Fd_in c)
                    | None -> failed := true)
      | R_dup_out (io, w_raw) ->
          let fd = match io with Some n -> n | None -> 1 in
          let w = expand_nosplit st w_raw in
          (match int_of_string_opt w with
           | Some n ->
               (match Hashtbl.find_opt tbl n with
                | Some v -> Hashtbl.replace tbl fd v
                | None -> ())
           | None ->
               if w = "-" then Hashtbl.replace tbl fd Fd_closed
               else Hashtbl.replace tbl fd
                      (Fd_out { sbuf = ref ""; sfile = w; sapp = false }))
      | R_rdwr (io, w_raw) ->
          let fd = match io with Some n -> n | None -> 1 in
          let w = expand_nosplit st w_raw in
          Hashtbl.replace tbl fd
            (Fd_out { sbuf = ref ""; sfile = w; sapp = false })
      | R_here (io, dash, body, do_expand) ->
          let fd = match io with Some n -> n | None -> 0 in
          let processed =
            let lines = split_on body '\n' in
            let map_line l =
              let l =
                if dash then
                  let k = ref 0 in
                  while !k < String.length l && l.[!k] = '\t' do
                    incr k
                  done;
                  String.sub l !k (String.length l - !k)
                else l
              in
              if do_expand then expand_nosplit st l else l
            in
            String.concat "\n" (List.map map_line lines)
          in
          Hashtbl.replace tbl fd (Fd_in processed))
    redirs;
  (tbl, sink1, sink2, !failed)

let snapshot_tbl (t : ('k, 'v) Hashtbl.t) : ('k * 'v) list =
  Hashtbl.fold (fun k v a -> (k, v) :: a) t []

let restore_tbl (t : ('k, 'v) Hashtbl.t) (snap : ('k * 'v) list) : unit =
  Hashtbl.clear t;
  List.iter (fun (k, v) -> Hashtbl.replace t k v) snap

let rec exec_list st input l =
  match l with
  | [] -> (0, "", "")
  | [ c ] -> exec_cmd st input c
  | c :: tl ->
      let (_, o1, e1) = exec_cmd st input c in
      let (s, o2, e2) = exec_list st "" tl in
      (s, o1 ^ o2, e1 ^ e2)

and exec_simple st input ({ sm_assigns; sm_argv; sm_redirs } : simple) =
  (* POSIX 2.9.1: prefix assignments expand without field splitting. With a
     command name they bind only for that command and are then undone; with no
     command name they persist in the current execution environment. *)
  let binds =
    List.map
      (fun (k, v) -> (expand_nosplit st k, expand_nosplit st v))
      sm_assigns
  in
  let saved =
    List.map (fun (k, _) -> (k, Hashtbl.find_opt st.vars k)) binds
  in
  List.iter (fun (k, v) -> set_var st k v) binds;
  let unbind () =
    List.iter2
      (fun (k, _) (_, old) ->
        match old with
        | Some o -> Hashtbl.replace st.vars k o
        | None -> Hashtbl.remove st.vars k)
      binds saved
  in
  let scoped f x =
    if sm_argv = [] then f x
    else begin
      let r = try f x with ExitShell c -> unbind (); raise (ExitShell c) in
      unbind ();
      r
    end
  in
  let (tbl, sink1, sink2, open_failed) = build_fds st input sm_redirs in
  if open_failed then begin
    log st "open fail";
    let errf =
      match Hashtbl.find_opt tbl 2 with
      | Some (Fd_out s) -> s
      | _ -> sink2
    in
    errf.sbuf := !(errf.sbuf) ^ "sh: no such file\n";
    let (_, ve) = route st tbl sink1 sink2 in
    unbind ();
    (2, "", ve)
  end
  else
    scoped
      (fun () ->
        let in_fd =
          match Hashtbl.find_opt tbl 0 with
          | Some (Fd_in c) -> c
          | _ -> ""
        in
        let fields =
          List.concat_map (fun raw -> expand_fields st raw) sm_argv
        in
        let name = if fields = [] then "" else List.hd fields in
        let rest = if fields = [] then [] else List.tl fields in
        log st ("run " ^ name ^ " " ^ String.concat "," rest);
        let (code, out, err) =
          if name = "exit" then begin
            (* exit is a special builtin: a non-numeric operand is an error
               status >1, and no further commands run *)
            match rest with
            | [] -> raise (ExitShell st.last_status)
            | [ x ] -> (
                match int_of_string_opt x with
                | Some n -> raise (ExitShell (norm n))
                | None ->
                    raise (ExitShell 2))
            | _ -> raise (ExitShell 2)
          end
          else
            match Hashtbl.find_opt st.funcs name with
            | Some body ->
                (* function lookup precedes command lookup, POSIX 2.9.1.1 *)
                decr_fuel st;
                let saved_params = st.params in
                st.params <- rest;
                let (s, o, e) =
                  try exec_cmd st in_fd body
                  with ExitShell c ->
                    st.params <- saved_params;
                    raise (ExitShell c)
                in
                st.params <- saved_params;
                (s, o, e)
            | None -> run_extern name rest in_fd
        in
        (match Hashtbl.find_opt tbl 1 with
         | Some (Fd_out s) -> s.sbuf := !(s.sbuf) ^ out
         | _ -> ());
        (match Hashtbl.find_opt tbl 2 with
         | Some (Fd_out s) -> s.sbuf := !(s.sbuf) ^ err
         | _ -> ());
        let (vout, verr) = route st tbl sink1 sink2 in
        (code, vout, verr))
      ()

and run_extern name args input =
  match name with
  | "" -> (0, "", "")
  | "true" -> (0, "", "")
  | "false" -> (1, "", "")
  | "echo" -> (0, String.concat " " args ^ "\n", "")
  | "cat" -> (0, input, "")
  | "wc" ->
      let c = List.length (split_ifs input) in
      (0, string_of_int c ^ "\n", "")
  | "test" ->
      (match args with
       | [ a; "="; b ] -> (if a = b then (0, "", "") else (1, "", ""))
       | _ -> (2, "", "test: usage\n"))
  | _ ->
      (127, "", Printf.sprintf "sh: %s: not found\n" name)

and exec_cmd st input c =
  let (s, o, e) = exec_cmd' st input c in
  st.last_status <- s;
  st.last_out <- o;
  st.last_err <- e;
  (s, o, e)

and exec_cmd' st input c =
  match c with
  | Simple x -> exec_simple st input x
  | Pipeline { pl_bang; pl_stages } ->
      let rec run_stages inp errs = function
        | [] -> (0, "", errs)
        | [ s2 ] ->
            let (code, o, e) = exec_cmd st inp s2 in
            (code, o, errs ^ e)
        | s2 :: tl ->
            (* POSIX 2.9.2: every stage runs; the whole pipeline's input to the
               next stage is this stage's output regardless of its status *)
            let (_code, o, e) = exec_cmd st inp s2 in
            run_stages o (errs ^ e) tl
      in
      let (code, out, err) = run_stages "" "" pl_stages in
      let code = if pl_bang then (if code = 0 then 1 else 0) else code in
      (code, out, err)
  | AndIf (l, r) ->
      let (ls, lo, le) = exec_cmd st "" l in
      if ls = 0 then begin
        let (rs, ro, re) = exec_cmd st "" r in
        (rs, lo ^ ro, le ^ re)
      end
      else (ls, lo, le)
  | OrIf (l, r) ->
      let (ls, lo, le) = exec_cmd st "" l in
      if ls <> 0 then begin
        let (rs, ro, re) = exec_cmd st "" r in
        (rs, lo ^ ro, le ^ re)
      end
      else (ls, lo, le)
  | Seq (l, r) ->
      let (_, lo, le) = exec_cmd st "" l in
      let (rs, ro, re) = exec_cmd st "" r in
      (rs, lo ^ ro, le ^ re)
  | BraceGroup body -> exec_list st input body
  | Subshell body ->
      let saved_vars = snapshot_tbl st.vars in
      let saved_funcs = snapshot_tbl st.funcs in
      let saved_params = st.params in
      (try
         let res = exec_list st input body in
         restore_tbl st.vars saved_vars;
         restore_tbl st.funcs saved_funcs;
         st.params <- saved_params;
         res
       with ExitShell cc ->
         restore_tbl st.vars saved_vars;
         restore_tbl st.funcs saved_funcs;
         st.params <- saved_params;
         (cc, "", ""))
  | IfClause { ic_cond; ic_then; ic_elifs; ic_else } ->
      let (cs, co, ce) = exec_list st "" ic_cond in
      if cs = 0 then begin
        let (s, o, e) = exec_list st "" ic_then in
        (s, co ^ o, ce ^ e)
      end
      else begin
        let found = ref None in
        List.iter
          (fun (ec, et) ->
            if !found = None then begin
              let (s, o, e) = exec_list st "" ec in
              if s = 0 then found := Some (s, o, e, et)
            end)
          ic_elifs;
        match !found with
        | Some (_, eo, ee, body) ->
            let (s, o, e) = exec_list st "" body in
            (s, co ^ eo ^ o, ce ^ ee ^ e)
        | None ->
            (match ic_else with
             | Some body ->
                 let (s, o, e) = exec_list st "" body in
                 (s, co ^ o, ce ^ e)
             | None -> (0, co, ce))
      end
  | WhileClause { wl_cond; wl_body } -> loop_run st wl_cond wl_body true
  | UntilClause { ul_cond; ul_body } -> loop_run st ul_cond ul_body false
  | ForClause { fc_var; fc_words; fc_body } ->
      (* POSIX 2.9.5.1: with no words after `in', iterate the positional params *)
      let words =
        match fc_words with
        | None -> st.params
        | Some ws -> List.concat_map (fun w -> expand_fields st w) ws
      in
      let st_acc = ref (0, "", "") in
      List.iter
        (fun w ->
          set_var st fc_var w;
          let (s, o, e) = exec_list st "" fc_body in
          let (po, pe) =
            match !st_acc with (_, po, pe) -> (po, pe)
          in
          st_acc := (s, po ^ o, pe ^ e))
        words;
      !st_acc
  | CaseClause { cc_word; cc_items } ->
      let word = expand_nosplit st cc_word in
      let res = ref (0, "", "") in
      let done_ = ref false in
      List.iter
        (fun (pats, body) ->
          if not !done_ then
            if List.exists
                 (fun pat -> glob_match (expand_nosplit st pat) word)
                 pats
            then begin
              done_ := true;
              res := exec_list st "" body
            end)
        cc_items;
      !res
  | FunctionDef { fd_name; fd_body } ->
      Hashtbl.replace st.funcs fd_name fd_body;
      (0, "", "")
  | Compound (inner, redirs) ->
      let (tbl, sink1, sink2, open_failed) = build_fds st input redirs in
      if open_failed then (2, "", "sh: no such file\n")
      else begin
        let in_fd =
          match Hashtbl.find_opt tbl 0 with Some (Fd_in c) -> c | _ -> ""
        in
        let (s, o, e) = exec_cmd st in_fd inner in
        (match Hashtbl.find_opt tbl 1 with
         | Some (Fd_out sn) -> sn.sbuf := !(sn.sbuf) ^ o
         | _ -> ());
        (match Hashtbl.find_opt tbl 2 with
         | Some (Fd_out sn) -> sn.sbuf := !(sn.sbuf) ^ e
         | _ -> ());
        let (vo, ve) = route st tbl sink1 sink2 in
        (s, vo, ve)
      end

(* while/until share one fuel-bounded driver: the body runs while the
   condition status equals `run_on_zero` (true for while, false for until).
   The loop status is the last body status, or 0 when the body never ran
   (POSIX 2.9.5: a loop that is never entered returns success). *)
and loop_run st cond body run_on_zero =
  let outs = ref ("", "") in
  let status = ref 0 in
  let stop = ref false in
  while not !stop do
    decr_fuel st;
    let (cs, co, ce) = exec_list st "" cond in
    outs := (fst !outs ^ co, snd !outs ^ ce);
    if (cs = 0) = run_on_zero then begin
      let (bs, bo, be) = exec_list st "" body in
      outs := (fst !outs ^ bo, snd !outs ^ be);
      status := bs
    end
    else stop := true
  done;
  (!status, fst !outs, snd !outs)

(* POSIX 2.13.1 basic pattern matching: * ? [...] with ! negation and ranges *)
and glob_match pat str =
  let pn = String.length pat and sn = String.length str in
  let rec go pi si =
    if pi = pn then si = sn
    else match pat.[pi] with
      | '*' ->
          let rec star k = k <= sn && (go (pi + 1) k || star (k + 1)) in
          star si
      | '?' -> si < sn && go (pi + 1) (si + 1)
      | '[' ->
          let close =
            let rec find j =
              if j >= pn then -1
              else if pat.[j] = ']' && j > pi + 1 then j
              else find (j + 1)
            in
            find (pi + 1)
          in
          if close = -1 then false
          else begin
            let neg = pi + 1 < pn && pat.[pi + 1] = '!' in
            let cs =
              String.sub pat (if neg then pi + 2 else pi + 1)
                (close - (if neg then pi + 2 else pi + 1))
            in
            si < sn &&
            (if si >= sn then false
             else
               let hit = class_member cs str.[si] in
               (hit <> neg) && go (close + 1) (si + 1))
          end
      | '\\' -> pi + 1 < pn && si < sn && str.[si] = pat.[pi + 1]
                && go (pi + 2) (si + 1)
      | ch -> si < sn && str.[si] = ch && go (pi + 1) (si + 1)
  and class_member cs ch =
    let len = String.length cs in
    let rec scan i =
      if i >= len then false
      else if i + 2 < len && cs.[i + 1] = '-' then
        (* a-b is a range: it either matches or scanning resumes after it *)
        if ch >= cs.[i] && ch <= cs.[i + 2] then true else scan (i + 3)
      else cs.[i] = ch || scan (i + 1)
    in
    scan 0
  in
  go 0 0

(* ── §6 Invariants & runner ─────────────────────────────────────── *)

let inv_status_range n = 0 <= n && n <= 255

(* assignment round-trip: expanding "$k" yields exactly the stored value *)
let inv_assignment_roundtrip st =
  let ok = ref true in
  Hashtbl.iter
    (fun k _ ->
      if k <> "" && not (is_digit k.[0]) then
        let fields = expand_fields st ("\"" ^ "$" ^ k ^ "\"") in
        let v = match Hashtbl.find_opt st.vars k with Some x -> x | None -> "" in
        if fields <> [v] && fields <> [String.concat "" fields] then
          if fields <> [v] then ok := false)
    st.vars;
  !ok

(* Parse then execute: the whole program is validated before any command runs,
   which is what makes the determinism checks in §7 meaningful. *)
let sh ?env ?files src =
  let st = new_state ?env ?files () in
  let p =
    { toks = Array.of_list (tokenize src); src; pos = 0; spans = [] }
  in
  let items = parse_program p in
  let (final_status, out, err) =
    try exec_list st "" items with ExitShell n -> (n, "", "")
  in
  let final_status = norm final_status in
  st.last_status <- final_status;
  if not (inv_status_range final_status) then
    failwith "INV violated: exit status outside 0..255";
  if not (inv_assignment_roundtrip st) then
    failwith "INV violated: parameter expansion round-trip broken";
  (final_status, st, out, err)

(* ── §7 Verification suite ──────────────────────────────────────── *)

let fails = ref 0
let checks = ref 0

let check name cond =
  incr checks;
  if cond then printf "  [PASS] %s\n" name
  else begin
    printf "  [FAIL] %s\n" name;
    incr fails
  end;
  flush stdout

(* (status, out, state) *)
(* A corpus program that fails to parse or exhausts fuel must report FAIL, not
   abort the oracle: 256 and -1 are statuses no POSIX check can match. *)
let run3 ?env ?files src =
  try
    let (s, st, o, e) = sh ?env ?files src in
    (s, o ^ e, st)
  with
  | Syntax m ->
      printf "  [corpus syntax error: %s in %S]\n" m src;
      (256, "", new_state ())
  | FuelExhausted ->
      printf "  [corpus fuel exhausted in %S]\n" src;
      (-1, "", new_state ())

let run ?env ?files src =
  let (s, _, st) = run3 ?env ?files src in
  (s, st)

let expect_syntax nm src =
  try
    ignore (sh src);
    check nm false
  with Syntax _ -> check nm true

let expect_fuel nm src =
  try
    ignore (sh src);
    check nm false
  with FuelExhausted -> check nm true

let file_of st name =
  match Hashtbl.find_opt st.files name with Some c -> c | None -> "\000missing"

let var_of st name =
  match Hashtbl.find_opt st.vars name with Some v -> v | None -> ""

let log_str st = String.concat ";" (List.rev !(st.log))

let contains hay needle =
  let lh = String.length hay and ln = String.length needle in
  let rec go i =
    i + ln <= lh && (String.sub hay i ln = needle || go (i + 1))
  in
  ln > 0 && go 0

let snapshot st =
  let dump t =
    List.sort String.compare
      (Hashtbl.fold (fun k v acc -> (k ^ "=" ^ v) :: acc) t [])
  in
  let keys t =
    List.sort String.compare (Hashtbl.fold (fun k _ acc -> k :: acc) t [])
  in
  (keys st.funcs, dump st.vars, dump st.files, List.rev !(st.log),
   st.params, st.last_status, st.last_out, st.last_err)

let kinds src = List.map (fun t -> t.k) (tokenize src)
let values src = List.map (fun t -> t.v) (tokenize src)

let () =
  printf "=== Synrc POSIX Shell Reference Model (full BNF scope) ===\n\n";

  printf "-- L1: lexer --\n";
  check "lex reserved words & structural operators"
    (kinds "if x=1; then true fi"
     = [ K_IF; K_ASSIGN; K_SEMI; K_THEN; K_WORD; K_FI; K_EOF ]);
  check "reserved-word boundary: ifx stays WORD"
    (kinds "ifx" = [ K_WORD; K_EOF ]);
  check "two-char ops beat one-char"
    (kinds "a&&b||c;;d>>e>|f<&g" =
      [ K_WORD; K_ANDIF; K_WORD; K_ORIF; K_WORD; K_DSEMI; K_WORD; K_DGREAT
      ; K_WORD; K_CLOBBER; K_WORD; K_LESSAND; K_WORD; K_EOF ]);
  check "IO_NUMBER only before an I/O operator"
    (kinds "2> f 12x 3" =
      [ K_I_NUM; K_GREAT; K_WORD; K_WORD; K_WORD; K_EOF ]);
  check "DLESSDASH before DLESS" (kinds "<<-" = [ K_DLESSDASH; K_EOF ]);
  check "assignment split vs leading '='"
    (kinds "a=b =c" = [ K_ASSIGN; K_WORD; K_EOF ]);
  check "quotes hold words together"
    (values "echo \"a b\" c' d'e" = [ "echo"; "\"a b\""; "c' d'e"; "" ]);
  check "backslash escape inside word"
    (values "a\\;b" = [ "a\\;b"; "" ]);
  check "comments skipped" (kinds "a # c\nb" = [ K_WORD; K_NL; K_WORD; K_EOF ]);
  check "EOF sentinel"
    (match tokenize "" with [ { k = K_EOF } ] -> true | _ -> false);

  printf "\n-- E1: expansion & field splitting --\n";
  let (s, _, st) = run3 ~env:[ ("HOME", "/home/t") ] "echo $HOME > f" in
  check "env parameter" (s = 0 && file_of st "f" = "/home/t\n");
  let (_, _, st) = run3 "x=5; echo $x > f" in
  check "assignment then expansion" (var_of st "x" = "5" && file_of st "f" = "5\n");
  let (_, _, st) = run3 "x=ell; echo $x-o > f" in
  check "mid-word expansion" (file_of st "f" = "ell-o\n");
  let (_, _, st) = run3 "x=braced; echo ${x}z > f" in
  check "braced name" (file_of st "f" = "bracedz\n");
  let (_, _, st) = run3 "y=V; x=$y; echo $x > f" in
  check "eager assignment expansion" (file_of st "f" = "V\n");
  let (_, _, st) = run3 "x=$y; y=LATE; echo $x > f" in
  check "forward reference stays empty" (file_of st "f" = "\n");
  let (_, _, st) = run3 "echo $ > f" in
  check "bare $ literal" (file_of st "f" = "$\n");
  let (_, _, st) = run3 "echo $UNSET > f" in
  check "unset expands to nothing (word disappears)" (file_of st "f" = "\n");
  let (_, _, st) = run3 "echo \"$UNSET\" > f" in
  check "quoted empty expansion keeps empty field" (file_of st "f" = "\n");
  let (_, _, st) = run3 "v=\"a b c\"; for i in $v; do echo $i >> fs; done" in
  check "unquoted expansion undergoes field splitting"
    (file_of st "fs" = "a\nb\nc\n");
  let (_, _, st) = run3 "x=V; echo 'a $x' > q1" in
  check "single quotes disable expansion" (file_of st "q1" = "a $x\n");
  let (_, _, st) = run3 "x=V; echo \"a $x\" > q2" in
  check "double quotes expand, keep spacing" (file_of st "q2" = "a V\n");
  let (_, _, st) = run3 "echo a\\ b > q3" in
  check "escaped blank is one field" (file_of st "q3" = "a b\n");
  let (_, _, st) = run3 "false; echo $? > e4; true; echo $? > e5" in
  check "$? tracks last status"
    (file_of st "e4" = "1\n" && file_of st "e5" = "0\n");

  printf "\n-- S1: status algebra --\n";
  check "true 0 / false 1" (fst (run "true") = 0 && fst (run "false") = 1);
  check "unknown command 127" (fst (run "nosuch") = 127);
  check "empty command 0" (fst (run "> f") = 0);
  check "list status is last" (fst (run "true; false") = 1);
  check "; does not short-circuit"
    (snd (run "false; true") |> fun st -> contains (log_str st) "run true");
  check "exit propagates" (fst (run "exit 7") = 7);
  check "exit normalizes mod 256" (fst (run "exit 300") = 44);
  check "exit stops program"
    (contains (log_str (snd (run "exit 3; echo never"))) "run exit"
     && not (contains (log_str (snd (run "exit 3; echo never"))) "never"));

  printf "\n-- R1: redirections --\n";
  let (_, _, st) = run3 "echo a > f" in
  check "> truncates" (file_of st "f" = "a\n");
  let (_, _, st) = run3 "echo a > f; echo b >> f" in
  check ">> appends" (file_of st "f" = "a\nb\n");
  let (_, _, st) = run3 "echo a > f; echo b >| f" in
  check ">| clobbers" (file_of st "f" = "b\n");
  let (_, _, st) = run3 "echo x > f; cat < f > g" in
  check "< feeds stdin, > captures" (file_of st "g" = "x\n");
  (* POSIX 2.11: a redirection error gives a status >1 and aborts the command *)
  check "< missing file fails with status > 1" (fst (run "cat < nope") = 2);
  let (_, _, st) = run3 "cat < in.txt > out.txt" in
  check "both directions in one command"
    (* in.txt missing -> open fail; but with file seeded: *)
    (file_of st "out.txt" = "\000missing");
  let (_, _, st) = run3 ~files:[ ("in.txt", "sourced\n") ]
      "cat < in.txt > out.txt" in
  check "in+out redirect round-trip" (file_of st "out.txt" = "sourced\n");
  let (_, _, st) = run3 "echo a > f; > f" in
  check "null command truncates" (file_of st "f" = "");
  let (_, _, st) = run3 "echo hi 1> nf" in
  check "IO_NUMBER selects fd" (file_of st "nf" = "hi\n");
  let (_, _, st) = run3 "nosuch > o.txt 2> e.txt" in
  check "stderr separated into its file"
    (file_of st "o.txt" = ""
     && contains (file_of st "e.txt") "not found");
  let (s, out, st) = run3 "nosuch 2>&1 > o2" in
  check "2>&1 dups err into inherited stdout before > moves fd1"
    (s = 127 && contains out "not found" && file_of st "o2" = "");
  let (_, _, st) = run3 "nosuch 2>&1 | cat > d3" in
  check "duplicated stderr flows through pipeline"
    (contains (file_of st "d3") "not found");
  let (_, _, st) = run3 "echo rw <> rwf" in
  check "<> opens for writing" (file_of st "rwf" = "rw\n");

  printf "\n-- H1: here-documents --\n";
  let (_, _, st) = run3 "cat << EOF > hd\nhello world\nsecond line\nEOF" in
  check "here body verbatim" (file_of st "hd" = "hello world\nsecond line\n");
  let (_, _, st) = run3 "x=V; cat << EOF > hd4\nval=$x\nEOF" in
  check "unquoted delimiter expands body" (file_of st "hd4" = "val=V\n");
  let (_, _, st) = run3 "x=V; cat << \"END\" > hd3\n$x literal\nEND" in
  check "quoted delimiter keeps body literal"
    (file_of st "hd3" = "$x literal\n");
  let (_, _, st) = run3 "cat <<- EOH > hd2\n\ttabbed\n\tEOH" in
  check "<<- strips leading tabs" (file_of st "hd2" = "tabbed\n");
  expect_syntax "missing here delimiter" "cat << EOF\nnever ended" ;

  printf "\n-- P1: pipelines & bang --\n";
  let (s, _, st) = run3 "echo a > f; cat < f | wc > g" in
  check "pipeline data + last status" (s = 0 && file_of st "g" = "1\n");
  check "pipeline status is last stage" (fst (run "echo hi > f | false") = 1);
  check "bang inverts" (fst (run "! false") = 0 && fst (run "! true") = 1);
  (* POSIX 2.9.2: `!' is only an operator at the start of a pipeline, so a
     second `!' cannot start a command; double negation goes through a
     subshell (2.9.2 pipeline inversion applied twice). *)
  expect_syntax "second bang is not a nested operator" "! ! true";
  check "double negation via subshell"
    (fst (run "! (false)") = 0 && fst (run "! (true)") = 1);

  printf "\n-- A1: and_or laws --\n";
  check "&& keeps left status when false" (fst (run "false && true") = 1);
  check "&& skips RHS"
    (not (contains (log_str (snd (run "false && echo nope > f"))) "nope"));
  check "|| skips RHS when true"
    (not (contains (log_str (snd (run "true || echo nope"))) "nope"));
  check "|| runs RHS when false" (fst (run "false || true") = 0);
  check "left-assoc" (file_of (snd (run "true && false || echo z > f")) "f" = "z\n");

  printf "\n-- I1: if / elif / else --\n";
  let (_, _, st) = run3 "if true; then echo t > f; else echo e > g; fi" in
  check "then branch" (file_of st "f" = "t\n" && file_of st "g" = "\000missing");
  let (_, _, st) = run3 "if false; then echo t > f; else echo e > g; fi" in
  check "else branch" (file_of st "g" = "e\n");
  let (_, _, st) =
    run3 "if false; then echo a > f; elif false; then echo b > f; elif true; then echo c > f; fi"
  in
  check "elif fallthrough" (file_of st "f" = "c\n");
  check "no branch taken -> 0" (fst (run "if false; then true; fi") = 0);
  let (_, _, st) = run3 "if false; true; then echo t > f; fi" in
  check "condition list uses last status" (file_of st "f" = "t\n");
  let (_, _, st) = run3 "if true; then echo t; fi > ifout" in
  check "redirect on compound captures branch output"
    (file_of st "ifout" = "t\n");

  printf "\n-- W1: while / until --\n";
  let (s, _, st) = run3 "x=go; while test $x = go; do echo tick >> f; x=; done" in
  check "while iterates until cond fails" (s = 0 && file_of st "f" = "tick\n");
  check "while false skips body"
    (not (contains (log_str (snd (run "while false; do echo nope > f; done"))) "nope"));
  check "while no iterations -> 0" (fst (run "while false; do true; done") = 0);
  let (_, _, st) = run3 "x=1; while false; test $x = 1; do echo w >> wc1; x=; done" in
  check "condition list is while-style (last wins)"
    (file_of st "wc1" = "w\n");
  expect_fuel "while true bounded by fuel" "while true; do true; done";
  let (_, _, st) = run3 "x=go; until test $x = stop; do x=stop; done" in
  check "until loops while cond fails" (var_of st "x" = "stop");

  printf "\n-- F1: for --\n";
  let (_, _, st) = run3 "for i in a b c; do echo $i >> f; done" in
  check "for in wordlist" (file_of st "f" = "a\nb\nc\n" && var_of st "i" = "c");
  check "for without in-list runs zero times"
    (not (contains (log_str (snd (run "for i do echo nope > g; done"))) "nope"));
  let (s, _, _) = run3 "for i in a b; do false; done" in
  check "for status is last body status" (s = 1);

  printf "\n-- C1: case --\n";
  let (_, _, st) = run3 "case ab in a*) echo star > c1;; b|ab) echo alt > c2;; esac" in
  check "first match wins, glob *"
    (file_of st "c1" = "star\n" && file_of st "c2" = "\000missing");
  let (_, _, st) = run3 "case 7 in (7|8) echo low > c4;; *) echo hi > c5;; esac" in
  check "leading ( and | alternatives" (file_of st "c4" = "low\n" && file_of st "c5" = "\000missing");
  check "no match -> status 0, no body"
    (let (s, _, st) = run3 "case zz in a*) echo x > c3;; esac" in
     s = 0 && file_of st "c3" = "\000missing");
  (* a bracket expression matches exactly one character: 'b' is outside [x-z],
     so the negated class accepts it *)
  let (_, _, st) = run3 "case abc in a[!x-z]c) echo bang > c6;; *) echo no > c7;; esac" in
  check "negated class [!...] match" (file_of st "c6" = "bang\n");
  let (_, _, st) = run3 "case azz in a[x-z]c) echo in1 > c8;; a[x-z]z) echo in2 > c9;; esac" in
  check "class range matches, wrong length does not"
    (file_of st "c8" = "\000missing" && file_of st "c9" = "in2\n");

  printf "\n-- G1: brace groups & subshells --\n";
  let (_, _, st) = run3 "x=o; { x=i; echo $x > bg; }; echo $x > bg2" in
  check "brace group shares parameter space"
    (file_of st "bg" = "i\n" && file_of st "bg2" = "i\n");
  let (_, _, st) = run3 "{ echo b1; echo b2; } > bo" in
  check "group redirect captures all output" (file_of st "bo" = "b1\nb2\n");
  let (s, _, st) = run3 "x=o; (x=i; echo $x > sg); echo $x > sg2" in
  check "subshell isolates parameter space"
    (s = 0 && file_of st "sg" = "i\n" && file_of st "sg2" = "o\n" && var_of st "x" = "o");
  check "subshell writes are visible (shared files)"
    (file_of (snd (run "(echo inside > si)")) "si" = "inside\n");
  check "subshell status propagates" (fst (run "(false)") = 1);
  let (_, _, st) = run3 "(exit 5); echo b > f2" in
  check "exit terminates only its subshell" (file_of st "f2" = "b\n");
  check "exit 5 subshell overall status"
    (let (s, _, _) = run3 "(exit 5)" in s = 5);
  let (_, _, st) = run3 "f() { (exit 3); echo after > fa; }; f; echo z > fz" in
  (* the subshell's exit ends only the subshell; both the function body and the
     outer shell keep running, and the function status is the last command's *)
  check "exit inside function subshell continues shell"
    (file_of st "fa" = "after\n" && file_of st "fz" = "z\n");

  printf "\n-- D1: functions & positional parameters --\n";
  let (s, _, st) = run3 "f() { echo hi >> logf; x=in_f; }; f" in
  check "definition + call, status propagates"
    (s = 0 && file_of st "logf" = "hi\n" && var_of st "x" = "in_f");
  check "definition alone runs nothing"
    (not (contains (log_str (snd (run "f() { echo hi >> logf; }"))) "run echo"));
  check "nested calls"
    (file_of (snd (run "f() { echo a >> l; }; g() { f; }; f; g")) "l" = "a\na\n");
  let (_, _, st) = run3 "f() { echo $1-$2 > a2; }; f p1 q2; " in
  check "$1 $2 positional in function" (file_of st "a2" = "p1-q2\n");
  let (_, _, st) = run3 "f() { echo $# > a1; }; f p1 p2 p3" in
  check "$# counts positional params" (file_of st "a1" = "3\n");
  let (_, _, st) = run3 "f() { echo \"$@\" > a3; echo \"$*\" > a4; }; f p1 \"q 2\"" in
  check "\"$@\" keeps fields separate, \"$*\" joins"
    (file_of st "a3" = "p1 q 2\n" && file_of st "a4" = "p1 q 2\n");
  let (_, _, st) = run3 "f() { echo $1 > r1; }; f A; g() { echo $# > r2; }; g" in
  check "positional params restored after call" (file_of st "r1" = "A\n" && file_of st "r2" = "0\n");
  expect_fuel "recursive function bounded" "r() { echo x >> f; r; }; r";

  printf "\n-- X1: syntax discipline --\n";
  expect_syntax "if without fi" "if true; then echo a";
  expect_syntax "missing stage after pipe" "echo a |";
  expect_syntax "empty and_or operand" "a && | b";
  expect_syntax "function body must be compound" "f() echo hi";
  expect_syntax "while needs do" "while true; echo";
  expect_syntax "case needs esac" "case a in b) echo";

  printf "\n-- N1: invariants & determinism --\n";
  let programs =
    [ "echo hello > f; echo world >> f; cat < f | wc > g"
    ; "x=1; y=$x; for i in a b; do echo $y >> out; done; if true; then exit 5; fi"
    ; "f() { echo hi >> h; }; f; ! f || echo alt > k"
    ; "case $x in *) v=matched;; esac; { a=1; b=2; }; (c=3)" ]
  in
  List.iteri
    (fun i src ->
      let (s1, o1, st1) = run3 src in
      let (s2, o2, st2) = run3 src in
      check
        ("determinism #" ^ string_of_int (i + 1))
        (s1 = s2 && o1 = o2 && snapshot st1 = snapshot st2))
    programs;
  check "status range invariant" (inv_status_range (fst (run "true")));
  check "assignment round-trip invariant"
    (inv_assignment_roundtrip (snd (run "q=1; r=$q; w=$UNSET; s='lit$er'"))) ;
  check "last assignment wins"
    (let (_, _, st) = run3 "x=a; x=b; echo $x > f" in
     var_of st "x" = "b" && file_of st "f" = "b\n");

  printf "\n";
  if !fails = 0 then
    printf "All %d shell model checks and invariants passed successfully!\n"
      !checks
  else begin
    printf "%d of %d shell model checks FAILED\n" !fails !checks;
    exit 1
  end
