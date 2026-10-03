open Ast
open Unix
open Stdlib
module K = Sh_run

(* ush — the executable shell.  Its CONTROL FLOW and WORD EXPANSION are no
   longer hand-written here: they are the extracted kernel `Sh_run.run` /
   `Sh_run.expand`, generated from the verified model sh_concrete.v (the single
   source of truth).  This file supplies only the two things the pure kernel
   deliberately omits:
     (1) a lowering bridge  Ast.exp -> Sh_run.cmd  (the parser's rich AST mapped
         onto the kernel's eleven constructors; anything the kernel models —
         ;, &&, ||, !, if/elif, while, until, for, case, assignment — becomes a
         kernel node so run interprets it), and
     (2) the effect seam  phi : Sh_run.run_phi  that run invokes at each command
         leaf (Ext idx argv).  phi performs the real OS effects (fork/execvp,
         pipes, redirections, cd/exit/:) and reads/writes the shell status; the
         opaque idx keys a host-side plan carrying the argv, redirects and nested
         command structure the pure semantics does not model.
   The engine's control-flow rules, verified in the Rocq kernel, are:
     ;     runs both, list status = last;  && runs right iff left status = 0;
     ||    runs right iff left status <> 0;  ! inverts 0<>non-0;
     if/while/until branch purely on the condition status. *)

(* ── boundary conversions: OCaml <-> the extracted Peano/text representation ── *)

let rec nat_of_int n = if n <= 0 then K.O else K.S (nat_of_int (n - 1))
let rec int_of_nat = function K.O -> 0 | K.S k -> 1 + int_of_nat k

let text_of_string s =
  List.init (String.length s) (fun i -> nat_of_int (Char.code s.[i]))

let rec string_of_text = function
  | [] -> ""
  | b :: r -> String.make 1 (Char.chr (int_of_nat b)) ^ string_of_text r

(* The kernel's expander is fuel-bounded; this budget is far above any real
   command's word/nesting depth, so run never truncates mid-program. *)
let fuel = nat_of_int 4096

(* strip one layer of surrounding matching quotes (the lexer already unquotes
   most words; assignment values keep theirs).  Idempotent on unquoted text. *)
let unquote (s : string) : string =
  let n = String.length s in
  if n >= 2 && ((s.[0] = '"' && s.[n - 1] = '"') || (s.[0] = '\'' && s.[n - 1] = '\''))
  then String.sub s 1 (n - 2) else s

(* Expand one already-unquoted kernel word against the live shell state using the
   single extracted expander.  This is the ONLY place command words get expanded,
   and it is the verified Sh_run.expand — no duplicate string expander survives. *)
let expand_word (st : K.cstate) (t : K.text) : string =
  string_of_text (K.expand fuel st.K.cenv st.K.cstatus t)

let status_of = function
  | WEXITED n | WSTOPPED n -> n
  | WSIGNALED s -> 128 + s

(* ── the effect seam's host data ─────────────────────────────────── *)

(* argv of a pipeline stage (unquoted words) + its redirects, or a nested command
   to be run through the kernel in the stage's pipe-connected child. *)
type stage =
  | St_exec of K.text list * Ast.exp list
  | St_cmd of K.cmd

type plan =
  | P_simple of Ast.exp list                       (* redirects for a simple command; argv comes from phi *)
  | P_pipeline of bool * stage list                (* bang, stages *)
  | P_subshell of K.cmd                            (* ( commands ) -> fork a child, run there *)
  | P_compound of K.cmd * Ast.exp list             (* compound_command with redirections *)
  | P_funcdef of string * K.cmd

let plan_tbl : (int, plan) Hashtbl.t = Hashtbl.create 64
let idx_ctr = ref 0
let new_idx () = let i = !idx_ctr in incr idx_ctr; i

let funcs : (string * K.cmd) list ref = ref []
let find_func c = try Some (List.assoc c !funcs) with Not_found -> None

(* Shell variables, the loop counter for `$?`, etc. live entirely in the kernel's
   cstate (cenv/cstatus); the host no longer keeps a parallel variable table. *)

let apply_redirect (st : K.cstate) = function
  | IoFile (_, op, file) ->
      let f = expand_word st (text_of_string (unquote file)) in
      (match op with
       | Less -> let fd = openfile f [O_RDONLY] 0o644 in dup2 fd Unix.stdin; close fd
       | Great -> let fd = openfile f [O_WRONLY; O_CREAT; O_TRUNC] 0o666 in dup2 fd Unix.stdout; close fd
       | DGreat -> let fd = openfile f [O_WRONLY; O_CREAT; O_APPEND] 0o666 in dup2 fd Unix.stdout; close fd
       | LessGreat -> let fd = openfile f [O_RDWR; O_CREAT] 0o666 in dup2 fd Unix.stdin; dup2 fd Unix.stdout; close fd
       | _ -> ())
  | _ -> ()

(* A handful of builtins run in the current shell so their effects (cwd, exit
   status) take hold; everything else is fork+execvp'd. *)
let lookup_builtin c args =
  match c with
  | ":" | "true" -> Some 0
  | "false" -> Some 1
  | "exit" -> Some (match args with [x] -> (try int_of_string x with _ -> 0) | _ -> 0)
  | "cd" ->
      let dir = match args with [x] -> x | _ -> (try Sys.getenv "HOME" with _ -> "/") in
      (try Sys.chdir dir; Some 0 with _ -> prerr_string "cd: failed\n"; Some 1)
  | _ -> None

let ret_status st code = Some { st with K.cstatus = nat_of_int (code land 255) }

(* fork+exec one simple external command with the given redirects, return its
   wait status.  Runs entirely host-side; the kernel never models file descriptors. *)
let run_external (st : K.cstate) (c : string) (rest : string list) (redirs : Ast.exp list) : int =
  let pid = fork () in
  if pid = 0 then begin
    (try
       List.iter (apply_redirect st) redirs;
       execvp c (Array.of_list (c :: rest))
     with Unix_error (ENOENT, _, _) ->
       prerr_string "ush: command not found: "; prerr_string c; prerr_newline (); exit 127);
    exit 127
  end
  else status_of (snd (waitpid [] pid))

(* ── (2) the effect seam phi: run's single callback into the OS ───── *)

let rec phi : K.run_phi = fun idx argv st ->
  let i = int_of_nat idx in
  match Hashtbl.find plan_tbl i with
  | P_simple redirs ->
      let ws = List.map (expand_word st) argv in
      (match ws with
       | [] -> ret_status st 0
       | c :: rest ->
           match lookup_builtin c rest with
           | Some code -> ret_status st code
           | None ->
               (match find_func c with
                | Some body ->
                    (match K.run phi fuel body st with Some s2 -> Some s2 | None -> Some st)
                | None -> ret_status st (run_external st c rest redirs)))
  | P_pipeline (bang, stages) ->
      let n = List.length stages in
      let raw =
        if n = 0 then 0
        else begin
          let sv = Array.of_list stages in
          let pfd = Array.make (max 0 (n - 1)) (Unix.stdin, Unix.stdin) in
          for k = 0 to n - 2 do pfd.(k) <- pipe () done;
          let pids = Array.make n 0 in
          Array.iteri
            (fun k stage ->
              let pid = fork () in
              if pid = 0 then begin
                if k > 0 then dup2 (fst pfd.(k - 1)) Unix.stdin;
                if k < n - 1 then dup2 (snd pfd.(k)) Unix.stdout;
                for j = 0 to n - 2 do close (fst pfd.(j)); close (snd pfd.(j)) done;
                (match stage with
                 | St_exec (argv, redirs) ->
                     (match List.map (expand_word st) argv with
                      | [] -> exit 0
                      | c :: rest ->
                          List.iter (apply_redirect st) redirs;
                          (try execvp c (Array.of_list (c :: rest))
                           with Unix_error (ENOENT, _, _) -> exit 127))
                 | St_cmd cmd ->
                     (match K.run phi fuel cmd st with
                      | Some s2 -> exit (int_of_nat s2.K.cstatus)
                      | None -> exit 0));
                exit 127
              end
              else pids.(k) <- pid)
            sv;
          for j = 0 to n - 2 do close (fst pfd.(j)); close (snd pfd.(j)) done;
          let stt = ref 0 in
          for k = 0 to n - 1 do
            let (_, s) = waitpid [] pids.(k) in stt := status_of s
          done;
          !stt
        end
      in
      let code = if bang then (if raw = 0 then 1 else 0) else raw in
      ret_status st code
  | P_subshell cmd -> ret_status st (run_external_subshell st [] cmd)
  | P_compound (cmd, redirs) ->
      let pid = fork () in
      if pid = 0 then begin
        List.iter (apply_redirect st) redirs;
        (match K.run phi fuel cmd st with
         | Some s2 -> exit (int_of_nat s2.K.cstatus)
         | None -> exit 0);
        exit 0
      end
      else ret_status st (status_of (snd (waitpid [] pid)))
  | P_funcdef (name, body) ->
      funcs := (name, body) :: !funcs;
      ret_status st 0

(* fork a child that runs a nested kernel command; the child's stdout is the
   parent's (subshells don't redirect), its variable edits are discarded. *)
and run_external_subshell (st : K.cstate) (_ : Ast.exp list) (cmd : K.cmd) : int =
  let pid = fork () in
  if pid = 0 then begin
    (match K.run phi fuel cmd st with
     | Some s2 -> exit (int_of_nat s2.K.cstatus)
     | None -> exit 0);
    exit 0
  end
  else status_of (snd (waitpid [] pid))

(* ── (1) the lowering bridge  Ast.exp -> Sh_run.cmd ──────────────── *)

let kv s = match String.index_opt s '=' with
  | Some i -> (String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1))
  | None -> (s, "")

let leaf plan argv =
  let i = new_idx () in Hashtbl.replace plan_tbl i plan; K.Ext (nat_of_int i, argv)

(* A command list -> a right-nested `Seq` chain: the status is the last one's,
   matching the kernel's sequential-;; reading. *)
let rec lower_list (cmds : Ast.exp list) : K.cmd =
  match cmds with
  | [] -> K.Skip
  | [ c ] -> lower c
  | c :: r -> K.Seq (lower c, lower_list r)

(* kernel For/Case bodies are already command LISTS (run_seq handles empty -> 0). *)
and lower_body cmds = List.map lower cmds

and lower (e : Ast.exp) : K.cmd =
  match e with
  | Program items -> lower_list items
  | ListItem (a, _) -> lower a
  | AndOr a -> lower a
  | List (a, _sep, b) -> K.Seq (lower a, lower b)
  | AndIf (a, b) -> K.And (lower a, lower b)
  | OrIf (a, b) -> K.Or (lower a, lower b)
  | BraceGroup cmds -> lower_list cmds
  | IfClause (cond, th, elifs, els) -> lower_if cond th elifs els
  | WhileClause (cond, body) -> K.While (lower_list cond, lower_list body)
  | UntilClause (cond, body) -> K.While (K.Bang (lower_list cond), lower_list body)
  | ForClause (var, ws, body) ->
      K.For (text_of_string (unquote var),
             List.map (fun w -> text_of_string (unquote w)) (match ws with Some l -> l | None -> []),
             lower_body body)
  | CaseClause (w, cases) ->
      K.Case (text_of_string (unquote w),
              List.map (fun (pats, body) ->
                  (List.map (fun p -> text_of_string (unquote p)) pats, lower_body body)) cases)
  | Simple _ -> lower_simple e
  | Subshell cmds -> leaf (P_subshell (lower_list cmds)) []
  (* A one-stage, un-negated pipeline is just its command: run it inline so its
     effects (assignments, cd, function definitions) persist in the shell.  A
     real multi-stage pipeline must fork each stage, which discards such edits —
     matching POSIX, where the last stage of `x=1 | cmd` also cannot persist. *)
  | Pipeline (false, [ single ]) -> lower single
  | Pipeline (bang, stages) -> leaf (P_pipeline (bang, List.map stage_of stages)) []
  | Compound (cc, redirs) ->
      if redirs = [] then lower cc else leaf (P_compound (lower cc, redirs)) []
  | FunctionDef (name, body) -> leaf (P_funcdef (name, lower body)) [ text_of_string name ]
  | Word _ | IoFile _ | IoHere _ | Assignment _ -> K.Skip

and lower_if cond th elifs els =
  let rec probe = function
    | [] -> (match els with Some e -> lower_list e | None -> K.Skip)
    | (c, t) :: rest -> K.If (lower_list c, lower_list t, probe rest)
  in
  K.If (lower_list cond, lower_list th, probe elifs)

and lower_simple (e : Ast.exp) : K.cmd =
  let (assigns, redirs, cmd_opt) =
    match e with
    | Simple (Some (c, args), items) -> (prefix_assigns items, redirects items, Some (c, args))
    | Simple (None, items) -> (prefix_assigns items, redirects items, None)
    | _ -> ([], [], None)
  in
  let argv =
    match cmd_opt with
    | Some (c, args) -> text_of_string (unquote c) :: List.map (fun a -> text_of_string (unquote a)) args
    | None -> []
  in
  let node = leaf (P_simple redirs) argv in
  (* assignment prefixes persist to the shell, then the command runs *)
  List.fold_left (fun acc (k, v) ->
      K.Seq (K.Assign (text_of_string (unquote k), text_of_string (unquote v)), acc))
    node (List.rev assigns)

and prefix_assigns items =
  List.filter_map (fun it -> match it with Assignment s -> Some (kv s) | _ -> None) items

and redirects items =
  List.filter_map (fun it -> match it with (IoFile _ as r) -> Some r | _ -> None) items

and stage_of (e : Ast.exp) : stage =
  match e with
  | Simple (Some (c, args), items) ->
      St_exec (text_of_string (unquote c) :: List.map (fun a -> text_of_string (unquote a)) args,
               redirects items)
  | _ -> St_cmd (lower e)

(* ── driver ──────────────────────────────────────────────────────── *)

let last_status = ref 0

let execute_exp (e : Ast.exp) : int =
  match K.run phi fuel (lower e) { K.cstatus = K.O; K.cenv = [] } with
  | Some st -> int_of_nat st.K.cstatus
  | None -> 1

let parse_line input =
  let lexbuf = Lexing.from_string (input ^ "\n") in
  try Some (Parser.main Lexer.token lexbuf) with
  | Lexer.Error msg -> Printf.eprintf "ush: lexer error: %s\n" msg; None
  | Parser.Error ->
      Printf.eprintf "ush: syntax error near offset %d\n" (Lexing.lexeme_start lexbuf); None

let read_file filename =
  let ic = open_in_gen [Open_rdonly; Open_text] 0 filename in
  let buf = Buffer.create 4096 in
  (try while true do Buffer.add_channel buf ic 1 done with End_of_file -> ());
  close_in ic;
  Buffer.contents buf

let run_source filename =
  ignore (Option.map execute_exp (parse_line (read_file filename)))

let repl () =
  print_endline "ush - POSIX shell prototype (Ctrl-D to exit)";
  try
    while true do
      print_string "$ "; flush stdout;
      let line = read_line () in
      match parse_line line with
      | Some ast -> last_status := execute_exp ast
      | None -> ()
    done
  with End_of_file -> print_newline ()

let parse_only filename =
  match parse_line (read_file filename) with
  | Some ast -> print_string (Ast.string_of_exp ast); print_newline (); print_endline "[PARSE OK]"
  | None -> print_endline "[PARSE FAIL]"; exit 1

let () =
  match Array.to_list Sys.argv with
  | [ _; "-p"; file ] -> parse_only file
  | [ _; file ] -> run_source file
  | _ -> repl ()
