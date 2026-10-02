open Ast
open Unix
open Stdlib

(* Reference interpreter.  Its control-flow rules mirror the verified model in
   verify/models (sh_model.ml and sh_properties.v):
     ;     runs both commands, the list status is the last command's status
     &&    runs the right command only when the left status is zero
     ||    runs the right command only when the left status is non-zero
     !     inverts a zero/non-zero status
   if/while/until branch purely on the status of their condition list. *)

let vars : (string * string) list ref = ref []
let funcs : (string * exp) list ref = ref []
let last_status = ref 0

let setvar k v = vars := (k, v) :: List.remove_assoc k !vars
let getvar k = try Some (List.assoc k !vars) with Not_found -> None

(* expand $name, ${name} and $? ; strip one layer of surrounding quotes *)
let expand (s : string) : string =
  let s =
    let n = String.length s in
    if n >= 2 && ((s.[0] = '"' && s.[n - 1] = '"') || (s.[0] = '\'' && s.[n - 1] = '\''))
    then String.sub s 1 (n - 2) else s
  in
  let is_name_char c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_'
  in
  let buf = Buffer.create (String.length s + 8) in
  let i = ref 0 and n = String.length s in
  while !i < n do
    let c = String.unsafe_get s !i in
    if c <> '$' then (Buffer.add_char buf c; incr i)
    else begin
      incr i;                                   (* consume '$' *)
      let consumed, value =
        if !i < n && String.unsafe_get s !i = '{' then begin
          incr i;
          let name = Buffer.create 8 in
          while !i < n && String.unsafe_get s !i <> '}' do
            Buffer.add_char name (String.unsafe_get s !i); incr i
          done;
          if !i < n then incr i;                (* consume '}' *)
          (true, getvar (Buffer.contents name))
        end
        else if !i < n && is_name_char (String.unsafe_get s !i) then begin
          let name = Buffer.create 8 in
          while !i < n && is_name_char (String.unsafe_get s !i) do
            Buffer.add_char name (String.unsafe_get s !i); incr i
          done;
          (true, getvar (Buffer.contents name))
        end
        else if !i < n && String.unsafe_get s !i = '?' then begin
          incr i; (true, Some (string_of_int !last_status))
        end
        else (false, None)
      in
      (* A $name / ${name} / $? reference always expands (unset => empty,
         matching the model's lookup_param); a lone '$' that is not a valid
         parameter reference is left literal. *)
      match consumed, value with
      | true, Some v -> Buffer.add_string buf v
      | true, None -> ()
      | false, _ -> Buffer.add_char buf '$'
    end
  done;
  Buffer.contents buf

let expand_all ws = List.map expand ws

let status_of = function
  | WEXITED n | WSTOPPED n -> n
  | WSIGNALED s -> 128 + s

(* case pattern match: exact text, with '*' and '?' globbing *)
let rec glob pat str =
  let lp = String.length pat and ls = String.length str in
  if lp = 0 then ls = 0
  else match pat.[0] with
    | '*' ->
        let rest = String.sub pat 1 (lp - 1) in
        let rec go i = i > ls || (glob rest (String.sub str i (ls - i)) || go (i + 1)) in
        go 0
    | '?' -> ls > 0 && glob (String.sub pat 1 (lp - 1)) (String.sub str 1 (ls - 1))
    | c -> ls > 0 && c = str.[0] && glob (String.sub pat 1 (lp - 1)) (String.sub str 1 (ls - 1))

let apply_redirect = function
  | IoFile (_, op, file) ->
      let f = expand file in
      (match op with
       | Less -> let fd = openfile f [O_RDONLY] 0o644 in dup2 fd Unix.stdin; close fd
       | Great -> let fd = openfile f [O_WRONLY; O_CREAT; O_TRUNC] 0o666 in dup2 fd Unix.stdout; close fd
       | DGreat -> let fd = openfile f [O_WRONLY; O_CREAT; O_APPEND] 0o666 in dup2 fd Unix.stdout; close fd
       | LessGreat -> let fd = openfile f [O_RDWR; O_CREAT] 0o666 in dup2 fd Unix.stdin; dup2 fd Unix.stdout; close fd
       | _ -> ())
  | _ -> ()

(* run a block, returning the status of its last command (0 when empty) *)
let rec execute_exp e = let s = execute_exp_node e in last_status := s; s

and run_seq (cmds : exp list) : int =
  List.fold_left (fun _ c -> execute_exp c) 0 cmds

and execute_exp_node : exp -> int = function
  | List (a, sep, b) ->
      (* ';' runs both, status = right; '&' is sequential here, like the model *)
      ignore sep; ignore (execute_exp a); execute_exp b
  | AndIf (a, b) -> let s = execute_exp a in if s = 0 then execute_exp b else s
  | OrIf (a, b) -> let s = execute_exp a in if s = 0 then s else execute_exp b
  | Pipeline (bang, cmds) ->
      let s = run_pipeline cmds in
      if bang then (if s = 0 then 1 else 0) else s
  | Compound (cc, redirs) ->
      if redirs = [] then execute_exp cc
      else begin
        let pid = fork () in
        if pid = 0 then begin
          List.iter apply_redirect redirs;
          exit (execute_exp cc)
        end
        else status_of (snd (waitpid [] pid))
      end
  | Simple _ as c -> execute_command c
  | FunctionDef (name, body) -> funcs := (name, body) :: !funcs; 0
  | BraceGroup cmds -> run_seq cmds
  | Subshell cmds ->
      let pid = fork () in
      if pid = 0 then exit (run_seq cmds) else status_of (snd (waitpid [] pid))
  | ForClause (var, words, body) ->
      let ws = match words with Some l -> l | None -> [] in
      List.fold_left (fun _ w -> setvar var (expand w); run_seq body) 0 ws
  | CaseClause (w, cases) ->
      let target = expand w in
      (match List.find_map
               (fun (pats, body) ->
                 if List.exists (fun p -> glob (expand p) target) pats then Some (run_seq body)
                 else None)
               cases
       with Some s -> s | None -> 0)
  | IfClause (cond, then_part, elifs, else_part) ->
      if run_seq cond = 0 then run_seq then_part
      else begin
        let rec probe = function
          | [] -> (match else_part with Some e -> run_seq e | None -> 0)
          | (c, t) :: rest -> if run_seq c = 0 then run_seq t else probe rest
        in probe elifs
      end
  | WhileClause (cond, body) ->
      let s = ref 0 in
      while run_seq cond = 0 do s := run_seq body done; !s
  | UntilClause (cond, body) ->
      let s = ref 0 in
      while run_seq cond <> 0 do s := run_seq body done; !s
  | ListItem (e, _) -> execute_exp e
  | Program items -> run_seq items
  | AndOr e -> execute_exp e
  | _ -> 1

and run_pipeline cmds =
  let n = List.length cmds in
  if n <= 1 then
    (match cmds with [c] -> execute_command c | _ -> 0)
  else begin
    let pfd = Array.make (n - 1) (Unix.stdin, Unix.stdin) in
    for i = 0 to n - 2 do pfd.(i) <- pipe () done;
    let pids = Array.make n 0 in
    List.iteri
      (fun i cmd ->
        let pid = fork () in
        if pid = 0 then begin
          if i > 0 then dup2 (fst pfd.(i - 1)) Unix.stdin;
          if i < n - 1 then dup2 (snd pfd.(i)) Unix.stdout;
          for j = 0 to n - 2 do close (fst pfd.(j)); close (snd pfd.(j)) done;
          exit (execute_command cmd)
        end
        else pids.(i) <- pid)
      cmds;
    for j = 0 to n - 2 do close (fst pfd.(j)); close (snd pfd.(j)) done;
    let st = ref 0 in
    for i = 0 to n - 1 do
      let (_, s) = waitpid [] pids.(i) in st := status_of s
    done;
    !st
  end

and execute_command = function
  | Simple (Some (cmd, args), items) ->
      (* assignment prefixes update the shell variables (model semantics) *)
      List.iter
        (fun it -> match it with Assignment s -> bind_assignment s | _ -> ())
        items;
      let c = expand cmd in
      let rest = expand_all args in
      (match lookup_builtin c rest with
       | Some code -> code
       | None ->
           match List.find_opt (fun (n, _) -> n = c) !funcs with
           | Some (_, body) -> execute_exp body
           | None ->
               let pid = fork () in
               if pid = 0 then begin
                 List.iter
                   (fun it -> match it with IoFile _ -> apply_redirect it | _ -> ())
                   items;
                 try execvp c (Array.of_list (c :: rest))
                 with Unix_error (ENOENT, _, _) ->
                   prerr_string "ush: command not found: "; prerr_string c;
                   prerr_newline (); exit 127
               end
               else status_of (snd (waitpid [] pid)))
  | Simple (None, items) ->
      List.iter
        (fun it -> match it with
          | Assignment s -> bind_assignment s
          | IoFile _ -> apply_redirect it
          | _ -> ())
        items;
      0
  | e -> execute_exp e

and bind_assignment s =
  match String.index_opt s '=' with
  | Some i ->
      let k = String.sub s 0 i in
      let v = String.sub s (i + 1) (String.length s - i - 1) in
      setvar k (expand v)
  | None -> ()

(* a few builtins run in the current shell so their effects persist *)
and lookup_builtin c args =
  match c with
  | ":" | "true" -> Some 0
  | "false" -> Some 1
  | "exit" -> Some (match args with [x] -> (try int_of_string x with _ -> 0) | _ -> 0)
  | "cd" ->
      let dir = match args with [x] -> x | _ -> (try Sys.getenv "HOME" with _ -> "/") in
      (try Sys.chdir dir; Some 0 with _ -> prerr_string "cd: failed\n"; Some 1)
  | _ -> None

(* ── driver ──────────────────────────────────────────────────────── *)

let parse_line input =
  let lexbuf = Lexing.from_string (input ^ "\n") in
  try Some (Parser.main Lexer.token lexbuf) with
  | Lexer.Error msg -> Printf.eprintf "ush: lexer error: %s\n" msg; None
  | Parser.Error ->
      Printf.eprintf "ush: syntax error near offset %d\n" (Lexing.lexeme_start lexbuf); None

let run_source filename =
  let ic = open_in_gen [Open_rdonly; Open_text] 0 filename in
  let buf = Buffer.create 4096 in
  (try while true do Buffer.add_channel buf ic 1 done with End_of_file -> ());
  close_in ic;
  ignore (Option.map execute_exp (parse_line (Buffer.contents buf)))

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
  let ic = open_in_gen [Open_rdonly; Open_text] 0 filename in
  let buf = Buffer.create 4096 in
  (try while true do Buffer.add_channel buf ic 1 done with End_of_file -> ());
  close_in ic;
  match parse_line (Buffer.contents buf) with
  | Some ast -> print_string (Ast.string_of_exp ast); print_newline (); print_endline "[PARSE OK]"
  | None -> print_endline "[PARSE FAIL]"; exit 1

let () =
  match Array.to_list Sys.argv with
  | [ _; "-p"; file ] -> parse_only file
  | [ _; file ] -> run_source file
  | _ -> repl ()
