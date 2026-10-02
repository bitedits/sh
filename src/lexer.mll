{
  open Parser
  open Lexing

  (* Command-position bookkeeping.  We normalise the token stream so the LALR
     grammar can ignore line breaks entirely: a newline behaves as a `;`
     statement separator *unless* it sits in a line-continuation context (right
     after `then`, `do`, an operator, an open bracket, or another separator),
     where POSIX forbids it from terminating a list.  [prev] remembers the last
     significant token to make that call. *)
  let continues_after = function
    | THEN | ELSE | DO | IN | LBRACE | LPAREN | BANG
    | AND_IF | OR_IF | PIPE | DSEMI | SEMI | AMP
    | LESS | GREAT | DLESS | DGREAT | LESSAND | GREATAND | LESSGREAT
    | DLESSDASH | CLOBBER -> true
    | _ -> false

  (* A word is treated as a reserved word only where a fresh command may begin.
     `in` is excluded here: POSIX reserves it solely after a `for`/`case`
     target, which is tracked separately via [expect_in]. *)
  let command_position = function
    | SEMI | AND_IF | OR_IF | PIPE | AMP | BANG
    | LPAREN | LBRACE | RBRACE
    | IF | WHILE | UNTIL | FOR | CASE
    | THEN | ELSE | DO | DSEMI -> true
    | _ -> false

  let reserved_tok = function
    | "if"    -> Some IF
    | "then"  -> Some THEN
    | "else"  -> Some ELSE
    | "elif"  -> Some ELIF
    | "fi"    -> Some FI
    | "do"    -> Some DO
    | "done"  -> Some DONE
    | "case"  -> Some CASE
    | "esac"  -> Some ESAC
    | "while" -> Some WHILE
    | "until" -> Some UNTIL
    | "for"   -> Some FOR
    | "in"    -> Some IN
    | _       -> None

  let prev = ref SEMI            (* leading newlines are dropped *)
  let set_prev t = prev := t

  (* [armed] is set after FOR/CASE: the next word is the loop/case target.
     [expect_in] is set after that target: the next `in` is the reserved one. *)
  let armed = ref false
  let expect_in = ref false

  let peek_char lexbuf =
    let p = lexbuf.lex_curr_pos in
    let b = lexbuf.lex_buffer in
    if p < Bytes.length b then Bytes.get b p else '\000'

  let valid_name s =
    let n = String.length s in
    n > 0
    && (let c = String.unsafe_get s 0 in
        (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_')
    && (let ok = ref true in
        for i = 0 to n - 1 do
          let c = String.unsafe_get s i in
          if not ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
                  || (c >= '0' && c <= '9') || c = '_' || c = '/')
          then ok := false
        done; !ok)

  (* a[=...] is an assignment word when the text before the first '=' is a name *)
  let is_assignment s =
    match String.index_opt s '=' with
    | Some 0 -> false
    | Some i -> valid_name (String.sub s 0 i)
    | None -> false

  (* an ordinary word: function-name if it is a name immediately followed by '(' *)
  let word_like lexbuf w =
    let tok =
      if valid_name w && peek_char lexbuf = '(' then NAME w else WORD w
    in
    if !armed then begin armed := false; expect_in := true end
    else expect_in := false;
    set_prev tok; tok

  exception Error of string
}

let nl = '\r' '\n' | '\n' | '\r'

rule token = parse
  | [' ' '\t' '\r']+          { token lexbuf }
  | '#' [^ '\n' '\r']*        { token lexbuf }                 (* comment to EOL *)
  | nl                          {
      if continues_after !prev then token lexbuf                (* keep the line open *)
      else begin prev := SEMI; SEMI end
    }
  | "&&"                      { set_prev AND_IF;  AND_IF }
  | "||"                      { set_prev OR_IF;   OR_IF }
  | "<<-"                     { set_prev DLESSDASH;DLESSDASH }
  | "<<"                      { set_prev DLESS;   DLESS }
  | ">>"                      { set_prev DGREAT;  DGREAT }
  | "<&"                      { set_prev LESSAND; LESSAND }
  | ">&"                      { set_prev GREATAND;GREATAND }
  | "<>"                      { set_prev LESSGREAT;LESSGREAT }
  | ">|"                      { set_prev CLOBBER; CLOBBER }
  | ";;"                      { set_prev DSEMI;   DSEMI }
  | "<"                       { set_prev LESS;    LESS }
  | ">"                       { set_prev GREAT;   GREAT }
  | "|"                       { set_prev PIPE;    PIPE }
  | "&"                       { set_prev AMP;     AMP }
  | ";"                       { set_prev SEMI;    SEMI }
  | "!"                       { set_prev BANG;    BANG }
  | "("                       { set_prev LPAREN;  LPAREN }
  | ")"                       { set_prev RPAREN;  RPAREN }
  | "{"                       { set_prev LBRACE;  LBRACE }
  | "}"                       { set_prev RBRACE;  RBRACE }
  (* A whole quoted field is one word, spaces included (the quotes are removed
     so the interpreter expands any $refs inside a double-quoted string).
     Escapes, adjacent quote-concatenation and quoted assignment values remain
     out of scope. *)
  | '"' ([^ '\n' '"']* as inner) '"'   { word_like lexbuf inner }
  | '\'' ([^ '\n' '\'']* as inner) '\'' { word_like lexbuf inner }
  | ['0'-'9']+ as n           {
      (* Digits are an IO_NUMBER only when they immediately precede a
         redirection operator; otherwise they are an ordinary WORD. *)
      match peek_char lexbuf with
      | '<' | '>' -> armed := false; expect_in := false;
                     set_prev (IO_NUMBER (int_of_string n)); IO_NUMBER (int_of_string n)
      | _         -> word_like lexbuf n
    }
  | [^ ' ' '\t' '\n' '\r' ';' '&' '|' '<' '>' '(' ')' '{' '}' '=' ]+ '='
    [^ ' ' '\t' '\n' '\r' ';' '&' '|' '<' '>' '(' ')' '{' '}' ]* as a {
      (* name=value (assignment prefix); '=' delimits, so capture both sides *)
      armed := false; expect_in := false;
      set_prev (ASSIGNMENT_WORD a); ASSIGNMENT_WORD a
    }
  | [^ ' ' '\t' '\n' '\r' ';' '&' '|' '<' '>' '(' ')' '{' '}' ]+ as w {
      if is_assignment w
      then (armed := false; expect_in := false;
            set_prev (ASSIGNMENT_WORD w); ASSIGNMENT_WORD w)
      else match reserved_tok w with
        | Some t ->
            let cmd_pos = command_position !prev && t <> IN in
            let for_in  = t = IN && !expect_in in
            if cmd_pos || for_in
            then begin
              armed := (t = FOR || t = CASE);
              expect_in := false;
              set_prev t; t
            end
            else word_like lexbuf w
        | None -> word_like lexbuf w
    }
  | eof                       { armed := false; expect_in := false; prev := SEMI; EOF }
  | _ as c                    { raise (Error (String.make 1 c)) }
