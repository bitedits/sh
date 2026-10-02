%{
open Ast
let fst4 (a, _, _, _) = a
let snd4 (_, b, _, _) = b
let trd4 (_, _, c, _) = c
let fth4 (_, _, _, d) = d
let fst3 (a, _, _) = a
let snd3 (_, b, _) = b
let trd3 (_, _, c) = c
let fst (a, _) = a
let snd (_, b) = b
let extract_words = List.map (function Word w -> w | _ -> raise (Failure "Expected Word"))
(* split an exp list into (assignment-strings, other exps) / (word-args, other exps) *)
let part_asg xs =
  List.fold_left
    (fun (a, d) e -> match e with
      | Assignment s -> (a @ [s], d)
      | _ -> (a, d @ [e])) ([], []) xs
let part_words xs =
  List.fold_left
    (fun (a, d) e -> match e with
      | Word w -> (a @ [w], d)
      | _ -> (a, d @ [e])) ([], []) xs
let asg_exps ss = List.map (fun s -> Assignment s) ss
%}

%token <string> WORD ASSIGNMENT_WORD NAME
%token <int> IO_NUMBER
%token AND_IF OR_IF DSEMI DLESS DGREAT LESSAND GREATAND LESSGREAT DLESSDASH CLOBBER
%token LESS GREAT PIPE AMP SEMI EOF BANG LPAREN RPAREN LBRACE RBRACE
%token IF THEN ELSE ELIF FI DO DONE CASE ESAC WHILE UNTIL FOR IN
%start <Ast.exp> main

%%

(* https://pubs.opengroup.org/onlinepubs/9695969399/toc.pdf *)
(* The lexer folds newline into SEMI (dropping it inside continuation contexts),
   so this grammar is line-oriented only through SEMI separators. *)

main:          | list EOF                          { $1 }
               | list separator EOF               { $1 }   (* trailing separator *)

list:          | list separator and_or             { List ($1, $2, $3) }
               | and_or                            { $1 }

and_or:        | pipeline                          { Pipeline (fst $1, snd $1) }
               | and_or AND_IF pipeline            { AndIf ($1, Pipeline (fst $3, snd $3)) }
               | and_or OR_IF  pipeline            { OrIf  ($1, Pipeline (fst $3, snd $3)) }

pipeline:      | pipe_sequence                     { (false, $1) }
               | BANG pipe_sequence                { (true,  $2) }

pipe_sequence: | command                           { [$1] }
               | pipe_sequence PIPE command        { $1 @ [$3] }

command:       | scmd                              { $1 }
               | compound                          { Compound ($1, []) }
               | compound rlist                    { Compound ($1, $2) }
               | function_def                      { $1 }

(* a block is a complete command list used as an if/while/for/case body or a
   brace/subshell group.  The lexer turns each line break into a SEMI, so a
   block may end with a trailing separator just before a closing keyword. *)
block:         | list                              { [$1] }
               | list separator                    { [$1] }
               |                                   { [] }

compound:      | brace_group                       { BraceGroup $1 }
               | subshell                          { Subshell $1 }
               | for_clause                        { ForClause (fst3 $1, Option.map extract_words (snd3 $1), trd3 $1) }
               | case_clause                       { CaseClause (fst $1, snd $1) }
               | if_clause                         { IfClause (fst4 $1, snd4 $1, trd4 $1, fth4 $1) }
               | while_clause                      { WhileClause (fst $1, snd $1) }
               | until_clause                      { UntilClause (fst $1, snd $1) }

subshell:      | LPAREN block RPAREN               { $2 }
brace_group:   | LBRACE block RBRACE               { $2 }
do_group:      | DO block DONE                      { $2 }

(* for-variable is a plain WORD; `in words` and the pre-do separator are optional *)
for_clause:    | FOR WORD IN wlist SEMI do_group   { ($2, Some $4, $6) }
               | FOR WORD IN wlist     do_group    { ($2, Some $4, $5) }
               | FOR WORD IN     SEMI do_group     { ($2, Some [], $5) }
               | FOR WORD     IN     do_group      { ($2, Some [], $4) }
               | FOR WORD SEMI     do_group        { ($2, None,    $4) }
               | FOR WORD          do_group        { ($2, None,    $3) }

wlist:         | WORD                              { [Word $1] }
               | wlist WORD                        { $1 @ [Word $2] }

case_clause:   | CASE WORD IN case_list ESAC       { ($2, $4) }
               | CASE WORD IN           ESAC       { ($2, []) }
case_list:     | case_list case_item               { $1 @ [$2] }
               | case_item                         { [$1] }
case_item:     | pattern RPAREN        block DSEMI { (extract_words $1, $3) }
               | LPAREN pattern RPAREN block DSEMI { (extract_words $2, $4) }
               | LPAREN pattern RPAREN      DSEMI  { (extract_words $2, []) }
               | pattern RPAREN             DSEMI  { (extract_words $1, []) }
pattern:       | WORD                              { [Word $1] }
               | pattern PIPE WORD                 { $1 @ [Word $3] }

if_clause:     | IF block THEN block FI                       { ($2, $4, [], None) }
               | IF block THEN block else_part FI             { ($2, $4, fst $5, snd $5) }
else_part:     | ELSE block                                   { ([], Some $2) }
               | ELIF block THEN block                        { ([($2, $4)], None) }
               | ELIF block THEN block else_part              { (($2, $4) :: fst $5, snd $5) }

while_clause:  | WHILE block DO block DONE          { ($2, $4) }
until_clause:  | UNTIL block DO block DONE          { ($2, $4) }

function_def:  | NAME LPAREN RPAREN function_body   { FunctionDef ($1, $4) }
function_body: | compound                          { Compound ($1, []) }
               | compound rlist                    { Compound ($1, $2) }

(* a simple command: assignment/redirect prefix, command word, then word
   arguments and redirects.  Prefix assignments are preserved as Assignment
   exps (they update the environment); assignment-shaped words after the
   command word stay literal arguments. *)
scmd:          | prefix WORD suffix                 { let (a, r)  = part_asg $1 in
                                                       let (w, r') = part_words $3 in
                                                       Simple (Some ($2, w), asg_exps a @ r @ r') }
               | prefix WORD                        { let (a, r) = part_asg $1 in
                                                       Simple (Some ($2, []), asg_exps a @ r) }
               | prefix                             { let (a, r) = part_asg $1 in
                                                       Simple (None, asg_exps a @ r) }
               | WORD suffix                        { let (w, r) = part_words $2 in
                                                       Simple (Some ($1, w), r) }
               | WORD                               { Simple (Some ($1, []), []) }

prefix:        | assign                             { [Assignment $1] }
               | prefix assign                      { $1 @ [Assignment $2] }
               | io_redirect                        { [$1] }
               | prefix io_redirect                 { $1 @ [$2] }
assign:        | ASSIGNMENT_WORD                    { $1 }

suffix:        | suffix_word                        { [$1] }
               | suffix suffix_word                 { $1 @ [$2] }
               | suffix io_redirect                 { $1 @ [$2] }
suffix_word:   | WORD                               { Word $1 }
               | ASSIGNMENT_WORD                    { Word $1 }   (* literal arg after the command word *)

rlist:         | io_redirect                        { [$1] }
               | rlist io_redirect                  { $1 @ [$2] }

io_redirect:   | io_file                            { IoFile (None, fst $1, snd $1) }
               | IO_NUMBER io_file                  { IoFile (Some $1, fst $2, snd $2) }
               | io_here                            { IoHere (None, fst $1, snd $1) }
               | IO_NUMBER io_here                  { IoHere (Some $1, fst $2, snd $2) }

io_file:       | LESS      WORD                     { (Less, $2) }
               | GREAT     WORD                     { (Great, $2) }
               | DGREAT    WORD                     { (DGreat, $2) }
               | LESSAND   WORD                     { (LessAnd, $2) }
               | GREATAND  WORD                     { (GreatAnd, $2) }
               | LESSGREAT WORD                     { (LessGreat, $2) }
               | CLOBBER   WORD                     { (Clobber, $2) }
io_here:       | DLESS      WORD                    { (DLess, $2) }
               | DLESSDASH  WORD                    { (DLessDash, $2) }

separator:     | AMP                                { `Amp }
               | SEMI                               { `Semi }
