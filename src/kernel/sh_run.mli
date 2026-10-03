
type nat =
| O
| S of nat

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : nat -> nat -> nat

module Nat :
 sig
  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val divmod : nat -> nat -> nat -> nat -> nat * nat

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat
 end

type text = nat list

val teqb : text -> text -> bool

val nstat : nat -> nat

val bstat : nat -> nat

type cstate = { cstatus : nat; cenv : (text * text) list }

val getv : text -> (text * text) list -> text option

val setv : text -> text -> (text * text) list -> (text * text) list

val true_w : text

val false_w : text

val ex_status : text -> cstate -> nat

val b_dollar : nat

val b_lbrace : nat

val b_rbrace : nat

val b_qmark : nat

val b_uscore : nat

val b_0 : nat

val is_digit : nat -> bool

val is_alpha : nat -> bool

val is_name : nat -> bool

val nat_digits : nat -> nat -> text -> text

val nat2text : nat -> text

val subst_var : (text * text) list -> text -> text -> text

val expand : nat -> (text * text) list -> nat -> text -> text

val expand_name : nat -> (text * text) list -> nat -> text -> text -> text

val expand_brace : nat -> (text * text) list -> nat -> text -> text -> text

val b_star : nat

val glob : nat -> text -> text -> bool

val match_any : nat -> text list -> text -> bool

type run_phi = nat -> text list -> cstate -> cstate option

type cmd =
| Skip
| Ext of nat * text list
| Assign of text * text
| Seq of cmd * cmd
| And of cmd * cmd
| Or of cmd * cmd
| Bang of cmd
| If of cmd * cmd * cmd
| While of cmd * cmd
| For of text * text list * cmd list
| Case of text * (text list * cmd list) list

val obind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

val pure_phi : nat -> text list -> cstate -> cstate option

val run : run_phi -> nat -> cmd -> cstate -> cstate option

val run_seq : run_phi -> nat -> cmd list -> cstate -> cstate option

val run_for :
  run_phi -> nat -> text -> text list -> cmd list -> cstate -> cstate option

val run_case :
  run_phi -> nat -> text -> (text list * cmd list) list -> cstate -> cstate
  option
