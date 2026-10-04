
val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

val mul : int -> int -> int

module Nat :
 sig
  val add : int -> int -> int

  val sub : int -> int -> int

  val max : int -> int -> int

  val divmod : int -> int -> int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int
 end

val rev : 'a1 list -> 'a1 list

val rev_append : 'a1 list -> 'a1 list -> 'a1 list

val forallb : ('a1 -> bool) -> 'a1 list -> bool

type text = int list

val teqb : text -> text -> bool

val nstat : int -> int

val bstat : int -> int

type cstate = { cstatus : int; cenv : (text * text) list }

val getv : text -> (text * text) list -> text option

val setv : text -> text -> (text * text) list -> (text * text) list

val true_w : text

val false_w : text

val ex_status : text -> cstate -> int

val b_dollar : int

val b_lbrace : int

val b_rbrace : int

val b_qmark : int

val b_uscore : int

val b_0 : int

val is_digit : int -> bool

val is_alpha : int -> bool

val is_name : int -> bool

val nat_digits : int -> int -> text -> text

val nat2text : int -> text

val subst_var : (text * text) list -> text -> text -> text

val expand : int -> (text * text) list -> int -> text -> text

val expand_name : int -> (text * text) list -> int -> text -> text -> text

val expand_brace : int -> (text * text) list -> int -> text -> text -> text

val b_star : int

val glob : int -> text -> text -> bool

val match_any : int -> text list -> text -> bool

type run_phi = int -> text list -> cstate -> cstate option

type cmd =
| Skip
| Ext of int * text list
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

val pure_phi : int -> text list -> cstate -> cstate option

val run : run_phi -> int -> cmd -> cstate -> cstate option

val run_seq : run_phi -> int -> cmd list -> cstate -> cstate option

val run_for :
  run_phi -> int -> text -> text list -> cmd list -> cstate -> cstate option

val run_case :
  run_phi -> int -> text -> (text list * cmd list) list -> cstate -> cstate
  option

val mAX_WIDTH : int

val mAX_WORD : int

val mAX_ARGV : int

val mAX_ENV : int

val mAX_LIST : int

val gLOB_FUEL : int

val mAX_FUEL : int

val max_cmd_from_margin : int

val max_stack_from_margin : int

type jpl_caps = { jpl_width : int; jpl_word : int; jpl_argv : int;
                  jpl_env : int; jpl_list : int; jpl_cmd : int;
                  jpl_stack : int; jpl_glob_fuel : int; jpl_fuel : int }

val jpl_caps_table : jpl_caps

type 'a bres =
| BOk of 'a
| BLimit

type bword = { bw_bytes : text; bw_len : int }

val raw_bword : text -> bword

type benv = { be_pairs : (text * text) list; be_len : int }

type frame =
| FSeq of int * cmd
| FAnd of int * cmd
| FOr of int * cmd
| FBang
| FIf of int * cmd * cmd
| FWhile of int * cmd * cmd
| FWhileBody of int * cmd * cmd
| FSeqList of int * cmd list
| FForRest of int * text * text list * cmd list

type stack = frame list

type cfg = { cf : int; cc : cmd option; ck : stack; cs : cstate }

type out =
| Onext of cfg
| Oeffect of int * text list * stack * cstate
| Odone of cstate
| Olimit

val isz : cstate -> bool

val enter_seq : int -> cmd list -> cstate -> stack -> out

val bind_word : int -> text -> text -> cstate -> cstate

val enter_for : int -> text -> text list -> cmd list -> cstate -> stack -> out

val enter_case :
  int -> text -> (text list * cmd list) list -> cstate -> stack -> out

val step_cmd : int -> cmd -> stack -> cstate -> out

val step_ret : stack -> cstate -> out

val step : cfg -> out

val pure_run_phi : run_phi

type dres =
| DDone of cstate
| DEff of int * text list * stack * cstate
| DLim

val mrun : int -> cfg -> dres

val glob_it : int -> text -> text -> (text * text) option -> bool

val glob_iter : int -> text -> text -> bool

val match_any_iter : int -> text list -> text -> bool

val branch_need : text list -> text -> int

val branch_guardb : int -> text list -> text -> bool

val getv_it : int -> text -> (text * text) list -> text option

val setv_it :
  int -> text -> text -> (text * text) list -> (text * text) list ->
  (text * text) list option

val be_getv : text -> benv -> text option

val be_setv : text -> text -> benv -> benv bres

type exp_mode =
| EMain
| EName
| EBrace

type exp_k = { ek_mode : exp_mode; ek_inp : text; ek_out : text;
               ek_name : text }

val ek_value : (text * text) list -> text -> text

val expand_go : int -> (text * text) list -> int -> exp_k -> text

val expand_it : int -> (text * text) list -> int -> text -> text

val expand_c : int -> (text * text) list -> int -> text -> bword bres

val assign_c : text -> text -> stack -> cstate -> out

val bind_word_o : int -> text -> text -> cstate -> cstate option

val enter_for_c :
  int -> text -> text list -> cmd list -> cstate -> stack -> out

val enter_case_c :
  int -> text -> (text list * cmd list) list -> cstate -> stack -> out

val step_cmd_c : int -> cmd -> stack -> cstate -> out

val step_ret_c : stack -> cstate -> out

val step_c : cfg -> out

val mrun_c : int -> cfg -> dres
