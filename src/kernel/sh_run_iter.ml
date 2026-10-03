
type nat =
| O
| S of nat

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

module Nat =
 struct
  (** val sub : nat -> nat -> nat **)

  let rec sub n m =
    match n with
    | O -> n
    | S k -> (match m with
              | O -> n
              | S l -> sub k l)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n' -> (match m with
               | O -> false
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> true
    | S n' -> (match m with
               | O -> false
               | S m' -> leb n' m')

  (** val divmod : nat -> nat -> nat -> nat -> nat * nat **)

  let rec divmod x y q u =
    match x with
    | O -> (q, u)
    | S x' ->
      (match u with
       | O -> divmod x' y (S q) y
       | S u' -> divmod x' y q u')

  (** val div : nat -> nat -> nat **)

  let div x y = match y with
  | O -> y
  | S y' -> fst (divmod x y' O y')

  (** val modulo : nat -> nat -> nat **)

  let modulo x = function
  | O -> x
  | S y' -> sub y' (snd (divmod x y' O y'))
 end

type text = nat list

(** val teqb : text -> text -> bool **)

let rec teqb s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _ :: _ -> false)
  | a1 :: r1 ->
    (match s2 with
     | [] -> false
     | a2 :: r2 -> if Nat.eqb a1 a2 then teqb r1 r2 else false)

(** val nstat : nat -> nat **)

let nstat k =
  Nat.modulo k (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val bstat : nat -> nat **)

let bstat n =
  if Nat.eqb n O then S O else O

type cstate = { cstatus : nat; cenv : (text * text) list }

(** val getv : text -> (text * text) list -> text option **)

let rec getv k = function
| [] -> None
| p :: r -> let (k', v) = p in if teqb k k' then Some v else getv k r

(** val setv : text -> text -> (text * text) list -> (text * text) list **)

let rec setv k v = function
| [] -> (k, v) :: []
| p :: r ->
  let (k', v') = p in
  if teqb k k' then (k, v) :: r else (k', v') :: (setv k v r)

(** val true_w : text **)

let true_w =
  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: [])))

(** val false_w : text **)

let false_w =
  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: ((S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) :: []))))

(** val ex_status : text -> cstate -> nat **)

let ex_status name _ =
  if teqb name true_w
  then O
  else if teqb name false_w
       then S O
       else S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val b_dollar : nat **)

let b_dollar =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))

(** val b_lbrace : nat **)

let b_lbrace =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val b_rbrace : nat **)

let b_rbrace =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val b_qmark : nat **)

let b_qmark =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val b_uscore : nat **)

let b_uscore =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val b_0 : nat **)

let b_0 =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))

(** val is_digit : nat -> bool **)

let is_digit b =
  (&&) (Nat.leb b_0 b)
    (Nat.leb b (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val is_alpha : nat -> bool **)

let is_alpha b =
  (||)
    ((&&)
      (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) b)
      (Nat.leb b (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    ((&&)
      (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        b)
      (Nat.leb b (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val is_name : nat -> bool **)

let is_name b =
  (||) ((||) (is_alpha b) (is_digit b)) (Nat.eqb b b_uscore)

(** val nat_digits : nat -> nat -> text -> text **)

let rec nat_digits f n acc =
  match f with
  | O -> acc
  | S f' ->
    if Nat.eqb n O
    then acc
    else nat_digits f' (Nat.div n (S (S (S (S (S (S (S (S (S (S O)))))))))))
           ((add (Nat.modulo n (S (S (S (S (S (S (S (S (S (S O))))))))))) b_0) :: acc)

(** val nat2text : nat -> text **)

let nat2text n = match n with
| O -> b_0 :: []
| S _ -> nat_digits (S (S (S (S (S (S (S (S (S (S O)))))))))) n []

(** val subst_var : (text * text) list -> text -> text -> text **)

let subst_var m nm rest =
  match getv nm m with
  | Some v -> app v rest
  | None -> rest

(** val expand : nat -> (text * text) list -> nat -> text -> text **)

let rec expand f m st inp =
  match f with
  | O -> []
  | S f' ->
    (match inp with
     | [] -> []
     | b :: bs ->
       if Nat.eqb b b_dollar
       then (match bs with
             | [] -> b_dollar :: []
             | b2 :: bs2 ->
               if Nat.eqb b2 b_lbrace
               then expand_brace f' m st bs2 []
               else if is_name b2
                    then expand_name f' m st bs2 (b2 :: [])
                    else if Nat.eqb b2 b_qmark
                         then app (nat2text st) (expand f' m st bs2)
                         else b_dollar :: (expand f' m st bs))
       else b :: (expand f' m st bs))

(** val expand_name :
    nat -> (text * text) list -> nat -> text -> text -> text **)

and expand_name f m st inp acc =
  match f with
  | O -> subst_var m acc []
  | S f' ->
    (match inp with
     | [] -> subst_var m acc []
     | b :: bs ->
       if is_name b
       then expand_name f' m st bs (app acc (b :: []))
       else subst_var m acc (expand f' m st inp))

(** val expand_brace :
    nat -> (text * text) list -> nat -> text -> text -> text **)

and expand_brace f m st inp acc =
  match f with
  | O -> []
  | S f' ->
    (match inp with
     | [] -> []
     | b :: bs ->
       if Nat.eqb b b_rbrace
       then subst_var m acc (expand f' m st bs)
       else expand_brace f' m st bs (app acc (b :: [])))

(** val b_star : nat **)

let b_star =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))

(** val glob : nat -> text -> text -> bool **)

let rec glob f pat str =
  match f with
  | O -> false
  | S f' ->
    (match pat with
     | [] -> (match str with
              | [] -> true
              | _ :: _ -> false)
     | p :: ps ->
       if Nat.eqb p b_star
       then (match str with
             | [] -> glob f' ps []
             | _ :: ss -> (||) (glob f' ps str) (glob f' pat ss))
       else (match str with
             | [] -> false
             | s :: ss ->
               if Nat.eqb p b_qmark
               then glob f' ps ss
               else if Nat.eqb p s then glob f' ps ss else false))

(** val match_any : nat -> text list -> text -> bool **)

let rec match_any f pats scrut =
  match f with
  | O -> false
  | S f' ->
    (match pats with
     | [] -> false
     | p :: r -> (||) (glob f' p scrut) (match_any f' r scrut))

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

(** val obind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let obind x f =
  match x with
  | Some a -> f a
  | None -> None

(** val pure_phi : nat -> text list -> cstate -> cstate option **)

let pure_phi _ argv s =
  match argv with
  | [] -> Some { cstatus = O; cenv = s.cenv }
  | w :: _ -> Some { cstatus = (nstat (ex_status w s)); cenv = s.cenv }

(** val run : run_phi -> nat -> cmd -> cstate -> cstate option **)

let rec run phi f c s =
  match f with
  | O ->
    (match c with
     | Skip -> Some s
     | Ext (idx, argv) -> phi idx argv s
     | Assign (k, v) -> Some { cstatus = O; cenv = (setv k v s.cenv) }
     | _ -> None)
  | S f' ->
    (match c with
     | Skip -> Some s
     | Ext (idx, argv) -> phi idx argv s
     | Assign (k, v) -> Some { cstatus = O; cenv = (setv k v s.cenv) }
     | Seq (c1, c2) -> obind (run phi f' c1 s) (run phi f' c2)
     | And (c1, c2) ->
       obind (run phi f' c1 s) (fun s1 ->
         if Nat.eqb s1.cstatus O then run phi f' c2 s1 else Some s1)
     | Or (c1, c2) ->
       obind (run phi f' c1 s) (fun s1 ->
         if Nat.eqb s1.cstatus O then Some s1 else run phi f' c2 s1)
     | Bang c0 ->
       obind (run phi f' c0 s) (fun s1 -> Some { cstatus = (bstat s1.cstatus);
         cenv = s1.cenv })
     | If (cond, t, e) ->
       obind (run phi f' cond s) (fun sc ->
         if Nat.eqb sc.cstatus O then run phi f' t sc else run phi f' e sc)
     | While (cond, body) ->
       obind (run phi f' cond s) (fun sc ->
         if Nat.eqb sc.cstatus O
         then obind (run phi f' body sc) (run phi f' (While (cond, body)))
         else Some sc)
     | For (var, ws, body) -> run_for phi f' var ws body s
     | Case (scrut, brs) -> run_case phi f' scrut brs s)

(** val run_seq : run_phi -> nat -> cmd list -> cstate -> cstate option **)

and run_seq phi f cmds s =
  match f with
  | O -> None
  | S f' ->
    (match cmds with
     | [] -> Some { cstatus = O; cenv = s.cenv }
     | c :: l ->
       (match l with
        | [] -> run phi f' c s
        | c2 :: r -> obind (run phi f' c s) (run_seq phi f' (c2 :: r))))

(** val run_for :
    run_phi -> nat -> text -> text list -> cmd list -> cstate -> cstate option **)

and run_for phi f var ws body s =
  match f with
  | O -> None
  | S f' ->
    (match ws with
     | [] -> Some { cstatus = O; cenv = s.cenv }
     | w :: l ->
       (match l with
        | [] ->
          let s1 = { cstatus = s.cstatus; cenv =
            (setv var (expand f' s.cenv s.cstatus w) s.cenv) }
          in
          run_seq phi f' body s1
        | w2 :: r ->
          let s1 = { cstatus = s.cstatus; cenv =
            (setv var (expand f' s.cenv s.cstatus w) s.cenv) }
          in
          obind (run_seq phi f' body s1) (run_for phi f' var (w2 :: r) body)))

(** val run_case :
    run_phi -> nat -> text -> (text list * cmd list) list -> cstate -> cstate
    option **)

and run_case phi f scrut brs s =
  match f with
  | O -> None
  | S f' ->
    (match brs with
     | [] -> Some { cstatus = O; cenv = s.cenv }
     | p :: r ->
       let (pats, body) = p in
       if match_any f' pats (expand f' s.cenv s.cstatus scrut)
       then run_seq phi f' body s
       else run_case phi f' scrut r s)

type 'a bres =
| BOk of 'a
| BLimit

type frame =
| FSeq of nat * cmd
| FAnd of nat * cmd
| FOr of nat * cmd
| FBang
| FIf of nat * cmd * cmd
| FWhile of nat * cmd * cmd
| FWhileBody of nat * cmd * cmd
| FSeqList of nat * cmd list
| FForRest of nat * text * text list * cmd list

type stack = frame list

type cfg = { cf : nat; cc : cmd option; ck : stack; cs : cstate }

type out =
| Onext of cfg
| Oeffect of nat * text list * stack * cstate
| Odone of cstate
| Olimit

(** val isz : cstate -> bool **)

let isz s =
  Nat.eqb s.cstatus O

(** val enter_seq : nat -> cmd list -> cstate -> stack -> out **)

let enter_seq h l s k =
  match h with
  | O -> Olimit
  | S g ->
    (match l with
     | [] ->
       Onext { cf = O; cc = None; ck = k; cs = { cstatus = O; cenv =
         s.cenv } }
     | c :: r ->
       (match r with
        | [] -> Onext { cf = g; cc = (Some c); ck = k; cs = s }
        | _ :: _ ->
          Onext { cf = g; cc = (Some c); ck = ((FSeqList (g, r)) :: k); cs =
            s }))

(** val bind_word : nat -> text -> text -> cstate -> cstate **)

let bind_word g var w s =
  { cstatus = s.cstatus; cenv =
    (setv var (expand g s.cenv s.cstatus w) s.cenv) }

(** val enter_for :
    nat -> text -> text list -> cmd list -> cstate -> stack -> out **)

let enter_for h var ws body s k =
  match h with
  | O -> Olimit
  | S g ->
    (match ws with
     | [] ->
       Onext { cf = O; cc = None; ck = k; cs = { cstatus = O; cenv =
         s.cenv } }
     | w :: l ->
       (match l with
        | [] -> enter_seq g body (bind_word g var w s) k
        | w2 :: r ->
          enter_seq g body (bind_word g var w s) ((FForRest (g, var,
            (w2 :: r), body)) :: k)))

(** val enter_case :
    nat -> text -> (text list * cmd list) list -> cstate -> stack -> out **)

let rec enter_case h scrut brs s k =
  match h with
  | O -> Olimit
  | S g ->
    (match brs with
     | [] ->
       Onext { cf = O; cc = None; ck = k; cs = { cstatus = O; cenv =
         s.cenv } }
     | p :: r ->
       let (pats, body) = p in
       if match_any g pats (expand g s.cenv s.cstatus scrut)
       then enter_seq g body s k
       else enter_case g scrut r s k)

(** val step_cmd : nat -> cmd -> stack -> cstate -> out **)

let step_cmd f c k s =
  match f with
  | O ->
    (match c with
     | Skip -> Onext { cf = O; cc = None; ck = k; cs = s }
     | Ext (idx, argv) -> Oeffect (idx, argv, k, s)
     | Assign (k', v) ->
       Onext { cf = O; cc = None; ck = k; cs = { cstatus = O; cenv =
         (setv k' v s.cenv) } }
     | _ -> Olimit)
  | S f' ->
    (match c with
     | Skip -> Onext { cf = O; cc = None; ck = k; cs = s }
     | Ext (idx, argv) -> Oeffect (idx, argv, k, s)
     | Assign (k', v) ->
       Onext { cf = O; cc = None; ck = k; cs = { cstatus = O; cenv =
         (setv k' v s.cenv) } }
     | Seq (c1, c2) ->
       Onext { cf = f'; cc = (Some c1); ck = ((FSeq (f', c2)) :: k); cs = s }
     | And (c1, c2) ->
       Onext { cf = f'; cc = (Some c1); ck = ((FAnd (f', c2)) :: k); cs = s }
     | Or (c1, c2) ->
       Onext { cf = f'; cc = (Some c1); ck = ((FOr (f', c2)) :: k); cs = s }
     | Bang c0 -> Onext { cf = f'; cc = (Some c0); ck = (FBang :: k); cs = s }
     | If (cond, t, e) ->
       Onext { cf = f'; cc = (Some cond); ck = ((FIf (f', t, e)) :: k); cs =
         s }
     | While (cond, body) ->
       Onext { cf = f'; cc = (Some cond); ck = ((FWhile (f', cond,
         body)) :: k); cs = s }
     | For (var, ws, body) -> enter_for f' var ws body s k
     | Case (scrut, brs) -> enter_case f' scrut brs s k)

(** val step_ret : stack -> cstate -> out **)

let step_ret k s =
  match k with
  | [] -> Odone s
  | fr :: r ->
    (match fr with
     | FSeq (f, c2) -> Onext { cf = f; cc = (Some c2); ck = r; cs = s }
     | FAnd (f, c2) ->
       if isz s
       then Onext { cf = f; cc = (Some c2); ck = r; cs = s }
       else Onext { cf = O; cc = None; ck = r; cs = s }
     | FOr (f, c2) ->
       if isz s
       then Onext { cf = O; cc = None; ck = r; cs = s }
       else Onext { cf = f; cc = (Some c2); ck = r; cs = s }
     | FBang ->
       Onext { cf = O; cc = None; ck = r; cs = { cstatus = (bstat s.cstatus);
         cenv = s.cenv } }
     | FIf (f, t, e) ->
       if isz s
       then Onext { cf = f; cc = (Some t); ck = r; cs = s }
       else Onext { cf = f; cc = (Some e); ck = r; cs = s }
     | FWhile (f, cnd, bdy) ->
       if isz s
       then Onext { cf = f; cc = (Some bdy); ck = ((FWhileBody (f, cnd,
              bdy)) :: r); cs = s }
       else Onext { cf = O; cc = None; ck = r; cs = s }
     | FWhileBody (f, cnd, bdy) ->
       Onext { cf = f; cc = (Some (While (cnd, bdy))); ck = r; cs = s }
     | FSeqList (f, l) -> enter_seq f l s r
     | FForRest (f, var, rws, body) -> enter_for f var rws body s r)

(** val step : cfg -> out **)

let step g =
  match g.cc with
  | Some c -> step_cmd g.cf c g.ck g.cs
  | None -> step_ret g.ck g.cs

(** val mloop : run_phi -> nat -> cfg -> cstate bres **)

let rec mloop phi b g =
  match b with
  | O -> BLimit
  | S b' ->
    (match step g with
     | Onext g' -> mloop phi b' g'
     | Oeffect (idx, argv, k, s) ->
       (match phi idx argv s with
        | Some s' -> mloop phi b' { cf = O; cc = None; ck = k; cs = s' }
        | None -> BLimit)
     | Odone st -> BOk st
     | Olimit -> BLimit)
