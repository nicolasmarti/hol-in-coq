
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h



(** val in_dec :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y :: l0 -> let s = h y a in if s then true else in_dec h a l0

(** val remove :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list **)

let rec remove eq_dec x = function
| [] -> []
| y :: tl ->
  if eq_dec x y
  then remove eq_dec x tl
  else y :: (remove eq_dec x tl)

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x :: l0 -> app x (concat l0)

(** val list_eq_dec :
    ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _ :: _ -> false)
  | y :: l0 ->
    (match l' with
     | [] -> false
     | a :: l1 ->
       if eq_dec y a then list_eq_dec eq_dec l0 l1 else false)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val string_dec : char list -> char list -> bool **)

let rec string_dec s x =
  match s with
  | [] -> (match x with
           | [] -> true
           | _::_ -> false)
  | a::s0 ->
    (match x with
     | [] -> false
     | a0::s1 -> if (=) a a0 then string_dec s0 s1 else false)

(** val list_dec_obligation_1 :
    'a1 list -> ('a1 -> __ -> 'a1 -> bool) -> 'a1 list -> bool **)

let list_dec_obligation_1 _ _ = function
| [] -> true
| _ :: _ -> false

(** val list_dec_obligation_2 :
    'a1 list -> ('a1 -> __ -> 'a1 -> bool) -> 'a1 list -> 'a1 ->
    'a1 list -> ('a1 list -> bool) -> bool **)

let list_dec_obligation_2 _ a_dec l2 hd _ x =
  match l2 with
  | [] -> false
  | a :: l -> if a_dec hd __ a then x l else false

(** val list_dec_obligation_3 :
    'a1 list -> ('a1 -> __ -> 'a1 -> bool) -> 'a1 -> 'a1 list ->
    'a1 -> 'a1 -> bool **)

let list_dec_obligation_3 _ a_dec _ _ a1 a2 =
  a_dec a1 __ a2

(** val list_dec :
    'a1 list -> ('a1 -> __ -> 'a1 -> bool) -> 'a1 list -> bool **)

let rec list_dec l1 a_dec l2 =
  match l1 with
  | [] -> list_dec_obligation_1 l1 a_dec l2
  | hd :: tl ->
    list_dec_obligation_2 l1 a_dec l2 hd tl
      (list_dec tl (fun a1 _ a2 ->
        list_dec_obligation_3 l1 a_dec hd tl a1 a2))

(** val zip : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec zip l1 l2 =
  match l1 with
  | [] -> []
  | hd1 :: tl1 ->
    (match l2 with
     | [] -> []
     | hd2 :: tl2 -> (hd1, hd2) :: (zip tl1 tl2))

(** val unzip : ('a1 * 'a2) list -> 'a1 list * 'a2 list **)

let rec unzip = function
| [] -> ([], [])
| p :: tl ->
  let (hd1, hd2) = p in
  let (tl1, tl2) = unzip tl in ((hd1 :: tl1), (hd2 :: tl2))

type term =
| Var of char list
| Fn of char list * term list

(** val term_recursion_func :
    (term, (__, (char list -> __, char list -> term list ->
    (term -> __ -> __) -> __) sigT) sigT) sigT -> __ **)

let rec term_recursion_func x =
  let t = projT1 x in
  let p_var = projT1 (projT2 (projT2 x)) in
  let p_fn = projT2 (projT2 (projT2 x)) in
  let term_recursion0 = fun t0 p_var0 p_fn0 ->
    term_recursion_func (ExistT (t0, (ExistT (__, (ExistT
      (p_var0, p_fn0))))))
  in
  (match t with
   | Var s -> p_var s
   | Fn (s, l) ->
     p_fn s l (fun x0 _ -> term_recursion0 x0 p_var p_fn))

(** val term_recursion :
    term -> (char list -> 'a1) -> (char list -> term list ->
    (term -> __ -> 'a1) -> 'a1) -> 'a1 **)

let term_recursion t p_var p_fn =
  Obj.magic term_recursion_func (ExistT (t, (ExistT (__, (ExistT
    ((Obj.magic p_var), (Obj.magic p_fn)))))))

(** val map_term :
    term list -> (term -> __ -> 'a1) -> 'a1 list **)

let rec map_term l p =
  match l with
  | [] -> []
  | hd :: tl -> (p hd __) :: (map_term tl (fun x _ -> p x __))

(** val term_eq_dec_obligation_1 : char list -> term -> bool **)

let term_eq_dec_obligation_1 s = function
| Var s0 -> string_dec s s0
| Fn (_, _) -> false

(** val term_eq_dec_obligation_2 :
    char list -> term list -> (term -> __ -> term -> bool) ->
    term -> bool **)

let term_eq_dec_obligation_2 s l h = function
| Var _ -> false
| Fn (s0, l0) ->
  if string_dec s s0 then list_dec l h l0 else false

(** val term_eq_dec : term -> term -> bool **)

let term_eq_dec t1 =
  term_recursion t1 term_eq_dec_obligation_1
    term_eq_dec_obligation_2

(** val term_free_vars : term -> char list list **)

let term_free_vars t =
  term_recursion t (fun s -> s :: []) (fun _ l h ->
    concat (map_term l h))

type formula =
| Ftrue
| Ffalse
| Atom of char list * term list
| Eq of term * term
| Not of formula
| And of formula * formula
| Or of formula * formula
| Imp of formula * formula
| Iff of formula * formula
| Forall of char list * formula
| Exists of char list * formula

(** val formula_dec : formula -> formula -> bool **)

let rec formula_dec f x =
  match f with
  | Ftrue -> (match x with
              | Ftrue -> true
              | _ -> false)
  | Ffalse -> (match x with
               | Ffalse -> true
               | _ -> false)
  | Atom (s, l) ->
    (match x with
     | Atom (s0, l0) ->
       if string_dec s s0
       then list_eq_dec term_eq_dec l l0
       else false
     | _ -> false)
  | Eq (t, t0) ->
    (match x with
     | Eq (t1, t2) ->
       if term_eq_dec t t1 then term_eq_dec t0 t2 else false
     | _ -> false)
  | Not f0 ->
    (match x with
     | Not f1 -> formula_dec f0 f1
     | _ -> false)
  | And (f0, f1) ->
    (match x with
     | And (f2, f3) ->
       if formula_dec f0 f2 then formula_dec f1 f3 else false
     | _ -> false)
  | Or (f0, f1) ->
    (match x with
     | Or (f2, f3) ->
       if formula_dec f0 f2 then formula_dec f1 f3 else false
     | _ -> false)
  | Imp (f0, f1) ->
    (match x with
     | Imp (f2, f3) ->
       if formula_dec f0 f2 then formula_dec f1 f3 else false
     | _ -> false)
  | Iff (f0, f1) ->
    (match x with
     | Iff (f2, f3) ->
       if formula_dec f0 f2 then formula_dec f1 f3 else false
     | _ -> false)
  | Forall (s, f0) ->
    (match x with
     | Forall (s0, f1) ->
       if string_dec s s0 then formula_dec f0 f1 else false
     | _ -> false)
  | Exists (s, f0) ->
    (match x with
     | Exists (s0, f1) ->
       if string_dec s s0 then formula_dec f0 f1 else false
     | _ -> false)

(** val formula_free_vars : formula -> char list list **)

let rec formula_free_vars = function
| Atom (_, args) -> concat (map term_free_vars args)
| Eq (t1, t2) -> app (term_free_vars t1) (term_free_vars t2)
| Not f0 -> formula_free_vars f0
| And (f1, f2) ->
  app (formula_free_vars f1) (formula_free_vars f2)
| Or (f1, f2) ->
  app (formula_free_vars f1) (formula_free_vars f2)
| Imp (f1, f2) ->
  app (formula_free_vars f1) (formula_free_vars f2)
| Iff (f1, f2) ->
  app (formula_free_vars f1) (formula_free_vars f2)
| Forall (x, f0) -> remove string_dec x (formula_free_vars f0)
| Exists (x, f0) -> remove string_dec x (formula_free_vars f0)
| _ -> []

module type ProofSystem =
 sig
  type coq_Thm

  val concl : coq_Thm -> formula

  val modusponens : coq_Thm -> coq_Thm -> coq_Thm

  val gen : char list -> coq_Thm -> coq_Thm

  val axiom_addimp : formula -> formula -> coq_Thm

  val axiom_distribimp : formula -> formula -> formula -> coq_Thm

  val axiom_doubleneg : formula -> coq_Thm

  val axiom_allimp : char list -> formula -> formula -> coq_Thm

  val axiom_impall : char list -> formula -> coq_Thm

  val axiom_existseq : char list -> term -> coq_Thm

  val axiom_eqrefl : term -> coq_Thm

  val axiom_funcong :
    char list -> term list -> term list -> coq_Thm

  val axiom_predcong :
    char list -> term list -> term list -> coq_Thm

  val axiom_iffimp1 : formula -> formula -> coq_Thm

  val axiom_iffimp2 : formula -> formula -> coq_Thm

  val axiom_impiff : formula -> formula -> coq_Thm

  val axiom_true : coq_Thm

  val axiom_not : formula -> coq_Thm

  val axiom_and : formula -> formula -> coq_Thm

  val axiom_or : formula -> formula -> coq_Thm

  val axiom_exists : char list -> formula -> coq_Thm
 end

type thm = formula

(** val concl0 : thm -> formula **)

let concl0 thm0 =
  thm0

(** val mkThm : formula -> thm **)

let mkThm f =
  f

(** val t_Thm : formula **)

let t_Thm =
  Ftrue

(** val modusponens_thm : thm -> thm -> thm **)

let modusponens_thm thm1 thm2 =
  let filtered_var = concl0 thm1 in
  (match filtered_var with
   | Imp (f1, f2) ->
     let filtered_var0 = formula_dec f1 thm2 in
     if filtered_var0 then mkThm f2 else t_Thm
   | _ -> t_Thm)

(** val gen_thm : char list -> thm -> thm **)

let gen_thm x thm0 =
  mkThm (Forall (x, (concl0 thm0)))

(** val addimp_thm : formula -> formula -> thm **)

let addimp_thm p q =
  mkThm (Imp (p, (Imp (q, p))))

(** val distribimp_thm : formula -> formula -> formula -> thm **)

let distribimp_thm p q r =
  mkThm (Imp ((Imp (p, (Imp (q, r)))), (Imp ((Imp (p, q)), (Imp
    (p, r))))))

(** val doubleneg_thm : formula -> thm **)

let doubleneg_thm p =
  mkThm (Imp ((Imp ((Imp (p, Ffalse)), Ffalse)), p))

(** val allimp_thm : char list -> formula -> formula -> thm **)

let allimp_thm x p q =
  mkThm (Imp ((Forall (x, (Imp (p, q)))), (Imp ((Forall (x, p)),
    (Forall (x, q))))))

(** val impall_thm : char list -> formula -> thm **)

let impall_thm x p =
  let filtered_var = in_dec string_dec x (formula_free_vars p) in
  if filtered_var
  then t_Thm
  else mkThm (Imp (p, (Forall (x, p))))

(** val existseq_thm : char list -> term -> thm **)

let existseq_thm x t =
  let filtered_var = in_dec string_dec x (term_free_vars t) in
  if filtered_var
  then t_Thm
  else mkThm (Exists (x, (Eq ((Var x), t))))

(** val eqrefl_thm : term -> thm **)

let eqrefl_thm t =
  mkThm (Eq (t, t))

(** val iffimp1_thm : formula -> formula -> thm **)

let iffimp1_thm p q =
  mkThm (Imp ((Iff (p, q)), (Imp (p, q))))

(** val iffimp2_thm : formula -> formula -> thm **)

let iffimp2_thm p q =
  mkThm (Imp ((Iff (p, q)), (Imp (q, p))))

(** val impiff_thm : formula -> formula -> thm **)

let impiff_thm p q =
  mkThm (Imp ((Imp (p, q)), (Imp ((Imp (q, p)), (Iff (p, q))))))

(** val true_thm : thm **)

let true_thm =
  mkThm (Iff (Ftrue, (Imp (Ffalse, Ffalse))))

(** val not_thm : formula -> thm **)

let not_thm p =
  mkThm (Iff ((Not p), (Imp (p, Ffalse))))

(** val and_thm : formula -> formula -> thm **)

let and_thm p q =
  mkThm (Iff ((And (p, q)), (Imp ((Imp (p, (Imp (q, Ffalse)))),
    Ffalse))))

(** val or_thm : formula -> formula -> thm **)

let or_thm p q =
  mkThm (Iff ((Or (p, q)), (Not (And ((Not p), (Not q))))))

(** val exists_thm : char list -> formula -> thm **)

let exists_thm x p =
  mkThm (Iff ((Exists (x, p)), (Not (Forall (x, (Not p))))))

(** val formulas_imp : formula list -> formula -> formula **)

let rec formulas_imp l ccl =
  match l with
  | [] -> ccl
  | hd :: tl -> Imp (hd, (formulas_imp tl ccl))

(** val funcong_thm :
    char list -> term list -> term list -> thm **)

let funcong_thm f lhs rhs =
  mkThm
    (formulas_imp
      (map (fun x -> Eq ((fst x), (snd x))) (zip lhs rhs)) (Eq
      ((Fn (f, (fst (unzip (zip lhs rhs))))), (Fn (f,
      (snd (unzip (zip lhs rhs))))))))

(** val predcong_thm :
    char list -> term list -> term list -> thm **)

let predcong_thm p lhs rhs =
  mkThm
    (formulas_imp
      (map (fun x -> Eq ((fst x), (snd x))) (zip lhs rhs)) (Imp
      ((Atom (p, (fst (unzip (zip lhs rhs))))), (Atom (p,
      (snd (unzip (zip lhs rhs))))))))

module Proven =
 struct
  type coq_Thm = thm

  (** val concl : coq_Thm -> formula **)

  let concl =
    concl0

  (** val modusponens : coq_Thm -> coq_Thm -> coq_Thm **)

  let modusponens =
    modusponens_thm

  (** val gen : char list -> coq_Thm -> coq_Thm **)

  let gen =
    gen_thm

  (** val axiom_addimp : formula -> formula -> coq_Thm **)

  let axiom_addimp =
    addimp_thm

  (** val axiom_distribimp :
      formula -> formula -> formula -> coq_Thm **)

  let axiom_distribimp =
    distribimp_thm

  (** val axiom_doubleneg : formula -> coq_Thm **)

  let axiom_doubleneg =
    doubleneg_thm

  (** val axiom_allimp :
      char list -> formula -> formula -> coq_Thm **)

  let axiom_allimp =
    allimp_thm

  (** val axiom_impall : char list -> formula -> coq_Thm **)

  let axiom_impall =
    impall_thm

  (** val axiom_existseq : char list -> term -> coq_Thm **)

  let axiom_existseq =
    existseq_thm

  (** val axiom_eqrefl : term -> coq_Thm **)

  let axiom_eqrefl =
    eqrefl_thm

  (** val axiom_funcong :
      char list -> term list -> term list -> coq_Thm **)

  let axiom_funcong =
    funcong_thm

  (** val axiom_predcong :
      char list -> term list -> term list -> coq_Thm **)

  let axiom_predcong =
    predcong_thm

  (** val axiom_iffimp1 : formula -> formula -> coq_Thm **)

  let axiom_iffimp1 =
    iffimp1_thm

  (** val axiom_iffimp2 : formula -> formula -> coq_Thm **)

  let axiom_iffimp2 =
    iffimp2_thm

  (** val axiom_impiff : formula -> formula -> coq_Thm **)

  let axiom_impiff =
    impiff_thm

  (** val axiom_true : coq_Thm **)

  let axiom_true =
    true_thm

  (** val axiom_not : formula -> coq_Thm **)

  let axiom_not =
    not_thm

  (** val axiom_and : formula -> formula -> coq_Thm **)

  let axiom_and =
    and_thm

  (** val axiom_or : formula -> formula -> coq_Thm **)

  let axiom_or =
    or_thm

  (** val axiom_exists : char list -> formula -> coq_Thm **)

  let axiom_exists =
    exists_thm
 end
