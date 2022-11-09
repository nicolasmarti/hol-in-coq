(*

thoughts/points:

- original goal: formalizing Chapter 6 of Harrison's 
                 [Handbook of Practical Logic and Automated Reasoning]
  => extraction of a certified Ocaml module for lcf kernel
  => decision procedure by reflection [? quantifying effort vs reward, extraction, ... ?]
  => decision procedure as tactics [more flexible, no extraction]
  => testing a few Coq tools (e.g., coq-hammer ... elpi )

- non primitive structural recursive definition of term
  => requires a taylor made induction principle 
     (based on Program/measure)
  => for each constructor applied to the induction predicate, 
     we have a rewriting lemma [ Rec (c a_0 ... a_n) = P a_0 ... a_n ]
     (avoiding verbose goals on unfolding/reducing proof terms)

- usual logic's notions:
  ==> a model maps terms to values, and propositions to booleans/Prop@coq
  ==> a model satifies a formula := the model evaluates the formula to true/True 
      (m |= f)
  ==> validity of a formula := all model satifies the formula
      (|- m := V m, m |= f)


- need a dependent type bearing: (1) a formula and, (2) its proof. Otherwise, 
  extracting a function/lemma based purely on (|-) leads to an empty Ocaml code 
  [c.f. illustrating extraction of modusponens and modusponens_thm]
  ==> also provide generic lemmas for conversion

- in Harrison, equality is the predicate ("="). 
  We made it a formula constructor, for the following reasons:
  ==> if defined as a predicate, models needs extra assumptions
      [ the semantics of the predicate "=" ]
  ==> equality is an ubiquitous primitive for reasoning systems (e.g., superposition)
  This modification has a consequence: we need to add some extra rules in the kernel.
  Harrison only required reflexivity, we will need to add commutativity and transitivity.

- sometime Program generates opaque obligations:
  ==> where are they coming from ?
  ==> what is their purpose ?
  ==> how can they be proved ? (tactics knows ... not me)

- We have validity schemas with variable numbers of premises :
  (e.g.,  |- p_0 ==> ... ==> p_n ==> p_i { for i in [0, n] })
  (e.g.,  |- p_0 //\\ ... //\\ p_n ==> p_i { for i in [0, n] })
  for those, dependent types are of essence, but not easy to apply 
  (for use case for reification by tactics)

*)

(*
  In progress:  
  6.6: Proving Tautologies by inference
  6.7: First Order Derivatives Rules
  6.9: Interactive Proof Styles
*)

(*
TODO:
- use case for elpi/ltac ~~> Thm from/to (|- p)
- clean proof:
  ==> branches/cases to be more readable
  ==> make key cut assertions explicit
  ==> remove all garbage / exploratory tactics, replacing by sauto
 *)

(*
stupid ideas:
- connection with why3 ??
- coq-hammer: could it helps quantifying what are the proper lemmas ??
  ==> the more all lemmas are automatically provable, the better the formalization in terms of elementary/helper lemmas
  ==> could we test/quantify this ? take a well known theory [e.g., binary number], and a goal lemma (signed/unsigned addition circuit/algo)
      - 

- could be usefull to make definition Opaque for testing if
  one is truly reusing helper lemma, and not reducing the goal
  definitions and solving in a bit more brute force.

- how to discriminate which definition (and possibly program obligation)
  to be made Opaque ???

- that would be nice to have a "free" window in proof general
  ==> input some test Definition, Axioms, Commands, ... [showing not the latest input but full trace]
  ==> to be evaluated using the current state of Coq [debugging, so far so good ...]

*)

Require Import Bool.
Require Import Nat.
Require Import Peano_dec.
Require Import List.
Import ListNotations.
Require Import String.
Require Import Lia.

(* just for dev time *)

From Hammer Require Import Hammer.
Set Hammer GSMode 2.

(**)


(* funky stuff (c.f. above) *)
From Hammer Require Import Tactics.
From elpi Require Import elpi.
(**)


Require Import Coq.Program.Wf.

Open Scope string_scope.
Open Scope list_scope.


Require Import Coq.extraction.ExtrOcamlString.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import ExtrOcamlNatBigInt.

(**** some general helper lemmas ******)
(*
[ TODO: try to find equivalents in standard library and remove this section ]
*)

Program Fixpoint list_dec {A: Set} (l1: list A) (A_dec: forall a1, In a1 l1 -> forall a2, { a1 = a2 } + { a1 <> a2 }) (l2: list A) { struct l1 }: { l1 = l2 } + { l1 <> l2 } :=
  match l1 with
  | nil => _
  | hd::tl => _ (@list_dec A tl _)
  end.
Next Obligation.
  sauto lq: on.  
Defined.
Next Obligation.
  destruct l2; simpl; auto.
  sfirstorder.
  assert (In hd (hd::tl)) by intuition.
  assert ({hd = a} + {hd <> a}) by hauto lq: on.
  inversion_clear H0.
  subst a; generalize (x l2); intro H0; inversion_clear H0.
  sfirstorder.
  hauto lq: on.
  hauto lq: on.
Defined.
Next Obligation.
  intuition.
Defined.

(* this one is highly suspicious *)

Lemma remove_In_diff: forall {A: Set} H
                             (l: list A) (x x0: A), x <> x0 -> List.In x l -> List.In x (@List.remove _ H x0 l).
  do 2 intro.
  induction l; simpl; intros; auto.
  inversion_clear H1.
  subst x.
  destruct (H x0 a); intuition.
  destruct (H x0 a); intuition.
Qed.

(* tuples *)

Inductive tuple: forall (l: list Prop), Type :=
| tnil: tuple nil
| tcons: forall {hd: Prop} (thd: hd) {tl: list Prop} (ttl: tuple tl), tuple (hd::tl).

Lemma in_f_map:
  forall {A B: Type} (f: A -> B) (l: list A) (x: A),
    In x l ->
    In (f x) (map f l).
  induction l.
  sauto.
  sauto.
Qed.

(**)

Fixpoint remove_dec
  {A: Type}
  (A_dec: forall (x y: A), { x = y } + { x <> y })
  (x: A)
  (l: list A) :=
  match l with
  | nil => nil
  | hd::tl =>
      match A_dec x hd with
      | left _ => remove_dec A_dec x tl
      | right _ => hd::(remove_dec A_dec x tl)
      end
  end.

Lemma remove_dec_in1 {A: Type} (A_dec: forall (x y: A), { x = y } + { x <> y }) (x: A):
  forall (l: list A),
  forall (e: A), In e (remove_dec A_dec x l) -> e <> x.
  induction l; simpl; intros; auto.
  destruct (A_dec x a).
  sauto.
  sauto.
Qed.

Lemma remove_dec_in2  {A: Type} (A_dec: forall (x y: A), { x = y } + { x <> y }) (x: A):
  forall (l: list A),
  forall (e: A), In e l -> e <>x -> In e (remove_dec A_dec x l).
  induction l; simpl; intros; auto.
  destruct (A_dec x a).
  sauto.
  sauto.
Qed.

(**)


Fixpoint replace_dec
  {A: Type}
  (A_dec: forall (x y: A), { x = y } + { x <> y })
  (e: A)
  (r: list A)
  (l: list A) :=
  match l with
  | nil => nil
  | hd::tl =>
      match A_dec hd e with
      | left _ => r ++ replace_dec A_dec e r tl
      | right _ => hd::(replace_dec A_dec e r tl)
      end
  end.

Lemma replace_dec_eq {A: Type}
  (A_dec: forall (x y: A), { x = y } + { x <> y })
  (e: A)
  (r: list A): forall (l: list A),
    In e l -> incl r (replace_dec A_dec e r l).
  induction l; simpl; intros; auto.
  sauto.
  inversion_clear H.
  subst a.
  destruct (A_dec e e).
  apply incl_appl.
  apply incl_refl.
  sauto.
  destruct (A_dec a e).
  apply incl_appl.
  apply incl_refl.
  sauto.
Qed.  

Lemma replace_dec_neq {A: Type}
  (A_dec: forall (x y: A), { x = y } + { x <> y })
  (e: A)
  (r: list A): forall (l: list A),
    forall (x: A),
    In x l -> x <> e -> In x (replace_dec A_dec e r l).
  induction l; simpl; intros; auto.
  inversion_clear H.
  destruct (A_dec a e).
  sauto.
  subst a.
  sauto.
  destruct (A_dec a e).
  subst a.
  apply in_or_app.
  sauto.
  sauto.
Qed.

Lemma replace_dec_eq_remove_eq_dec {A: Type}
  (A_dec: forall (x y: A), { x = y } + { x <> y })
  (e: A): forall (l: list A),
    replace_dec A_dec e [] l = remove_dec A_dec e l.
  induction l; simpl; intros; auto.
  sauto.
Qed.  

(**)
Fixpoint zip {A B} (l1: list A) (l2: list B): list (A * B) :=
  match l1 with
  | nil => nil
  | hd1::tl1 =>
      match l2 with
      | nil => nil
      | hd2::tl2 => (hd1, hd2)::(zip tl1 tl2)
      end
  end.

Fixpoint unzip {A B} (l: list (A * B)): list A * list B :=
  match l with
  | nil => (nil, nil)
  | (hd1, hd2)::tl =>
      let (tl1, tl2) := unzip tl in
      (hd1::tl1, hd2::tl2)
  end.

Lemma unzip_fst_snd {A B}: forall (l: list (A * B)),
    unzip l = (fst (unzip l), snd (unzip l)).
  induction l; simpl; intros; auto.
  rewrite IHl; simpl.
  destruct a; simpl; auto.
Qed.  
  
Lemma unzip_unfold {A B}: forall (tl: list (A * B)) hd1 hd2,
    unzip ((hd1, hd2)::tl) = (hd1::(fst (unzip tl)), hd2::(snd (unzip tl))).
  induction tl.
  intuition.
  intros.
  destruct a.
  rewrite (IHtl a b).
  sauto.
Qed.

Fixpoint funpow (n: nat) {A} (f: A -> A) (x: A): A :=
  match n with
  | 0 => x
  | S n => funpow n f (f x)
  end.

(*****************************************)

(* 
a model gives semantics to:
1) variables
2) functions
3) predicates
*)

Record InhabitedType : Type := {
                                set :> Set;
                                witness: exists v: set, True;
                              }.


Record Model {Value: InhabitedType}: Type := {
    var_sem: string -> Value;
    fn_sem: string -> list Value -> Value;
    pred_sem: string -> list Value -> Prop;
  }.

(*
  updating a model (changing variables mapping), together with variant / invariant lemmas
 *)

Definition updated_model {V} (m: @Model V) (x: string) (v: V): @Model V :=
  {| var_sem := fun s => match string_dec x s with | left _ => v | right _ => var_sem m s end ;
    fn_sem := fn_sem m;
    pred_sem := pred_sem m ;
  |}.

Lemma updated_model_var_sem1 {V} (m: @Model V) (x: string) (v: V):
  forall y, x <> y -> var_sem (updated_model m x v) y = var_sem m y.
  destruct m.
  simpl; intros.
  sauto.
Qed.

Lemma updated_model_var_sem2 {V} (m: @Model V) (x: string) (v: V):
  forall y, x = y -> var_sem (updated_model m x v) y = v.
  destruct m.
  simpl; intros.
  sauto.
Qed.

Lemma updated_model_fn_sem {V} (m: @Model V) (x: string) (v: V):
  forall f l,
    fn_sem m f l = fn_sem (updated_model m x v) f l.
  destruct m.
  simpl; intros.
  sauto.
Qed.

Lemma updated_model_pred_sem {V} (m: @Model V) (x: string) (v: V):
  forall p l,
    pred_sem m p l <-> pred_sem (updated_model m x v) p l.
  destruct m.
  simpl; intros.
  sauto.
Qed.

(*****************************************)

(* term datatype + helper lemma/function *)

Inductive term: Set :=
| var: string -> term
| fn: string -> list term -> term.

Fixpoint sum_list_nat (l: list nat) : nat :=
  match l with
  | nil => 0
  | hd::tl => hd + sum_list_nat tl
  end.

Lemma sum_list_nat_elt: forall (l: list nat) (x: nat),
    In x l -> sum_list_nat l >= x.
  induction l; simpl; intro; intuition.
  subst a; lia.
  generalize (IHl _ H0); intros; intuition; lia.
Qed.

Fixpoint term_measure (t: term): nat :=
  match t with
  | var s => 1
  | fn s l => 1 + sum_list_nat (map term_measure l)
  end.

Lemma term_measure_elt: forall s l x,
    In x l ->
    term_measure x < term_measure (fn s l).
intro; induction l; intuition.
inversion H.
subst x; simpl.
lia.
simpl.
generalize (IHl x H0); simpl; intros; auto.
lia.
Qed.

(* Maybe the most interesting point of this formalization: terms
  cannot be used with the usual inductive type mechanism of Coq. So we
   need to redefine the recursion scheme. The key point is that all
  terms explored are subterms [!not clear!]<possibly interesting point
  for more generic induction scheme>. Furthermore, we define a lemma
  for rewriting the induction lemma applied to each constructors
  (avoiding too much verbose coq unfolding/reduction). In this case,
  the lemmas in WfExtensionality are instrumentals. *)

Program Fixpoint term_recursion
  (t: term) 
  (P: term -> Type)
  (P_var: forall s: string, P (var s))
  (P_fn: forall (s: string) (l: list term),
      (forall x, In x l -> P x) -> P (fn s l))
  { measure (term_measure t) } : P t :=
  match t with
  | var s => P_var s
  | fn s l => P_fn s l (fun x H => term_recursion x P P_var P_fn)
  end.
Next Obligation.  
apply term_measure_elt; auto.
Qed.

(* the rewriting lemma for both constructors *)
Lemma term_recursion_var P P_var P_fn: forall s,
    term_recursion (var s) P P_var P_fn = P_var s.
auto.
Qed.

Lemma term_recursion_fn P P_var P_fn: forall s l,
    term_recursion (fn s l) P P_var P_fn = P_fn s l (fun x H => term_recursion x P P_var P_fn).
  intros.
  unfold term_recursion.
  unfold term_recursion_func.
  rewrite WfExtensionality.fix_sub_eq_ext.
  simpl.
  auto.
Qed.

(* We will need a variant of map which covers the extra hypothesis
  that the term belongs to the function arguments *)

Program Fixpoint map_term {A: Set} (l: list term) (P: forall x: term, In x l -> A) { struct l }: list A :=
  match l with
  | nil => nil
  | hd::tl => (P hd _)::(@map_term A tl (fun x H => P x _))
  end.
Next Obligation.
  intuition.
Qed.
Next Obligation.
  intuition.
Qed.

(* specialization of the term_recursion rewriting rule *)
Lemma term_recursion_map_term_var {A: Set} (f_var: string -> A) (f_fn: string -> list A -> A): forall s,
    term_recursion (var s) (fun t => A) f_var (fun s l H => f_fn s (map_term l H)) =
    f_var s.
  intros.
  rewrite term_recursion_var.
  auto.
Qed.
  
  Lemma term_recursion_map_term_fn {A: Set} (f_var: string -> A) (f_fn: string -> list A -> A): forall s l,
    term_recursion (fn s l) (fun t => A) f_var (fun s l H => f_fn s (map_term l H)) =
    f_fn s (map (fun t => term_recursion t (fun t => A) f_var (fun s l H => f_fn s (map_term l H))) l).
  intros.
  rewrite term_recursion_fn.
  f_equal.
  generalize l; clear l.
  induction l; simpl; intros; intuition.
  f_equal.
  rewrite <- IHl.
  auto.
  Qed.

(*
  decidability of equiality on terms
*)  

Program Definition term_eq_dec (t1: term) : forall t2, { t1 = t2 } + { t1 <> t2 }:=
  term_recursion t1 (fun t => forall t2, { t = t2 } + { t <> t2 }) _ _.
Next Obligation.
  destruct t2.
  generalize (string_dec s s0); intro H0; inversion_clear H0.
  subst; intuition.
  right; injection; intuition.
  right; intro H0; inversion_clear H0.
Defined.
Next Obligation.
  destruct t2.
  right; intro H0; inversion_clear H0.
  generalize (string_dec s s0); intro H0; inversion_clear H0.
  generalize (list_dec l H l0); intro H0; inversion_clear H0.
  subst s l; intuition.
  right; injection; intuition.
  right; injection; intuition.
Defined.

(* Evaluation of a term given a model, together with rewriting lemmas
  for constructors *)

Definition eval {V} (m: @Model V) (t: term) : V :=
  term_recursion t (fun _ => V) (var_sem m) (fun s l H => (fn_sem m) s (map_term l H)).

Lemma eval_var {V} (m: @Model V):
  forall s,
    eval m (var s) = var_sem m s. 
sauto.
Qed.

Lemma eval_fn {V} (m: @Model V):
  forall f l,
    eval m (fn f l) = fn_sem m f (map (eval m) l).
  intros.
  unfold eval.
  apply term_recursion_map_term_fn.
Qed.

(* 
   free variables of a terms: set of variables in a term
 *)

Definition term_free_vars (t: term): list string :=
  term_recursion t (fun t => list string) (fun s => s::nil) (fun s l H => List.concat (map_term l H)).

(* just an helper for list of arguments *)
Lemma term_free_vars_fn: forall s l,
    term_free_vars (fn s l) = List.concat (map term_free_vars l).
  intros.
  unfold term_free_vars.
  apply term_recursion_map_term_fn with (f_fn := fun s l => List.concat l).
Qed.

(*
  if two models have the same values for the free variables of a term => there evaluations are the same
*)
Lemma free_vars_term_sem {V}:
  forall (t: term) (m1 m2: @Model V),
    (forall s, List.In s (term_free_vars t) -> var_sem m1 s = var_sem m2 s) ->
    (forall f l, fn_sem m1 f l = fn_sem m2 f l) ->
    eval m1 t = eval m2 t.
  intro.
  apply (term_recursion t); simpl; intros.
  do 2 rewrite eval_var.
  sauto.
  do 2 rewrite eval_fn.
  rewrite H1.
  f_equal.
  apply map_ext_in; intros.
  apply H; auto; intros.
  apply H0.
  rewrite term_free_vars_fn.
  rewrite <- flat_map_concat_map; rewrite in_flat_map; exists a; auto.
Qed.

Lemma free_vars_terms_sem {V}:
  forall (l: list term) (m1 m2: @Model V),
    (forall s, List.In s (List.concat (map term_free_vars l)) -> var_sem m1 s = var_sem m2 s) ->
    (forall f l, fn_sem m1 f l = fn_sem m2 f l) ->
    map (eval m1) l = map (eval m2) l.
  induction l; simpl; intros; auto.
  rewrite (free_vars_term_sem a m1 m2); auto.
  rewrite (IHl m1 m2); auto.
  intros; apply H; intuition.
  intros; apply H; intuition.
Qed.


(**************************************)

(*
  First order formulas 
  ==> we skip the type parameterization (inlining fol in Atom)
  ==> equality defined as a primitive (rather than a predicate)
*)

Inductive formula: Set :=
| ftrue: formula
| ffalse: formula
| Atom: string -> list term -> formula
| Eq: term -> term -> formula
| Not: formula -> formula
| And: formula -> formula -> formula
| Or: formula -> formula -> formula
| Imp: formula -> formula -> formula
| Iff: formula -> formula -> formula
| Forall: string -> formula -> formula
| Exists: string -> formula -> formula.

Notation "x1 == x2" := (Eq x1 x2) (at level 70, right associativity).
Notation "~~ b" := (Not b) (at level 75, right associativity).
Notation "b1 //\\ b2" := (And b1 b2) (at level 80, right associativity).
Notation "b1 \\// b2" := (Or b1 b2) (at level 85, right associativity).
Notation "b1 ==> b2" := (Imp b1 b2) (at level 90, right associativity).
Notation "b1 <=> b2" := (Iff b1 b2) (at level 90, right associativity).
Notation "'F' x , f" := (Forall x f) (at level 100, right associativity).
Notation "'E' x , f" := (Exists x f) (at level 100, right associativity).

(* formula equality decidability *)

Definition formula_dec: forall (f1 f2: formula), {f1 = f2} + {f1 <> f2}.
  decide equality.
  apply List.list_eq_dec; apply term_eq_dec.
  apply string_dec.
  apply term_eq_dec.
  apply term_eq_dec.
  apply string_dec.
  apply string_dec.
Defined.

(* semantics of models *)

Fixpoint models {V} (m: @Model V) (f: formula): Prop :=
  match f with
  | ftrue => True
  | ffalse => False
  | Atom P args => pred_sem m P (map (eval m) args)
  | Eq t1 t2 => eval m t1 = eval m t2
  | Not f => ~ models m f
  | And f1 f2 => models m f1 /\ models m f2
  | Or f1 f2 => models m f1 \/ models m f2
  | Imp f1 f2 => models m f1 -> models m f2
  | Iff f1 f2 => models m f1 <-> models m f2
  | Forall x f => forall v: V,
      models (updated_model m x v) f
  | Exists x f => exists v: V,
      models (updated_model m x v) f
  end.

Notation "m '|=' f" := (@models _ m f) (at level 150, right associativity).

(*

  This axiom might be removed if:
1) add equality decidability to inhabitedtype
2) change the domain of predicate semantics in model from prop to true

*)

Axiom models_classical:
  forall {V} (m: @Model V) (f: formula),
    (m |= f) \/ ~ (m |= f).

(* 
   free variables of a terms: set of variables in a term
*)

Fixpoint formula_free_vars (f: formula) : list string :=
    match f with
  | ftrue => nil
  | ffalse => nil
  | Atom P args => List.concat (map term_free_vars args)
  | Eq t1 t2 => term_free_vars t1 ++ term_free_vars t2
  | Not f => formula_free_vars f
  | And f1 f2 => formula_free_vars f1 ++ formula_free_vars f2
  | Or f1 f2 => formula_free_vars f1 ++ formula_free_vars f2
  | Imp f1 f2 => formula_free_vars f1 ++ formula_free_vars f2
  | Iff f1 f2 => formula_free_vars f1 ++ formula_free_vars f2
  | Forall x f => List.remove string_dec x (formula_free_vars f)
  | Exists x f => List.remove string_dec x (formula_free_vars f)
  end.

(*
  for all models with same valuation over free variables variable valuation,
  semantics is preserved
*)

Lemma formula_vars_term_sem {V}:
  forall (f: formula) (m1 m2: @Model V),
    (forall s, List.In s (formula_free_vars f) -> var_sem m1 s = var_sem m2 s) ->
    (forall f l, fn_sem m1 f l = fn_sem m2 f l) ->
    (forall p l, pred_sem m1 p l = pred_sem m2 p l) ->
    (m1 |= f) <-> (m2 |= f).

  (*
[ TODO: clean this proof ... ]
   *)
  
induction f; simpl; intros; auto.

intuition.

intuition.

rewrite <- H1.
rewrite (free_vars_terms_sem l m1 m2); auto.
intuition.
rewrite (free_vars_term_sem t m2 m1); auto.
rewrite (free_vars_term_sem t0 m2 m1); auto.
intuition.  
intros; rewrite H; intuition.
intros; rewrite H; intuition.

rewrite IHf; auto.
intuition.

rewrite (IHf1 m1 m2); auto.
rewrite (IHf2 m1 m2); auto.
intuition.
intros; apply H; intuition.
intros; apply H; intuition.

rewrite (IHf1 m1 m2); auto.
rewrite (IHf2 m1 m2); auto.
intuition.
intros; apply H; intuition.
intros; apply H; intuition.

rewrite (IHf1 m1 m2); auto.
rewrite (IHf2 m1 m2); auto.
intuition.
intros; apply H; intuition.
intros; apply H; intuition.

rewrite (IHf1 m1 m2); auto.
rewrite (IHf2 m1 m2); auto.
intuition.
intros; apply H; intuition.
intros; apply H; intuition.

split; intros; auto.
(**)
rewrite <- (IHf (updated_model m1 s v) (updated_model m2 s v)); auto.
intros.
destruct (string_dec s s0); auto.
rewrite (updated_model_var_sem2 m1 s v); auto.
rewrite (updated_model_var_sem2 m2 s v); auto.
rewrite (updated_model_var_sem1 m1 s v); auto.
rewrite (updated_model_var_sem1 m2 s v); auto.
apply H; auto.
apply remove_In_diff; auto.
(**)
rewrite (IHf (updated_model m1 s v) (updated_model m2 s v)); auto.
intros.
destruct (string_dec s s0); auto.
rewrite (updated_model_var_sem2 m1 s v); auto.
rewrite (updated_model_var_sem2 m2 s v); auto.
rewrite (updated_model_var_sem1 m1 s v); auto.
rewrite (updated_model_var_sem1 m2 s v); auto.
apply H; auto.
apply remove_In_diff; auto.

split; intros; auto.
(**)
inversion_clear H2.
exists x.
rewrite <- (IHf (updated_model m1 s x) (updated_model m2 s x)); auto.
intros.
destruct (string_dec s s0); auto.
rewrite (updated_model_var_sem2 m1 s x); auto.
rewrite (updated_model_var_sem2 m2 s x); auto.
rewrite (updated_model_var_sem1 m1 s x); auto.
rewrite (updated_model_var_sem1 m2 s x); auto.
apply H; auto.
apply remove_In_diff; auto.
(**)
inversion_clear H2.
exists x.
rewrite (IHf (updated_model m1 s x) (updated_model m2 s x)); auto.
intros.
destruct (string_dec s s0); auto.
rewrite (updated_model_var_sem2 m1 s x); auto.
rewrite (updated_model_var_sem2 m2 s x); auto.
rewrite (updated_model_var_sem1 m1 s x); auto.
rewrite (updated_model_var_sem1 m2 s x); auto.
apply H; auto.
apply remove_In_diff; auto.

Qed.

(************************************************************)

(* definition of validity: all models satisfy the formula *)

Definition is_valid (f: formula) : Prop :=
  forall {V} (m: @Model V),
    m |= f.

Notation "'|-' f" := (is_valid f) (at level 150, right associativity).
  
(************************************************************)

(*** Module for Ocaml extraction  ***)

Module Type ProofSystem.

  Parameter Thm: Set.
  Parameter concl: Thm -> formula.
           
  (*  if |- p ==> q and |- p then |- q                                         *)
  Parameter modusponens: Thm -> Thm -> Thm.

  (*  if |- p then |- forall x. p                                              *)
  Parameter gen: string -> Thm -> Thm.
  
  (*  |- p ==> (q ==> p)                                                       *)
  Parameter axiom_addimp: formula -> formula -> Thm.
  
  (*  |- (p ==> q ==> r) ==> (p ==> q) ==> (p ==> r)                           *)
  Parameter axiom_distribimp: formula -> formula -> formula -> Thm.
  
  (*  |- ((p ==> false) ==> false) ==> p                                       *)
  Parameter axiom_doubleneg: formula -> Thm.
  
  (*  |- (forall x. p ==> q) ==> (forall x. p) ==> (forall x. q)               *)
  Parameter axiom_allimp: string -> formula -> formula -> Thm.
    
  (*  |- p ==> forall x. p                            [x not free in p]        *)
  Parameter axiom_impall: string -> formula -> Thm.
  
  (*  |- exists x. x = t                              [x not free in t]        *)
  Parameter axiom_existseq: string -> term -> Thm.

  (*  |- t = t                                                                 *)
  Parameter axiom_eqrefl: term -> Thm.

  (*  |- t = s ==> s = t *)
  Parameter axiom_eqcomm: term -> term -> Thm.

  (*  |- t = s ==> s = r ==> t = r *)
  Parameter axiom_eqtrans: term -> term -> term -> Thm.
  
  (*  |- s1 = t1 ==> ... ==> sn = tn ==> f(s1,..,sn) = f(t1,..,tn)             *)
  Parameter axiom_funcong: string -> list term -> list term -> Thm.
  
  (*  |- s1 = t1 ==> ... ==> sn = tn ==> P(s1,..,sn) ==> P(t1,..,tn)           *)
  Parameter axiom_predcong: string -> list term -> list term -> Thm.
  
  (*  |- (p <=> q) ==> p ==> q                                                 *)
  Parameter axiom_iffimp1: formula -> formula -> Thm.
  
  (*  |- (p <=> q) ==> q ==> p                                                 *)
  Parameter axiom_iffimp2: formula -> formula -> Thm.

  (*  |- (p ==> q) ==> (q ==> p) ==> (p <=> q)                                 *)
  Parameter axiom_impiff: formula -> formula -> Thm.

  (*  |- true <=> (false ==> false)                                            *)
  Parameter axiom_true: Thm.
  
  (*  |- ~p <=> (p ==> false)                                                  *)
  Parameter axiom_not: formula -> Thm.
  
  (*  |- p /\ q <=> (p ==> q ==> false) ==> false                              *)
  Parameter axiom_and: formula -> formula -> Thm.
  
  (*  |- p \/ q <=> ~(~p /\ ~q)                                                *)
  Parameter axiom_or: formula -> formula -> Thm.

  (*  |- (exists x. p) <=> ~(forall x. ~p)                                     *)
  Parameter axiom_exists: string -> formula -> Thm.

End ProofSystem.

(* Implementation for a Module of type ProofSystem *)

(* we defined those outside because we will reuse them later *)
Definition Thm := { f: formula | |- f }.

Definition concl (thm: Thm): formula :=
  match thm with
  | exist _ x _ => x
  end.

Definition prf (thm: Thm): |- concl thm :=
    match thm with
    | exist _ _ p => p
    end.

Definition mkThm f prf: Thm := exist is_valid f prf.

Definition mkThm2 {f} ( prf: |- f ) : Thm := exist is_valid f prf.

Program Definition T_Thm := exist is_valid ftrue _.
Next Obligation.
  sauto.
Qed.

(** all the lemmas to be used in the implementation **)
(** comming in two flavors
1) with  (|- f) goals / hypothesis
2) with Thm dependent type of provable formulas [required for extraction]
**)

Lemma modusponens {p q: formula}:
  forall (A: |- p ==> q)
         (B: |- p),
    (|- q).
  unfold is_valid.
  intros.
  generalize (A V m); clear A; intro A.
  generalize (B V m); clear B; intro B.
  apply A.
  auto.
Qed.

(* the extraction leads to "empty" code ... *)
Extraction "test1.ml" modusponens.

Program Definition modusponens_thm (thm1 thm2: Thm): Thm :=
  match concl thm1 with
  | Imp f1 f2 =>
      match formula_dec f1 thm2 with
      | left _ => (**) mkThm f2 _
      | right _ => T_Thm
      end
  | _ => T_Thm
  end.
Next Obligation.
  destruct thm1; destruct thm2.
  eapply modusponens.
  simpl in Heq_anonymous0.
  subst x.
  apply i.
  apply i0.
Qed.

(* .. hence the need of the dependent type for generating genuine OCaml code *)
Extraction "test2.ml" modusponens_thm.

(**)

Lemma lemma_gen {p: formula}:
  forall (H: |- p) x,
    (|- Forall x p).
  unfold is_valid.
  intros.
  simpl; intros.
  apply H.
Qed.

Definition gen_thm (x: string) (thm: Thm): Thm := mkThm _ (lemma_gen (prf thm) x).

(**)

Lemma lemma_addimp (p q: formula):
  |- p ==> (q ==> p).
  red.
  intros.
  intro.
  intro.
  auto.
Qed.

Program Definition addimp_thm (p q: formula): Thm := mkThm _ (lemma_addimp p q).

(**)

Lemma lemma_distribimp (p q r: formula):
      |- (p ==> q ==> r) ==> (p ==> q) ==> (p ==> r).
  red; intros.
  intro.
  intro.
  intro.
  apply H.
  apply H1.
  apply H0.
  apply H1.
Qed.

Program Definition distribimp_thm (p q r: formula): Thm :=
  mkThm _ (lemma_distribimp p q r).

(**)

Lemma lemma_doubleneg (p : formula):
      |- ((p ==> ffalse) ==> ffalse) ==> p.
  red; intros.
  intro.
  destruct (models_classical m p); auto.
  generalize (H H0); intros; intuition.
Qed.

Program Definition doubleneg_thm (p: formula): Thm :=
  mkThm _ (lemma_doubleneg p).

(**)

Lemma lemma_allimp x (p q: formula) :
  |- (F x, p ==> q) ==> (F x, p) ==> (F x, q).
  red; intros.
  intro.
  intro.
  intro.
  apply H.
  apply H0.
Qed.

Program Definition allimp_thm (x: string) (p q: formula): Thm :=
  mkThm _ (lemma_allimp x p q).

(**)

Lemma lemma_impall x (p: formula):
  ~ In x (formula_free_vars p) ->
  |- p ==> Forall x p.
  intros.
  red; intros.
  intro.
  intro.
  rewrite (formula_vars_term_sem _ _ m); auto.
  intros; auto.
  destruct (string_dec x s); auto.
  subst x; intuition.
  rewrite updated_model_var_sem1; auto.
Qed.

Program Definition impall_thm (x: string) (p: formula): Thm :=
  match List.in_dec string_dec x (formula_free_vars p) with
  | left _ => T_Thm
  | right _ => mkThm _ (lemma_impall x p _)
  end.

(**)

Lemma lemma_existseq x (t: term):
  ~ In x (term_free_vars t) ->
      |- Exists x (var x == t).
  red; intros.
  exists (eval m t).
  simpl.
  rewrite eval_var.
  rewrite updated_model_var_sem2; auto.  
  rewrite (free_vars_term_sem t (updated_model m x (eval m t)) m); auto; intros.
  rewrite updated_model_var_sem1; auto.  
  intro; subst x; intuition.
Qed.

Program Definition existseq_thm (x: string) (t: term) : Thm :=
  match List.in_dec string_dec x (term_free_vars t) with
  | left _ => T_Thm
  | right _ => mkThm _ (lemma_existseq x t _)
  end.

(**)

Lemma lemma_eqrefl (t: term):
  |- t == t.
  red; intros.
  red; auto.
Qed.

Program Definition eqrefl_thm (t: term): Thm :=
  mkThm _ (lemma_eqrefl t).    


(**)

Lemma lemma_eqcomm (t s: term):
  |- t == s ==> s == t.
  red; intros.
  red; auto.
Qed.

Program Definition eqcomm_thm (t s: term): Thm :=
  mkThm _ (lemma_eqcomm t s).    

(**)

Lemma lemma_eqtrans (t s r: term):
  |- t == s ==> s == r ==> t == r.
  red; intros.
  sauto.
Qed.

Program Definition eqtrans_thm (t s r: term): Thm :=
  mkThm _ (lemma_eqtrans t s r).    

(**)

Lemma lemma_iffimp1 (p q: formula):
      |- (p <=> q) ==> p ==> q.
  red; intros.
  intro.
  inversion_clear H.  
  intuition.
Qed.

Program Definition  iffimp1_thm (p q: formula) : Thm :=
  mkThm _ (lemma_iffimp1 p q).

(**)

Lemma lemma_iffimp2 (p q: formula):
      |- (p <=> q) ==> q ==> p.
  red; intros.
  intro.
  inversion_clear H.  
  intuition.
Qed.

Program Definition iffimp2_thm (p q: formula) : Thm :=
  mkThm _ (lemma_iffimp2 p q).

(**)

Lemma lemma_impiff (p q: formula):
      |- (p ==> q) ==> (q ==> p) ==> (p <=> q).
  red; intros.
  intro.
  intro.
  split; intuition.
Qed.  

Program Definition impiff_thm (p q: formula) : Thm :=
  mkThm _ (lemma_impiff p q).

(**)

Lemma lemma_true:
      |- ftrue <=> (ffalse ==> ffalse).
  red; intros.
  split; intro.
  intro; intuition.
  red; auto.
Qed.

Program Definition true_thm: Thm :=
  mkThm _ lemma_true.

(**)

Lemma lemma_not (p: formula):
      |- ~~ p <=> (p ==> ffalse) .
  red; intros.
  split; intros; intuition.
Qed.

Program Definition not_thm (p: formula): Thm := 
  mkThm _ (lemma_not p).

(**)

Lemma lemma_and (p q: formula):
      |- p //\\ q <=> (p ==> q ==> ffalse) ==> ffalse.
  red; intros.
  split; intuition.
  inversion_clear H.
  intro.
  apply H; intuition.
  destruct (models_classical m (p //\\ q)); intuition.
  assert False; intuition.
  apply H.
  intros.
  apply H0.
  split; intuition.
Qed.

Program Definition and_thm (p q: formula): Thm :=
  mkThm _ (lemma_and p q).

(**)

Lemma lemma_or (p q: formula):
      |- p \\// q <=> ~~(~~ p //\\ ~~ q).
  split; intros.
  intro.
  inversion_clear H0.
  inversion_clear H; intuition.
  destruct (models_classical m (p \\// q)); intuition.
  assert False; intuition.
  apply H.
  split; intro; apply H0.
  left; intuition.
  right; intuition.
Qed.  

Program Definition or_thm (p q: formula): Thm := 
  mkThm _ (lemma_or p q).

(**)

Lemma lemma_exists x (p: formula):
      |- (E x, p) <=> ~~(F x, ~~p).
  red; intros.
  split; intro.
  intro.
  inversion_clear H.
  apply (H0 x0).
  sauto.
  destruct (models_classical m (E x, p)); intuition.
  cut False; intuition.
  apply H.
  sauto.
Qed.

Program Definition exists_thm (x: string) (p: formula): Thm := 
  mkThm _ (lemma_exists x p).

(* need to cleanup this part 
   this is the first instance where we need to deal with
   inferrence rules over formulas with a variable number of elements
   ( p_0 -> ... -> p_n -> ____ )
   dependent types helps simplifying the formalization
*)
  
Lemma l1 (l: list( term * term)) {V} (m: @Model V):
    (forall x, In x l -> let (x1, x2) := x in eval m x1 = eval m x2) ->
    let (l1, l2) := unzip l in
    map (eval m) l1 = map (eval m) l2.
  induction l; simpl; intros; auto.
  destruct a.
  rewrite unzip_fst_snd.
  simpl.
  rewrite (H (t, t0)); intuition.
  cutrewrite (map (eval m) (fst (unzip l)) =
                map (eval m) (snd (unzip l))
             ); intuition.
  rewrite unzip_fst_snd in IHl.
  rewrite IHl; intuition.
  apply H; intuition.
Qed.

Lemma l1_2 (l: list( term * term)) {V} (m: @Model V):
    (forall x, In x l -> let (x1, x2) := x in eval m x1 = eval m x2) ->    
    map (eval m) (fst (unzip l)) = map (eval m) (snd (unzip l)).
  intros.
  generalize (l1 _ _ H); intros.
  rewrite unzip_fst_snd in H0; intuition.
Qed.  

Lemma l2 (l: list( term * term)) {V} (m: @Model V) f:
  (forall x, In x l -> let (x1, x2) := x in eval m x1 = eval m x2) ->
  let (l1, l2) := unzip l in
  m |= fn f l1 == fn f l2.  
  intros.
  rewrite unzip_fst_snd.
  red.
  do 2 rewrite eval_fn.
  rewrite l1_2; intuition.
Qed.

Lemma eq_fun (l: list( term * term)) {V} (m: @Model V) f:
  (forall x, In x l -> let (x1, x2) := x in eval m x1 = eval m x2) ->
  let (l1, l2) := unzip l in
  m |= fn f l1 == fn f l2.  
  intros.
  rewrite unzip_fst_snd.
  red.
  do 2 rewrite eval_fn.
  rewrite l1_2; intuition.
Qed.

Lemma eq_pred (l: list( term * term)) {V} (m: @Model V) P:
  (forall x, In x l -> let (x1, x2) := x in eval m x1 = eval m x2) ->
  let (l1, l2) := unzip l in
  m |= Atom P l1 ==> Atom P l2.  
  intros.
  rewrite unzip_fst_snd.
  red.
  rewrite l1_2; intuition.
Qed.

(* This is the generic definition (easy to use in proof) *)
Fixpoint formulas_conj (l: list formula) : formula :=
  match l with
  | nil => ftrue
  | hd::tl => hd //\\ formulas_conj tl
  end.

(* for sake of computing over dependent type, we might prefer this version *)
Fixpoint formulas_conj_alt (l: list formula) : formula :=
  match l with
  | nil => ftrue
  | hd::nil => hd
  | hd::tl => hd //\\ formulas_conj_alt tl
  end.

(****)

(* and we prove all the required equivalences *)
Lemma formulas_conj_alt_eq_satisfibility {V} (m: @Model V):
  forall l,
    (m |= formulas_conj l) <-> (m |= formulas_conj_alt l).
  induction l; simpl.
  intuition.
  split; intros.
  destruct l.
  intuition.
  split.
  intuition.
  rewrite <- IHl.
  intuition.
  split.
  destruct l; intuition.
  inversion_clear H; auto.
  rewrite IHl.
  destruct l; intuition.
  sauto.
  inversion_clear H; auto.
Qed.  

Lemma formulas_conj_alt_eq_satisfibility2 {V} (m: @Model V):
  forall ccl l,
    (m |= formulas_conj l ==> ccl) <-> (m |= formulas_conj_alt l ==> ccl).
  intros.
  split; intros; intro.
  
  cut (m |= formulas_conj l).
  sauto.
  rewrite formulas_conj_alt_eq_satisfibility; auto.

  cut (m |= formulas_conj_alt l).
  sauto.
  rewrite <- formulas_conj_alt_eq_satisfibility; auto.

Qed.
  
Lemma formulas_conj_alt_eq_validity:
  forall l,
    (|- formulas_conj l) <-> (|- formulas_conj_alt l).
  intros; split; intros.
  red; intros.
  generalize (H _ m); intros.
  rewrite <- formulas_conj_alt_eq_satisfibility; auto.
  red; intros.
  generalize (H _ m); intros.
  rewrite formulas_conj_alt_eq_satisfibility; auto.
Qed.  

Lemma formulas_conj_alt_eq_validity2:
  forall ccl l,
    (|- formulas_conj l ==> ccl) <-> (|- formulas_conj_alt l ==> ccl).
  intros; split; intros.
  red; intros.
  generalize (H _ m); intros.
  rewrite <- formulas_conj_alt_eq_satisfibility2; auto.
  red; intros.
  generalize (H _ m); intros.
  rewrite formulas_conj_alt_eq_satisfibility2; auto.
Qed.  

(****)


Lemma conj_forall_eq_m (l: list formula) {V} (m: @Model V):
  (forall x, In x l -> m |= x) <->
    (m |= formulas_conj l).
  induction l; simpl; intros.
  split; intros; intuition.
  sauto.
Qed.

Lemma conj_forall_eq_v (l: list formula):
  (forall x, In x l -> |- x) <->
    (|- formulas_conj l).
  induction l; simpl; intros.
  split; intros; sauto.  
  split; simpl; intros; auto.
  generalize (H a); intros; sauto.
  inversion_clear H0.  
  subst x; red; intros.
  generalize (H _ m); intro H1; inversion_clear H1; auto.
  inversion_clear IHl.
  apply H2; auto.
  red; intros.
  generalize (H _ m); intros; sauto.
Qed.

Lemma conj_forall_eq (l: list (term * term)) {V} (m: @Model V):
  (forall x, In x l -> let (x1, x2) := x in eval m x1 = eval m x2) <->
    (m |= formulas_conj (map (fun x => fst x == snd x) l)).
  induction l; simpl; intros; auto.
  sauto.
  split; simpl; intros; auto.
  sauto.
  sauto.
Qed.
  
Fixpoint formulas_imp (l: list formula) (ccl: formula): formula :=
  match l with
  | nil => ccl
  | hd::tl => hd ==> formulas_imp tl ccl
  end.

Lemma build_conj_imp_equiv {V} (m: @Model V) (l: list formula) (ccl: formula):
  (m |= formulas_conj l ==> ccl) <-> (m |= formulas_imp l ccl).
  induction l; simpl; intros; auto.  
  sauto.
  rewrite <- IHl.
  sauto.
Qed.  

Lemma lemma_fun_congruence_aux f (l: list (term * term)):
  let (l1, l2) := unzip l in
  |- formulas_imp (map (fun x => fst x == snd x) l) (fn f l1 == fn f l2).
  rewrite unzip_fst_snd.
  red; intros.
  rewrite <- build_conj_imp_equiv.
  intro.
  generalize (conj_forall_eq l m); intros.
  generalize (eq_fun l m f); intros.
  rewrite unzip_fst_snd in H1.
  apply H1.
  sauto.
Qed.

Lemma lemma_funcong_ f (l: list (term * term)):
  let (l1, l2) := unzip l in
  |- formulas_imp (map (fun x => fst x == snd x) l) (fn f l1 == fn f l2).
  rewrite unzip_fst_snd.
  red; intros.
  rewrite <- build_conj_imp_equiv.
  intro.
  generalize (conj_forall_eq l m); intros.
  generalize (eq_fun l m f); intros.
  rewrite unzip_fst_snd in H1.
  apply H1.
  sauto.
Qed.

Lemma lemma_funcong f (l: list (term * term)):
      |- formulas_imp (map (fun x => fst x == snd x) l) (fn f (fst (unzip l)) == fn f (snd (unzip l))).
  red; intros.
  rewrite <- build_conj_imp_equiv.
  intro.
  generalize (conj_forall_eq l m); intros.
  generalize (eq_fun l m f); intros.
  rewrite unzip_fst_snd in H1.
  apply H1.
  sauto.
Qed.

Program Definition funcong_thm (f: string) (lhs rhs: list term) : Thm :=
  mkThm _ (lemma_funcong f (zip lhs rhs)).

(**)

Lemma lemma_predcong_ P (l: list (term * term)):
  let (l1, l2) := unzip l in
  |- formulas_imp (map (fun x => fst x == snd x) l) (Atom P l1 ==> Atom P l2).
  rewrite unzip_fst_snd.
  red; intros.
  rewrite <- build_conj_imp_equiv.
  intro.
  generalize (conj_forall_eq l m); intros.
  generalize (eq_pred l m P); intros.
  rewrite unzip_fst_snd in H1.
  apply H1.
  sauto.
Qed.

Lemma lemma_predcong P (l: list (term * term)):
  |- formulas_imp (map (fun x => fst x == snd x) l) (Atom P (fst (unzip l)) ==> Atom P (snd (unzip l))).
  red; intros.
  rewrite <- build_conj_imp_equiv.
  intro.
  generalize (conj_forall_eq l m); intros.
  generalize (eq_pred l m P); intros.
  rewrite unzip_fst_snd in H1.
  apply H1.
  sauto.
Qed.

Program Definition predcong_thm (P: string) (lhs rhs: list term) : Thm :=
    mkThm _ (lemma_predcong P (zip lhs rhs)).

(* making is_valid Opaque (making sure we only reuse the base rules) *)
Opaque is_valid.

(** the lcf kernel as a extractable module **)
  
Module Proven: ProofSystem.

  Definition Thm := Thm.

  Print Thm.
  
  Print exist.

  Check exist.
  
  Definition concl (thm: Thm): formula := concl thm.
  
  Definition prf (thm: Thm): |- concl thm := prf thm.

  Definition mkThm f prf: Thm := mkThm f prf.
  
  Definition T_Thm := T_Thm.
  
  (*  if |- p ==> q and |- p then |- q                                         *)
  Definition modusponens (thm1 thm2: Thm): Thm := modusponens_thm thm1 thm2.    
  (*  if |- p then |- forall x. p                                              *)
  Definition gen (x: string) (thm: Thm): Thm := gen_thm x thm.
  
  (*  |- p ==> (q ==> p)                                                       *)
  Definition axiom_addimp (p q: formula): Thm := addimp_thm p q.
    
  (*  |- (p ==> q ==> r) ==> (p ==> q) ==> (p ==> r)                           *)
  Definition axiom_distribimp (p q r: formula): Thm := distribimp_thm p q r.
  
  (*  |- ((p ==> false) ==> false) ==> p                                       *)
  Definition axiom_doubleneg (p: formula): Thm := doubleneg_thm p.
  
  (*  |- (forall x. p ==> q) ==> (forall x. p) ==> (forall x. q)               *)
  Definition axiom_allimp (x: string) (p q: formula): Thm := allimp_thm x p q.
    
  (*  |- p ==> forall x. p                            [x not free in p]        *)
  Definition axiom_impall (x: string) (p: formula): Thm := impall_thm x p.
   
                                                                     
  (*  |- exists x. x = t                              [x not free in t]        *)
  Definition axiom_existseq (x: string) (t: term) : Thm := existseq_thm x t.
  
  (*  |- t = t                                                                 *)
  Definition axiom_eqrefl (t: term): Thm := eqrefl_thm t.
  
  (*  |- t = s ==> s |- t *)
  Definition axiom_eqcomm (t s: term): Thm := eqcomm_thm t s.

  (*  |- t = s ==> s |- r ==> t = r *)
  Definition axiom_eqtrans (t s r: term): Thm := eqtrans_thm t s r.
  
  (*  |- s1 = t1 ==> ... ==> sn = tn ==> f(s1,..,sn) = f(t1,..,tn)             *)
  
  Definition axiom_funcong (f: string) (lhs rhs: list term) : Thm := funcong_thm f lhs rhs.
    
  (*  |- s1 = t1 ==> ... ==> sn = tn ==> P(s1,..,sn) ==> P(t1,..,tn)           *)
  Definition axiom_predcong (P: string) (lhs rhs: list term) : Thm := predcong_thm P lhs rhs.
    
  (*  |- (p <=> q) ==> p ==> q                                                 *)
  Definition axiom_iffimp1 (p q: formula) : Thm := iffimp1_thm p q.
  
  (*  |- (p <=> q) ==> q ==> p                                                 *)
  Definition axiom_iffimp2 (p q: formula) : Thm := iffimp2_thm p q.
    
  (*  |- (p ==> q) ==> (q ==> p) ==> (p <=> q)                                 *)
  Definition axiom_impiff (p q: formula) : Thm := impiff_thm p q.
  
  (*  |- true <=> (false ==> false)                                            *)
  Definition axiom_true: Thm := true_thm.
  
  (*  |- ~p <=> (p ==> false)                                                  *)
  Definition axiom_not (p: formula): Thm := not_thm p.
  
  (*  |- p /\ q <=> (p ==> q ==> false) ==> false                              *)
  Definition axiom_and (p q: formula): Thm := and_thm p q.

  (*  |- p \/ q <=> ~(~p /\ ~q)                                                *)
  Definition axiom_or (p q: formula): Thm := or_thm p q.
  
  (*  |- (exists x. p) <=> ~(forall x. ~p)                                     *)
  Definition axiom_exists (x: string) (p: formula): Thm := exists_thm x p.
  
End Proven.

(* the original objective of this formalization *)
Extraction "harrison.ml" Proven.

(************************************************************)

(******* further propositional lemmas *********)

Lemma imp_refl p: |- p ==> p.
  generalize (lemma_distribimp p (p ==> p) p); intros.
  generalize (lemma_addimp p (p ==> p)); intros.
  generalize (modusponens H H0); intros.
  generalize (lemma_addimp p p); intros.
  apply (modusponens H1 H2).
Qed.  
  
Lemma imp_undiplicate {p q} (H: |- p ==> p ==> q): |- p ==> q.
  generalize (lemma_distribimp p p q); intros.
  generalize (modusponens H0 H); intros.
  generalize (imp_refl p); intros.
  apply (modusponens H1 H2).
Qed.

Lemma add_assum p {q} (H: |- q): |- p ==> q.
  generalize (lemma_addimp q p); intros.
  apply (modusponens H0 H).
Qed.

Lemma imp_add_assum p {q r} (H: |- q ==> r): |- (p ==> q) ==> (p ==> r).
  generalize (lemma_distribimp p q r); intros.
  generalize (add_assum p H); intros.
  apply (modusponens H0 H1).
Qed.

Lemma imp_trans {p q r} (H0: |- p ==> q) (H1: |- q ==> r): |- p ==> r.
  apply (modusponens
           (imp_add_assum p H1)
           H0
        ).
Qed.

Lemma imp_insert q {p r} (H: |- p ==> r): |- p ==> q ==> r.
  generalize (lemma_addimp r q); intros.
  apply (imp_trans H H0).
Qed.

Lemma imp_swap {p q r} (H: |- p ==> q ==> r): |- q ==> p ==> r.
  generalize (lemma_addimp q p); intro H0.
  generalize (lemma_distribimp p q r); intro H1.
  generalize (modusponens H1 H); intro H2.
  apply (imp_trans H0 H2).
Qed.

Lemma imp_trans_th p q r: |- (q ==> r) ==> (p ==> q) ==> (p ==> r).
  apply ( imp_trans
            (lemma_addimp (q ==> r) p)
            (lemma_distribimp p q r)
        ).
Qed.

Lemma imp_add_concl r {p q} (H: |- p ==> q): |- (q ==> r) ==> (p ==> r).
  apply (
      modusponens
        (imp_swap (imp_trans_th p q r))
        H
    ).
Qed.

Lemma imp_swap_th p q r: |- (p ==> q ==> r) ==> (q ==> p ==> r).
  apply ( imp_trans
            (lemma_distribimp p q r)
            (imp_add_concl
               (p ==> r)
               (lemma_addimp q p)
            )
        ).
Qed.

Lemma imp_swap2 {p q r s t u} (H: |- (p ==> q ==> r) ==> (s ==> t ==> u)): |- (q ==> p ==> r) ==> (t ==> s ==> u).
  apply (
      imp_trans
        (imp_swap_th q p r)
        (imp_trans H (imp_swap_th s t u))
    ).
Qed.

Lemma right_mp {p q r} (H0: |- p ==> q ==> r) (H1: |- p ==> q): |- p ==> r.
  apply (imp_undiplicate (imp_trans H1 (imp_swap H0))).
Qed.

Lemma iff_imp1 {p q} (H: |- p <=> q): |- p ==> q.
  generalize (lemma_iffimp1 p q); intros.
  apply (modusponens H0 H).
Qed.

Lemma iff_imp2 {p q} (H: |- p <=> q): |- q ==> p.
  generalize (lemma_iffimp2 p q); intros.
  apply (modusponens H0 H).
Qed.

Lemma imp_antisym {p q} (H0: |- p ==> q) (H1: |- q ==> p): |- p <=> q.
  apply (modusponens
           (modusponens
              (lemma_impiff p q)
              H0
           )
           H1
        ).
Qed.

Lemma right_doubleneg {p q} (H: |- p ==> (q ==> ffalse) ==> ffalse ): |- p ==> q.
  generalize (lemma_doubleneg q); intro.
  generalize (imp_trans H H0); intro.
  apply H1.
Qed.

Lemma ex_falso p: |- ffalse ==> p.
  apply (right_doubleneg
           (lemma_addimp ffalse (p ==> ffalse))
        ).
Qed.

Lemma imp_trans2 {p q r s} (H0: |- p ==> q ==> r) (H1: |- r ==> s): |- p ==> q ==> s.
  generalize (
      imp_add_assum p
        (modusponens
           (imp_trans_th q r s)
           H1
        )
    ); intro.
  apply (modusponens H H0).
Qed.

Lemma truth: |- ftrue.
  apply (modusponens
           (iff_imp2 lemma_true)
           (imp_refl ffalse)
        ).
Qed.

(*

second instance with inference rules over formulas with variable
number of elements.

We need to make is_valid transparent 
- could we avoid it ?
- should we move those definition above

*)

Transparent is_valid.

Lemma tuple_formulas_conj: forall
    (l: list formula)
    (t: tuple (map (fun x => |- x) l)),
    |- formulas_conj l.
  induction l; simpl; intros; auto.
  apply truth.
  inversion_clear t.
  red; intros.
  split.
  apply thd.
  intuition.
Qed.

Lemma imp_trans_chain_aux :
  forall (l: list formula)
         {p} (Hs: tuple (map (fun x => is_valid x) (map (fun x => p ==> x) l)))
         {r} (H: |- formulas_conj l ==> r),
    |- p ==> r.
  intros.  
  
  cut (|- p ==> formulas_conj l).
  intros.
  apply (imp_trans H0 H).
  
  generalize (tuple_formulas_conj _ Hs); intros.

  red; intros.
  intro.
  generalize (H0 _ m); intros.
  rewrite <- conj_forall_eq_m in H2.
  rewrite <- (@conj_forall_eq_m l _ m).
  intros.
  generalize (H2 (p ==>x) ); intros.
  apply H4; auto.
  apply in_f_map; auto.
Qed.

Lemma imp_trans_chain :
  forall (l: list formula)
         {p} (Hs: tuple (map (fun x => is_valid x) (map (fun x => p ==> x) l)))
         {r} (H: |- formulas_imp l r),
    |- p ==> r.
  intros.
  eapply imp_trans_chain_aux.
  apply Hs.
  red; intros.
  generalize (H _ m); intros.
  rewrite build_conj_imp_equiv.
  auto.
Qed.

Opaque is_valid.

(**)

Lemma imp_truefalse p q: |- (q ==> ffalse) ==> p ==> (p ==> q) ==> ffalse.
  apply ( imp_trans
            (imp_trans_th p q ffalse)
            (imp_swap_th
               (p ==> q)
               p
               ffalse
            )
        ).
Qed.

Lemma imp_mono p p' q q': |- (p' ==> p) ==> (q ==> q') ==> (p ==> q) ==> p' ==> q'.
  generalize (imp_trans_th (p ==> q) (p' ==> q) (p' ==> q')); intro H1.
  generalize (imp_trans_th p' q q'); intro H2.
  generalize (imp_swap (imp_trans_th p' p q)); intro H3.
  apply (imp_trans H3 (imp_swap (imp_trans H2 H1))).
Qed.


Lemma contrapos {p q} (H: |- p ==> q): |- ~~ q ==> ~~ p.
  apply (imp_trans
           (imp_trans
              (iff_imp1 (lemma_not q))
              (imp_add_concl ffalse H)
           )
           (iff_imp2 (lemma_not p))
    ).
Qed.

Lemma and_left p q: |- p //\\ q ==> p.
  generalize (imp_add_assum p (lemma_addimp ffalse q)); intro H1.
  generalize (right_doubleneg (imp_add_concl ffalse H1)); intro H2.
  apply (imp_trans (iff_imp1 (lemma_and p q)) H2).
Qed.

Lemma and_right p q: |- p //\\ q ==> q.
  generalize (lemma_addimp (q ==> ffalse) p); intro H1.
  generalize (right_doubleneg (imp_add_concl ffalse H1)); intro H2.
  apply (imp_trans
           (iff_imp1 (lemma_and p q))
           H2
        ).
Qed.

(* once again, I think it make it clear that the lemmas  
   set is not properly set ...
*)

Transparent is_valid.

Lemma conjths {l: list formula}:
  forall
    p, In p l ->
              |- (formulas_conj l) ==> p.
  intros.
  red; intros.
  intro.
  rewrite <- conj_forall_eq_m in H0.
  sauto.
Qed.

Opaque is_valid.

(**)

Lemma and_pair p q: |- p ==> q ==> p //\\ q.
  generalize (iff_imp2 (lemma_and p q)); intro H1.
  generalize (imp_swap_th (p ==> q ==> ffalse) q ffalse); intro H2.
  generalize (imp_add_assum p (imp_trans2 H2 H1)); intro H3.
  apply (modusponens
           H3
           (imp_swap (imp_refl (p ==> q ==> ffalse)))
        ).
Qed.

Lemma shunt {p q r} (H: |- p //\\ q ==> r): |- p ==> q ==> r.
  generalize (fold_right); intro.
  apply (modusponens
           (imp_add_assum p (imp_add_assum q H))
           (and_pair p q)
        ).
Qed.

Lemma unshunt {p q r} (H: |- p ==> q ==> r): |- p //\\ q ==> r.
  
  generalize (tcons (and_left p q) (tcons (and_right p q) tnil)); intro.
  
  apply (@imp_trans_chain [p; q] (p //\\ q)); intros.

  eapply tcons.
  apply and_left.
  eapply tcons.
  apply and_right.
  apply tnil.

  auto.
Qed.


(************************************************************)
(****** p. 506 => tableau procedure ********)

Definition theorem_tuple (l: list formula) : Type := tuple (map (fun x => is_valid x) l).

Lemma iff_def p q: |- (p <=> q) <=> ((p ==> q) //\\ (q ==> p)).
  assert (theorem_tuple [(p <=> q) ==> (p ==> q); (p <=> q) ==> (q ==> p)]).
  eapply tcons.
  apply (lemma_iffimp1 p q).
  eapply tcons.
  apply (lemma_iffimp2 p q).
  apply tnil.
  generalize (@imp_trans_chain [(p ==> q); (q ==> p)] (p <=> q) X ((p ==> q) //\\ (q ==> p))); intros.  
  generalize (and_pair (p ==> q) (q ==> p)); intros.
  generalize (unshunt (lemma_impiff p q)); intros.
  apply imp_antisym.
  apply H.
  simpl.
  apply H0.
  apply H1.
Qed.

Definition iff_refl (p: formula): |- p <=> p.
  exact (modusponens (modusponens (lemma_impiff p p) (imp_refl p)) (imp_refl p)).
Qed.


(***)

(* looks like this is a corner case for program ... 
   no clue of where all the obligations are coming from ...
*)
(*
Program Definition expand_connective (f: formula) : { fm: formula | |- f <=> fm } :=
  match f with
  | true => @exist formula (fun x => |- true <=> x) (false ==> false) lemma_true

  | ~~ p => @exist formula (fun x => |- ~~p <=> x) (p ==> false) (lemma_not p)

  | p => @exist formula (fun x => |- p <=> x) p (iff_refl p)
  end.
*)

Definition expand_connective (f: formula): Thm :=
  match f with
  | ftrue => mkThm _ lemma_true
  | ~~ p => mkThm _ (lemma_not p)
  | p //\\ q => mkThm _ (lemma_and p q)
  | p \\// q => mkThm _ (lemma_or p q)
  | p <=> q => mkThm _ (iff_def p q)
  | E x, p => mkThm _ (lemma_exists x p)
  | _ => T_Thm
  end.

Definition negatef (f: formula): formula :=
  match f with
  | p ==> ffalse => p
  | p => p ==> ffalse
  end.

Definition negativef (f: formula): bool :=
  match f with
  | p ==> ffalse => true
  | p => false
  end.

(*** experimental ***)

(*
  definition to perform transformation: thm <-> |- p
*)
Program Definition prfthm_2 {p q} (H: (|- p) -> |- q) (thm: Thm): Thm :=
  match formula_dec p (concl thm) with
  | left Heq => mkThm q _
  | right _ => T_Thm
  end.
Next Obligation.
  apply H.
  sauto. (* I absolutely do not understand ... *)
Qed.

Program Definition prfthm_3 {p q r} (H: (|- p) -> (|- q) -> |-r ) (thm_p thm_q: Thm): Thm :=
  match formula_dec p (concl thm_p) with
  | left Heq1 =>
      match formula_dec q (concl thm_q) with
      | left Heq2 => mkThm r (H _ _)
      | right _ => T_Thm
      end
  | right _ => T_Thm
  end.
Next Obligation.
  sauto. (* I absolutely do not understand ... *)
Qed.

Program Definition prfthm_4 {p q r s} (H: (|- p) -> (|- q) -> (|- r)-> |- s ) (thm_p thm_q thm_r: Thm): Thm :=
  match formula_dec p (concl thm_p) with
  | left Heq1 =>
      match formula_dec q (concl thm_q) with
      | left Heq2 =>
          match formula_dec r (concl thm_r) with
          | left Heq2 => mkThm s (H _ _ _)
          | right _ => T_Thm
      end
      | right _ => T_Thm
      end
  | right _ => T_Thm
  end.
Next Obligation.
  sauto. (* I absolutely do not understand ... *)
Qed.
Next Obligation.
  sauto. (* I absolutely do not understand ... *)
Qed.
Next Obligation.
  sauto. (* I absolutely do not understand ... *)
Qed.
Next Obligation.
  sauto. (* I absolutely do not understand ... *)
Qed.
  
(* usage *)

Definition iff_imp1_thm (t: Thm (* |- p <=> q *)): Thm (* |- p ==> q *) :=
  match concl t with
  | p <=> q => prfthm_2 (@iff_imp1 p q) t
  | _ => T_Thm
  end.

Definition iff_imp2_thm (t: Thm (* |- p <=> q *)): Thm  (* |- q ==> p *) :=
  match concl t with
  | p <=> q => prfthm_2 (@iff_imp2 p q) t
  | _ => T_Thm
  end.

Definition imp_add_concl_thm r (t: Thm (* |- p ==> q *)) : Thm (* |- (q ==> r) ==> (p ==> r) *) :=
  match concl t with
  | p ==> q => prfthm_2 (@imp_add_concl r p q) t
  | _ => T_Thm
  end.

Definition eliminate_connective f : Thm :=
  if negb (negativef f) then
    iff_imp1_thm (expand_connective f)
  else
    imp_add_concl_thm ffalse (iff_imp2_thm (expand_connective (negatef f))).

(* TODO *)

(*
Definition p: formula := Atom "p" [].
Definition q: formula := Atom "q" [].
Definition r: formula := Atom "r" [].
Axiom p_iff_q: |- p <=> q.
Definition p_iff_q_thm := mkThm2 p_iff_q.
Eval lazy in (concl p_iff_q_thm).
Definition p_imp_q_thm := iff_imp1_thm p_iff_q_thm.
Eval lazy in (concl p_imp_q_thm).
Definition q_imp_p_thm := iff_imp2_thm p_iff_q_thm.
Eval lazy in (concl q_imp_p_thm).
Eval lazy in (concl (imp_add_concl_thm r p_imp_q_thm)).
Definition f := p <=> q ==> ~~ r.
Eval lazy in (concl (eliminate_connective f)).
*)
               
(************************************************************)

(******* FOL lemmas *************)

(* FOL lemmas *)
Definition eq_sym (s t: term): |- (s == t) ==> (t == s) := lemma_eqcomm s t.

Definition eq_trans (s t u: term): |- (s == t) ==> (t == u) ==> (s == u) := lemma_eqtrans s t u.

(*to continue*)

(************************************************************)

(********* interactive proof style *********)

(* the dependent type *)
Definition Justification (hypos: list formula) (conclusion: formula) :=  |- formulas_conj_alt hypos ==> conclusion.

Notation "hyps '|--' ccl" := (Justification hyps ccl) (at level 150, right associativity).

(* the datatype *)

Record goal: Type := {
    hypothesises: list formula;
    ccl: formula;
    justification: hypothesises |-- ccl
  }.

Lemma close_goal (g: goal) (t: tuple (map (fun x => |- x) (hypothesises g) )): |- ccl g.
  destruct g.
  simpl in t; simpl.
  generalize (tuple_formulas_conj _ t); intros.
  apply (modusponens justification0).
  rewrite <- formulas_conj_alt_eq_validity; auto.
Qed.

Definition closed_goal (g: goal): Prop := (List.length (hypothesises g)) = 0.
Lemma closed_goal_empty_hypo (g: goal) (H: closed_goal g):  hypothesises g = [].
  strivial use: length_zero_iff_nil unfold: closed_goal, hypothesises.
Qed.
  
Lemma closed_goal_ccl (g: goal):
  closed_goal g ->
      |- ccl g.  
  intros.
  generalize (closed_goal_empty_hypo _ H); intros.
  hauto use: justification, truth, @modusponens unfold: hypothesises, formulas_conj_alt, ccl.
Qed.

(* solving a subgoal 

given
(1) |- p_0 /\ ... /\ p_i /\ ... -> p_n -> g
(2) |- p_i

we can remove the p_i
(3) |- p_0 /\ ... /\ p_n -> g

rmq: surprising how we mess in the lemma with the order of inference rule:

 (2) (3) 
---------
   (1)

but here: (2) -> (1) -> (3)

[need to clarify this point]

*)

Lemma solved_hypothesis {l: list formula} {ccl: formula} {p: formula}:
  forall
    (H: |- p)
    (H1: l |-- ccl)
    ,  (remove_dec formula_dec p l) |-- ccl.
  intros.
  red; red in H1.
  rewrite <- formulas_conj_alt_eq_validity2.
  rewrite <- formulas_conj_alt_eq_validity2 in H1.
  
  red; intros.
  intro.
  rewrite <- conj_forall_eq_m in H0.
  cut ( m |= formulas_conj l); intuition.
  apply H1; intuition.
  rewrite <- conj_forall_eq_m.
  intros.
  clear H1.
  destruct (formula_dec x p).
  sauto.
  apply H0.
  apply remove_dec_in2; auto.
Qed.  

Program Definition solve_hypothesis (g: goal) {p} (H: |- p): goal :=
  {|
    hypothesises:= remove_dec formula_dec p (hypothesises g);
    ccl := ccl g;
    justification := solved_hypothesis H (justification g)
  |}.

(*  this is a generalization of above *)
(*
given
|- p_0 /\ ... /\ p_i /\ ... /\ p_n -> g
|- q_0 /\ ... /\ q_m -> p_i

we can replace p_i by the q_0, ..., q_m
|- p_0 /\ ... /\ q_0 /\ ... /\ q_m /\ p_n -> g

same remarque as above

We also provide the alternative

given
|- p_0 /\ ... /\ p_i /\ ... /\ p_n -> g
|- q_0 -> ... -> q_m -> p_i

we can replace p_i by the q_0, ..., q_m
|- p_0 /\ ... /\ q_0 /\ ... /\ q_m /\ p_n -> g

*)

Lemma formulas_conj_incl_m {V} (m: @Model V) (l1 l2: list formula):
  incl l1 l2 ->
  (m |= formulas_conj l2) -> m |= formulas_conj l1.
  intros.
  rewrite <- conj_forall_eq_m.
  rewrite <- conj_forall_eq_m in H0.
  intros.
  apply H0.
  sauto.
Qed.

Lemma generalize_implication
  {l1: list formula} {ccl1: formula}
  {l2: list formula} {ccl2: formula}  
  :
  forall
    (H1: l1 |-- ccl1)
    (H2: l2 |-- ccl2)
    , (replace_dec formula_dec ccl2 l2 l1) |-- ccl1.
  intros.
  red in H1; red in H2; red.
  
  rewrite <- formulas_conj_alt_eq_validity2.
  rewrite <- formulas_conj_alt_eq_validity2 in H1.
  rewrite <- formulas_conj_alt_eq_validity2 in H2.

  red; intros.
  intro.
  generalize (H1 _ m); intro.
  cut (m |= formulas_conj l1).
  sauto.
  generalize (H2 _ m); intro.
  clear H1 H2 H0.
  rewrite <- conj_forall_eq_m.
  intros.
  destruct (formula_dec x ccl2).
  subst x.
  cut (m |= formulas_conj l2).
  sauto.
  generalize (replace_dec_eq formula_dec ccl2 l2 l1 H0); intros.
  apply (formulas_conj_incl_m _ _ _ H1).
  sauto.
  generalize (replace_dec_neq formula_dec ccl2 l2 l1 _ H0 n); intros.
  generalize (@conj_forall_eq_m  (replace_dec formula_dec ccl2 l2 l1) _ m).
  sauto.
Qed.

Program Definition apply_to_goal (g: goal)
  {l_hyps: list formula} {l_ccl: formula}
  (H: |- formulas_conj l_hyps ==> l_ccl): goal :=
  {|
    hypothesises:= (replace_dec formula_dec l_ccl l_hyps (hypothesises g));
    ccl := ccl g;
    justification := generalize_implication (justification g) H
  |}.

Lemma generalize_implication2
  {l1: list formula} {ccl1: formula}
  {l2: list formula} {ccl2: formula}  
  :
  forall
    (H1: l1 |-- ccl1)
    (H2: |- formulas_imp l2 ccl2),
    (replace_dec formula_dec ccl2 l2 l1) |-- ccl1.
  intros.
  red in H1; red.
  apply generalize_implication; auto.
  red.
  rewrite <- formulas_conj_alt_eq_validity2.
  red; intros.
  rewrite build_conj_imp_equiv.
  apply H2; auto.
Qed.
  
Program Definition apply_to_goal2 (g: goal)
  {l_hyps: list formula} {l_ccl: formula}
  (H: |- formulas_imp l_hyps l_ccl): goal :=
  {|
    hypothesises:= (replace_dec formula_dec l_ccl l_hyps (hypothesises g));
    ccl := ccl g;
    justification := generalize_implication2 (justification g) H
  |}.

Extraction "harrison.ml" Proven.

(* check *)
Lemma solved_hypothesis2 {l: list formula} {ccl: formula} {p: formula}:
  forall
    (H: |- p)
    (H1: l |-- ccl),
    (remove_dec formula_dec p l) |-- ccl.
  strivial use: @solved_hypothesis.
Qed.

(***********)

(* just for testing *)

#[arguments(raw)] Elpi Command cmd.
Elpi Accumulate File "harrison.elpi".
Elpi Typecheck.
Elpi Export cmd.

#[arguments(raw)] Elpi Command tac.
Elpi Accumulate File "harrison.elpi".
Elpi Typecheck.
Elpi Export cmd.

Elpi cmd (|- ftrue).
cmd "x y" => y / z.


Lemma l {p q}: |- (p <=> q) ==> p.
  red; intros.
  elpi tac.
Abort.

