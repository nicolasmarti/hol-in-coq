Require Import List.
Import ListNotations.
Require Import String.
Require Import Lia.
From Hammer Require Import Tactics.
Require Import Coq.Program.Wf.

Open Scope string_scope.
Open Scope list_scope.

(************)

Program Fixpoint list_dec {A: Set} (l1: list A) (A_dec: forall a1, In a1 l1 -> forall a2, { a1 = a2 } + { a1 <> a2 }) (l2: list A) { struct l1 }: { l1 = l2 } + { l1 <> l2 } :=
  match l1 with
  | nil => _
  | hd::tl => _ (@list_dec A tl _)
  end.
Next Obligation.
  destruct l2; simpl; auto.
  right; intro H; inversion H.
Defined.
Next Obligation.
  destruct l2 ;simpl; auto.
  right; intro H; inversion H.
  assert (In hd (hd::tl)) by intuition.
  generalize (A_dec _ H a); intro H1; inversion_clear H1.
  subst a; generalize (x l2); intro H0; inversion_clear H0.
  subst l2; left; intuition.
  right; simpl; injection.
  auto.
  right; injection; intuition.
Defined.
Next Obligation.
  intuition.
Defined.

(*****************************************)

Record InhabitedType : Type := {
                                S :> Set;
                                witness: exists v: S, True;
                              }.

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

(* this is a couple simple rewriting rule that one could use for simplification in lemmas *)
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

(* we are going to need a map variant *)
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

Definition term_free_vars (t: term): list string :=
  term_recursion t (fun t => list string) (fun s => s::nil) (fun s l H => List.concat (map_term l H)).

Lemma term_free_vars_fn: forall s l,
    term_free_vars (fn s l) = List.concat (map term_free_vars l).
  intros.
  unfold term_free_vars.
  apply term_recursion_map_term_fn with (f_fn := fun s l => List.concat l).
Qed.

(**************************************)

Inductive formula: Set :=
| true: formula
| false: formula
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

Definition formula_dec: forall (f1 f2: formula), {f1 = f2} + {f1 <> f2}.
  decide equality.
  apply List.list_eq_dec; apply term_eq_dec.
  apply string_dec.
  apply term_eq_dec.
  apply term_eq_dec.
  apply string_dec.
  apply string_dec.
Defined.

(***************************************)

Record Model {Value: InhabitedType}: Type := {
    var_sem: string -> Value;
    fn_sem: string -> list Value -> Value;
    pred_sem: string -> list Value -> Prop;
  }.

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

Fixpoint models {V} (m: @Model V) (f: formula): Prop :=
  match f with
  | true => True
  | false => False
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

Axiom models_classical:
  forall {V} (m: @Model V) (f: formula),
    (m |= f) \/ ~ (m |= f).

Fixpoint formula_free_vars (f: formula) : list string :=
    match f with
  | true => nil
  | false => nil
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

Lemma remove_In_diff: forall {A: Set} H
                             (l: list A) (x x0: A), x <> x0 -> List.In x l -> List.In x (@List.remove _ H x0 l).
  do 2 intro.
  induction l; simpl; intros; auto.
  inversion_clear H1.
  subst x.
  destruct (H x0 a); intuition.
  destruct (H x0 a); intuition.
Qed.

Lemma formula_vars_term_sem {V}:
  forall (f: formula) (m1 m2: @Model V),
    (forall s, List.In s (formula_free_vars f) -> var_sem m1 s = var_sem m2 s) ->
    (forall f l, fn_sem m1 f l = fn_sem m2 f l) ->
    (forall p l, pred_sem m1 p l = pred_sem m2 p l) ->
    (m1 |= f) <-> (m2 |= f).
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


Definition is_valid (f: formula) : Prop :=
  forall {V} (m: @Model V),
    m |= f.

Notation "'|-' f" := (is_valid f) (at level 150, right associativity).

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

Lemma lemma_gen {p: formula}:
  forall (H: |- p) x,
    (|- Forall x p).
  unfold is_valid.
  intros.
  simpl; intros.
  apply H.
Qed.

Lemma lemma_addimp (p q: formula):
  |- p ==> (q ==> p).
  red.
  intros.
  intro.
  intro.
  auto.
Qed.

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

Lemma lemma_doubleneg (p : formula):
      |- ((p ==> false) ==> false) ==> p.
  red; intros.
  intro.
  destruct (models_classical m p); auto.
  generalize (H H0); intros; intuition.
Qed.

Lemma lemma_allimp x (p q: formula) :
  |- (F x, p ==> q) ==> (F x, p) ==> (F x, q).
  red; intros.
  intro.
  intro.
  intro.
  apply H.
  apply H0.
Qed.

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

Lemma lemma_eqrefl (t: term):
  |- t == t.
  red; intros.
  red; auto.
Qed.

Lemma lemma_iffimp1 (p q: formula):
      |- (p <=> q) ==> p ==> q.
  red; intros.
  intro.
  inversion_clear H.  
  intuition.
Qed.

Lemma lemma_iffimp2 (p q: formula):
      |- (p <=> q) ==> q ==> p.
  red; intros.
  intro.
  inversion_clear H.  
  intuition.
Qed.

Lemma lemma_impiff (p q: formula):
      |- (p ==> q) ==> (q ==> p) ==> (p <=> q).
  red; intros.
  intro.
  intro.
  split; intuition.
Qed.  

Lemma lemma_true:
      |- true <=> (false ==> false).
  red; intros.
  split; intro.
  intro; intuition.
  red; auto.
Qed.

Lemma lemma_not (p: formula):
      |- ~~ p <=> (p ==> false) .
  red; intros.
  split; intros; intuition.
Qed.

Lemma lemma_and (p q: formula):
      |- p //\\ q <=> (p ==> q ==> false) ==> false.
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

(* need to cleanup *)

Fixpoint unzip (l: list (term * term)): list term * list term :=
  match l with
  | nil => (nil, nil)
  | (hd1, hd2)::tl =>
      let (tl1, tl2) := unzip tl in
      (hd1::tl1, hd2::tl2)
  end.

Lemma unzip_fst_snd: forall l,
    unzip l = (fst (unzip l), snd (unzip l)).
  induction l; simpl; intros; auto.
  rewrite IHl; simpl.
  destruct a; simpl; auto.
Qed.  
  
Lemma unzip_unfold: forall tl hd1 hd2,
    unzip ((hd1, hd2)::tl) = (hd1::(fst (unzip tl)), hd2::(snd (unzip tl))).
  induction tl.
  intuition.
  intros.
  destruct a.
  rewrite (IHtl t t0).
  sauto.
Qed.
  
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

Fixpoint formulas_conj (l: list formula) : formula :=
  match l with
  | nil => true
  | hd::tl => hd //\\ formulas_conj tl
  end.

Lemma conj_forall_eq_m (l: list formula) {V} (m: @Model V):
  (forall x, In x l -> m |= x) <->
    (m |= formulas_conj l).
  induction l; simpl; intros.
  split; intros; intuition.
  sauto.
Qed.

Lemma conj_forall_eq_v (l: list formula) {V} (m: @Model V):
  (forall x, In x l -> |- x) <->
    (|- formulas_conj l).
  induction l; simpl; intros.
  split; intros; sauto.  
  split; simpl; intros; auto.
  generalize (H a); intros; sauto.
  inversion_clear H0.  
  subst x; red; intros.
  generalize (H _ m0); intro H1; inversion_clear H1; auto.
  inversion_clear IHl.
  apply H2; auto.
  red; intros.
  generalize (H _ m0); intros; sauto.
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
(*
Lemma build_conj_imp_equiv {V} (m: @Model V) (l: list (term * term)) (ccl: formula):
  (m |= (formulas_conj (map (fun x => fst x == snd x) l)) ==> ccl) <-> (m |= formulas_imp (map (fun x => fst x == snd x) l) ccl).
  induction l; simpl; intros; auto.  
  sauto.
  rewrite <- IHl.
  sauto.
Qed.  
 *)

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

(*** Module for Ocaml extraction  ***)

Module Type ProofSystem.

  Parameter Thm: Set.
  Parameter concl: Thm -> formula.
           
  (*  if |- p ==> q and |- p then |- q                                         *)
  Parameter modus_ponens: Thm -> Thm -> Thm.

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

Module Proven: ProofSystem.

  Definition Thm := { f: formula | |- f }.

  Print exist.

  Check exist.
  
  Definition concl (thm: Thm): formula :=
    match thm with
    | exist _ x _ => x
    end.

  Definition prf (thm: Thm): |- concl thm :=
    match thm with
    | exist _ _ p => p
    end.
  
  Program Definition T_Thm := exist is_valid true _.
  Next Obligation.
    sauto.
  Qed.

  Definition mkThm f prf: Thm := exist is_valid f prf .
  
  (*  if |- p ==> q and |- p then |- q                                         *)
  Program Definition modus_ponens (thm1 thm2: Thm): Thm :=
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
    
  (*  if |- p then |- forall x. p                                              *)
  Program Definition gen (x: string) (thm: Thm): Thm := mkThm _ (lemma_gen (prf thm) x).
  
  (*  |- p ==> (q ==> p)                                                       *)
  Program Definition axiom_addimp (p q: formula): Thm := mkThm _ (lemma_addimp p q).
    
  (*  |- (p ==> q ==> r) ==> (p ==> q) ==> (p ==> r)                           *)
  Program Definition axiom_distribimp (p q r: formula): Thm :=
    mkThm _ (lemma_distribimp p q r).
  
  (*  |- ((p ==> false) ==> false) ==> p                                       *)
  Program Definition axiom_doubleneg (p: formula): Thm :=
    mkThm _ (lemma_doubleneg p).
  
  (*  |- (forall x. p ==> q) ==> (forall x. p) ==> (forall x. q)               *)
  Program Definition axiom_allimp (x: string) (p q: formula): Thm :=
    mkThm _ (lemma_allimp x p q).
    
  (*  |- p ==> forall x. p                            [x not free in p]        *)
  Program Definition axiom_impall (x: string) (p: formula): Thm :=
    match List.in_dec string_dec x (formula_free_vars p) with
    | left _ => T_Thm
    | right _ => mkThm _ (lemma_impall x p _)
    end.
   
                                                                     
  (*  |- exists x. x = t                              [x not free in t]        *)
  Program Definition axiom_existseq (x: string) (t: term) : Thm :=
    match List.in_dec string_dec x (term_free_vars t) with
    | left _ => T_Thm
    | right _ => mkThm _ (lemma_existseq x t _)
    end.
  
  (*  |- t = t                                                                 *)
  Program Definition axiom_eqrefl (t: term): Thm :=
    mkThm _ (lemma_eqrefl t).    
  
  (*  |- s1 = t1 ==> ... ==> sn = tn ==> f(s1,..,sn) = f(t1,..,tn)             *)
  Fixpoint zip (l1 l2: list term): list (term * term) :=
    match l1 with
    | nil => nil
    | hd1::tl1 =>
        match l2 with
        | nil => nil
        | hd2::tl2 => (hd1, hd2)::(zip tl1 tl2)
        end
    end.
  
  Program Definition axiom_funcong (f: string) (lhs rhs: list term) : Thm :=
    mkThm _ (lemma_funcong f (zip lhs rhs)).
    
  (*  |- s1 = t1 ==> ... ==> sn = tn ==> P(s1,..,sn) ==> P(t1,..,tn)           *)
  Program Definition axiom_predcong (P: string) (lhs rhs: list term) : Thm :=
    mkThm _ (lemma_predcong P (zip lhs rhs)).
    
  (*  |- (p <=> q) ==> p ==> q                                                 *)
  Program Definition  axiom_iffimp1 (p q: formula) : Thm :=
    mkThm _ (lemma_iffimp1 p q).
  
  (*  |- (p <=> q) ==> q ==> p                                                 *)
  Program Definition axiom_iffimp2 (p q: formula) : Thm :=
    mkThm _ (lemma_iffimp2 p q).
    
  (*  |- (p ==> q) ==> (q ==> p) ==> (p <=> q)                                 *)
  Program Definition axiom_impiff (p q: formula) : Thm :=
    mkThm _ (lemma_impiff p q).
  
  (*  |- true <=> (false ==> false)                                            *)
  Program Definition axiom_true: Thm :=
    mkThm _ lemma_true.
  
  (*  |- ~p <=> (p ==> false)                                                  *)
  Program Definition axiom_not (p: formula): Thm := 
    mkThm _ (lemma_not p).
  
  (*  |- p /\ q <=> (p ==> q ==> false) ==> false                              *)
  Program Definition axiom_and (p q: formula): Thm :=
    mkThm _ (lemma_and p q).

  (*  |- p \/ q <=> ~(~p /\ ~q)                                                *)
  Program Definition axiom_or (p q: formula): Thm := 
    mkThm _ (lemma_or p q).
  
  (*  |- (exists x. p) <=> ~(forall x. ~p)                                     *)
  Program Definition axiom_exists (x: string) (p: formula): Thm := 
    mkThm _ (lemma_exists x p).
  
End Proven.


Require Import Coq.extraction.ExtrOcamlString.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import ExtrOcamlNatBigInt.

Extraction "harrison.ml" Proven.

(**  **)
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

Lemma right_doubleneg {p q} (H: |- p ==> (q ==> false) ==> false ): |- p ==> q.
  generalize (lemma_doubleneg q); intro.
  generalize (imp_trans H H0); intro.
  apply H1.
Qed.

Lemma ex_falso p: |- false ==> p.
  apply (right_doubleneg
           (lemma_addimp false (p ==> false))
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

Lemma truth: |- true.
  apply (modusponens
           (iff_imp2 lemma_true)
           (imp_refl false)
        ).
Qed.

Inductive tuple: forall (l: list Prop), Type :=
| tnil: tuple nil
| tcons: forall {hd: Prop} (thd: hd) {tl: list Prop} (ttl: tuple tl), tuple (hd::tl).

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

Lemma in_f_map:
  forall {A B: Type} (f: A -> B) (l: list A) (x: A),
    In x l ->
    In (f x) (map f l).
  induction l.
  sauto.
  sauto.
Qed.

(* interesting *)
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

Lemma imp_truefalse p q: |- (q ==> false) ==> p ==> (p ==> q) ==> false.
  apply ( imp_trans
            (imp_trans_th p q false)
            (imp_swap_th
               (p ==> q)
               p
               false
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
              (imp_add_concl false H)
           )
           (iff_imp2 (lemma_not p))
    ).
Qed.

Lemma and_left p q: |- p //\\ q ==> p.
  generalize (imp_add_assum p (lemma_addimp false q)); intro H1.
  generalize (right_doubleneg (imp_add_concl false H1)); intro H2.
  apply (imp_trans (iff_imp1 (lemma_and p q)) H2).
Qed.

Lemma and_right p q: |- p //\\ q ==> q.
  generalize (lemma_addimp (q ==> false) p); intro H1.
  generalize (right_doubleneg (imp_add_concl false H1)); intro H2.
  apply (imp_trans
           (iff_imp1 (lemma_and p q))
           H2
        ).
Qed.


(*
Lemma conjths
 *)

Lemma and_pair p q: |- p ==> q ==> p //\\ q.
  generalize (iff_imp2 (lemma_and p q)); intro H1.
  generalize (imp_swap_th (p ==> q ==> false) q false); intro H2.
  generalize (imp_add_assum p (imp_trans2 H2 H1)); intro H3.
  apply (modusponens
           H3
           (imp_swap (imp_refl (p ==> q ==> false)))
        ).
Qed.

Lemma shunt {p q r} (H: |- p //\\ q ==> r): |- p ==> q ==> r.
  generalize (fold_right); intro.
  apply (modusponens
           (imp_add_assum p (imp_add_assum q H))
           (and_pair p q)
        ).
Qed.

Lemma unshut {p q r} (H: |- p ==> q ==> r): |- p //\\ q ==> r.
  
  generalize (tcons (and_left p q) (tcons (and_right p q) tnil)); intro.
  
  apply (@imp_trans_chain [p; q] (p //\\ q)); intros.

  eapply tcons.
  apply and_left.
  eapply tcons.
  apply and_right.
  apply tnil.

  auto.
Qed.

(******)

(* p. 506 => tableau procedure ~~> Elpi*)

(*** interactive proof style ***)

Record goal: Type := {
    hypothesises: list formula;
    ccl: formula;
    justification: |- formulas_conj hypothesises ==> ccl
  }.

Lemma close_goal (g: goal) (t: tuple (map (fun x => |- x) (hypothesises g) )): |- ccl g.
  destruct g.
  simpl in t; simpl.
  generalize (tuple_formulas_conj _ t); intros.
  apply (modusponens justification0 H).
Qed.

(*
Definition update_goals
             (root: goal)
*)
