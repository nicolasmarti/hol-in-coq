Require Import List.
Require Import String.

Open Scope string_scope.
Open Scope list_scope.

(*****************************************)

Record InhabitedType : Type := {
                                S :> Set;
                                witness: exists v: S, True;
                              }.

(*****************************************)


Inductive term: Set :=
| var: string -> term
| fn: string -> list term -> term.

(* now because we have list of term inside of term definition, we need to redefine our own induction scheme *)

Fixpoint sum_list_nat (l: list nat) : nat :=
  match l with
  | nil => 0
  | hd::tl => hd + sum_list_nat tl
  end.

Require Import Omega.

Lemma sum_list_nat_elt: forall (l: list nat) (x: nat),
    In x l -> sum_list_nat l >= x.
  induction l; simpl; intros; intuition.
  generalize (IHl _ H0); intros; intuition.
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
simpl; simpl in IHl.
inversion_clear H.
subst a; omega.
generalize (IHl x H0); intros; auto.
omega.
Qed.

Require Import Coq.Program.Wf.

Program Fixpoint term_recursion
        (P: term -> Type)
        (P_var: forall s: string, P (var s))
        (P_fn: forall (s: string) (l: list term),
            (forall x, In x l -> P x) -> P (fn s l))
        (t: term) { measure (term_measure t) } : P t :=
  match t with
  | var s => P_var s
  | fn s l => P_fn s l (fun x H => term_recursion P P_var P_fn x)
  end.
Next Obligation.  
apply term_measure_elt; auto.
Qed.

(* this is a couple simple rewriting rule that one could use for simplification in lemmas *)
Lemma term_recursion_var P P_var P_fn: forall s,
    term_recursion P P_var P_fn (var s) = P_var s.
auto.
Qed.

Lemma term_recursion_fn P P_var P_fn: forall s l,
    term_recursion P P_var P_fn (fn s l) = P_fn s l (fun x H => term_recursion P P_var P_fn x).
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
    term_recursion (fun t => A) f_var (fun s l H => f_fn s (map_term l H)) (var s) =
    f_var s.
  intros.
  rewrite term_recursion_var.
  auto.
Qed.
  
  Lemma term_recursion_map_term_fn {A: Set} (f_var: string -> A) (f_fn: string -> list A -> A): forall s l,
    term_recursion (fun t => A) f_var (fun s l H => f_fn s (map_term l H)) (fn s l) =
    f_fn s (map (term_recursion (fun t => A) f_var (fun s l H => f_fn s (map_term l H))) l).
  intros.
  rewrite term_recursion_fn.
  f_equal.
  generalize l; clear l.
  induction l; simpl; intros; intuition.
  f_equal.
  rewrite <- IHl.
  auto.
Qed.
  
(**)

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

Program Definition term_eq_dec (t1: term) : forall t2, { t1 = t2 } + { t1 <> t2 }:=
  term_recursion (fun t => forall t2, { t = t2 } + { t <> t2 }) _ _ t1.
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

(**)


Definition term_semantics
           {Value: InhabitedType}
           (ctxt_var: string -> Value)
           (ctxt_fn: string -> list Value -> Value)
           (t: term): Value :=
  term_recursion (fun t => Value) ctxt_var (fun s l H => ctxt_fn s (map_term l H)) t.

Lemma term_semantics_var
      {Value: InhabitedType}
      (ctxt_var: string -> Value)
      (ctxt_fn: string -> list Value -> Value): forall s,
    term_semantics ctxt_var ctxt_fn (var s) =
    ctxt_var s.
  intros.
  unfold term_semantics.
  apply term_recursion_map_term_var.
Qed.


Lemma term_semantics_fn
      {Value: InhabitedType}
      (ctxt_var: string -> Value)
      (ctxt_fn: string -> list Value -> Value): forall s l,
    term_semantics ctxt_var ctxt_fn (fn s l) =
    ctxt_fn s (map (term_semantics ctxt_var ctxt_fn) l).
  intros.
  unfold term_semantics.
  apply term_recursion_map_term_fn.
Qed.

Definition term_free_vars (t: term): list string :=
  term_recursion (fun t => list string) (fun s => s::nil) (fun s l H => concat (map_term l H)) t.

Lemma term_free_vars_fn: forall s l,
    term_free_vars (fn s l) = concat (map term_free_vars l).
  intros.
  unfold term_free_vars.
  apply term_recursion_map_term_fn with (f_fn := fun s l => concat l).
Qed.

Program Definition term_semantics_free_vars
        {Value: InhabitedType}
        (t: term)
        (ctxt_fn: string -> list Value -> Value)
        (ctxt_var1: string -> Value)
        (ctxt_var2: string -> Value):
        (forall s, List.In s (term_free_vars t) -> ctxt_var1 s = ctxt_var2 s) ->
  @term_semantics Value ctxt_var1 ctxt_fn t = @term_semantics Value ctxt_var2 ctxt_fn t :=
  term_recursion (fun t =>
                    (forall s, List.In s (term_free_vars t) -> ctxt_var1 s = ctxt_var2 s) ->
                    @term_semantics Value ctxt_var1 ctxt_fn t = @term_semantics Value ctxt_var2 ctxt_fn t) _ _ t.
Next Obligation.
cut (ctxt_var1 s = ctxt_var2 s); intuition.
Qed.
Next Obligation.
  do 2 rewrite term_semantics_fn.
  f_equal.
  apply map_ext_in; intros.
  apply H; auto.
  intros.
  apply H0.
  rewrite term_free_vars_fn.
  rewrite <- flat_map_concat_map; rewrite in_flat_map; exists a; auto.
Qed.
  
(*****************************************)

(* this is just really to match the ocaml code on extraction *)

Inductive fol: Set :=
  | R: string -> list term -> fol.

Inductive formula {A: Set}: Set :=
| True: formula
| False: formula
| Atom: A -> formula
| Eq: term -> term -> formula
| Not: formula -> formula
| And: formula -> formula -> formula
| Or: formula -> formula -> formula
| Imp: formula -> formula -> formula
| Iff: formula -> formula -> formula
| Forall: string -> formula -> formula
| Exists: string -> formula -> formula
.


Definition formula_dec: forall (f1 f2: @formula fol), {f1 = f2} + {f1 <> f2}.
  decide equality.
  decide equality.
  apply List.list_eq_dec; apply term_eq_dec.
  apply string_dec.
  apply term_eq_dec.
  apply term_eq_dec.
  apply string_dec.
  apply string_dec.
Defined.

Fixpoint formula_semantics 
         {Value: InhabitedType}
         (ctxt_var: string -> Value)
         (ctxt_fn: string -> list Value -> Value)
         (ctxt_pred: string -> list Value -> Prop)
         (f: @formula fol) : Prop :=
  match f with
  | True => Logic.True
  | False => Logic.False
  | Atom (R P args) => ctxt_pred P (map (term_semantics ctxt_var ctxt_fn) args)
  | Eq t1 t2 => term_semantics ctxt_var ctxt_fn t1 = term_semantics ctxt_var ctxt_fn t2
  | Not f => ~ (formula_semantics ctxt_var ctxt_fn ctxt_pred f)
  | And f1 f2 => (formula_semantics ctxt_var ctxt_fn ctxt_pred f1) /\ (formula_semantics ctxt_var ctxt_fn ctxt_pred f2) 
  | Or f1 f2 => (formula_semantics ctxt_var ctxt_fn ctxt_pred f1) \/ (formula_semantics ctxt_var ctxt_fn ctxt_pred f2) 
  | Imp f1 f2 => (formula_semantics ctxt_var ctxt_fn ctxt_pred f1) -> (formula_semantics ctxt_var ctxt_fn ctxt_pred f2) 
  | Iff f1 f2 => (formula_semantics ctxt_var ctxt_fn ctxt_pred f1) <-> (formula_semantics ctxt_var ctxt_fn ctxt_pred f2)
  | Forall x f => forall (v: Value),
      formula_semantics
        (fun y => match string_dec x y with | left _ => v | right _ => ctxt_var y end)
        ctxt_fn ctxt_pred f
  | Exists x f => exists (v: Value),
      formula_semantics
        (fun y => match string_dec x y with | left _ => v | right _ => ctxt_var y end)
        ctxt_fn ctxt_pred f
  end.

Axiom classical_formula:
  forall {Value: InhabitedType}
         (ctxt_var: string -> Value)
         (ctxt_fn: string -> list Value -> Value)
         (ctxt_pred: string -> list Value -> Prop)
         (f: formula),
    (formula_semantics ctxt_var ctxt_fn ctxt_pred f) \/ ~ (formula_semantics ctxt_var ctxt_fn ctxt_pred f).

Fixpoint formula_free_vars (f: formula) : list string :=
    match f with
  | True => nil
  | False => nil
  | Atom (R P args) => concat (map term_free_vars args)
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
  subst a.
  intuition.
  destruct (H x0 a); intuition.
Qed.

Lemma formula_semantics_free_vars:
  forall
      {Value: InhabitedType}
      (f: formula)
      (ctxt_fn: string -> list Value -> Value)
      (ctxt_pred: string -> list Value -> Prop)
      (ctxt_var1: string -> Value)
      (ctxt_var2: string -> Value)
      (Hyp: forall s, List.In s (formula_free_vars f) -> ctxt_var1 s = ctxt_var2 s),
  (formula_semantics ctxt_var1 ctxt_fn ctxt_pred f) <-> (formula_semantics ctxt_var2 ctxt_fn ctxt_pred f).

  induction f; simpl; intros.

  intuition.
  intuition.

  destruct a.
  cut (map (term_semantics ctxt_var1 ctxt_fn) l = map (term_semantics ctxt_var2 ctxt_fn) l).
  intro H; rewrite H; split; auto.
  apply map_ext_in; intros.
  eapply term_semantics_free_vars.
  intuition.
  eapply Hyp.
  rewrite <- flat_map_concat_map; rewrite in_flat_map; exists a; auto.

  rewrite term_semantics_free_vars with (ctxt_var3 := ctxt_var1) (ctxt_var4 := ctxt_var2).
  rewrite term_semantics_free_vars with (ctxt_var3 := ctxt_var1) (ctxt_var4 := ctxt_var2).
  intuition.
  intros; apply Hyp; apply List.in_or_app; right; auto.
  intros; apply Hyp; apply List.in_or_app; left; auto.

  rewrite IHf with (ctxt_var1 := ctxt_var1) (ctxt_var2 := ctxt_var2); intuition.

  rewrite IHf1 with (ctxt_var1 := ctxt_var1) (ctxt_var2 := ctxt_var2).
  rewrite IHf2 with (ctxt_var1 := ctxt_var1) (ctxt_var2 := ctxt_var2).
  intuition.
  intuition.
  intuition.

  rewrite IHf1 with (ctxt_var1 := ctxt_var1) (ctxt_var2 := ctxt_var2).
  rewrite IHf2 with (ctxt_var1 := ctxt_var1) (ctxt_var2 := ctxt_var2).
  intuition.
  intuition.
  intuition.

  rewrite IHf1 with (ctxt_var1 := ctxt_var1) (ctxt_var2 := ctxt_var2).
  rewrite IHf2 with (ctxt_var1 := ctxt_var1) (ctxt_var2 := ctxt_var2).
  intuition.
  intuition.
  intuition.

  rewrite IHf1 with (ctxt_var1 := ctxt_var1) (ctxt_var2 := ctxt_var2).
  rewrite IHf2 with (ctxt_var1 := ctxt_var1) (ctxt_var2 := ctxt_var2).
  intuition.
  intuition.
  intuition.

  split; intros; intuition.
  rewrite IHf with (ctxt_var2 := (fun y : string => if string_dec s y then v else ctxt_var1 y)); auto.
  intros.
  destruct (string_dec s s0); auto.
  rewrite Hyp; auto.
  apply remove_In_diff; intuition.

  rewrite IHf with (ctxt_var2 := (fun y : string => if string_dec s y then v else ctxt_var2 y)); auto.
  intros.
  destruct (string_dec s s0); auto.
  rewrite Hyp; auto.
  apply remove_In_diff; intuition.

  split; intros; intuition.
  inversion_clear H.
  exists x.
  rewrite IHf with (ctxt_var2 := (fun y : string => if string_dec s y then x else ctxt_var1 y)); auto.
  intros.
  destruct (string_dec s s0); auto.
  rewrite Hyp; auto.
  apply remove_In_diff; intuition.
  inversion_clear H.
  exists x.
  rewrite IHf with (ctxt_var2 := (fun y : string => if string_dec s y then x else ctxt_var2 y)); auto.
  intros.
  destruct (string_dec s s0); auto.
  rewrite Hyp; auto.
  apply remove_In_diff; intuition.
Qed.

(*****************************************)

Module Type ProofSystem.

  Parameter Thm: Set.
  Parameter concl: Thm -> @formula fol.

  Parameter proof:
    forall (thm: Thm)
           {Value: InhabitedType}
           (ctxt_var: string -> Value)
           (ctxt_fn: string -> list Value -> Value)
           (ctxt_pred: string -> list Value -> Prop),
      @formula_semantics Value ctxt_var ctxt_fn ctxt_pred (concl thm).

  (*  if |- p ==> q and |- p then |- q                                         *)
  Parameter modus_ponens: Thm -> Thm -> Thm.

  (*  if |- p then |- forall x. p                                              *)
  Parameter gen: string -> Thm -> Thm.
  
  (*  |- p ==> (q ==> p)                                                       *)
  Parameter axiom_addimp: @formula fol -> @formula fol -> Thm.
  
  (*  |- (p ==> q ==> r) ==> (p ==> q) ==> (p ==> r)                           *)
  Parameter axiom_distribimp: @formula fol -> @formula fol -> @formula fol -> Thm.
  
  (*  |- ((p ==> false) ==> false) ==> p                                       *)
  Parameter axiom_doubleneg: @formula fol -> Thm.
  
  (*  |- (forall x. p ==> q) ==> (forall x. p) ==> (forall x. q)               *)
  Parameter axiom_allimp: string -> @formula fol -> @formula fol -> Thm.
    
  (*  |- p ==> forall x. p                            [x not free in p]        *)
  Parameter axiom_impall: string -> @formula fol -> Thm.
  
  (*  |- exists x. x = t                              [x not free in t]        *)
  Parameter axiom_existseq: string -> term -> Thm.

  (*  |- t = t                                                                 *)
  Parameter axiom_eqrefl: term -> Thm.
  
  (*  |- s1 = t1 ==> ... ==> sn = tn ==> f(s1,..,sn) = f(t1,..,tn)             *)
  Parameter axiom_funcong: string -> list term -> list term -> Thm.
  
  (*  |- s1 = t1 ==> ... ==> sn = tn ==> P(s1,..,sn) ==> P(t1,..,tn)           *)
  Parameter axiom_predcong: string -> list term -> list term -> Thm.
  
  (*  |- (p <=> q) ==> p ==> q                                                 *)
  Parameter axiom_iffimp1: @formula fol -> @formula fol -> Thm.
  
  (*  |- (p <=> q) ==> q ==> p                                                 *)
  Parameter axiom_iffimp2: @formula fol -> @formula fol -> Thm.

  (*  |- (p ==> q) ==> (q ==> p) ==> (p <=> q)                                 *)
  Parameter axiom_impiff: @formula fol -> @formula fol -> Thm.

  (*  |- true <=> (false ==> false)                                            *)
  Parameter axiom_true: Thm.
  
  (*  |- ~p <=> (p ==> false)                                                  *)
  Parameter axiom_not: @formula fol -> Thm.
  
  (*  |- p /\ q <=> (p ==> q ==> false) ==> false                              *)
  Parameter axiom_and: @formula fol -> @formula fol -> Thm.
  
  (*  |- p \/ q <=> ~(~p /\ ~q)                                                *)
  Parameter axiom_or: @formula fol -> @formula fol -> Thm.

  (*  |- (exists x. p) <=> ~(forall x. ~p)                                     *)
  Parameter axiom_exists: string -> @formula fol -> Thm.

End ProofSystem.

Module Proven: ProofSystem.

  Record Impl: Set := mkImpl {
                       concl :> formula;
                       proof: forall 
                           {Value: InhabitedType}
                           (ctxt_var: string -> Value)
                           (ctxt_fn: string -> list Value -> Value)
                           (ctxt_pred: string -> list Value -> Prop),
                           formula_semantics ctxt_var ctxt_fn ctxt_pred concl;
                       }.

  Definition Thm := Impl.

  Program Definition T_Thm := mkImpl True _.
  
  (*  if |- p ==> q and |- p then |- q                                         *)
  Program Definition modus_ponens (thm1 thm2: Thm): Thm :=
    match concl thm1 with
    | Imp f1 f2 =>
      match formula_dec f1 thm2 with
      | left _ => mkImpl f2 _
      | right _ => T_Thm
      end
    | _ => T_Thm
    end.
  Next Obligation.
    generalize (@proof thm1 Value ctxt_var ctxt_fn ctxt_pred); intros.
    generalize (@proof thm2 Value ctxt_var ctxt_fn ctxt_pred); intros.
    rewrite <- Heq_anonymous0 in H.
    simpl in H.
    intuition.
  Qed.
    
  (*  if |- p then |- forall x. p                                              *)
  Program Definition gen (x: string) (thm: Thm): Thm := mkImpl (Forall x thm) _.
  Next Obligation.
    apply (@proof thm Value).
  Qed.
  
  (*  |- p ==> (q ==> p)                                                       *)
  Program Definition axiom_addimp (p q: formula): Thm := mkImpl (Imp p (Imp q p)) _.
    
  (*  |- (p ==> q ==> r) ==> (p ==> q) ==> (p ==> r)                           *)
  Program Definition axiom_distribimp (p q r: formula): Thm :=
    mkImpl (Imp (Imp p (Imp q r)) (Imp (Imp p q) (Imp p r))) _.
  
  (*  |- ((p ==> false) ==> false) ==> p                                       *)
  Program Definition axiom_doubleneg (p: formula): Thm := mkImpl (Imp (Imp (Imp p False) False) p) _.
  Next Obligation.
    generalize (classical_formula ctxt_var ctxt_fn ctxt_pred p); intro H0; inversion_clear H0; auto.
    intuition.
  Qed.  
  
  (*  |- (forall x. p ==> q) ==> (forall x. p) ==> (forall x. q)               *)
  Program Definition axiom_allimp (x: string) (p q: formula): Thm :=
    mkImpl (Imp
              (Forall x (Imp p q))
              (Imp
                 (Forall x p)
                 (Forall x q)
              )
        ) _.
    
  (*  |- p ==> forall x. p                            [x not free in p]        *)
  Program Definition axiom_impall (x: string) (p: formula): Thm :=
    match List.in_dec string_dec x (formula_free_vars p) with
    | left _ => T_Thm
    | right _ => mkImpl (Imp p (Forall x p)) _
    end.
  Next Obligation.
    rewrite formula_semantics_free_vars.
    apply H.
    intros.
    destruct (string_dec x s); auto.
    subst s; contradiction.
  Qed.
  
  (*  |- exists x. x = t                              [x not free in t]        *)
  Program Definition axiom_existseq (x: string) (t: term) : Thm :=
    match List.in_dec string_dec x (term_free_vars t) with
    | left _ => T_Thm
    | right _ => mkImpl (Exists x (Eq (var x) t)) _
    end.
  Next Obligation.
    exists (term_semantics ctxt_var ctxt_fn t).
    rewrite term_semantics_var.
    destruct (string_dec x x); [ idtac | intuition ].
    eapply term_semantics_free_vars; intros.
    destruct (string_dec x s).
    subst s; contradiction.
    auto.
  Qed.

  (*  |- t = t                                                                 *)
  Program Definition axiom_eqrefl (t: term): Thm := mkImpl (Eq t t) _.    
  
  (*  |- s1 = t1 ==> ... ==> sn = tn ==> f(s1,..,sn) = f(t1,..,tn)             *)
  Fixpoint list_term_prefix (l1 l2: list term): list term :=
    match l2 with
    | nil  => l1
    | hd2::tl2 =>
      match l1 with
      | nil => nil
      | hd1::tl1 =>
        hd2::(list_term_prefix tl1 tl2)
      end
    end.

  Lemma list_term_prefix_nil_right: forall l,
      list_term_prefix l nil = l.
    induction l; simpl; auto.
  Qed.

  Fixpoint zip_list_term (l1 l2: list term): list (term * term) :=
    match l1, l2 with
    | hd1::tl1, hd2::tl2 =>
      (hd1, hd2)::(zip_list_term tl1 tl2)
    | _, _ => nil
    end.

  Lemma zip_list_term_nil_left: forall l,
      zip_list_term nil l = nil.
    intuition.
  Qed.

  Lemma zip_list_term_nil_right: forall l,
      zip_list_term l nil = nil.
    induction l; simpl; intuition.
  Qed.

  Lemma list_term_semantics_eq_term:
    forall {Value: InhabitedType}
           (ctxt_var: string -> Value)
           (ctxt_fn: string -> list Value -> Value),
    forall rhs lhs,
             (forall x, List.In x (zip_list_term lhs rhs) ->
                        let (x1, x2) := x in
                        @term_semantics Value ctxt_var ctxt_fn x1 = @term_semantics Value ctxt_var ctxt_fn x2) ->
             map (@term_semantics Value ctxt_var ctxt_fn) lhs =
             map (@term_semantics Value ctxt_var ctxt_fn) (list_term_prefix lhs rhs).
    do 4 intro.
    induction rhs; simpl; intros; auto.
    rewrite list_term_prefix_nil_right; auto.
    destruct lhs; auto.
    simpl; simpl in H; rewrite (H (t, a)).
    apply f_equal.
    apply IHrhs.
    intros.
    apply H.
    right; auto.
    left; auto.
Qed.

  Lemma fun_congruence_eq_term:
    forall {Value: InhabitedType}
           (ctxt_var: string -> Value)
           (ctxt_fn: string -> list Value -> Value)
           (ctxt_pred: string -> list Value -> Prop),
    forall f rhs lhs,
             (forall x, List.In x (zip_list_term lhs rhs) ->
                        let (x1, x2) := x in
                        @formula_semantics Value ctxt_var ctxt_fn ctxt_pred (Eq x1 x2)
                        ) ->
             @formula_semantics Value ctxt_var ctxt_fn ctxt_pred (Eq (fn f lhs) (fn f (list_term_prefix lhs rhs))).
    simpl; intros.
    do 2 rewrite term_semantics_fn.
    rewrite <- list_term_semantics_eq_term; auto.
  Qed.

  Lemma pred_congruence_eq_term:
    forall {Value: InhabitedType}
           (ctxt_var: string -> Value)
           (ctxt_fn: string -> list Value -> Value)
           (ctxt_pred: string -> list Value -> Prop),
    forall P rhs lhs,
             (forall x, List.In x (zip_list_term lhs rhs) ->
                        let (x1, x2) := x in
                        @formula_semantics Value ctxt_var ctxt_fn ctxt_pred (Eq x1 x2)
                        ) ->
             @formula_semantics Value ctxt_var ctxt_fn ctxt_pred (
                                  Imp
                                    (Atom (R P lhs))
                                    (Atom (R P (list_term_prefix lhs rhs)))
                                ).
    simpl; intros.
    rewrite <- list_term_semantics_eq_term; auto.
  Qed.
  
  Fixpoint build_conj (fs: list (@formula fol)) : formula :=
    match fs with
    | nil => True
    | hd::tl => And hd (build_conj tl)
    end.

  Lemma build_conj_sem:
    forall {Value: InhabitedType}
           (ctxt_var: string -> Value)
           (ctxt_fn: string -> list Value -> Value)
           (ctxt_pred: string -> list Value -> Prop),
    forall l,
      @formula_semantics Value ctxt_var ctxt_fn ctxt_pred (
                           build_conj (List.map (fun x: (term * term) => let (x1, x2) := x in Eq x1 x2) l)
                         ) <->
      (forall x, List.In x l ->
                        let (x1, x2) := x in
                        @formula_semantics Value ctxt_var ctxt_fn ctxt_pred (Eq x1 x2)
                        ).
    do 4 intro.
    induction l; simpl; intros.
    intuition.
    split; intros.
    inversion_clear H.
    inversion_clear H0.
    subst a.
    destruct x.
    intuition.
    rewrite IHl in H2.
    generalize (H2 x H).
    destruct x; intuition.
    split.
    generalize (H a); intros.
    destruct a.
    intuition.
    rewrite IHl.
    intros.
    generalize (H x).
    destruct x; intuition.
Qed.

  Fixpoint build_imp (fs: list (@formula fol)) (ccl: formula): formula :=
    match fs with
    | nil => ccl
    |hd::tl => Imp hd (build_imp tl ccl)
    end.

  Lemma build_conj_imp_equiv:
    forall {Value: InhabitedType}
           (ctxt_var: string -> Value)
           (ctxt_fn: string -> list Value -> Value)
           (ctxt_pred: string -> list Value -> Prop),
    forall fs ccl,
      @formula_semantics Value ctxt_var ctxt_fn ctxt_pred (
                           Imp (build_conj fs) ccl
                         ) <->
      @formula_semantics Value ctxt_var ctxt_fn ctxt_pred (
                           build_imp fs ccl
                         ).
    do 4 intro; induction fs; split; simpl; intros.
    intuition.
    intuition.
    rewrite <- IHfs; simpl; intuition.
    simpl in IHfs.
    inversion_clear H0.
    generalize (H H1); intros.
    rewrite <- IHfs in H0; intros.
    intuition.
  Qed.    

  Program Definition axiom_funcong_aux (f: string) (lhs rhs: list term) : Thm :=
    mkImpl (
        Imp
          (build_conj (List.map (fun x: (term * term) => let (x1, x2) := x in Eq x1 x2) (zip_list_term lhs rhs)))
          (Eq (fn f lhs) (fn f (list_term_prefix lhs rhs)))
      ) _.
  Next Obligation.
    apply (fun_congruence_eq_term ctxt_var ctxt_fn ctxt_pred).
    rewrite <- build_conj_sem; auto.
  Qed.

  Program Definition axiom_funcong (f: string) (lhs rhs: list term) : Thm :=
    mkImpl (
        build_imp
          (List.map (fun x: (term * term) => let (x1, x2) := x in Eq x1 x2) (zip_list_term lhs rhs))
          (Eq (fn f lhs) (fn f (list_term_prefix lhs rhs)))
      ) _.
  Next Obligation.
    rewrite <- build_conj_imp_equiv.
    apply axiom_funcong_aux_obligation_1.
  Qed.
  
  (*  |- s1 = t1 ==> ... ==> sn = tn ==> P(s1,..,sn) ==> P(t1,..,tn)           *)
  Program Definition axiom_predcong_aux (P: string) (lhs rhs: list term) : Thm :=
    mkImpl (
        Imp
          (build_conj (List.map (fun x: (term * term) => let (x1, x2) := x in Eq x1 x2) (zip_list_term lhs rhs)))
          (Imp (Atom (R P lhs)) (Atom (R P (list_term_prefix lhs rhs))))
      ) _.
  Next Obligation.
    apply (pred_congruence_eq_term ctxt_var ctxt_fn ctxt_pred).
    rewrite <- build_conj_sem; auto.
    auto.
  Qed.

  Program Definition axiom_predcong (P: string) (lhs rhs: list term) : Thm :=
    mkImpl (
        build_imp (List.map (fun x: (term * term) => let (x1, x2) := x in Eq x1 x2) (zip_list_term lhs rhs))
           (Imp (Atom (R P lhs)) (Atom (R P (list_term_prefix lhs rhs))))
      ) _.
  Next Obligation.
    rewrite <- build_conj_imp_equiv.
    apply axiom_predcong_aux_obligation_1.
  Qed.
  
  (*  |- (p <=> q) ==> p ==> q                                                 *)
  Program Definition  axiom_iffimp1 (p q: formula) : Thm :=
    mkImpl (
        Imp
          (Iff p q)
          (Imp p q)
        ) _.
  Next Obligation.
    rewrite <- H; auto.
  Qed.
  
  (*  |- (p <=> q) ==> q ==> p                                                 *)
  Program Definition axiom_iffimp2 (p q: formula) : Thm :=
    mkImpl (
        Imp
          (Iff p q)
          (Imp q p)
        ) _.
  Next Obligation.
    rewrite H; auto.
  Qed.

  (*  |- (p ==> q) ==> (q ==> p) ==> (p <=> q)                                 *)
  Program Definition axiom_impiff (p q: formula) : Thm :=
    mkImpl (
        Imp
          (Imp p q)
          (Imp
             (Imp q p)
             (Iff p q)
          )
        ) _.
  Next Obligation.
    split; auto.
  Qed.
  
  (*  |- true <=> (false ==> false)                                            *)
  Program Definition axiom_true: Thm := mkImpl (Iff True (Imp False False)) _.
  Next Obligation.
    split; auto.
  Qed.
  
  (*  |- ~p <=> (p ==> false)                                                  *)
  Program Definition axiom_not (p: formula): Thm := mkImpl (Iff (Not p) (Imp p False)) _.
  Next Obligation.
    split; auto.
  Qed.  
  
  (*  |- p /\ q <=> (p ==> q ==> false) ==> false                              *)
  Program Definition axiom_and (p q: formula): Thm :=
    mkImpl (
        Iff
          (And p q)
          (Imp (Imp p (Imp q False)) False)
      ) _.
  Next Obligation.
    split; intros; auto.
    intuition.
    generalize (classical_formula ctxt_var ctxt_fn ctxt_pred p); intro H1.
    generalize (classical_formula ctxt_var ctxt_fn ctxt_pred q); intro H2.
    intuition.
  Qed.
        
  (*  |- p \/ q <=> ~(~p /\ ~q)                                                *)
  Program Definition axiom_or (p q: formula): Thm :=
    mkImpl (
        Iff
          (Or p q)
          (Not (And (Not p) (Not q)))
        ) _.
  Next Obligation.
    split; intros; auto.
    intuition.
    generalize (classical_formula ctxt_var ctxt_fn ctxt_pred p); intro H1.
    generalize (classical_formula ctxt_var ctxt_fn ctxt_pred q); intro H2.
    intuition.
  Qed.

  (*  |- (exists x. p) <=> ~(forall x. ~p)                                     *)
  Program Definition axiom_exists (x: string) (p: formula): Thm :=
    mkImpl (
        Iff
          (Exists x p)
          (Not (Forall x (Not p)))
        ) _.
  Next Obligation.
    split; intros; auto; intros.
    red; intros.
    inversion_clear H.
    generalize (H0 x0).
    contradiction.
    generalize (classical_formula ctxt_var ctxt_fn ctxt_pred (Exists x p)); simpl; intro H1.
    inversion_clear H1; auto.
    assert Logic.False.
    apply H.
    intros; red; intros.
    apply H0.
    exists v; auto.
    intuition.    
  Qed.

End Proven.


Require Import Coq.extraction.ExtrOcamlString.
Require Import Coq.extraction.ExtrOcamlBasic.
Require Import ExtrOcamlNatBigInt.

Extraction "harrison.ml" Proven.






  