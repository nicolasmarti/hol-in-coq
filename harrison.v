Require Import List.
Require Import String.

Open Local Scope string_scope.
Open Local Scope list_scope.

(*****************************************)

Record InhabitedType : Type := {
                                S :> Set;
                                witness: exists v: S, True;
                              }.

(*****************************************)

Inductive term: Set :=
| var: string -> term
| fct: string -> list_term -> term
  with
  list_term : Set :=
| nil_term: list_term
| cons_term: term -> list_term -> list_term.

Program Fixpoint term_dec (t1 t2: term): {t1 = t2} + {t1 <> t2} :=
  match t1, t2 with
  | var s1, var s2 => _
  | fct f1 args1, fct f2 args2 =>
    match string_dec f1 f2 with
    | right _ => _
    | left _ =>
      match list_term_dec args1 args2 with
      | right _ => _
      | left _ => _
      end
    end
  | var _, fct _ _ => _
  | fct _ _, var _ => _
  end
with
list_term_dec (l1 l2: list_term): {l1 = l2} + {l1 <> l2} :=
  match l1, l2 with
  | nil_term, nil_term => _
  | cons_term hd1 tl1, cons_term hd2 tl2 =>
    match term_dec hd1 hd2 with
    | left _ =>
      match list_term_dec tl1 tl2 with
      | left _ => _
      | right _ => _
      end
    | right _ => _
    end
  | nil_term, cons_term hd tl => _
  | cons_term hd tl, nil_term => _
  end.
Next Obligation.
  left; congruence.
Defined.
Next Obligation.
  left; congruence.
Defined.
Next Obligation.
  right; congruence.
Defined.
Next Obligation.
  right; congruence.
Defined.
Next Obligation.
  right; congruence.
Defined.
Next Obligation.
  right; congruence.
Defined.
Next Obligation.
  destruct (string_dec s1 s2).
  left; congruence.
  right; congruence.
Defined.
Next Obligation.
  right; congruence.
Defined.
Next Obligation.
  right; congruence.
Defined.
Next Obligation.
  left; congruence.
Defined.
Next Obligation.
  right; congruence.
Defined.
Next Obligation.
  right; congruence.
Defined.

Fixpoint term_semantics
         {Value: InhabitedType}
         (ctxt_var: string -> Value)
         (ctxt_fct: string -> list Value -> Value)
         (t: term): Value :=
  match t with
  | var x => ctxt_var x
  | fct f args => ctxt_fct f (list_term_semantics ctxt_var ctxt_fct args)
  end
with
list_term_semantics
  {Value: InhabitedType}
  (ctxt_var: string -> Value)
  (ctxt_fct: string -> list Value -> Value)
  (lt: list_term): list Value :=
  match lt with
  | nil_term => nil
  | cons_term hd tl =>
    (term_semantics ctxt_var ctxt_fct hd)::(list_term_semantics ctxt_var ctxt_fct tl)
  end.

Fixpoint term_free_vars (t: term) : list string :=
  match t with
  | var s => s::nil
  | fct f ts => list_term_free_vars ts
  end
with
list_term_free_vars (ts: list_term): list string :=
  match ts with
  | nil_term => nil
  | cons_term hd tl =>
    term_free_vars hd ++ list_term_free_vars tl
  end.

Program Fixpoint term_semantics_free_vars
        {Value: InhabitedType}
        (t: term)
        (ctxt_fct: string -> list Value -> Value)
        (ctxt_var1: string -> Value)
        (ctxt_var2: string -> Value)
        (Hyp: forall s, List.In s (term_free_vars t) -> ctxt_var1 s = ctxt_var2 s):
  @term_semantics Value ctxt_var1 ctxt_fct t = @term_semantics Value ctxt_var2 ctxt_fct t :=
  match t with
  | var s => _
  | fct f lt =>
    let H := @list_term_semantics_free_vars Value lt ctxt_fct ctxt_var1 ctxt_var2 _ in
    _ H
  end
with
list_term_semantics_free_vars
  {Value: InhabitedType}
  (lt: list_term)
  (ctxt_fct: string -> list Value -> Value)
  (ctxt_var1: string -> Value)
  (ctxt_var2: string -> Value)
  (Hyp: forall s, List.In s (list_term_free_vars lt) -> ctxt_var1 s = ctxt_var2 s):
  @list_term_semantics Value ctxt_var1 ctxt_fct lt = @list_term_semantics Value ctxt_var2 ctxt_fct lt :=
  match lt with
  | nil_term => _
  | cons_term hd tl =>
    let H1 := @term_semantics_free_vars Value hd ctxt_fct ctxt_var1 ctxt_var2 _ in
    let H2 := @list_term_semantics_free_vars Value tl ctxt_fct ctxt_var1 ctxt_var2 _ in
    _ H1 H2
  end.
Next Obligation.
  apply Hyp; simpl; apply List.in_or_app; auto.
Defined.
Next Obligation.
  apply Hyp; simpl; apply List.in_or_app; auto.
Defined.
Next Obligation.
  apply Hyp; simpl; auto.
Defined.

(*****************************************)

Inductive formula : Set :=
| T: formula
| F: formula
| Atom: string -> list_term -> formula
| Eq: term -> term -> formula
| Not: formula -> formula
| And: formula -> formula -> formula
| Or: formula -> formula -> formula
| Imp: formula -> formula -> formula
| Iff: formula -> formula -> formula
| Forall: string -> formula -> formula
| Exists: string -> formula -> formula
.

Definition list_dec:
  forall {A: Set}
         (A_dec: forall (a1 a2: A), {a1 = a2} + {a1 <> a2})
         (l1 l2: list A),
    {l1 = l2} + {l1 <> l2}.
decide equality.
Defined.


Definition formula_dec: forall (f1 f2: formula), {f1 = f2} + {f1 <> f2}.
  decide equality.
  apply list_term_dec; apply term_dec.
  apply string_dec.
  apply term_dec.
  apply term_dec.
  apply string_dec.
  apply string_dec.
Defined.

Fixpoint formula_semantics 
         {Value: InhabitedType}
         (ctxt_var: string -> Value)
         (ctxt_fct: string -> list Value -> Value)
         (ctxt_pred: string -> list Value -> Prop)
         (f: formula) : Prop :=
  match f with
  | T => True
  | F => False
  | Atom P args => ctxt_pred P (list_term_semantics ctxt_var ctxt_fct args)
  | Eq t1 t2 => term_semantics ctxt_var ctxt_fct t1 = term_semantics ctxt_var ctxt_fct t2
  | Not f => ~ (formula_semantics ctxt_var ctxt_fct ctxt_pred f)
  | And f1 f2 => (formula_semantics ctxt_var ctxt_fct ctxt_pred f1) /\ (formula_semantics ctxt_var ctxt_fct ctxt_pred f2) 
  | Or f1 f2 => (formula_semantics ctxt_var ctxt_fct ctxt_pred f1) \/ (formula_semantics ctxt_var ctxt_fct ctxt_pred f2) 
  | Imp f1 f2 => (formula_semantics ctxt_var ctxt_fct ctxt_pred f1) -> (formula_semantics ctxt_var ctxt_fct ctxt_pred f2) 
  | Iff f1 f2 => (formula_semantics ctxt_var ctxt_fct ctxt_pred f1) <-> (formula_semantics ctxt_var ctxt_fct ctxt_pred f2)
  | Forall x f => forall (v: Value),
      formula_semantics
        (fun y => match string_dec x y with | left _ => v | right _ => ctxt_var y end)
        ctxt_fct ctxt_pred f
  | Exists x f => exists (v: Value),
      formula_semantics
        (fun y => match string_dec x y with | left _ => v | right _ => ctxt_var y end)
        ctxt_fct ctxt_pred f
  end.

Axiom classical_formula:
  forall {Value: InhabitedType}
         (ctxt_var: string -> Value)
         (ctxt_fct: string -> list Value -> Value)
         (ctxt_pred: string -> list Value -> Prop)
         (f: formula),
    (formula_semantics ctxt_var ctxt_fct ctxt_pred f) \/ ~ (formula_semantics ctxt_var ctxt_fct ctxt_pred f).

Fixpoint formula_free_vars (f: formula) : list string :=
    match f with
  | T => nil
  | F => nil
  | Atom P args => list_term_free_vars args
  | Eq t1 t2 => term_free_vars t1 ++ term_free_vars t2
  | Not f => formula_free_vars f
  | And f1 f2 => formula_free_vars f1 ++ formula_free_vars f2
  | Or f1 f2 => formula_free_vars f1 ++ formula_free_vars f2
  | Imp f1 f2 => formula_free_vars f1 ++ formula_free_vars f2
  | Iff f1 f2 => formula_free_vars f1 ++ formula_free_vars f2
  | Forall x f => List.remove string_dec x (formula_free_vars f)
  | Exists x f => List.remove string_dec x (formula_free_vars f)
  end.

Lemma formula_semantics_free_vars:
  forall
      {Value: InhabitedType}
      (f: formula)
      (ctxt_fct: string -> list Value -> Value)
      (ctxt_pred: string -> list Value -> Prop)
      (ctxt_var1: string -> Value)
      (ctxt_var2: string -> Value)
      (Hyp: forall s, List.In s (formula_free_vars f) -> ctxt_var1 s = ctxt_var2 s),
  (formula_semantics ctxt_var1 ctxt_fct ctxt_pred f) <-> (formula_semantics ctxt_var2 ctxt_fct ctxt_pred f).

  induction f; simpl; intros.

  intuition.
  intuition.

  rewrite list_term_semantics_free_vars with (ctxt_var4 := ctxt_var2).
  intuition.
  auto.

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
  Parameter concl: Thm -> formula.

  Parameter proof:
    forall (thm: Thm)
           {Value: InhabitedType}
           (ctxt_var: string -> Value)
           (ctxt_fct: string -> list Value -> Value)
           (ctxt_pred: string -> list Value -> Prop),
      @formula_semantics Value ctxt_var ctxt_fct ctxt_pred (concl thm).

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
  Parameter axiom_funcong: string -> list_term -> list_term -> Thm.
  
  (*  |- s1 = t1 ==> ... ==> sn = tn ==> P(s1,..,sn) ==> P(t1,..,tn)           *)
  Parameter axiom_predcong: string -> list_term -> list_term -> Thm.
  
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

  Record Impl: Set := mkImpl {
                       concl :> formula;
                       proof: forall 
                           {Value: InhabitedType}
                           (ctxt_var: string -> Value)
                           (ctxt_fct: string -> list Value -> Value)
                           (ctxt_pred: string -> list Value -> Prop),
                           formula_semantics ctxt_var ctxt_fct ctxt_pred concl;
                       }.

  Definition Thm := Impl.

  Program Definition T_Thm := mkImpl T _.
  
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
    generalize (@proof thm1 Value ctxt_var ctxt_fct ctxt_pred); intros.
    generalize (@proof thm2 Value ctxt_var ctxt_fct ctxt_pred); intros.
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
  Program Definition axiom_doubleneg (p: formula): Thm := mkImpl (Imp (Imp (Imp p F) F) p) _.
  Next Obligation.
    generalize (classical_formula ctxt_var ctxt_fct ctxt_pred p); intro H0; inversion_clear H0; auto.
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
    exists (term_semantics ctxt_var ctxt_fct t).
    destruct (string_dec x x).
    apply term_semantics_free_vars; intros.
    destruct (string_dec x s).
    subst s; contradiction.
    auto.
    intuition.
  Qed.

  (*  |- t = t                                                                 *)
  Program Definition axiom_eqrefl (t: term): Thm := mkImpl (Eq t t) _.    
  
  (*  |- s1 = t1 ==> ... ==> sn = tn ==> f(s1,..,sn) = f(t1,..,tn)             *)
  Fixpoint list_term_prefix (l1 l2: list_term): list_term :=
    match l2 with
    | nil_term => l1
    | cons_term hd2 tl2 =>
      match l1 with
      | nil_term => nil_term
      | cons_term hd1 tl1 =>
        cons_term hd2 (list_term_prefix tl1 tl2)
      end
    end.

  Lemma list_term_prefix_nil_right: forall l,
      list_term_prefix l nil_term = l.
    induction l; simpl; auto.
  Qed.

  Fixpoint zip_list_term (l1 l2: list_term): list (term * term) :=
    match l1, l2 with
    | cons_term hd1 tl1, cons_term hd2 tl2 =>
      (hd1, hd2)::(zip_list_term tl1 tl2)
    | _, _ => nil
    end.

  Lemma zip_list_term_nil_left: forall l,
      zip_list_term nil_term l = nil.
    intuition.
  Qed.

  Lemma zip_list_term_nil_right: forall l,
      zip_list_term l nil_term = nil.
    induction l; simpl; intuition.
  Qed.

  Lemma list_term_semantics_eq_term:
    forall {Value: InhabitedType}
           (ctxt_var: string -> Value)
           (ctxt_fct: string -> list Value -> Value),
    forall rhs lhs,
             (forall x, List.In x (zip_list_term lhs rhs) ->
                        let (x1, x2) := x in
                        @term_semantics Value ctxt_var ctxt_fct x1 = @term_semantics Value ctxt_var ctxt_fct x2) ->
             @list_term_semantics Value ctxt_var ctxt_fct lhs =
             @list_term_semantics Value ctxt_var ctxt_fct (list_term_prefix lhs rhs).
    do 4 intro.
    induction rhs; simpl; intros; auto.
    rewrite list_term_prefix_nil_right; auto.
    destruct lhs; auto.
    simpl; simpl in H; rewrite (H (t0, t)).
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
           (ctxt_fct: string -> list Value -> Value)
           (ctxt_pred: string -> list Value -> Prop),
    forall f rhs lhs,
             (forall x, List.In x (zip_list_term lhs rhs) ->
                        let (x1, x2) := x in
                        @formula_semantics Value ctxt_var ctxt_fct ctxt_pred (Eq x1 x2)
                        ) ->
             @formula_semantics Value ctxt_var ctxt_fct ctxt_pred (Eq (fct f lhs) (fct f (list_term_prefix lhs rhs))).
    simpl; intros.
    rewrite <- list_term_semantics_eq_term; auto.
  Qed.

  Lemma pred_congruence_eq_term:
    forall {Value: InhabitedType}
           (ctxt_var: string -> Value)
           (ctxt_fct: string -> list Value -> Value)
           (ctxt_pred: string -> list Value -> Prop),
    forall P rhs lhs,
             (forall x, List.In x (zip_list_term lhs rhs) ->
                        let (x1, x2) := x in
                        @formula_semantics Value ctxt_var ctxt_fct ctxt_pred (Eq x1 x2)
                        ) ->
             @formula_semantics Value ctxt_var ctxt_fct ctxt_pred (
                                  Imp
                                    (Atom P lhs)
                                    (Atom P (list_term_prefix lhs rhs))
                                ).
    simpl; intros.
    rewrite <- list_term_semantics_eq_term; auto.
  Qed.
  
  Fixpoint build_conj (fs: list formula) : formula :=
    match fs with
    | nil => T
    | hd::tl => And hd (build_conj tl)
    end.

  Lemma build_conj_sem:
    forall {Value: InhabitedType}
           (ctxt_var: string -> Value)
           (ctxt_fct: string -> list Value -> Value)
           (ctxt_pred: string -> list Value -> Prop),
    forall l,
      @formula_semantics Value ctxt_var ctxt_fct ctxt_pred (
                           build_conj (List.map (fun x: (term * term) => let (x1, x2) := x in Eq x1 x2) l)
                         ) <->
      (forall x, List.In x l ->
                        let (x1, x2) := x in
                        @formula_semantics Value ctxt_var ctxt_fct ctxt_pred (Eq x1 x2)
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

  Fixpoint build_imp (fs: list formula) (ccl: formula): formula :=
    match fs with
    | nil => ccl
    |hd::tl => Imp hd (build_imp tl ccl)
    end.

  Lemma build_conj_imp_equiv:
    forall {Value: InhabitedType}
           (ctxt_var: string -> Value)
           (ctxt_fct: string -> list Value -> Value)
           (ctxt_pred: string -> list Value -> Prop),
    forall fs ccl,
      @formula_semantics Value ctxt_var ctxt_fct ctxt_pred (
                           Imp (build_conj fs) ccl
                         ) <->
      @formula_semantics Value ctxt_var ctxt_fct ctxt_pred (
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

  Program Definition axiom_funcong_aux (f: string) (lhs rhs: list_term) : Thm :=
    mkImpl (
        Imp
          (build_conj (List.map (fun x: (term * term) => let (x1, x2) := x in Eq x1 x2) (zip_list_term lhs rhs)))
          (Eq (fct f lhs) (fct f (list_term_prefix lhs rhs)))
      ) _.
  Next Obligation.
    apply (fun_congruence_eq_term ctxt_var ctxt_fct ctxt_pred).
    rewrite <- build_conj_sem; auto.
  Qed.

  Program Definition axiom_funcong (f: string) (lhs rhs: list_term) : Thm :=
    mkImpl (
        build_imp
          (List.map (fun x: (term * term) => let (x1, x2) := x in Eq x1 x2) (zip_list_term lhs rhs))
          (Eq (fct f lhs) (fct f (list_term_prefix lhs rhs)))
      ) _.
  Next Obligation.
    rewrite <- build_conj_imp_equiv.
    apply axiom_funcong_aux_obligation_1.
  Qed.
  
  (*  |- s1 = t1 ==> ... ==> sn = tn ==> P(s1,..,sn) ==> P(t1,..,tn)           *)
  Program Definition axiom_predcong_aux (P: string) (lhs rhs: list_term) : Thm :=
    mkImpl (
        Imp
          (build_conj (List.map (fun x: (term * term) => let (x1, x2) := x in Eq x1 x2) (zip_list_term lhs rhs)))
          (Imp (Atom P lhs) (Atom P (list_term_prefix lhs rhs)))
      ) _.
  Next Obligation.
    apply (pred_congruence_eq_term ctxt_var ctxt_fct ctxt_pred).
    rewrite <- build_conj_sem; auto.
    auto.
  Qed.

  Program Definition axiom_predcong (P: string) (lhs rhs: list_term) : Thm :=
    mkImpl (
        build_imp (List.map (fun x: (term * term) => let (x1, x2) := x in Eq x1 x2) (zip_list_term lhs rhs))
           (Imp (Atom P lhs) (Atom P (list_term_prefix lhs rhs)))
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
  Program Definition axiom_true: Thm := mkImpl (Iff T (Imp F F)) _.
  Next Obligation.
    split; auto.
  Qed.
  
  (*  |- ~p <=> (p ==> false)                                                  *)
  Program Definition axiom_not (p: formula): Thm := mkImpl (Iff (Not p) (Imp p F)) _.
  Next Obligation.
    split; auto.
  Qed.  
  
  (*  |- p /\ q <=> (p ==> q ==> false) ==> false                              *)
  Program Definition axiom_and (p q: formula): Thm :=
    mkImpl (
        Iff
          (And p q)
          (Imp (Imp p (Imp q F)) F)
      ) _.
  Next Obligation.
    split; intros; auto.
    intuition.
    generalize (classical_formula ctxt_var ctxt_fct ctxt_pred p); intro H1.
    generalize (classical_formula ctxt_var ctxt_fct ctxt_pred q); intro H2.
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
    generalize (classical_formula ctxt_var ctxt_fct ctxt_pred p); intro H1.
    generalize (classical_formula ctxt_var ctxt_fct ctxt_pred q); intro H2.
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
    generalize (classical_formula ctxt_var ctxt_fct ctxt_pred (Exists x p)); simpl; intro H1.
    inversion_clear H1; auto.
    assert False.
    apply H.
    intros; red; intros.
    apply H0.
    exists v; auto.
    intuition.    
  Qed.

End Proven.







  