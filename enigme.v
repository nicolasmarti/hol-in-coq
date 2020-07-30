Require Import List.

Axiom A: Set.

Axiom A_eq_dec : forall (x y: A), { x = y } + { x <> y }.

Record Ord (A: Set) := {
  lt: A -> A -> Prop;
  lt_dec: forall (x y: A), { lt x y } + { x = y } + { lt y x };
  lt_anti_refl: forall x, ~ lt x x;
  lt_trans: forall x y z, lt x y -> lt y z -> lt x z
                         }.

Inductive list_lt (PA: Ord A): list A -> list A -> Prop :=
| list_lt_nil: forall hd tl, list_lt PA nil (hd::tl)
| list_lt_hd_tl: forall hd1 hd2 tl1 tl2,
    lt A PA hd1 hd2 -> list_lt PA (hd1::tl1) (hd2::tl2)
| list_lt_hd_tl_eq: forall hd1 hd2 tl1 tl2,
    hd1 = hd2 ->
    list_lt PA tl1 tl2 -> list_lt PA (hd1::tl1) (hd2::tl2)
.

Lemma L1 {PA: Ord A}: forall (x y: list A), { @list_lt PA x y } + { x = y } + { list_lt PA y x }.
induction x; simpl; intros.
destruct y.
auto.
left; left; apply list_lt_nil.
destruct y; simpl; intros; intuition.
right; apply list_lt_nil.
generalize (lt_dec A PA a a0); intro a_a0_dec; inversion_clear a_a0_dec.
inversion_clear H.
left; left; apply list_lt_hd_tl; auto.
subst a0.
generalize (IHx y); intro Hyp; inversion_clear Hyp.
inversion_clear H.
left; left; apply list_lt_hd_tl_eq; auto.
left; right; subst; intuition.
right; apply list_lt_hd_tl_eq; auto.
right; apply list_lt_hd_tl; auto.
Qed.

Lemma L2 {PA: Ord A}: forall x, ~ (list_lt PA x x).
  induction x; intros.
  red; intros.
  inversion_clear H.
  syelles.
Qed.

Lemma L3 {PA: Ord A}: forall x y z, @list_lt PA x y -> @list_lt PA y z -> @list_lt PA x z.
  induction x; simpl; intros. qcrush.
  destruct y; simpl; intuition. scrush.
  destruct z; simpl; intuition. scrush.
  inversion_clear H.
  inversion_clear H0. qcrush. scrush.
  subst a0.
  inversion_clear H0. scrush. scrush.
Qed.

Definition ListOrd (PA: Ord A): Ord (list A).
  eapply Build_Ord.
  apply (@L1 PA).
  apply (@L2 PA).
  apply (@L3 PA).
Defined.  
  
Inductive Ordered {A: Set} (PA: Ord A): list A -> Prop :=
| ordered_nil: Ordered PA nil
| ordered_cons: forall hd tl,
    (forall x, In x tl -> lt A PA hd x) ->
    Ordered PA tl ->
    Ordered PA (hd::tl).

Goal forall l: list (list A),
    (exists PA, Ordered (ListOrd PA) l) \/ (forall PA, ~ Ordered (ListOrd PA) l ).


  
(* *)


