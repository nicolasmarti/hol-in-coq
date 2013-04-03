Class non_empty_set (A: Set) := {
  witeness: A
}. 



(* the primary type bool (we overwrite the coq bool type) *)
Axiom bool: Set.

(* from bool to Prop *)
Axiom judgment: bool -> Prop.
Notation "|-  x" := (judgment x) (at level 95, no associativity).

(* basic primitives: equality, implication and choice *)
Axiom eq: forall {A: Set}, A -> A -> bool.
Notation "x = y" := (@eq _ x y) (at level 70, no associativity).

Axiom imp: bool -> bool -> bool.
Notation "b1 ==> b2" := (imp b1 b2) (at level 90, right associativity).

Axiom choice: forall {A: Set} {H: non_empty_set A}, (A -> bool) -> A.
Notation "'@@' x , p" := (choice (fun x => p)) (at level 100, x ident).

(* *)

(* the deduction system axioms *)
Axiom eq_refl: forall {A: Set} (a: A), |- a = a.
Axiom mk_comb: forall {A B: Set} (f1 f2: A -> B) (t1 t2: A), (|- f1 = f2) -> (|- t1 = t2) -> (|- f1 t1 = f2 t2).
Axiom mk_abs: forall {A B: Set} (f1 f2: A -> B), (forall x, |- f1 x = f2 x) -> (|- f1 = f2).
Axiom disch: forall b1 b2, ((|- b1) -> (|- b2)) -> (|- b1 ==> b2).
Axiom mp: forall b1 b2, (|- b1 ==> b2) -> (|- b1) -> (|- b2).
Axiom eq_mp: forall b1 b2, (|- b1 = b2) -> (|- b1) -> (|- b2).
Axiom eta_ax: forall {A B: Set} (f: A -> B), (|- (fun x => f x) = f).
Axiom imp_antisym_ax: forall p1 p2, |- (p1 ==> p2) ==> ((p2 ==> p1) ==> (p1 = p2)).
Axiom select_ax: forall {A: Set} {H: non_empty_set A} (P: A -> bool) (x: A), |- P x ==> P (choice P).

(* few definitions *)

(* true *)
Definition true : bool := (fun x: bool => x) = (fun x => x).

(* universal quantification *)
Definition forall_def {A: Set} (P: A -> bool) : bool := P = (fun _ => true). 
Notation "'Forall' x , p" := (forall_def (fun x => p)) (at level 200, x ident).
Notation "'Forall' x : t , p" := (forall_def (fun x:t => p)) (at level 200, x ident, format "'Forall' '/ ' x : t , '/ ' p").

(* conjunction *)
Definition conj_def (p1 p2: bool) : bool := Forall p, (p1 ==> (p2 ==> p)) ==> p.
Notation "b1 /\ b2" := (conj_def b1 b2) (at level 80, right associativity).

(* existential *)
Definition exists_def {A: Set} {H: non_empty_set A} (P: A -> bool) : bool := P (choice P). 
Notation "'Exists' x , p" := (exists_def (fun x => p)) (at level 200, x ident).
Notation "'Exists' x : t , p" := (exists_def (fun x:t => p)) (at level 200, x ident, format "'Exists' '/ ' x : t , '/ ' p").

(* some lemmas on equality *)
Lemma mk_comb1 {A B: Set} (f1 f2: A -> B) (t: A): (|- f1 = f2) -> (|- f1 t = f2 t). 
intros.
apply mk_comb; [auto | apply eq_refl].
Qed.

Lemma mk_comb2 {A B: Set} (f: A -> B) (t1 t2: A): (|- t1 = t2) -> (|- f t1 = f t2). 
intros.
apply mk_comb; [apply eq_refl | auto].
Qed.

Lemma eq_trans {A: Set} (t1 t2 t3: A): (|- t1 = t2) -> (|- t2 = t3) -> (|- t1 = t3).
intros.
cut (|- (t1 = t2) = (t1 = t3)); intros.
eapply eq_mp; [apply H1 | auto].
apply mk_comb2; auto.
Qed.

Lemma eq_sym {A: Set} (t1 t2: A): (|- t1 = t2) -> (|- t2 = t1).
intros.
cut (|- (t1 = t1) = (t2 = t1)); intros. 
eapply eq_mp; [apply H0 | apply eq_refl].
apply mk_comb2 with (f := fun x => x = t1); auto.
Qed.

(* false *)
Definition false : bool := Forall b: bool, b.

(* disjunction *)
Definition disj_def (p1 p2: bool) : bool := Forall p, (p1 ==> p) ==> (p2 ==> p) ==> p.
Notation "b1 \/ b2" := (disj_def b1 b2) (at level 85, right associativity).

(* negation *)
Definition not_def (p: bool) : bool := p ==> false.
Notation "~~ x" := (not_def x) (at level 75, no associativity).

(* unique existential *)
Definition uexists_def {A: Set} {H: non_empty_set A} (P: A -> bool) : bool := Exists x, P x /\ (Forall y, P y ==> x = y).
Notation "'UExists' x , p" := (uexists_def (fun x => p)) (at level 200, x ident).
Notation "'UExists' x : t , p" := (uexists_def (fun x:t => p)) (at level 200, x ident, format "'UExists' '/ ' x : t , '/ ' p").

(* condition *)
Definition cond {A: Set} {HA: non_empty_set A} p (t1 t2: A) := @@ x, (p = true ==> x = t1) /\ (p = false ==> x = t1).

(* derived inference rule *)
Lemma truth: (|- true).
apply mk_abs; intros.
apply eq_refl.
Qed.

Lemma eqt_elim p: (|- p = true) -> (|- p).
intros.
eapply eq_mp.
apply eq_sym; exact H.
apply truth.
Qed.

Lemma eq_imp1 p q: (|- p = q) -> (|- p ==> q).
intros.
apply disch; intros.
apply eq_mp with p; auto.
Qed.

Lemma eq_imp2 p q: (|- p = q) -> (|- q ==> p).
intros.
apply disch; intros.
apply eq_mp with q; auto.
apply eq_sym; auto.
Qed.

Lemma contrapos p q: (|- p = q) -> (|- ~~ q ==>  ~~p).
intros.
apply disch; intros.
apply disch; intros.
eapply mp with q; auto.
apply eq_mp with p; auto.
Qed.

Lemma eqf_elim p: (|- p = false) -> (|- ~~ p).
intros.
apply eq_imp1; auto.
Qed.

Lemma imp_trans p q r: (|- p ==> q) -> (|- q ==> r) -> (|- p ==> r).
intros.
apply disch; intros.
apply mp with q; auto.
apply mp with p; auto.
Qed.

Lemma spec {A: Set} p (t: A): (|- forall_def p) -> (|- p t).
intros.
unfold forall_def in H.
apply eqt_elim.
eapply (mk_comb1 _ _ _ H).
Qed.

Lemma contr p: (|- false) -> (|- p).
intros.
apply (spec _ p H).
Qed.

Lemma deduct_antisym p q: (|- p) -> (|- q) -> (|- p = q).
intros.
cut (|- p ==> q); intros.
cut (|- q ==> p); intros.
generalize (imp_antisym_ax p q); intros.
generalize (mp _ _ H3 H1); intros.
generalize (mp _ _ H4 H2); intros.
auto.
apply disch; intros; auto.
apply disch; intros; auto.
Qed.

Lemma eqt_intro p: (|- p) -> (|- p = true).
intros.
apply deduct_antisym; auto.
apply truth.
Qed.

Lemma eqf_intro p: (|- ~~ p) -> (|- p = false).
intros.
cut (|- false ==> p).
intros.
apply (mp _ _ (mp _ _ (imp_antisym_ax _ _) H) H0).
apply disch; apply contr.
Qed.

Lemma gen {A: Set} p: (|- p) -> (|- forall_def (fun _: A => p)).
intros.
unfold forall_def.
apply mk_abs.
intros.
apply eqt_intro; auto.
Qed.

Lemma conj_intro p q: (|- p) -> (|- q) -> (|- p /\ q).
intros.
unfold conj_def.
unfold forall_def.
apply mk_abs; intros.
apply eqt_intro.
apply disch; intros.
apply (mp _ _ (mp _ _ H1 H)); auto.
Qed.

Lemma conj1_elim p q: (|- p /\ q) -> (|- p).
intros.
unfold conj_def in H.
apply (mp _ _ (spec _ p H )).
apply disch; intros.
apply disch; intros; auto.
Qed.

Lemma conj2_elim p q: (|- p /\ q) -> (|- q).
intros.
unfold conj_def in H.
apply (mp _ _ (spec _ q H)).
apply disch; intros.
apply disch; intros; auto.
Qed.

Lemma disj_cases p q r: ((|- p) -> (|- r)) -> ((|- q) -> (|- r)) -> ((|- p \/ q) -> (|- r)).
intros.
unfold disj_def in H1.
generalize (disch _ _ H); intros.
generalize (disch _ _ H0); intros.
apply (mp _ _  (mp _ _ (spec _ r H1) H2) H3).
Qed.

Lemma disj1_lemma p q: (|- p) -> (|- p \/ q).
intros.
unfold disj_def.
apply mk_abs; intros; apply eqt_intro.
apply disch; intros.
apply disch; intros.
apply (mp _ _ H0); auto.
Qed.

Lemma disj2_lemma p q: (|- q) -> (|- p \/ q).
intros.
unfold disj_def.
apply mk_abs; intros; apply eqt_intro.
apply disch; intros.
apply disch; intros.
apply (mp _ _ H1); auto.
Qed.

(* choose rule ?? *)


