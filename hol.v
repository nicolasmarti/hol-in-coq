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

Axiom choice: forall {A: Set}, (A -> bool) -> A.

(* *)

(* the deduction system axioms *)
Axiom eq_refl: forall {A: Set} (a: A), |- a = a.
Axiom mk_comb: forall {A B: Set} (f1 f2: A -> B) (t1 t2: A), (|- f1 = f2) -> (|- t1 = t2) -> (|- f1 t1 = f2 t2).
Axiom mk_abs: forall {A B: Set} (f1 f2: A -> B), (forall x, |- f1 x = f2 x) -> (|- f1 = f2).
Axiom disch: forall b1 b2, (|- b2) -> (|- b1 ==> b2).
Axiom mp: forall b1 b2, (|- b1 ==> b2) -> (|- b1) -> (|- b2).
Axiom eq_mp: forall b1 b2, (|- b1 = b2) -> (|- b1) -> (|- b2).
Axiom eta_ax: forall {A B: Set} (f: A -> B), (|- (fun x => f x) = f).
Axiom imp_antisym: forall p1 p2, |- (p1 ==> p2) ==> ((p2 ==> p1) ==> (p1 = p2)).
Axiom select_ax: forall {A: Set} (P: A -> bool) (x: A), |- P x ==> P (choice P).

(* few definitions *)

(* true *)
Definition true : bool := (fun x: bool => x) = (fun x => x).

(* universal quantification *)
Definition forall_def {A: Set} (P: A -> bool) : bool := P = (fun _ => true). 
Notation "'Forall' x , p" := (forall_def (fun x => p)) (at level 200, x ident).
Notation "'Forall' x : t , p" := (forall_def (fun x:t => p)) (at level 200, x ident, format "'Forall' '/ ' x : t , '/ ' p").

(* conjunction *)
Definition conj_def (p1 p2: bool) : bool := Forall p, (p1 ==> (p2 ==> p)) ==> p.

(* existential *)
Definition exists_def {A: Set} (P: A -> bool) : bool := P (choice P). 

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

(* subst rules ??? *)
