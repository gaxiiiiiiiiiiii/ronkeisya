
Require Export base Bool.Export ListNotations.
Set Implicit Arguments.

Module Type sound_mod (X : base_mod).
Import X.


Inductive PropF : Set :=
 | Var : PropVars -> PropF
 | Bot : PropF
 | Conj : PropF -> PropF -> PropF
 | Disj : PropF -> PropF -> PropF
 | Impl : PropF -> PropF -> PropF
.

Notation "# P" := (Var P) (at level 1) : My_scope.
Notation "A ∨ B" := (Disj A B) (at level 15, right associativity) : My_scope.
Notation "A ∧ B" := (Conj A B) (at level 15, right associativity) : My_scope.
Notation "A → B" := (Impl A B) (at level 16, right associativity) : My_scope.
Notation "⊥" := Bot (at level 0)  : My_scope.
Definition Neg A := A → ⊥.
Notation "¬ A" := (Neg A) (at level 5) : My_scope.
Definition Top := ¬⊥.
Notation "⊤" := Top (at level 0) : My_scope.
Definition BiImpl A B := (A→B)∧(B→A).
Notation "A ↔ B" := (BiImpl A B) (at level 17, right associativity) : My_scope.

Fixpoint TrueQ v A : bool := match A with
 | # P   => v P
 | ⊥     => false
 | B ∨ C => (TrueQ v B) || (TrueQ v C)
 | B ∧ C => (TrueQ v B) && (TrueQ v C)
 | B → C => (negb (TrueQ v B)) || (TrueQ v C)
end.
Definition Satisfies v Γ := forall A, In A Γ -> Is_true (TrueQ v A).
Definition Models Γ A := forall v,Satisfies v Γ->Is_true (TrueQ v A).
Notation "Γ ⊨ A" := (Models Γ A) (at level 80).
Definition Valid A := [] ⊨ A.

Reserved Notation "Γ ⊢ A" (at level 80).
Inductive Nc : list PropF -> PropF -> Prop :=
  | Nax   Γ A     : In A Γ                    -> Γ ⊢ A
  | ImpI  Γ A B   : A :: Γ ⊢ B                -> Γ ⊢ A → B
  | ImpE  Γ A B   : Γ ⊢ A → B     ->   Γ ⊢ A  -> Γ ⊢ B
  | BotC  Γ A     : ¬ A :: Γ ⊢ ⊥              -> Γ ⊢ A
  | AndI  Γ A B   : Γ ⊢ A         ->   Γ ⊢ B  -> Γ ⊢ A ∧ B
  | AndE1 Γ A B   : Γ ⊢ A ∧ B                 -> Γ ⊢ A
  | AndE2 Γ A B   : Γ ⊢ A ∧ B                 -> Γ ⊢ B
  | OrI1  Γ A B   : Γ ⊢ A                     -> Γ ⊢ A ∨ B
  | OrI2  Γ A B   : Γ ⊢ B                     -> Γ ⊢ A ∨ B
  | OrE   Γ A B C : Γ ⊢ A ∨ B -> A :: Γ ⊢ C -> B :: Γ ⊢ C -> Γ ⊢ C
  where "Γ ⊢ A" := (Nc Γ A) : My_scope.

Definition Provable A := [] ⊢ A.

Definition Prop_Soundness := forall A, Provable A -> Valid A.
Definition Prop_Completeness := forall A, Valid A -> Provable A.

Ltac mp := eapply ImpE.
Ltac AddNilL :=
  match goal with
  | |- _ ?Γ _ => change Γ with ([] ++ Γ)
  end.
Ltac in_solve :=
  intros; repeat (
    eassumption
    || match goal with
       | H : In _ (_ :: _) |- _ => destruct H; [subst; try discriminate|]
       | H : In _ (_ ++ _) |- _ => apply in_app_iff in H as []; subst
       | |- In _ (_ ++ _) => apply in_app_iff; (left; in_solve; fail) || (right; in_solve; fail)
       end
    || (constructor; reflexivity)
    || constructor 2
  ).
Ltac is_ass := econstructor; in_solve.

Ltac case_bool v A := let HA := fresh "H" in
  (case_eq (TrueQ v A); intro HA;
   try rewrite HA in *; simpl in *;
   try trivial;
   try contradiction
  ).

Local Ltac prove_satisfaction :=
intros ? K;destruct K;[subst;simpl;
match goal with
| [ H : TrueQ _ _ = _  |-  _ ] => rewrite H
end;exact I|auto].

Lemma PropFeq_dec :
  forall (x y : PropF), {x = y} + {x <> y}.
Proof.
  induction x; destruct y;
    try (right; discriminate);
    try (
      destruct (IHx1 y1); [destruct (IHx2 y2); [left; f_equal; auto|]|];
      right; injection; intros; contradiction
    ).
    - destruct (X.Varseq_dec p p0); [left|right].
      * f_equal; auto.
      * injection; intro; contradiction.
    - left; auto.
Qed.

Lemma Excluded_Middle :
  forall Γ A, Γ ⊢ A ∨ ¬ A.
Proof.
  intros.
  apply BotC.
  eapply ImpE with (A ∨ ¬ A).
  - constructor; left; auto.
  - apply OrI2.
    apply ImpI.
    eapply ImpE with (A ∨ ¬ A).
    * constructor; right; left; auto.
    * apply OrI1; constructor; left; auto.
Qed.

Local Hint Constructors Nc : My_scope.


Lemma weakening2 :
  forall Γ A, Γ ⊢ A -> forall Δ, (forall B, In B Γ -> In B Δ) -> Δ ⊢ A.
Proof.
  induction 1; intros Δ HD; try solve [econstructor; auto].
  - apply ImpI; apply IHNc.
    intros C HC.
    destruct HC; subst; [left|right]; auto.
  - apply BotC.
    apply IHNc; intros.
    destruct H0; [left|right]; auto.
  - apply OrE with A B; eauto; [apply IHNc2 |apply IHNc3];
      intros; destruct H2; subst; try solve [left; auto | right; auto].
Qed.

Lemma weakening :
  forall Γ Δ A, Γ ⊢ A -> Γ ++ Δ ⊢ A.
Proof.
  intros; eapply weakening2; eauto; intros.
  apply in_app_iff; left; auto.
Qed.

Lemma deduction :
  forall Γ A B, Γ ⊢ A → B -> A :: Γ ⊢ B.
Proof.
  intros.
  apply ImpE with A.
  - apply weakening2 with (Γ); auto.
    intros; right; auto.
  - constructor; left; auto.
Qed.

Lemma prov_impl :
  forall A B, Provable (A → B) -> forall Γ, Γ ⊢ A ->  Γ ⊢ B.
Proof.
  intros A B H Γ HA.
  apply ImpE with A; auto.
  rewrite <- (app_nil_l Γ).
  apply weakening; auto.
Qed.


Theorem Soundness_general :
  forall A Γ, Γ ⊢ A -> Γ ⊨ A.
Proof.
  intros A Γ H f.
  induction H; simpl; intros Hf; simpl; eauto;
  try simpl in IHNc;
  try simpl in IHNc1;
  try simpl in IHNc2;
  try (case_bool f A);
  try (case_bool f B; fail);
  try (apply IHNc || apply IHNc2; prove_satisfaction);
  case_bool f B;apply IHNc3; prove_satisfaction.
Qed.




End sound_mod.





