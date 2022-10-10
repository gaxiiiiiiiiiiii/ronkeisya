Require Import List Bool Lia Classical.

Import ListNotations.
From mathcomp Require Import ssreflect.

Variable var : Type.
Variable fls tru : var.

Inductive prop :=
  | Var : var -> prop
  | Not : prop -> prop
  | And : prop -> prop -> prop
  | Or : prop -> prop -> prop
  | Imp : prop -> prop -> prop
  (* | Top : prop *)
  (* | Bot : prop *)
  .



Notation "# p" := (Var p) (at level 1).
Notation "A ∨ B" := (Or A B) (at level 15, right associativity).
Notation "A ∧ B" := (And A B) (at level 15, right associativity).
Notation "A ⊃ B" := (Imp A B) (at level 16, right associativity).
Notation "¬ A" := (Not A) (at level 5).
(* Notation "⊥" := Bot (at level 0). *)
(* Notation "⊤" := ( Not Bot) (at level 0). *)
Notation "⊥" := (# fls).
Notation "⊤" := (# tru).

Definition assign := var -> bool.
Axiom fls_false : forall f : assign, f fls = false.
Axiom tru_true  : forall f : assign, f tru = true.


Fixpoint valuation (v : assign) (A : prop) :=
  match A with
  | # p => v p
  | ¬ A => negb (valuation v A)
  | A ∧ B => andb (valuation v A) (valuation v B)
  | A ∨ B => orb (valuation v A) (valuation v B)
  | A ⊃ B => implb (valuation v A) (valuation v B)
  (* | ⊤ => true *)
  (* | ⊥ => false *)
  end.

Definition tautology A :=
  forall v, valuation v A = true.

Definition equiv A B :=
  (A ⊃ B) ∧ (B ⊃ A).

Definition eqtot A B :=
  tautology (equiv A B).

Reserved Notation "Γ → Δ" (at level 80).
Inductive prv : list prop -> list prop -> Prop :=
  | init A : [A] → [A]
  | initTop : [] → [⊤]
  | initBot : [⊥] → []

  | weakL A Γ Δ : Γ → Δ -> (A :: Γ) → Δ
  | weakR A Γ Δ : Γ → Δ -> Γ → (Δ ++ [A])

  | contraL A Γ Δ : (A :: A :: Γ) → Δ -> (A :: Γ) → Δ
  | contraR A Γ Δ : Γ → (Δ ++ [A ; A]) -> Γ → (Δ ++ [A])

  | changeL A B Γ Π Δ : (Γ ++ A :: B :: Π) → Δ -> (Γ ++ B :: A :: Π) → Δ
  | changeR A B Γ Δ Σ : Γ → (Δ ++ A :: B :: Σ) -> Γ → (Δ ++ B :: A :: Σ)

  | cut A Γ Π Δ Σ : Γ → (Δ ++ [A]) -> A :: Π → Σ -> Γ ++ Π → Δ ++ Σ

  | andL1 A B Γ Δ : A :: Γ → Δ ->  A ∧ B :: Γ → Δ
  | andL2 A B Γ Δ : B :: Γ → Δ ->  A ∧ B :: Γ → Δ
  | andR A B Γ Δ : Γ → Δ ++ [A] -> Γ → Δ ++ [B] ->  Γ → Δ ++ [A ∧ B]

  | orL A B Γ Δ : A :: Γ → Δ -> B :: Γ → Δ -> A ∨ B :: Γ → Δ
  | orR1 A B Γ Δ : Γ → Δ ++ [A] -> Γ → Δ ++ [A ∨ B]
  | orR2 A B Γ Δ : Γ → Δ ++ [B] -> Γ → Δ ++ [A ∨ B]

  | impL A B Γ Π Δ Σ : Γ → Δ ++ [A] -> B :: Π → Σ -> A ⊃ B :: Γ ++ Π → Δ ++ Σ
  | impR A B Γ Δ : A :: Γ → Δ ++ [B] -> Γ → Δ ++ [A ⊃ B]

  | notL A Γ Δ : Γ → Δ ++ [A] -> ¬ A :: Γ → Δ
  | notR A Γ Δ : A :: Γ → Δ -> Γ → Δ ++ [¬ A]

  where "Γ → Δ" := (prv Γ Δ).

Lemma cons_app {A} (a : A) l :
  a :: l = [a] ++ l.
Proof.
  induction l => //=.
Qed.

(* 1.13 *)
Goal forall A, [] → [A ∨ ¬ A].
Proof.
  intro A.

  rewrite <- app_nil_l;
  apply contraR; simpl.

  rewrite cons_app;
  apply orR1; simpl.

  rewrite <- app_nil_l;
  apply changeR; simpl.

  rewrite cons_app;
  apply orR2.

  apply notR.
  apply init.
Qed.

(*　問1.14 *)
Goal forall A B, [(A ⊃ B)] → [¬ (A ∧ ¬ B)].
Proof.
  intros A B.
  rewrite <- app_nil_l;
  apply notR.

  rewrite <- (app_nil_l [_; _]);
  apply contraL.
  apply andL2.

  rewrite <- (app_nil_l [¬ B; A ∧ ¬ B; A ⊃ B]);
  apply changeL; simpl.
  apply andL1.

  rewrite cons_app;
  apply changeL; simpl.

  rewrite <- (app_nil_l ([A; A ⊃ B; ¬ B]));
  apply changeL; simpl.

  rewrite <- (app_nil_l nil);
  rewrite (cons_app A [¬ B]);
  eapply impL; simpl.
  - apply init.
  - rewrite <- (app_nil_l [B; ¬ B]);
    apply changeL; simpl.
    apply notL; simpl.
    apply init.
Qed.

Goal forall A B Γ Δ, A :: Γ → Δ ++ [B] -> Γ → Δ ++ [¬ A ∨ B].
Proof.
  intros A B Γ Δ H.
  apply contraR.
  assert (Δ ++ [¬ A ∨ B; ¬ A ∨ B] = (Δ ++ [¬ A ∨ B]) ++  [¬ A ∨ B]). {
    rewrite <- app_assoc; auto.
  }
  rewrite H0; clear H0.
  apply orR1.
  apply notR.
  apply orR2.
  apply H.
Qed.


(* 1.115.1 *)
Theorem cons_andor  A1 A2 B1 B2 :
  [A1; A2] → [B1; B2] -> [A1 ∧ A2] → [B1 ∨ B2].
Proof.
  intros H.
  apply contraL.
  apply andL2.
  rewrite <- (app_nil_l [_; _]);
  apply changeL; simpl.
  apply andL1.
  rewrite <- (app_nil_l [_ ∨ _]);
  apply contraR; simpl.
  assert ([B1 ∨ B2; B1 ∨ B2] = [B1 ∨ B2] ++ [B1 ∨ B2]) by auto;
  rewrite H0; clear H0;
  apply orR1; simpl.
  rewrite <- (app_nil_l [_; B1]);
  apply changeR; simpl.
  assert ([B1; B1 ∨ B2] = [B1] ++  [B1 ∨ B2]) by auto;
  rewrite H0; clear H0;
  apply orR2; simpl.
  auto.
Qed.

(* 1.115.2 *)
Theorem andor_imp A1 A2 B1 B2 :
  [A1 ∧ A2] → [B1 ∨ B2] -> [] → [A1 ∧ A2 ⊃ B1 ∨ B2].
Proof.
  intros H;
  rewrite <- (app_nil_l [_ ⊃ _]);
  apply impR; simpl.
  auto.
Qed.

(* 1.115.3 *)
Theorem imp_cons A1 A2 B1 B2 :
  [] → [A1 ∧ A2 ⊃ B1 ∨ B2] -> [A1 ; A2] → [B1 ; B2].
Proof.
  intro H.
  rewrite <- (app_nil_l [_; _]).
  rewrite <- (app_nil_l [B1;_]).
  apply cut with ( A := A1 ∧ A2 ⊃ B1 ∨ B2); simpl.
  - auto.
  - assert ([A1 ∧ A2 ⊃ B1 ∨ B2; A1; A2] = A1 ∧ A2 ⊃ B1 ∨ B2 ::  [A1; A2] ++ []) by auto;
    rewrite H0; clear H0;
    rewrite <- (app_nil_l [B1; B2]);
    apply impL; simpl.
    - rewrite <- (app_nil_l [_ ∧ _]);
      apply andR; simpl.
      - rewrite <- (app_nil_l [_ ; _]);
        apply changeL; simpl.
        apply weakL.
        apply init.
      - apply weakL.
        apply init.
    - apply orL.
      * rewrite (cons_app B1 [B2]);
        apply weakR.
        apply init.
      * rewrite <- app_nil_l;
        rewrite <- (app_nil_r [B1; B2]);
        apply changeR; simpl.
        rewrite (cons_app B2 [B1]);
        apply weakR.
        apply init.
Qed.


Fixpoint bigAnd l :=
  match l with
  | [] => ⊤
  | p :: l' => p ∧ bigAnd l'
  end.


Fixpoint bigOr l :=
  match l with
  | [] => ⊥
  | p :: l' => p ∨ bigOr l'
  end.

Notation "Γ ₊" := (bigAnd Γ)(at level 15).
Notation "Γ ⁺" := (bigOr Γ)(at level 15).

Lemma bigOr_app l r v :
  valuation v (bigOr (l ++ r)) = valuation v  (bigOr l ∨ bigOr r).
Proof.
  induction l => //=.
  rewrite fls_false => //=.
  rewrite IHl => /=.
  apply orb_assoc.
Qed.

Lemma bigAnd_app l r v :
  valuation v (bigAnd (l ++ r)) = valuation v  (bigAnd l ∧ bigAnd r).
Proof.
  induction l => //=.
  rewrite tru_true; simpl; auto .
  rewrite IHl => //=.
  apply andb_assoc.
Qed.


Theorem soundness Γ Δ :
  Γ → Δ -> tautology (bigAnd Γ ⊃ bigOr Δ).
Proof.
  induction 1; intro v; simpl;
    try repeat match goal with
    | [H : tautology _ |- _] => specialize (H v); simpl in H
    end;

    try rewrite bigOr_app in IHprv;
    try rewrite bigOr_app in IHprv1;
    try rewrite bigOr_app in IHprv2;
    try rewrite bigAnd_app in IHprv;
    try rewrite bigAnd_app in IHprv1;
    try rewrite bigAnd_app in IHprv2; simpl in *;

    try rewrite IHprv;
    try rewrite IHprv1;
    try rewrite IHprv2;
    try rewrite bigAnd_app;
    try rewrite bigOr_app;
    try rewrite fls_false;
    try rewrite tru_true; simpl; auto;

    try destruct (valuation v (bigAnd Γ));
    try destruct (valuation v (bigOr Δ));
    try destruct (valuation v (bigAnd Π));
    try destruct (valuation v (bigOr Σ));
    try destruct (valuation v A);
    try destruct (valuation v B); simpl; auto;

    try rewrite fls_false in IHprv;
    try rewrite fls_false in IHprv1;
    try rewrite fls_false in IHprv2; simpl in *; auto;
    inversion IHprv.
Qed.


Notation sqc := (prod (list prop) (list prop)).
Notation dcp :=( prod (option sqc) (option sqc)).

(* Inductive decomp : dcp -> sqc -> Prop :=
  | andRt A B Γ Δ1 Δ2 :
    decomp (Some (Γ, ( Δ1 ++ A :: Δ2)), (Some (Γ ,( Δ1 ++ B :: Δ2)))) (Γ, ( Δ1 ++ A ∧ B :: Δ2))
  | andLt A B Γ1 Γ2 Δ :
     decomp ((Some (Γ1 ++ A :: B :: Γ2, Δ)), None) ((Γ1 ++ A ∧ B :: Γ2 ), Δ)
  | orRt A B Γ Δ1 Δ2 :
    decomp (Some (Γ, ( Δ1 ++ A :: B :: Δ2)), None) (Γ, ( Δ1 ++ A ∨ B :: Δ2))
  | orLt A B Γ1 Γ2 Δ :
    decomp (Some ((Γ1 ++ A :: Γ2 ), Δ), Some ((Γ1 ++ B :: Γ2 ),Δ )) ((Γ1 ++ A ∨ B :: Γ2 ), Δ)
  | impRt A B Γ Δ1 Δ2 :
    decomp (Some ((A :: Γ ), ( Δ1 ++ B :: Δ2)), None) (Γ, ( Δ1 ++ A ⊃ B :: Δ2))
  | impLt A B Γ1 Γ2 Δ :
    decomp (Some ((Γ1 ++  Γ2 ), ( Δ ++ [A])), Some ((Γ1 ++ B :: Γ2 ), Δ)) ((Γ1 ++ A ⊃ B :: Γ2 ), Δ)
  | notRt A Γ Δ1 Δ2 :
    decomp (Some ((A :: Γ ), ( Δ1 ++ Δ2)), None) (Γ, ( Δ1 ++ ¬ A :: Δ2))
  | notLt A Γ1 Γ2 Δ :
    decomp (Some ((Γ1 ++ Γ2 ), ( Δ ++ [A])), None) ((Γ1 ++ ¬ A :: Γ2 ), Δ). *)





Inductive decomp : list prop -> list prop -> list prop -> list prop -> Prop :=
  | andR1P A B Γ Δ1 Δ2 : decomp Γ ( Δ1 ++ A :: Δ2) Γ ( Δ1 ++ A ∧ B :: Δ2)
  | andR2P A B Γ Δ1 Δ2 : decomp Γ ( Δ1 ++ B :: Δ2) Γ ( Δ1 ++ A ∧ B :: Δ2)
  | andLP A B Γ1 Γ2 Δ : decomp (Γ1 ++ A :: B :: Γ2 ) Δ (Γ1 ++ A ∧ B :: Γ2 ) Δ

  | orRP A B Γ Δ1 Δ2 : decomp Γ ( Δ1 ++ A :: B :: Δ2) Γ ( Δ1 ++ A ∨ B :: Δ2)
  | orLP1 A B Γ1 Γ2 Δ : decomp (Γ1 ++ A :: Γ2 ) Δ (Γ1 ++ A ∨ B :: Γ2 ) Δ
  | orLP2 A B Γ1 Γ2 Δ : decomp (Γ1 ++ B :: Γ2 ) Δ (Γ1 ++ A ∨ B :: Γ2 ) Δ

  | impRP A B Γ Δ1 Δ2 : decomp (A :: Γ ) ( Δ1 ++ B :: Δ2) Γ ( Δ1 ++ A ⊃ B :: Δ2)
  | impLP1 A B Γ1 Γ2 Δ : decomp (Γ1 ++  Γ2 ) ( Δ ++ [A]) (Γ1 ++ A ⊃ B :: Γ2 ) Δ
  | impLP2 A B Γ1 Γ2 Δ : decomp (Γ1 ++ B :: Γ2 ) Δ (Γ1 ++ A ⊃ B :: Γ2 ) Δ

  | notRP A Γ Δ1 Δ2 : decomp (A :: Γ ) ( Δ1 ++ Δ2) Γ ( Δ1 ++ ¬ A :: Δ2)
  | notLP A Γ1 Γ2 Δ : decomp (Γ1 ++ Γ2 ) ( Δ ++ [A]) (Γ1 ++ ¬ A :: Γ2 ) Δ.


Fixpoint count (A : prop) : nat :=
  match A with
  | # p => 0

  (* | ⊥ => 0 *)
  | ¬ B => 1 + count B
  | B ∧ C => 1 + count B + count C
  | B ∨ C => 1 + count B + count C
  | B ⊃ C => 1 + count B + count C
  end.



Fixpoint sum l : nat :=
  match l with
  | [] => 0
  | a :: l' => a + sum l'
  end.

Definition counts (l : list prop) := sum (map count l).
Definition counts' p := counts (fst p) + counts (snd p).


Theorem sum_app l r :
  sum (l ++ r) = sum l + sum r.
Proof.
  induction l => //=.
  rewrite IHl.
  rewrite PeanoNat.Nat.add_assoc; auto.
Qed.

(* Theorem decomp_lt pp p :
  decomp pp p ->
  match pp with
  | (Some pl, None) => counts' pl < counts' p
  | (Some pl, Some pr) => counts' pl < counts' p /\ counts' pr < counts' p
  | _ => False
  end.
Proof.
  move => H; induction H; try split;
  rewrite /counts' /counts;
  repeat rewrite  map_app sum_app => //=; lia.
Qed. *)


Theorem decomp_lt Γ Δ Γ' Δ' :
  decomp Γ' Δ' Γ Δ -> counts Γ' + counts Δ' < counts Γ + counts Δ.
Proof.
  induction 1;
  repeat rewrite /counts map_app sum_app //=; try lia.
Qed.

Definition tautology' p := tautology (((fst p)₊ ⊃ (snd p)⁺)).

(* Theorem decomp_tautology pp p :
  decomp pp p -> tautology' p ->
  match pp with
  | (Some pl, None) => tautology' p
  | (Some pl, Some pr) => tautology' pl /\ tautology' pr
  | _ => False
  end.
Proof.
  inversion_clear 1 => H; try split;
  move => f;
  specialize (H f);
  simpl in *;
  try rewrite bigOr_app;
  try rewrite bigAnd_app;
  try rewrite bigOr_app in H;
  try rewrite bigAnd_app in H;
  simpl in *;
  try destruct (valuation f A);
  try destruct (valuation f B);
  try destruct (valuation f (bigAnd Γ));
  try destruct (valuation f (bigAnd Γ1));
  try destruct (valuation f (bigAnd Γ2));
  try destruct (valuation f (bigOr Δ));
  try destruct (valuation f (bigOr Δ1));
  try destruct (valuation f (bigOr Δ2));
  simpl in *; auto; inversion H.
Qed. *)




(* 1.10.2 *)
Theorem decomp_tautology Γ Δ Γ' Δ' :
  decomp Γ' Δ' Γ Δ -> tautology (Γ₊⊃Δ⁺) -> tautology (Γ'₊⊃Δ'⁺).
Proof.
  move => H;
    inversion_clear H => H f;
    specialize (H f);
    simpl in *;
    try rewrite bigOr_app;
    try rewrite bigAnd_app;
    try rewrite bigOr_app in H;
    try rewrite bigAnd_app in H;
    simpl in *;
    try destruct (valuation f A);
    try destruct (valuation f B);
    try destruct (valuation f (bigAnd Γ));
    try destruct (valuation f (bigAnd Γ1));
    try destruct (valuation f (bigAnd Γ2));
    try destruct (valuation f (bigOr Δ));
    try destruct (valuation f (bigOr Δ1));
    try destruct (valuation f (bigOr Δ2));
    simpl in *; auto; inversion H.
Qed.

Theorem in_ex {A} (a : A) (l : list A) :
  In a l -> exists h t, l = h ++ a :: t.
Proof.
  induction l => H //=.
  induction H; subst.
  - exists [], l; auto.
  - move : (IHl H) => [h [t Hl]]; subst.
    exists (a0 :: h), t; auto.
Qed.

Definition allf := fun _ : var => false.



Definition allt := fun _ : var => true.






Reserved Notation "Γ ⟶ Δ" (at level 80).
Inductive prv' : list prop -> list prop -> Prop :=
  | initc A : [A] ⟶ [A]
  | initTopc : [] ⟶ [⊤]
  | initBotc : [⊥] ⟶ []

  | weakLc A Γ Δ : Γ ⟶ Δ -> (A :: Γ) ⟶ Δ
  | weakRc A Γ Δ : Γ ⟶ Δ -> Γ ⟶ (Δ ++ [A])

  | contraLc A Γ Δ : (A :: A :: Γ) ⟶ Δ -> (A :: Γ) ⟶ Δ
  | contraRc A Γ Δ : Γ ⟶ (Δ ++ [A ; A]) -> Γ ⟶ (Δ ++ [A])

  | changeLc A B Γ Π Δ : (Γ ++ A :: B :: Π) ⟶ Δ -> (Γ ++ B :: A :: Π) ⟶ Δ
  | changeRc A B Γ Δ Σ : Γ ⟶ (Δ ++ A :: B :: Σ) -> Γ ⟶ (Δ ++ B :: A :: Σ)

  | andL1c A B Γ Δ : A :: Γ ⟶ Δ ->  A ∧ B :: Γ ⟶ Δ
  | andL2c A B Γ Δ : B :: Γ ⟶ Δ ->  A ∧ B :: Γ ⟶ Δ
  | andRc A B Γ Δ : Γ ⟶ Δ ++ [A] -> Γ ⟶ Δ ++ [B] ->  Γ ⟶ Δ ++ [A ∧ B]

  | orLc A B Γ Δ : A :: Γ ⟶ Δ -> B :: Γ ⟶ Δ -> A ∨ B :: Γ ⟶ Δ
  | orR1c A B Γ Δ : Γ ⟶ Δ ++ [A] -> Γ ⟶ Δ ++ [A ∨ B]
  | orR2c A B Γ Δ : Γ ⟶ Δ ++ [B] -> Γ ⟶ Δ ++ [A ∨ B]

  | impLc A B Γ Π Δ Σ : Γ ⟶ Δ ++ [A] -> B :: Π ⟶ Σ -> A ⊃ B :: Γ ++ Π ⟶ Δ ++ Σ
  | impRc A B Γ Δ : A :: Γ ⟶ Δ ++ [B] -> Γ ⟶ Δ ++ [A ⊃ B]

  | notLc A Γ Δ : Γ ⟶ Δ ++ [A] -> ¬ A :: Γ ⟶ Δ
  | notRc A Γ Δ : A :: Γ ⟶ Δ -> Γ ⟶ Δ ++ [¬ A]
  where "Γ ⟶ Δ" := (prv' Γ Δ).








Theorem changeL' A l1 l2 r :
  l1 ++ l2 ++ [A] ⟶ r -> l1 ++ A :: l2 ⟶ r.
Proof.
  move : l1; induction l2 => //= l1 H.
  apply changeLc.
  assert (a :: A :: l2 = [a] ++ A :: l2) by induction l2 => //=.
  rewrite H0; clear H0.
  rewrite app_assoc.
  apply IHl2.
  rewrite <- app_assoc.
  assert ([a] ++ l2 ++ [A] = a :: l2 ++ [A]) by induction l2 => //=.
  rewrite H0; clear H0; auto.
Qed.

Theorem changeL'' A l1 l2 r :
  l1 ++ A :: l2 ⟶ r -> l1 ++ l2 ++ [A] ⟶ r.
Proof.
  move : l1.
  induction l2 => /= l1 H //=.
  rewrite app_comm_cons.
  rewrite app_assoc.
  assert (l1 ++ a :: l2 = (l1 ++ [a]) ++ l2). {
    clear H.
    induction l1 => //=.
    rewrite IHl1; auto.
  }
  rewrite H0; clear H0.
  rewrite <- app_assoc.
  apply IHl2.
  assert ((l1 ++ [a]) ++ A :: l2 = l1 ++ a :: A :: l2). {
    clear H; induction l1 => //=; rewrite IHl1; auto.
  }
  rewrite H0; clear H0.
  apply changeLc; auto.
Qed.






Theorem changeR' A l r1 r2 :
  l ⟶ r1 ++ r2 ++ [A] -> l ⟶ r1 ++ A :: r2.
Proof.
  move : r1; induction r2 => //= r1 H.
  apply changeRc.
  assert (a :: A :: r2 = [a] ++ A :: r2) by induction r2 => //=.
  rewrite H0; clear H0.
  rewrite app_assoc.
  apply IHr2.
  rewrite <- app_assoc.
  assert ([a] ++ r2 ++ [A] = a :: r2 ++ [A]) by induction r2 => //=.
  rewrite H0; clear H0; auto.
Qed.

Theorem changeR'' A l r1 r2 :
l ⟶ r1 ++ A :: r2 ->  l ⟶ r1 ++ r2 ++ [A] .
Proof.
  move : r1; induction r2 => r1 H //=.
  rewrite app_comm_cons.
  rewrite app_assoc.
  assert (r1 ++ a :: r2 = (r1 ++ [a]) ++ r2). {
    clear H.
    induction r1 => //=.
    rewrite IHr1; auto.
  }
  rewrite H0; clear H0.
  rewrite <- app_assoc.
  apply IHr2.
  assert ((r1 ++ [a]) ++ A :: r2 = r1 ++ a :: A :: r2). {
    clear H; induction r1 => //=; rewrite IHr1; auto.
  }
  rewrite H0; clear H0.
  apply changeRc; auto.
Qed.

Theorem swapL l1 l2 r :
  (l1 ++ l2) ⟶ r -> (l2 ++ l1) ⟶ r.
Proof.
  move : l1; induction l2 => l1 //= H.
  - rewrite app_nil_r in H; auto.
  - rewrite cons_app app_assoc in H.
    apply IHl2 in H.
    rewrite app_comm_cons.
    assert (a :: l2 = [a] ++ l2) by (induction l2 => //=).
    rewrite H0; clear H0.
    rewrite <- app_assoc.
    rewrite <- (app_nil_l (_ ++ _)).
    apply changeL'; simpl.
    rewrite <- app_assoc; auto.
Qed.

Theorem swapR l r1 r2 :
  l ⟶ r1 ++ r2 -> l ⟶ r2 ++ r1.
Proof.
  move : r1; induction r2 => r1 //= H.
  - rewrite app_nil_r in H; auto.
  - rewrite cons_app app_assoc in H.
    apply IHr2 in H.
    rewrite app_comm_cons.
    rewrite cons_app.
    rewrite <- app_assoc.
    rewrite <- (app_nil_l (_ ++ _)).
    apply changeR'; simpl.
    rewrite <- app_assoc; auto.
Qed.

Theorem changeL''' A l1 l2 r :
  A :: (l1 ++ l2) ⟶ r -> l1 ++ A :: l2 ⟶ r.
Proof.
  move : r l2; induction l1 => //= r l2 H.
  rewrite <- (app_nil_l (a :: _)).
  apply changeL'; simpl.
  rewrite <- app_assoc.
  rewrite cons_app.
  rewrite <- app_assoc.
  rewrite <- (cons_app A).
  apply IHl1.
  rewrite cons_app.
  apply swapL.
  repeat rewrite <- app_assoc.
  rewrite app_assoc; simpl.
  apply changeLc.
  apply swapL; simpl; auto.
Qed.

Theorem weakL' A l r :
  [A] ⟶ r -> A :: l ⟶ r .
Proof.
  move : A r; induction l => // A r H.
  rewrite <- (app_nil_l (A :: _)).
  apply changeLc; simpl.
  apply weakLc.
  apply IHl; auto.
Qed.

Theorem weakR' A l r :
  l ⟶ [A] -> l ⟶ r ++ [A].
Proof.
  move : A l; induction r => //= A l H.
  rewrite <- (app_nil_l (a :: _)).
  apply changeR'; simpl.
  apply weakRc.
  apply IHr; auto.
Qed.

(* 1.11.2 *)
Theorem same_elm A Γ1 Γ2 Δ1 Δ2 :
  Γ1 ++ A :: Γ2 ⟶ Δ1 ++ A :: Δ2.
Proof.
  apply changeL'''.
  apply changeR'.
  apply weakL'.
  rewrite app_assoc.
  apply weakR'.
  apply initc.
Qed.



Theorem contraR' l r1 r2 :
  l ⟶ r1 ++ r2 ++ r2 -> l ⟶ r1 ++ r2.
Proof.
  move : r1; induction r2 => r1 H //=.
  rewrite cons_app app_assoc.
  apply IHr2.
  rewrite <- app_assoc.
  apply changeR'.
  rewrite app_assoc.
  apply contraRc.
  rewrite cons_app in H.
  rewrite <- app_assoc in H.
  apply changeR'' in H.
  rewrite app_assoc in H.
  rewrite (app_assoc r1 r2) in H.
  rewrite <- app_assoc in H.
  assert (([a] ++ r2) ++ [a] = [a] ++ r2 ++ [a]).
    rewrite app_assoc; auto.
  rewrite H0 in H.
  apply changeR'' in H.
  repeat rewrite <- app_assoc in H.
  simpl in H.
  repeat rewrite <- app_assoc; auto.
Qed.

Theorem contraL' l1 l2 r :
  l1 ++ l2 ++ l2 ⟶ r -> l1 ++ l2 ⟶ r.
Proof.
  move : l1; induction l2 => l1 H //=.
  rewrite cons_app app_assoc.
  apply IHl2.
  rewrite <- app_assoc.
  apply swapL.
  repeat rewrite  <- app_assoc.
  rewrite <- cons_app.
  apply contraLc.
  repeat rewrite app_comm_cons.
  rewrite app_assoc.
  apply swapL.
  repeat rewrite <- app_comm_cons.
  apply changeL'.
  rewrite <- app_comm_cons.
  apply changeL'.
  repeat rewrite <- app_assoc.
  rewrite <- app_comm_cons in H.
  apply changeL'' in H.
  repeat rewrite app_assoc in H.
  rewrite <- app_assoc in H.
  rewrite <- app_comm_cons in H.
  apply changeL'' in H.
  repeat rewrite <- app_assoc in H; auto.
Qed.

Definition prv'' (pp : dcp) :=
    match pp with
    | (Some p, None) => fst p ⟶ snd p
    | (Some pl, Some pr) => fst pl ⟶ snd pl /\ fst pr ⟶ snd pr
    | _ => False
    end.





Theorem decomp_prv A B X Y :
  (* decomp X Y A B <==> X ⟶ Y が A ⟶ B の分解 *)
  (forall X Y, decomp X Y A B -> X ⟶ Y) ->
  decomp X Y A B ->
  X ⟶ Y -> A ⟶ B.
Proof.
  move => H0 Hd XY.
  inversion Hd; subst.
  - apply changeR'.
    rewrite app_assoc.
    apply andRc;
      rewrite <- app_assoc;
      eapply changeR'' => //.
    apply H0; constructor.
  - apply changeR'.
    rewrite app_assoc.
    apply andRc;
      rewrite <- app_assoc;
      eapply changeR'' => //.
    apply H0; constructor.
  - apply swapL.
    rewrite <- app_comm_cons.
    apply contraLc.
    apply andL1c.
    rewrite <- (app_nil_l (_ :: _)); apply changeL'; simpl.
    apply andL2c.
    rewrite <- (app_nil_l (_ :: _)); apply changeL'; simpl.
    repeat rewrite <- app_assoc.
    apply swapL.
    repeat rewrite <- app_assoc.
    repeat rewrite <- cons_app; auto.
  - apply swapR.
    rewrite cons_app.
    rewrite <- app_assoc.
    rewrite <- (app_nil_l).
    apply changeR'; simpl.
    apply contraRc.
    rewrite cons_app app_assoc.
    apply orR1c.
    rewrite <- app_assoc.
    apply changeR'.
    rewrite app_assoc.
    apply orR2c.
    repeat rewrite <- app_assoc.
    apply swapR.
    repeat rewrite <- app_assoc.
    repeat rewrite <- cons_app; auto.
  - apply swapL.
    rewrite <- app_comm_cons.
    apply orLc.
    - rewrite <- (app_nil_l (_ :: _)). apply changeL'; simpl.
      rewrite <- app_assoc.
      apply swapL.
      rewrite <- app_assoc, <- cons_app; auto.
    - rewrite <- (app_nil_l (_ :: _)). apply changeL'; simpl.
      rewrite <- app_assoc.
      apply swapL.
      rewrite <- app_assoc, <- cons_app.
      apply H0; constructor.
  - apply swapL.
    rewrite <- app_comm_cons.
    apply orLc.
    - rewrite <- (app_nil_l (_ :: _)). apply changeL'; simpl.
      rewrite <- app_assoc.
      apply swapL.
      rewrite <- app_assoc, <- cons_app.
      apply H0; constructor.
    - rewrite <- (app_nil_l (_ :: _)). apply changeL'; simpl.
      rewrite <- app_assoc.
      apply swapL.
      rewrite <- app_assoc, <- cons_app; auto.
  - rewrite cons_app.
    apply swapR.
    rewrite <- app_assoc, <- app_nil_l.
    apply changeR'; simpl.
    apply impRc.
    rewrite <- app_assoc.
    apply swapR.
    rewrite <- app_assoc.
    rewrite <- cons_app; auto.
  - apply swapL.
    rewrite <- app_comm_cons.
    rewrite <- app_nil_l.
    apply contraR'; simpl.
    rewrite cons_app.
    apply contraL'.
    rewrite <- cons_app.
    apply impLc.
    - apply swapL; auto.
    - rewrite cons_app app_assoc.
      apply swapL.
      rewrite <- cons_app.
      apply H0; constructor.
  { apply swapL.
    rewrite <- app_comm_cons;
    rewrite <- app_nil_l;
    apply contraR'; simpl.
    rewrite cons_app;
    apply contraL'.
    rewrite <- cons_app;
    apply impLc.
    - apply swapL.
      apply H0.
      constructor.
    - rewrite cons_app app_assoc;
      apply swapL.
      rewrite <- cons_app.
      auto.
  }
  - apply changeR'.
    rewrite app_assoc.
    apply notRc; auto.
  - apply swapL.
    rewrite cons_app.
    rewrite  <- app_assoc.
    rewrite <- cons_app.
    apply notLc.
    apply swapL; auto.
Qed.




Lemma op_ex l :
  counts l > 1 ->
    (exists A B, In (A ∧ B) l) \/
    (exists A B, In (A ∨ B) l) \/
    (exists A B, In (A ⊃ B) l) \/
    (exists A, In (¬ A) l).
Proof.
  induction l => H; [inversion H|].
  destruct a; try (
    rewrite /counts in H;
    move : (IHl H) => [[A [B H']] | [[A [B H']] | [[A [B H']] | [A  H']]]];
    [left | right; left | right; right; left | right; right; right];
    try (exists A, B; right; auto );
    exists A; right; auto);
    [right; right; right | left | right; left | right; right; left];
    try (exists a; left; auto);
    exists a1, a2; left; auto.
Qed.



Inductive tree : list prop -> list prop -> Type :=
  | leaf l r : counts l = 0 -> counts r = 0 -> tree l r
  | andRt A B Γ Δ1 Δ2 :
    tree Γ ( Δ1 ++ A :: Δ2) -> tree Γ ( Δ1 ++ B :: Δ2) -> tree Γ ( Δ1 ++ A ∧ B :: Δ2)
  | andLt A B Γ1 Γ2 Δ :
    tree (Γ1 ++ A :: B :: Γ2 ) Δ -> tree (Γ1 ++ A ∧ B :: Γ2 ) Δ
  | orRt A B Γ Δ1 Δ2 :
    tree Γ ( Δ1 ++ A :: B :: Δ2) -> tree  Γ ( Δ1 ++ A ∨ B :: Δ2)
  | orLt A B Γ1 Γ2 Δ :
    tree (Γ1 ++ A :: Γ2 ) Δ -> tree  (Γ1 ++ B :: Γ2 ) Δ ->  tree (Γ1 ++ A ∨ B :: Γ2 ) Δ
  | impRt A B Γ Δ1 Δ2 :
    tree (A :: Γ ) ( Δ1 ++ B :: Δ2) -> tree Γ ( Δ1 ++ A ⊃ B :: Δ2)
  | impLt A B Γ1 Γ2 Δ :
    tree (Γ1 ++  Γ2 ) ( Δ ++ [A]) -> tree (Γ1 ++ B :: Γ2 ) Δ  ->tree (Γ1 ++ A ⊃ B :: Γ2 ) Δ
  | notRt A Γ Δ1 Δ2 :
    tree (A :: Γ ) ( Δ1 ++ Δ2) -> tree Γ ( Δ1 ++ ¬ A :: Δ2)
  | notLt A Γ1 Γ2 Δ :
    tree (Γ1 ++ Γ2 ) ( Δ ++ [A]) -> tree (Γ1 ++ ¬ A :: Γ2 ) Δ
  .

Fixpoint leaves {l r} (t : tree l r) : list (list prop * list prop):=
  match t with
  | andRt _ _ _ _ _ l' r' => leaves l' ++ leaves r'
  | andLt _ _ _ _ _ t' => leaves t'
  | orRt _ _ _ _ _ t' => leaves t'
  | orLt _ _ _ _ _ l' r' => leaves l' ++ leaves r'
  | impRt _ _ _ _ _ t' => leaves t'
  | impLt _ _ _ _ _ l' r' => leaves l' ++ leaves r'
  | notRt _ _ _ _ t' => leaves t'
  | notLt _ _ _ _ t' => leaves t'
  | leaf l' r' _ _ => [(l',r')]
  (* | _ => [] *)
  end.









Theorem leaves_counts0 l r (t : tree l r) :
  Forall (fun p => counts' p = 0) (leaves t).
Proof.
  induction t => //=; try (rewrite Forall_app; split; auto).
  constructor => //=.
  rewrite  /counts' => //=.
  rewrite e e0; auto.
Qed.



Inductive path (p : list prop * list prop) : (list prop * list prop) -> Prop :=
  | here : path p p
  | step A B X Y : decomp X Y A B -> path p (A,B) -> path p (X,Y).

Theorem path_taut p X Y :
  tautology' p ->  path p (X, Y) -> tautology' (X,Y).
Proof.
  move => H H0.
  induction H0; subst => //=.
  eapply decomp_tautology; eauto.
Qed.

Theorem leaves_path l r (t : tree l r) :
  forall p, In p (leaves t) -> path (l,r) p.
Proof.
  induction t => /= p Hp;
  try (case : Hp; [move ->; constructor| move => F; inversion F] );
  try (apply in_app_or in Hp; case : Hp; [
       move /IHt1 | move /IHt2] => H;
       induction H; econstructor; eauto; constructor);
  try (apply IHt in Hp; induction Hp; (econstructor; eauto); constructor).
Qed.

Theorem leaves_taut l r (t : tree l r) :
  tautology' (l,r) -> forall p, In p (leaves t) -> tautology' p.
Proof.
  move => H [l' r'] /leaves_path /path_taut.
  apply; auto.
Qed.

Theorem tree_taut l r (t : tree l r) :
  (forall l' r', In (l',r') (leaves t) -> l' ⟶ r') -> l ⟶ r.
Proof.
  move => H.
  induction t.
  -apply H; left => //.
  - apply changeR';
    rewrite app_assoc;
    apply andRc;
    rewrite <- app_assoc;
    apply swapR;
    rewrite <- app_assoc;
    apply changeR';
    apply swapR;
    rewrite <- app_assoc;
    rewrite <- cons_app;
    [apply IHt1| apply IHt2];
    move => l' r' Hp; apply H => /=;
    apply in_or_app;
    [left| right]; auto.
Admitted.

Theorem ex_tree l r :
  counts l + counts r <> 0 -> tree l r.
Proof.
Admitted.


Theorem completeness l r :
  tautology' (l,r) -> l ⟶ r.
Proof.
  move => H.
Admitted.


Fixpoint subform A B :=
  match B with
  | L ∧ R => A = B \/ subform A L \/ subform A R
  | L ∨ R => A = B \/ subform A L \/ subform A R
  | L ⊃ R => A = B \/ subform A L \/ subform A R
  | ¬ B' => A = B \/ subform A B'
  | _ => A = B
  end.



Fixpoint noImp (A : prop) : Prop :=
  match A with
  | L ∧ R => noImp L /\ noImp R
  | L ∨ R => noImp L /\ noImp R
  | _ ⊃ _ => False
  | ¬ A' => noImp A'
  | _ => True
  end.



Fixpoint dual (A : prop) : prop :=
  match A with
  | L ∧ R => dual L ∨ dual R
  | L ∨ R => dual L ∧ dual R
  | L ⊃ R => dual L ⊃ dual R
  | _ => A
  end.

Axiom entail_imp :
  forall A B, A → B <-> [] → [bigAnd A ⊃ bigOr B].

Axiom dummy : assign.
(* Axiom dummy_bot : dummy fls = false. *)
(* Axiom dummy_top : dummy tru = true. *)

Theorem nil_entail_nil :
  ~ ([] → []).
Proof.
  move /entail_imp => /= /soundness F.
  move : (F dummy); simpl.
  move => f; inversion f.
Qed.











Theorem to_entail A :
  [] → A -> In ⊤ A.
Proof.
  induction A.
  - move => F; case (nil_entail_nil F).
  - move => H.
    inversion a.
Admitted.

Theorem dual_entail_extension L R:
  Forall noImp L -> Forall noImp R -> L → R -> map dual L → map dual R.
Proof.
  move : R; induction L => R HL HR H; simpl.
Admitted.

Theorem cut_elim A B :
  A → B -> A ⟶ B.
Proof.
  move /soundness => H.
  apply completeness; auto.
Qed.

Theorem cut_intro A B :
  A ⟶ B -> A → B.
Proof.
Admitted.

Axiom entail_top :
  forall v, [] → [# v] -> # v = ⊤.

Axiom bot_entail :
  forall v, [# v] → [] -> # v = ⊥.

Lemma var_entail v A :
  [# v] → [A] -> A = # v \/ A = ⊤ \/ # v = ⊥.
Proof.
  move : v.
  induction A => u H.
  { admit. }
  {
    admit.
  }
  {

  }

Admitted.




Theorem prv_prop_ind (P : prop -> prop -> Prop) :
  (forall v B, # v = B -> P #v B) ->
  (forall B, P ⊥ B) ->
  (forall Al Ar B, [Al ∧ Ar] ⟶ [B] -> P (Al ∧ Ar) B) ->
  (forall Al Ar B, [Al ∨ Ar] ⟶ [B] -> P (Al ∨ Ar) B) ->
  (forall Al Ar B, [Al ⊃ Ar] ⟶ [B] -> P (Al ⊃ Ar) B) ->
  (forall A B, [¬ A] ⟶ [B] -> P (¬ A) B) ->
  forall A B, [A] ⟶ [B] -> P A B.
Proof.
  intros.
  destruct A; eauto.
Qed.



Theorem dual_entail A B :
  noImp A -> noImp B -> [A] → [B] -> [dual B] → [dual A].
Proof.
  move  => HA HB /cut_elim H.
  apply prv_prop_ind with (P := fun A B => [dual B] → [dual A]); intros; auto; simpl.
  Check prv'_ind.
  - admit.
  - admit.
  - apply cut_intro; apply completeness.
Restart.
  move => HA HB /soundness H.
  apply cut_intro.
  apply completeness => f.
  move : (H f); clear H; simpl.
  repeat rewrite andb_true_r orb_false_r.
  induction A; simpl; auto => H.
Restart.
  move => HA HB /cut_elim H.
  (* apply cut_intro. *)
  inversion H; subst.
  - constructor.
  - apply cut_intro.
    apply completeness => f.
    apply cut_intro in H; apply soundness in H; move : (H f); clear H .
    apply cut_intro in H3; apply soundness in H3; move : (H3 f); clear H3.
    simpl.
    repeat rewrite andb_true_r orb_false_r => fB.
    rewrite andb_true_r orb_false_r.
    rewrite fB.
    rewrite implb_true_r => _.

Restart.
  move => HA HB.
  move /cut_elim.
  eapply (prv_prop_ind (fun )).
  induction A; simpl.
  try match goal with
  | [ F : noImp (_ ⊃ _) |- _] => inversion F
  end.
  apply prv'_ind; intros; try solve [constructor].
  -











