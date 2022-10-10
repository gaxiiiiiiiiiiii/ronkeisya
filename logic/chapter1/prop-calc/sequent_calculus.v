Require Export completeness.
Set Implicit Arguments.

Module Type sequent_mod (B : base_mod) (S : sound_mod B) (C : complete_mod B S).
Import B S C.

Reserved Notation "Γ ⊃ A" (at level 80).
Inductive G : list PropF -> list PropF -> Prop :=
  | Gax A Γ Δ : In A Γ -> In A Δ -> Γ ⊃ Δ
  | GBot Γ Δ : In ⊥ Γ -> Γ ⊃ Δ
  | AndL A B Γ1 Γ2 Δ :
      Γ1 ++ A :: B :: Γ2 ⊃ Δ -> Γ1 ++ A ∧ B :: Γ2 ⊃ Δ
  | AndR A B Γ Δ1 Δ2 :
      Γ ⊃ Δ1 ++ A :: Δ2 -> Γ ⊃ Δ1 ++ B :: Δ2 -> Γ ⊃ Δ1 ++ A ∧ B :: Δ2
  | OrL A B Γ1 Γ2 Δ :
      Γ1 ++ A :: Γ2 ⊃ Δ -> Γ1 ++ B :: Γ2 ⊃ Δ -> Γ1 ++ A ∨ B :: Γ2 ⊃ Δ
  | OrR A B Γ Δ1 Δ2 :
       Γ ⊃ Δ1 ++ A :: B :: Δ2 -> Γ ⊃ Δ1 ++ A ∨ B :: Δ2
  | ImpL A B Γ1 Γ2 Δ :
      Γ1 ++ B :: Γ2 ⊃ Δ -> Γ1 ++ Γ2 ⊃ A :: Δ -> Γ1 ++ A → B :: Γ2 ⊃ Δ
  | ImpR A B Γ Δ1 Δ2 :
      A :: Γ ⊃ Δ1 ++ B :: Δ2 -> Γ ⊃ Δ1 ++ A → B :: Δ2
  | Cut A Γ Δ : Γ ⊃ A :: Δ -> A :: Γ ⊃ Δ -> Γ ⊃ Δ
  where "Γ ⊃ Δ" := (G Γ Δ) : My_scope.

Definition BigOr := fold_right Disj ⊥.
Notation "⨆ Δ" := (BigOr Δ)(at level 19).

(* Γ ⊢⊢ Δ iff forall A ∈ Δ, Γ ⊢ A *)
Definition Ncl Γ := map_fold_right (Nc Γ) and True.
Notation "Γ ⊢⊢ Δ" := (Ncl Γ Δ)(at level 80).
Notation "¬l Γ" := (map Neg Γ)(at level 40).

Lemma NegAnd_impl_OrNeg Γ A B :
  Γ ⊢ ¬ (A ∧ B) -> Γ ⊢ ¬ A ∨ ¬ B.
Proof.
  move => H.
  eapply OrE with A (¬ A).
  - apply Excluded_Middle.
  - apply OrI2.
    apply ImpI.
    apply ImpE with (A ∧ B).
    * apply weakening2 with Γ; auto.
      intros; right; right; auto.
    * apply AndI; is_ass.
  - apply OrI1. is_ass.
Restart.
  intro H.
  eapply prov_impl with (¬ (A ∧ B)); auto.
  apply ImpI.
  apply BotC.
  apply ImpE with (A ∧ B).
  - is_ass.
  - apply AndI; apply BotC;
    eapply ImpE with (¬ A ∨ ¬ B);
    [| apply OrI1| | apply OrI2]; is_ass.
Qed.

Lemma Nc_list_weakening Γ1 Γ2 Δ :
  (forall B, In B Γ1 -> In B Γ2) -> Γ1 ⊢⊢ Δ -> Γ2 ⊢⊢ Δ.
Proof.
   induction Δ; rewrite /Ncl => //= H H1.
   destruct H1 as [Ha H1].
   split.
   -  apply weakening2 with Γ1; auto.
   -  apply IHΔ; auto.
Qed.


Lemma Nc_list_impl Γ A :
  Γ ⊢ A -> forall Δ, Δ ⊢⊢ Γ -> Δ ⊢ A.
Proof.
  move : A.
  induction Γ => /= A H Δ HD.
  - rewrite <- (app_nil_l Δ).
    apply weakening; auto.
  - destruct HD as [Ha HD].
    apply ImpE with a; auto.
    apply IHΓ; auto.
    apply ImpI; auto.
Qed.

Lemma Nc_list_contained Γ Δ :
  (forall B, In B Δ -> In B Γ) -> Γ ⊢⊢ Δ.
Proof.
  move : Γ.
  induction Δ; rewrite /Ncl; simpl; auto => Γ H.
  split.
  - apply weakening2 with (a :: Δ); auto; is_ass.
  - apply IHΔ; intros; apply H.
    right; auto.
Qed.


Lemma Nc_list_app Γ Δ1 Δ2 :
  Γ ⊢⊢ Δ1 -> Γ ⊢⊢ Δ2 -> Γ ⊢⊢ Δ1++Δ2.
Proof.
  move : Γ Δ2.
  induction Δ1; simpl; auto => Γ Δ2 [Ha H1] H2; split; auto.
  apply IHΔ1; auto.
Qed.


Ltac Ncl_solve := repeat match goal with
| |- _ ⊢ _     => idtac
| |- _ ⊢⊢ _::_ => split;[eassumption||(try (is_ass;fail))|]
| |- _ ⊢⊢ _++_ => apply Nc_list_app
| |- map_fold_right (Nc ?Γ) and True _ => change (map_fold_right (Nc Γ) and True) with (Ncl Γ)
| _            => eassumption||(apply Nc_list_contained;in_solve)
end.

Ltac destruct_or :=
  try repeat match goal with
  | |- _ \/ _ -> _ => intro
  | H : _ \/ _ |- _ => destruct H
  end.

Lemma G_to_Nc_Neg Γ Δ :
  Γ ⊃ Δ -> Γ ++ (¬l Δ) ⊢ ⊥.
Proof.
  induction 1.
  {
    apply ImpE with A.
    - is_ass.
      move : (in_split _ _ H0) => [l1 [l2]] ->.
      rewrite in_app_iff map_app in_app_iff; simpl.
      right; right; left; auto.
    - apply weakening; is_ass.
  }{
    apply weakening; is_ass.
  }{
    eapply Nc_list_impl with ((Γ1 ++ A :: B :: Γ2) ++ ¬l Δ); auto.
    repeat apply Nc_list_app.
    - apply Nc_list_contained; in_solve.
    - repeat split; Ncl_solve.
      * apply Nc_list_impl with [A ∧ B].
        apply AndE1 with B; is_ass.
        repeat is_ass.
      * apply Nc_list_impl with [A ∧ B].
        apply AndE2 with A; is_ass.
        repeat is_ass.
    - Ncl_solve.
  }{
    move : IHG1 IHG2.
    repeat rewrite map_app; simpl => IH1 IH2.
    apply OrE with (¬ A) (¬ B).
    - apply NegAnd_impl_OrNeg; is_ass.
    - eapply weakening2.
      apply IH1.
      intro C; simpl.
      repeat rewrite in_app_iff; simpl; intro.
      destruct_or.
        right; left; auto.
        right; right; left; auto.
        left; auto.
        right; right; right; right; auto.
    - eapply weakening2.
      apply IH2.
      intro C; simpl.
      repeat rewrite in_app_iff; simpl; intro.
      destruct_or.
        right; left; auto.
        right; right; left; auto.
        left; auto.
        right; right; right; right; auto.
  }{
    apply OrE with A B.
    - is_ass.
    - eapply Nc_list_impl.
      apply IHG1.
      apply Nc_list_contained; in_solve.
    - eapply Nc_list_impl.
      apply IHG2.
      apply Nc_list_contained; in_solve.
  }{
    move : IHG; repeat rewrite map_app; simpl => IH.
    apply OrE with A (¬ A).
    - apply Excluded_Middle.
    - apply ImpE with (A ∨ B).
      * is_ass.
      * apply OrI1. is_ass.
    - apply OrE with B (¬ B).
      * apply Excluded_Middle.
      * apply ImpE with (A ∨ B).
        + is_ass.
        + apply OrI2. is_ass.
      * eapply Nc_list_impl.
        apply IH.
        apply Nc_list_contained => C /=.
        repeat rewrite in_app_iff; simpl.
        destruct_or.
          right; right; left; auto.
          right; right; right; left; auto.
          right; left; auto.
          left; auto.
          right; right; right; right; right; auto.
  }{
    apply OrE with B (¬ B).
    - apply Excluded_Middle.
    - eapply Nc_list_impl.
      apply IHG1.
      Ncl_solve.
    - apply OrE with A (¬ A).
      * apply Excluded_Middle.
      * apply ImpE with B.
        is_ass.
        apply ImpE with A; is_ass.
      * eapply Nc_list_impl.
        apply IHG2.
        apply Nc_list_contained => /= C.
        repeat rewrite in_app_iff; simpl.
        destruct_or.
        right; right; left; left; auto.
        right; right; left; right; right; auto.
        left; auto.
        right; right; right; auto.
  }{
    move : IHG.
    repeat rewrite map_app; simpl => /= IH.
    eapply Nc_list_impl; eauto.
    split.
    - apply BotC.
      apply ImpE with (A → B). is_ass.
      apply ImpI. apply BotC. apply ImpE with A; is_ass.
    - apply Nc_list_app.
      * Ncl_solve.
      * apply Nc_list_app.
        + Ncl_solve.
        + split.
          - apply ImpI.
            apply ImpE with (A → B). is_ass.
            apply ImpI. is_ass.
          - Ncl_solve.
  }{
    apply OrE with A (¬ A); auto.
    - apply Excluded_Middle.
    - eapply Nc_list_impl.
      apply IHG1.
      apply Nc_list_contained => /= C.
      repeat rewrite in_app_iff; simpl.
      destruct_or.
      right; left; auto.
      left; auto.
      right; right; auto.
  }
Qed.

Lemma ConjNeg_Disj Δ Γ :
  Γ ++ ¬l Δ ⊢ ⊥ -> Γ ⊢ ⨆ Δ.
Proof.
  move : Γ.
  induction Δ => //= Γ H.
  - rewrite <- (app_nil_r Γ); auto.
  - eapply OrE.
    apply Excluded_Middle.
    apply OrI1. is_ass.
    apply OrI2.
    apply IHΔ.
    eapply Nc_list_impl. apply H.
    apply Nc_list_contained => C /=.
    repeat rewrite in_app_iff; simpl.
    destruct_or.
    right; left; auto.
    left; auto.
    right; right; auto.
Qed.

Lemma G_to_Nc Γ Δ :
  Γ ⊃ Δ -> Γ ⊢ ⨆ Δ.
Proof.
  move => H.
  apply ConjNeg_Disj.
  apply G_to_Nc_Neg; auto.
Qed.

Local Ltac temp1 := econstructor; split; reflexivity || (rewrite app_comm_cons; reflexivity).

Lemma in_split_app : forall A (a : A) l2 l4 l1 l3,
  l1 ++ a :: l2 = l3 ++ l4 ->
  ((exists l, l3 = l1 ++ a :: l /\ l2 = l ++ l4) \/
   (exists l, l4 = l ++ a :: l2 /\ l1 = l3 ++ l)).
Proof.
  induction l1; destruct l3; simpl.
  - move <-.
    right; exists nil; auto.
  - inversion 1; subst a0 l2.
    left; exists l3; auto.
  - move <-; simpl.
    right; exists (a0 :: l1); auto.
  - inversion 1. subst a0.
    move : (IHl1 _ H2) => [[l [Hl Hr]]|[l [Hl Hr]]]; subst;
    [left|right]; exists l; auto.
Qed.


Ltac rew1 := repeat rewrite <- app_assoc; repeat rewrite <- app_comm_cons.
Ltac rew2 := repeat rewrite app_comm_cons; try rewrite app_assoc.
Ltac constr := constructor 3||constructor 4||constructor 5||
               constructor 6||constructor 7||constructor 8.

Local Ltac temp2 X Y Z :=
  (rew1;constr;rew2;eapply X;rew1;reflexivity)||
  (rew2;constr;rew1;eapply X;rew2;reflexivity)||
  (rew1;constr;rew2;[eapply Y|eapply Z];rew1;reflexivity)||
  (rew2;constr;rew1;[eapply Y|eapply Z];rew2;reflexivity).

Local Ltac temp3 H IHG IHG1 IHG2 Heql A0 := induction H;intros;subst;
 try apply in_split_app in Heql as [(?&?&?)|(?&?&?)];
  subst;try (temp2 IHG IHG1 IHG2;fail);[is_ass|constructor 2;in_solve|
   apply Cut with A0;[try rewrite app_comm_cons|rew2];auto..].

Lemma WeakL : forall Γ1 Γ2 Δ A,
  Γ1 ++ Γ2 ⊃ Δ -> Γ1 ++ A :: Γ2 ⊃ Δ.
Proof.
  intros.
  remember (Γ1 ++ Γ2).
  induction H; try subst l; try subst Γ.
  - econstructor 1; eauto.
    case /in_app_iff : H => H; apply in_app_iff; [left|right; right]; eauto.
  - case /in_app_iff: H => H; constructor 2; apply in_app_iff; [left| right; right]; auto.
Restart.
  intros.
  remember (Γ1 ++ Γ2).
  move : Γ1 Γ2 Heql.
  temp3 H IHG IHG1 IHG2 Heql A0.
Qed.

Lemma WeakR : forall Γ Δ1 Δ2 A, Γ ⊃ Δ1++Δ2 -> Γ ⊃ Δ1++A::Δ2.
intros;remember (Δ1++Δ2);revert Δ1 Δ2 Heql;temp3 H IHG IHG1 IHG2 Heql A0.
Qed.

Theorem Nc_to_G : forall Γ A, Γ ⊢ A -> Γ ⊃ [A].
induction 1.
 is_ass.
 apply ImpR with (Δ1:=[]);assumption.
 apply Cut with (A→B).
   apply WeakR with (Δ1:=[_]);assumption.
   apply ImpL with (Γ1:=[]).
     is_ass.
     apply WeakR with (Δ1:=[_]);assumption.
 apply Cut with (¬A).
   apply ImpR with (Δ1:=[]);is_ass.
   eapply Cut.
    apply WeakR with (Δ1:=[⊥]);assumption.
    apply GBot;in_solve.
 apply AndR with (Δ1:=[]);assumption.
 apply Cut with (A ∧ B).
   apply WeakR with (Δ1:=[_]);assumption.
   apply AndL with (Γ1:=[]);is_ass.
 apply Cut with (A ∧ B).
   apply WeakR with (Δ1:=[_]);assumption.
   apply AndL with (Γ1:=[]);constructor 1 with B;in_solve.
 apply OrR with (Δ1:=[]);apply WeakR with (Δ1:=[_]);assumption.
 apply OrR with (Δ1:=[]);apply WeakR;assumption.
 apply Cut with (A ∨ B).
   apply WeakR with (Δ1:=[_]);assumption.
   apply OrL with (Γ1:=[]);assumption.
Qed.

End sequent_mod.

















