Require Export soundness.
Require Export Decidable.
Require Export Lia.
Set Implicit Arguments.

Module Type complete_mod (X : base_mod) (Y : sound_mod X).
Import X.
Import Y.

(* Negation Normal Form (NNF) *)
Inductive NNF : Set :=
  | NPos : PropVars -> NNF
  | NNeg : PropVars -> NNF
  | NBot : NNF
  | NTop : NNF
  | NConj : NNF -> NNF -> NNF
  | NDisj : NNF -> NNF -> NNF
  .

Fixpoint MakeNNF A : NNF :=
    match A with
    | # P => NPos P
    | ⊥ => NBot
    | B ∨ C => NDisj (MakeNNF B) (MakeNNF C)
    | B ∧ C => NConj (MakeNNF B) (MakeNNF C)
    | B → C => NDisj (MakeNNFN B) (MakeNNF C)
    end
(* MakeNNFN does sama as ¬ A *)
with MakeNNFN A : NNF :=
  match A with
  | # P => NNeg P
  | ⊥ => NTop
  | B ∨ C => NConj (MakeNNFN B) (MakeNNFN C)
  | B ∧ C => NDisj (MakeNNFN B) (MakeNNFN C)
  | B → C => NConj (MakeNNF B) (MakeNNFN C)
  end.

Fixpoint NNFtoPropF A : PropF :=
  match A with
  | NPos P => # P
  | NNeg P => ¬ # P
  | NBot => ⊥
  | NTop => ⊤
  | NConj B C => NNFtoPropF B ∧ NNFtoPropF C
  | NDisj B C => NNFtoPropF B ∨ NNFtoPropF C
  end.

(* l := p | ¬ p | ⊤ | ⊥ *)
Inductive Literal :=
  | LPos : PropVars -> Literal
  | LNeg : PropVars -> Literal
  | LBot : Literal
  | LTop : Literal
  .


Definition Bar P :=
  match P with
  | LPos Q => LNeg Q
  | LNeg Q => LPos Q
  | LBot => LTop
  | LTop => LBot
  end.

Definition LiteraltoPropF P : PropF :=
  match P with
  | LPos Q => # Q
  | LNeg Q => ¬ # Q
  | LBot => ⊥
  | LTop => ⊤
  end.

(* c := {lᵢ} *)
Definition Clause := list Literal.

(* {lᵢ} => l₁ ∨ l₂ ∨ ... ∨ lᵢ *)
Definition ClausetoPropF := map_fold_right LiteraltoPropF Disj ⊥.

(* CNF := {cᵢ} *)
Definition CNF := list Clause.

(*
  {cᵢ} => (l₁₁ ∨ l₁₂ ∨ ... l₁ₙ₁) ∧
          (l₂₁ ∨ l₂₂ ∨ ... l₂ₙₙ₂) ∧
          ...
          (lₘ₁ ∨ lₘ₂ ∨ ... lₘₙₘ )
*)
Definition CNFtoPropF := map_fold_right ClausetoPropF Conj ⊤.

(* AddClause l {lᵢ} := {l++l₁, l++l₂, ..., l++lᵢ} *)
Definition AddClause (l : Clause) (ll : CNF) : CNF := map (fun l2 => l ++ l2) ll.

(*
  ll1 := [[a;b;c];[d;e;f];[g;h;i]].
  ll2 := [[A;B;C];[D;E;F];[G;H;I]].
  Disjunct ll1 ll2 =
    [[a; b; c; A; B; C]; [a; b; c; D; E; F]; [a; b; c; G; H; I];
     [d; e; f; A; B; C]; [d; e; f; D; E; F]; [d; e; f; G; H; I];
     [g; h; i; A; B; C]; [g; h; i; D; E; F]; [g; h; i; G; H; I]
    ]
*)
Definition Disjunct (ll ll2 : CNF) : CNF := flat_map (fun l => AddClause l ll2) ll.

Fixpoint MakeCNF A : CNF :=
  match A with
  | NPos P => [[LPos P]]
  | NNeg P => [[LNeg P]]
  | NBot => [[LBot]]
  | NTop => [[LTop]]
  | NConj B C => MakeCNF B ++ MakeCNF C
  | NDisj B C => Disjunct (MakeCNF B) (MakeCNF C)
  end.

Definition Valid_Clause (l : Clause) := In LTop l \/ (exists A, In (LPos A) l /\ In (LNeg A) l).
Definition Valid_CNF ll := forall l, In l ll -> Valid_Clause l.

Lemma Literal_eqdec :
  forall (x y : Literal), {x = y} + {x <> y}.
Proof.
  intros x y; destruct x,y;
    try solve [left; auto| right; discriminate];
    destruct (X.Varseq_dec p p0);
    try solve [left; f_equal; auto];
    right; intro F; inversion F; auto.
Qed.


Lemma NNF_equiv_valid v A :
  TrueQ v (NNFtoPropF (MakeNNF A)) = TrueQ v A /\
  TrueQ v (NNFtoPropF (MakeNNFN A)) = TrueQ v ¬ A.
Proof.
  induction A; simpl;
    try destruct (v p); simpl; split;
    try destruct IHA1 as [L1 L2];
    try destruct IHA2 as [R1 R2];
    try rewrite L1;
    try rewrite L2;
    try rewrite R1;
    try rewrite R2; simpl;
    repeat rewrite orb_false_r;
    try rewrite negb_orb;
    try rewrite negb_andb;
    try rewrite negb_involutive;
    auto.
Qed.

Lemma CNF_and_valid v ll1 ll2 :
  TrueQ v (CNFtoPropF (ll1 ++ ll2)) =
  TrueQ v (CNFtoPropF ll1) && TrueQ v (CNFtoPropF ll2).
Proof.
  generalize dependent ll2.
  induction ll1; simpl; auto; intro ll2.
  rewrite <- andb_assoc.
  f_equal.
  rewrite IHll1; auto.
Qed.

Lemma CNF_or_clause_valid v l1 l2 :
  TrueQ v (ClausetoPropF (l1 ++ l2)) =
  TrueQ v (ClausetoPropF l1) || TrueQ v (ClausetoPropF l2).
Proof.
    generalize dependent l2.
    induction l1; auto; simpl; intro l2.
    rewrite <- orb_assoc; f_equal; rewrite IHl1; auto.
Qed.

Lemma cons_app {A} (a : A) (l : list A) :
  a :: l = [a] ++ l.
Proof.
  induction l; simpl; auto.
Qed.

Lemma CNF_add_clause_valid v l ll :
  TrueQ v (CNFtoPropF (AddClause l ll)) =
  TrueQ v (ClausetoPropF l) || TrueQ v (CNFtoPropF ll).
Proof.
  induction ll; simpl in *.
  - destruct l; simpl; auto.
    rewrite orb_true_r; auto.
  - unfold CNFtoPropF in IHll.
    rewrite IHll; clear IHll.
    rewrite CNF_or_clause_valid.
    remember (TrueQ v (ClausetoPropF l)) as P.
    remember (TrueQ v (ClausetoPropF a)) as Q.
    remember (TrueQ v (map_fold_right ClausetoPropF Conj ⊤ ll)) as R.
    rewrite orb_andb_distrib_r; auto.
Qed.

Lemma CNF_or_valid v ll1 ll2 :
  TrueQ v (CNFtoPropF (Disjunct ll1 ll2)) =
  TrueQ v (CNFtoPropF ll1) || TrueQ v (CNFtoPropF ll2).
Proof.
  induction ll1; auto; simpl.
  rewrite CNF_and_valid, CNF_add_clause_valid, IHll1.
  unfold CNFtoPropF.
  remember (TrueQ v (map_fold_right ClausetoPropF Conj ⊤ ll1)) as P.
  remember (TrueQ v (map_fold_right ClausetoPropF Conj ⊤ ll2)) as Q.
  remember (TrueQ v (ClausetoPropF a)) as R.
  rewrite orb_andb_distrib_l; auto.
Qed.

Theorem CNF_equiv_valid v A :
  TrueQ v (CNFtoPropF (MakeCNF A)) = TrueQ v (NNFtoPropF A).
Proof.
  induction A;simpl;
    try repeat rewrite orb_false_r;
    try repeat rewrite andb_true_r;
    try rewrite CNF_and_valid;
    try rewrite CNF_or_valid;
    try rewrite IHA1, IHA2; auto.
Qed.


Definition Countervaluation l P :=
  if (in_dec Literal_eqdec (LNeg P) l) then true else false.
Definition Validates v Δ :=
  exists A, In A Δ /\ Is_true (TrueQ v A).


Lemma TrueQ_impl_Validates v m :
  Is_true (TrueQ v (ClausetoPropF m)) -> Validates v (map LiteraltoPropF m).
Proof.
  induction m; simpl; intro H.
  - inversion H.
  - unfold Validates.
    apply Is_true_eq_true in H.
    apply orb_prop in H.
    destruct H.
    * exists (LiteraltoPropF a); split; auto.
      + left; auto.
      + rewrite H; simpl; auto.
    * apply Is_true_eq_left in H.
      apply IHm in H.
      destruct H as [x [Hxm Hx]].
      exists x; split; auto.
      right; auto.
Qed.

Lemma Validated_valid l :
  Validates (Countervaluation l) (map LiteraltoPropF l) -> Valid_Clause l.
Proof.
  destruct 1 as [A [HA Hx]].
  apply in_map_iff in HA as [p [Hp pl]]; subst.
  destruct p;
  unfold Countervaluation in Hx; simpl in Hx;
  try solve [left; auto];
  try destruct (in_dec Literal_eqdec (LNeg p) l);
  simpl in *;
  try contradiction.
  try right; exists p; split; auto.
Qed.

Theorem Clause_valid l :
  Valid (ClausetoPropF l) -> Valid_Clause l.
Proof.
  intro H; apply Validated_valid.
  apply TrueQ_impl_Validates.
  apply H.
  intros A HA.
  contradiction.
Qed.



Theorem CNF_valid ll :
  Valid (CNFtoPropF ll) -> Valid_CNF ll.
Proof.
  induction ll; simpl; intro H.
  - unfold Valid, Valid_CNF; intros; contradiction.
  - intros l Hl.
    apply Clause_valid.
    intros f Hf.
    specialize (H f Hf).
    rewrite cons_app in H.
    rewrite CNF_and_valid in H.
    apply andb_prop_elim in H as [Ha Hll].
    destruct Hl; subst; auto.
    * simpl in Ha; rewrite andb_true_r in Ha; auto.
    *  apply in_split in H as [h [t]]; subst.
        rewrite CNF_and_valid in Hll.
        apply andb_prop_elim in Hll as [_].
        simpl in H.
        apply andb_prop_elim in H as []; auto.
Qed.

Lemma Clause_provable_3 a l1 l2 Γ :
  In (LiteraltoPropF a) Γ -> Γ ⊢ ClausetoPropF (l1 ++ a :: l2).
Proof.
  intro H; induction l1; simpl.
  - unfold ClausetoPropF; simpl.
    apply OrI1; constructor; auto.
  - unfold ClausetoPropF; simpl; apply OrI2; simpl; auto.
Qed.

Lemma provable_or_comm l A B :
  l ⊢ A ∨ B -> l ⊢ B ∨ A.
Proof.
  intro H.
  apply OrE with A B; auto; [apply OrI2| apply OrI1]; is_ass.
Qed.

Lemma Clause_provable_2 a l1 l2 l3 :
  Provable (ClausetoPropF (l1 ++ (Bar a) :: l2 ++ a :: l3)).
Proof.
  induction l1; simpl.
  - apply OrE with (LiteraltoPropF (Bar a)) (LiteraltoPropF a).
    * destruct a; simpl;
      try apply Excluded_Middle;
      apply provable_or_comm; apply Excluded_Middle.
    * unfold ClausetoPropF; simpl.
      apply OrI1; is_ass.
    * unfold ClausetoPropF; simpl.
      apply OrI2.
      induction l2; simpl.
      { apply OrI1. is_ass. }
      { apply OrI2; auto. }
  - unfold ClausetoPropF; simpl; apply OrI2; auto.
Qed.

Lemma Clause_provable l :
  Valid_Clause l -> Provable (ClausetoPropF l).
Proof.
  unfold Valid_Clause.
  intros H; destruct H.
  - apply in_split in H as [h [t]]; subst.
    induction h; simpl.
    * unfold ClausetoPropF; simpl.
      apply OrI1; apply ImpI; is_ass.
    * unfold ClausetoPropF; simpl.
      apply OrI2; auto.
  - destruct H as [A [HP HN]].
    assert (LPos A = Bar (LNeg A)) as HLP by auto.
    assert (LNeg A = Bar (LPos A)) as HLN by auto.
    apply in_split in HP as [l1 [l2]]; subst.
    apply in_app_or in HN.
    destruct HN.
    * apply in_split in H as [l3 [l4]]; subst.
      rewrite <- app_assoc, <- app_comm_cons, HLN.
      apply Clause_provable_2.
    * destruct H; try contradiction.
      inversion H.
      apply in_split in H as [l3 [l4]]; subst.
      rewrite HLP.
      apply Clause_provable_2.
Qed.

Theorem CNF_provable ll :
  Valid_CNF ll -> Provable (CNFtoPropF ll).
Proof.
  unfold Valid_CNF.
  induction ll; unfold CNFtoPropF; simpl.
  - intro H; apply ImpI; is_ass.
  - intro H.
    apply AndI.
    * apply Clause_provable; apply H; left; auto.
    * apply IHll; intros l Hll.
      apply H; right; auto.
Qed.


Lemma prov_or A1 A2 B1 B2 Γ :
  Provable (A1 → A2) -> Provable (B1 → B2) -> In (A1 ∨ B1) Γ -> Γ ⊢ A2 ∨ B2.
Proof.
  intros HA HB H1.
  eapply OrE with A1 B1;
    [is_ass|apply OrI1|apply OrI2];
    apply deduction;
    rewrite <- (app_nil_l Γ);
    apply weakening; auto.
Qed.

From mathcomp Require Export ssreflect.

Lemma prov_and_assoc A B C Γ :
  Γ ⊢ A ∧ B ∧ C -> Γ ⊢ (A ∧ B) ∧ C.
Proof.
  move => H.
  apply AndI; [apply AndI|].
  - apply AndE1 with (B ∧ C); auto.
  - apply AndE1 with C.
    apply AndE2 with A; auto.
  - apply AndE2 with B.
    apply AndE2 with A; auto.
Qed.


Lemma CNF_and_prov ll1 ll2 :
  Provable (CNFtoPropF (ll1 ++ ll2) → CNFtoPropF ll1 ∧ CNFtoPropF ll2).
Proof.
  induction ll1; simpl.
  - unfold CNFtoPropF; simpl.
    apply ImpI. apply AndI.
    * rewrite <- (app_nil_l [_]).
      apply weakening.
      apply ImpI; is_ass.
    * is_ass.
  - move : (prov_impl IHll1) => H.
    apply ImpI.
    unfold CNFtoPropF; simpl.
    apply prov_and_assoc.
    apply AndI.
    * eapply AndE1; is_ass.
    * apply H.
      eapply AndE2; is_ass.
Qed.

Lemma prov_or_assoc A B C Γ :
  Γ ⊢ A ∨ B ∨ C -> Γ ⊢ (A ∨ B) ∨ C.
Proof.
  move => H.
  eapply OrE with A (B ∨ C); auto.
  - repeat apply OrI1; is_ass.
  - eapply prov_or with B C.
    * apply ImpI; apply OrI2; is_ass.
    * apply ImpI; is_ass.
    * left; auto.
Qed.

Lemma CNF_or_clause_prov l1 l2 :
  Provable (ClausetoPropF (l1 ++ l2) → ClausetoPropF l1 ∨ ClausetoPropF l2).
Proof.
  induction l1; rewrite /ClausetoPropF => /=; apply ImpI.
  - apply OrI2; is_ass.
  - apply prov_or_assoc.
    eapply prov_or with (LiteraltoPropF a) (ClausetoPropF (l1 ++ l2)); auto.
    * apply ImpI; is_ass.
    * left; auto.
Qed.

Ltac prov_impl_in IH := let H := fresh "K" in
try (remember (prov_impl IH) as H eqn:HeqH;clear IH HeqH).

Lemma CNF_add_clause_prov l ll :
  Provable (CNFtoPropF (AddClause l ll) → ClausetoPropF l ∨ CNFtoPropF ll).
Proof.
  induction ll.
    (* rewrite /CNFtoPropF; simpl. *)
  - apply ImpI; apply OrI2; apply ImpI; is_ass.
  - apply ImpI.
    move : (prov_impl IHll) => IH.
    unfold CNFtoPropF; simpl.
    apply OrE with (ClausetoPropF l) (ClausetoPropF a).
    * eapply prov_impl.
      + apply CNF_or_clause_prov.
      + eapply AndE1; is_ass.
    * apply OrI1; is_ass.
    * apply OrE with (ClausetoPropF l) (CNFtoPropF ll).
      - apply IH. eapply AndE2; is_ass.
      - apply OrI1; is_ass.
      - apply OrI2; apply AndI; is_ass.
Qed.

Lemma CNF_or_prov ll1 ll2 :
  Provable (CNFtoPropF (Disjunct ll1 ll2) → CNFtoPropF ll1 ∨ CNFtoPropF ll2).
Proof.
  induction ll1.
  { apply ImpI; apply OrI1; is_ass. }
  {
    move : (prov_impl IHll1) => IH; clear IHll1.
    apply ImpI; simpl.
    rewrite /CNFtoPropF; simpl.
    apply OrE with (ClausetoPropF a) (CNFtoPropF ll2).
    {
      eapply prov_impl.
      - apply CNF_add_clause_prov.
      - eapply AndE1.
        eapply prov_impl.
        * apply CNF_and_prov.
        * is_ass.
    }
    {
      apply OrE with (CNFtoPropF ll1) (CNFtoPropF ll2).
        apply IH. eapply AndE2.
        eapply prov_impl.
        - apply CNF_and_prov.
        - is_ass.
        apply OrI1; apply AndI; is_ass.
        apply OrI2; is_ass.
    }
    {
      apply OrI2; is_ass.
    }
  }
Qed.

Theorem CNF_impl_prov A :
  Provable (CNFtoPropF (MakeCNF A) → NNFtoPropF A).
Proof.
  induction A; apply ImpI; simpl.
  - rewrite /CNFtoPropF /ClausetoPropF; simpl;
    eapply OrE;[ eapply AndE1 | | apply BotC]; is_ass.
  - rewrite /CNFtoPropF /ClausetoPropF; simpl;
    eapply OrE; [ eapply AndE1 | | apply BotC]; is_ass.
  - rewrite /CNFtoPropF /ClausetoPropF; simpl;
    eapply OrE; [ eapply AndE1 | | apply BotC]; is_ass.
  - rewrite /CNFtoPropF /ClausetoPropF; simpl;
    eapply OrE; [ eapply AndE1 | | apply BotC]; is_ass.
  - eapply prov_impl.
    * apply ImpI.
      eapply AndI; eapply prov_impl; eauto;
      [eapply AndE1|eapply AndE2]; is_ass.
    * eapply prov_impl; [apply CNF_and_prov|is_ass].
  - eapply OrE with (CNFtoPropF (MakeCNF A1)) ((CNFtoPropF (MakeCNF A2))).
    * eapply prov_impl; [apply CNF_or_prov| is_ass].
    * apply OrI1. eapply prov_impl. apply IHA1; is_ass. is_ass.
    * apply OrI2. eapply prov_impl. apply IHA2; is_ass. is_ass.
Qed.

Lemma prov_and A1 A2 B1 B2 Γ :
  Provable (A1 → A2) -> Provable (B1 → B2) -> In (A1 ∧ B1) Γ -> Γ ⊢ A2 ∧ B2.
Proof.
  move => HA HB H1.
  apply AndI; eapply prov_impl; eauto; [eapply AndE1 | eapply AndE2]; is_ass.
Qed.

Theorem prov_not_or_and A B Γ :
  Γ ⊢ ¬ (A ∨ B) -> Γ ⊢ (¬ A) ∧ (¬ B).
Proof.
  intro H; apply AndI; apply ImpI; apply ImpE with (A ∨ B);
    try (eapply weakening2; [apply H| intros; right; auto]);
    [apply OrI1|apply OrI2]; is_ass.
Qed.


Theorem prov_and_not_or A B Γ :
  Γ ⊢ (¬ A) ∧ (¬ B) -> Γ ⊢ ¬ (A ∨ B).
Proof.
  move => H. apply ImpI.
  eapply OrE with A B.
  is_ass.
  apply ImpE with A. eapply weakening2 with Γ;
  [eapply AndE1; apply H| intros; right; right; auto].
  is_ass.
  apply ImpE with B. eapply weakening2 with Γ;
  [eapply AndE2; apply H| intros; right; right; auto].
  is_ass.
Qed.

Theorem prov_or_not_and A B Γ :
  Γ ⊢ (¬ A) ∨ (¬ B) -> Γ ⊢ ¬ (A ∧ B).
Proof.
  move => H.
  apply ImpI.
  apply OrE with (¬ A) (¬ B).
  - apply weakening2 with Γ; auto.
    intros; right; auto.
  - apply ImpE with A.
    is_ass.
    eapply AndE1; is_ass.
  - apply ImpE with B.
    is_ass.
    eapply AndE2; is_ass.
Qed.





Theorem prov_or_imply A B Γ :
  Γ ⊢ (¬ A) ∨ B -> Γ ⊢ A → B.
Proof.
  move => H.
  apply ImpI.
  apply OrE with (¬ A) B.
  - apply weakening2 with Γ; auto.
    intros; right; auto.
  - apply BotC.
    apply ImpE with A; is_ass.
  - is_ass.
Qed.




Theorem NN A Γ :
 Γ ⊢ A -> Γ ⊢ ¬ ¬ A.
Proof.
  intro H.
  apply ImpI.
  apply ImpE with A.
  is_ass.
  apply weakening2 with Γ; auto.
  intros; right; auto.
Qed.

Theorem prov_and_imply A B Γ :
   Γ ⊢ A ∧ ¬ B -> Γ ⊢ ¬ (A → B).
Proof.
  move => H.
  apply ImpI.
  apply ImpE with (A ∧ ¬ B).
  - apply prov_or_not_and.
    apply OrE with A (¬ A).
    eapply Excluded_Middle.
    apply OrI2. apply NN. eapply ImpE with A; is_ass.
    apply OrI1. is_ass.
  - apply weakening2 with Γ; auto.
    intros; right; auto.
Qed.





Lemma NNF_impl_prov A :
  Provable (NNFtoPropF (MakeNNF A)  →   A) /\
  Provable (NNFtoPropF (MakeNNFN A) → ¬ A).
Proof.
  induction A; split; simpl; apply ImpI;
  try destruct IHA1 as [IHA1 IHA1']; try destruct IHA2 as [IHA2 IHA2'].
  - is_ass.
  - is_ass.
  - is_ass.
  - is_ass.
  - eapply prov_and.
    apply IHA1.
    apply IHA2.
    left; auto.
  - apply OrE with (NNFtoPropF (MakeNNFN A1)) (NNFtoPropF (MakeNNFN A2)).
    * is_ass.
    * apply ImpI.
      apply ImpE with A1.
      apply  (prov_impl IHA1'). is_ass.
      apply AndE1 with A2. is_ass.
    * apply ImpI.
      apply ImpE with A2.
      apply (prov_impl IHA2'). is_ass.
      eapply AndE2; is_ass.
  - eapply prov_or.
    eapply IHA1.
    eapply IHA2.
    left; auto.
    - eapply prov_and_not_or.
    move : (prov_impl IHA1') => IH1; clear IHA1.
    move : (prov_impl IHA2') => IH2; clear IHA2.
    apply AndI; [apply IH1|apply IH2]; [eapply AndE1|eapply AndE2]; is_ass.
  - apply ImpI.
    apply OrE with (¬ A1) A2.
    * eapply prov_or; try assumption; in_solve.
    * apply BotC.
      apply ImpE with A1; is_ass.
    * is_ass.
  - apply ImpI.
    apply ImpE with A2.
    * eapply prov_impl.
      apply IHA2'.
      eapply AndE2; is_ass.
    * apply ImpE with A1.
      is_ass.
      eapply prov_impl.
      apply IHA1.
      eapply AndE1.
      is_ass.
Qed.

Theorem Completeness : Prop_Completeness.
Proof.
  move => A HA.
  mp. apply NNF_impl_prov.
  mp. apply CNF_impl_prov.
  apply CNF_provable.
  apply CNF_valid.
  move => f Hf.
  Search (TrueQ _ (NNFtoPropF _)).
  rewrite CNF_equiv_valid.
  move : (NNF_equiv_valid f A) => [H _].
  rewrite H.
  apply HA; auto.
Qed.

End complete_mod.