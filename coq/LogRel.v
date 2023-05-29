Require Import Utf8.
Require Import Nat.
Require Import Syntax.
Require Import Reduction.
Require Import Typ.


Definition SemType := val0 → Prop.

Inductive stkop :=
  SO : val0 → nat → SemType → stkop
.

Definition SemEff := stkop → Prop.

Definition basis (κ : kind) : Type :=
  match κ with
  | kT => val0
  | kE => stkop
  | kR => stkop
  end.

Definition K (κ : kind) := basis κ → Prop.

Inductive Sem (μ : SemType) (ξ : SemEff) (e : exp0) : Prop :=
| Evl : ∀ {v}, redm e (e_val v) → μ v → Sem μ ξ e
| Stk : ∀ {v K n ν}
      , redm e (plug K (e_do v))
      → ξ (SO v n ν)
      → free n K
      → (∀ u, ν u → Sem μ ξ (plug K (e_val u)))
      → Sem μ ξ e
.

Fixpoint V (τ : typ kT) v : Prop :=
  match τ with
  | t_base => match v with
      | v_lam (e_val (v_var None)) => True
      | _ => False
      end
  | t_arr τ₁ ρ τ₂ =>
      match v with
      | v_lam e => ∀ v, V τ₁ v → Sem (V τ₂) (FR ρ) (sub1 v e)
      | _ => False
      end
  end
with F (ε : typ kE) so :=
  match ε with
  | t_eff τ₁ τ₂ =>
      match so with
      | SO v O μ => V τ₁ v ∧ eq (V τ₂) μ
      | SO _ (S _) _ => False
      end
  end
with FR (ρ : typ kR) so :=
  match ρ with
  | t_empty => False
  | t_cons ε ρ' =>
      match so with
      | SO v O μ => F ε so
      | SO v (S n) μ => FR ρ' (SO v n μ)
      end
  end.
Definition E τ ρ : exp0 → Prop := Sem (V τ) (FR ρ).

Lemma lam_compat
  : ∀ e τ₁ ρ τ₂, (∀ v, V τ₁ v → E τ₂ ρ (sub1 v e))
  → E (t_arr τ₁ ρ τ₂) t_empty (e_val (v_lam e)).
Proof.
  intros.
  eapply Evl.
  - apply r_id.
  - cbn. exact H.
Qed.

Lemma lift_compat : ∀ e τ ε ρ, E τ ρ e → E τ (t_cons ε ρ) (e_lift e).
Proof.
  intros.
  induction H.
  - eapply Evl.
    + eapply r_trans.
      * eapply (plug_redm (k_lift k_hole)). exact H.
      * cbn. eapply r_one. eapply r_contr. apply c_lift.
    + exact H0.
  - eapply Stk.
    + apply (plug_redm (k_lift k_hole)) in H. simpl in H.
      instantiate (2 := k_lift _). cbn. exact H. (* right to left numbering ??? *)
    + instantiate (2 := S n). exact H0.
    + apply f_lift. exact H1.
    + trivial.
Qed.

Lemma E_val : ∀ τ ρ v, E τ ρ (e_val v) → V τ v.
Proof.
  intros.
  inversion H.
  - eapply redm_val in H0. inversion H0. subst v. trivial.
  - eapply redm_val in H0. destruct K0.
    all: simpl; inversion H0.
Qed.


Lemma do_compat
  : ∀ v τ₁ τ₂, E τ₁ t_empty (e_val v)
  → E τ₂ (t_cons (t_eff τ₁ τ₂) t_empty) (e_do v).
Proof.
  intros.
  eapply Stk.
  - instantiate (2 := k_hole). simpl. apply r_id.
  - instantiate (2 := O). simpl.
    apply E_val in H.
    eapply (conj H). trivial.
  - constructor.
  - intros.
    eapply Evl.
    + eapply r_id.
    + trivial.
Qed.

Lemma antir : ∀ {τ ρ e₁ e₂}, redm e₁ e₂ → E τ ρ e₂ → E τ ρ e₁.
Proof.
  intros.
  destruct H0.
  - eapply Evl.
    eapply (r_trans _ _ _ H).
    exact H0.
    exact H1.
  - eapply Stk.
    eapply (r_trans _ _ _ H).
    exact H0.
    exact H1.
    assumption.
    assumption.
Qed.

Lemma app_compat1
  : ∀ {τ₁ τ₂ ρ f e}, V (t_arr τ₁ ρ τ₂) (v_lam f) → E τ₁ ρ e
  → E τ₂ ρ (e_app (e_val (v_lam f)) e).
Proof.
  intros.
  induction H0; apply (plug_redm (k_arg (v_lam f) k_hole)) in H0; simpl in H0.
  - apply (antir H0).
    eapply antir.
    eapply r_one. eapply r_contr. eapply c_fun.
    simpl in H.
    apply H in H1.
    assumption.
  - eapply Stk.
    instantiate (2 := k_arg (v_lam f) K0). exact H0.
    exact H1.
    apply f_arg. exact H2.
    exact H4.
Qed.


Lemma app_compat
  : ∀ {τ₁ τ₂ ρ e₁ e₂}, E (t_arr τ₁ ρ τ₂) ρ e₁ → E τ₁ ρ e₂
  → E τ₂ ρ (e_app e₁ e₂).
Proof.
  intros.
  induction H; apply (plug_redm (k_fun k_hole e₂)) in H; simpl in H.
  destruct v; try contradiction.
  - apply (antir H).
    apply (app_compat1 (τ₁ := τ₁)). assumption. assumption.
  - eapply Stk.
    instantiate (2 := k_fun K0 e₂). exact H.
    exact H1.
    apply f_fun. exact H2.
    assumption.
Qed.

Lemma hndl_compat
  : ∀ {τ τ₁ τ₂ τr ρ e eh er}
  , E τ (t_cons (t_eff τ₁ τ₂) ρ) e
  → (∀ v, V τ₁ v → ∀ k, V (t_arr τ₂ ρ τr) k → E τr ρ (sub2 v k eh))
  → (∀ v, V τ v → E τr ρ (sub1 v er))
  → E τr ρ (e_hndl e eh er).
Proof.
  intros.
  induction H;
  apply (plug_redm (k_hndl k_hole eh er)) in H;
  simpl in H;
  apply (antir H).
  - eapply antir.
    apply r_one. apply r_contr. constructor.
    apply H1. assumption.
  - destruct n.
    + eapply antir. apply r_one. apply r_contr. constructor. assumption.
      apply H0.
      simpl in H2.
      destruct H2.
      assumption.
      simpl.
      intros.
      rewrite (sub1_weaken (k_hndl K0 eh er)).
      apply H5.
      destruct H2.
      rewrite <- H7.
      assumption.
    + eapply Stk.
      instantiate (2 := k_hndl K0 eh er).
      apply r_id.
      exact H2.
      apply f_hndl. assumption.
      apply H5.
Qed.


Import SigTNotations.
Definition G {U : Set} (Γ : U → typ kT) γ := ∀ (u : U), V (Γ u) (γ u).

Lemma extG {U : Set} {Γ : U → typ kT} {τ} γ u
  : G Γ γ → V τ u → G (ext Γ τ) (ext γ u).
Proof.
  unfold G.
  intros.
  destruct u0.
  - simpl. apply H.
  - simpl. assumption.
Qed.


Theorem fundamental
  : ∀ {U : Set} {Γ : U → typ kT} {e τ ρ} γ, types Γ e τ ρ → G Γ γ
  → E τ ρ (bind_exp γ e).
Proof.
  intros.
  induction H.
  - eapply Evl.
    apply r_id.
    apply H0.
  - apply lam_compat.
    intros.
    unfold sub1.
    rewrite <- bind_compose_exp.
    rewrite <- (bind_cong_exp (ext γ v)).
    apply IHtypes.
    apply extG.
    assumption. assumption.
    intro.
    destruct v0.
    + cbn.
      rewrite bind_map_val.
      rewrite <- (bind_cong_val v_var).
      rewrite bind_pure_val.
      trivial.
      intro.
      trivial.
    + simpl.
      trivial.
  - eapply app_compat.
    apply IHtypes1; assumption.
    apply IHtypes2; assumption.
  - eapply lift_compat.
    apply IHtypes; assumption.
  - eapply do_compat.
    apply IHtypes; assumption.
  - eapply hndl_compat.
    apply IHtypes1; assumption.
    + unfold sub2.
      intros.
      erewrite <- bind_compose_exp.
      rewrite <- (bind_cong_exp (ext (ext γ v) k)).
      apply IHtypes2.
      repeat eapply extG.
      assumption.
      assumption.
      assumption.
      intros.
      unfold Basics.compose.
      destruct v0.
      * destruct i.
        simpl.
        rewrite bind_map_val.
        rewrite bind_map_val.
        rewrite <- (bind_cong_val v_var).
        rewrite bind_pure_val. trivial.
        intros.
        unfold Basics.compose.
        trivial.
        simpl.
        trivial.
      * trivial.
    + unfold sub1.
      intros.
      erewrite <- bind_compose_exp.
      rewrite <- (bind_cong_exp (ext γ v)).
      apply IHtypes3.
      apply extG.
      assumption.
      assumption.
      intros.
      destruct v0.
      * simpl.
        unfold Basics.compose.
        simpl.
        rewrite bind_map_val.
        rewrite <- (bind_cong_val v_var).
        rewrite bind_pure_val. trivial.
        intros.
        trivial.
      * unfold Basics.compose.
        trivial.
Qed.

Theorem termination
  : ∀ e τ, types (fun x : Empty_set => match x with end) e τ t_empty
  → ∃ v, redm e (e_val v).
Proof.
  intros.
  eapply fundamental in H.
  unfold E in H.
  inversion H.
  - econstructor.
    erewrite bind_pure_exp in H0.
    exact H0.
  - inversion H1.
  - unfold G.
    intros.
    contradiction.
Qed.
