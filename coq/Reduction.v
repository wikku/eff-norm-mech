Require Import Utf8.
Require Import Syntax.

Inductive contr : exp0 → exp0 → Set :=
| c_fun : ∀ (e : exp1) (v : val0), contr (e_app (e_val (v_lam e)) (e_val v)) (sub1 v e)
| c_lift : ∀ (v : val0), contr (e_lift (e_val v)) (e_val v)
| c_hndl : ∀ K, free O K → ∀ (v : val0) (eh : exp2) (er : exp1),
    contr (e_hndl (plug K (e_do v)) eh er)
          (sub2 v (v_lam (plug (weaken_ktx (k_hndl K eh er)) (e_val (v_var None)))) eh)
| c_ret : ∀ (v : val0) (eh : exp2) (er : exp1), contr (e_hndl (e_val v) eh er) (sub1 v er)
.

Inductive red : exp0 → exp0 → Set :=
| r_contr : ∀ {e1 e2}, contr e1 e2 → red e1 e2
| r_fun : ∀ {e1 e2} a, red e1 e2 → red (e_app e1 a) (e_app e2 a)
| r_arg : ∀ {e1 e2} f, red e1 e2 → red (e_app (e_val f) e1) (e_app (e_val f) e2)
| r_lift : ∀ {e1 e2}, red e1 e2 → red (e_lift e1) (e_lift e2)
| r_hndl : ∀ {e1 e2} eh er, red e1 e2 → red (e_hndl e1 eh er) (e_hndl e2 eh er)
.

Inductive redm : exp0 → exp0 → Prop :=
| r_id : ∀ e, redm e e
| r_one : ∀ e1 e2, red e1 e2 → redm e1 e2
| r_trans : ∀ e1 e2 e3, redm e1 e2 → redm e2 e3 → redm e1 e3
.

Lemma plug_red (K : ktx0) {e1 e2} : red e1 e2 → red (plug K e1) (plug K e2).
Proof.
  intros.
  induction K.
  assumption.
  all: cbn.
  - apply r_fun. trivial.
  - apply r_arg. trivial.
  - apply r_lift. trivial.
  - apply r_hndl. trivial.
Qed.

Lemma plug_redm (K : ktx0) {e1 e2} : redm e1 e2 → redm (plug K e1) (plug K e2).
Proof.
  intros.
  induction H.
  - apply r_id.
  - apply r_one. apply plug_red. assumption.
  - eapply r_trans.
    + exact IHredm1.
    + exact IHredm2.
Qed.

Lemma redm_val : ∀ v e, redm (e_val v) e → eq (e_val v) e.
Proof.
  intros.
  remember (e_val v) as v0 in H.
  induction H.
  - symmetry. assumption.
  - subst e1. inversion H. inversion H0.
  - subst e1.
    specialize (IHredm1 eq_refl).
    transitivity e2.
    + trivial.
    + apply eq_sym in IHredm1.
      specialize (IHredm2 IHredm1).
      subst e2. trivial.
Qed.

