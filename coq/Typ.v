Require Import Utf8.
Require Import Syntax.

Variant kind : Set := kT | kE | kR .

Inductive typ : kind → Set :=
  | t_base : typ kT
  | t_arr : typ kT → typ kR → typ kT → typ kT
  | t_empty : typ kR
  | t_cons : typ kE → typ kR → typ kR
  | t_eff : typ kT → typ kT → typ kE
.

Inductive types {V : Set} (Γ : V → typ kT) : exp V → typ kT → typ kR → Set :=
| T_var : ∀ {v : V}, types Γ (e_val (v_var v)) (Γ v) t_empty
| T_lam : ∀ {τ₁ τ₂ ρ e}, types (ext Γ τ₁) e τ₂ ρ
  → types Γ (e_val (v_lam e)) (t_arr τ₁ ρ τ₂) t_empty
| T_app : ∀ {τ₁ τ₂ ρ e₁ e₂}
  , types Γ e₁ (t_arr τ₁ ρ τ₂) ρ
  → types Γ e₂ τ₁ ρ
  → types Γ (e_app e₁ e₂) τ₂ ρ
| T_lift : ∀ {τ ε ρ e}, types Γ e τ ρ → types Γ (e_lift e) τ (t_cons ε ρ)
| T_do : ∀ {τ₁ τ₂ v}, types Γ (e_val v) τ₁ t_empty
  → types Γ (e_do v) τ₂ (t_cons (t_eff τ₁ τ₂) t_empty)
| T_hndl : ∀ {τ τ₁ τ₂ τr ρ e eh er}
  , types Γ e τ (t_cons (t_eff τ₁ τ₂) ρ)
  → types (ext (ext Γ τ₁) (t_arr τ₂ ρ τr)) eh τr ρ
  → types (ext Γ τ) er τr ρ
  → types Γ (e_hndl e eh er) τr ρ
.
