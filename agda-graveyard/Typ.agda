module Typ where

open import Syntax
open import Agda.Builtin.Nat renaming (zero to Z ; suc to S)


data Kind : Set where
  T E R : Kind

-- well-kinded type
data Typ : Kind → Set where
  B : Typ T
  _-_⇒_ : Typ T → Typ R → Typ T → Typ T
  ι : Typ R
  _·_ : Typ E → Typ R → Typ R
  E_⇒_ : Typ T → Typ T → Typ E


--infix 19 _<_
---- subtyping derivation
--data _<_ : ∀{κ} → Typ κ → Typ κ → Set where
--  refl : ∀{κ} → (τ : Typ κ) → τ < τ
--  mt   : (ρ : Typ R) → ι < ρ
--  ext  : ∀{ρ₁ ρ₂} → (ε : Typ E) → ρ₁ < ρ₂ → ε · ρ₁ < ε · ρ₂
--  arr  : ∀{τ₁¹ τ₁² τ₂¹ τ₂²} {ρ₁ ρ₂}
--       → τ₂¹ < τ₁¹ → ρ₁ < ρ₂ → τ₁² < τ₂²
--       → τ₁¹ - ρ₁ ⇒ τ₁² < τ₂¹ - ρ₂ ⇒ τ₂²

data Ctx : Nat → Set where
  ø    : Ctx Z
  _,_  : ∀{n} → Ctx n → Typ T → Ctx (S n)

infixl 20 _,_

infix 19 _∋_
data _∋_ : ∀{n} → Ctx n → Typ T → Set where
  z : ∀{n} {Γ : Ctx n} {τ : Typ T}                      → Γ , τ ∋ τ
  s : ∀{n} {Γ : Ctx n} {τ : Typ T} {τ' : Typ T} → Γ ∋ τ → Γ , τ' ∋ τ

stripvar : ∀{n} {Γ : Ctx n} {τ} → Γ ∋ τ → < n
stripvar z = z
stripvar (s x) = s (stripvar x)


infix 19 _⊢_⦂_/_
data _⊢_⦂_/_ {n : Nat} (Γ : Ctx n) : Exp n → Typ T → Typ R → Set where
  T-var  : ∀{τ} → (x : Γ ∋ τ) → Γ ⊢ ′ (stripvar x) ⦂ τ / ι
  T-lam  : ∀{τ₁ τ₂ ρ e} → Γ , τ₁ ⊢ e ⦂ τ₂ / ρ → Γ ⊢ ƛ e ⦂ τ₁ - ρ ⇒ τ₂ / ι
  T-app  : ∀{τ₁ τ₂ ρ e₁ e₂} → Γ ⊢ e₁ ⦂ τ₁ - ρ ⇒ τ₂ / ρ → Γ ⊢ e₂ ⦂ τ₁ / ρ → Γ ⊢ e₁ · e₂ ⦂ τ₂ / ρ
  T-lift : ∀{τ ε ρ e} → Γ ⊢ e ⦂ τ / ρ → Γ ⊢ [ e ] ⦂ τ / ε · ρ
  T-do   : ∀{τ₁ τ₂ v} → {Val v}
         → Γ ⊢ v ⦂ τ₁ / ι
         → Γ ⊢ (do' v) ⦂ τ₂ / ((E τ₁ ⇒ τ₂) · ι)
  T-hndl : ∀ {τ τᵣ} {ρ} {τ₁ τ₂} {e eₕ eᵣ}
         → Γ ⊢ e ⦂ τ / (E τ₁ ⇒ τ₂) · ρ
         → Γ , τ₁ , (τ₂ - ρ ⇒ τᵣ) ⊢ eₕ ⦂ τᵣ / ρ
         → Γ , τ ⊢ eᵣ ⦂ τᵣ / ρ
         → Γ ⊢ hndl e eₕ eᵣ ⦂ τᵣ / ρ
