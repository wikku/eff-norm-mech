module Impl where


_∘_ : ∀{a b c : Set} → (b → c) → (a → b) → a → c
f ∘ g = \x → f (g x)

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

data Ctx : Set where
  ø    : Ctx
  _,_  : Ctx → Typ T → Ctx

infixl 20 _,_

infix 19 _∋_
data _∋_ : Ctx → Typ T → Set where
  Z : ∀{Γ} {τ : Typ T}                       → Γ , τ ∋ τ
  S : ∀{Γ} {τ : Typ T} {τ' : Typ T} → Γ ∋ τ → Γ , τ' ∋ τ

infix 19 _⊢_/_
data _⊢_/_  Γ : Typ T → Typ R → Set where
  ′    : ∀{τ} → Γ ∋ τ → Γ ⊢ τ / ι
  ƛ    : ∀{τ₁ τ₂ ρ} → Γ , τ₁ ⊢ τ₂ / ρ → Γ ⊢ τ₁ - ρ ⇒ τ₂ / ι
  _·_  : ∀{τ₁ τ₂ ρ} → Γ ⊢ τ₁ - ρ ⇒ τ₂ / ρ → Γ ⊢ τ₁ / ρ → Γ ⊢ τ₂ / ρ
  [_]  : ∀{τ ε ρ} → Γ ⊢ τ / ρ → Γ ⊢ τ / ε · ρ
  do'  : ∀{τ₁ τ₂ : Typ T}
       → Γ ⊢ τ₁ / ι
       → Γ ⊢ τ₂ / (E τ₁ ⇒ τ₂) · ι
  hndl : ∀ {τ τᵣ : Typ T} {ρ : Typ R} {τ₁ τ₂ : Typ T}
       → Γ ⊢ τ / (E τ₁ ⇒ τ₂) · ρ
       → Γ , τ₁ , (τ₂ - ρ ⇒ τᵣ)
         ⊢ τᵣ / ρ
       → Γ , τ ⊢ τᵣ / ρ
       → Γ ⊢ τᵣ / ρ
  -- TODO: subtyping

-- TODO: rename rather than extend??
