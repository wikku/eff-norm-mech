{-# OPTIONS --cumulativity #-}

module LogRel where

open import Data.Empty
open import Data.Sum
open import Data.Unit
open import Data.Product using (_×_ ; Σ ; proj₁ ; proj₂)
--open import Agda.Builtin.Sigma
--open import Agda.Builtin.Bool
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)
open import Agda.Builtin.Nat using (Nat) renaming (zero to Z ; suc to S)
import Level
open import Level.Literals

open import Syntax
open import Typ

data CVal : Set₁ where
  CV : (e : Exp Z) → {Val e} → CVal

unCV : CVal → Exp Z
unCV (CV e) = e

open import Reduction

data _↠v_ : Exp Z → CVal → Set where
  eval : ∀{e v} → e ↠* unCV v → e ↠v v


data _↠^_ : Exp Z → (Exp Z → Set₁) → Set₁ where
  trace : ∀{e e' P} → e ↠ e' → P e' → e ↠^ P

data _↠v^_ : Exp Z → (CVal → Set₁) → Set₁ where
  tracev : ∀{e v P} → e ↠v v → P v → e ↠v^ P

β-lift-v : (v : CVal) → [ unCV v ] ↦ unCV v
β-lift-v (CV e {v}) = β-lift e {v}


SemType : Set₁
SemType = CVal → Set

data StkOp : Set₁ where
  SO : CVal → Nat → SemType → StkOp

SemEff : Set₁
SemEff = StkOp → Set

basis : Kind → Set₁
--basis T = Level.Lift (Level.levelOfType StkOp) CVal
basis T = CVal
basis E = StkOp
basis R = StkOp

K⟦_⟧ : Kind → Set₁
K⟦ κ ⟧ = basis κ → Set

--data EorR : Kind → Set where
--  IsE : EorR E
--  IsR : EorR R
--
--data K⟦_⟧ : Kind → Set where
--  SV : SemType → K⟦ T ⟧
--  SE : ∀{κ : Kind} → {EorR κ} → SemEff → K⟦ κ ⟧


--data D⟦_⟧ : Ctx* → Set where
--  ø    : D⟦ ø ⟧
--  _&_ : ∀{Δ κ} → D⟦ Δ ⟧ → K⟦ κ ⟧ → D⟦ Δ ,* κ ⟧

--FULL : SemType
--FULL x = true
data FULL : SemType where
  any : ∀ (v : CVal) → FULL v



--data _∈T⟦_⟧ : ∀{κ} → basis κ → Typ κ → Set₁ where
--  Fun : ∀ {τ₁ τ₂ : Typ T} {ρ : Typ R} {e : Exp (S Z)} → (∀ v {v∈T⟦ τ₁ ⟧} → v) → (CV (Lam e) {VLam}) ∈T⟦ τ₁ - ρ ⇒ τ₂ ⟧
----  Eff : ∀ {τ₁ τ₂} v {v ∈T⟦ τ₁ ⟧} → (SO (do' v) Z (_∈T⟦ τ₂ ⟧)) ∈T⟦ E τ₁ ⇒ τ₂ ⟧



data _∈E[_/_] : Exp Z → (CVal → Set₁) → (StkOp → Set₁) → Set₁ where
  Evl : ∀{e v μ ξ} → e ↠v v → μ v → e ∈E[ μ / ξ ]
  Stk : ∀{e v K n μ μ' ξ}
      → e ↠* plug K (do' (unCV v))
      → ξ (SO v n μ')
      → n free K
      → (∀ u → μ' u → plug K (unCV u) ∈E[ μ / ξ ])
      → e ∈E[ μ / ξ ]


mutual
  --infix 19 _∈V⟦_⟧
  _∈V⟦_⟧ : CVal → Typ T → Set₁
  CV (Lit n) ∈V⟦ B ⟧ = ⊤
  CV (ƛ e) ∈V⟦ τ₁ - ρ ⇒ τ₂ ⟧ = (v : CVal) → v ∈V⟦ τ₁ ⟧ → (sub1 (unCV v) e) ∈E⟦ τ₂ / ρ ⟧
  _ ∈V⟦ _ ⟧ = ⊥

  _∈F'⟦_⟧ : StkOp → Typ E → Set₁
  (SO v Z μ) ∈F'⟦ E τ₁ ⇒ τ₂ ⟧ = v ∈V⟦ τ₁ ⟧
    × (∀ u → μ u → u ∈V⟦ τ₂ ⟧) -- FIXME
    × (∀ u → u ∈V⟦ τ₂ ⟧ → μ u) -- FIXME
  (SO _ _ μ) ∈F'⟦ E τ₁ ⇒ τ₂ ⟧ = ⊥

  _∈F⟦_⟧ : StkOp → Typ R → Set₁
  (SO e Z μ) ∈F⟦ ε · ρ ⟧ = (SO e Z μ) ∈F'⟦ ε ⟧
  (SO e (S n) μ) ∈F⟦ ε · ρ ⟧ = (SO e n μ) ∈F⟦ ρ ⟧
  (SO _ _ _) ∈F⟦ ι ⟧ = ⊥

  _∈E⟦_/_⟧ : (e : Exp Z) → Typ T → Typ R → Set₁
  e ∈E⟦ τ / ρ ⟧ = e ∈E[ (_∈V⟦ τ ⟧) / (_∈F⟦ ρ ⟧) ]

  --_∈S⟦_/_⟧ : (e : Exp Z) → Typ T → Typ R → Set₁
  --e ∈S⟦ τ / ρ ⟧ = ⊤

--liftF : ∀{v n μ ε ρ} → (SO v n μ) ∈F⟦ ρ ⟧ → (SO v (S n) μ) ∈F⟦ ε · ρ ⟧
--liftF = λ z₁ → z₁


len : ∀{n} → Ctx n → Nat
len {n} _ = n


G⟦_⟧ : ∀{n} → Ctx n → Set₁
G⟦ Γ ⟧ = ∀ {τ} → Γ ∋ τ → Σ {# 1} {# 1} CVal _∈V⟦ τ ⟧ -- TODO: wtf? explicit levels

ext$ : ∀{n} {Γ : Ctx n} {τ} → G⟦ Γ ⟧ → ∀ v →  v ∈V⟦ τ ⟧ → G⟦ Γ , τ ⟧
ext$ γ v w z = v Data.Product., w
ext$ γ v w (s x) = γ x


--sub$ : ∀{n} {Γ} → G⟦ Γ ⟧ → Exp (len Γ) → Exp 0
--sub$ {Γ} γ (′ x) = {!!}
--sub$ {Γ} γ t = t
--sub$ {Γ} γ f = f
--sub$ {Γ} γ (ƛ e) = ƛ (sub$ (lift$ γ) e)
--sub$ {Γ} γ (e · e₁) = {!!}
--sub$ {Γ} γ [ e ] = {!!}
--sub$ {Γ} γ (do' e) = {!!}
--sub$ {Γ} γ (hndl e e₁ e₂) = {!!}

stripsub : ∀{n} {Γ : Ctx n} → G⟦ Γ ⟧ → Sub n 0
stripsub {n} {Γ , τ} γ z = unCV (proj₁ (γ z))
stripsub {S n} {Γ , τ} γ (s x) = stripsub {n} {Γ} (\y → γ (s y)) x

--commute : ∀ {Γ γ τ} {x} → sub (stripsub γ) (strip (′ x)) ≡ proj₁ (γ x)
stripsub-ext$ : ∀{n} {Γ : Ctx n} {γ : G⟦ Γ ⟧} {τ : Typ T} {v} {w : v ∈V⟦ τ ⟧} (x : < S n)
              → stripsub (ext$ γ v w) x ≡ ext (stripsub γ) (unCV v) x
stripsub-ext$ z = refl
stripsub-ext$ (s x) = refl

stripsub-stripvar : ∀{n} {Γ : Ctx n} {γ : G⟦ Γ ⟧} {τ : Typ T} (x : Γ ∋ τ)
                  → unCV (proj₁ (γ x)) ≡ stripsub γ (stripvar x)
stripsub-stripvar z = refl
stripsub-stripvar (s x) = stripsub-stripvar x


lam-compat : ∀{e τ₁ ρ τ₂} → (∀{v} → v ∈V⟦ τ₁ ⟧ → sub1 (unCV v) e ∈E⟦ τ₂ / ρ ⟧) → ƛ e ∈E⟦ τ₁ - ρ ⇒ τ₂ / ι ⟧
lam-compat {e} f = let cv = CV (ƛ e) {VLam} in Evl (eval {_} {cv} (↠id (ƛ e))) (\v u → f u) -- TODO: ugly

lift-compat : ∀{e τ ε ρ} → e ∈E⟦ τ / ρ ⟧ → [ e ] ∈E⟦ τ / ε · ρ ⟧
lift-compat (Evl (eval {_} {v} t) w) = Evl (eval (plugr* (Lift Hole) t ↠trans ↠one (cong Hole (β-lift-v v)))) w
lift-compat (Stk t so f k) = Stk (plugr* (Lift Hole) t) so (flift f) (\u w → lift-compat (k u w))

compat : ∀{n} {Γ : Ctx n} {τ ρ} {e : Exp n} → Γ ⊢ e ⦂ τ / ρ → (γ : G⟦ Γ ⟧) → sub (stripsub γ) e ∈E⟦ τ / ρ ⟧
-- compat {_} {Γ} {_} {_} {.(′ (stripvar x))} (T-var x) γ with γ x
-- ... | v Data.Product., w = Evl (subst (_↠v v) (stripsub-stripvar x) (eval (↠id (unCV v)))) w
compat {_} {Γ} {_} {_} {.(′ (stripvar x))} (T-var x) γ =
  let v = proj₁ (γ x); w = proj₂ (γ x) in
  Evl (subst (_↠v v) (stripsub-stripvar x) (eval (↠id (unCV v)))) w
compat {_} {Γ} {_} {_} {(ƛ e)} (T-lam d) γ =
  lam-compat (\{v} w → let p = compat d (ext$ γ v w)
                           eq = sub1-comp {γ = stripsub γ} {e' = unCV v} {e = e} in
                           subst _∈E⟦ _ / _ ⟧ (trans (sub-cong stripsub-ext$ e) (sym eq)) p)
compat {_} {Γ} {_} {_} {.(_ · _)} (T-app d d₁) γ = {!!}
compat {_} {Γ} {_} {_} {([ e ])} (T-lift d) γ = lift-compat (compat d γ)
compat {_} {Γ} {_} {_} {.(do' _)} (T-do d) γ = {!!}
compat {_} {Γ} {_} {_} {.(hndl _ _ _)} (T-hndl d d₁ d₂) γ = {!!}
