module Reduction where

open import Syntax
open import Agda.Builtin.Nat renaming (zero to Z ; suc to S)

data _↦_ : Exp Z → Exp Z → Set where
  β-fun  : ∀ (e : Exp (S Z)) (v : Exp Z) → {Val v} → (ƛ e · v) ↦ sub1 v e
  β-lift : ∀ v → {Val v} → [ v ] ↦ v
  β-hndl : ∀ {v} {eₕ : Exp (S (S Z))} {eᵣ : Exp (S Z)} → {Val v} → ∀ K → {0 free K}
         → hndl (plug K (do' v)) eₕ eᵣ ↦
         sub2 v (ƛ (hndl (plug (weakenK K) (′ z)) (weaken eₕ) (weaken eᵣ))) eₕ
  β-ret  : ∀ v eₕ eᵣ → {Val v}
         → hndl v eₕ eᵣ ↦ sub1 v eᵣ

data _↠_ : Exp Z → Exp Z → Set where
  cong : ∀{e e'} → ∀ K → e ↦ e' → plug K e ↠ plug K e'

data _↠*_ : Exp Z → Exp Z → Set where
  ↠id    : ∀ e → e ↠* e
  ↠one   : ∀{e e'} → e ↠ e' → e ↠* e'
  _↠trans_ : ∀{e e' e''} → e ↠* e' → e' ↠* e'' → e ↠* e''


Fun-cong : ∀{e e'} a → e ↠ e' → (e · a) ↠ (e' · a)
Fun-cong a (cong K r) = cong (Fun K a) r

Arg-cong : ∀{e e'} v → Val v → e ↠ e' → (v · e) ↠ (v · e')
Arg-cong v u (cong K r) = cong (Arg v {u} K) r

Lift-cong : ∀{e e'} → e ↠ e' → [ e ] ↠ [ e' ]
Lift-cong (cong K r) = cong (Lift K) r

Hndl-cong : ∀{e e'} eₕ eᵣ → e ↠ e' → (hndl e eₕ eᵣ) ↠ (hndl e' eₕ eᵣ)
Hndl-cong eₕ eᵣ (cong K x) = cong (Hndl K eₕ eᵣ) x

plugr : (K : Ktx Z) → ∀{e e'} → e ↠ e' → plug K e ↠ plug K e'
plugr Hole (cong K₁ r) = cong K₁ r
plugr (Fun K x) t = Fun-cong x (plugr K t)
--plugr (Fun K x) t with (plugr K t)
--... | w = {!!} -- can't generalize because needs ∀{K[e] K[e']}??? TODO
plugr (Arg v {u} K) t = Arg-cong v u (plugr K t)
plugr (Lift K) t = Lift-cong (plugr K t)
plugr (Hndl K eₕ eᵣ) t = Hndl-cong eₕ eᵣ (plugr K t)

plugr* : (K : Ktx Z) → ∀{e e'} → e ↠* e' → plug K e ↠* plug K e'
plugr* K (↠id e) = ↠id (plug K e)
plugr* K (↠one r) = ↠one (plugr K r)
plugr* K (t₁ ↠trans t₂) = plugr* K t₁ ↠trans plugr* K t₂
