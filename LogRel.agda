{-# OPTIONS --cumulativity #-}

module LogRel where

open import Impl
open import Data.Empty
open import Data.Sum
open import Data.Unit
open import Data.Product using (_×_ ; Σ ; proj₁ ; proj₂)
--open import Agda.Builtin.Sigma
--open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat renaming (zero to Z ; suc to S)
import Level
open import Level.Literals

--data Nat : Set where
--  Z : Nat
--  S : Nat → Nat

data <_ : Nat -> Set where
  z : ∀{n} → < (S n)
  s : ∀{n} → < n → < (S n)


data Exp n : Set where
  Var  : < n → Exp n
  t f  : Exp n
  Lam  : Exp (S n) → Exp n
  _·_  : Exp n → Exp n → Exp n
  [_]  : Exp n → Exp n
  do'  : Exp n → Exp n
  hndl : Exp n → Exp (S (S n)) → Exp (S n) → Exp n

data Val : {n : Nat} → Exp n → Set where
  VVar : ∀{n} {m : < n} → Val (Var m)
  VLam : ∀{n} {e : Exp (S n)} → Val (Lam e)

data Ktx : Nat → Set where
  Hole : ∀{n} → Ktx n
  Fun  : ∀{n} → Ktx n → Exp n → Ktx n
  Arg  : ∀{n} → (v : Exp n) → {Val v} → Ktx n → Ktx n
  Lift : ∀{n} → Ktx n → Ktx n
  Hndl : ∀{n} → Ktx n → Exp (S (S n)) → Exp (S n) → Ktx n

data _free_ : Nat → {b : Nat} → Ktx b → Set where
  fhole : ∀{b} → Z free (Hole {b})
  ffun  : ∀{n b} {K : Ktx b} → n free K → (e : Exp b) → n free (Fun K e)
  farg  : ∀{n b} {K : Ktx b} → n free K → (v : Exp b) → {u : Val v} → n free (Arg v {u} K)
  flift : ∀{n b} {K : Ktx b} → n free K → (S n) free (Lift K)
  fhndl : ∀{n b} {K : Ktx b}
        → (S n) free K → (eₕ : Exp (S (S b))) → (eᵣ : Exp (S b))
        → n free (Hndl K eₕ eᵣ)

plug : ∀{n} → Ktx n → Exp n → Exp n
plug Hole e = e
plug (Fun K x) e = plug K e · x
plug (Arg v K) e = v · plug K e
plug (Lift K) e = [ plug K e ]
plug (Hndl K eₕ eᵣ) e = hndl (plug K e) eₕ eᵣ

Ren : Nat → Nat → Set
Ren n m = < n → < m

lift : ∀{n m} → Ren n m → Ren (S n) (S m)
lift ρ z = z
lift ρ (s x) = s (ρ x)

ren : ∀{n m} → Ren n m → Exp n → Exp m
ren ρ (Var x) = Var (ρ x)
ren ρ t = t
ren ρ f = f
ren ρ (Lam e) = Lam (ren (lift ρ) e)
ren ρ (e₁ · e₂) = ren ρ e₁ · ren ρ e₂
ren ρ [ e ] = [ ren ρ e ]
ren ρ (do' e) = do' (ren ρ e)
ren ρ (hndl e e₁ e₂) = hndl (ren ρ e) (ren (lift (lift ρ)) e₁) (ren (lift ρ) e₂)

renV : ∀{n m ρ} {e : Exp n} → Ren n m → Val e → Val (ren {n} {m} ρ e)
renV ρ VVar = VVar
renV ρ VLam = VLam

renK : ∀{n m} → Ren n m → Ktx n → Ktx m
renK ρ Hole = Hole
renK ρ (Fun K x) = Fun (renK ρ K) (ren ρ x)
renK ρ (Arg v {p} K) = Arg (ren ρ v) {renV ρ p} (renK ρ K)
renK ρ (Lift K) = Lift (renK ρ K)
renK ρ (Hndl K eₕ eᵣ) = Hndl (renK ρ K) (ren (lift (lift ρ)) eₕ) (ren (lift ρ) eᵣ)

weaken : ∀{n} → Exp n → Exp (S n)
weaken = ren s

weakenK : ∀{n} → Ktx n → Ktx (S n)
weakenK = renK s

Sub : Nat → Nat → Set
Sub n m = < n → Exp m

liftsub : ∀{n m} → Sub n m → Sub (S n) (S m)
liftsub γ z = Var z
liftsub γ (s x) = weaken (γ x)

sub : ∀{n m} → Sub n m → Exp n → Exp m
sub γ (Var x) = γ x
sub γ t = t
sub γ f = f
sub γ (Lam e) = Lam (sub (liftsub γ) e)
sub γ (e₁ · e₂) = sub γ e₁ · sub γ e₂
sub γ [ e ] = [ sub γ e ]
sub γ (do' e) = do' (sub γ e)
sub γ (hndl e e₁ e₂) = hndl (sub γ e) (sub (liftsub (liftsub γ)) e₁) (sub (liftsub γ) e₂)

ext : ∀{n m} → Sub n m → Exp m → Sub (S n) m
ext γ e z = e
ext γ e (s x) = γ x

sub1 : Exp Z → Exp (S Z) → Exp Z
sub1 e' e = sub (ext Var e') e

sub2 : Exp Z → Exp Z → Exp (S (S Z)) → Exp Z
sub2 e' e'' e = sub (ext (ext Var e') e'') e

--
--K⟦_⟧   : Kind → Set
--K⟦ T ⟧ = CVal
--K⟦ E ⟧ = SemEff
--K⟦ R ⟧ = SemEff

data CVal : Set where
  CV : (e : Exp Z) → {Val e} → CVal

unCV : CVal → Exp Z
unCV (CV e) = e

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
K⟦ κ ⟧ = basis κ → Set -- which universe for predicate??

--K⟦_⟧ : Kind → Set₁
--K⟦ T ⟧ = SemType
--K⟦ E ⟧ = SemEff
--K⟦ R ⟧ = SemEff

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


data _↦_ : Exp Z → Exp Z → Set where
  β-fun  : ∀ e (v : Exp Z) → {Val v} → (Lam e · v) ↦ sub1 v e
  β-lift : ∀ v → {Val v} → [ v ] ↦ v
  β-hndl : ∀ v eₕ eᵣ → {Val v} → ∀ K → {Z free K}
         → hndl (plug K (do' v)) eₕ eᵣ ↦
         sub2 v (Lam (hndl (plug (weakenK K) (Var z)) (weaken eₕ) (weaken eᵣ))) eₕ
  β-ret  : ∀ v eₕ eᵣ → {Val v}
         → hndl v eₕ eᵣ ↦ sub1 v eᵣ

data _↠_ : Exp Z → Exp Z → Set where
  cong : ∀{e e'} → e ↦ e' → ∀ K → plug K e ↠ plug K e'

data _↠*_ : Exp Z → Exp Z → Set where
  ↠id    : ∀{e} → e ↠* e
  ↠trans : ∀{e e' e''} → e ↠ e' → e' ↠* e'' → e ↠* e''

data _↠v_ : Exp Z → CVal → Set where
  eval : ∀{e v} → e ↠* unCV v → e ↠v v


data _↠^_ : Exp Z → (Exp Z → Set₁) → Set₁ where
  trace : ∀{e e' P} → e ↠ e' → P e' → e ↠^ P

data _↠v^_ : Exp Z → (CVal → Set₁) → Set₁ where
  tracev : ∀{e v P} → e ↠v v → P v → e ↠v^ P

data _∈E[_/_] : Exp Z → (CVal → Set₁) → (StkOp → Set₁) → Set₁ where
  Evl : ∀{e v μ ξ} → e ↠v v → μ v → e ∈E[ μ / ξ ]
  Stk : ∀{e v K n μ μ' ξ}
      → e ↠* plug K (do' (unCV v))
      → ξ (SO v n μ')
      → n free K
      → (∀ u → μ' u → plug K (unCV u) ∈E[ μ / ξ ])
      → e ∈E[ μ / ξ ]


mutual
  _∈V⟦_⟧ : CVal → Typ T → Set₁
  CV t ∈V⟦ B ⟧ = ⊤
  CV f ∈V⟦ B ⟧ = ⊤
  CV (Lam e) ∈V⟦ τ₁ - ρ ⇒ τ₂ ⟧ = (v : CVal) → v ∈V⟦ τ₂ ⟧ → (sub1 (unCV v) e) ∈E⟦ τ₂ / ρ ⟧
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


len : Ctx → Nat
len ø = Z
len (g , x) = S (len g)


stripvar : ∀{Γ κ} → Γ ∋ κ → < (len Γ)
stripvar Z = z
stripvar (S x) = s (stripvar x)

strip : ∀{Γ τ ρ} → Γ ⊢ τ / ρ → Exp (len Γ)
strip (′ x) = Var (stripvar x)
strip (ƛ e) = Lam (strip e)
strip (e₁ · e₂) = strip e₁ · strip e₂
strip [ e ] = [ strip e ]
strip (do' e) = do' (strip e)
strip (hndl e e₁ e₂) = hndl (strip e) (strip e₁) (strip e₂)



G⟦_⟧ : Ctx → Set₁
G⟦ Γ ⟧ = ∀ {τ} → Γ ∋ τ → Σ {# 1} {# 1} CVal _∈V⟦ τ ⟧ -- TODO: wtf? explicit levels


sub$ : ∀{Γ} → G⟦ Γ ⟧ → Exp (len Γ) → Exp 0
sub$ {Γ} γ (Var x) = {!!}
sub$ {Γ} γ t = t
sub$ {Γ} γ f = f
sub$ {Γ} γ (Lam e) = Lam (sub$ (lift$ γ) e)
sub$ {Γ} γ (e · e₁) = {!!}
sub$ {Γ} γ [ e ] = {!!}
sub$ {Γ} γ (do' e) = {!!}
sub$ {Γ} γ (hndl e e₁ e₂) = {!!}

stripsub : ∀{Γ} → G⟦ Γ ⟧ → Sub (len Γ) 0
stripsub {Γ , τ} γ z = unCV (proj₁ (γ Z))
stripsub {Γ , τ} γ (s x) = stripsub {Γ} (\y → γ (S y)) x

--commute : ∀ {Γ γ τ} {x} → sub (stripsub γ) (strip (′ x)) ≡ proj₁ (γ x)

compat : ∀{Γ τ ρ} → (e : Γ ⊢ τ / ρ) → (γ : G⟦ Γ ⟧) → sub (stripsub γ) (strip e) ∈E⟦ τ / ρ ⟧
compat (′ x) γ = Evl {!!} (proj₂ (γ x))
compat (ƛ e) γ = {!!}
compat (e · e₁) γ = {!!}
compat [ e ] γ = {!!}
compat (do' e) γ = {!!}
compat (hndl e e₁ e₂) γ = {!!}
