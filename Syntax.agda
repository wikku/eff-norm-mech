module Syntax where

open import Agda.Builtin.Nat renaming (zero to Z ; suc to S)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

open import Function.Base using (_∘_)


data <_ : Nat -> Set where
  z : ∀{n} → < (S n)
  s : ∀{n} → < n → < (S n)

data Exp (n : Nat) : Set where
  ′    : < n → Exp n
  Lit  : Nat → Exp n
  ƛ    : Exp (S n) → Exp n
  _·_  : Exp n → Exp n → Exp n
  [_]  : Exp n → Exp n
  do'  : Exp n → Exp n
  hndl : Exp n → Exp (S (S n)) → Exp (S n) → Exp n

data Val : ∀ {n} → Exp n → Set where
  VVar : ∀{n} → {x : < n} → Val (′ x)
  VLit : ∀{m n : Nat} → Val {m} (Lit n)
  VLam : ∀{n} → {e : Exp (S n)} → Val (ƛ e)

data Ktx n : Set where
  Hole : Ktx n
  Fun  : Ktx n → Exp n → Ktx n
  Arg  : (v : Exp n) → {Val v} → Ktx n → Ktx n
  Lift : Ktx n → Ktx n
  Hndl : Ktx n → Exp (S (S n)) → Exp (S n) → Ktx n

data _free_ : Nat → ∀{n} → Ktx n → Set where
  fhole : ∀{n} → Z free (Hole {n})
  ffun  : ∀{n m} {K : Ktx m} → n free K → (e : Exp m) → n free (Fun K e)
  farg  : ∀{n m} {K : Ktx m} → n free K → (v : Exp m) → {u : Val v} → n free (Arg v {u} K)
  flift : ∀{n m} {K : Ktx m} → n free K → (S n) free (Lift K)
  fhndl : ∀{n m} {K : Ktx m}
        → (S n) free K → (eₕ : Exp (S (S m))) → (eᵣ : Exp (S m))
        → n free (Hndl K eₕ eᵣ)


plug : ∀{n} → Ktx n → Exp n → Exp n
plug Hole e = e
plug (Fun K x) e = plug K e · x
plug (Arg v K) e = v · plug K e
plug (Lift K) e = [ plug K e ]
plug (Hndl K eₕ eᵣ) e = hndl (plug K e) eₕ eᵣ

plugK : ∀{n} → Ktx n → Ktx n → Ktx n
plugK Hole K' = K'
plugK (Fun K x) K' = Fun (plugK K K') x
plugK (Arg v {u} K) K' = Arg v {u} (plugK K K')
plugK (Lift K) K' = Lift (plugK K K')
plugK (Hndl K x x₁) K' = Hndl (plugK K K') x x₁

Ren : Nat → Nat → Set
Ren n m = < n → < m

lift : ∀{n m} → Ren n m → Ren (S n) (S m)
lift ρ z = z
lift ρ (s x) = s (ρ x)

ren : ∀{n m} → Ren n m → Exp n → Exp m
ren ρ (′ x) = ′ (ρ x)
ren ρ (Lit n) = (Lit n)
ren ρ (ƛ e) = ƛ (ren (lift ρ) e)
ren ρ (e₁ · e₂) = ren ρ e₁ · ren ρ e₂
ren ρ [ e ] = [ ren ρ e ]
ren ρ (do' e) = do' (ren ρ e)
ren ρ (hndl e e₁ e₂) = hndl (ren ρ e) (ren (lift (lift ρ)) e₁) (ren (lift ρ) e₂)

renV : ∀{n m} {e : Exp n} → (ρ : Ren n m) → Val e → Val (ren {n} {m} ρ e)
renV ρ VVar = VVar
renV ρ VLit = VLit
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

-- renaming properties


-- substitutions

Sub : Nat → Nat → Set
Sub n m = < n → Exp m

liftsub : ∀{n m} → Sub n m → Sub (S n) (S m)
liftsub γ z = ′ z
liftsub γ (s x) = weaken (γ x)

sub : ∀{n m} → Sub n m → Exp n → Exp m
sub γ (′ x) = γ x
sub γ (Lit n) = Lit n
sub γ (ƛ e) = ƛ (sub (liftsub γ) e)
sub γ (e₁ · e₂) = sub γ e₁ · sub γ e₂
sub γ [ e ] = [ sub γ e ]
sub γ (do' e) = do' (sub γ e)
sub γ (hndl e e₁ e₂) = hndl (sub γ e) (sub (liftsub (liftsub γ)) e₁) (sub (liftsub γ) e₂)

ext : ∀{n m} → Sub n m → Exp m → Sub (S n) m
ext γ e z = e
ext γ e (s x) = γ x

sub1 : ∀{n} → Exp n → Exp (S n) → Exp n
sub1 e' e = sub (ext ′ e') e

sub2 : ∀{n} → Exp n → Exp n → Exp (S (S n)) → Exp n
sub2 e' e'' e = sub (ext (ext ′ e') e'') e

-- substitution properties

-- liftsub-id : ∀{n} {x : < S n} → liftsub ′ x ≡ ′ x
-- liftsub-id {n} {z} = refl
-- liftsub-id {n} {s x} = refl

liftsub-id : ∀{n} {x : < S n} → liftsub ′ x ≡ ′ x
liftsub-id {n} {z} = refl
liftsub-id {n} {s x} = refl


liftsub-ext-id : ∀{n} {γ} → ((x : < n) → γ x ≡ ′ x) → (x : < S n) → liftsub γ x ≡ ′ x
liftsub-ext-id {n} {γ} f z = refl
liftsub-ext-id {n} {γ} f (s x) = cong weaken (f x)

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x x' y y' z z'} → x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

liftsub-cong : ∀{n m} {γ₁ γ₂ : Sub n m} → ((x : < n) → γ₁ x ≡ γ₂ x) → (x : < S n) → liftsub γ₁ x ≡ liftsub γ₂ x
liftsub-cong ext z = refl
liftsub-cong ext (s x) = cong weaken (ext x)

sub-cong : ∀{n m} {γ₁ γ₂ : Sub n m} → ((x : < n) → γ₁ x ≡ γ₂ x) → (e : Exp n) → sub γ₁ e ≡ sub γ₂ e
sub-cong ext (′ x) = ext x
sub-cong ext (Lit x) = refl
sub-cong ext (ƛ e) = cong ƛ (sub-cong (liftsub-cong ext) e)
sub-cong ext (e₁ · e₂) = cong₂ _·_ (sub-cong ext e₁) (sub-cong ext e₂)
sub-cong ext [ e ] = cong [_] (sub-cong ext e)
sub-cong ext (do' e) = cong do' (sub-cong ext e)
sub-cong ext (hndl e eₕ eᵣ) = cong₃ hndl (sub-cong ext e) (sub-cong (liftsub-cong (liftsub-cong ext)) eₕ) (sub-cong (liftsub-cong ext) eᵣ)

sub-ext-id : ∀{n} {γ} → ((x : < n) → γ x ≡ ′ x) → (e : Exp n) → sub γ e ≡ e
sub-ext-id {n} {γ} ext (′ x₁) = ext x₁
sub-ext-id {n} {γ} ext (Lit x₁) = refl
sub-ext-id {n} {γ} ext (ƛ e) = cong ƛ (sub-ext-id (liftsub-ext-id ext) e)
sub-ext-id {n} {γ} ext (e · e₁) = cong₂ _·_ (sub-ext-id ext e) (sub-ext-id ext e₁)
sub-ext-id {n} {γ} ext [ e ] = cong [_] (sub-ext-id ext e)
sub-ext-id {n} {γ} ext (do' e) = cong do' (sub-ext-id ext e)
sub-ext-id {n} {γ} ext (hndl e e₁ e₂) =
  cong₃ hndl (sub-ext-id ext e)
             (sub-ext-id (liftsub-ext-id (liftsub-ext-id ext)) (e₁))
             (sub-ext-id (liftsub-ext-id ext) e₂)

sub-′-id : ∀{n} {e : Exp n} → sub ′ e ≡ e
sub-′-id {n} {e} = sub-ext-id (\x → refl) e

sub1-weaken-id : ∀{n} {e'} {e : Exp n} → sub1 e' (weaken e) ≡ e
sub1-weaken-id {n} {e'} {′ x} = refl
sub1-weaken-id {n} {e'} {Lit x} = refl
sub1-weaken-id {n} {e'} {ƛ e} = let eq = sub1-weaken-id {S n} {weaken e'} {e} in {!!}
sub1-weaken-id {n} {e'} {e · e₁} = {!!}
sub1-weaken-id {n} {e'} {[ e ]} = cong [_] sub1-weaken-id
sub1-weaken-id {n} {e'} {do' e} = cong do' sub1-weaken-id
sub1-weaken-id {n} {e'} {hndl e e₁ e₂} = {!!}

liftsub-comp : ∀{n m k} {γ : Sub m k} {ρ : Ren n m} (x : < S n) → (liftsub γ) (lift ρ x) ≡ (liftsub (γ ∘ ρ)) x
liftsub-comp {n} {m} {k} {γ} {ρ} (z) = refl
liftsub-comp {n} {m} {k} {γ} {ρ} (s x) = refl

sub-ren-lift : ∀{n m k} (γ : Sub m k) (ρ : Ren n m) (e : Exp (S n))
             → sub (liftsub γ) (ren (lift ρ) e) ≡ sub (liftsub (γ ∘ ρ)) e
sub-ren-lift {n} {m} {k} γ ρ (′ z) = refl
sub-ren-lift {n} {m} {k} γ ρ (′ (s x)) = refl
sub-ren-lift {n} {m} {k} γ ρ (Lit x) = refl
sub-ren-lift {n} {m} {k} γ ρ (ƛ e) =
  cong ƛ (trans (sub-ren-lift (liftsub γ) (lift ρ) e) (sub-cong (liftsub-cong liftsub-comp) e))
sub-ren-lift {n} {m} {k} γ ρ (e₁ · e₂) = cong₂ _·_ (sub-ren-lift γ ρ e₁) (sub-ren-lift γ ρ e₂)
sub-ren-lift {n} {m} {k} γ ρ ([ e ]) = cong [_] (sub-ren-lift γ ρ e)
sub-ren-lift {n} {m} {k} γ ρ (do' e) = cong do' (sub-ren-lift γ ρ e)
sub-ren-lift {n} {m} {k} γ ρ (hndl e eₕ eᵣ) =
  cong₃ hndl (sub-ren-lift γ ρ e)
             (trans (sub-ren-lift (liftsub (liftsub γ)) (lift (lift ρ)) eₕ)
                    (trans (sub-cong (liftsub-cong liftsub-comp) eₕ)
                           (sub-cong (liftsub-cong (liftsub-cong liftsub-comp)) eₕ)))
             (trans (sub-ren-lift (liftsub γ) (lift ρ) eᵣ) (sub-cong (liftsub-cong liftsub-comp) eᵣ))

sub-ren : ∀{n m k} {γ : Sub m k} {ρ : Ren n m} {e : Exp n} → sub γ (ren ρ e) ≡ sub (γ ∘ ρ) e
sub-ren {n} {m} {k} {γ} {ρ} {′ x} = refl
sub-ren {n} {m} {k} {γ} {ρ} {Lit x} = refl
sub-ren {n} {m} {k} {γ} {ρ} {ƛ e} = {!!}
sub-ren {n} {m} {k} {γ} {ρ} {e · e₁} = {!!}
sub-ren {n} {m} {k} {γ} {ρ} {[ e ]} = {!!}
sub-ren {n} {m} {k} {γ} {ρ} {do' e} = {!!}
sub-ren {n} {m} {k} {γ} {ρ} {hndl e e₁ e₂} = {!!}

sub1-comm : ∀{n γ} {e' : Exp Z} {e : Exp (S n)} → sub1 e' (sub (liftsub γ) e) ≡ sub (ext γ e') e
sub1-comm {n} {γ} {e'} {′ z} = refl
sub1-comm {n} {γ} {e'} {′ (s x)} = {!!}
sub1-comm {n} {γ} {e'} {Lit x} = refl
sub1-comm {n} {γ} {e'} {ƛ e} = {!!}
sub1-comm {n} {γ} {e'} {e · e₁} = {!!}
sub1-comm {n} {γ} {e'} {[ e ]} = {!!}
sub1-comm {n} {γ} {e'} {do' e} = {!!}
sub1-comm {n} {γ} {e'} {hndl e e₁ e₂} = {!!}
