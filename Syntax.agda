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
  _·_  : (e₁ : Exp n) → (e₂ : Exp n) → Exp n
  [_]  : Exp n → Exp n
  do'  : Exp n → Exp n
  hndl : (e : Exp n) → (eₕ : Exp (S (S n))) → (eᵣ : Exp (S n)) → Exp n

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

-- properties

-- liftsub-id : ∀{n} {x : < S n} → liftsub ′ x ≡ ′ x
-- liftsub-id {n} {z} = refl
-- liftsub-id {n} {s x} = refl


cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x x' y y' z z'} → x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

lift-cong : ∀{n m} {ρ₁ ρ₂ : Ren n m} → ((x : < n) → ρ₁ x ≡ ρ₂ x) → (x : < S n) → lift ρ₁ x ≡ lift ρ₂ x
lift-cong ext z = refl
lift-cong ext (s x) = cong s (ext x)

ren-cong : ∀{n m} {ρ₁ ρ₂ : Ren n m} → ((x : < n) → ρ₁ x ≡ ρ₂ x) → (e : Exp n) → ren ρ₁ e ≡ ren ρ₂ e
ren-cong ext (′ x) = cong ′ (ext x)
ren-cong ext (Lit x) = refl
ren-cong ext (ƛ e) = cong ƛ (ren-cong (lift-cong ext) e)
ren-cong ext (e₁ · e₂) = cong₂ _·_ (ren-cong ext e₁) (ren-cong ext e₂)
ren-cong ext [ e ] = cong [_] (ren-cong ext e)
ren-cong ext (do' e) = cong do' (ren-cong ext e)
ren-cong ext (hndl e eₕ eᵣ) = cong₃ hndl (ren-cong ext e) (ren-cong (lift-cong (lift-cong ext)) eₕ) (ren-cong (lift-cong ext) eᵣ)

lift-comp : ∀{n m k} {ρ₁ : Ren m k} {ρ₂ : Ren n m} (x : < (S n)) → lift (ρ₁ ∘ ρ₂) x ≡ (lift ρ₁) (lift ρ₂ x)
lift-comp z = refl
lift-comp (s x) = refl

ren-comp : ∀{n m k} {ρ₁ : Ren m k} {ρ₂ : Ren n m} (e : Exp n) → ren (ρ₁ ∘ ρ₂) e ≡ ren ρ₁ (ren ρ₂ e)
ren-comp (′ x) = refl
ren-comp (Lit x) = refl
ren-comp (ƛ e) = cong ƛ (trans (ren-cong lift-comp e) (ren-comp e))
ren-comp (e · e₁) = cong₂ _·_ (ren-comp e) (ren-comp e₁)
ren-comp [ e ] = cong [_] (ren-comp e)
ren-comp (do' e) = cong do' (ren-comp e)
ren-comp (hndl e eₕ eᵣ) =
  cong₃ hndl (ren-comp e)
             (trans (ren-cong (lift-cong lift-comp) eₕ)
                    (trans (ren-cong lift-comp eₕ) (ren-comp eₕ)))
             (trans (ren-cong lift-comp eᵣ) (ren-comp eᵣ))

liftsub-id : ∀{n} (x : < S n) → liftsub ′ x ≡ ′ x
liftsub-id (z) = refl
liftsub-id (s x) = refl


liftsub-ext-id : ∀{n} {γ} → ((x : < n) → γ x ≡ ′ x) → (x : < S n) → liftsub γ x ≡ ′ x
liftsub-ext-id {n} {γ} f z = refl
liftsub-ext-id {n} {γ} f (s x) = cong weaken (f x)


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

sub-id : ∀{n} {e : Exp n} → sub ′ e ≡ e
sub-id {n} {′ x} = refl
sub-id {n} {Lit x} = refl
sub-id {n} {ƛ e} = cong ƛ (trans (sub-cong liftsub-id e) sub-id)
sub-id {n} {e · e₁} = cong₂ _·_ sub-id sub-id
sub-id {n} {[ e ]} = cong [_] sub-id
sub-id {n} {do' e} = cong do' sub-id
sub-id {n} {hndl e e₁ e₂} =
  cong₃ hndl sub-id
             (trans (sub-cong (liftsub-cong liftsub-id) e₁)
                    (trans (sub-cong liftsub-id e₁) sub-id))
             (trans (sub-cong liftsub-id e₂) sub-id)

sub-ext-id : ∀{n} {γ} → ((x : < n) → γ x ≡ ′ x) → (e : Exp n) → sub γ e ≡ e
sub-ext-id {n} {γ} ext e = trans (sub-cong ext e) sub-id

-- sub1-weaken-id : ∀{n} {e'} {e : Exp n} → sub1 e' (weaken e) ≡ e
-- sub1-weaken-id {n} {e'} {′ x} = refl
-- sub1-weaken-id {n} {e'} {Lit x} = refl
-- sub1-weaken-id {n} {e'} {ƛ e} = let eq = sub1-weaken-id {S n} {weaken e'} {e} in {!!}
-- sub1-weaken-id {n} {e'} {e · e₁} = {!!}
-- sub1-weaken-id {n} {e'} {[ e ]} = cong [_] sub1-weaken-id
-- sub1-weaken-id {n} {e'} {do' e} = cong do' sub1-weaken-id
-- sub1-weaken-id {n} {e'} {hndl e e₁ e₂} = {!!}

liftsub-comp : ∀{n m k} {γ : Sub m k} {ρ : Ren n m} (x : < S n) → (liftsub γ) (lift ρ x) ≡ (liftsub (γ ∘ ρ)) x
liftsub-comp {n} {m} {k} {γ} {ρ} (z) = refl
liftsub-comp {n} {m} {k} {γ} {ρ} (s x) = refl

liftsub-comp-2 : ∀{n m k} {ρ : Ren m k} {γ : Sub n m} (x : < S n) → ren (lift ρ) (liftsub γ x) ≡ (liftsub (ren ρ ∘ γ)) x
liftsub-comp-2 z = refl
liftsub-comp-2 {γ = γ} (s x) = trans (sym (ren-comp (γ x))) (ren-comp (γ x))

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

-- liftsub-comp : ∀{n m k} {γ : Sub m k} {ρ : Ren n m} (x : < S n) → sub ≡ (liftsub (γ ∘ ρ)) x
-- liftsub-comp {n} {m} {k} {γ} {ρ} (z) = refl
-- liftsub-comp {n} {m} {k} {γ} {ρ} (s x) = refl



sub-ren : ∀{n m k} (γ : Sub m k) (ρ : Ren n m) (e : Exp n) → sub γ (ren ρ e) ≡ sub (γ ∘ ρ) e
sub-ren {n} {m} {k} γ (ρ) (′ x) = refl
sub-ren {n} {m} {k} γ ρ (Lit x) = refl
sub-ren {n} {m} {k} γ ρ (ƛ e) = cong ƛ (trans (sub-ren (liftsub γ) (lift ρ) e) (sub-cong liftsub-comp e))
sub-ren {n} {m} {k} γ ρ (e₁ · e₂) = cong₂ _·_ (sub-ren γ ρ e₁) (sub-ren γ ρ e₂)
sub-ren {n} {m} {k} γ ρ ([ e ]) = cong [_] (sub-ren γ ρ e)
sub-ren {n} {m} {k} γ ρ (do' e) = cong do' (sub-ren γ ρ e)
sub-ren {n} {m} {k} γ ρ (hndl e eₕ eᵣ) =
  cong₃ hndl (sub-ren γ ρ e)
             (trans (sub-ren (liftsub (liftsub γ)) (lift (lift ρ)) eₕ)
                    (trans (sub-cong liftsub-comp eₕ)
                           (sub-cong (liftsub-cong liftsub-comp) eₕ)))
             (trans (sub-ren (liftsub γ) (lift ρ) eᵣ) (sub-cong liftsub-comp eᵣ))

ren-sub : ∀{n m k} {ρ : Ren m k} {γ : Sub n m} (e : Exp n) → sub (ren ρ ∘ γ) e ≡ ren ρ (sub γ e)
ren-sub (′ x) = refl
ren-sub (Lit x) = refl
ren-sub (ƛ e) = cong ƛ (trans (sym (sub-cong liftsub-comp-2 e)) (ren-sub e))
ren-sub (e₁ · e₂) = cong₂ _·_ (ren-sub e₁) (ren-sub e₂)
ren-sub [ e ] = cong [_] (ren-sub e)
ren-sub (do' e) = cong do' (ren-sub e)
ren-sub (hndl e eₕ eᵣ) =
  cong₃ hndl (ren-sub e)
             (trans (sym (sub-cong (liftsub-cong liftsub-comp-2) eₕ))
                    (trans (sym (sub-cong liftsub-comp-2 eₕ)) (ren-sub eₕ)))
             (trans (sym (sub-cong liftsub-comp-2 eᵣ)) (ren-sub eᵣ))

liftsub-sub-comp : ∀{n m k} {γ₁ : Sub m k} {γ₂ : Sub n m} (x : < S n)
                 → sub (liftsub γ₁) (liftsub γ₂ x) ≡ (liftsub (sub γ₁ ∘ γ₂)) x
liftsub-sub-comp {γ₁ = γ₁} {γ₂ = γ₂} z = refl
liftsub-sub-comp {γ₁ = γ₁} {γ₂ = γ₂} (s x) =
  trans (sub-ren (liftsub γ₁) s (γ₂ x))
        (ren-sub (γ₂ x))

sub-comp : ∀{n m k} {γ₁ : Sub m k} {γ₂ : Sub n m} (e : Exp n)
         → sub γ₁ (sub γ₂ e) ≡ sub (sub γ₁ ∘ γ₂) e
sub-comp (′ x) = refl
sub-comp (Lit x) = refl
sub-comp (ƛ e) = cong ƛ (trans (sub-comp e) (sub-cong liftsub-sub-comp e))
sub-comp (e₁ · e₂) = cong₂ _·_ (sub-comp e₁) (sub-comp e₂)
sub-comp [ e ] = cong [_] (sub-comp e)
sub-comp (do' e) = cong do' (sub-comp e)
sub-comp (hndl e eₕ eᵣ) =
  cong₃ hndl
        (sub-comp e)
        (trans (sub-comp eₕ) (trans (sub-cong liftsub-sub-comp eₕ)
                                    (sub-cong (liftsub-cong liftsub-sub-comp) eₕ)))
        (trans (sub-comp eᵣ) (sub-cong liftsub-sub-comp eᵣ))

sub1-comp-var : ∀{n γ} {e' : Exp Z} (x : < (S n)) → sub1 e' (liftsub γ x) ≡ ext γ e' x
sub1-comp-var {n} {γ} {e'} (z) = refl
sub1-comp-var {n} {γ} {e'} (s x) =
  trans (trans (sub-ren (ext ′ e') s (γ x))
               (trans (sub-ext-id (λ x → refl) (γ x)) refl))
        (sym (sub-ren (ext γ e') s (′ x)))

sub1-comp : ∀{n γ} {e' : Exp Z} {e : Exp (S n)} → sub1 e' (sub (liftsub γ) e) ≡ sub (ext γ e') e
sub1-comp {n} {γ} {e'} {e} = trans (sub-comp e) (sub-cong sub1-comp-var e)


-- subcat : ∀{n₁ n₂ m} → Sub n₁ m → Sub n₂ m → Sub (n₁ + n₂) m
-- subcat {S n₁} γ₁ γ₂ z = γ₁ z
-- subcat {S n₁} γ₁ γ₂ (s x) = subcat (γ₁ ∘ s) γ₂ x
-- subcat {Z} {S n₂} γ₁ γ₂ x = γ₂ x

-- liftsub^ : ∀{n m} → (k : Nat) → Sub n m → Sub (k + n) (m + k) -- NOTE lol
-- liftsub^ {S n} k γ z = {!!}

-- sub-homo : ∀{n₁ n₂} {e : Exp (n₁ + n₂)} {γ : Sub n₁ Z} {γ' : Sub n₂ Z}
--          → sub γ (sub (liftsub^ n₁ γ') e) ≡ sub (subcat γ γ') e
-- sub-homo = {!!}
