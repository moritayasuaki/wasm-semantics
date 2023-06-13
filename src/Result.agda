{-# OPTIONS --without-K --safe #-}

open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties
open import Axiom.UniquenessOfIdentityProofs
open import Relation.Nullary
open import Data.Nat

module Result where

data Error : Set where
  no-branch-target annotation-mismatch stack-underflow value-type-error value-type-mismatch branch-outside : Error

eid : Error → ℕ
eid no-branch-target = 0
eid annotation-mismatch = 1
eid stack-underflow = 2
eid value-type-error = 3
eid value-type-mismatch = 4
eid branch-outside = 5

eid-injective : Injective _≡_ _≡_ eid
eid-injective {no-branch-target} {no-branch-target} eq = refl
eid-injective {annotation-mismatch} {annotation-mismatch} eq = refl
eid-injective {stack-underflow} {stack-underflow} eq = refl
eid-injective {value-type-error} {value-type-error} eq = refl
eid-injective {value-type-mismatch} {value-type-mismatch} eq = refl
eid-injective {branch-outside} {branch-outside} eq = refl

deceq-via-injection-to-nat : {X : Set} {f : X → ℕ} → Injective _≡_ _≡_ f  → DecidableEquality X
deceq-via-injection-to-nat {X} {f} f-inj x y with f x ≟ f y
... | yes p = yes (f-inj p)
... | no np = no (np ∘ cong f)

_≟Error_ : DecidableEquality Error
_≟Error_ = deceq-via-injection-to-nat eid-injective

uipError : UIP Error
uipError = Decidable⇒UIP.≡-irrelevant _≟Error_

data Result (X : Set) : Set where
  err : Error → Result X
  ok : X → Result X

deceqResult : ∀ {X} → DecidableEquality X → DecidableEquality (Result X)
deceqResult _≟_ (err e) (err e') with e ≟Error e'
... | yes p = yes (cong err p)
... | no np = no \ { refl → np refl }
deceqResult _≟_ (err _) (ok _) = no \()
deceqResult _≟_ (ok _) (err _) = no \()
deceqResult _≟_ (ok x) (ok x') with x ≟ x'
... | yes p = yes (cong ok p)
... | no np = no \ {refl → np refl}

uipResult : ∀ {X} → DecidableEquality X → UIP (Result X)
uipResult decEqX = Decidable⇒UIP.≡-irrelevant (deceqResult decEqX)

elimResult : {X : Set} (C : Result X → Set) → ((e : Error) → C (err e)) → ((x : X) → C (ok x)) → (r : Result X) → C r
elimResult C cerr cok (err e) = cerr e
elimResult C cerr cok (ok x) = cok x

recResult : {X C : Set} → (Error → C) → (X → C) → Result X → C
recResult = elimResult (const _)

okThen : {X C : Set} → (X → (Result C)) → Result X → Result C
okThen = recResult err

ok-injective : {X : Set} {x y : X} → ok x ≡ ok y → x ≡ y
ok-injective refl = refl
