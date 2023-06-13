{-# OPTIONS --without-K --safe #-}

open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary as BR
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Level

module Arrow where

infix 5 _→'_

record Arrow (D : Set) (C : Set) : Set where
  constructor _→'_
  field
    dom : D
    cod : C

private
  variable
    A B : Set
    _~_ : Rel A Level.zero

open Arrow public

-- RelLift lifts a reltion pointwisely, but contravariant on its domain

RelLift : Rel A Level.zero → Rel (Arrow A A) Level.zero
RelLift _~_ (a →' r) (a' →' r') = Arrow (a' ~ a) (r ~ r')

--
RelLiftCo : Rel A Level.zero → Rel (Arrow A A) Level.zero
RelLiftCo _~_ (a →' r) (a' →' r') = Arrow (a ~ a') (r ~ r')

-- A function type is balanced iff its domain and codmain are in a (given) relation
Balanced : Rel A Level.zero → Arrow A A → Set
Balanced _~_ (a →' r)  = a ~ r

RelLift-decidable : Decidable _~_ → Decidable (RelLift _~_)
RelLift-decidable _~?_ (a →' r) (a' →' r') with a' ~? a | r ~? r'
... | no ¬p | _ = no $ ¬p ∘ dom
... | _ | no ¬p = no $ ¬p ∘ cod
... | yes p | yes p' = yes (p →' p')

RelLiftCo-decidable : Decidable _~_ → Decidable (RelLiftCo _~_)
RelLiftCo-decidable _~?_ (a →' r) (a' →' r') with a ~? a' | r ~? r'
... | no ¬p | _ = no $ ¬p ∘ dom
... | _ | no ¬p = no $ ¬p ∘ cod
... | yes p | yes p' = yes (p →' p')

RelLift-irrelevant : BR.Irrelevant _~_ → BR.Irrelevant (RelLift _~_)
RelLift-irrelevant irr (dom₁ →' cod₁) (dom₂ →' cod₂) rewrite irr dom₁ dom₂ | irr cod₁ cod₂ = refl

RelLiftCo-irrelevant : BR.Irrelevant _~_ → BR.Irrelevant (RelLiftCo _~_)
RelLiftCo-irrelevant irr (dom₁ →' cod₁) (dom₂ →' cod₂) rewrite irr dom₁ dom₂ | irr cod₁ cod₂ = refl

RelLift-trans : Transitive _~_ → Transitive (RelLift _~_)
RelLift-trans trans (dom₁ →' cod₁) (dom₂ →' cod₂) = trans dom₂ dom₁ →' trans cod₁ cod₂

RelLift-≡⇒≡ : RelLift (_≡_ {A = A}) ⇒ _≡_
RelLift-≡⇒≡ (refl →' refl) = _≡_.refl

-- if _~_ is transitive , then balancedness on _~_ respects the lifted relation
--  RelLift f g → balanced f → balanced g
trans-balanced : Transitive _~_ → (Balanced _~_) Respects (RelLift _~_)
trans-balanced trans (a'~a →' r~r') balanced
  = trans a'~a $ trans balanced $ r~r'

→'-injective : ∀ {ft gt : Arrow A B} → ft ≡ gt → Arrow (dom ft ≡ dom gt) (cod ft ≡ cod gt)
→'-injective refl = refl →' refl

≡-dec : DecidableEquality A → DecidableEquality B → DecidableEquality (Arrow A B)
≡-dec decA decB (a →' b) (a' →' b') with decA a a' | decB b b'
... | yes refl | yes refl = yes refl
... | no na= | _ = no $ \ {refl → na= refl}
... | _ | no nb= = no $ \ {refl → nb= refl}

≡→'≡ : {X : Set} {Y : Set} {a b : Arrow X Y } → a ≡ b → Arrow (dom a ≡ dom b) (cod a ≡ cod b)
≡→'≡ refl = refl →' refl

→'≡→' : {X : Set} {Y : Set} {a b : Arrow X Y } → Arrow (dom a ≡ dom b) (cod a ≡ cod b) → a ≡ b
→'≡→' (refl →' refl) = refl
