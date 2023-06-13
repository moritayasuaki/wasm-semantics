{-# OPTIONS --without-K --safe #-}
module Partial where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Data.Product
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤ ; tt)
open import Data.Sum

data Partial (X : Set) : Set where
  div : Partial X -- diverge
  con : X → Partial X -- converge

elimPartial : {X : Set} (C : Partial X → Set) → C div → ((x : X) → C (con x)) → (p : Partial X) → C p
elimPartial C cdiv ccon div = cdiv
elimPartial C cdiv ccon (con x) = ccon x

recPartial : {X C : Set} → C → (X → C) → Partial X → C
recPartial = elimPartial _

_<P_ : {X : Set} → Partial X → Partial X → Set
div <P (con x) = ⊤
_ <P _ = ⊥

_≤P_ : {X : Set} → Partial X → Partial X → Set
x ≤P y = (x ≡ y) ⊎ (x <P y)

private variable
  X : Set

Monotone : (ℕ → Partial X) → Set
Monotone f = ∀ n m → n ≤ m → f n ≤P f m

Diverge : (ℕ → Partial X) → Set
Diverge f = ∀ n → f n ≡ div

ConvergeAt : (ℕ → Partial X) → ℕ → X → Set
ConvergeAt f n x = f n ≡ con x

Converge : (ℕ → Partial X) → X → Set
Converge f x = Σ _ \n → ConvergeAt f n x

[Con⇒Con]⇒[Div⇐Div] : {X : Set} → (f g : ℕ → Partial X) → (∀ x → Converge g x → Converge f x) → Diverge f → Diverge g
[Con⇒Con]⇒[Div⇐Div] f g gcon-fcon fdiv n with g n in gcon-n
... | div = refl
... | con x with m , fcon-m ← gcon-fcon x (n , gcon-n) = trans (sym fcon-m) (fdiv m)

con-suc : (ℕ → Partial X) → Set
con-suc f = ∀ x m → f m ≡ con x → f (suc m) ≡ con x

con-≤ : (ℕ → Partial X) → Set
con-≤ f = ∀ x m n → m ≤ n → f m ≡ con x → f n ≡ con x

con-n+ : (ℕ → Partial X) → Set
con-n+ f = ∀ x m n → f m ≡ con x → f (n + m) ≡ con x

con-n⊔ : (ℕ → Partial X) → Set
con-n⊔ f = ∀ x m n → f m ≡ con x → f (n ⊔ m) ≡ con x

con-+n : (ℕ → Partial X) → Set
con-+n f = ∀ x m n → f m ≡ con x → f (m + n) ≡ con x

con-⊔n : (ℕ → Partial X) → Set
con-⊔n f = ∀ x m n → f m ≡ con x → f (m ⊔ n) ≡ con x

con-suc⇒≤ : (f : ℕ → Partial X) → con-suc f → con-≤ f
con-suc⇒≤ f con-suc-f x zero zero n≤m fn-con = fn-con
con-suc⇒≤ f con-suc-f x zero (suc m) n≤m fn-con = con-suc-f x m (con-suc⇒≤ f con-suc-f x zero m z≤n fn-con)
con-suc⇒≤ f con-suc-f x (suc n) (suc m) (s≤s n≤m) fn-con with suc n ≤? m
... | yes n<m
  = con-suc-f x m (con-suc⇒≤ f con-suc-f x (suc n) m n<m fn-con)
... | no n≮m
  with refl ← ≤∧≮⇒≡ n≤m n≮m
  = fn-con

con-≤⇒n+ : (f : ℕ → Partial X) → con-≤ f → con-n+ f
con-≤⇒n+ f con-≤-f x m n = con-≤-f x m (n + m) (m≤n+m m n)

con-≤⇒n⊔ : (f : ℕ → Partial X) → con-≤ f → con-n⊔ f
con-≤⇒n⊔ f con-≤-f x m n = con-≤-f x m (n ⊔ m) (m≤n⊔m n m)

con-n+⇒con-+n : (f : ℕ → Partial X) → con-n+ f → con-+n f
con-n+⇒con-+n f p x m n = subst (\ eq → f m ≡ con x → f eq ≡ con x)  (+-comm n m) (p x m n)

con-n⊔⇒con-⊔n : (f : ℕ → Partial X) → con-n⊔ f → con-⊔n f
con-n⊔⇒con-⊔n f p x m n = subst (\ eq → f m ≡ con x → f eq ≡ con x)  (⊔-comm n m) (p x m n)

open import Function
con-≤⇒monotone : (f : ℕ → Partial X) → con-≤ f → Monotone f
con-≤⇒monotone f con-≤-f m n m≤n with f m in fm≡ | f n in fn≡
... | div | div = inj₁ refl
... | div | con x = inj₂ tt
... | con x | p
  rewrite con-≤-f x m n m≤n fm≡
  = inj₁ fn≡

module ConvergeProps {X : Set} {f : ℕ → Partial X} (con-suc-f : con-suc f) where
  con-≤-f = con-suc⇒≤ f con-suc-f
  con-n+-f = con-≤⇒n+ f con-≤-f
  con-+n-f = con-n+⇒con-+n f con-n+-f
  con-n⊔-f = con-≤⇒n⊔ f con-≤-f
  con-⊔n-f = con-n⊔⇒con-⊔n f con-n⊔-f
  con-monotone = con-≤⇒monotone f con-≤-f
