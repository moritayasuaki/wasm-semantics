{-# OPTIONS --without-K --safe #-}
module ListOps where

open import Data.Nat
open import Data.List
open import Arrow
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Function
open import Algebra.Definitions
open import Data.List.Properties
open import Arrow

private variable
  X Y Z W : Set

-- take prefix of length of list from list
-- tl ≡ take ∘ length
tl : List X → List X → List X
tl [] ys = []
tl (x ∷ xs) [] = []
tl (x ∷ xs) (y ∷ ys) = y ∷ tl xs ys

tl≗take-length : ∀ (l : List X) (l' : List X) → tl l l' ≡ (take ∘ length) l l'
tl≗take-length [] x = refl
tl≗take-length (x ∷ l) [] = refl
tl≗take-length (x ∷ l) (x₁ ∷ l') = cong (\ l → x₁ ∷ l) (tl≗take-length  l l')

-- drop suffix of length of list from list
-- dl ≡ drop ∘ length
dl : List X → List X → List X
dl [] ys = ys
dl (x ∷ xs) [] = []
dl (x ∷ xs) (y ∷ ys) = dl xs ys

dl≗drop-length : ∀ (l : List X) (l' : List X) → dl l l' ≡ (drop ∘ length) l l'
dl≗drop-length [] x = refl
dl≗drop-length (x ∷ l) [] = refl
dl≗drop-length (x ∷ l) (x₁ ∷ l') = dl≗drop-length l l'

ListArrow : Set → Set
ListArrow X = Arrow (List X) (List X)

→'pw1 : ∀{X} → (P : X → Set) → (prop : (x : X) → P x) → (x : Arrow X X) → Arrow (P (dom x)) (P (cod x))
→'pw1 P prop x = prop (dom x) →' prop (cod x)

→'pw2 : ∀{X} → (P : X → X → Set) → (prop : (x y : X) → P x y) → (x y : Arrow X X) → Arrow (P (dom x) (dom y)) (P (cod x) (cod y))
→'pw2 P prop x y = prop (dom x) (dom y) →' prop (cod x) (cod y)

→'pw1-nondep : ∀{X Y} → (X → Y) → Arrow X X → Arrow Y Y
→'pw1-nondep {Y = Y} = →'pw1 (const Y)

→'pw2-nondep : ∀{X Y} → (X → X → Y) → Arrow X X → Arrow X X → Arrow Y Y
→'pw2-nondep {Y = Y} = →'pw2 ((const ∘ const) Y)

tl² : ListArrow X → ListArrow X → ListArrow X
tl² {X = X} = →'pw2 (\ _ _ → List X) tl
dl² : ListArrow X → ListArrow X → ListArrow X
dl² = →'pw2-nondep dl
_++²_ : ListArrow X → ListArrow X → ListArrow X
_++²_ = →'pw2-nondep _++_

_++¹_ : Arrow (List X) (List X) → List X → Arrow (List X) (List X)
(dom₁ →' cod₁) ++¹ xs = (dom₁ ++ xs) →' (cod₁ ++ xs)

-- height ordering
_≡len_ : List X  → List X → Set
rt ≡len rt' = length rt ≡ length rt'

_≤len_ : List X → List Y → Set
rt ≤len rt' = length rt ≤ length rt'

_≤len?_ : Decidable (_≤len_ {X} {Y})
x ≤len? y = length x ≤? length y

_≤len²_ : Arrow (List X) (List Y) → Arrow (List Z) (List W) → Set
ft ≤len² f' = Arrow (dom ft ≤len dom f') (cod ft ≤len cod f')

tl-[] : (xs : List X) → tl [] xs ≡ []
tl-[] [] = refl
tl-[] (x ∷ xs) = refl

tl-id : (xs : List X) → tl xs xs ≡ xs
tl-id [] = refl
tl-id (x ∷ xs) rewrite tl-id xs = refl

dl-[] : (xs : List X) → dl xs [] ≡ []
dl-[] [] = refl
dl-[] (x ∷ xs) = refl

dl-id : (xs : List X) → dl xs xs ≡ []
dl-id [] = refl
dl-id (x ∷ xs) rewrite dl-id xs = refl

tl++dl : (xs ys : List X) → tl xs ys ++ dl xs ys ≡ ys
tl++dl [] ys = refl
tl++dl (x ∷ xs) [] = refl
tl++dl (x ∷ xs) (y ∷ ys) = cong (y ∷_) $ tl++dl xs ys

tl++ : (xs ys : List X) → tl xs (xs ++ ys) ≡ xs
tl++ [] ys = refl
tl++ (x ∷ xs) ys rewrite tl++ xs ys = refl

dl++ : (xs ys : List X) → dl xs (xs ++ ys) ≡ ys
dl++ [] ys = refl
dl++ (x ∷ xs) ys rewrite dl++ xs ys = refl

++≡⇒dl≡ : {xs ys zs : List X} → xs ++ ys ≡ zs → dl xs zs ≡ ys
++≡⇒dl≡ {X} {xs} {ys} {zs} refl = dl++ xs ys

tl⇒++dl : (rt rt' : List X) → rt ≡ tl rt rt' → rt ++ dl rt rt' ≡ rt'
tl⇒++dl rt rt' p =  cong (\ rt'' → rt'' ++ dl rt rt') p ⟨ trans ⟩ tl++dl rt rt'

tl²-id : (xs : ListArrow X) → tl² xs xs ≡ xs
tl²-id (dom₁ →' cod₁) rewrite tl-id dom₁ | tl-id cod₁ = refl

dl²-id : (xs : ListArrow X) → dl² xs xs ≡ ([] →' [])
dl²-id (dom₁ →' cod₁) rewrite dl-id dom₁ | dl-id cod₁ = refl

tl++dl² : (xs ys : ListArrow X) → tl² xs ys ++² dl² xs ys ≡ ys
tl++dl² (dom₁ →' cod₁) (dom₂ →' cod₂) rewrite tl++dl dom₁ dom₂ | tl++dl cod₁ cod₂ = refl

tl++² : (xs ys : ListArrow X) → tl² xs (xs ++² ys) ≡ xs
tl++² (dom₁ →' cod₁) (dom₂ →' cod₂) rewrite tl++ dom₁ dom₂ | tl++ cod₁ cod₂ = refl

dl++² : (xs ys : ListArrow X) → dl² xs (xs ++² ys) ≡ ys
dl++² (dom₁ →' cod₁) (dom₂ →' cod₂) rewrite dl++ dom₁ dom₂ | dl++ cod₁ cod₂ = refl

tl⇒++dl² : (rt rt' : ListArrow X) → rt ≡ tl² rt rt' → rt ++² dl² rt rt' ≡ rt'
tl⇒++dl² (a →' r) (a' →' r') p =
  let ap →' rp = →'-injective p
  in cong₂ _→'_ (tl⇒++dl a a' ap) (tl⇒++dl r r' rp)

-- univariate stack polymorphism
++²-identity : RightIdentity _≡_ ([] →' []) (_++²_ {X})
++²-identity (dom₁ →' cod₁) rewrite ++-identityʳ dom₁ | ++-identityʳ cod₁ = refl

++²-assoc : Associative _≡_ (_++²_ {X})
++²-assoc (dom₁ →' cod₁) (dom₂ →' cod₂) (dom₃ →' cod₃) rewrite ++-assoc dom₁ dom₂ dom₃ | ++-assoc cod₁ cod₂ cod₃ = refl

++²-cancelˡ : ∀ (xs : ListArrow X) {ys zs} → xs ++² ys ≡ xs ++² zs → ys ≡ zs
++²-cancelˡ xs {ys} {zs} x
  with pdom →' pcod ← →'-injective x
  with refl ← ++-cancelˡ (dom xs) pdom
  with refl ← ++-cancelˡ (cod xs) pcod
  = refl

++²-cancelʳ : ∀ {xs : ListArrow X} ys zs → ys ++² xs ≡ zs ++² xs → ys ≡ zs
++²-cancelʳ {xs = dom₃ →' cod₃} (dom₁ →' cod₁) (dom₂ →' cod₂) x with →'-injective x
... | dom≡ →' cod≡  with ++-cancelʳ cod₁ cod₂ cod≡ | ++-cancelʳ dom₁ dom₂ dom≡
... | refl | refl = refl

_∷₂_ : Arrow X X → ListArrow X → ListArrow X
(x →' y) ∷₂ (xs →' ys) = (x ∷ xs) →' (y ∷ ys)

append-assoc : ∀ {xs xs' xs'' dxs dxs' : List X} → xs ++ dxs ≡ xs' → xs' ++ dxs' ≡ xs'' → xs ++ dxs ++ dxs' ≡ xs''
append-assoc {xs = xs} {dxs = dxs} {dxs'} refl refl = sym (++-assoc xs dxs dxs')

open import Data.Product
≡∷≡ : {X : Set} {vt vt' : X} {rt rt' : List X} → vt ∷ rt ≡ vt' ∷ rt' → (vt ≡ vt') × (rt ≡ rt')
≡∷≡ = Data.List.Properties.∷-injective

∷≡∷ : {X : Set} {vt vt' : X} {rt rt' : List X} → vt ≡ vt' → rt ≡ rt' → _≡_ {A = List X} (vt ∷ rt) (vt' ∷ rt')
∷≡∷ refl refl = refl
