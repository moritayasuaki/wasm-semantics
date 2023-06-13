{-# OPTIONS --without-K --safe #-}
module BlockList where

open import Data.Nat
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Relation.Nullary

-- Definitions
data Kind : Set where
  Item Seq : Kind

data BList (X B : Set) : (k : Kind) → Set where
  [] :  BList X B Seq
  _∷_ : (x : BList X B Item) → (xs : BList X B Seq) → BList X B Seq
  atm : (x : X) → BList X B Item -- atomic
  blk : (b : B) → (xs : BList X B Seq) → BList X B Item

ΣBList : Set → Set → Set
ΣBList X B = Σ _ (BList X B)




module _ where
  private variable
    X : Set
    B : Set
    k : Kind

  _++_ : BList X B Seq → BList X B Seq → BList X B Seq
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  _∷ʳ_ : BList X B Seq → BList X B Item → BList X B Seq
  xs ∷ʳ x = xs ++ (x ∷ [])

  data _≺_ {X B : Set} : ΣBList X B → ΣBList X B → Set where
    head≺ : ∀ {x xs} → (Item , x) ≺ (Seq , x ∷ xs)
    tail≺ : ∀ {x xs} → (Seq , xs) ≺ (Seq , x ∷ xs)
    init≺ : ∀ {xsx x xs} → xsx ≡ xs ∷ʳ x → (Seq , xs) ≺ (Seq , xsx)
    last≺ : ∀ {xsx x xs} → xsx ≡ xs ∷ʳ x → (Item , x) ≺ (Seq , xsx)
    blk≺ : ∀ {b xs} → (Seq , xs) ≺ (Item , blk b xs)

  []≢∷ʳ : (x : BList X B Item) (xs : BList X B Seq) → [] ≢ xs ∷ʳ x
  []≢∷ʳ x [] ()
  []≢∷ʳ x (_ ∷ _) ()

  ⊀[] : (b : ΣBList X B) → ¬ (b ≺ (Seq , []))
  ⊀[] .(Seq , _) (init≺ eq) = []≢∷ʳ _ _ eq
  ⊀[] .(Item , _) (last≺ eq) = []≢∷ʳ _ _ eq

  ⊀atm : ∀ x → (b : ΣBList X B) → ¬ (b ≺ (Item , atm x))
  ⊀atm x b ()



  snoc' : BList X B Item → BList X B Seq → BList X B Seq × BList X B Item
  snoc' x [] = [] , x
  snoc' x (x' ∷ xs) = case snoc' x' xs of \ where
    (ys , y) → (x ∷ ys , y)

  snoc : BList X B Item × BList X B Seq → BList X B Seq × BList X B Item
  snoc = uncurry snoc'

  unsnoc : BList X B Seq × BList X B Item → BList X B Item × BList X B Seq
  unsnoc ([] , x) = x , []
  unsnoc (x' ∷ xs , x) = x' , xs ∷ʳ x

  size : BList X B k → ℕ
  size (atm x) = 1
  size (blk b x) = 1 + size x
  size [] = 0
  size (x ∷ xs) = size x + size xs

-- Properties
open import Data.Nat.Properties

module _ where
  private variable
    X : Set
    B : Set
    k : Kind
    x x' y y' : BList X B Item
    xs xs' ys ys' : BList X B Seq

  ++-assoc : ∀ (xs xs' xs'' : BList X B Seq) → (xs ++ xs') ++ xs'' ≡ xs ++ (xs' ++ xs'')
  ++-assoc [] xs' xs'' = refl
  ++-assoc (x ∷ xs) xs' xs'' = cong (_∷_ x) $ ++-assoc xs xs' xs''

  ∷-∷ʳ-assoc : ∀ (x : BList X B Item) xs x' → (x ∷ xs) ∷ʳ x' ≡ x ∷ (xs ∷ʳ x')
  ∷-∷ʳ-assoc x xs x' = ++-assoc (x ∷ []) xs (x' ∷ [])

  snoc≡' : (x : BList X B Item) → (xs : BList X B Seq) →
    let ys , y = snoc (x , xs)
    in ys ∷ʳ y ≡ x ∷ xs
  snoc≡' x [] = refl
  snoc≡' x (x' ∷ xs) = cong (x ∷_) (snoc≡' x' xs)

  snoc≡ : (xxs : BList X B Item × BList X B Seq) →
    let x , xs = xxs
        ys , y = snoc xxs
    in ys ∷ʳ y ≡ x ∷ xs
  snoc≡ = uncurry snoc≡'

  unsnoc≡ : (xsx : BList X B Seq × BList X B Item) →
    let xs , x = xsx
        y , ys = unsnoc xsx
    in y ∷ ys ≡ xs ∷ʳ x
  unsnoc≡ ([] , x) = refl
  unsnoc≡ (x' ∷ xs , x) = ∷-∷ʳ-assoc x' xs x

  ∷-injective : x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
  ∷-injective refl = refl , refl

  ∷ʳ-injective : (xs ys : BList X B Seq) → (xs ∷ʳ x) ≡ ys ∷ʳ y → xs ≡ ys × x ≡ y
  ∷ʳ-injective [] [] refl = refl , refl
  ∷ʳ-injective (x' ∷ xs) (y' ∷ ys) eq with ∷-injective eq
  ... | refl , eq' = map (cong (_∷_ y')) id (∷ʳ-injective xs ys eq')
  ∷ʳ-injective (_ ∷ (_ ∷ _)) [] ()
  ∷ʳ-injective [] (_ ∷ (_ ∷ _)) ()

  inv : ∀ (xxs : BList X B Item × BList X B Seq) → (unsnoc ∘ snoc) xxs ≡ xxs
  inv (x , xs) with snoc (x , xs) | snoc≡ (x , xs)
  ... | ys , y | P with unsnoc (ys , y) | unsnoc≡ (ys , y)
  ... | x' , xs' | Q with trans Q P
  ... | refl = refl

  inv' : ∀ (xsx : BList X B Seq × BList X B Item) → (snoc ∘ unsnoc) xsx ≡ xsx
  inv' (xs , x) with unsnoc (xs , x) | unsnoc≡ (xs , x)
  ... | y , ys | P with snoc (y , ys) | snoc≡ (y , ys)
  ... | xs' , x' | Q with ∷ʳ-injective xs' xs (trans Q P)
  ... | refl , refl = refl

  |x|>0 : (x : BList X B Item) → size x > 0
  |x|>0 (atm x) = s≤s z≤n
  |x|>0 (blk b x) = s≤s z≤n

  |xs|<|x∷xs| : (x : BList X B Item) → (xs : BList X B Seq) → size xs < size (x ∷ xs)
  |xs|<|x∷xs| x xs = +-monoˡ-≤ (size xs) (|x|>0 x)  -- +-monoʳ-≤ (≤-reflexive (erefl (size xs))) (|x|>0 x)

  |xs∷ʳx|≡|xs|+|x| : (xs : BList X B Seq) → (x : BList X B Item) → size (xs ∷ʳ x) ≡ size xs + size x
  |xs∷ʳx|≡|xs|+|x| [] x = +-identityʳ (size x)
  |xs∷ʳx|≡|xs|+|x| (x' ∷ xs) x = trans (cong (_+_ (size x')) (|xs∷ʳx|≡|xs|+|x| xs x)) (sym (+-assoc (size x') (size xs) (size x)))

  |xs|<|xs∷ʳx| : (xs : BList X B Seq) → (x : BList X B Item) → size xs < size (xs ∷ʳ x)
  |xs|<|xs∷ʳx| xs x rewrite |xs∷ʳx|≡|xs|+|x| xs x | sym $ +-comm (size x) (size xs) = +-monoˡ-≤ (size xs) (|x|>0 x)

  |xs|≤|x∷xs| : (x : BList X B Item) → (xs : BList X B Seq) → size x ≤ size (x ∷ xs)
  |xs|≤|x∷xs| x xs = m≤m+n (size x) (size xs)

  |x|≤|xs∷ʳx| : (xs : BList X B Seq) → (x : BList X B Item) → size x ≤ size (xs ∷ʳ x)
  |x|≤|xs∷ʳx| xs x rewrite |xs∷ʳx|≡|xs|+|x| xs x = m≤n+m (size x) (size xs)

length : {X B : Set} → BList X B Seq → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)
