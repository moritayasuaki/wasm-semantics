{-# OPTIONS --without-K --safe #-}

module Syntax where


import Level

open import Data.Nat as N using (ℕ ; suc ; zero)
open import Data.Bool as B using (Bool ; true ; false)
open import Data.List as L using (List ; [] ; _∷_)
open import BlockList as BL using (BList ; atm ; blk ; [] ; _∷_ ; Kind ; Item ; Seq)
open import Arrow as AR using (Arrow ; _→'_ ; dom ; cod)

open import Function
open import Relation.Binary as BR
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Vec
open import Data.Sum
open import ListOps

LT = ℕ -- type of label-type

data VT : Set where -- type of value type
  i32 i64 : VT

Lit = ℕ -- type of number literals


RT : Set -- type of cod types
RT = List VT

open Arrow public
FT = Arrow RT RT  -- type of function types

module _ where
  private
    variable
      k : Kind

  data Atm : Set where
    cons : (t : VT) → (n : Lit)→ Atm
    add : (t : VT) → Atm
    -- pop : Atm
    store load : (t : VT) → Atm
    br brif : (ℓ : LT) → Atm

  data Blk : Set where
    block loop : Blk

infix 1 _:'_
record Annotated (X : Set) (T : Set) : Set where
  constructor _:'_
  field
    b : X
    ft : T

Code = BList Atm (Annotated Blk FT)
Inst = Code Item
InstSeq = Code Seq

Ctx = List RT

open import Relation.Nullary
open import Data.List.Relation.Binary.Pointwise as LP using ([] ; _∷_ )
open import Relation.Binary.Definitions

module Examples where
  ex1 ex3 ex4 ex5 ex6 : InstSeq
  ex1 = atm (cons i32 1) ∷ atm (cons i32 5) ∷ atm (add i32) ∷ []
  ex3 = atm (cons i32 1) ∷ atm (add i32) ∷ []
  ex4 = atm (br 0) ∷ []
  ex5 = blk (block :' [] →' []) (atm (br 0) ∷ []) ∷ []
  ex6 = blk (block :' [] →' []) (atm (br 0) ∷ atm (cons i32 1) ∷ []) ∷ []

open import Axiom.UniquenessOfIdentityProofs

import Data.List.Relation.Binary.Pointwise as LP
open LP using ([] ; _∷_)

_≟VT_ : DecidableEquality VT
i32 ≟VT i32 = yes ≡.refl
i32 ≟VT i64 = no \()
i64 ≟VT i32 = no \()
i64 ≟VT i64 = yes ≡.refl

uipVT : UIP VT
uipVT = Decidable⇒UIP.≡-irrelevant _≟VT_

_≟RT_ : DecidableEquality RT
_≟RT_ = ≡-dec _≟VT_
  where open import Data.List.Properties

uipRT : UIP RT
uipRT = Decidable⇒UIP.≡-irrelevant _≟RT_

_≟FT_ : DecidableEquality FT
_≟FT_ = AR.≡-dec _≟RT_ _≟RT_

uipFT : UIP FT
uipFT = Decidable⇒UIP.≡-irrelevant _≟FT_
