{-# OPTIONS --without-K --safe #-}
open import OperationalSemantics
open import Data.Product
open import Data.Nat
open import Syntax
open import TypeSystem
open import Data.Unit
open import BlockList hiding (_++_ ; ++-assoc)
open Memory
open Store
open import Arrow
open import ListOps
open import Data.List
open import Data.Bool
open import Function
open import Relation.Nullary.Decidable
open import Subtype
open import TypeCast
open import TypeCast0

open import Partial

module DenotationalSemantics0 where

private variable
  k : Kind

evalAddT : ∀{t} → mapVT t → mapVT t → mapVT t
evalAddT {i32} (x , _) (y , _) = toI32 (x + y)
evalAddT {i64} (x , _) (y , _) = toI64 (x + y)

evalStoreT : (vt : VT) → I32 → mapVT vt → Store → ⊤ × Store
evalStoreT i32 loc (n , _) S = tt , (record S {mem = mstore (mem S) loc n})
evalStoreT i64 loc (n , _) S = tt , (record S {mem = mstore (mem S) loc n})

evalLoadT : (vt : VT) → I32 → Store → mapVT vt × Store
evalLoadT i32 loc S = toI32 (mload (mem S) loc) , S
evalLoadT i64 loc S = toI64 (mload (mem S) loc) , S

open import Relation.Binary.PropositionalEquality
open import Data.List.Properties

open import Data.Empty

open Sub

semExit0 : ∀{C lt ct q} → semQFT0 (semCtx C) ((lt →' ct) , uni) → Partial (semQRT (semCtx (lt ∷ C)) (ct , q)) → Partial (semQRT (semCtx C) (ct , uni))
semExit0 f div = div
semExit0 f (con (tbranch (tjump {ℓ = zero} ℓ< vs) , S)) = f (vs , S)
semExit0 f (con (tbranch (tjump {ℓ = suc ℓ} (s≤s ℓ<) vs) , S)) = con (tbranch (tjump ℓ< vs) , S)
semExit0 f (con (right (qv , vs) , S)) = con (tnormal vs , S)


semCode0 : ∀ {c : Code k} {qft} C → (C ⊢ c :' qft) → ℕ → semQFT0 (semCtx C) qft
semCodeBase0 : ∀ {c : Code k} {qft} C → (C ⊢[base] c :' qft) → ℕ → semQFT0 (semCtx C) qft

semCode0 C (sub qft≤qft' tc) n = castQFT0 (semCtx C) _ _ qft≤qft' (semCode0 C tc n)
semCode0 C (base tc) n = semCodeBase0 C tc n

semCodeBase0 {c = atm (cons i32 v)} C (atm (cons i32)) n ([] , S) = con (tnormal (toI32 v ∷ []) , S)
semCodeBase0 {c = atm (cons i64 v)} C (atm (cons i64)) n ([] , S) = con (tnormal (toI64 v ∷ []) , S)
semCodeBase0 C (atm (add t)) n ((v2 ∷ v1 ∷ []) , S) = con (tnormal (evalAddT v1 v2 ∷ []) , S)
semCodeBase0 C (atm (store t)) n ((v2 ∷ v1 ∷ []) , S) = let (_ , S') = evalStoreT t v2 v1 S in con (tnormal [] , S')
semCodeBase0 C (atm (load t)) n (v ∷ [] , S) = let (v' , S') = evalLoadT t v S in con (tnormal (v' ∷ []) , S')  
semCodeBase0 C (atm (brif-refl ℓ<)) n ((x ∷ vs) , S) = if isYes (proj₁ x Data.Nat.≟ 0)
  then (con (tnormal vs , S))
  else (con (tbranch (tjump ℓ< vs) , S))
semCodeBase0 C (br-refl ℓ<) n (vs , S) = con (tbranch (tjump ℓ< vs) , S)
semCodeBase0 C (blk ft (block x)) n (vs , S) = semExit0 (\ p @ (vs' , S') → con (tnormal vs' , S')) (semCode0 (cod ft ∷ C) x n (vs , S))
semCodeBase0 C (blk ft (loop x)) n (vs , S) = semExit0 (\ st → case n of \{ zero → div ; (suc m) → semCodeBase0 C (blk ft (loop x)) m st}) (semCode0 (dom ft ∷ C) x n (vs , S))
semCodeBase0 C [] n (vs , S) = con (tnormal vs , S)
semCodeBase0 C (ti ∷ tis) n = semCode0 C ti n >=>0 semCode0 C tis n

∷-sub-commute0 : ∀ C i is a0 m0 r0 qi0 qis0 a m r qi qis (ti : C ⊢ i :' (a0 →' m0 , qi0)) (tis : C ⊢ is :' (m0 →' r0 , qis0))
  (≤a→m : (a0 →' m0 , qi0) ≤QFT (a →' m , qi)) (≤m→r : (m0 →' r0 , qis0) ≤QFT (m →' r , qis)) (≤a→r : (a0 →' r0 , qi0 ⊓QT qis0) ≤QFT (a →' r , qi ⊓QT qis))
  → ∀ n → semCode0 C (sub ≤a→r (base (ti ∷ tis))) n ≗ semCode0 C (base (sub ≤a→m ti ∷ sub ≤m→r tis)) n
∷-sub-commute0 C i is a0 m0 r0 qi0 qis0 a m r qi qis ti tis ≤a→m ≤m→r ≤a→r n x
  = ( castQFT0-cong _ ≤a→r F ⟨ ≗-trans ⟩ ≗-sym (>=>0-castQFT0-commute _ _ _ _ _ _ _ _ _ _ _ ≤a→m ≤m→r ≤a→r (semCode0 C ti n) (semCode0 C tis n))) x
  where F : semCode0 C (base (ti ∷ tis)) n ≗ (semCode0 C ti n >=>0 semCode0 C tis n)
        F _ = refl

⟦_⟧0 : ∀ {c : Code k} {ft q C} → (C ⊢ c :' (ft , q)) → ℕ → semQRT (semCtx C) (dom ft , uni) → Partial (semQRT (semCtx C) (cod ft , q))
⟦_⟧0 {C = C} tc n (right (_ , vs) , S) = semCode0 C tc n (vs , S)
⟦_⟧0 {C = C} tc n (tbranch b , S)  = con (tbranch b , S)
