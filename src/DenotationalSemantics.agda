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
open import Relation.Binary.PropositionalEquality

open import Partial

module DenotationalSemantics where

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

open import Data.List.Properties

open import Data.Empty

open Sub

castRT-[] : ∀ {a} D → semRT ((a ++ []) ++ D) → semRT (a ++ D)
castRT-[] {a} D vs = castRT _ _ (++-assoc a [] D) vs

semExit : ∀ {X lt codft q C} {D : RT}
    → semRT D
    → Partial (semQRT (semCtx (lt ∷ C)) (codft ++ [] , q))
    → semQFT X (semCtx C) (lt →' codft , uni) D
    → Partial (semQRT (semCtx C) (codft ++ D , uni))
semExit res-vs div f = div
semExit res-vs (con (tbranch (tjump {ℓ = suc ℓ} (s≤s ℓ<) vs) , S)) f = con (tbranch (tjump {ℓ = ℓ} ℓ< vs) , S)
semExit {D = D} res-vs (con (right (qv , vs) , S)) f = con (tnormal ((castRT-[] D) (vs safe++ res-vs)) , S)
semExit {D = D} res-vs (con (tbranch (tjump {ℓ = zero} ℓ< vs) , S)) f = f (tnormal (vs safe++ res-vs) , S)

semCode : ∀ {c : Code k} {qft} C → (C ⊢ c :' qft) → ℕ → ∀ D → semQFT (semCtx C) (semCtx C) qft D
semCodeBase : ∀ {c : Code k} {qft} C → (C ⊢[base] c :' qft) → ℕ → ∀ D → semQFT (semCtx C) (semCtx C) qft D

-- semCodeCore C (sub qft≤qft' tc) n D (tbranch b , S) = con (tbranch b , S)
-- semCodeCore C (sub qft≤qft' tc) n = castQFT (semCtx C) (semCtx C) _ _ qft≤qft' (semCodeCore C tc n)
-- semCodeCore C (base tc) n D = (semCodeBase C tc n) D

-- semCodeBase C _ n D (tbranch b , S) = con (tbranch b , S)
semCodeBase C ([]) n D (tnormal vs  , S) = con (tnormal vs , S)
semCodeBase C ((ti ∷ tis)) n D (tnormal vs , S)
  = ((semCode C ti n) >=> (semCode C tis n)) D (tnormal vs , S)
-- = bind {D = D} (semCode C ti n D (tnormal vs , S)) (semCode C tis n D) -- (semCodeBase C tis n D)

semCodeBase {c = atm (cons i32 v)} C ((atm (cons .i32))) n D (tnormal vs , S) = con (tnormal (toI32 v ∷ vs) , S)
semCodeBase {c = atm (cons i64 v)} C ((atm (cons .i64))) n D (tnormal vs , S) = con (tnormal (toI64 v ∷ vs) , S)
semCodeBase C ((atm (add t))) n D (tnormal (v₂ ∷ v₁ ∷ vs) , S) = con (tnormal (evalAddT v₁ v₂ ∷ vs) , S)
semCodeBase C ((atm (store t))) n D (tnormal (l ∷ v ∷ vs) , S) = let _ , S' = evalStoreT t l v S in con (tnormal vs , S')
semCodeBase C ((atm (load t))) n D (tnormal (x ∷ vs) , S) = let v' , S' = evalLoadT t x S in con (tnormal (v' ∷ vs) , S')
semCodeBase {c = atm (brif ℓ)} C ((atm (brif-refl ℓ<))) n D (tnormal (x ∷ vs) , S) =
 if isYes (proj₁ x Data.Nat.≟ 0)
  then con (tnormal vs , S)
  else con (tbranch (tjump ℓ< (safetake (safe-lookup C ℓ<) vs)) , S)
semCodeBase C ((br-refl ℓ<)) n D (tnormal vs , S) =
  con (tbranch (tjump ℓ< (safetake (safe-lookup C ℓ<) vs)) , S)
semCodeBase C ((blk ft b)) n D (tnormal vs , S) =
  let (top-vs , res-vs) = safesplit (dom ft) vs
  in case b of \ where
    (block x) →
      let res = semCode (cod ft ∷ C) x n [] (tnormal (top-vs safe++ []) , S) in
        semExit res-vs res con
    (loop x) →
      let res = semCode (dom ft ∷ C) x n [] (tnormal (top-vs safe++ []) , S) in
        semExit res-vs res (case n of \where
          zero → \ _ → div
          (suc n) → semCodeBase C ((blk ft (loop x))) n D)
semCodeBase C _ n D (tbranch vs  , S) = con (tbranch vs , S)

-- semCode : ∀ {c : Code k} {qft} C → (C ⊢ c :' qft) → ℕ → ∀ D → semQFT (semCtx C) (semCtx C) qft D
semCode C (sub qft≤qft' tc) n = castQFT (semCtx C) (semCtx C) _ _ qft≤qft' (semCode C tc n)
semCode C (base tc) n = semCodeBase C tc n

⟦_⟧ : ∀ {c : Code k} {qft} {C} → (C ⊢ c :' qft) → ℕ → ∀ D → semQFT (semCtx C) (semCtx C) qft D
⟦_⟧ {C = C} = semCode C

⟦_⟧₀ : ∀ {c : Code k} {qft} {C} → (C ⊢ c :' qft) → ℕ → semQFT (semCtx C) (semCtx C) qft []
⟦ tc ⟧₀ n = ⟦ tc ⟧ n []


semCode-con-on-tbranch : ∀ {k} {C t} {is : Code k} (tc : C ⊢ is :' t) → ∀ n D b S → semCode C tc n D (tbranch b , S) ≡ con (tbranch b , S)
semCode-con-on-tbranch (base (atm (cons i32))) n D b S = refl
semCode-con-on-tbranch (base (atm (cons i64))) n D b S = refl
semCode-con-on-tbranch (base (atm (add t))) n D b S = refl
semCode-con-on-tbranch (base (atm (store t))) n D b S = refl
semCode-con-on-tbranch (base (atm (load t))) n D b S = refl
semCode-con-on-tbranch (base (atm (brif-refl ℓ<))) n D b S = refl
semCode-con-on-tbranch (base (br-refl ℓ<)) n D b S = refl
semCode-con-on-tbranch (base (blk ft x)) n D b S = refl
semCode-con-on-tbranch (base []) n D b S = refl
semCode-con-on-tbranch (base (x ∷ x₁)) n D b S = refl
semCode-con-on-tbranch (sub (≤QFT-intro x ((da , ++da=) →' (dr , ++dr=)) uim) tc) n D b S
 rewrite semCode-con-on-tbranch tc n (da ++ D) b S = refl

∷-sub-commute : ∀ C i is a0 m0 r0 qi0 qis0 a m r qi qis (ti : C ⊢ i :' (a0 →' m0 , qi0)) (tis : C ⊢ is :' (m0 →' r0 , qis0))
  (≤a→m : (a0 →' m0 , qi0) ≤QFT (a →' m , qi)) (≤m→r : (m0 →' r0 , qis0) ≤QFT (m →' r , qis)) (≤a→r : (a0 →' r0 , qi0 ⊓QT qis0) ≤QFT (a →' r , qi ⊓QT qis))
  → ∀ n D → semCode C (sub ≤a→r (base (ti ∷ tis))) n D ≗ semCode C (base (sub ≤a→m ti ∷ sub ≤m→r tis)) n D
-- ∷-sub-commute C i is a0 m0 r0 qi0 qis0 a m r qi qis ti tis ≤a→m ≤m→r ≤a→r n D x
∷-sub-commute C i is a0 m0 r0 qi0 qis0 a m r qi qis ti tis ≤a→m ≤m→r ≤a→r n D (tbranch b , S) = semCode-con-on-tbranch (sub ≤a→r (base (ti ∷ tis))) n D b S
∷-sub-commute C i is a0 m0 r0 qi0 qis0 a m r qi qis ti tis ≤a→m ≤m→r ≤a→r n D (tnormal vs , S)
  = ( castQFT-cong _ _ ≤a→r F D  ⟨ ≗-trans ⟩ ≗-sym (>=>-castQFT-commute _ _ _ _ _ _ _ _ _ _ _ ≤a→m ≤m→r ≤a→r (semCode C ti n) (semCode C tis n) D)) (tnormal vs , S)
  where F : ∀ D → semCode C (base (ti ∷ tis)) n D ≗ (semCode C ti n >=> semCode C tis n) D
        F D (tbranch b , S) rewrite semCode-con-on-tbranch ti n D b S = refl
        F D (right _ , _) = refl

semExit-cong-pointwise : ∀ {X lt codft q C} {D : RT} → (vs : semRT D)
    → (res : Partial (semQRT (semCtx (lt ∷ C)) (codft ++ [] , q)))
    → {f g : semQFT X (semCtx C) (lt →' codft , uni) D}
    → f ≗ g → semExit vs res f ≡ semExit vs res g
semExit-cong-pointwise vs div f=g = refl
semExit-cong-pointwise vs (con (tbranch (tjump {ℓ = zero} ℓ< vs') , S)) f=g = f=g (tnormal (vs' safe++ vs) , S)
semExit-cong-pointwise vs (con (tbranch (tjump {ℓ = suc ℓ} (s≤s ℓ<) vs') , S)) f=g = refl
semExit-cong-pointwise vs (con (right x , _)) f=g = refl
