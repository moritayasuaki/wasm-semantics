{-# OPTIONS --without-K --safe #-}
module Equivalence where

open import Data.Bool as Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Nat as Nat using (ℕ ; suc ; zero ; z≤n ; s≤s ; _+_ ; _<_ ; _≤_ ; _⊔_)
open import Data.Unit using (⊤  ; tt)
open import Data.Sum renaming ([_,_] to [_,_]Sum)
open import Data.Product
open import Data.Empty
open import Relation.Unary
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Nat.Properties
open import Data.Product.Properties
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.List as List using (List ; [] ; _∷_)
open import Data.Nat.Induction
open import Function
open import TypeSystem
open import Syntax
open import BlockList as BList using (BList ; [] ; _∷_ ; atm ; blk ; Kind ; Item ; Seq)
open import Partial
open import OperationalSemantics
open import Result
import Level


open BigStep
open SmallStep


-- We say big-step semantis and small-step semantics is equivalent if and only if
-- for any program (`is') and its initial state (`st'), both semantics results the same result (`ans').
--
-- `big⇔small : ∀ ans is st → ((is , [] , st) ⇓ ans) ⇔ ((is , [] , st) ↓ ans)'

-- To prove this, we need come up with a statemant with big-step semantics with context.
--
-- 1 , `big⇒small-ctx : ∀ ans is B st → ((is , types B , st) ⇓ ans) → ((is , B , st) ⇉ ([] , B , ans))'
--
-- For any context C and block context B where B and C are in relation (C ≡ types B),
-- if big-step semantics results `ans' in a given context C, small-steps also reaches a configuration ([] , B , ans) after some steps.
--
-- 2. `small⇒big-ctx : ∀ ans is C B st → (C ≡ types B)
--  → ((is , B , st) ↓ ans) → Σ _ \ st' → ((is , C , st) ⇓ st') × ([] , B , st') ↓ ans
--
-- For any context C and block context B where B and C are in relation (C ≡ types B),
-- if (is , B , st) converges to `ans' in small-step semantics, then big-step results st' for (is , C  st) and ([] , B , st') converges to ans in small-step semantics
--
-- In the proofs of 1 and 2 , we need simltaneous induction on instruction ans instruction sequences.

-- equivalence only refer to convergence but

checkStk-err⇒⇉[1] : ∀ {ft vs b is res-is B S e} → checkStk (dom ft) vs ≡ err e
  → ((blk (b :' ft) is ∷ res-is) , B , normal vs , S) ⇉[ 1 ] (res-is , B , err e , S)
checkStk-err⇒⇉[1] chkErr rewrite chkErr = refl

checkStk-err⇒⇉ : ∀ {ft vs b is res-is B S e} → checkStk (dom ft) vs ≡ err e → ((blk (b :' ft) is ∷ res-is) , B , normal vs , S) ⇉ (res-is , B , err e , S)
checkStk-err⇒⇉ chkErr = 1 , checkStk-err⇒⇉[1] chkErr

checkStk-ok⇒⇉[1] : ∀ {ft vs b is res-is B S top-vs res-vs} → checkStk (dom ft) vs ≡ ok (top-vs , res-vs)
  → ((blk (b :' ft) is ∷ res-is) , B , normal vs , S) ⇉[ 1 ] (is , (res-is , res-vs , labeltype b ft , labelis b ft is) ∷ B , normal top-vs , S)
checkStk-ok⇒⇉[1] chkOk rewrite chkOk = refl

checkStk-ok⇒⇉ : ∀ {ft vs b is res-is B S top-vs res-vs} → checkStk (dom ft) vs ≡ ok (top-vs , res-vs)
  → ((blk (b :' ft) is ∷ res-is) , B , normal vs , S) ⇉ (is , (res-is , res-vs , labeltype b ft , labelis b ft is) ∷ B , normal top-vs , S)
checkStk-ok⇒⇉ chkOk = 1 , checkStk-ok⇒⇉[1] chkOk


big⇒small-ctx : ∀ ans is C B st → (C ≡ types B) → ((is , C , st) ⇓ ans) → ((is , B , st) ⇉ ([] , B , ans))
big⇒small-ctx ans is C B st refl (lc , ⇓[lc]ans) = indS ans is B st lc ⇓[lc]ans where

  indS : ∀ ans is B st lc → ((is , types B , st) ⇓[ lc ] ans) → ((is , B , st) ⇉ ([] , B , ans))
  indI : ∀ ans i is B st lc → ((i , types B , st) ⇓[ lc ] ans) → ((i ∷ is , B , st) ⇉ (is , B , ans))

  indS ans [] B st lc ⇓ans with refl ← ⇓ans = 0 , refl
  indS ans (i ∷ is) B st lc ⇓ans
    with con ans' ← bigstep-loopcount (i , types B , st) lc in eq
    = indI ans' i is B st lc eq ∙ indS ans is B ans' lc ⇓ans

  indI ans i is B (err x , S) lc refl = 1 , refl
  indI ans i is B (branch x , S) lc refl = 1 , refl
  indI ans (atm x) is B (normal vs , S) lc refl = 1 , refl
  indI ans (blk (b :' ft) is) res-is B (normal vs , S) lc ⇓ans
    with checkStk (dom ft) vs in eq
  ... | err _ with refl ← ⇓ans = checkStk-err⇒⇉ eq
  ... | ok (top-vs , res-vs)
    with con (r , S') ← bigstep-loopcount (is , (labeltype b ft ∷ types B) , normal top-vs , S) lc in eq'
    with r | indS (r , S') is ((res-is , res-vs , labeltype b ft , labelis b ft is) ∷ B) (normal top-vs , S) lc eq'
  ... | err _ | ⇉err with refl ← ⇓ans = checkStk-ok⇒⇉ eq ∙ (⇉err ∙ (1 , refl))
  ... | normal vs' | ⇉normal with refl ← ⇓ans = checkStk-ok⇒⇉ eq ∙ (⇉normal ∙ (1 , refl))
  ... | branch (suc ℓ , vs') | ⇉branch with refl ← ⇓ans = checkStk-ok⇒⇉ eq ∙ (⇉branch ∙ (1 , refl))
  ... | branch (zero , vs') | ⇉branch0 with b | lc
  ... | block | _  with refl ← ⇓ans = checkStk-ok⇒⇉ eq ∙ (⇉branch0 ∙ (1 , refl))
  ... | loop | suc lc' =
    let ⇉ans = indI ans (blk (loop :' ft) is) res-is B (normal (vs' List.++ res-vs) , S') lc' ⇓ans in
      checkStk-ok⇒⇉ eq ∙ (⇉branch0 ∙ ((1 , refl) ∙ ⇉ans))

-- predicate on initial state and final state, if there is middle state that is reached from the initial state by bigstep and reaches final state by smallstep
_⇓↓[_]_ : InstSeq × BlkCtx × State → StepCount → State → Set
_⇓↓[_]_ cfg sc ans = let (is , B , st) = cfg in Σ _ \ st' → ((is , types B , st) ⇓ st') × ([] , B , st') ↓[ sc ] ans

_⇓↓[_]i_ : Inst × InstSeq × BlkCtx × State → StepCount → State → Set
_⇓↓[_]i_ cfg sc ans = let (i , is , B , st) = cfg in Σ _ \ st' → ((i , types B , st) ⇓ st') × (is , B , st') ↓[ sc ] ans

_⇓↓_ : InstSeq × BlkCtx × State → State → Set
cfg ⇓↓ ans = Σ _ \ sc → cfg ⇓↓[ sc ] ans

runBlk-err⇒⇓[lc] : ∀ {lc ft top-vs res-vs} C is b {S S' e}
  → (is , (labeltype b ft ∷ C) , normal top-vs , S) ⇓[ lc ] (err e , S')
  → bigstep-blk-case1 lc b ft is C top-vs S res-vs (bigstep lc is (labeltype b ft ∷ C) (normal top-vs , S) ) ≡ con (err e , S')
runBlk-err⇒⇓[lc] C is b x rewrite x = refl

runBlk-branch⇒⇓[lc] : ∀ {lc ft top-vs res-vs} C is b {S S' ℓ vs'}
  → (is , (labeltype b ft ∷ C) , normal top-vs , S) ⇓[ lc ] (branch (suc ℓ , vs') , S')
  → bigstep-blk-case1 lc b ft is C top-vs S res-vs (bigstep lc is (labeltype b ft ∷ C) (normal top-vs , S) ) ≡ con (branch (ℓ , vs') , S')
runBlk-branch⇒⇓[lc] C is b x rewrite x = refl

runBlk-normal⇒⇓[lc] : ∀ {lc ft top-vs res-vs} C is b {S S' vs'}
  → (is , (labeltype b ft ∷ C) , normal top-vs , S) ⇓[ lc ] (normal vs' , S')
  → bigstep-blk-case1 lc b ft is C top-vs S res-vs (bigstep lc is (labeltype b ft ∷ C) (normal top-vs , S) ) ≡ con (normal (vs' List.++ res-vs) , S')
runBlk-normal⇒⇓[lc] C is b x rewrite x = refl

runBlk-branch0-block⇒⇓[lc] : ∀ {lc ft top-vs res-vs} C is {S S' vs'}
  → (is , (labeltype block ft ∷ C) , normal top-vs , S) ⇓[ lc ] (branch (zero , vs') , S')
  → bigstep-blk-case1 lc block ft is C top-vs S res-vs (bigstep lc is (labeltype block ft ∷ C) (normal top-vs , S) ) ≡ con (normal (vs' List.++ res-vs) , S')
runBlk-branch0-block⇒⇓[lc] C is x rewrite x = refl

small⇒big-ctx : ∀ ans is C B st → (C ≡ types B) → ((is , B , st) ↓ ans)
  → Σ _ \ st' → ((is , C , st) ⇓ st') × ([] , B , st') ↓ ans
small⇒big-ctx ans is C B st refl (sc , ↓[sc]) =
  let (sc' , (st' , ⇓st' , ↓[sc']ans ) , _) = indS ans is B st sc ↓[sc] (<-wellFounded sc)
  in st' , ⇓st' , sc' , ↓[sc']ans
    where
  indS : ∀ ans is B st sc → (is , B , st) ↓[ sc ] ans → (Acc _<_ sc)
      → Σ _ \ sc' → ((is , B , st) ⇓↓[ sc' ] ans) × sc' ≤ sc
  indI : ∀ ans i is B st sc → (i ∷ is , B , st) ↓[ sc ] ans → (Acc _<_ sc)
    → Σ _ \ sc' → ((i , is , B , st) ⇓↓[ sc' ]i ans) × sc' < sc

  indS ans [] B st sc ↓[sc] sc-acc = sc , (st , ((0 , refl) , ↓[sc])) , ≤-refl
  indS ans (i ∷ is) B st (suc sc) st↓[ssc] (acc rec) with indI ans i is B st (suc sc) st↓[ssc] (acc rec)
  ... | sc' , (st' , (lc , ⇓[lc]st') , st'↓[sc']) , s≤s sc'≤sc with indS ans is B st' sc' st'↓[sc'] (rec _ (s≤s sc'≤sc))
  ... | sc'' , (st'' , (lc' , ⇓[lc']st'') , st''↓[sc'']) , sc''≤sc' =
    sc'' , (st'' , ((lc ⊔ lc') , P) , st''↓[sc'']) , (≤-step sc''≤sc' ⟨ ≤-trans ⟩ s≤s sc'≤sc)
    where P : (bigstep-seq-case1 (lc ⊔ lc') i is (types B) st)
                (bigstep (lc ⊔ lc') i (types B) st)
                ≡ con st''
          P rewrite bigstep-con-⊔n i (types B) st st' lc lc' ⇓[lc]st'
            rewrite bigstep-con-n⊔ is (types B) st' st'' lc' lc ⇓[lc']st''
            = refl

  indI ans i is B (err e , S) (suc sc) ↓[ssc] sc-acc = sc , ((err e , S) , ((0 , refl) , ↓-stepin sc ↓[ssc])) , ≤-refl
  indI ans i is B (branch b , S) (suc sc) ↓[ssc] sc-acc = sc , ((branch b , S) , ((0 , refl) , ↓-stepin sc ↓[ssc])) , ≤-refl
  indI ans (atm x) is B (normal vs , S) (suc sc) ↓[ssc] sc-acc = sc , (evalAtm x (types B) vs S , (0 , refl) , ↓-stepin sc ↓[ssc]) , ≤-refl
  indI ans (blk (b :' ft) is) res-is B (normal vs , S) (suc sc) ↓[ssc] (acc rec) with checkStk (dom ft) vs in eq | ↓-stepin sc ↓[ssc]
  ... | err e | ↓[sc] = sc , ((err e , S) , ((0 , refl) , ↓[sc])) , ≤-refl
  ... | ok (top-vs , res-vs) | ↓[sc]
    with indS ans is ((res-is , res-vs , labeltype b ft , labelis b ft is) ∷ B) (normal top-vs , S) sc ↓[sc] (rec _ ≤-refl)
  ... | suc sc' , ((err e , S') , (lc , ⇓[lc]st') , ↓[ssc']) , ssc'≤sc
    = sc' , (((err e , S') , ((lc , runBlk-err⇒⇓[lc] (types B) is b ⇓[lc]st') , ↓-stepin sc' ↓[ssc'])) , ≤-step ssc'≤sc)
  ... | suc sc' , ((branch (suc ℓ , vs') , S') , (lc , ⇓[lc]st') , ↓[ssc']) , ssc'≤sc
    = sc' , (((branch (ℓ , vs') , S') , ((lc , runBlk-branch⇒⇓[lc] (types B) is b ⇓[lc]st') , ↓-stepin sc' ↓[ssc'])) , ≤-step ssc'≤sc)
  ... | suc sc' , ((normal vs' , S') , (lc , ⇓[lc]st') , ↓[ssc']) , ssc'≤sc
    = sc' , ((normal (vs' List.++ res-vs) , S') , (lc , runBlk-normal⇒⇓[lc] (types B) is b ⇓[lc]st') , ↓-stepin sc' ↓[ssc']) , ≤-step ssc'≤sc
  ... | suc sc' , ((branch (zero , vs') , S') , (lc , ⇓[lc]st') , ↓[ssc']) , ssc'≤sc
    with b
  ... | block
    = sc' , ((normal (vs' List.++ res-vs) , S') , (lc , runBlk-branch0-block⇒⇓[lc] (types B) is ⇓[lc]st') , ↓-stepin sc' ↓[ssc']) , ≤-step ssc'≤sc
  ... | loop
    with indI ans (blk (loop :' ft) is) res-is B (normal (vs' List.++ res-vs) , S') sc' (↓-stepin sc' ↓[ssc']) (rec _ (≤-step ssc'≤sc))
  ... | sc'' , (st'' , (lc' , ⇓[lc']st'') , ↓[sc'']) , ssc''≤sc'  = sc'' , (st'' , (suc (lc ⊔ lc') , P) , ↓[sc'']) , (ssc''≤sc' ⟨ ≤-trans ⟩ ( ≤-step ≤-refl ⟨ ≤-trans ⟩ (ssc'≤sc ⟨ ≤-trans ⟩ ≤-step ≤-refl)))
    where P : (bigstep-blk-case1 (suc (lc ⊔ lc')) loop ft is (types B) top-vs S res-vs)
              (bigstep (suc (lc ⊔ lc')) is (dom ft ∷ types B) (normal top-vs , S))
                ≡ con st''
          P with ⇓[lc⊔lc']st' ← bigstep-con-⊔n is (dom ft ∷ types B) (normal top-vs , S) (branch (0 , vs') , S') lc lc' ⇓[lc]st'
            rewrite bigstep-con-suc is (dom ft ∷ types B) (normal top-vs , S) (branch (0 , vs') , S') (lc ⊔ lc') ⇓[lc⊔lc']st'
            with ⇓[lc⊔lc']st'' ← bigstep-con-n⊔ (blk (loop :' ft) is) (types B) (normal (vs' List.++ res-vs) , S') st'' lc' lc ⇓[lc']st''
            rewrite ⇓[lc⊔lc']st'' = refl

big⇒small : ∀ ans is st → (is , [] , st) ⇓ ans → (is , [] , st) ↓ ans
big⇒small ans is st ⇓ans =
  let sc , ⇉ans = big⇒small-ctx ans is [] [] st refl ⇓ans
  in sc , ≡.cong checkAns ⇉ans

small⇒big : ∀ ans is st → (is , [] , st) ↓ ans → (is , [] , st) ⇓ ans
small⇒big ans is st ↓ans
  with (ans' , ⇓ans'  , ↓ans) ← small⇒big-ctx ans is [] [] st refl ↓ans
  with refl ← smallstep-ans-constant ans ans' ↓ans
  = ⇓ans'

big⇔small : ∀ ans is st → ((is , [] , st) ⇓ ans) ⇔ ((is , [] , st) ↓ ans)
big⇔small ans is st = mk⇔ (big⇒small ans is st) (small⇒big ans is st)
