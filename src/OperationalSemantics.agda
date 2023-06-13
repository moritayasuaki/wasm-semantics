{-# OPTIONS --without-K --safe #-}
module OperationalSemantics where
open import Data.Bool as Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Nat as Nat using (ℕ ; suc ; zero ; z≤n ; s≤s)
open import Data.Nat.DivMod using (_%_ ; m%n<n)
-- open import Data.List renaming ([_] to [_]L ; _∷_ to _∷ₗ_ ; [] to []ₗ )
open import Data.Unit using (⊤  ; tt)
open import Data.Sum renaming ([_,_] to [_,_]Sum)
open import Data.Product
open import Data.Empty
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl ; _≗_ ; erefl ; sym ; trans)
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
import Level


private
  variable
    nbits : ℕ
abstract
  2^n-1 : ℕ → ℕ
  2^n-1 zero = zero
  2^n-1 (suc n) = 2^n-1 n Nat.+ suc (2^n-1 n)

2^ : ℕ → ℕ
2^ n = suc (2^n-1 n)

Int : ℕ → Set
Int nbits = ∃ \ (n : ℕ) → (n Nat.< 2^ nbits)

toInt : (nbits : ℕ) → ℕ → Int nbits
toInt nbits m = (m % (2^ nbits) , m%n<n m (2^n-1 nbits))

open Data.Nat.Properties

I32 = Int 32
I64 = Int 64
toℕ : Int nbits → ℕ
toℕ (i , _) = i
toI32 = toInt 32
toI64 = toInt 64

Loc = I32

pattern izero = (zero , z≤n)

_≟I_ : DecidableEquality (Int nbits)
_≟I_ x y = ≡-dec Nat._≟_ (\p q → yes (<-irrelevant p q)) x y

open Nat using (_+_ ; _<_ ; _≤_ ; _⊔_)

OpeStack = List
record Memory : Set where
  field
    bytes : Loc → ℕ

  mstore : Loc → ℕ → Memory
  mstore loc val = record
    { bytes = \ loc' → if isYes (loc ≟I loc') then val else bytes loc'
    }

  mload : Loc → ℕ
  mload loc = bytes loc

open Memory

record Store : Set where
  field
    mem : Memory

open Store

mapVT : VT → Set
mapVT i32 = I32
mapVT i64 = I64

Value = Σ VT mapVT

OpeStk = List Value

vtype : Value → VT
vtype = proj₁

rtype : OpeStk → RT
rtype [] = []
rtype (v ∷ vs) = vtype v ∷ rtype vs


open import Syntax
open import Subtype
-- open import BlockList

LoopCount = ℕ
RecCount = ℕ
StepCount = ℕ

BlkCtx = List (InstSeq × OpeStk × RT × InstSeq)

types : BlkCtx → Ctx
types [] = []
types ((_ , _ , rt , _) ∷ B) = rt ∷ types B

open import Result

data Either (L R : Set) : Set where
  left : L → Either L R
  right : R → Either L R



elimEither : {L R : Set} (C : Either L R → Set) → ((l : L) → C (left l)) → ((r : R) → C (right r)) → (e : Either L R) → C e
elimEither C cleft cright (left l) = cleft l
elimEither C cleft cright (right r) = cright r

recEither : {L R C : Set} → (L → C) → (R → C) → Either L R → C
recEither = elimEither (const _)

-- Checks if a value has a value typeq
checkVal : VT → Value → Bool
checkVal vt' (vt , _) = isYes (vt ≟VT vt')

-- Checks if the top part of a given operand stack has a result type. The operand stack is split into checked and unchecked portions.
checkStk : RT → OpeStk → Result (OpeStk × OpeStk)
checkStk [] vs = ok ([] , vs)
checkStk (vt ∷ rt) [] = err stack-underflow
checkStk (vt ∷ rt) (v ∷ vs) = if checkVal vt v
  then (case checkStk rt vs of \where
    (err e) → err e
    (ok (checked , unchecked)) → ok (v ∷ checked , unchecked))
  else err value-type-mismatch

evalCons : VT → ℕ → Value
evalCons i32 n = (i32 , toI32 n)
evalCons i64 n = (i64 , toI64 n)

evalStore : VT → Value → Value → Store → Result ⊤ × Store
evalStore i32 (i32 , loc) (i32 , n , _) S = ok tt , (record S {mem = mstore (mem S) loc n})
evalStore i64 (i32 , loc) (i64 , n , _) S = ok tt , (record S {mem = mstore (mem S) loc n})
evalStore _ _ _ S = err value-type-mismatch , S

evalLoad : VT → Value → Store → Result Value × Store
evalLoad i32 (i32 , loc) S = ok (i32 , toI32 (mload (mem S) loc)) , S
evalLoad i64 (i32 , loc) S = ok (i64 , toI64 (mload (mem S) loc)) , S
evalLoad _ _ S = err value-type-mismatch , S

evalAdd : VT → Value → Value → Result Value
evalAdd i32 (i32 , m , _) (i32 , n , _) = ok (i32 , toI32 (m + n))
evalAdd i64 (i64 , m , _) (i64 , n , _) = ok (i64 , toI64 (m + n))
evalAdd _ _ _ = err value-type-mismatch

dropLabels : ∀{L : Set} → List L → ℕ → Result (L × List L)
dropLabels C ℓ = case dropCtx C ℓ of \ where
  (just (rs , C')) → ok (rs , C')
  nothing → err branch-outside

evalBranch : ℕ → OpeStk → List RT → Result OpeStk
evalBranch ℓ vs rts = dropLabels rts ℓ |> okThen
  \ (x @ (rs , _)) → checkStk rs vs |> okThen
  \ (vs @ (top-vs , rest-vs)) → ok top-vs

pattern i32-false {p} = (i32 , zero , p)
pattern i32-true {n} {p} = (i32 , suc n , p)
pattern branch p = ok (left p)
pattern normal p = ok (right p)

evalAtm : Atm → Ctx → OpeStk → Store → Result (Either (ℕ × OpeStk) OpeStk) × Store
evalAtm (cons t n) _ vs S =
  normal (evalCons t n ∷ vs) , S
evalAtm (add t) _ (v₂ ∷ v₁ ∷ vs) S =
  case evalAdd t v₁ v₂ of \where
    (err e) → (err e , S)
    (ok v) → normal (v ∷ vs) , S
evalAtm (store t) _ (v₁ ∷ v₂ ∷ vs) S =
  let r , S' = evalStore t v₁ v₂ S
  in case r of \where
    (err e) → (err e , S')
    (ok tt) → (normal vs , S')
evalAtm (load t) _ (v ∷ vs) S =
  let r , S' = evalLoad t v S
  in case r of \where
    (err e) → (err e , S')
    (ok v) → (normal (v ∷ vs) , S')
evalAtm (br ℓ) C vs S =
  case evalBranch ℓ vs C of \where
    (err e) → (err e , S)
    (ok vs') → (branch (ℓ , vs') , S)
evalAtm (brif ℓ) _ (i32-false ∷ vs) S =
  normal vs , S
evalAtm (brif ℓ) C (i32-true ∷ vs) S =
  case evalBranch ℓ vs C of \where
    (err e) → (err e , S)
    (ok vs') → (branch (ℓ , vs') , S)
evalAtm _ _ _ S =
    (err stack-underflow , S)

private variable
  k : Kind

State = Result (Either (ℕ × OpeStk) OpeStk) × Store
Cont = InstSeq × BlkCtx

labeltype : Blk → FT → RT
labeltype block = cod
labeltype loop = dom

labelis : Blk → FT → InstSeq → InstSeq
labelis block ft is = []
labelis loop ft is = blk (loop :' ft) is  ∷ []

module BigStep where


  bigstep : LoopCount → Code k → Ctx → State → Partial State
  bigstep {k = Item} lc i C (err e , S) = con (err e , S)
  bigstep {k = Item} lc i C (branch b , S) = con (branch b , S)
  bigstep lc [] C st = con st
  bigstep lc (i ∷ is) C st =
    case bigstep lc i C st of bigstep-seq-case1 module _ where
    bigstep-seq-case1 = \where
      div → div
      (con st') → bigstep lc is C st'
  bigstep lc (atm x) C (normal vs , S) = con (evalAtm x C vs S)
  bigstep lc (blk (b :' ft) is) C (normal vs , S) =
    case checkStk (dom ft) vs of \where
        (err e) → con (err e , S)
        (ok (top-vs , res-vs)) →
          case bigstep lc is (labeltype b ft ∷ C) (normal top-vs , S) of bigstep-blk-case1 res-vs module _ where
        bigstep-blk-case1 = \ res-vs → \where
          div → div
          (con (err e , S')) → con (err e , S')
          (con (branch (suc ℓ , vs') , S')) → con (branch (ℓ , vs') , S')
          (con (branch (zero , vs') , S')) → case b of \where
            block → con (normal (vs' List.++ res-vs) , S')
            loop → case lc of \where
              zero → div
              (suc lc') → bigstep lc' (blk (b :' ft) is) C (normal (vs' List.++ res-vs) , S')
          (con (normal vs' , S')) → con (normal (vs' List.++ res-vs) , S')

  bigstep-loopcount : Code k × Ctx × State → (LoopCount → Partial State)
  bigstep-loopcount (c , C , st) lc = bigstep lc c C st

  bigstep-con-suc : ∀ (c : Code k) C st → con-suc (bigstep-loopcount (c , C , st))
  bigstep-con-suc {k = Item} c C (err x , S) a lc = id
  bigstep-con-suc {k = Item} c C (branch x , S) a lc = id
  bigstep-con-suc [] C st a lc = id
  bigstep-con-suc (i ∷ is) C st ans lc
    with con st' ← bigstep lc i C st in eq-i
    rewrite bigstep-con-suc i C st st' lc eq-i
    = bigstep-con-suc is C st' ans lc
  bigstep-con-suc (atm x) C (normal vs , S) a lc = id
  bigstep-con-suc (blk (b :' ft) c) C (normal vs , S) a lc
    with checkStk (dom ft) vs
  ... | err _ = id
  ... | ok (top-vs , res-vs)
    with bigstep lc c (labeltype b ft ∷ C) (normal top-vs , S) in eq
  ... | div = \()
  ... | con st'
    rewrite bigstep-con-suc c (labeltype b ft ∷ C) (normal top-vs , S) st' lc eq
    with st'
  ... | err _ , S' = id
  ... | branch (suc ℓ , vs') , S' = id
  ... | normal vs' , S' = id
  ... | branch (zero , vs') , S' with b | lc
  ... |  block | _ = id
  ... |  loop | zero = \()
  ... |  loop | suc lc' = bigstep-con-suc (blk (loop :' ft) c) C (normal (vs' List.++ res-vs) , S') a lc'

  module _ (c : Code k) (C : Ctx) (st : State) where
    open ConvergeProps (bigstep-con-suc c C st) renaming (con-n⊔-f to bigstep-con-n⊔ ; con-⊔n-f to bigstep-con-⊔n) public

  _⇓[_]_ : Code k × Ctx × State → LoopCount → State → Set
  cfg ⇓[ lc ] st' = ConvergeAt (bigstep-loopcount cfg) lc st'

  _⇓_ : Code k × Ctx × State → State → Set
  cfg ⇓ st' = Σ _ \ lc → cfg ⇓[ lc ] st'

  bigstep-con-on-branch : ∀ {k} lc (c : Code k) C b S → bigstep lc c C (branch b , S) ≡ con (branch b , S)
  bigstep-con-on-branch lc [] C b S = refl
  bigstep-con-on-branch lc (i ∷ is) C b S
    with bigstep-con-on-branch lc i C b S
  ... | _
    = bigstep-con-on-branch lc is C b S
  bigstep-con-on-branch lc (atm x) C b S = refl
  bigstep-con-on-branch lc (blk blktype c) C b S = refl

module SmallStep where
  smallstep1' : InstSeq → BlkCtx → State → InstSeq × BlkCtx × State
  smallstep1' [] [] st = [] , [] , st
  smallstep1' [] ((res-is , res-vs , _ , lbl-is) ∷ B) (err x , S) = (res-is , B , err x , S)
  smallstep1' [] ((res-is , res-vs , _ , lbl-is) ∷ B) (branch (zero , vs) , S) = (lbl-is BList.++ res-is , B , normal (vs List.++ res-vs) , S)
  smallstep1' [] ((res-is , res-vs , _ , lbl-is) ∷ B) (branch (suc ℓ , vs) , S) = (res-is , B , branch (ℓ , vs) , S)
  smallstep1' [] ((res-is , res-vs , _ , lbl-is) ∷ B) (normal vs , S) = (res-is , B , normal (vs List.++ res-vs) , S)
  smallstep1' (i ∷ is) B (err e , S) = is , B , (err e , S)
  smallstep1' (i ∷ is) B (branch b , S) = is , B , (branch b , S)
  smallstep1' (atm x ∷ is) B (normal vs , S) = (is , B , evalAtm x (types B) vs S)
  smallstep1' (blk (b :' ft) is ∷ res-is) B (normal vs , S) =
    case checkStk (dom ft) vs of \ where
      (err e) → (res-is , B , err e , S)
      (ok (top-vs , res-vs)) → (is , (res-is , res-vs , labeltype b ft , labelis b ft is) ∷ B , normal top-vs , S)

  smallstep1 : InstSeq × BlkCtx × State → InstSeq × BlkCtx × State
  smallstep1 (is , B , st) = smallstep1' is B st

  smallstepN : StepCount → InstSeq × BlkCtx × State → InstSeq × BlkCtx × State
  smallstepN zero = id
  smallstepN (suc sc) = smallstep1 ∘ smallstepN sc

  checkAns : InstSeq × BlkCtx × State → Partial State
  checkAns ([] , [] , ans) = con ans
  checkAns _ = div

  inv-checkAns : ∀ cfg ans → checkAns cfg ≡ con ans → cfg ≡ ([] , [] , ans)
  inv-checkAns ([] , [] , ans) .ans refl = refl

  smallstep : StepCount → InstSeq × BlkCtx × State → Partial State
  smallstep sc = checkAns ∘ smallstepN sc

  smallstep-stepcount : InstSeq × BlkCtx × State → StepCount → Partial State
  smallstep-stepcount = flip smallstep

  smallstep-+ : ∀ m n cfg → smallstepN (m + n) cfg ≡ smallstepN m (smallstepN n cfg)
  smallstep-+ zero n cfg = refl
  smallstep-+ (suc m) n cfg = ≡.cong smallstep1 (smallstep-+ m n cfg)

  smallstep-suc-comm : ∀ n cfg → smallstepN (suc n) cfg ≡ smallstepN n (smallstep1 cfg)
  smallstep-suc-comm zero cfg = refl
  smallstep-suc-comm (suc n) cfg = ≡.cong smallstep1 (smallstep-suc-comm n cfg)

  _⇉[_]_ : InstSeq × BlkCtx × State → StepCount → InstSeq × BlkCtx × State → Set
  cfg ⇉[ sc ] cfg' = smallstepN sc cfg ≡ cfg'

  _∙sc_ : ∀ {cfg cfg' cfg'' sc sc'} → cfg ⇉[ sc ] cfg' → cfg' ⇉[ sc' ] cfg'' → cfg ⇉[ sc' + sc ] cfg''
  _∙sc_ {cfg} {sc = sc} {sc' = sc'} refl refl = smallstep-+ sc' sc cfg

  _⇉_ : InstSeq × BlkCtx × State → InstSeq × BlkCtx × State → Set
  cfg ⇉ cfg' = Σ _ \ sc → cfg ⇉[ sc ] cfg'

  _∙_ : ∀ {cfg cfg' cfg''} → cfg ⇉ cfg' → cfg' ⇉ cfg'' → cfg ⇉ cfg''
  _∙_ {cfg} (sc , refl) (sc' , refl) = sc' + sc , smallstep-+ sc' sc cfg

  _↓[_]_ : InstSeq × BlkCtx × State → StepCount → State → Set
  cfg ↓[ sc ] st = ConvergeAt (smallstep-stepcount cfg) sc st

  _↓_ : InstSeq × BlkCtx × State → State → Set
  cfg ↓ st = Σ _ \ sc → cfg ↓[ sc ] st



  smallstep-con-suc : ∀ cfg → con-suc (smallstep-stepcount cfg)
  smallstep-con-suc cfg ans sc eq
    rewrite inv-checkAns (smallstepN sc cfg) ans eq
    = refl

  module _ (cfg : InstSeq × BlkCtx × State) where
    open ConvergeProps (smallstep-con-suc cfg) renaming (con-≤-f to smallstep-con-≤) public

  ⇉0 : ∀ {cfg cfg'} → cfg ≡ cfg' → cfg ⇉ cfg'
  ⇉0 p = 0 , p

  ⇉1 : ∀ {cfg cfg'} → smallstep1 cfg ≡ cfg' → cfg ⇉ cfg'
  ⇉1 p = 1 , p

  ⇉-stepin : ∀ {cfg cfg'} n → cfg ⇉[ suc n ] cfg' → smallstep1 cfg ⇉[ n ] cfg'
  ⇉-stepin {cfg} {cfg'} n ⇉[sn] = ≡.trans (≡.sym (smallstep-suc-comm n cfg)) ⇉[sn]

  ↓-stepin : ∀ {cfg a} n → cfg ↓[ suc n ] a → smallstep1 cfg ↓[ n ] a
  ↓-stepin {cfg} {a} n ↓[sn] = ≡.trans (≡.cong checkAns (≡.sym (smallstep-suc-comm n cfg))) ↓[sn]

  smallstep-stop : ∀ ans cfg sc → checkAns cfg ≡ con ans → cfg ⇉[ sc ] ([] , [] , ans)
  smallstep-stop ans cfg sc eq = inv-checkAns (smallstepN sc cfg) ans (smallstep-con-≤ cfg ans 0 sc z≤n eq)

  smallstep-ans-constant : ∀ ans st → ([] , [] , st) ↓ ans → st ≡ ans
  smallstep-ans-constant ans st (sc , ↓[sc]) = ind sc ↓[sc] where
    ind : ∀ sc → ([] , [] , st) ↓[ sc ] ans → st ≡ ans
    ind zero refl = refl
    ind (suc sc) ↓[ssc] = ind sc (↓-stepin sc ↓[ssc])
