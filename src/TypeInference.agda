{-# OPTIONS --without-K --safe #-}

-- This inference works including br / drop but not for select (it requires quantifier over value types and type variable)
module TypeInference where

open import Relation.Nullary.Decidable
open import Data.Bool as Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Nat as ℕ using (ℕ ; suc ; zero ; _≤_ ; _<_ ; s≤s ; z≤n)
open import Data.Product as Product using (_,_ ; proj₁ ; proj₂ ; Σ ; ∃ ; _×_)
open import Arrow
open import Data.List as List using (List ; [] ; _∷_ ; length ; _++_)
open import BlockList as BList using (BList ; atm ; blk ; [] ; _∷_ ; Kind ; Item ; Seq)
open import Syntax
open import Subtype
open import TypeSystem
open import Data.Unit as Unit using (⊤ ; tt)
open import Data.Empty as Empty using (⊥ ; ⊥-elim)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl ; erefl ; _≢_)
open import Data.Maybe as Maybe using (Maybe ; just ; nothing ; maybe)
open import Function
open import Category.Monad
open import Function.Identity.Categorical as Id
open import Data.Sum as Sum using (_⊎_ ; inj₁ ; inj₂)
open import Level
open import Relation.Nullary as RN
open import Relation.Nullary.Decidable as Dec
-- open import Data.List.Relation.Binary.Prefix.Heterogeneous as PX
open import ListOps
open import Data.List.Properties
open import Data.Nat.Properties
open import UntypedLift
open RSub

private variable
  k : Kind
  X  Y : Set

open import Result

safe-lookup-refines-lookup : ∀ {X : Set} {ℓ} (xs : List X) → (ℓ< : ℓ < length xs) → lookup xs ℓ ≡ just (safe-lookup xs ℓ<)
safe-lookup-refines-lookup {ℓ = zero} (x ∷ xs) (s≤s ℓ<) = ≡.refl
safe-lookup-refines-lookup {ℓ = suc ℓ} (x ∷ xs) (s≤s ℓ<) = safe-lookup-refines-lookup xs ℓ<

inversion-lookup : ∀ {X : Set} {ℓ} {xs : List X} {x : X} → lookup xs ℓ ≡ just x → ∃ \ (ℓ< : ℓ < length xs) → safe-lookup xs ℓ< ≡ x
inversion-lookup {ℓ = zero} {x ∷ xs} {.x} ≡.refl = (s≤s z≤n) , ≡.refl
inversion-lookup {ℓ = suc ℓ} {x' ∷ xs} {x} eq = let (p≤ , p≡) = inversion-lookup {ℓ = ℓ} {xs} {x} eq in s≤s p≤ , p≡

maybeToResult : Error → Maybe X → Result X
maybeToResult _ (just x) = ok x
maybeToResult e nothing = err e

maybeToResultInv : ∀ {e m} {x : X} → maybeToResult e m ≡ ok x → m ≡ just x
maybeToResultInv {e = e} {m = just x} .{x} refl = refl

decToResult : Error → Dec X → Result X
decToResult e = maybeToResult e ∘ Maybe.decToMaybe

import Relation.Nullary.Reflects as RNR
decToResultInv :  ∀ {e d} {x : X} → decToResult e d ≡ ok x → d ≡ yes x
decToResultInv {e = e} {d = yes p} .{RNR.invert (ofʸ p)} refl = refl

private
  M : Set → Set
  M X = (Ctx → Result X)

  _>>=_ : M X → (X → M Y) → M Y
  (m >>= f) C = case m C of \ where
    (err e) → err e
    (ok r) → f r C

  _>>_ : M X → M Y → M Y
  m >> f = m >>= const f

  pure : X → M X
  pure = const ∘ ok

  guard : Error → (Ctx → Dec X) → M X
  guard e pr C = decToResult e (pr C)

  ask : M Ctx
  ask C = ok C

  raise : Error → M X
  raise = const ∘ err

enterBlock : RT → M X → M X
enterBlock rt m C = m (rt ∷ C)

getLabelType : ℕ → M RT
getLabelType ℓ C = maybeToResult no-branch-target (lookup C ℓ)

getLabelTypeInv : ∀ {ℓ C rt} → getLabelType ℓ C ≡ ok rt → ∃ \ (ℓ< : ℓ ℕ.< List.length C) → safe-lookup C ℓ< ≡ rt
getLabelTypeInv = inversion-lookup ∘ maybeToResultInv

_*Q_ : QT → RT → RT
bi *Q rt = []
uni *Q rt = rt

_⊔RT_ : RT → RT → Maybe RT
[] ⊔RT rt' = just rt'
(vt ∷ rt) ⊔RT [] = just (vt ∷ rt)
(vt ∷ rt) ⊔RT (vt' ∷ rt') = Maybe.decToMaybe (vt ≟VT vt') Maybe.>>= (\ _ → (rt ⊔RT rt') Maybe.>>= \ rt' → just (vt' ∷ rt'))

record IsUpperBound {X : Set} (_≤_ : X → X → Set) (l r : X) (ub : X) : Set where
  constructor mk-ub
  field
    ≤-l : l ≤ ub
    ≤-r : r ≤ ub

record IsLeastUpperBound {X : Set} (_≤_ : X → X → Set) (l r : X) (lub : X) : Set where
  constructor mk-lub
  field
    ub : IsUpperBound _≤_ l r lub
    least : ∀ x → IsUpperBound _≤_ l r x → lub ≤ x

-- ⊔RT but with proof of either lub-prefix or emptiness of ub
⊔RT-with-proof : (rt rt' : RT) → Σ RT (IsLeastUpperBound _⊑RT_ rt rt') ⊎ (∀ x → ¬ IsUpperBound _⊑RT_ rt rt' x)
⊔RT-with-proof [] rt' = inj₁ (rt' , mk-lub (mk-ub ([]⊑RT _)  ⊑RT-refl) (\ ub (mk-ub rt⊑ub rt'⊑ub) → rt'⊑ub))
⊔RT-with-proof (r ∷ rt) [] = inj₁ (r ∷ rt , mk-lub (mk-ub (⊑RT-refl) ([]⊑RT _)) (\ ub (mk-ub rt⊑ub rt'⊑ub) → rt⊑ub))
⊔RT-with-proof (x ∷ rt) (x' ∷ rt') = case x ≟VT x' of \where
  (yes p) → case ⊔RT-with-proof rt rt' of \where
    (inj₁ (lub , mk-lub (mk-ub rt<lub rt'<lub) least)) → inj₁ ((x' ∷ lub , mk-lub (mk-ub (≡×⊑⇒∷⊑∷ p rt<lub) (≡×⊑⇒∷⊑∷ refl rt'<lub))
      \ { (u ∷ ub) (mk-ub xrt<ub xrt'<ub) → ≡×⊑⇒∷⊑∷ (≡.sym p ⟨ ≡.trans ⟩ proj₁ (∷⊑∷⇒≡×⊑ xrt<ub)) (least ub (mk-ub (proj₂ (∷⊑∷⇒≡×⊑ xrt<ub)) (proj₂ (∷⊑∷⇒≡×⊑ xrt'<ub))))}))
    (inj₂ noub) → inj₂ \ { (u ∷ ub) (mk-ub xrt<uub xrt'<uub) → noub ub (mk-ub (proj₂ (∷⊑∷⇒≡×⊑ xrt<uub)) (proj₂ (∷⊑∷⇒≡×⊑ xrt'<uub))) }
  (no np) → inj₂ \{ (u ∷ ub) (mk-ub xrt<uub xrt'<uub) → np (proj₁ (∷⊑∷⇒≡×⊑ xrt<uub) ⟨ ≡.trans ⟩ ≡.sym ( proj₁ (∷⊑∷⇒≡×⊑ xrt'<uub) ) )}

{-
⊔RT-with-proof : (rt rt' : RT) → (Σ RT \ lub → rt ⊑RT lub × rt' ⊑RT lub × ∀ ub → rt ⊑RT ub → rt' ⊑RT ub → lub ⊑RT ub) ⊎ (∀ rt'' → rt ⊑RT rt'' → rt' ⊑RT rt'' → ⊥)
⊔RT-with-proof [] rt' = inj₁ (rt' , []⊑RT _ , ⊑RT-refl , \ ub rt⊑ub rt'⊑ub → rt'⊑ub)
⊔RT-with-proof (r ∷ rt) [] = inj₁ ((r ∷ rt) , ⊑RT-refl , []⊑RT _ , \ ub rt⊑ub rt'⊑ub → rt⊑ub)
⊔RT-with-proof (x ∷ rt) (x' ∷ rt') = case x ≟VT x' of \where
  (yes p) → case ⊔RT-with-proof rt rt' of \where
    (inj₁ (lub , rt<lub , rt'<lub , proof-lub)) → inj₁ ((x' ∷ lub , ≡×⊑⇒∷⊑∷ p rt<lub , ≡×⊑⇒∷⊑∷ refl rt'<lub ,
      \ { (u ∷ ub) xrt<ub xrt'<ub → ≡×⊑⇒∷⊑∷ (≡.sym p ⟨ ≡.trans ⟩ proj₁ (∷⊑∷⇒≡×⊑ xrt<ub)) (proof-lub ub (proj₂ (∷⊑∷⇒≡×⊑ xrt<ub)) (proj₂ (∷⊑∷⇒≡×⊑ xrt'<ub)))}))
    (inj₂ noub) → inj₂ \ { (u ∷ ub) xrt<uub xrt'<uub → noub ub (proj₂ (∷⊑∷⇒≡×⊑ xrt<uub)) (proj₂ (∷⊑∷⇒≡×⊑ xrt'<uub)) }
  (no np) → inj₂ \{ (u ∷ ub) xrt<uub xrt'<uub → np (proj₁ (∷⊑∷⇒≡×⊑ xrt<uub) ⟨ ≡.trans ⟩ ≡.sym ( proj₁ (∷⊑∷⇒≡×⊑ xrt'<uub) ) )}
-}

proof-refines-⊔RT : ∀ x y → x ⊔RT y ≡ (case ⊔RT-with-proof x y of \{ (inj₁ x) → just (proj₁ x) ; (inj₂ _) → nothing })
proof-refines-⊔RT [] y = refl
proof-refines-⊔RT (x ∷ x₁) [] = refl
proof-refines-⊔RT (v ∷ xs) (v' ∷ xs') with v ≟VT v'
... | no _ = refl
... | yes _ with xs ⊔RT xs' | ⊔RT-with-proof xs xs' | proof-refines-⊔RT xs xs'
... | nothing | inj₂ y | r = refl
... | just .(proj₁ x₁) | inj₁ x₁ | refl = refl

infer : Code k → Ctx → RQFT
infer (atm (add t)) C = ok ((t ∷ t ∷ []) →' (t ∷ []) , uni)
infer (atm (cons t _)) C = ok ([] →' (t ∷ []) , uni)
-- infer (atm pop) = pure ((i32 ∷ []) →' [] , uni)
infer (atm (store t)) C = ok ((i32 ∷ t ∷ []) →' [] , uni)
infer (atm (load t)) C = ok ((i32 ∷ []) →' (t ∷ []) , uni)
infer (atm (br ℓ)) C = case ℓ <? length C of \ where
  (no _) → err no-branch-target
  (yes ℓ<) → ok (safe-lookup C ℓ< →' [] , bi)
infer (atm (brif ℓ)) C = case ℓ <? length C of \ where
  (no _) → err no-branch-target
  (yes ℓ<) → ok ((i32 ∷ safe-lookup C ℓ<) →' safe-lookup C ℓ< , uni)
infer (blk (block :' ft) is) C = case infer is (cod ft ∷ C) of \where
  (err e) → err e
  (ok qft) → case qft ≤?QFT (ft , uni) of \where
    (no _) → err annotation-mismatch
    (yes _) → ok (ft , uni)
infer (blk (loop :' ft) is) C = case infer is (dom ft ∷ C) of \where
  (err e) → err e
  (ok qft) → case qft ≤?QFT (ft , uni) of \where
    (no _) → err annotation-mismatch
    (yes _) → ok (ft , uni)
infer [] C = ok ([] →' [] , uni)
infer (i ∷ is) C with infer i C | infer is C
... | err e | _ = err e
... | ok _ | err e = err e
... | ok (a' →' mi , qi) | ok (mis →' r' , qis) = case mi ⊔RT mis of \where
  nothing → err value-type-error
  (just m) → ok ((a' →' r') ++² ((qi *Q dl mi m) →' (qis *Q dl mis m)) , qi ⊓QT qis)

module Helper where

{-
  mk≡FTcod : ∀ {ft : FT} {rt rt'} → (cod ft List.++ dl (cod ft) rt) ≡ rt → ft ≡ tl² ft ((dom ft List.++ rt') →' rt)
  mk≡FTcod {ft} {rt} {rt'} x rewrite ≡.sym x = (≡.sym (tl++² ft (rt' →' dl (cod ft) rt)))

  mk≡FTdom : ∀ {ft : FT} {rt rt'} → (dom ft List.++ dl (dom ft) rt) ≡ rt → ft ≡ tl² ft (rt →' (cod ft List.++ rt'))
  mk≡FTdom {ft} {rt} {rt'} x rewrite ≡.sym x = (≡.sym (tl++² ft (dl (dom ft) rt →' rt')))

  mk≡IdTypecod : ∀ {rt rt' : RT} rt'' → rt ≡ tl rt rt' → dl rt rt' ≡ dl rt'' (rt'' List.++ dl rt rt')
  mk≡IdTypecod {rt = rt} {rt'} rt'' x rewrite dl++ rt'' (dl rt rt') = ≡.refl

  mk≡IdTypedom : ∀ {rt rt' : RT} rt'' → rt ≡ tl rt rt' → dl rt'' (rt'' List.++ dl rt rt') ≡ dl rt rt'
  mk≡IdTypedom {rt = rt} {rt'} rt'' x rewrite dl++ rt'' (dl rt rt') = ≡.refl

  mk≡RTcod : ∀ {m m' r r' : RT} → dl m m' ≡ dl r r' → tl m m' ≡ m → m' ≡ (m List.++ dl r r')
  mk≡RTcod {m = m} {m'} dlmr tlm = ≡.trans (≡.sym (tl++dl m m')) (≡.cong₂ List._++_ tlm dlmr)
-}
-- mere soundness (if some type are infered, then the code gets the type)
Soundness : (∀ {k} → Code k → Ctx → RQFT) → Set
Soundness f = ∀ {k} (c : Code k) C → C ⊢? c :' f c C

-- converse of completeness (trivial)
SoundnessSub : (∀ {k} → Code k → Ctx → RQFT) → Set
SoundnessSub f = ∀ {k} (c : Code k) C t → f c C ≤RQFT t → (C ⊢? c :' t)

-- property that the root of the derivation tree is made by either of base rules , and not by subtyping
-- this property is used for base case to construct canonical derivation tree
BaseSoundness : (∀ {k} → Code k → Ctx → RQFT) → Set
BaseSoundness f = ∀ {k} (c : Code k) C → C ⊢[base]? c :' f c C

LowerBound : ∀ {k} → Code k → Ctx → RQFT → Set
LowerBound c C t0 = (∀ t → (C ⊢? c :' t) → t0 ≤RQFT t)

Principal : ∀ {k} → Code k → Ctx → RQFT → Set
Principal c C t0 = (C ⊢? c :' t0) × LowerBound c C t0

BasePrincipal : ∀ {k} → Code k → Ctx → RQFT → Set
BasePrincipal c C t0 = (C ⊢[base]? c :' t0) × LowerBound c C t0

-- an inference is complete iff it returns a lower bound of a set of valid types
Completeness : (∀ {k} → Code k → Ctx → RQFT) → Set
Completeness f = ∀ {k} (c : Code k) C → LowerBound c C (f c C)
-- Completeness f = ∀ {k} (c : Code k) C t → (C ⊢ c :' t) → f c C ≤RQFT t

StrongCompleteness : (∀ {k} → Code k → Ctx → RQFT) → Set
StrongCompleteness f = ∀ {k} (c : Code k) C → ∀ t → (C ⊢ c :' t) → ⊥


Principality : (∀ {k} → Code k → Ctx → RQFT) → Set
Principality f = ∀ {k} (c : Code k) C → Principal c C (f c C)

BasePrincipality : (∀ {k} → Code k → Ctx → RQFT) → Set
BasePrincipality f = ∀ {k} (c : Code k) C → BasePrincipal c C (f c C)

Canonical : ∀ {k} {c : Code k} {C t} → (C ⊢? c :' t) → Set
Canonical {c = c} {C} {t} tc = Σ RQFT \ t0 → LowerBound c C t0 × Σ (C ⊢[base]? c :' t0) \ tc0 → Σ (t0 ≤RQFT t) \ tc0≤t → tc ≡ sub? tc0≤t (base? tc0)

Transform : ∀ {k} → Code k → Ctx → RQFT → Set
Transform c C t = (C ⊢? c :' t) → (C ⊢? c :' t)

Canonify : ∀ {k} (c : Code k) C t → Transform c C t → Set
Canonify c C t F = (tc : C ⊢? c :' t) → Canonical (F tc)

Normalise : ∀ {k} (c : Code k) C t → Transform c C t → Set
Normalise c C t F = (tc tc' : C ⊢? c :' t) → F tc ≡ F tc'

Soundness⇒SoundnessSub : {f : ∀ {k} → Code k → Ctx → RQFT} → Soundness f → SoundnessSub f
Soundness⇒SoundnessSub f-sound c C rqft ≤rqft = sub? ≤rqft (f-sound c C)

BaseSoundness⇒Soundness : {f : ∀ {k} → Code k → Ctx → RQFT} → BaseSoundness f → Soundness f
BaseSoundness⇒Soundness f-basesound c C = base? (f-basesound c C)

Soundness∧Completeness⇒Principality : {f : (∀ {k} → Code k → Ctx → RQFT)} → Soundness f → Completeness f → Principality f
Soundness∧Completeness⇒Principality f-sound f-complete c C = f-sound c C , f-complete c C

BaseSoundness∧Completeness⇒BasePrincipality : {f : (∀ {k} → Code k → Ctx → RQFT)} → BaseSoundness f → Completeness f → BasePrincipality f
BaseSoundness∧Completeness⇒BasePrincipality f-basesound f-complete c C = f-basesound c C , f-complete c C

SoundnessSub∧Completeness⇒Transform : {f : ∀ {k} → Code k → Ctx → RQFT} → SoundnessSub f → Completeness f → ∀ {k} {c : Code k} {C t} → Transform c C t
SoundnessSub∧Completeness⇒Transform f-soundsub f-complete tc = f-soundsub _ _ _ (f-complete _ _ _ tc)

BaseSoundness∧Completeness⇒Canonify : (f : ∀ {k} → Code k → Ctx → RQFT) → (f-basesound : BaseSoundness f) → (f-complete : Completeness f) → ∀ {k} (c : Code k) C t
  → let f-sound = BaseSoundness⇒Soundness f-basesound
        f-soundsub = Soundness⇒SoundnessSub f-sound
        f-transform = SoundnessSub∧Completeness⇒Transform f-soundsub f-complete
    in Canonify c C t f-transform
BaseSoundness∧Completeness⇒Canonify f f-basesound f-complete c C t tc
  = f c C -- f infers a base principal type
  , f-complete c C -- f infers a lower bound type of all valid types
  , f-basesound c C -- f-infered type has a base (non-sub) type derivation
  , f-complete c C t tc -- subtype relation f c C ≤ t
  , refl -- tree-conv tc = sub (f c C ≤ t) (base tc0)

SoundnessSub∧Completeness⇒Normalise : (f : ∀ {k} → Code k → Ctx → RQFT) → (f-soundsub : SoundnessSub f) → (f-complete : Completeness f) → ∀ {k} (c : Code k) C t
  → let f-transform = SoundnessSub∧Completeness⇒Transform f-soundsub f-complete
    in Normalise c C t f-transform
SoundnessSub∧Completeness⇒Normalise f f-soundsub f-complete c C t tc tc'
  with f-complete c C t tc | f-complete c C t tc'
... | tc0≤tc | tc0≤tc'
  with refl ← ≤RQFT-irrelevant tc0≤tc tc0≤tc'
  = refl

module _ where
  uni-helper : ∀ {mi mis m} → (mi⊑m : mi ⊑RT m) → (mis⊑m : mis ⊑RT m) → mi ++ proj₁ mi⊑m ≡ mis ++ proj₁ mis⊑m
  uni-helper {mi} {mis} {m} (dmi , ++dmi≡m) (dmis , ++dmis≡m) = ++dmi≡m ⟨ ≡.trans ⟩ ≡.sym ++dmis≡m

  bi-helper' : ∀ {m' m : RT} → (m'⊑m : m' ⊑RT m) → (q : QT) → UniId q (proj₁ m'⊑m →' (q *Q proj₁ m'⊑m))
  bi-helper' m'⊑m bi = tt
  bi-helper' m'⊑m uni = refl


  uni-sym : ∀ {q a b} → UniId q (a →' b) → UniId q (b →' a)
  uni-sym {bi} x = tt
  uni-sym {uni} x = ≡.sym x

  ⊓QT-glb : ∀ q q' → (q ⊓QT q') ≤QT q × (q ⊓QT q') ≤QT q'
  ⊓QT-glb bi q' = bi≤q , bi≤q
  ⊓QT-glb uni bi = bi≤q , bi≤q
  ⊓QT-glb uni uni = uni≤uni , uni≤uni

  ⊓QT-mono : ∀ {q q' p p'} → q ≤QT q' → p ≤QT p' → (q ⊓QT p) ≤QT (q' ⊓QT p')
  ⊓QT-mono bi≤q _ = bi≤q
  ⊓QT-mono uni≤uni bi≤q = bi≤q
  ⊓QT-mono uni≤uni uni≤uni = uni≤uni

  ++RT⊑ : ∀ a d → a ⊑RT (a ++ d)
  ++RT⊑ a d = (d , refl)
  op : ∀ {X Y : Set} → Arrow X Y → Arrow Y X
  op (a →' b) = (b →' a)

  op⊑ : ∀ {x y} → x ⊑FT y → (op x) ⊑FT (op y)
  op⊑ (a⊑a' →' r⊑r') = (r⊑r' →' a⊑a')

  opQId : ∀ {q p} → QId q p → QId q (op p)
  opQId qid qv = ≡.sym (qid qv)

  opUniId : ∀ {q p} → UniId q p → UniId q (op p)
  opUniId {bi} uni-id = tt
  opUniId {uni} uni-id = ≡.sym uni-id

  opQFT : QFT → QFT
  opQFT (ft , q) = (op ft , q)

  op≤QFT : ∀ {qft qft'} → qft ≤QFT qft' → (opQFT qft) ≤QFT (opQFT qft')
  op≤QFT (≤QFT-intro q-≤ ft-⊑ d-qid) = (≤QFT-intro q-≤ (op⊑ ft-⊑) (opUniId d-qid))

  solve-basesound : ∀ qi a {mi m} → mi ⊑RT m → (a →' mi , qi) ≤QFT ((a ++ (qi *Q dl mi m)) →' m , qi)
  solve-basesound bi a {mi} {m} mi⊑m = ≤QFT-intro ≤QT-refl (→'⊑→' ((++RT⊑ a []) →' mi⊑m)) tt
  solve-basesound uni a {mi} {m} mi⊑m = ≤QFT-intro ≤QT-refl (→'⊑→' (((++RT⊑ a (uni *Q dl mi m)) →' mi⊑m))) (⊑≡dl mi⊑m)

  infer-basesound : BaseSoundness infer
  infer-basesound [] C = exists []
  infer-basesound (i ∷ is) C
    with infer i C  | infer-basesound i C |  infer is C | infer-basesound is C
  ... | err e | _ | _ | _ = maybe-not e
  ... | ok _ | _ | err e' | _ = maybe-not e'
  ... | ok (a →' mi , qi) | exists si | ok (mis →' r , qis) | exists sis
    with mi ⊔RT mis | ⊔RT-with-proof mi mis | proof-refines-⊔RT mi mis
  ... | nothing | _ | _ = maybe-not value-type-error
  ... | just .m | inj₁ (m ,  mk-lub (mk-ub mi⊑m mis⊑m) m-is-lub) | refl
    = exists (sub (solve-basesound qi a mi⊑m) (base si) ∷ (sub (op≤QFT (solve-basesound qis r mis⊑m)) (base sis)))

  infer-basesound (atm (cons t n)) C = exists (atm (cons t))
  infer-basesound (atm (add t)) C =  exists (atm (add t))
  infer-basesound (atm (store t)) C =  exists (atm (store t))
  infer-basesound (atm (load t)) C =  exists (atm (load t))
  infer-basesound (atm (br ℓ)) C
    with ℓ <? length C
  ... | no _ =  (maybe-not no-branch-target)
  ... | yes ℓ<
    = ( (exists (br-refl ℓ<)))
  infer-basesound (atm (brif ℓ)) C
    with ℓ <? length C
  ... | no _ =  (maybe-not no-branch-target)
  ... | yes ℓ<
    =  (exists (atm (brif-refl ℓ<)))
  infer-basesound (blk (block :' ft) is) C
    with infer is (cod ft ∷ C) | infer-basesound is (cod ft ∷ C)
  ... | err e | _ =  (maybe-not e)
  ... | ok qft' | exists tis
    with qft' ≤?QFT (ft , uni)
  ... | no _ = (maybe-not annotation-mismatch)
  ... | yes qft'≤uft
    = exists (blk ft (block (sub (qft'≤uft) (base tis))))
  infer-basesound (blk (loop :' ft) is) C
    with infer is (dom ft ∷ C) | infer-basesound is (dom ft ∷ C)
  ... | err e | _ = (maybe-not e)
  ... | ok qft' | exists tis
    with qft' ≤?QFT (ft , uni)
  ... | no _ = (maybe-not annotation-mismatch)
  ... | yes qft'≤uft
    = (exists (blk ft (loop (sub (qft'≤uft) (base tis)))))

  _≡∘⊑_ : ∀ {p' p q} → p' ≡ p → p ⊑RT q → p' ⊑RT q
  refl ≡∘⊑ leq = leq

  _⊑∘≡_ : ∀ {p q q'} → p ⊑RT q → q ≡ q' →  p ⊑RT q'
  leq ⊑∘≡ refl = leq

  ⊑diff⇒++⊑² : ∀ {ft ft' d} → (p : ft' ⊑FT ft) → d ⊑FT diff-⊑FT p → (ft' ++² d) ⊑FT ft
  ⊑diff⇒++⊑² {ft} {ft'} {d} ((da , a++da=a') →' (dr , r++dr=r')) ((dpa , refl) →' (dpr , refl))
    = (dpa , (++-assoc (dom ft') (dom d) dpa ⟨ ≡.trans ⟩ a++da=a')) →' (dpr , (++-assoc (cod ft') (cod d) dpr ⟨ ≡.trans ⟩ r++dr=r'))


  ⊑diff⇒++⊑ : ∀ {a b d} → (p : a ⊑RT b) → d ⊑RT proj₁ p → (a ++ d) ⊑RT b
  ⊑diff⇒++⊑ {a} {b} {d} (b-a , a++[b-a]≡b) ([b-a]-d , d++[[b-a]-d]≡[b-a]) =
    ([b-a]-d , ( ++-assoc a d _ ⟨ ≡.trans ⟩ ≡.cong (\r → a ++ r) d++[[b-a]-d]≡[b-a] ⟨ ≡.trans ⟩ a++[b-a]≡b))

  diff-⊑diff⇒++⊑≡ : ∀ {a b d} p r → proj₁ (⊑diff⇒++⊑ {a} {b} {d} p r) ≡ proj₁ r
  diff-⊑diff⇒++⊑≡ p r = refl

  trans-⊑-diff : ∀{m' m0 m} → (m0-m' : m' ⊑RT m0) → (m-m' : m' ⊑RT m) →  (m-m0 : m0 ⊑RT m) → proj₁ m0-m' ⊑RT proj₁ m-m'
  trans-⊑-diff {m'} {m0} {m} (m0-m' , m'+[m0-m']) (m-m' , m'+[m-m']) (m-m0 , m0+[m-m0])
    = m-m0 , ++-cancelˡ m' (≡.sym (++-assoc m' m0-m' m-m0) ⟨ ≡.trans ⟩  ≡.cong (\ d → d ++ m-m0) m'+[m0-m'] ⟨ ≡.trans ⟩ m0+[m-m0] ⟨ ≡.trans ⟩ ≡.sym m'+[m-m'])

  common-prefix-⊑⇒⊑ : ∀ {m m' m''} →  (m''⊑m' : m'' ⊑RT m') →  (m''⊑m : m'' ⊑RT m) → (m'⊑m : m' ⊑RT m) →  proj₁ m''⊑m' ⊑RT proj₁ m''⊑m
  common-prefix-⊑⇒⊑  (d' , refl) (d , refl) (d'' , p) = d'' , ++-cancelˡ _ (≡.sym (++-assoc _ d' d'') ⟨ ≡.trans ⟩ p)

  proj₁-common-prefix-⊑⇒⊑≡ : ∀ {m m' m''} → (m''⊑m' : m'' ⊑RT m') → (m''⊑m : m'' ⊑RT m) → (m'⊑m : m' ⊑RT m) →  proj₁ (common-prefix-⊑⇒⊑ m''⊑m' m''⊑m m'⊑m) ≡ proj₁ m'⊑m
  proj₁-common-prefix-⊑⇒⊑≡ (_ , refl) (_ , refl) _ = refl

  diff-⊑RT-refl≡[] : ∀ {rt rt'} (p : rt ≡ rt') → proj₁ (⊑RT-reflexive p) ≡ []
  diff-⊑RT-refl≡[] refl = refl

  ok≤ok⇒≤QFT : ∀ {qft qft'} → ok qft ≤RQFT ok qft' → qft ≤QFT qft'
  ok≤ok⇒≤QFT (ok≤ok x) = x
  open QP-≤QFT

  q-lemma : ∀ {t0 m' t m m0} q → (tm-t0m' : (t0 →' m') ⊑FT (t →' m)) → QId q (diff-⊑FT tm-t0m') → m' ⊑RT m0 → m0 ⊑RT m → (q *Q dl m' m0) ⊑RT (proj₁ (dom-⊑ tm-t0m'))
  q-lemma bi tm-t0m' q[t-t0≡m-m'] m0-m' m-m0 = []⊑RT _
  q-lemma uni tm-t0m' q[t-t0≡m-m'] m0-m' m-m0 = ⊑RT-reflexive (⊑≡dl m0-m') ⟨ ⊑RT-trans ⟩  trans-⊑-diff  m0-m' (cod-⊑ tm-t0m') m-m0  ⟨ ⊑RT-trans ⟩ ⊑RT-reflexive (≡.sym (q[t-t0≡m-m'] _))

  q-lemma-diff : ∀ {t0 m' t m m0} q tm-t0m' q[t-t0≡m-m'] m0-m' m-m0 → QId q (proj₁ (q-lemma {t0} {m'} {t} {m} {m0} q tm-t0m' q[t-t0≡m-m'] m0-m' m-m0) →' proj₁ m-m0)
  q-lemma-diff uni tm-t0m' q[t-t0≡m-m'] m0-m' m-m0 qv
      rewrite (diff-⊑RT-refl≡[] (⊑≡dl m0-m'))
      rewrite (diff-⊑RT-refl≡[] (≡.sym (q[t-t0≡m-m'] tt)))
      =  ++-identityʳ _
  open import OperationalSemantics
  open import TypeCast
  open IsUpperBound
  open IsLeastUpperBound


  abstract
    solve-seq-completeness : ∀ {a r a0 r0 mi mis m0 m qi qis}
      → (am-a0mi : (a0 →' mi) ⊑FT (a →' m))
      → QId qi (diff-⊑FT am-a0mi)
      → (mr-misr0 : (mis →' r0) ⊑FT (m →' r))
      → QId qis (diff-⊑FT mr-misr0)
      → IsLeastUpperBound _⊑RT_ mi mis m0
      →  Σ (Arrow ((a0 ++ qi *Q dl mi m0) ⊑RT a) ((r0 ++ qis *Q dl mis m0) ⊑RT r)) \ (⊑a →' ⊑r) → QId (qi ⊓QT qis) (proj₁ ⊑a →' proj₁ ⊑r)
    solve-seq-completeness {m = m} {qi} {qis} am-a0mi id-am-a0mi mr-misr0 id-mr-misr0 (mk-lub (mk-ub m0-mi m0-mis) m0-least) =
      let   a-a0 = dom (⊑→'⊑ am-a0mi)
            r-r0 = cod (⊑→'⊑ mr-misr0)
            m-mi = cod (⊑→'⊑ am-a0mi)
            m-mis = dom (⊑→'⊑ mr-misr0)
            m-m0 = m0-least m (mk-ub m-mi m-mis)
            qi-l = ⊑diff⇒++⊑ a-a0 (q-lemma qi am-a0mi id-am-a0mi m0-mi m-m0)
            qis-l = ⊑diff⇒++⊑ r-r0 ((q-lemma qis (op⊑ mr-misr0) (opQId id-mr-misr0) m0-mis m-m0))
            qi-dif = q-lemma-diff qi am-a0mi id-am-a0mi m0-mi m-m0
            qis-dif = q-lemma-diff qis (op⊑ mr-misr0) (opQId id-mr-misr0) m0-mis m-m0
            castQT-qi = (castQT (qi ⊓QT qis) qi (proj₁ (⊓QT-glb qi qis)))
            castQT-qis = (castQT (qi ⊓QT qis) qis (proj₂ (⊓QT-glb qi qis)))
      in qi-l →' qis-l , \qv → qi-dif (castQT-qi qv) ⟨ ≡.trans ⟩ ≡.sym (qis-dif (castQT-qis qv))

    solve-completeness : ∀ {a r a0 r0 mi mis m0 m qi0 qis0 qi qis}
      → (a0 →' mi , qi0) ≤QFT (a →' m , qi)
      → (mis →' r0 , qis0) ≤QFT (m →' r , qis)
      → IsLeastUpperBound _⊑RT_ mi mis m0
      → (((a0 →' r0) ++² ((qi0 *Q dl mi m0) →' (qis0 *Q dl mis m0))) , (qi0 ⊓QT qis0)) ≤QFT (a →' r , (qi ⊓QT qis))
    solve-completeness {m0 = m0} {m = m} {qi0 = qi0} {qis0 = qis0}
      (≤QFT-intro qi0≤qi (a0⊑a →' mi⊑m) qid-i)
      (≤QFT-intro qis0≤qis (mis⊑m →' r0⊑r) qid-is) m0-lub
      =
      let m0⊑m = least m0-lub m (mk-ub mi⊑m mis⊑m)
          mi⊑m0 = ≤-l (ub m0-lub)
          mis⊑m0 = ≤-r (ub m0-lub)
      in ≤QFT-intro
        (⊓QT-mono qi0≤qi qis0≤qis)
        (⊑diff⇒++⊑ a0⊑a (q-lemma qi0 (a0⊑a →' mi⊑m) (UniId⇒QId qid-i) mi⊑m0 m0⊑m) →' (⊑diff⇒++⊑ r0⊑r (q-lemma qis0 (op⊑ (mis⊑m →' r0⊑r)) (opQId (UniId⇒QId qid-is)) mis⊑m0 m0⊑m)))
        (QId⇒UniId \ qv → q-lemma-diff qi0 (a0⊑a →' mi⊑m) (UniId⇒QId (qid-i)) mi⊑m0 m0⊑m (castQT _ _ (proj₁ (⊓QT-glb qi0 qis0)) qv) ⟨ ≡.trans ⟩  ≡.sym (q-lemma-diff qis0 (op⊑ (mis⊑m →' r0⊑r)) (opQId (UniId⇒QId (qid-is))) mis⊑m0 m0⊑m (castQT _ _ (proj₂ (⊓QT-glb qi0 qis0)) qv)))
  infer-complete-exists : ∀{k} (c : Code k) C t (tc : C ⊢ c :' t) → infer c C ≤RQFT (ok t)
  infer-complete-exists c C t (sub t0≤t tc) = ≤RQFT-trans (infer-complete-exists c C _ tc) (ok≤ok t0≤t)
  infer-complete-exists (atm .(cons t _)) C .([] →' (t ∷ []) , uni) (base (atm (cons t))) = ≤RQFT-refl
  infer-complete-exists (atm .(add t)) C .((t ∷ t ∷ []) →' (t ∷ []) , uni) (base (atm (add t))) = ≤RQFT-refl
  infer-complete-exists (atm .(store t)) C .((i32 ∷ t ∷ []) →' [] , uni) (base (atm (store t))) = ≤RQFT-refl
  infer-complete-exists (atm .(load t)) C .((i32 ∷ []) →' (t ∷ []) , uni) (base (atm (load t))) = ≤RQFT-refl
  infer-complete-exists (atm (brif-refl ℓ)) C .((i32 ∷ safe-lookup C ℓ<) →' safe-lookup C ℓ< , uni) (base (atm (brif-refl ℓ<)))
    with ℓ <? length C  | dec-yes-irr (ℓ <? length C) ≤-irrelevant ℓ<
  ... | yes ℓ<' | refl
    = ≤RQFT-refl
  infer-complete-exists (atm (br ℓ)) C .(_ →' [] , bi) (base (br-refl ℓ<))
    with ℓ <? length C  | dec-yes-irr (ℓ <? length C) ≤-irrelevant ℓ<
  ... | yes ℓ<' | refl
    = ≤RQFT-refl
  infer-complete-exists (blk (block :' ft) is) C .(ft , uni) (base (blk ft (block tis)))
    with infer is (cod ft ∷ C) | infer-complete-exists is (cod ft ∷ C) (ft , uni) tis
  ... | ok qft | IH
    with qft ≤?QFT (ft , uni) | {dec-yes-irr (qft ≤?QFT (ft , uni)) ≤QFT-irrelevant (ok≤ok⇒≤QFT IH)}
  ... | yes p = ≤RQFT-refl
  infer-complete-exists (blk (loop :' ft) is) C .(ft , uni) (base (blk ft (loop tis)))
    with infer is (dom ft ∷ C) | infer-complete-exists is (dom ft ∷ C) (ft , uni) tis
  ... | ok qft | IH
    with qft ≤?QFT (ft , uni) | {dec-yes-irr (qft ≤?QFT (ft , uni)) ≤QFT-irrelevant (ok≤ok⇒≤QFT IH)}
  ... | yes p = ≤RQFT-refl
  infer-complete-exists .[] C .([] →' [] , uni) (base []) = ≤RQFT-refl
  infer-complete-exists (i ∷ is) C qft (base (_∷_  {a = a} {m = m} {q = qi'}  {r = r} {q' = qis' } ti tis))
    with infer i C | infer-complete-exists i C _ ti | infer is C | infer-complete-exists is C _ tis
  ... | ok (a' →' mi , qi) | ok≤ok (≤QFT-intro qi≤qi' a'→mi⊑a→m qi-di)
      | ok (mis →' r' , qis) | ok≤ok (≤QFT-intro qis≤qis' mis→r'⊑m→r qis-dis)
    with mi ⊔RT mis | ⊔RT-with-proof mi mis | proof-refines-⊔RT mi mis
  ... | nothing | inj₂ noub | refl = ⊥-elim (noub m (mk-ub (cod-⊑ a'→mi⊑a→m) (dom-⊑ mis→r'⊑m→r))) -- contradiction (mi ⊔ mis is undefined implies no upper bounds of mi ans mis but mi⊑m and mis⊑m
  ... | just m' | inj₁ (.m' , m'-lub) | refl
    = ok≤ok (solve-completeness (≤QFT-intro qi≤qi' a'→mi⊑a→m qi-di) (≤QFT-intro qis≤qis' mis→r'⊑m→r qis-dis)  m'-lub)

  infer-complete : Completeness infer
  infer-complete c C .(err e) (maybe-not e) = ≤err e
  infer-complete c C (ok t) (exists tc) = infer-complete-exists c C t tc

infer-sound : Soundness infer
infer-sound = BaseSoundness⇒Soundness infer-basesound

infer-soundsub : SoundnessSub infer
infer-soundsub = Soundness⇒SoundnessSub infer-sound

infer-transform : ∀ {k} {c : Code k} {C t} → Transform c C t
infer-transform = SoundnessSub∧Completeness⇒Transform infer-soundsub infer-complete

infer-transform-canonify : ∀ {k} {c : Code k} {C t} → Canonify c C t infer-transform
infer-transform-canonify {c = c} {C} {t} = BaseSoundness∧Completeness⇒Canonify infer infer-basesound infer-complete c C t

infer-transform-normalise : ∀ {k} {c : Code k} {C t} → Normalise c C t infer-transform
infer-transform-normalise {c = c} {C} {t} = SoundnessSub∧Completeness⇒Normalise infer infer-soundsub infer-complete c C t
