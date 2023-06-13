{-# OPTIONS --without-K --safe #-}
module TypeSystem where

open import Function
open import Data.Bool as Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Nat as Nat using (ℕ ; suc ; zero ; s≤s ; z≤n ; _<_ ; _≤_)
open import Data.Unit
open import Data.Sum renaming ([_,_] to [_,_]Sum)
open import Data.Product
open import Data.Empty
open import Syntax
open import Data.Nat.Properties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.List as L using (List ; [] ; _∷_ ; length)
open import BlockList hiding (length)
open import Data.List.Properties as LProp
open import Data.Vec.Properties
open import Level
open import ListOps

-- open import BlockListProperties
open import Subtype
open import Arrow

module _ where
  open import Data.Maybe
  open import Data.Fin using (fromℕ<)

  dropCtx : ∀ {X : Set} → List X → ℕ → Maybe (X × List X)
  dropCtx [] _ = nothing
  dropCtx (rt ∷ C) zero = just (rt , C)
  dropCtx (rt ∷ C) (suc ℓ) = dropCtx C ℓ

  lookup : ∀ {X : Set} → List X → ℕ → Maybe X
  lookup C ℓ = case dropCtx C ℓ of \ { (just p) → just (proj₁ p) ; nothing → nothing}

  safe-dropCtx : ∀ {ℓ} {X : Set} (C : List X) → (ℓ < length C) → X × List X
  safe-dropCtx {zero} (rt ∷ C) _ = rt , C
  safe-dropCtx {suc ℓ} (rt ∷ C) (s≤s n≤ℓ) = safe-dropCtx C n≤ℓ

  safe-lookup : ∀ {ℓ} {X : Set} (C : List X) → (ℓ < L.length C) → X
  safe-lookup C ℓ< = proj₁ (safe-dropCtx C ℓ<)

  safe-dropCtx-refines-dropCtx : ∀ {X : Set} (C : List X) ℓ (ℓ< : ℓ < length C) → dropCtx C ℓ ≡ just (safe-dropCtx C ℓ<)
  safe-dropCtx-refines-dropCtx (x ∷ C) Nat.zero ℓ< = ≡.refl
  safe-dropCtx-refines-dropCtx (x ∷ C) (Nat.suc ℓ) (s≤s ℓ<) = safe-dropCtx-refines-dropCtx C ℓ ℓ<

private
  variable
    k : Kind
    t : VT
    z z1 z2 : Lit
    C : Ctx
    ℓ : LT
    is is' : Code Seq
    i i' : Code Item
    a m r d e : RT
    l : ℕ
    rss : List RT
    q q' q'' : QT
    ft ft' ft'' : FT
    qft qft' qft0 : QFT

-- judgements and rules for ordinary instructions
data AtmJ : Ctx → Code Item → FT → Set where
  cons : ∀ t → AtmJ C (atm (cons t z)) ([] →' (t ∷ []))
  add : ∀ t → AtmJ C (atm (add t)) ((t ∷ t ∷ []) →' (t ∷ []))
  store : ∀ t → AtmJ C (atm (store t)) ((i32 ∷ t ∷ []) →' [])
  load : ∀ t → AtmJ C (atm (load t)) ((i32 ∷ []) →' (t ∷ []))
  brif : (ℓ< : ℓ Nat.< L.length C) → {- ∀ {rt} → (rt ≡ safe-lookup C ℓ<) → -} AtmJ C (atm (brif ℓ)) ((i32 ∷ safe-lookup C ℓ<) →' safe-lookup C ℓ<)

pattern brif-refl ℓ< = brif ℓ< {- ≡.refl -}

-- judgements and rules for block instructions , parmeterized by type derivations for sequences (it will be substituted by type of whole judgements)
data BlkJ (seqJ : Ctx → Code Seq → FT → Set) : Ctx → Code Item → FT → Set where
  block : seqJ (cod ft ∷ C) is ft → BlkJ seqJ C (blk (block :' ft) is) ft
  loop : seqJ (dom ft ∷ C) is ft → BlkJ seqJ C (blk (loop :' ft) is) ft


module Spec where
  infix 0 _⊢_:'_
  infixl 5 _∷ʳ′_
  data BaseJ : {k : Kind} → Ctx → Code k → FT → Set where
    atm : AtmJ C i ft → BaseJ C i ft
    -- pop : ∀ t → C ⊢ atm pop :' ((t ∷ []) →' [])
    br : (ℓ< : ℓ Nat.< L.length C) →
      ∀ d e → BaseJ C (atm (br ℓ)) ((safe-lookup C ℓ< L.++ d) →' e)
    blk : ∀ ft → BlkJ BaseJ C i ft → BaseJ C i ft
    [] : BaseJ C [] (d →' d)
    _∷ʳ′_ : ∀ d → let (is' , i') = snoc (i , is) in
      BaseJ C is' (a →' (m L.++ d)) → BaseJ C i' (m →' r)
      → BaseJ C (i ∷ is) (a →' (r L.++ d))

  _⊢_:'_ = BaseJ

module Dir' where
  infix 0 _⊢_:'_
  infixl 5 _∷ʳ′_
  data BaseJ : {k : Kind} → Ctx → Code k → FT → Set where
    atm : AtmJ C i ft → ∀ d → BaseJ C i (ft ++¹ d)
    -- pop : ∀ t → ∀ d → C ⊢ atm pop :' ((t ∷ d) →' d)
    br : (ℓ< : ℓ Nat.< L.length C) →
      ∀ d e → BaseJ C (atm (br ℓ)) ((safe-lookup C ℓ< L.++ d) →' e)
    blk : ∀ ft → BlkJ BaseJ C i ft → ∀ d → BaseJ C i (ft ++¹ d)
    [] : BaseJ C [] (d →' d)
    _∷ʳ′_ : let (is' , i') = snoc (i , is) in BaseJ C is' (a →' m) → BaseJ C i' (m →' r) → BaseJ C (i ∷ is) (a →' r)

  _⊢_:'_ = BaseJ
-- Properties of the type systems

module Spec⇔Dir' where -- equivalence in typeability of sequences, and relationship in typeability of instructions between Spec and Dir'
  open Spec
  open Dir'

  Dir'I⇒SpecI : C Dir'.⊢ i :' ft → ∃ \ f' → ∃ \ d → (ft ≡ f' ++¹ d) × (C Spec.⊢ i :' f')
  Dir'S⇒SpecS : C Dir'.⊢ is :' ft → C Spec.⊢ is :' ft

  Dir'I⇒SpecI (atm (cons t) d) = [] →' (t ∷ []) , d , ≡.refl , atm (cons t)
  Dir'I⇒SpecI (atm (add t) d) = (t ∷ t ∷ []) →' (t ∷ []) , d , ≡.refl , atm (add t)
  -- Dir'I⇒SpecI (pop t d) = (t ∷ []) →' [] , d , ≡.refl , pop t
  Dir'I⇒SpecI (atm (store t) d) = (i32 ∷ t ∷ []) →' [] , d , ≡.refl , atm (store t) 
  Dir'I⇒SpecI (atm (load t) d) = (i32 ∷ []) →' (t ∷ []) , d , ≡.refl , atm (load t)
  Dir'I⇒SpecI {C = C} (atm (brif-refl ℓ<) d) = (i32 ∷ safe-lookup C ℓ<) →' safe-lookup C ℓ< , d , ≡.refl , atm (brif-refl ℓ<)
  Dir'I⇒SpecI {C = C} (br ℓ< d e) = let ft = (safe-lookup C ℓ< L.++ d) →' e in ft , [] , (≡.sym $ ++²-identity ft) , br ℓ< d e
  Dir'I⇒SpecI (blk ft (block tis) d) = ft , d , ≡.refl , blk ft (block (Dir'S⇒SpecS tis))
  Dir'I⇒SpecI (blk ft (loop tis) d) = ft , d , ≡.refl , blk ft (loop (Dir'S⇒SpecS tis))
  Dir'S⇒SpecS ([]) = Spec.[]
  Dir'S⇒SpecS (tis Dir'.∷ʳ′ ti) with Dir'I⇒SpecI ti
  ... | ft , d , ≡.refl , ti' = _∷ʳ′_ d (Dir'S⇒SpecS tis) ti'

  SpecI⇒Dir'I : C Spec.⊢ i :' ft → ∀ d → C Dir'.⊢ i :' (ft ++¹ d)
  SpecS⇒Dir'S : C Spec.⊢ is :' ft → C Dir'.⊢ is :' ft
  SpecI⇒Dir'I (atm ti) = atm ti
  -- SpecI⇒Dir'I (pop t) = pop t
  SpecI⇒Dir'I (br {C = C} ℓ< d₁ e) d₂ with Dir'.br {C = C} ℓ< (d₁ L.++ d₂) (e L.++ d₂) | ≡.sym (LProp.++-assoc (safe-lookup C ℓ<) d₁ d₂)
  ... | P | Q rewrite Q = P
  SpecI⇒Dir'I (blk ft (block {C = C} tis)) = blk ft (block {C = C} (SpecS⇒Dir'S tis))
  SpecI⇒Dir'I (blk ft (loop {C = C} tis)) = blk ft (loop {C = C} (SpecS⇒Dir'S tis))
  SpecS⇒Dir'S ([]) = []
  SpecS⇒Dir'S (_∷ʳ′_ d tis ti) =
    let tis' = SpecS⇒Dir'S tis
        ti' = SpecI⇒Dir'I ti
    in tis' ∷ʳ′ ti' d

module Dir where -- cons style typing rules for sequences
  infix 0 _⊢_:'_
  infixr 5 _∷_
  data _⊢_:'_ : {k : Kind} → Ctx → Code k → FT → Set where
    atm : AtmJ C i ft → ∀ d → C ⊢ i :' (ft ++¹ d)
    -- pop : ∀ t → ∀ d → C ⊢ atm pop :' ((t ∷ d) →' d)
    br : (ℓ< : ℓ Nat.< L.length C) → ∀ d e → C ⊢ (atm (br ℓ)) :' ((safe-lookup C ℓ< L.++ d) →' e)
    blk : ∀ ft → BlkJ (_⊢_:'_) C i ft → ∀ d → C ⊢ i :' (ft ++¹ d)
    [] : C ⊢ [] :' (d →' d)
    _∷_ : C ⊢ i :' (a →' m) → C ⊢ is :' (m →' r) → C ⊢ i ∷ is :' (a →' r)

module Dir'⇔Dir where -- 1 to 1 correspondence (every derivation tree correspons to a mirror image of the other's)
  open import Data.Nat.Induction
  open import Data.Nat.Properties
  open Dir'
  open Dir

  module Sublists (i : Code Item) (i' : Code Item) (is : Code Seq) where -- helper module for extracting proper sublists from a list of length 2 or more
    head last : Code Item
    whole tail mid init : Code Seq

    whole = i ∷ i' ∷ is
    head = i
    tail = i' ∷ is
    mid = proj₁ (snoc (i' , is))
    last = proj₂ (snoc (i' , is))
    init = i ∷ mid
    mid∷last≡tail = snoc≡ (i' , is)

    |tail|< : size tail Nat.< size whole
    |tail|< = |xs|<|x∷xs| head tail

    |init|< : size init Nat.< size whole
    |init|< = +-monoʳ-< (size head) (≤-trans (|xs|<|xs∷ʳx| mid last) (≤-reflexive (≡.cong size mid∷last≡tail)))

    |mid|< : size mid Nat.< size whole
    |mid|< = ≤-trans (|xs|<|xs∷ʳx| mid last) (≤-trans (≤-reflexive (≡.cong size mid∷last≡tail)) (<⇒≤ $ |xs|<|x∷xs| head tail))

  -- TODO show inverse relation (1 to 1 correspondence)
  toDir' : ∀ {c : Code k} → {h : Acc Nat._<_ (size c)} → C Dir.⊢ c :' ft → C Dir'.⊢ c :' ft
  fromDir' : ∀ {c : Code k} → {h : Acc Nat._<_ (size c)} → C Dir'.⊢ c :' ft → C Dir.⊢ c :' ft

  toDir' (atm x d) = atm x d
  toDir' (br ℓ< d e) = br ℓ< d e
  -- toDir' (pop t d) = pop t d
  toDir' {c = blk (block :' ft) is} {h = acc rec} (blk ft (block x) d) =
    Dir'.blk ft (block (toDir' {h = rec (size is) ≤-refl} x)) d
  toDir' {c = blk (loop :' ft) is} {h = acc rec} (blk ft (loop x) d) =
    Dir'.blk ft (loop (toDir' {h = rec (size is) ≤-refl} x)) d
  toDir' ([]) = []
  toDir' {c = i ∷ []} {h = h} (ti ∷ [])
    rewrite +-identityʳ (size i)
    = [] ∷ʳ′ toDir' {h = h} ti
  toDir' {c = i ∷ (i' ∷ is)} {h = acc rec} (thead ∷ ttail) -- When we have a sequence c of length 2 or more, c is made by three sub-parts, the first and the last indexAtent, and a list between them. i.e, c = head ∷ mid ∷ʳ last. c includes two proper sublists, tail ( = mid ∷ʳ last) , and init (= head ∷ mid). and we have dervtaions for head and last in Dir.
    with toDir' {h = rec (size tail) |tail|<} ttail -- split a derivation for tail in Dir' into derivations for mid and last in Dir'
      where open Sublists i i' is
  ... | tmid' ∷ʳ′ tlast'
    with fromDir' {h = rec (size mid) |mid|<} tmid' -- turn a derivation for mid in Dir' to derivation for mid in Dir'
      where open Sublists i i' is
  ... | tmid
    with (toDir' {h = rec (size init) |init|<} (thead ∷ tmid)) -- composing the derivations for head and mid in Dir, it cods in a derivation for init in Dir'
      where open Sublists i i' is
  ... | tinit' = tinit' ∷ʳ′ tlast' -- combining the derivations for init and last in Dir' , we get a derivation for the whole sequence in Dir'

  fromDir' (atm ti d) = atm ti d
  fromDir' (br ℓ< d e) = br ℓ< d e
  -- fromDir' (pop t d) = pop t d
  fromDir' {c = blk (block :' f) is} {h = acc rec} (blk ft (block tis') d) =
    blk ft (block (fromDir' {h = rec (size is) ≤-refl} tis')) d
  fromDir' {c = blk (loop :' f) is} {h = acc rec} (blk ft (loop tis') d) =
    blk ft (loop  (fromDir' {h = rec (size is) ≤-refl} tis')) d
  fromDir' ([]) = []
  fromDir' {c = i ∷ []} {h = h} ([] ∷ʳ′  ti')
    rewrite +-identityʳ (size i)
    = fromDir' {h = h} ti' ∷ []
  fromDir' {c = i ∷ i' ∷ is} {h = acc rec} (tinit' ∷ʳ′ tlast') -- reverse the tree manipulation in the proof of toDir'
    with fromDir' {h = rec (size init) |init|<} tinit'
      where open Sublists i i' is
  ... | thead ∷ tmid
    with toDir' {h = rec (size mid) |mid|<} tmid
      where open Sublists i i' is
  ... | tmid'
    with fromDir' {h = rec (size tail) |tail|<} (tmid' ∷ʳ′ tlast')
      where open Sublists i i' is
  ... | ttail = thead ∷ ttail

  -- proof by well-founded induction on a the size of a sequence
  Dir⇒Dir' : ∀ {c : Code k} → C Dir.⊢ c :' ft → C Dir'.⊢ c :' ft
  Dir⇒Dir' {c = c} = toDir' {c = c} {h = <-wellFounded (size c)}
  Dir'⇒Dir : ∀ {c : Code k} → C Dir'.⊢ c :' ft → C Dir.⊢ c :' ft
  Dir'⇒Dir {c = c} = fromDir' {c = c} {h = <-wellFounded (size c)}

record SubJ (CT : Set) (subR : CT → CT → Set) (J : ∀ {k} → Ctx → Code k → CT → Set) {k : Kind} (C : Ctx) (c : Code k) (t : CT) : Set where
  constructor sub!
  field
    {t0} : CT
    t0≤t : subR t0 t
    tc : J C c t0

module Sub where

  data BaseJ (J : ∀ {k} → Ctx → Code k → QFT → Set) : {k : Kind} → Ctx → Code k → QFT → Set where
    -- ordinary instructions get uni-qualified principal types
    atm : AtmJ C i ft → BaseJ J C i (ft , uni)
    -- pop instruction
    -- pop : C ⊢ atm pop :' ((t ∷ []) →' [] , uni)
    -- branch instructions get bi-qualified principal types
    br : (ℓ< : ℓ Nat.< L.length C) {- → ∀ {rt} → rt ≡ safe-lookup C ℓ< -}
      → BaseJ J C (atm (br ℓ)) (safe-lookup C ℓ< →' [] , bi)
    -- block instructions get uni-qualified principal types
    blk : ∀ ft → BlkJ (\ C is ft → J C is (ft , uni)) C i ft → BaseJ J C i (ft , uni)
    -- an empty sequence gets a uni-qualified principal type
    [] : BaseJ J C [] ([] →' [] , uni)
    -- each sequencing gets a type if the post-type of its pre-instruction coincides the pre-type of its post sequence
    _∷_ : J C i (a →' m , q) → J C is (m →' r , q') → BaseJ J C (i ∷ is) (a →' r , q ⊓QT q')

  data SubBaseJ : {k : Kind} → Ctx → Code k → QFT → Set where
    base : {c : Code k} → BaseJ SubBaseJ C c qft → SubBaseJ C c qft
    subJ : {c : Code k} → SubJ QFT _≤QFT_ SubBaseJ C c qft → SubBaseJ C c qft

  pattern sub {t0} tr tc = subJ (sub! {t0 = t0} tr tc)

  _⊢_:'_ = SubBaseJ
  _⊢[base]_:'_ = BaseJ SubBaseJ

  pattern br-refl ℓ< = br ℓ<
  pattern _∷[_,_,_]_ ti qi m qis tis = _∷_ {m = m} {q = qi} {q' = qis} ti tis

module Dir⇔Sub where
  open Dir
  open Sub


  -- Dir⇒Sub-lift is a property of function type ft and code c
  -- if ft is a valid type for c in Dir, then (liftQFT ft) is a valid type for c in Sub
  Dir⇒Sub-lift : {c : Code k} → C Dir.⊢ c :' ft → C Sub.⊢ c :' (ft , uni)
  Dir⇒Sub-lift (atm {ft = ft} x d) = sub (mkuni≤ d d) (base (atm x))

  -- Dir⇒Sub-lift (pop t d) = sub (mkuni≤  d) pop
  Dir⇒Sub-lift {C = C} (br ℓ< d e) = sub (mkbi≤ d e) (base (br-refl ℓ<))
  Dir⇒Sub-lift (blk ft (block x) d) = sub (mkuni≤ d d) (base (blk ft (block (Dir⇒Sub-lift x))))
  Dir⇒Sub-lift (blk ft (loop x) d) = sub (mkuni≤ d d) (base (blk ft (loop (Dir⇒Sub-lift x))))
  Dir⇒Sub-lift ([] {d = d}) = (sub (mkuni≤ d d) (base []))
  Dir⇒Sub-lift (ti ∷ tis) = base (Dir⇒Sub-lift ti ∷ Dir⇒Sub-lift tis)

  -- Sub⇒≤Dir is a property of function type ft and code c
  -- if qft is a valid type for c in Sub, then every type ft s.t. qft ≤ (liftQFT ft) is valid type for c in Dir
  Sub⇒≤Dir : {c : Code k} → C Sub.⊢ c :' qft → qft ≤QFT (ft , uni) → C Dir.⊢ c :' ft
  Sub⇒≤Dir (base (atm ti)) (mkuni≤ d d) = atm ti d
  Sub⇒≤Dir (base (br-refl ℓ<)) (mkbi≤ d e) = br ℓ< d e
  Sub⇒≤Dir (base (blk ft' (block tis))) (mkuni≤ d d) = blk ft' (block (Sub⇒≤Dir tis ≤QFT-refl)) d
  Sub⇒≤Dir (base (blk ft' (loop tis))) (mkuni≤ d d) = blk ft' (loop (Sub⇒≤Dir tis ≤QFT-refl)) d
  Sub⇒≤Dir (base []) (mkuni≤ d d) = []
  Sub⇒≤Dir (base (_∷_ {q = bi} {q' = bi} ti tis)) (mkbi≤ d e) =
    Sub⇒≤Dir ti (mkbi≤ d []) ∷ Sub⇒≤Dir tis (mkbi≤ [] e)
  Sub⇒≤Dir (base (_∷_ {q = bi} {q' = uni} ti tis)) (mkbi≤ d e) =
    Sub⇒≤Dir ti (mkbi≤ d e) ∷ Sub⇒≤Dir tis (mkuni≤ e e)
  Sub⇒≤Dir (base (_∷_ {q = uni} {q' = bi} ti tis)) (mkbi≤ d e) =
    Sub⇒≤Dir ti (mkuni≤ d d) ∷ Sub⇒≤Dir tis (mkbi≤ d e)
  Sub⇒≤Dir (base (_∷_ {q = uni} {q' = uni} ti tis)) (mkuni≤ d d) =
    Sub⇒≤Dir ti (mkuni≤ d d) ∷ Sub⇒≤Dir tis (mkuni≤ d d)
  Sub⇒≤Dir (sub qft≤qft' tc) qft'≤qft'' = Sub⇒≤Dir tc (≤QFT-trans qft≤qft' qft'≤qft'')

  lemma-bitype : ∀ {c : Code k} {C a a' r r'} d
    → (a' ≡ a L.++ d)
    → (C Dir.⊢ c :' a →' r)
    → (C Dir.⊢ c :' a' →' r')
    → (C Sub.⊢ c :' (a →' r , bi)) ⊎ (r' ≡ (r L.++ d))
  lemma-bitype {c = atm (cons t n)} d a'≡a++d (atm (cons .t) d₁) (atm (cons .t) d₂) = inj₂ (≡.cong ((t ∷ []) L.++_) a'≡a++d)
  lemma-bitype {c = atm (add t)} d a'≡a++d (atm (add .t) d₁) (atm (add .t) d₂) = inj₂ (≡.cong (L.drop 1) a'≡a++d)
  -- lemma-bitype {c = atm pop} d a'≡a++d (pop t _) (pop t' _) = inj₂ (≡.cong (L.drop 1) a'≡a++d)
  lemma-bitype {c = atm (store t)} d a'≡a++d (atm (store .t) d₁) (atm (store .t) d₂) = inj₂ (≡.cong (L.drop 2) a'≡a++d)
  lemma-bitype {c = atm (load t)} d a'≡a++d (atm (load .t) d₁) (atm (load .t) d₂) = inj₂ (≡.cong (((t ∷ []) L.++_) ∘ L.drop 1) a'≡a++d)
  lemma-bitype {c = atm (br ℓ)} d a'≡a++d (br ℓ< d₁ e₁) (br ℓ<₁ d₂ e₂) = inj₁ (sub (mkbi≤ d₁ e₁ {q = bi} ) (base (br-refl ℓ<)))
  lemma-bitype {c = atm (brif ℓ)} d a'≡a++d (atm (brif-refl ℓ<) d₁) (atm (brif-refl ℓ<₁) d₂) = inj₂ (≡.cong (L.drop 1) a'≡a++d)
  lemma-bitype {c = blk (block :' ft) c} d a'≡a++d (blk .ft (block x) d₁) (blk .ft (block x₁) d₂)
    rewrite LProp.++-assoc (cod ft) d₁ d | LProp.++-assoc (dom ft) d₁ d
    = inj₂ (≡.cong (cod ft L.++_) (LProp.++-cancelˡ (dom ft) a'≡a++d))
  lemma-bitype {c = blk (loop :' ft) c} d a'≡a++d (blk .ft (loop x) d₁) (blk .ft (loop x₁) d₂)
    rewrite LProp.++-assoc (cod ft) d₁ d | LProp.++-assoc (dom ft) d₁ d
    = inj₂ (≡.cong (cod ft L.++_) (LProp.++-cancelˡ (dom ft) a'≡a++d))
  lemma-bitype {c = []} d a'≡a++d [] [] = inj₂ a'≡a++d
  lemma-bitype {c = i ∷ is} d a'≡a++d (ti ∷ tis) (ti' ∷ tis') with lemma-bitype d a'≡a++d ti ti'
  ... | inj₁ tisub =  inj₁ $ base (tisub ∷ Dir⇒Sub-lift tis)
  ... | inj₂ m'≡m++d with lemma-bitype d m'≡m++d tis tis'
  ... | inj₁ tissub = inj₁ $ base (Dir⇒Sub-lift ti ∷ tissub)
  ... | inj₂ r'≡r++d = inj₂ r'≡r++d

  -- liftQFT makes uni qualified type
  -- A property of qft and c, if every type ft s.t. qft ≤ (liftQFT ft) is valid type for c in Dir, then qft is a valid for c in Sub
  ≤Dir⇒Sub : {c : Code k} → {C : Ctx} → (∀ ft → qft ≤QFT' (ft , uni) → C Dir.⊢ c :' ft) → C Sub.⊢ c :' qft
  ≤Dir⇒Sub {qft = ft , uni} ≤Dir = Dir⇒Sub-lift (≤Dir ft ≤QFT'-refl)
  ≤Dir⇒Sub {qft = (a →' r) , bi} {c = c} {C = C} ≤Dir with lemma-bitype {c = c} {C = C} (i32 ∷ []) ≡.refl p₁ p₂
    where  p₁ = ≤Dir (a →' r) ≤QFT'-unirefl
           p₂ = ≤Dir ((a →' r) ++² ((i32 ∷ []) →' [])) (mkbi≤ (i32 ∷ []) [])
  ... | inj₁ tissub = tissub
  ... | inj₂ r++i32≡r = case LProp.++-cancelˡ r r++i32≡r of \()
