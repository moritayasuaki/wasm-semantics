{-# OPTIONS --without-K --safe #-}
module Subtype where

open import Syntax
open import Function

open import Data.Bool as B using (Bool ; true ; false)
open import Data.Nat as N using (ℕ ; zero ; suc ; z≤n ; s≤s)
open import Relation.Unary as UR
open import Relation.Binary as BR
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl)
open import Relation.Binary.Definitions
open import Data.Unit as Unit using (⊤ ; tt)
open import Data.Empty
open import Data.Product using (_×_ ; _,_ ; ∃ ; proj₁ ; proj₂ ; Σ)
open import Data.List as L using (List ;  _∷_ ; [] ; _++_)
open import Data.Vec using (Vec ; _∷_ ; []) renaming (_++_ to _++V_ ; length to lengthV)
open import Data.Sum
import Level
open import Data.List.Properties
open import Data.List.Relation.Binary.Pointwise as LP using (Pointwise ; [] ; _∷_)
open import Relation.Nullary
open import Data.Maybe using (Maybe ; just ; nothing ; maybe ; decToMaybe)
import Relation.Nullary.Decidable as Dec
open import Axiom.UniquenessOfIdentityProofs
open import Syntax
open import Arrow
open import Data.Bool as B
open import ListOps

data QT : Set where
  bi uni : QT

_≟QT_ : DecidableEquality QT
bi ≟QT bi = yes refl
bi ≟QT uni = no \()
uni ≟QT bi = no \()
uni ≟QT uni = yes refl

uipQT : UIP QT
uipQT = Decidable⇒UIP.≡-irrelevant _≟QT_

QRT : Set
QRT = RT × QT

data _≤QT_ : Rel QT Level.zero where
  bi≤q : ∀ {q} → bi ≤QT q
  uni≤uni : uni ≤QT uni

QFT : Set
QFT = FT × QT

_≟QFT_ : DecidableEquality QFT
_≟QFT_ = Product.≡-dec _≟FT_ _≟QT_
  where open import Data.Product.Properties as Product

uipQFT : UIP QFT
uipQFT = Decidable⇒UIP.≡-irrelevant _≟QFT_

module _ where

  ≤QT-refl : Reflexive _≤QT_
  ≤QT-refl {bi} = bi≤q
  ≤QT-refl {uni} = uni≤uni

  ≤QT-reflexive : _≡_ BR.⇒ _≤QT_
  ≤QT-reflexive ≡.refl = ≤QT-refl

  _≤?QT_ : BR.Decidable _≤QT_
  bi ≤?QT q = yes bi≤q
  uni ≤?QT bi = no \ ()
  uni ≤?QT uni = yes uni≤uni

  ≤QT-irrelevant : BR.Irrelevant _≤QT_
  ≤QT-irrelevant uni≤uni uni≤uni = ≡.refl
  ≤QT-irrelevant bi≤q bi≤q = ≡.refl

  ≤QT-trans : Transitive _≤QT_
  ≤QT-trans uni≤uni uni≤uni = uni≤uni
  ≤QT-trans bi≤q _ = bi≤q

  ≤QT-antisym : Antisymmetric _≡_ _≤QT_
  ≤QT-antisym bi≤q bi≤q = refl
  ≤QT-antisym uni≤uni uni≤uni = refl

  q≤uni : ∀ {q} → q ≤QT uni
  q≤uni {bi} = bi≤q
  q≤uni {uni} = uni≤uni

_⊓QT_ : QT → QT → QT
bi ⊓QT q' = bi
uni ⊓QT q' = q'

IdType : FT → Set
IdType = Balanced _≡_


projRT : ∀ {ft} → IdType ft → Σ _ \ rt → dom ft ≡ rt × rt ≡ cod ft
projRT {a →' .a} refl = a , refl , refl

module _ where
  private
    variable
      q q' : QT
      ft ft' : FT
      vt vt' : VT

  semQT : QT → Set
  semQT bi = ⊥
  semQT uni = ⊤


  NT : QT → RT → RT → Set
  NT uni d e = d ≡ e
  NT bi _ _ = ⊤

  syntax NT q d e = d ≡[ q ] e

  nt : ∀ {q d e} → d ≡[ q ] e → semQT q → d ≡ e
  nt {bi} _ ()
  nt {uni} eq _ = eq

  !nt : ∀ {q d e} → (semQT q → d ≡ e) → d ≡[ q ] e
  !nt {bi} _ = _
  !nt {uni} qeq = qeq _

  !nt-nt=id : ∀ {d e} → (qeq : d ≡[ q ] e) → (!nt ∘ nt) qeq ≡ qeq
  !nt-nt=id {bi} qeq = refl
  !nt-nt=id {uni} qeq = refl

  UniId : QT → FT → Set
  UniId uni ft = IdType ft
  UniId bi ft = ⊤

  QId : QT → FT → Set
  QId q ft = semQT q → IdType ft

  UniId⇒QId : ∀ {q ft} → UniId q ft → QId q ft
  UniId⇒QId {bi} {ft} _ = \()
  UniId⇒QId {uni} {ft} = const

  QId⇒UniId : ∀ {q ft} → QId q ft → UniId q ft
  QId⇒UniId {bi} {ft} = const tt
  QId⇒UniId {uni} {ft} = \ p → p tt

  UniId-irrelevant : BR.Irrelevant UniId
  UniId-irrelevant {bi} a b = ≡.refl
  UniId-irrelevant {uni} a b = uipRT a b

  QIdF : ∀ {q ft} → QId q ft → QId q ft
  QIdF = UniId⇒QId ∘ QId⇒UniId

  abstract
    QIdF-constant : ∀ {q ft} → (qid qid' : QId q ft) → QIdF qid ≡ QIdF qid'
    QIdF-constant {q} {ft} qid qid' rewrite UniId-irrelevant (QId⇒UniId qid') (QId⇒UniId qid) = refl

  UniId-id : ∀ {ft q} → IdType ft → UniId q ft
  UniId-id {q = bi} idft = tt
  UniId-id {q = uni} idft  = idft

  castQT' : ∀ {q q'} → (q≤q' : q ≤QT q') → semQT q → semQT q'
  castQT' uni≤uni x = x
{-
  QIdFix-id  : ∀ {ft q} → IdType ft → QIdFix q ft
  QIdFix-id idft = UniId⇒QIdFix (UniId-id idft)
-}
  UniId-cast : q ≤QT q' → UniId q' ft → UniId q ft
  UniId-cast {q' = uni} bi≤q uid = tt
  UniId-cast {q' = bi} bi≤q uid = tt
  UniId-cast uni≤uni uid = uid

  QId-cast : q ≤QT q' → QId q' ft → QId q ft
  QId-cast uni≤uni = id

  UniId-++ : q ≤QT q' → UniId q ft → UniId q' ft' → UniId q (ft ++² ft')
  UniId-++ bi≤q uid uid' = tt
  UniId-++ uni≤uni uid uid' = ≡.cong₂ _++_ uid uid'

  UniId-trans : ∀ {a m r} → q ≤QT q' → UniId q (a →' m) → UniId q' (m →' r) → UniId q (a →' r)
  UniId-trans q≤q' uni-a→m uni-m→r = QId⇒UniId \ qv → UniId⇒QId uni-a→m qv ⟨ ≡.trans ⟩ UniId⇒QId uni-m→r (castQT' q≤q' qv)

  UniRT-trans : ∀ {rt rt' rt'' q''} → q ≤QT q' × UniId q (rt →' rt') → q' ≤QT q'' × UniId q' (rt' →' rt'') → q ≤QT q'' × UniId q (rt →' rt'')
  UniRT-trans (bi≤q , _) (bi≤q , _) = bi≤q , tt
  UniRT-trans (bi≤q , _) (uni≤uni , _) = bi≤q , tt
  UniRT-trans (uni≤uni , rt=rt') (uni≤uni , rt'=rt'') = uni≤uni , ≡.trans rt=rt' rt'=rt''

  _tl≡RT_ : RT → RT → Set
  rt tl≡RT rt' = rt ≡ tl rt rt'

  _⊑RT_ : RT → RT → Set
  rt ⊑RT rt' = Σ RT \ drt → rt ++ drt ≡ rt'

  diff-⊑RT : ∀{m m'} → m ⊑RT m' → RT
  diff-⊑RT = proj₁

  ⊑≡dl : ∀{m' m} → (m⊑m' : m ⊑RT m') → dl m m' ≡ proj₁ m⊑m'
  ⊑≡dl {m'} {m} (d , refl) = dl++ m d


  _tl≡FT_ : FT → FT → Set
  ft tl≡FT ft' = ft ≡ tl² ft ft'

{-
  _⊑FT_ : FT → FT → Set
  ft ⊑FT ft' = Σ FT \ dft → ft ++² dft ≡ ft'
-}
  _⊑FT_ : FT → FT → Set
  ft ⊑FT ft' = Arrow (dom ft ⊑RT dom ft') (cod ft ⊑RT cod ft')

  ⊑≡dl² : ∀{m' m} → (m⊑m' : m ⊑FT m') → dl² m m' ≡ (proj₁ (dom m⊑m') →' proj₁ (cod m⊑m'))
  ⊑≡dl² {m'} {m} ((d , refl) →' (d' , refl)) = dl++² m (d →' d')

  diff-⊑FT : ∀{m m'} → m ⊑FT m' → FT
  diff-⊑FT ((d , ++d=) →' (e , ++e=)) = d →' e

  data _≤QRT'_ : QRT → QRT → Set where
    ≤QRT-intro : ∀ {q q' rt rt'} → q ≤QT q' → UniId q (rt →' rt') → (rt , q) ≤QRT' (rt' , q')

  record _≤QRT_ (qrt : QRT) (qrt' : QRT) : Set where
    constructor ≤QRT-intro
    field
      q≤q' : proj₂ qrt ≤QT proj₂ qrt'
      uni-id : UniId (proj₂ qrt) (proj₁ qrt →' proj₁ qrt')


  data _≤QFT_ : QFT → QFT → Set where
    ≤QFT-intro : ∀{q ft q' ft'} → q ≤QT q' → (ft⊑ft' : ft ⊑FT ft') → UniId q (diff-⊑FT ft⊑ft') → (ft , q) ≤QFT (ft' , q')

  module ≤QFT where
    q-≤ : ∀ {qft qft'} → qft ≤QFT qft' → (proj₂ qft) ≤QT (proj₂ qft')
    q-≤ (≤QFT-intro q _ _) = q

    ft-⊑ : ∀ {qft qft'} → qft ≤QFT qft' → (proj₁ qft) ⊑FT (proj₁ qft')
    ft-⊑ (≤QFT-intro _ f _) = f


record QP-tl≡QFT (QP : QT → FT → Set) (qft : QFT) (qft' : QFT) : Set where
  constructor tl≡QFT-intro
  private
    q = proj₂ qft
    q' = proj₂ qft'
    ft = proj₁ qft
    ft' = proj₁ qft'

  field
    q-≤ : q ≤QT q'
    ft-⊑ : ft tl≡FT ft'

  diff = dl² ft ft'
  field
    d-qid : QP q diff

record QP-≤QFT (QP : QT → FT →  Set) (qft : QFT) (qft' : QFT) : Set where
  constructor ≤QFT-intro
  private
    q = proj₂ qft
    q' = proj₂ qft'
    ft = proj₁ qft
    ft' = proj₁ qft'

  field
    q-≤ : q ≤QT q'
    ft-⊑ : ft ⊑FT ft'

  diff = diff-⊑FT ft-⊑
  field
    d-qid : QP q diff

∷⊑∷⇒≡×⊑ : ∀ {v v' vs vs'} → (v ∷ vs) ⊑RT (v' ∷ vs') → v ≡ v' × vs ⊑RT vs'
∷⊑∷⇒≡×⊑ (d , eq) = let p , q = ≡∷≡ eq in p , (d , q)

≡×⊑⇒∷⊑∷ : ∀ {v v' vs vs'} → v ≡ v' → vs ⊑RT vs' → (v ∷ vs) ⊑RT (v' ∷ vs')
≡×⊑⇒∷⊑∷ p (d , eq) = (d , ≡.cong₂ _∷_ p eq)

[]⊑RT : BR.Minimum _⊑RT_ []
[]⊑RT x = (x , refl)

[]→'[]⊑FT : BR.Minimum _⊑FT_ ([] →' [])
[]→'[]⊑FT (a →' r)  = ((a , refl) →' (r , refl))

tl≡RT⇒⊑RT : ∀ {rt rt'} → rt tl≡RT rt' → rt ⊑RT rt'
tl≡RT⇒⊑RT {[]} {rt'} eq = rt' , refl
tl≡RT⇒⊑RT {vt ∷ rt} {vt' ∷ rt'} eq
  with refl , eq' ← ∷-injective eq
  with vt' , p ← tl≡RT⇒⊑RT eq'
  = vt' , ≡.cong (\rt → vt ∷ rt) p

⊑RT⇒tl≡RT : ∀ {rt rt'} → rt ⊑RT rt' → rt tl≡RT rt'
⊑RT⇒tl≡RT {[]} _ = refl
⊑RT⇒tl≡RT {vt ∷ rt} {vt' ∷ rt'} (drt , rt++drt≡rt')
  with refl , eq' ← ∷-injective rt++drt≡rt'
  = ≡.cong (\rt → vt ∷ rt) (⊑RT⇒tl≡RT {rt} {rt'} (drt , eq'))

tl≡FT⇒⊑FT : ∀ {ft ft'} → ft tl≡FT ft' → ft ⊑FT ft'
tl≡FT⇒⊑FT {ft} {ft'} eq =
  let eql →' eqr = →'-injective eq
      (dl , pl)  = tl≡RT⇒⊑RT eql
      (dr , pr) = tl≡RT⇒⊑RT eqr
  in (dl , pl) →' (dr , pr)

⊑FT⇒tl≡FT : ∀ {ft ft'} → ft ⊑FT ft' → ft tl≡FT ft'
⊑FT⇒tl≡FT {ft} {ft'} ((l , eql) →' (r , eqr)) =
  let pl = ⊑RT⇒tl≡RT (l , eql)
      pr = ⊑RT⇒tl≡RT (r , eqr)
  in ≡.cong₂ _→'_ pl pr

⊑RT-dl : ∀ rt rt' → (p : rt ⊑RT rt') → let drt , _ = p in dl rt rt' ≡ drt
⊑RT-dl rt rt' (drt , p) = ≡.cong (dl rt) (≡.sym p) ⟨ ≡.trans ⟩ dl++ rt drt

⊑FT-dl² : ∀ ft ft' → (p : ft ⊑FT ft') → dl² ft ft' ≡ diff-⊑FT p
⊑FT-dl² (l →' r) (l' →' r') ((dl , pl) →' (dr , pr)) =
  let pl' = ⊑RT-dl l l' (dl , pl)
      pr' = ⊑RT-dl r r' (dr , pr)
  in ≡.cong₂ _→'_ pl' pr'


dom-⊑ : {ft ft' : FT} → ft ⊑FT ft' → dom ft ⊑RT dom ft'
dom-⊑ = dom

cod-⊑ : {ft ft' : FT} → ft ⊑FT ft' → cod ft ⊑RT cod ft'
cod-⊑ = cod

⊑→'⊑ : {ft ft' : FT} → ft ⊑FT ft' → Arrow (dom ft ⊑RT dom ft') (cod ft ⊑RT cod ft')
⊑→'⊑ = id

→'⊑→' : {at at' rt rt' : RT} → Arrow (at ⊑RT at') (rt ⊑RT rt') → (at →' rt) ⊑FT (at' →' rt')
→'⊑→' = id

++-⊑ : (rt : RT) → {rt' rt'' : RT} → rt' ⊑RT rt'' → (rt ++ rt') ⊑RT (rt ++ rt'')
++-⊑ rt (d , ++d≡) = d , (++-assoc rt _ d ⟨ ≡.trans ⟩ ≡.cong (\ xs → rt ++ xs) ++d≡)

++²-⊑ : (ft : FT) → {ft' ft'' : FT} → ft' ⊑FT ft'' → (ft ++² ft') ⊑FT (ft ++² ft'')
++²-⊑ ft ft'⊑ft'' = →'⊑→' (++-⊑ (dom ft) (dom-⊑ ft'⊑ft'') →' ++-⊑ (cod ft) (cod-⊑ ft'⊑ft''))


++-cancel-⊑ : (rt : RT) → {rt' rt'' : RT} → (rt ++ rt') ⊑RT (rt ++ rt'') → rt' ⊑RT rt''
++-cancel-⊑ rt {rt'} {rt''} (d , ++d≡) = (d , ++-cancelˡ rt (≡.sym (++-assoc rt _ d) ⟨ ≡.trans ⟩ ++d≡))


≤QFT⇒tl≡QFT : ∀ {QP qft qft'} → QP-tl≡QFT QP qft qft' → QP-≤QFT QP qft qft'
≤QFT⇒tl≡QFT {QP} {ft , q} {ft' , q'} (tl≡QFT-intro q-≤ ft-⊑ d-qid)
  = ≤QFT-intro q-≤ (tl≡FT⇒⊑FT ft-⊑) (≡.subst (QP q) P d-qid)
    where P = (⊑FT-dl² ft ft') (tl≡FT⇒⊑FT ft-⊑)

tl≡QFT⇒≤QFT : ∀ {QP qft qft'} → QP-≤QFT QP qft qft' → QP-tl≡QFT QP qft qft'
tl≡QFT⇒≤QFT {QP} {ft , q} {ft' , q'} (≤QFT-intro q-≤ ft-⊑' d-qid)
  = tl≡QFT-intro q-≤ (⊑FT⇒tl≡FT ft-⊑') (≡.subst (QP q) P d-qid)
  where P = ≡.sym ((⊑FT-dl² ft ft') ft-⊑')

{-
liftQFT : FT → QFT
liftQFT pft = (pft , uni)
-}

⊑RT-refl : Reflexive _⊑RT_
proj₁ ⊑RT-refl = []
proj₂ (⊑RT-refl {x}) = ++-identityʳ x

⊑RT-reflexive : _≡_ BR.⇒ _⊑RT_
⊑RT-reflexive refl = ⊑RT-refl

⊑FT-refl : Reflexive _⊑FT_
⊑FT-refl = ⊑RT-refl →' ⊑RT-refl


⊑RT-trans : Transitive _⊑RT_
⊑RT-trans (d , eq) (d' , eq') =  d ++ d' , (≡.sym (++-assoc _ d d') ⟨ ≡.trans ⟩  ≡.cong (\r → r ++ d') eq ⟨ ≡.trans ⟩ eq')

⊑RT-irrelevant : BR.Irrelevant _⊑RT_
⊑RT-irrelevant {x} (fst , refl) (fst₁ , snd₁)
  with refl ← ++-cancelˡ x snd₁
  with refl ← uipRT refl snd₁
  = refl

⊑RT-antisym : Antisymmetric _≡_ _⊑RT_
⊑RT-antisym {i = i} (d , refl) (d' , eq')
  with p ← ≡.sym eq' ⟨ ≡.trans ⟩ (++-assoc _ d d')
  with q ← (++-identityʳ-unique i p)
  with refl ← ++-conicalˡ d d' q
  = ≡.sym (++-identityʳ i)

⊑FT-trans : Transitive _⊑FT_
⊑FT-trans (l⊑ →' r⊑) (l⊑' →' r⊑') = ⊑RT-trans l⊑ l⊑' →' ⊑RT-trans r⊑ r⊑'

⊑FT-irrelevant : BR.Irrelevant _⊑FT_
⊑FT-irrelevant {x} (l⊑ →' r⊑) (l⊑' →' r⊑')
  with refl ← ⊑RT-irrelevant l⊑ l⊑'
  with refl ← ⊑RT-irrelevant r⊑ r⊑'
  = refl

Σ≡,≡ : {X : Set} {Y : X → Set} {a b : Σ X Y } → a ≡ b → Σ (proj₁ a ≡ proj₁ b) \ p → ≡.subst Y p (proj₂ a) ≡ (proj₂ b)
Σ≡,≡ refl = refl , refl

×≡,≡ : {X : Set} {Y : Set} {a b : X × Y } → a ≡ b → (proj₁ a ≡ proj₁ b) × (proj₂ a ≡ proj₂ b)
×≡,≡ refl = refl , refl

×,≡, : {X : Set} {Y : Set} {a b : X × Y } → (proj₁ a ≡ proj₁ b) × (proj₂ a ≡ proj₂ b) → a ≡ b
×,≡, (refl , refl) = refl

⊑FT-antisym : Antisymmetric  _≡_ _⊑FT_
⊑FT-antisym {i = i} (r⊑ →' l⊑) (r⊑' →' l⊑')
  = →'≡→' (⊑RT-antisym r⊑ r⊑' →' ⊑RT-antisym l⊑ l⊑')

diff-trans : ∀ {ft ft' ft''} → (p : ft ⊑FT ft') → (q : ft' ⊑FT ft'') → (pq : ft ⊑FT ft'') → diff-⊑FT p ++² diff-⊑FT q ≡ diff-⊑FT pq
diff-trans p q pq with refl ← ⊑FT-irrelevant (⊑FT-trans p q) pq = ≡.refl

≤QRT-refl : Reflexive _≤QRT_
≤QRT-refl = ≤QRT-intro ≤QT-refl (UniId-id ≡.refl)

≤QRT-reflexive : _≡_ BR.⇒ _≤QRT_
≤QRT-reflexive refl = ≤QRT-refl

≤QRT-trans : Transitive _≤QRT_
≤QRT-trans (≤QRT-intro q≤ q-ft-id) (≤QRT-intro q≤' q-ft-id') = ≤QRT-intro (≤QT-trans q≤ q≤') (UniId-trans q≤ q-ft-id q-ft-id')

semQT-irrelevant : ∀ {q} (p p' : semQT q) → p ≡ p'
semQT-irrelevant {uni} p p' = refl

≤QRT-irrelevant : BR.Irrelevant _≤QRT_
≤QRT-irrelevant (≤QRT-intro ≤q qid) (≤QRT-intro ≤q' qid')
  with refl ← ≤QT-irrelevant ≤q ≤q'
  with refl ← UniId-irrelevant qid qid' = refl

≤QFT-refl : Reflexive _≤QFT_
≤QFT-refl = ≤QFT-intro ≤QT-refl ⊑FT-refl (UniId-id ≡.refl)

≤QFT-reflexive : _≡_ BR.⇒ _≤QFT_
≤QFT-reflexive refl = ≤QFT-refl

≤QFT-trans : Transitive _≤QFT_
≤QFT-trans (≤QFT-intro q≤ ft⊑ q-id) (≤QFT-intro q≤' ft⊑' q-id') = ≤QFT-intro (≤QT-trans q≤ q≤') (⊑FT-trans ft⊑ ft⊑') (UniId-++ q≤ q-id q-id')

≤QFT-irrelevant : BR.Irrelevant _≤QFT_
≤QFT-irrelevant (≤QFT-intro ≤q ⊑ft qid) (≤QFT-intro ≤q' ⊑ft' qid')
  with refl ← ≤QT-irrelevant ≤q ≤q'
  with refl ← ⊑FT-irrelevant ⊑ft ⊑ft'
  with refl ← UniId-irrelevant qid qid'
  = refl

_≤QFT'_ = QP-≤QFT UniId

module QP-Props (QP : QT → FT → Set) (QP-id : ∀ {q ft} → IdType ft → QP q ft) (QP-++ : ∀ {q q' ft ft'} → q ≤QT q' → QP q ft → QP q' ft' → QP q (ft ++² ft')) (QP-irr : BR.Irrelevant QP) where

  QP-≤QFT-refl : Reflexive (QP-≤QFT QP)
  QP-≤QFT.q-≤ QP-≤QFT-refl = ≤QT-refl
  QP-≤QFT.ft-⊑ QP-≤QFT-refl = ⊑FT-refl
  QP-≤QFT.d-qid QP-≤QFT-refl = QP-id ≡.refl

  QP-≤QFT-reflexive :  _≡_ BR.⇒ (QP-≤QFT QP)
  QP-≤QFT-reflexive refl = QP-≤QFT-refl

  QP-≤QFT-trans : Transitive (QP-≤QFT QP)
  QP-≤QFT.q-≤ (QP-≤QFT-trans (≤QFT-intro q-≤ ft-⊑ d-qid) (≤QFT-intro q-≤₁ ft-⊑₁ d-qid₁)) = ≤QT-trans q-≤ q-≤₁
  QP-≤QFT.ft-⊑ (QP-≤QFT-trans (≤QFT-intro q-≤ ft-⊑ d-qid) (≤QFT-intro q-≤₁ ft-⊑₁ d-qid₁)) = ⊑FT-trans ft-⊑ ft-⊑₁
  QP-≤QFT.d-qid (QP-≤QFT-trans (≤QFT-intro q-≤ ft-⊑ d-qid) (≤QFT-intro q-≤₁ ft-⊑₁ d-qid₁)) = QP-++ q-≤ d-qid d-qid₁

  QP-≤QFT-irrelevant : BR.Irrelevant (QP-≤QFT QP)
  QP-≤QFT-irrelevant (≤QFT-intro q-≤ ft-⊑ d-qid) (≤QFT-intro q-≤₁ ft-⊑₁ d-qid₁)
    with refl ← ≤QT-irrelevant q-≤ q-≤₁
    with refl ← ⊑FT-irrelevant ft-⊑ ft-⊑₁
    with refl ← QP-irr d-qid d-qid₁
    = refl

  QP-≤QFT-antisym : Antisym (QP-≤QFT QP) (QP-≤QFT QP) _≡_
  QP-≤QFT-antisym {i} {j} (≤QFT-intro q-≤ ft-⊑ d-qid) (≤QFT-intro q-≤₁ ft-⊑₁ d-qid₁)
    with refl ← ⊑FT-antisym ft-⊑ ft-⊑₁
    with refl ← ≤QT-antisym q-≤ q-≤₁
    = refl

  QP-≤QFT-unirefl : ∀ {ft q} → QP-≤QFT QP (ft , q) (ft , uni)
  QP-≤QFT-unirefl {q = uni} = ≤QFT-intro uni≤uni ⊑FT-refl (QP-id ≡.refl)
  QP-≤QFT-unirefl {q = bi} = ≤QFT-intro bi≤q ⊑FT-refl (QP-id ≡.refl)

open QP-Props UniId UniId-id UniId-++ UniId-irrelevant public renaming
  ( QP-≤QFT-refl to ≤QFT'-refl
  ; QP-≤QFT-reflexive to ≤QFT'-reflexive
  ; QP-≤QFT-trans to ≤QFT'-trans
  ; QP-≤QFT-irrelevant to ≤QFT'-irrelevant
  ; QP-≤QFT-antisym to ≤QFT'-antisym
  ; QP-≤QFT-unirefl to ≤QFT'-unirefl
  )

pattern mkbi≤ d e {q} = ≤QFT-intro (bi≤q {q}) ((d , ≡.refl) →' (e , ≡.refl)) tt
pattern mkuni≤ d e = ≤QFT-intro uni≤uni ((d , ≡.refl) →' (e , ≡.refl)) ≡.refl

_≤?QFT'_ : BR.Decidable _≤QFT'_
(ft , q) ≤?QFT' (ft' , q') with ft ≟FT tl² ft ft'
... | no np = no \ p → np  let q = tl≡QFT⇒≤QFT {UniId} p in QP-tl≡QFT.ft-⊑ q
... | yes p with q | q'
... | bi | _ = yes (≤QFT⇒tl≡QFT (tl≡QFT-intro bi≤q p tt)  )
... | uni | bi = no  \()
... | uni | uni with (let d = dl² ft ft' in dom d ≟RT cod d )
... | yes pt = yes (≤QFT⇒tl≡QFT (tl≡QFT-intro {UniId} uni≤uni p pt))
... | no np = no \ x →  case tl≡QFT⇒≤QFT x of \ { (tl≡QFT-intro q-≤ ft-⊑ d-qid) → np d-qid}

_⊑?RT_ : BR.Decidable _⊑RT_
[] ⊑?RT xs = yes (xs , refl)
(_ ∷ _) ⊑?RT [] = no \()
(x ∷ xs) ⊑?RT (y ∷ ys) with x ≟VT y | xs ⊑?RT ys
... | yes p | yes (ds , ++ds=) = yes (ds , ≡.cong₂ _∷_ p ++ds=)
... | yes _ | no nps = no \{ (ds , ++ds=) → nps (ds , proj₂ (≡∷≡ ++ds=)) }
... | no np | _ = no \ { (ds , ++ds=) → np (proj₁ (≡∷≡ ++ds=)) }

_⊑?FT_ : BR.Decidable _⊑FT_
(a →' r) ⊑?FT (a' →' r') with a ⊑?RT a' | r ⊑?RT r'
... | yes a⊑a' | yes r⊑r' = yes (a⊑a' →' r⊑r')
... | yes _ | no np = no \{ (_ →' r⊑r') → np r⊑r' }
... | no np | _ = no \{ (a⊑a' →' _) → np a⊑a'}

_≤QT?_ : BR.Decidable _≤QT_
bi ≤QT? _ = yes bi≤q
uni ≤QT? bi = no \()
uni ≤QT? uni = yes uni≤uni

_≤?QFT_ : BR.Decidable _≤QFT_
(ft , q) ≤?QFT (ft' , q') with ft ⊑?FT ft' | q ≤QT? q'
... | no np | _ = no \{(≤QFT-intro _ ft⊑ft' _) → np ft⊑ft'}
... | yes _ | no np = no \{(≤QFT-intro q≤q' _ _) → np q≤q'}
... | yes ft⊑ft' | yes bi≤q = yes (≤QFT-intro bi≤q ft⊑ft' _)
... | yes ((da , a++da=a') →' (dr , r++dr=r')) | yes uni≤uni with da ≟RT dr
... | yes p = yes (≤QFT-intro uni≤uni ((da , a++da=a') →' (dr , r++dr=r')) p)
... | no np
  = no \{(≤QFT-intro uni≤uni ((da2 , a++da=a'2) →' (dr2 , r++dr=r'2)) refl) → np ( ++-cancelˡ (dom ft) (a++da=a' ⟨ ≡.trans ⟩ ≡.sym a++da=a'2)  ⟨ ≡.trans ⟩ ++-cancelˡ (cod ft) (r++dr=r'2 ⟨ ≡.trans ⟩ ≡.sym r++dr=r'))}
