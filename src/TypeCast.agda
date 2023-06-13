{-# OPTIONS --without-K --safe --auto-inline #-}
module TypeCast where

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
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; refl ; _≗_ ; erefl ; sym ; trans ; cong ; subst ; cong₂)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Nat.Properties
open import Data.Product.Properties
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.List as List using (List ; [] ; _∷_)
open import Data.Nat.Induction
open import Data.Nat
open import Function
open import TypeSystem
open import Syntax
open import BlockList as BList using (BList ; [] ; _∷_ ; atm ; blk ; Kind ; Item ; Seq)
open import Partial
import Level

open import Subtype
open import TypeSystem
open import Arrow
open import ListOps
open import Data.List.Properties
open import Data.List using (_++_ ; length)

-- defnitional equality can be useful for untyped semantics
subst-const-id :
  {I : Set} {i j : I} (i=j : i ≡ j) (X : Set) → subst (const X) i=j ≡ id
subst-const-id refl _  = refl
-- defnitional equality between functions can be useful when rewriting terms without pattern match on argument data types
subst-sym-f-subst :
  {I : Set}
  (S : I → Set)
  (T : I → Set)
  (f : ∀ i → (si : S i) → T i)
  {i j : I} (i=j : i ≡ j)
  → (subst T (sym i=j)) ∘ f j ∘ (subst S i=j) ≡ f i
subst-sym-f-subst S T f refl = refl

module _ where
  open import OperationalSemantics

  nq : QT → QT
  nq uni = bi
  nq bi = uni

  semVT : VT → Set
  semVT vt = mapVT vt

  _≟⟦VT⟧_ : ∀ {vt} → DecidableEquality (semVT vt)
  _≟⟦VT⟧_ {i32} (n , np) (m , mp) with n ≟ m
  ... | yes refl rewrite ≤-irrelevant np mp = yes refl
  ... | no p = no (p ∘ \{ refl → refl})
  _≟⟦VT⟧_ {i64} (n , np) (m , mp) with n ≟ m
  ... | yes refl rewrite ≤-irrelevant np mp = yes refl
  ... | no p = no (p ∘ \{ refl → refl})

  data semRT : RT → Set where
    [] : semRT []
    _∷_ : ∀ {vt rt} → semVT vt → semRT rt → semRT (vt ∷ rt)

  record semCtx (C : Ctx) : Set where
    inductive
    constructor tjump
    field
      {ℓ} : ℕ
      ℓ< : ℓ < length C
      vs : semRT (safe-lookup C ℓ<)

  pattern tbranch v = left v
  pattern tnormal v = right (tt , v)

  -- if [q] is the empty type then the codomain never take tnormal
  TState : Set → Set → Set → Set
  TState [C] [q] [R] = Either [C] ([q] × [R]) × Store

  mapEither : ∀ {L L' R R'} → (L → L') → (R → R') → Either L R → Either L' R'
  mapEither l r (left x) = left (l x)
  mapEither l r (right x) = right (r x)

  liftL : ∀ {L R} → Either ⊥ R → Either L R
  liftL = mapEither (\()) id

  mapR : ∀ {L R R'} → (R → R') → Either L R → Either L R'
  mapR f = mapEither id f

  mapR-id : ∀ {L R} {f : R → R} → f ≗ id → mapR {L} f ≗ id
  mapR-id f-id (tbranch x) = refl
  mapR-id f-id (right x) rewrite f-id x = refl

  mapTState : (X : Set) {Q Q' R R' : Set} → (Q → Q') → (Q → R → R') → TState X Q R → TState X Q' R'
  mapTState X qf rf (r , S) = (mapR (\ qv-vs → (qf (proj₁ qv-vs) , rf (proj₁ qv-vs) (proj₂ qv-vs))) r , S)

  liftTState : (X : Set) {Q R : Set} → TState ⊥ Q R → TState X Q R
  liftTState X (r , S) = liftL r , S

  mapTState-id : ∀ X {Q R} → {qf : Q → Q} → {rf : Q → R → R} → qf ≗ id → (∀ q → rf q ≗ id) → mapTState X qf rf ≗ id
  mapTState-id X {rf = rf} qf-id rf-cid (tbranch x , S) = refl
  mapTState-id X {rf = rf} qf-id rf-cid (right (qv , vs) , S)
    rewrite qf-id qv
    rewrite rf-cid qv vs
    = refl

  mapTState-comp : ∀ X {Q R Q' R' Q'' R''} (qf : Q → Q') (rf : Q → R → R') (qf' : Q' → Q'') (rf' : Q' → R' → R'')
    → (mapTState X qf' rf' ∘ mapTState X qf rf) ≗ mapTState X (qf' ∘ qf) \ q r → let r' = rf q r in let q' = qf q in rf' q' r'
  mapTState-comp X qf rf qf' rf' (tbranch x , S) = refl
  mapTState-comp X qf rf qf' rf' (right (qv , vs) , S)
    = refl

  mapTState-comp' : ∀ X {Q R Q' R' Q'' R''}
    (qf : Q → Q') (qf' : Q' → Q'') (qf'' :  Q → Q'')
    (rf : Q → R → R') (rf' : Q' → R' → R'') (rf'' : Q → R → R'')
    → (qf' ∘ qf ≗ qf'') → (∀ q r → rf' (qf q) (rf q r) ≡ rf'' q r)
    → (mapTState X qf' rf' ∘ mapTState X qf rf) ≗ mapTState X qf'' rf''
  mapTState-comp' X qf qf' qf'' rf rf' rf'' comp-qf comp-rf (tbranch x , S) = refl
  mapTState-comp' X qf qf' qf'' rf rf' rf'' comp-qf comp-rf (right (qv , x) , S)
    = ≡.cong (\p → right  p , S) (×,≡, (comp-qf qv , comp-rf qv x))

  mapTState-cong : ∀ X {Q Q' R R'} (qf qf' : Q → Q') (rf rf' : Q → R → R')
    → (qf ≗ qf') → (∀ q r → rf q r ≡ rf' q r) → mapTState X qf rf ≗ mapTState X qf' rf'
  mapTState-cong X qf qf' rf rf' qf=qf' rf=rf' (tbranch x , S) = refl
  mapTState-cong X qf qf' rf rf' qf=qf' rf=rf' (right (qv , vs) , S) rewrite (erefl tt)
    = cong₂ (\v1 v2 → right (v1 , v2) , S) (qf=qf' qv) (rf=rf' qv vs) 

  mapPartial : ∀ {X Y} → (X → Y) → Partial X → Partial Y
  mapPartial f div = div
  mapPartial f (con x) = con (f x)

  mapPartial-id : ∀ {X} → {f : X → X} → f ≗ id → mapPartial f ≗ id
  mapPartial-id f≡id div = refl
  mapPartial-id f≡id (con x) = ≡.cong con (f≡id x)

  mapPartial-comp : ∀ {X Y Z} → (f : X → Y) → (g : Y → Z) → mapPartial g ∘ mapPartial f ≗ mapPartial (g ∘ f)
  mapPartial-comp f g div = refl
  mapPartial-comp f g (con x) = refl

  mapPartial-comp' : ∀ {X Y Z} → (f : X → Y) → (f' : Y → Z) → (f'' : X → Z) →
    f' ∘ f ≗ f'' → mapPartial f' ∘ mapPartial f ≗ mapPartial f''
  mapPartial-comp' f f' f'' comp-f div = refl
  mapPartial-comp' f f' f'' comp-f (con x) = ≡.cong con (comp-f x)

  mapPartial-cong : ∀ {X Y} → (f g : X → Y) → f ≗ g → mapPartial f ≗ mapPartial g
  mapPartial-cong f g f=g div = refl
  mapPartial-cong f g f=g (con x) = cong con (f=g x)

  semQRT : Set → QRT → Set
  semQRT [C] (rt , q) = TState [C] (semQT q) (semRT rt)


  liftQRT : ∀ {qrt} X → semQRT ⊥ qrt → semQRT X qrt
  liftQRT X = liftTState X

  semQFT : Set → Set → QFT → RT → Set
  semQFT X Y (at →' rt , q) D = semQRT X (at ++ D , uni) → Partial (semQRT Y (rt ++ D , q))


  semQFT-N : Set → QFT → RT → Set
  semQFT-N [C] qft = semQFT ⊥ [C] qft

  semQFT-BN : Set → QFT → RT → Set
  semQFT-BN [C] qft = semQFT [C] [C] qft

  semQFT-N⇒semQFT-BN : ∀ [C] qft D → semQFT-N [C] qft D → semQFT-BN [C] qft D
  semQFT-N⇒semQFT-BN [C] qft D f (tbranch b , S) = con (tbranch b , S)
  semQFT-N⇒semQFT-BN [C] qft D f (right v , S) = f (right v , S)

  ∷-typed : ∀ {vt rt} → semVT vt → semRT rt → semRT (vt ∷ rt)
  ∷-typed tv tvs = tv ∷ tvs

  ++-typed : ∀ {rt rt'} → semRT rt → semRT rt' → semRT (rt ++ rt')
  ++-typed {rt = []} [] tvs = tvs
  ++-typed {rt = vt ∷ rt} (tv ∷ tvs') tvs = tv ∷ ++-typed tvs' tvs

{-
  split-typed : ∀ {rt rt'} → semRT (rt ++ rt') → semRT rt × semRT rt'
  split-typed {[]} tvs = [] , tvs
  split-typed {(vt ∷ rt)} (tv ∷ tvs) = let (tvs' , tvs'') = split-typed tvs in (tv ∷ tvs') , tvs''

  take-typed : ∀ {rt} rt' → semRT (rt ++ rt') → semRT rt
  take-typed {[]} rt' tvs = []
  take-typed {vt ∷ rt} rt' (tv ∷ tvs) = tv ∷ take-typed rt' tvs
  -}


  t∷≡∷ : ∀ {vt} {rt} {tv tv' : semVT vt} {tvs tvs' : semRT rt} → tv ≡ tv' → tvs ≡ tvs' → _≡_ {A = semRT (vt ∷ rt)} (tv ∷ tvs) (tv' ∷ tvs')
  t∷≡∷ refl refl = refl


  safetake : ∀ rt {D} → semRT (rt ++ D) → semRT rt
  safetake [] x = []
  safetake (x₁ ∷ rt) (x ∷ x₂) = x ∷ safetake rt x₂

  safedrop : ∀ rt {D} → semRT (rt ++ D) → semRT D
  safedrop [] x = x
  safedrop (x₁ ∷ G) (x ∷ g) = safedrop G g

  safesplit : ∀ rt {D} → semRT (rt ++ D) → semRT rt × semRT D
  safesplit rt vs = safetake rt vs , safedrop rt vs

  _safe++_ : ∀ {rt rt'} → semRT rt → semRT rt' → semRT (rt ++ rt')
  [] safe++ tvs' = tvs'
  (tv ∷ tvs) safe++ tvs' = tv ∷ (tvs safe++ tvs')

  Cast : (X : Set) (El : X → Set) (R : X → X → Set) → Set
  Cast X El R = (a b : X) → R a b → El a → El b

  Cast-ReflId : ∀ {X El R} → Cast X El R → Reflexive R → Set
  Cast-ReflId cast r = ∀ {x} → cast x x r ≗ id

  Cast-SymInv : ∀ {X El R} → Cast X El R → Symmetric R → Set
  Cast-SymInv {R = R} cast s = ∀ {x y} (p : R x y) → cast y x (s p) ∘ cast x y p ≗ id

  Cast-Antisym : ∀ {X El R} → Cast X El R → Antisymmetric _≡_ R → Set
  Cast-Antisym {R = R} cast as = ∀ {x y} (p : R x y) (q : R y x) → case as p q of \ { refl → cast x y p ≡ cast y x q }

  Cast-TransComp : ∀ {X El R} → Cast X El R → Transitive R → Set
  Cast-TransComp {R = R} cast t = ∀ {x y z} (p : R x y) (q : R y z) → (cast y z) q ∘ (cast x y) p ≗ (cast x z) (t p q)

  Cast-Irrelevant : ∀ {X El R} → Cast X El R → Set
  Cast-Irrelevant {R = R} cast = ∀ {a b} → (r1 r2 : R a b) → cast a b r1 ≡ cast a b r2

  Cast-Id : ∀ {X El R} → Cast X El R → Set
  Cast-Id cast = ∀ {x} p → cast x x p ≗ id

  Cast-Comp : ∀ {X El R} → Cast X El R → Set
  Cast-Comp cast = ∀ {x y z} p q r → cast y z p ∘ cast x y q ≗ cast x z r

  irr⇒irr : ∀ {X El R} → (cast : Cast X El R) → Relation.Binary.Irrelevant R → Cast-Irrelevant cast
  irr⇒irr _ irr r1 r2 rewrite irr r1 r2 = refl
  open import Level
  antisym : {A : Set} → Antisym {A = A} {B = A} {ℓ₁ = Level.zero} {ℓ₂ = Level.zero} {ℓ₃ = Level.zero }  _≡_  _≡_ _≡_
  antisym x _ = x

  ≗-sym : {X Y : Set} {f g : X → Y} → f ≗ g → g ≗ f
  ≗-sym f=g x = sym (f=g x)

  ≗-trans : {X Y : Set} {f g h : X → Y} → f ≗ g → g ≗ h → f ≗ h
  ≗-trans f=g g=h x = trans (f=g x) (g=h x)

  ≗-cong : {X Y Z : Set} {f g : X → Y} (h : Y → Z) → f ≗ g → h ∘ f ≗ h ∘ g
  ≗-cong h f=g x = ≡.cong h (f=g x)

  ≗-≡ : {X Y : Set} {f g : X → Y} {x y : X} → f ≗ g → x ≡ y → f x ≡ g y
  ≗-≡ f=g refl = f=g _

  ≡⇒≗ : {X Y : Set} {f g : X → Y} → f ≡ g → f ≗ g
  ≡⇒≗ refl x = refl

  ≗-∘ : {X Y Z : Set} {f g : X → Y} {h k : Y → Z} → h ≗ k → f ≗ g → h ∘ f ≗ k ∘ g
  ≗-∘ h=k f=g x = ≗-≡ h=k (f=g x)

  castVT : Cast VT semVT _≡_
  castVT r .r refl = id

  castVT-refl-id : Cast-ReflId castVT refl
  castVT-refl-id _ = refl

  castVT-sym-inv : Cast-SymInv castVT sym
  castVT-sym-inv refl x = refl

  castVT-irr : Cast-Irrelevant castVT
  castVT-irr = irr⇒irr castVT uipVT

  castVT-antisym : Cast-Antisym castVT antisym
  castVT-antisym p q
    with refl ← antisym p q
    with refl ← uipVT p refl
    with refl ← uipVT q refl
    = refl

  castVT-trans-comp : Cast-TransComp castVT trans
  castVT-trans-comp refl refl x = refl

  module _ where
    castRT : Cast RT semRT _≡_
    castRT [] [] p [] = []
    castRT (vt ∷ rt) (vt' ∷ rt') pps (v ∷ vs) =
      let p , ps = ≡∷≡ pps
      in castVT vt vt' p v ∷ castRT rt rt' ps vs

    castRT-irr : Cast-Irrelevant castRT
    castRT-irr = irr⇒irr castRT uipRT

    castRT-refl-id : Cast-ReflId castRT refl
    castRT-refl-id [] = refl
    castRT-refl-id (_∷_ v vs) = ≡.cong₂ _∷_ (castVT-refl-id v) (castRT-refl-id vs)

    castRT-id : ∀ {rt : RT} → (p : rt ≡ rt) → castRT _ _ p ≗ id
    castRT-id p with refl ← uipRT p refl = castRT-refl-id

    castRT-sym-inv : Cast-SymInv castRT sym
    castRT-sym-inv refl [] = refl
    castRT-sym-inv refl (v ∷ vs) = ≡.cong (_∷_ v) (castRT-sym-inv refl vs)

    castRT-trans-comp : Cast-TransComp castRT trans
    castRT-trans-comp refl refl [] = refl
    castRT-trans-comp refl refl (v ∷ vs) = ≡.cong (_∷_ v) (castRT-trans-comp refl refl vs)

    castRT-antisym : Cast-Antisym castRT antisym
    castRT-antisym p q
      with refl ← antisym p q
      with refl ← uipRT p refl
      with refl ← uipRT q refl
      = refl

    castRT-subst : ∀ {rt rt'} (p : rt ≡ rt') → castRT _ _ p ≗ ≡.subst semRT p
    castRT-subst {[]} refl [] = refl
    castRT-subst {vt ∷ rt} {vt' ∷ rt'} refl (v ∷ vs) = ≡.cong (_∷_ v) (castRT-subst refl vs)

    castRT-comp : ∀ {i j k} → (ij : i ≡ j) → (jk : j ≡ k) → (ik : i ≡ k) → (v : semRT i) →  castRT _ _ jk (castRT _ _ ij v) ≡ castRT _ _ ik v
    castRT-comp ij jk ik rewrite uipRT ik (trans ij jk) = castRT-trans-comp ij jk

    castRT-inv : ∀ {i j} → (ij : i ≡ j) → (ji : j ≡ i) → (v : semRT i) →  castRT _ _ ji (castRT _ _ ij v) ≡ v
    castRT-inv ij ji v = castRT-comp ij ji ≡.refl v ⟨ ≡.trans ⟩ castRT-refl-id v

  module _ where
    castQT : Cast QT semQT _≤QT_
    castQT _ _ uni≤uni = id

    castQT-implicit : {q q' : QT} → q ≤QT q' → semQT q → semQT q'
    castQT-implicit = castQT _ _

    castQT-irr : Cast-Irrelevant castQT
    castQT-irr = irr⇒irr castQT ≤QT-irrelevant

    castQT-refl-id : Cast-ReflId castQT ≤QT-refl
    castQT-refl-id {uni} q = refl

    castQT-trans-comp : Cast-TransComp castQT ≤QT-trans
    castQT-trans-comp uni≤uni uni≤uni x = refl

    castQT-antisym : Cast-Antisym castQT ≤QT-antisym
    castQT-antisym p q with refl ← ≤QT-antisym p q
      with refl ← ≤QT-irrelevant p ≤QT-refl
      with refl ← ≤QT-irrelevant q ≤QT-refl
      = refl

  castRT-UniId-trans-comp  : ∀{rt rt' rt'' q q' q''} (u : UniId q (rt →' rt')) (u' : UniId q' (rt' →' rt'')) (q≤q' : q ≤QT q') (q'≤q'' : q' ≤QT q'')
      → (qv : semQT q) → castRT rt' rt'' (UniId⇒QId u' (castQT q q' q≤q' qv)) ∘ (castRT rt rt' (UniId⇒QId u qv)) ≗ castRT rt rt'' (UniId⇒QId (UniId-trans q≤q' u u') qv)
  castRT-UniId-trans-comp u u' q≤q' q'≤q'' qv rewrite uipRT (UniId⇒QId (UniId-trans q≤q' u u') qv) (trans (UniId⇒QId u qv) (UniId⇒QId u' (castQT _ _ q≤q' qv)))
    = castRT-trans-comp (UniId⇒QId u qv) (UniId⇒QId u' (castQT _ _ q≤q' qv))

  module _ where
    qsubst : ∀ {X qrt qrt'} → qrt ≤QRT qrt' → semQRT X qrt → semQRT X qrt'
    qsubst (≤QRT-intro q≤q' uni-id) (tbranch x , S) = (tbranch x , S)
    qsubst (≤QRT-intro q≤q' uni-id) (right (qv , vs) , S) = (right (castQT _ _ q≤q' qv , subst semRT (UniId⇒QId uni-id qv) vs) , S)

    castQRT : ∀ X → Cast QRT (semQRT X) _≤QRT_
    castQRT X (rt , q) (rt' , q') (≤QRT-intro q≤q' uni-id) =
      mapTState X (castQT q q' q≤q') (castRT rt rt' ∘ UniId⇒QId uni-id)

    castQRT-refl-id : ∀ X → Cast-ReflId (castQRT X) ≤QRT-refl
    castQRT-refl-id X {rt , q} x =  mapTState-id X castQT-refl-id ( \q qv → castRT-id (UniId⇒QId (UniId-id refl) q) qv) x

    castQRT-trans-comp : ∀ X → Cast-TransComp (castQRT X) ≤QRT-trans
    castQRT-trans-comp X (≤QRT-intro q≤q' u) (≤QRT-intro  q'≤q'' u')
      with (≤QRT-intro q≤q'' u'') ← (≤QRT-trans (≤QRT-intro q≤q' u) (≤QRT-intro q'≤q'' u'))
      = (mapTState-comp' X (castQT _ _ q≤q') (castQT _ _ q'≤q'') (castQT _ _ (≤QT-trans q≤q' q'≤q''))
                           (castRT _ _ ∘ UniId⇒QId u) (castRT _ _ ∘ UniId⇒QId u') (castRT _ _ ∘ UniId⇒QId (UniId-trans q≤q' u u'))
                           (castQT-trans-comp q≤q' q'≤q'') (castRT-UniId-trans-comp u u' q≤q' q'≤q''))

    partial-castQRT-trans-comp : ∀ X {qrt qrt' qrt''} → (p : qrt ≤QRT qrt') → (p' : qrt' ≤QRT qrt'') → mapPartial (castQRT X qrt' qrt'' p') ∘ mapPartial (castQRT X qrt qrt' p) ≗ mapPartial (castQRT X qrt qrt'' (≤QRT-trans p p'))
    partial-castQRT-trans-comp X {qrt} {qrt'} {qrt''} p p' = mapPartial-comp' (castQRT X _ _ p) (castQRT X _ _ p') (castQRT X _ _ (≤QRT-trans p p')) (castQRT-trans-comp X p p')

    castQRT-irrelevant : ∀ X → Cast-Irrelevant (castQRT X)
    castQRT-irrelevant X = irr⇒irr (castQRT X) ≤QRT-irrelevant

    castQRT-id : ∀ X → {qrt : QRT} → (p : qrt ≤QRT qrt) → castQRT X qrt qrt p ≗ id
    castQRT-id X {rt , q} p x with refl ← ≤QRT-irrelevant p ≤QRT-refl = castQRT-refl-id X x

    castQRT-qsubst : ∀ {X qrt qrt'} (p : qrt ≤QRT qrt') → (qvs : semQRT X qrt) → castQRT X _ _ p qvs ≡ qsubst p qvs
    castQRT-qsubst {qrt = rt , q} (≤QRT-intro q≤q' uni-id) (tbranch x , S) = refl
    castQRT-qsubst {qrt = rt , q} (≤QRT-intro q≤q' uni-id) (right (qv , vs) , S)
      with refl ← UniId⇒QId uni-id qv
      rewrite castRT-refl-id vs = refl

  d++d'≡d⇒d'≡[] : {X : Set} (d : List X) {d' : List X} → d ++ d' ≡ d → d' ≡ []
  d++d'≡d⇒d'≡[] [] x = x
  d++d'≡d⇒d'≡[] (_ ∷ d) x = d++d'≡d⇒d'≡[] d (∷-injectiveʳ x)

  d++d'≡d⇒d'≡[]² : {X : Set} (d : ListArrow X) {d' : ListArrow X} → d ++² d' ≡ d → d' ≡ ([] →' [])
  d++d'≡d⇒d'≡[]² (l →' r) p
    with lp →' rp ← ≡→'≡ p
    = →'≡→' (d++d'≡d⇒d'≡[] l lp →' d++d'≡d⇒d'≡[] r rp)

  _++Id_ : ∀ {D} → (rt : RT) → IdType D → IdType ((rt →' rt) ++² D)
  rt ++Id D-id = ≡.cong₂ _++_ (erefl rt) D-id

  -- El is indexed by X and Y, but `cast` only matters for X.
  CastF : (X Y : Set) (El : X → Y → Set) (R : X → X → Set) → Set
  CastF X Y El R = (a b : X) → R a b → ((d : Y) → El a d) → ((d : Y) → El b d)


  CastF-ReflId : ∀ {X Y El R} → CastF X Y El R → Reflexive R → (_≅_ : {x : X} → ((d : Y) → El x d) → ((d : Y) → El x d) → Set) → Set
  CastF-ReflId cast r _≅_ = ∀ {x f} → cast x x r f ≅ id f


  CastF-TransComp : ∀ {X Y El R} → CastF X Y El R → Transitive R → (_≅_ : {x : X} → ((d : Y) → El x d) → ((d : Y) → El x d) → Set) → Set
  CastF-TransComp {R = R} cast t _≅_ = ∀ {x y z} (p : R x y) (q : R y z) → ∀ {f} → ((cast y z q ∘ cast x y p) f) ≅ ((cast x z) (t p q) f)

  CastF-Antisym : ∀ {X El R} → Cast X El R → Antisymmetric _≡_ R → Set
  CastF-Antisym {R = R} cast as = ∀ {x y} (p : R x y) (q : R y x) → case as p q of \ { refl → cast x y p ≡ cast y x q }

  semQT-⊓QT : ∀ {q} q' → (qv : semQT q) → (q' ≤QT (q ⊓QT q'))
  semQT-⊓QT {uni} _ _ = ≤QT-refl

  sem⊓QT : ∀ {q q'} → (qv : semQT q) → (qv' : semQT q') → semQT (q ⊓QT q')
  sem⊓QT {uni} {uni} qv qv' = tt

{-
  kleisli⊥ : ∀ {X a r q q'} → (∀ D → semQFT ⊥ X (a →' r , q') D) → (∀ D → Partial (semQRT X (a ++ D , q)) →  Partial (semQRT X (r ++ D , q ⊓QT q')))
  kleisli⊥ f D div = div
  kleisli⊥ f D (con (tbranch b , S)) = con (tbranch b , S)
  kleisli⊥ f D (con (right (qv , vs) , S)) = mapPartial (castQRT _ _ _ (≤QRT-intro (semQT-⊓QT _ qv) (UniId-id refl))) (f D (right (_ , vs) , S))
-}
  liftQFT : ∀ {qft X} → (∀ D → semQFT ⊥ X qft D) → (∀ D → semQFT X X qft D)
  liftQFT f D (tbranch b , S) = con (tbranch b , S)
  liftQFT f D (right x , S) = f D (right x , S)

{-
  _>=>⊥_ : ∀ {X a m r q q'} → (∀ D → semQFT ⊥ X (a →' m , q) D) → (∀ D → semQFT ⊥ X (m →' r , q') D) → (∀ D → semQFT ⊥ X (a →' r , q ⊓QT q') D)
  (f >=>⊥ g) D x = kleisli⊥ g D (f D x)
-}
  kleisli : ∀ {X a r q q'} → (∀ D → semQFT X X (a →' r , q') D) → (∀ D → Partial (semQRT X (a ++ D , q)) →  Partial (semQRT X (r ++ D , q ⊓QT q')))
  kleisli f D div = div
  kleisli f D (con (tbranch x , S)) = con (tbranch x , S)
  kleisli f D (con (right (qv , vs) , S)) = mapPartial (castQRT _ _ _ (≤QRT-intro (semQT-⊓QT _ qv) (UniId-id refl))) (f D (right (_ , vs) , S))

  _>=>_ : ∀ {X a m r q q'} → (∀ D → semQFT X X (a →' m , q) D) → (∀ D → semQFT X X (m →' r , q') D) → (∀ D → semQFT X X (a →' r , q ⊓QT q') D)
  (f >=> g) D x = kleisli g D (f D x)

  proof-dom-dom : (D : RT) → ∀ {a a'} d → (a ++ d ≡ a') → (a' ++ D) ≡ (a ++ d ++ D)
  proof-dom-dom D d a++d=a' = ≡.sym (≡.sym (++-assoc _ d D) ⟨ ≡.trans ⟩ ≡.cong (\P → P ++ D) a++d=a')

  proof-cod-cod : (D : RT) → ∀ {r} {r'} {d} e → (q : QT) → (r ++ e ≡ r') → QId q (d →' e) → QId q ((r ++ d ++ D) →' (r' ++ D))
  proof-cod-cod D {d = d} e q r++e=r' u qv = (≡.sym (++-assoc _ d D) ⟨ ≡.trans ⟩ ≡.cong (\P → P ++ D) (≡.cong (\ d → _ ++ d) (u qv) ⟨ ≡.trans ⟩ (r++e=r')))

  ≤-proof-dom-dom : ∀ {rt rt'} → (D : RT) → (d : RT) → rt ++ d ≡ rt' → (rt' ++ D , uni) ≤QRT (rt ++ d ++ D , uni)
  ≤-proof-dom-dom D d rt+d=rt' = let prt = (proof-dom-dom D d rt+d=rt') in (≤QRT-intro uni≤uni prt)

  ≤-proof-cod-cod : ∀ {rt rt' q q'} D {d} e → q ≤QT q' → rt ++ e ≡ rt' → UniId q (d →' e) → (rt ++ d ++ D , q) ≤QRT (rt' ++ D , q')
  ≤-proof-cod-cod {q = q} D {d = d} e q≤q' rt+e=rt' u = let prt = QId⇒UniId (proof-cod-cod D e q rt+e=rt' (UniId⇒QId u)) in ≤QRT-intro q≤q' prt

  castQFT : ∀ X Y → CastF QFT RT (semQFT X Y) _≤QFT_
  castQFT X Y (a0 →' r0 , q0) (a →' r , q) (≤QFT-intro q≤q' ((da , a0++da=a) →' (dr , r0++dr=r)) qid) f D =
    let dom-dom = ≤-proof-dom-dom D da a0++da=a
        cod-cod = ≤-proof-cod-cod D dr q≤q' r0++dr=r qid
    in mapPartial (castQRT Y (r0 ++ da ++ D , q0) (r ++ D , q) cod-cod) ∘ f (da ++ D) ∘ castQRT X (a ++ D , uni) (a0 ++ da ++ D , uni) dom-dom


  liftQFT-castQFT-commute : ∀ X t t' (p : t ≤QFT t') (f : ∀ D → semQFT ⊥ X t D) → ∀ D x → liftQFT (castQFT ⊥ X t t' p f) D x ≡ castQFT X X t t' p (liftQFT f) D x
  liftQFT-castQFT-commute X (ft , q) (ft' , q') (≤QFT-intro a b c) f D (tbranch v' , S)
    = refl
  liftQFT-castQFT-commute X (ft , q) (ft' , q') (≤QFT-intro a b c) f D (right v , S)
    = refl

  comp≡comp : ∀ X i k {j h} ij jk ih hk → mapPartial (castQRT X j k jk) ∘ (mapPartial (castQRT X i j ij)) ≗ mapPartial (castQRT X h k hk) ∘ (mapPartial (castQRT X i h ih))
  comp≡comp X i k ij jk ih hk x =
    partial-castQRT-trans-comp X ij jk x ⟨ ≡.trans ⟩
    ≡.cong (\ p → mapPartial (castQRT X _ _ p) x) (≤QRT-irrelevant (≤QRT-trans ij jk) (≤QRT-trans ih hk)) ⟨ ≡.trans ⟩
    ≡.sym (partial-castQRT-trans-comp X ih hk x)

  >=>-castQFT-commute : ∀ X a0 m0 r0 qi0 qis0 a m r qi qis
    (≤a→m : (a0 →' m0 , qi0) ≤QFT (a →' m , qi))
    (≤m→r : (m0 →' r0 , qis0) ≤QFT (m →' r , qis))
    (≤a→r : (a0 →' r0 , qi0 ⊓QT qis0) ≤QFT (a →' r , qi ⊓QT qis))
    (f : ∀ D → semQFT X X (a0 →' m0 , qi0) D)
    (g : ∀ D → semQFT X X (m0 →' r0 , qis0) D)
    → ∀ D → (castQFT _ _ _ _ ≤a→m f >=> castQFT _ _ _ _ ≤m→r g) D ≗ castQFT _ _ _ _ ≤a→r (f >=> g) D
  >=>-castQFT-commute X a0 m0 r0 qi0 qis0 a m r qi qis
    (≤QFT-intro ≤qi ((da , a0++da=a) →' (dm , m0++dm=m)) q-da=dm)
    (≤QFT-intro ≤qis ((dm' , m0++dm'=m) →' (dr' , r0++dr'=r)) q-dm'=dr')
    (≤QFT-intro ≤qi⊓qis ((da'' , a0++da''=a) →' (dr'' , r0++dr''=r)) q-da''=dr'') f g D x
      with refl ← ++-cancelˡ a0 (a0++da=a ⟨ ≡.trans ⟩ ≡.sym a0++da''=a) -- proof / substitution for da == da''
      with refl ← ++-cancelˡ m0 (m0++dm=m ⟨ ≡.trans ⟩ ≡.sym m0++dm'=m) -- proof / substitution for dm == dm'
      with refl ← ++-cancelˡ r0 (r0++dr'=r ⟨ ≡.trans ⟩ ≡.sym r0++dr''=r) -- proof / substitution for dr == dr''
      with refl ← uipRT a0++da=a a0++da''=a -- uip (to equate castQRT proof arguments)
      with refl ← uipRT m0++dm=m m0++dm'=m
      with refl ← uipRT r0++dr'=r r0++dr''=r
      with (f (da ++ D) ∘ castQRT X (a ++ D , uni) (a0 ++ da ++ D , uni) (≤-proof-dom-dom D da a0++da=a)) x -- apply first function
  ... | div = refl
  ... | con (tbranch _ , _) = refl
  ... | con (right (qv , vs) , S)
      with refl ← UniId⇒QId q-da=dm qv
      rewrite castRT-inv (UniId⇒QId (QId⇒UniId (proof-cod-cod D da _ m0++dm=m (UniId⇒QId q-da=dm))) qv) (proof-dom-dom D da m0++dm=m) vs -- two casts in between cancels each other
      with (g (da ++ D) (tnormal vs , S))
  ... | div = refl
  ... | con (tbranch _ , _) = refl
  ... | con (right (qv' , vs') , S')
      with refl ← UniId⇒QId q-dm'=dr' qv'
    = comp≡comp X (r0 ++ da ++ D , qis0) (r ++ D , qi ⊓QT qis) -- we get two functions in the same form (mapParital castQRT _∘ castQRT _), they are same if domain and codomain are the same
        (≤-proof-cod-cod D dr'' ≤qis r0++dr''=r q-dm'=dr')
        (≤QRT-intro (semQT-⊓QT qis (castQT _ _ ≤qi qv)) (UniId-id refl))
        (≤QRT-intro (semQT-⊓QT qis0 qv) (UniId-id refl))
        (≤-proof-cod-cod D dr'' ≤qi⊓qis r0++dr'=r q-da''=dr'')
        (con (right (qv' , vs') , S'))

  castQFT-refl-id : ∀ X Y → CastF-ReflId (castQFT X Y) (≤QFT-refl) (\ f g → (D : RT) → f D ≗ g D)
  castQFT-refl-id X Y {a →' r , q} {f} D st
    rewrite castQRT-id X (≤-proof-dom-dom D [] (++-identityʳ a)) st
    = mapPartial-id (castQRT-id Y (≤-proof-cod-cod D [] ≤QT-refl (++-identityʳ r) (UniId-id ≡.refl))) (f D st)

  lemma : ∀ X Y qft a r d1 d2 p1 q1 p2 q2 (f : ∀ d → semQFT X Y qft d) →
        d1 ≡ d2 →
        mapPartial (castQRT Y _ r p1) ∘ (f d1) ∘ (castQRT X a _ q1) ≗ mapPartial (castQRT Y _ r p2) ∘ (f d2) ∘ (castQRT X a _ q2)
  lemma X Y qft a r d1 .d1 p1 q1 p2 q2 f refl st
    with refl ← ≤QRT-irrelevant p1 p2
    with refl ← ≤QRT-irrelevant q1 q2
    = refl

  castQFT-trans-comp : ∀ X Y → CastF-TransComp (castQFT X Y) (≤QFT-trans) (\ f g → (D : RT) → f D ≗ g D)
  castQFT-trans-comp X Y {a →' r , q} {a' →' r' , q'} {a'' →' r'' , q''} qft≤qft' qft'≤qft'' {f = f} D x
      with qft≤qft' | qft'≤qft'' | ≤QFT-trans qft≤qft' qft'≤qft'' in eq
  ... | (≤QFT-intro q≤q' ((da , a++da=a') →' (dr , r++dr=r')) uni-id) | (≤QFT-intro q'≤q'' ((da' , a'++da'=a'') →' (dr' , r'++dr'=r'')) uni-id')
      | (≤QFT-intro q≤q'' ((da++da' , a++da++da''=a'') →' (dr++dr' , r++dr++dr'=r'')) uni-id'')
    rewrite castQRT-trans-comp X (≤-proof-dom-dom D da' a'++da'=a'') (≤-proof-dom-dom _ da a++da=a') x
    rewrite partial-castQRT-trans-comp Y (≤-proof-cod-cod _ dr q≤q' r++dr=r' uni-id) (≤-proof-cod-cod D dr' q'≤q'' r'++dr'=r'' uni-id')
      ((f (da ++ da' ++ D) ∘ castQRT X (a'' ++ D , uni) (a ++ da ++ da' ++ D , uni) (≤QRT-trans (≤-proof-dom-dom D da' a'++da'=a'') (≤-proof-dom-dom _ da a++da=a'))) x)
    = lemma X Y (a →' r , q) (a'' ++ D , uni) (r'' ++ D , q'') (da ++ da' ++ D) ((da++da') ++ D)
            (≤QRT-trans (≤-proof-cod-cod _ dr q≤q' r++dr=r' uni-id) (≤-proof-cod-cod D dr' q'≤q'' r'++dr'=r'' uni-id'))
            (≤QRT-trans (≤-proof-dom-dom D da' a'++da'=a'') (≤-proof-dom-dom _ da a++da=a'))
            (≤-proof-cod-cod _ dr++dr' q≤q'' r++dr++dr'=r'' uni-id'')
            (≤-proof-dom-dom _ da++da' a++da++da''=a'')
            f (≡.sym (++-assoc da da' D) ⟨ trans ⟩
            ≡.cong (\ d → d ++ D) (++-cancelˡ a (append-assoc {xs = a} a++da=a' a'++da'=a'' ⟨ trans ⟩ ≡.sym a++da++da''=a'') )  ) x
  castQFT-cong : ∀ X Y {t t'} {f g}  → (p : t ≤QFT t') → (∀ D → f D ≗ g D) → (∀ D → (castQFT X Y t t' p f) D ≗ (castQFT X Y t t' p g) D)
  castQFT-cong X Y (≤QFT-intro q≤q' ((da , a+da=a') →' (dr , r+dr=r')) uid) f~g D x
    rewrite f~g (da ++ D) (castQRT X _ _ (≤-proof-dom-dom D da a+da=a') x)
    = refl

  castQFT-cong' : ∀ {Y} {t t'} {f g}  → (p : t ≤QFT t') → (∀ D vs S → f D (tnormal vs , S) ≡ g D (tnormal vs , S)) → (∀ D vs S → (castQFT ⊥ Y t t' p f) D (tnormal vs , S) ≡ (castQFT ⊥ Y t t' p g) D (tnormal vs , S))
  castQFT-cong' (≤QFT-intro q≤q' ((da , a+da=a') →' (dr , r+dr=r')) uid) f~g D vs S
    with vs' ← castRT _ _ (proof-dom-dom D da a+da=a') vs
    rewrite f~g (da ++ D) vs' S
    = refl

  liftQFT-cong-pointwise : ∀ {X t} {f g : ∀ D → semQFT ⊥ X t D} → (∀ D → f D ≗ g D) → (∀ D → liftQFT f D ≗ liftQFT g D)
  liftQFT-cong-pointwise f=g D (tbranch x , S) = refl
  liftQFT-cong-pointwise f=g D (right x , S) = f=g D (right x , S)
