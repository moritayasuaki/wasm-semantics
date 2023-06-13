{-# OPTIONS --without-K --safe #-}

module TypeCast0 where
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
open import TypeCast
open import OperationalSemantics

CastF0 : (X : Set) (El : X → Set) (R : X → X → Set) → Set
CastF0 X El R = (a b : X) → R a b → El a → El b

CastF0-ReflId : ∀ {X El R} → CastF0 X El R → Reflexive R → (_≅_ : {x : X} → El x → El x → Set) → Set
CastF0-ReflId cast r _≅_ = ∀ {x f} → cast x x r f ≅ f

CastF0-TransComp : ∀ {X El R} → CastF0 X El R → Transitive R → (_≅_ : {x : X} → El x → El x → Set) → Set
CastF0-TransComp {R = R} cast t _≅_ = ∀ {x y z} (p : R x y) (q : R y z) → ∀ {f} → ((cast y z q ∘ cast x y p) f) ≅ ((cast x z) (t p q) f)

semQFT0 : Set → QFT → Set
semQFT0 X (at →' rt , q) = semRT at × Store → Partial (semQRT X (rt , q))

castQFT0 : ∀ X → CastF0 QFT (semQFT0 X) _≤QFT_
castQFT0 X (a0 →' r0 , q0) (a →' r , q) (≤QFT-intro q0≤q ((da , a0++da=a) →' (dr , r0++dr=r)) qid) f (vs , S) =
      let top-vs , res-vs = safesplit a0 (castRT _ _ (sym a0++da=a) vs)
      in mapPartial (mapTState X (castQT q0 q q0≤q) (\ qv vs' → castRT _ _ (cong (r0 ++_) (UniId⇒QId qid qv) ⟨ trans ⟩ r0++dr=r) (vs' safe++ res-vs))) (f (top-vs , S))

safetake-a++[]-id : ∀ a p → safetake a ∘ castRT a (a ++ []) p ≗ id
safetake-a++[]-id .[] p [] = refl
safetake-a++[]-id (vt ∷ rt) ps (x ∷ xs)
  with ≡∷≡ ps
... | p , ps
  with refl ← uipVT p refl
  = cong (_∷_ x) (safetake-a++[]-id rt ps xs)

safedrop-a++[]-[] : ∀ a p → safedrop a ∘ castRT a (a ++ []) p ≗ const []
safedrop-a++[]-[] .[] p [] = refl
safedrop-a++[]-[] .(_ ∷ _) p (x ∷ x₁) = safedrop-a++[]-[] _ (proj₂ (≡∷≡ p)) x₁

safe++[] : ∀ r p → (\ vs → castRT _ r p (vs safe++ [])) ≗ id
safe++[] .[] p [] = refl
safe++[] .(_ ∷ _) ps (x ∷ xs) with ≡∷≡ ps
... | p , ps
  with refl ← uipVT p refl
  = cong (_∷_ x) (safe++[] _ ps xs)

castQFT0-refl-id : ∀ X → CastF0-ReflId (castQFT0 X) ≤QFT-refl _≗_
castQFT0-refl-id X {a →' r , q} {f} (vs , S)
  rewrite safetake-a++[]-id a (sym (++-identityʳ a)) vs
  rewrite safedrop-a++[]-[] a (sym (++-identityʳ a)) vs
  with f (vs , S)
... | div = refl
... | con (tbranch b , S) = refl
... | con (right (qv , vs) , S)
  rewrite safe++[] _ (trans (cong (_++_ r) (UniId⇒QId (UniId-id refl) qv)) (++-identityʳ r)) vs
  rewrite castQT-refl-id qv
  = refl

safetake-trans : ∀ a a' a'' da da' (++da : a ++ da ≡ a') (++da' : a' ++ da' ≡ a'') vs
  → safetake a (castRT a' (a ++ da) (sym ++da) (safetake a' (castRT a'' (a' ++ da') (sym ++da') vs)))
  ≡ safetake a (castRT a'' (a ++ da ++ da') (sym (trans (trans (sym (++-assoc a da da')) (cong (λ r₁ → r₁ ++ da') ++da)) ++da')) vs)
safetake-trans a a' .[] da da' ++da ++da' []
  with ++-conicalˡ a' da' ++da' | ++-conicalʳ a' da' ++da'
... | refl | refl
  with ++-conicalˡ a da ++da | ++-conicalʳ a da ++da
... | refl | refl
  = refl
safetake-trans [] [] _  da da' ++da ++da' vs = refl
safetake-trans [] (x ∷ a') _ da da' ++da ++da' vs = refl
safetake-trans (_ ∷ a) (_ ∷ a') (vt ∷ rt) da da' ++da ++da' (v ∷ vs)
  with ≡∷≡ ++da | ≡∷≡ ++da'
... | refl , ++da''  | refl , ++da'''
  rewrite uipRT (proj₂ (∷-injective (sym ++da))) (sym ++da'')
  rewrite uipRT (proj₂ (∷-injective (sym ++da'))) (sym ++da''')
  rewrite uipRT (proj₂ (∷-injective (sym (trans (trans (sym (cong (_∷_ vt) (++-assoc a da da'))) (cong (λ r₁ → r₁ ++ da') ++da)) ++da')))) (sym (trans (trans (sym (++-assoc a da da')) (cong (λ r₁ → r₁ ++ da') ++da'')) ++da'''))
  rewrite uipVT (proj₁ (∷-injective (sym (trans (trans (sym (cong (_∷_ vt) (++-assoc a da da'))) (cong (λ r₁ → r₁ ++ da') ++da)) ++da')))) (trans (proj₁ (∷-injective (sym ++da'))) (proj₁ (∷-injective (sym ++da))))
  = cong₂ _∷_ (castVT-trans-comp (proj₁ (∷-injective (sym ++da'))) (proj₁ (∷-injective (sym ++da))) v) (safetake-trans a a' rt da da' ++da'' ++da''' vs)

take++drop' : ∀ dr D (vs : semRT (dr ++ D)) → vs ≡ safetake dr vs safe++ safedrop dr vs
take++drop' [] D vs = refl
take++drop' (x ∷ dr) D (v ∷ vs) = cong (_∷_ v) (take++drop' dr D vs)

castVT-id : ∀ x p → castVT x x p ≗ id
castVT-id x p v' with refl ← uipVT p refl = refl

castRT-assoc : ∀ a dr dr' p → castRT _ _ p ≗ castRT _ _ (++-assoc a dr dr')
castRT-assoc a dr dr' p x with refl ← uipRT p (++-assoc a dr dr') = refl

castRT-sym-assoc : ∀ r dr dr' p → castRT _ _ p ≗ castRT _ _ (sym (++-assoc r dr dr'))
castRT-sym-assoc r dr dr' p x with refl ← uipRT p (sym (++-assoc r dr dr')) = refl

safe++drop : ∀ a r dr dr' p p' vs vs'
  → castRT (r ++ dr ++ dr') ((r ++ dr) ++ dr') p (vs' safe++ safedrop a (castRT ((a ++ dr) ++ dr') (a ++ dr ++ dr') p' vs))
    ≡ (vs' safe++ safedrop a (safetake (a ++ dr) vs)) safe++ safedrop (a ++ dr) vs
safe++drop a r dr dr' p p' vs vs' with uipRT p (sym (++-assoc r dr dr')) | uipRT p' (++-assoc a dr dr')
safe++drop [] [] dr dr' .(refl) .(refl) vs [] | refl | refl = castRT-refl-id (castRT _ _ refl vs) ⟨ trans ⟩ (castRT-refl-id vs ⟨ trans ⟩ take++drop' dr _ vs)
safe++drop (x ∷ a) [] dr dr' .(refl) .(cong (_∷_ x) (++-assoc a dr dr')) (v ∷ vs) [] | refl | refl
  rewrite uipRT (proj₂ (≡∷≡ (cong (_∷_ x) (++-assoc a dr dr')))) (++-assoc a dr dr') =
  cong (\ vs → castRT _ _ refl (safedrop a vs)) (castRT-assoc a dr dr' (proj₂ (≡∷≡ (cong (_∷_ x) (++-assoc a dr dr')))) vs) ⟨ trans ⟩ safe++drop a [] dr dr' refl (++-assoc a dr dr') vs []
safe++drop [] (x ∷ r) dr dr' .(sym (++-assoc (x ∷ r) dr dr')) .(refl) vs (v' ∷ vs') | refl | refl =
  let ih = safe++drop [] r dr dr' (sym (++-assoc r dr dr')) refl vs vs'
      v= = castVT-id x (proj₁ (≡∷≡ (sym (cong (_∷_ x) (++-assoc r dr dr'))))) v'
      vs= = castRT-sym-assoc r dr dr' (proj₂ (≡∷≡ (sym (cong (_∷_ x) (++-assoc r dr dr'))))) (vs' safe++ castRT _ _ refl vs)
      p =   cong (\ v' → v' ∷ (castRT (r ++ dr ++ dr') ((r ++ dr) ++ dr') (proj₂ (≡∷≡ (sym (cong (_∷_ x) (++-assoc r dr dr'))))) (vs' safe++ castRT (dr ++ dr') (dr ++ dr') refl vs))) v= ⟨ trans ⟩ cong (_∷_ v') (vs= ⟨ trans ⟩ ih) in p
safe++drop (x ∷ a) (y ∷ r) dr dr' .(sym (++-assoc (y ∷ r) dr dr')) .(++-assoc (x ∷ a) dr dr') (v ∷ vs) (v' ∷ vs') | refl | refl =
  let ih = safe++drop a r dr dr' (sym (++-assoc r dr dr')) (++-assoc a dr dr') vs vs'
      v= = castVT-id y (proj₁ (≡∷≡ (sym (cong (_∷_ y) (++-assoc r dr dr'))))) v'
      vs= = safe++drop a r dr dr' (sym (++-assoc r dr dr')) (proj₂ (≡∷≡ (cong (_∷_ x) (++-assoc a dr dr')))) vs vs'
      vs=' = castRT-sym-assoc r dr dr' (proj₂ (≡∷≡ (sym (cong (_∷_ y) (++-assoc r dr dr'))))) (vs' safe++ safedrop a (castRT ((a ++ dr) ++ dr') (a ++ dr ++ dr') (proj₂ (≡∷≡ (cong (_∷_ x) (++-assoc a dr dr')))) vs))
  in cong₂ _∷_ v= (vs=' ⟨ trans ⟩ vs=)

castQFT0-trans-comp : ∀ X → CastF0-TransComp (castQFT0 X) ≤QFT-trans _≗_
-- castQFT0-trans-comp X (≤QFT-intro {ft = a →' r} {ft' = a' →' r'}  q≤q' ((da , ++da) →' (dr , ++dr)) qid) (≤QFT-intro {ft' = a'' →' r''} q'≤q'' ((da' , ++da') →' (dr' , ++dr')) qid') {f} (vs , S)
castQFT0-trans-comp X (≤QFT-intro {ft = a →' r} {ft' = a' →' r'}  q≤q' ((da , ++da) →' (dr , ++dr)) qid) (≤QFT-intro {ft' = a'' →' r''} q'≤q'' ((da' , ++da') →' (dr' , ++dr')) qid') {f} (vs , S)
  rewrite safetake-trans a a' a'' da da' ++da ++da' vs
  with f (safetake a (castRT a'' (a ++ da ++ da') (sym (trans (trans (sym (++-assoc a da da')) (cong (λ r₁ → r₁ ++ da') ++da)) ++da'))  vs) , S)
... | div = refl
... | con (tbranch _ , _) = refl
castQFT0-trans-comp X (≤QFT-intro {_} {a →' r} {_} {a' →' r'} q≤q' ((da , ++da) →' (dr , ++dr)) qid) (≤QFT-intro {_} {_} {_} {a'' →' r''} q'≤q'' ((da' , ++da') →' (dr' , ++dr')) qid') {f} (vs , S)  | con (right (qv , vs') , S')
  with refl ← ++da
  with refl ← ++dr
  with refl ← ++da'
  with refl ← ++dr'
  with q≤q' | q'≤q''
... | uni≤uni | uni≤uni
  with refl ← qid
  with refl ← qid'
  rewrite castRT-id refl vs
  rewrite castRT-id refl (safetake (a ++ da) vs)
  rewrite castRT-id refl (vs' safe++ safedrop a (safetake (a ++ dr) vs))
  rewrite castRT-id refl ((vs' safe++ safedrop a (safetake (a ++ dr) vs)) safe++ safedrop (a ++ dr) vs)
  = cong (\ r → con (right (qv , r) , S')) (sym (safe++drop a r dr dr' _ _ vs vs'))

kleisli0 : ∀{X a r q} → semQFT0 X (a →' r , q) → Partial (semQRT X (a , uni)) → Partial (semQRT X (r , q))
kleisli0 f div = div
kleisli0 f (con (tbranch b , S)) = con (tbranch b , S)
kleisli0 f (con (tnormal vs , S)) = f (vs , S)
_⊛_ : ∀{q q'} → semQT q → semQT q' → semQT (q ⊓QT q')
_⊛_ {uni} {uni} _ _ = _

_>=>0_ : ∀{X a m r q q'} → semQFT0 X (a →' m , q) → semQFT0 X (m →' r , q') → semQFT0 X (a →' r , q ⊓QT q')
_>=>0_ f g (vs , S) = case f (vs , S) of \ where
  div → div
  (con (tbranch b , S')) → (con (tbranch b , S'))
  (con (right (qv , vs') , S')) → case g (vs' , S') of \ where
    div → div
    (con (tbranch b , S'')) → (con (tbranch b , S''))
    (con (right (qv' , vs'') , S'')) → con (right ((qv ⊛ qv') , vs'') , S'')

castQFT0-cong : ∀ X {t t'} {f g}  → (p : t ≤QFT t') → f ≗ g → (castQFT0 X t t' p f) ≗ (castQFT0 X t t' p g)
castQFT0-cong X {t = (a →' r) , q} {t' = (a' →' r') , q'} (≤QFT-intro q≤q' ((da , a+da=a') →' (dr , r+dr=r')) uid) f~g (vs , S)
  rewrite f~g (proj₁ (safesplit a (castRT a' (a ++ da) (sym a+da=a') vs)) , S)
  = refl 

>=>0-cong : ∀{X a m r q q'} → {f g : semQFT0 X (a →' m , q)} → {h k : semQFT0 X (m →' r , q')} → f ≗ g → h ≗ k → (f >=>0 h) ≗ (g >=>0 k)
>=>0-cong {f = f} {g} {h} {k} f=g h=k x
  with f x | g x | f=g x
... | div | .div | refl = refl
... | con (tbranch _ , _) | .(con (tbranch _ , _)) | refl = refl
... | con (right (qv , vs) , S) | .(con (right (qv , vs) , S)) | refl
  with h (vs , S) | k (vs , S) | h=k (vs , S)
... | _ | _ | refl = refl

safetake-++-safedrop : ∀ {m0 a0} D (vs : semRT (a0 ++ D)) (vs' : semRT m0) → safetake m0 (vs' safe++ safedrop a0 vs) ≡ vs'
safetake-++-safedrop D vs [] = refl
safetake-++-safedrop D vs (x ∷ vs') = cong (_∷_ x) (safetake-++-safedrop D vs vs')

safedrop-++-safedrop : ∀ {m0 a0} D (vs : semRT (a0 ++ D)) (vs' : semRT m0) → safedrop m0 (vs' safe++ safedrop a0 vs) ≡ safedrop a0 vs
safedrop-++-safedrop D vs [] = refl
safedrop-++-safedrop D vs (x ∷ vs') = safedrop-++-safedrop D vs vs'

>=>0-castQFT0-commute : ∀ X a0 m0 r0 qi0 qis0 a m r qi qis
  (≤a→m : (a0 →' m0 , qi0) ≤QFT (a →' m , qi))
  (≤m→r : (m0 →' r0 , qis0) ≤QFT (m →' r , qis))
  (≤a→r : (a0 →' r0 , qi0 ⊓QT qis0) ≤QFT (a →' r , qi ⊓QT qis))
  (f : semQFT0 X (a0 →' m0 , qi0))
  (g : semQFT0 X (m0 →' r0 , qis0))
  → (castQFT0 _ _ _ ≤a→m f >=>0 castQFT0 _ _ _ ≤m→r g) ≗ castQFT0 _ _ _ ≤a→r (f >=>0 g)
>=>0-castQFT0-commute X a0 m0 r0 qi0 qis0 a m r qi qis
  (≤QFT-intro ≤qi ((da , a0++da=a) →' (dm , m0++dm=m)) q-da=dm)
  (≤QFT-intro ≤qis ((dm' , m0++dm'=m) →' (dr' , r0++dr'=r)) q-dm'=dr')
  (≤QFT-intro ≤qi⊓qis ((da'' , a0++da''=a) →' (dr'' , r0++dr''=r)) q-da''=dr'')
  f g (vs , S)
  with refl ← ++-cancelˡ a0 (a0++da=a ⟨ ≡.trans ⟩ ≡.sym a0++da''=a) -- proof / substitution for da == da''
  with refl ← ++-cancelˡ m0 (m0++dm=m ⟨ ≡.trans ⟩ ≡.sym m0++dm'=m) -- proof / substitution for dm == dm'
  with refl ← ++-cancelˡ r0 (r0++dr'=r ⟨ ≡.trans ⟩ ≡.sym r0++dr''=r) -- proof / substitution for dr == dr''
  with refl ← uipRT a0++da=a a0++da''=a -- uip (to equate castQRT proof arguments)
  with refl ← uipRT m0++dm=m m0++dm'=m
  with refl ← uipRT r0++dr'=r r0++dr''=r
  with f (safetake a0 (castRT a (a0 ++ da) (sym a0++da=a) vs) , S)
... | div = refl
... | con (tbranch _ , _) = refl
... | con (right (qv , vs') , S')
  with refl ← UniId⇒QId q-da=dm qv
  with refl ← m0++dm=m
  with refl ← a0++da=a
  rewrite castRT-refl-id vs
  rewrite castRT-refl-id (vs' safe++ safedrop a0 vs)
  rewrite castRT-refl-id (vs' safe++ safedrop a0 vs)
  rewrite safetake-++-safedrop da vs vs'
  with g (vs' , S')
... | div = refl
... | con (tbranch _ , _) = refl
... | con (right (qv' , vs'') , S'')
  with qi0 | qis0 | ≤qi | ≤qis | ≤qi⊓qis
... | uni | uni | uni≤uni | uni≤uni | uni≤uni
  with refl ← uipRT q-dm'=dr' q-da''=dr''
  rewrite safedrop-++-safedrop da vs vs'
  = refl
