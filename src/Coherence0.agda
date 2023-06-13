{-# OPTIONS --without-K --safe --auto-inline #-}

module Coherence0 where

open import Relation.Nullary.Decidable
open import Arrow
open import Function
open import Syntax
open import ListOps
open import OperationalSemantics
open import TypeInference
open import TypeSystem
open import TypeCast0
open import DenotationalSemantics0
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Partial
open import BlockList hiding (_++_; length ; ++-assoc ; ∷-injective)
open import Subtype
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Relation.Unary hiding (_⊢_)
open import Relation.Nullary
open import Data.Bool hiding (_<?_)
open import Result
open import Data.List hiding (lookup)
open import Data.List.Properties
open import Data.Product
open import Data.Maybe
open import UntypedLift
open import Data.Sum
open import TypeCast
open RSub

open import Result

private variable
  k : Kind

Coherence0 : (∀ {k} {c : Code k} {C t} → (C ⊢? c :' t) → ℕ → semRQFT0 t C) → Set
Coherence0 ⟦_⟧ = ∀ {k} {c : Code k} {C t} → (tc tc' : C ⊢? c :' t) → ∀ n → ⟦ tc ⟧ n ≅0 ⟦ tc' ⟧ n

open import Data.Nat.Properties
open QP-≤QFT

qid-diff : ∀ mi m0 qi → QId qi ((qi *Q dl mi m0) →' dl mi m0)
qid-diff mi m0 uni qv = refl

pw-trans : ∀ {X t} {f g h : ∀ D → semQFT X X t D} → (∀ D → f D ≗ g D) → (∀ D → g D ≗ h D) → (∀ D → f D ≗ h D)
pw-trans f=g g=h D x = f=g D x ⟨ trans ⟩ g=h D x

pw-sym : ∀ {X t} {f g : ∀ D → semQFT X X t D} → (∀ D → f D ≗ g D) → (∀ D → g D ≗ f D)
pw-sym f=g D x = sym (f=g D x)

>=>-cong₂ : ∀ {X a m r q q'} {f g : ∀ D → semQFT X X (a →' m , q) D} {h k : ∀ D → semQFT X X (m →' r , q') D}
  → (∀ D → f D ≗ g D) → (∀ D → h D ≗ k D) → ∀ D → (f >=> h) D ≗ (g >=> k) D
>=>-cong₂ {q = q} {f = f} {g = g} {h = h} {k = k} f=g h=k D x
  with f D x | g D x | f=g D x
... | .div | div | refl = refl
... | ._ | con (tbranch v , S) | refl = refl
... | ._ | con (right (qv , vs) , S) | refl
  with h D (tnormal vs , S) | k D (tnormal vs , S) | h=k D (tnormal vs , S)
... | ._ | x' | refl = refl

to-dl≡dl : ∀ {ft ft'} q (p : ft ⊑FT ft') → UniId q (diff-⊑FT p) → QId q (dl² ft ft')
to-dl≡dl q p uid = UniId⇒QId (subst (UniId q) (sym (⊑≡dl² p)) uid)

from-dl≡dl : ∀ {ft ft'} q (p : ft ⊑FT ft') → QId q (dl² ft ft') → UniId q (diff-⊑FT p)
from-dl≡dl q p qid = QId⇒UniId (subst (QId q) (⊑≡dl² p) qid)

-- TODO : rewrite this in equation reasnoning style (begin ≡⟨ ⟩ ∎)
diff-lemma : ∀ a0 a mi m0 qi0  m → a0 ⊑RT a → mi ⊑RT m0 → m0 ⊑RT m
  → ((a0 ++ qi0 *Q dl mi m0) ⊑RT a) → (QId qi0 (dl a0 a →' dl mi m)) → (QId qi0 (dl (a0 ++ qi0 *Q dl mi m0) a →' dl m0 m))
diff-lemma a0 a mi m0 uni m ([d+d'] , a0++[d+d']=a) (d , mi++d=m0) (d' , m0++d'=m) ([d'] , a0++d++[d']=a) q-dl-a0-a=dl-mi-m qv
  with dla0a=dlmim ← q-dl-a0-a=dl-mi-m qv
  = cong (\ d → dl (a0 ++ d) a) dl-mi-m0=d ⟨ trans ⟩ ( sym (cong (\ a → dl (a0 ++ d) a) a0++[d+d']=a) ⟨ trans ⟩ (dl-p++p++ a0 d [d+d'] ⟨ trans ⟩ (cong (dl d) [d+d']=d++d' ⟨ trans ⟩ dl++ d d')) ⟨ trans ⟩ sym dl-m0-m=d')
    where
      ++⇒dl : ∀{x y : RT} d → x ++ d ≡ y → dl x y ≡ d
      ++⇒dl {x} d p = cong (dl x) (sym p) ⟨ trans ⟩ dl++ x d
      dl-p++p++ : ∀ p d d' → dl (p ++ d) (p ++ d') ≡ dl d d'
      dl-p++p++ [] d d' = refl
      dl-p++p++ (x ∷ p) d d' = dl-p++p++ p d d'
      dl-mi-m0=d : dl mi m0 ≡ d
      dl-mi-m0=d = ++⇒dl d mi++d=m0
      dl-m0-m=d' : dl m0 m ≡ d'
      dl-m0-m=d' = ++⇒dl d' m0++d'=m
      dl-mi-m=d+d' : dl mi m ≡ d ++ d'
      dl-mi-m=d+d' = ++⇒dl {x = mi} (d ++ d') (sym (++-assoc mi d d') ⟨ trans ⟩ (cong (\ p → p ++ d') mi++d=m0 ⟨ trans ⟩ m0++d'=m))
      dl-a0++a=[d+d'] : dl a0 a ≡ [d+d']
      dl-a0++a=[d+d'] = ++⇒dl [d+d'] a0++[d+d']=a
      [d+d']=d++d' : [d+d'] ≡ d ++ d'
      [d+d']=d++d' = sym dl-a0++a=[d+d'] ⟨ trans ⟩ dla0a=dlmim ⟨ trans ⟩ dl-mi-m=d+d'

-- In general, a composition `i ∷ is : a → r` is reasoned by `i : a → m' and `is : m → r`.
-- By completeness, we have principal types
-- `i : a0 → mis`
-- `is : mi → r0`
-- `(i ∷ is) : a0 + (m0 ∸ m0-is) → r0 + (m0 ∸ m0-is)`
-- We still does not have instances of the following subtype relation. (we need some calculation)
-- `(a0 + (m0 ∸ mi)) → m0 ≤ a → m`
-- `(m0 → r0 + (m0 ∸ mis)) ≤ m → r`

≤QFT-decompose :
  ∀ {a0 qi0 mi r0 qis0 mis m0 a r qi qis m}
  → ((a0 →' mi , qi0)) ≤QFT ((a →' m) , qi)
  → ((mis →' r0 , qis0)) ≤QFT ((m →' r) , qis)
  → IsLeastUpperBound _⊑RT_ mi mis m0
  → ((a0 ++ (qi0 *Q dl mi m0)) →' (r0 ++ (qis0 *Q dl mis m0)) , (qi0 ⊓QT qis0)) ≤QFT (a →' r , (qi ⊓QT qis))
  → Arrow
    (((a0 ++ (qi0 *Q dl mi m0)) →' m0 , qi0) ≤QFT (a →' m , qi))
    ((m0 →' (r0 ++ (qis0 *Q dl mis m0)) , qis0) ≤QFT (m →' r , qis))
≤QFT-decompose {qi0 = qi0} {qis0 = qis0} {m = m}
  (≤QFT-intro qi0≤qi (a0mi⊑am @ (a0⊑a →' mi⊑m)) qid-a0mi⊑am)
  (≤QFT-intro qis0≤qis (misr0⊑mr @ (mis⊑m →' r0⊑r)) qid-misr0⊑mr)
  (mk-lub (mk-ub mi⊑m0 mis⊑m0) m0-least) (≤QFT-intro qi0⊓qis0≤qi⊓qis (a0+d⊑a →' r0+d⊑r) qid-p)
  = let m0⊑m = m0-least m (mk-ub mi⊑m mis⊑m) in
    (≤QFT-intro qi0≤qi ((a0+d⊑a →' m0⊑m)) (from-dl≡dl qi0 ((a0+d⊑a →' m0⊑m)) (diff-lemma _ _ _ _ qi0 m a0⊑a mi⊑m0 m0⊑m a0+d⊑a (to-dl≡dl qi0 a0mi⊑am qid-a0mi⊑am))))
    →'
    ≤QFT-intro qis0≤qis ((m0⊑m →' r0+d⊑r)) (from-dl≡dl qis0 ((m0⊑m →' r0+d⊑r)) (opQId (diff-lemma _ _ _ _ qis0 m r0⊑r mis⊑m0 m0⊑m r0+d⊑r (opQId (to-dl≡dl qis0 misr0⊑mr qid-misr0⊑mr)))))

castQFT0-comp : ∀ {X} {t t' t''}
  → (t<t' : t ≤QFT t')
  → (t'<t'' : t' ≤QFT t'')
  → (t<t'' : t ≤QFT t'')
  → ∀ f → (castQFT0 X t' t'' t'<t'' (castQFT0 X t t' t<t' f)) ≗ (castQFT0 X t t'' t<t'' f)
castQFT0-comp t<t' t'<t'' t<t'' f with refl ← ≤QFT-irrelevant t<t'' (≤QFT-trans t<t' t'<t'')
  = castQFT0-trans-comp _ t<t' t'<t'' {f = f}

ft-⊑' : ∀ {q q' ft ft'} → (ft , q) ≤QFT (ft' , q') → ft ⊑FT ft'
ft-⊑' (≤QFT-intro x ft⊑ft' x₁) = ft⊑ft'

++dom-proj₁-ft-⊑ : ∀ {a0 r0 q0 a r q} D → (≤qft : (a0 →' r0 , q0) ≤QFT (a →' r , q)) → (a0 ++ diff-⊑RT (dom (ft-⊑' ≤qft)) ++ D , uni) ≡ (a ++ D , uni)
++dom-proj₁-ft-⊑ {a0} D (≤QFT-intro _ ((d , refl) →' (r , refl)) _) rewrite ++-assoc a0 d D = refl

safetake++[] : ∀{a : RT} (vs : semRT a) → safetake a (castRT a (a ++ []) (sym (++-identityʳ a)) vs) ≡ vs
safetake++[] [] = refl
safetake++[] {vt ∷ rt} (x ∷ vs)
  rewrite uipVT (proj₁ (∷-injective (sym (cong (_∷_ vt) (++-identityʳ rt))))) refl
  rewrite uipRT (proj₂ (∷-injective (sym (cong (_∷_ vt) (++-identityʳ rt))))) (sym (++-identityʳ rt))
  = cong (_∷_ x) (safetake++[] vs)

castQFT0-id : ∀ {X : Set} → ∀ {x} f → f ≗ castQFT0 X x x ≤QFT-refl f
castQFT0-id {X} {x} f = ≗-sym (castQFT0-refl-id X {f = f})

preserves-sem : ∀ (c : Code k) C t (tc : C ⊢? c :' t) n → semRCode0 tc n ≅0 semRCode0 (infer-transform tc) n
preserves-sem-ok : ∀ (c : Code k) C t (tc : C ⊢ c :' t) t0
  (tc0 : C ⊢[base] c :' t0) (tc0≤tc : t0 ≤QFT t)
  (transform≡sub-base : sub? (infer-complete-exists c C t tc) (base? (infer-basesound c C)) ≡ exists (sub tc0≤tc (base tc0)))
  → ∀ n → ⟦ tc ⟧0 n ≗ ⟦ sub tc0≤tc (base tc0) ⟧0 n


preserves-sem-base : ∀ (c : Code k) C t (tc : C ⊢[base] c :' t) t0
  (tc0 : C ⊢[base] c :' t0) (tc0≤tc : t0 ≤QFT t)
  (transform≡sub-base : sub? (infer-complete-exists c C t (base tc)) (base? (infer-basesound c C)) ≡ exists (sub tc0≤tc (base tc0)))
  → ∀ n → semCodeBase0 C tc n ≗ castQFT0 (semCtx C) t0 t tc0≤tc (semCodeBase0 C tc0 n)

preserves-sem c C (err x) tc n = \ _ → refl
preserves-sem c C (ok t) tc n x with infer-transform-canonify tc
preserves-sem c C (ok t) (exists tc) n (vs , S) | ok t0 , _ , exists tc0 , ok≤ok t0≤t , transform≡sub-base
  = preserves-sem-ok c C t tc t0 tc0 t0≤t transform≡sub-base n (tnormal vs , S) ⟨ trans ⟩ sym (cong (\ tc → semRCode0 tc n (vs , S)) transform≡sub-base)

preserves-sem-ok c C t _ t0 tc0 t0≤t transform≡sub-base n (tbranch x , S) = refl
preserves-sem-ok c C t (base tc) t0 tc0 t0≤t transform≡sub-base n (right (_ , vs) , S) = preserves-sem-base c C t tc t0 tc0 t0≤t transform≡sub-base n (vs , S)
preserves-sem-ok c C t (sub {t0 = t'} t'≤t tc) t0 tc0 t0≤t transform≡sub-base n (right (_ , vs) , S)
  with infer c C | infer-basesound c C | infer-complete  c C (ok t') (exists tc)
     | preserves-sem c C (ok t') (exists tc) n
... | ok t0 | exists base-tc0 | ok≤ok t0≤t' | IH
  with refl ← transform≡sub-base
  = (castQFT0-cong (semCtx C) t'≤t IH ⟨ ≗-trans ⟩ castQFT0-comp t0≤t' t'≤t (≤QFT-trans t0≤t' t'≤t) (semCodeBase0 C base-tc0 n)) (vs , S)

{-
preserves-sem-ok c C t (base tc) t0 tc0 t0≤t transform≡sub-base n x = preserves-sem-base c C t tc t0 tc0 t0≤t transform≡sub-base n x
preserves-sem-ok c C t (sub {t0 = t'} t'≤t tc) t0  tc0 t0≤t transform≡sub-base n
  with infer c C | infer-basesound c C | infer-complete  c C (ok t') (exists tc)
     | preserves-sem c C (ok t') (exists tc) n
... | ok t0 | exists base-tc0 | ok≤ok t0≤t' | IH
  with refl ← transform≡sub-base
  = castQFT0-cong (semCtx C) t'≤t IH ⟨ ≗-trans ⟩ castQFT0-comp t0≤t' t'≤t (≤QFT-trans t0≤t' t'≤t) (semCodeBase0 C base-tc0 n)
-}

preserves-sem-base .(atm (cons t _)) C .([] →' (t ∷ []) , uni) (atm (cons t)) .([] →' (t ∷ []) , uni)  .(atm (cons t)) .≤QFT-refl refl n
  = castQFT0-id _
preserves-sem-base .(atm (add t)) C .((t ∷ t ∷ []) →' (t ∷ []) , uni) (atm (add t)) t0  tc0 tc0≤tc refl n
  = castQFT0-id _
preserves-sem-base .(atm (store t)) C .((i32 ∷ t ∷ []) →' [] , uni) (atm (store t)) t0  tc0 tc0≤tc refl n
  = castQFT0-id _
preserves-sem-base .(atm (load t)) C .((i32 ∷ []) →' (t ∷ []) , uni) (atm (load t)) t0  tc0 tc0≤tc refl n
  = castQFT0-id _
preserves-sem-base (atm (brif-refl ℓ)) C .((i32 ∷ safe-lookup C ℓ<) →' safe-lookup C ℓ< , uni) (atm (brif-refl ℓ<)) t0  tc0 tc0≤tc transform≡sub-base n
  with ℓ <? length C | dec-yes-irr (ℓ <? length C) ≤-irrelevant ℓ<
... | yes ℓ<' | refl
  with refl ← transform≡sub-base
  = castQFT0-id _
preserves-sem-base (atm (br-refl ℓ)) C .(safe-lookup C ℓ< →' [] , bi) (br-refl ℓ<) t0  tc0 tc0≤tc transform≡sub-base n
  with ℓ <? length C | dec-yes-irr (ℓ <? length C) ≤-irrelevant ℓ<
... | yes ℓ<' | refl
  with refl ← transform≡sub-base
  = castQFT0-id _
preserves-sem-base (blk (block :' ft) is) C .(ft , uni) (blk ft (block tis)) t0  tc0 tc0≤tc transform≡sub-base n (vs , S)
  with infer is (cod ft ∷ C) | infer-basesound is (cod ft ∷ C) | infer-complete-exists is (cod ft ∷ C) (ft , uni) tis
    | preserves-sem is (cod ft ∷ C) (ok (ft , uni)) (exists tis)
... | (ok tis0) | (exists tcis0) | (ok≤ok tis0≤) | IH-is
  with tis0 ≤?QFT (ft , uni) | dec-yes-irr (tis0 ≤?QFT (ft , uni)) ≤QFT-irrelevant (ok≤ok⇒≤QFT (ok≤ok tis0≤))
... | yes tis0≤ftu | refl
  with refl ← transform≡sub-base
  rewrite IH-is n (vs , S)
  = castQFT0-id (semCodeBase0 C (blk ft (block (sub tis0≤ (base tcis0)))) n) (vs , S)

preserves-sem-base (blk (loop :' ft) is) C .(ft , uni) (blk ft (loop tis)) t0 tc0 tc0≤tc transform≡sub-base zero (vs , S)
  with infer is (dom ft ∷ C) | infer-basesound is (dom ft ∷ C) | infer-complete-exists is (dom ft ∷ C) (ft , uni) tis
    | preserves-sem is (dom ft ∷ C) (ok (ft , uni)) (exists tis)
... | (ok tis0) | (exists tcis0) | (ok≤ok tis0≤) | IH-is
  with tis0 ≤?QFT (ft , uni) | dec-yes-irr (tis0 ≤?QFT (ft , uni)) ≤QFT-irrelevant (ok≤ok⇒≤QFT (ok≤ok tis0≤))
... | yes tis0≤ftu | refl
  with refl ← transform≡sub-base
  rewrite sym (castQFT0-id (semCodeBase0 C (blk ft (loop (sub tis0≤ (base tcis0)))) zero) (vs , S))
  rewrite sym (IH-is zero (vs , S))
  with semCode0 (dom ft ∷ C) tis 0 (vs , S)
... | div = refl
... | con (right x , S') = refl
... | con (tbranch (tjump {ℓ = suc ℓ} (s≤s ℓ<) vs') , S') = refl
... | con (tbranch (tjump {ℓ = zero} (s≤s ℓ<) vs') , S') = refl

preserves-sem-base (blk (loop :' ft) is) C .(ft , uni) (blk ft (loop tis)) t0  tc0 tc0≤tc transform≡sub-base (suc n) (vs , S)
  with preserves-sem-base (blk (loop :' ft) is) C (ft , uni) (blk ft (loop tis)) t0  tc0 tc0≤tc transform≡sub-base n
... | IH-loop
  with infer is (dom ft ∷ C) | infer-basesound is (dom ft ∷ C) | infer-complete-exists is (dom ft ∷ C) (ft , uni) tis
    | preserves-sem is (dom ft ∷ C) (ok (ft , uni)) (exists tis)
... | (ok tis0) | (exists tcis0) | (ok≤ok tis0≤) | IH-is
  with tis0 ≤?QFT (ft , uni) | dec-yes-irr (tis0 ≤?QFT (ft , uni)) ≤QFT-irrelevant (ok≤ok⇒≤QFT (ok≤ok tis0≤))
... | yes tis0≤ftu | refl
  with refl ← transform≡sub-base
  rewrite sym (castQFT0-id (semCodeBase0 C (blk ft (loop (sub tis0≤ (base tcis0)))) (suc n)) (vs , S))
  rewrite sym (IH-is (suc n) (vs , S))
  with semCode0 (dom ft ∷ C) tis (suc n) (vs , S)
... | div = refl
... | con (right x , S') = refl
... | con (tbranch (tjump {ℓ = suc ℓ} (s≤s ℓ<) vs') , S') = refl
... | con (tbranch (tjump {ℓ = zero} (s≤s ℓ<) vs') , S')
  = IH-loop (vs' , S') ⟨ trans ⟩ (mapPartial-id (mapTState-id _ (\ _ → refl) P'') _ ⟨ trans ⟩ cong (semExit0 _) P)
  where P : (castQFT0 (semCtx (dom ft ∷ C)) tis0 (ft , uni) tis0≤
                      (semCodeBase0 (dom ft ∷ C) tcis0 n)
                      (safetake (dom ft)
                      (castRT (dom ft) (dom ft ++ []) (sym (++-identityʳ (dom ft))) vs') , S')) ≡ (castQFT0 (semCtx (dom ft ∷ C)) tis0 (ft , uni) tis0≤ (semCodeBase0 (dom ft ∷ C) tcis0 n) (vs' , S'))
        P rewrite (safetake-a++[]-id (dom ft) (sym (++-identityʳ (dom ft))) vs') = refl
        P'' : (q : semQT uni) →
                (λ z →
                   castRT (cod ft ++ []) (cod ft) (++-identityʳ (cod ft))
                   (z safe++
                    safedrop (dom ft)
                    (castRT (dom ft) (dom ft ++ []) (sym (++-identityʳ (dom ft)))
                     vs')))
                ≗ id
        P'' q x rewrite (safedrop-a++[]-[] (dom ft) (sym (++-identityʳ (dom ft))) vs')
            =  safe++[] (cod ft) (++-identityʳ _) _

preserves-sem-base .[] C .([] →' [] , uni) [] t0 tc0 tc0≤tc refl n
  = castQFT0-id _
preserves-sem-base (i ∷ is) C (a →' r , q) (ti ∷[ qi , m , qis ] tis) t0 tc0 tc0≤tc transform≡sub-base n (vs , S)
  with infer i C | infer-basesound i C | infer-complete i C _ (exists ti) | preserves-sem i C _ (exists ti) n
     | infer is C | infer-basesound is C | infer-complete is C _ (exists tis) | preserves-sem is C _ (exists tis) n
... | ok (a0 →' mi , qi0) | exists deriv-a0→mi | ok≤ok (a0→mi≤a→m @(≤QFT-intro qi0≤qi a0→mi⊑a→m qi0-di)) | IH-i
    | ok (mis →' r0 , qis0) | exists deriv-mis→r0 |  ok≤ok (mis→r0≤m→r @ (≤QFT-intro qis0≤qis mis→r0⊑m→r qis-dis)) | IH-is
  with mi ⊔RT mis | ⊔RT-with-proof mi mis | proof-refines-⊔RT mi mis
... | nothing | inj₂ noub | refl = ⊥-elim (noub m (mk-ub (cod-⊑ a0→mi⊑a→m) (dom-⊑ mis→r0⊑m→r)))
... | just m0 | inj₁ (m0 , m0-lub @ (mk-lub (mk-ub mi⊑m0 mis⊑m0) m0-least)) | refl
  with refl ← transform≡sub-base
  with solve-basesound qi0 a0 mi⊑m0 | op≤QFT (solve-basesound qis0 r0 mis⊑m0) | solve-completeness (≤QFT-intro qi0≤qi a0→mi⊑a→m qi0-di) (≤QFT-intro qis0≤qis mis→r0⊑m→r qis-dis) (mk-lub (mk-ub mi⊑m0 mis⊑m0) m0-least)
... | a0→mi≤a0d→m0 | mis→r0≤m0→r0d | a0d→r0d≤a→r
  with a0d→m0≤a→m →' m0→r0d≤m→r ← ≤QFT-decompose a0→mi≤a→m mis→r0≤m→r m0-lub a0d→r0d≤a→r
  with IH-i∷is ← >=>0-cong IH-i IH-is
  with cast-comp-i ← castQFT0-comp a0→mi≤a0d→m0 a0d→m0≤a→m a0→mi≤a→m (semCodeBase0 C deriv-a0→mi n)
  with cast-comp-is ← castQFT0-comp mis→r0≤m0→r0d m0→r0d≤m→r mis→r0≤m→r (semCodeBase0 C deriv-mis→r0 n)
  with cast-comp-i∷is ← >=>0-cong cast-comp-i cast-comp-is
  with comm-result ← ∷-sub-commute0 _ _ _ _ _ _ _ _ _ _ _ _ _ (sub (a0→mi≤a0d→m0) (base (deriv-a0→mi))) (sub (mis→r0≤m0→r0d) (base (deriv-mis→r0))) a0d→m0≤a→m m0→r0d≤m→r a0d→r0d≤a→r n
  = IH-i∷is (vs , S) ⟨ trans ⟩ sym (cast-comp-i∷is (vs , S)) ⟨ trans ⟩ sym (comm-result (vs , S))

semRCode0-coherent : Coherence0 semRCode0
semRCode0-coherent tc tc' n
  with infer-transform tc | infer-transform tc' | infer-transform-normalise tc tc' | preserves-sem _ _ _ tc n | preserves-sem _ _ _ tc' n
... | ntc | ntc' | ntc≡ntc' | ⟦tc⟧=⟦ntc⟧ | ⟦tc'⟧=⟦ntc'⟧ =
  let ⟦ntc⟧=⟦ntc'⟧ = cong (\tc → semRCode0 tc n) ntc≡ntc'
  in  ⟦tc⟧=⟦ntc⟧ ⟨ ≅0-trans ⟩ ≅0-reflexive ⟦ntc⟧=⟦ntc'⟧ ⟨ ≅0-trans ⟩ ≅0-sym ⟦tc'⟧=⟦ntc'⟧
