{-# OPTIONS --without-K --safe #-}
module Adequacy0 where


open import DenotationalSemantics
open import DenotationalSemantics0
open import OperationalSemantics
open import Syntax
open BigStep
open import Data.Product
open import Data.Nat
open import Syntax
open import TypeSystem
open import Data.Unit
open import BlockList hiding (_++_ ; ++-assoc ; length)
open Memory
open Store
open import Arrow
open import ListOps
open import Data.List
open import Data.Bool hiding (_<?_)
open import Function
open import Relation.Nullary.Decidable
open import Subtype
open import TypeCast
open import TypeCast0
open import Data.Nat.Properties
open import Data.List.Properties
open import Relation.Nullary
open import Data.Maybe
open import Result
open import TypeInference

open import Partial
open import UntypedLift
open import Relation.Binary.PropositionalEquality

private variable
  k : Kind


open RSub

-- cast to untyped values
eraseVT :  ∀ {rt} → semVT rt → Value
eraseVT {i32} v = (i32 , v)
eraseVT {i64} v = (i64 , v)

eraseRT : ∀ {rt} → semRT rt → OpeStk
eraseRT {[]} [] = []
eraseRT {vt ∷ rt} (v ∷ vs) = eraseVT v ∷ eraseRT vs

eraseRT++ : ∀ {rt rt'} → (vs : semRT rt) → (vs' : semRT rt') → eraseRT (vs safe++ vs') ≡ eraseRT vs ++ eraseRT vs'
eraseRT++ {[]} {rt'} [] vs' = refl
eraseRT++ {vt ∷ rt} {rt'} (v ∷ vs) vs' = cong (_∷_ (eraseVT v)) (eraseRT++ vs vs')

-- TODO OpStk → OpeStk
eraseRT∘castRT≡eraseRT : ∀ {rt rt'} → (p : rt ≡ rt') → (vs : semRT rt) → eraseRT (castRT rt rt' p vs) ≡ eraseRT vs
eraseRT∘castRT≡eraseRT refl vs = cong eraseRT (castRT-refl-id vs)

eraseRTPair : ∀ {rt D} → semRT rt × semRT D → OpeStk × OpeStk
eraseRTPair (vs , vs') = eraseRT vs , eraseRT vs'

eraseBranchType : ∀ {C} → semCtx C → ℕ × OpeStk
eraseBranchType (tjump {ℓ} ℓ< vs) = ℓ , eraseRT vs

eraseNormalType : ∀ {q vt} → semQT q × semRT vt → OpeStk
eraseNormalType (_ , vs) = eraseRT vs


eraseStateType : ∀ {C rt} → semQRT (semCtx C) rt → State
eraseStateType (tbranch b , S) = branch (eraseBranchType b) , S
eraseStateType (right v , S) = normal (eraseNormalType v) , S

eraseStateType∘castQRT≡eraseStateType : ∀ {C qrt qrt'} → (p : qrt ≤QRT qrt') → (st : semQRT (semCtx C) qrt) → eraseStateType (castQRT (semCtx C) qrt qrt' p st) ≡ eraseStateType st
eraseStateType∘castQRT≡eraseStateType (≤QRT-intro q≤q' uni-id) (tbranch b , S) = refl
eraseStateType∘castQRT≡eraseStateType (≤QRT-intro q≤q' uni-id) (right (qv , vs) , S) = cong (\ p → normal p , S) (eraseRT∘castRT≡eraseRT (UniId⇒QId uni-id qv) vs)

safe-checkVal : ∀ vt → (v : semVT (vt)) → checkVal vt (eraseVT v) ≡ true
safe-checkVal i32 v = refl
safe-checkVal i64 v = refl

safesplit-refines-checkStk : ∀ rt {D} → (vs : semRT (rt ++ D)) → checkStk rt (eraseRT vs) ≡ ok (eraseRTPair (safesplit rt vs))
safesplit-refines-checkStk [] {D} vs = refl
safesplit-refines-checkStk (vt ∷ rt) {D} (v ∷ vs)
  with checkVal vt (eraseVT v) | safe-checkVal vt v
... | true | refl
  with checkStk rt (eraseRT vs) | safesplit-refines-checkStk rt vs
... | ok (taken , dropped) | refl = refl

checkStk-ok : ∀ {rt} (vs : semRT rt) → checkStk rt (eraseRT vs) ≡ ok (eraseRT vs , [])
checkStk-ok [] = refl
checkStk-ok {r ∷ rt} (v ∷ vs)
  with checkVal r (eraseVT v) | safe-checkVal r v
... | true | refl
  with checkStk rt (eraseRT vs) | checkStk-ok vs
... | .(ok (eraseRT vs , [])) | refl = refl

checkStk-ok' : ∀ rt {d} (vs : semRT (rt ++ d)) → checkStk rt (eraseRT vs) ≡ ok (eraseRT (safetake rt vs) , eraseRT (safedrop rt vs))
checkStk-ok' [] vs = refl
checkStk-ok' (r ∷ rt) (v ∷ vs)
  with checkVal r (eraseVT v) | safe-checkVal r v
... | true | refl
  with checkStk rt (eraseRT vs) | checkStk-ok' rt vs
... | .(ok (eraseRT (safetake rt vs) , eraseRT (safedrop rt vs))) | refl = refl

safesplit=safetake×safedrop : ∀ rt {D} → (vs : semRT (rt ++ D)) → proj₁ (safesplit rt vs) ≡ safetake rt vs × proj₂ (safesplit rt vs) ≡ safedrop rt vs
safesplit=safetake×safedrop rt vs = refl , refl

castRT-refl∘castRT-refl : ∀ d → (castRT d d refl ∘ castRT d d refl) ≗ id
castRT-refl∘castRT-refl d vs = castRT-refl-id (castRT d d refl vs) ⟨ trans ⟩ castRT-refl-id vs
safetake++drop : ∀ a d (vs : semRT (a ++ d)) → safetake a vs safe++ safedrop a vs ≡ vs
safetake++drop [] d vs = refl
safetake++drop (x ∷ a) d (x₁ ∷ vs) = cong (_∷_ x₁) (safetake++drop a d vs)

safetake-safe++ : ∀ {d d'} (vs : semRT d) (vs' : semRT d') → safetake d (vs safe++ vs') ≡ vs
safetake-safe++ {[]} [] vs' = refl
safetake-safe++ {x ∷ d} (v ∷ vs) vs' = cong (_∷_ v) (safetake-safe++ vs vs') 
safedrop-safe++ : ∀ {d d'} (vs : semRT d) (vs' : semRT d') → safedrop d (vs safe++ vs') ≡ vs'
safedrop-safe++ {[]} [] vs' = refl
safedrop-safe++ {x ∷ d} (v ∷ vs) vs' = safedrop-safe++ vs vs'

castRT-lemma : ∀ a d vs → castRT (a ++ d)
      (a ++ d) refl
      (safetake a
       (castRT (a ++ d)
        (a ++ d) refl vs)
       safe++
       safedrop a
       (castRT (a ++ d)
        (a ++ d) refl vs)) ≡ vs
castRT-lemma a d vs = castRT-refl-id (safetake a (castRT (a ++ d) (a ++ d) refl vs) safe++ safedrop a (castRT (a ++ d) (a ++ d) refl vs)) ⟨ trans ⟩ (safetake++drop a d (castRT (a ++ d) (a ++ d) refl vs) ⟨ trans ⟩ castRT-refl-id vs)

adequacy-sub : ∀ (c : Code k) C t t' → (deriv : C ⊢ c :' t) → (t≤t' : t ≤QFT t') → ∀ lc vs uvs S
  → eraseRT vs ≡ uvs
  → bigstep lc c C (normal uvs , S) ≡ mapPartial eraseStateType ((semCode0 C (sub t≤t' deriv) lc) (vs , S))
adequacy-sub (atm (cons i32 z)) C .([] →' (i32 ∷ []) , uni) .(d →' ((i32 ∷ []) ++ d) , uni) (base (atm (cons i32))) (mkuni≤ d d) lc vs .(eraseRT vs) S refl
  = cong (\v → con (normal (_ ∷ eraseRT v) , S)) (sym (castRT-refl∘castRT-refl d vs))
adequacy-sub (atm (cons i64 z)) C .([] →' (i64 ∷ []) , uni) .(d →' ((i64 ∷ []) ++ d) , uni) (base (atm (cons i64))) (mkuni≤ d d) lc vs .(eraseRT vs) S refl
  = cong (\v → con (normal (_ ∷ eraseRT v) , S)) (sym (castRT-refl∘castRT-refl d vs))
adequacy-sub .(atm (add i32)) C .((i32 ∷ i32 ∷ []) →' (i32 ∷ []) , uni) .(((i32 ∷ i32 ∷ []) ++ d) →' ((i32 ∷ []) ++ d) , uni) (base (atm (add i32))) (mkuni≤ d d) lc (x ∷ (x₁ ∷ vs)) _ S refl
  = cong (\v → con (normal (_ ∷ eraseRT v) , S)) (sym (castRT-refl∘castRT-refl d vs)) 
adequacy-sub .(atm (add i64)) C .((i64 ∷ i64 ∷ []) →' (i64 ∷ []) , uni) .(((i64 ∷ i64 ∷ []) ++ d) →' ((i64 ∷ []) ++ d) , uni) (base (atm (add i64))) (mkuni≤ d d) lc (x ∷ (x₁ ∷ vs)) _ S refl
  = cong (\v → con (normal (_ ∷ eraseRT v) , S)) (sym (castRT-refl∘castRT-refl d vs))
adequacy-sub .(atm (store i32)) C .((i32 ∷ i32 ∷ []) →' [] , uni) .(((i32 ∷ i32 ∷ []) ++ d) →' d , uni) (base (atm (store i32))) (mkuni≤ d d) lc (x ∷ (x₁ ∷ vs)) ._ S refl
  = cong (\v → con (normal (eraseRT v) , _)) (sym (castRT-refl∘castRT-refl d vs))
adequacy-sub .(atm (store i64)) C .((i32 ∷ i64 ∷ []) →' [] , uni) .(((i32 ∷ i64 ∷ []) ++ d) →' d , uni) (base (atm (store i64))) (mkuni≤ d d) lc (x ∷ (x₁ ∷ vs)) ._ S refl
  = cong (\v → con (normal (eraseRT v) , _)) (sym (castRT-refl∘castRT-refl d vs))
adequacy-sub .(atm (load i32)) C .((i32 ∷ []) →' (i32 ∷ []) , uni) .(((i32 ∷ []) ++ d) →' ((i32 ∷ []) ++ d) , uni) (base (atm (load i32))) (mkuni≤ d d) lc (x ∷ vs) ._ S refl
  = cong (\v → con (normal (_ ∷ eraseRT v) , _)) (sym (castRT-refl∘castRT-refl d vs))
adequacy-sub .(atm (load i64)) C .((i32 ∷ []) →' (i64 ∷ []) , uni) .(((i32 ∷ []) ++ d) →' ((i64 ∷ []) ++ d) , uni) (base (atm (load i64))) (mkuni≤ d d) lc (x ∷ vs) ._ S refl
  = cong (\v → con (normal (_ ∷ eraseRT v) , _)) (sym (castRT-refl∘castRT-refl d vs))
adequacy-sub (atm (brif-refl ℓ)) C .((i32 ∷ safe-lookup C ℓ<) →' safe-lookup C ℓ< , uni) .(((i32 ∷ safe-lookup C ℓ<) ++ d) →' (safe-lookup C ℓ< ++ d) , uni) (base (atm (brif-refl ℓ<))) (mkuni≤ d d) lc ((zero , _) ∷ vs) _ S refl
  = cong (\v → con (normal (eraseRT v) , S)) (sym (castRT-lemma _ d vs))
adequacy-sub (atm (brif-refl ℓ)) C .((i32 ∷ safe-lookup C ℓ<) →' safe-lookup C ℓ< , uni) .(((i32 ∷ safe-lookup C ℓ<) ++ d) →' (safe-lookup C ℓ< ++ d) , uni) (base (atm (brif-refl ℓ<))) (mkuni≤ d d) lc ((suc n , _) ∷ vs) _ S refl
  with ℓ <? length C | dec-yes-irr (ℓ <? length C) ≤-irrelevant ℓ<
... | yes ℓ<' | refl
  with dropCtx C ℓ | safe-dropCtx C ℓ< | safe-dropCtx-refines-dropCtx C ℓ ℓ<
... | .(just (rt , C')) | (rt , C') | refl
  with checkStk rt (eraseRT vs) | checkStk-ok' rt vs
... | .(ok (eraseRT (safetake rt vs) , eraseRT (safedrop rt vs))) | refl
  = cong (\v → con (branch (ℓ , eraseRT (safetake rt v)) , S)) (sym (castRT-refl-id vs))
adequacy-sub (atm (br-refl ℓ)) C .(safe-lookup C ℓ< →' [] , bi) .(_ , _) (base (br-refl ℓ<)) (mkbi≤ d e) lc vs _ S refl
  with ℓ <? length C | dec-yes-irr (ℓ <? length C) ≤-irrelevant ℓ<
... | yes ℓ<' | refl
  with dropCtx C ℓ | safe-dropCtx C ℓ< | safe-dropCtx-refines-dropCtx C ℓ ℓ<
... | .(just (rt , C')) | (rt , C') | refl
  with checkStk rt (eraseRT vs) | checkStk-ok' rt vs
... | .(ok (eraseRT (safetake rt vs) , eraseRT (safedrop rt vs))) | refl
  = cong (\v → con (branch (ℓ , eraseRT (safetake rt v)) , S)) (sym (castRT-refl-id vs))
adequacy-sub (blk (block :' ft) is) C .(ft , uni) .((dom ft ++ d) →' (cod ft ++ d) , uni) (base (blk ft (block tis))) (mkuni≤ d d) lc vs .(eraseRT vs) S refl
  with checkStk (dom ft) (eraseNormalType (tt , vs)) | checkStk-ok' (dom ft) vs
... | .(ok (eraseRT (safetake (dom ft) vs) , eraseRT (safedrop (dom ft) vs))) | refl
  with bigstep lc is (cod ft ∷ C) (normal (eraseRT (safetake (dom ft) vs)) , S) | semCode0 (cod ft ∷ C) tis lc (safetake (dom ft) (castRT (dom ft ++ d) (dom ft ++ d) refl vs) , S)
     | adeq'
     -- | adequacy-sub is (cod ft ∷ C) (ft , uni) (ft , uni) tis ≤QFT-refl lc (safetake (dom ft) vs) (eraseRT (safetake (dom ft) vs)) S refl ⟨ trans ⟩ {!!}
     where D : castQFT0 _ _ _ ≤QFT-refl (semCode0 (cod ft ∷ C) tis lc) (safetake (dom ft) vs , S)
                ≡
               semCode0 (cod ft ∷ C) tis lc
                (safetake (dom ft) (castRT (dom ft ++ d) (dom ft ++ d) refl vs) , S)
           D = castQFT0-refl-id _ {f = semCode0 (cod ft ∷ C) tis lc} (safetake (dom ft) vs , S) ⟨ trans ⟩ cong (\v → semCode0 (cod ft ∷ C) tis lc (safetake (dom ft) v , S)) (sym (castRT-refl-id vs))
           adeq' : bigstep lc is (cod ft ∷ C) (normal (eraseRT (safetake (dom ft) vs)) , S) ≡ mapPartial eraseStateType (semCode0 (cod ft ∷ C) tis lc (safetake (dom ft) (castRT (dom ft ++ d) (dom ft ++ d) refl vs) , S))
           adeq' = adequacy-sub is (cod ft ∷ C) (ft , uni) (ft , uni) tis ≤QFT-refl lc (safetake (dom ft) vs) (eraseRT (safetake (dom ft) vs)) S refl ⟨ trans ⟩ cong (mapPartial eraseStateType) D
... | ._ | div | refl = refl
... | ._ | con (tbranch (tjump {ℓ = suc ℓ} (s≤s ℓ<) vs') , S') | refl = refl
... | ._ | con (right (_ , vs') , S') | refl
  = cong (\v → con (normal v , S')) (sym (eraseRT++ vs' (safedrop (dom ft) vs)) ⟨ trans ⟩
         cong eraseRT (sym (castRT-refl-id _) ⟨ trans ⟩
           cong (\v → castRT _ _ refl (vs' safe++ (safedrop (dom ft) v))) (sym (castRT-refl-id vs))))
... | ._ | con (tbranch (tjump {ℓ = zero} ℓ< vs') , S') | refl
  = cong (\v → con (normal v , S')) (sym (eraseRT++ vs' (safedrop (dom ft) vs)) ⟨ trans ⟩
         cong eraseRT (sym (castRT-refl-id _) ⟨ trans ⟩
           cong (\v → castRT _ _ refl (vs' safe++ (safedrop (dom ft) v))) (sym (castRT-refl-id vs))))
adequacy-sub (blk (loop :' ft) is) C .(ft , uni) .((dom ft ++ d) →' (cod ft ++ d) , uni) (base (blk ft (loop tis))) (mkuni≤ d d) zero vs .(eraseRT vs) S refl
  with checkStk (dom ft) (eraseNormalType (tt , vs)) | checkStk-ok' (dom ft) vs
... | .(ok (eraseRT (safetake (dom ft) vs) , eraseRT (safedrop (dom ft) vs))) | refl
  with bigstep zero is (dom ft ∷ C) (normal (eraseRT (safetake (dom ft) vs)) , S) | semCode0 (dom ft ∷ C) tis zero (safetake (dom ft) (castRT (dom ft ++ d) (dom ft ++ d) refl vs) , S)
     | adeq'
     -- | adequacy-sub is (dom ft ∷ C) (ft , uni) (ft , uni) tis ≤QFT-refl lc (safetake (dom ft) vs) (eraseRT (safetake (dom ft) vs)) S refl ⟨ trans ⟩ {!!}
     where D : castQFT0 _ _ _ ≤QFT-refl (semCode0 (dom ft ∷ C) tis zero) (safetake (dom ft) vs , S)
                ≡
               semCode0 (dom ft ∷ C) tis zero
                (safetake (dom ft) (castRT (dom ft ++ d) (dom ft ++ d) refl vs) , S)
           D = castQFT0-refl-id _ {f = semCode0 (dom ft ∷ C) tis zero} (safetake (dom ft) vs , S) ⟨ trans ⟩ cong (\v → semCode0 (dom ft ∷ C) tis zero (safetake (dom ft) v , S)) (sym (castRT-refl-id vs))
           adeq' : bigstep zero is (dom ft ∷ C) (normal (eraseRT (safetake (dom ft) vs)) , S) ≡ mapPartial eraseStateType (semCode0 (dom ft ∷ C) tis zero (safetake (dom ft) (castRT (dom ft ++ d) (dom ft ++ d) refl vs) , S))
           adeq' = adequacy-sub is (dom ft ∷ C) (ft , uni) (ft , uni) tis ≤QFT-refl zero (safetake (dom ft) vs) (eraseRT (safetake (dom ft) vs)) S refl ⟨ trans ⟩ cong (mapPartial eraseStateType) D
... | ._ | div | refl = refl
... | ._ | con (tbranch (tjump {ℓ = suc ℓ} (s≤s ℓ<) vs') , S') | refl = refl
... | ._ | con (right (_ , vs') , S') | refl
  = cong (\v → con (normal v , S')) (sym (eraseRT++ vs' (safedrop (dom ft) vs)) ⟨ trans ⟩
         cong eraseRT (sym (castRT-refl-id _) ⟨ trans ⟩
           cong (\v → castRT _ _ refl (vs' safe++ (safedrop (dom ft) v))) (sym (castRT-refl-id vs))))
... | ._ | con (tbranch (tjump {ℓ = zero} ℓ< vs') , S') | refl = refl
adequacy-sub (blk (loop :' ft) is) C .(ft , uni) .((dom ft ++ d) →' (cod ft ++ d) , uni) (base (blk ft (loop tis))) (mkuni≤ d d) (suc lc) vs .(eraseRT vs) S refl
  with IH-loop ← adequacy-sub (blk (loop :' ft) is) C (ft , uni) ((dom ft ++ d) →' (cod ft ++ d) , uni) (base (blk ft (loop tis))) (mkuni≤ d d) lc
  with checkStk (dom ft) (eraseNormalType (tt , vs)) | checkStk-ok' (dom ft) vs
... | .(ok (eraseRT (safetake (dom ft) vs) , eraseRT (safedrop (dom ft) vs))) | refl
  with bigstep (suc lc) is (dom ft ∷ C) (normal (eraseRT (safetake (dom ft) vs)) , S) | semCode0 (dom ft ∷ C) tis (suc lc) (safetake (dom ft) (castRT (dom ft ++ d) (dom ft ++ d) refl vs) , S)
     | adeq'
     -- | adequacy-sub is (dom ft ∷ C) (ft , uni) (ft , uni) tis ≤QFT-refl lc (safetake (dom ft) vs) (eraseRT (safetake (dom ft) vs)) S refl ⟨ trans ⟩ {!!}
     where D : castQFT0 _ _ _ ≤QFT-refl (semCode0 (dom ft ∷ C) tis (suc lc)) (safetake (dom ft) vs , S)
                ≡
               semCode0 (dom ft ∷ C) tis (suc lc)
                (safetake (dom ft) (castRT (dom ft ++ d) (dom ft ++ d) refl vs) , S)
           D = castQFT0-refl-id _ {f = semCode0 (dom ft ∷ C) tis (suc lc)} (safetake (dom ft) vs , S) ⟨ trans ⟩ cong (\v → semCode0 (dom ft ∷ C) tis (suc lc) (safetake (dom ft) v , S)) (sym (castRT-refl-id vs))
           adeq' : bigstep (suc lc) is (dom ft ∷ C) (normal (eraseRT (safetake (dom ft) vs)) , S) ≡ mapPartial eraseStateType (semCode0 (dom ft ∷ C) tis (suc lc) (safetake (dom ft) (castRT (dom ft ++ d) (dom ft ++ d) refl vs) , S))
           adeq' = adequacy-sub is (dom ft ∷ C) (ft , uni) (ft , uni) tis ≤QFT-refl (suc lc) (safetake (dom ft) vs) (eraseRT (safetake (dom ft) vs)) S refl ⟨ trans ⟩ cong (mapPartial eraseStateType) D
... | ._ | div | refl = refl
... | ._ | con (tbranch (tjump {ℓ = suc ℓ} (s≤s ℓ<) vs') , S') | refl = refl
... | ._ | con (right (_ , vs') , S') | refl
  = cong (\v → con (normal v , S')) (sym (eraseRT++ vs' (safedrop (dom ft) vs)) ⟨ trans ⟩
         cong eraseRT (sym (castRT-refl-id _) ⟨ trans ⟩
           cong (\v → castRT _ _ refl (vs' safe++ (safedrop (dom ft) v))) (sym (castRT-refl-id vs))))
... | ._ | con (tbranch (tjump {ℓ = zero} ℓ< vs') , S') | refl
  rewrite IH-loop (vs' safe++ safedrop (dom ft) vs) (eraseRT vs' ++ (eraseRT (safedrop (dom ft) vs))) S' (eraseRT++ vs' (safedrop (dom ft) vs))
  rewrite castRT-refl-id (vs' safe++ safedrop (dom ft) vs)
  rewrite safetake-safe++ vs' (safedrop (dom ft) vs)
  rewrite castRT-refl-id vs
  rewrite safedrop-safe++ vs' (safedrop (dom ft) vs)
  = refl
adequacy-sub .[] C .([] →' [] , uni) .(_ , _) (base []) (mkuni≤ d d) lc vs .(eraseRT vs) S refl
  = cong (\v → con (normal (eraseRT v) , S)) (sym (castRT-refl∘castRT-refl d vs))
adequacy-sub (i ∷ is) C (a →' r , .(bi ⊓QT qis)) (_ →' _ , _) (base (ti ∷[ bi , m , qis ] tis)) (≤QFT-intro qiqis≤q ((d , refl) →' (e , refl)) qiqis-d=e) lc vs .(eraseRT vs) S refl
  rewrite adequacy-sub i C (a →' m , bi) ((a ++ d) →' (m ++ e) , bi) ti (mkbi≤ d e) lc vs (eraseRT vs) S refl
  with semCode0 C ti lc (safetake a (castRT (a ++ d) (a ++ d) refl vs) , S)
... | div = refl
... | con (tbranch (tjump ℓ< vs') , S') = bigstep-con-on-branch lc is C _ S'
adequacy-sub (i ∷ is) C (a →' r , .(uni ⊓QT qis)) (_ →' _ , _) (base (ti ∷[ uni , m , qis ] tis)) (≤QFT-intro qiqis≤q ((d , refl) →' (e , refl)) qiqis-d=e) lc vs .(eraseRT vs) S refl
  rewrite adequacy-sub i C (a →' m , uni) ((a ++ d) →' (m ++ d) , uni) ti (mkuni≤ d d) lc vs (eraseRT vs) S refl
  with semCode0 C ti lc (safetake a (castRT (a ++ d) (a ++ d) refl vs) , S)
... | div = refl
... | con (tbranch (tjump ℓ< vs') , S') = bigstep-con-on-branch lc is C _ S'
adequacy-sub (i ∷ is) C (a →' r , .(uni ⊓QT bi)) (.(a ++ d) →' .(r ++ e) , _) (base (ti ∷[ uni , m , bi ] tis)) (≤QFT-intro qiqis≤q ((d , refl) →' (e , refl)) qiqis-d=e) lc vs .(eraseRT vs) S refl | con (tnormal vs' , S')
  rewrite castRT-refl-id vs
  rewrite castRT-refl-id (vs' safe++ safedrop a vs)
  rewrite adequacy-sub is C (m →' r , bi) ((m ++ d) →' (r ++ e) , bi) tis (mkbi≤ d e) lc (vs' safe++ safedrop a vs) (eraseRT (vs' safe++ safedrop a vs))  S' refl
  rewrite castRT-refl-id (vs' safe++ safedrop a vs)
  rewrite safetake-safe++ vs' (safedrop a vs)
  with semCode0 C tis lc (vs' , S')
... | div = refl
... | con (tbranch x , snd) = refl
adequacy-sub (i ∷ is) C (a →' r , .(uni ⊓QT uni)) (.(a ++ d) →' .(r ++ d) , uni) (base (ti ∷[ uni , m , uni ] tis)) (≤QFT-intro uni≤uni ((d , refl) →' (d , refl)) refl) lc vs .(eraseRT vs) S refl | con (tnormal vs' , S')
  rewrite castRT-refl-id vs
  rewrite castRT-refl-id (vs' safe++ safedrop a vs)
  rewrite adequacy-sub is C (m →' r , uni) ((m ++ d) →' (r ++ d) , uni) tis (mkuni≤ d d) lc (vs' safe++ safedrop a vs) (eraseRT (vs' safe++ safedrop a vs)) S' refl
  rewrite castRT-refl-id (vs' safe++ safedrop a vs)
  rewrite safetake-safe++ vs' (safedrop a vs)
  with semCode0 C tis lc (vs' , S')
... | div = refl
... | con (tbranch x , S'') = refl
... | con (tnormal _ , S'')
  rewrite safedrop-safe++ vs' (safedrop a vs)
  = refl 
adequacy-sub c C t' t (sub {t0} t≤t' tc) t'≤t'' lc vs .(eraseRT vs) S refl = adequacy-sub c C t0 t tc (≤QFT-trans t≤t' t'≤t'') lc vs (eraseRT vs) S refl ⟨ trans ⟩ sym (cong (mapPartial eraseStateType) (castQFT0-trans-comp (semCtx C) t≤t' t'≤t'' {f = semCode0 C tc lc} (vs , S)))

adequacy0 : ∀ (c : Code k) C t →
  (deriv : C ⊢ c :' t) → ∀ lc st ust → eraseStateType st ≡ ust
  → bigstep lc c C ust ≡ mapPartial eraseStateType (⟦ deriv ⟧0 lc st)
adequacy0 c C t tc lc (tbranch b , S) (branch b' , S) refl
  rewrite bigstep-con-on-branch lc c C b' S
  = refl
adequacy0 c C t tc lc (tnormal vs , S) (normal uvs , S) refl = adequacy-sub c C t t tc ≤QFT-refl lc vs uvs S refl ⟨ trans ⟩ cong (mapPartial eraseStateType) (castQFT0-refl-id (semCtx C) {f = (semCode0 C tc lc)} (vs , S))
