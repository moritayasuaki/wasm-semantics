{-# OPTIONS --without-K --safe #-}
module Adequacy where


open import DenotationalSemantics
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

eraseStateType∘f∘castQRT≡eraseStateType∘castQFT∘f
  : ∀ {C qft qft'} → (qft≤ : qft ≤QFT qft') → (f : ∀ D → semQFT (semCtx C) (semCtx C) qft D) → ∀ D D' qrt≤
    → mapPartial eraseStateType ∘ f D ∘ castQRT _ _ _ qrt≤ ≗ mapPartial eraseStateType ∘ castQFT _ _ qft qft' qft≤ f D'
eraseStateType∘f∘castQRT≡eraseStateType∘castQFT∘f
  {C = C} {qft = a0 →' r0 , q0} {qft' = a →' r , q}
  (≤QFT-intro q0≤q ((da , a0++da=a) →' (dr , r0++dr=r)) q-id) f D0 D (≤QRT-intro uni≤uni a++D=a0++D0) x
   with refl ← ++-cancelˡ a0 (sym (++-assoc a0 da D) ⟨ trans ⟩ (cong (\p → p ++ D) a0++da=a) ⟨ trans ⟩ a++D=a0++D0)
   with refl ← ≤QRT-irrelevant (≤QRT-intro uni≤uni (sym (trans (sym (++-assoc a0 da D)) (cong (λ P₁ → P₁ ++ D) a0++da=a)))) (≤QRT-intro uni≤uni a++D=a0++D0)
   with f (da ++ D) (castQRT _ _ _ (≤QRT-intro uni≤uni a++D=a0++D0) x)
... | div = refl
... | con (tbranch b , S) = refl
... | con (right (qv , vs) , S)
  with refl ← UniId⇒QId q-id qv = cong (\ t → con (normal t , S)) (sym (eraseRT∘castRT≡eraseRT _ vs))

eraseStateType∘castQFT∘f∘castQRT=f
  : ∀ {C qft qft'} → (qft≤ : qft ≤QFT qft') → (f : ∀ D → semQFT (semCtx C) (semCtx C) qft D) → ∀ D D' qrt≤
    → mapPartial eraseStateType ∘ ((castQFT _ _ qft qft' qft≤ f D') ∘ castQRT _ _ _ qrt≤) ≗ mapPartial eraseStateType ∘ (f D)
eraseStateType∘castQFT∘f∘castQRT=f {C = C} {qft = a →' r , q} {qft' = a' →' r' , q'} (≤QFT-intro q≤q' ((da , a++da=a') →' (dr , r++dr=r')) q-uid) f D D' (≤QRT-intro uni≤uni a++D≡a'++D') x
  rewrite castQRT-trans-comp _ (≤QRT-intro uni≤uni a++D≡a'++D') (≤-proof-dom-dom D' da a++da=a') x
  with refl ← a++da=a'
  with refl ← r++dr=r'
  with refl ← ++-cancelˡ a (a++D≡a'++D' ⟨ trans ⟩ ++-assoc a da D')
  rewrite uipRT (trans a++D≡a'++D' (sym (trans (sym (++-assoc a da D')) refl))) refl
  rewrite castQRT-refl-id _ x
  with f (da ++ D') x
... | div = refl
... | con (tbranch b , S) = refl
... | con (right (qv , vs) , S)
  with refl ← UniId⇒QId q-uid qv
  with uni ← q
  = cong con (eraseStateType∘castQRT≡eraseStateType {C = C} (≤QRT-intro uni≤uni ((trans (sym (++-assoc r da D')) (cong (λ P → P ++ D') (trans (cong (_++_ r) (UniId⇒QId q-uid tt)) refl))))) (right (qv , vs) , S))



safe-checkVal : ∀ vt → (v : semVT (vt)) → checkVal vt (eraseVT v) ≡ true
safe-checkVal i32 v = refl
safe-checkVal i64 v = refl

safesplit-refines-checkStk : ∀ rt {D} → (vs : semRT (rt ++ D)) → checkStk rt (eraseRT vs) ≡ ok (eraseRTPair (safesplit rt vs))
safesplit-refines-checkStk [] {D} vs = refl
safesplit-refines-checkStk (vt ∷ rt) {D} (v ∷ vs) with checkVal vt (eraseVT v) | safe-checkVal vt v
... | true | refl rewrite erefl tt
  with checkStk rt (eraseRT vs) | safesplit-refines-checkStk rt vs
... | ok (taken , dropped) | refl = refl

safesplit=safetake×safedrop : ∀ rt {D} → (vs : semRT (rt ++ D)) → proj₁ (safesplit rt vs) ≡ safetake rt vs × proj₂ (safesplit rt vs) ≡ safedrop rt vs
safesplit=safetake×safedrop rt vs = refl , refl


adequacy :
  ∀ (c : Code k) C t → (deriv : C ⊢ c :' t) → ∀ n D st ust
  → eraseStateType st ≡ ust
  → bigstep n c C ust ≡ mapPartial eraseStateType (⟦ deriv ⟧ n D st)
adequacy c C t tc lc D (tbranch b , S) (branch b' , S) refl
  rewrite semCode-con-on-tbranch tc lc D b S
  rewrite bigstep-con-on-branch lc c C b' S
  = refl
adequacy .(atm (cons i32 _)) C .([] →' (i32 ∷ []) , uni) (base (atm (cons i32))) n D (right x , S) (normal x' , S) refl = refl
adequacy .(atm (cons i64 _)) C .([] →' (i64 ∷ []) , uni) (base (atm (cons i64))) n D (right x , S) (normal x' , S) refl = refl
adequacy .(atm (add i32)) C .((i32 ∷ i32 ∷ []) →' (i32 ∷ []) , uni) (base (atm (add i32))) n D (tnormal (_ ∷ _ ∷ _) , S) (normal (_ ∷ _ ∷ _) , S) refl = refl
adequacy .(atm (add i64)) C .((i64 ∷ i64 ∷ []) →' (i64 ∷ []) , uni) (base (atm (add i64))) n D (tnormal (_ ∷ _ ∷ _) , S) (normal (_ ∷ _ ∷ _) , S) refl = refl
adequacy .(atm (store i32)) C .((i32 ∷ i32 ∷ []) →' [] , uni) (base (atm (store i32))) n D (tnormal (_ ∷ _ ∷ _) , S) (normal (_ ∷ _ ∷ _) , S) refl = refl
adequacy .(atm (store i64)) C .((i32 ∷ i64 ∷ []) →' [] , uni) (base (atm (store i64))) n D (tnormal (_ ∷ _ ∷ _) , S) (normal (_ ∷ _ ∷ _) , S) refl = refl
adequacy .(atm (load i32)) C .((i32 ∷ []) →' (i32 ∷ []) , uni) (base (atm (load i32))) n D (tnormal (_ ∷ _) , S) (normal (_ ∷ _) , S) refl = refl
adequacy .(atm (load i64)) C .((i32 ∷ []) →' (i64 ∷ []) , uni) (base (atm (load i64))) n D (tnormal (_ ∷ _) , S) (normal (_ ∷ _) , S) refl = refl
adequacy .(atm (brif-refl _)) C .((i32 ∷ safe-lookup C ℓ<) →' safe-lookup C ℓ< , uni) (base (atm (brif-refl ℓ<))) n D (tnormal ((zero , _) ∷ _) , S) (normal (_ ∷ _) , S) refl = refl
adequacy (atm (brif-refl ℓ)) C .((i32 ∷ safe-lookup C ℓ<) →' safe-lookup C ℓ< , uni) (base (atm (brif-refl ℓ<))) n D (tnormal ((suc z , _) ∷ vs) , S) (normal (_ ∷ _) , S) refl
  with ℓ <? length C | dec-yes-irr (ℓ <? length C) ≤-irrelevant ℓ<
... | yes ℓ<' | refl
  with dropCtx C ℓ | safe-dropCtx C ℓ< | safe-dropCtx-refines-dropCtx C ℓ ℓ<
... | (just (rt , C')) | (rt , C') | refl
  with checkStk rt (eraseRT vs) | safesplit rt vs | safesplit-refines-checkStk rt vs
... | _ | _ | refl
  = refl
adequacy (atm (br-refl ℓ)) C .(safe-lookup C ℓ< →' [] , bi) (base (br-refl ℓ<)) n D (tnormal vs , S) (normal _ , S) refl
  with ℓ <? length C | dec-yes-irr (ℓ <? length C) ≤-irrelevant ℓ<
... | yes ℓ<' | refl
  with dropCtx C ℓ | safe-dropCtx C ℓ< | safe-dropCtx-refines-dropCtx C ℓ ℓ<
... | (just (rt , C')) | (rt , C') | refl
  with checkStk rt (eraseRT vs) | safesplit rt vs | safesplit-refines-checkStk rt vs
... | _ | _ | refl
  = refl
adequacy (blk (block :' ft) is) C .(ft , uni) (base (blk ft (block tis))) n D (tnormal vs , S) (normal _ , S) refl
   with checkStk (dom ft) (eraseNormalType (tt , vs)) | safedrop (dom ft) vs | safetake (dom ft) vs | safesplit-refines-checkStk (dom ft) vs
... | ok (top-vs , res-vs) | t-res-vs | t-top-vs | refl
  with bigstep n is (cod ft ∷ C) (normal top-vs , S) | semCode (cod ft ∷ C) tis n [] (tnormal (t-top-vs safe++ []) , S)
     | adequacy is (cod ft ∷ C) (ft , uni) tis n [] (tnormal (t-top-vs safe++ []) , S) (normal top-vs , S) (cong (\t → normal t , S) (eraseRT++ t-top-vs [] ⟨ trans ⟩ ++-identityʳ _))
... | div | div | refl = refl
... | con ._ | con (tbranch (tjump {ℓ = zero} (s≤s ℓ<) vs') , S') | refl = cong (\ p → con (normal p , S')) (sym (eraseRT++ vs' t-res-vs))
... | con ._ | con (tbranch (tjump {ℓ = suc ℓ} (s≤s ℓ<) vs') , S') | refl = refl
... | con ._ | con (tnormal vs' , S') | refl = cong (\ p → con (normal p , S')) ( sym (eraseRT++ vs' t-res-vs) ⟨ trans ⟩ sym (eraseRT∘castRT≡eraseRT _ (vs' safe++ t-res-vs)))
adequacy (blk (loop :' ft) is) C .(ft , uni) (base (blk ft (loop tis))) n D (tnormal vs , S) (normal _ , S) refl
   with checkStk (dom ft) (eraseNormalType (tt , vs)) | safedrop (dom ft) vs | safetake (dom ft) vs | safesplit-refines-checkStk (dom ft) vs
... | ok (top-vs , res-vs) | t-res-vs | t-top-vs | refl
  with bigstep n is (dom ft ∷ C) (normal top-vs , S) | semCode (dom ft ∷ C) tis n [] (tnormal (t-top-vs safe++ []) , S)
     | adequacy is (dom ft ∷ C) (ft , uni) tis n [] (tnormal (t-top-vs safe++ []) , S) (normal top-vs , S) (cong (\t → normal t , S) (eraseRT++ t-top-vs [] ⟨ trans ⟩ ++-identityʳ _))
... | div | div | refl = refl
... | con ._ | con (tbranch (tjump {ℓ = suc ℓ} (s≤s ℓ<) vs') , S') | refl = refl
... | con ._ | con (tnormal vs' , S') | refl = cong (\ p → con (normal p , S')) ( sym (eraseRT++ vs' t-res-vs) ⟨ trans ⟩ sym (eraseRT∘castRT≡eraseRT _ (vs' safe++ t-res-vs)))
... | con ._ | con (tbranch (tjump {ℓ = zero} (s≤s ℓ<) vs') , S') | refl with n
... | zero = refl
... | suc n' = adequacy (blk (loop :' ft) is) C (ft , uni) (base (blk ft (loop tis))) n' D (tnormal (vs' safe++ t-res-vs) , S') (normal _ , S') (cong (\ p → normal p , S') (eraseRT++ vs' t-res-vs))
adequacy .[] C .([] →' [] , uni) (base []) n D (tnormal vs , S) (normal _ , S) refl = refl
adequacy (i ∷ is) C (a →' r , q) (base (ti ∷[ qi , m , qis ] tis)) n D (tnormal vs , S) (normal uvs , S) refl
  with adequacy i C (a →' m , qi) ti n D | adequacy is C (m →' r , qis) tis n D
... | IH-i | IH-is
  with bigstep n i C (normal (eraseRT vs) , S) | semCode C ti n D (tnormal vs , S) | IH-i (tnormal vs , S) (normal uvs , S) refl
... | div | div | refl = refl
... | con ._ | con (tbranch b , S') | refl
  rewrite semCode-con-on-tbranch tis n D b S'
  rewrite bigstep-con-on-branch n is C (eraseBranchType b) S'
  = refl
... | con ._ | con (right (qv , vs') , S') | refl
  with bigstep n is C (normal (eraseRT vs') , S') | semCode C tis n D (tnormal vs' , S') | IH-is (tnormal vs' , S') (normal (eraseRT vs') , S') refl
... | div | div | refl = refl
adequacy (i ∷ is) C (a →' r , .(uni ⊓QT qis)) (base (ti ∷[ uni , m , qis ] tis)) n D (tnormal vs , S) (normal .(eraseNormalType (tt , vs)) , S) refl | IH-i | IH-is | con .(eraseStateType {C = C} (right (qv , vs') , S')) | con (right (qv , vs') , S') | refl | con .(eraseStateType st') | con st' | refl = cong con (sym (eraseStateType∘castQRT≡eraseStateType ≤QRT-refl st'))

adequacy c C (a →' r , q) (sub {(a0 →' r0 , q0)} (≤QFT-intro q0≤q ((da , a0++da=a) →' (dr , r0++dr=r)) u) tc) n D st .(eraseStateType st) refl
  rewrite adequacy c C (a0 →' r0 , q0) tc n (da ++ D)
                   (castQRT _ _ _ (≤QRT-intro uni≤uni ( sym (sym (++-assoc a0 da D) ⟨ trans ⟩ cong (\a → a ++ D) a0++da=a))) st)
                   (eraseStateType st) (eraseStateType∘castQRT≡eraseStateType (≤QRT-intro uni≤uni (sym (sym (++-assoc a0 da D) ⟨ trans ⟩ cong (\a → a ++ D) a0++da=a))) st)
  =  eraseStateType∘f∘castQRT≡eraseStateType∘castQFT∘f (≤QFT-intro q0≤q ((da , a0++da=a) →' (dr , r0++dr=r)) u) (semCode C tc n) (da ++ D) D
     (≤QRT-intro uni≤uni (sym (trans (sym (++-assoc a0 da D)) (cong (λ a₁ → a₁ ++ D) a0++da=a)))) st
