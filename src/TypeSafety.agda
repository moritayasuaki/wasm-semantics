module TypeSafety where

open import Data.Nat
open import Data.Bool hiding (_<_)
open import Arrow
open import BlockList as BList hiding (length ; _++_)
open import Syntax
open import OperationalSemantics
open import TypeSystem
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Unary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Subtype
open import Data.List as List
open import Partial
open import Result
open BigStep
open SmallStep
open import Equivalence
open import Adequacy
open import DenotationalSemantics
open import TypeCast
open import Data.List.Properties

private variable
  k : Kind

-- well-typedness of state
wt : Ctx → QRT → State → Set
wt C qrt st = Σ (semQRT (semCtx C) qrt) \ st-typed → st ≡ eraseStateType st-typed

con-injective : {X : Set} {p q : X} → (con p ≡ con q) → p ≡ q
con-injective refl = refl

castRT-stripRT : ∀ {r r' : RT} (vs : semRT r) (p : r ≡ r') → eraseRT vs ≡ eraseRT (castRT _ _ p vs)
castRT-stripRT vs refl rewrite castRT-refl-id vs = refl

bigstep-soundness : ∀ (c : Code k) C a r q st ans → (deriv : C Sub.⊢ c :' (a →' r , q)) → (c , C , st) ⇓ ans → wt C (a , uni) st → wt C (r , q) ans
bigstep-soundness c C a r q _ ans deriv (lc , bigstep-st=ans) ((tbranch b , S) , refl)
  rewrite bigstep-con-on-branch lc c C (eraseBranchType b) S
  with refl ← bigstep-st=ans
  = (tbranch b , S) , refl
bigstep-soundness c C a r q (normal uvs , S) ans deriv (lc , bigstep-st=ans) ((tnormal vs , S) , refl)
  with adequacy-result ← adequacy c C (a →' r , q) deriv lc [] (tnormal (vs safe++ []) , S) (normal (uvs ++ []) , S) (cong (\p → normal p , S) (eraseRT++ vs []))
  with sym adequacy-result ⟨ trans ⟩ cong (\p → bigstep lc c C (normal p , S)) (++-identityʳ (eraseNormalType (tt , vs))) ⟨ trans ⟩ bigstep-st=ans
... | bigstep-result
  with ⟦ deriv ⟧ lc [] (tnormal (vs safe++ []) , S) | bigstep-result
... | con (tbranch b , S) | P = (tbranch b , S) , sym (con-injective P)
... | con (right (qv' , vs') , S') | P = (right (qv' , castRT _ _ (++-identityʳ r) vs') , S') , (sym (con-injective P) ⟨ trans ⟩ cong (\uvs → (normal uvs , S')) (castRT-stripRT vs' (++-identityʳ r)))

smallstep-soundness : ∀ is a r q st ans → (deriv : [] Sub.⊢ is :' (a →' r , q)) → (is , [] , st) ↓ ans → wt [] (a , uni) st → Σ QRT \ qrt → wt [] qrt ans
smallstep-soundness is a r q st ans deriv st↓ans well-typed =
  let st⇓ans = small⇒big ans is st st↓ans
      wt-ans = bigstep-soundness is [] a r q st ans deriv st⇓ans well-typed
  in (r , q) , wt-ans
