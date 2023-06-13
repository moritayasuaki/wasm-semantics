{-# OPTIONS --without-K --safe #-}
open import Function
open import Result
open import Relation.Binary.PropositionalEquality
open import Axiom.UniquenessOfIdentityProofs
open import Relation.Binary.Definitions
open import Relation.Nullary
open import Subtype
open import Syntax
open import Data.Unit
open import Data.Empty
open import TypeSystem
open import OperationalSemantics
open import DenotationalSemantics
open import DenotationalSemantics0
open import Data.Nat
open import Data.Product
open import Partial
open import TypeCast
open import TypeCast0

module UntypedLift where

module LiftR
  (Type : Set) (_≤_ : Type → Type → Set) (Context : Set) (Term : Set) (_⊢_::_ : Context → Term → Type → Set)
  (semCtx : Context → Set) (semType : Type → Set) (semTerm : ∀ {Γ x T} → (Γ ⊢ x :: T) → semCtx Γ → semType T)
  (semUType : Set) (semUTerm : ∀ {Γ} → Term → semCtx Γ →  semUType)
  (≤-refl : Reflexive _≤_) (≤-trans : Transitive _≤_) (_≤?_ : Decidable _≤_) (≤-irrelevant : Relation.Binary.Definitions.Irrelevant _≤_)
  where

  RType = Result Type

  data _≤RType_ : RType → RType → Set where
    err : ∀ {rt} e → rt ≤RType err e
    ok : ∀ {T T'} → T ≤ T' → ok T ≤RType ok T'

  data _⊢R_::_ :  Context → Term → RType → Set where
    err : ∀ {Γ x} (e : Error) → Γ ⊢R x :: err e
    ok : ∀ {Γ x T} → Γ ⊢ x :: T → Γ ⊢R x :: ok T

  semRType : RType → Set
  semRType (err e) = semUType
  semRType (ok T) = semType T

  semRTerm : ∀ {Γ x RT} → (Γ ⊢R x :: RT) → semCtx Γ → semRType RT
  semRTerm {x = x} {RT = err e} (err e) ctx = semUTerm x ctx
  semRTerm (ok 𝓓) ctx = semTerm 𝓓 ctx

RQFT : Set
RQFT = Result QFT

data _≤RQFT_ : RQFT → RQFT → Set where
  ≤err : ∀ {rqft} e → rqft ≤RQFT err e
  ok≤ok : ∀ {qft qft'} → qft ≤QFT qft' → ok qft ≤RQFT ok qft'

≤RQFT-reflexive : ∀ {a b} → a ≡ b → a ≤RQFT b
≤RQFT-reflexive {err x} .{err x} refl = ≤err x
≤RQFT-reflexive {ok x} .{ok x} refl = ok≤ok ≤QFT-refl

≤RQFT-refl : ∀ {a} → a ≤RQFT a
≤RQFT-refl {err e} = ≤err e
≤RQFT-refl {ok qft} = ok≤ok ≤QFT-refl

open import Relation.Binary.Definitions
≤RQFT-trans : Transitive _≤RQFT_
≤RQFT-trans {_} {_} {err e} p q = ≤err e
≤RQFT-trans (ok≤ok qft≤qft') (ok≤ok qft'≤qft'') = ok≤ok (≤QFT-trans qft≤qft' qft'≤qft'')

_≤?RQFT_ : Decidable _≤RQFT_
_ ≤?RQFT err e' = yes (≤err e')
err e ≤?RQFT ok v' = no \()
ok v ≤?RQFT ok v' = case v ≤?QFT v' of \ where
  (yes p) → yes (ok≤ok p)
  (no np) → no \{(ok≤ok p) → np p}

≤RQFT-irrelevant : Relation.Binary.Definitions.Irrelevant _≤RQFT_
≤RQFT-irrelevant (≤err e) (≤err .e) = refl
≤RQFT-irrelevant (ok≤ok x) (ok≤ok x₁) = cong ok≤ok (≤QFT-irrelevant x x₁)

module RSub where
  open import BlockList
  private variable
    k : Kind
    C : Ctx
    qft : QFT
    rqft : RQFT

  open Sub public

  data _⊢?_:'_ : ∀{k} → Ctx → Code k → RQFT → Set where
    maybe-not : ∀ {C} {c : Code k} e → C ⊢? c :' (err e)
    exists : ∀ {C} {c : Code k} {t} → C ⊢ c :' t → C ⊢? c :' (ok t)

  data _⊢[base]?_:'_ : ∀{k} → Ctx → Code k → RQFT → Set where
    maybe-not : ∀ {C} {c : Code k}  e → C ⊢[base]? c :' err e
    exists : ∀ {C} {c : Code k} {t} → C ⊢[base] c :' t  → C ⊢[base]? c :' ok t

  sub? : ∀ {k} {c : Code k} {C t t'} → t ≤RQFT t' → C ⊢? c :' t → C ⊢? c :' t'
  sub? (≤err e) _ = maybe-not e
  sub? (ok≤ok x) (exists tc) = exists (sub x tc)

  base? : ∀ {k} {c : Code k} {C t} → C ⊢[base]? c :' t → C ⊢? c :' t
  base? (maybe-not e) = maybe-not e
  base? (exists x) = exists (base x)

open RSub

_≟RQFT_ : DecidableEquality RQFT
_≟RQFT_ = deceqResult _≟QFT_

uipRQFT : UIP RQFT
uipRQFT = uipResult _≟QFT_

semRQFT : RQFT → Ctx → Set
semRQFT (err _) C = Result (Either (ℕ × OpeStk) OpeStk) × Store → Partial (Result (Either (ℕ × OpeStk) OpeStk) × Store)
semRQFT (ok qft) C = (D : RT) → semQFT (semCtx C) (semCtx C) qft D

semRCode : ∀ {k} {c : Code k} {C t} → (C ⊢? c :' t) → ℕ → semRQFT t C
semRCode {c = c} {C} {err x} _ n = BigStep.bigstep n c C
semRCode {c = c} {C} {ok x} (exists tc) n = ⟦ tc ⟧ n

semRQFT0 : RQFT → Ctx → Set
semRQFT0 (err _) C = Result (Either (ℕ × OpeStk) OpeStk) × Store → Partial (Result (Either (ℕ × OpeStk) OpeStk) × Store)
semRQFT0 (ok qft) C = semQFT0 (semCtx C) qft

semRCode0 : ∀ {k} {c : Code k} {C t} → (C ⊢? c :' t) → ℕ → semRQFT0 t C
semRCode0 {c = c} {C} {err x} _ n = BigStep.bigstep n c C
semRCode0 {c = c} {C} {ok x} (exists tc) n = semCode0 C tc n

_≅0_ : ∀ {C t} → semRQFT0 t C → semRQFT0 t C → Set
_≅0_ {t = err x} f f' = f ≗ f'
_≅0_ {t = ok x} f f' = f ≗ f'

≅0-trans : ∀ {C t} → {a b c : semRQFT0 t C} → a ≅0 b → b ≅0 c → a ≅0 c
≅0-trans {t = err x} p q = ≗-trans p q
≅0-trans {t = ok x} p q = ≗-trans p q

≅0-reflexive : ∀ {C t} → {a b : semRQFT0 t C} → a ≡ b → a ≅0 b
≅0-reflexive {t = err x} refl = \_ → refl
≅0-reflexive {t = ok x} refl = \_ → refl

≅0-sym : ∀ {C t} → {a b : semRQFT0 t C} → a ≅0 b → b ≅0 a
≅0-sym {t = err x₁} a=b = ≗-sym a=b
≅0-sym {t = ok x₁} a=b = ≗-sym a=b

_≅_ : ∀ {C t} → semRQFT t C → semRQFT t C → Set
_≅_ {t = err x} f f' = f ≗ f'
_≅_ {t = ok x} f f' = ∀ d → f d  ≗ f' d

≅-trans : ∀ {C t} → {a b c : semRQFT t C} → a ≅ b → b ≅ c → a ≅ c
≅-trans {t = err x} p q = ≗-trans p q
≅-trans {t = ok x} p q d = ≗-trans (p d) (q d)

≅-reflexive : ∀ {C t} → {a b : semRQFT t C} → a ≡ b → a ≅ b
≅-reflexive {t = err x} refl = \_ → refl
≅-reflexive {t = ok x} refl = \_ _ → refl

≅-sym : ∀ {C t} → {a b : semRQFT t C} → a ≅ b → b ≅ a
≅-sym {t = err x₁} a=b x = sym (a=b x)
≅-sym {t = ok x₁} a=b d = ≗-sym (a=b d)
