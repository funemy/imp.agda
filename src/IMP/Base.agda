module IMP.Base where

open import IMP.Syntax
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_; not)
open import Data.Integer as I using (ℤ; +_; -_)
open import Data.Maybe as M using (Maybe; just; nothing)
open import Relation.Nullary.Decidable.Core using (isYes)

-- Value is represented as numbers (i.e., integers)
Value : Set
Value = Num

-- We are using the type `Maybe A` to model exceptional computation,
-- where `nothing` represent some exceptions.
-- Renaming `nothing` to `exn` here for clarity.
exn : {A : Set} → Maybe A
exn = nothing

-- Value extended with a special case (i.e., `exn`) to denote exceptions.
Value⊥ : Set
Value⊥ = Maybe Num

Bool⊥ : Set
Bool⊥ = Maybe Bool

vplus : Value⊥ → Value⊥ → Value⊥
vplus (just x1) (just x2) = just (x1 I.+ x2)
vplus _ _ = exn

vmul : Value⊥ → Value⊥ → Value⊥
vmul (just x1) (just x2) = just (x1 I.* x2)
vmul _ _ = exn

vsub : Value⊥ → Value⊥ → Value⊥
vsub (just x1) (just x2) = just (x1 I.- x2)
vsub _ _ = exn

veq : Value⊥ → Value⊥ → Maybe Bool
veq (just x1) (just x2) = just (isYes (x1 I.≟ x2))
veq _ _ = exn

vleq : Value⊥ → Value⊥ → Maybe Bool
vleq (just x1) (just x2) = just (isYes (x1 I.≤? x2))
vleq _ _ = exn

vand : Maybe Bool → Maybe Bool → Maybe Bool
vand (just b1) (just b2) = just (b1 ∧ b2)
vand _ _ = exn

-- State is represented as a function from symbols to values
State : Set
State = SSymbol → Value⊥

-- State update
_[_:=_] : State → SSymbol → Num → State
h [ s := v ] = λ x → if (s == x) then just v else h x

-- State access
_[_] : State → SSymbol → Value⊥
h [ s ] = h s

-- an initial (i.e., empty) state, where any access will leads to exceptions
σ₀ : State
σ₀ = λ x → exn

-- denotational semantics for Arithmetic expressions (Aexp)
A⟦_⟧_ : Aexp → State → Value⊥
A⟦ num x ⟧ σ = just x
A⟦ var x ⟧ σ = σ x
A⟦ plus a₁ a₂ ⟧ σ = vplus (A⟦ a₁ ⟧ σ) (A⟦ a₂ ⟧ σ)
A⟦ mul a₁ a₂ ⟧ σ = vmul (A⟦ a₁ ⟧ σ) (A⟦ a₂ ⟧ σ)
A⟦ sub a₁ a₂ ⟧ σ = vsub (A⟦ a₁ ⟧ σ) (A⟦ a₂ ⟧ σ)

-- denotational semantics for Boolean expressions (Bexp)
B⟦_⟧_ : Bexp → State → Bool⊥
B⟦ tt ⟧ σ = just true
B⟦ ff ⟧ σ = just false
B⟦ eq a₁ a₂ ⟧ σ = veq (A⟦ a₁ ⟧ σ) (A⟦ a₂ ⟧ σ)
B⟦ leq a₁ a₂ ⟧ σ = vleq (A⟦ a₁ ⟧ σ) (A⟦ a₂ ⟧ σ)
B⟦ lneg b ⟧ σ = M.map not (B⟦ b ⟧ σ)
B⟦ land b₁ b₂ ⟧ σ = vand (B⟦ b₁ ⟧ σ) (B⟦ b₂ ⟧ σ)

A⌊_⌋ : Aexp → State → Value
A⌊ exp ⌋ σ with A⟦ exp ⟧ σ
... | just x = x
... | nothing = + 0

B⌊_⌋ : Bexp → State → Bool
B⌊ exp ⌋ σ with B⟦ exp ⟧ σ
... | just x = x
... | nothing = false
