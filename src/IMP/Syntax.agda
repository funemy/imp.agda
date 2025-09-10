module IMP.Syntax where

open import Data.Nat using (ℕ)
open import Data.String using (String) renaming (_==_ to strEq)
open import Data.Bool using (Bool)
open import Data.Integer using (ℤ; +_; -_)

Num : Set
Num = ℤ

data Symbol (T : Set) : Set where
    sym : T → Symbol T

-- Symbols represented by Strings
SSymbol : Set
SSymbol = Symbol String

-- Decidable equality of symbols is the decidable equality of their underlying representation
infix 4 _==_
_==_ : SSymbol → SSymbol → Bool
(sym s1) == (sym s2) = strEq s1 s2

data Aexp : Set where
    num : Num → Aexp
    var : SSymbol → Aexp
    plus : Aexp → Aexp → Aexp
    mul : Aexp → Aexp → Aexp
    sub : Aexp → Aexp → Aexp

data Bexp : Set where
    tt : Bexp
    ff : Bexp
    eq : Aexp → Aexp → Bexp
    leq : Aexp → Aexp → Bexp
    lneg : Bexp → Bexp
    land : Bexp → Bexp → Bexp

data Stm : Set where
    assign : (x : SSymbol) → (aexp : Aexp) → Stm
    skip : Stm
    seq : (stm1 : Stm) → (stm2 : Stm) → Stm
    ite : (p : Bexp) → (stm1 : Stm) → (stm2 : Stm) → Stm
    whiledo : (p : Bexp) → Stm → Stm

-- Below is some syntactic sugar for the language defined above
N : ℕ → Aexp
N n = num (+ n)

-N : ℕ → Aexp
-N n = num (- (+ n))

infix 1 WHILE_DO_
WHILE_DO_ : Bexp → Stm → Stm
WHILE b DO s = whiledo b s

IF_THEN_ELSE_ : Bexp → Stm → Stm → Stm
IF b THEN s1 ELSE s2 = ite b s1 s2

_←_ : SSymbol → Aexp → Stm
x ← e = assign x e

_≟_ : Aexp → Aexp → Bexp
a ≟ b = eq a b

_≤?_ : Aexp → Aexp → Bexp
a ≤? b = leq a b

-- Sugar for sequencing.
-- I would like to use semicolon, but it's special in Agda.
infixr 0  _⨾_
_⨾_ : Stm → Stm → Stm
s1 ⨾ s2 = seq s1 s2