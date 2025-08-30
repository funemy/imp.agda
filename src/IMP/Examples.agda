module IMP.Examples where

open import Data.Integer using (+_; -_)
open import Data.Maybe as M using (just)
open import IMP.Base
open import IMP.Syntax
open import IMP.BigStep
open import IMP.SmallStep
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Define symbols and variables X, Y, Z to make it easier to construct examples
X : SSymbol
X = sym "X"

`X : Aexp
`X = var X

Y : SSymbol
Y = sym "Y"

`Y : Aexp
`Y = var Y

Z : SSymbol
Z = sym "Z"

`Z : Aexp
`Z = var Z

testState1 : State
testState1 = σ₀ [ X := (+ 42) ]

_ : σ₀ [ X ] ≡ exn
_ = refl

_ : testState1 [ X ] ≡ just (+ 42)
_ = refl

_ : [ skip , σ₀ ]⟶* σ₀
_ = σ₀ ::⟶⟨ s-skip ⟩∎ σ₀

_ : [ skip ⨾ skip , σ₀ ]⟶* σ₀
_ = σ₀ ::⟶⟨ s-seq-2 s-skip ⟩
    σ₀ ::⟶⟨ s-skip ⟩∎
    σ₀

-- An example program
prog1 : Stm
prog1 =
    X ← N 0 ⨾
    WHILE `X ≤? N 1 DO
        X ← (plus `X (N 1))

-- The expected final program state when prog1 terminates
σ-prog1 : State
σ-prog1 = σ₀ [ X := (+ 0) ] [ X := (+ 1) ] [ X := (+ 2) ]

-- Execution of prog1 using big-step semantics
exec-prog1 : [ prog1 , σ₀ ]⇓ just σ-prog1
exec-prog1 = b-seq
                (b-assign refl)
                (b-whiledo-tt
                    refl
                    (b-assign refl)
                    (b-whiledo-tt
                        refl
                        (b-assign refl)
                        (b-whiledo-ff refl)))

-- Construct the derivation sequence of prog1 without using any sugar
dseq-prog1 : [ prog1 , σ₀ ]⟶* σ-prog1
dseq-prog1 = dseq-cons
                (s-seq-2 (s-assign refl))
                (dseq-cons
                    (s-while-tt refl)
                    (dseq-cons
                        (s-seq-2 (s-assign refl))
                        (dseq-cons
                            (s-while-tt refl)
                            (dseq-cons
                                (s-seq-2 (s-assign refl))
                                (dseq-cons
                                    (s-while-ff refl)
                                    (dseq-id s-skip))))))

-- Construct the derivation sequence of prog1 using the syntactic sugar defined in `IMP.SmallStep`
dseq-sugared-prog1 : [ prog1 , σ₀ ]⟶* σ-prog1
dseq-sugared-prog1 =
    σ₀ ::⟶⟨ s-seq-2 (s-assign refl) ⟩
    σ₀ [ X := (+ 0) ] ::⟶⟨ s-while-tt refl ⟩
    σ₀ [ X := (+ 0) ] ::⟶⟨ s-seq-2 (s-assign refl) ⟩
    σ₀ [ X := (+ 0) ] [ X := (+ 1) ] ::⟶⟨ s-while-tt refl ⟩
    σ₀ [ X := (+ 0) ] [ X := (+ 1) ] ::⟶⟨ s-seq-2 (s-assign refl) ⟩
    σ₀ [ X := (+ 0) ] [ X := (+ 1) ] [ X := (+ 2) ] ::⟶⟨ s-while-ff refl ⟩
    σ₀ [ X := (+ 0) ] [ X := (+ 1) ] [ X := (+ 2) ] ::⟶⟨ s-skip ⟩∎
    σ₀ [ X := (+ 0) ] [ X := (+ 1) ] [ X := (+ 2) ]