{-# OPTIONS --guardedness #-}

-- This module extends our small-step semantics (i.e., IMP.SmallStep)
-- with coinductive infinite derivation sequences.
-- It is kept separate because coinductive definitions require the
-- `--guardedness` option, which can only be imported if the parent
-- module also turned on the same option, hence it's more convenient
-- to keep this separate.
module IMP.SmallStepExt where

open import Agda.Builtin.Sigma using (_,_)
open import Data.Maybe using (Maybe; just)
open import Data.Sum using (inj₂)
open import IMP.Base
open import IMP.Syntax
open import IMP.SmallStep

-- This coinductive record represent **infinite** derivation sequences
-- for small-step semantics.
--
-- Note that this definition only covers divergence, but not terminating executions.
record [_,_]⟶∞ (stm : Stm) (σ : State) : Set where
    coinductive
    field
        tl :
            { stm' : Stm } →
            { σ' : State } →
            [ stm , σ ]⟶ just (inj₂ (stm' , σ')) →
            [ stm' , σ' ]⟶∞

open [_,_]⟶∞ public

eval⟶∞ : (stm : Stm) → (σ : State) → [ stm , σ ]⟶∞
eval⟶∞ (seq stm1 stm2) σ .tl (s-seq-1 {stm1' = stm1'} {σ' = σ'} step) =
    eval⟶∞ (seq stm1' stm2) σ'
eval⟶∞ (seq stm1 stm2) σ .tl (s-seq-2 step) = eval⟶∞ stm2 _
eval⟶∞ (ite p stm1 stm2) σ .tl (s-ite-tt x) = eval⟶∞ stm1 σ
eval⟶∞ (ite p stm1 stm2) σ .tl (s-ite-ff x) = eval⟶∞ stm2 σ
eval⟶∞ (whiledo p stm) σ .tl (s-while-tt x) = eval⟶∞ (seq stm (whiledo p stm)) σ
eval⟶∞ (whiledo p stm) σ .tl (s-while-ff x) = eval⟶∞ skip σ

_ : [ skip , σ₀ ]⟶∞
_ = eval⟶∞ skip σ₀