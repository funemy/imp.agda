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
        { stm' } : Stm
        { σ' } : State
        hd : [ stm , σ ]⟶ just (inj₂ (stm' , σ'))
        tl : [ stm' , σ' ]⟶∞
