module IMP.Properties where

open import Data.Maybe using (Maybe; just)
open import Data.Product.Base using (∃-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import IMP.Base
open import IMP.BigStep
open import IMP.SmallStep
open import IMP.Syntax

-- For any big-step intepretation that doesn't raise exceptions,
-- there is a corresponding small-step derivation sequence.
-- Proof sketch:
--    1. first case-splitting on statements (Stm) of IMP
--    2. then doing induction on big-step derivation
-- In pen-and-paper proof, I suppose the order is more commonly flipped,
-- as in you first apply the induction principle of derivation tree, then
-- case-splitting on statements.
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ : ∀ (stm : Stm) (σ σ' : State) → [ stm , σ ]⇓ just σ' → [ stm , σ ]⟶* σ'
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ (assign x aexp) σ σ' (b-assign x₁) = dseq-id (s-assign x₁)
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ skip σ σ' b-skip = dseq-id s-skip
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ (seq stm1 stm2) σ σ' (b-seq {σ'' = σ''} deriv1 deriv2) =
    let sub-dseq1 = [∙,∙]⇓∙-implies-[∙,∙]⟶*∙ stm1 σ σ'' deriv1 in
    let sub-dseq2 = [∙,∙]⇓∙-implies-[∙,∙]⟶*∙ stm2 σ'' σ' deriv2 in
    dseq∘ sub-dseq1 sub-dseq2
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ (ite x stm1 stm2) σ σ' (b-ite-tt b deriv) =
    let sub-dseq = [∙,∙]⇓∙-implies-[∙,∙]⟶*∙ stm1 σ σ' deriv in
    dseq-cons (s-ite-tt b) sub-dseq
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ (ite x stm1 stm2) σ σ' (b-ite-ff b deriv) =
    let sub-dseq = [∙,∙]⇓∙-implies-[∙,∙]⟶*∙ stm2 σ σ' deriv in
    dseq-cons (s-ite-ff b) sub-dseq
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ (whiledo pred stm) σ σ' (b-whiledo-tt {σ'' = σ''} pred/tt deriv/stm deriv/while) =
    let sub-dseq/stm = [∙,∙]⇓∙-implies-[∙,∙]⟶*∙ stm σ σ'' deriv/stm in
    let sub-dseq/while = [∙,∙]⇓∙-implies-[∙,∙]⟶*∙ (whiledo pred stm) σ'' σ' deriv/while in
    dseq-cons (s-while-tt pred/tt) (dseq∘ sub-dseq/stm sub-dseq/while)
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ (whiledo pred stm) σ σ' (b-whiledo-ff pred/ff) = dseq-cons (s-while-ff pred/ff) (dseq-id s-skip)

-- Lemma:
-- if a config (stm , σ) small-steps into another config (stm' , σ'),
-- and (stm' , σ') big-steps into σ'', then there exist a derivation
-- of (stm , σ) big-steps into σ''
prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ :
    { stm stm' : Stm } →
    { σ σ' : State } →
    { σ'' : Maybe State } →
    [ stm , σ ]⟶ just (inj₂ (stm' , σ')) →
    [ stm' , σ' ]⇓ σ'' →
    [ stm , σ ]⇓ σ''
prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ (s-seq-1 step) (b-seq deriv1 deriv2) =
    let deriv1' = prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ step deriv1 in
    b-seq deriv1' deriv2
prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ (s-seq-1 step) (b-seq-⊥ deriv) =
    let deriv' = prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ step deriv in
    b-seq-⊥ deriv'
prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ (s-seq-2 (s-assign ⟦aexp⟧=v) ) deriv = b-seq (b-assign ⟦aexp⟧=v) deriv
prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ (s-seq-2 s-skip) deriv = b-seq b-skip deriv
prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ (s-ite-tt pred/tt) deriv = b-ite-tt pred/tt deriv
prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ (s-ite-ff pred/ff) deriv = b-ite-ff pred/ff deriv
prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ (s-while-tt pred/tt) (b-seq deriv1 deriv2) = b-whiledo-tt pred/tt deriv1 deriv2
prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ (s-while-tt pred/tt) (b-seq-⊥ deriv) = b-whiledo-⊥₂ pred/tt deriv
prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ (s-while-ff pred/ff) b-skip = b-whiledo-ff pred/ff

-- For any small-step derivation sequence defined by [∙,∙]⟶*∙,
-- there is a corresponding big-step derivation.
-- Proof sketch:
-- Notice that the definition of derivation sequence is basically a glorified inductive list;
-- hence the proof is an induction over the list structure.
-- The Lemma above (i.e., prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙) is essentially the inductive case.
[∙,∙]⟶*∙-implies-[∙,∙]⇓∙ : ∀ (stm : Stm) (σ σ' : State) →
    [ stm , σ ]⟶* σ' →
    [ stm , σ ]⇓ (just σ')
[∙,∙]⟶*∙-implies-[∙,∙]⇓∙ (assign x aexp) σ σ' (dseq-id (s-assign eval/aexp)) = b-assign eval/aexp
[∙,∙]⟶*∙-implies-[∙,∙]⇓∙ skip σ σ' (dseq-id s-skip) = b-skip
[∙,∙]⟶*∙-implies-[∙,∙]⇓∙ (seq stm1 stm2) σ σ' (dseq-cons {stm' = stm'} {σ'' = σ''} hd tl) =
    let deriv = [∙,∙]⟶*∙-implies-[∙,∙]⇓∙ stm' σ'' σ' tl in
    prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ hd deriv
[∙,∙]⟶*∙-implies-[∙,∙]⇓∙ (ite pred stm1 stm2) σ σ' (dseq-cons {stm' = stm'} {σ'' = σ''} step dseq) =
    let deriv = [∙,∙]⟶*∙-implies-[∙,∙]⇓∙ stm' σ'' σ' dseq in
    prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ step deriv
[∙,∙]⟶*∙-implies-[∙,∙]⇓∙ (whiledo pred stm) σ σ' (dseq-cons {stm' = stm'} {σ'' = σ''} step dseq) =
    let deriv = [∙,∙]⟶*∙-implies-[∙,∙]⇓∙ stm' σ'' σ' dseq in
    prepend-[∙,∙]⟶∙-to-[∙,∙]⇓∙ step deriv
