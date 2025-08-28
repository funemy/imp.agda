module IMP.Properties where

-- For any big-step intepretation that doesn't raise exceptions,
-- there is a corresponding small-step derivation sequence.
-- Proof sketch:
--    1. first case-splitting on statements (Stm) of IMP
--    2. then doing induction on big-step derivation
-- In pen-and-paper proof, I suppose the order is more commonly flipped,
-- as in you first apply the induction principle of derivation tree, then
-- case-splitting on statements.
[∙,∙]⇓∙-implies-[∙,∙]⟶*∙ : ∀ (stm : Stm) (σ σ' : Heap) → [ stm , σ ]⇓ just σ' → [ stm , σ ]⟶* σ'
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