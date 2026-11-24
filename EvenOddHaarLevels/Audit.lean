import EvenOddHaarLevels.Results

open EvenOddHaarLevels

-- Exact public types, including both scalar specializations.
#check (EvenOddHaarLevels.main_result : ∀ (𝕂 : Type) [RCLike 𝕂],
  IsEmpty (X₀ 𝕂 ≃L[𝕂] L1 𝕂) ∧ IsEmpty (X₁ 𝕂 ≃L[𝕂] L1 𝕂))
#check (EvenOddHaarLevels.main_result ℝ)
#check (EvenOddHaarLevels.main_result ℂ)
#print axioms EvenOddHaarLevels.main_result

-- Supporting proof audits: these must have no project-specific assumptions.
#print axioms EvenOddHaarLevels.coefficientOperator_norm
#print axioms EvenOddHaarLevels.coefficient_test_obstruction
#print axioms EvenOddHaarLevels.gaussianLinear_integral_fourth
#print axioms EvenOddHaarLevels.dualL2Representative_essential_bound
#print axioms EvenOddHaarLevels.even_not_isomorphic_L1
#print axioms EvenOddHaarLevels.grothendieck_matrix
#print axioms EvenOddHaarLevels.l1_finiteSummingTwo
#print axioms EvenOddHaarLevels.l1Absorption
#print axioms EvenOddHaarLevels.evenOddEquiv
#print axioms EvenOddHaarLevels.chainSynthesisEquiv

-- Corollary 3.4: exact public type and complete dependency audit.
#check (EvenOddHaarLevels.infinite_coinfinite_levels : ∀ (𝕂 : Type) [RCLike 𝕂]
  (S : Set ℕ), S.Infinite → Sᶜ.Infinite → Nonempty (haarClosedSpan 𝕂 S ≃L[𝕂] X₀ 𝕂))
#check (EvenOddHaarLevels.infinite_coinfinite_levels ℝ)
#check (EvenOddHaarLevels.infinite_coinfinite_levels ℂ)
#print axioms EvenOddHaarLevels.infinite_coinfinite_levels
#print axioms EvenOddHaarLevels.walshPolynomial_norm_cube
#print axioms EvenOddHaarLevels.walshLevelSpan_eq_haarClosedSpan
#print axioms EvenOddHaarLevels.levelComplementedEmbedding
