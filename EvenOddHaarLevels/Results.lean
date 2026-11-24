import EvenOddHaarLevels.Definitions
import EvenOddHaarLevels.MainTheorem
import EvenOddHaarLevels.LevelClassification

/-!
# Public statements

All mathematical objects below are defined in EvenOddHaarLevels/Definitions.lean.
The statements and their proofs are uniform over an RCLike scalar field 𝕂,
including both ℝ and ℂ.
-/

noncomputable section

namespace EvenOddHaarLevels

/-- Theorem 1.1: neither the even nor the odd Haar span is isomorphic to L¹[0,1].
Here an isomorphism is a 𝕂-linear continuous equivalence with continuous inverse. -/
theorem main_result (𝕂 : Type*) [RCLike 𝕂] :
    IsEmpty (X₀ 𝕂 ≃L[𝕂] L1 𝕂) ∧ IsEmpty (X₁ 𝕂 ≃L[𝕂] L1 𝕂) := by
  exact main_result_proved

/-- Corollary 3.4: the closed span of an infinite, coinfinite set of Haar levels is
isomorphic to the even-level span, over the scalar field 𝕂. -/
theorem infinite_coinfinite_levels (𝕂 : Type*) [RCLike 𝕂]
    (S : Set ℕ) (hS : S.Infinite) (hSc : Sᶜ.Infinite) :
    Nonempty (haarClosedSpan 𝕂 S ≃L[𝕂] X₀ 𝕂) := by
  exact ⟨infiniteCoinfiniteLevelsEquiv S hS hSc⟩

end EvenOddHaarLevels
