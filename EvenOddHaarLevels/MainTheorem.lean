import EvenOddHaarLevels.EvenNonisomorphism
import EvenOddHaarLevels.HaarAssembly
import EvenOddHaarLevels.HaarChainCompletion
import EvenOddHaarLevels.HaarChainLower

noncomputable section
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

/-- The concrete chain synthesis equivalence, using the proved finite lower estimate. -/
def chainSynthesisEquiv : Seq₁ 𝕂 ≃L[𝕂] (chainSpan (𝕂 := 𝕂)) :=
  (chainSynthesisEquivOfFiniteLower (𝕂 := 𝕂)) (chainFinite_lower (𝕂 := 𝕂))

/-- The chain/off-chain decomposition identifies the canonical even and odd spans. -/
def evenOddEquiv : (X₀ 𝕂) ≃L[𝕂] (X₁ 𝕂) := (evenOddEquivOfChain (𝕂 := 𝕂)) (chainSynthesisEquiv (𝕂 := 𝕂))

/-- Both clauses of the scalar-parametric main theorem. -/
theorem main_result_proved :
    IsEmpty ((X₀ 𝕂) ≃L[𝕂] (L1 𝕂)) ∧ IsEmpty ((X₁ 𝕂) ≃L[𝕂] (L1 𝕂)) := by
  exact ⟨⟨fun V => (even_not_isomorphic_L1 (𝕂 := 𝕂)) ⟨V⟩⟩,
    ⟨fun V => (even_not_isomorphic_L1 (𝕂 := 𝕂)) ⟨(evenOddEquiv (𝕂 := 𝕂)).trans V⟩⟩⟩

end EvenOddHaarLevels
