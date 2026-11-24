import EvenOddHaarLevels.HaarMultiplier
import EvenOddHaarLevels.L1SequenceEquivalences


noncomputable section
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

theorem chainSpan_le_X₀ : (chainSpan (𝕂 := 𝕂)) ≤ (X₀ 𝕂) := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  exact Set.image_mono (fun _ h => h.1)

theorem offChainSpan_le_X₀ : (offChainSpan (𝕂 := 𝕂)) ≤ (X₀ 𝕂) := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  exact Set.image_mono (fun _ h => h.1)

def chainRangeEquiv : (chainProjection (𝕂 := 𝕂)).range ≃ₗᵢ[𝕂] (chainSpan (𝕂 := 𝕂)) where
  toFun x := ⟨x.val.val, by
    apply ((chainProjection_fixed_iff (𝕂 := 𝕂)) x.val).mp
    obtain ⟨f,hf⟩ := x.property
    rw [← hf]
    exact congrArg (fun P : (X₀ 𝕂) →L[𝕂] (X₀ 𝕂) => P f) (chainProjection_idempotent (𝕂 := 𝕂))⟩
  invFun y := ⟨⟨y.val,(chainSpan_le_X₀ (𝕂 := 𝕂)) y.property⟩,
    ⟨⟨y.val,(chainSpan_le_X₀ (𝕂 := 𝕂)) y.property⟩,((chainProjection_fixed_iff (𝕂 := 𝕂)) _).mpr y.property⟩⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl
  norm_map' _ := rfl

def offChainKernelEquiv : (chainProjection (𝕂 := 𝕂)).ker ≃ₗᵢ[𝕂] (offChainSpan (𝕂 := 𝕂)) where
  toFun x := ⟨x.val.val,((chainProjection_zero_iff (𝕂 := 𝕂)) x.val).mp x.property⟩
  invFun y := ⟨⟨y.val,(offChainSpan_le_X₀ (𝕂 := 𝕂)) y.property⟩,((chainProjection_zero_iff (𝕂 := 𝕂)) _).mpr y.property⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl
  norm_map' _ := rfl

def evenChainSplit : (X₀ 𝕂) ≃L[𝕂] Sum₁ (chainSpan (𝕂 := 𝕂)) (offChainSpan (𝕂 := 𝕂)) := by
  letI : NormedSpace 𝕂 (chainProjection (𝕂 := 𝕂)).range := Submodule.normedSpace _
  letI : NormedSpace 𝕂 (chainProjection (𝕂 := 𝕂)).ker := Submodule.normedSpace _
  exact ((projectionDecomposition (𝕂 := 𝕂)) (chainProjection (𝕂 := 𝕂)) (chainProjection_idempotent (𝕂 := 𝕂))).trans
    ((sumOneCongr (𝕂 := 𝕂)) (chainRangeEquiv (𝕂 := 𝕂)).toContinuousLinearEquiv (offChainKernelEquiv (𝕂 := 𝕂)).toContinuousLinearEquiv)

end EvenOddHaarLevels
