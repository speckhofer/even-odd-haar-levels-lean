import EvenOddHaarLevels.WalshEmbedding
import EvenOddHaarLevels.LevelSelection
import EvenOddHaarLevels.MainTheorem

noncomputable section
set_option maxHeartbeats 1200000
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

/-- Every membership pattern embeds complementably into any infinite,
coinfinite set of Haar levels. -/
def selectedLevelsEmbedding (S T : Set ℕ) (hT : T.Infinite) (hTc : Tᶜ.Infinite) :
    (ComplementedEmbedding (𝕂 := 𝕂)) ((haarClosedSpan 𝕂) S) ((haarClosedSpan 𝕂) T) := by
  let φ := Classical.choose (exists_strictMono_level_selection S T hT hTc)
  have hφ := Classical.choose_spec (exists_strictMono_level_selection S T hT hTc)
  exact (levelComplementedEmbedding (𝕂 := 𝕂)) S T φ hφ.1 hφ.2

theorem even_levels_infinite : ({n : ℕ | Even n} : Set ℕ).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2*n)
  · intro a b h; dsimp at h; omega
  · intro n
    exact ⟨n, by omega⟩

theorem even_levels_compl_infinite : ({n : ℕ | Even n}ᶜ : Set ℕ).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2*n+1)
  · intro a b h; dsimp at h; omega
  · intro n
    change ¬ Even (2*n+1)
    rintro ⟨k,hk⟩
    omega

/-- Corollary 3.4, with the canonical Haar spaces and actual bounded inverses. -/
def infiniteCoinfiniteLevelsEquiv (S : Set ℕ) (hS : S.Infinite) (hSc : Sᶜ.Infinite) :
    (haarClosedSpan 𝕂) S ≃L[𝕂] (X₀ 𝕂) := by
  let E : Set ℕ := {n | Even n}
  let e := (selectedLevelsEmbedding (𝕂 := 𝕂)) E S hS hSc
  let f := (selectedLevelsEmbedding (𝕂 := 𝕂)) S E even_levels_infinite even_levels_compl_infinite
  letI : NormedSpace 𝕂 e.retraction.ker := Submodule.normedSpace _
  letI : NormedSpace 𝕂 f.retraction.ker := Submodule.normedSpace _
  let u : (X₀ 𝕂) ≃L[𝕂] (haarClosedSpan 𝕂) E := ContinuousLinearEquiv.refl 𝕂 (X₀ 𝕂)
  let a : (X₀ 𝕂) ≃L[𝕂] Sum₁ ((haarClosedSpan 𝕂) S) f.retraction.ker := u.trans f.split
  let b : (haarClosedSpan 𝕂) S ≃L[𝕂] Sum₁ (X₀ 𝕂) e.retraction.ker :=
    e.split.trans ((sumOneCongr (𝕂 := 𝕂)) u.symm (ContinuousLinearEquiv.refl 𝕂 e.retraction.ker))
  exact ((l1Absorption (𝕂 := 𝕂)) ((evenSequenceEquivOfChain (𝕂 := 𝕂)) (chainSynthesisEquiv (𝕂 := 𝕂))) a b).symm

end EvenOddHaarLevels
