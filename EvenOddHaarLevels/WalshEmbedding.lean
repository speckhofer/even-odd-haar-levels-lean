import EvenOddHaarLevels.WalshOperators
import EvenOddHaarLevels.ComplementedEmbedding

noncomputable section
attribute [local instance] Classical.propDecidable
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

theorem walshSynthesis_dense : DenseRange (walshSynthesis (𝕂 := 𝕂)) := (walshPolynomial_dense (𝕂 := 𝕂))

/-- A continuous map preserving the selected generators preserves their closed span. -/
theorem maps_walshLevelSpan (L : (L1 𝕂) →L[𝕂] (L1 𝕂)) (S T : Set ℕ)
    (h : ∀ A, (∃ n ∈ S, n ∈ A ∧ ∀ k ∈ A, k ≤ n) →
      L ((walshL1 (𝕂 := 𝕂)) A) ∈ (walshLevelSpan (𝕂 := 𝕂)) T) :
    ∀ f ∈ (walshLevelSpan (𝕂 := 𝕂)) S, L f ∈ (walshLevelSpan (𝕂 := 𝕂)) T := by
  have hle : Submodule.span 𝕂 ((walshL1 (𝕂 := 𝕂)) ''
      {A | ∃ n ∈ S, n ∈ A ∧ ∀ k ∈ A, k ≤ n}) ≤
      ((walshLevelSpan (𝕂 := 𝕂)) T).comap L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A,hA,rfl⟩
    exact h A hA
  exact Submodule.topologicalClosure_minimal _ hle
    ((Submodule.isClosed_topologicalClosure _).preimage L.continuous)

theorem walshSubstitution_mem_levels (S T : Set ℕ) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (hST : ∀ n, n ∈ S ↔ φ n ∈ T) :
    ∀ f ∈ (walshLevelSpan (𝕂 := 𝕂)) S, (walshSubstitution (𝕂 := 𝕂)) φ f ∈ (walshLevelSpan (𝕂 := 𝕂)) T := by
  apply (maps_walshLevelSpan (𝕂 := 𝕂))
  intro A hA
  obtain ⟨n,hn,hnA,hmax⟩ := hA
  rw [(walshSubstitution_walsh (𝕂 := 𝕂)) (walshSynthesis_dense (𝕂 := 𝕂)) φ hφ.injective]
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨A.image φ, ⟨φ n, (hST n).mp hn, Finset.mem_image.mpr ⟨n,hnA,rfl⟩,?_⟩, rfl⟩
  intro k hk
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
  exact hφ.monotone (hmax j hj)

theorem walshRetraction_mem_levels (S T : Set ℕ) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (hST : ∀ n, n ∈ S ↔ φ n ∈ T) :
    ∀ f ∈ (walshLevelSpan (𝕂 := 𝕂)) T, (walshRetraction (𝕂 := 𝕂)) φ f ∈ (walshLevelSpan (𝕂 := 𝕂)) S := by
  apply (maps_walshLevelSpan (𝕂 := 𝕂))
  intro A hA
  rw [(walshRetraction_walsh (𝕂 := 𝕂)) (walshSynthesis_dense (𝕂 := 𝕂)) φ hφ.injective]
  split_ifs with hR
  · obtain ⟨m,hm,hmA,hmax⟩ := hA
    let ψ := Function.invFun φ
    have hi (j : ℕ) (hj : j ∈ A) : φ (ψ j) = j := Function.invFun_eq (hR hj)
    have hn : ψ m ∈ S := (hST (ψ m)).mpr (by rw [hi m hmA]; exact hm)
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨A.image ψ, ⟨ψ m, hn, Finset.mem_image.mpr ⟨m,hmA,rfl⟩,?_⟩, rfl⟩
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    apply hφ.le_iff_le.mp
    rw [hi j hj, hi m hmA]
    exact hmax j hj
  · exact Submodule.zero_mem _

/-- The Walsh substitution, restricted to selected canonical Haar spans, with its
bounded partial inverse as a retraction. -/
def levelComplementedEmbedding (S T : Set ℕ) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (hST : ∀ n, n ∈ S ↔ φ n ∈ T) :
    (ComplementedEmbedding (𝕂 := 𝕂)) ((haarClosedSpan 𝕂) S) ((haarClosedSpan 𝕂) T) := by
  have hJ : ∀ f ∈ (haarClosedSpan 𝕂) S, (walshSubstitution (𝕂 := 𝕂)) φ f ∈ (haarClosedSpan 𝕂) T := by
    simpa only [← (walshLevelSpan_eq_haarClosedSpan (𝕂 := 𝕂))] using (walshSubstitution_mem_levels (𝕂 := 𝕂)) S T φ hφ hST
  have hU : ∀ f ∈ (haarClosedSpan 𝕂) T, (walshRetraction (𝕂 := 𝕂)) φ f ∈ (haarClosedSpan 𝕂) S := by
    simpa only [← (walshLevelSpan_eq_haarClosedSpan (𝕂 := 𝕂))] using (walshRetraction_mem_levels (𝕂 := 𝕂)) S T φ hφ hST
  exact
    { inclusion := (((walshSubstitution (𝕂 := 𝕂)) φ).comp ((haarClosedSpan 𝕂) S).subtypeL).codRestrict
        ((haarClosedSpan 𝕂) T) (fun f => hJ f f.property)
      retraction := (((walshRetraction (𝕂 := 𝕂)) φ).comp ((haarClosedSpan 𝕂) T).subtypeL).codRestrict
        ((haarClosedSpan 𝕂) S) (fun f => hU f f.property)
      retract_inclusion := fun f => Subtype.ext
        ((walshRetraction_substitution (𝕂 := 𝕂)) (walshSynthesis_dense (𝕂 := 𝕂)) φ hφ.injective f) }

end EvenOddHaarLevels
