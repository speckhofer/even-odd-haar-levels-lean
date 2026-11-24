import EvenOddHaarLevels.HaarMultiplier
import EvenOddHaarLevels.HaarOffChainGeometry
import EvenOddHaarLevels.L1SequenceEquivalences

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

theorem dyadicDilation_supported (J : DyadicIndex) (f : (L1 𝕂)) :
    ∀ᵐ x ∂unitIntervalMeasure, x ∉ dyadicInterval J → (dyadicDilation (𝕂 := 𝕂)) J f x = 0 := by
  have hh := (dilationL1_mem_intervalSupportedL1 (𝕂 := 𝕂))
    ((J.2 : ℝ)/(2 : ℝ)^J.1) (dyadicMeasure_pos J)
    (by rw [dyadicInterval_eq_affine J]; exact dyadicInterval_subset_unit J) f
  change ∀ᵐ x ∂unitIntervalMeasure, x ∉ Set.Ico _ _ → (dyadicDilation (𝕂 := 𝕂)) J f x = 0 at hh
  rwa [dyadicInterval_eq_affine J] at hh

theorem norm_sum_offChainDilation (s : Finset OffChainAddress) (f : OffChainAddress → (L1 𝕂)) :
    ‖∑ p ∈ s, (dyadicDilation (𝕂 := 𝕂)) (offChainCell p) (f p)‖ = ∑ p ∈ s, ‖f p‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.sum_insert hp, Finset.sum_insert hp]
    have hf : ∀ᵐ x ∂unitIntervalMeasure,
        x ∉ ⋃ q ∈ s, dyadicInterval (offChainCell q) →
          (∑ q ∈ s, (dyadicDilation (𝕂 := 𝕂)) (offChainCell q) (f q)) x = 0 := by
      have ha : ∀ᵐ x ∂unitIntervalMeasure,
          ∀ q ∈ s, x ∉ dyadicInterval (offChainCell q) →
            (dyadicDilation (𝕂 := 𝕂)) (offChainCell q) (f q) x = 0 := by
        exact (ae_all_iff.mpr fun q => ae_all_iff.mpr fun _ => (dyadicDilation_supported (𝕂 := 𝕂)) _ _)
      filter_upwards [ha, Lp.coeFn_finsetSum s (fun q => (dyadicDilation (𝕂 := 𝕂)) (offChainCell q) (f q))] with x hx hs
      intro hn
      rw [hs, Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro q hq
      apply hx q hq
      intro hm
      exact hn (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq,hm⟩⟩)
    have hd : Disjoint (dyadicInterval (offChainCell p))
        (⋃ q ∈ s, dyadicInterval (offChainCell q)) := by
      apply Set.disjoint_iUnion_right.mpr
      intro q
      apply Set.disjoint_iUnion_right.mpr
      intro hq
      exact offChainCell_disjoint (by intro he; subst q; exact hp hq)
    rw [(norm_add_of_disjoint_support (𝕂 := 𝕂)) _ _ _ _ hd ((dyadicDilation_supported (𝕂 := 𝕂)) _ _) hf,
      LinearIsometry.norm_map, ih]

def offChainCoordinateMap (p : OffChainAddress) : (X₀ 𝕂) →L[𝕂] (L1 𝕂) :=
  ((dyadicDilation (𝕂 := 𝕂)) (offChainCell p)).toContinuousLinearMap.comp (X₀ 𝕂).subtypeL

theorem norm_offChainCoordinateMap_le (p : OffChainAddress) : ‖(offChainCoordinateMap (𝕂 := 𝕂)) p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖(dyadicDilation (𝕂 := 𝕂)) (offChainCell p) (f : (L1 𝕂))‖ ≤ 1 * ‖f‖
  simp

def offChainSynthesis : Seq₁On OffChainAddress (X₀ 𝕂) →L[𝕂] (L1 𝕂) :=
  (lp.tsumCLM 𝕂 OffChainAddress (L1 𝕂)).comp
    (lp.mapCLM 1 (offChainCoordinateMap (𝕂 := 𝕂)) (by norm_num) (norm_offChainCoordinateMap_le (𝕂 := 𝕂)))

theorem offChainSynthesis_apply (f : Seq₁On OffChainAddress (X₀ 𝕂)) :
    (offChainSynthesis (𝕂 := 𝕂)) f = ∑' p, (dyadicDilation (𝕂 := 𝕂)) (offChainCell p) (f p : (L1 𝕂)) := rfl

theorem norm_offChainSynthesis (f : Seq₁On OffChainAddress (X₀ 𝕂)) :
    ‖(offChainSynthesis (𝕂 := 𝕂)) f‖ = ‖f‖ := by
  have hs : Summable (fun p => ‖(f p : (L1 𝕂))‖) := by
    simpa only [Submodule.norm_coe] using (l1_mem_iff _).mp f.property
  have hsn : Summable (fun p => ‖(dyadicDilation (𝕂 := 𝕂)) (offChainCell p) (f p : (L1 𝕂))‖) := by
    simpa only [LinearIsometry.norm_map] using hs
  have ht := hsn.of_norm.hasSum
  have hn := continuous_norm.continuousAt.tendsto.comp ht
  change Filter.Tendsto
    (fun s : Finset OffChainAddress => ‖∑ p ∈ s, (dyadicDilation (𝕂 := 𝕂)) (offChainCell p) (f p : (L1 𝕂))‖)
    Filter.atTop (nhds ‖∑' p, (dyadicDilation (𝕂 := 𝕂)) (offChainCell p) (f p : (L1 𝕂))‖) at hn
  simp only [(norm_sum_offChainDilation (𝕂 := 𝕂))] at hn
  have he := tendsto_nhds_unique hn hs.hasSum
  rw [(offChainSynthesis_apply (𝕂 := 𝕂)), he, l1_norm]
  simp only [Submodule.norm_coe]

/-- Disjoint affine copies summed as an actual linear isometry. -/
def offChainSynthesisIsometry : Seq₁On OffChainAddress (X₀ 𝕂) →ₗᵢ[𝕂] (L1 𝕂) where
  toLinearMap := (offChainSynthesis (𝕂 := 𝕂)).toLinearMap
  norm_map' := (norm_offChainSynthesis (𝕂 := 𝕂))

theorem offChainCoordinateMap_mem (p : OffChainAddress) (f : (X₀ 𝕂)) :
    (offChainCoordinateMap (𝕂 := 𝕂)) p f ∈ (offChainSpan (𝕂 := 𝕂)) := by
  have hf : (dyadicDilation (𝕂 := 𝕂)) (offChainCell p) f ∈
      (X₀ 𝕂).map ((dyadicDilation (𝕂 := 𝕂)) (offChainCell p)).toLinearMap := ⟨f,f.property,rfl⟩
  change (dyadicDilation (𝕂 := 𝕂)) (offChainCell p) f ∈
    ((Submodule.span 𝕂 ((haarL1 𝕂) '' {I : DyadicIndex | Even I.1})).topologicalClosure).map _ at hf
  rw [(dyadicDilation_closed_span (𝕂 := 𝕂))] at hf
  apply (Submodule.topologicalClosure_mono (Submodule.span_mono (show
    (haarL1 𝕂) '' (dyadicDilationIndex (offChainCell p) '' {I : DyadicIndex | Even I.1}) ⊆
      (haarL1 𝕂) '' {I : DyadicIndex | Even I.1 ∧ I.2.val ≠ 0} from ?_))) hf
  rintro _ ⟨_,⟨I,hI,rfl⟩,rfl⟩
  refine ⟨dyadicDilationIndex (offChainCell p) I, ⟨?_,?_⟩,rfl⟩
  · rcases hI with ⟨m,hm⟩
    refine ⟨p.1+1+m,?_⟩
    simp only [dyadicDilationIndex_level, offChainCell_level]
    omega
  · rw [dyadicDilationIndex_position, offChainCell_position]
    have hp : 0 < 2^I.1 := Nat.two_pow_pos I.1
    nlinarith

theorem offChainSynthesis_mem (f : Seq₁On OffChainAddress (X₀ 𝕂)) :
    (offChainSynthesis (𝕂 := 𝕂)) f ∈ (offChainSpan (𝕂 := 𝕂)) := by
  rw [(offChainSynthesis_apply (𝕂 := 𝕂))]
  have hs : Summable (fun p => (dyadicDilation (𝕂 := 𝕂)) (offChainCell p) (f p : (L1 𝕂))) := by
    apply Summable.of_norm
    simpa only [LinearIsometry.norm_map, Submodule.norm_coe] using (l1_mem_iff _).mp f.property
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hs.hasSum
  apply Filter.Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro p _
  exact (offChainCoordinateMap_mem (𝕂 := 𝕂)) p (f p)

theorem offChainSynthesis_single (p : OffChainAddress) (f : (X₀ 𝕂)) :
    (offChainSynthesis (𝕂 := 𝕂)) (lp.single 1 p f) = (dyadicDilation (𝕂 := 𝕂)) (offChainCell p) (f : (L1 𝕂)) := by
  rw [(offChainSynthesis_apply (𝕂 := 𝕂)), tsum_eq_single p]
  · rw [lp.single_apply_self]
  · intro q hq
    rw [lp.single_apply_ne (E := fun _ : OffChainAddress => X₀ 𝕂) 1 p f hq]
    exact map_zero _

theorem offChainSynthesis_range : (offChainSynthesis (𝕂 := 𝕂)).toLinearMap.range = (offChainSpan (𝕂 := 𝕂)) := by
  have : CompleteSpace (X₀ 𝕂) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hc : IsClosed ((offChainSynthesis (𝕂 := 𝕂)).toLinearMap.range : Set (L1 𝕂)) :=
    (offChainSynthesisIsometry (𝕂 := 𝕂)).isometry.isClosedEmbedding.isClosed_range
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    exact (offChainSynthesis_mem (𝕂 := 𝕂)) f
  · apply Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) hc
    rintro _ ⟨K,hK,rfl⟩
    obtain ⟨p,I,hI,rfl⟩ := offChain_address K hK.1 hK.2
    let f : (X₀ 𝕂) := ⟨((2 : 𝕂)^(offChainCell p).1)⁻¹ • (haarL1 𝕂) I,
      (X₀ 𝕂).smul_mem _ (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨I,hI,rfl⟩))⟩
    refine ⟨lp.single 1 p f,?_⟩
    change (offChainSynthesis (𝕂 := 𝕂)) (lp.single 1 p f) = _
    rw [(offChainSynthesis_single (𝕂 := 𝕂))]
    change (dyadicDilation (𝕂 := 𝕂)) (offChainCell p) (((2 : 𝕂)^(offChainCell p).1)⁻¹ • (haarL1 𝕂) I) = _
    rw [map_smul, (dyadicDilation_haarL1 (𝕂 := 𝕂)), smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num)), one_smul]

/-- The off-chain span is the disjoint sum of affine copies of the even space. -/
def offChainAddressEquiv : Seq₁On OffChainAddress (X₀ 𝕂) ≃ₗᵢ[𝕂] (offChainSpan (𝕂 := 𝕂)) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (offChainSynthesis (𝕂 := 𝕂)).toLinearMap.codRestrict (offChainSpan (𝕂 := 𝕂)) (offChainSynthesis_mem (𝕂 := 𝕂))
      norm_map' := (norm_offChainSynthesis (𝕂 := 𝕂)) } (by
        intro f
        have hf : (f : (L1 𝕂)) ∈ (offChainSynthesis (𝕂 := 𝕂)).toLinearMap.range := by
          rw [(offChainSynthesis_range (𝕂 := 𝕂))]
          exact f.property
        obtain ⟨g,hg⟩ := hf
        exact ⟨g,Subtype.ext hg⟩)

/-- Enumerate the three branches at each chain depth. -/
def offChainEquiv : Seq₁ (X₀ 𝕂) ≃ₗᵢ[𝕂] (offChainSpan (𝕂 := 𝕂)) :=
  ((l1Reindex (𝕂 := 𝕂)) (Nat.divModEquiv 3)).trans (offChainAddressEquiv (𝕂 := 𝕂))

end EvenOddHaarLevels
