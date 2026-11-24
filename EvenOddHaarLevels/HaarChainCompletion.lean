import EvenOddHaarLevels.HaarChain

noncomputable section
open MeasureTheory
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

section FiniteLower
variable (hfinite : ∀ (F : Finset ℕ) (c : ℕ → 𝕂),
  (∑ n ∈ F, ‖c n‖) ≤ 2 * ‖∑ n ∈ F, c n • (chainVector (𝕂 := 𝕂)) n‖)
include hfinite

theorem chainSynthesis_lower_of_finite (f : Seq₁ 𝕂) :
    ‖f‖ ≤ 2 * ‖(chainSynthesis (𝕂 := 𝕂)) f‖ := by
  have hs : Summable (fun n => ‖f n‖) := by
    simpa only [Real.norm_eq_abs] using (l1_mem_iff _).mp f.property
  have ht := (chainSynthesis (𝕂 := 𝕂)).hasSum (lp.hasSum_single (by norm_num : (1 : ENNReal) ≠ ⊤) f)
  simp only [(chainSynthesis_single (𝕂 := 𝕂))] at ht
  have hn : Filter.Tendsto (fun F : Finset ℕ => 2 * ‖∑ n ∈ F, f n • (chainVector (𝕂 := 𝕂)) n‖)
      Filter.atTop (nhds (2 * ‖(chainSynthesis (𝕂 := 𝕂)) f‖)) :=
    tendsto_const_nhds.mul (continuous_norm.continuousAt.tendsto.comp ht)
  have hl := le_of_tendsto_of_tendsto hs.hasSum hn (Filter.Eventually.of_forall fun F => hfinite F f)
  simpa only [l1_norm, Real.norm_eq_abs] using hl

theorem chainSynthesis_injective_of_finite : Function.Injective (chainSynthesis (𝕂 := 𝕂)) :=
  ((chainSynthesis (𝕂 := 𝕂)).antilipschitz_of_bound (K := 2) ((chainSynthesis_lower_of_finite (𝕂 := 𝕂)) hfinite)).injective

theorem chainSynthesis_closed_range_of_finite :
    IsClosed ((chainSynthesis (𝕂 := 𝕂)).toLinearMap.range : Set (L1 𝕂)) :=
  ((chainSynthesis (𝕂 := 𝕂)).antilipschitz_of_bound (K := 2) ((chainSynthesis_lower_of_finite (𝕂 := 𝕂)) hfinite)).isClosed_range
    (chainSynthesis (𝕂 := 𝕂)).uniformContinuous

omit hfinite in
theorem chainSynthesis_mem_chainSpan (f : Seq₁ 𝕂) : (chainSynthesis (𝕂 := 𝕂)) f ∈ (chainSpan (𝕂 := 𝕂)) := by
  have ht := (chainSynthesis (𝕂 := 𝕂)).hasSum (lp.hasSum_single (by norm_num : (1 : ENNReal) ≠ ⊤) f)
  simp only [(chainSynthesis_single (𝕂 := 𝕂))] at ht
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro F
  apply Submodule.sum_mem
  intro n _
  apply Submodule.smul_mem
  unfold chainVector
  apply Submodule.smul_mem
  apply Submodule.le_topologicalClosure _
  apply Submodule.subset_span
  exact ⟨chainIndex n, ⟨⟨n,by dsimp [chainIndex]; omega⟩,rfl⟩,rfl⟩

theorem chainSynthesis_range_of_finite : (chainSynthesis (𝕂 := 𝕂)).toLinearMap.range = (chainSpan (𝕂 := 𝕂)) := by
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    exact (chainSynthesis_mem_chainSpan (𝕂 := 𝕂)) f
  · apply Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
      ((chainSynthesis_closed_range_of_finite (𝕂 := 𝕂)) hfinite)
    rintro _ ⟨⟨n,k⟩,⟨⟨m,hm⟩,hk⟩,rfl⟩
    have hn : n = 2*m := by dsimp at hm; omega
    have hk0 : k = 0 := Fin.ext hk
    subst k
    subst n
    refine ⟨lp.single 1 m ((4 : 𝕂)^m)⁻¹, ?_⟩
    change (chainSynthesis (𝕂 := 𝕂)) (lp.single 1 m ((4 : 𝕂)^m)⁻¹) = _
    rw [(chainSynthesis_single (𝕂 := 𝕂)), chainVector, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num)), one_smul]
    rfl

/-- The actual chain synthesis map, completed using the finite lower estimate. -/
def chainSynthesisEquivOfFiniteLower : Seq₁ 𝕂 ≃L[𝕂] (chainSpan (𝕂 := 𝕂)) := by
  let T : Seq₁ 𝕂 →L[𝕂] (chainSpan (𝕂 := 𝕂)) := (chainSynthesis (𝕂 := 𝕂)).codRestrict (chainSpan (𝕂 := 𝕂)) (chainSynthesis_mem_chainSpan (𝕂 := 𝕂))
  have hi : Function.Injective T := by
    intro f g hfg
    apply (chainSynthesis_injective_of_finite (𝕂 := 𝕂)) hfinite
    exact congrArg Subtype.val hfg
  have ho : Function.Surjective T := by
    intro g
    have hg : (g : (L1 𝕂)) ∈ (chainSynthesis (𝕂 := 𝕂)).toLinearMap.range := by
      rw [(chainSynthesis_range_of_finite (𝕂 := 𝕂)) hfinite]
      exact g.property
    obtain ⟨f,hf⟩ := hg
    exact ⟨f,Subtype.ext hf⟩
  have : CompleteSpace (chainSpan (𝕂 := 𝕂)) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  exact ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr ho)

@[simp] theorem chainSynthesisEquivOfFiniteLower_apply (f : Seq₁ 𝕂) :
    ((chainSynthesisEquivOfFiniteLower (𝕂 := 𝕂)) hfinite f : (L1 𝕂)) = (chainSynthesis (𝕂 := 𝕂)) f := rfl

theorem chainSynthesisEquivOfFiniteLower_symm_bound (g : (chainSpan (𝕂 := 𝕂))) :
    ‖((chainSynthesisEquivOfFiniteLower (𝕂 := 𝕂)) hfinite).symm g‖ ≤ 2 * ‖g‖ := by
  have hh := (chainSynthesis_lower_of_finite (𝕂 := 𝕂)) hfinite
    (((chainSynthesisEquivOfFiniteLower (𝕂 := 𝕂)) hfinite).symm g)
  have he : (chainSynthesis (𝕂 := 𝕂)) (((chainSynthesisEquivOfFiniteLower (𝕂 := 𝕂)) hfinite).symm g) = (g : (L1 𝕂)) := by
    rw [← (chainSynthesisEquivOfFiniteLower_apply (𝕂 := 𝕂)) hfinite]
    exact congrArg Subtype.val (((chainSynthesisEquivOfFiniteLower (𝕂 := 𝕂)) hfinite).apply_symm_apply g)
  rwa [he] at hh

end FiniteLower
end EvenOddHaarLevels
