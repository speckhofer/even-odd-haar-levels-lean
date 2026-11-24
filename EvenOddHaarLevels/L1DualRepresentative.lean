import EvenOddHaarLevels.DyadicAveraging

noncomputable section
open MeasureTheory
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

/-- Inclusion of L² classes into L¹ on the canonical probability space. -/
def l2ToL1Linear : (L2 (𝕂 := 𝕂)) →ₗ[𝕂] (L1 𝕂) where
  toFun f := ⟨f.val, Lp.antitone (by norm_num : (1 : ENNReal) ≤ 2) f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem l2ToL1_bound (f : (L2 (𝕂 := 𝕂))) : ‖(l2ToL1Linear (𝕂 := 𝕂)) f‖ ≤ ‖f‖ := by
  simp only [Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.memLp f).2.ne
  exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.memLp f).1

def l2ToL1 : (L2 (𝕂 := 𝕂)) →L[𝕂] (L1 𝕂) :=
  (l2ToL1Linear (𝕂 := 𝕂)).mkContinuous 1 (fun f => by simpa using (l2ToL1_bound (𝕂 := 𝕂)) f)

theorem l2ToL1_norm : ‖(l2ToL1 (𝕂 := 𝕂))‖ ≤ 1 :=
  (l2ToL1Linear (𝕂 := 𝕂)).mkContinuous_norm_le zero_le_one _

theorem l2ToL1_ae (f : (L2 (𝕂 := 𝕂))) : ((l2ToL1 (𝕂 := 𝕂)) f : ℝ → 𝕂) =ᵐ[unitIntervalMeasure] f :=
  Filter.Eventually.of_forall fun _ => rfl

/-- Riesz representative of the restriction of an L¹ functional to L². -/
def dualL2Representative (Φ : (L1 𝕂) →L[𝕂] 𝕂) : (L2 (𝕂 := 𝕂)) :=
  (InnerProductSpace.toDual 𝕂 (L2 (𝕂 := 𝕂))).symm (Φ.comp (l2ToL1 (𝕂 := 𝕂)))

theorem dualL2Representative_pairing (Φ : (L1 𝕂) →L[𝕂] 𝕂) (f : (L2 (𝕂 := 𝕂))) :
    Φ ((l2ToL1 (𝕂 := 𝕂)) f) = ∫ x, f x * star ((dualL2Representative (𝕂 := 𝕂)) Φ x) ∂unitIntervalMeasure := by
  have h : inner 𝕂 ((dualL2Representative (𝕂 := 𝕂)) Φ) f = Φ ((l2ToL1 (𝕂 := 𝕂)) f) :=
    InnerProductSpace.toDual_symm_apply
  rw [← h, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp [RCLike.inner_apply]

theorem dualL2Representative_indicator (Φ : (L1 𝕂) →L[𝕂] 𝕂)
    (s : Set ℝ) (hs : MeasurableSet s) :
    Φ (indicatorConstLp 1 hs (measure_ne_top _ _) (1 : 𝕂)) =
      ∫ x in s, star ((dualL2Representative (𝕂 := 𝕂)) Φ x) ∂unitIntervalMeasure := by
  have h := (dualL2Representative_pairing (𝕂 := 𝕂)) Φ
    (indicatorConstLp 2 hs (measure_ne_top _ _) (1 : 𝕂))
  have hi : (l2ToL1 (𝕂 := 𝕂)) (indicatorConstLp 2 hs (measure_ne_top _ _) (1 : 𝕂)) =
      indicatorConstLp 1 hs (measure_ne_top _ _) (1 : 𝕂) := rfl
  rw [hi] at h
  rw [h, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs)
    (hμs := measure_ne_top _ _) (c := (1 : 𝕂))] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

theorem dualL2Representative_setIntegral_bound (Φ : (L1 𝕂) →L[𝕂] 𝕂)
    (s : Set ℝ) (hs : MeasurableSet s) :
    ‖∫ x in s, star ((dualL2Representative (𝕂 := 𝕂)) Φ x) ∂unitIntervalMeasure‖ ≤
      ‖Φ‖ * unitIntervalMeasure.real s := by
  rw [← (dualL2Representative_indicator (𝕂 := 𝕂)) Φ s hs]
  have h := Φ.le_opNorm (indicatorConstLp 1 hs (measure_ne_top _ _) (1 : 𝕂))
  simpa [norm_indicatorConstLp, Real.norm_eq_abs] using h

/-- Testing the Riesz representative restricted to measurable sets gives
∫_s ‖g‖² ≤ ‖Φ‖ ∫_s ‖g‖. AE comparison then gives the essential norm bound.
This norm argument applies over both scalar fields. -/
theorem dualL2Representative_essential_bound (Φ : (L1 𝕂) →L[𝕂] 𝕂) :
    ∀ᵐ x ∂unitIntervalMeasure, ‖(dualL2Representative (𝕂 := 𝕂)) Φ x‖ ≤ ‖Φ‖ := by
  let g := dualL2Representative Φ
  have hg := Lp.memLp g
  have hg1 : Integrable g unitIntervalMeasure :=
    memLp_one_iff_integrable.mp (hg.mono_exponent (by norm_num))
  have hsq : Integrable (fun x => ‖g x‖ ^ 2) unitIntervalMeasure := hg.integrable_norm_pow (by decide)
  have hcomp : (fun x => ‖g x‖ ^ 2) ≤ᵐ[unitIntervalMeasure] (fun x => ‖Φ‖ * ‖g x‖) := by
    apply ae_le_of_forall_setIntegral_le hsq (hg1.norm.const_mul ‖Φ‖)
    intro s hs _
    let f : L2 (𝕂 := 𝕂) := (hg.indicator hs).toLp (s.indicator g)
    have hf : (f : ℝ → 𝕂) =ᵐ[unitIntervalMeasure] s.indicator g := (hg.indicator hs).coeFn_toLp
    have hn : ‖l2ToL1 f‖ = ∫ x in s, ‖g x‖ ∂unitIntervalMeasure := by
      rw [MeasureTheory.L1.norm_eq_integral_norm, ← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [l2ToL1_ae f, hf] with x hx hy
      rw [hx, hy]
      by_cases hxs : x ∈ s <;> simp [hxs]
    have hp : Φ (l2ToL1 f) = ((∫ x in s, ‖g x‖ ^ 2 ∂unitIntervalMeasure : ℝ) : 𝕂) := by
      rw [dualL2Representative_pairing, ← integral_ofReal, ← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]
      by_cases hxs : x ∈ s
      · simp only [Set.indicator_of_mem hxs]
        simpa only [g, RCLike.ofReal_pow, RCLike.star_def] using RCLike.mul_conj (g x)
      · simp [hxs]
    have hb := Φ.le_opNorm (l2ToL1 f)
    rw [hp, RCLike.norm_ofReal, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _)), hn] at hb
    simpa only [integral_const_mul] using hb
  filter_upwards [hcomp] with x hx
  change ‖g x‖ ≤ ‖Φ‖
  by_cases hz : ‖g x‖ = 0
  · rw [hz]; exact norm_nonneg _
  · rw [pow_two] at hx
    exact le_of_mul_le_mul_right hx (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))

theorem dualL2Representative_norm (Φ : (L1 𝕂) →L[𝕂] 𝕂) : ‖(dualL2Representative (𝕂 := 𝕂)) Φ‖ ≤ ‖Φ‖ := by
  calc
    _ = ‖Φ.comp (l2ToL1 (𝕂 := 𝕂))‖ := (InnerProductSpace.toDual 𝕂 (L2 (𝕂 := 𝕂))).symm.norm_map _
    _ ≤ ‖Φ‖ * ‖(l2ToL1 (𝕂 := 𝕂))‖ := Φ.opNorm_comp_le (l2ToL1 (𝕂 := 𝕂))
    _ ≤ ‖Φ‖ := by nlinarith [norm_nonneg Φ, (l2ToL1_norm (𝕂 := 𝕂))]

def dyadicAverageL2 (m : ℕ) (f : (L1 𝕂)) : (L2 (𝕂 := 𝕂)) :=
  ∑ k : Fin (2^m), ((dyadicMeasure ⟨m,k⟩ : 𝕂)⁻¹ * (intervalFunctional (𝕂 := 𝕂)) ⟨m,k⟩ f) •
    indicatorConstLp 2 (dyadicInterval_measurable ⟨m,k⟩) (measure_ne_top _ _) (1 : 𝕂)

theorem l2ToL1_dyadicAverageL2 (m : ℕ) (f : (L1 𝕂)) :
    (l2ToL1 (𝕂 := 𝕂)) ((dyadicAverageL2 (𝕂 := 𝕂)) m f) = (dyadicAverage (𝕂 := 𝕂)) m f := by
  rw [dyadicAverageL2, map_sum, (dyadicAverage_apply (𝕂 := 𝕂))]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  rfl

def boundedDualPairing (Φ : (L1 𝕂) →L[𝕂] 𝕂) : (L1 𝕂) →L[𝕂] 𝕂 :=
  (boundedPairing (𝕂 := 𝕂)) (fun x => star ((dualL2Representative (𝕂 := 𝕂)) Φ x)) ‖Φ‖ (Lp.memLp ((dualL2Representative (𝕂 := 𝕂)) Φ)).1.star
    (((dualL2Representative_essential_bound (𝕂 := 𝕂)) Φ).mono (fun _ hx => by simpa only [norm_star] using hx))

theorem boundedDualPairing_l2 (Φ : (L1 𝕂) →L[𝕂] 𝕂) (f : (L2 (𝕂 := 𝕂))) :
    (boundedDualPairing (𝕂 := 𝕂)) Φ ((l2ToL1 (𝕂 := 𝕂)) f) = Φ ((l2ToL1 (𝕂 := 𝕂)) f) := by
  rw [boundedDualPairing, (boundedPairing_apply (𝕂 := 𝕂)), (dualL2Representative_pairing (𝕂 := 𝕂))]
  apply integral_congr_ae
  filter_upwards [(l2ToL1_ae (𝕂 := 𝕂)) f] with x hx
  rw [hx]

theorem boundedDualPairing_eq (Φ : (L1 𝕂) →L[𝕂] 𝕂) (f : (L1 𝕂)) : (boundedDualPairing (𝕂 := 𝕂)) Φ f = Φ f := by
  have hclosed : IsClosed {x : (L1 𝕂) | (boundedDualPairing (𝕂 := 𝕂)) Φ x = Φ x} :=
    isClosed_eq ((boundedDualPairing (𝕂 := 𝕂)) Φ).continuous Φ.continuous
  apply hclosed.mem_of_tendsto ((dyadicAverage_tendsto (𝕂 := 𝕂)) f)
  exact Filter.Eventually.of_forall fun m => by
    rw [← (l2ToL1_dyadicAverageL2 (𝕂 := 𝕂))]
    exact (boundedDualPairing_l2 (𝕂 := 𝕂)) Φ _

theorem exists_bounded_dualRepresentative (Φ : (L1 𝕂) →L[𝕂] 𝕂) :
    ∃ g : (L2 (𝕂 := 𝕂)), (∀ᵐ x ∂unitIntervalMeasure, ‖g x‖ ≤ ‖Φ‖) ∧
      ∀ f : (L1 𝕂), Φ f = ∫ x, f x * star (g x) ∂unitIntervalMeasure := by
  refine ⟨(dualL2Representative (𝕂 := 𝕂)) Φ, (dualL2Representative_essential_bound (𝕂 := 𝕂)) Φ, fun f => ?_⟩
  rw [← (boundedDualPairing_eq (𝕂 := 𝕂)) Φ f, boundedDualPairing, (boundedPairing_apply (𝕂 := 𝕂))]

end EvenOddHaarLevels
