import EvenOddHaarLevels.HaarFunctions

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

def meanFunctional : (L1 𝕂) →L[𝕂] 𝕂 := MeasureTheory.L1.integralCLM' 𝕂

theorem meanFunctional_apply (f : (L1 𝕂)) :
    (meanFunctional (𝕂 := 𝕂)) f = ∫ x, f x ∂unitIntervalMeasure := by
  rw [meanFunctional, ← MeasureTheory.L1.integral_eq' 𝕂]
  exact MeasureTheory.L1.integral_eq_integral f

theorem meanFunctional_norm : ‖meanFunctional (𝕂 := 𝕂)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul, meanFunctional_apply] using
    (MeasureTheory.norm_integral_le_integral_norm (f : ℝ → 𝕂)).trans_eq
      (MeasureTheory.L1.norm_eq_integral_norm f).symm

def boundedPairing (b : ℝ → 𝕂) (M : ℝ)
    (hb : AEStronglyMeasurable b unitIntervalMeasure)
    (hbound : ∀ᵐ x ∂unitIntervalMeasure, ‖b x‖ ≤ M) : (L1 𝕂) →L[𝕂] 𝕂 :=
  ContinuousLinearMap.lpPairing unitIntervalMeasure ∞ 1 (ContinuousLinearMap.mul 𝕂 𝕂)
    ((memLp_top_of_bound hb M hbound).toLp b)

theorem boundedPairing_apply (b : ℝ → 𝕂) (M : ℝ)
    (hb : AEStronglyMeasurable b unitIntervalMeasure)
    (hbound : ∀ᵐ x ∂unitIntervalMeasure, ‖b x‖ ≤ M) (f : (L1 𝕂)) :
    (boundedPairing (𝕂 := 𝕂)) b M hb hbound f = ∫ x, f x * b x ∂unitIntervalMeasure := by
  rw [boundedPairing, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(memLp_top_of_bound hb M hbound).coeFn_toLp] with x hx
  change _ * f x = f x * b x
  rw [hx, mul_comm]

theorem boundedPairing_norm (b : ℝ → 𝕂) {M : ℝ} (hM : 0 ≤ M)
    (hb : AEStronglyMeasurable b unitIntervalMeasure)
    (hbound : ∀ᵐ x ∂unitIntervalMeasure, ‖b x‖ ≤ M) :
    ‖(boundedPairing (𝕂 := 𝕂)) b M hb hbound‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro f
  rw [(boundedPairing_apply (𝕂 := 𝕂))]
  have hi := (ContinuousLinearMap.mul 𝕂 𝕂).integrable_of_bilin_of_bdd_right M
    (MeasureTheory.L1.integrable_coeFn f) hb hbound
  change Integrable (fun x => f x * b x) unitIntervalMeasure at hi
  calc
    ‖∫ x, f x * b x ∂unitIntervalMeasure‖ ≤ ∫ x, ‖f x * b x‖ ∂unitIntervalMeasure :=
      by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x * b x)
    _ ≤ ∫ x, M * ‖f x‖ ∂unitIntervalMeasure := by
      apply integral_mono_ae hi.norm ((MeasureTheory.L1.integrable_coeFn f).norm.const_mul M)
      filter_upwards [hbound] with x hx
      rw [norm_mul]
      nlinarith [norm_nonneg (f x)]
    _ = M * ‖f‖ := by rw [integral_const_mul, MeasureTheory.L1.norm_eq_integral_norm]

def haarCoefficient (I : DyadicIndex) : (L1 𝕂) →L[𝕂] 𝕂 :=
  (boundedPairing (𝕂 := 𝕂)) ((haarFunction 𝕂) I) 1 ((haarFunction_measurable (𝕂 := 𝕂)) I).aestronglyMeasurable
    (.of_forall fun x => by simpa only [Real.norm_eq_abs] using (haarFunction_abs_le_one (𝕂 := 𝕂)) I x)

theorem haarCoefficient_apply (I : DyadicIndex) (f : (L1 𝕂)) :
    (haarCoefficient (𝕂 := 𝕂)) I f = ∫ x, f x * (haarFunction 𝕂) I x ∂unitIntervalMeasure :=
  (boundedPairing_apply (𝕂 := 𝕂)) _ _ _ _ _

theorem haarCoefficient_norm (I : DyadicIndex) : ‖(haarCoefficient (𝕂 := 𝕂)) I‖ ≤ 1 :=
  (boundedPairing_norm (𝕂 := 𝕂)) _ zero_le_one _ _

theorem closedSpan_vanish {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    [NormedAddCommGroup F] [NormedSpace 𝕂 F] (L : E →L[𝕂] F) (A : Set E)
    (h : ∀ a ∈ A, L a = 0) {x : E} (hx : x ∈ (Submodule.span 𝕂 A).topologicalClosure) :
    L x = 0 := by
  have hs : Submodule.span 𝕂 A ≤ L.ker := Submodule.span_le.mpr h
  exact (Submodule.topologicalClosure_minimal _ hs L.isClosed_ker) hx

theorem meanFunctional_haar (I : DyadicIndex) : (meanFunctional (𝕂 := 𝕂)) ((haarL1 𝕂) I) = 0 := by
  rw [(meanFunctional_apply (𝕂 := 𝕂))]
  exact (integral_congr_ae ((haarL1_ae (𝕂 := 𝕂)) I)).trans ((haar_integral (𝕂 := 𝕂)) I)

theorem meanFunctional_X₀ (f : (X₀ 𝕂)) : (meanFunctional (𝕂 := 𝕂)) f = 0 := by
  apply (closedSpan_vanish (𝕂 := 𝕂)) (meanFunctional (𝕂 := 𝕂)) _ _ f.property
  rintro _ ⟨I, _, rfl⟩
  exact (meanFunctional_haar (𝕂 := 𝕂)) I

theorem meanFunctional_X₁ (f : (X₁ 𝕂)) : (meanFunctional (𝕂 := 𝕂)) f = 0 := by
  apply (closedSpan_vanish (𝕂 := 𝕂)) (meanFunctional (𝕂 := 𝕂)) _ _ f.property
  rintro _ ⟨I, _, rfl⟩
  exact (meanFunctional_haar (𝕂 := 𝕂)) I

theorem haarCoefficient_haar (I J : DyadicIndex) :
    (haarCoefficient (𝕂 := 𝕂)) I ((haarL1 𝕂) J) = if I = J then (dyadicMeasure I : 𝕂) else 0 := by
  rw [(haarCoefficient_apply (𝕂 := 𝕂))]
  have he : (∫ x, (haarL1 𝕂) J x * (haarFunction 𝕂) I x ∂unitIntervalMeasure) =
      ∫ x, (haarFunction 𝕂) J x * (haarFunction 𝕂) I x ∂unitIntervalMeasure := by
    apply integral_congr_ae
    filter_upwards [(haarL1_ae (𝕂 := 𝕂)) J] with x hx
    rw [hx]
  rw [he]
  by_cases h : I = J
  · subst J
    simp only [ite_true]
    simp_rw [← pow_two, (haarFunction_sq (𝕂 := 𝕂))]
    rw [integral_indicator_const (1 : 𝕂) (dyadicInterval_measurable I)]
    simp [dyadicInterval_real_measure, RCLike.real_smul_eq_coe_mul]
  · rw [if_neg h]
    exact (haar_cross_integral (𝕂 := 𝕂)) J I (Ne.symm h)

theorem haarCoefficient_vanishes_on_X₀ (I : DyadicIndex) (hI : Odd I.1) (f : (X₀ 𝕂)) :
    (haarCoefficient (𝕂 := 𝕂)) I f = 0 := by
  apply (closedSpan_vanish (𝕂 := 𝕂)) ((haarCoefficient (𝕂 := 𝕂)) I) _ _ f.property
  rintro _ ⟨J, hJ, rfl⟩
  rw [(haarCoefficient_haar (𝕂 := 𝕂)), if_neg]
  intro he
  subst J
  exact (Nat.not_even_iff_odd.mpr hI) hJ

theorem haarCoefficient_vanishes_on_X₁ (I : DyadicIndex) (hI : Even I.1) (f : (X₁ 𝕂)) :
    (haarCoefficient (𝕂 := 𝕂)) I f = 0 := by
  apply (closedSpan_vanish (𝕂 := 𝕂)) ((haarCoefficient (𝕂 := 𝕂)) I) _ _ f.property
  rintro _ ⟨J, hJ, rfl⟩
  rw [(haarCoefficient_haar (𝕂 := 𝕂)), if_neg]
  intro he
  subst J
  exact (Nat.not_even_iff_odd.mpr hJ) hI

end EvenOddHaarLevels
