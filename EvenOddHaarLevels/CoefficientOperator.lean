import EvenOddHaarLevels.DyadicAveraging

open MeasureTheory

noncomputable section
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

/-- The scalar core of the four-quarter estimate (api:quarter, Step D7).
The hypotheses encode the absolute integral on each quarter. -/
theorem quarter_scalar_bound (a b c d : ℝ) (α β : 𝕂)
    (ha : ‖α‖ ≤ a) (hb : ‖α‖ ≤ b) (hc : ‖β‖ ≤ c) (hd : ‖β‖ ≤ d) :
    ‖2*(α-β)‖^2 ≤ 2*((a+b+c+d)^2 - (a^2+b^2+c^2+d^2)) := by
  have ha0 := (norm_nonneg α).trans ha
  have hb0 := (norm_nonneg α).trans hb
  have hc0 := (norm_nonneg β).trans hc
  have hd0 := (norm_nonneg β).trans hd
  have hab : ‖α‖^2 ≤ a*b := by nlinarith [mul_le_mul ha hb (norm_nonneg α) ha0]
  have hcd : ‖β‖^2 ≤ c*d := by nlinarith [mul_le_mul hc hd (norm_nonneg β) hc0]
  have hac : ‖α‖ * ‖β‖ ≤ a*c := mul_le_mul ha hc (norm_nonneg β) ha0
  have had : ‖α‖ * ‖β‖ ≤ a*d := mul_le_mul ha hd (norm_nonneg β) ha0
  have hbc : ‖α‖ * ‖β‖ ≤ b*c := mul_le_mul hb hc (norm_nonneg β) hb0
  have hbd : ‖α‖ * ‖β‖ ≤ b*d := mul_le_mul hb hd (norm_nonneg β) hb0
  have ht := norm_sub_le α β
  have hs := pow_le_pow_left₀ (norm_nonneg (α-β)) ht 2
  rw [norm_mul, RCLike.norm_ofNat] 
  nlinarith [mul_nonneg (norm_nonneg α) (norm_nonneg β)]

/-- The telescoping step, including N=0 and a nonnegative terminal remainder. -/
theorem finite_level_telescope (A B : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ n ≤ N, B n ≤ 2*(A n-A (n+1))) (hterm : 0 ≤ A (N+1)) :
    ∑ n ∈ Finset.range (N+1), B n ≤ 2*A 0 := by
  have hsum : ∀ m ≤ N+1, ∑ n ∈ Finset.range m, B n ≤ 2*(A 0-A m) := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hprev := ih (by omega)
      have hn := hstep m (by omega)
      linarith
  have hf := hsum (N+1) le_rfl
  linarith

def intervalMass (I : DyadicIndex) (f : (L1 𝕂)) : ℝ :=
  ∫ x in dyadicInterval I, ‖f x‖ ∂unitIntervalMeasure

theorem intervalMass_nonneg (I : DyadicIndex) (f : (L1 𝕂)) : 0 ≤ (intervalMass (𝕂 := 𝕂)) I f :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem intervalMass_children (I : DyadicIndex) (f : (L1 𝕂)) :
    (intervalMass (𝕂 := 𝕂)) I f = (intervalMass (𝕂 := 𝕂)) (dyadicChild I 0) f + (intervalMass (𝕂 := 𝕂)) (dyadicChild I 1) f :=
  dyadicIntegral_children I (MeasureTheory.L1.integrable_coeFn f).norm

theorem intervalFunctional_abs_le_mass (I : DyadicIndex) (f : (L1 𝕂)) :
    ‖(intervalFunctional (𝕂 := 𝕂)) I f‖ ≤ (intervalMass (𝕂 := 𝕂)) I f := by
  rw [(intervalFunctional_apply (𝕂 := 𝕂)), intervalMass]
  simpa only [Real.norm_eq_abs] using
    norm_integral_le_integral_norm (μ := unitIntervalMeasure.restrict (dyadicInterval I)) f

theorem intervalFunctional_children (I : DyadicIndex) (f : (L1 𝕂)) :
    (intervalFunctional (𝕂 := 𝕂)) I f = (intervalFunctional (𝕂 := 𝕂)) (dyadicChild I 0) f +
      (intervalFunctional (𝕂 := 𝕂)) (dyadicChild I 1) f := by
  simp only [(intervalFunctional_apply (𝕂 := 𝕂))]
  exact dyadicIntegral_children I (MeasureTheory.L1.integrable_coeFn f)

/-- Vanishing odd child coefficients equates each adjacent pair of quarter integrals. -/
theorem even_quarter_integrals (I : DyadicIndex) (hI : Even I.1) (f : (X₀ 𝕂)) :
    (intervalFunctional (𝕂 := 𝕂)) (dyadicQuarter I 0) f = (intervalFunctional (𝕂 := 𝕂)) (dyadicQuarter I 1) f ∧
    (intervalFunctional (𝕂 := 𝕂)) (dyadicQuarter I 2) f = (intervalFunctional (𝕂 := 𝕂)) (dyadicQuarter I 3) f := by
  have hc (j : Fin 2) := (haarCoefficient_vanishes_on_X₀ (𝕂 := 𝕂)) (dyadicChild I j)
    (hI.add_odd (by decide : Odd 1)) f
  have h0 := hc 0
  have h1 := hc 1
  rw [(haarCoefficient_children (𝕂 := 𝕂))] at h0 h1
  simp only [dyadicChild_child] at h0 h1
  exact ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1⟩

theorem even_quarter_bound (I : DyadicIndex) (hI : Even I.1) (f : (X₀ 𝕂)) :
    ‖(haarCoefficient (𝕂 := 𝕂)) I f‖^2 ≤ 2 * ((intervalMass (𝕂 := 𝕂)) I f ^ 2 -
      ∑ j : Fin 4, (intervalMass (𝕂 := 𝕂)) (dyadicQuarter I j) f ^ 2) := by
  obtain ⟨h01,h23⟩ := (even_quarter_integrals (𝕂 := 𝕂)) I hI f
  have hcoef : (haarCoefficient (𝕂 := 𝕂)) I f = 2 *
      ((intervalFunctional (𝕂 := 𝕂)) (dyadicQuarter I 0) f - (intervalFunctional (𝕂 := 𝕂)) (dyadicQuarter I 2) f) := by
    rw [(haarCoefficient_children (𝕂 := 𝕂)), (intervalFunctional_children (𝕂 := 𝕂)) (dyadicChild I 0),
      (intervalFunctional_children (𝕂 := 𝕂)) (dyadicChild I 1)]
    simp only [dyadicChild_child]
    change (intervalFunctional (𝕂 := 𝕂)) (dyadicQuarter I 0) f + (intervalFunctional (𝕂 := 𝕂)) (dyadicQuarter I 1) f -
      ((intervalFunctional (𝕂 := 𝕂)) (dyadicQuarter I 2) f + (intervalFunctional (𝕂 := 𝕂)) (dyadicQuarter I 3) f) = _
    rw [h01, h23]
    ring
  have hmass : (intervalMass (𝕂 := 𝕂)) I f = (intervalMass (𝕂 := 𝕂)) (dyadicQuarter I 0) f +
      (intervalMass (𝕂 := 𝕂)) (dyadicQuarter I 1) f + (intervalMass (𝕂 := 𝕂)) (dyadicQuarter I 2) f +
      (intervalMass (𝕂 := 𝕂)) (dyadicQuarter I 3) f := by
    rw [(intervalMass_children (𝕂 := 𝕂)) I, (intervalMass_children (𝕂 := 𝕂)) (dyadicChild I 0),
      (intervalMass_children (𝕂 := 𝕂)) (dyadicChild I 1)]
    simp only [dyadicChild_child]
    change (intervalMass (𝕂 := 𝕂)) (dyadicQuarter I 0) f + (intervalMass (𝕂 := 𝕂)) (dyadicQuarter I 1) f +
      ((intervalMass (𝕂 := 𝕂)) (dyadicQuarter I 2) f + (intervalMass (𝕂 := 𝕂)) (dyadicQuarter I 3) f) = _
    ring
  rw [hcoef, hmass, Fin.sum_univ_four]
  apply quarter_scalar_bound
  · exact (intervalFunctional_abs_le_mass (𝕂 := 𝕂)) _ _
  · rw [h01]; exact (intervalFunctional_abs_le_mass (𝕂 := 𝕂)) _ _
  · exact (intervalFunctional_abs_le_mass (𝕂 := 𝕂)) _ _
  · rw [h23]; exact (intervalFunctional_abs_le_mass (𝕂 := 𝕂)) _ _

def evenLevelMass (n : ℕ) (f : (L1 𝕂)) : ℝ :=
  ∑ k : Fin (2^(2*n)), (intervalMass (𝕂 := 𝕂)) ⟨2*n,k⟩ f ^ 2

theorem evenLevelMass_nonneg (n : ℕ) (f : (L1 𝕂)) : 0 ≤ (evenLevelMass (𝕂 := 𝕂)) n f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem even_level_bound (n : ℕ) (f : (X₀ 𝕂)) :
    (∑ k : Fin (2^(2*n)), ‖(haarCoefficient (𝕂 := 𝕂)) ⟨2*n,k⟩ f‖^2) ≤
      2 * ((evenLevelMass (𝕂 := 𝕂)) n f - (evenLevelMass (𝕂 := 𝕂)) (n+1) f) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (k : Fin (2^(2*n))) _ => (even_quarter_bound (𝕂 := 𝕂)) ⟨2*n,k⟩ (by exact even_two_mul n) f)
  have hre : (evenLevelMass (𝕂 := 𝕂)) (n+1) f =
      ∑ k : Fin (2^(2*n)), ∑ j : Fin 4, (intervalMass (𝕂 := 𝕂)) (dyadicQuarter ⟨2*n,k⟩ j) f ^ 2 := by
    unfold evenLevelMass
    have hn : 2*(n+1) = 2*n+2 := by omega
    exact dyadicQuarter_sum (2*n) (fun I => (intervalMass (𝕂 := 𝕂)) I f ^ 2)
  rw [hre]
  unfold evenLevelMass
  simpa only [← Finset.mul_sum, Finset.sum_sub_distrib] using h

theorem evenLevelMass_zero (f : (L1 𝕂)) : (evenLevelMass (𝕂 := 𝕂)) 0 f = ‖f‖^2 := by
  unfold evenLevelMass
  change (∑ k : Fin 1, (intervalMass (𝕂 := 𝕂)) ⟨0,k⟩ f ^ 2) = _
  rw [Fin.sum_univ_one]
  have hi : dyadicInterval ⟨0,0⟩ = Set.Ico (0 : ℝ) 1 := by norm_num [dyadicInterval]
  change (intervalMass (𝕂 := 𝕂)) ⟨0,0⟩ f ^ 2 = _
  rw [intervalMass, hi]
  simp only [unitIntervalMeasure, Measure.restrict_restrict measurableSet_Ico, Set.inter_self]
  change (∫ x, ‖f x‖ ∂unitIntervalMeasure)^2 = ‖f‖^2
  rw [← MeasureTheory.L1.norm_eq_integral_norm]

theorem finite_even_level_bound (N : ℕ) (f : (X₀ 𝕂)) :
    (∑ n ∈ Finset.range (N+1), ∑ k : Fin (2^(2*n)), ‖(haarCoefficient (𝕂 := 𝕂)) ⟨2*n,k⟩ f‖^2) ≤
      2 * ‖(f : (L1 𝕂))‖^2 := by
  have h := finite_level_telescope (fun n => (evenLevelMass (𝕂 := 𝕂)) n f)
    (fun n => ∑ k : Fin (2^(2*n)), ‖(haarCoefficient (𝕂 := 𝕂)) ⟨2*n,k⟩ f‖^2) N
    (fun n _ => (even_level_bound (𝕂 := 𝕂)) n f) ((evenLevelMass_nonneg (𝕂 := 𝕂)) (N+1) f)
  rwa [(evenLevelMass_zero (𝕂 := 𝕂))] at h

/-- An even interval encoded by its half-level and its position. -/
abbrev EvenDyadicIndex := (n : ℕ) × Fin (2^(2*n))

def evenDyadic (I : EvenDyadicIndex) : DyadicIndex := ⟨2*I.1,I.2⟩

theorem finite_even_subset_bound (F : Finset EvenDyadicIndex) (f : (X₀ 𝕂)) :
    ∑ I ∈ F, ‖(haarCoefficient (𝕂 := 𝕂)) (evenDyadic I) f‖^2 ≤ 2 * ‖(f : (L1 𝕂))‖^2 := by
  classical
  let N := F.sup (fun I => I.1)
  let S : Finset EvenDyadicIndex := (Finset.range (N+1)).sigma (fun _ => Finset.univ)
  have hs : F ⊆ S := by
    intro I hI
    simp only [S, Finset.mem_sigma, Finset.mem_range, Finset.mem_univ, and_true]
    exact Nat.lt_succ_of_le (Finset.le_sup hI)
  calc
    _ ≤ ∑ I ∈ S, ‖(haarCoefficient (𝕂 := 𝕂)) (evenDyadic I) f‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => sq_nonneg _)
    _ = ∑ n ∈ Finset.range (N+1), ∑ k : Fin (2^(2*n)), ‖(haarCoefficient (𝕂 := 𝕂)) ⟨2*n,k⟩ f‖^2 := by
      rw [Finset.sum_sigma]
      rfl
    _ ≤ _ := (finite_even_level_bound (𝕂 := 𝕂)) N f

theorem evenCoefficients_memℓp (f : (X₀ 𝕂)) :
    Memℓp (fun I : EvenDyadicIndex => (haarCoefficient (𝕂 := 𝕂)) (evenDyadic I) f) 2 := by
  apply memℓp_gen' (C := 2 * ‖(f : (L1 𝕂))‖^2)
  intro F
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs] using (finite_even_subset_bound (𝕂 := 𝕂)) F f

def coefficientLinear : (X₀ 𝕂) →ₗ[𝕂] lp (fun _ : EvenDyadicIndex => 𝕂) 2 where
  toFun f := ⟨fun I => (haarCoefficient (𝕂 := 𝕂)) (evenDyadic I) f, (evenCoefficients_memℓp (𝕂 := 𝕂)) f⟩
  map_add' f g := by ext I; exact map_add ((haarCoefficient (𝕂 := 𝕂)) (evenDyadic I)) (f : (L1 𝕂)) (g : (L1 𝕂))
  map_smul' c f := by ext I; exact map_smul ((haarCoefficient (𝕂 := 𝕂)) (evenDyadic I)) c (f : (L1 𝕂))

theorem coefficientLinear_bound (f : (X₀ 𝕂)) : ‖(coefficientLinear (𝕂 := 𝕂)) f‖ ≤ Real.sqrt 2 * ‖f‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  intro F
  change (∑ I ∈ F, ‖(haarCoefficient (𝕂 := 𝕂)) (evenDyadic I) (f : (L1 𝕂))‖ ^ (2 : ENNReal).toReal) ≤
    (Real.sqrt 2 * ‖(f : (L1 𝕂))‖) ^ (2 : ENNReal).toReal
  have h := (finite_even_subset_bound (𝕂 := 𝕂)) F f
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using h

def coefficientOperator : (X₀ 𝕂) →L[𝕂] lp (fun _ : EvenDyadicIndex => 𝕂) 2 :=
  (coefficientLinear (𝕂 := 𝕂)).mkContinuous (Real.sqrt 2) (coefficientLinear_bound (𝕂 := 𝕂))

theorem coefficientOperator_norm : ‖(coefficientOperator (𝕂 := 𝕂))‖ ≤ Real.sqrt 2 :=
  (coefficientLinear (𝕂 := 𝕂)).mkContinuous_norm_le (Real.sqrt_nonneg _) (coefficientLinear_bound (𝕂 := 𝕂))

@[simp] theorem coefficientOperator_apply (f : (X₀ 𝕂)) (I : EvenDyadicIndex) :
    (coefficientOperator (𝕂 := 𝕂)) f I = (haarCoefficient (𝕂 := 𝕂)) (evenDyadic I) f := rfl

end EvenOddHaarLevels
