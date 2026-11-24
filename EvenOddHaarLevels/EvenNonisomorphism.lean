import EvenOddHaarLevels.CoefficientOperator
import EvenOddHaarLevels.L1DualRepresentative
import EvenOddHaarLevels.FiniteSummingEstimates

noncomputable section
open MeasureTheory
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

theorem evenDyadic_injective : Function.Injective evenDyadic := by
  intro I J h
  cases I with | mk n k =>
    cases J with | mk m l =>
      have hn : n = m := by
        have he := congrArg Sigma.fst h
        dsimp [evenDyadic] at he
        omega
      subst m
      have hk : k = l := by
        have he := congrArg (fun d : DyadicIndex => d.2.val) h
        exact Fin.ext he
      subst l
      rfl

theorem haarL1_mem_X₀ (I : DyadicIndex) (hI : Even I.1) : (haarL1 𝕂) I ∈ (X₀ 𝕂) :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨I,hI,rfl⟩)

/-- The paper's normalized Haar test vector in the actual closed even span. -/
def normalizedEvenHaar (I : EvenDyadicIndex) : (X₀ 𝕂) :=
  (Real.sqrt (dyadicMeasure (evenDyadic I)))⁻¹ •
    (⟨(haarL1 𝕂) (evenDyadic I), (haarL1_mem_X₀ (𝕂 := 𝕂)) _ (even_two_mul I.1)⟩ : (X₀ 𝕂))

theorem coefficientOperator_normalizedEvenHaar (I : EvenDyadicIndex) :
    (coefficientOperator (𝕂 := 𝕂)) ((normalizedEvenHaar (𝕂 := 𝕂)) I) =
      lp.single 2 I ((Real.sqrt (dyadicMeasure (evenDyadic I)) : ℝ) : 𝕂) := by
  classical
  ext J
  rw [(coefficientOperator_apply (𝕂 := 𝕂))]
  change (haarCoefficient (𝕂 := 𝕂)) (evenDyadic J)
    ((Real.sqrt (dyadicMeasure (evenDyadic I)))⁻¹ • (haarL1 𝕂) (evenDyadic I)) = _
  rw [ContinuousLinearMap.map_smul_of_tower, (haarCoefficient_haar (𝕂 := 𝕂))]
  by_cases h : J = I
  · subst J
    rw [if_pos rfl, lp.single_apply_self]
    simp only [RCLike.real_smul_eq_coe_mul]
    have hp := dyadicMeasure_pos (evenDyadic I)
    have hs := (Real.sqrt_pos.mpr hp).ne'
    norm_cast
    field_simp
    exact (Real.sq_sqrt hp.le).symm
  · rw [if_neg (fun he => h (evenDyadic_injective he)), lp.single_apply_ne 2 I _ h]
    simp

theorem coefficientOperator_normalized_norm_sq (I : EvenDyadicIndex) :
    ‖(coefficientOperator (𝕂 := 𝕂)) ((normalizedEvenHaar (𝕂 := 𝕂)) I)‖^2 = dyadicMeasure (evenDyadic I) := by
  rw [(coefficientOperator_normalizedEvenHaar (𝕂 := 𝕂)), lp.norm_single (by norm_num)]
  simp [abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (dyadicMeasure_pos _).le]

def normalizedEvenHaarL2 (I : EvenDyadicIndex) : (L2 (𝕂 := 𝕂)) :=
  (Real.sqrt (dyadicMeasure (evenDyadic I)))⁻¹ • (haarL2 (𝕂 := 𝕂)) (evenDyadic I)

theorem haarL2_inner (I J : DyadicIndex) :
    inner 𝕂 ((haarL2 (𝕂 := 𝕂)) I) ((haarL2 (𝕂 := 𝕂)) J) = if I = J then (dyadicMeasure I : 𝕂) else 0 := by
  by_cases h : I = J
  · subst J
    rw [if_pos rfl, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, (haarL2_norm_sq (𝕂 := 𝕂))]
  · rw [if_neg h, MeasureTheory.L2.inner_def]
    have he : (∫ x, inner 𝕂 ((haarL2 (𝕂 := 𝕂)) I x) ((haarL2 (𝕂 := 𝕂)) J x) ∂unitIntervalMeasure) =
        ∫ x, (haarFunction 𝕂) I x * (haarFunction 𝕂) J x ∂unitIntervalMeasure := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [(haarL2_ae (𝕂 := 𝕂)) I, (haarL2_ae (𝕂 := 𝕂)) J] with x hi hj
      simp [hi, hj, RCLike.inner_apply, ← RCLike.star_def, mul_comm]
    exact he.trans ((haar_cross_integral (𝕂 := 𝕂)) I J h)

theorem normalizedEvenHaarL2_orthonormal : Orthonormal 𝕂 (normalizedEvenHaarL2 (𝕂 := 𝕂)) := by
  classical
  rw [orthonormal_iff_ite]
  intro I J
  rw [normalizedEvenHaarL2, normalizedEvenHaarL2,
    inner_smul_left_eq_smul, inner_smul_right_eq_smul, (haarL2_inner (𝕂 := 𝕂))]
  by_cases h : I = J
  · subst J
    rw [if_pos rfl, if_pos rfl]
    have hp := dyadicMeasure_pos (evenDyadic I)
    have hs := (Real.sqrt_pos.mpr hp).ne'
    simp only [RCLike.real_smul_eq_coe_mul]
    norm_cast
    field_simp
    nlinarith [Real.sq_sqrt hp.le]
  · rw [if_neg (fun he => h (evenDyadic_injective he)), if_neg h]
    simp

theorem l2ToL1_normalizedEvenHaar (I : EvenDyadicIndex) :
    (l2ToL1 (𝕂 := 𝕂)) ((normalizedEvenHaarL2 (𝕂 := 𝕂)) I) = ((normalizedEvenHaar (𝕂 := 𝕂)) I : (L1 𝕂)) := by
  rw [normalizedEvenHaarL2, ContinuousLinearMap.map_smul_of_tower]
  rfl

theorem normalizedEvenHaar_weak_bound (F : Finset EvenDyadicIndex)
    (φ : (X₀ 𝕂) →L[𝕂] 𝕂) (hφ : ‖φ‖ ≤ 1) :
    ∑ I ∈ F, ‖φ ((normalizedEvenHaar (𝕂 := 𝕂)) I)‖^2 ≤ 1 := by
  obtain ⟨Φ,hext,hnorm⟩ := exists_extension_norm_eq (X₀ 𝕂) φ
  let g := (dualL2Representative (𝕂 := 𝕂)) Φ
  have hg : ‖g‖ ≤ 1 := ((dualL2Representative_norm (𝕂 := 𝕂)) Φ).trans (hnorm.trans_le hφ)
  have hpair (I : EvenDyadicIndex) : φ ((normalizedEvenHaar (𝕂 := 𝕂)) I) =
      inner 𝕂 g ((normalizedEvenHaarL2 (𝕂 := 𝕂)) I) := by
    have hh : inner 𝕂 g ((normalizedEvenHaarL2 (𝕂 := 𝕂)) I) =
        Φ ((l2ToL1 (𝕂 := 𝕂)) ((normalizedEvenHaarL2 (𝕂 := 𝕂)) I)) :=
      InnerProductSpace.toDual_symm_apply
    rw [(l2ToL1_normalizedEvenHaar (𝕂 := 𝕂)), hext] at hh
    exact hh.symm
  calc
    _ = ∑ I ∈ F, ‖inner 𝕂 ((normalizedEvenHaarL2 (𝕂 := 𝕂)) I) g‖^2 := by
      apply Finset.sum_congr rfl
      intro I _
      rw [hpair, norm_inner_symm]
    _ ≤ ‖g‖^2 := (normalizedEvenHaarL2_orthonormal (𝕂 := 𝕂)).sum_inner_products_le g
    _ ≤ 1 := by nlinarith [norm_nonneg g]

theorem test_level_image_sum (n : ℕ) :
    (∑ k : Fin (2^(2*n)), ‖(coefficientOperator (𝕂 := 𝕂)) ((normalizedEvenHaar (𝕂 := 𝕂)) ⟨n,k⟩)‖^2) = 1 := by
  simp only [(coefficientOperator_normalized_norm_sq (𝕂 := 𝕂)), evenDyadic, dyadicMeasure]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hp : (2 : ℝ)^(2*n) ≠ 0 := by positivity
  push_cast
  exact mul_inv_cancel₀ hp

theorem test_initial_levels_image_sum (N : ℕ) :
    (∑ n ∈ Finset.range (N+1), ∑ k : Fin (2^(2*n)),
      ‖(coefficientOperator (𝕂 := 𝕂)) ((normalizedEvenHaar (𝕂 := 𝕂)) ⟨n,k⟩)‖^2) = N+1 := by
  simp [(test_level_image_sum (𝕂 := 𝕂))]

/-- Arbitrarily large coefficient-image square sums with weak square sums at most one. -/
theorem coefficient_test_obstruction (C : ℝ) :
    ∃ F : Finset EvenDyadicIndex,
      C^2 < ∑ I ∈ F, ‖(coefficientOperator (𝕂 := 𝕂)) ((normalizedEvenHaar (𝕂 := 𝕂)) I)‖^2 ∧
      ∀ φ : (X₀ 𝕂) →L[𝕂] 𝕂, ‖φ‖ ≤ 1 → ∑ I ∈ F, ‖φ ((normalizedEvenHaar (𝕂 := 𝕂)) I)‖^2 ≤ 1 := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_gt (C^2)
  refine ⟨(Finset.range (N+1)).sigma (fun n => (Finset.univ : Finset (Fin (2^(2*n))))), ?_, ?_⟩
  · rw [Finset.sum_sigma]
    have he := (test_initial_levels_image_sum (𝕂 := 𝕂)) N
    rw [he]
    exact lt_trans hN (by norm_num)
  · intro φ hφ
    exact (normalizedEvenHaar_weak_bound (𝕂 := 𝕂)) _ φ hφ

theorem normalizedEvenHaar_finiteWeakTwo {q : ℕ} (e : Fin q → EvenDyadicIndex)
    (he : Function.Injective e) : (finiteWeakTwo (𝕂 := 𝕂)) (fun i => (normalizedEvenHaar (𝕂 := 𝕂)) (e i)) ≤ 1 := by
  classical
  apply ((finiteWeakTwo_le_iff (𝕂 := 𝕂)) _ _).mpr
  intro φ hφ
  have h := (normalizedEvenHaar_weak_bound (𝕂 := 𝕂)) (Finset.univ.image e) φ hφ
  have hs : (∑ i, ‖φ ((normalizedEvenHaar (𝕂 := 𝕂)) (e i))‖^2) ≤ 1 := by
    simpa only [Finset.sum_image (fun a _ b _ hab => he hab)] using h
  apply Real.sqrt_le_iff.mpr
  exact ⟨by norm_num, by simpa using hs⟩

theorem coefficientOperator_not_two_summing :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (x : Fin q → (X₀ 𝕂)),
      Real.sqrt (∑ i, ‖(coefficientOperator (𝕂 := 𝕂)) (x i)‖^2) ≤ C * (finiteWeakTwo (𝕂 := 𝕂)) x := by
  classical
  rintro ⟨C,hC,hA⟩
  obtain ⟨F,hlarge,_⟩ := (coefficient_test_obstruction (𝕂 := 𝕂)) C
  let e := (Fintype.equivFin F).symm
  let j : Fin (Fintype.card F) → EvenDyadicIndex := fun i => (e i).val
  have hj : Function.Injective j := Subtype.val_injective.comp e.injective
  have hweak := (normalizedEvenHaar_finiteWeakTwo (𝕂 := 𝕂)) j hj
  have hsum : (∑ i, ‖(coefficientOperator (𝕂 := 𝕂)) ((normalizedEvenHaar (𝕂 := 𝕂)) (j i))‖^2) =
      ∑ I ∈ F, ‖(coefficientOperator (𝕂 := 𝕂)) ((normalizedEvenHaar (𝕂 := 𝕂)) I)‖^2 := by
    calc
      _ = ∑ I : F, ‖(coefficientOperator (𝕂 := 𝕂)) ((normalizedEvenHaar (𝕂 := 𝕂)) I.val)‖^2 :=
        e.sum_comp _
      _ = _ := Finset.sum_coe_sort F (fun I : EvenDyadicIndex => ‖(coefficientOperator (𝕂 := 𝕂)) ((normalizedEvenHaar (𝕂 := 𝕂)) I)‖^2)
  have h := hA _ (fun i => (normalizedEvenHaar (𝕂 := 𝕂)) (j i))
  have hsqrt : Real.sqrt (∑ i, ‖(coefficientOperator (𝕂 := 𝕂)) ((normalizedEvenHaar (𝕂 := 𝕂)) (j i))‖^2) ≤ C :=
    h.trans (by nlinarith)
  have hnonneg : 0 ≤ ∑ i, ‖(coefficientOperator (𝕂 := 𝕂)) ((normalizedEvenHaar (𝕂 := 𝕂)) (j i))‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq := Real.sq_sqrt hnonneg
  rw [hsum] at hsqrt hsq
  have hp := Real.sqrt_nonneg (∑ I ∈ F, ‖(coefficientOperator (𝕂 := 𝕂)) ((normalizedEvenHaar (𝕂 := 𝕂)) I)‖^2)
  nlinarith

/-- The even closed Haar span is not isomorphic to the canonical scalar-valued L¹ space. -/
theorem even_not_isomorphic_L1 : ¬ Nonempty ((X₀ 𝕂) ≃L[𝕂] (L1 𝕂)) := by
  rintro ⟨V⟩
  apply (coefficientOperator_not_two_summing (𝕂 := 𝕂))
  refine ⟨(81/8) * ‖(coefficientOperator (𝕂 := 𝕂))‖ * ‖V.symm.toContinuousLinearMap‖ * ‖V.toContinuousLinearMap‖,
    by positivity, ?_⟩
  intro q x
  exact (finiteSummingTwo_transport (𝕂 := 𝕂)) V.symm (coefficientOperator (𝕂 := 𝕂)) x

end EvenOddHaarLevels
