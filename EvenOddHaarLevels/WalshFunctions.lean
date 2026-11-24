import EvenOddHaarLevels.DyadicAveraging
import EvenOddHaarLevels.WalshCube
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

def rademacherFunction (n : ℕ) : ℝ → 𝕂 :=
  fun x => ∑ k : Fin (2^n), (haarFunction 𝕂) ⟨n,k⟩ x

def walshFunction (A : Finset ℕ) : ℝ → 𝕂 :=
  fun x => ∏ n ∈ A, (rademacherFunction (𝕂 := 𝕂)) n x

theorem rademacherFunction_eq_haar (n : ℕ) (k : Fin (2^n))
    {x : ℝ} (hx : x ∈ dyadicInterval ⟨n,k⟩) :
    (rademacherFunction (𝕂 := 𝕂)) n x = (haarFunction 𝕂) ⟨n,k⟩ x := by
  apply Finset.sum_eq_single k
  · intro b _ hb
    exact (haarFunction_zero_off (𝕂 := 𝕂)) ⟨n,b⟩
      (Set.disjoint_left.mp (dyadic_level_disjoint n hb).symm hx)
  · simp

theorem rademacherFunction_abs_le_one (n : ℕ) (x : ℝ) :
    ‖(rademacherFunction (𝕂 := 𝕂)) n x‖ ≤ 1 := by
  by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
  · rw [← dyadic_partition n] at hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
    rw [(rademacherFunction_eq_haar (𝕂 := 𝕂)) n k hk]
    exact (haarFunction_abs_le_one (𝕂 := 𝕂)) _ _
  · have hz : (rademacherFunction (𝕂 := 𝕂)) n x = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      exact (haarFunction_zero_off (𝕂 := 𝕂)) _ (fun hk => hx (dyadicInterval_subset_unit _ hk))
    simp [hz]

theorem rademacherFunction_sq (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    (rademacherFunction (𝕂 := 𝕂)) n x ^ 2 = 1 := by
  rw [← dyadic_partition n] at hx
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
  rw [(rademacherFunction_eq_haar (𝕂 := 𝕂)) n k hk, (haarFunction_sq (𝕂 := 𝕂)), Set.indicator_of_mem hk]

theorem rademacherFunction_measurable (n : ℕ) : Measurable ((rademacherFunction (𝕂 := 𝕂)) n) := by
  exact Finset.measurable_sum _ (fun k _ => (haarFunction_measurable (𝕂 := 𝕂)) ⟨n,k⟩)

theorem walshFunction_measurable (A : Finset ℕ) : Measurable ((walshFunction (𝕂 := 𝕂)) A) := by
  exact Finset.measurable_prod _ (fun n _ => (rademacherFunction_measurable (𝕂 := 𝕂)) n)

theorem walshFunction_abs_le_one (A : Finset ℕ) (x : ℝ) : ‖(walshFunction (𝕂 := 𝕂)) A x‖ ≤ 1 := by
  simpa [walshFunction, norm_prod] using
    Finset.prod_le_one (fun n (_ : n ∈ A) => norm_nonneg ((rademacherFunction (𝕂 := 𝕂)) n x))
      (fun n (_ : n ∈ A) => (rademacherFunction_abs_le_one (𝕂 := 𝕂)) n x)

theorem walshFunction_memLp (A : Finset ℕ) (p : ℝ≥0∞) :
    MemLp ((walshFunction (𝕂 := 𝕂)) A) p unitIntervalMeasure :=
  MemLp.of_bound ((walshFunction_measurable (𝕂 := 𝕂)) A).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using (walshFunction_abs_le_one (𝕂 := 𝕂)) A x)

def walshL1 (A : Finset ℕ) : (L1 𝕂) := ((walshFunction_memLp (𝕂 := 𝕂)) A 1).toLp ((walshFunction (𝕂 := 𝕂)) A)

theorem walshL1_ae (A : Finset ℕ) :
    ((walshL1 (𝕂 := 𝕂)) A : ℝ → 𝕂) =ᵐ[unitIntervalMeasure] (walshFunction (𝕂 := 𝕂)) A :=
  ((walshFunction_memLp (𝕂 := 𝕂)) A 1).coeFn_toLp

@[simp] theorem walshFunction_empty : (walshFunction (𝕂 := 𝕂)) ∅ = fun _ => 1 := by funext x; simp [walshFunction]
@[simp] theorem walshFunction_singleton (n : ℕ) :
    (walshFunction (𝕂 := 𝕂)) {n} = (rademacherFunction (𝕂 := 𝕂)) n := by funext x; simp [walshFunction]

theorem walshFunction_insert {n : ℕ} {A : Finset ℕ} (hn : n ∉ A) :
    (walshFunction (𝕂 := 𝕂)) (insert n A) = fun x => (rademacherFunction (𝕂 := 𝕂)) n x * (walshFunction (𝕂 := 𝕂)) A x := by
  funext x
  simp [walshFunction, hn]

theorem walshFunction_sq (A : Finset ℕ) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    (walshFunction (𝕂 := 𝕂)) A x ^ 2 = 1 := by
  simp only [walshFunction, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun n _ => (rademacherFunction_sq (𝕂 := 𝕂)) n hx

theorem rademacher_constant_on_deeper (n : ℕ) (J : DyadicIndex) (h : n < J.1) :
    ∃ c : 𝕂, ∀ x ∈ dyadicInterval J, (rademacherFunction (𝕂 := 𝕂)) n x = c := by
  choose c hc using fun k : Fin (2^n) => (haar_constant_on_deeper (𝕂 := 𝕂)) ⟨n,k⟩ J h
  refine ⟨∑ k, c k, fun x hx => ?_⟩
  exact Finset.sum_congr rfl fun k _ => hc k x hx

theorem walsh_constant_on_deeper (A : Finset ℕ) (J : DyadicIndex)
    (h : ∀ n ∈ A, n < J.1) :
    ∃ c : 𝕂, ∀ x ∈ dyadicInterval J, (walshFunction (𝕂 := 𝕂)) A x = c := by
  induction A using Finset.induction_on with
  | empty => exact ⟨1, fun _ _ => rfl⟩
  | @insert n A hn ih =>
    obtain ⟨c,hc⟩ := (rademacher_constant_on_deeper (𝕂 := 𝕂)) n J (h n (Finset.mem_insert_self _ _))
    obtain ⟨d,hd⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨c*d, fun x hx => ?_⟩
    simp only [(walshFunction_insert (𝕂 := 𝕂)) hn, hc x hx, hd x hx]

theorem rademacher_integral (n : ℕ) :
    ∫ x, (rademacherFunction (𝕂 := 𝕂)) n x ∂unitIntervalMeasure = 0 := by
  change (∫ x, ∑ k : Fin (2^n), (haarFunction 𝕂) ⟨n,k⟩ x ∂unitIntervalMeasure) = 0
  rw [integral_finsetSum]
  · simp [(haar_integral (𝕂 := 𝕂))]
  · intro k _
    exact haarFunction_integrable 𝕂 _


/-- A Walsh monomial with largest coordinate `n` is a level-`n` Haar polynomial. -/
theorem walshFunction_insert_expansion (n : ℕ) (A : Finset ℕ)
    (h : ∀ i ∈ A, i < n) :
    ∃ c : Fin (2^n) → 𝕂, ∀ x,
      (walshFunction (𝕂 := 𝕂)) (insert n A) x = ∑ k, c k * (haarFunction 𝕂) ⟨n,k⟩ x := by
  choose c hc using fun k : Fin (2^n) => (walsh_constant_on_deeper (𝕂 := 𝕂)) A ⟨n,k⟩ h
  refine ⟨c, fun x => ?_⟩
  have hn : n ∉ A := fun hn => (lt_irrefl n) (h n hn)
  rw [(walshFunction_insert (𝕂 := 𝕂)) hn]
  change (rademacherFunction (𝕂 := 𝕂)) n x * (walshFunction (𝕂 := 𝕂)) A x = _
  by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
  · rw [← dyadic_partition n] at hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
    rw [(rademacherFunction_eq_haar (𝕂 := 𝕂)) n k hk, hc k x hk,
      Finset.sum_eq_single k]
    · exact mul_comm _ _
    · intro b _ hb
      rw [(haarFunction_zero_off (𝕂 := 𝕂)) ⟨n,b⟩
        (Set.disjoint_left.mp (dyadic_level_disjoint n hb).symm hk), mul_zero]
    · simp
  · have hz (k : Fin (2^n)) : (haarFunction 𝕂) ⟨n,k⟩ x = 0 :=
      (haarFunction_zero_off (𝕂 := 𝕂)) _ (fun hk => hx (dyadicInterval_subset_unit _ hk))
    simp [rademacherFunction, hz]


theorem walsh_integral_insert (n : ℕ) (A : Finset ℕ) (h : ∀ i ∈ A, i < n) :
    ∫ x, (walshFunction (𝕂 := 𝕂)) (insert n A) x ∂unitIntervalMeasure = 0 := by
  obtain ⟨c,hc⟩ := (walshFunction_insert_expansion (𝕂 := 𝕂)) n A h
  simp_rw [hc]
  rw [integral_finsetSum]
  · simp [integral_const_mul, (haar_integral (𝕂 := 𝕂))]
  · intro k _
    exact (haarFunction_integrable 𝕂 _).const_mul _

theorem walsh_integral_nonempty (A : Finset ℕ) (hA : A.Nonempty) :
    ∫ x, (walshFunction (𝕂 := 𝕂)) A x ∂unitIntervalMeasure = 0 := by
  let n := A.max' hA
  have hn : n ∈ A := Finset.max'_mem A hA
  have h : ∀ i ∈ A.erase n, i < n := by
    intro i hi
    have hi' := Finset.mem_erase.mp hi
    exact lt_of_le_of_ne (Finset.le_max' A i hi'.2) hi'.1
  have hh := (walsh_integral_insert (𝕂 := 𝕂)) n (A.erase n) h
  simpa [Finset.insert_erase hn] using hh


theorem walshFunction_mul (A B : Finset ℕ) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    (walshFunction (𝕂 := 𝕂)) A x * (walshFunction (𝕂 := 𝕂)) B x = (walshFunction (𝕂 := 𝕂)) (symmDiff A B) x := by
  have hu : A ∪ B = (symmDiff A B) ∪ (A ∩ B) := by ext i; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_symmDiff]; tauto
  have hd : Disjoint (symmDiff A B) (A ∩ B) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [Finset.mem_symmDiff, Finset.mem_inter] at hi hj
    aesop
  have hh := Finset.prod_union_inter (s₁ := A) (s₂ := B)
    (f := fun n => (rademacherFunction (𝕂 := 𝕂)) n x)
  rw [hu, Finset.prod_union hd] at hh
  change _ = (walshFunction (𝕂 := 𝕂)) A x * (walshFunction (𝕂 := 𝕂)) B x at hh
  calc
    _ = (walshFunction (𝕂 := 𝕂)) (symmDiff A B) x * ((walshFunction (𝕂 := 𝕂)) (A ∩ B) x)^2 := by
      simpa only [walshFunction, pow_two, mul_assoc] using hh.symm
    _ = _ := by rw [(walshFunction_sq (𝕂 := 𝕂)) _ hx, mul_one]

theorem walsh_orthogonality (A B : Finset ℕ) :
    ∫ x, (walshFunction (𝕂 := 𝕂)) A x * (walshFunction (𝕂 := 𝕂)) B x ∂unitIntervalMeasure =
      if A = B then 1 else 0 := by
  have he : (fun x => (walshFunction (𝕂 := 𝕂)) A x * (walshFunction (𝕂 := 𝕂)) B x) =ᵐ[unitIntervalMeasure]
      (walshFunction (𝕂 := 𝕂)) (symmDiff A B) := by
    filter_upwards [show ∀ᵐ x ∂unitIntervalMeasure, x ∈ Set.Ico (0 : ℝ) 1 from
      ae_restrict_mem measurableSet_Ico] with x hx
    exact (walshFunction_mul (𝕂 := 𝕂)) A B hx
  rw [integral_congr_ae he]
  by_cases h : A = B
  · subst B
    simp [walshFunction]
  · rw [if_neg h]
    exact (walsh_integral_nonempty (𝕂 := 𝕂)) _ (Finset.symmDiff_nonempty.mpr h)


def walshCoefficient (A : Finset ℕ) : (L1 𝕂) →L[𝕂] 𝕂 :=
  (boundedPairing (𝕂 := 𝕂)) ((walshFunction (𝕂 := 𝕂)) A) 1 ((walshFunction_measurable (𝕂 := 𝕂)) A).aestronglyMeasurable
    (.of_forall fun x => by simpa only [Real.norm_eq_abs] using (walshFunction_abs_le_one (𝕂 := 𝕂)) A x)

theorem walshCoefficient_walsh (A B : Finset ℕ) :
    (walshCoefficient (𝕂 := 𝕂)) A ((walshL1 (𝕂 := 𝕂)) B) = if A = B then 1 else 0 := by
  rw [walshCoefficient, (boundedPairing_apply (𝕂 := 𝕂))]
  calc
    _ = ∫ x, (walshFunction (𝕂 := 𝕂)) B x * (walshFunction (𝕂 := 𝕂)) A x ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [(walshL1_ae (𝕂 := 𝕂)) B] with x hx
      rw [hx]
    _ = _ := by simpa [eq_comm] using (walsh_orthogonality (𝕂 := 𝕂)) B A

def walshPolynomial (c : (Finset ℕ) →₀ 𝕂) : (L1 𝕂) :=
  c.sum (fun A a => a • (walshL1 (𝕂 := 𝕂)) A)

theorem walshCoefficient_polynomial (A : Finset ℕ) (c : (Finset ℕ) →₀ 𝕂) :
    (walshCoefficient (𝕂 := 𝕂)) A ((walshPolynomial (𝕂 := 𝕂)) c) = c A := by
  classical
  simp only [walshPolynomial, Finsupp.sum, map_sum, map_smul, smul_eq_mul,
    (walshCoefficient_walsh (𝕂 := 𝕂))]
  simp only [mul_ite, mul_one, mul_zero]
  simp_rw [eq_comm (a := A)]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

theorem walshPolynomial_injective : Function.Injective (walshPolynomial (𝕂 := 𝕂)) := by
  intro c d h
  ext A
  rw [← (walshCoefficient_polynomial (𝕂 := 𝕂)) A c, h, (walshCoefficient_polynomial (𝕂 := 𝕂))]


theorem integral_rademacher_product_one_add (F : Finset ℕ) (a : ℕ → 𝕂) :
    ∫ x, ∏ n ∈ F, (1 + a n * (rademacherFunction (𝕂 := 𝕂)) n x) ∂unitIntervalMeasure = 1 := by
  have he (x : ℝ) : (∏ n ∈ F, (1 + a n * (rademacherFunction (𝕂 := 𝕂)) n x)) =
      ∑ A ∈ F.powerset, (∏ n ∈ A, a n) * (walshFunction (𝕂 := 𝕂)) A x := by
    rw [Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro A _
    exact Finset.prod_mul_distrib
  simp_rw [he]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    have hz (A : Finset ℕ) :
        (∏ n ∈ A, a n) * (∫ x, (walshFunction (𝕂 := 𝕂)) A x ∂unitIntervalMeasure) =
          if A = ∅ then 1 else 0 := by
      by_cases h : A = ∅
      · subst A; simp [walshFunction]
      · rw [if_neg h, (walsh_integral_nonempty (𝕂 := 𝕂)) A (Finset.nonempty_iff_ne_empty.mpr h), mul_zero]
    simp_rw [hz]
    simp
  · intro A _
    exact (memLp_one_iff_integrable.mp ((walshFunction_memLp (𝕂 := 𝕂)) A 1)).const_mul _


def rademacherCylinder (F : Finset ℕ) (ε : ℕ → Bool) : Set ℝ :=
  {x | ∀ n ∈ F, (rademacherFunction (𝕂 := 𝕂)) n x = if ε n then -1 else 1}

theorem rademacherCylinder_measurable (F : Finset ℕ) (ε : ℕ → Bool) :
    MeasurableSet ((rademacherCylinder (𝕂 := 𝕂)) F ε) := by
  have he : (rademacherCylinder (𝕂 := 𝕂)) F ε = ⋂ n ∈ F, {x | (rademacherFunction (𝕂 := 𝕂)) n x = if ε n then -1 else 1} := by ext x; simp [rademacherCylinder]
  rw [he]
  apply Finset.measurableSet_biInter
  intro n _
  exact measurableSet_eq_fun ((rademacherFunction_measurable (𝕂 := 𝕂)) n) measurable_const

theorem rademacher_sign_indicator (n : ℕ) (b : Bool) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    (1 + (if b then -1 else 1) * (rademacherFunction (𝕂 := 𝕂)) n x) / 2 =
      if (rademacherFunction (𝕂 := 𝕂)) n x = (if b then -1 else 1) then 1 else 0 := by
  have hs := (rademacherFunction_sq (𝕂 := 𝕂)) n hx
  have hr : (rademacherFunction (𝕂 := 𝕂)) n x = 1 ∨ (rademacherFunction (𝕂 := 𝕂)) n x = -1 := by
    have : ((rademacherFunction (𝕂 := 𝕂)) n x - 1) * ((rademacherFunction (𝕂 := 𝕂)) n x + 1) = 0 := by linear_combination hs
    rcases mul_eq_zero.mp this with h | h
    · left; exact sub_eq_zero.mp h
    · right; exact eq_neg_of_add_eq_zero_left h
  rcases hr with h | h <;> cases b <;> norm_num [h]

theorem rademacherCylinder_indicator (F : Finset ℕ) (ε : ℕ → Bool) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    ((rademacherCylinder (𝕂 := 𝕂)) F ε).indicator (fun _ => (1 : 𝕂)) x =
      (2 : 𝕂)⁻¹ ^ F.card * ∏ n ∈ F, (1 + (if ε n then -1 else 1) * (rademacherFunction (𝕂 := 𝕂)) n x) := by
  classical
  have hp : ∏ n ∈ F, ((1 + (if ε n then -1 else 1) * (rademacherFunction (𝕂 := 𝕂)) n x) / 2) =
      if x ∈ (rademacherCylinder (𝕂 := 𝕂)) F ε then 1 else 0 := by
    simp_rw [(rademacher_sign_indicator (𝕂 := 𝕂)) _ _ hx]
    induction F using Finset.induction_on with
    | empty => simp [rademacherCylinder]
    | @insert n F hn ih =>
      rw [Finset.prod_insert hn, ih]
      have hm : x ∈ (rademacherCylinder (𝕂 := 𝕂)) (insert n F) ε ↔
          ((rademacherFunction (𝕂 := 𝕂)) n x = (if ε n then -1 else 1) ∧ x ∈ (rademacherCylinder (𝕂 := 𝕂)) F ε) := by
        simp only [rademacherCylinder, Set.mem_ofPred_eq, Finset.mem_insert, forall_eq_or_imp]
      simp only [hm]
      by_cases h : (rademacherFunction (𝕂 := 𝕂)) n x = (if ε n then -1 else 1) <;>
        by_cases hF : x ∈ (rademacherCylinder (𝕂 := 𝕂)) F ε <;> simp only [h, hF, if_true, if_false,
          mul_one, mul_zero, and_false, and_true]

  change (if x ∈ (rademacherCylinder (𝕂 := 𝕂)) F ε then 1 else 0) = _
  rw [← hp]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, div_eq_mul_inv, inv_pow]
  ring


/-- Every finite family of distinct coordinates has the uniform sign distribution. -/
theorem rademacherCylinder_measure (F : Finset ℕ) (ε : ℕ → Bool) :
    unitIntervalMeasure.real ((rademacherCylinder (𝕂 := 𝕂)) F ε) = (2 : ℝ)⁻¹ ^ F.card := by
  have he : ((rademacherCylinder (𝕂 := 𝕂)) F ε).indicator (fun _ => (1 : 𝕂)) =ᵐ[unitIntervalMeasure]
      (fun x => (2 : 𝕂)⁻¹ ^ F.card * ∏ n ∈ F,
        (1 + (if ε n then -1 else 1) * (rademacherFunction (𝕂 := 𝕂)) n x)) := by
    filter_upwards [show ∀ᵐ x ∂unitIntervalMeasure, x ∈ Set.Ico (0 : ℝ) 1 from
      ae_restrict_mem measurableSet_Ico] with x hx
    exact (rademacherCylinder_indicator (𝕂 := 𝕂)) F ε hx
  have hi := integral_congr_ae he
  rw [integral_indicator_const (1 : 𝕂) ((rademacherCylinder_measurable (𝕂 := 𝕂)) F ε),
    integral_const_mul, (integral_rademacher_product_one_add (𝕂 := 𝕂)), mul_one] at hi
  apply RCLike.ofReal_injective (K := 𝕂)
  simpa [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_pow, RCLike.ofReal_inv, RCLike.ofReal_ofNat] using hi


def rademacherBits (x : ℝ) (n : ℕ) : Bool := decide ((rademacherFunction (𝕂 := 𝕂)) n x = -1)

theorem rademacherBits_sign (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    (walshSign (𝕂 := 𝕂)) ((rademacherBits (𝕂 := 𝕂)) x n) = (rademacherFunction (𝕂 := 𝕂)) n x := by
  have hs := (rademacherFunction_sq (𝕂 := 𝕂)) n hx
  by_cases h : (rademacherFunction (𝕂 := 𝕂)) n x = -1
  · simp [rademacherBits, walshSign, h]
  · have hz : ((rademacherFunction (𝕂 := 𝕂)) n x - 1) * ((rademacherFunction (𝕂 := 𝕂)) n x + 1) = 0 := by linear_combination hs
    have h' : (rademacherFunction (𝕂 := 𝕂)) n x = 1 := by
      rcases mul_eq_zero.mp hz with hh | hh
      · exact sub_eq_zero.mp hh
      · exact False.elim (h (eq_neg_of_add_eq_zero_left hh))
    norm_num [rademacherBits, walshSign, h']

theorem rademacherCylinder_bits (F : Finset ℕ) (ε : F → Bool) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    x ∈ (rademacherCylinder (𝕂 := 𝕂)) F (walshCubeExtend F ε) ↔
      (fun n : F => (rademacherBits (𝕂 := 𝕂)) x n) = ε := by
  constructor
  · intro h
    funext n
    have hn := h n n.property
    have hs := (rademacherBits_sign (𝕂 := 𝕂)) n.val hx
    simp only [walshCubeExtend, dif_pos n.property] at hn
    have he : (walshSign (𝕂 := 𝕂)) ((rademacherBits (𝕂 := 𝕂)) x n) = (walshSign (𝕂 := 𝕂)) (ε n) := hs.trans hn
    cases hb : (rademacherBits (𝕂 := 𝕂)) x n <;> cases heps : ε n <;>
      (try rfl) <;> norm_num [hb, heps, walshSign] at he
  · intro h n hn
    have he := congrFun h ⟨n,hn⟩
    change (rademacherFunction (𝕂 := 𝕂)) n x = (walshSign (𝕂 := 𝕂)) (walshCubeExtend F ε n)
    rw [walshCubeExtend, dif_pos hn, ← he, (rademacherBits_sign (𝕂 := 𝕂)) n hx]

theorem integral_rademacher_cube (F : Finset ℕ) (Q : (F → Bool) → ℝ) :
    (∫ x, Q (fun n : F => (rademacherBits (𝕂 := 𝕂)) x n) ∂unitIntervalMeasure) = cubeMean Q := by
  classical
  have he : (fun x => Q (fun n : F => (rademacherBits (𝕂 := 𝕂)) x n)) =ᵐ[unitIntervalMeasure]
      (fun x => ∑ ε : F → Bool,
        ((rademacherCylinder (𝕂 := 𝕂)) F (walshCubeExtend F ε)).indicator (fun _ => Q ε) x) := by
    filter_upwards [show ∀ᵐ x ∂unitIntervalMeasure, x ∈ Set.Ico (0 : ℝ) 1 from
      ae_restrict_mem measurableSet_Ico] with x hx
    rw [Finset.sum_eq_single (fun n : F => (rademacherBits (𝕂 := 𝕂)) x n)]
    · rw [Set.indicator_of_mem (((rademacherCylinder_bits (𝕂 := 𝕂)) F _ hx).mpr rfl)]
    · intro ε _ hε
      rw [Set.indicator_of_notMem]
      exact fun h => hε (((rademacherCylinder_bits (𝕂 := 𝕂)) F ε hx).mp h).symm
    · simp
  rw [integral_congr_ae he, integral_finsetSum]
  · simp_rw [integral_indicator_const _ ((rademacherCylinder_measurable (𝕂 := 𝕂)) _ _),
      (rademacherCylinder_measure (𝕂 := 𝕂)), smul_eq_mul]
    rw [← Finset.mul_sum]
    simp [cubeMean, Fintype.expect_eq_sum_div_card,
      div_eq_mul_inv, inv_pow, mul_comm]
  · intro ε _
    exact (integrable_const _).indicator ((rademacherCylinder_measurable (𝕂 := 𝕂)) _ _)


theorem walshPolynomial_ae (c : (Finset ℕ) →₀ 𝕂) :
    ((walshPolynomial (𝕂 := 𝕂)) c : ℝ → 𝕂) =ᵐ[unitIntervalMeasure]
      (fun x => c.sum (fun A a => a * (walshFunction (𝕂 := 𝕂)) A x)) := by
  have hs := Lp.coeFn_finsetSum c.support (fun A => c A • (walshL1 (𝕂 := 𝕂)) A)
  have hm := ae_all_iff.mpr (fun A : Finset ℕ => Lp.coeFn_smul (c A) ((walshL1 (𝕂 := 𝕂)) A))
  have hw := ae_all_iff.mpr (fun A : Finset ℕ => (walshL1_ae (𝕂 := 𝕂)) A)
  filter_upwards [hs, hm, hw] with x hx hm hw
  change (∑ A ∈ c.support, c A • (walshL1 (𝕂 := 𝕂)) A) x = _ at hx ⊢
  rw [hx]
  simp only [Finset.sum_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro A _
  simpa [hw A] using hm A

theorem walshCubeEval_bits (c : (Finset ℕ) →₀ 𝕂) (F : Finset ℕ)
    (hc : ∀ A ∈ c.support, A ⊆ F) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    (walshCubeEval (𝕂 := 𝕂)) c (walshCubeExtend F (fun n : F => (rademacherBits (𝕂 := 𝕂)) x n)) =
      c.sum (fun A a => a * (walshFunction (𝕂 := 𝕂)) A x) := by
  apply Finset.sum_congr rfl
  intro A hA
  change c A * _ = c A * _
  congr 1
  apply Finset.prod_congr rfl
  intro n hn
  rw [walshCubeExtend, dif_pos (hc A hA hn)]
  exact (rademacherBits_sign (𝕂 := 𝕂)) n hx

/-- The finite-coordinate norm identity used by substitution and coordinate averaging. -/
theorem walshPolynomial_norm_cube (c : (Finset ℕ) →₀ 𝕂) (F : Finset ℕ)
    (hc : ∀ A ∈ c.support, A ⊆ F) :
    ‖(walshPolynomial (𝕂 := 𝕂)) c‖ =
      cubeMean (fun ε : F → Bool => ‖(walshCubeEval (𝕂 := 𝕂)) c (walshCubeExtend F ε)‖) := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ x, ‖(walshCubeEval (𝕂 := 𝕂)) c (walshCubeExtend F (fun n : F => (rademacherBits (𝕂 := 𝕂)) x n))‖
        ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [(walshPolynomial_ae (𝕂 := 𝕂)) c,
        show ∀ᵐ x ∂unitIntervalMeasure, x ∈ Set.Ico (0 : ℝ) 1 from
          ae_restrict_mem measurableSet_Ico] with x hp hx
      rw [hp, (walshCubeEval_bits (𝕂 := 𝕂)) c F hc hx]
    _ = _ := (integral_rademacher_cube (𝕂 := 𝕂)) F (fun ε : F → Bool => ‖(walshCubeEval (𝕂 := 𝕂)) c (walshCubeExtend F ε)‖)


theorem walshL1_linearIndependent : LinearIndependent 𝕂 (walshL1 (𝕂 := 𝕂)) := by
  rw [linearIndependent_iff_injective_finsuppLinearCombination]
  exact (walshPolynomial_injective (𝕂 := 𝕂))

theorem walshL1_insert_mem_levelSpan (n : ℕ) (A : Finset ℕ)
    (h : ∀ i ∈ A, i < n) :
    (walshL1 (𝕂 := 𝕂)) (insert n A) ∈ Submodule.span 𝕂 (Set.range (fun k : Fin (2^n) => (haarL1 𝕂) ⟨n,k⟩)) := by
  obtain ⟨c,hc⟩ := (walshFunction_insert_expansion (𝕂 := 𝕂)) n A h
  have he : (walshL1 (𝕂 := 𝕂)) (insert n A) = ∑ k, c k • (haarL1 𝕂) ⟨n,k⟩ := by
    apply Lp.ext
    have hs := Lp.coeFn_finsetSum Finset.univ (fun k : Fin (2^n) => c k • (haarL1 𝕂) ⟨n,k⟩)
    have hm := ae_all_iff.mpr (fun k : Fin (2^n) => Lp.coeFn_smul (c k) ((haarL1 𝕂) ⟨n,k⟩))
    have hh := ae_all_iff.mpr (fun k : Fin (2^n) => (haarL1_ae (𝕂 := 𝕂)) ⟨n,k⟩)
    filter_upwards [(walshL1_ae (𝕂 := 𝕂)) (insert n A), hs, hm, hh] with x hw hs hm hh
    rw [hw, hs]
    simp only [Finset.sum_apply]
    rw [hc]
    apply Finset.sum_congr rfl
    intro k _
    simpa [hh k] using (hm k).symm
  rw [he]
  apply Submodule.sum_mem
  intro k _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,rfl⟩)

def levelWalshIndices (n : ℕ) := ↥((Finset.range n).powerset)
instance (n : ℕ) : Fintype (levelWalshIndices n) := inferInstanceAs (Fintype ↥((Finset.range n).powerset))

def levelWalshFamily (n : ℕ) (A : levelWalshIndices n) : (L1 𝕂) := (walshL1 (𝕂 := 𝕂)) (insert n A.val)

theorem levelWalshFamily_linearIndependent (n : ℕ) : LinearIndependent 𝕂 ((levelWalshFamily (𝕂 := 𝕂)) n) := by
  apply (walshL1_linearIndependent (𝕂 := 𝕂)).comp
  intro A B h
  apply Subtype.ext
  have ha : n ∉ A.val := by
    intro hn
    exact (Nat.lt_irrefl n) (Finset.mem_range.mp ((Finset.mem_powerset.mp A.property) hn))
  have hb : n ∉ B.val := by
    intro hn
    exact (Nat.lt_irrefl n) (Finset.mem_range.mp ((Finset.mem_powerset.mp B.property) hn))
  have he := congrArg (fun C : Finset ℕ => C.erase n) h
  simpa [ha,hb] using he

theorem levelWalsh_span_eq_haar (n : ℕ) :
    Submodule.span 𝕂 (Set.range ((levelWalshFamily (𝕂 := 𝕂)) n)) =
      Submodule.span 𝕂 (Set.range (fun k : Fin (2^n) => (haarL1 𝕂) ⟨n,k⟩)) := by
  classical
  have hle : Submodule.span 𝕂 (Set.range ((levelWalshFamily (𝕂 := 𝕂)) n)) ≤
      Submodule.span 𝕂 (Set.range (fun k : Fin (2^n) => (haarL1 𝕂) ⟨n,k⟩)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A,rfl⟩
    exact (walshL1_insert_mem_levelSpan (𝕂 := 𝕂)) n A.val
      (fun i hi => Finset.mem_range.mp ((Finset.mem_powerset.mp A.property) hi))
  have := FiniteDimensional.span_of_finite 𝕂 (Set.finite_range (fun k : Fin (2^n) => (haarL1 𝕂) ⟨n,k⟩))
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [finrank_span_eq_card ((levelWalshFamily_linearIndependent (𝕂 := 𝕂)) n)]
  calc
    Module.finrank 𝕂 (Submodule.span 𝕂 (Set.range (fun k : Fin (2^n) => (haarL1 𝕂) ⟨n,k⟩))) ≤
        Fintype.card (Fin (2^n)) := finrank_range_le_card _
    _ = Fintype.card (levelWalshIndices n) := by
      rw [Fintype.card_fin]
      change 2^n = Fintype.card ↥((Finset.range n).powerset)
      rw [Fintype.card_coe]
      simp


def walshLevelSpan (S : Set ℕ) : Submodule 𝕂 (L1 𝕂) :=
  (Submodule.span 𝕂 ((walshL1 (𝕂 := 𝕂)) '' {A | ∃ n ∈ S, n ∈ A ∧ ∀ k ∈ A, k ≤ n})).topologicalClosure

theorem walshLevelSpan_eq_haarClosedSpan (S : Set ℕ) :
    (walshLevelSpan (𝕂 := 𝕂)) S = (haarClosedSpan 𝕂) S := by
  have he : Submodule.span 𝕂 ((walshL1 (𝕂 := 𝕂)) '' {A | ∃ n ∈ S, n ∈ A ∧ ∀ k ∈ A, k ≤ n}) =
      Submodule.span 𝕂 ((haarL1 𝕂) '' {I : DyadicIndex | I.1 ∈ S}) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨A, ⟨n,hn,hnA,hmax⟩,rfl⟩
      have hA : (walshL1 (𝕂 := 𝕂)) A ∈ Submodule.span 𝕂 (Set.range (fun k : Fin (2^n) => (haarL1 𝕂) ⟨n,k⟩)) := by
        rw [← Finset.insert_erase hnA]
        apply (walshL1_insert_mem_levelSpan (𝕂 := 𝕂))
        intro i hi
        have hh := Finset.mem_erase.mp hi
        exact lt_of_le_of_ne (hmax i hh.2) hh.1
      apply Submodule.span_mono _ hA
      rintro _ ⟨k,rfl⟩
      exact ⟨⟨n,k⟩,hn,rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨n,k⟩,hn,rfl⟩
      have hh : (haarL1 𝕂) ⟨n,k⟩ ∈ Submodule.span 𝕂 (Set.range ((levelWalshFamily (𝕂 := 𝕂)) n)) := by
        rw [(levelWalsh_span_eq_haar (𝕂 := 𝕂))]
        exact Submodule.subset_span ⟨k,rfl⟩
      apply Submodule.span_mono _ hh
      rintro _ ⟨A,rfl⟩
      refine ⟨insert n A.val, ⟨n,hn,Finset.mem_insert_self _ _,?_⟩,rfl⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · rfl
      · exact (Finset.mem_range.mp ((Finset.mem_powerset.mp A.property) hi)).le
  exact congrArg Submodule.topologicalClosure he

@[simp] theorem walshL1_empty : (walshL1 (𝕂 := 𝕂)) ∅ = (constantL1 (𝕂 := 𝕂)) := by
  apply Lp.ext
  filter_upwards [(walshL1_ae (𝕂 := 𝕂)) ∅, (cellL1_ae (𝕂 := 𝕂)) ⟨0,0⟩,
    show ∀ᵐ x ∂unitIntervalMeasure, x ∈ Set.Ico (0 : ℝ) 1 from
      ae_restrict_mem measurableSet_Ico] with x hw hc hx
  change _ = (cellL1 (𝕂 := 𝕂)) ⟨0,0⟩ x
  rw [hw, hc]
  simp only [(walshFunction_empty (𝕂 := 𝕂))]
  have hmem : x ∈ dyadicInterval ⟨0,0⟩ := by simpa [dyadicInterval] using hx
  rw [Set.indicator_of_mem hmem]

theorem haarL1_mem_walshSpan (I : DyadicIndex) :
    (haarL1 𝕂) I ∈ Submodule.span 𝕂 (Set.range (walshL1 (𝕂 := 𝕂))) := by
  obtain ⟨n,k⟩ := I
  have hh : (haarL1 𝕂) ⟨n,k⟩ ∈ Submodule.span 𝕂 (Set.range ((levelWalshFamily (𝕂 := 𝕂)) n)) := by
    rw [(levelWalsh_span_eq_haar (𝕂 := 𝕂))]
    exact Submodule.subset_span ⟨k,rfl⟩
  apply Submodule.span_mono _ hh
  rintro _ ⟨A,rfl⟩
  exact ⟨insert n A.val,rfl⟩

theorem walshPolynomial_dense : DenseRange (walshPolynomial (𝕂 := 𝕂)) := by
  have hr : Set.range (walshPolynomial (𝕂 := 𝕂)) = (Submodule.span 𝕂 (Set.range (walshL1 (𝕂 := 𝕂))) : Set (L1 𝕂)) := by
    exact congrArg (fun U : Submodule 𝕂 (L1 𝕂) => (U : Set (L1 𝕂))) (Finsupp.range_linearCombination 𝕂 (v := (walshL1 (𝕂 := 𝕂))))
  intro f
  rw [hr]
  apply (Submodule.span 𝕂 (Set.range (walshL1 (𝕂 := 𝕂)))).isClosed_topologicalClosure.mem_of_tendsto
    ((dyadicAverage_tendsto (𝕂 := 𝕂)) f)
  apply Filter.Eventually.of_forall
  intro m
  apply Submodule.le_topologicalClosure
  rw [(dyadicAverage_finite_expansion (𝕂 := 𝕂))]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (by rw [← (walshL1_empty (𝕂 := 𝕂))]; exact Submodule.subset_span ⟨∅,rfl⟩)
  · apply Submodule.sum_mem
    intro n _
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ _ ((haarL1_mem_walshSpan (𝕂 := 𝕂)) _)


theorem walsh_dense_meanZero : (walshLevelSpan (𝕂 := 𝕂)) Set.univ = (H₀ (𝕂 := 𝕂)) := by
  rw [(walshLevelSpan_eq_haarClosedSpan (𝕂 := 𝕂)), (haar_dense_meanZero (𝕂 := 𝕂))]

theorem meanFunctional_walsh (A : Finset ℕ) :
    (meanFunctional (𝕂 := 𝕂)) ((walshL1 (𝕂 := 𝕂)) A) = if A = ∅ then 1 else 0 := by
  rw [(meanFunctional_apply (𝕂 := 𝕂)), integral_congr_ae ((walshL1_ae (𝕂 := 𝕂)) A)]
  by_cases h : A = ∅
  · subst A; simp [walshFunction]
  · rw [if_neg h]
    exact (walsh_integral_nonempty (𝕂 := 𝕂)) A (Finset.nonempty_iff_ne_empty.mpr h)

theorem walshCoefficient_empty_eq_mean : (walshCoefficient (𝕂 := 𝕂)) ∅ = (meanFunctional (𝕂 := 𝕂)) := by
  ext f
  rw [walshCoefficient, (boundedPairing_apply (𝕂 := 𝕂)), (meanFunctional_apply (𝕂 := 𝕂))]
  simp [walshFunction]

end EvenOddHaarLevels
