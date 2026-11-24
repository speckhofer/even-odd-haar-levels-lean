import Mathlib

/-! Gaussian probability space and elementary moment inputs for the truncation proof. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace EvenOddHaarLevels

abbrev stdNormal : Measure ℝ := gaussianReal 0 1

def gaussianProduct (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ => stdNormal)

instance (d : ℕ) : IsProbabilityMeasure (gaussianProduct d) := by
  unfold gaussianProduct
  infer_instance

def gaussianLinear {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (x : Fin d → ℝ) : ℝ :=
  ∑ r, a r * x r

theorem standardNormal_integrable_pow (k : ℕ) :
    Integrable (fun t : ℝ => t ^ k) stdNormal := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) (k : ℝ≥0∞) (by simp)).integrable_norm_pow'
  exact h.mono' (by fun_prop) (Filter.Eventually.of_forall fun t => by simp)

@[simp] theorem standardNormal_integral_pow_zero :
    ∫ t : ℝ, t ^ (0 : ℕ) ∂stdNormal = 1 := by simp

@[simp] theorem standardNormal_integral_id : ∫ t : ℝ, t ∂stdNormal = 0 := by
  exact integral_id_gaussianReal

@[simp] theorem standardNormal_integral_pow_two :
    ∫ t : ℝ, t ^ (2 : ℕ) ∂stdNormal = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable] at h
  simpa [stdNormal] using h

theorem gaussianProduct_integrable_monomial {d : ℕ} (e : Fin d → ℕ) :
    Integrable (fun x : Fin d → ℝ => ∏ r, (x r) ^ (e r)) (gaussianProduct d) := by
  exact Integrable.fintype_prod (fun r => standardNormal_integrable_pow (e r))

theorem gaussianProduct_integral_monomial {d : ℕ} (e : Fin d → ℕ) :
    (∫ x : Fin d → ℝ, ∏ r, (x r) ^ (e r) ∂gaussianProduct d) =
      ∏ r, ∫ t : ℝ, t ^ (e r) ∂stdNormal := by
  exact integral_fintype_prod_eq_prod (fun r t => t ^ (e r))

@[simp] theorem standardNormal_integral_pow_three :
    ∫ t : ℝ, t ^ (3 : ℕ) ∂stdNormal = 0 := by
  have hm : stdNormal.map (fun t : ℝ => -t) = stdNormal := by
    simpa [stdNormal] using (gaussianReal_map_neg (μ := 0) (v := 1))
  have h := integral_map (μ := stdNormal) (φ := fun t : ℝ => -t)
    (f := fun t : ℝ => t ^ (3 : ℕ)) (by fun_prop) (by fun_prop)
  rw [hm] at h
  have hf : (fun t : ℝ => (-t) ^ (3 : ℕ)) = fun t => -(t ^ (3 : ℕ)) := by
    funext t
    ring
  rw [hf, integral_neg] at h
  linarith

/-- Polynomial multiples of the density are integrable on the whole line. -/
theorem standardNormal_density_integrable_pow (k : ℕ) :
    Integrable (fun t : ℝ => t ^ k * gaussianPDFReal 0 1 t) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ))
    (by norm_num) (s := (k : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have he : (fun t : ℝ => t ^ k * gaussianPDFReal 0 1 t) =
      fun t : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        (t ^ (k : ℝ) * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) := by
    funext t
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Real.rpow_natCast]
    rw [show -t ^ 2 / (2) = -(1 / 2 : ℝ) * t ^ 2 by ring]
    ring
  rw [he]
  exact h.const_mul _

theorem standardNormal_density_hasDerivAt (t : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-t * gaussianPDFReal 0 1 t) t := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  convert! (((hasDerivAt_id t).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹ using 1; (try simp); (try ring)

/-- Whole-line integration by parts, with integrability discharging the boundary term. -/
theorem standardNormal_density_recurrence (k : ℕ) :
    (∫ t : ℝ, t ^ (k + 2) * gaussianPDFReal 0 1 t) =
      (k + 1 : ℝ) * ∫ t : ℝ, t ^ k * gaussianPDFReal 0 1 t := by
  have hleft : Integrable (fun t : ℝ => t ^ (k + 1) *
      (-t * gaussianPDFReal 0 1 t)) := by
    convert (standardNormal_density_integrable_pow (k + 2)).neg using 1
    funext t
    simp only [Pi.neg_apply]
    ring
  have hright : Integrable (fun t : ℝ =>
      ((k + 1 : ℝ) * t ^ k) * gaussianPDFReal 0 1 t) := by
    convert (standardNormal_density_integrable_pow k).const_mul (k + 1 : ℝ) using 1
    funext t
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t : ℝ => t ^ (k + 1)) (u' := fun t => (k + 1 : ℝ) * t ^ k)
    (v := gaussianPDFReal 0 1) (v' := fun t => -t * gaussianPDFReal 0 1 t)
    (fun t _ => by convert! (hasDerivAt_id t).pow (k + 1) using 1; (try simp))
    (fun t _ => standardNormal_density_hasDerivAt t)
    hleft hright (standardNormal_density_integrable_pow (k + 1))
  have he : (fun t : ℝ => t ^ (k + 1) * (-t * gaussianPDFReal 0 1 t)) =
      fun t => -(t ^ (k + 2) * gaussianPDFReal 0 1 t) := by
    funext t
    ring
  have he' : (fun t : ℝ => ((k + 1 : ℝ) * t ^ k) * gaussianPDFReal 0 1 t) =
      fun t => (k + 1 : ℝ) * (t ^ k * gaussianPDFReal 0 1 t) := by
    funext t
    ring
  rw [he, he', integral_neg, integral_const_mul] at h
  linarith

@[simp] theorem standardNormal_integral_pow_four :
    ∫ t : ℝ, t ^ (4 : ℕ) ∂stdNormal = 3 := by
  have h := standardNormal_density_recurrence 2
  have hconv (k : ℕ) : (∫ t : ℝ, t ^ k ∂stdNormal) =
      ∫ t : ℝ, t ^ k * gaussianPDFReal 0 1 t := by
    rw [stdNormal, integral_gaussianReal_eq_integral_smul (by norm_num)]
    congr 1
    funext t
    simp only [smul_eq_mul]
    ring
  rw [← hconv 4, ← hconv 2, standardNormal_integral_pow_two] at h
  norm_num at h ⊢
  exact h

theorem gaussianProduct_coordinate_integrable_pow {d : ℕ} (i : Fin d) (k : ℕ) :
    Integrable (fun x : Fin d → ℝ => (x i) ^ k) (gaussianProduct d) := by
  exact (measurePreserving_eval (fun _ : Fin d => stdNormal) i).integrable_comp_of_integrable
    (standardNormal_integrable_pow k)

theorem gaussianProduct_coordinate_memLp {d : ℕ} (i : Fin d) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x : Fin d → ℝ => x i) p (gaussianProduct d) := by
  exact (memLp_id_gaussianReal' (μ := 0) (v := 1) p hp).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin d => stdNormal) i)

theorem gaussianLinear_memLp {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp (gaussianLinear a) p (gaussianProduct d) := by
  exact memLp_finsetSum _ (fun r _ => (gaussianProduct_coordinate_memLp r p hp).const_mul (a r))

theorem gaussianProduct_coordinate_integral_pow {d : ℕ} (i : Fin d) (k : ℕ) :
    (∫ x : Fin d → ℝ, (x i) ^ k ∂gaussianProduct d) = ∫ t : ℝ, t ^ k ∂stdNormal := by
  have hm := (measurePreserving_eval (fun _ : Fin d => stdNormal) i).map_eq
  rw [← hm, integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]
  rfl

theorem gaussianProduct_iIndepFun (d : ℕ) :
    iIndepFun (fun i : Fin d => fun x : Fin d → ℝ => x i) (gaussianProduct d) := by
  exact iIndepFun_pi (X := fun _ : Fin d => fun t : ℝ => t) (fun _ => by fun_prop)

theorem gaussianProduct_coordinate_integral_mul {d : ℕ} (i j : Fin d) :
    (∫ x : Fin d → ℝ, x i * x j ∂gaussianProduct d) = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst j
    simpa only [pow_two] using
      (gaussianProduct_coordinate_integral_pow i 2).trans standardNormal_integral_pow_two
  · have h := ((gaussianProduct_iIndepFun d).indepFun hij).integral_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable
    have hi : (∫ x : Fin d → ℝ, x i ∂gaussianProduct d) = 0 := by
      simpa using (gaussianProduct_coordinate_integral_pow i 1)
    have hj : (∫ x : Fin d → ℝ, x j ∂gaussianProduct d) = 0 := by
      simpa using (gaussianProduct_coordinate_integral_pow j 1)
    simpa [hi, hj] using h

theorem gaussianLinear_integral_mul {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) :
    (∫ x, gaussianLinear a x * gaussianLinear b x ∂gaussianProduct d) = inner ℝ a b := by
  have hint (i j : Fin d) : Integrable (fun x : Fin d → ℝ =>
      (a i * b j) * (x i * x j)) (gaussianProduct d) :=
    ((gaussianProduct_coordinate_memLp i 2 (by norm_num)).integrable_mul
      (gaussianProduct_coordinate_memLp j 2 (by norm_num))).const_mul _
  have he : (fun x => gaussianLinear a x * gaussianLinear b x) =
      fun x => ∑ i, ∑ j, (a i * b j) * (x i * x j) := by
    funext x
    simp only [gaussianLinear, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j), integral_const_mul,
    gaussianProduct_coordinate_integral_mul]
  simp [PiLp.inner_apply, mul_comm]

/-- The concrete L² realization, with representatives specified by `coeFn_toLp`. -/
def gaussianL2 {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) : Lp ℝ 2 (gaussianProduct d) :=
  (gaussianLinear_memLp a 2 (by norm_num)).toLp (gaussianLinear a)

theorem gaussianL2_coeFn {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) :
    (gaussianL2 a : (Fin d → ℝ) → ℝ) =ᵐ[gaussianProduct d] gaussianLinear a :=
  (gaussianLinear_memLp a 2 (by norm_num)).coeFn_toLp

theorem gaussianL2_inner {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (gaussianL2 a) (gaussianL2 b) = inner ℝ a b := by
  rw [L2.inner_def]
  calc
    (∫ x, inner ℝ ((gaussianL2 a) x) ((gaussianL2 b) x) ∂gaussianProduct d) =
        ∫ x, gaussianLinear a x * gaussianLinear b x ∂gaussianProduct d := by
      apply integral_congr_ae
      filter_upwards [gaussianL2_coeFn a, gaussianL2_coeFn b] with x ha hb
      simp [ha, hb, mul_comm]
    _ = inner ℝ a b := gaussianLinear_integral_mul a b

theorem gaussianL2_norm {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) : ‖gaussianL2 a‖ = ‖a‖ := by
  have h := gaussianL2_inner a a
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (gaussianL2 a), norm_nonneg a]

theorem gaussianLinear_integrable_fourth {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun x => (gaussianLinear a x) ^ (4 : ℕ)) (gaussianProduct d) := by
  have h := (gaussianLinear_memLp a 4 (by norm_num)).integrable_norm_pow' (p := 4)
  exact h.mono' ((gaussianLinear_memLp a 4 (by norm_num)).aestronglyMeasurable.pow 4) (Filter.Eventually.of_forall fun x => by simp)

/-- Finite Gaussian realization as a genuine linear isometry into L². -/
def gaussianL2Isometry (d : ℕ) : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] Lp ℝ 2 (gaussianProduct d) where
  toFun := gaussianL2
  map_add' a b := by
    apply Lp.ext
    filter_upwards [gaussianL2_coeFn (a + b), gaussianL2_coeFn a, gaussianL2_coeFn b,
      Lp.coeFn_add (gaussianL2 a) (gaussianL2 b)] with x hab ha hb hs
    rw [hab, hs, Pi.add_apply, ha, hb]
    simp [gaussianLinear, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    apply Lp.ext
    filter_upwards [gaussianL2_coeFn (c • a), gaussianL2_coeFn a,
      Lp.coeFn_smul c (gaussianL2 a)] with x hca ha hs
    change (gaussianL2 (c • a)) x = (c • gaussianL2 a) x
    rw [hca, hs, Pi.smul_apply, ha]
    simp [gaussianLinear, Finset.mul_sum, mul_assoc]
  norm_map' := gaussianL2_norm

/-- Fubini factorization of powers of two independent real variables. -/
theorem indep_integral_pow_mul {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {X Y : Ω → ℝ} (hXY : IndepFun X Y ν)
    (hX : AEStronglyMeasurable X ν) (hY : AEStronglyMeasurable Y ν) (r s : ℕ) :
    (∫ ω, (X ω) ^ r * (Y ω) ^ s ∂ν) =
      (∫ ω, (X ω) ^ r ∂ν) * ∫ ω, (Y ω) ^ s ∂ν := by
  exact (hXY.comp (by fun_prop : Measurable (fun t : ℝ => t ^ r))
    (by fun_prop : Measurable (fun t : ℝ => t ^ s))).integral_mul_eq_mul_integral
      (hX.pow r) (hY.pow s)

/-- The binomial fourth-moment expansion, before using vanishing odd moments. -/
theorem indep_integral_add_pow_four {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {X Y : Ω → ℝ} (hXY : IndepFun X Y ν)
    (hX : ∀ k : ℕ, Integrable (fun ω => (X ω) ^ k) ν)
    (hY : ∀ k : ℕ, Integrable (fun ω => (Y ω) ^ k) ν) :
    (∫ ω, (X ω + Y ω) ^ (4 : ℕ) ∂ν) =
      (∫ ω, (X ω) ^ (4 : ℕ) ∂ν) +
      4 * ((∫ ω, (X ω) ^ (3 : ℕ) ∂ν) * ∫ ω, Y ω ∂ν) +
      6 * ((∫ ω, (X ω) ^ (2 : ℕ) ∂ν) * ∫ ω, (Y ω) ^ (2 : ℕ) ∂ν) +
      4 * ((∫ ω, X ω ∂ν) * ∫ ω, (Y ω) ^ (3 : ℕ) ∂ν) +
      ∫ ω, (Y ω) ^ (4 : ℕ) ∂ν := by
  have hp (r s : ℕ) : Integrable (fun ω => (X ω) ^ r * (Y ω) ^ s) ν :=
    (hXY.comp (by fun_prop : Measurable (fun t : ℝ => t ^ r))
      (by fun_prop : Measurable (fun t : ℝ => t ^ s))).integrable_mul (hX r) (hY s)
  have h31 := (hp 3 1).const_mul 4
  have h22 := (hp 2 2).const_mul 6
  have h13 := (hp 1 3).const_mul 4
  have he : (fun ω => (X ω + Y ω) ^ (4 : ℕ)) = fun ω =>
      (X ω) ^ (4 : ℕ) + 4 * ((X ω) ^ (3 : ℕ) * (Y ω) ^ (1 : ℕ)) +
      6 * ((X ω) ^ (2 : ℕ) * (Y ω) ^ (2 : ℕ)) +
      4 * ((X ω) ^ (1 : ℕ) * (Y ω) ^ (3 : ℕ)) + (Y ω) ^ (4 : ℕ) := by
    funext ω
    ring
  erw [he, integral_add (((hX 4).add h31).add h22 |>.add h13) (hY 4),
    integral_add (((hX 4).add h31).add h22) h13,
    integral_add ((hX 4).add h31) h22, integral_add (hX 4) h31]
  simp_rw [integral_const_mul,
    indep_integral_pow_mul hXY (by simpa using (hX 1).aestronglyMeasurable)
      (by simpa using (hY 1).aestronglyMeasurable)]
  simp

theorem indep_integral_add_pow_two {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {X Y : Ω → ℝ} (hXY : IndepFun X Y ν)
    (hX : ∀ k : ℕ, Integrable (fun ω => (X ω) ^ k) ν)
    (hY : ∀ k : ℕ, Integrable (fun ω => (Y ω) ^ k) ν) :
    (∫ ω, (X ω + Y ω) ^ (2 : ℕ) ∂ν) =
      (∫ ω, (X ω) ^ (2 : ℕ) ∂ν) +
      2 * ((∫ ω, X ω ∂ν) * ∫ ω, Y ω ∂ν) + ∫ ω, (Y ω) ^ (2 : ℕ) ∂ν := by
  have hXi : Integrable X ν := by simpa using hX 1
  have hYi : Integrable Y ν := by simpa using hY 1
  have hp := (hXY.integrable_mul hXi hYi).const_mul 2
  have he : (fun ω => (X ω + Y ω) ^ (2 : ℕ)) =
      fun ω => (X ω) ^ (2 : ℕ) + 2 * (X ω * Y ω) + (Y ω) ^ (2 : ℕ) := by
    funext ω
    ring
  erw [he, integral_add ((hX 2).add hp) (hY 2), integral_add (hX 2) hp,
    integral_const_mul]
  rw [hXY.integral_mul_eq_mul_integral hXi.aestronglyMeasurable hYi.aestronglyMeasurable]

theorem gaussianFinset_moments {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : Finset (Fin d)) :
    ((∫ x : Fin d → ℝ, (∑ i ∈ s, a i * x i) ^ (2 : ℕ) ∂gaussianProduct d) = ∑ i ∈ s, (a i) ^ 2) ∧
    ((∫ x : Fin d → ℝ, (∑ i ∈ s, a i * x i) ^ (4 : ℕ) ∂gaussianProduct d) =
      3 * (∑ i ∈ s, (a i) ^ 2) ^ 2) := by
  have hsingle (i : Fin d) (k : ℕ) :
      (∫ x : Fin d → ℝ, (a i * x i) ^ k ∂gaussianProduct d) =
        (a i) ^ k * ∫ t : ℝ, t ^ k ∂stdNormal := by
    simp_rw [mul_pow]
    rw [integral_const_mul, gaussianProduct_coordinate_integral_pow]
  have hsingle_mean (i : Fin d) : (∫ x : Fin d → ℝ, a i * x i ∂gaussianProduct d) = 0 := by
    simpa using hsingle i 1
  have hpow (s : Finset (Fin d)) (k : ℕ) :
      Integrable (fun x : Fin d → ℝ => (∑ i ∈ s, a i * x i) ^ k) (gaussianProduct d) := by
    have hm : MemLp (fun x : Fin d → ℝ => ∑ i ∈ s, a i * x i) (k : ℝ≥0∞) (gaussianProduct d) :=
      memLp_finsetSum s (fun i _ => (gaussianProduct_coordinate_memLp i k (by simp)).const_mul (a i))
    exact hm.integrable_norm_pow'.mono' (hm.aestronglyMeasurable.pow k)
      (Filter.Eventually.of_forall fun x => by simp)
  have hsingle_int (i : Fin d) (k : ℕ) :
      Integrable (fun x : Fin d → ℝ => (a i * x i) ^ k) (gaussianProduct d) := by
    simpa using hpow {i} k
  have hind : iIndepFun (fun i : Fin d => fun x : Fin d → ℝ => a i * x i) (gaussianProduct d) :=
    iIndepFun_pi (fun i => by fun_prop)
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hXY : IndepFun (fun x : Fin d → ℝ => a i * x i)
        (fun x : Fin d → ℝ => ∑ j ∈ s, a j * x j) (gaussianProduct d) := by
      convert! (hind.indepFun_finsetSum_of_notMem (fun j => by fun_prop) hi).symm using 1
      funext x
      simp only [Finset.sum_apply]
    have htwo := indep_integral_add_pow_two hXY (hsingle_int i) (hpow s)
    have hfour := indep_integral_add_pow_four hXY (hsingle_int i) (hpow s)
    simp only [hsingle, hsingle_mean, standardNormal_integral_pow_two,
      standardNormal_integral_pow_three, standardNormal_integral_pow_four, mul_zero, zero_mul,
      mul_one, add_zero, ih.1, ih.2] at htwo hfour
    simp only [Finset.sum_insert hi]
    constructor
    · exact htwo
    · rw [hfour]
      ring

/-- Fourth-moment identity obtained by finite binomial expansion and product integration. -/
theorem gaussianLinear_integral_fourth {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) :
    (∫ x, (gaussianLinear a x) ^ (4 : ℕ) ∂gaussianProduct d) = 3 * ‖a‖ ^ 4 := by
  have he : (∑ i, (a i) ^ 2) = ‖a‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp [pow_two]
  have h := (gaussianFinset_moments a Finset.univ).2
  change (∫ x, (gaussianLinear a x) ^ (4 : ℕ) ∂gaussianProduct d) =
    3 * (∑ i, (a i) ^ 2) ^ 2 at h
  rw [he] at h
  convert h using 1; ring

theorem gaussianLinear_fourth_le_three {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (ha : ‖a‖ ≤ 1) : (∫ x, (gaussianLinear a x) ^ (4 : ℕ) ∂gaussianProduct d) ≤ 3 := by
  rw [gaussianLinear_integral_fourth]
  have h := pow_le_one₀ (norm_nonneg a) ha (n := 4)
  linarith

end EvenOddHaarLevels
