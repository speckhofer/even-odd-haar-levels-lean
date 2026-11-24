import EvenOddHaarLevels.Grothendieck
import EvenOddHaarLevels.DyadicAveraging

/-! Concrete finite weak norms; no generic absolutely summing operator theory. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] {q : ℕ}

def finiteWeakOne (x : Fin q → E) : ℝ :=
  sSup {r : ℝ | ∃ φ : E →L[𝕂] 𝕂, ‖φ‖ ≤ 1 ∧ r = ∑ i, ‖φ (x i)‖}

def finiteWeakTwo (x : Fin q → E) : ℝ :=
  sSup {r : ℝ | ∃ φ : E →L[𝕂] 𝕂, ‖φ‖ ≤ 1 ∧ r = Real.sqrt (∑ i, ‖φ (x i)‖ ^ 2)}

theorem finiteWeakOne_set_nonempty (x : Fin q → E) :
    Set.Nonempty {r : ℝ | ∃ φ : E →L[𝕂] 𝕂, ‖φ‖ ≤ 1 ∧ r = ∑ i, ‖φ (x i)‖} := by
  exact ⟨0, 0, by simp, by simp⟩

theorem finiteWeakTwo_set_nonempty (x : Fin q → E) :
    Set.Nonempty {r : ℝ | ∃ φ : E →L[𝕂] 𝕂, ‖φ‖ ≤ 1 ∧ r = Real.sqrt (∑ i, ‖φ (x i)‖ ^ 2)} := by
  exact ⟨0, 0, by simp, by simp⟩

theorem unitDual_apply_le (φ : E →L[𝕂] 𝕂) (hφ : ‖φ‖ ≤ 1) (z : E) : ‖φ z‖ ≤ ‖z‖ := by
  calc ‖φ z‖ ≤ ‖φ‖ * ‖z‖ := φ.le_opNorm z
    _ ≤ ‖z‖ := by nlinarith [norm_nonneg z]

theorem finiteWeakOne_set_bddAbove (x : Fin q → E) :
    BddAbove {r : ℝ | ∃ φ : E →L[𝕂] 𝕂, ‖φ‖ ≤ 1 ∧ r = ∑ i, ‖φ (x i)‖} := by
  refine ⟨∑ i, ‖x i‖, ?_⟩
  rintro r ⟨φ, hφ, rfl⟩
  exact Finset.sum_le_sum (fun i _ => (unitDual_apply_le (𝕂 := 𝕂)) φ hφ (x i))

theorem finiteWeakTwo_set_bddAbove (x : Fin q → E) :
    BddAbove {r : ℝ | ∃ φ : E →L[𝕂] 𝕂, ‖φ‖ ≤ 1 ∧ r = Real.sqrt (∑ i, ‖φ (x i)‖ ^ 2)} := by
  refine ⟨Real.sqrt (∑ i, ‖x i‖ ^ 2), ?_⟩
  rintro r ⟨φ, hφ, rfl⟩
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) ((unitDual_apply_le (𝕂 := 𝕂)) φ hφ (x i)) 2

theorem finiteWeakOne_nonneg (x : Fin q → E) : 0 ≤ (finiteWeakOne (𝕂 := 𝕂)) x := by
  exact le_csSup ((finiteWeakOne_set_bddAbove (𝕂 := 𝕂)) x) ⟨0, by simp, by simp⟩

theorem finiteWeakTwo_nonneg (x : Fin q → E) : 0 ≤ (finiteWeakTwo (𝕂 := 𝕂)) x := by
  exact le_csSup ((finiteWeakTwo_set_bddAbove (𝕂 := 𝕂)) x) ⟨0, by simp, by simp⟩

theorem finiteWeakOne_le_sum_norm (x : Fin q → E) : (finiteWeakOne (𝕂 := 𝕂)) x ≤ ∑ i, ‖x i‖ := by
  apply csSup_le ((finiteWeakOne_set_nonempty (𝕂 := 𝕂)) x)
  rintro r ⟨φ, hφ, rfl⟩
  exact Finset.sum_le_sum (fun i _ => (unitDual_apply_le (𝕂 := 𝕂)) φ hφ (x i))

theorem finiteWeakTwo_le_sqrt_sum_norm_sq (x : Fin q → E) :
    (finiteWeakTwo (𝕂 := 𝕂)) x ≤ Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
  apply csSup_le ((finiteWeakTwo_set_nonempty (𝕂 := 𝕂)) x)
  rintro r ⟨φ, hφ, rfl⟩
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum (fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) ((unitDual_apply_le (𝕂 := 𝕂)) φ hφ (x i)) 2)

theorem finiteWeakOne_eval_le (x : Fin q → E) (φ : E →L[𝕂] 𝕂) (hφ : ‖φ‖ ≤ 1) :
    (∑ i, ‖φ (x i)‖) ≤ (finiteWeakOne (𝕂 := 𝕂)) x :=
  le_csSup ((finiteWeakOne_set_bddAbove (𝕂 := 𝕂)) x) ⟨φ, hφ, rfl⟩

theorem finiteWeakTwo_eval_le (x : Fin q → E) (φ : E →L[𝕂] 𝕂) (hφ : ‖φ‖ ≤ 1) :
    Real.sqrt (∑ i, ‖φ (x i)‖ ^ 2) ≤ (finiteWeakTwo (𝕂 := 𝕂)) x :=
  le_csSup ((finiteWeakTwo_set_bddAbove (𝕂 := 𝕂)) x) ⟨φ, hφ, rfl⟩

theorem finiteWeakOne_le_iff (x : Fin q → E) (C : ℝ) :
    (finiteWeakOne (𝕂 := 𝕂)) x ≤ C ↔ ∀ φ : E →L[𝕂] 𝕂, ‖φ‖ ≤ 1 → (∑ i, ‖φ (x i)‖) ≤ C := by
  constructor
  · intro h φ hφ
    exact ((finiteWeakOne_eval_le (𝕂 := 𝕂)) x φ hφ).trans h
  · intro h
    apply csSup_le ((finiteWeakOne_set_nonempty (𝕂 := 𝕂)) x)
    rintro r ⟨φ, hφ, rfl⟩
    exact h φ hφ

theorem finiteWeakTwo_le_iff (x : Fin q → E) (C : ℝ) :
    (finiteWeakTwo (𝕂 := 𝕂)) x ≤ C ↔ ∀ φ : E →L[𝕂] 𝕂, ‖φ‖ ≤ 1 →
      Real.sqrt (∑ i, ‖φ (x i)‖ ^ 2) ≤ C := by
  constructor
  · intro h φ hφ
    exact ((finiteWeakTwo_eval_le (𝕂 := 𝕂)) x φ hφ).trans h
  · intro h
    apply csSup_le ((finiteWeakTwo_set_nonempty (𝕂 := 𝕂)) x)
    rintro r ⟨φ, hφ, rfl⟩
    exact h φ hφ

@[simp] theorem finiteWeakOne_empty (x : Fin 0 → E) : (finiteWeakOne (𝕂 := 𝕂)) x = 0 := by
  exact le_antisymm (by simpa using (finiteWeakOne_le_sum_norm (𝕂 := 𝕂)) x) ((finiteWeakOne_nonneg (𝕂 := 𝕂)) x)

@[simp] theorem finiteWeakTwo_empty (x : Fin 0 → E) : (finiteWeakTwo (𝕂 := 𝕂)) x = 0 := by
  exact le_antisymm (by simpa using (finiteWeakTwo_le_sqrt_sum_norm_sq (𝕂 := 𝕂)) x) ((finiteWeakTwo_nonneg (𝕂 := 𝕂)) x)

theorem finiteWeakOne_le_add (x y : Fin q → E) :
    (finiteWeakOne (𝕂 := 𝕂)) x ≤ (finiteWeakOne (𝕂 := 𝕂)) y + ∑ i, ‖x i - y i‖ := by
  rw [(finiteWeakOne_le_iff (𝕂 := 𝕂))]
  intro φ hφ
  calc
    (∑ i, ‖φ (x i)‖) ≤ ∑ i, (‖φ (y i)‖ + ‖x i - y i‖) := by
      apply Finset.sum_le_sum
      intro i _
      have h := (unitDual_apply_le (𝕂 := 𝕂)) φ hφ (x i - y i)
      rw [map_sub] at h
      have ht := norm_add_le (φ (y i)) (φ (x i) - φ (y i))
      rw [add_sub_cancel] at ht
      linarith
    _ = (∑ i, ‖φ (y i)‖) + ∑ i, ‖x i - y i‖ := Finset.sum_add_distrib
    _ ≤ (finiteWeakOne (𝕂 := 𝕂)) y + ∑ i, ‖x i - y i‖ := by
      gcongr
      exact (finiteWeakOne_eval_le (𝕂 := 𝕂)) y φ hφ

theorem finiteWeakOne_lipschitz (x y : Fin q → E) :
    ‖(finiteWeakOne (𝕂 := 𝕂)) x - (finiteWeakOne (𝕂 := 𝕂)) y‖ ≤ ∑ i, ‖x i - y i‖ := by
  rw [Real.norm_eq_abs, abs_le]
  have hxy := (finiteWeakOne_le_add (𝕂 := 𝕂)) x y
  have hyx := (finiteWeakOne_le_add (𝕂 := 𝕂)) y x
  simp_rw [norm_sub_rev (y _) (x _)] at hyx
  constructor <;> linarith

/-- The finite exponent-conversion inequality; no summing-operator abstraction. -/
theorem weighted_finiteWeakOne_le_finiteWeakTwo (x : Fin q → E) (c : Fin q → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hcsq : (∑ i, c i ^ 2) ≤ 1) :
    (finiteWeakOne (𝕂 := 𝕂)) (fun i => (c i : 𝕂) • x i) ≤ (finiteWeakTwo (𝕂 := 𝕂)) x := by
  rw [(finiteWeakOne_le_iff (𝕂 := 𝕂))]
  intro φ hφ
  have hroot : Real.sqrt (∑ i, c i ^ 2) ≤ 1 := by
    exact (Real.sqrt_le_sqrt hcsq).trans_eq (by norm_num)
  calc
    (∑ i, ‖φ ((c i : 𝕂) • x i)‖) = ∑ i, c i * ‖φ (x i)‖ := by
      apply Finset.sum_congr rfl
      intro i _
      simp [abs_of_nonneg (hc i)]
    _ ≤ Real.sqrt (∑ i, c i ^ 2) * Real.sqrt (∑ i, ‖φ (x i)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ i, ‖φ (x i)‖ ^ 2) := by
      nlinarith [Real.sqrt_nonneg (∑ i, ‖φ (x i)‖ ^ 2)]
    _ ≤ (finiteWeakTwo (𝕂 := 𝕂)) x := (finiteWeakTwo_eval_le (𝕂 := 𝕂)) x φ hφ

theorem sqrt_sum_abs_sq_mul (c : 𝕂) (b : Fin q → 𝕂) :
    Real.sqrt (∑ i, ‖c * b i‖ ^ 2) = ‖c‖ * Real.sqrt (∑ i, ‖b i‖ ^ 2) := by
  simp_rw [norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem finiteWeakTwo_eval_le_norm_mul (x : Fin q → E) (φ : E →L[𝕂] 𝕂) :
    Real.sqrt (∑ i, ‖φ (x i)‖ ^ 2) ≤ ‖φ‖ * (finiteWeakTwo (𝕂 := 𝕂)) x := by
  by_cases hzero : ‖φ‖ = 0
  · have hz : φ = 0 := norm_eq_zero.mp hzero
    simp [hz]
  · have hp : 0 < ‖φ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    let ψ : E →L[𝕂] 𝕂 := (‖φ‖ : 𝕂)⁻¹ • φ
    have hψ : ‖ψ‖ ≤ 1 := by
      simp [ψ, norm_smul, inv_mul_cancel₀ hzero]
    have he : (fun i => φ (x i)) = fun i => (‖φ‖ : 𝕂) * ψ (x i) := by
      funext i
      simp [ψ, ← mul_assoc, mul_inv_cancel₀ (show (‖φ‖ : 𝕂) ≠ 0 from RCLike.ofReal_ne_zero.mpr hzero)]
    rw [show (∑ i, ‖φ (x i)‖ ^ 2) = ∑ i, ‖(‖φ‖ : 𝕂) * ψ (x i)‖ ^ 2 by
      exact Finset.sum_congr rfl (fun i _ => by rw [congrFun he i])]
    rw [sqrt_sum_abs_sq_mul, RCLike.norm_ofReal, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left ((finiteWeakTwo_eval_le (𝕂 := 𝕂)) x ψ hψ) hp.le

theorem finiteWeakTwo_map_le {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
    (U : E →L[𝕂] F) (x : Fin q → E) :
    (finiteWeakTwo (𝕂 := 𝕂)) (fun i => U (x i)) ≤ ‖U‖ * (finiteWeakTwo (𝕂 := 𝕂)) x := by
  rw [(finiteWeakTwo_le_iff (𝕂 := 𝕂))]
  intro φ hφ
  calc
    Real.sqrt (∑ i, ‖φ (U (x i))‖ ^ 2) ≤ ‖φ.comp U‖ * (finiteWeakTwo (𝕂 := 𝕂)) x :=
      (finiteWeakTwo_eval_le_norm_mul (𝕂 := 𝕂)) x (φ.comp U)
    _ ≤ (‖φ‖ * ‖U‖) * (finiteWeakTwo (𝕂 := 𝕂)) x :=
      mul_le_mul_of_nonneg_right (φ.opNorm_comp_le U) ((finiteWeakTwo_nonneg (𝕂 := 𝕂)) x)
    _ ≤ ‖U‖ * (finiteWeakTwo (𝕂 := 𝕂)) x := by
      nlinarith [mul_nonneg (norm_nonneg U) ((finiteWeakTwo_nonneg (𝕂 := 𝕂)) x)]

/-- The real sign encoded by a Boolean coordinate. -/
def cubeSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem cubeSign_abs (b : Bool) : ‖cubeSign b‖ = 1 := by cases b <;> norm_num [cubeSign]

/-- Any combination with scalar coefficients in the unit ball is controlled by the finite weak-one norm. -/
theorem norm_cube_sum_le_finiteWeakOne (x : Fin q → E) (t : Fin q → 𝕂)
    (ht : ∀ i, ‖t i‖ ≤ 1) : ‖∑ i, t i • x i‖ ≤ (finiteWeakOne (𝕂 := 𝕂)) x := by
  obtain ⟨φ, hφ, hv⟩ := exists_dual_vector'' 𝕂 (∑ i, t i • x i)
  calc
    ‖∑ i, t i • x i‖ = ‖φ (∑ i, t i • x i)‖ := by simpa only [RCLike.norm_ofReal, abs_norm] using (congrArg norm hv).symm
    _ = ‖∑ i, t i * φ (x i)‖ := by simp
    _ ≤ ∑ i, ‖t i * φ (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖φ (x i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      nlinarith [ht i, norm_nonneg (φ (x i))]
    _ ≤ (finiteWeakOne (𝕂 := 𝕂)) x := (finiteWeakOne_eval_le (𝕂 := 𝕂)) x φ hφ

/-- The scalar unit ball replaces Boolean signs over a complex field. -/
theorem finiteWeakOne_eq_scalar_sup (x : Fin q → E) :
    (finiteWeakOne (𝕂 := 𝕂)) x = sSup (Set.range (fun t : {t : Fin q → 𝕂 // ∀ i, ‖t i‖ ≤ 1} =>
      ‖∑ i, t.val i • x i‖)) := by
  classical
  let M := Set.range (fun t : {t : Fin q → 𝕂 // ∀ i, ‖t i‖ ≤ 1} => ‖∑ i, t.val i • x i‖)
  have hbd : BddAbove M := ⟨(finiteWeakOne (𝕂 := 𝕂)) x, by
    rintro r ⟨t, rfl⟩
    exact (norm_cube_sum_le_finiteWeakOne (𝕂 := 𝕂)) x t.val t.property⟩
  apply le_antisymm
  · rw [(finiteWeakOne_le_iff (𝕂 := 𝕂))]
    intro φ hφ
    let t : Fin q → 𝕂 := fun i => star (φ (x i)) / (‖φ (x i)‖ : 𝕂)
    have ht (i : Fin q) : ‖t i‖ ≤ 1 := by
      dsimp [t]
      rw [norm_div, RCLike.norm_conj, RCLike.norm_ofReal, abs_norm]
      exact div_self_le_one ‖φ (x i)‖
    have he (i : Fin q) : t i * φ (x i) = (‖φ (x i)‖ : 𝕂) := by
      by_cases hz : φ (x i) = 0
      · simp [t, hz]
      · have hn : (‖φ (x i)‖ : 𝕂) ≠ 0 := RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
        dsimp [t]
        rw [div_mul_eq_mul_div, mul_comm ((starRingEnd 𝕂) _), RCLike.mul_conj]
        field_simp
    let : Nonempty {t : Fin q → 𝕂 // ∀ i, ‖t i‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
    have heq : ‖∑ i, t i • x i‖ ≥ ∑ i, ‖φ (x i)‖ := by
      have hh := unitDual_apply_le φ hφ (∑ i, t i • x i)
      rw [map_sum] at hh
      simp only [map_smul, smul_eq_mul, he] at hh
      rw [← RCLike.ofReal_sum, RCLike.norm_ofReal,
        abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at hh
      exact hh
    exact heq.trans (le_csSup hbd (show ‖∑ i, t i • x i‖ ∈ M from ⟨⟨t, ht⟩, rfl⟩))
  · apply csSup_le (show M.Nonempty from ⟨‖∑ i, (0 : 𝕂) • x i‖, ⟨⟨0, by simp⟩, rfl⟩⟩)
    rintro r ⟨t, rfl⟩
    exact (norm_cube_sum_le_finiteWeakOne (𝕂 := 𝕂)) x t.val t.property

/-- Explicit product weights for the finite cube, including its unique empty vertex. -/
def cubeWeight (t : Fin q → ℝ) (ε : Fin q → Bool) : ℝ :=
  ∏ i, (1 + cubeSign (ε i) * t i) / 2

theorem cubeWeight_nonneg (t : Fin q → ℝ) (ht : ∀ i, ‖t i‖ ≤ 1) (ε : Fin q → Bool) :
    0 ≤ cubeWeight t ε := by
  apply Finset.prod_nonneg
  intro i _
  have hi := abs_le.mp (by simpa only [Real.norm_eq_abs] using ht i)
  cases hε : ε i <;> simp [cubeSign] <;> linarith

theorem sum_cubeWeight (t : Fin q → ℝ) : (∑ ε : Fin q → Bool, cubeWeight t ε) = 1 := by
  unfold cubeWeight
  erw [← Fintype.prod_sum (fun (i : Fin q) (b : Bool) => (1 + cubeSign b * t i) / 2)]
  have h (i : Fin q) : (∑ b : Bool, (1 + cubeSign b * t i) / 2) = 1 := by
    simp [cubeSign]
    ring
  simp_rw [h]
  simp

theorem cubeWeight_barycenter (t : Fin q → ℝ) (i : Fin q) :
    (∑ ε : Fin q → Bool, cubeWeight t ε * cubeSign (ε i)) = t i := by
  classical
  have he (ε : Fin q → Bool) : cubeWeight t ε * cubeSign (ε i) =
      ∏ j, ((if j = i then cubeSign (ε j) else 1) * ((1 + cubeSign (ε j) * t j) / 2)) := by
    rw [Finset.prod_mul_distrib]
    simp [cubeWeight, mul_comm]
  simp_rw [he]
  erw [← Fintype.prod_sum (fun (j : Fin q) (b : Bool) =>
    (if j = i then cubeSign b else 1) * ((1 + cubeSign b * t j) / 2))]
  have h (j : Fin q) :
      (∑ b : Bool, (if j = i then cubeSign b else 1) * ((1 + cubeSign b * t j) / 2)) =
        if j = i then t i else 1 := by
    by_cases hj : j = i
    · subst j
      simp [cubeSign]
      ring
    · simp [hj, cubeSign]
      ring
  simp_rw [h]
  simp

/-- The scalar matrix bound for a finite family in disjoint normalized coordinates. -/
theorem matrixScalarBound_of_l1_coordinates {r : ℕ} (e : Fin r → E)
    (he : ∀ c : Fin r → 𝕂, ‖∑ j, c j • e j‖ = ∑ j, ‖c j‖)
    (f : Fin q → E) (b : Fin r → Fin q → 𝕂) (hf : ∀ i, f i = ∑ j, b j i • e j)
    (p : 𝕂 →L[ℝ] ℝ) (hp : ∀ z, |p z| ≤ ‖z‖) :
    matrixScalarBound (fun j i => p (b j i)) ≤ (finiteWeakOne (𝕂 := 𝕂)) f := by
  rw [matrixScalarBound_le_iff]
  intro s t hs ht
  have hcomb : (∑ j, (∑ i, (t i : 𝕂) * b j i) • e j) = ∑ i, (t i : 𝕂) • f i := by
    simp_rw [hf, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
  have hexpr (j : Fin r) : (∑ i, p (b j i) * (s j * t i)) =
      s j * p (∑ i, (t i : 𝕂) * b j i) := by
    simp only [map_sum, ← RCLike.real_smul_eq_coe_mul, map_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hexpr]
  calc
    _ ≤ ∑ j, |s j * p (∑ i, (t i : 𝕂) * b j i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ‖∑ i, (t i : 𝕂) * b j i‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hs j) (abs_nonneg _)).trans (by simpa only [one_mul] using hp (∑ i, (t i : 𝕂) * b j i))
    _ = ‖∑ j, (∑ i, (t i : 𝕂) * b j i) • e j‖ := (he _).symm
    _ = ‖∑ i, (t i : 𝕂) • f i‖ := by rw [hcomb]
    _ ≤ (finiteWeakOne (𝕂 := 𝕂)) f := (norm_cube_sum_le_finiteWeakOne (𝕂 := 𝕂)) f _
      (fun i => by simpa only [RCLike.norm_ofReal] using ht i)

/-- Grothendieck applied to a finite normalized disjoint coordinate system.
The real Gaussian inequality is applied to the real and imaginary coefficient
matrices in the underlying real Hilbert space. This gives the common constant
81/8 over either scalar field, without transporting any real Banach-space proof. -/
theorem finiteSummingOne_of_l1_coordinates {r : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕂 H]
    (A : E →L[𝕂] H) (e : Fin r → E)
    (he : ∀ c : Fin r → 𝕂, ‖∑ j, c j • e j‖ = ∑ j, ‖c j‖)
    (f : Fin q → E) (b : Fin r → Fin q → 𝕂) (hf : ∀ i, f i = ∑ j, b j i • e j) :
    (∑ i, ‖A (f i)‖) ≤ (81 / 8) * ‖A‖ * (finiteWeakOne (𝕂 := 𝕂)) f := by
  classical
  by_cases hz : ‖A‖ = 0
  · have hAz : A = 0 := norm_eq_zero.mp hz
    simp [hAz]
  have hp : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hen (j : Fin r) : ‖e j‖ = 1 := by
    simpa [ite_smul, apply_ite] using he (fun k => if k = j then 1 else 0)
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal 𝕂 H
  let u : Fin r → H := fun j => ‖A‖⁻¹ • A (e j)
  let v : Fin q → H := fun i => ‖A (f i)‖⁻¹ • A (f i)
  have hu (j : Fin r) : ‖u j‖ ≤ 1 := by
    have h := A.le_opNorm (e j)
    rw [hen j, mul_one] at h
    change ‖‖A‖⁻¹ • A (e j)‖ ≤ 1
    simp only [norm_smul, norm_inv, norm_norm]
    exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (norm_nonneg _))).trans_eq (inv_mul_cancel₀ hz)
  have hv (i : Fin q) : ‖v i‖ ≤ 1 := by
    by_cases hi : ‖A (f i)‖ = 0
    · simp [v, hi]
    · simp [v, norm_smul, inv_mul_cancel₀ hi]
  have huv (j : Fin r) : ‖A‖ • u j = A (e j) := by
    simp [u, smul_smul, mul_inv_cancel₀ hz]
  have hself (i : Fin q) : inner ℝ (A (f i)) (v i) = ‖A (f i)‖ := by
    dsimp [v]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    by_cases hi : ‖A (f i)‖ = 0
    · simp [hi]
    · field_simp
  have hrow (i : Fin q) : ‖A (f i)‖ = ‖A‖ *
      ((∑ j, RCLike.re (b j i) * inner ℝ (u j) (v i)) +
       ∑ j, RCLike.im (b j i) * inner ℝ ((RCLike.I : 𝕂) • u j) (v i)) := by
    rw [← hself i]
    have hb (j : Fin r) : b j i • A (e j) =
        RCLike.re (b j i) • A (e j) +
        RCLike.im (b j i) • ((RCLike.I : 𝕂) • A (e j)) := by
      rw [RCLike.real_smul_eq_coe_smul (K := 𝕂), RCLike.real_smul_eq_coe_smul (K := 𝕂), smul_smul, ← add_smul, RCLike.re_add_im]
    rw [hf i, map_sum]
    simp only [A.map_smul, hb]
    simp only [sum_inner, inner_add_left, real_inner_smul_left,
      ← huv, smul_comm (RCLike.I : 𝕂), real_inner_smul_left]
    simp only [Finset.sum_add_distrib, mul_add, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  have hB₁ := (matrixScalarBound_of_l1_coordinates (𝕂 := 𝕂)) e he f b hf
    (RCLike.reCLM : 𝕂 →L[ℝ] ℝ) RCLike.abs_re_le_norm
  have hB₂ := (matrixScalarBound_of_l1_coordinates (𝕂 := 𝕂)) e he f b hf
    (RCLike.imCLM : 𝕂 →L[ℝ] ℝ) RCLike.abs_im_le_norm
  have hG₁ := grothendieck_matrix (fun j i => RCLike.re (b j i)) u v hu hv
  have hG₂ := grothendieck_matrix (fun j i => RCLike.im (b j i))
    (fun j => (RCLike.I : 𝕂) • u j) v
    (fun j => by rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (show ‖(RCLike.I : 𝕂)‖ ≤ 1 by rw [RCLike.norm_I]; split_ifs <;> norm_num) (norm_nonneg _)).trans (by simpa using hu j)) hv
  have hwhole : (∑ i, ‖A (f i)‖) = ‖A‖ *
      ((∑ j, ∑ i, RCLike.re (b j i) * inner ℝ (u j) (v i)) +
       ∑ j, ∑ i, RCLike.im (b j i) * inner ℝ ((RCLike.I : 𝕂) • u j) (v i)) := by
    simp_rw [hrow, ← Finset.mul_sum, Finset.sum_add_distrib]
    congr 2 <;> apply Finset.sum_comm
  rw [hwhole]
  have h₁ := (le_abs_self _).trans (hG₁.trans (mul_le_mul_of_nonneg_left hB₁ (by norm_num : (0 : ℝ) ≤ 81/16)))
  have h₂ := (le_abs_self _).trans (hG₂.trans (mul_le_mul_of_nonneg_left hB₂ (by norm_num : (0 : ℝ) ≤ 81/16)))
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (norm_nonneg A)]

/-- A positive-measure cell, normalized in the canonical L¹ space. -/
def normalizedPartitionCell (D : Set ℝ) (hD : MeasurableSet D) : (L1 𝕂) :=
  indicatorConstLp 1 hD (measure_ne_top _ _) ((unitIntervalMeasure.real D : ℝ) : 𝕂)⁻¹

theorem normalizedPartitionCell_ae (D : Set ℝ) (hD : MeasurableSet D) :
    ((normalizedPartitionCell (𝕂 := 𝕂)) D hD : ℝ → 𝕂) =ᵐ[unitIntervalMeasure]
      D.indicator (fun _ => (unitIntervalMeasure.real D : 𝕂)⁻¹) :=
  indicatorConstLp_coeFn

theorem normalizedPartitionCell_norm_sum {r : ℕ} (D : Fin r → Set ℝ)
    (hm : ∀ j, MeasurableSet (D j)) (hd : Pairwise (fun j k => Disjoint (D j) (D k)))
    (hp : ∀ j, 0 < unitIntervalMeasure.real (D j)) (c : Fin r → 𝕂) :
    ‖∑ j, c j • (normalizedPartitionCell (𝕂 := 𝕂)) (D j) (hm j)‖ = ∑ j, ‖c j‖ := by
  have hsingle (j : Fin r) :
      (c j • (normalizedPartitionCell (𝕂 := 𝕂)) (D j) (hm j) : (L1 𝕂)) =ᵐ[unitIntervalMeasure]
        (D j).indicator (fun _ => c j / (unitIntervalMeasure.real (D j) : 𝕂)) := by
    filter_upwards [Lp.coeFn_smul (c j) ((normalizedPartitionCell (𝕂 := 𝕂)) (D j) (hm j)),
      (normalizedPartitionCell_ae (𝕂 := 𝕂)) (D j) (hm j)] with x hs hc
    rw [hs, Pi.smul_apply, hc]
    by_cases hx : x ∈ D j <;> simp [hx, smul_eq_mul, div_eq_mul_inv]
  have hsum : ((∑ j, c j • (normalizedPartitionCell (𝕂 := 𝕂)) (D j) (hm j) : (L1 𝕂)) : ℝ → 𝕂) =ᵐ[unitIntervalMeasure]
      (fun x => ∑ j, (D j).indicator (fun _ => c j / (unitIntervalMeasure.real (D j) : 𝕂)) x) := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j => c j • (normalizedPartitionCell (𝕂 := 𝕂)) (D j) (hm j)),
      ae_all_iff.mpr hsingle] with x hs hall
    rw [hs]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => hall j)
  rw [MeasureTheory.L1.norm_eq_integral_norm]
  calc
    (∫ x, ‖(∑ j, c j • (normalizedPartitionCell (𝕂 := 𝕂)) (D j) (hm j) : (L1 𝕂)) x‖ ∂unitIntervalMeasure) =
        ∫ x, ‖∑ j, (D j).indicator (fun _ => c j / (unitIntervalMeasure.real (D j) : 𝕂)) x‖ ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [hsum] with x hx
      rw [hx]
    _ = ∑ j, ‖c j / (unitIntervalMeasure.real (D j) : 𝕂)‖ * unitIntervalMeasure.real (D j) :=
      finite_disjoint_integral_norm D hm hd _
    _ = ∑ j, ‖c j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_div, RCLike.norm_ofReal, abs_of_pos (hp j), div_mul_cancel₀ _ (hp j).ne']

theorem finiteSummingOne_of_partition {r : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕂 H]
    (A : (L1 𝕂) →L[𝕂] H) (D : Fin r → Set ℝ)
    (hm : ∀ j, MeasurableSet (D j)) (hd : Pairwise (fun j k => Disjoint (D j) (D k)))
    (hp : ∀ j, 0 < unitIntervalMeasure.real (D j))
    (f : Fin q → (L1 𝕂)) (b : Fin r → Fin q → 𝕂)
    (hf : ∀ i, f i = ∑ j, b j i • (normalizedPartitionCell (𝕂 := 𝕂)) (D j) (hm j)) :
    (∑ i, ‖A (f i)‖) ≤ (81 / 8) * ‖A‖ * (finiteWeakOne (𝕂 := 𝕂)) f := by
  exact (finiteSummingOne_of_l1_coordinates (𝕂 := 𝕂)) A (fun j => (normalizedPartitionCell (𝕂 := 𝕂)) (D j) (hm j))
    ((normalizedPartitionCell_norm_sum (𝕂 := 𝕂)) D hm hd hp) f b hf

theorem finiteWeakOne_tendsto (f : ℕ → Fin q → E) (x : Fin q → E)
    (hx : ∀ i, Filter.Tendsto (fun n => f n i) Filter.atTop (nhds (x i))) :
    Filter.Tendsto (fun n => (finiteWeakOne (𝕂 := 𝕂)) (f n)) Filter.atTop (nhds ((finiteWeakOne (𝕂 := 𝕂)) x)) := by
  have hd : Filter.Tendsto (fun n => ∑ i, ‖f n i - x i‖) Filter.atTop (nhds 0) := by
    have h := tendsto_finsetSum Finset.univ (fun i _ => ((hx i).sub (tendsto_const_nhds (x := x i))).norm)
    simpa using h
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero (fun n => norm_nonneg _) _ hd
  intro n
  simpa only [Real.norm_eq_abs] using (finiteWeakOne_lipschitz (𝕂 := 𝕂)) (f n) x

/-- Passage to the limit for a common finite-family estimate. -/
theorem finiteSummingOne_of_tendsto {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
    (A : E →L[𝕂] F) (C : ℝ) (f : ℕ → Fin q → E) (x : Fin q → E)
    (hx : ∀ i, Filter.Tendsto (fun n => f n i) Filter.atTop (nhds (x i)))
    (hb : ∀ n, (∑ i, ‖A (f n i)‖) ≤ C * (finiteWeakOne (𝕂 := 𝕂)) (f n)) :
    (∑ i, ‖A (x i)‖) ≤ C * (finiteWeakOne (𝕂 := 𝕂)) x := by
  have hl : Filter.Tendsto (fun n => ∑ i, ‖A (f n i)‖) Filter.atTop (nhds (∑ i, ‖A (x i)‖)) :=
    tendsto_finsetSum _ (fun i _ => ((A.continuous.tendsto (x i)).comp (hx i)).norm)
  exact le_of_tendsto_of_tendsto hl (tendsto_const_nhds.mul ((finiteWeakOne_tendsto (𝕂 := 𝕂)) f x hx))
    (Filter.Eventually.of_forall hb)

theorem normalizedPartitionCell_dyadic (I : DyadicIndex) :
    (normalizedPartitionCell (𝕂 := 𝕂)) (dyadicInterval I) (dyadicInterval_measurable I) =
      (dyadicMeasure I : 𝕂)⁻¹ • (cellL1 (𝕂 := 𝕂)) I := by
  apply Lp.ext
  filter_upwards [(normalizedPartitionCell_ae (𝕂 := 𝕂)) (dyadicInterval I) (dyadicInterval_measurable I),
    Lp.coeFn_smul ((dyadicMeasure I : 𝕂)⁻¹) ((cellL1 (𝕂 := 𝕂)) I), (cellL1_ae (𝕂 := 𝕂)) I] with x hn hs hc
  rw [hn, hs, Pi.smul_apply, hc, dyadicInterval_real_measure]
  by_cases hx : x ∈ dyadicInterval I <;> simp [hx]

theorem dyadicAverage_normalized_expansion (m : ℕ) (f : (L1 𝕂)) :
    (dyadicAverage (𝕂 := 𝕂)) m f = ∑ k : Fin (2 ^ m), (intervalFunctional (𝕂 := 𝕂)) ⟨m, k⟩ f •
      (normalizedPartitionCell (𝕂 := 𝕂)) (dyadicInterval ⟨m, k⟩) (dyadicInterval_measurable ⟨m, k⟩) := by
  rw [(dyadicAverage_apply (𝕂 := 𝕂))]
  simp_rw [(normalizedPartitionCell_dyadic (𝕂 := 𝕂)), smul_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]

theorem finiteSummingOne_dyadicAverage {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕂 H]
    (A : (L1 𝕂) →L[𝕂] H) (m : ℕ) (f : Fin q → (L1 𝕂)) :
    (∑ i, ‖A ((dyadicAverage (𝕂 := 𝕂)) m (f i))‖) ≤
      (81 / 8) * ‖A‖ * (finiteWeakOne (𝕂 := 𝕂)) (fun i => (dyadicAverage (𝕂 := 𝕂)) m (f i)) := by
  apply (finiteSummingOne_of_partition (𝕂 := 𝕂)) A (fun k : Fin (2 ^ m) => dyadicInterval ⟨m, k⟩)
    (fun k => dyadicInterval_measurable ⟨m, k⟩) (fun _ _ h => dyadic_level_disjoint m h)
    (fun k => by rw [dyadicInterval_real_measure]; exact dyadicMeasure_pos ⟨m, k⟩)
    (fun i => (dyadicAverage (𝕂 := 𝕂)) m (f i)) (fun k i => (intervalFunctional (𝕂 := 𝕂)) ⟨m, k⟩ (f i))
  intro i
  exact (dyadicAverage_normalized_expansion (𝕂 := 𝕂)) m (f i)

theorem finiteWeakOne_map_le {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
    (U : E →L[𝕂] F) (x : Fin q → E) :
    (finiteWeakOne (𝕂 := 𝕂)) (fun i => U (x i)) ≤ ‖U‖ * (finiteWeakOne (𝕂 := 𝕂)) x := by
  rw [(finiteWeakOne_eq_scalar_sup (𝕂 := 𝕂))]
  have hne : (Set.range (fun t : {t : Fin q → 𝕂 // ∀ i, ‖t i‖ ≤ 1} =>
      ‖∑ i, t.val i • U (x i)‖)).Nonempty := ⟨0, ⟨⟨0, by simp⟩, by simp⟩⟩
  apply csSup_le hne
  rintro r ⟨t, rfl⟩
  have he : (∑ i, t.val i • U (x i)) = U (∑ i, t.val i • x i) := by simp
  change ‖∑ i, t.val i • U (x i)‖ ≤ _
  rw [he]
  exact (U.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left ((norm_cube_sum_le_finiteWeakOne (𝕂 := 𝕂)) x t.val t.property) (norm_nonneg _))

/-- The finite 1-to-2 summing implication, using normalized image lengths. -/
theorem finiteSummingTwo_of_finiteSummingOne {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕂 F] (A : E →L[𝕂] F) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ y : Fin q → E, (∑ i, ‖A (y i)‖) ≤ C * (finiteWeakOne (𝕂 := 𝕂)) y) (x : Fin q → E) :
    Real.sqrt (∑ i, ‖A (x i)‖ ^ 2) ≤ C * (finiteWeakTwo (𝕂 := 𝕂)) x := by
  let b := Real.sqrt (∑ i, ‖A (x i)‖ ^ 2)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = ∑ i, ‖A (x i)‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  by_cases hz : b = 0
  · change b ≤ C * (finiteWeakTwo (𝕂 := 𝕂)) x
    rw [hz]
    exact mul_nonneg hC ((finiteWeakTwo_nonneg (𝕂 := 𝕂)) x)
  have hp : 0 < b := lt_of_le_of_ne hb (Ne.symm hz)
  let c := fun i => ‖A (x i)‖ / b
  have hc (i : Fin q) : 0 ≤ c i := div_nonneg (norm_nonneg _) hb
  have hcsq : (∑ i, c i ^ 2) ≤ 1 := by
    dsimp [c]
    simp_rw [div_pow, ← Finset.sum_div, ← hb2]
    rw [div_self (pow_ne_zero 2 hz)]
  have hleft : (∑ i, ‖A ((c i : 𝕂) • x i)‖) = b := by
    simp_rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (hc _)]
    calc
      (∑ i, c i * ‖A (x i)‖) = (∑ i, ‖A (x i)‖ ^ 2) / b := by
        simp only [c, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = b := by rw [← hb2]; field_simp
  have h := hA (fun i => (c i : 𝕂) • x i)
  rw [hleft] at h
  exact h.trans (mul_le_mul_of_nonneg_left ((weighted_finiteWeakOne_le_finiteWeakTwo (𝕂 := 𝕂)) x c hc hcsq) hC)

/-- Every bounded operator on canonical scalar-valued L¹ satisfies the finite one-summing estimate. -/
theorem l1_finiteSummingOne {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕂 H]
    (A : (L1 𝕂) →L[𝕂] H) (x : Fin q → (L1 𝕂)) :
    (∑ i, ‖A (x i)‖) ≤ (81 / 8) * ‖A‖ * (finiteWeakOne (𝕂 := 𝕂)) x := by
  exact (finiteSummingOne_of_tendsto (𝕂 := 𝕂)) A ((81 / 8) * ‖A‖)
    (fun m i => (dyadicAverage (𝕂 := 𝕂)) m (x i)) x (fun i => (dyadicAverage_tendsto (𝕂 := 𝕂)) (x i))
    (fun m => (finiteSummingOne_dyadicAverage (𝕂 := 𝕂)) A m x)

/-- The finite two-summing estimate, with no generic summing-operator theory. -/
theorem l1_finiteSummingTwo {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕂 H]
    (A : (L1 𝕂) →L[𝕂] H) (x : Fin q → (L1 𝕂)) :
    Real.sqrt (∑ i, ‖A (x i)‖ ^ 2) ≤ (81 / 8) * ‖A‖ * (finiteWeakTwo (𝕂 := 𝕂)) x := by
  exact (finiteSummingTwo_of_finiteSummingOne (𝕂 := 𝕂)) A (by positivity)
    (fun y => (l1_finiteSummingOne (𝕂 := 𝕂)) A y) x

/-- Transporting the canonical L¹ finite-family estimate across a Banach-space isomorphism. -/
theorem finiteSummingTwo_transport {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕂 H]
    (V : (L1 𝕂) ≃L[𝕂] E) (T : E →L[𝕂] H) (x : Fin q → E) :
    Real.sqrt (∑ i, ‖T (x i)‖ ^ 2) ≤
      (81 / 8) * ‖T‖ * ‖V.toContinuousLinearMap‖ * ‖V.symm.toContinuousLinearMap‖ * (finiteWeakTwo (𝕂 := 𝕂)) x := by
  have h := (l1_finiteSummingTwo (𝕂 := 𝕂)) (T.comp V.toContinuousLinearMap) (fun i => V.symm (x i))
  have hn := T.opNorm_comp_le V.toContinuousLinearMap
  have hw := (finiteWeakTwo_map_le (𝕂 := 𝕂)) V.symm.toContinuousLinearMap x
  calc
    Real.sqrt (∑ i, ‖T (x i)‖ ^ 2) ≤
        (81 / 8) * ‖T.comp V.toContinuousLinearMap‖ * (finiteWeakTwo (𝕂 := 𝕂)) (fun i => V.symm (x i)) := by
      simpa using h
    _ ≤ (81 / 8) * (‖T‖ * ‖V.toContinuousLinearMap‖) *
        (‖V.symm.toContinuousLinearMap‖ * (finiteWeakTwo (𝕂 := 𝕂)) x) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hn (by norm_num)
      · exact hw
      · exact (finiteWeakTwo_nonneg (𝕂 := 𝕂)) _
      · positivity
    _ = (81 / 8) * ‖T‖ * ‖V.toContinuousLinearMap‖ * ‖V.symm.toContinuousLinearMap‖ * (finiteWeakTwo (𝕂 := 𝕂)) x := by ring

end EvenOddHaarLevels
