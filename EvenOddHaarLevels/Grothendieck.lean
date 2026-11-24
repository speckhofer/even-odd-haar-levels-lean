import EvenOddHaarLevels.GaussianMoments

/-! Scalar clipping and the numerical absorption step in the Gaussian proof. -/
noncomputable section
namespace EvenOddHaarLevels

def clip (M t : ℝ) : ℝ := max (-M) (min t M)

theorem continuous_clip (M : ℝ) : Continuous (clip M) := by
  unfold clip
  fun_prop

theorem clip_abs_le {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : |clip M t| ≤ M := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem clip_eq_self {M t : ℝ} (ht : |t| ≤ M) : clip M t = t := by
  obtain ⟨hl, hu⟩ := abs_le.mp ht
  simp [clip, min_eq_left hu, max_eq_right hl]

theorem clip_abs_le_self {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : |clip M t| ≤ |t| := by
  by_cases ht : |t| ≤ M
  · rw [clip_eq_self ht]
  · exact (clip_abs_le hM t).trans (le_of_not_ge ht)

/-- The scalar fourth-moment estimate underlying the L² truncation error. -/
theorem clip_error_sq {M : ℝ} (hM : 0 < M) (t : ℝ) :
    |t - clip M t| ^ 2 ≤ |t| ^ 4 / (16 * M ^ 2) := by
  rw [le_div_iff₀ (by positivity)]
  by_cases hl : t < -M
  · have hc : clip M t = -M := by simp [clip, min_eq_left (by linarith : t ≤ M), max_eq_left hl.le]
    rw [hc, sq_abs, show |t| ^ 4 = t ^ 4 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]; ring]
    have hp : 0 ≤ t ^ 2 - 4 * M * (t + M) := by
      nlinarith [sq_nonneg t, mul_nonpos_of_nonneg_of_nonpos hM.le (show t + M ≤ 0 by linarith)]
    nlinarith [mul_nonneg (sq_nonneg (t + 2 * M)) hp]
  · by_cases hu : M < t
    · have hc : clip M t = M := by simp [clip, min_eq_right hu.le, max_eq_right (by linarith : -M ≤ M)]
      rw [hc, sq_abs, show |t| ^ 4 = t ^ 4 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]; ring]
      have hp : 0 ≤ t ^ 2 + 4 * M * (t - M) := by
        nlinarith [sq_nonneg t, mul_nonneg hM.le (show 0 ≤ t - M by linarith)]
      nlinarith [mul_nonneg (sq_nonneg (t - 2 * M)) hp]
    · rw [clip_eq_self (abs_le.mpr ⟨by linarith, by linarith⟩)]
      simp

/-- Absorbing the two Gaussian clipping errors with the paper's constant. -/
theorem truncation_absorption {C : ℝ}
    (h : ∀ M : ℝ, 0 < M → C ≤ M ^ 2 + Real.sqrt 3 / (2 * M) * C) :
    C ≤ 81 / 16 := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc := h (3 * Real.sqrt 3 / 4) (by positivity)
  have hr : Real.sqrt 3 / (2 * (3 * Real.sqrt 3 / 4)) = 2 / 3 := by
    field_simp
    ring
  rw [hr] at hc
  nlinarith

open MeasureTheory
open scoped ENNReal

/-- Clipping acts on every Lp space by pointwise norm domination. -/
theorem clip_memLp {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {U : Ω → ℝ} {p : ℝ≥0∞} (hU : MemLp U p ν) {M : ℝ} (hM : 0 ≤ M) :
    MemLp (fun ω => clip M (U ω)) p ν := by
  apply hU.mono ((continuous_clip M).comp_aestronglyMeasurable hU.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun ω => by simpa using clip_abs_le_self hM (U ω))

/-- The pointwise truncation, as an actual L² equivalence class. -/
def clipL2 {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {U : Ω → ℝ} (hU : MemLp U 2 ν) {M : ℝ} (hM : 0 ≤ M) : Lp ℝ 2 ν :=
  (clip_memLp hU hM).toLp (fun ω => clip M (U ω))

theorem clipL2_norm_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {U : Ω → ℝ} (hU : MemLp U 2 ν) {M : ℝ} (hM : 0 ≤ M) :
    ‖clipL2 hU hM‖ ≤ ‖hU.toLp U‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(clip_memLp hU hM).coeFn_toLp, hU.coeFn_toLp] with ω hc hu
  simpa [clipL2, hc, hu] using clip_abs_le_self hM (U ω)

/-- Squared L² norm expressed using the chosen representative. -/
theorem realL2_norm_sq {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {U : Ω → ℝ} (hU : MemLp U 2 ν) :
    ‖hU.toLp U‖ ^ 2 = ∫ ω, (U ω) ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hU.coeFn_toLp] with ω hω
  simp [hω, pow_two]

/-- Integrating the sharp scalar error bound, with integrability explicit. -/
theorem clip_error_integral_sq_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {U : Ω → ℝ} (hU : MemLp U 2 ν)
    (hfour : Integrable (fun ω => (U ω) ^ (4 : ℕ)) ν) {M : ℝ} (hM : 0 < M) :
    (∫ ω, (U ω - clip M (U ω)) ^ 2 ∂ν) ≤
      (∫ ω, (U ω) ^ (4 : ℕ) ∂ν) / (16 * M ^ 2) := by
  rw [← integral_div]
  apply integral_mono (hU.sub (clip_memLp hU hM.le)).integrable_sq (hfour.div_const _)
  intro ω
  convert! clip_error_sq hM (U ω) using 1
  · simp
  · rw [show |U ω| ^ 4 = (U ω) ^ 4 by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]; ring]

/-- The L² truncation error used for each of the two Hilbert error terms. -/
theorem clipL2_error_norm_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {U : Ω → ℝ} (hU : MemLp U 2 ν)
    (hfour : Integrable (fun ω => (U ω) ^ (4 : ℕ)) ν)
    (hbound : (∫ ω, (U ω) ^ (4 : ℕ) ∂ν) ≤ 3) {M : ℝ} (hM : 0 < M) :
    ‖hU.toLp U - clipL2 hU hM.le‖ ≤ Real.sqrt 3 / (4 * M) := by
  have herr := clip_error_integral_sq_le hU hfour hM
  have hden : 0 < 16 * M ^ 2 := by positivity
  have hsq : ‖hU.toLp U - clipL2 hU hM.le‖ ^ 2 ≤ 3 / (16 * M ^ 2) := by
    rw [clipL2, ← MemLp.toLp_sub hU (clip_memLp hU hM.le), realL2_norm_sq]
    exact herr.trans (div_le_div_of_nonneg_right hbound hden.le)
  have hs : (Real.sqrt 3 / (4 * M)) ^ 2 = 3 / (16 * M ^ 2) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    congr 1; ring
  have hp : 0 ≤ Real.sqrt 3 / (4 * M) := by positivity
  nlinarith [norm_nonneg (hU.toLp U - clipL2 hU hM.le)]

/-- Finite-dimensional orthonormal coordinates padded by standard coordinate vectors. -/
theorem finiteHilbertCompression {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {r : ℕ} (z : Fin r → H) :
    Nonempty ((Submodule.span ℝ (Set.range z)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) := by
  classical
  let S := Submodule.span ℝ (Set.range z)
  let : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range z)
  let b := stdOrthonormalBasis ℝ S
  have hd : Module.finrank ℝ S ≤ r := by
    simpa [S, Set.finrank] using (finrank_range_le_card (R := ℝ) z)
  let f : Fin (Module.finrank ℝ S) → EuclideanSpace ℝ (Fin r) :=
    fun i => EuclideanSpace.single (Fin.castLE hd i) 1
  let L : S →ₗ[ℝ] EuclideanSpace ℝ (Fin r) := b.toBasis.constr ℝ f
  have ho : Orthonormal ℝ (L ∘ b.toBasis) := by
    convert! (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin r)).comp
      (Fin.castLE hd) (Fin.castLE_injective hd) using 1
    funext i
    simp [L, f]
  exact ⟨L.isometryOfOrthonormal b.orthonormal ho⟩

def matrixScalarSet {m n : ℕ} (A : Fin m → Fin n → ℝ) : Set ℝ :=
  {r | ∃ (s : Fin m → ℝ) (t : Fin n → ℝ),
    (∀ i, |s i| ≤ 1) ∧ (∀ j, |t j| ≤ 1) ∧ r = |∑ i, ∑ j, A i j * (s i * t j)|}

def matrixHilbertSet {m n : ℕ} (A : Fin m → Fin n → ℝ) : Set ℝ :=
  {r | ∃ (u : Fin m → EuclideanSpace ℝ (Fin (m + n)))
    (v : Fin n → EuclideanSpace ℝ (Fin (m + n))),
    (∀ i, ‖u i‖ ≤ 1) ∧ (∀ j, ‖v j‖ ≤ 1) ∧ r = |∑ i, ∑ j, A i j * inner ℝ (u i) (v j)|}

def matrixScalarBound {m n : ℕ} (A : Fin m → Fin n → ℝ) : ℝ := sSup (matrixScalarSet A)
def matrixHilbertBound {m n : ℕ} (A : Fin m → Fin n → ℝ) : ℝ := sSup (matrixHilbertSet A)

theorem matrix_sum_abs_le {m n : ℕ} (A w : Fin m → Fin n → ℝ)
    (hw : ∀ i j, |w i j| ≤ 1) :
    |∑ i, ∑ j, A i j * w i j| ≤ ∑ i, ∑ j, |A i j| := by
  calc
    |∑ i, ∑ j, A i j * w i j| ≤ ∑ i, |∑ j, A i j * w i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j * w i j| :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |A i j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      nlinarith [abs_nonneg (A i j), hw i j]

theorem matrixScalarSet_nonempty {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    (matrixScalarSet A).Nonempty := by
  exact ⟨0, 0, 0, by simp, by simp, by simp⟩

theorem matrixHilbertSet_nonempty {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    (matrixHilbertSet A).Nonempty := by
  exact ⟨0, 0, 0, by simp, by simp, by simp⟩

theorem matrixScalarSet_bddAbove {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    BddAbove (matrixScalarSet A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro r ⟨s, t, hs, ht, rfl⟩
  apply matrix_sum_abs_le
  intro i j
  rw [abs_mul]
  exact (mul_le_mul (hs i) (ht j) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem matrixHilbertSet_bddAbove {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    BddAbove (matrixHilbertSet A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro r ⟨u, v, hu, hv, rfl⟩
  apply matrix_sum_abs_le
  intro i j
  exact (abs_real_inner_le_norm _ _).trans
    ((mul_le_mul (hu i) (hv j) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))

theorem matrixScalarBound_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    0 ≤ matrixScalarBound A :=
  le_csSup (matrixScalarSet_bddAbove A) ⟨0, 0, by simp, by simp, by simp⟩

theorem matrixHilbertBound_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    0 ≤ matrixHilbertBound A :=
  le_csSup (matrixHilbertSet_bddAbove A) ⟨0, 0, by simp, by simp, by simp⟩

theorem matrixScalarBound_eval_le {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (s : Fin m → ℝ) (t : Fin n → ℝ) (hs : ∀ i, |s i| ≤ 1) (ht : ∀ j, |t j| ≤ 1) :
    |∑ i, ∑ j, A i j * (s i * t j)| ≤ matrixScalarBound A :=
  le_csSup (matrixScalarSet_bddAbove A) ⟨s, t, hs, ht, rfl⟩

theorem matrixHilbertBound_eval_le {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin (m + n)))
    (v : Fin n → EuclideanSpace ℝ (Fin (m + n)))
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) :
    |∑ i, ∑ j, A i j * inner ℝ (u i) (v j)| ≤ matrixHilbertBound A :=
  le_csSup (matrixHilbertSet_bddAbove A) ⟨u, v, hu, hv, rfl⟩

/-- The Euclidean supremum controls arbitrary real Hilbert spaces, including L². -/
theorem matrixHilbertBound_universal {m n : ℕ} (A : Fin m → Fin n → ℝ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : Fin m → H) (v : Fin n → H)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) :
    |∑ i, ∑ j, A i j * inner ℝ (u i) (v j)| ≤ matrixHilbertBound A := by
  let z := Fin.append u v
  let S := Submodule.span ℝ (Set.range z)
  have hzu (i : Fin m) : u i ∈ S := by
    apply Submodule.subset_span
    exact ⟨Fin.castAdd n i, Fin.append_left u v i⟩
  have hzv (j : Fin n) : v j ∈ S := by
    apply Submodule.subset_span
    exact ⟨Fin.natAdd m j, Fin.append_right u v j⟩
  obtain ⟨L⟩ := finiteHilbertCompression z
  let u' (i : Fin m) : EuclideanSpace ℝ (Fin (m + n)) := L ⟨u i, hzu i⟩
  let v' (j : Fin n) : EuclideanSpace ℝ (Fin (m + n)) := L ⟨v j, hzv j⟩
  have hu' (i : Fin m) : ‖u' i‖ ≤ 1 := by simpa [u'] using hu i
  have hv' (j : Fin n) : ‖v' j‖ ≤ 1 := by simpa [v'] using hv j
  have he (i : Fin m) (j : Fin n) : inner ℝ (u' i) (v' j) = inner ℝ (u i) (v j) := by
    exact L.inner_map_map ⟨u i, hzu i⟩ ⟨v j, hzv j⟩
  have h := matrixHilbertBound_eval_le A u' v' hu' hv'
  simpa only [he] using h

theorem matrixScalarBound_le_iff {m n : ℕ} (A : Fin m → Fin n → ℝ) (C : ℝ) :
    matrixScalarBound A ≤ C ↔ ∀ (s : Fin m → ℝ) (t : Fin n → ℝ),
      (∀ i, |s i| ≤ 1) → (∀ j, |t j| ≤ 1) → |∑ i, ∑ j, A i j * (s i * t j)| ≤ C := by
  constructor
  · intro h s t hs ht
    exact (matrixScalarBound_eval_le A s t hs ht).trans h
  · intro h
    apply csSup_le (matrixScalarSet_nonempty A)
    rintro r ⟨s, t, hs, ht, rfl⟩
    exact h s t hs ht

theorem matrixHilbertBound_le_iff {m n : ℕ} (A : Fin m → Fin n → ℝ) (C : ℝ) :
    matrixHilbertBound A ≤ C ↔
      ∀ (u : Fin m → EuclideanSpace ℝ (Fin (m + n)))
        (v : Fin n → EuclideanSpace ℝ (Fin (m + n))),
      (∀ i, ‖u i‖ ≤ 1) → (∀ j, ‖v j‖ ≤ 1) → |∑ i, ∑ j, A i j * inner ℝ (u i) (v j)| ≤ C := by
  constructor
  · intro h u v hu hv
    exact (matrixHilbertBound_eval_le A u v hu hv).trans h
  · intro h
    apply csSup_le (matrixHilbertSet_nonempty A)
    rintro r ⟨u, v, hu, hv, rfl⟩
    exact h u v hu hv

/-- Uniform norm bounds suffice; this formulation also covers empty families. -/
theorem matrixHilbertBound_scaled {m n : ℕ} (A : Fin m → Fin n → ℝ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : Fin m → H) (v : Fin n → H) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hu : ∀ i, ‖u i‖ ≤ α) (hv : ∀ j, ‖v j‖ ≤ β) :
    |∑ i, ∑ j, A i j * inner ℝ (u i) (v j)| ≤ matrixHilbertBound A * α * β := by
  by_cases ha : α = 0
  · have hz (i : Fin m) : u i = 0 :=
      norm_eq_zero.mp (le_antisymm (by simpa [ha] using hu i) (norm_nonneg _))
    simp [hz, ha]
  by_cases hb : β = 0
  · have hz (j : Fin n) : v j = 0 :=
      norm_eq_zero.mp (le_antisymm (by simpa [hb] using hv j) (norm_nonneg _))
    simp [hz, hb]
  have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm ha)
  have hβp : 0 < β := lt_of_le_of_ne hβ (Ne.symm hb)
  let u' := fun i => α⁻¹ • u i
  let v' := fun j => β⁻¹ • v j
  have hu' (i : Fin m) : ‖u' i‖ ≤ 1 := by
    dsimp [u']
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hαp)]
    exact (mul_le_mul_of_nonneg_left (hu i) (inv_nonneg.mpr hα)).trans_eq (inv_mul_cancel₀ ha)
  have hv' (j : Fin n) : ‖v' j‖ ≤ 1 := by
    dsimp [v']
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβp)]
    exact (mul_le_mul_of_nonneg_left (hv j) (inv_nonneg.mpr hβ)).trans_eq (inv_mul_cancel₀ hb)
  have he (i : Fin m) (j : Fin n) :
      inner ℝ (u i) (v j) = (α * β) * inner ℝ (u' i) (v' j) := by
    simp [u', v', inner_smul_left, inner_smul_right, ← mul_assoc, ha, hb]
  have hexpr : (∑ i, ∑ j, A i j * inner ℝ (u i) (v j)) =
      (α * β) * (∑ i, ∑ j, A i j * inner ℝ (u' i) (v' j)) := by
    simp_rw [he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpr, abs_mul, abs_of_nonneg (mul_nonneg hα hβ)]
  have h := mul_le_mul_of_nonneg_left (matrixHilbertBound_universal A u' v' hu' hv') (mul_nonneg hα hβ)
  nlinarith

theorem matrixScalarBound_scaled {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (s : Fin m → ℝ) (t : Fin n → ℝ) {M : ℝ} (hM : 0 < M)
    (hs : ∀ i, |s i| ≤ M) (ht : ∀ j, |t j| ≤ M) :
    |∑ i, ∑ j, A i j * (s i * t j)| ≤ M ^ 2 * matrixScalarBound A := by
  have hsn (i : Fin m) : |s i / M| ≤ 1 := by
    rw [abs_div, abs_of_pos hM, div_le_one hM]
    exact hs i
  have htn (j : Fin n) : |t j / M| ≤ 1 := by
    rw [abs_div, abs_of_pos hM, div_le_one hM]
    exact ht j
  have he : (∑ i, ∑ j, A i j * (s i * t j)) =
      M ^ 2 * (∑ i, ∑ j, A i j * ((s i / M) * (t j / M))) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg M)]
  exact mul_le_mul_of_nonneg_left (matrixScalarBound_eval_le A _ _ hsn htn) (sq_nonneg M)

/-- The scalar matrix estimate integrated over a probability space after clipping. -/
theorem integral_clipped_matrix_le {m n : ℕ} (A : Fin m → Fin n → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (U : Fin m → Ω → ℝ) (V : Fin n → Ω → ℝ)
    (hU : ∀ i, AEStronglyMeasurable (U i) ν) (hV : ∀ j, AEStronglyMeasurable (V j) ν)
    {M : ℝ} (hM : 0 < M) (hA : matrixScalarBound A ≤ 1) :
    Integrable (fun ω => ∑ i, ∑ j, A i j * (clip M (U i ω) * clip M (V j ω))) ν ∧
    |∫ ω, ∑ i, ∑ j, A i j * (clip M (U i ω) * clip M (V j ω)) ∂ν| ≤ M ^ 2 := by
  have hp (ω : Ω) : |∑ i, ∑ j, A i j * (clip M (U i ω) * clip M (V j ω))| ≤ M ^ 2 := by
    exact (matrixScalarBound_scaled A _ _ hM (fun i => clip_abs_le hM.le _)
      (fun j => clip_abs_le hM.le _)).trans
      (by nlinarith [sq_nonneg M])
  have hm : AEStronglyMeasurable
      (fun ω => ∑ i, ∑ j, A i j * (clip M (U i ω) * clip M (V j ω))) ν := by
    have hm' : AEStronglyMeasurable (∑ i, ∑ j, fun ω =>
        A i j * (clip M (U i ω) * clip M (V j ω))) ν := by
      apply Finset.aestronglyMeasurable_sum
      intro i _
      apply Finset.aestronglyMeasurable_sum
      intro j _
      exact (((continuous_clip M).comp_aestronglyMeasurable (hU i)).mul
        ((continuous_clip M).comp_aestronglyMeasurable (hV j))).const_mul (A i j)
    convert! hm' using 1
    funext ω
    simp only [Finset.sum_apply]
  constructor
  · exact ⟨hm, HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using hp ω)⟩
  · simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := ν)
        (f := fun ω => ∑ i, ∑ j, A i j * (clip M (U i ω) * clip M (V j ω)))
        (C := M ^ 2) (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using hp ω))

theorem realL2_inner_toLp {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {U V : Ω → ℝ} (hU : MemLp U 2 ν) (hV : MemLp V 2 ν) :
    inner ℝ (hU.toLp U) (hV.toLp V) = ∫ ω, U ω * V ω ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hU.coeFn_toLp, hV.coeFn_toLp] with ω hu hv
  simp [hu, hv, mul_comm]

theorem integral_matrix_toLp {m n : ℕ} (A : Fin m → Fin n → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (U : Fin m → Ω → ℝ) (V : Fin n → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 ν) (hV : ∀ j, MemLp (V j) 2 ν) :
    (∫ ω, ∑ i, ∑ j, A i j * (U i ω * V j ω) ∂ν) =
      ∑ i, ∑ j, A i j * inner ℝ ((hU i).toLp (U i)) ((hV j).toLp (V j)) := by
  have hint (i : Fin m) (j : Fin n) :
      Integrable (fun ω => A i j * (U i ω * V j ω)) ν :=
    ((hU i).integrable_mul (hV j)).const_mul _
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j), integral_const_mul,
    realL2_inner_toLp]

/-- The Gaussian truncation inequality, including both arbitrary-L² error families. -/
theorem matrixHilbertBound_truncation {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hA : matrixScalarBound A ≤ 1) {M : ℝ} (hM : 0 < M) :
    matrixHilbertBound A ≤ M ^ 2 + Real.sqrt 3 / (2 * M) * matrixHilbertBound A := by
  rw [matrixHilbertBound_le_iff]
  intro u v hu hv
  let U := fun i => gaussianLinear (u i)
  let V := fun j => gaussianLinear (v j)
  let hU := fun i => gaussianLinear_memLp (u i) 2 (by norm_num)
  let hV := fun j => gaussianLinear_memLp (v j) 2 (by norm_num)
  let uc := fun i => clipL2 (hU i) hM.le
  let vc := fun j => clipL2 (hV j) hM.le
  let ug := fun i => gaussianL2 (u i)
  let vg := fun j => gaussianL2 (v j)
  let P := ∑ i, ∑ j, A i j * inner ℝ (uc i) (vc j)
  let Q := ∑ i, ∑ j, A i j * inner ℝ (ug i - uc i) (vc j)
  let R := ∑ i, ∑ j, A i j * inner ℝ (ug i) (vg j - vc j)
  have huc (i : Fin m) : ‖uc i‖ ≤ 1 :=
    (clipL2_norm_le (hU i) hM.le).trans (by
      change ‖gaussianL2 (u i)‖ ≤ 1
      simpa only [gaussianL2_norm] using hu i)
  have hvc (j : Fin n) : ‖vc j‖ ≤ 1 :=
    (clipL2_norm_le (hV j) hM.le).trans (by
      change ‖gaussianL2 (v j)‖ ≤ 1
      simpa only [gaussianL2_norm] using hv j)
  have hue (i : Fin m) : ‖ug i - uc i‖ ≤ Real.sqrt 3 / (4 * M) :=
    clipL2_error_norm_le (hU i) (gaussianLinear_integrable_fourth (u i))
      (gaussianLinear_fourth_le_three (u i) (hu i)) hM
  have hve (j : Fin n) : ‖vg j - vc j‖ ≤ Real.sqrt 3 / (4 * M) :=
    clipL2_error_norm_le (hV j) (gaussianLinear_integrable_fourth (v j))
      (gaussianLinear_fourth_le_three (v j) (hv j)) hM
  have hP : |P| ≤ M ^ 2 := by
    have h := (integral_clipped_matrix_le A U V
      (fun i => (hU i).aestronglyMeasurable) (fun j => (hV j).aestronglyMeasurable) hM hA).2
    rw [integral_matrix_toLp A _ _ (fun i => clip_memLp (hU i) hM.le)
      (fun j => clip_memLp (hV j) hM.le)] at h
    exact h
  have hQ : |Q| ≤ matrixHilbertBound A * (Real.sqrt 3 / (4 * M)) := by
    simpa only [mul_one] using matrixHilbertBound_scaled A (fun i => ug i - uc i) vc
      (by positivity : 0 ≤ Real.sqrt 3 / (4 * M)) (by norm_num : (0 : ℝ) ≤ 1) hue hvc
  have hR : |R| ≤ matrixHilbertBound A * (Real.sqrt 3 / (4 * M)) := by
    simpa only [mul_one] using matrixHilbertBound_scaled A ug (fun j => vg j - vc j)
      (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ Real.sqrt 3 / (4 * M))
      (fun i => by simpa [ug, gaussianL2_norm] using hu i) hve
  have he : (∑ i, ∑ j, A i j * inner ℝ (u i) (v j)) = P + Q + R := by
    dsimp [P, Q, R]
    simp only [inner_sub_left, inner_sub_right, mul_sub, Finset.sum_sub_distrib]
    dsimp [ug, vg]
    simp_rw [gaussianL2_inner]
    ring
  rw [he]
  have ht : |P + Q + R| ≤ |P| + |Q| + |R| := by
    linarith [abs_add_le (P + Q) R, abs_add_le P Q]
  have hc : 2 * (matrixHilbertBound A * (Real.sqrt 3 / (4 * M))) =
      Real.sqrt 3 / (2 * M) * matrixHilbertBound A := by
    field_simp
    ring
  nlinarith

theorem matrixHilbertBound_le_of_scalar_le_one {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hA : matrixScalarBound A ≤ 1) : matrixHilbertBound A ≤ 81 / 16 := by
  exact truncation_absorption (fun M hM => matrixHilbertBound_truncation A hA hM)

theorem matrixScalarBound_entry_le {m n : ℕ} (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    |A i j| ≤ matrixScalarBound A := by
  classical
  have h := matrixScalarBound_eval_le A (fun k => if k = i then 1 else 0)
    (fun l => if l = j then 1 else 0) (fun k => by split_ifs <;> norm_num)
    (fun l => by split_ifs <;> norm_num)
  simpa [mul_ite, ite_mul] using h

theorem matrixScalarBound_eq_zero_iff {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    matrixScalarBound A = 0 ↔ ∀ i j, A i j = 0 := by
  constructor
  · intro h i j
    have he := matrixScalarBound_entry_le A i j
    rw [h] at he
    exact abs_eq_zero.mp (le_antisymm he (abs_nonneg _))
  · intro h
    apply le_antisymm _ (matrixScalarBound_nonneg A)
    rw [matrixScalarBound_le_iff]
    intro s t hs ht
    simp [h]

/-- Grothendieck's real matrix inequality, with the paper's Gaussian constant. -/
theorem grothendieck_matrix {m n : ℕ} (A : Fin m → Fin n → ℝ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : Fin m → H) (v : Fin n → H)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1) :
    |∑ i, ∑ j, A i j * inner ℝ (u i) (v j)| ≤ (81 / 16) * matrixScalarBound A := by
  by_cases hzero : matrixScalarBound A = 0
  · have hz := (matrixScalarBound_eq_zero_iff A).mp hzero
    simp [hz, hzero]
  have hp : 0 < matrixScalarBound A :=
    lt_of_le_of_ne (matrixScalarBound_nonneg A) (Ne.symm hzero)
  let A' := fun i j => A i j / matrixScalarBound A
  have hs : matrixScalarBound A' ≤ 1 := by
    rw [matrixScalarBound_le_iff]
    intro s t hs ht
    have he : (∑ i, ∑ j, A' i j * (s i * t j)) =
        (∑ i, ∑ j, A i j * (s i * t j)) / matrixScalarBound A := by
      simp only [A', div_mul_eq_mul_div, Finset.sum_div]
    rw [he, abs_div, abs_of_pos hp, div_le_one hp]
    exact matrixScalarBound_eval_le A s t hs ht
  have h := (matrixHilbertBound_universal A' u v hu hv).trans
    (matrixHilbertBound_le_of_scalar_le_one A' hs)
  have he : (∑ i, ∑ j, A' i j * inner ℝ (u i) (v j)) =
      (∑ i, ∑ j, A i j * inner ℝ (u i) (v j)) / matrixScalarBound A := by
    simp only [A', div_mul_eq_mul_div, Finset.sum_div]
  rw [he, abs_div, abs_of_pos hp] at h
  exact (div_le_iff₀ hp).mp h

end EvenOddHaarLevels
