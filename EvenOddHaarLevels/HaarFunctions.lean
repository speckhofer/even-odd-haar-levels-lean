import EvenOddHaarLevels.DyadicIndex

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

def haarLeft (I : DyadicIndex) : Set ℝ :=
  Set.Ico ((I.2 : ℝ)/(2 : ℝ)^I.1) (((I.2 : ℝ)+1/2)/(2 : ℝ)^I.1)
def haarRight (I : DyadicIndex) : Set ℝ :=
  Set.Ico (((I.2 : ℝ)+1/2)/(2 : ℝ)^I.1) (((I.2 : ℝ)+1)/(2 : ℝ)^I.1)

theorem haar_halves_disjoint (I : DyadicIndex) : Disjoint (haarLeft I) (haarRight I) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (not_lt_of_ge hy.1) hx.2

theorem haar_halves_union (I : DyadicIndex) : haarLeft I ∪ haarRight I = dyadicInterval I := by
  have hp : (0 : ℝ) < 2^I.1 := by positivity
  apply Set.Ico_union_Ico_eq_Ico <;> apply (div_le_div_iff_of_pos_right hp).2 <;> linarith

theorem haarLeft_subset (I : DyadicIndex) : haarLeft I ⊆ dyadicInterval I := by
  rw [← haar_halves_union]
  exact Set.subset_union_left

theorem haarRight_subset (I : DyadicIndex) : haarRight I ⊆ dyadicInterval I := by
  rw [← haar_halves_union]
  exact Set.subset_union_right

theorem haar_halves_measure (I : DyadicIndex) :
    unitIntervalMeasure.real (haarLeft I) = dyadicMeasure I / 2 ∧
    unitIntervalMeasure.real (haarRight I) = dyadicMeasure I / 2 := by
  have hp : (0 : ℝ) < 2^I.1 := by positivity
  have hs (s : Set ℝ) (hm : MeasurableSet s) (h : s ⊆ dyadicInterval I) :
      unitIntervalMeasure.real s = volume.real s := by
    rw [unitIntervalMeasure, measureReal_restrict_apply hm,
      Set.inter_eq_left.mpr (h.trans (dyadicInterval_subset_unit I))]
  constructor
  · rw [hs (haarLeft I) measurableSet_Ico (haarLeft_subset I), haarLeft, measureReal_def,
      Real.volume_Ico, ENNReal.toReal_ofReal (by apply sub_nonneg.mpr; apply (div_le_div_iff_of_pos_right hp).2; linarith)]
    simp only [dyadicMeasure]
    ring
  · rw [hs (haarRight I) measurableSet_Ico (haarRight_subset I), haarRight, measureReal_def,
      Real.volume_Ico, ENNReal.toReal_ofReal (by apply sub_nonneg.mpr; apply (div_le_div_iff_of_pos_right hp).2; linarith)]
    simp only [dyadicMeasure]
    ring

theorem haarFunction_eq (I : DyadicIndex) :
    (haarFunction 𝕂) I = (haarLeft I).indicator (fun _ => 1) -
      (haarRight I).indicator (fun _ => 1) := rfl

theorem haarFunction_measurable (I : DyadicIndex) : Measurable ((haarFunction 𝕂) I) :=
  (measurable_const.indicator measurableSet_Ico).sub
    (measurable_const.indicator measurableSet_Ico)

theorem haarFunction_abs (I : DyadicIndex) (x : ℝ) :
    ‖(haarFunction 𝕂) I x‖ = (dyadicInterval I).indicator (fun _ => 1) x := by
  rw [(haarFunction_eq (𝕂 := 𝕂)), ← haar_halves_union]
  have hd := Set.disjoint_left.mp (haar_halves_disjoint I)
  by_cases hl : x ∈ haarLeft I
  · have hr := hd hl
    simp [hl, hr]
  · by_cases hr : x ∈ haarRight I <;> simp [hl, hr]

theorem haarFunction_abs_le_one (I : DyadicIndex) (x : ℝ) : ‖(haarFunction 𝕂) I x‖ ≤ 1 := by
  rw [(haarFunction_abs (𝕂 := 𝕂))]
  by_cases h : x ∈ dyadicInterval I <;> simp [h]

theorem haarFunction_memLp (I : DyadicIndex) (p : ℝ≥0∞) :
    MemLp ((haarFunction 𝕂) I) p unitIntervalMeasure :=
  MemLp.of_bound ((haarFunction_measurable (𝕂 := 𝕂)) I).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using (haarFunction_abs_le_one (𝕂 := 𝕂)) I x)

abbrev L2 := MeasureTheory.Lp 𝕂 2 unitIntervalMeasure

def haarL2 (I : DyadicIndex) : (L2 (𝕂 := 𝕂)) := ((haarFunction_memLp (𝕂 := 𝕂)) I 2).toLp ((haarFunction 𝕂) I)

theorem haarL1_ae (I : DyadicIndex) : ((haarL1 𝕂) I : ℝ → 𝕂) =ᵐ[unitIntervalMeasure] (haarFunction 𝕂) I :=
  (haarFunction_integrable 𝕂 I).coeFn_toL1

theorem haarL2_ae (I : DyadicIndex) : ((haarL2 (𝕂 := 𝕂)) I : ℝ → 𝕂) =ᵐ[unitIntervalMeasure] (haarFunction 𝕂) I :=
  ((haarFunction_memLp (𝕂 := 𝕂)) I 2).coeFn_toLp

theorem haar_integral (I : DyadicIndex) : ∫ x, (haarFunction 𝕂) I x ∂unitIntervalMeasure = 0 := by
  simp only [(haarFunction_eq (𝕂 := 𝕂)), Pi.sub_apply]
  have hl : Integrable ((haarLeft I).indicator (fun _ => (1 : 𝕂))) unitIntervalMeasure :=
    (integrable_const 1).indicator measurableSet_Ico
  have hr : Integrable ((haarRight I).indicator (fun _ => (1 : 𝕂))) unitIntervalMeasure :=
    (integrable_const 1).indicator measurableSet_Ico
  rw [integral_sub hl hr]
  rw [integral_indicator (show MeasurableSet (haarLeft I) from measurableSet_Ico),
    integral_indicator (show MeasurableSet (haarRight I) from measurableSet_Ico)]
  simp only [integral_const, measureReal_restrict_apply_univ]
  rw [(haar_halves_measure I).1, (haar_halves_measure I).2, sub_self]

theorem haar_norm (I : DyadicIndex) : ‖(haarL1 𝕂) I‖ = dyadicMeasure I := by
  rw [MeasureTheory.L1.norm_eq_integral_norm]
  calc
    _ = ∫ x, ‖(haarFunction 𝕂) I x‖ ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [(haarL1_ae (𝕂 := 𝕂)) I] with x hx
      simp [hx]
    _ = ∫ x, (dyadicInterval I).indicator (fun _ => (1 : ℝ)) x ∂unitIntervalMeasure := by
      congr 1
      funext x
      exact (haarFunction_abs (𝕂 := 𝕂)) I x
    _ = _ := by
      rw [integral_indicator_const (1 : ℝ) (dyadicInterval_measurable I)]
      simpa using dyadicInterval_real_measure I

theorem haarFunction_sq (I : DyadicIndex) (x : ℝ) :
    (haarFunction 𝕂) I x ^ 2 = (dyadicInterval I).indicator (fun _ => 1) x := by
  rw [(haarFunction_eq (𝕂 := 𝕂)), ← haar_halves_union]
  have hd := Set.disjoint_left.mp (haar_halves_disjoint I)
  by_cases hl : x ∈ haarLeft I
  · have hr := hd hl
    simp [hl, hr]
  · by_cases hr : x ∈ haarRight I <;> simp [hl, hr]

@[simp] theorem haarFunction_conj (I : DyadicIndex) (x : ℝ) :
    star ((haarFunction 𝕂) I x) = (haarFunction 𝕂) I x := by
  rw [(haarFunction_eq (𝕂 := 𝕂))]
  by_cases hl : x ∈ haarLeft I <;> by_cases hr : x ∈ haarRight I <;> simp [hl, hr]

theorem haarL2_norm_sq (I : DyadicIndex) : ‖(haarL2 (𝕂 := 𝕂)) I‖^2 = dyadicMeasure I := by
  rw [← @inner_self_eq_norm_sq 𝕂, MeasureTheory.L2.inner_def, ← integral_re (MeasureTheory.L2.integrable_inner ..)]
  simp_rw [inner_self_eq_norm_sq]
  calc
    _ = ∫ x, ‖(haarFunction 𝕂) I x‖ ^ 2 ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [(haarL2_ae (𝕂 := 𝕂)) I] with x hx
      rw [hx]
    _ = ∫ x, (dyadicInterval I).indicator (fun _ => (1 : ℝ)) x ∂unitIntervalMeasure := by
      congr 1
      funext x
      rw [(haarFunction_abs (𝕂 := 𝕂))]
      by_cases hx : x ∈ dyadicInterval I <;> simp [hx]
    _ = _ := by
      rw [integral_indicator_const (1 : ℝ) (dyadicInterval_measurable I)]
      simpa using dyadicInterval_real_measure I

theorem haarLeft_child (I : DyadicIndex) :
    haarLeft I = dyadicInterval (dyadicChild I 0) := by
  unfold haarLeft dyadicInterval dyadicChild
  simp only [Nat.cast_mul, Nat.cast_ofNat, add_zero,
    Fin.val_zero, pow_succ]
  congr 1 <;> field_simp

theorem haarRight_child (I : DyadicIndex) :
    haarRight I = dyadicInterval (dyadicChild I 1) := by
  unfold haarRight dyadicInterval dyadicChild
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Fin.val_one, pow_succ]
  (congr 1 <;> field_simp); ring

theorem haarFunction_zero_off (I : DyadicIndex) {x : ℝ} (hx : x ∉ dyadicInterval I) :
    (haarFunction 𝕂) I x = 0 := by
  have h := (haarFunction_abs (𝕂 := 𝕂)) I x
  rw [Set.indicator_of_notMem hx] at h
  exact norm_eq_zero.mp h

theorem haar_constant_on_deeper (I J : DyadicIndex) (h : I.1 < J.1) :
    ∃ c : 𝕂, ∀ x ∈ dyadicInterval J, (haarFunction 𝕂) I x = c := by
  let A := dyadicAncestor J (I.1+1) h
  have hs : dyadicInterval J ⊆ dyadicInterval A := dyadicAncestor_contains J _ h
  by_cases h0 : A.2 = (dyadicChild I 0).2
  · have he : A = dyadicChild I 0 := by
      exact Sigma.ext (show A.1 = (dyadicChild I 0).1 from rfl) (heq_of_eq h0)
    refine ⟨1, fun x hx => ?_⟩
    have hl : x ∈ haarLeft I := by rw [haarLeft_child, ← he]; exact hs hx
    have hr := Set.disjoint_left.mp (haar_halves_disjoint I) hl
    simp [(haarFunction_eq (𝕂 := 𝕂)), hl, hr]
  · by_cases h1 : A.2 = (dyadicChild I 1).2
    · have he : A = dyadicChild I 1 := by
        exact Sigma.ext (show A.1 = (dyadicChild I 1).1 from rfl) (heq_of_eq h1)
      refine ⟨-1, fun x hx => ?_⟩
      have hr : x ∈ haarRight I := by rw [haarRight_child, ← he]; exact hs hx
      have hl := Set.disjoint_left.mp (haar_halves_disjoint I).symm hr
      simp [(haarFunction_eq (𝕂 := 𝕂)), hl, hr]
    · refine ⟨0, fun x hx => ?_⟩
      have hl : x ∉ haarLeft I := by
        rw [haarLeft_child]
        exact Set.disjoint_left.mp (dyadic_level_disjoint (I.1+1) h0) (hs hx)
      have hr : x ∉ haarRight I := by
        rw [haarRight_child]
        exact Set.disjoint_left.mp (dyadic_level_disjoint (I.1+1) h1) (hs hx)
      simp [(haarFunction_eq (𝕂 := 𝕂)), hl, hr]

theorem haar_cross_integral (I J : DyadicIndex) (h : I ≠ J) :
    ∫ x, (haarFunction 𝕂) I x * (haarFunction 𝕂) J x ∂unitIntervalMeasure = 0 := by
  wlog hlev : I.1 ≤ J.1 generalizing I J
  · have hh := this J I (Ne.symm h) (by omega)
    simpa only [mul_comm] using hh
  rcases eq_or_lt_of_le hlev with he | hl
  · have hd : Disjoint (dyadicInterval I) (dyadicInterval J) := by
      cases I with | mk n k =>
        cases J with | mk m l =>
          dsimp at he
          subst m
          apply dyadic_level_disjoint
          intro hk
          apply h
          cases hk
          rfl
    have hf : (fun x => (haarFunction 𝕂) I x * (haarFunction 𝕂) J x) = fun _ => 0 := by
      funext x
      by_cases hx : x ∈ dyadicInterval I
      · rw [(haarFunction_zero_off (𝕂 := 𝕂)) J (Set.disjoint_left.mp hd hx), mul_zero]
      · rw [(haarFunction_zero_off (𝕂 := 𝕂)) I hx, zero_mul]
    rw [hf, integral_zero]
  · obtain ⟨c,hc⟩ := (haar_constant_on_deeper (𝕂 := 𝕂)) I J hl
    have hf : (fun x => (haarFunction 𝕂) I x * (haarFunction 𝕂) J x) = fun x => c * (haarFunction 𝕂) J x := by
      funext x
      by_cases hx : x ∈ dyadicInterval J
      · rw [hc x hx]
      · rw [(haarFunction_zero_off (𝕂 := 𝕂)) J hx, mul_zero, mul_zero]
    rw [hf, integral_const_mul, (haar_integral (𝕂 := 𝕂)), mul_zero]

end EvenOddHaarLevels
