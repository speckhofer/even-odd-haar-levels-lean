import EvenOddHaarLevels.Definitions

noncomputable section
open MeasureTheory
namespace EvenOddHaarLevels

instance : IsProbabilityMeasure unitIntervalMeasure := ⟨by simp [unitIntervalMeasure]⟩

def dyadicInterval (I : DyadicIndex) : Set ℝ :=
  Set.Ico ((I.2 : ℝ) / (2 : ℝ)^I.1) (((I.2 : ℝ)+1)/(2 : ℝ)^I.1)

def dyadicMeasure (I : DyadicIndex) : ℝ := ((2 : ℝ)^I.1)⁻¹

def dyadicChild (I : DyadicIndex) (j : Fin 2) : DyadicIndex :=
  ⟨I.1+1, ⟨2*I.2.val+j.val, by
    have := I.2.isLt
    have := j.isLt
    rw [pow_succ]
    omega⟩⟩

def dyadicQuarter (I : DyadicIndex) (j : Fin 4) : DyadicIndex :=
  ⟨I.1+2, ⟨4*I.2.val+j.val, by
    have := I.2.isLt
    have := j.isLt
    simp only [pow_add]
    norm_num
    omega⟩⟩

@[simp] theorem dyadicChild_level (I : DyadicIndex) (j : Fin 2) :
    (dyadicChild I j).1 = I.1+1 := rfl
@[simp] theorem dyadicQuarter_level (I : DyadicIndex) (j : Fin 4) :
    (dyadicQuarter I j).1 = I.1+2 := rfl
@[simp] theorem dyadicChild_position (I : DyadicIndex) (j : Fin 2) :
    (dyadicChild I j).2.val = 2*I.2.val+j.val := rfl
@[simp] theorem dyadicQuarter_position (I : DyadicIndex) (j : Fin 4) :
    (dyadicQuarter I j).2.val = 4*I.2.val+j.val := rfl

theorem dyadicMeasure_pos (I : DyadicIndex) : 0 < dyadicMeasure I := by
  unfold dyadicMeasure
  positivity

def dyadicRefinementEquiv (n r : ℕ) :
    Fin (2^(n+r)) ≃ Fin (2^n) × Fin (2^r) :=
  (finCongr (pow_add 2 n r)).trans finProdFinEquiv.symm

def dyadicQuarter_equiv (n : ℕ) :
    Fin (2^(n+2)) ≃ Fin (2^n) × Fin 4 :=
  dyadicRefinementEquiv n 2

theorem dyadic_refinement_sum {M : Type*} [AddCommMonoid M]
    (n r : ℕ) (f : Fin (2^(n+r)) → M) :
    ∑ k, f k = ∑ k : Fin (2^n), ∑ j : Fin (2^r),
      f ((dyadicRefinementEquiv n r).symm (k,j)) := by
  calc
    _ = ∑ p : Fin (2^n) × Fin (2^r), f ((dyadicRefinementEquiv n r).symm p) :=
      ((dyadicRefinementEquiv n r).symm.sum_comp f).symm
    _ = _ := Fintype.sum_prod_type _

theorem dyadicInterval_measurable (I : DyadicIndex) : MeasurableSet (dyadicInterval I) :=
  measurableSet_Ico

theorem dyadicInterval_subset_unit (I : DyadicIndex) :
    dyadicInterval I ⊆ Set.Ico (0 : ℝ) 1 := by
  have hp : (0 : ℝ) < 2^I.1 := by positivity
  have hk : (I.2 : ℝ)+1 ≤ (2 : ℝ)^I.1 := by
    exact_mod_cast I.2.isLt
  intro x hx
  exact ⟨le_trans (div_nonneg (by positivity) hp.le) hx.1,
    lt_of_lt_of_le hx.2 ((div_le_one hp).2 hk)⟩

theorem dyadicInterval_volume (I : DyadicIndex) :
    unitIntervalMeasure (dyadicInterval I) = ENNReal.ofReal (dyadicMeasure I) := by
  rw [unitIntervalMeasure, Measure.restrict_apply (dyadicInterval_measurable I),
    Set.inter_eq_left.mpr (dyadicInterval_subset_unit I), dyadicInterval, Real.volume_Ico]
  congr 1
  simp only [dyadicMeasure]
  ring

theorem dyadicInterval_real_measure (I : DyadicIndex) :
    unitIntervalMeasure.real (dyadicInterval I) = dyadicMeasure I := by
  rw [measureReal_def, dyadicInterval_volume, ENNReal.toReal_ofReal (dyadicMeasure_pos I).le]

theorem dyadic_level_disjoint (n : ℕ) {k l : Fin (2^n)} (h : k ≠ l) :
    Disjoint (dyadicInterval ⟨n,k⟩) (dyadicInterval ⟨n,l⟩) := by
  have hp : (0 : ℝ) < 2^n := by positivity
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hk : (k : ℝ) ≤ x*2^n := (div_le_iff₀ hp).mp hx.1
  have hk' : x*2^n < (k : ℝ)+1 := (lt_div_iff₀ hp).mp hx.2
  have hl : (l : ℝ) ≤ x*2^n := (div_le_iff₀ hp).mp hy.1
  have hl' : x*2^n < (l : ℝ)+1 := (lt_div_iff₀ hp).mp hy.2
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne h) with hkl | hlk
  · have : (k : ℝ)+1 ≤ (l : ℝ) := by exact_mod_cast hkl
    linarith
  · have : (l : ℝ)+1 ≤ (k : ℝ) := by exact_mod_cast hlk
    linarith

theorem dyadic_partition (n : ℕ) :
    (⋃ k : Fin (2^n), dyadicInterval ⟨n,k⟩) = Set.Ico (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun k => dyadicInterval_subset_unit ⟨n,k⟩
  · intro x hx
    have hp : (0 : ℝ) < 2^n := by positivity
    have hx0 : 0 ≤ x*2^n := mul_nonneg hx.1 hp.le
    have hk : ⌊x*2^n⌋₊ < 2^n := by
      apply (Nat.floor_lt hx0).2
      push_cast
      nlinarith [hx.2]
    apply Set.mem_iUnion.mpr
    refine ⟨⟨⌊x*2^n⌋₊,hk⟩, ?_⟩
    exact ⟨(div_le_iff₀ hp).2 (Nat.floor_le hx0),
      (lt_div_iff₀ hp).2 (Nat.lt_floor_add_one _)⟩

theorem dyadic_descendant_subset (n r : ℕ) (k : Fin (2^n)) (j : Fin (2^r)) :
    dyadicInterval ⟨n+r, (dyadicRefinementEquiv n r).symm (k,j)⟩ ⊆
      dyadicInterval ⟨n,k⟩ := by
  have hn : (0 : ℝ) < 2^n := by positivity
  have hr : (0 : ℝ) < 2^r := by positivity
  have hj : (j : ℝ)+1 ≤ (2 : ℝ)^r := by exact_mod_cast j.isLt
  intro x hx
  have hval : (((dyadicRefinementEquiv n r).symm (k,j) : Fin (2^(n+r))) : ℝ) =
      (j : ℝ) + (2 : ℝ)^r*(k : ℝ) := by
    simp [dyadicRefinementEquiv, finProdFinEquiv]
  change (k : ℝ)/2^n ≤ x ∧ x < ((k : ℝ)+1)/2^n
  change _ ≤ x ∧ x < _ at hx
  rw [hval, pow_add] at hx
  constructor
  · apply (div_le_iff₀ hn).2
    have := (div_le_iff₀ (mul_pos hn hr)).mp hx.1
    have hj0 : (0 : ℝ) ≤ j := by positivity
    nlinarith
  · apply (lt_div_iff₀ hn).2
    have := (lt_div_iff₀ (mul_pos hn hr)).mp hx.2
    nlinarith

def dyadicAncestor (I : DyadicIndex) (n : ℕ) (h : n ≤ I.1) : DyadicIndex :=
  ⟨n, (dyadicRefinementEquiv n (I.1-n) (Fin.cast (by congr 1; omega) I.2)).1⟩

theorem dyadicAncestor_contains (I : DyadicIndex) (n : ℕ) (h : n ≤ I.1) :
    dyadicInterval I ⊆ dyadicInterval (dyadicAncestor I n h) := by
  let p := dyadicRefinementEquiv n (I.1-n) (Fin.cast (by congr 1; omega) I.2)
  have hd := dyadic_descendant_subset n (I.1-n) p.1 p.2
  have hi : (⟨n+(I.1-n), (dyadicRefinementEquiv n (I.1-n)).symm (p.1,p.2)⟩ : DyadicIndex) = I := by
    change (⟨n+(I.1-n), (dyadicRefinementEquiv n (I.1-n)).symm
      (dyadicRefinementEquiv n (I.1-n) (Fin.cast _ I.2))⟩ : DyadicIndex) = I
    rw [Equiv.symm_apply_apply]
    apply Sigma.ext (Nat.add_sub_of_le h)
    exact (Fin.heq_ext_iff (by dsimp; congr 1; omega)).mpr rfl
  rw [hi] at hd
  exact hd

theorem dyadic_nested_or_disjoint (I J : DyadicIndex) :
    Disjoint (dyadicInterval I) (dyadicInterval J) ∨
    dyadicInterval I ⊆ dyadicInterval J ∨ dyadicInterval J ⊆ dyadicInterval I := by
  wlog h : I.1 ≤ J.1 generalizing I J
  · have hh := this J I (by omega)
    rcases hh with hd | hs | hs
    · exact Or.inl hd.symm
    · exact Or.inr (Or.inr hs)
    · exact Or.inr (Or.inl hs)
  let A := dyadicAncestor J I.1 h
  have hs := dyadicAncestor_contains J I.1 h
  by_cases he : A.2 = I.2
  · right; right
    have : A = I := by exact Sigma.ext rfl (heq_of_eq he)
    rwa [← this]
  · left
    exact (dyadic_level_disjoint I.1 (Ne.symm he)).mono_right hs

theorem dyadicChild_child (I : DyadicIndex) (a b : Fin 2) :
    dyadicChild (dyadicChild I a) b =
      dyadicQuarter I ⟨2*a.val+b.val, by have := a.isLt; have := b.isLt; omega⟩ := by
  apply Sigma.ext (show (dyadicChild (dyadicChild I a) b).1 =
    (dyadicQuarter I ⟨2*a.val+b.val, by have := a.isLt; have := b.isLt; omega⟩).1 from rfl)
  apply (Fin.heq_ext_iff rfl).mpr
  simp only [dyadicChild_position, dyadicQuarter_position]
  omega

theorem dyadicQuarter_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (g : DyadicIndex → M) :
    ∑ k : Fin (2^(n+2)), g ⟨n+2,k⟩ =
      ∑ k : Fin (2^n), ∑ j : Fin 4, g (dyadicQuarter ⟨n,k⟩ j) := by
  rw [dyadic_refinement_sum n 2]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Sigma.ext (show n+2 = (dyadicQuarter ⟨n,k⟩ j).1 from rfl)
  apply (Fin.heq_ext_iff rfl).mpr
  simp [dyadicRefinementEquiv, finProdFinEquiv, dyadicQuarter, Nat.add_comm]

theorem dyadicChild_sum {M : Type*} [AddCommMonoid M] (n : ℕ) (g : DyadicIndex → M) :
    ∑ k : Fin (2^(n+1)), g ⟨n+1,k⟩ =
      ∑ k : Fin (2^n), ∑ j : Fin 2, g (dyadicChild ⟨n,k⟩ j) := by
  rw [dyadic_refinement_sum n 1]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Sigma.ext (show n+1 = (dyadicChild ⟨n,k⟩ j).1 from rfl)
  apply (Fin.heq_ext_iff rfl).mpr
  simp [dyadicRefinementEquiv, finProdFinEquiv, dyadicChild, Nat.add_comm]

end EvenOddHaarLevels
