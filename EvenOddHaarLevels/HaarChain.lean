import EvenOddHaarLevels.HaarMultiplier
import EvenOddHaarLevels.L1SequenceEquivalences
import EvenOddHaarLevels.HaarOffChainGeometry

noncomputable section
open MeasureTheory
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

def chainIndex (n : ℕ) : DyadicIndex := ⟨2*n,0⟩
def chainVector (n : ℕ) : (L1 𝕂) := (4 : 𝕂)^n • (haarL1 𝕂) (chainIndex n)

theorem chainIndex_measure (n : ℕ) : dyadicMeasure (chainIndex n) = ((4 : ℝ)^n)⁻¹ := by
  unfold dyadicMeasure chainIndex
  rw [pow_mul]
  norm_num

theorem chainVector_norm (n : ℕ) : ‖(chainVector (𝕂 := 𝕂)) n‖ = 1 := by
  rw [chainVector, norm_smul, (haar_norm (𝕂 := 𝕂)), chainIndex_measure, norm_pow, RCLike.norm_ofNat]
  exact mul_inv_cancel₀ (by positivity)

def chainSynthesis : Seq₁ 𝕂 →L[𝕂] (L1 𝕂) :=
  (lp.tsumCLM 𝕂 ℕ (L1 𝕂)).comp
    (lp.mapCLM 1 (fun n => (ContinuousLinearMap.id 𝕂 𝕂).smulRight ((chainVector (𝕂 := 𝕂)) n))
      (by norm_num : (0 : ℝ) ≤ 1) (fun n => by
        rw [ContinuousLinearMap.norm_smulRight_apply, (chainVector_norm (𝕂 := 𝕂))]
        simp))

theorem chainSynthesis_norm : ‖(chainSynthesis (𝕂 := 𝕂))‖ ≤ 1 := by
  apply le_trans (ContinuousLinearMap.opNorm_comp_le _ _) _
  have h1 := lp.norm_tsumCLM_le (𝕜 := 𝕂) (α := ℕ) (E := (L1 𝕂))
  have h2 := lp.norm_mapCLM_le 1
    (fun n => (ContinuousLinearMap.id 𝕂 𝕂).smulRight ((chainVector (𝕂 := 𝕂)) n))
    (by norm_num : (0 : ℝ) ≤ 1) (fun n => by
      rw [ContinuousLinearMap.norm_smulRight_apply, (chainVector_norm (𝕂 := 𝕂))]
      simp)
  nlinarith [norm_nonneg (lp.tsumCLM 𝕂 ℕ (L1 𝕂))]

@[simp] theorem chainSynthesis_single (n : ℕ) (a : 𝕂) :
    (chainSynthesis (𝕂 := 𝕂)) (lp.single 1 n a) = a • (chainVector (𝕂 := 𝕂)) n := by
  classical
  rw [chainSynthesis, ContinuousLinearMap.comp_apply, lp.tsumCLM_apply]
  have hfun : (fun k => (lp.mapCLM 1
      (fun n => (ContinuousLinearMap.id 𝕂 𝕂).smulRight ((chainVector (𝕂 := 𝕂)) n))
      (by norm_num : (0 : ℝ) ≤ 1) (fun n => by
        rw [ContinuousLinearMap.norm_smulRight_apply, (chainVector_norm (𝕂 := 𝕂))]; simp)
      (lp.single 1 n a)) k) = Pi.single n (a • (chainVector (𝕂 := 𝕂)) n) := by
    funext k
    change (lp.single 1 n a : Seq₁ 𝕂) k • (chainVector (𝕂 := 𝕂)) k = (Pi.single n (a • (chainVector (𝕂 := 𝕂)) n) : ℕ → (L1 𝕂)) k
    by_cases hk : k = n
    · subst k; simp []
    · simp [hk]
  rw [hfun, tsum_eq_single n]
  · simp
  · intro k hk
    simp [hk]

theorem chainIndex_interval (n : ℕ) :
    dyadicInterval (chainIndex n) = Set.Ico (0 : ℝ) (dyadicMeasure (chainIndex n)) := by
  simp [dyadicInterval,chainIndex,dyadicMeasure,one_div]

theorem chainIndex_next_measure (n : ℕ) :
    dyadicMeasure (chainIndex (n+1)) = dyadicMeasure (chainIndex n) / 4 := by
  rw [chainIndex_measure,chainIndex_measure,pow_succ,mul_inv_rev]
  ring

theorem chainIndex_nested {n m : ℕ} (h : n ≤ m) :
    dyadicInterval (chainIndex m) ⊆ dyadicInterval (chainIndex n) := by
  rw [chainIndex_interval,chainIndex_interval]
  have hp : (4 : ℝ)^n ≤ 4^m := pow_le_pow_right₀ (by norm_num) h
  have hi : dyadicMeasure (chainIndex m) ≤ dyadicMeasure (chainIndex n) := by
    rw [chainIndex_measure,chainIndex_measure]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hp
  intro x hx
  exact ⟨hx.1,lt_of_lt_of_le hx.2 hi⟩

theorem chainIndex_next_subset_left (n : ℕ) :
    dyadicInterval (chainIndex (n+1)) ⊆ haarLeft (chainIndex n) := by
  have he : haarLeft (chainIndex n) = Set.Ico (0 : ℝ) (dyadicMeasure (chainIndex n)/2) := by
    unfold haarLeft chainIndex dyadicMeasure
    simp only [Fin.val_zero,Nat.cast_zero,zero_div,zero_add]
    congr 1
    ring
  rw [chainIndex_interval,he,chainIndex_next_measure]
  intro x hx
  exact ⟨hx.1,lt_of_lt_of_le hx.2 (by have := (dyadicMeasure_pos (chainIndex n)).le; linarith)⟩

theorem chain_haar_earlier_on_cell {j n : ℕ} (hj : j < n) (k : Fin 3)
    {x : ℝ} (hx : x ∈ dyadicInterval (offChainCell (n,k))) :
    (haarFunction 𝕂) (chainIndex j) x = 1 := by
  have hsub := offChainCell_deeper_subset hj k hx
  have hi : x ∈ dyadicInterval (chainIndex (j+1)) := by
    exact hsub
  have hl := chainIndex_next_subset_left j hi
  have hr := Set.disjoint_left.mp (haar_halves_disjoint (chainIndex j)) hl
  simp [(haarFunction_eq (𝕂 := 𝕂)),hl,hr]

theorem chain_haar_later_on_cell {j n : ℕ} (hj : n < j) (k : Fin 3)
    {x : ℝ} (hx : x ∈ dyadicInterval (offChainCell (n,k))) :
    (haarFunction 𝕂) (chainIndex j) x = 0 := by
  have hsub := chainIndex_nested (by omega : n+1 ≤ j)
  have hd : Disjoint (dyadicInterval (offChainCell (n,k))) (dyadicInterval (chainIndex (n+1))) := by
    have he : chainIndex (n+1) = (⟨2*n+2,0⟩ : DyadicIndex) := rfl
    rw [he]
    apply dyadic_level_disjoint
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_zero] at hv
    omega
  exact (haarFunction_zero_off (𝕂 := 𝕂)) _ (fun hjx => Set.disjoint_left.mp hd hx (hsub hjx))

theorem haarFunction_on_quarter (I : DyadicIndex) (j : Fin 4) {x : ℝ}
    (hx : x ∈ dyadicInterval (dyadicQuarter I j)) :
    (haarFunction 𝕂) I x = if j.val < 2 then 1 else -1 := by
  have hp : (0 : ℝ) < 2^I.1 := by positivity
  have hp4 : (0 : ℝ) < 2^I.1*4 := by positivity
  have hl : (4 : ℝ)*(I.2 : ℝ)+(j : ℝ) ≤ x*(2^I.1*4) := by
    apply (div_le_iff₀ hp4).mp
    convert hx.1 using 1; simp [dyadicQuarter, pow_add]; ring
  have hu : x*(2^I.1*4) < (4 : ℝ)*(I.2 : ℝ)+(j : ℝ)+1 := by
    apply (lt_div_iff₀ hp4).mp
    convert hx.2 using 1; simp [dyadicQuarter, pow_add]; ring
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hj4 : (j : ℝ)+1 ≤ 4 := by exact_mod_cast j.isLt
  by_cases hj : j.val < 2
  · rw [if_pos hj]
    have hj2 : (j : ℝ)+1 ≤ 2 := by exact_mod_cast hj
    have hleft : x ∈ haarLeft I := by
      constructor
      · apply (div_le_iff₀ hp).mpr
        nlinarith
      · apply (lt_div_iff₀ hp).mpr
        nlinarith
    have hright := Set.disjoint_left.mp (haar_halves_disjoint I) hleft
    simp [(haarFunction_eq (𝕂 := 𝕂)),hleft,hright]
  · rw [if_neg hj]
    have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast (by omega : 2 ≤ j.val)
    have hright : x ∈ haarRight I := by
      constructor
      · apply (div_le_iff₀ hp).mpr
        nlinarith
      · apply (lt_div_iff₀ hp).mpr
        nlinarith
    have hleft := Set.disjoint_left.mp (haar_halves_disjoint I).symm hright
    simp [(haarFunction_eq (𝕂 := 𝕂)),hleft,hright]

theorem offChainCell_quarter (n : ℕ) (k : Fin 3) :
    offChainCell (n,k) = dyadicQuarter (chainIndex n) ⟨k.val+1,by have := k.isLt; omega⟩ := by
  apply Sigma.ext (show (offChainCell (n,k)).1 =
    (dyadicQuarter (chainIndex n) ⟨k.val+1,by have := k.isLt; omega⟩).1 from rfl)
  apply (Fin.heq_ext_iff rfl).mpr
  simp [offChainCell,dyadicQuarter,chainIndex]

theorem chain_haar_same_on_cell (n : ℕ) (k : Fin 3) {x : ℝ}
    (hx : x ∈ dyadicInterval (offChainCell (n,k))) :
    (haarFunction 𝕂) (chainIndex n) x = if k.val = 0 then 1 else -1 := by
  rw [offChainCell_quarter] at hx
  have hh := (haarFunction_on_quarter (𝕂 := 𝕂)) (chainIndex n) _ hx
  change (haarFunction 𝕂) (chainIndex n) x = (if k.val+1 < 2 then 1 else -1) at hh
  have hcond : k.val+1 < 2 ↔ k.val = 0 := by omega
  simpa only [hcond] using hh

end EvenOddHaarLevels
