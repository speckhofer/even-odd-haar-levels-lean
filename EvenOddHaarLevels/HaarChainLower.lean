import EvenOddHaarLevels.HaarChain

noncomputable section
open MeasureTheory
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

def chainFiniteFunction (F : Finset ℕ) (c : ℕ → 𝕂) : ℝ → 𝕂 :=
  fun x => ∑ j ∈ F, (c j * (4 : 𝕂)^j) * (haarFunction 𝕂) (chainIndex j) x

def chainBefore (F : Finset ℕ) (c : ℕ → 𝕂) (n : ℕ) : 𝕂 :=
  ∑ j ∈ F, if j < n then c j * (4 : 𝕂)^j else 0

theorem chainFiniteFunction_integrable (F : Finset ℕ) (c : ℕ → 𝕂) :
    Integrable ((chainFiniteFunction (𝕂 := 𝕂)) F c) unitIntervalMeasure :=
  integrable_finsetSum F (fun j _ => (haarFunction_integrable 𝕂 (chainIndex j)).const_mul _)

theorem chainFiniteFunction_value (F : Finset ℕ) (c : ℕ → 𝕂) (n : ℕ) (hn : n ∈ F)
    (k : Fin 3) {x : ℝ} (hx : x ∈ dyadicInterval (offChainCell (n,k))) :
    (chainFiniteFunction (𝕂 := 𝕂)) F c x = (chainBefore (𝕂 := 𝕂)) F c n +
      (c n * (4 : 𝕂)^n) * (if k.val = 0 then 1 else -1) := by
  classical
  calc
    _ = ∑ j ∈ F, ((if j < n then c j * (4 : 𝕂)^j else 0) +
        (if j = n then (c n * (4 : 𝕂)^n) * (if k.val = 0 then 1 else -1) else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j < n
      · rw [(chain_haar_earlier_on_cell (𝕂 := 𝕂)) hj k hx]
        simp [hj,show j ≠ n by omega]
      · by_cases he : j = n
        · subst j
          rw [(chain_haar_same_on_cell (𝕂 := 𝕂)) n k hx]
          simp
        · rw [(chain_haar_later_on_cell (𝕂 := 𝕂)) (by omega : n < j) k hx]
          simp [hj,he]
    _ = _ := by rw [Finset.sum_add_distrib]; simp [chainBefore,hn]

theorem offChainCell_chain_measure (n : ℕ) (k : Fin 3) :
    dyadicMeasure (offChainCell (n,k)) = ((4 : ℝ)^n)⁻¹ / 4 := by
  change ((2 : ℝ)^(2*n+2))⁻¹ = _
  rw [pow_add,pow_mul]
  norm_num
  ring

theorem chainFinite_cell_integral (F : Finset ℕ) (c : ℕ → 𝕂) (n : ℕ) (hn : n ∈ F)
    (k : Fin 3) :
    (∫ x in dyadicInterval (offChainCell (n,k)), ‖(chainFiniteFunction (𝕂 := 𝕂)) F c x‖ ∂unitIntervalMeasure) =
      (((4 : ℝ)^n)⁻¹/4) * ‖(chainBefore (𝕂 := 𝕂)) F c n + (c n * (4 : 𝕂)^n) * (if k.val = 0 then 1 else -1)‖ := by
  calc
    _ = ∫ _ in dyadicInterval (offChainCell (n,k)),
        ‖(chainBefore (𝕂 := 𝕂)) F c n + (c n * (4 : 𝕂)^n) * (if k.val = 0 then 1 else -1)‖ ∂unitIntervalMeasure := by
      apply setIntegral_congr_fun (dyadicInterval_measurable _)
      intro x hx
      change ‖(chainFiniteFunction (𝕂 := 𝕂)) F c x‖ = _
      rw [(chainFiniteFunction_value (𝕂 := 𝕂)) F c n hn k hx]
    _ = _ := by rw [setIntegral_const,dyadicInterval_real_measure,offChainCell_chain_measure,smul_eq_mul]

theorem chainFinite_local_lower (F : Finset ℕ) (c : ℕ → 𝕂) (n : ℕ) (hn : n ∈ F) :
    ‖c n‖ ≤ 2 * ((∫ x in dyadicInterval (offChainCell (n,0)), ‖(chainFiniteFunction (𝕂 := 𝕂)) F c x‖ ∂unitIntervalMeasure) +
      ∫ x in dyadicInterval (offChainCell (n,1)), ‖(chainFiniteFunction (𝕂 := 𝕂)) F c x‖ ∂unitIntervalMeasure) := by
  rw [(chainFinite_cell_integral (𝕂 := 𝕂)) F c n hn 0,(chainFinite_cell_integral (𝕂 := 𝕂)) F c n hn 1]
  simp only [Fin.val_zero,Fin.val_one,one_ne_zero,ite_true,ite_false,mul_one,mul_neg,← sub_eq_add_neg]
  have ht := norm_sub_le ((chainBefore (𝕂 := 𝕂)) F c n + c n * (4 : 𝕂)^n) ((chainBefore (𝕂 := 𝕂)) F c n - c n * (4 : 𝕂)^n)
  have he : ((chainBefore (𝕂 := 𝕂)) F c n + c n * (4 : 𝕂)^n) -
      ((chainBefore (𝕂 := 𝕂)) F c n - c n * (4 : 𝕂)^n) = 2*(c n * (4 : 𝕂)^n) := by ring
  rw [he,norm_mul] at ht
  simp only [norm_mul, norm_pow, RCLike.norm_ofNat] at ht
  have hp : (0 : ℝ) < 4^n := by positivity
  have halg : 2 * (((4 : ℝ)^n)⁻¹/4 * ‖(chainBefore (𝕂 := 𝕂)) F c n + c n * (4 : 𝕂)^n‖ +
      ((4 : ℝ)^n)⁻¹/4 * ‖(chainBefore (𝕂 := 𝕂)) F c n - c n * (4 : 𝕂)^n‖) =
      (‖(chainBefore (𝕂 := 𝕂)) F c n + c n * (4 : 𝕂)^n‖ + ‖(chainBefore (𝕂 := 𝕂)) F c n - c n * (4 : 𝕂)^n‖) / (2*(4 : ℝ)^n) := by
    field_simp
    ring
  rw [halg]
  apply (le_div_iff₀ (show (0 : ℝ) < 2*4^n by positivity)).mpr
  nlinarith


theorem finite_disjoint_setIntegral_sum_le {ι : Type*} [Fintype ι]
    (D : ι → Set ℝ) (hm : ∀ i, MeasurableSet (D i))
    (hd : Pairwise (fun i j => Disjoint (D i) (D j)))
    (u : ℝ → ℝ) (hu : Integrable u unitIntervalMeasure) (hu0 : ∀ x, 0 ≤ u x) :
    (∑ i, ∫ x in D i, u x ∂unitIntervalMeasure) ≤ ∫ x, u x ∂unitIntervalMeasure := by
  classical
  simp_rw [← integral_indicator (hm _)]
  rw [← integral_finsetSum _ (fun i _ => hu.indicator (hm i))]
  apply integral_mono (integrable_finsetSum _ (fun i _ => hu.indicator (hm i))) hu
  intro x
  change (∑ i, (D i).indicator u x) ≤ u x
  by_cases hx : ∃ i, x ∈ D i
  · obtain ⟨i,hi⟩ := hx
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hj : x ∉ D j := Set.disjoint_left.mp (hd (Ne.symm hji)) hi
      simp [hj]
    · simp
  · have hz : ∀ i, x ∉ D i := by simpa using hx
    simpa [hz] using hu0 x

theorem chainFinite_norm_integral (F : Finset ℕ) (c : ℕ → 𝕂) :
    ‖∑ n ∈ F, c n • (chainVector (𝕂 := 𝕂)) n‖ = ∫ x, ‖(chainFiniteFunction (𝕂 := 𝕂)) F c x‖ ∂unitIntervalMeasure := by
  have ht : ∀ᵐ x ∂unitIntervalMeasure, ∀ n : ℕ,
      (c n • (chainVector (𝕂 := 𝕂)) n : (L1 𝕂)) x = (c n * (4 : 𝕂)^n) * (haarFunction 𝕂) (chainIndex n) x := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [Lp.coeFn_smul (c n) ((chainVector (𝕂 := 𝕂)) n),
      Lp.coeFn_smul ((4 : 𝕂)^n) ((haarL1 𝕂) (chainIndex n)), (haarL1_ae (𝕂 := 𝕂)) (chainIndex n)] with x hc hv hh
    rw [hc]
    change c n * (chainVector (𝕂 := 𝕂)) n x = _
    rw [show (chainVector (𝕂 := 𝕂)) n x = (4 : 𝕂)^n * (haarL1 𝕂) (chainIndex n) x from hv]
    rw [hh]
    ring
  rw [MeasureTheory.L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_finsetSum F (fun n => c n • (chainVector (𝕂 := 𝕂)) n),ht] with x hs ht
  rw [hs]
  simp only [Finset.sum_apply,chainFiniteFunction]
  congr 1
  exact Finset.sum_congr rfl (fun n _ => ht n)

theorem chainFinite_lower (F : Finset ℕ) (c : ℕ → 𝕂) :
    (∑ n ∈ F, ‖c n‖) ≤ 2 * ‖∑ n ∈ F, c n • (chainVector (𝕂 := 𝕂)) n‖ := by
  classical
  let e : F × Fin 2 → OffChainAddress := fun p => (p.1.val, Fin.castLE (by decide : 2 ≤ 3) p.2)
  have he : Function.Injective e := by
    intro p q h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · apply Fin.ext
      exact congrArg (fun p : OffChainAddress => p.2.val) h
  have hpart := finite_disjoint_setIntegral_sum_le
    (fun p : F × Fin 2 => dyadicInterval (offChainCell (e p)))
    (fun _ => dyadicInterval_measurable _)
    (fun p q hpq => offChainCell_disjoint (fun hp => hpq (he hp)))
    (fun x => ‖(chainFiniteFunction (𝕂 := 𝕂)) F c x‖) ((chainFiniteFunction_integrable (𝕂 := 𝕂)) F c).norm (fun _ => norm_nonneg _)
  calc
    _ ≤ ∑ n ∈ F, 2 * ((∫ x in dyadicInterval (offChainCell (n,0)), ‖(chainFiniteFunction (𝕂 := 𝕂)) F c x‖ ∂unitIntervalMeasure) +
        ∫ x in dyadicInterval (offChainCell (n,1)), ‖(chainFiniteFunction (𝕂 := 𝕂)) F c x‖ ∂unitIntervalMeasure) :=
      Finset.sum_le_sum (fun n hn => (chainFinite_local_lower (𝕂 := 𝕂)) F c n hn)
    _ = 2 * ∑ p : F × Fin 2, ∫ x in dyadicInterval (offChainCell (e p)), ‖(chainFiniteFunction (𝕂 := 𝕂)) F c x‖ ∂unitIntervalMeasure := by
      rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_two]
      rw [Finset.mul_sum]
      let b : ℕ → ℝ := fun n =>
        (∫ x in dyadicInterval (offChainCell (n,0)), ‖(chainFiniteFunction (𝕂 := 𝕂)) F c x‖ ∂unitIntervalMeasure) +
        ∫ x in dyadicInterval (offChainCell (n,1)), ‖(chainFiniteFunction (𝕂 := 𝕂)) F c x‖ ∂unitIntervalMeasure
      change (∑ n ∈ F, 2 * b n) = ∑ i : F, 2 * b i.val
      exact (Finset.sum_coe_sort F (fun n => 2 * b n)).symm
    _ ≤ 2 * ∫ x, ‖(chainFiniteFunction (𝕂 := 𝕂)) F c x‖ ∂unitIntervalMeasure :=
      mul_le_mul_of_nonneg_left hpart (by norm_num)
    _ = _ := by rw [(chainFinite_norm_integral (𝕂 := 𝕂))]

end EvenOddHaarLevels
