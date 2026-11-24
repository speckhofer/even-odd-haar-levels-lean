import EvenOddHaarLevels.HaarCoefficients

noncomputable section
open MeasureTheory
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

def cellL1 (I : DyadicIndex) : (L1 𝕂) :=
  indicatorConstLp 1 (dyadicInterval_measurable I) (measure_ne_top _ _) (1 : 𝕂)

theorem cellL1_ae (I : DyadicIndex) :
    ((cellL1 (𝕂 := 𝕂)) I : ℝ → 𝕂) =ᵐ[unitIntervalMeasure] (dyadicInterval I).indicator (fun _ => 1) :=
  indicatorConstLp_coeFn

theorem cellL1_norm (I : DyadicIndex) : ‖(cellL1 (𝕂 := 𝕂)) I‖ = dyadicMeasure I := by
  rw [cellL1, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp [dyadicInterval_real_measure]

def intervalFunctional (I : DyadicIndex) : (L1 𝕂) →L[𝕂] 𝕂 :=
  (boundedPairing (𝕂 := 𝕂)) ((dyadicInterval I).indicator (fun _ => 1)) 1
    (measurable_const.indicator (dyadicInterval_measurable I)).aestronglyMeasurable
    (.of_forall fun x => by by_cases hx : x ∈ dyadicInterval I <;> simp [hx])

theorem intervalFunctional_apply (I : DyadicIndex) (f : (L1 𝕂)) :
    (intervalFunctional (𝕂 := 𝕂)) I f = ∫ x in dyadicInterval I, f x ∂unitIntervalMeasure := by
  rw [intervalFunctional, (boundedPairing_apply (𝕂 := 𝕂))]
  rw [← integral_indicator (dyadicInterval_measurable I)]
  congr 1
  funext x
  by_cases hx : x ∈ dyadicInterval I <;> simp [hx]

def dyadicAverage (m : ℕ) : (L1 𝕂) →L[𝕂] (L1 𝕂) :=
  ∑ k : Fin (2^m), (dyadicMeasure ⟨m,k⟩ : 𝕂)⁻¹ •
    ((intervalFunctional (𝕂 := 𝕂)) ⟨m,k⟩).smulRight ((cellL1 (𝕂 := 𝕂)) ⟨m,k⟩)

theorem dyadicAverage_apply (m : ℕ) (f : (L1 𝕂)) :
    (dyadicAverage (𝕂 := 𝕂)) m f = ∑ k : Fin (2^m),
      ((dyadicMeasure ⟨m,k⟩ : 𝕂)⁻¹ * (intervalFunctional (𝕂 := 𝕂)) ⟨m,k⟩ f) • (cellL1 (𝕂 := 𝕂)) ⟨m,k⟩ := by
  simp [dyadicAverage, smul_smul]

theorem dyadic_sum_indicators (m : ℕ) {V : Type*} [AddCommMonoid V] (g : ℝ → V) (x : ℝ) :
    ∑ k : Fin (2^m), (dyadicInterval ⟨m,k⟩).indicator g x =
      (Set.Ico (0 : ℝ) 1).indicator g x := by
  classical
  by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
  · have hu : x ∈ ⋃ k : Fin (2^m), dyadicInterval ⟨m,k⟩ := by rwa [dyadic_partition]
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hu
    rw [Finset.sum_eq_single k]
    · simp [hk, hx]
    · intro j _ hj
      have hnot : x ∉ dyadicInterval ⟨m,j⟩ :=
        Set.disjoint_left.mp (dyadic_level_disjoint m (Ne.symm hj)) hk
      simp [hnot]
    · simp
  · rw [Set.indicator_of_notMem hx]
    apply Finset.sum_eq_zero
    intro k _
    have hnot : x ∉ dyadicInterval ⟨m,k⟩ := fun hk => hx (dyadicInterval_subset_unit _ hk)
    simp [hnot]

theorem dyadic_integral_norm_partition (m : ℕ) (f : (L1 𝕂)) :
    ∑ k : Fin (2^m), ∫ x in dyadicInterval ⟨m,k⟩, ‖f x‖ ∂unitIntervalMeasure = ‖f‖ := by
  have hi := (MeasureTheory.L1.integrable_coeFn f).norm
  simp_rw [← integral_indicator (dyadicInterval_measurable _)]
  rw [← integral_finsetSum _ (fun k _ => hi.indicator (dyadicInterval_measurable ⟨m,k⟩))]
  simp_rw [dyadic_sum_indicators]
  rw [integral_indicator measurableSet_Ico]
  simp only [unitIntervalMeasure, Measure.restrict_restrict measurableSet_Ico, Set.inter_self]
  exact (MeasureTheory.L1.norm_eq_integral_norm f).symm

theorem dyadicAverage_contract (m : ℕ) (f : (L1 𝕂)) : ‖(dyadicAverage (𝕂 := 𝕂)) m f‖ ≤ ‖f‖ := by
  rw [(dyadicAverage_apply (𝕂 := 𝕂))]
  calc
    _ ≤ ∑ k : Fin (2^m), ‖((dyadicMeasure ⟨m,k⟩ : 𝕂)⁻¹ * (intervalFunctional (𝕂 := 𝕂)) ⟨m,k⟩ f) • (cellL1 (𝕂 := 𝕂)) ⟨m,k⟩‖ := norm_sum_le _ _
    _ = ∑ k : Fin (2^m), ‖(intervalFunctional (𝕂 := 𝕂)) ⟨m,k⟩ f‖ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [norm_smul, (cellL1_norm (𝕂 := 𝕂)), norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos (dyadicMeasure_pos _)]
      field_simp [(dyadicMeasure_pos (⟨m,k⟩ : DyadicIndex)).ne']
    _ ≤ ∑ k : Fin (2^m), ∫ x in dyadicInterval ⟨m,k⟩, ‖f x‖ ∂unitIntervalMeasure := by
      apply Finset.sum_le_sum
      intro k _
      rw [(intervalFunctional_apply (𝕂 := 𝕂))]
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := unitIntervalMeasure.restrict (dyadicInterval ⟨m,k⟩)) f
    _ = _ := (dyadic_integral_norm_partition (𝕂 := 𝕂)) m f

theorem dyadicAverage_norm (m : ℕ) : ‖(dyadicAverage (𝕂 := 𝕂)) m‖ ≤ 1 :=
  ((dyadicAverage (𝕂 := 𝕂)) m).opNorm_le_bound zero_le_one (fun f => by simpa using (dyadicAverage_contract (𝕂 := 𝕂)) m f)

theorem finite_disjoint_abs_sum {ι : Type*} [Fintype ι]
    (D : ι → Set ℝ) (hd : Pairwise (fun i j => Disjoint (D i) (D j))) (a : ι → 𝕂) (x : ℝ) :
    ‖∑ i, (D i).indicator (fun _ => a i) x‖ =
      ∑ i, (D i).indicator (fun _ => ‖a i‖) x := by
  classical
  by_cases hx : ∃ i, x ∈ D i
  · obtain ⟨i,hi⟩ := hx
    have hzero (j : ι) (hji : j ≠ i) : x ∉ D j :=
      Set.disjoint_left.mp (hd (Ne.symm hji)) hi
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji; simp [hzero j hji]
    · simp
    · intro j _ hji; simp [hzero j hji]
    · simp
  · have hz : ∀ i, x ∉ D i := by simpa using hx
    simp [hz]

theorem finite_disjoint_integral_norm {ι : Type*} [Fintype ι]
    (D : ι → Set ℝ) (hm : ∀ i, MeasurableSet (D i))
    (hd : Pairwise (fun i j => Disjoint (D i) (D j))) (a : ι → 𝕂) :
    (∫ x, ‖∑ i, (D i).indicator (fun _ => a i) x‖ ∂unitIntervalMeasure) =
      ∑ i, ‖a i‖ * unitIntervalMeasure.real (D i) := by
  simp_rw [finite_disjoint_abs_sum D hd a]
  rw [integral_finsetSum _ (fun i _ => (integrable_const ‖a i‖).indicator (hm i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (hm i), integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_comm]

theorem dyadicAverage_ae (m : ℕ) (f : (L1 𝕂)) :
    ((dyadicAverage (𝕂 := 𝕂)) m f : ℝ → 𝕂) =ᵐ[unitIntervalMeasure]
      fun x => ∑ k : Fin (2^m),
        ((dyadicMeasure ⟨m,k⟩ : 𝕂)⁻¹ * (intervalFunctional (𝕂 := 𝕂)) ⟨m,k⟩ f) *
          (dyadicInterval ⟨m,k⟩).indicator (fun _ => 1) x := by
  rw [(dyadicAverage_apply (𝕂 := 𝕂))]
  have hterm : ∀ᵐ x ∂unitIntervalMeasure, ∀ k : Fin (2^m),
      ((((dyadicMeasure ⟨m,k⟩ : 𝕂)⁻¹ * (intervalFunctional (𝕂 := 𝕂)) ⟨m,k⟩ f) • (cellL1 (𝕂 := 𝕂)) ⟨m,k⟩ : (L1 𝕂)) : ℝ → 𝕂) x =
        ((dyadicMeasure ⟨m,k⟩ : 𝕂)⁻¹ * (intervalFunctional (𝕂 := 𝕂)) ⟨m,k⟩ f) *
          (dyadicInterval ⟨m,k⟩).indicator (fun _ => 1) x := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [Lp.coeFn_smul ((dyadicMeasure ⟨m,k⟩ : 𝕂)⁻¹ * (intervalFunctional (𝕂 := 𝕂)) ⟨m,k⟩ f)
      ((cellL1 (𝕂 := 𝕂)) ⟨m,k⟩), (cellL1_ae (𝕂 := 𝕂)) ⟨m,k⟩] with x hs hc
    simpa [hc] using hs
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun k : Fin (2^m) => ((dyadicMeasure ⟨m,k⟩ : 𝕂)⁻¹ * (intervalFunctional (𝕂 := 𝕂)) ⟨m,k⟩ f) • (cellL1 (𝕂 := 𝕂)) ⟨m,k⟩),
    hterm] with x hx ht
  change _ = _ at hx
  rw [hx]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun k _ => ht k)

theorem dyadicIntegral_children (I : DyadicIndex) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {u : ℝ → V}
    (hu : Integrable u unitIntervalMeasure) :
    (∫ x in dyadicInterval I, u x ∂unitIntervalMeasure) =
      (∫ x in dyadicInterval (dyadicChild I 0), u x ∂unitIntervalMeasure) +
      (∫ x in dyadicInterval (dyadicChild I 1), u x ∂unitIntervalMeasure) := by
  rw [← haarLeft_child, ← haarRight_child, ← haar_halves_union]
  exact setIntegral_union (haar_halves_disjoint I) measurableSet_Ico hu.integrableOn hu.integrableOn

theorem haarCoefficient_children (I : DyadicIndex) (f : (L1 𝕂)) :
    (haarCoefficient (𝕂 := 𝕂)) I f = (intervalFunctional (𝕂 := 𝕂)) (dyadicChild I 0) f -
      (intervalFunctional (𝕂 := 𝕂)) (dyadicChild I 1) f := by
  rw [(haarCoefficient_apply (𝕂 := 𝕂)), (intervalFunctional_apply (𝕂 := 𝕂)), (intervalFunctional_apply (𝕂 := 𝕂)),
    ← haarLeft_child, ← haarRight_child, ← integral_indicator (show MeasurableSet (haarLeft I) from measurableSet_Ico),
    ← integral_indicator (show MeasurableSet (haarRight I) from measurableSet_Ico),
    ← integral_sub ((MeasureTheory.L1.integrable_coeFn f).indicator (show MeasurableSet (haarLeft I) from measurableSet_Ico))
      ((MeasureTheory.L1.integrable_coeFn f).indicator (show MeasurableSet (haarRight I) from measurableSet_Ico))]
  congr 1
  funext x
  simp only [(haarFunction_eq (𝕂 := 𝕂)), Pi.sub_apply]
  by_cases hl : x ∈ haarLeft I <;> by_cases hr : x ∈ haarRight I <;> simp [hl, hr]

theorem finite_disjoint_norm {ι : Type*} [Fintype ι]
    (D : ι → Set ℝ) (hm : ∀ i, MeasurableSet (D i))
    (hd : Pairwise (fun i j => Disjoint (D i) (D j))) (a : ι → 𝕂)
    (hi : Integrable (fun x => ∑ i, (D i).indicator (fun _ => a i) x) unitIntervalMeasure) :
    ‖hi.toL1 (fun x => ∑ i, (D i).indicator (fun _ => a i) x)‖ =
      ∑ i, ‖a i‖ * unitIntervalMeasure.real (D i) := by
  rw [MeasureTheory.L1.norm_eq_integral_norm]
  calc
    _ = ∫ x, ‖∑ i, (D i).indicator (fun _ => a i) x‖ ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [hi.coeFn_toL1] with x hx
      rw [hx]
    _ = _ := finite_disjoint_integral_norm D hm hd a

theorem dyadicInterval_dist_le (I : DyadicIndex) {x y : ℝ}
    (hx : x ∈ dyadicInterval I) (hy : y ∈ dyadicInterval I) : dist x y ≤ dyadicMeasure I := by
  have hlen : (((I.2 : ℝ)+1)/(2 : ℝ)^I.1) - (I.2 : ℝ)/(2 : ℝ)^I.1 = dyadicMeasure I := by
    unfold dyadicMeasure
    ring
  rw [Real.dist_eq, abs_le]
  change _ ≤ x ∧ x < _ at hx
  change _ ≤ y ∧ y < _ at hy
  constructor <;> linarith

theorem intervalFunctional_toL1 (I : DyadicIndex) (u : ℝ → 𝕂)
    (hu : Integrable u unitIntervalMeasure) :
    (intervalFunctional (𝕂 := 𝕂)) I (hu.toL1 u) = ∫ x in dyadicInterval I, u x ∂unitIntervalMeasure := by
  rw [(intervalFunctional_apply (𝕂 := 𝕂))]
  exact integral_congr_ae (ae_restrict_of_ae hu.coeFn_toL1)

theorem dyadicAverage_cell_ae (m : ℕ) (f : (L1 𝕂)) :
    ∀ᵐ x ∂unitIntervalMeasure, ∀ k : Fin (2^m), x ∈ dyadicInterval ⟨m,k⟩ →
      (dyadicAverage (𝕂 := 𝕂)) m f x = (dyadicMeasure ⟨m,k⟩ : 𝕂)⁻¹ * (intervalFunctional (𝕂 := 𝕂)) ⟨m,k⟩ f := by
  classical
  filter_upwards [(dyadicAverage_ae (𝕂 := 𝕂)) m f] with x hx
  intro k hk
  rw [hx, Finset.sum_eq_single k]
  · simp [hk]
  · intro j _ hj
    have hnot : x ∉ dyadicInterval ⟨m,j⟩ :=
      Set.disjoint_left.mp (dyadic_level_disjoint m (Ne.symm hj)) hk
    simp [hnot]
  · simp

theorem dyadic_cell_average_error (I : DyadicIndex) (u : ℝ → 𝕂)
    (hu : Integrable u unitIntervalMeasure) {ε : ℝ} {x : ℝ}
    (_hx : x ∈ dyadicInterval I)
    (hosc : ∀ y ∈ dyadicInterval I, ‖u y-u x‖ ≤ ε) :
    ‖(dyadicMeasure I : 𝕂)⁻¹ * (∫ y in dyadicInterval I, u y ∂unitIntervalMeasure) - u x‖ ≤ ε := by
  have hp := dyadicMeasure_pos I
  have he : (dyadicMeasure I : 𝕂)⁻¹ * (∫ y in dyadicInterval I, u y ∂unitIntervalMeasure) - u x =
      (dyadicMeasure I : 𝕂)⁻¹ * ∫ y in dyadicInterval I, (u y-u x) ∂unitIntervalMeasure := by
    rw [integral_sub hu.integrableOn (integrable_const _), setIntegral_const,
      dyadicInterval_real_measure, RCLike.real_smul_eq_coe_mul]
    field_simp [(RCLike.ofReal_ne_zero.mpr hp.ne')]
  rw [he, norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos hp]
  have hbound := norm_setIntegral_le_of_norm_le_const
    (measure_lt_top unitIntervalMeasure (dyadicInterval I)) hosc
  rw [dyadicInterval_real_measure] at hbound
  calc
    _ ≤ (dyadicMeasure I)⁻¹ * (ε * dyadicMeasure I) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hp.le)
    _ = ε := by field_simp

theorem dyadicAverage_oscillation_bound (m : ℕ) (u : ℝ → 𝕂)
    (hu : Integrable u unitIntervalMeasure) {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ I : DyadicIndex, I.1 = m → ∀ x ∈ dyadicInterval I, ∀ y ∈ dyadicInterval I,
      ‖u y-u x‖ ≤ ε) :
    ‖(dyadicAverage (𝕂 := 𝕂)) m (hu.toL1 u) - hu.toL1 u‖ ≤ ε := by
  have hpoint : ∀ᵐ x ∂unitIntervalMeasure, ‖((dyadicAverage (𝕂 := 𝕂)) m (hu.toL1 u) - hu.toL1 u : (L1 𝕂)) x‖ ≤ ε := by
    have hunit : ∀ᵐ x ∂unitIntervalMeasure, x ∈ Set.Ico (0 : ℝ) 1 :=
      ae_restrict_mem measurableSet_Ico
    filter_upwards [Lp.coeFn_sub ((dyadicAverage (𝕂 := 𝕂)) m (hu.toL1 u)) (hu.toL1 u),
      (dyadicAverage_cell_ae (𝕂 := 𝕂)) m (hu.toL1 u), hu.coeFn_toL1, hunit] with x hsub hcell huval hx
    have hi : x ∈ ⋃ k : Fin (2^m), dyadicInterval ⟨m,k⟩ := by rwa [dyadic_partition]
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hi
    rw [hsub]
    change ‖(dyadicAverage (𝕂 := 𝕂)) m (hu.toL1 u) x - hu.toL1 u x‖ ≤ ε
    rw [hcell k hk, huval, (intervalFunctional_toL1 (𝕂 := 𝕂))]
    exact (dyadic_cell_average_error (𝕂 := 𝕂)) ⟨m,k⟩ u hu hk (hosc ⟨m,k⟩ rfl x hk)
  have h := Lp.norm_le_of_ae_bound hε hpoint
  simpa [measureUnivNNReal, measure_univ] using h

theorem dyadicAverage_tendsto_continuous (u : ℝ → 𝕂)
    (hu : Integrable u unitIntervalMeasure) (hc : ContinuousOn u (Set.Icc (0 : ℝ) 1)) :
    Filter.Tendsto (fun m => (dyadicAverage (𝕂 := 𝕂)) m (hu.toL1 u)) Filter.atTop (nhds (hu.toL1 u)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hc
  obtain ⟨δ,hδ,hosc⟩ := Metric.uniformContinuousOn_iff.mp huc (ε/2) (by linarith)
  have ht : Filter.Tendsto (fun m : ℕ => ((2 : ℝ)^m)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun m hm => ?_⟩
  rw [dist_eq_norm]
  have hb : ‖(dyadicAverage (𝕂 := 𝕂)) m (hu.toL1 u) - hu.toL1 u‖ ≤ ε/2 := by
    apply (dyadicAverage_oscillation_bound (𝕂 := 𝕂)) m u hu (by linarith)
    intro I hI x hx y hy
    have hxunit := dyadicInterval_subset_unit I hx
    have hyunit := dyadicInterval_subset_unit I hy
    have hd : dist y x < δ := lt_of_le_of_lt (dyadicInterval_dist_le I hy hx) (by
      simpa [dyadicMeasure, hI] using hN m hm)
    have hh := hosc y ⟨hyunit.1,hyunit.2.le⟩ x ⟨hxunit.1,hxunit.2.le⟩ hd
    simpa only [dist_eq_norm] using hh.le
  linarith

/-- Dyadic averaging converges strongly on the canonical L¹ space. -/
theorem dyadicAverage_tendsto (f : (L1 𝕂)) :
    Filter.Tendsto (fun m => (dyadicAverage (𝕂 := 𝕂)) m f) Filter.atTop (nhds f) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hd := BoundedContinuousFunction.toLp_denseRange 𝕂 unitIntervalMeasure 𝕂 (by norm_num : (1 : ENNReal) ≠ ⊤)
  obtain ⟨u,huclose⟩ := hd.exists_dist_lt f (by linarith : 0 < ε/4)
  have hu : Integrable u unitIntervalMeasure :=
    memLp_one_iff_integrable.mp ((u.memLp_top (μ := unitIntervalMeasure)).mono_exponent le_top)
  have he : hu.toL1 u = BoundedContinuousFunction.toLp 1 unitIntervalMeasure 𝕂 u := by
    apply Lp.ext
    exact hu.coeFn_toL1.trans (BoundedContinuousFunction.coeFn_toLp 1 unitIntervalMeasure 𝕂 u).symm
  have hc := (dyadicAverage_tendsto_continuous (𝕂 := 𝕂)) u hu u.continuous.continuousOn
  rw [he] at hc
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hc (ε/2) (by linarith)
  refine ⟨N, fun m hm => ?_⟩
  let v := BoundedContinuousFunction.toLp 1 unitIntervalMeasure 𝕂 u
  have heps : ‖f-v‖ < ε/4 := by simpa only [dist_eq_norm] using huclose
  have havg : ‖(dyadicAverage (𝕂 := 𝕂)) m v-v‖ < ε/2 := by simpa only [dist_eq_norm] using hN m hm
  have hcontract : ‖(dyadicAverage (𝕂 := 𝕂)) m f-(dyadicAverage (𝕂 := 𝕂)) m v‖ ≤ ‖f-v‖ := by
    rw [← map_sub]
    exact (dyadicAverage_contract (𝕂 := 𝕂)) m (f-v)
  have ht := dist_triangle ((dyadicAverage (𝕂 := 𝕂)) m f) ((dyadicAverage (𝕂 := 𝕂)) m v) f
  have ht' := dist_triangle ((dyadicAverage (𝕂 := 𝕂)) m v) v f
  simp only [dist_eq_norm] at ht ht'
  rw [dist_eq_norm]
  have hr : ‖v-f‖ = ‖f-v‖ := norm_sub_rev v f
  linarith

theorem dyadicChild_measure (I : DyadicIndex) (j : Fin 2) :
    dyadicMeasure (dyadicChild I j) = dyadicMeasure I / 2 := by
  simp only [dyadicMeasure, dyadicChild_level, pow_succ, mul_inv_rev]
  ring

theorem cellL1_children (I : DyadicIndex) :
    (cellL1 (𝕂 := 𝕂)) I = (cellL1 (𝕂 := 𝕂)) (dyadicChild I 0) + (cellL1 (𝕂 := 𝕂)) (dyadicChild I 1) := by
  apply Lp.ext
  filter_upwards [(cellL1_ae (𝕂 := 𝕂)) I, (cellL1_ae (𝕂 := 𝕂)) (dyadicChild I 0), (cellL1_ae (𝕂 := 𝕂)) (dyadicChild I 1),
    Lp.coeFn_add ((cellL1 (𝕂 := 𝕂)) (dyadicChild I 0)) ((cellL1 (𝕂 := 𝕂)) (dyadicChild I 1))] with x hi h0 h1 hadd
  rw [hadd, hi]
  simp only [Pi.add_apply]
  rw [h0, h1, ← haarLeft_child, ← haarRight_child, ← haar_halves_union]
  exact congrFun (Set.indicator_union_of_disjoint (haar_halves_disjoint I) (fun _ => (1 : 𝕂))) x

theorem haarL1_children (I : DyadicIndex) :
    (haarL1 𝕂) I = (cellL1 (𝕂 := 𝕂)) (dyadicChild I 0) - (cellL1 (𝕂 := 𝕂)) (dyadicChild I 1) := by
  apply Lp.ext
  filter_upwards [(haarL1_ae (𝕂 := 𝕂)) I, (cellL1_ae (𝕂 := 𝕂)) (dyadicChild I 0), (cellL1_ae (𝕂 := 𝕂)) (dyadicChild I 1),
    Lp.coeFn_sub ((cellL1 (𝕂 := 𝕂)) (dyadicChild I 0)) ((cellL1 (𝕂 := 𝕂)) (dyadicChild I 1))] with x hi h0 h1 hsub
  rw [hsub, hi]
  simp only [Pi.sub_apply]
  rw [h0, h1, ← haarLeft_child, ← haarRight_child]
  rfl

theorem parent_average_split (I : DyadicIndex) (f : (L1 𝕂)) :
    ((dyadicMeasure (dyadicChild I 0) : 𝕂)⁻¹ * (intervalFunctional (𝕂 := 𝕂)) (dyadicChild I 0) f) • (cellL1 (𝕂 := 𝕂)) (dyadicChild I 0) +
    ((dyadicMeasure (dyadicChild I 1) : 𝕂)⁻¹ * (intervalFunctional (𝕂 := 𝕂)) (dyadicChild I 1) f) • (cellL1 (𝕂 := 𝕂)) (dyadicChild I 1) =
    ((dyadicMeasure I : 𝕂)⁻¹ * (intervalFunctional (𝕂 := 𝕂)) I f) • (cellL1 (𝕂 := 𝕂)) I +
    ((dyadicMeasure I : 𝕂)⁻¹ * (haarCoefficient (𝕂 := 𝕂)) I f) • (haarL1 𝕂) I := by
  have hf : (intervalFunctional (𝕂 := 𝕂)) I f = (intervalFunctional (𝕂 := 𝕂)) (dyadicChild I 0) f + (intervalFunctional (𝕂 := 𝕂)) (dyadicChild I 1) f := by
    simp only [(intervalFunctional_apply (𝕂 := 𝕂))]
    exact dyadicIntegral_children I (MeasureTheory.L1.integrable_coeFn f)
  rw [hf, (haarCoefficient_children (𝕂 := 𝕂)) I f, (cellL1_children (𝕂 := 𝕂)) I, (haarL1_children (𝕂 := 𝕂)) I]
  simp only [dyadicChild_measure, div_eq_mul_inv, smul_add, smul_sub, add_smul, sub_smul, mul_smul]
  module

theorem intervalFunctional_root (f : (L1 𝕂)) : (intervalFunctional (𝕂 := 𝕂)) ⟨0,0⟩ f = (meanFunctional (𝕂 := 𝕂)) f := by
  rw [(intervalFunctional_apply (𝕂 := 𝕂)), (meanFunctional_apply (𝕂 := 𝕂))]
  have hi : dyadicInterval ⟨0,0⟩ = Set.Ico (0 : ℝ) 1 := by norm_num [dyadicInterval]
  rw [hi]
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  have hunit : ∀ᵐ x ∂unitIntervalMeasure, x ∈ Set.Ico (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ico
  filter_upwards [hunit] with x hx
  exact fun hn => False.elim (hn hx)

def constantL1 : (L1 𝕂) := (cellL1 (𝕂 := 𝕂)) ⟨0,0⟩

theorem dyadicAverage_zero (f : (L1 𝕂)) : (dyadicAverage (𝕂 := 𝕂)) 0 f = (meanFunctional (𝕂 := 𝕂)) f • (constantL1 (𝕂 := 𝕂)) := by
  rw [(dyadicAverage_apply (𝕂 := 𝕂))]
  change (∑ k : Fin 1, ((dyadicMeasure ⟨0,k⟩ : 𝕂)⁻¹ * (intervalFunctional (𝕂 := 𝕂)) ⟨0,k⟩ f) • (cellL1 (𝕂 := 𝕂)) ⟨0,k⟩) = _
  rw [Fin.sum_univ_one, (intervalFunctional_root (𝕂 := 𝕂))]
  simp [dyadicMeasure, constantL1]

theorem dyadicAverage_succ (n : ℕ) (f : (L1 𝕂)) :
    (dyadicAverage (𝕂 := 𝕂)) (n+1) f = (dyadicAverage (𝕂 := 𝕂)) n f +
      ∑ k : Fin (2^n), ((dyadicMeasure ⟨n,k⟩ : 𝕂)⁻¹ * (haarCoefficient (𝕂 := 𝕂)) ⟨n,k⟩ f) • (haarL1 𝕂) ⟨n,k⟩ := by
  rw [(dyadicAverage_apply (𝕂 := 𝕂)) (n+1)]
  rw [dyadicChild_sum n (fun I => ((dyadicMeasure I : 𝕂)⁻¹ * intervalFunctional I f) • cellL1 I)]
  simp only [Fin.sum_univ_two]
  simp_rw [(parent_average_split (𝕂 := 𝕂))]
  rw [Finset.sum_add_distrib, ← (dyadicAverage_apply (𝕂 := 𝕂))]

theorem dyadicAverage_finite_expansion (m : ℕ) (f : (L1 𝕂)) :
    (dyadicAverage (𝕂 := 𝕂)) m f = (meanFunctional (𝕂 := 𝕂)) f • (constantL1 (𝕂 := 𝕂)) +
      ∑ n ∈ Finset.range m, ∑ k : Fin (2^n),
        ((dyadicMeasure ⟨n,k⟩ : 𝕂)⁻¹ * (haarCoefficient (𝕂 := 𝕂)) ⟨n,k⟩ f) • (haarL1 𝕂) ⟨n,k⟩ := by
  induction m with
  | zero => simpa using (dyadicAverage_zero (𝕂 := 𝕂)) f
  | succ m ih =>
    rw [(dyadicAverage_succ (𝕂 := 𝕂)), ih, Finset.sum_range_succ, add_assoc]

theorem mem_haarClosedSpan_iff (S : Set ℕ) (f : (L1 𝕂)) :
    f ∈ (haarClosedSpan 𝕂) S ↔ (meanFunctional (𝕂 := 𝕂)) f = 0 ∧
      ∀ I : DyadicIndex, I.1 ∉ S → (haarCoefficient (𝕂 := 𝕂)) I f = 0 := by
  constructor
  · intro hf
    constructor
    · apply (closedSpan_vanish (𝕂 := 𝕂)) (meanFunctional (𝕂 := 𝕂)) _ _ hf
      rintro _ ⟨I,_,rfl⟩
      exact (meanFunctional_haar (𝕂 := 𝕂)) I
    · intro I hI
      apply (closedSpan_vanish (𝕂 := 𝕂)) ((haarCoefficient (𝕂 := 𝕂)) I) _ _ hf
      rintro _ ⟨J,hJ,rfl⟩
      rw [(haarCoefficient_haar (𝕂 := 𝕂)), if_neg]
      exact fun he => hI (he.symm ▸ hJ)
  · rintro ⟨hm,hc⟩
    have he (m : ℕ) : (dyadicAverage (𝕂 := 𝕂)) m f ∈
        Submodule.span 𝕂 ((haarL1 𝕂) '' {I : DyadicIndex | I.1 ∈ S}) := by
      rw [(dyadicAverage_finite_expansion (𝕂 := 𝕂)), hm, zero_smul, zero_add]
      apply Submodule.sum_mem
      intro n _
      apply Submodule.sum_mem
      intro k _
      by_cases hn : n ∈ S
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨n,k⟩,hn,rfl⟩)
      · simp [hc ⟨n,k⟩ hn]
    exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ((dyadicAverage_tendsto (𝕂 := 𝕂)) f)
      (Filter.Eventually.of_forall fun m => Submodule.le_topologicalClosure _ (he m))

def H₀ : Submodule 𝕂 (L1 𝕂) := (meanFunctional (𝕂 := 𝕂)).ker

theorem haar_dense_meanZero : (haarClosedSpan 𝕂) Set.univ = (H₀ (𝕂 := 𝕂)) := by
  ext f
  rw [(mem_haarClosedSpan_iff (𝕂 := 𝕂))]
  simp [H₀]

theorem X₀_eq_haarClosedSpan : (X₀ 𝕂) = (haarClosedSpan 𝕂) {n | Even n} := rfl

theorem X₁_eq_haarClosedSpan : (X₁ 𝕂) = (haarClosedSpan 𝕂) {n | Odd n} := rfl

theorem haarCoefficient_ext (f g : (L1 𝕂)) (hm : (meanFunctional (𝕂 := 𝕂)) f = (meanFunctional (𝕂 := 𝕂)) g)
    (hc : ∀ I, (haarCoefficient (𝕂 := 𝕂)) I f = (haarCoefficient (𝕂 := 𝕂)) I g) : f = g := by
  have he (m : ℕ) : (dyadicAverage (𝕂 := 𝕂)) m f = (dyadicAverage (𝕂 := 𝕂)) m g := by
    simp only [(dyadicAverage_finite_expansion (𝕂 := 𝕂)), hm, hc]
  have ht : Filter.Tendsto (fun m => (dyadicAverage (𝕂 := 𝕂)) m f) Filter.atTop (nhds g) := by
    have hfun : (fun m => (dyadicAverage (𝕂 := 𝕂)) m f) = (fun m => (dyadicAverage (𝕂 := 𝕂)) m g) := funext he
    rw [hfun]
    exact (dyadicAverage_tendsto (𝕂 := 𝕂)) g
  exact tendsto_nhds_unique ((dyadicAverage_tendsto (𝕂 := 𝕂)) f) ht

end EvenOddHaarLevels
