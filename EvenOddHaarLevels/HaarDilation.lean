import EvenOddHaarLevels.HaarCoefficients

/-! Affine measure transport and normalized dilation in canonical scalar-valued L¹. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

def affineToUnit (a l : ℝ) (x : ℝ) : ℝ := (x - a) / l

theorem affineToUnit_preimage_unit (a : ℝ) {l : ℝ} (hl : 0 < l) :
    affineToUnit a l ⁻¹' Set.Ico (0 : ℝ) 1 = Set.Ico a (a + l) := by
  ext x
  simp only [affineToUnit, Set.mem_preimage, Set.mem_Ico]
  constructor
  · rintro ⟨h0, h1⟩
    have h0' : 0 ≤ x - a := by simpa using (le_div_iff₀ hl).mp h0
    have h1' : x - a < l := (div_lt_one hl).mp h1
    constructor <;> linarith
  · rintro ⟨h0, h1⟩
    exact ⟨div_nonneg (by linarith) hl.le, (div_lt_one hl).mpr (by linarith)⟩

theorem affineToUnit_map_volume (a : ℝ) {l : ℝ} (hl : 0 < l) :
    Measure.map (affineToUnit a l) volume = ENNReal.ofReal l • (volume : Measure ℝ) := by
  have he : affineToUnit a l = (fun x : ℝ => l⁻¹ * x) ∘ (fun x : ℝ => x + -a) := by
    funext x
    simp only [affineToUnit, Function.comp_def]
    ring
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), map_add_right_eq_self,
    Real.map_volume_mul_left (inv_ne_zero hl.ne')]
  simp [abs_of_pos hl]

/-- The restricted affine pushforward; no interval-containment hypothesis is needed. -/
theorem affine_restrict_map (a : ℝ) {l : ℝ} (hl : 0 < l) :
    Measure.map (affineToUnit a l) (volume.restrict (Set.Ico a (a + l))) =
      ENNReal.ofReal l • unitIntervalMeasure := by
  have h := Measure.restrict_map (μ := (volume : Measure ℝ))
    (show Measurable (affineToUnit a l) by unfold affineToUnit; fun_prop)
    (s := Set.Ico (0 : ℝ) 1) measurableSet_Ico
  rw [affineToUnit_map_volume a hl, affineToUnit_preimage_unit a hl, Measure.restrict_smul] at h
  exact h.symm

theorem unitIntervalMeasure_restrict_interval (a l : ℝ)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) :
    unitIntervalMeasure.restrict (Set.Ico a (a + l)) =
      volume.restrict (Set.Ico a (a + l)) := by
  rw [unitIntervalMeasure, Measure.restrict_restrict measurableSet_Ico,
    Set.inter_eq_left.mpr hJ]

/-- The normalized affine image of an ordinary representative. -/
def dilationFunction (a l : ℝ) (f : ℝ → 𝕂) : ℝ → 𝕂 :=
  (Set.Ico a (a + l)).indicator (fun x => (l : 𝕂)⁻¹ * f (affineToUnit a l x))

theorem integrable_affine_comp {f : ℝ → 𝕂} (hf : Integrable f unitIntervalMeasure)
    (a : ℝ) {l : ℝ} (hl : 0 < l) :
    Integrable (f ∘ affineToUnit a l) (volume.restrict (Set.Ico a (a + l))) := by
  have hf' : Integrable f (Measure.map (affineToUnit a l)
      (volume.restrict (Set.Ico a (a + l)))) := by
    rw [affine_restrict_map a hl]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hf'.comp_aemeasurable (by unfold affineToUnit; fun_prop)

theorem integrable_dilationFunction {f : ℝ → 𝕂} (hf : Integrable f unitIntervalMeasure)
    (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) :
    Integrable ((dilationFunction (𝕂 := 𝕂)) a l f) unitIntervalMeasure := by
  rw [dilationFunction, integrable_indicator_iff measurableSet_Ico, IntegrableOn,
    unitIntervalMeasure_restrict_interval a l hJ]
  exact ((integrable_affine_comp (𝕂 := 𝕂)) hf a hl).const_mul (l : 𝕂)⁻¹

theorem integral_affine_comp {f : ℝ → 𝕂} (hf : Integrable f unitIntervalMeasure)
    (a : ℝ) {l : ℝ} (hl : 0 < l) :
    (∫ x, f (affineToUnit a l x) ∂volume.restrict (Set.Ico a (a + l))) =
      l * ∫ x, f x ∂unitIntervalMeasure := by
  have hf' : AEStronglyMeasurable f (Measure.map (affineToUnit a l)
      (volume.restrict (Set.Ico a (a + l)))) := by
    rw [affine_restrict_map a hl]
    exact hf.aestronglyMeasurable.smul_measure (c := ENNReal.ofReal l)
  rw [← integral_map (by unfold affineToUnit; fun_prop) hf', affine_restrict_map a hl,
    integral_smul_measure]
  simp [hl.le, RCLike.real_smul_eq_coe_mul]

theorem integral_norm_dilationFunction {f : ℝ → 𝕂} (hf : Integrable f unitIntervalMeasure)
    (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) :
    (∫ x, ‖(dilationFunction (𝕂 := 𝕂)) a l f x‖ ∂unitIntervalMeasure) =
      ∫ x, ‖f x‖ ∂unitIntervalMeasure := by
  have he : (fun x => ‖(dilationFunction (𝕂 := 𝕂)) a l f x‖) =
      (Set.Ico a (a + l)).indicator (fun x => l⁻¹ * ‖f (affineToUnit a l x)‖) := by
    funext x
    simp only [dilationFunction, Set.indicator]
    split_ifs <;> simp [norm_mul, abs_of_pos hl]
  rw [he, integral_indicator measurableSet_Ico,
    unitIntervalMeasure_restrict_interval a l hJ, integral_const_mul,
    (integral_affine_comp (𝕂 := ℝ)) hf.norm a hl]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  field_simp

theorem dilationFunction_congr_ae {f g : ℝ → 𝕂} (hfg : f =ᵐ[unitIntervalMeasure] g)
    (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) :
    (dilationFunction (𝕂 := 𝕂)) a l f =ᵐ[unitIntervalMeasure] (dilationFunction (𝕂 := 𝕂)) a l g := by
  have hmap : f =ᵐ[Measure.map (affineToUnit a l)
      (volume.restrict (Set.Ico a (a + l)))] g := by
    rw [affine_restrict_map a hl]
    exact Measure.ae_smul_measure hfg _
  have hc := ae_of_ae_map (show AEMeasurable (affineToUnit a l)
      (volume.restrict (Set.Ico a (a + l))) by unfold affineToUnit; fun_prop) hmap
  apply (ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ico).mp
  rw [unitIntervalMeasure_restrict_interval a l hJ]
  filter_upwards [hc] with x hx
  exact congrArg ((l : 𝕂)⁻¹ * ·) hx

/-- Normalized dilation of canonical L¹ classes into an interval. -/
def dilationL1 (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) (f : (L1 𝕂)) : (L1 𝕂) :=
  ((integrable_dilationFunction (𝕂 := 𝕂)) (MeasureTheory.L1.integrable_coeFn f) a hl hJ).toL1 _

theorem coeFn_dilationL1 (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) (f : (L1 𝕂)) :
    (dilationL1 (𝕂 := 𝕂)) a hl hJ f =ᵐ[unitIntervalMeasure] (dilationFunction (𝕂 := 𝕂)) a l f :=
  Integrable.coeFn_toL1 _

theorem norm_dilationL1 (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) (f : (L1 𝕂)) :
    ‖(dilationL1 (𝕂 := 𝕂)) a hl hJ f‖ = ‖f‖ := by
  rw [MeasureTheory.L1.norm_eq_integral_norm, MeasureTheory.L1.norm_eq_integral_norm f]
  exact (integral_congr_ae (((coeFn_dilationL1 (𝕂 := 𝕂)) a hl hJ f).fun_comp norm)).trans
    ((integral_norm_dilationFunction (𝕂 := 𝕂)) (MeasureTheory.L1.integrable_coeFn f) a hl hJ)

/-- The genuine normalized affine linear isometry on the quotient space. -/
def dilationL1LinearIsometry (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) : (L1 𝕂) →ₗᵢ[𝕂] (L1 𝕂) where
  toFun := (dilationL1 (𝕂 := 𝕂)) a hl hJ
  map_add' f g := by
    apply Lp.ext
    refine ((coeFn_dilationL1 (𝕂 := 𝕂)) a hl hJ (f + g)).trans ?_
    refine ((dilationFunction_congr_ae (𝕂 := 𝕂)) (Lp.coeFn_add f g) a hl hJ).trans ?_
    filter_upwards [(coeFn_dilationL1 (𝕂 := 𝕂)) a hl hJ f, (coeFn_dilationL1 (𝕂 := 𝕂)) a hl hJ g,
      Lp.coeFn_add ((dilationL1 (𝕂 := 𝕂)) a hl hJ f) ((dilationL1 (𝕂 := 𝕂)) a hl hJ g)] with x hf hg ha
    rw [ha, Pi.add_apply, hf, hg]
    simp only [dilationFunction, Pi.add_apply, Set.indicator]
    split_ifs <;> ring
  map_smul' c f := by
    apply Lp.ext
    refine ((coeFn_dilationL1 (𝕂 := 𝕂)) a hl hJ (c • f)).trans ?_
    refine ((dilationFunction_congr_ae (𝕂 := 𝕂)) (Lp.coeFn_smul c f) a hl hJ).trans ?_
    filter_upwards [(coeFn_dilationL1 (𝕂 := 𝕂)) a hl hJ f,
      Lp.coeFn_smul c ((dilationL1 (𝕂 := 𝕂)) a hl hJ f)] with x hf hs
    change (dilationFunction (𝕂 := 𝕂)) a l (c • ⇑f) x = (c • (dilationL1 (𝕂 := 𝕂)) a hl hJ f) x
    rw [hs, Pi.smul_apply, hf]
    simp only [dilationFunction, Pi.smul_apply, smul_eq_mul, Set.indicator]
    split_ifs <;> ring
  norm_map' := (norm_dilationL1 (𝕂 := 𝕂)) a hl hJ

def affineFromUnit (a l : ℝ) (t : ℝ) : ℝ := a + l * t

theorem affineFromUnit_map (a : ℝ) {l : ℝ} (hl : 0 < l) :
    Measure.map (affineFromUnit a l) unitIntervalMeasure =
      (ENNReal.ofReal l)⁻¹ • volume.restrict (Set.Ico a (a + l)) := by
  have h := congrArg (Measure.map (affineFromUnit a l)) (affine_restrict_map a hl)
  rw [Measure.map_map (by unfold affineFromUnit; fun_prop)
      (by unfold affineToUnit; fun_prop), Measure.map_smul] at h
  have hc : affineFromUnit a l ∘ affineToUnit a l = id := by
    funext x
    dsimp [affineFromUnit, affineToUnit, Function.comp_def]
    field_simp [hl.ne']
    ring
  rw [hc, Measure.map_id] at h
  rw [h, smul_smul, ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hl)
    ENNReal.ofReal_ne_top, one_smul]

theorem integrable_affineFromUnit {g : ℝ → 𝕂}
    (hg : Integrable g unitIntervalMeasure) (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) :
    Integrable (g ∘ affineFromUnit a l) unitIntervalMeasure := by
  have hgJ : Integrable g (volume.restrict (Set.Ico a (a + l))) := by
    rw [← unitIntervalMeasure_restrict_interval a l hJ]
    exact hg.restrict
  have hg' : Integrable g (Measure.map (affineFromUnit a l) unitIntervalMeasure) := by
    rw [affineFromUnit_map a hl]
    exact hgJ.smul_measure (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hl))
  exact hg'.comp_aemeasurable (by unfold affineFromUnit; fun_prop)

/-- Affine restriction, the inverse of dilation on classes supported in the interval. -/
def undilationL1 (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) (g : (L1 𝕂)) : (L1 𝕂) :=
  (((integrable_affineFromUnit (𝕂 := 𝕂)) (MeasureTheory.L1.integrable_coeFn g) a hl hJ).const_mul l).toL1 _

theorem coeFn_undilationL1 (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) (g : (L1 𝕂)) :
    (undilationL1 (𝕂 := 𝕂)) a hl hJ g =ᵐ[unitIntervalMeasure]
      (fun t => (l : 𝕂) * g (affineFromUnit a l t)) := Integrable.coeFn_toL1 _

omit [RCLike 𝕂] in
theorem affineFromUnit_comp_congr_ae {f g : ℝ → 𝕂}
    (hfg : f =ᵐ[unitIntervalMeasure] g) (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) :
    f ∘ affineFromUnit a l =ᵐ[unitIntervalMeasure] g ∘ affineFromUnit a l := by
  have hfgJ : f =ᵐ[volume.restrict (Set.Ico a (a + l))] g := by
    rw [← unitIntervalMeasure_restrict_interval a l hJ]
    exact ae_restrict_of_ae hfg
  have he : f =ᵐ[Measure.map (affineFromUnit a l) unitIntervalMeasure] g := by
    rw [affineFromUnit_map a hl]
    exact Measure.ae_smul_measure hfgJ _
  exact ae_of_ae_map (by unfold affineFromUnit; fun_prop) he

theorem undilationL1_dilationL1 (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) (f : (L1 𝕂)) :
    (undilationL1 (𝕂 := 𝕂)) a hl hJ ((dilationL1 (𝕂 := 𝕂)) a hl hJ f) = f := by
  apply Lp.ext
  refine ((coeFn_undilationL1 (𝕂 := 𝕂)) a hl hJ _).trans ?_
  have hc := (affineFromUnit_comp_congr_ae (𝕂 := 𝕂)) ((coeFn_dilationL1 (𝕂 := 𝕂)) a hl hJ f) a hl hJ
  have hu : ∀ᵐ t ∂unitIntervalMeasure, t ∈ Set.Ico (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ico
  filter_upwards [hc, hu] with t ht htu
  rw [show (dilationL1 a hl hJ f) (affineFromUnit a l t) =
    dilationFunction a l f (affineFromUnit a l t) from ht]
  have hm : affineFromUnit a l t ∈ Set.Ico a (a + l) := by
    rcases htu with ⟨ht0, ht1⟩
    constructor <;> dsimp [affineFromUnit] <;> nlinarith
  rw [dilationFunction, Set.indicator_of_mem hm]
  have hi : affineToUnit a l (affineFromUnit a l t) = t := by
    dsimp [affineToUnit, affineFromUnit]
    field_simp [hl.ne']
    ring
  rw [hi, ← mul_assoc, mul_inv_cancel₀ (RCLike.ofReal_ne_zero.mpr hl.ne'), one_mul]

theorem dilationL1_undilationL1 (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) (g : (L1 𝕂)) :
    (dilationL1 (𝕂 := 𝕂)) a hl hJ ((undilationL1 (𝕂 := 𝕂)) a hl hJ g) =ᵐ[unitIntervalMeasure]
      (Set.Ico a (a + l)).indicator (g : ℝ → 𝕂) := by
  refine ((coeFn_dilationL1 (𝕂 := 𝕂)) a hl hJ _).trans ?_
  refine ((dilationFunction_congr_ae (𝕂 := 𝕂)) ((coeFn_undilationL1 (𝕂 := 𝕂)) a hl hJ g) a hl hJ).trans ?_
  apply Filter.Eventually.of_forall
  intro x
  have hi : affineFromUnit a l (affineToUnit a l x) = x := by
    dsimp [affineToUnit, affineFromUnit]
    field_simp [hl.ne']
    ring
  simp only [dilationFunction, Set.indicator]
  split_ifs <;> simp [hi, hl.ne']

/-- The subspace of canonical L¹ classes supported in the dilation interval. -/
def intervalSupportedL1 (a l : ℝ) : Submodule 𝕂 (L1 𝕂) where
  carrier := {f | ∀ᵐ x ∂unitIntervalMeasure, x ∉ Set.Ico a (a + l) → f x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero 𝕂 1 unitIntervalMeasure] with x hx
    intro _
    exact hx
  add_mem' {f g} hf hg := by
    filter_upwards [hf, hg, Lp.coeFn_add f g] with x hx hy ha
    intro hn
    change (f + g) x = 0
    rw [ha, Pi.add_apply, hx hn, hy hn, add_zero]
  smul_mem' c {f} hf := by
    filter_upwards [hf, Lp.coeFn_smul c f] with x hx hs
    intro hn
    simp [hs, hx hn]

theorem dilationL1_mem_intervalSupportedL1 (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) (f : (L1 𝕂)) :
    (dilationL1 (𝕂 := 𝕂)) a hl hJ f ∈ (intervalSupportedL1 (𝕂 := 𝕂)) a l := by
  filter_upwards [(coeFn_dilationL1 (𝕂 := 𝕂)) a hl hJ f] with x hx
  intro hn
  simp [hx, dilationFunction, Set.indicator_of_notMem hn]

theorem dilationL1_undilationL1_of_supported (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) (g : (intervalSupportedL1 (𝕂 := 𝕂)) a l) :
    (dilationL1 (𝕂 := 𝕂)) a hl hJ ((undilationL1 (𝕂 := 𝕂)) a hl hJ g) = g := by
  apply Lp.ext
  refine ((dilationL1_undilationL1 (𝕂 := 𝕂)) a hl hJ g).trans ?_
  filter_upwards [g.property] with x hx
  by_cases hm : x ∈ Set.Ico a (a + l)
  · simp [hm]
  · simp [hm, hx hm]

/-- Dilation identifies L¹ isometrically with the supported subspace. -/
def dilationL1Equiv (a : ℝ) {l : ℝ} (hl : 0 < l)
    (hJ : Set.Ico a (a + l) ⊆ Set.Ico (0 : ℝ) 1) :
    (L1 𝕂) ≃ₗᵢ[𝕂] (intervalSupportedL1 (𝕂 := 𝕂)) a l :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := ((dilationL1LinearIsometry (𝕂 := 𝕂)) a hl hJ).toLinearMap.codRestrict
        ((intervalSupportedL1 (𝕂 := 𝕂)) a l) ((dilationL1_mem_intervalSupportedL1 (𝕂 := 𝕂)) a hl hJ)
      norm_map' := (norm_dilationL1 (𝕂 := 𝕂)) a hl hJ } (by
        intro g
        refine ⟨(undilationL1 (𝕂 := 𝕂)) a hl hJ g, ?_⟩
        apply Subtype.ext
        exact (dilationL1_undilationL1_of_supported (𝕂 := 𝕂)) a hl hJ g)

theorem affineToUnit_preimage_Ico (a : ℝ) {l : ℝ} (hl : 0 < l) (s t : ℝ) :
    affineToUnit a l ⁻¹' Set.Ico s t = Set.Ico (a + l * s) (a + l * t) := by
  ext x
  simp only [affineToUnit, Set.mem_preimage, Set.mem_Ico, le_div_iff₀ hl, div_lt_iff₀ hl]
  constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> nlinarith

/-- Descending through a fixed dyadic interval, with the local index preserved. -/
def dyadicDilationIndex (J I : DyadicIndex) : DyadicIndex :=
  ⟨J.1 + I.1, (dyadicRefinementEquiv J.1 I.1).symm (J.2, I.2)⟩

@[simp] theorem dyadicDilationIndex_level (J I : DyadicIndex) :
    (dyadicDilationIndex J I).1 = J.1 + I.1 := rfl

@[simp] theorem dyadicDilationIndex_position (J I : DyadicIndex) :
    (dyadicDilationIndex J I).2.val = I.2.val + 2^I.1 * J.2.val := by
  simp [dyadicDilationIndex, dyadicRefinementEquiv, finProdFinEquiv]

theorem dyadicDilation_endpoint (J I : DyadicIndex) (c : ℝ) :
    (J.2 : ℝ) / (2 : ℝ)^J.1 + dyadicMeasure J * (((I.2 : ℝ) + c) / (2 : ℝ)^I.1) =
      (((dyadicDilationIndex J I).2 : ℝ) + c) / (2 : ℝ)^(dyadicDilationIndex J I).1 := by
  have hv : ((dyadicDilationIndex J I).2 : ℝ) =
      (I.2 : ℝ) + (2 : ℝ)^I.1 * (J.2 : ℝ) := by
    exact_mod_cast dyadicDilationIndex_position J I
  rw [hv, dyadicDilationIndex_level, pow_add]
  unfold dyadicMeasure
  field_simp
  ring

theorem dyadicDilation_haarLeft (J I : DyadicIndex) :
    affineToUnit ((J.2 : ℝ) / (2 : ℝ)^J.1) (dyadicMeasure J) ⁻¹' haarLeft I =
      haarLeft (dyadicDilationIndex J I) := by
  rw [haarLeft, affineToUnit_preimage_Ico _ (dyadicMeasure_pos J)]
  change Set.Ico _ _ = Set.Ico _ _
  rw [show (I.2 : ℝ) / (2 : ℝ)^I.1 = ((I.2 : ℝ) + 0) / (2 : ℝ)^I.1 by ring,
    dyadicDilation_endpoint J I 0, dyadicDilation_endpoint J I (1/2)]
  simp

theorem dyadicDilation_haarRight (J I : DyadicIndex) :
    affineToUnit ((J.2 : ℝ) / (2 : ℝ)^J.1) (dyadicMeasure J) ⁻¹' haarRight I =
      haarRight (dyadicDilationIndex J I) := by
  rw [haarRight, affineToUnit_preimage_Ico _ (dyadicMeasure_pos J)]
  change Set.Ico _ _ = Set.Ico _ _
  rw [dyadicDilation_endpoint J I (1/2), dyadicDilation_endpoint J I 1]

theorem haarFunction_affineToUnit (J I : DyadicIndex) (x : ℝ) :
    (haarFunction 𝕂) I (affineToUnit ((J.2 : ℝ) / (2 : ℝ)^J.1) (dyadicMeasure J) x) =
      (haarFunction 𝕂) (dyadicDilationIndex J I) x := by
  have hl : affineToUnit ((J.2 : ℝ) / (2 : ℝ)^J.1) (dyadicMeasure J) x ∈ haarLeft I ↔
      x ∈ haarLeft (dyadicDilationIndex J I) := by
    change x ∈ _ ⁻¹' haarLeft I ↔ _
    rw [dyadicDilation_haarLeft]
  have hr : affineToUnit ((J.2 : ℝ) / (2 : ℝ)^J.1) (dyadicMeasure J) x ∈ haarRight I ↔
      x ∈ haarRight (dyadicDilationIndex J I) := by
    change x ∈ _ ⁻¹' haarRight I ↔ _
    rw [dyadicDilation_haarRight]
  simp only [(haarFunction_eq (𝕂 := 𝕂)), Pi.sub_apply, Set.indicator]
  by_cases hL : x ∈ haarLeft (dyadicDilationIndex J I) <;>
    by_cases hR : x ∈ haarRight (dyadicDilationIndex J I) <;>
    simp_all only [ite_true, ite_false]

theorem dyadicInterval_eq_affine (J : DyadicIndex) :
    Set.Ico ((J.2 : ℝ) / (2 : ℝ)^J.1)
      ((J.2 : ℝ) / (2 : ℝ)^J.1 + dyadicMeasure J) = dyadicInterval J := by
  unfold dyadicInterval dyadicMeasure
  congr 1
  ring

def dyadicDilation (J : DyadicIndex) : (L1 𝕂) →ₗᵢ[𝕂] (L1 𝕂) :=
  (dilationL1LinearIsometry (𝕂 := 𝕂)) ((J.2 : ℝ) / (2 : ℝ)^J.1) (dyadicMeasure_pos J)
    (by rw [dyadicInterval_eq_affine]; exact dyadicInterval_subset_unit J)

theorem dyadicDilation_haarL1 (J I : DyadicIndex) :
    (dyadicDilation (𝕂 := 𝕂)) J ((haarL1 𝕂) I) = (2 : 𝕂)^J.1 • (haarL1 𝕂) (dyadicDilationIndex J I) := by
  have hsub : Set.Ico ((J.2 : ℝ) / (2 : ℝ)^J.1)
      ((J.2 : ℝ) / (2 : ℝ)^J.1 + dyadicMeasure J) ⊆ Set.Ico (0 : ℝ) 1 := by
    rw [dyadicInterval_eq_affine]
    exact dyadicInterval_subset_unit J
  apply Lp.ext
  change (dilationL1 (𝕂 := 𝕂)) _ (dyadicMeasure_pos J) hsub ((haarL1 𝕂) I) =ᵐ[unitIntervalMeasure] _
  refine ((coeFn_dilationL1 (𝕂 := 𝕂)) _ (dyadicMeasure_pos J) hsub ((haarL1 𝕂) I)).trans ?_
  refine ((dilationFunction_congr_ae (𝕂 := 𝕂)) ((haarL1_ae (𝕂 := 𝕂)) I) _ (dyadicMeasure_pos J) hsub).trans ?_
  filter_upwards [(haarL1_ae (𝕂 := 𝕂)) (dyadicDilationIndex J I),
    Lp.coeFn_smul ((2 : 𝕂)^J.1) ((haarL1 𝕂) (dyadicDilationIndex J I))] with x hh hs
  rw [hs, Pi.smul_apply, hh, smul_eq_mul]
  unfold dilationFunction
  rw [dyadicInterval_eq_affine]
  by_cases hx : x ∈ dyadicInterval J
  · rw [Set.indicator_of_mem hx, (haarFunction_affineToUnit (𝕂 := 𝕂))]
    simp [dyadicMeasure, RCLike.ofReal_pow, RCLike.ofReal_ofNat]
  · rw [Set.indicator_of_notMem hx]
    have hd : dyadicInterval (dyadicDilationIndex J I) ⊆ dyadicInterval J :=
      dyadic_descendant_subset J.1 I.1 J.2 I.2
    rw [(haarFunction_zero_off (𝕂 := 𝕂)) _ (fun hh => hx (hd hh)), mul_zero]

@[simp] theorem dyadicDilationIndex_even_iff (J I : DyadicIndex) (hJ : Even J.1) :
    Even (dyadicDilationIndex J I).1 ↔ Even I.1 := by
  rw [dyadicDilationIndex_level, Nat.even_add]
  simp [hJ]

@[simp] theorem dyadicDilationIndex_odd_iff (J I : DyadicIndex) (hJ : Odd J.1) :
    Even (dyadicDilationIndex J I).1 ↔ Odd I.1 := by
  rw [dyadicDilationIndex_level, Nat.even_add]
  have hn : ¬ Even J.1 := Nat.not_even_iff_odd.mpr hJ
  simp [hn, Nat.not_even_iff_odd]

theorem dyadicDilation_closed_span (J : DyadicIndex) (S : Set DyadicIndex) :
    ((Submodule.span 𝕂 ((haarL1 𝕂) '' S)).topologicalClosure).map
      ((dyadicDilation (𝕂 := 𝕂)) J).toLinearMap =
    (Submodule.span 𝕂 ((haarL1 𝕂) '' (dyadicDilationIndex J '' S))).topologicalClosure := by
  have hm : (Submodule.span 𝕂 ((haarL1 𝕂) '' S)).map ((dyadicDilation (𝕂 := 𝕂)) J).toLinearMap =
      Submodule.span 𝕂 ((haarL1 𝕂) '' (dyadicDilationIndex J '' S)) := by
    rw [Submodule.map_span]
    have he : ((dyadicDilation (𝕂 := 𝕂)) J).toLinearMap '' ((haarL1 𝕂) '' S) =
        (2 : 𝕂)^J.1 • ((haarL1 𝕂) '' (dyadicDilationIndex J '' S)) := by
      ext f
      constructor
      · rintro ⟨_, ⟨I, hI, rfl⟩, rfl⟩
        exact ⟨(haarL1 𝕂) (dyadicDilationIndex J I), ⟨_, ⟨I, hI, rfl⟩, rfl⟩,
          ((dyadicDilation_haarL1 (𝕂 := 𝕂)) J I).symm⟩
      · rintro ⟨_, ⟨_, ⟨I, hI, rfl⟩, rfl⟩, rfl⟩
        exact ⟨(haarL1 𝕂) I, ⟨I, hI, rfl⟩, (dyadicDilation_haarL1 (𝕂 := 𝕂)) J I⟩
    rw [he, Submodule.span_smul_eq_of_isUnit _ _ (isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num)))]
  rw [← hm]
  apply SetLike.coe_injective
  simp only [Submodule.map_coe, Submodule.topologicalClosure_coe]
  exact (((dyadicDilation (𝕂 := 𝕂)) J).isometry.isClosedEmbedding.closure_image_eq _).symm

theorem norm_add_of_disjoint_support (f g : (L1 𝕂)) (s t : Set ℝ)
    (hd : Disjoint s t)
    (hf : ∀ᵐ x ∂unitIntervalMeasure, x ∉ s → f x = 0)
    (hg : ∀ᵐ x ∂unitIntervalMeasure, x ∉ t → g x = 0) :
    ‖f + g‖ = ‖f‖ + ‖g‖ := by
  rw [MeasureTheory.L1.norm_eq_integral_norm, MeasureTheory.L1.norm_eq_integral_norm f,
    MeasureTheory.L1.norm_eq_integral_norm g, ← integral_add
      (MeasureTheory.L1.integrable_coeFn f).norm (MeasureTheory.L1.integrable_coeFn g).norm]
  apply integral_congr_ae
  filter_upwards [hf, hg, Lp.coeFn_add f g] with x hx hy ha
  rw [ha, Pi.add_apply]
  by_cases hs : x ∈ s
  · have ht : x ∉ t := fun ht => Set.disjoint_left.mp hd hs ht
    rw [hy ht, add_zero, norm_zero, add_zero]
  · rw [hx hs, zero_add, norm_zero, zero_add]

/-- Sum of normalized dilations on two distinct cells of a common level. -/
def dyadicDilationPair (n : ℕ) (j k : Fin (2^n)) (hjk : j ≠ k) :
    WithLp 1 ((L1 𝕂) × (L1 𝕂)) →ₗᵢ[𝕂] (L1 𝕂) where
  toFun f := (dyadicDilation (𝕂 := 𝕂)) ⟨n,j⟩ f.fst + (dyadicDilation (𝕂 := 𝕂)) ⟨n,k⟩ f.snd
  map_add' f g := by
    change (dyadicDilation (𝕂 := 𝕂)) ⟨n,j⟩ (f.fst + g.fst) + (dyadicDilation (𝕂 := 𝕂)) ⟨n,k⟩ (f.snd + g.snd) = _
    simp only [map_add]
    module
  map_smul' c f := by
    change (dyadicDilation (𝕂 := 𝕂)) ⟨n,j⟩ (c • f.fst) + (dyadicDilation (𝕂 := 𝕂)) ⟨n,k⟩ (c • f.snd) =
      c • ((dyadicDilation (𝕂 := 𝕂)) ⟨n,j⟩ f.fst + (dyadicDilation (𝕂 := 𝕂)) ⟨n,k⟩ f.snd)
    simp only [map_smul]
    module
  norm_map' f := by
    change ‖(dyadicDilation (𝕂 := 𝕂)) ⟨n,j⟩ f.fst + (dyadicDilation (𝕂 := 𝕂)) ⟨n,k⟩ f.snd‖ = ‖f‖
    rw [WithLp.prod_norm_eq_of_L1]
    rw [(norm_add_of_disjoint_support (𝕂 := 𝕂)) _ _ _ _ (dyadic_level_disjoint n hjk)]
    · simp only [LinearIsometry.norm_map]
    · have hh := (dilationL1_mem_intervalSupportedL1 (𝕂 := 𝕂))
        ((j : ℝ)/(2 : ℝ)^n) (dyadicMeasure_pos ⟨n,j⟩)
        (by rw [dyadicInterval_eq_affine ⟨n,j⟩]; exact dyadicInterval_subset_unit ⟨n,j⟩) f.fst
      change ∀ᵐ x ∂unitIntervalMeasure,
        x ∉ Set.Ico _ _ → ((dyadicDilation (𝕂 := 𝕂)) ⟨n,j⟩ f.fst) x = 0 at hh
      rw [dyadicInterval_eq_affine ⟨n,j⟩] at hh
      exact hh
    · have hh := (dilationL1_mem_intervalSupportedL1 (𝕂 := 𝕂))
        ((k : ℝ)/(2 : ℝ)^n) (dyadicMeasure_pos ⟨n,k⟩)
        (by rw [dyadicInterval_eq_affine ⟨n,k⟩]; exact dyadicInterval_subset_unit ⟨n,k⟩) f.snd
      change ∀ᵐ x ∂unitIntervalMeasure,
        x ∉ Set.Ico _ _ → ((dyadicDilation (𝕂 := 𝕂)) ⟨n,k⟩ f.snd) x = 0 at hh
      rw [dyadicInterval_eq_affine ⟨n,k⟩] at hh
      exact hh

theorem dyadicDilationIndex_half_exists (K : DyadicIndex) (hK : 0 < K.1) :
    ∃ j : Fin 2, ∃ I : DyadicIndex, I.1 + 1 = K.1 ∧
      dyadicDilationIndex ⟨1,j⟩ I = K := by
  rcases K with ⟨n,k⟩
  cases n with
  | zero => change 0 < 0 at hK; omega
  | succ n =>
    let k' : Fin (2^(1+n)) := Fin.cast (by congr 1; omega) k
    let p := dyadicRefinementEquiv 1 n k'
    refine ⟨p.1, ⟨n,p.2⟩, rfl, ?_⟩
    change (⟨1+n, (dyadicRefinementEquiv 1 n).symm
      ((dyadicRefinementEquiv 1 n k').1, (dyadicRefinementEquiv 1 n k').2)⟩ : DyadicIndex) = ⟨n+1,k⟩
    rw [Equiv.symm_apply_apply]
    apply Sigma.ext (show 1+n = n+1 by omega)
    exact (Fin.heq_ext_iff (by dsimp; congr 1; omega)).mpr rfl

theorem halfDilation_X₀_mem_X₁ (j : Fin 2) (f : (X₀ 𝕂)) :
    (dyadicDilation (𝕂 := 𝕂)) ⟨1,j⟩ f ∈ (X₁ 𝕂) := by
  have hf : (dyadicDilation (𝕂 := 𝕂)) ⟨1,j⟩ f ∈ (X₀ 𝕂).map ((dyadicDilation (𝕂 := 𝕂)) ⟨1,j⟩).toLinearMap :=
    ⟨f, f.property, rfl⟩
  change (dyadicDilation (𝕂 := 𝕂)) ⟨1,j⟩ f ∈
    ((Submodule.span 𝕂 ((haarL1 𝕂) '' {I : DyadicIndex | Even I.1})).topologicalClosure).map
      ((dyadicDilation (𝕂 := 𝕂)) ⟨1,j⟩).toLinearMap at hf
  rw [(dyadicDilation_closed_span (𝕂 := 𝕂))] at hf
  apply (Submodule.topologicalClosure_mono (Submodule.span_mono (show
    (haarL1 𝕂) '' (dyadicDilationIndex ⟨1,j⟩ '' {I : DyadicIndex | Even I.1}) ⊆
      (haarL1 𝕂) '' {I : DyadicIndex | Odd I.1} from ?_))) hf
  rintro _ ⟨_, ⟨I,hI,rfl⟩, rfl⟩
  refine ⟨dyadicDilationIndex ⟨1,j⟩ I, ?_, rfl⟩
  change Odd (1 + I.1)
  rcases hI with ⟨r,hr⟩
  exact ⟨r, by omega⟩

/-- The first half decomposition, with the actual sum norm on its domain. -/
def halfEvenSynthesis : WithLp 1 ((X₀ 𝕂) × (X₀ 𝕂)) →ₗᵢ[𝕂] (X₁ 𝕂) where
  toFun f := ⟨(dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ f.fst + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ f.snd,
    (X₁ 𝕂).add_mem ((halfDilation_X₀_mem_X₁ (𝕂 := 𝕂)) 0 f.fst) ((halfDilation_X₀_mem_X₁ (𝕂 := 𝕂)) 1 f.snd)⟩
  map_add' f g := by
    apply Subtype.ext
    change (dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ ((f.fst : (L1 𝕂)) + g.fst) +
      (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ ((f.snd : (L1 𝕂)) + g.snd) =
      ((dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ f.fst + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ f.snd) +
      ((dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ g.fst + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ g.snd)
    simp only [map_add]
    module
  map_smul' c f := by
    apply Subtype.ext
    change (dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ (c • (f.fst : (L1 𝕂))) +
      (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ (c • (f.snd : (L1 𝕂))) =
      c • ((dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ f.fst + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ f.snd)
    simp only [map_smul]
    module
  norm_map' f := by
    change ‖(dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ (f.fst : (L1 𝕂)) + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ (f.snd : (L1 𝕂))‖ = ‖f‖
    have hh := ((dyadicDilationPair (𝕂 := 𝕂)) 1 0 1 (by decide)).norm_map
      (WithLp.toLp 1 ((f.fst : (L1 𝕂)), (f.snd : (L1 𝕂))))
    change ‖(dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ (f.fst : (L1 𝕂)) + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ (f.snd : (L1 𝕂))‖ =
      ‖WithLp.toLp 1 ((f.fst : (L1 𝕂)), (f.snd : (L1 𝕂)))‖ at hh
    simpa only [WithLp.prod_norm_eq_of_L1, WithLp.toLp_fst, WithLp.toLp_snd,
      Submodule.norm_coe] using hh

theorem halfEvenSynthesis_surjective : Function.Surjective (halfEvenSynthesis (𝕂 := 𝕂)) := by
  let T := (X₁ 𝕂).subtypeₗᵢ.comp (halfEvenSynthesis (𝕂 := 𝕂))
  have : CompleteSpace (X₀ 𝕂) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hclosed : IsClosed (T.toLinearMap.range : Set (L1 𝕂)) :=
    T.isometry.isClosedEmbedding.isClosed_range
  have hgen : (haarL1 𝕂) '' {I : DyadicIndex | Odd I.1} ⊆ T.toLinearMap.range := by
    rintro _ ⟨K,hK,rfl⟩
    have hpos : 0 < K.1 := by rcases hK with ⟨r,hr⟩; omega
    obtain ⟨j,I,hlev,rfl⟩ := dyadicDilationIndex_half_exists K hpos
    have hI : Even I.1 := by
      have ho := hK
      change Odd (1 + I.1) at ho
      rcases ho with ⟨r,hr⟩
      exact ⟨r, by omega⟩
    let f : (X₀ 𝕂) := ⟨(1/2 : 𝕂) • (haarL1 𝕂) I,
      (X₀ 𝕂).smul_mem _ (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨I,hI,rfl⟩))⟩
    fin_cases j
    · refine ⟨WithLp.toLp 1 (f,0), ?_⟩
      change (dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ ((1/2 : 𝕂) • (haarL1 𝕂) I) + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ 0 = _
      rw [map_zero, add_zero, map_smul, (dyadicDilation_haarL1 (𝕂 := 𝕂)), smul_smul]
      norm_num
    · refine ⟨WithLp.toLp 1 (0,f), ?_⟩
      change (dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ 0 + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ ((1/2 : 𝕂) • (haarL1 𝕂) I) = _
      rw [map_zero, zero_add, map_smul, (dyadicDilation_haarL1 (𝕂 := 𝕂)), smul_smul]
      norm_num
  have hle : (X₁ 𝕂) ≤ T.toLinearMap.range :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hgen) hclosed
  intro f
  obtain ⟨g,hg⟩ := hle f.property
  exact ⟨g, Subtype.ext hg⟩

/-- The concrete half splitting of the odd Haar space. -/
def oddHalfEquiv : WithLp 1 ((X₀ 𝕂) × (X₀ 𝕂)) ≃ₗᵢ[𝕂] (X₁ 𝕂) :=
  LinearIsometryEquiv.ofSurjective (halfEvenSynthesis (𝕂 := 𝕂)) (halfEvenSynthesis_surjective (𝕂 := 𝕂))

def evenPositiveSpan : Submodule 𝕂 (L1 𝕂) :=
  (Submodule.span 𝕂 ((haarL1 𝕂) '' {I : DyadicIndex | Even I.1 ∧ 0 < I.1})).topologicalClosure

theorem halfDilation_X₁_mem_evenPositive (j : Fin 2) (f : (X₁ 𝕂)) :
    (dyadicDilation (𝕂 := 𝕂)) ⟨1,j⟩ f ∈ (evenPositiveSpan (𝕂 := 𝕂)) := by
  have hf : (dyadicDilation (𝕂 := 𝕂)) ⟨1,j⟩ f ∈ (X₁ 𝕂).map ((dyadicDilation (𝕂 := 𝕂)) ⟨1,j⟩).toLinearMap :=
    ⟨f, f.property, rfl⟩
  change (dyadicDilation (𝕂 := 𝕂)) ⟨1,j⟩ f ∈
    ((Submodule.span 𝕂 ((haarL1 𝕂) '' {I : DyadicIndex | Odd I.1})).topologicalClosure).map
      ((dyadicDilation (𝕂 := 𝕂)) ⟨1,j⟩).toLinearMap at hf
  rw [(dyadicDilation_closed_span (𝕂 := 𝕂))] at hf
  apply (Submodule.topologicalClosure_mono (Submodule.span_mono (show
    (haarL1 𝕂) '' (dyadicDilationIndex ⟨1,j⟩ '' {I : DyadicIndex | Odd I.1}) ⊆
      (haarL1 𝕂) '' {I : DyadicIndex | Even I.1 ∧ 0 < I.1} from ?_))) hf
  rintro _ ⟨_, ⟨I,hI,rfl⟩, rfl⟩
  refine ⟨dyadicDilationIndex ⟨1,j⟩ I, ?_, rfl⟩
  change Even (1 + I.1) ∧ 0 < 1 + I.1
  rcases hI with ⟨r,hr⟩
  exact ⟨⟨r+1, by omega⟩, by omega⟩

/-- The first half decomposition, with the actual sum norm on its domain. -/
def halfOddSynthesis : WithLp 1 ((X₁ 𝕂) × (X₁ 𝕂)) →ₗᵢ[𝕂] (evenPositiveSpan (𝕂 := 𝕂)) where
  toFun f := ⟨(dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ f.fst + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ f.snd,
    (evenPositiveSpan (𝕂 := 𝕂)).add_mem ((halfDilation_X₁_mem_evenPositive (𝕂 := 𝕂)) 0 f.fst) ((halfDilation_X₁_mem_evenPositive (𝕂 := 𝕂)) 1 f.snd)⟩
  map_add' f g := by
    apply Subtype.ext
    change (dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ ((f.fst : (L1 𝕂)) + g.fst) +
      (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ ((f.snd : (L1 𝕂)) + g.snd) =
      ((dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ f.fst + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ f.snd) +
      ((dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ g.fst + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ g.snd)
    simp only [map_add]
    module
  map_smul' c f := by
    apply Subtype.ext
    change (dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ (c • (f.fst : (L1 𝕂))) +
      (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ (c • (f.snd : (L1 𝕂))) =
      c • ((dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ f.fst + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ f.snd)
    simp only [map_smul]
    module
  norm_map' f := by
    change ‖(dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ (f.fst : (L1 𝕂)) + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ (f.snd : (L1 𝕂))‖ = ‖f‖
    have hh := ((dyadicDilationPair (𝕂 := 𝕂)) 1 0 1 (by decide)).norm_map
      (WithLp.toLp 1 ((f.fst : (L1 𝕂)), (f.snd : (L1 𝕂))))
    change ‖(dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ (f.fst : (L1 𝕂)) + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ (f.snd : (L1 𝕂))‖ =
      ‖WithLp.toLp 1 ((f.fst : (L1 𝕂)), (f.snd : (L1 𝕂)))‖ at hh
    simpa only [WithLp.prod_norm_eq_of_L1, WithLp.toLp_fst, WithLp.toLp_snd,
      Submodule.norm_coe] using hh

theorem halfOddSynthesis_surjective : Function.Surjective (halfOddSynthesis (𝕂 := 𝕂)) := by
  let T := (evenPositiveSpan (𝕂 := 𝕂)).subtypeₗᵢ.comp (halfOddSynthesis (𝕂 := 𝕂))
  have : CompleteSpace (X₁ 𝕂) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hclosed : IsClosed (T.toLinearMap.range : Set (L1 𝕂)) :=
    T.isometry.isClosedEmbedding.isClosed_range
  have hgen : (haarL1 𝕂) '' {I : DyadicIndex | Even I.1 ∧ 0 < I.1} ⊆ T.toLinearMap.range := by
    rintro _ ⟨K,hK,rfl⟩
    have hpos : 0 < K.1 := hK.2
    obtain ⟨j,I,hlev,rfl⟩ := dyadicDilationIndex_half_exists K hpos
    have hI : Odd I.1 := by
      have ho := hK.1
      change Even (1 + I.1) at ho
      rcases ho with ⟨r,hr⟩
      exact ⟨r-1, by omega⟩
    let f : (X₁ 𝕂) := ⟨(1/2 : 𝕂) • (haarL1 𝕂) I,
      (X₁ 𝕂).smul_mem _ (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨I,hI,rfl⟩))⟩
    fin_cases j
    · refine ⟨WithLp.toLp 1 (f,0), ?_⟩
      change (dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ ((1/2 : 𝕂) • (haarL1 𝕂) I) + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ 0 = _
      rw [map_zero, add_zero, map_smul, (dyadicDilation_haarL1 (𝕂 := 𝕂)), smul_smul]
      norm_num
    · refine ⟨WithLp.toLp 1 (0,f), ?_⟩
      change (dyadicDilation (𝕂 := 𝕂)) ⟨1,0⟩ 0 + (dyadicDilation (𝕂 := 𝕂)) ⟨1,1⟩ ((1/2 : 𝕂) • (haarL1 𝕂) I) = _
      rw [map_zero, zero_add, map_smul, (dyadicDilation_haarL1 (𝕂 := 𝕂)), smul_smul]
      norm_num
  have hle : (evenPositiveSpan (𝕂 := 𝕂)) ≤ T.toLinearMap.range :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hgen) hclosed
  intro f
  obtain ⟨g,hg⟩ := hle f.property
  exact ⟨g, Subtype.ext hg⟩

def evenPositiveHalfEquiv : WithLp 1 ((X₁ 𝕂) × (X₁ 𝕂)) ≃ₗᵢ[𝕂] (evenPositiveSpan (𝕂 := 𝕂)) :=
  LinearIsometryEquiv.ofSurjective (halfOddSynthesis (𝕂 := 𝕂)) (halfOddSynthesis_surjective (𝕂 := 𝕂))

theorem evenPositiveSpan_le_X₀ : (evenPositiveSpan (𝕂 := 𝕂)) ≤ (X₀ 𝕂) :=
  Submodule.topologicalClosure_mono (Submodule.span_mono (Set.image_mono (by
    intro I hI
    exact hI.1)))

def rootHaar : (X₀ 𝕂) := ⟨(haarL1 𝕂) ⟨0,0⟩,
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨0,0⟩, ⟨0,rfl⟩, rfl⟩)⟩

theorem haarCoefficient_rootHaar : (haarCoefficient (𝕂 := 𝕂)) ⟨0,0⟩ (rootHaar (𝕂 := 𝕂)) = 1 := by
  change (haarCoefficient (𝕂 := 𝕂)) ⟨0,0⟩ ((haarL1 𝕂) ⟨0,0⟩) = 1
  rw [(haarCoefficient_haar (𝕂 := 𝕂))]
  norm_num [dyadicMeasure]

theorem rootCoefficient_evenPositive (f : (evenPositiveSpan (𝕂 := 𝕂))) :
    (haarCoefficient (𝕂 := 𝕂)) ⟨0,0⟩ f = 0 := by
  apply (closedSpan_vanish (𝕂 := 𝕂)) ((haarCoefficient (𝕂 := 𝕂)) ⟨0,0⟩) _ _ f.property
  rintro _ ⟨I,hI,rfl⟩
  rw [(haarCoefficient_haar (𝕂 := 𝕂)), if_neg]
  intro he
  have hi := congrArg Sigma.fst he
  dsimp at hi
  have := hI.2
  omega

def rootRemainder : (L1 𝕂) →L[𝕂] (L1 𝕂) :=
  ContinuousLinearMap.id 𝕂 (L1 𝕂) - ((haarCoefficient (𝕂 := 𝕂)) ⟨0,0⟩).smulRight ((haarL1 𝕂) ⟨0,0⟩)

theorem rootRemainder_mem_evenPositive (f : (X₀ 𝕂)) : (rootRemainder (𝕂 := 𝕂)) f ∈ (evenPositiveSpan (𝕂 := 𝕂)) := by
  have hc : IsClosed (((evenPositiveSpan (𝕂 := 𝕂)).comap (rootRemainder (𝕂 := 𝕂)).toLinearMap : Submodule 𝕂 (L1 𝕂)) : Set (L1 𝕂)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (rootRemainder (𝕂 := 𝕂)).continuous
  apply (Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) hc) f.property
  rintro _ ⟨I,hI,rfl⟩
  change (haarL1 𝕂) I - (haarCoefficient (𝕂 := 𝕂)) ⟨0,0⟩ ((haarL1 𝕂) I) • (haarL1 𝕂) ⟨0,0⟩ ∈ (evenPositiveSpan (𝕂 := 𝕂))
  by_cases hi : I = ⟨0,0⟩
  · subst I
    rw [(haarCoefficient_haar (𝕂 := 𝕂))]
    norm_num [dyadicMeasure]
  · rw [(haarCoefficient_haar (𝕂 := 𝕂)), if_neg (Ne.symm hi), zero_smul, sub_zero]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨I,⟨hI,by
      by_contra hn
      have hlevel : I.1 = 0 := by omega
      apply hi
      rcases I with ⟨n,k⟩
      dsimp at hlevel
      subst n
      congr
      exact Fin.eq_zero k⟩,rfl⟩)

/-- Reattach the root Haar coordinate to the positive-depth even part. -/
def evenRootSynthesis : 𝕂 × (evenPositiveSpan (𝕂 := 𝕂)) →L[𝕂] (X₀ 𝕂) :=
  ((ContinuousLinearMap.fst 𝕂 𝕂 (evenPositiveSpan (𝕂 := 𝕂))).smulRight (rootHaar (𝕂 := 𝕂))) +
    ((Submodule.inclusion (evenPositiveSpan_le_X₀ (𝕂 := 𝕂))).mkContinuous 1 (by
      intro f
      change ‖(f : (L1 𝕂))‖ ≤ 1 * ‖(f : (L1 𝕂))‖
      simp)).comp (ContinuousLinearMap.snd 𝕂 𝕂 (evenPositiveSpan (𝕂 := 𝕂)))

theorem evenRootSynthesis_bijective : Function.Bijective (evenRootSynthesis (𝕂 := 𝕂)) := by
  constructor
  · intro p q hpq
    have hc := congrArg (fun f : (X₀ 𝕂) => (haarCoefficient (𝕂 := 𝕂)) ⟨0,0⟩ f) hpq
    change (haarCoefficient (𝕂 := 𝕂)) ⟨0,0⟩ (p.1 • ((rootHaar (𝕂 := 𝕂)) : (L1 𝕂)) + p.2) =
      (haarCoefficient (𝕂 := 𝕂)) ⟨0,0⟩ (q.1 • ((rootHaar (𝕂 := 𝕂)) : (L1 𝕂)) + q.2) at hc
    simp only [map_add, map_smul, (haarCoefficient_rootHaar (𝕂 := 𝕂)), (rootCoefficient_evenPositive (𝕂 := 𝕂)),
      smul_eq_mul, mul_one, add_zero] at hc
    apply Prod.ext hc
    apply Subtype.ext
    have hv := congrArg (fun f : (X₀ 𝕂) => (f : (L1 𝕂))) hpq
    change p.1 • ((rootHaar (𝕂 := 𝕂)) : (L1 𝕂)) + p.2 = q.1 • ((rootHaar (𝕂 := 𝕂)) : (L1 𝕂)) + q.2 at hv
    rw [hc] at hv
    exact add_left_cancel hv
  · intro f
    refine ⟨((haarCoefficient (𝕂 := 𝕂)) ⟨0,0⟩ f, ⟨(rootRemainder (𝕂 := 𝕂)) f, (rootRemainder_mem_evenPositive (𝕂 := 𝕂)) f⟩), ?_⟩
    apply Subtype.ext
    change (haarCoefficient (𝕂 := 𝕂)) ⟨0,0⟩ f • (haarL1 𝕂) ⟨0,0⟩ +
      ((f : (L1 𝕂)) - (haarCoefficient (𝕂 := 𝕂)) ⟨0,0⟩ f • (haarL1 𝕂) ⟨0,0⟩) = f
    module

def evenRootEquiv : (𝕂 × (evenPositiveSpan (𝕂 := 𝕂))) ≃L[𝕂] (X₀ 𝕂) := by
  haveI : CompleteSpace (evenPositiveSpan (𝕂 := 𝕂)) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have : CompleteSpace (X₀ 𝕂) := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  exact ContinuousLinearEquiv.ofBijective (evenRootSynthesis (𝕂 := 𝕂))
    (LinearMap.ker_eq_bot.mpr (evenRootSynthesis_bijective (𝕂 := 𝕂)).1)
    (LinearMap.range_eq_top.mpr (evenRootSynthesis_bijective (𝕂 := 𝕂)).2)

/-- The even space splits into its root coordinate and two odd copies.
The ordinary product has the maximum norm; this is a bounded equivalence. -/
def evenHalfEquiv : (X₀ 𝕂) ≃L[𝕂] 𝕂 × ((X₁ 𝕂) × (X₁ 𝕂)) :=
  (evenRootEquiv (𝕂 := 𝕂)).symm.trans ((ContinuousLinearEquiv.refl 𝕂 𝕂).prodCongr
    ((evenPositiveHalfEquiv (𝕂 := 𝕂)).symm.toContinuousLinearEquiv.trans
      (WithLp.prodContinuousLinearEquiv 1 𝕂 (X₁ 𝕂) (X₁ 𝕂))))

end EvenOddHaarLevels
