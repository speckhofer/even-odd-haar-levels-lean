import EvenOddHaarLevels.DyadicAveraging

noncomputable section
open MeasureTheory
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

/-- Finite Haar synthesis on the actual canonical L¹ classes. -/
def haarSynthesis : (DyadicIndex →₀ 𝕂) →ₗ[𝕂] (L1 𝕂) :=
  Finsupp.linearCombination 𝕂 (haarL1 𝕂)

theorem haarSynthesis_coefficient (c : DyadicIndex →₀ 𝕂) (I : DyadicIndex) :
    (haarCoefficient (𝕂 := 𝕂)) I ((haarSynthesis (𝕂 := 𝕂)) c) = c I * dyadicMeasure I := by
  classical
  by_cases hI : I ∈ c.support
  · simp [haarSynthesis, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_smul, (haarCoefficient_haar (𝕂 := 𝕂)), smul_eq_mul, hI]
  · have hc : c I = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hI
    simp [haarSynthesis, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_smul, (haarCoefficient_haar (𝕂 := 𝕂)), smul_eq_mul, hI, hc]

theorem haarSynthesis_injective : Function.Injective (haarSynthesis (𝕂 := 𝕂)) := by
  intro c d h
  ext I
  have he := congrArg ((haarCoefficient (𝕂 := 𝕂)) I) h
  rw [(haarSynthesis_coefficient (𝕂 := 𝕂)), (haarSynthesis_coefficient (𝕂 := 𝕂))] at he
  exact mul_right_cancel₀ (RCLike.ofReal_ne_zero.mpr (dyadicMeasure_pos I).ne') he

theorem haarSynthesis_range : (haarSynthesis (𝕂 := 𝕂)).range = Submodule.span 𝕂 (Set.range (haarL1 𝕂)) :=
  Finsupp.range_linearCombination 𝕂

theorem haarSynthesis_mean_zero (c : DyadicIndex →₀ 𝕂) : (meanFunctional (𝕂 := 𝕂)) ((haarSynthesis (𝕂 := 𝕂)) c) = 0 := by
  classical
  simp [haarSynthesis, Finsupp.linearCombination_apply, Finsupp.sum, (meanFunctional_haar (𝕂 := 𝕂))]

theorem haarSynthesis_range_closure : (haarSynthesis (𝕂 := 𝕂)).range.topologicalClosure = (H₀ (𝕂 := 𝕂)) := by
  rw [(haarSynthesis_range (𝕂 := 𝕂))]
  have he : Set.range (haarL1 𝕂) = (haarL1 𝕂) '' {I : DyadicIndex | I.1 ∈ (Set.univ : Set ℕ)} := by simp
  rw [he]
  exact (haar_dense_meanZero (𝕂 := 𝕂))

/-- The algebraic diagonal action on the uniquely defined finite coefficients. -/
def haarMultiplierCoefficients (d : DyadicIndex → 𝕂) :
    (DyadicIndex →₀ 𝕂) →ₗ[𝕂] (DyadicIndex →₀ 𝕂) where
  toFun c := Finsupp.onFinset c.support (fun I => d I * c I) (by
    intro I hI
    apply Finsupp.mem_support_iff.mpr
    exact fun hc => hI (by rw [hc, mul_zero]))
  map_add' c e := by ext I; simp [mul_add]
  map_smul' a c := by ext I; simp [mul_left_comm]

@[simp] theorem haarMultiplierCoefficients_apply (d : DyadicIndex → 𝕂)
    (c : DyadicIndex →₀ 𝕂) (I : DyadicIndex) : (haarMultiplierCoefficients (𝕂 := 𝕂)) d c I = d I * c I := rfl

theorem haarMultiplierCoefficients_idempotent (d : DyadicIndex → 𝕂)
    (hd : ∀ I, d I = 0 ∨ d I = 1) (c : DyadicIndex →₀ 𝕂) :
    (haarMultiplierCoefficients (𝕂 := 𝕂)) d ((haarMultiplierCoefficients (𝕂 := 𝕂)) d c) = (haarMultiplierCoefficients (𝕂 := 𝕂)) d c := by
  ext I
  rcases hd I with hi | hi <;> simp [hi]

def haarPolynomialFunction (c : DyadicIndex →₀ 𝕂) : ℝ → 𝕂 :=
  fun x => ∑ I ∈ c.support, c I * (haarFunction 𝕂) I x

theorem haarPolynomialFunction_integrable (c : DyadicIndex →₀ 𝕂) :
    Integrable ((haarPolynomialFunction (𝕂 := 𝕂)) c) unitIntervalMeasure :=
  integrable_finsetSum c.support (fun I _ => (haarFunction_integrable 𝕂 I).const_mul (c I))

theorem haarSynthesis_ae (c : DyadicIndex →₀ 𝕂) :
    ((haarSynthesis (𝕂 := 𝕂)) c : ℝ → 𝕂) =ᵐ[unitIntervalMeasure] (haarPolynomialFunction (𝕂 := 𝕂)) c := by
  have hterm : ∀ᵐ x ∂unitIntervalMeasure, ∀ I : DyadicIndex,
      (c I • (haarL1 𝕂) I : (L1 𝕂)) x = c I * (haarFunction 𝕂) I x := by
    apply ae_all_iff.mpr
    intro I
    filter_upwards [Lp.coeFn_smul (c I) ((haarL1 𝕂) I), (haarL1_ae (𝕂 := 𝕂)) I] with x hs hi
    simpa [hi] using hs
  have hsum := Lp.coeFn_finsetSum c.support (fun I => c I • (haarL1 𝕂) I)
  filter_upwards [hsum,hterm] with x hs ht
  change (∑ I ∈ c.support, c I • (haarL1 𝕂) I : (L1 𝕂)) x = _
  rw [hs]
  simp only [Finset.sum_apply, haarPolynomialFunction]
  exact Finset.sum_congr rfl (fun I _ => ht I)

theorem haarSynthesis_norm_integral (c : DyadicIndex →₀ 𝕂) :
    ‖(haarSynthesis (𝕂 := 𝕂)) c‖ = ∫ x, ‖(haarPolynomialFunction (𝕂 := 𝕂)) c x‖ ∂unitIntervalMeasure := by
  rw [MeasureTheory.L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [(haarSynthesis_ae (𝕂 := 𝕂)) c] with x hx
  rw [hx]

/-- Deleting a deepest Haar term cannot increase the L¹ norm when the remainder
is constant on its support. This is the local analytic step of finite deletion. -/
theorem haar_delete_term_integral_norm (I : DyadicIndex) (v : ℝ → 𝕂)
    (hv : Integrable v unitIntervalMeasure) (c a : 𝕂)
    (hconst : ∀ x ∈ dyadicInterval I, v x = c) :
    (∫ x, ‖v x‖ ∂unitIntervalMeasure) ≤
      ∫ x, ‖v x + a * (haarFunction 𝕂) I x‖ ∂unitIntervalMeasure := by
  have hw : Integrable (fun x => v x + a * (haarFunction 𝕂) I x) unitIntervalMeasure :=
    hv.add ((haarFunction_integrable 𝕂 I).const_mul a)
  have hleft : (∫ x in haarLeft I, ‖v x + a * (haarFunction 𝕂) I x‖ ∂unitIntervalMeasure) =
      (dyadicMeasure I / 2) * ‖c+a‖ := by
    calc
      _ = ∫ _ in haarLeft I, ‖c+a‖ ∂unitIntervalMeasure := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro x hx
        change ‖v x + a * (haarFunction 𝕂) I x‖ = ‖c+a‖
        have hr := Set.disjoint_left.mp (haar_halves_disjoint I) hx
        rw [hconst x (haarLeft_subset I hx)]
        simp only [(haarFunction_eq (𝕂 := 𝕂)), Pi.sub_apply, Set.indicator_of_mem (show x ∈ haarLeft I from hx),
          Set.indicator_of_notMem hr, sub_zero, mul_one]
      _ = _ := by rw [setIntegral_const, (haar_halves_measure I).1, smul_eq_mul]
  have hright : (∫ x in haarRight I, ‖v x + a * (haarFunction 𝕂) I x‖ ∂unitIntervalMeasure) =
      (dyadicMeasure I / 2) * ‖c-a‖ := by
    calc
      _ = ∫ _ in haarRight I, ‖c-a‖ ∂unitIntervalMeasure := by
        apply setIntegral_congr_fun measurableSet_Ico
        intro x hx
        change ‖v x + a * (haarFunction 𝕂) I x‖ = ‖c-a‖
        have hl := Set.disjoint_left.mp (haar_halves_disjoint I).symm hx
        rw [hconst x (haarRight_subset I hx)]
        simp only [(haarFunction_eq (𝕂 := 𝕂)), Pi.sub_apply, Set.indicator_of_mem (show x ∈ haarRight I from hx),
          Set.indicator_of_notMem hl, zero_sub, mul_neg, mul_one]
        simp [sub_eq_add_neg]
      _ = _ := by rw [setIntegral_const, (haar_halves_measure I).2, smul_eq_mul]
  have hinside : (∫ x in dyadicInterval I, ‖v x‖ ∂unitIntervalMeasure) = dyadicMeasure I * ‖c‖ := by
    calc
      _ = ∫ _ in dyadicInterval I, ‖c‖ ∂unitIntervalMeasure := by
        apply setIntegral_congr_fun (dyadicInterval_measurable I)
        intro x hx
        simp [hconst x hx]
      _ = _ := by rw [setIntegral_const, dyadicInterval_real_measure, smul_eq_mul]
  have hout : (∫ x in (dyadicInterval I)ᶜ, ‖v x + a * (haarFunction 𝕂) I x‖ ∂unitIntervalMeasure) =
      ∫ x in (dyadicInterval I)ᶜ, ‖v x‖ ∂unitIntervalMeasure := by
    apply setIntegral_congr_fun (dyadicInterval_measurable I).compl
    intro x hx
    change ‖v x + a * (haarFunction 𝕂) I x‖ = ‖v x‖
    rw [(haarFunction_zero_off (𝕂 := 𝕂)) I hx, mul_zero, add_zero]
  have hsplit := setIntegral_union (haar_halves_disjoint I)
    (show MeasurableSet (haarRight I) from measurableSet_Ico) hw.norm.integrableOn hw.norm.integrableOn
  rw [haar_halves_union, hleft, hright] at hsplit
  have hold := integral_add_compl (dyadicInterval_measurable I) hv.norm
  have hnew := integral_add_compl (dyadicInterval_measurable I) hw.norm
  rw [hinside] at hold
  rw [hsplit, hout] at hnew
  have htri : 2*‖c‖ ≤ ‖c+a‖+‖c-a‖ := by
    have ht := norm_add_le (c+a) (c-a)
    have he : (c+a)+(c-a)=2*c := by ring
    rw [he, norm_mul] at ht
    norm_num at ht
    exact ht
  have hm : dyadicMeasure I * ‖c‖ ≤ (dyadicMeasure I/2)*‖c+a‖ + (dyadicMeasure I/2)*‖c-a‖ := by
    nlinarith [mul_nonneg (dyadicMeasure_pos I).le (show 0 ≤ ‖c+a‖+‖c-a‖-2*‖c‖ by linarith)]
  linarith

theorem haarPolynomial_constant (I : DyadicIndex) (c : DyadicIndex →₀ 𝕂)
    (hgeom : ∀ J ∈ c.support, J.1 < I.1 ∨ Disjoint (dyadicInterval J) (dyadicInterval I)) :
    ∃ a : 𝕂, ∀ x ∈ dyadicInterval I, (haarPolynomialFunction (𝕂 := 𝕂)) c x = a := by
  classical
  have hterm (J : DyadicIndex) (hJ : J ∈ c.support) :
      ∃ a : 𝕂, ∀ x ∈ dyadicInterval I, (haarFunction 𝕂) J x = a := by
    rcases hgeom J hJ with hl | hd
    · exact (haar_constant_on_deeper (𝕂 := 𝕂)) J I hl
    · exact ⟨0, fun x hx => (haarFunction_zero_off (𝕂 := 𝕂)) J (Set.disjoint_left.mp hd.symm hx)⟩
  have hs : ∀ F : Finset DyadicIndex, F ⊆ c.support →
      ∃ a : 𝕂, ∀ x ∈ dyadicInterval I, (∑ J ∈ F, c J * (haarFunction 𝕂) J x) = a := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro _; exact ⟨0, fun _ _ => by simp⟩
    | @insert J F hJF ih =>
      intro hF
      obtain ⟨a,ha⟩ := hterm J (hF (Finset.mem_insert_self _ _))
      obtain ⟨b,hb⟩ := ih (fun K hK => hF (Finset.mem_insert_of_mem hK))
      refine ⟨c J * a + b, fun x hx => ?_⟩
      rw [Finset.sum_insert hJF, ha x hx, hb x hx]
  exact hs c.support (fun _ h => h)

theorem haar_add_term_norm (I : DyadicIndex) (c : DyadicIndex →₀ 𝕂) (a : 𝕂)
    (hgeom : ∀ J ∈ c.support, J.1 < I.1 ∨ Disjoint (dyadicInterval J) (dyadicInterval I)) :
    ‖(haarSynthesis (𝕂 := 𝕂)) c‖ ≤ ‖(haarSynthesis (𝕂 := 𝕂)) c + a • (haarL1 𝕂) I‖ := by
  obtain ⟨b,hb⟩ := (haarPolynomial_constant (𝕂 := 𝕂)) I c hgeom
  rw [(haarSynthesis_norm_integral (𝕂 := 𝕂)), MeasureTheory.L1.norm_eq_integral_norm]
  have hraw : (∫ x, ‖((haarSynthesis (𝕂 := 𝕂)) c + a • (haarL1 𝕂) I : (L1 𝕂)) x‖ ∂unitIntervalMeasure) =
      ∫ x, ‖(haarPolynomialFunction (𝕂 := 𝕂)) c x + a * (haarFunction 𝕂) I x‖ ∂unitIntervalMeasure := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add ((haarSynthesis (𝕂 := 𝕂)) c) (a • (haarL1 𝕂) I),
      Lp.coeFn_smul a ((haarL1 𝕂) I), (haarSynthesis_ae (𝕂 := 𝕂)) c, (haarL1_ae (𝕂 := 𝕂)) I] with x hadd hsm hc hi
    rw [hadd]
    change ‖(haarSynthesis (𝕂 := 𝕂)) c x + (a • (haarL1 𝕂) I : (L1 𝕂)) x‖ = _
    rw [hc, hsm]
    simp [hi]
  rw [hraw]
  exact (haar_delete_term_integral_norm (𝕂 := 𝕂)) I _ ((haarPolynomialFunction_integrable (𝕂 := 𝕂)) c) b a hb

theorem dyadic_disjoint_or_descendant (I J : DyadicIndex) (h : I.1 ≤ J.1) :
    Disjoint (dyadicInterval I) (dyadicInterval J) ∨ dyadicInterval J ⊆ dyadicInterval I := by
  let A := dyadicAncestor J I.1 h
  have hs := dyadicAncestor_contains J I.1 h
  by_cases he : A.2 = I.2
  · right
    have ha : A = I := Sigma.ext rfl (heq_of_eq he)
    rwa [← ha]
  · left
    exact (dyadic_level_disjoint I.1 (Ne.symm he)).mono_right hs

theorem dyadic_disjoint_of_same_level (I J : DyadicIndex) (h : I.1 = J.1) (hne : I ≠ J) :
    Disjoint (dyadicInterval I) (dyadicInterval J) := by
  cases I with | mk n k =>
    cases J with | mk m l =>
      dsimp at h
      subst m
      apply dyadic_level_disjoint
      intro he
      apply hne
      cases he
      rfl

/-- Finite deletion in decreasing depth, for a multiplier whose zero set contains
all descendants. The child-closure version follows by propagation on the tree. -/
theorem haarMultiplier_finite_contract (d : DyadicIndex → 𝕂)
    (hd : ∀ I, d I = 0 ∨ d I = 1)
    (hdown : ∀ I J, I.1 ≤ J.1 → dyadicInterval J ⊆ dyadicInterval I → d I = 0 → d J = 0)
    (c : DyadicIndex →₀ 𝕂) :
    ‖(haarSynthesis (𝕂 := 𝕂)) ((haarMultiplierCoefficients (𝕂 := 𝕂)) d c)‖ ≤ ‖(haarSynthesis (𝕂 := 𝕂)) c‖ := by
  classical
  let K (c : DyadicIndex →₀ 𝕂) := c.support.filter (fun I => d I = 0)
  have main : ∀ n : ℕ, ∀ c : DyadicIndex →₀ 𝕂, (K c).card = n →
      ‖(haarSynthesis (𝕂 := 𝕂)) ((haarMultiplierCoefficients (𝕂 := 𝕂)) d c)‖ ≤ ‖(haarSynthesis (𝕂 := 𝕂)) c‖ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hn
      by_cases hK : (K c).Nonempty
      · obtain ⟨I,hIK,hmax⟩ := Finset.exists_max_image (K c) (fun I => I.1) hK
        have hIc : I ∈ c.support := (Finset.mem_filter.mp hIK).1
        have hId : d I = 0 := (Finset.mem_filter.mp hIK).2
        have hgeom : ∀ J ∈ (c.erase I).support,
            J.1 < I.1 ∨ Disjoint (dyadicInterval J) (dyadicInterval I) := by
          intro J hJ
          have hJc : J ∈ c.support ∧ J ≠ I := by
            simpa only [Finsupp.support_erase, Finset.mem_erase, and_comm] using hJ
          by_cases hl : J.1 < I.1
          · exact Or.inl hl
          · right
            by_cases he : I.1 = J.1
            · exact (dyadic_disjoint_of_same_level I J he (Ne.symm hJc.2)).symm
            · rcases dyadic_disjoint_or_descendant I J (by omega) with hdj | hs
              · exact hdj.symm
              · have hJd := hdown I J (by omega) hs hId
                have hm := hmax J (Finset.mem_filter.mpr ⟨hJc.1,hJd⟩)
                omega
        have hKe : K (c.erase I) = (K c).erase I := by
          simp [K, Finsupp.support_erase, Finset.filter_erase]
        have hlt : (K (c.erase I)).card < n := by
          rw [hKe, ← hn]
          exact Finset.card_erase_lt_of_mem hIK
        have hb := ih _ hlt (c.erase I) rfl
        have hdc : (haarMultiplierCoefficients (𝕂 := 𝕂)) d (c.erase I) = (haarMultiplierCoefficients (𝕂 := 𝕂)) d c := by
          ext J
          by_cases he : J = I
          · subst J; simp [hId]
          · simp [he]
        have hsplit : (haarSynthesis (𝕂 := 𝕂)) (c.erase I) + c I • (haarL1 𝕂) I = (haarSynthesis (𝕂 := 𝕂)) c := by
          have he := congrArg (haarSynthesis (𝕂 := 𝕂)) (Finsupp.erase_add_single I c)
          simpa only [map_add, haarSynthesis, Finsupp.linearCombination_single] using he
        rw [hdc] at hb
        exact hb.trans (hsplit ▸ (haar_add_term_norm (𝕂 := 𝕂)) I (c.erase I) (c I) hgeom)
      · have he : (haarMultiplierCoefficients (𝕂 := 𝕂)) d c = c := by
          ext I
          by_cases hc : c I = 0
          · simp [hc]
          · have hnot : d I ≠ 0 := fun hi => hK ⟨I,Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hc,hi⟩⟩
            rcases hd I with hi | hi
            · exact False.elim (hnot hi)
            · simp [hi]
        rw [he]
  exact main _ c rfl

instance : CompleteSpace (H₀ (𝕂 := 𝕂)) :=
  (show IsClosed ((H₀ (𝕂 := 𝕂)) : Set (L1 𝕂)) from (meanFunctional (𝕂 := 𝕂)).isClosed_ker).completeSpace_coe

def haarSynthesisH0 : (DyadicIndex →₀ 𝕂) →ₗ[𝕂] (H₀ (𝕂 := 𝕂)) :=
  (haarSynthesis (𝕂 := 𝕂)).codRestrict (H₀ (𝕂 := 𝕂)) (haarSynthesis_mean_zero (𝕂 := 𝕂))

theorem haarSynthesisH0_dense : DenseRange (haarSynthesisH0 (𝕂 := 𝕂)) := by
  change Dense (Set.range (haarSynthesisH0 (𝕂 := 𝕂)))
  apply Topology.IsInducing.subtypeVal.dense_iff.mpr
  have he : Subtype.val '' Set.range (haarSynthesisH0 (𝕂 := 𝕂)) = Set.range (haarSynthesis (𝕂 := 𝕂)) := by
    ext x
    constructor
    · rintro ⟨y,⟨c,rfl⟩,rfl⟩
      exact ⟨c,rfl⟩
    · rintro ⟨c,rfl⟩
      exact ⟨(haarSynthesisH0 (𝕂 := 𝕂)) c,⟨c,rfl⟩,rfl⟩
  change ∀ x : (H₀ (𝕂 := 𝕂)), (x : (L1 𝕂)) ∈ closure (Subtype.val '' Set.range (haarSynthesisH0 (𝕂 := 𝕂)))
  intro x
  rw [he]
  change (x : (L1 𝕂)) ∈ (haarSynthesis (𝕂 := 𝕂)).range.topologicalClosure
  rw [(haarSynthesis_range_closure (𝕂 := 𝕂))]
  exact x.property

def haarMultiplier (d : DyadicIndex → 𝕂) : (H₀ (𝕂 := 𝕂)) →L[𝕂] (H₀ (𝕂 := 𝕂)) :=
  ((haarSynthesisH0 (𝕂 := 𝕂)).comp ((haarMultiplierCoefficients (𝕂 := 𝕂)) d)).extendOfNorm (haarSynthesisH0 (𝕂 := 𝕂))

theorem haarMultiplier_agrees (d : DyadicIndex → 𝕂)
    (hd : ∀ I, d I = 0 ∨ d I = 1)
    (hdown : ∀ I J, I.1 ≤ J.1 → dyadicInterval J ⊆ dyadicInterval I → d I = 0 → d J = 0)
    (c : DyadicIndex →₀ 𝕂) :
    (haarMultiplier (𝕂 := 𝕂)) d ((haarSynthesisH0 (𝕂 := 𝕂)) c) = (haarSynthesisH0 (𝕂 := 𝕂)) ((haarMultiplierCoefficients (𝕂 := 𝕂)) d c) := by
  exact LinearMap.extendOfNorm_eq (haarSynthesisH0_dense (𝕂 := 𝕂))
    ⟨1, fun c => by
      change ‖(haarSynthesis (𝕂 := 𝕂)) ((haarMultiplierCoefficients (𝕂 := 𝕂)) d c)‖ ≤ 1 * ‖(haarSynthesis (𝕂 := 𝕂)) c‖
      simpa only [one_mul] using (haarMultiplier_finite_contract (𝕂 := 𝕂)) d hd hdown c⟩ c

theorem haarMultiplier_norm (d : DyadicIndex → 𝕂)
    (hd : ∀ I, d I = 0 ∨ d I = 1)
    (hdown : ∀ I J, I.1 ≤ J.1 → dyadicInterval J ⊆ dyadicInterval I → d I = 0 → d J = 0) :
    ‖(haarMultiplier (𝕂 := 𝕂)) d‖ ≤ 1 := by
  apply LinearMap.opNorm_extendOfNorm_le (haarSynthesisH0_dense (𝕂 := 𝕂)) zero_le_one
  intro c
  change ‖(haarSynthesis (𝕂 := 𝕂)) ((haarMultiplierCoefficients (𝕂 := 𝕂)) d c)‖ ≤ 1 * ‖(haarSynthesis (𝕂 := 𝕂)) c‖
  simpa only [one_mul] using (haarMultiplier_finite_contract (𝕂 := 𝕂)) d hd hdown c

theorem haarMultiplier_idempotent (d : DyadicIndex → 𝕂)
    (hd : ∀ I, d I = 0 ∨ d I = 1)
    (hdown : ∀ I J, I.1 ≤ J.1 → dyadicInterval J ⊆ dyadicInterval I → d I = 0 → d J = 0) :
    ((haarMultiplier (𝕂 := 𝕂)) d).comp ((haarMultiplier (𝕂 := 𝕂)) d) = (haarMultiplier (𝕂 := 𝕂)) d := by
  apply ContinuousLinearMap.ext
  intro x
  refine (haarSynthesisH0_dense (𝕂 := 𝕂)).induction ?_ ?_ x
  · rintro _ ⟨c,rfl⟩
    simp only [ContinuousLinearMap.comp_apply, (haarMultiplier_agrees (𝕂 := 𝕂)) d hd hdown,
      (haarMultiplierCoefficients_idempotent (𝕂 := 𝕂)) d hd]
  · exact isClosed_eq (by fun_prop) (by fun_prop)

theorem haarMultiplier_coefficient (d : DyadicIndex → 𝕂)
    (hd : ∀ I, d I = 0 ∨ d I = 1)
    (hdown : ∀ I J, I.1 ≤ J.1 → dyadicInterval J ⊆ dyadicInterval I → d I = 0 → d J = 0)
    (I : DyadicIndex) (f : (H₀ (𝕂 := 𝕂))) :
    (haarCoefficient (𝕂 := 𝕂)) I ((haarMultiplier (𝕂 := 𝕂)) d f) = d I * (haarCoefficient (𝕂 := 𝕂)) I f := by
  refine (haarSynthesisH0_dense (𝕂 := 𝕂)).induction ?_ ?_ f
  · rintro _ ⟨c,rfl⟩
    rw [(haarMultiplier_agrees (𝕂 := 𝕂)) d hd hdown]
    change (haarCoefficient (𝕂 := 𝕂)) I ((haarSynthesis (𝕂 := 𝕂)) ((haarMultiplierCoefficients (𝕂 := 𝕂)) d c)) =
      d I * (haarCoefficient (𝕂 := 𝕂)) I ((haarSynthesis (𝕂 := 𝕂)) c)
    rw [(haarSynthesis_coefficient (𝕂 := 𝕂)), (haarSynthesis_coefficient (𝕂 := 𝕂)), (haarMultiplierCoefficients_apply (𝕂 := 𝕂))]
    ring
  · exact isClosed_eq (by fun_prop) (by fun_prop)

def evenIntoH0 : (X₀ 𝕂) →L[𝕂] (H₀ (𝕂 := 𝕂)) :=
  (X₀ 𝕂).subtypeL.codRestrict (H₀ (𝕂 := 𝕂)) (meanFunctional_X₀ (𝕂 := 𝕂))

theorem haarMultiplier_preserves_X₀ (d : DyadicIndex → 𝕂)
    (hd : ∀ I, d I = 0 ∨ d I = 1)
    (hdown : ∀ I J, I.1 ≤ J.1 → dyadicInterval J ⊆ dyadicInterval I → d I = 0 → d J = 0)
    (f : (X₀ 𝕂)) : ((haarMultiplier (𝕂 := 𝕂)) d ((evenIntoH0 (𝕂 := 𝕂)) f) : (L1 𝕂)) ∈ (X₀ 𝕂) := by
  change ((haarMultiplier (𝕂 := 𝕂)) d ((evenIntoH0 (𝕂 := 𝕂)) f) : (L1 𝕂)) ∈ (haarClosedSpan 𝕂) {n | Even n}
  apply ((mem_haarClosedSpan_iff (𝕂 := 𝕂)) _ _).mpr
  refine ⟨((haarMultiplier (𝕂 := 𝕂)) d ((evenIntoH0 (𝕂 := 𝕂)) f)).property, ?_⟩
  intro I hI
  rw [(haarMultiplier_coefficient (𝕂 := 𝕂)) d hd hdown]
  have hodd : Odd I.1 := Nat.not_even_iff_odd.mp hI
  change d I * (haarCoefficient (𝕂 := 𝕂)) I (f : (L1 𝕂)) = 0
  rw [(haarCoefficient_vanishes_on_X₀ (𝕂 := 𝕂)) I hodd f, mul_zero]

def evenHaarMultiplier (d : DyadicIndex → 𝕂)
    (hd : ∀ I, d I = 0 ∨ d I = 1)
    (hdown : ∀ I J, I.1 ≤ J.1 → dyadicInterval J ⊆ dyadicInterval I → d I = 0 → d J = 0) :
    (X₀ 𝕂) →L[𝕂] (X₀ 𝕂) :=
  (((H₀ (𝕂 := 𝕂)).subtypeL.comp ((haarMultiplier (𝕂 := 𝕂)) d)).comp (evenIntoH0 (𝕂 := 𝕂))).codRestrict (X₀ 𝕂)
    ((haarMultiplier_preserves_X₀ (𝕂 := 𝕂)) d hd hdown)

theorem evenHaarMultiplier_norm (d : DyadicIndex → 𝕂)
    (hd : ∀ I, d I = 0 ∨ d I = 1)
    (hdown : ∀ I J, I.1 ≤ J.1 → dyadicInterval J ⊆ dyadicInterval I → d I = 0 → d J = 0) :
    ‖(evenHaarMultiplier (𝕂 := 𝕂)) d hd hdown‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖(haarMultiplier (𝕂 := 𝕂)) d ((evenIntoH0 (𝕂 := 𝕂)) f)‖ ≤ 1 * ‖f‖
  have h := ((haarMultiplier (𝕂 := 𝕂)) d).le_of_opNorm_le ((haarMultiplier_norm (𝕂 := 𝕂)) d hd hdown) ((evenIntoH0 (𝕂 := 𝕂)) f)
  exact h

def chainMask (I : DyadicIndex) : 𝕂 := if I.2.val = 0 then 1 else 0

theorem chainMask_values (I : DyadicIndex) : (chainMask (𝕂 := 𝕂)) I = 0 ∨ (chainMask (𝕂 := 𝕂)) I = 1 := by
  by_cases h : I.2.val = 0 <;> simp [chainMask,h]

theorem chainMask_descendant (I J : DyadicIndex) (_ : I.1 ≤ J.1)
    (hs : dyadicInterval J ⊆ dyadicInterval I) (hI : (chainMask (𝕂 := 𝕂)) I = 0) : (chainMask (𝕂 := 𝕂)) J = 0 := by
  by_cases hj : J.2.val = 0
  · have hi : I.2.val ≠ 0 := by intro he; simp [chainMask,he] at hI
    have hjr : (J.2 : ℝ) = 0 := by exact_mod_cast hj
    have h0 : (0 : ℝ) ∈ dyadicInterval J := by
      constructor
      · simp [hjr]
      · simp only [hjr, zero_add]
        positivity
    have hm := (hs h0).1
    have hp : (0 : ℝ) < (I.2 : ℝ)/(2 : ℝ)^I.1 := by
      apply div_pos
      · exact_mod_cast Nat.pos_of_ne_zero hi
      · positivity
    exact False.elim (not_le_of_gt hp hm)
  · simp [chainMask,hj]

def chainProjection : (X₀ 𝕂) →L[𝕂] (X₀ 𝕂) :=
  (evenHaarMultiplier (𝕂 := 𝕂)) (chainMask (𝕂 := 𝕂)) (chainMask_values (𝕂 := 𝕂)) chainMask_descendant

theorem chainProjection_norm : ‖(chainProjection (𝕂 := 𝕂))‖ ≤ 1 :=
  (evenHaarMultiplier_norm (𝕂 := 𝕂)) (chainMask (𝕂 := 𝕂)) (chainMask_values (𝕂 := 𝕂)) chainMask_descendant

theorem chainProjection_coefficient (I : DyadicIndex) (f : (X₀ 𝕂)) :
    (haarCoefficient (𝕂 := 𝕂)) I ((chainProjection (𝕂 := 𝕂)) f) = (chainMask (𝕂 := 𝕂)) I * (haarCoefficient (𝕂 := 𝕂)) I f :=
  (haarMultiplier_coefficient (𝕂 := 𝕂)) (chainMask (𝕂 := 𝕂)) (chainMask_values (𝕂 := 𝕂)) chainMask_descendant I ((evenIntoH0 (𝕂 := 𝕂)) f)

theorem chainProjection_idempotent : (chainProjection (𝕂 := 𝕂)).comp (chainProjection (𝕂 := 𝕂)) = (chainProjection (𝕂 := 𝕂)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply (haarCoefficient_ext (𝕂 := 𝕂))
  · rw [(meanFunctional_X₀ (𝕂 := 𝕂)), (meanFunctional_X₀ (𝕂 := 𝕂))]
  · intro I
    simp only [ContinuousLinearMap.comp_apply, (chainProjection_coefficient (𝕂 := 𝕂))]
    rcases (chainMask_values (𝕂 := 𝕂)) I with hi | hi <;> simp [hi]

def haarIndexSpan (A : Set DyadicIndex) : Submodule 𝕂 (L1 𝕂) :=
  (Submodule.span 𝕂 ((haarL1 𝕂) '' A)).topologicalClosure

theorem mem_haarIndexSpan_iff (A : Set DyadicIndex) (f : (L1 𝕂)) :
    f ∈ (haarIndexSpan (𝕂 := 𝕂)) A ↔ (meanFunctional (𝕂 := 𝕂)) f = 0 ∧ ∀ I, I ∉ A → (haarCoefficient (𝕂 := 𝕂)) I f = 0 := by
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
    have he (m : ℕ) : (dyadicAverage (𝕂 := 𝕂)) m f ∈ Submodule.span 𝕂 ((haarL1 𝕂) '' A) := by
      rw [(dyadicAverage_finite_expansion (𝕂 := 𝕂)), hm, zero_smul, zero_add]
      apply Submodule.sum_mem
      intro n _
      apply Submodule.sum_mem
      intro k _
      by_cases hI : (⟨n,k⟩ : DyadicIndex) ∈ A
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨n,k⟩,hI,rfl⟩)
      · simp [hc ⟨n,k⟩ hI]
    exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ((dyadicAverage_tendsto (𝕂 := 𝕂)) f)
      (Filter.Eventually.of_forall fun m => Submodule.le_topologicalClosure _ (he m))

def chainSpan : Submodule 𝕂 (L1 𝕂) := (haarIndexSpan (𝕂 := 𝕂)) {I | Even I.1 ∧ I.2.val = 0}
def offChainSpan : Submodule 𝕂 (L1 𝕂) := (haarIndexSpan (𝕂 := 𝕂)) {I | Even I.1 ∧ I.2.val ≠ 0}

theorem chainProjection_fixed_iff (f : (X₀ 𝕂)) :
    (chainProjection (𝕂 := 𝕂)) f = f ↔ (f : (L1 𝕂)) ∈ (chainSpan (𝕂 := 𝕂)) := by
  rw [chainSpan, (mem_haarIndexSpan_iff (𝕂 := 𝕂))]
  constructor
  · intro hf
    refine ⟨(meanFunctional_X₀ (𝕂 := 𝕂)) f, ?_⟩
    intro I hI
    by_cases he : Even I.1
    · have hk : I.2.val ≠ 0 := fun hk => hI ⟨he,hk⟩
      have hh := congrArg (fun g : (X₀ 𝕂) => (haarCoefficient (𝕂 := 𝕂)) I (g : (L1 𝕂))) hf
      rw [(chainProjection_coefficient (𝕂 := 𝕂))] at hh
      simpa [chainMask,hk] using hh.symm
    · exact (haarCoefficient_vanishes_on_X₀ (𝕂 := 𝕂)) I (Nat.not_even_iff_odd.mp he) f
  · rintro ⟨_,hc⟩
    apply Subtype.ext
    apply (haarCoefficient_ext (𝕂 := 𝕂))
    · rw [(meanFunctional_X₀ (𝕂 := 𝕂)),(meanFunctional_X₀ (𝕂 := 𝕂))]
    · intro I
      rw [(chainProjection_coefficient (𝕂 := 𝕂))]
      by_cases hk : I.2.val = 0
      · simp [chainMask,hk]
      · rw [hc I (fun hi => hk hi.2)]
        simp

theorem chainProjection_zero_iff (f : (X₀ 𝕂)) :
    (chainProjection (𝕂 := 𝕂)) f = 0 ↔ (f : (L1 𝕂)) ∈ (offChainSpan (𝕂 := 𝕂)) := by
  rw [offChainSpan, (mem_haarIndexSpan_iff (𝕂 := 𝕂))]
  constructor
  · intro hf
    refine ⟨(meanFunctional_X₀ (𝕂 := 𝕂)) f, ?_⟩
    intro I hI
    by_cases he : Even I.1
    · have hk : I.2.val = 0 := by by_contra hn; exact hI ⟨he,hn⟩
      have hh := congrArg (fun g : (X₀ 𝕂) => (haarCoefficient (𝕂 := 𝕂)) I (g : (L1 𝕂))) hf
      rw [(chainProjection_coefficient (𝕂 := 𝕂))] at hh
      simpa [chainMask,hk] using hh
    · exact (haarCoefficient_vanishes_on_X₀ (𝕂 := 𝕂)) I (Nat.not_even_iff_odd.mp he) f
  · rintro ⟨_,hc⟩
    apply Subtype.ext
    apply (haarCoefficient_ext (𝕂 := 𝕂))
    · simp [(meanFunctional_X₀ (𝕂 := 𝕂))]
    · intro I
      rw [(chainProjection_coefficient (𝕂 := 𝕂))]
      by_cases hk : I.2.val = 0
      · rw [hc I (fun hi => hi.2 hk)]
        simp
      · simp [chainMask,hk]

end EvenOddHaarLevels
