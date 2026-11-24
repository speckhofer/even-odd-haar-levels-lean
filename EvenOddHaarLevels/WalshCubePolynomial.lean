import EvenOddHaarLevels.WalshCube

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

/-- A finite polynomial's coordinates. -/
def walshCoordinates (c : (Finset ℕ) →₀ 𝕂) : Finset ℕ := c.support.biUnion id

theorem walshCoordinates_subset (c : (Finset ℕ) →₀ 𝕂) (A : Finset ℕ)
    (hA : A ∈ c.support) : A ⊆ (walshCoordinates (𝕂 := 𝕂)) c := by
  intro n hn
  exact Finset.mem_biUnion.mpr ⟨A, hA, hn⟩

def walshMaskCoefficients (R : Set ℕ) :
    ((Finset ℕ) →₀ 𝕂) →ₗ[𝕂] ((Finset ℕ) →₀ 𝕂) where
  toFun c := c.filter (fun A => (↑A : Set ℕ) ⊆ R)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := by ext A; simp [Finsupp.filter_apply]

@[simp] theorem walshMaskCoefficients_apply (R : Set ℕ) (c : (Finset ℕ) →₀ 𝕂)
    (A : Finset ℕ) : (walshMaskCoefficients (𝕂 := 𝕂)) R c A = if (↑A : Set ℕ) ⊆ R then c A else 0 := by
  simp [walshMaskCoefficients, Finsupp.filter_apply]

theorem walshMaskCoefficients_support (R : Set ℕ) (c : (Finset ℕ) →₀ 𝕂) :
    ((walshMaskCoefficients (𝕂 := 𝕂)) R c).support ⊆ c.support := by
  intro A hA
  simpa [walshMaskCoefficients, Finsupp.support_filter] using
    (Finset.mem_filter.mp hA).1

def globalCubeCharacter (F A : Finset ℕ) (ε : F → Bool) : 𝕂 :=
  ∏ n ∈ A, (walshSign (𝕂 := 𝕂)) (walshCubeExtend F ε n)

theorem globalCubeCharacter_mean (F A : Finset ℕ) (hAF : A ⊆ F) :
    cubeMean ((globalCubeCharacter (𝕂 := 𝕂)) F A) = if A = ∅ then 1 else 0 := by
  by_cases h : A = ∅
  · simp [h, globalCubeCharacter, cubeMean]
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr h
    let jF : F := ⟨j, hAF hj⟩
    have flip (ε : F → Bool) : (globalCubeCharacter (𝕂 := 𝕂)) F A (cubeFlip jF ε) =
        -(globalCubeCharacter (𝕂 := 𝕂)) F A ε := by
      have hf : (fun n => (walshSign (𝕂 := 𝕂)) (walshCubeExtend F (cubeFlip jF ε) n)) =
          Function.update (fun n => (walshSign (𝕂 := 𝕂)) (walshCubeExtend F ε n)) j
            (-(walshSign (𝕂 := 𝕂)) (walshCubeExtend F ε j)) := by
        ext n
        by_cases hn : n = j
        · subst n; simp [walshCubeExtend, cubeFlip, jF, hAF hj]
        · by_cases hnF : n ∈ F
          · have hne : (⟨n, hnF⟩ : F) ≠ jF := fun he => hn (congrArg Subtype.val he)
            simp [walshCubeExtend, cubeFlip, hnF, hn, hne]
          · simp [walshCubeExtend, hnF, hn]
      unfold globalCubeCharacter
      rw [hf, Finset.prod_update_of_mem hj, ← Finset.prod_erase_mul _ _ hj]
      simp only [Finset.sdiff_singleton_eq_erase]
      ring
    have he := Fintype.expect_equiv (cubeFlip jF) ((globalCubeCharacter (𝕂 := 𝕂)) F A)
      (fun ε => -(globalCubeCharacter (𝕂 := 𝕂)) F A ε) (fun ε => by rw [flip]; simp)
    have hn : cubeMean ((globalCubeCharacter (𝕂 := 𝕂)) F A) = -cubeMean ((globalCubeCharacter (𝕂 := 𝕂)) F A) := by
      simpa [cubeMean, Finset.expect_neg_distrib] using he
    simp only [if_neg h]
    linear_combination (1/2 : 𝕂) * hn

theorem globalCubeCharacter_translate (F A : Finset ℕ) (R : Set ℕ)
    (ε η : F → Bool) :
    (globalCubeCharacter (𝕂 := 𝕂)) F A (cubeTranslate {i : F | i.val ∈ R} η ε) =
      (globalCubeCharacter (𝕂 := 𝕂)) F A ε * (globalCubeCharacter (𝕂 := 𝕂)) F (A.filter (fun n => n ∉ R)) η := by
  have hp : (∏ n ∈ A.filter (fun n => n ∉ R), (walshSign (𝕂 := 𝕂)) (walshCubeExtend F η n)) =
      ∏ n ∈ A, if n ∈ R then 1 else (walshSign (𝕂 := 𝕂)) (walshCubeExtend F η n) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro n hn
    by_cases h : n ∈ R <;> simp [h]
  unfold globalCubeCharacter
  rw [hp, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro n hn
  by_cases hnF : n ∈ F <;> by_cases hnR : n ∈ R <;>
    simp [walshCubeExtend, cubeTranslate, hnF, hnR, (walshSign_xor (𝕂 := 𝕂))]

theorem globalCubeCharacter_average (F A : Finset ℕ) (hAF : A ⊆ F)
    (R : Set ℕ) (ε : F → Bool) :
    cubeMean (fun η => (globalCubeCharacter (𝕂 := 𝕂)) F A (cubeTranslate {i : F | i.val ∈ R} η ε)) =
      if (↑A : Set ℕ) ⊆ R then (globalCubeCharacter (𝕂 := 𝕂)) F A ε else 0 := by
  simp_rw [(globalCubeCharacter_translate (𝕂 := 𝕂))]
  rw [cubeMean, ← Finset.mul_expect, ← cubeMean,
    (globalCubeCharacter_mean (𝕂 := 𝕂)) F _ (Finset.Subset.trans (Finset.filter_subset _ _) hAF)]
  have he : A.filter (fun n => n ∉ R) = ∅ ↔ (↑A : Set ℕ) ⊆ R := by
    simp [Finset.filter_eq_empty_iff, Set.subset_def]
  by_cases h : (↑A : Set ℕ) ⊆ R
  · simp [he.mpr h, h]
  · simp [he.not.mpr h, h]

theorem walshCubeEval_mask_average (R : Set ℕ) (c : (Finset ℕ) →₀ 𝕂)
    (F : Finset ℕ) (hF : ∀ A ∈ c.support, A ⊆ F) (ε : F → Bool) :
    (walshCubeEval (𝕂 := 𝕂)) ((walshMaskCoefficients (𝕂 := 𝕂)) R c) (walshCubeExtend F ε) =
      cubeMean (fun η => (walshCubeEval (𝕂 := 𝕂)) c
        (walshCubeExtend F (cubeTranslate {i : F | i.val ∈ R} η ε))) := by
  change (c.filter (fun A : Finset ℕ => (↑A : Set ℕ) ⊆ R)).sum _ = _
  rw [Finsupp.sum_filter_index]
  rw [Finsupp.support_filter, Finset.sum_filter]
  unfold walshCubeEval
  simp only [cubeMean, Finsupp.sum, Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Finset.mul_expect]
  change (if (↑A : Set ℕ) ⊆ R then c A * (globalCubeCharacter (𝕂 := 𝕂)) F A ε else 0) =
    c A * cubeMean (fun η => (globalCubeCharacter (𝕂 := 𝕂)) F A
      (cubeTranslate {i : F | i.val ∈ R} η ε))
  rw [(globalCubeCharacter_average (𝕂 := 𝕂)) F A (hF A hA)]
  split_ifs <;> simp

/-- The finite-coordinate projection bound before completion. -/
theorem walshCubeEval_mask_contract (R : Set ℕ) (c : (Finset ℕ) →₀ 𝕂)
    (F : Finset ℕ) (hF : ∀ A ∈ c.support, A ⊆ F) :
    cubeMean (fun ε : F → Bool => ‖(walshCubeEval (𝕂 := 𝕂)) ((walshMaskCoefficients (𝕂 := 𝕂)) R c)
      (walshCubeExtend F ε)‖) ≤
    cubeMean (fun ε : F → Bool => ‖(walshCubeEval (𝕂 := 𝕂)) c (walshCubeExtend F ε)‖) := by
  simp_rw [(walshCubeEval_mask_average (𝕂 := 𝕂)) R c F hF]
  exact (cubeMean_average_contract (𝕂 := 𝕂)) {i : F | i.val ∈ R}
    (fun ε => (walshCubeEval (𝕂 := 𝕂)) c (walshCubeExtend F ε))

/-- Injective renaming of the finite Walsh coordinates. -/
def walshReindexCoefficients (φ : ℕ → ℕ) :
    ((Finset ℕ) →₀ 𝕂) →ₗ[𝕂] ((Finset ℕ) →₀ 𝕂) :=
  Finsupp.lmapDomain 𝕂 𝕂 (fun A => A.image φ)

theorem walshCubeEval_reindex (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (c : (Finset ℕ) →₀ 𝕂) (ε : ℕ → Bool) :
    (walshCubeEval (𝕂 := 𝕂)) ((walshReindexCoefficients (𝕂 := 𝕂)) φ c) ε = (walshCubeEval (𝕂 := 𝕂)) c (ε ∘ φ) := by
  change (c.mapDomain (fun A => A.image φ)).sum _ = _
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
  unfold walshCubeEval
  apply Finsupp.sum_congr
  intro A a
  rw [Finset.prod_image hφ.injOn]
  rfl

theorem walshCubeEval_reindex_mean (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (c : (Finset ℕ) →₀ 𝕂) (F : Finset ℕ) (hF : ∀ A ∈ c.support, A ⊆ F) :
    cubeMean (fun ε : F.map ⟨φ,hφ⟩ → Bool =>
      ‖(walshCubeEval (𝕂 := 𝕂)) ((walshReindexCoefficients (𝕂 := 𝕂)) φ c) (walshCubeExtend _ ε)‖) =
    cubeMean (fun ε : F → Bool => ‖(walshCubeEval (𝕂 := 𝕂)) c (walshCubeExtend F ε)‖) := by
  let e : F ≃ F.map ⟨φ,hφ⟩ := Finset.equivMap ⟨φ,hφ⟩ F
  let u : (F → Bool) ≃ (F.map ⟨φ,hφ⟩ → Bool) := Equiv.arrowCongr e (Equiv.refl Bool)
  symm
  apply Fintype.expect_equiv u
  intro ε
  rw [(walshCubeEval_reindex (𝕂 := 𝕂)) φ hφ]
  congr 1
  apply Finsupp.sum_congr
  intro A hA
  congr 1
  apply Finset.prod_congr rfl
  intro n hn
  have hnF := hF A hA hn
  have hm : φ n ∈ F.map ⟨φ,hφ⟩ := Finset.mem_map.mpr ⟨n, hnF, rfl⟩
  have he : e ⟨n,hnF⟩ = ⟨φ n,hm⟩ := rfl
  simp only [Function.comp_apply, walshCubeExtend, dif_pos hnF, dif_pos hm]
  change (walshSign (𝕂 := 𝕂)) (ε ⟨n,hnF⟩) = (walshSign (𝕂 := 𝕂)) (ε (e.symm ⟨φ n,hm⟩))
  rw [← he, e.symm_apply_apply]

@[simp] theorem walshReindexCoefficients_single (φ : ℕ → ℕ) (A : Finset ℕ) (a : 𝕂) :
    (walshReindexCoefficients (𝕂 := 𝕂)) φ (Finsupp.single A a) = Finsupp.single (A.image φ) a := by
  simp [walshReindexCoefficients, Finsupp.mapDomain_single]

@[simp] theorem walshMaskCoefficients_single (R : Set ℕ) (A : Finset ℕ) (a : 𝕂) :
    (walshMaskCoefficients (𝕂 := 𝕂)) R (Finsupp.single A a) =
      if (↑A : Set ℕ) ⊆ R then Finsupp.single A a else 0 := by
  ext B
  by_cases h : (↑A : Set ℕ) ⊆ R <;> by_cases hBA : B = A <;>
    simp [(walshMaskCoefficients_apply (𝕂 := 𝕂)), h, hBA]

/-- Undo coordinate substitution on its image, deleting the other coordinates. -/
def walshUnindexCoefficients (φ : ℕ → ℕ) :
    ((Finset ℕ) →₀ 𝕂) →ₗ[𝕂] ((Finset ℕ) →₀ 𝕂) :=
  ((walshReindexCoefficients (𝕂 := 𝕂)) (Function.invFun φ)).comp ((walshMaskCoefficients (𝕂 := 𝕂)) (Set.range φ))

theorem walsh_image_invFun (φ : ℕ → ℕ) (hφ : Function.Injective φ) (A : Finset ℕ) :
    (A.image φ).image (Function.invFun φ) = A := by
  rw [Finset.image_image]
  have hi (n : ℕ) : Function.invFun φ (φ n) = n := Function.leftInverse_invFun hφ n
  simp only [Function.comp_def, hi]
  exact Finset.image_id

theorem walsh_invFun_image (φ : ℕ → ℕ) (A : Finset ℕ)
    (hA : (↑A : Set ℕ) ⊆ Set.range φ) :
    (A.image (Function.invFun φ)).image φ = A := by
  rw [Finset.image_image]
  calc
    _ = A.image id := Finset.image_congr (fun n hn => Function.invFun_eq (hA hn))
    _ = A := Finset.image_id

theorem walshUnindex_reindex (φ : ℕ → ℕ) (hφ : Function.Injective φ) :
    ((walshUnindexCoefficients (𝕂 := 𝕂)) φ).comp ((walshReindexCoefficients (𝕂 := 𝕂)) φ) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro A a
  have hA : (↑(A.image φ) : Set ℕ) ⊆ Set.range φ := by
    intro n hn
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    exact ⟨k,rfl⟩
  simp [walshUnindexCoefficients, walsh_image_invFun φ hφ]

theorem walshReindex_unindex (φ : ℕ → ℕ) :
    ((walshReindexCoefficients (𝕂 := 𝕂)) φ).comp ((walshUnindexCoefficients (𝕂 := 𝕂)) φ) =
      (walshMaskCoefficients (𝕂 := 𝕂)) (Set.range φ) := by
  apply Finsupp.lhom_ext
  intro A a
  by_cases hA : (↑A : Set ℕ) ⊆ Set.range φ
  · simp [walshUnindexCoefficients, hA, walsh_invFun_image φ A hA]
  · simp [walshUnindexCoefficients, hA]

end EvenOddHaarLevels
