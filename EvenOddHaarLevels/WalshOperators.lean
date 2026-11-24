import EvenOddHaarLevels.WalshFunctions
import EvenOddHaarLevels.WalshCubePolynomial

noncomputable section
attribute [local instance] Classical.propDecidable
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

/-- Finite synthesis of the canonical Walsh classes. -/
def walshSynthesis : ((Finset ℕ) →₀ 𝕂) →ₗ[𝕂] (L1 𝕂) :=
  Finsupp.linearCombination 𝕂 (walshL1 (𝕂 := 𝕂))

theorem walshSynthesis_eq (c : (Finset ℕ) →₀ 𝕂) :
    (walshSynthesis (𝕂 := 𝕂)) c = (walshPolynomial (𝕂 := 𝕂)) c := rfl

theorem walshMask_finite_contract (R : Set ℕ) (c : (Finset ℕ) →₀ 𝕂) :
    ‖(walshSynthesis (𝕂 := 𝕂)) ((walshMaskCoefficients (𝕂 := 𝕂)) R c)‖ ≤ ‖(walshSynthesis (𝕂 := 𝕂)) c‖ := by
  let F := (walshCoordinates (𝕂 := 𝕂)) c
  have hF := (walshCoordinates_subset (𝕂 := 𝕂)) c
  rw [(walshSynthesis_eq (𝕂 := 𝕂)), (walshSynthesis_eq (𝕂 := 𝕂)),
    (walshPolynomial_norm_cube (𝕂 := 𝕂)) _ F (fun A hA => hF A ((walshMaskCoefficients_support (𝕂 := 𝕂)) R c hA)),
    (walshPolynomial_norm_cube (𝕂 := 𝕂)) _ F hF]
  exact (walshCubeEval_mask_contract (𝕂 := 𝕂)) R c F hF

theorem walshReindex_finite_isometry (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (c : (Finset ℕ) →₀ 𝕂) :
    ‖(walshSynthesis (𝕂 := 𝕂)) ((walshReindexCoefficients (𝕂 := 𝕂)) φ c)‖ = ‖(walshSynthesis (𝕂 := 𝕂)) c‖ := by
  classical
  let F := (walshCoordinates (𝕂 := 𝕂)) c
  have hF := (walshCoordinates_subset (𝕂 := 𝕂)) c
  have hG : ∀ A ∈ ((walshReindexCoefficients (𝕂 := 𝕂)) φ c).support, A ⊆ F.map ⟨φ,hφ⟩ := by
    intro A hA
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hA)
    intro n hn
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_map.mpr ⟨k, hF B hB hk, rfl⟩
  rw [(walshSynthesis_eq (𝕂 := 𝕂)), (walshSynthesis_eq (𝕂 := 𝕂)), (walshPolynomial_norm_cube (𝕂 := 𝕂)) _ _ hG,
    (walshPolynomial_norm_cube (𝕂 := 𝕂)) _ F hF]
  exact (walshCubeEval_reindex_mean (𝕂 := 𝕂)) φ hφ c F hF

/-- Coordinate deletion on L¹, defined by bounded extension from polynomials. -/
def walshProjection (R : Set ℕ) : (L1 𝕂) →L[𝕂] (L1 𝕂) :=
  ((walshSynthesis (𝕂 := 𝕂)).comp ((walshMaskCoefficients (𝕂 := 𝕂)) R)).extendOfNorm (walshSynthesis (𝕂 := 𝕂))

/-- Injective coordinate substitution on L¹. -/
def walshSubstitution (φ : ℕ → ℕ) : (L1 𝕂) →L[𝕂] (L1 𝕂) :=
  ((walshSynthesis (𝕂 := 𝕂)).comp ((walshReindexCoefficients (𝕂 := 𝕂)) φ)).extendOfNorm (walshSynthesis (𝕂 := 𝕂))

theorem walshUnindex_finite_contract (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (c : (Finset ℕ) →₀ 𝕂) :
    ‖(walshSynthesis (𝕂 := 𝕂)) ((walshUnindexCoefficients (𝕂 := 𝕂)) φ c)‖ ≤ ‖(walshSynthesis (𝕂 := 𝕂)) c‖ := by
  rw [← (walshReindex_finite_isometry (𝕂 := 𝕂)) φ hφ (walshUnindexCoefficients φ c)]
  have he := LinearMap.congr_fun ((walshReindex_unindex (𝕂 := 𝕂)) φ) c
  change (walshReindexCoefficients (𝕂 := 𝕂)) φ ((walshUnindexCoefficients (𝕂 := 𝕂)) φ c) = _ at he
  rw [he]
  exact (walshMask_finite_contract (𝕂 := 𝕂)) _ _

/-- Bounded partial inverse to injective Walsh substitution. -/
def walshRetraction (φ : ℕ → ℕ) : (L1 𝕂) →L[𝕂] (L1 𝕂) :=
  ((walshSynthesis (𝕂 := 𝕂)).comp ((walshUnindexCoefficients (𝕂 := 𝕂)) φ)).extendOfNorm (walshSynthesis (𝕂 := 𝕂))

section Density
variable (hdense : DenseRange (walshSynthesis (𝕂 := 𝕂)))
include hdense

theorem walshProjection_polynomial (R : Set ℕ) (c : (Finset ℕ) →₀ 𝕂) :
    (walshProjection (𝕂 := 𝕂)) R ((walshSynthesis (𝕂 := 𝕂)) c) = (walshSynthesis (𝕂 := 𝕂)) ((walshMaskCoefficients (𝕂 := 𝕂)) R c) := by
  exact LinearMap.extendOfNorm_eq hdense
    ⟨1, fun c => by simpa using (walshMask_finite_contract (𝕂 := 𝕂)) R c⟩ c

theorem walshProjection_contract (R : Set ℕ) (f : (L1 𝕂)) : ‖(walshProjection (𝕂 := 𝕂)) R f‖ ≤ ‖f‖ := by
  change ‖(((walshSynthesis (𝕂 := 𝕂)).comp ((walshMaskCoefficients (𝕂 := 𝕂)) R)).extendOfNorm (walshSynthesis (𝕂 := 𝕂))) f‖ ≤ ‖f‖
  simpa using LinearMap.norm_extendOfNorm_apply_le hdense 1
    (fun c => by simpa using (walshMask_finite_contract (𝕂 := 𝕂)) R c) f

theorem walshSubstitution_polynomial (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (c : (Finset ℕ) →₀ 𝕂) :
    (walshSubstitution (𝕂 := 𝕂)) φ ((walshSynthesis (𝕂 := 𝕂)) c) = (walshSynthesis (𝕂 := 𝕂)) ((walshReindexCoefficients (𝕂 := 𝕂)) φ c) := by
  exact LinearMap.extendOfNorm_eq hdense
    ⟨1, fun c => by simp [(walshReindex_finite_isometry (𝕂 := 𝕂)) φ hφ c]⟩ c

theorem walshSubstitution_norm (φ : ℕ → ℕ) (hφ : Function.Injective φ) (f : (L1 𝕂)) :
    ‖(walshSubstitution (𝕂 := 𝕂)) φ f‖ = ‖f‖ := by
  refine hdense.induction ?_ ?_ f
  · rintro _ ⟨c,rfl⟩
    rw [(walshSubstitution_polynomial (𝕂 := 𝕂)) hdense φ hφ, (walshReindex_finite_isometry (𝕂 := 𝕂)) φ hφ]
  · exact isClosed_eq (by fun_prop) (by fun_prop)

/-- The substitution is the actual linear isometry specified by its Walsh action. -/
def walshSubstitutionIsometry (φ : ℕ → ℕ) (hφ : Function.Injective φ) : (L1 𝕂) →ₗᵢ[𝕂] (L1 𝕂) :=
  { ((walshSubstitution (𝕂 := 𝕂)) φ).toLinearMap with norm_map' := (walshSubstitution_norm (𝕂 := 𝕂)) hdense φ hφ }

omit hdense in
@[simp] theorem walshSynthesis_single (A : Finset ℕ) (a : 𝕂) :
    (walshSynthesis (𝕂 := 𝕂)) (Finsupp.single A a) = a • (walshL1 (𝕂 := 𝕂)) A := by
  simp [walshSynthesis]

theorem walshProjection_walsh (R : Set ℕ) (A : Finset ℕ) :
    (walshProjection (𝕂 := 𝕂)) R ((walshL1 (𝕂 := 𝕂)) A) = if (↑A : Set ℕ) ⊆ R then (walshL1 (𝕂 := 𝕂)) A else 0 := by
  classical
  have hs : (walshMaskCoefficients (𝕂 := 𝕂)) R (Finsupp.single A 1) =
      if (↑A : Set ℕ) ⊆ R then Finsupp.single A 1 else 0 := by
    ext B
    by_cases h : (↑A : Set ℕ) ⊆ R <;> by_cases hBA : B = A <;>
      simp [h, hBA]
  have he := (walshProjection_polynomial (𝕂 := 𝕂)) hdense R (Finsupp.single A 1)
  by_cases h : (↑A : Set ℕ) ⊆ R <;> simpa [hs, h] using he

theorem walshSubstitution_walsh (φ : ℕ → ℕ) (hφ : Function.Injective φ) (A : Finset ℕ) :
    (walshSubstitution (𝕂 := 𝕂)) φ ((walshL1 (𝕂 := 𝕂)) A) = (walshL1 (𝕂 := 𝕂)) (A.image φ) := by
  have he := (walshSubstitution_polynomial (𝕂 := 𝕂)) hdense φ hφ (Finsupp.single A 1)
  simpa [walshReindexCoefficients, Finsupp.mapDomain_single] using he

theorem walshRetraction_polynomial (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (c : (Finset ℕ) →₀ 𝕂) :
    (walshRetraction (𝕂 := 𝕂)) φ ((walshSynthesis (𝕂 := 𝕂)) c) = (walshSynthesis (𝕂 := 𝕂)) ((walshUnindexCoefficients (𝕂 := 𝕂)) φ c) := by
  exact LinearMap.extendOfNorm_eq hdense
    ⟨1, fun c => by simpa using (walshUnindex_finite_contract (𝕂 := 𝕂)) φ hφ c⟩ c

theorem walshRetraction_substitution (φ : ℕ → ℕ) (hφ : Function.Injective φ) (f : (L1 𝕂)) :
    (walshRetraction (𝕂 := 𝕂)) φ ((walshSubstitution (𝕂 := 𝕂)) φ f) = f := by
  refine hdense.induction ?_ ?_ f
  · rintro _ ⟨c,rfl⟩
    rw [(walshSubstitution_polynomial (𝕂 := 𝕂)) hdense φ hφ, (walshRetraction_polynomial (𝕂 := 𝕂)) hdense φ hφ]
    have he := LinearMap.congr_fun ((walshUnindex_reindex (𝕂 := 𝕂)) φ hφ) c
    change (walshUnindexCoefficients (𝕂 := 𝕂)) φ ((walshReindexCoefficients (𝕂 := 𝕂)) φ c) = c at he
    rw [he]
  · exact isClosed_eq (by fun_prop) continuous_id

theorem walshSubstitution_retraction (φ : ℕ → ℕ) (hφ : Function.Injective φ) (f : (L1 𝕂)) :
    (walshSubstitution (𝕂 := 𝕂)) φ ((walshRetraction (𝕂 := 𝕂)) φ f) = (walshProjection (𝕂 := 𝕂)) (Set.range φ) f := by
  refine hdense.induction ?_ ?_ f
  · rintro _ ⟨c,rfl⟩
    rw [(walshRetraction_polynomial (𝕂 := 𝕂)) hdense φ hφ, (walshSubstitution_polynomial (𝕂 := 𝕂)) hdense φ hφ,
      (walshProjection_polynomial (𝕂 := 𝕂)) hdense]
    have he := LinearMap.congr_fun ((walshReindex_unindex (𝕂 := 𝕂)) φ) c
    change (walshReindexCoefficients (𝕂 := 𝕂)) φ ((walshUnindexCoefficients (𝕂 := 𝕂)) φ c) = _ at he
    rw [he]
  · exact isClosed_eq (by fun_prop) (by fun_prop)

theorem walshRetraction_walsh (φ : ℕ → ℕ) (hφ : Function.Injective φ) (A : Finset ℕ) :
    (walshRetraction (𝕂 := 𝕂)) φ ((walshL1 (𝕂 := 𝕂)) A) =
      if (↑A : Set ℕ) ⊆ Set.range φ then (walshL1 (𝕂 := 𝕂)) (A.image (Function.invFun φ)) else 0 := by
  have he := (walshRetraction_polynomial (𝕂 := 𝕂)) hdense φ hφ (Finsupp.single A 1)
  by_cases h : (↑A : Set ℕ) ⊆ Set.range φ <;>
    simpa [walshUnindexCoefficients, h] using he

end Density

end EvenOddHaarLevels
