import Mathlib

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

/-- Left dyadic half has sign +1. -/
def walshSign (b : Bool) : 𝕂 := if b then -1 else 1
@[simp] theorem walshSign_false : (walshSign (𝕂 := 𝕂)) false = 1 := rfl
@[simp] theorem walshSign_true : (walshSign (𝕂 := 𝕂)) true = -1 := rfl
@[simp] theorem walshSign_not (b : Bool) : (walshSign (𝕂 := 𝕂)) (!b) = -(walshSign (𝕂 := 𝕂)) b := by
  cases b <;> norm_num [walshSign]
theorem walshSign_xor (a b : Bool) :
    (walshSign (𝕂 := 𝕂)) (Bool.xor a b) = (walshSign (𝕂 := 𝕂)) a * (walshSign (𝕂 := 𝕂)) b := by
  cases a <;> cases b <;> norm_num [walshSign]

/-- Uniform average on a finite Boolean cube. -/
def cubeMean {ι : Type*} [Fintype ι] [DecidableEq ι] {V : Type*} [AddCommGroup V] [Module ℚ≥0 V] (f : (ι → Bool) → V) : V :=
  𝔼 ε : ι → Bool, f ε

def walshCubeExtend (F : Finset ℕ) (ε : F → Bool) (n : ℕ) : Bool :=
  if h : n ∈ F then ε ⟨n, h⟩ else false

def walshCubeEval (c : (Finset ℕ) →₀ 𝕂) (ε : ℕ → Bool) : 𝕂 :=
  c.sum (fun A a => a * ∏ n ∈ A, (walshSign (𝕂 := 𝕂)) (ε n))

section Finite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cubeCharacter (A : Finset ι) (ε : ι → Bool) : 𝕂 :=
  ∏ i ∈ A, (walshSign (𝕂 := 𝕂)) (ε i)

def cubeFlip (j : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun ε := Function.update ε j (!ε j)
  invFun ε := Function.update ε j (!ε j)
  left_inv ε := by ext i; by_cases h : i = j <;> simp [h]
  right_inv ε := by ext i; by_cases h : i = j <;> simp [h]

omit [Fintype ι] in
theorem cubeCharacter_flip (A : Finset ι) (j : ι) (hj : j ∈ A) (ε : ι → Bool) :
    (cubeCharacter (𝕂 := 𝕂)) A (cubeFlip j ε) = -(cubeCharacter (𝕂 := 𝕂)) A ε := by
  have hfun : (fun i => (walshSign (𝕂 := 𝕂)) (cubeFlip j ε i)) =
      Function.update (fun i => (walshSign (𝕂 := 𝕂)) (ε i)) j (-(walshSign (𝕂 := 𝕂)) (ε j)) := by
    ext i
    by_cases hi : i = j <;> simp [cubeFlip, hi]
  unfold cubeCharacter
  rw [hfun, Finset.prod_update_of_mem hj]
  rw [← Finset.prod_erase_mul _ _ hj]
  simp only [Finset.sdiff_singleton_eq_erase]
  ring

theorem cubeMean_character (A : Finset ι) :
    cubeMean ((cubeCharacter (𝕂 := 𝕂)) A) = if A = ∅ then 1 else 0 := by
  by_cases h : A = ∅
  · simp [h, cubeMean, cubeCharacter]
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr h
    have he := Fintype.expect_equiv (cubeFlip j) ((cubeCharacter (𝕂 := 𝕂)) A)
      (fun ε => -(cubeCharacter (𝕂 := 𝕂)) A ε) (fun ε => by
        rw [(cubeCharacter_flip (𝕂 := 𝕂)) A j hj]; simp)
    have hn : cubeMean ((cubeCharacter (𝕂 := 𝕂)) A) = -cubeMean ((cubeCharacter (𝕂 := 𝕂)) A) := by
      simpa [cubeMean, Finset.expect_neg_distrib] using he
    simp only [if_neg h]
    linear_combination (1/2 : 𝕂) * hn

/-- Flip only the coordinates that are to be discarded. -/
def cubeTranslate (R : Set ι) (η : ι → Bool) : (ι → Bool) ≃ (ι → Bool) := by
  exact
    { toFun := fun ε i => if i ∈ R then ε i else Bool.xor (ε i) (η i)
      invFun := fun ε i => if i ∈ R then ε i else Bool.xor (ε i) (η i)
      left_inv := by intro ε; ext i; by_cases hi : i ∈ R <;> simp [hi]
      right_inv := by intro ε; ext i; by_cases hi : i ∈ R <;> simp [hi] }

omit [Fintype ι] [DecidableEq ι] in
theorem cubeCharacter_translate (R : Set ι) (A : Finset ι) (ε η : ι → Bool) :
    (cubeCharacter (𝕂 := 𝕂)) A (cubeTranslate R η ε) =
      (cubeCharacter (𝕂 := 𝕂)) A ε * (cubeCharacter (𝕂 := 𝕂)) (A.filter (fun i => i ∉ R)) η := by
  unfold cubeCharacter
  have hp : (∏ i ∈ A.filter (fun i => i ∉ R), (walshSign (𝕂 := 𝕂)) (η i)) =
      ∏ i ∈ A, if i ∈ R then 1 else (walshSign (𝕂 := 𝕂)) (η i) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : i ∈ R <;> simp [h]
  rw [hp, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : i ∈ R <;> simp [cubeTranslate, h, (walshSign_xor (𝕂 := 𝕂))]

theorem cubeMean_translate_character (R : Set ι) (A : Finset ι) (ε : ι → Bool) :
    cubeMean (fun η => (cubeCharacter (𝕂 := 𝕂)) A (cubeTranslate R η ε)) =
      if (↑A : Set ι) ⊆ R then (cubeCharacter (𝕂 := 𝕂)) A ε else 0 := by
  simp_rw [(cubeCharacter_translate (𝕂 := 𝕂))]
  rw [cubeMean, ← Finset.mul_expect, ← cubeMean, (cubeMean_character (𝕂 := 𝕂))]
  have he : A.filter (fun i => i ∉ R) = ∅ ↔ (↑A : Set ι) ⊆ R := by
    simp [Finset.filter_eq_empty_iff, Set.subset_def]
  by_cases h : (↑A : Set ι) ⊆ R
  · simp [he.mpr h, h]
  · simp [he.not.mpr h, h]

/-- Averaging coordinate sign changes is a contraction on the finite cube. -/
theorem cubeMean_average_contract (R : Set ι) (f : (ι → Bool) → 𝕂) :
    cubeMean (fun ε => ‖cubeMean (fun η => f (cubeTranslate R η ε))‖) ≤
      cubeMean (fun ε => ‖f ε‖) := by
  calc
    _ ≤ cubeMean (fun ε => cubeMean (fun η => ‖f (cubeTranslate R η ε)‖)) := by
      exact Finset.expect_le_expect (fun ε _ => RCLike.norm_expect_le (K := 𝕂))
    _ = cubeMean (fun η => cubeMean (fun ε => ‖f (cubeTranslate R η ε)‖)) := by
      exact Finset.expect_comm _ _ _
    _ = cubeMean (fun _η : ι → Bool => cubeMean (fun ε => ‖f ε‖)) := by
      apply Finset.expect_congr rfl
      intro η hη
      exact (Fintype.expect_equiv (cubeTranslate R η) (fun ε => ‖f (cubeTranslate R η ε)‖)
        (fun ε => ‖f ε‖) (fun _ => rfl))
    _ = _ := Fintype.expect_const _

end Finite
end EvenOddHaarLevels
