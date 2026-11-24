import Mathlib

noncomputable section
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

/-- Choose an increasing sequence with an arbitrary prescribed membership pattern. -/
theorem exists_strictMono_level_selection (S T : Set ℕ)
    (hT : T.Infinite) (hTc : Tᶜ.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, n ∈ S ↔ φ n ∈ T := by
  classical
  have step (n b : ℕ) : ∃ k, b < k ∧ (n ∈ S ↔ k ∈ T) := by
    by_cases hn : n ∈ S
    · obtain ⟨k, hk, hb⟩ := hT.exists_gt b
      exact ⟨k, hb, by simp [hn, hk]⟩
    · obtain ⟨k, hk, hb⟩ := hTc.exists_gt b
      exact ⟨k, hb, by simpa [hn] using hk⟩
  let next (n b : ℕ) := Classical.choose (step n b)
  have next_spec (n b : ℕ) := Classical.choose_spec (step n b)
  let φ : ℕ → ℕ := fun n => Nat.rec (next 0 0) (fun n b => next (n+1) b) n
  refine ⟨φ, strictMono_nat_of_lt_succ (fun n => ?_), fun n => ?_⟩
  · exact (next_spec (n+1) (φ n)).1
  · cases n with
    | zero => exact (next_spec 0 0).2
    | succ n => exact (next_spec (n+1) (φ n)).2

end EvenOddHaarLevels
