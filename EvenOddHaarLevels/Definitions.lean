import Mathlib

/-!
# Definitions for the public statements in EvenOddHaarLevels/Results.lean

This module collects the statement vocabulary: DyadicIndex, unitIntervalMeasure,
L1, haarFunction, haarL1, X₀, X₁, and haarClosedSpan. The original canonical
objects retain their original bodies. Proof-specific constructions live in the
other EvenOddHaarLevels modules; no project proof module is imported here.
-/

noncomputable section

open MeasureTheory

namespace EvenOddHaarLevels

/-- A dyadic interval is indexed by its level and its position at that level. -/
abbrev DyadicIndex := (n : ℕ) × Fin (2 ^ n)

scoped notation "𝒟" => DyadicIndex

/-- Lebesgue measure restricted to the unit interval. -/
def unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Set.Ico (0 : ℝ) 1)

instance : IsFiniteMeasure unitIntervalMeasure := ⟨by
  simp [unitIntervalMeasure]
⟩

variable (𝕂 : Type*) [RCLike 𝕂]

/-- Scalar-valued L¹ on the same real unit interval. -/
abbrev L1 := MeasureTheory.Lp 𝕂 1 unitIntervalMeasure

/-- The same unnormalized Haar function, with values in the chosen scalar field. -/
def haarFunction (I : 𝒟) : ℝ → 𝕂 :=
  (Set.Ico ((I.2 : ℝ) / (2 : ℝ) ^ I.1)
    (((I.2 : ℝ) + 1 / 2) / (2 : ℝ) ^ I.1)).indicator (fun _ => 1) -
  (Set.Ico (((I.2 : ℝ) + 1 / 2) / (2 : ℝ) ^ I.1)
    (((I.2 : ℝ) + 1) / (2 : ℝ) ^ I.1)).indicator (fun _ => 1)

theorem haarFunction_integrable (I : 𝒟) :
    Integrable (haarFunction 𝕂 I) unitIntervalMeasure := by
  exact ((integrable_const (1 : 𝕂)).indicator measurableSet_Ico).sub
    ((integrable_const (1 : 𝕂)).indicator measurableSet_Ico)

/-- The Haar function as its actual scalar-valued L¹ class. -/
def haarL1 (I : 𝒟) : L1 𝕂 :=
  (haarFunction_integrable 𝕂 I).toL1 (haarFunction 𝕂 I)

/-- Closed scalar-linear span of selected levels; no constant generator. -/
def haarClosedSpan (S : Set ℕ) : Submodule 𝕂 (L1 𝕂) :=
  (Submodule.span 𝕂 (haarL1 𝕂 '' {I : 𝒟 | I.1 ∈ S})).topologicalClosure

/-- The closed span of even levels over the chosen field. -/
def X₀ : Submodule 𝕂 (L1 𝕂) := haarClosedSpan 𝕂 {n | Even n}

/-- The closed span of odd levels over the chosen field. -/
def X₁ : Submodule 𝕂 (L1 𝕂) := haarClosedSpan 𝕂 {n | Odd n}

end EvenOddHaarLevels
