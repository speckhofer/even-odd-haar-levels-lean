# Subspaces of L¹ spanned by the even and odd levels of the Haar system

This repository contains a Lean 4 formalization accompanying the paper
**[“Subspaces of L¹ spanned by the even and odd levels of the Haar system”](https://arxiv.org/abs/2609.16735)** by Thomas Speckhofer.

This project proves, over either real or complex scalars:

- **Theorem 1.1:** The closed spans of the even and odd Haar levels in L¹[0,1] are not isomorphic to L¹[0,1].
- **Corollary 3.4:** The closed span in L¹[0,1] of an infinite set of Haar levels with infinite complement is isomorphic to the even-level span.

## Checking the proof

Install Lean following the [official installation guide](https://lean-lang.org/install/), with `elan` and `lake` available in your terminal. Git must also be installed: Lake uses it to download the pinned Mathlib dependency and its dependencies on a fresh checkout.

Clone or download this repository. In a terminal in its root directory (the directory containing `lakefile.toml`), run:

```sh
lake exe cache get
lake build
```

The first command downloads precompiled Mathlib files. The second checks the project, including the public statements and axiom audit. Initial setup needs an internet connection and disk space for Lean and Mathlib and can take several minutes. Successful verification ends with `Build completed successfully`.

| Dependency | Pinned version                             |
| ---------- | ------------------------------------------ |
| Lean       | `leanprover/lean4:v4.33.0`                 |
| Mathlib    | `db584cd6d46c92f209a44c0f1c829460d327499d` |

`lean-toolchain` selects Lean automatically through elan. `lakefile.toml` and `lake-manifest.json` pin Mathlib and its dependencies. Use these files as supplied; verification does not require `lake update` or upgrading Lean.

The main entry point is [EvenOddHaarLevels.lean](EvenOddHaarLevels.lean), which imports:

```lean
import EvenOddHaarLevels.Results
import EvenOddHaarLevels.Audit
```

The first module presents the main results; the second checks their types and reports their axiom dependencies. Both are included in `lake build`. After building, you can also check the main entry point or either module individually:

```sh
lake env lean EvenOddHaarLevels.lean
lake env lean EvenOddHaarLevels/Results.lean
lake env lean EvenOddHaarLevels/Audit.lean
```

Checking `Results.lean` normally produces no output on success. `Audit.lean` prints the theorem types and axiom dependencies.

## Reading the public statements

[EvenOddHaarLevels/Results.lean](EvenOddHaarLevels/Results.lean) contains the two public theorems. All project declarations are in the namespace `EvenOddHaarLevels`.

Theorem 1.1:

```lean
theorem main_result (𝕂 : Type*) [RCLike 𝕂] :
    IsEmpty (X₀ 𝕂 ≃L[𝕂] L1 𝕂) ∧ IsEmpty (X₁ 𝕂 ≃L[𝕂] L1 𝕂)
```

Corollary 3.4:

```lean
theorem infinite_coinfinite_levels (𝕂 : Type*) [RCLike 𝕂]
    (S : Set ℕ) (hS : S.Infinite) (hSc : Sᶜ.Infinite) :
    Nonempty (haarClosedSpan 𝕂 S ≃L[𝕂] X₀ 𝕂)
```

Here `∧` means “and,” `Sᶜ` is the complement in ℕ, and `hS` and `hSc` name the infinitude hypotheses. Lean's `ℕ` includes zero and therefore represents the paper's ℕ₀.

### Scalars and `RCLike`

`𝕂 : Type*` introduces an arbitrary type 𝕂. The following assumption `[RCLike 𝕂]` equips it with Mathlib's structure for real or complex scalars: field operations, a compatible norm, conjugation, real and imaginary parts, and their standard identities. It is a Lean interface for arguments common to ℝ and ℂ. The statement is not about an arbitrary normed field.

Both ℝ and ℂ have this structure. `main_result ℝ` is the real theorem and `main_result ℂ` is the complex theorem. Similarly, specialize `infinite_coinfinite_levels` to either field. `Audit.lean` checks all four specializations explicitly.

Spans, maps, and equivalences are linear over the selected 𝕂. The measure space remains the **real** unit interval in both cases. `‖z‖` is a real-valued norm: absolute value for a real scalar and modulus for a complex scalar. The same notation denotes vector and operator norms, as determined by the type.

### Isomorphism, `Nonempty`, and non-isomorphism

`E ≃L[𝕂] F` is the **type of continuous 𝕂-linear equivalences** between E and F. An element contains an actual linear bijection, its inverse, and proofs that both maps are continuous. For normed spaces these are the bounded isomorphisms used in the paper.

An equivalence is an object, so its type is not itself the assertion that an equivalence exists. `Nonempty (E ≃L[𝕂] F)` asserts that there is at least one such object: **E and F are isomorphic**. The corollary proves this by constructing an equivalence.

The main theorem uses `IsEmpty (E ≃L[𝕂] F)`: the type of equivalences has no elements, so **E and F are not isomorphic**. This is equivalent to `¬ Nonempty (E ≃L[𝕂] F)`.

## Definitions and their mathematical meaning

[EvenOddHaarLevels/Definitions.lean](EvenOddHaarLevels/Definitions.lean) imports Mathlib and defines the objects in the public statements independently of the project's main proof modules.

| Paper object                          | Lean name             | Lean construction                                                                  |
| ------------------------------------- | --------------------- | ---------------------------------------------------------------------------------- |
| Dyadic interval as index              | `DyadicIndex`         | `(n : ℕ) × Fin (2 ^ n)`                                                            |
| Lebesgue measure on the unit interval | `unitIntervalMeasure` | `volume.restrict (Set.Ico (0 : ℝ) 1)`                                              |
| L¹[0,1] over 𝕂                        | `L1 𝕂`                | `MeasureTheory.Lp 𝕂 1 unitIntervalMeasure`                                         |
| Haar function h_I                     | `haarFunction 𝕂 I`    | See below.                                                                         |
| h_I as an L¹ vector                   | `haarL1 𝕂 I`          | `(haarFunction_integrable 𝕂 I).toL1 (haarFunction 𝕂 I)`                            |
| X_S                                   | `haarClosedSpan 𝕂 S`  | `(Submodule.span 𝕂 (haarL1 𝕂 '' {I : DyadicIndex \| I.1 ∈ S})).topologicalClosure` |
| X₀                                    | `X₀ 𝕂`                | `haarClosedSpan 𝕂 {n \| Even n}`                                                   |
| X₁                                    | `X₁ 𝕂`                | `haarClosedSpan 𝕂 {n \| Odd n}`                                                    |

`DyadicIndex` is defined by `(n : ℕ) × Fin (2 ^ n)`, a dependent pair in which `Fin (2 ^ n)` is the type of natural numbers less than `2 ^ n`, encoding the position bound. Positions start at **zero**: Lean's k corresponds to the paper's interval index i−1. `Set.Ico a b` denotes `[a,b)`. Using [0,1) instead of [0,1] does not change L¹ because the endpoint has measure zero. `𝒟` is notation for `DyadicIndex`.

The pointwise Haar function is defined directly as the difference of indicator functions of the two half-intervals:

```lean
def haarFunction (I : 𝒟) : ℝ → 𝕂 :=
  (Set.Ico ((I.2 : ℝ) / (2 : ℝ) ^ I.1)
    (((I.2 : ℝ) + 1 / 2) / (2 : ℝ) ^ I.1)).indicator (fun _ => 1) -
  (Set.Ico (((I.2 : ℝ) + 1 / 2) / (2 : ℝ) ^ I.1)
    (((I.2 : ℝ) + 1) / (2 : ℝ) ^ I.1)).indicator (fun _ => 1)
```

Here `I.1` and `I.2` are the level and position, and `A.indicator (fun _ => 1)` is the characteristic function of A.

`haarFunction_integrable 𝕂 I` is a proof that `haarFunction 𝕂 I` is integrable with respect to `unitIntervalMeasure`. Its `.toL1` method uses this proof to construct the function’s almost-everywhere equivalence class in L¹; this is the definition of `haarL1 𝕂 I`. Lemmas such as `haarL1_ae` connect a representative to the explicit Haar function. `=ᵐ[μ]` means equality μ-almost everywhere. Thus the formalization respects the quotient inherent in L¹.

The closed span of all Haar levels from a given set S of natural numbers is defined by:

```lean
(Submodule.span 𝕂
  (haarL1 𝕂 '' {I : DyadicIndex | I.1 ∈ S})).topologicalClosure
```

`I.1` is the level, `''` is the image of a set, `Submodule.span` is the algebraic linear span, and `topologicalClosure` is the norm closure. A `Submodule` records a vector subspace and its closure under the vector-space operations. Used as a type in an equivalence, it means the space of vectors belonging to the subspace, with inherited norm.

The constant function is not a generator of any of these selected spans. This agrees with the paper, although the full Schauder basis of L¹ also includes the constant function.

`noncomputable section` permits constructions such as integrals and choices of inverses that need not be executable algorithms. It does not weaken proof checking.

## Scope and axiom audit

The public results are Theorem 1.1 and Corollary 3.4. Supporting results include even/odd equivalence and ℓ¹ self-similarity. This repository does not claim a formalization of every introductory or bibliographical assertion, or of the finite-dimensional Banach–Mazur distance estimate.

[EvenOddHaarLevels/Audit.lean](EvenOddHaarLevels/Audit.lean) checks the exact public types and their ℝ and ℂ specializations, and reports the axiom dependencies of the main results and supporting lemmas. Both public theorems depend only on:

```text
[propext, Classical.choice, Quot.sound]
```

These are the standard foundational principles used by Mathlib: propositional extensionality, classical choice, and quotient soundness. The project introduces no custom axioms and uses no `sorry` or `admit` placeholders. The default build includes the audit.

## AI assistance

The formalization was developed using OpenAI's GPT-6 Astra and GPT-6.1 Sol.
