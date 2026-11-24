import EvenOddHaarLevels.HaarDecomposition
import EvenOddHaarLevels.HaarOffChain
import EvenOddHaarLevels.HaarDilation

/-! Concrete finite compositions completing the decomposition argument.
The chain equivalence is an explicit construction parameter to these helpers;
no project-specific assumption is introduced. -/
noncomputable section
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

/-- The chain/off-chain splitting in sequence coordinates. -/
def evenChainSequenceSplit (eChain : Seq₁ 𝕂 ≃L[𝕂] (chainSpan (𝕂 := 𝕂))) :
    (X₀ 𝕂) ≃L[𝕂] Sum₁ (Seq₁ 𝕂) (Seq₁ (X₀ 𝕂)) :=
  (evenChainSplit (𝕂 := 𝕂)).trans ((sumOneCongr (𝕂 := 𝕂)) eChain.symm (offChainEquiv (𝕂 := 𝕂)).symm.toContinuousLinearEquiv)

/-- Lift the splitting to sequences, flatten both terms, and reconstruct the even space. -/
def evenSequenceEquivOfChain (eChain : Seq₁ 𝕂 ≃L[𝕂] (chainSpan (𝕂 := 𝕂))) :
    (X₀ 𝕂) ≃L[𝕂] Seq₁ (X₀ 𝕂) := by
  let e := (evenChainSequenceSplit (𝕂 := 𝕂)) eChain
  let r : Seq₁ (X₀ 𝕂) ≃L[𝕂] Sum₁ (Seq₁ (Seq₁ 𝕂)) (Seq₁ (Seq₁ (X₀ 𝕂))) :=
    ((l1MapEquiv (𝕂 := 𝕂)) e).trans (l1SplitPairs (𝕂 := 𝕂)).toContinuousLinearEquiv
  let s : Sum₁ (Seq₁ (Seq₁ 𝕂)) (Seq₁ (Seq₁ (X₀ 𝕂))) ≃L[𝕂]
      Sum₁ (Seq₁ 𝕂) (Seq₁ (X₀ 𝕂)) :=
    (sumOneCongr (𝕂 := 𝕂)) (l1FlattenNat (𝕂 := 𝕂)).toContinuousLinearEquiv (l1FlattenNat (𝕂 := 𝕂)).toContinuousLinearEquiv
  exact (r.trans (s.trans e.symm)).symm

/-- Expose one odd copy as a complemented summand of the even space. -/
def evenOddComplementSplit : (X₀ 𝕂) ≃L[𝕂] Sum₁ (X₁ 𝕂) (𝕂 × (X₁ 𝕂)) :=
  (evenHalfEquiv (𝕂 := 𝕂)).trans
    ((ContinuousLinearEquiv.prodAssoc 𝕂 𝕂 (X₁ 𝕂) (X₁ 𝕂)).symm.trans
      ((ContinuousLinearEquiv.prodComm 𝕂 (𝕂 × (X₁ 𝕂)) (X₁ 𝕂)).trans
        (WithLp.prodContinuousLinearEquiv 1 𝕂 (X₁ 𝕂) (𝕂 × (X₁ 𝕂))).symm))

/-- The concrete absorption argument with the actual half decompositions. -/
def evenOddEquivOfChain (eChain : Seq₁ 𝕂 ≃L[𝕂] (chainSpan (𝕂 := 𝕂))) : (X₀ 𝕂) ≃L[𝕂] (X₁ 𝕂) :=
  (l1Absorption (𝕂 := 𝕂)) ((evenSequenceEquivOfChain (𝕂 := 𝕂)) eChain)
    (evenOddComplementSplit (𝕂 := 𝕂)) (oddHalfEquiv (𝕂 := 𝕂)).symm.toContinuousLinearEquiv

end EvenOddHaarLevels
