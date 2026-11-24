import EvenOddHaarLevels.L1SequenceEquivalences

noncomputable section
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  [NormedAddCommGroup F] [NormedSpace 𝕂 F]

/-- A concrete bounded inclusion together with a bounded retraction. -/
structure ComplementedEmbedding (E F : Type*) [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    [NormedAddCommGroup F] [NormedSpace 𝕂 F] where
  inclusion : E →L[𝕂] F
  retraction : F →L[𝕂] E
  retract_inclusion : ∀ x, retraction (inclusion x) = x

namespace ComplementedEmbedding

/-- The direct sum decomposition associated with an inclusion and retraction. -/
def split (e : (ComplementedEmbedding (𝕂 := 𝕂)) E F) : F ≃L[𝕂] Sum₁ E e.retraction.ker := by
  let f : F →L[𝕂] E × e.retraction.ker :=
    e.retraction.prod ((ContinuousLinearMap.id 𝕂 F - e.inclusion.comp e.retraction).codRestrict
      e.retraction.ker (fun x => by
        simp [ContinuousLinearMap.comp_apply,
          e.retract_inclusion]))
  let g : E × e.retraction.ker →L[𝕂] F :=
    (e.inclusion.comp (ContinuousLinearMap.fst 𝕂 E e.retraction.ker)) +
      (e.retraction.ker.subtypeL.comp (ContinuousLinearMap.snd 𝕂 E e.retraction.ker))
  let u : F ≃L[𝕂] E × e.retraction.ker :=
    { toLinearEquiv :=
        { toLinearMap := f.toLinearMap
          invFun := g
          left_inv := by intro x; simp [f, g]
          right_inv := by
            intro x
            apply Prod.ext
            · simp [f, g, e.retract_inclusion]
            · apply Subtype.ext
              simp [f, g, e.retract_inclusion] }
      continuous_toFun := f.continuous
      continuous_invFun := g.continuous }
  exact u.trans (WithLp.prodContinuousLinearEquiv 1 𝕂 E e.retraction.ker).symm

end ComplementedEmbedding
end EvenOddHaarLevels
