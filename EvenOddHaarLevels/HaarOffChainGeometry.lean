import EvenOddHaarLevels.HaarDilation
import EvenOddHaarLevels.L1SequenceEquivalences

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace EvenOddHaarLevels

abbrev OffChainAddress := ℕ × Fin 3

def offChainCell (p : OffChainAddress) : DyadicIndex :=
  ⟨2*p.1+2, ⟨p.2.val+1, by
    have hj := p.2.isLt
    have hp : 4 ≤ 2^(2*p.1+2) := Nat.pow_le_pow_right (n := 2) (i := 2) (by decide) (by omega)
    omega⟩⟩

@[simp] theorem offChainCell_level (p : OffChainAddress) :
    (offChainCell p).1 = 2*p.1+2 := rfl
@[simp] theorem offChainCell_position (p : OffChainAddress) :
    (offChainCell p).2.val = p.2.val+1 := rfl

theorem offChainCell_deeper_subset {n m : ℕ} (hnm : n < m) (k : Fin 3) :
    dyadicInterval (offChainCell (m,k)) ⊆
      dyadicInterval ⟨2*n+2,0⟩ := by
  let j : Fin (2^(2*(m-n))) := ⟨k.val+1, by
    have hk := k.isLt
    have hp : 4 ≤ 2^(2*(m-n)) := Nat.pow_le_pow_right (n := 2) (i := 2) (by decide) (by omega)
    omega⟩
  have hs := dyadic_descendant_subset (2*n+2) (2*(m-n)) 0 j
  have he : (⟨(2*n+2)+(2*(m-n)),
      (dyadicRefinementEquiv (2*n+2) (2*(m-n))).symm (0,j)⟩ : DyadicIndex) =
      offChainCell (m,k) := by
    apply Sigma.ext (show (2*n+2)+(2*(m-n)) = 2*m+2 by omega)
    apply (Fin.heq_ext_iff (by dsimp; congr 1; omega)).mpr
    simp [dyadicRefinementEquiv, finProdFinEquiv, j, offChainCell]
  rwa [he] at hs

theorem offChainCell_disjoint_of_lt {p q : OffChainAddress} (hlt : p.1 < q.1) :
    Disjoint (dyadicInterval (offChainCell p)) (dyadicInterval (offChainCell q)) := by
  have hd : Disjoint (dyadicInterval (offChainCell p))
        (dyadicInterval ⟨2*p.1+2,0⟩) := by
      apply dyadic_level_disjoint
      intro he
      have hv := congrArg Fin.val he
      simp [] at hv
  exact hd.mono_right (offChainCell_deeper_subset hlt q.2)

theorem offChainCell_disjoint {p q : OffChainAddress} (hpq : p ≠ q) :
    Disjoint (dyadicInterval (offChainCell p)) (dyadicInterval (offChainCell q)) := by
  rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
  · exact offChainCell_disjoint_of_lt hlt
  · rcases p with ⟨n,j⟩
    rcases q with ⟨m,k⟩
    dsimp at heq
    subst m
    apply dyadic_level_disjoint
    intro he
    apply hpq
    have hv := congrArg Fin.val he
    congr 1
    apply Fin.ext
    simpa only [offChainCell_position, add_left_inj] using hv
  · exact (offChainCell_disjoint_of_lt hgt).symm

theorem dyadicDilationIndex_assoc (A B C : DyadicIndex) :
    dyadicDilationIndex A (dyadicDilationIndex B C) =
      dyadicDilationIndex (dyadicDilationIndex A B) C := by
  apply Sigma.ext (show A.1 + (B.1 + C.1) = (A.1 + B.1) + C.1 by omega)
  apply (Fin.heq_ext_iff (by dsimp [dyadicDilationIndex]; congr 1; omega)).mpr
  simp only [dyadicDilationIndex_position, dyadicDilationIndex_level, pow_add]
  ring

theorem dyadicDilationIndex_zeroQuarter_cell (p : OffChainAddress) :
    dyadicDilationIndex ⟨2,0⟩ (offChainCell p) = offChainCell (p.1+1,p.2) := by
  apply Sigma.ext (show 2+(2*p.1+2) = 2*(p.1+1)+2 by omega)
  apply (Fin.heq_ext_iff (by dsimp [dyadicDilationIndex,offChainCell]; congr 1; omega)).mpr
  simp

theorem offChain_address_level (m : ℕ) (k : Fin (2^(2*m))) (hk : k.val ≠ 0) :
    ∃ p : OffChainAddress, ∃ I : DyadicIndex, Even I.1 ∧
      dyadicDilationIndex (offChainCell p) I = ⟨2*m,k⟩ := by
  induction m with
  | zero => have : k = 0 := Fin.eq_zero k; simp [this] at hk
  | succ m ih =>
    let k' : Fin (2^(2+2*m)) := Fin.cast (by congr 1; omega) k
    let p := dyadicRefinementEquiv 2 (2*m) k'
    have hrec : dyadicDilationIndex ⟨2,p.1⟩ ⟨2*m,p.2⟩ = ⟨2*(m+1),k⟩ := by
      change (⟨2+2*m, (dyadicRefinementEquiv 2 (2*m)).symm
        ((dyadicRefinementEquiv 2 (2*m) k').1, (dyadicRefinementEquiv 2 (2*m) k').2)⟩ : DyadicIndex) = _
      rw [Equiv.symm_apply_apply]
      apply Sigma.ext (show 2+2*m = 2*(m+1) by omega)
      exact (Fin.heq_ext_iff (by dsimp; congr 1; omega)).mpr rfl
    by_cases ha : p.1.val = 0
    · have hb : p.2.val ≠ 0 := by
        intro hb
        have hv := congrArg (fun K : DyadicIndex => K.2.val) hrec
        rw [dyadicDilationIndex_position] at hv
        simp only [ha, hb, mul_zero, add_zero] at hv
        exact hk hv.symm
      obtain ⟨q,I,hI,he⟩ := ih p.2 hb
      refine ⟨(q.1+1,q.2),I,hI,?_⟩
      have hap : p.1 = 0 := Fin.ext ha
      rw [hap] at hrec
      rw [← hrec, ← he, dyadicDilationIndex_assoc, dyadicDilationIndex_zeroQuarter_cell]
    · let j : Fin 3 := ⟨p.1.val-1, by have := p.1.isLt; change p.1.val < 4 at this; omega⟩
      refine ⟨(0,j),⟨2*m,p.2⟩,⟨m,by dsimp; omega⟩,?_⟩
      have he : offChainCell (0,j) = ⟨2,p.1⟩ := by
        apply Sigma.ext (show 2*0+2 = 2 from rfl)
        apply (Fin.heq_ext_iff rfl).mpr
        simp only [offChainCell_position]
        dsimp [j]
        omega
      rw [he]
      exact hrec

theorem offChain_address (K : DyadicIndex) (hK : Even K.1) (hk : K.2.val ≠ 0) :
    ∃ p : OffChainAddress, ∃ I : DyadicIndex, Even I.1 ∧
      dyadicDilationIndex (offChainCell p) I = K := by
  rcases K with ⟨n,k⟩
  rcases hK with ⟨m,hm⟩
  have hn : n = 2*m := by dsimp at hm; omega
  subst n
  exact offChain_address_level m k hk

end EvenOddHaarLevels
