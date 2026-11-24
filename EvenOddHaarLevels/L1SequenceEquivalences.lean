import Mathlib

noncomputable section
namespace EvenOddHaarLevels

variable {𝕂 : Type*} [RCLike 𝕂]

abbrev Seq₁ (E : Type*) [NormedAddCommGroup E] := lp (fun _ : ℕ => E) 1

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  [NormedAddCommGroup F] [NormedSpace 𝕂 F]

/-- Repeat one fixed equivalence in every coordinate; uniform bounds are built in. -/
def l1MapEquiv (U : E ≃L[𝕂] F) : Seq₁ E ≃L[𝕂] Seq₁ F :=
  let T := lp.mapCLM 1 (fun _ : ℕ => U.toContinuousLinearMap) (norm_nonneg _) (fun _ => le_rfl)
  let S := lp.mapCLM 1 (fun _ : ℕ => U.symm.toContinuousLinearMap) (norm_nonneg _) (fun _ => le_rfl)
  { T.toLinearMap with
    invFun := S
    left_inv := by intro x; ext n; simp [S, T]
    right_inv := by intro x; ext n; simp [S, T]
    continuous_toFun := T.continuous
    continuous_invFun := S.continuous }

@[simp] theorem l1MapEquiv_apply (U : E ≃L[𝕂] F) (x : Seq₁ E) (n : ℕ) :
    (l1MapEquiv (𝕂 := 𝕂)) U x n = U (x n) := rfl

@[simp] theorem l1MapEquiv_symm_apply (U : E ≃L[𝕂] F) (x : Seq₁ F) (n : ℕ) :
    ((l1MapEquiv (𝕂 := 𝕂)) U).symm x n = U.symm (x n) := rfl

end

section Reindex
variable {A B E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]

abbrev Seq₁On (A : Type*) (E : Type*) [NormedAddCommGroup E] := lp (fun _ : A => E) 1

theorem l1_mem_iff (f : A → E) : Memℓp f 1 ↔ Summable (fun i => ‖f i‖) := by
  simpa using (memℓp_gen_iff (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal) (f := f))

theorem l1_norm (x : Seq₁On A E) : ‖x‖ = ∑' i, ‖x i‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal) x

/-- Concrete reindexing by a bijection, including its membership and inverse laws. -/
def l1Reindex (e : A ≃ B) : Seq₁On A E ≃ₗᵢ[𝕂] Seq₁On B E where
  toFun x := ⟨fun b => x (e.symm b), l1_mem_iff _ |>.mpr
    (e.symm.summable_iff.mpr (l1_mem_iff _ |>.mp x.property))⟩
  invFun x := ⟨fun a => x (e a), l1_mem_iff _ |>.mpr
    (e.summable_iff.mpr (l1_mem_iff _ |>.mp x.property))⟩
  left_inv x := by ext a; simp
  right_inv x := by ext b; simp
  map_add' _ _ := by ext b; rfl
  map_smul' _ _ := by ext b; rfl
  norm_map' x := by
    rw [l1_norm, l1_norm]
    exact e.symm.tsum_eq (fun a => ‖x a‖)

def l1FlattenForward (x : Seq₁On A (Seq₁On B E)) : Seq₁On (A × B) E :=
  ⟨fun p => x p.1 p.2, (l1_mem_iff _).mpr
    ((summable_prod_of_nonneg (fun p => norm_nonneg (x p.1 p.2))).mpr
      ⟨fun a => (l1_mem_iff _).mp (x a).property,
        by simpa only [← l1_norm] using (l1_mem_iff _).mp x.property⟩)⟩

def l1FlattenReverse (x : Seq₁On (A × B) E) : Seq₁On A (Seq₁On B E) :=
  let hs := (l1_mem_iff _).mp x.property
  ⟨fun a => ⟨fun b => x (a,b), (l1_mem_iff _).mpr (hs.prod_factor a)⟩,
    (l1_mem_iff _).mpr (by simpa only [l1_norm] using hs.prod)⟩

/-- Flatten double summable sequences, with both row and total summability proved. -/
def l1Flatten : Seq₁On A (Seq₁On B E) ≃ₗᵢ[𝕂] Seq₁On (A × B) E where
  toFun := l1FlattenForward
  invFun := l1FlattenReverse
  left_inv x := by ext a b; rfl
  right_inv x := by ext p; rfl
  map_add' _ _ := by ext p; rfl
  map_smul' _ _ := by ext p; rfl
  norm_map' x := by
    change ‖l1FlattenForward x‖ = ‖x‖
    rw [l1_norm, l1_norm]
    have h := ((l1_mem_iff _).mp (l1FlattenForward x).property).tsum_prod
    simpa only [l1FlattenForward, l1_norm] using h

def l1Prepend (x : WithLp 1 (E × Seq₁ E)) : Seq₁ E :=
  ⟨fun n => Nat.casesOn n x.fst (fun k => x.snd k), (l1_mem_iff _).mpr
    ((summable_nat_add_iff 1).mp (by simpa using (l1_mem_iff _).mp x.snd.property))⟩

def l1Unprepend (x : Seq₁ E) : WithLp 1 (E × Seq₁ E) :=
  WithLp.toLp 1 (x 0, ⟨fun n => x (n+1), (l1_mem_iff _).mpr
    ((summable_nat_add_iff 1).mpr ((l1_mem_iff _).mp x.property))⟩)

/-- Prepending a head coordinate, with the exact sum norm. -/
def l1HeadTail : WithLp 1 (E × Seq₁ E) ≃ₗᵢ[𝕂] Seq₁ E where
  toFun := l1Prepend
  invFun := l1Unprepend
  left_inv x := by
    apply WithLp.ofLp_injective 1
    apply Prod.ext
    · rfl
    · ext n; rfl
  right_inv x := by ext n; cases n <;> rfl
  map_add' x y := by ext n; cases n <;> rfl
  map_smul' c x := by ext n; cases n <;> rfl
  norm_map' x := by
    change ‖l1Prepend x‖ = ‖x‖
    rw [l1_norm]
    have hs := (l1_mem_iff _).mp (l1Prepend x).property
    rw [hs.tsum_eq_zero_add]
    have hn : ‖x‖ = ‖x.fst‖ + ‖x.snd‖ := by
      simpa using WithLp.prod_norm_eq_add (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal) x
    rw [hn, l1_norm]
    rfl

def natPairEquiv : ℕ × ℕ ≃ ℕ where
  toFun p := Nat.pair p.1 p.2
  invFun := Nat.unpair
  left_inv p := Nat.unpair_pair p.1 p.2
  right_inv := Nat.pair_unpair

def l1FlattenNat : Seq₁ (Seq₁ E) ≃ₗᵢ[𝕂] Seq₁ E :=
  (l1Flatten (𝕂 := 𝕂)).trans ((l1Reindex (𝕂 := 𝕂)) natPairEquiv)

end Reindex

section SplitPairs
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  [NormedAddCommGroup F] [NormedSpace 𝕂 F]

theorem sumOne_norm (x : WithLp 1 (E × F)) : ‖x‖ = ‖x.fst‖ + ‖x.snd‖ := by
  simpa using WithLp.prod_norm_eq_add (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal) x

def l1SplitForward (x : Seq₁ (WithLp 1 (E × F))) : WithLp 1 (Seq₁ E × Seq₁ F) :=
  let hs := (l1_mem_iff _).mp x.property
  WithLp.toLp 1
    (⟨fun n => (x n).fst, (l1_mem_iff _).mpr
      (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
        rw [sumOne_norm]; exact le_add_of_nonneg_right (norm_nonneg _)) hs)⟩,
     ⟨fun n => (x n).snd, (l1_mem_iff _).mpr
      (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
        rw [sumOne_norm]; exact le_add_of_nonneg_left (norm_nonneg _)) hs)⟩)

def l1SplitReverse (x : WithLp 1 (Seq₁ E × Seq₁ F)) : Seq₁ (WithLp 1 (E × F)) :=
  ⟨fun n => WithLp.toLp 1 (x.fst n, x.snd n), (l1_mem_iff _).mpr (by
    have hs := ((l1_mem_iff _).mp x.fst.property).add ((l1_mem_iff _).mp x.snd.property)
    simpa only [sumOne_norm, WithLp.fst, WithLp.snd, WithLp.ofLp_toLp] using hs)⟩

/-- Split each pair without changing the ℓ¹ sum norm. -/
def l1SplitPairs : Seq₁ (WithLp 1 (E × F)) ≃ₗᵢ[𝕂] WithLp 1 (Seq₁ E × Seq₁ F) where
  toFun := l1SplitForward
  invFun := l1SplitReverse
  left_inv x := by ext n; rfl
  right_inv x := by
    apply WithLp.ofLp_injective 1
    apply Prod.ext <;> (ext n; rfl)
  map_add' x y := by
    apply WithLp.ofLp_injective 1
    apply Prod.ext <;> (ext n; rfl)
  map_smul' c x := by
    apply WithLp.ofLp_injective 1
    apply Prod.ext <;> (ext n; rfl)
  norm_map' x := by
    change ‖l1SplitForward x‖ = ‖x‖
    rw [sumOne_norm, l1_norm, l1_norm, l1_norm]
    have h1 := (l1_mem_iff _).mp (l1SplitForward x).fst.property
    have h2 := (l1_mem_iff _).mp (l1SplitForward x).snd.property
    rw [← h1.tsum_add h2]
    apply tsum_congr
    intro n
    exact (sumOne_norm (x n)).symm

end SplitPairs

section Absorption
variable {E F A B : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  [NormedAddCommGroup A] [NormedSpace 𝕂 A]
  [NormedAddCommGroup B] [NormedSpace 𝕂 B]

abbrev Sum₁ (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] := WithLp 1 (E × F)

def sumOneCongr (e : E ≃L[𝕂] F) (f : A ≃L[𝕂] B) : Sum₁ E A ≃L[𝕂] Sum₁ F B :=
  (WithLp.prodContinuousLinearEquiv 1 𝕂 E A).trans
    ((e.prodCongr f).trans (WithLp.prodContinuousLinearEquiv 1 𝕂 F B).symm)

/-- The concrete absorption argument, as finite compositions of fixed bounded maps. -/
def l1Absorption (eSelf : E ≃L[𝕂] Seq₁ E)
    (eEF : E ≃L[𝕂] Sum₁ F A) (eFE : F ≃L[𝕂] Sum₁ E B) : E ≃L[𝕂] F := by
  let r : E ≃L[𝕂] Sum₁ (Seq₁ F) (Seq₁ A) :=
    eSelf.trans (((l1MapEquiv (𝕂 := 𝕂)) eEF).trans (l1SplitPairs (𝕂 := 𝕂)).toContinuousLinearEquiv)
  let s : F ≃L[𝕂] Sum₁ (Seq₁ F) (Sum₁ (Seq₁ A) B) :=
    eFE.trans (((sumOneCongr (𝕂 := 𝕂)) r (ContinuousLinearEquiv.refl 𝕂 B)).trans
      (LinearIsometryEquiv.withLpProdAssoc 1 𝕂 (Seq₁ F) (Seq₁ A) B).toContinuousLinearEquiv)
  let t : Sum₁ (Sum₁ (Seq₁ A) B) A ≃L[𝕂] Sum₁ (Seq₁ A) B :=
    (LinearIsometryEquiv.withLpProdAssoc 1 𝕂 (Seq₁ A) B A).toContinuousLinearEquiv |>.trans
      ((sumOneCongr (𝕂 := 𝕂)) (ContinuousLinearEquiv.refl 𝕂 (Seq₁ A))
        (LinearIsometryEquiv.withLpProdComm 1 𝕂 B A).toContinuousLinearEquiv) |>.trans
      (LinearIsometryEquiv.withLpProdAssoc 1 𝕂 (Seq₁ A) A B).symm.toContinuousLinearEquiv |>.trans
      ((sumOneCongr (𝕂 := 𝕂))
        ((LinearIsometryEquiv.withLpProdComm 1 𝕂 (Seq₁ A) A).trans (l1HeadTail (𝕂 := 𝕂))).toContinuousLinearEquiv
        (ContinuousLinearEquiv.refl 𝕂 B))
  exact eEF.trans (((sumOneCongr (𝕂 := 𝕂)) s (ContinuousLinearEquiv.refl 𝕂 A)).trans
    ((LinearIsometryEquiv.withLpProdAssoc 1 𝕂 (Seq₁ F) (Sum₁ (Seq₁ A) B) A).toContinuousLinearEquiv.trans
      (((sumOneCongr (𝕂 := 𝕂)) (ContinuousLinearEquiv.refl 𝕂 (Seq₁ F)) t).trans s.symm)))

/-- Split a bounded projection into its actual range and kernel. -/
def projectionDecomposition (P : E →L[𝕂] E) (hP : P.comp P = P) :
    E ≃L[𝕂] Sum₁ P.range P.ker :=
  (Submodule.prodEquivOfIsTopCompl P.range P.ker (ContinuousLinearMap.IsIdempotentElem.isTopCompl (show IsIdempotentElem P from hP))).symm.trans
    (WithLp.prodContinuousLinearEquiv 1 𝕂 P.range P.ker).symm

end Absorption

end EvenOddHaarLevels
