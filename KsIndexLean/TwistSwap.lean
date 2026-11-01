module

/-
KsIndexLean — Twisted copy-swap and its character decomposition.

The operator `swapTwE ζ U (n,w) = ζ * U (n+1,w)` exchanges the two copies at
every point, including the seam circle. It is an involution when `ζ² = 1`
and commutes with `rotE 1 a` for every complex parameter `a`.

For `‖ζ‖ = 1`, the operator preserves the polarized form on regular families.
The final index decomposition assumes `k ≥ 2`, a nonzero unit twist with
`ζ² = 1`, and stability of `DomTw k ζ ⊓ E` under this operator. The submodule
`E` is arbitrary; domain stability is an explicit hypothesis. The index then
splits into the two swap eigenspaces with eigenvalues `1` and `-1`.
-/
public import KsIndexLean.TwistedPair
public import KsIndexLean.Bracket

@[expose] public section


noncomputable section

open Complex MeasureTheory
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.Bracket KsIndex.Twisted
  KsIndex.FormIndex KsIndex.GradOrtho
open scoped ContDiff

namespace KsIndex.TwistSwap

variable {k : ℕ}

/-! ### The twisted copy-swap -/

/-- The twisted copy-swap multiplies by `ζ` and exchanges the two copies at every
point, including the seam circle. -/
def swapTwE (ζ : ℂ) : Module.End ℂ (ZMod (2 * 1) × ℂ → ℂ) where
  toFun U := fun p => ζ * U (p.1 + 1, p.2)
  map_add' _ _ := by funext p; simp only [Pi.add_apply]; ring
  map_smul' _ _ := by funext p; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma swapTwE_apply (ζ : ℂ) (U : ZMod (2 * 1) × ℂ → ℂ) (p : ZMod (2 * 1) × ℂ) :
    swapTwE ζ U p = ζ * U (p.1 + 1, p.2) := rfl

/-- The curried twisted swap: `swapTwF ζ v n = ζ · v (n+1)` (all `w`). -/
def swapTwF (ζ : ℂ) (v : ZMod (2 * 1) → ℂ → ℂ) : ZMod (2 * 1) → ℂ → ℂ :=
  fun n w => ζ * v (n + 1) w

lemma uncurry_symm_swapTwE (ζ : ℂ) (U : ZMod (2 * 1) × ℂ → ℂ) :
    (uncurryE 1).symm (swapTwE ζ U) = swapTwF ζ ((uncurryE 1).symm U) := rfl

/-- **Involution** when `ζ² = 1`. -/
lemma swapTwE_sq {ζ : ℂ} (hζ : ζ ^ 2 = 1) (U : ZMod (2 * 1) × ℂ → ℂ) :
    (swapTwE ζ ^ 2) U = U := by
  funext p
  rw [pow_two, Module.End.mul_apply, swapTwE_apply, swapTwE_apply, add_one_add_one,
    ← mul_assoc, ← sq, hζ, one_mul]

/-- **Commutes with rotations** — for ALL `a` (no `‖a‖=1` needed, since `swapTwE` has no `‖w‖`
condition), because `rotE` acts only on the disk variable. -/
lemma swapTwE_rotE (ζ a : ℂ) (U : ZMod (2 * 1) × ℂ → ℂ) :
    swapTwE ζ (rotE 1 a U) = rotE 1 a (swapTwE ζ U) := by
  funext p
  simp only [swapTwE_apply, rotE_apply]

lemma swapTwE_mem_rot {ζ a μ : ℂ} {U : ZMod (2 * 1) × ℂ → ℂ}
    (hU : U ∈ Module.End.eigenspace (rotE 1 a) μ) :
    swapTwE ζ U ∈ Module.End.eigenspace (rotE 1 a) μ := by
  rw [Module.End.mem_eigenspace_iff] at hU ⊢
  rw [← swapTwE_rotE, hU, map_smul]

/-! ### Preservation of the polarized form -/

/-- **The twisted swap scales the polarized form by `‖ζ‖² = 1`.**  On the open disks it swaps the
two copies (reindex `n ↦ n+1`) and scales each by `ζ` in both slots; `gradInner` is conjugate-linear
on the left, so the factor is `conj ζ · ζ = ‖ζ‖² = 1`. -/
lemma jacobiB_swapTwF {ζ : ℂ} (hζ : ‖ζ‖ = 1) {u v : ZMod (2 * 1) → ℂ → ℂ}
    (hu : ∀ n, ContDiffOn ℝ ∞ (u n) disk) (hv : ∀ n, ContDiffOn ℝ ∞ (v n) disk) :
    jacobiB k 1 (swapTwF ζ u) (swapTwF ζ v) = jacobiB k 1 u v := by
  have hζ2 : (starRingEnd ℂ) ζ * ζ = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]; norm_num
  unfold jacobiB
  refine (Fintype.sum_equiv (Equiv.addRight (1 : ZMod (2 * 1))) _ _ fun n => ?_)
  simp only [Equiv.coe_addRight]
  congr 1
  · refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
    have hdf : DifferentiableAt ℝ (u (n + 1)) w :=
      ((hu (n + 1)).contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt (by simp)
    have hdg : DifferentiableAt ℝ (v (n + 1)) w :=
      ((hv (n + 1)).contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt (by simp)
    have hfd : fderiv ℝ (swapTwF ζ u n) w = ζ • fderiv ℝ (u (n + 1)) w := by
      have he : swapTwF ζ u n = fun z => ζ • u (n + 1) z := by funext z; simp [swapTwF]
      rw [he]; exact fderiv_const_smul hdf ζ
    have hgd : fderiv ℝ (swapTwF ζ v n) w = ζ • fderiv ℝ (v (n + 1)) w := by
      have he : swapTwF ζ v n = fun z => ζ • v (n + 1) z := by funext z; simp [swapTwF]
      rw [he]; exact fderiv_const_smul hdg ζ
    rw [gradInner, gradInner, hfd, hgd]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, map_mul]
    linear_combination ((starRingEnd ℂ) (fderiv ℝ (u (n + 1)) w 1) * fderiv ℝ (v (n + 1)) w 1
      + (starRingEnd ℂ) (fderiv ℝ (u (n + 1)) w I) * fderiv ℝ (v (n + 1)) w I) * hζ2
  · refine setIntegral_congr_fun measurableSet_disk fun w _ => ?_
    simp only [swapTwF, map_mul]
    linear_combination ((potV k w : ℂ) * (starRingEnd ℂ) (u (n + 1) w) * v (n + 1) w) * hζ2

/-- **`Bs`-preservation** of the twisted swap, for regular families (`‖ζ‖ = 1`). -/
lemma Bs_swapTwE {ζ : ℂ} (hζ : ‖ζ‖ = 1) {U V : ZMod (2 * 1) × ℂ → ℂ}
    (hU : Regular ((uncurryE 1).symm U)) (hV : Regular ((uncurryE 1).symm V)) :
    Bs k 1 (swapTwE ζ U) (swapTwE ζ V) = Bs k 1 U V := by
  rw [Bs, Bs, uncurry_symm_swapTwE, uncurry_symm_swapTwE]
  exact jacobiB_swapTwF hζ hU.1 hV.1

/-! ### Sesquilinearity and the character split -/

/-- The twisted pair (a common rotation eigenspace) is a sesquilinear domain of regular families. -/
theorem sesq_Tw (hk : 2 ≤ k) {ζ : ℂ} (hζ0 : ζ ≠ 0)
    (E : Submodule ℂ (ZMod (2 * 1) × ℂ → ℂ)) :
    Sesq (Qs k 1) (Bs k 1) (DomTw k ζ ⊓ E) :=
  sesq_of_regular hk _ fun _ hU =>
    regular_of_mem_NCc (TwistedCc_le_NCc hζ0 (mem_DomTw.mp hU.1))

/-- On a stable twisted domain with `k ≥ 2` and a nonzero unit twist satisfying
`ζ² = 1`, the index is the sum of the two swap-eigenspace indices. Stability of
`DomTw k ζ ⊓ E` is supplied by `hD`. -/
theorem formIndex_swapTw_split (hk : 2 ≤ k) {ζ : ℂ} (hζ2 : ζ ^ 2 = 1) (hζ1 : ‖ζ‖ = 1)
    (hζ0 : ζ ≠ 0) (E : Submodule ℂ (ZMod (2 * 1) × ℂ → ℂ))
    (hD : ∀ U ∈ DomTw k ζ ⊓ E, swapTwE ζ U ∈ DomTw k ζ ⊓ E) :
    formIndex (Qs k 1) (DomTw k ζ ⊓ E)
      = formIndex (Qs k 1) ((DomTw k ζ ⊓ E) ⊓ Module.End.eigenspace (swapTwE ζ) 1)
        + formIndex (Qs k 1) ((DomTw k ζ ⊓ E) ⊓ Module.End.eigenspace (swapTwE ζ) (-1)) := by
  have hS := sesq_Tw hk hζ0 E
  have hreg : ∀ U ∈ DomTw k ζ ⊓ E, Regular ((uncurryE 1).symm U) :=
    fun U hU => regular_of_mem_NCc (TwistedCc_le_NCc hζ0 (mem_DomTw.mp hU.1))
  have h := formIndex_eq_sum_eigen (swapTwE ζ) hS (N := 2) two_pos
    (fun U _ => swapTwE_sq hζ2 U) hD
    (fun U hU V hV => Bs_swapTwE hζ1 (hreg U hU) (hreg V hV))
  rw [h, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, zeta_two]

end KsIndex.TwistSwap
