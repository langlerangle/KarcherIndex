module

public import KsIndexLean.ReflectedChainCharacters
public import KsIndexLean.KarcherJacobiEquivalence

@[expose] public section


/-! Reflected disk representatives descend to actual bounded geometric Jacobi
fields with their period, rotation, and height-reflection characters. -/
noncomputable section
open Set
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.Trace KsIndex.WeakH1 KsIndex.JacobiFamily
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- The geometric lift agrees pointwise with the representative on the whole
punctured closed half-period disk, and carries the prescribed symmetries. -/
theorem reflected_disk_geometric_lift (R : PaperHalfPeriodRealization k)
    (ε d : ℂ) (hε : ε = 1 ∨ ε = -1) (f : ℂ → ℂ)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball 0 2))
    (hf : ∀ w ∈ seamDomain Set.univ isOpen_univ, f (Bracket.σ w) = ε * f w)
    (hb : ∃ C : ℝ, ∀ w ∈ Metric.closedBall (0 : ℂ) 1, ‖f w‖ ≤ C)
    (hP : ∀ w ∈ (Surface.disk : Set ℂ), laplacian f w + (potV k w : ℂ) * f w = 0)
    (hr : ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
      f (planeRotation (-(2 * Real.pi) / k) w) = d * f w) :
    ∃ G : R.boundedGeometricJacobi (m := m),
      (∀ w : PuncturedClosedDisk k, (R.diskFunctionPullback G.val).val (0, w) = f w.val.val) ∧
      (∀ q, G.val (HeightLift.periodDeck m 1 q) = G.val q) ∧
      (∀ q, G.val (R.periodRotation m q) = d * G.val q) ∧
      ∀ q, G.val (R.periodHeightReflection m q) = ε * G.val q := by
  let V := localReflectedJacobi h.out m ε hε f hsm hf hb hP
  let G := (R.geometricJacobiEquiv (m := m)).symm V
  have he : R.geometricJacobiEquiv G = V := R.geometricJacobiEquiv.apply_symm_apply V
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro w
    have hv := congrArg (fun U : BoundedJacobi k m => U.val 0 w.val.val) he
    change encodeDiskFunction (R.diskFunctionPullback G.val) 0 w.val.val =
      punc0 k (symFam m ε f) 0 w.val.val at hv
    rw [encodeDiskFunction_on_disk, punc0_of_notMem k _ _ w.val.property,
      symFam_zero_copy w.property] at hv
    exact hv
  · have ht := (R.geometricJacobiEquiv_translation_character G 1).mpr (by
      intro n z
      rw [he, one_mul]
      exact normalized_symFam_period ε f n z)
    simpa only [one_mul] using ht
  · apply (R.geometricJacobiEquiv_rotation_character G d).mpr
    intro n z
    rw [he]
    apply normalized_symFam_rotation ε f (Circle.norm_coe _) ?_ ?_
    · rw [show 2 * k = k * 2 from by omega, pow_mul, rotUnit_pow (by have := h.out; omega), one_pow]
    · intro w hw
      simpa only [planeRotation_apply, rotUnit, Circle.coe_exp] using hr w hw
  · apply (R.geometricJacobiEquiv_heightReflection_character G ε).mpr
    intro n z
    rw [he]
    have hh := normalized_symFam_reflection (k := k) hε f (-1 : ZMod (2 * m))
      (by rw [map_neg, map_one]; exact (by decide : -(1 : ZMod 2) = 1)) n z
    change punc0 k (symFam m ε f) (-n - 1) z = ε * punc0 k (symFam m ε f) n z
    rw [show -n - 1 = (-1 : ZMod (2 * m)) - n from by ring]
    exact hh

end KsIndex.KarcherData.PaperHalfPeriodRealization
