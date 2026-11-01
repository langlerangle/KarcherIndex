module

public import KsIndexLean.ReflectionAverageFixed
public import KsIndexLean.LocalizedMollification
public import KsIndexLean.L2MeasureRestriction

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket

lemma compactMollify_fderiv (φ : ContDiffBump (0 : ℂ)) {u : ℂ → ℂ}
    {J : ℂ → ℂ →L[ℝ] ℂ} (hu : MemLp u 2 volume)
    (hw : TauCeti.HasWeakFDerivOn volume ⊤ u J) (d z : ℂ) :
    fderiv ℝ (compactMollify φ u) z d = compactMollify φ (fun w => J w d) z := by
  have hd := ((compactMollify_smooth φ hu).differentiable (by norm_num) z).hasFDerivAt
  exact (hd.hasLineDerivAt d).unique (compactMollify_hasLineDerivAt φ (hw.hasWeakLineDerivOn d) z)

lemma compactMollify_reflection_fderiv (φ : ContDiffBump (0 : ℂ)) (s : ℂ) {u : ℂ → ℂ}
    {J : ℂ → ℂ →L[ℝ] ℂ} (hu : MemLp u 2 volume)
    (hw : TauCeti.HasWeakFDerivOn volume ⊤ u J) (d : ℂ) {z : ℂ} (hz : z ≠ 0) :
    fderiv ℝ (reflectionAverage s (compactMollify φ u)) z d =
      reflectionAverageJet s (compactMollify φ (fun w => J w 1))
        (compactMollify φ (fun w => J w Complex.I)) d z := by
  have hd := (compactMollify_smooth φ hu).differentiable (by norm_num)
  rw [fderiv_reflectionAverage s hz (hd z) (hd (σ z))]
  have hx : (fun w => fderiv ℝ (compactMollify φ u) w 1) =
      compactMollify φ (fun w => J w 1) := funext (compactMollify_fderiv φ hu hw 1)
  have hy : (fun w => fderiv ℝ (compactMollify φ u) w Complex.I) =
      compactMollify φ (fun w => J w Complex.I) := funext (compactMollify_fderiv φ hu hw Complex.I)
  rw [hx, hy]

end KsIndex.Trace
