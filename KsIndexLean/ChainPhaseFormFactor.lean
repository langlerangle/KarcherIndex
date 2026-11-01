module

public import KsIndexLean.PhaseCopyFormSum

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

lemma chainPhase_coordinates_reconstruct (k m : ℕ) [NeZero m] (c : ℂ)
    (q : chainChartPhaseDomain k m c) :
    weakPhaseCopies m c (chainPhasePairLinearMap k m c q).val =
      chainChartCoordinatesCLM k m q.val :=
  weakPhaseFamily_recover m c (chainChartCoordinatesCLM k m q.val)
    ((mem_chainChartPhaseDomain_iff_coordinates k m c q.val).mp q.property)

lemma chainPhase_dirichlet_factor (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (q r : chainChartPhaseDomain k m c) :
    chainChartDirichlet k m q.val r.val = (m : ℂ) *
      (dirichlet (chainPhasePairLinearMap k m c q).val.1 (chainPhasePairLinearMap k m c r).val.1 +
       dirichlet (chainPhasePairLinearMap k m c q).val.2
         (chainPhasePairLinearMap k m c r).val.2) := by
  unfold chainChartDirichlet
  rw [← chainPhase_coordinates_reconstruct k m c q, ← chainPhase_coordinates_reconstruct k m c r]
  exact sum_weakPhaseCopies_form m c hc dirichlet dirichlet_unit_smul _ _

lemma chainPhase_jacobi_factor (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (V : BoundedRealPotential) (q r : chainChartPhaseDomain k m c) :
    chainChartJacobi k m V q.val r.val = (m : ℂ) *
      (weakJacobi V (chainPhasePairLinearMap k m c q).val.1
         (chainPhasePairLinearMap k m c r).val.1 +
       weakJacobi V (chainPhasePairLinearMap k m c q).val.2
         (chainPhasePairLinearMap k m c r).val.2) := by
  unfold chainChartJacobi
  rw [← chainPhase_coordinates_reconstruct k m c q, ← chainPhase_coordinates_reconstruct k m c r]
  exact sum_weakPhaseCopies_form m c hc (weakJacobi V) (weakJacobi_unit_smul V) _ _

/-- Exact polarized form factor under the actual cyclic-to-spherical equivalence. -/
theorem chainPhaseSphere_dirichlet (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (q r : chainChartPhaseDomain k m c) :
    chainChartDirichlet k m q.val r.val = (m : ℂ) *
      sphereChartDirichlet (isOpen_boundaryArc k 1)
        (chainPhaseSphereLinearIsometryEquiv k m c hc q).val
        (chainPhaseSphereLinearIsometryEquiv k m c hc r).val := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne m)] at hc
    exact zero_ne_one hc
  change chainChartDirichlet k m q.val r.val = (m : ℂ) *
    sphereChartDirichlet (isOpen_boundaryArc k 1)
      (upperLowerSlitToSphere k c hc0 (chainPhasePairLinearMap k m c q)).val
      (upperLowerSlitToSphere k c hc0 (chainPhasePairLinearMap k m c r)).val
  rw [upperLowerSlitToSphere_dirichlet]
  exact chainPhase_dirichlet_factor k m c hc q r

theorem chainPhaseSphere_jacobi (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (V : BoundedRealPotential) (q r : chainChartPhaseDomain k m c) :
    chainChartJacobi k m V q.val r.val = (m : ℂ) *
      sphereChartJacobi (isOpen_boundaryArc k 1) V
        (chainPhaseSphereLinearIsometryEquiv k m c hc q).val
        (chainPhaseSphereLinearIsometryEquiv k m c hc r).val := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne m)] at hc
    exact zero_ne_one hc
  change chainChartJacobi k m V q.val r.val = (m : ℂ) *
    sphereChartJacobi (isOpen_boundaryArc k 1) V
      (upperLowerSlitToSphere k c hc0 (chainPhasePairLinearMap k m c q)).val
      (upperLowerSlitToSphere k c hc0 (chainPhasePairLinearMap k m c r)).val
  rw [upperLowerSlitToSphere_jacobi]
  exact chainPhase_jacobi_factor k m c hc V q r

end KsIndex.Trace
