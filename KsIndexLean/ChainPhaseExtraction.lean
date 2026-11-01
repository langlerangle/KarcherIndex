module

public import KsIndexLean.ChainChartShift
public import KsIndexLean.SphericalPaperPhase

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

lemma seamBoundary_zero (k m : ℕ) : seamBoundary k m 0 = boundaryArc k 1 := by
  rw [seamBoundary_eq_boundaryArc, zero_add, map_one]
  rfl

lemma seamBoundary_one (k m : ℕ) : seamBoundary k m 1 = boundaryArc k 0 := by
  rw [seamBoundary_eq_boundaryArc, one_add_one_eq_two, SurfaceSym.parity_two]
  rfl

/-- Extract in upper/lower order: copy 1 above, copy 0 below. -/
def chainPhaseUpperLowerPair (k m : ℕ) [NeZero m] (c : ℂ)
    (q : chainChartPhaseDomain k m c) : slitTraceDomain k c :=
  ⟨(chainChartCoordinatesCLM k m q.val 1, chainChartCoordinatesCLM k m q.val 0), by
    rw [mem_slitTraceDomain]
    have h0 := chainChartCoordinates_seam k m q.val 0
    have h1 := chainChartCoordinates_seam k m q.val 1
    have hp := (mem_chainChartPhaseDomain_iff_coordinates k m c q.val).mp q.property 0
    rw [seamBoundary_zero, zero_add] at h0
    rw [seamBoundary_one, one_add_one_eq_two] at h1
    rw [zero_add] at hp
    refine ⟨h0.symm, ?_⟩
    change arcTrace (boundaryArc k 0) (chainChartCoordinatesCLM k m q.val 1) = _
    rw [h1, hp, map_smul]⟩

def chainPhasePairLinearMap (k m : ℕ) [NeZero m] (c : ℂ) :
    chainChartPhaseDomain k m c →ₗ[ℂ] slitTraceDomain k c where
  toFun := chainPhaseUpperLowerPair k m c
  map_add' q r := by
    apply Subtype.ext
    change ((chainChartCoordinatesCLM k m) (q.val + r.val) 1,
      (chainChartCoordinatesCLM k m) (q.val + r.val) 0) = _
    rw [map_add]
    rfl
  map_smul' a q := by
    apply Subtype.ext
    change ((chainChartCoordinatesCLM k m) (a • q.val) 1,
      (chainChartCoordinatesCLM k m) (a • q.val) 0) = _
    rw [map_smul]
    rfl

lemma chainPhasePair_bound (k m : ℕ) [NeZero m] (c : ℂ)
    (q : chainChartPhaseDomain k m c) : ‖chainPhasePairLinearMap k m c q‖ ≤ ‖q‖ := by
  exact max_le (norm_le_pi_norm (chainChartCoordinatesCLM k m q.val) 1)
    (norm_le_pi_norm (chainChartCoordinatesCLM k m q.val) 0)

def chainPhasePairCLM (k m : ℕ) [NeZero m] (c : ℂ) :
    chainChartPhaseDomain k m c →L[ℂ] slitTraceDomain k c :=
  (chainPhasePairLinearMap k m c).mkContinuous 1 (by
    intro q
    simpa only [one_mul] using chainPhasePair_bound k m c q)

/-- Extraction followed by the orientation-correct spherical realization. -/
def chainPhaseToSphereCLM (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ≠ 0) :
    chainChartPhaseDomain k m c →L[ℂ] SphericalSlitPhaseSpace k c⁻¹ :=
  (upperLowerSlitToSphere k c hc).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (chainPhasePairCLM k m c)

lemma chainPhaseToSphere_coordinates (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ≠ 0)
    (q : chainChartPhaseDomain k m c) :
    sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) (chainPhaseToSphereCLM k m c hc q).val =
      (chainChartCoordinatesCLM k m q.val 0, chainChartCoordinatesCLM k m q.val 1) :=
  upperLowerSlitToSphere_coordinates k c hc (chainPhaseUpperLowerPair k m c q)

end KsIndex.Trace
