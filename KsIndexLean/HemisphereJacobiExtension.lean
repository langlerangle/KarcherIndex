module

public import KsIndexLean.JacobiExtensionFullDuality
public import KsIndexLean.JacobiExtensionUnique
public import KsIndexLean.HemisphereWeakDomains
public import KsIndexLean.HemisphereH1Comparison

@[expose] public section


/-! Jacobi extension on the actual hemisphere chart carrier, with its transported
Sobolev norm and literal spherical Jacobi integral. Traces use the equatorial
circle coordinate. The existing round H¹ size comparison also gives an
explicit intrinsic-size bound for this extension. -/
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.CircleSobolev KsIndex.DtnBridge

/-- Bounded linear extension into the hemisphere Sobolev chart carrier. -/
def hemisphereJacobiExtension {k : ℕ} (hk : 2 ≤ k) :
    dotted (1 / 2 : ℝ) →L[ℂ] HemisphereChartSpace :=
  hemisphereCoordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (jacobiExtensionCLM hk)

@[simp] lemma hemisphereJacobiExtension_coordinates {k : ℕ} (hk : 2 ≤ k)
    (f : dotted (1 / 2 : ℝ)) :
    hemisphereCoordinates (hemisphereJacobiExtension hk f) = jacobiExtensionCLM hk f :=
  hemisphereCoordinates.apply_symm_apply _

lemma hemisphereJacobiExtension_trace {k : ℕ} (hk : 2 ≤ k)
    (f : dotted (1 / 2 : ℝ)) :
    halfDiskTraceCLM (hemisphereCoordinates (hemisphereJacobiExtension hk f)) = f.val := by
  rw [hemisphereJacobiExtension_coordinates, jacobiExtensionCLM_halfTrace]

lemma hemisphereJacobiExtension_weak {k : ℕ} (hk : 2 ≤ k)
    (f : dotted (1 / 2 : ℝ)) (v : hemisphereDirichletDomain) :
    hemisphereJacobi (surfacePotential k) (hemisphereJacobiExtension hk f) v.val = 0 := by
  rw [hemisphereJacobi_eq, hemisphereJacobiExtension_coordinates]
  exact jacobiExtensionCLM_weak_zeroTrace hk f _ v.property

lemma hemisphereJacobiExtension_constantTrace {k : ℕ} (hk : 2 ≤ k)
    (f : dotted (1 / 2 : ℝ)) (v : HemisphereChartSpace)
    (hv : ∃ c : ℂ, diskTraceCLM (hemisphereCoordinates v) = c • circleOneL2) :
    hemisphereJacobi (surfacePotential k) (hemisphereJacobiExtension hk f) v = 0 := by
  rw [hemisphereJacobi_eq, hemisphereJacobiExtension_coordinates]
  exact jacobiExtensionCLM_constantTrace hk f _ hv

/-- Green identity on one hemisphere against every admissible H¹ test. -/
theorem hemisphereJacobiExtension_duality {k : ℕ} (hk : 2 ≤ k)
    (f : dotted (1 / 2 : ℝ)) (v : HemisphereChartSpace) :
    hemisphereJacobi (surfacePotential k) (hemisphereJacobiExtension hk f) v =
      duality (1 / 2 : ℝ) (dottedDtnCLM k f).val
        (halfDiskTraceCLM (hemisphereCoordinates v)) := by
  rw [hemisphereJacobi_eq, hemisphereJacobiExtension_coordinates]
  exact jacobiExtensionCLM_full_duality hk f _

/-- Among weak Jacobi solutions, the prescribed trace and mean-flux normalization
determine the hemisphere extension uniquely. -/
theorem hemisphereJacobiExtension_unique {k : ℕ} (hk : 2 ≤ k)
    (f : dotted (1 / 2 : ℝ)) (u : HemisphereChartSpace)
    (ht : halfDiskTraceCLM (hemisphereCoordinates u) = f.val)
    (hw : ∀ v : hemisphereDirichletDomain,
      hemisphereJacobi (surfacePotential k) u v.val = 0)
    (hn : ∀ v : HemisphereChartSpace,
      (∃ c : ℂ, diskTraceCLM (hemisphereCoordinates v) = c • circleOneL2) →
      hemisphereJacobi (surfacePotential k) u v = 0) :
    u = hemisphereJacobiExtension hk f := by
  apply hemisphereCoordinates.injective
  rw [hemisphereJacobiExtension_coordinates]
  apply eq_jacobiExtensionCLM_of_halfTrace hk f _ ht
  · intro v hv
    have he := hw ((hemisphereDomainEquiv (zeroTraceDomain Set.univ)) ⟨v, hv⟩)
    rw [hemisphereJacobi_eq] at he
    change weakJacobi (surfacePotential k) (hemisphereCoordinates u)
      (hemisphereCoordinates (hemisphereCoordinates.symm v)) = 0 at he
    simpa only [LinearIsometryEquiv.apply_symm_apply] using he
  · intro v hv
    have he := hn (hemisphereCoordinates.symm v)
      (by simpa only [LinearIsometryEquiv.apply_symm_apply] using hv)
    simpa only [hemisphereJacobi_eq, LinearIsometryEquiv.apply_symm_apply] using he

/-- Boundedness also holds for the literal round hemisphere H¹ size. -/
theorem hemisphereJacobiExtension_round_bound {k : ℕ} (hk : 2 ≤ k)
    (f : dotted (1 / 2 : ℝ)) :
    hemisphereH1Size (hemisphereJacobiExtension hk f) ≤
      (2 * ‖hemisphereJacobiExtension hk‖) * ‖f‖ := by
  have hsize := (hemisphereH1Size_comparison (hemisphereJacobiExtension hk f)).2
  have hnorm := (hemisphereJacobiExtension hk).le_opNorm f
  nlinarith

end KsIndex.Spherical
