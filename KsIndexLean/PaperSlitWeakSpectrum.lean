module

public import KsIndexLean.PaperSlitSpectralCoordinates
public import KsIndexLean.JacobiSolutionEigenvalue

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Weighted bulk pairing of the paper's lower/upper spherical charts. -/
def paperSlitChartMass (α : ℝ) (u v : PaperSphericalPhaseSpace α) : ℂ :=
  inner ℂ (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc 3 1) u.val).1)
    (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc 3 1) v.val).1) +
  inner ℂ (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc 3 1) u.val).2)
    (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc 3 1) v.val).2)

lemma paperSlitSpectralCoordinates_mass_pairing (α : ℝ)
    (u v : finiteH1Domain (pairFiniteDomain (paperSlitDomain α))) :
    paperSlitChartMass α (paperSlitSpectralCoordinates α u) (paperSlitSpectralCoordinates α v) =
      inner ℂ (finiteH1WeightedValue (pairFiniteDomain (paperSlitDomain α)) u)
        (finiteH1WeightedValue (pairFiniteDomain (paperSlitDomain α)) v) := by
  rw [pairFinite_mass_pairing_eq]
  change inner ℂ (weightedDiskValueCLM (sphereDiskCoordinatesCLM _
      (upperLowerSlitToSphere 3 _ (Complex.exp_ne_zero _) (pairHilbertCoordinates _ u)).val).1)
      (weightedDiskValueCLM (sphereDiskCoordinatesCLM _
      (upperLowerSlitToSphere 3 _ (Complex.exp_ne_zero _) (pairHilbertCoordinates _ v)).val).1) +
    inner ℂ (weightedDiskValueCLM (sphereDiskCoordinatesCLM _
      (upperLowerSlitToSphere 3 _ (Complex.exp_ne_zero _) (pairHilbertCoordinates _ u)).val).2)
      (weightedDiskValueCLM (sphereDiskCoordinatesCLM _
      (upperLowerSlitToSphere 3 _ (Complex.exp_ne_zero _) (pairHilbertCoordinates _ v)).val).2) = _
  simp only [upperLowerSlitToSphere_coordinates]
  exact add_comm _ _

/-- All chart tests, with the actual Jacobi and mass pairings, characterize the
reciprocal shifted solution eigenvalue. No restriction to smooth tests is used. -/
lemma paperSlitSolutionOperator_eigen_iff (α : ℝ)
    (V : BoundedRealPotential) (u : PaperSphericalPhaseSpace α) (t : ℝ) (ht : t ≠ 0) :
    finiteSolutionOperator (pairFiniteDomain (paperSlitDomain α)) V
        (finiteH1WeightedValue (pairFiniteDomain (paperSlitDomain α)) ((paperSlitSpectralCoordinates α).symm u)) =
      (t : ℂ) • finiteH1WeightedValue (pairFiniteDomain (paperSlitDomain α))
        ((paperSlitSpectralCoordinates α).symm u) ↔
    ∀ v : PaperSphericalPhaseSpace α, sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val v.val =
      ((t⁻¹ - (V.C + 1) : ℝ) : ℂ) * paperSlitChartMass α u v := by
  rw [finiteSolutionOperator_eigen_iff _ V _ t ht]
  constructor
  · intro h v
    obtain ⟨x, rfl⟩ := (paperSlitSpectralCoordinates α).surjective u
    obtain ⟨y, rfl⟩ := (paperSlitSpectralCoordinates α).surjective v
    simpa only [LinearEquiv.symm_apply_apply, paperSlitSpectralCoordinates_jacobi,
      paperSlitSpectralCoordinates_mass_pairing] using h y
  · intro h v
    have hv := h (paperSlitSpectralCoordinates α v)
    obtain ⟨x, rfl⟩ := (paperSlitSpectralCoordinates α).surjective u
    simpa only [LinearEquiv.symm_apply_apply, paperSlitSpectralCoordinates_jacobi,
      paperSlitSpectralCoordinates_mass_pairing] using hv

end KsIndex.Spectral
