module

public import KsIndexLean.SlitComparisonSpectrum
public import KsIndexLean.SphericalSlitForms

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Actual summed spherical mass in the two recovered charts. -/
def slitChartMass (k : ℕ) (u v : SphericalSlitNeumannSpace k) : ℂ :=
  inner ℂ (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) u).1)
    (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) v).1) +
  inner ℂ (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) u).2)
    (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) v).2)

def slitNeumannSpectralCoordinates (k : ℕ) :
    finiteH1Domain (pairFiniteDomain (slitNeumannDomain k)) ≃ₗ[ℂ] SphericalSlitNeumannSpace k :=
  (pairHilbertCoordinates (slitNeumannDomain k)).trans (slitNeumannLinearIsometryEquiv k).symm.toLinearEquiv

lemma slitNeumannSpectralCoordinates_pair (k : ℕ)
    (u : finiteH1Domain (pairFiniteDomain (slitNeumannDomain k))) :
    sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) (slitNeumannSpectralCoordinates k u) =
      (pairHilbertCoordinates (slitNeumannDomain k) u).val := by
  exact congrArg Subtype.val ((slitNeumannLinearIsometryEquiv k).apply_symm_apply (pairHilbertCoordinates (slitNeumannDomain k) u))

lemma slitNeumannSpectralCoordinates_jacobi (k : ℕ) (V : BoundedRealPotential)
    (u v : finiteH1Domain (pairFiniteDomain (slitNeumannDomain k))) :
    sphereChartJacobi (isOpen_boundaryArc k 1) V (slitNeumannSpectralCoordinates k u)
      (slitNeumannSpectralCoordinates k v) = finiteH1Jacobi (pairFiniteDomain (slitNeumannDomain k)) V u v := by
  rw [pairFiniteJacobi_eq]
  exact slitNeumann_jacobi k V (pairHilbertCoordinates (slitNeumannDomain k) u) (pairHilbertCoordinates (slitNeumannDomain k) v)

lemma slitNeumannSpectralCoordinates_mass (k : ℕ)
    (u v : finiteH1Domain (pairFiniteDomain (slitNeumannDomain k))) :
    slitChartMass k (slitNeumannSpectralCoordinates k u) (slitNeumannSpectralCoordinates k v) =
      inner ℂ (finiteH1WeightedValue (pairFiniteDomain (slitNeumannDomain k)) u)
        (finiteH1WeightedValue (pairFiniteDomain (slitNeumannDomain k)) v) := by
  simp only [slitChartMass, slitNeumannSpectralCoordinates_pair, pairFinite_mass_pairing_eq]

def slitDirichletSpectralCoordinates (k : ℕ) :
    finiteH1Domain (pairFiniteDomain (slitDirichletDomain k)) ≃ₗ[ℂ] SphericalSlitDirichletSpace k :=
  (pairHilbertCoordinates (slitDirichletDomain k)).trans (slitDirichletLinearIsometryEquiv k).symm.toLinearEquiv

lemma slitDirichletSpectralCoordinates_pair (k : ℕ)
    (u : finiteH1Domain (pairFiniteDomain (slitDirichletDomain k))) :
    sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) (slitDirichletSpectralCoordinates k u).val =
      (pairHilbertCoordinates (slitDirichletDomain k) u).val := by
  exact congrArg Subtype.val ((slitDirichletLinearIsometryEquiv k).apply_symm_apply (pairHilbertCoordinates (slitDirichletDomain k) u))

lemma slitDirichletSpectralCoordinates_jacobi (k : ℕ) (V : BoundedRealPotential)
    (u v : finiteH1Domain (pairFiniteDomain (slitDirichletDomain k))) :
    sphereChartJacobi (isOpen_boundaryArc k 1) V (slitDirichletSpectralCoordinates k u).val
      (slitDirichletSpectralCoordinates k v).val = finiteH1Jacobi (pairFiniteDomain (slitDirichletDomain k)) V u v := by
  rw [pairFiniteJacobi_eq]
  exact slitDirichlet_jacobi k V (pairHilbertCoordinates (slitDirichletDomain k) u) (pairHilbertCoordinates (slitDirichletDomain k) v)

lemma slitDirichletSpectralCoordinates_mass (k : ℕ)
    (u v : finiteH1Domain (pairFiniteDomain (slitDirichletDomain k))) :
    slitChartMass k (slitDirichletSpectralCoordinates k u).val (slitDirichletSpectralCoordinates k v).val =
      inner ℂ (finiteH1WeightedValue (pairFiniteDomain (slitDirichletDomain k)) u)
        (finiteH1WeightedValue (pairFiniteDomain (slitDirichletDomain k)) v) := by
  simp only [slitChartMass, slitDirichletSpectralCoordinates_pair, pairFinite_mass_pairing_eq]

end KsIndex.Spectral
