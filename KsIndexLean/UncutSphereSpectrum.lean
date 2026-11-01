module

public import KsIndexLean.SlitComparisonCoordinates
public import KsIndexLean.JacobiSolutionEigenvalue
public import KsIndexLean.SphericalZeroPhase

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Set KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Full-equator matching is the phase-one domain, transported to the actual
uncut weak sphere. No slit boundary condition remains. -/
def uncutSpectralCoordinates {k : ℕ} (hk : 1 ≤ k) :
    finiteH1Domain (pairFiniteDomain (slitTraceDomain k 1)) ≃ₗ[ℂ] UncutSphereSpace :=
  (pairHilbertCoordinates (slitTraceDomain k 1)).trans
    (((LinearIsometryEquiv.ofEq _ _ (slitTraceDomain_one_eq hk)).trans
      (sphereTransmissionLinearIsometryEquiv Set.univ isOpen_univ).symm).toLinearEquiv)

lemma uncutSpectralCoordinates_pair {k : ℕ} (hk : 1 ≤ k)
    (u : finiteH1Domain (pairFiniteDomain (slitTraceDomain k 1))) :
    sphereDiskCoordinatesCLM isOpen_univ (uncutSpectralCoordinates hk u) =
      (pairHilbertCoordinates (slitTraceDomain k 1) u).val := by
  exact congrArg Subtype.val
    ((sphereTransmissionLinearIsometryEquiv Set.univ isOpen_univ).apply_symm_apply
      (LinearIsometryEquiv.ofEq _ _ (slitTraceDomain_one_eq hk)
        (pairHilbertCoordinates (slitTraceDomain k 1) u)))

lemma uncutSpectralCoordinates_jacobi {k : ℕ} (hk : 1 ≤ k)
    (V : BoundedRealPotential)
    (u v : finiteH1Domain (pairFiniteDomain (slitTraceDomain k 1))) :
    sphereChartJacobi isOpen_univ V (uncutSpectralCoordinates hk u)
      (uncutSpectralCoordinates hk v) = finiteH1Jacobi (pairFiniteDomain (slitTraceDomain k 1)) V u v := by
  simp only [sphereChartJacobi, uncutSpectralCoordinates_pair, pairFiniteJacobi_eq]

/-- The actual uncut sphere mass from its recovered weak chart functions. -/
def uncutChartMass (u v : UncutSphereSpace) : ℂ :=
  inner ℂ (weightedDiskValueCLM (sphereDiskCoordinatesCLM isOpen_univ u).1)
    (weightedDiskValueCLM (sphereDiskCoordinatesCLM isOpen_univ v).1) +
  inner ℂ (weightedDiskValueCLM (sphereDiskCoordinatesCLM isOpen_univ u).2)
    (weightedDiskValueCLM (sphereDiskCoordinatesCLM isOpen_univ v).2)

lemma uncutSpectralCoordinates_mass {k : ℕ} (hk : 1 ≤ k)
    (u v : finiteH1Domain (pairFiniteDomain (slitTraceDomain k 1))) :
    uncutChartMass (uncutSpectralCoordinates hk u) (uncutSpectralCoordinates hk v) =
      inner ℂ (finiteH1WeightedValue (pairFiniteDomain (slitTraceDomain k 1)) u)
        (finiteH1WeightedValue (pairFiniteDomain (slitTraceDomain k 1)) v) := by
  simp only [uncutChartMass, uncutSpectralCoordinates_pair, pairFinite_mass_pairing_eq]

/-- Spectral data for the full sphere, using the phase-one matching domain
with `k = 3`. The coordinate identification above applies for every `k ≥ 1`. -/
def uncutSphereSpectralData (V : BoundedRealPotential) := slitSpectralData 3 1 V

lemma uncutSolutionOperator_eigen_iff {k : ℕ} (hk : 1 ≤ k)
    (V : BoundedRealPotential) (u : UncutSphereSpace) (t : ℝ) (ht : t ≠ 0) :
    finiteSolutionOperator (pairFiniteDomain (slitTraceDomain k 1)) V
        (finiteH1WeightedValue (pairFiniteDomain (slitTraceDomain k 1)) ((uncutSpectralCoordinates hk).symm u)) =
      (t : ℂ) • finiteH1WeightedValue (pairFiniteDomain (slitTraceDomain k 1))
        ((uncutSpectralCoordinates hk).symm u) ↔
    ∀ v : UncutSphereSpace, sphereChartJacobi isOpen_univ V u v =
      ((t⁻¹ - (V.C + 1) : ℝ) : ℂ) * uncutChartMass u v := by
  rw [finiteSolutionOperator_eigen_iff _ V _ t ht]
  constructor
  · intro h v
    obtain ⟨x, rfl⟩ := (uncutSpectralCoordinates hk).surjective u
    obtain ⟨y, rfl⟩ := (uncutSpectralCoordinates hk).surjective v
    simpa only [LinearEquiv.symm_apply_apply, uncutSpectralCoordinates_jacobi,
      uncutSpectralCoordinates_mass] using h y
  · intro h v
    have hv := h (uncutSpectralCoordinates hk v)
    obtain ⟨x, rfl⟩ := (uncutSpectralCoordinates hk).surjective u
    simpa only [LinearEquiv.symm_apply_apply, uncutSpectralCoordinates_jacobi,
      uncutSpectralCoordinates_mass] using hv


end KsIndex.Spectral
