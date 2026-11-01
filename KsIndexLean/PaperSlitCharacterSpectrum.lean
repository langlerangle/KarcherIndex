module

public import KsIndexLean.PaperSlitCharacterInvariants
public import KsIndexLean.PaperSlitWeakSpectrum

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

lemma slitCharacterSphere_coordinates (k : ℕ) (c : ℂ) (hc : c ≠ 0)
    (θ : ℝ) (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ)
    (u : ↥(slitTraceDomain k c ⊓ pairCharacterDomain θ d)) :
    sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
      (slitCharacterSphereEquiv k c hc θ hθ d u).val.val = (u.val.2, u.val.1) :=
  upperLowerSlitToSphere_coordinates k c hc ⟨u, u.property.1⟩

lemma paperSlitCharacterSpectralCoordinates_pair (α : ℝ) (j : ℕ)
    (u : finiteH1Domain (pairFiniteDomain (paperSlitCharacterDomain α j))) :
    sphereDiskCoordinatesCLM (isOpen_boundaryArc 3 1)
      (paperSlitCharacterSpectralCoordinates α j u).val.val =
        ((pairHilbertCoordinates _ u).val.2, (pairHilbertCoordinates _ u).val.1) :=
  slitCharacterSphere_coordinates 3 _ (Complex.exp_ne_zero _) _
    (paperRotation_root 3 (by decide)) _ (pairHilbertCoordinates _ u)

lemma paperSlitCharacterSpectralCoordinates_mass (α : ℝ) (j : ℕ)
    (u v : finiteH1Domain (pairFiniteDomain (paperSlitCharacterDomain α j))) :
    paperSlitChartMass α (paperSlitCharacterSpectralCoordinates α j u).val
      (paperSlitCharacterSpectralCoordinates α j v).val =
    inner ℂ (finiteH1WeightedValue (pairFiniteDomain (paperSlitCharacterDomain α j)) u)
      (finiteH1WeightedValue (pairFiniteDomain (paperSlitCharacterDomain α j)) v) := by
  simp only [paperSlitChartMass, paperSlitCharacterSpectralCoordinates_pair,
    pairFinite_mass_pairing_eq]
  exact add_comm _ _

/-- The actual spherical character equation, tested against its full weak
domain, is equivalent to the compact solution operator eigenvalue equation. -/
lemma paperSlitCharacterSolution_eigen_iff (α : ℝ) (j : ℕ)
    (V : BoundedRealPotential) (u : paperSphericalPhaseCharacter α j)
    (t : ℝ) (ht : t ≠ 0) :
    finiteSolutionOperator (pairFiniteDomain (paperSlitCharacterDomain α j)) V
      (finiteH1WeightedValue (pairFiniteDomain (paperSlitCharacterDomain α j))
        ((paperSlitCharacterSpectralCoordinates α j).symm u)) =
      (t : ℂ) • finiteH1WeightedValue (pairFiniteDomain (paperSlitCharacterDomain α j))
        ((paperSlitCharacterSpectralCoordinates α j).symm u) ↔
    ∀ v : paperSphericalPhaseCharacter α j,
      sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val.val v.val.val =
        ((t⁻¹ - (V.C + 1) : ℝ) : ℂ) * paperSlitChartMass α u.val v.val := by
  rw [finiteSolutionOperator_eigen_iff _ V _ t ht]
  constructor
  · intro h v
    obtain ⟨x, rfl⟩ := (paperSlitCharacterSpectralCoordinates α j).surjective u
    obtain ⟨y, rfl⟩ := (paperSlitCharacterSpectralCoordinates α j).surjective v
    simpa only [LinearEquiv.symm_apply_apply, paperSlitCharacterSpectralCoordinates_jacobi,
      paperSlitCharacterSpectralCoordinates_mass] using h y
  · intro h v
    have hv := h (paperSlitCharacterSpectralCoordinates α j v)
    obtain ⟨x, rfl⟩ := (paperSlitCharacterSpectralCoordinates α j).surjective u
    simpa only [LinearEquiv.symm_apply_apply, paperSlitCharacterSpectralCoordinates_jacobi,
      paperSlitCharacterSpectralCoordinates_mass] using hv

end KsIndex.Spectral
