module

public import KsIndexLean.MixedSignedWeakSpectrum
public import KsIndexLean.RadicalCoordinateTransport

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Set KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Full weak kernel of the actual signed chart form on its test domain. -/
def mixedSignedChartRadical (k : ℕ) (b1 b0 : Bool) (V : BoundedRealPotential) : Submodule ℂ (sphericalSignedDomain k b1 b0) :=
  @coordinateRadical (mixedTraceDomain k b1 b0) (sphericalSignedDomain k b1 b0) inferInstance
    (diskDomain_innerProductSpace _) inferInstance inferInstance
    (domainJacobiForm (mixedTraceDomain k b1 b0) V) (mixedSignedSphereLinearIsometryEquiv k b1 b0).toLinearEquiv

lemma mem_mixedSignedChartRadical (k : ℕ) (b1 b0 : Bool) (V : BoundedRealPotential) (u : sphericalSignedDomain k b1 b0) :
    u ∈ mixedSignedChartRadical k b1 b0 V ↔ ∀ v : sphericalSignedDomain k b1 b0,
      sphereChartJacobi (isOpen_boundaryArc k 1) V u.val v.val = 0 := by
  apply @mem_coordinateRadical_scaled (mixedTraceDomain k b1 b0) (sphericalSignedDomain k b1 b0) inferInstance
    (diskDomain_innerProductSpace _) inferInstance inferInstance
    (domainJacobiForm (mixedTraceDomain k b1 b0) V) (mixedSignedSphereLinearIsometryEquiv k b1 b0).toLinearEquiv
    (fun u v => sphereChartJacobi (isOpen_boundaryArc k 1) V u.val v.val)
    2 (by norm_num) _ u
  intro x y
  exact mixedSignedSphere_jacobi k b1 b0 V x y

lemma mixedSignedChartRadical_finrank (k : ℕ) (b1 b0 : Bool) (V : BoundedRealPotential) :
    Module.finrank ℂ (mixedSignedChartRadical k b1 b0 V) =
      Module.finrank ℂ (@formRadical (mixedTraceDomain k b1 b0) inferInstance
        (diskDomain_innerProductSpace _) (domainJacobiForm (mixedTraceDomain k b1 b0) V)) :=
  @coordinateRadical_finrank (mixedTraceDomain k b1 b0) (sphericalSignedDomain k b1 b0) inferInstance
    (diskDomain_innerProductSpace _) inferInstance inferInstance
    (domainJacobiForm (mixedTraceDomain k b1 b0) V) (mixedSignedSphereLinearIsometryEquiv k b1 b0).toLinearEquiv

lemma mixedSignedChartRadical_finiteDimensional (k : ℕ) (b1 b0 : Bool) (V : BoundedRealPotential) :
    FiniteDimensional ℂ (mixedSignedChartRadical k b1 b0 V) := by
  let := diskRadical_finiteDimensional (mixedTraceDomain k b1 b0) V
  exact (@coordinateRadicalEquiv (mixedTraceDomain k b1 b0) (sphericalSignedDomain k b1 b0) inferInstance
    (diskDomain_innerProductSpace _) inferInstance inferInstance
    (domainJacobiForm (mixedTraceDomain k b1 b0) V) (mixedSignedSphereLinearIsometryEquiv k b1 b0).toLinearEquiv).finiteDimensional

lemma mixedSignedChartRadical_infinite_count (k : ℕ) (b1 b0 : Bool) (V : BoundedRealPotential)
    [Infinite (diskSpectralData (mixedTraceDomain k b1 b0) V).eigenbasisIndex] :
    Module.finrank ℂ (mixedSignedChartRadical k b1 b0 V) =
      diskNonpositiveCount (mixedTraceDomain k b1 b0) V - diskNegativeCount (mixedTraceDomain k b1 b0) V := by
  rw [mixedSignedChartRadical_finrank]
  exact diskRadical_finrank_eq_count (mixedTraceDomain k b1 b0) V

lemma mixedSignedChartRadical_finite_count (k : ℕ) (b1 b0 : Bool) (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedTraceDomain k b1 b0))] :
    Module.finrank ℂ (mixedSignedChartRadical k b1 b0 V) =
      (diskSpectralData (mixedTraceDomain k b1 b0) V).finiteWeakCount (V.C + 1) 0 -
      (diskSpectralData (mixedTraceDomain k b1 b0) V).finiteStrictCount (V.C + 1) 0 := by
  rw [mixedSignedChartRadical_finrank]
  exact diskRadical_finrank_eq_finite_count (mixedTraceDomain k b1 b0) V

end KsIndex.Spectral
