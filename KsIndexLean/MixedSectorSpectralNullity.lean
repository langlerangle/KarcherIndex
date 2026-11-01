module

public import KsIndexLean.MixedSectorWeakSpectrum
public import KsIndexLean.RadicalCoordinateTransport

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Set KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Full weak kernel of the actual signed chart form on its test domain. -/
def mixedSectorChartRadical (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ) (V : BoundedRealPotential) : Submodule ℂ (signedSphereSectorDomain k b1 b0 θ hθ d) :=
  @coordinateRadical (mixedSectorDomain k b1 b0 θ d) (signedSphereSectorDomain k b1 b0 θ hθ d) inferInstance
    (diskDomain_innerProductSpace _) inferInstance inferInstance
    (domainJacobiForm (mixedSectorDomain k b1 b0 θ d) V) (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d).toLinearEquiv

lemma mem_mixedSectorChartRadical (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ) (V : BoundedRealPotential) (u : signedSphereSectorDomain k b1 b0 θ hθ d) :
    u ∈ mixedSectorChartRadical k b1 b0 θ hθ d V ↔ ∀ v : signedSphereSectorDomain k b1 b0 θ hθ d,
      sphereChartJacobi (isOpen_boundaryArc k 1) V u.val v.val = 0 := by
  apply @mem_coordinateRadical_scaled (mixedSectorDomain k b1 b0 θ d) (signedSphereSectorDomain k b1 b0 θ hθ d) inferInstance
    (diskDomain_innerProductSpace _) inferInstance inferInstance
    (domainJacobiForm (mixedSectorDomain k b1 b0 θ d) V) (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d).toLinearEquiv
    (fun u v => sphereChartJacobi (isOpen_boundaryArc k 1) V u.val v.val)
    2 (by norm_num) _ u
  intro x y
  exact mixedSectorSphere_jacobi k b1 b0 θ hθ d V x y

lemma mixedSectorChartRadical_finrank (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ) (V : BoundedRealPotential) :
    Module.finrank ℂ (mixedSectorChartRadical k b1 b0 θ hθ d V) =
      Module.finrank ℂ (@formRadical (mixedSectorDomain k b1 b0 θ d) inferInstance
        (diskDomain_innerProductSpace _) (domainJacobiForm (mixedSectorDomain k b1 b0 θ d) V)) :=
  @coordinateRadical_finrank (mixedSectorDomain k b1 b0 θ d) (signedSphereSectorDomain k b1 b0 θ hθ d) inferInstance
    (diskDomain_innerProductSpace _) inferInstance inferInstance
    (domainJacobiForm (mixedSectorDomain k b1 b0 θ d) V) (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d).toLinearEquiv

lemma mixedSectorChartRadical_finiteDimensional (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ) (V : BoundedRealPotential) :
    FiniteDimensional ℂ (mixedSectorChartRadical k b1 b0 θ hθ d V) := by
  let := diskRadical_finiteDimensional (mixedSectorDomain k b1 b0 θ d) V
  exact (@coordinateRadicalEquiv (mixedSectorDomain k b1 b0 θ d) (signedSphereSectorDomain k b1 b0 θ hθ d) inferInstance
    (diskDomain_innerProductSpace _) inferInstance inferInstance
    (domainJacobiForm (mixedSectorDomain k b1 b0 θ d) V) (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d).toLinearEquiv).finiteDimensional

lemma mixedSectorChartRadical_infinite_count (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ) (V : BoundedRealPotential)
    [Infinite (diskSpectralData (mixedSectorDomain k b1 b0 θ d) V).eigenbasisIndex] :
    Module.finrank ℂ (mixedSectorChartRadical k b1 b0 θ hθ d V) =
      diskNonpositiveCount (mixedSectorDomain k b1 b0 θ d) V - diskNegativeCount (mixedSectorDomain k b1 b0 θ d) V := by
  rw [mixedSectorChartRadical_finrank]
  exact diskRadical_finrank_eq_count (mixedSectorDomain k b1 b0 θ d) V

lemma mixedSectorChartRadical_finite_count (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ) (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedSectorDomain k b1 b0 θ d))] :
    Module.finrank ℂ (mixedSectorChartRadical k b1 b0 θ hθ d V) =
      (diskSpectralData (mixedSectorDomain k b1 b0 θ d) V).finiteWeakCount (V.C + 1) 0 -
      (diskSpectralData (mixedSectorDomain k b1 b0 θ d) V).finiteStrictCount (V.C + 1) 0 := by
  rw [mixedSectorChartRadical_finrank]
  exact diskRadical_finrank_eq_finite_count (mixedSectorDomain k b1 b0 θ d) V

end KsIndex.Spectral
