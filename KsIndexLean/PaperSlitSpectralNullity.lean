module

public import KsIndexLean.PaperSlitSpectralCoordinates
public import KsIndexLean.RadicalCoordinateTransport

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Full weak kernel in the paper’s spherical slit phase space. -/
def paperSlitChartRadical (α : ℝ) (V : BoundedRealPotential) :
    Submodule ℂ (PaperSphericalPhaseSpace α) :=
  @coordinateRadical (finiteH1Domain (pairFiniteDomain (paperSlitDomain α))) (PaperSphericalPhaseSpace α)
    inferInstance (finiteH1Domain_innerProductSpace _) inferInstance inferInstance
    (finiteJacobiForm (pairFiniteDomain (paperSlitDomain α)) V) (paperSlitSpectralCoordinates α)

lemma mem_paperSlitChartRadical (α : ℝ) (V : BoundedRealPotential)
    (u : PaperSphericalPhaseSpace α) : u ∈ paperSlitChartRadical α V ↔
      ∀ v : PaperSphericalPhaseSpace α, sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val v.val = 0 := by
  apply @mem_coordinateRadical (finiteH1Domain (pairFiniteDomain (paperSlitDomain α))) (PaperSphericalPhaseSpace α)
    inferInstance (finiteH1Domain_innerProductSpace _) inferInstance inferInstance
    (finiteJacobiForm (pairFiniteDomain (paperSlitDomain α)) V) (paperSlitSpectralCoordinates α)
    (fun u v : PaperSphericalPhaseSpace α => sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val v.val) _ u
  intro x y
  exact (paperSlitSpectralCoordinates_jacobi α V x y).trans (finiteJacobiForm_apply (pairFiniteDomain (paperSlitDomain α)) V x y).symm

lemma paperSlitChartRadical_finrank (α : ℝ) (V : BoundedRealPotential) :
    Module.finrank ℂ (paperSlitChartRadical α V) =
      Module.finrank ℂ (@formRadical (finiteH1Domain (pairFiniteDomain (paperSlitDomain α))) inferInstance
        (finiteH1Domain_innerProductSpace _) (finiteJacobiForm (pairFiniteDomain (paperSlitDomain α)) V)) :=
  @coordinateRadical_finrank (finiteH1Domain (pairFiniteDomain (paperSlitDomain α))) (PaperSphericalPhaseSpace α)
    inferInstance (finiteH1Domain_innerProductSpace _) inferInstance inferInstance
    (finiteJacobiForm (pairFiniteDomain (paperSlitDomain α)) V) (paperSlitSpectralCoordinates α)

lemma paperSlitChartRadical_infinite_count (α : ℝ) (V : BoundedRealPotential)
    [Infinite (finiteSpectralData (pairFiniteDomain (paperSlitDomain α)) V).eigenbasisIndex] :
    Module.finrank ℂ (paperSlitChartRadical α V) =
      finiteCopyNonpositiveCount (pairFiniteDomain (paperSlitDomain α)) V - finiteCopyNegativeCount (pairFiniteDomain (paperSlitDomain α)) V := by
  rw [paperSlitChartRadical_finrank]
  exact finiteCopyRadical_finrank_eq_count (pairFiniteDomain (paperSlitDomain α)) V

lemma paperSlitChartRadical_finite_count (α : ℝ) (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitDomain α)))] :
    Module.finrank ℂ (paperSlitChartRadical α V) =
      (finiteSpectralData (pairFiniteDomain (paperSlitDomain α)) V).finiteWeakCount (V.C + 1) 0 -
      (finiteSpectralData (pairFiniteDomain (paperSlitDomain α)) V).finiteStrictCount (V.C + 1) 0 := by
  rw [paperSlitChartRadical_finrank]
  exact finiteCopyRadical_finrank_eq_finite_count (pairFiniteDomain (paperSlitDomain α)) V

lemma paperSlitChartRadical_finiteDimensional (α : ℝ) (V : BoundedRealPotential) :
    FiniteDimensional ℂ (paperSlitChartRadical α V) := by
  let := finiteCopyRadical_finiteDimensional (pairFiniteDomain (paperSlitDomain α)) V
  exact (@coordinateRadicalEquiv (finiteH1Domain (pairFiniteDomain (paperSlitDomain α))) (PaperSphericalPhaseSpace α)
    inferInstance (finiteH1Domain_innerProductSpace _) inferInstance inferInstance
    (finiteJacobiForm (pairFiniteDomain (paperSlitDomain α)) V) (paperSlitSpectralCoordinates α)).finiteDimensional

end KsIndex.Spectral
