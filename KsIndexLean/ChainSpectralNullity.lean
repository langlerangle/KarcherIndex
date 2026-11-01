module

public import KsIndexLean.ChainSpectralCoordinates
public import KsIndexLean.RadicalCoordinateTransport

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Full weak kernel in the actual cyclic chart quotient. -/
def chainChartRadical (k m : ℕ) [NeZero m] (V : BoundedRealPotential) :
    Submodule ℂ (ChainChartSpace k m) :=
  @coordinateRadical (finiteH1Domain (weakDiskChain k m)) (ChainChartSpace k m)
    inferInstance (finiteH1Domain_innerProductSpace _) inferInstance inferInstance
    (finiteJacobiForm (weakDiskChain k m) V) (chainSpectralCoordinates k m)

lemma mem_chainChartRadical (k m : ℕ) [NeZero m] (V : BoundedRealPotential)
    (u : ChainChartSpace k m) : u ∈ chainChartRadical k m V ↔
      ∀ v, chainChartJacobi k m V u v = 0 := by
  apply @mem_coordinateRadical (finiteH1Domain (weakDiskChain k m)) (ChainChartSpace k m)
    inferInstance (finiteH1Domain_innerProductSpace _) inferInstance inferInstance
    (finiteJacobiForm (weakDiskChain k m) V) (chainSpectralCoordinates k m)
    (chainChartJacobi k m V) _ u
  intro x y
  exact (chainSpectralCoordinates_jacobi k m V x y).trans (finiteJacobiForm_apply (weakDiskChain k m) V x y).symm

lemma chainChartRadical_finrank (k m : ℕ) [NeZero m] (V : BoundedRealPotential) :
    Module.finrank ℂ (chainChartRadical k m V) =
      Module.finrank ℂ (@formRadical (finiteH1Domain (weakDiskChain k m)) inferInstance
        (finiteH1Domain_innerProductSpace _) (finiteJacobiForm (weakDiskChain k m) V)) :=
  @coordinateRadical_finrank (finiteH1Domain (weakDiskChain k m)) (ChainChartSpace k m)
    inferInstance (finiteH1Domain_innerProductSpace _) inferInstance inferInstance
    (finiteJacobiForm (weakDiskChain k m) V) (chainSpectralCoordinates k m)

lemma chainChartRadical_infinite_count (k m : ℕ) [NeZero m] (V : BoundedRealPotential)
    [Infinite (finiteSpectralData (weakDiskChain k m) V).eigenbasisIndex] :
    Module.finrank ℂ (chainChartRadical k m V) =
      finiteCopyNonpositiveCount (weakDiskChain k m) V - finiteCopyNegativeCount (weakDiskChain k m) V := by
  rw [chainChartRadical_finrank]
  exact finiteCopyRadical_finrank_eq_count (weakDiskChain k m) V

lemma chainChartRadical_finite_count (k m : ℕ) [NeZero m] (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedFiniteAmbient (weakDiskChain k m))] :
    Module.finrank ℂ (chainChartRadical k m V) =
      (finiteSpectralData (weakDiskChain k m) V).finiteWeakCount (V.C + 1) 0 -
      (finiteSpectralData (weakDiskChain k m) V).finiteStrictCount (V.C + 1) 0 := by
  rw [chainChartRadical_finrank]
  exact finiteCopyRadical_finrank_eq_finite_count (weakDiskChain k m) V

lemma chainChartRadical_finiteDimensional (k m : ℕ) [NeZero m] (V : BoundedRealPotential) :
    FiniteDimensional ℂ (chainChartRadical k m V) := by
  let := finiteCopyRadical_finiteDimensional (weakDiskChain k m) V
  exact (@coordinateRadicalEquiv (finiteH1Domain (weakDiskChain k m)) (ChainChartSpace k m)
    inferInstance (finiteH1Domain_innerProductSpace _) inferInstance inferInstance
    (finiteJacobiForm (weakDiskChain k m) V) (chainSpectralCoordinates k m)).finiteDimensional

end KsIndex.Spectral
