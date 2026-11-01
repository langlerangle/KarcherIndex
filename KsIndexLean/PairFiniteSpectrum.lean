module

public import KsIndexLean.NamedDomainSpectrum
public import KsIndexLean.WeakTransmissionDomains

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Trace KsIndex.Spherical

/-- Coordinate 0 is upper, coordinate 1 lower. -/
def pairFiniteDomain (D : Submodule ℂ DiskPairH1) : Submodule ℂ (Fin 2 → ComplexH1) :=
  D.comap (ContinuousLinearEquiv.finTwoArrow ℂ ComplexH1).toLinearMap

lemma pairFiniteDomain_closed (D : Submodule ℂ DiskPairH1) (hD : IsClosed (D : Set DiskPairH1)) :
    IsClosed (pairFiniteDomain D : Set (Fin 2 → ComplexH1)) :=
  hD.preimage (ContinuousLinearEquiv.finTwoArrow ℂ ComplexH1).continuous

lemma mem_pairFinite_slit (k : ℕ) (phase : ℂ) (u : Fin 2 → ComplexH1) :
    u ∈ pairFiniteDomain (slitTraceDomain k phase) ↔
      arcTrace (boundaryArc k 1) (u 0) = arcTrace (boundaryArc k 1) (u 1) ∧
      arcTrace (boundaryArc k 0) (u 0) = phase • arcTrace (boundaryArc k 0) (u 1) :=
  mem_slitTraceDomain k phase (u 0, u 1)

/-- Full-domain coordinate identification, not a restriction to smooth pairs. -/
def pairFiniteCoordinates (D : Submodule ℂ DiskPairH1) : pairFiniteDomain D ≃ₗ[ℂ] D where
  toFun u := ⟨(u.val 0, u.val 1), u.property⟩
  invFun u := ⟨![u.val.1, u.val.2], u.property⟩
  left_inv u := by apply Subtype.ext; funext i; fin_cases i <;> rfl
  right_inv u := by apply Subtype.ext; rfl
  map_add' u v := rfl
  map_smul' c u := rfl

/-- Combine the Hilbert-norm conversion with the ordered pair coordinates. -/
def pairHilbertCoordinates (D : Submodule ℂ DiskPairH1) :
    finiteH1Domain (pairFiniteDomain D) ≃ₗ[ℂ] D :=
  (LinearEquiv.ofBijective (finiteH1DomainCoordinates (pairFiniteDomain D)).toLinearMap
    (finiteH1DomainCoordinates_bijective (pairFiniteDomain D))).trans (pairFiniteCoordinates D)

lemma pairHilbertCoordinates_apply (D : Submodule ℂ DiskPairH1)
    (u : finiteH1Domain (pairFiniteDomain D)) :
    (pairHilbertCoordinates D u).val = (u.val 0, u.val 1) := rfl

lemma pairFiniteJacobi_eq (D : Submodule ℂ DiskPairH1) (V : BoundedRealPotential)
    (u v : finiteH1Domain (pairFiniteDomain D)) :
    finiteH1Jacobi (pairFiniteDomain D) V u v =
      weakJacobi V (pairHilbertCoordinates D u).val.1 (pairHilbertCoordinates D v).val.1 +
      weakJacobi V (pairHilbertCoordinates D u).val.2 (pairHilbertCoordinates D v).val.2 := by
  simp only [finiteH1Jacobi, Fin.sum_univ_two, pairHilbertCoordinates_apply]

instance slitFinite_complete (k : ℕ) (phase : ℂ) :
    CompleteSpace (finiteH1Domain (pairFiniteDomain (slitTraceDomain k phase))) :=
  finiteH1Domain_completeSpace _ (pairFiniteDomain_closed _ (isClosed_slitTraceDomain k phase))

def slitSpectralData (k : ℕ) (phase : ℂ) (V : BoundedRealPotential) :
    PositiveCompactSolution (WeightedFiniteAmbient (pairFiniteDomain (slitTraceDomain k phase))) :=
  finiteSpectralData (pairFiniteDomain (slitTraceDomain k phase)) V

def paperSlitSpectralData (α : ℝ) (V : BoundedRealPotential) :=
  slitSpectralData 3 (Complex.exp ((2 * Real.pi * α) * Complex.I)) V

end KsIndex.Spectral
