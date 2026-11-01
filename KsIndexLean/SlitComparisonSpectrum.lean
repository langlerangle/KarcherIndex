module

public import KsIndexLean.PairFiniteSpectrum

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Trace KsIndex.Spherical

/-- The spectral mass is the sum of the two actual spherical chart masses. -/
lemma pairFinite_mass_eq (D : Submodule ℂ DiskPairH1)
    (u : finiteH1Domain (pairFiniteDomain D)) :
    ‖finiteH1WeightedValue (pairFiniteDomain D) u‖ ^ 2 =
      ‖weightedDiskValueCLM (pairHilbertCoordinates D u).val.1‖ ^ 2 +
      ‖weightedDiskValueCLM (pairHilbertCoordinates D u).val.2‖ ^ 2 := by
  change ‖weightedFiniteValueCLM (Fin 2) (fun i => u.val i)‖ ^ 2 = _
  rw [weightedFiniteValueCLM_norm_sq, Fin.sum_univ_two]
  rfl

lemma pairFinite_mass_pairing_eq (D : Submodule ℂ DiskPairH1)
    (u v : finiteH1Domain (pairFiniteDomain D)) :
    inner ℂ (finiteH1WeightedValue (pairFiniteDomain D) u)
      (finiteH1WeightedValue (pairFiniteDomain D) v) =
      inner ℂ (weightedDiskValueCLM (pairHilbertCoordinates D u).val.1)
        (weightedDiskValueCLM (pairHilbertCoordinates D v).val.1) +
      inner ℂ (weightedDiskValueCLM (pairHilbertCoordinates D u).val.2)
        (weightedDiskValueCLM (pairHilbertCoordinates D v).val.2) := by
  change inner ℂ (weightedFiniteValueCLM (Fin 2) (fun i => u.val i))
    (weightedFiniteValueCLM (Fin 2) (fun i => v.val i)) = _
  change (∑ i : Fin 2, inner ℂ (weightedDiskValueCLM (u.val i)) (weightedDiskValueCLM (v.val i))) = _
  rw [Fin.sum_univ_two]
  rfl

instance slitNeumannFinite_complete (k : ℕ) :
    CompleteSpace (finiteH1Domain (pairFiniteDomain (slitNeumannDomain k))) :=
  finiteH1Domain_completeSpace _ (pairFiniteDomain_closed _ (isClosed_slitNeumannDomain k))

instance slitDirichletFinite_complete (k : ℕ) :
    CompleteSpace (finiteH1Domain (pairFiniteDomain (slitDirichletDomain k))) :=
  finiteH1Domain_completeSpace _ (pairFiniteDomain_closed _ (isClosed_slitDirichletDomain k))

instance paperSlitCharacterFinite_complete (α : ℝ) (j : ℕ) :
    CompleteSpace (finiteH1Domain (pairFiniteDomain (paperSlitCharacterDomain α j))) :=
  finiteH1Domain_completeSpace _ (pairFiniteDomain_closed _ (isClosed_paperSlitCharacterDomain α j))

def slitNeumannSpectralData (k : ℕ) (V : BoundedRealPotential) :
    PositiveCompactSolution (WeightedFiniteAmbient (pairFiniteDomain (slitNeumannDomain k))) :=
  finiteSpectralData (pairFiniteDomain (slitNeumannDomain k)) V

def slitDirichletSpectralData (k : ℕ) (V : BoundedRealPotential) :
    PositiveCompactSolution (WeightedFiniteAmbient (pairFiniteDomain (slitDirichletDomain k))) :=
  finiteSpectralData (pairFiniteDomain (slitDirichletDomain k)) V

def paperSlitCharacterSpectralData (α : ℝ) (j : ℕ) (V : BoundedRealPotential) :
    PositiveCompactSolution (WeightedFiniteAmbient (pairFiniteDomain (paperSlitCharacterDomain α j))) :=
  finiteSpectralData (pairFiniteDomain (paperSlitCharacterDomain α j)) V

/-- The Hilbert coordinate change preserves the actual bracketing domain
inclusions. Eigenvalue inequalities are subsequent consumers of these facts. -/
lemma slitDirichletFinite_le_phase (k : ℕ) (phase : ℂ) :
    finiteH1Domain (pairFiniteDomain (slitDirichletDomain k)) ≤
      finiteH1Domain (pairFiniteDomain (slitTraceDomain k phase)) := by
  intro u hu
  exact slitDirichlet_le_phase k phase hu

lemma slitPhaseFinite_le_Neumann (k : ℕ) (phase : ℂ) :
    finiteH1Domain (pairFiniteDomain (slitTraceDomain k phase)) ≤
      finiteH1Domain (pairFiniteDomain (slitNeumannDomain k)) := by
  intro u hu
  exact slitPhase_le_Neumann k phase hu

end KsIndex.Spectral
