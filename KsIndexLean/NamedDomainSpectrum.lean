module

public import KsIndexLean.DiskSpectralEquality
public import KsIndexLean.FiniteCopySpectralEquality
public import KsIndexLean.JacobiFormNullity
public import KsIndexLean.WeakBoundaryDomains
public import KsIndexLean.WeakDiskChain

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Trace KsIndex.Spherical

/-- Closed mixed-boundary domains inherit the actual H1 completeness. -/
instance mixedTraceDomain_complete (k : ℕ) (b1 b0 : Bool) :
    CompleteSpace (mixedTraceDomain k b1 b0) :=
  (isClosed_mixedTraceDomain k b1 b0).isComplete.completeSpace_coe

instance weakCharacterDomain_complete (θ : ℝ) (c : ℂ) :
    CompleteSpace (weakCharacterDomain θ c) :=
  (isClosed_weakCharacterDomain θ c).isComplete.completeSpace_coe

instance mixedCharacterDomain_complete (k r : ℕ) (b1 b0 : Bool) :
    CompleteSpace (mixedCharacterDomain k r b1 b0) :=
  (isClosed_mixedCharacterDomain k r b1 b0).isComplete.completeSpace_coe

/-- The chain uses the sum-of-squares H1 norm adopted by the finite-copy form,
not the sup norm of an unconverted function space. -/
instance weakDiskChain_hilbert_complete (k m : ℕ) [NeZero m] :
    CompleteSpace (finiteH1Domain (weakDiskChain k m)) :=
  finiteH1Domain_completeSpace _ (isClosed_weakDiskChain k m)

/-- All four mixed choices, including the unrestricted NN domain. -/
def mixedTraceSpectralData (k : ℕ) (b1 b0 : Bool) (V : BoundedRealPotential) :
    PositiveCompactSolution (WeightedDiskAmbient (mixedTraceDomain k b1 b0)) :=
  diskSpectralData (mixedTraceDomain k b1 b0) V

def mixedCharacterSpectralData (k r : ℕ) (b1 b0 : Bool) (V : BoundedRealPotential) :
    PositiveCompactSolution (WeightedDiskAmbient (mixedCharacterDomain k r b1 b0)) :=
  diskSpectralData (mixedCharacterDomain k r b1 b0) V

/-- Character value and rotation angle are unrestricted parameters. -/
def characterSpectralData (θ : ℝ) (c : ℂ) (V : BoundedRealPotential) :
    PositiveCompactSolution (WeightedDiskAmbient (weakCharacterDomain θ c)) :=
  diskSpectralData (weakCharacterDomain θ c) V

def chainSpectralData (k m : ℕ) [NeZero m] (V : BoundedRealPotential) :
    PositiveCompactSolution (WeightedFiniteAmbient (weakDiskChain k m)) :=
  finiteSpectralData (weakDiskChain k m) V

/-- A concrete mixed-boundary min-max statement with completeness discharged.
The finite-dimensional alternative is provided by diskJacobi_finite_minmax. -/
lemma mixedTrace_infinite_minmax (k : ℕ) (b1 b0 : Bool) (V : BoundedRealPotential)
    [Infinite (mixedTraceSpectralData k b1 b0 V).eigenbasisIndex] (n : ℕ) (L : ℝ) :
    (mixedTraceSpectralData k b1 b0 V).infiniteReciprocalShift (V.C + 1) n ≤ L ↔
      ∃ W : Submodule ℂ (mixedTraceDomain k b1 b0), FiniteDimensional ℂ W ∧
        Module.finrank ℂ W = n + 1 ∧ ∀ u : W,
          (weakJacobi V (u : mixedTraceDomain k b1 b0) (u : mixedTraceDomain k b1 b0)).re ≤
            L * ‖weightedDiskAmbientEmbedding (mixedTraceDomain k b1 b0) (u : mixedTraceDomain k b1 b0)‖ ^ 2 := by
  let : Infinite (diskSpectralData (mixedTraceDomain k b1 b0) V).eigenbasisIndex :=
    inferInstanceAs (Infinite (mixedTraceSpectralData k b1 b0 V).eigenbasisIndex)
  exact diskJacobi_infinite_minmax (mixedTraceDomain k b1 b0) V n L

lemma mixedTrace_finite_minmax (k : ℕ) (b1 b0 : Bool) (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedTraceDomain k b1 b0))]
    (n : Fin (Module.finrank ℂ (WeightedDiskAmbient (mixedTraceDomain k b1 b0)))) (L : ℝ) :
    (mixedTraceSpectralData k b1 b0 V).finiteReciprocalShift (V.C + 1) n ≤ L ↔
      ∃ W : Submodule ℂ (mixedTraceDomain k b1 b0), FiniteDimensional ℂ W ∧
        Module.finrank ℂ W = n.val + 1 ∧ ∀ u : W,
          (weakJacobi V (u : mixedTraceDomain k b1 b0) (u : mixedTraceDomain k b1 b0)).re ≤
            L * ‖weightedDiskAmbientEmbedding (mixedTraceDomain k b1 b0) (u : mixedTraceDomain k b1 b0)‖ ^ 2 :=
  diskJacobi_finite_minmax (mixedTraceDomain k b1 b0) V n L

end KsIndex.Spectral
