module

public import KsIndexLean.ArcCutoffSeparation
public import KsIndexLean.CutoffPlanarEquivalence

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Actual arc transmission is equivalent to all supported smooth planar cutoff tests. -/
theorem arcTrace_eq_iff_planar_cutoff_tests {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) :
    arcTrace A u = c • arcTrace A v ↔
    ∀ (η : ℂ → ℝ) (_hη : ContDiff ℝ (⊤ : ℕ∞) η),
      (∀ w : Circle₁, w ∉ A → η w = 0) →
      TauCeti.HasWeakFDerivOn volume (annulusOpens (1 / 2) 2) (cutoffDiskValue η u v c)
        (reconstructedJet (cutoffDiskRadial η u v c) (cutoffDiskAngular η u v c)) := by
  constructor
  · intro hm η hη hs
    exact cutoffDisk_weak_reconstruction hA.measurableSet hη hs u v c hm
  · intro h
    change boundaryRestrict A (diskTraceCLM u) = c • boundaryRestrict A (diskTraceCLM v)
    rw [← boundaryRestrict_smul]
    apply boundaryRestrict_eq_of_cutoff_tests hA
    intro η hη hs
    exact cutoff_trace_eq_of_planar_weak hη u v c (h η hη hs)

end KsIndex.Trace
