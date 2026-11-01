module

public import KsIndexLean.WeakChainChartCriterion

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Genuine H1 regularity on a center-containing chart is exactly arc transmission. -/
theorem extendedSeamDomain_H1_iff_trace {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) :
    (MemLp (joinedDiskValue u v c) 2 (volume.restrict (extendedSeamDomain A hA : Set ℂ)) ∧
      ∃ J, TauCeti.HasWeakFDerivOn volume (extendedSeamDomain A hA) (joinedDiskValue u v c) J ∧
        MemLp J 2 (volume.restrict (extendedSeamDomain A hA : Set ℂ))) ↔
      arcTrace A u = c • arcTrace A v := by
  constructor
  · rintro ⟨_, J, hJ, _⟩
    exact (extendedSeamDomain_weak_iff_trace hA u v c).mp ⟨J, hJ⟩
  · intro hm
    exact ⟨extendedSeamDomain_value_memLp hA u v c, joinedDiskJet u v c,
      extendedSeamDomain_weak hA u v c hm, extendedSeamDomain_jet_memLp hA u v c⟩

/-- Both actual slit trace conditions are equivalent to their genuine weak chart criteria. -/
theorem mem_slitTraceDomain_iff_weak_charts (k : ℕ) (c : ℂ) (u : DiskPairH1) :
    u ∈ slitTraceDomain k c ↔
      (∃ J, TauCeti.HasWeakFDerivOn volume
        (extendedSeamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1))
        (joinedDiskValue u.1 u.2 1) J) ∧
      (∃ J, TauCeti.HasWeakFDerivOn volume
        (extendedSeamDomain (boundaryArc k 0) (isOpen_boundaryArc k 0))
        (joinedDiskValue u.1 u.2 c) J) := by
  rw [mem_slitTraceDomain, extendedSeamDomain_weak_iff_trace,
    extendedSeamDomain_weak_iff_trace, one_smul]

end KsIndex.Trace
