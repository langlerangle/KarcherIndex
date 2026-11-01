module

public import KsIndexLean.PaperSmoothChainSector

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.NegativeDensity

/-- The original smooth sector cannot have more negative directions than its
weak realization. Density is needed only for the reverse inequality. -/
lemma paperSmoothSector_index_le (m n j : ℕ) [NeZero m] :
    KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m) (paperSmoothJointSector m n j) ≤
      negativeIndex (fun u : PaperChainSector m n j =>
        (chainChartJacobi 3 m (surfacePotential 3) u.val.val u.val.val).re) := by
  rw [KsIndex.FormIndex.formIndex_eq_negativeIndex]
  have hzero : chainChartJacobi 3 m (surfacePotential 3) 0 0 = 0 := by
    have h := chainChartJacobi_add_left 3 m (surfacePotential 3) 0 0 0
    simp only [add_zero] at h
    linear_combination -h
  have h := negativeIndex_pullback_le
    (fun u : PaperChainSector m n j =>
      (chainChartJacobi 3 m (surfacePotential 3) u.val.val u.val.val).re)
    (by change (chainChartJacobi 3 m (surfacePotential 3) 0 0).re = 0
        rw [hzero, Complex.zero_re]) (paperSmoothToChainSector m n j)
  simpa only [paperSmoothToChainSector_form] using h

end KsIndex.Spectral
