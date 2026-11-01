module

public import KsIndexLean.DiskTraceBound

@[expose] public section


open Set MeasureTheory

namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Any admissible annular data with the same value class produce the same endpoint.
The derivative may be any genuine weak derivative with the stated L² components. -/
theorem diskTrace_eq_of_annular_data (u : ComplexH1) {f : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume (annulusOpens (1 / 2) 1) f U)
    (hf : MemLp f 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 1)))
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 1)))
    (hI : MemLp (fun z => U z Complex.I) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 1)))
    (he : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 1)] f) :
    diskTraceCLM u = representative (by norm_num : (1 / 2 : ℝ) < 1)
      (sliceLp (1 / 2) 1 f) (sliceLp (1 / 2) 1 (radialField U)) 1 := by
  have hp := weak_polar_pullback (by norm_num) (by norm_num) hw hf h1 hI
  apply representative_unique (by norm_num) hp.2.2 hp.2.1
    (diskRepresentative_continuousOn u) ?_ (by norm_num)
  filter_upwards [diskRepresentative_ae u,
    sliceLp_congr_ae (by norm_num : (0 : ℝ) < 1 / 2) he] with t ht hs
  exact ht.symm.trans hs

/-- The trace depends only on the weak value class, including derivative-choice independence. -/
theorem diskTrace_congr_value_ae {u v : ComplexH1}
    (he : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] valueCLM v) :
    diskTraceCLM u = diskTraceCLM v := by
  rw [valueCLM_injective (Lp.ext he)]

end KsIndex.Trace
