module

public import KsIndexLean.WeakDerivativeLocalToGlobal

@[expose] public section


open Set MeasureTheory TopologicalSpace

noncomputable section
namespace KsIndex.Trace

/-- Genuine weak neighborhoods supply local integrability for globalization. -/
theorem weakF_of_weak_neighborhoods {Ω : Opens ℂ}
    {u : ℂ → ℂ} {J : ℂ → ℂ →L[ℝ] ℂ}
    (hlocal : ∀ z ∈ Ω, ∃ V : Opens ℂ, z ∈ V ∧
      TauCeti.HasWeakFDerivOn volume V u J) :
    TauCeti.HasWeakFDerivOn volume Ω u J := by
  apply weakF_of_local _ _ hlocal
  · intro z hz
    obtain ⟨V, hzV, hV⟩ := hlocal z hz
    have hi := hV.locallyIntegrableOn z hzV
    rw [V.isOpen.nhdsWithin_eq hzV] at hi
    exact hi.filter_mono nhdsWithin_le_nhds
  · intro d z hz
    obtain ⟨V, hzV, hV⟩ := hlocal z hz
    have hi := (hV.hasWeakLineDerivOn d).locallyIntegrableOn_deriv z hzV
    rw [V.isOpen.nhdsWithin_eq hzV] at hi
    exact hi.filter_mono nhdsWithin_le_nhds

end KsIndex.Trace
