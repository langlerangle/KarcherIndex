module

public import KsIndexLean.WeakDerivativeLocalToGlobal

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Global uncut planar gluing on the domain that retains exactly the matching seam arcs. -/
theorem seamDomain_weak_gluing {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) (hm : arcTrace A u = c • arcTrace A v) :
    TauCeti.HasWeakFDerivOn volume (seamDomain A hA)
      (joinedDiskValue u v c) (joinedDiskJet u v c) := by
  have hs : (seamDomain A hA : Set ℂ) ⊆ annulusSet (1 / 2 : ℝ) 2 := fun _ hz => hz.1
  apply weakF_of_local
  · exact (integrableOn_annulus_of_memLp (by norm_num) (by norm_num)
      (memLp_joinedDiskValue u v c)).locallyIntegrableOn.mono_set hs
  · intro d
    have hd := (memLp_joinedDiskJet u v c).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℂ d)
    have hi := integrableOn_annulus_of_memLp (by norm_num) (by norm_num) hd
    exact hi.locallyIntegrableOn.mono_set hs
  · intro z hz
    obtain ⟨V, hzV, _, hV⟩ := seamDomain_local_weak hA u v c hm hz
    exact ⟨V, hzV, hV⟩

lemma seamDomain_value_memLp {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) :
    MemLp (joinedDiskValue u v c) 2 (volume.restrict (seamDomain A hA : Set ℂ)) :=
  (memLp_joinedDiskValue u v c).mono_measure
    (Measure.restrict_mono (fun _ hz => hz.1) le_rfl)

lemma seamDomain_jet_memLp {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) :
    MemLp (joinedDiskJet u v c) 2 (volume.restrict (seamDomain A hA : Set ℂ)) :=
  (memLp_joinedDiskJet u v c).mono_measure
    (Measure.restrict_mono (fun _ hz => hz.1) le_rfl)

end KsIndex.Trace
