module

public import KsIndexLean.SeamCutoffLocalization
public import KsIndexLean.ArcCutoffSeparation
public import KsIndexLean.CutoffPlanarNecessity

@[expose] public section


open Set MeasureTheory
open scoped ContDiff Topology

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- A local nonvanishing family of multipliers suffices to recover the restricted L² class. -/
lemma boundaryRestrict_eq_of_local_multipliers (A : Set Circle₁) {F G : Lp ℂ 2 circleMeasure}
    (h : ∀ w ∈ A, ∃ η : C(Circle₁, ℝ), η w ≠ 0 ∧ circleMul η F = circleMul η G) :
    boundaryRestrict A F = boundaryRestrict A G := by
  classical
  choose η hn he using fun w : A => h w w.property
  let U : A → Set Circle₁ := fun w => {x | η w x ≠ 0}
  have ho : ∀ w, IsOpen (U w) := fun w =>
    (isClosed_eq (η w).continuous continuous_const).isOpen_compl
  have hc : A ⊆ ⋃ w, U w := by
    intro w hw
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, hn ⟨w, hw⟩⟩
  obtain ⟨s, hsc, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof A).elim_countable_subcover U ho hc
  have heU : F =ᵐ[circleMeasure.restrict (⋃ w ∈ s, U w)] G := by
    apply (ae_eq_restrict_biUnion_iff U hsc F G).mpr
    intro w _
    exact ae_eq_on_nonzero_of_circleMul_eq (η w) (he w)
  have heA := heU.filter_mono (ae_mono (Measure.restrict_mono hcover le_rfl))
  exact Lp.ext ((boundaryRestrict_coe_ae A F).trans (heA.trans (boundaryRestrict_coe_ae A G).symm))

/-- Genuine annular seam regularity is equivalent to scalar-matched disk traces. -/
theorem seamDomain_weak_iff_trace {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) :
    (∃ J, TauCeti.HasWeakFDerivOn volume (seamDomain A hA) (joinedDiskValue u v c) J) ↔
      arcTrace A u = c • arcTrace A v := by
  constructor
  · rintro ⟨J, hw⟩
    change boundaryRestrict A (diskTraceCLM u) = c • boundaryRestrict A (diskTraceCLM v)
    rw [← boundaryRestrict_smul]
    apply boundaryRestrict_eq_of_local_multipliers A
    intro w hwA
    obtain ⟨η, hη, hs, h1⟩ := exists_supported_seam_cutoff hA hwA
    refine ⟨realCircleMap η hη.continuous, ?_, ?_⟩
    · change η (w : ℂ) ≠ 0
      rw [h1.eq_of_nhds]
      exact one_ne_zero
    · exact cutoff_trace_eq_of_planar_weak hη u v c
        (seamDomain_cutoff_localization hA hη hs u v c hw)
  · intro hm
    exact ⟨joinedDiskJet u v c, seamDomain_weak_gluing hA u v c hm⟩

end KsIndex.Trace
