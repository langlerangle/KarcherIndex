module

public import KsIndexLean.SeamCutoff
public import KsIndexLean.SeamDomainLocal

@[expose] public section


open Set MeasureTheory
open scoped ContDiff Topology

noncomputable section
namespace KsIndex.Trace

/-- A cutoff equal to one near a matching point can vanish near every unmatched circle point. -/
theorem exists_supported_seam_cutoff {A : Set Circle₁} (hA : IsOpen A) {w : Circle₁}
    (hw : w ∈ A) :
    ∃ η : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧
      (∀ x : Circle₁, x ∉ A → η =ᶠ[𝓝 (x : ℂ)] (fun _ => 0)) ∧
      η =ᶠ[𝓝 (w : ℂ)] (fun _ => 1) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hA w hw
  let f : ContDiffBump (w : ℂ) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨f, f.contDiff, ?_, f.eventuallyEq_one⟩
  intro x hx
  apply notMem_tsupport_iff_eventuallyEq.mp
  intro ht
  rw [f.tsupport_eq] at ht
  have hd : dist (x : ℂ) (w : ℂ) ≤ ε / 2 := ht
  have hb : x ∈ Metric.ball w ε := by
    change dist (x : ℂ) (w : ℂ) < ε
    linarith
  exact hx (hball hb)

/-- Local vanishing at unmatched circle points puts the angular support inside the seam domain. -/
lemma angularCutoff_support_in_seamDomain {A : Set Circle₁} (hA : IsOpen A) {η : ℂ → ℝ}
    (hη : ∀ x : Circle₁, x ∉ A → η =ᶠ[𝓝 (x : ℂ)] (fun _ => 0)) :
    annulusSet (1 / 2 : ℝ) 2 ∩ tsupport (fun z => η (nUnit z)) ⊆
      (seamDomain A hA : Set ℂ) := by
  rintro z ⟨hz, ht⟩
  refine ⟨hz, ?_⟩
  rintro ⟨w, hw, he⟩
  have hc : Filter.Tendsto nUnit (𝓝 (w : ℂ)) (𝓝 (w : ℂ)) := by
    simpa only [ContinuousAt, nUnit_circle] using continuousAt_nUnit_circle w
  have hn : (w : ℂ) ∉ tsupport (fun z => η (nUnit z)) :=
    notMem_tsupport_iff_eventuallyEq.mpr (hc.eventually (hη w hw))
  exact hn (he.symm ▸ ht)

end KsIndex.Trace
