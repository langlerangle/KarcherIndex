module

public import KsIndexLean.AngularCutoff

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

/-- Arc equality suffices when the multiplier vanishes off that arc. -/
lemma circleMul_eq_of_restrict_eq {A : Set Circle₁} (hA : MeasurableSet A)
    (η : C(Circle₁, ℝ)) (hη : ∀ w ∉ A, η w = 0)
    {F G : Lp ℂ 2 circleMeasure} (h : boundaryRestrict A F = boundaryRestrict A G) :
    circleMul η F = circleMul η G := by
  have he : F =ᵐ[circleMeasure.restrict A] G := by
    have hF := boundaryRestrict_coe_ae A F
    rw [h] at hF
    exact hF.symm.trans (boundaryRestrict_coe_ae A G)
  apply Lp.ext
  filter_upwards [(ae_restrict_iff' hA).mp he, circleMul_coe η F, circleMul_coe η G]
    with w hw hF hG
  rw [hF, hG]
  by_cases hmem : w ∈ A
  · rw [hw hmem]
  · rw [hη w hmem, zero_smul, zero_smul]

lemma representative_circleMul {a b : ℝ} (hab : a < b)
    (η : C(Circle₁, ℝ)) {f g : ℝ → Lp ℂ 2 circleMeasure}
    (hf : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b) {r : ℝ} (hr : r ∈ Icc a b) :
    representative hab (fun t => circleMul η (f t)) (fun t => circleMul η (g t)) r =
      circleMul η (representative hab f g r) := by
  have hi : IntervalIntegrable (fun t => circleMul η (g t)) volume a b :=
    ⟨(circleMulCLM η).integrable_comp hg.1, (circleMulCLM η).integrable_comp hg.2⟩
  have hc := (circleMulCLM η).continuous.comp_continuousOn
    (representative_continuousOn hab f hg)
  have he : (fun t => circleMul η (representative hab f g t))
      =ᵐ[volume.restrict (Ioo a b)] (fun t => circleMul η (f t)) := by
    filter_upwards [representative_ae_eq hab hf hg] with t ht
    exact congrArg (circleMul η) ht.symm
  exact (representative_unique hab (circleMul_weakInterval η hf) hi hc he hr).symm

/-- Local trace matching removes the radial jump after a supported angular cutoff. -/
theorem cutoff_weak_joinAt_of_arc_match {a c b : ℝ} (hac : a < c) (hcb : c < b)
    {A : Set Circle₁} (hA : MeasurableSet A)
    (η : C(Circle₁, ℝ)) (hη : ∀ w ∉ A, η w = 0)
    {f g p q : ℝ → Lp ℂ 2 circleMeasure}
    (hf : TauCeti.HasWeakLineDerivOn volume (intervalOpens a c) f g 1)
    (hp : TauCeti.HasWeakLineDerivOn volume (intervalOpens c b) p q 1)
    (hg : IntervalIntegrable g volume a c) (hq : IntervalIntegrable q volume c b)
    (hm : boundaryRestrict A (representative hac f g c) =
      boundaryRestrict A (representative hcb p q c)) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (joinAt c (fun t => circleMul η (f t)) (fun t => circleMul η (p t)))
      (joinAt c (fun t => circleMul η (g t)) (fun t => circleMul η (q t))) 1 := by
  apply weak_joinAt_of_match hac hcb (circleMul_weakInterval η hf)
    (circleMul_weakInterval η hp)
    ⟨(circleMulCLM η).integrable_comp hg.1, (circleMulCLM η).integrable_comp hg.2⟩
    ⟨(circleMulCLM η).integrable_comp hq.1, (circleMulCLM η).integrable_comp hq.2⟩
  rw [representative_circleMul hac η hf hg (right_mem_Icc.mpr hac.le),
    representative_circleMul hcb η hp hq (left_mem_Icc.mpr hcb.le)]
  exact circleMul_eq_of_restrict_eq hA η hη hm

end KsIndex.Trace
