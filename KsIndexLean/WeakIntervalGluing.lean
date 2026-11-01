module

public import KsIndexLean.IntervalGluing

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
/-- Patch a.e. equalities on adjacent open intervals; the cut is a null singleton. -/
lemma joinAt_ae_of_sides {a c b : ℝ} {f p W : ℝ → E}
    (hl : f =ᵐ[volume.restrict (Ioo a c)] W)
    (hr : p =ᵐ[volume.restrict (Ioo c b)] W) :
    joinAt c f p =ᵐ[volume.restrict (Ioo a b)] W := by
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hl,
    (ae_restrict_iff' measurableSet_Ioo).mp hr, volume.ae_ne c] with t hl' hr' htc ht
  by_cases hle : t ≤ c
  · rw [joinAt, ite_eq_left hle]
    exact hl' ⟨ht.1, lt_of_le_of_ne hle htc⟩
  · rw [joinAt, ite_eq_right hle]
    exact hr' ⟨lt_of_not_ge hle, ht.2⟩

/-- Matching endpoint representatives produce one continuous representative across the cut. -/
theorem joinedPrimitive_ae {a c b : ℝ} (hac : a < c) (hcb : c < b)
    {f g p h : ℝ → E}
    (hl : TauCeti.HasWeakLineDerivOn volume (intervalOpens a c) f g 1)
    (hr : TauCeti.HasWeakLineDerivOn volume (intervalOpens c b) p h 1)
    (hg : IntervalIntegrable g volume a c) (hh : IntervalIntegrable h volume c b)
    (hm : representative hac f g c = representative hcb p h c) :
    joinAt c f p =ᵐ[volume.restrict (Ioo a b)]
      joinedPrimitive a c (representative hac f g a) g h := by
  apply joinAt_ae_of_sides
  · filter_upwards [representative_ae_eq hac hl hg,
      ae_restrict_mem measurableSet_Ioo] with t ht htI
    exact ht.trans (joinedPrimitive_left hac f hg (Ioo_subset_Icc_self htI)).symm
  · filter_upwards [representative_ae_eq hcb hr hh,
      ae_restrict_mem measurableSet_Ioo] with t ht htI
    exact ht.trans (joinedPrimitive_right hac hcb f p hg hh hm (Ioo_subset_Icc_self htI)).symm

/-- Radial weak gluing: matching endpoint traces remove the distributional jump. -/
theorem weak_joinAt_of_match {a c b : ℝ} (hac : a < c) (hcb : c < b)
    {f g p h : ℝ → E}
    (hl : TauCeti.HasWeakLineDerivOn volume (intervalOpens a c) f g 1)
    (hr : TauCeti.HasWeakLineDerivOn volume (intervalOpens c b) p h 1)
    (hg : IntervalIntegrable g volume a c) (hh : IntervalIntegrable h volume c b)
    (hm : representative hac f g c = representative hcb p h c) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) (joinAt c f p) (joinAt c g h) 1 :=
  (joinedPrimitive_weak hac hcb _ hg hh).congr_ae (joinedPrimitive_ae hac hcb hl hr hg hh hm).symm

/-- A common continuous representative forces the endpoint traces to match. -/
lemma match_of_common_representative {a c b : ℝ} (hac : a < c) (hcb : c < b)
    {f g p h W : ℝ → E}
    (hl : TauCeti.HasWeakLineDerivOn volume (intervalOpens a c) f g 1)
    (hr : TauCeti.HasWeakLineDerivOn volume (intervalOpens c b) p h 1)
    (hg : IntervalIntegrable g volume a c) (hh : IntervalIntegrable h volume c b)
    (hW : ContinuousOn W (Icc a b))
    (hfl : W =ᵐ[volume.restrict (Ioo a c)] f)
    (hpr : W =ᵐ[volume.restrict (Ioo c b)] p) :
    representative hac f g c = representative hcb p h c := by
  have h1 := representative_unique hac hl hg
    (hW.mono (Icc_subset_Icc le_rfl hcb.le)) hfl (right_mem_Icc.mpr hac.le)
  have h2 := representative_unique hcb hr hh
    (hW.mono (Icc_subset_Icc hac.le le_rfl)) hpr (left_mem_Icc.mpr hcb.le)
  exact h1.symm.trans h2

/-- Conversely, a global weak derivative with this integrable jet cannot hide a jump. -/
theorem match_of_weak_joinAt {a c b : ℝ} (hac : a < c) (hcb : c < b)
    {f g p h : ℝ → E}
    (hl : TauCeti.HasWeakLineDerivOn volume (intervalOpens a c) f g 1)
    (hr : TauCeti.HasWeakLineDerivOn volume (intervalOpens c b) p h 1)
    (hg : IntervalIntegrable g volume a c) (hh : IntervalIntegrable h volume c b)
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (joinAt c f p) (joinAt c g h) 1) :
    representative hac f g c = representative hcb p h c := by
  have hj := joinAt_integrable hac.le hcb.le hg hh
  apply match_of_common_representative hac hcb hl hr hg hh
    (representative_continuousOn (hac.trans hcb) (joinAt c f p) hj)
  · have he := (representative_ae_eq (hac.trans hcb) hw hj).symm.filter_mono
      (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo le_rfl hcb.le) le_rfl))
    filter_upwards [he, ae_restrict_mem measurableSet_Ioo] with t ht htI
    simpa only [joinAt, ite_eq_left htI.2.le] using ht
  · have he := (representative_ae_eq (hac.trans hcb) hw hj).symm.filter_mono
      (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo hac.le le_rfl) le_rfl))
    filter_upwards [he, ae_restrict_mem measurableSet_Ioo] with t ht htI
    simpa only [joinAt, ite_eq_right (not_le.mpr htI.1)] using ht

theorem weak_joinAt_iff_match {a c b : ℝ} (hac : a < c) (hcb : c < b)
    {f g p h : ℝ → E}
    (hl : TauCeti.HasWeakLineDerivOn volume (intervalOpens a c) f g 1)
    (hr : TauCeti.HasWeakLineDerivOn volume (intervalOpens c b) p h 1)
    (hg : IntervalIntegrable g volume a c) (hh : IntervalIntegrable h volume c b) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) (joinAt c f p) (joinAt c g h) 1 ↔
      representative hac f g c = representative hcb p h c :=
  ⟨match_of_weak_joinAt hac hcb hl hr hg hh, weak_joinAt_of_match hac hcb hl hr hg hh⟩

end KsIndex.Trace
