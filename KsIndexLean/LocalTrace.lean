module

public import KsIndexLean.BoundaryRestriction

@[expose] public section


open Set MeasureTheory

namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Annular a.e. predicates transport to almost every radius and circle point. -/
lemma ae_radial_predicate {a b : ℝ} (ha : 0 < a) {P : ℂ → Prop}
    (hP : ∀ᵐ z ∂volume.restrict (annulusSet a b), P z) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ᵐ w : Circle₁ ∂circleMeasure, P (t • (w : ℂ)) := by
  obtain ⟨N, hN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  have hn : volume (N ∩ annulusSet a b) = 0 := by
    rwa [Measure.restrict_apply' measurableSet_annulusSet] at hN0
  filter_upwards [slice_ae_null ha hNm hn] with t ht
  apply ae_iff.mpr
  exact measure_mono_null (fun w hw => hN hw) ht

lemma diskRepresentative_continuousOn_tail (u : ComplexH1) {c : ℝ} (hc : 1 / 2 ≤ c) :
    ContinuousOn (diskRepresentative u) (Icc c 1) :=
  (diskRepresentative_continuousOn u).mono (Icc_subset_Icc hc le_rfl)

/-- The restricted endpoint is determined by any continuous profile agreeing a.e. near it. -/
lemma arcTrace_eq_of_profile (A : Set Circle₁) (u : ComplexH1) {c : ℝ}
    (hc : 1 / 2 ≤ c) (hc1 : c < 1) {V : ℝ → Lp ℂ 2 (circleMeasure.restrict A)}
    (hV : ContinuousOn V (Icc c 1))
    (he : (fun t => boundaryRestrictCLM A (diskProfile u t)) =ᵐ[volume.restrict (Ioo c 1)] V) :
    arcTrace A u = V 1 := by
  have hr := (diskRepresentative_ae u).filter_mono
    (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo hc le_rfl) le_rfl))
  have hcont := (boundaryRestrictCLM A).continuous.comp_continuousOn
    (diskRepresentative_continuousOn_tail u hc)
  apply eqOn_Icc_of_ae_eq hc1 hcont hV ?_ ⟨hc1.le, le_rfl⟩
  filter_upwards [hr, he] with t ht he'
  change boundaryRestrictCLM A (diskRepresentative u t) = V t
  rw [← ht]
  exact he'

/-- A radial collar of a boundary set, with no pointwise condition at the outer endpoint. -/
def radialWedge (c : ℝ) (A : Set Circle₁) : Set ℂ :=
  {z | ∃ t ∈ Ioo c 1, ∃ w ∈ A, z = t • (w : ℂ)}

/-- Local collar agreement identifies the restricted trace with a continuous extension. -/
theorem arcTrace_eq_of_wedge (A : Set Circle₁) (hA : MeasurableSet A) (u : ComplexH1)
    {c : ℝ} (hc : 1 / 2 ≤ c) (hc1 : c < 1) {h : ℂ → ℂ} (hh : ContinuousOn h annulus)
    (he : ∀ᵐ z ∂volume.restrict (annulusSet c 1),
      z ∈ radialWedge c A → valueCLM u z = h z) :
    arcTrace A u = boundaryRestrictCLM A (closedAnnulusProfile hh 1) := by
  apply arcTrace_eq_of_profile A u hc hc1
    ((boundaryRestrictCLM A).continuous.comp (continuous_closedAnnulusProfile hh)).continuousOn
  have hs := (sliceLp_coe_ae (by norm_num) (collar_memLp (valueCLM u))).filter_mono
    (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo hc le_rfl) le_rfl))
  have hp := ae_radial_predicate (by linarith : 0 < c) he
  filter_upwards [hs, hp, ae_restrict_mem measurableSet_Ioo] with t ht hp' htI
  apply Lp.ext
  have hv := (closedAnnulusProfile_coe_ae hh
    (show t ∈ Icc (1 / 2 : ℝ) 1 from ⟨hc.trans htI.1.le, htI.2.le⟩)).filter_mono
      (ae_mono (Measure.restrict_le_self (s := A)))
  have ht' := ht.filter_mono (ae_mono (Measure.restrict_le_self (s := A)))
  have hp'' := hp'.filter_mono (ae_mono (Measure.restrict_le_self (s := A)))
  filter_upwards [boundaryRestrict_coe_ae A (diskProfile u t),
    boundaryRestrict_coe_ae A (closedAnnulusProfile hh t), hv, ht', hp'',
    ae_restrict_mem hA] with w h1 h2 hvw htw hpw hw
  change (boundaryRestrict A (diskProfile u t) : Circle₁ → ℂ) w =
    (boundaryRestrict A (closedAnnulusProfile hh t) : Circle₁ → ℂ) w
  change (diskProfile u t : Circle₁ → ℂ) w = valueCLM u (t • (w : ℂ)) at htw
  rw [h1, h2, hvw, htw]
  exact hpw ⟨t, htI, w, hw, rfl⟩

end KsIndex.Trace
