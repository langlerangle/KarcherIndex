module

public import KsIndexLean.IntervalGluing
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Function.Jacobian

@[expose] public section


open Set MeasureTheory intervalIntegral

noncomputable section
namespace KsIndex.Trace

lemma inv_mem_inner_collar {r : ℝ} (hr : r ∈ Icc 1 2) :
    r⁻¹ ∈ Icc (1 / 2 : ℝ) 1 := by
  constructor
  · simpa only [one_div] using one_div_le_one_div_of_le (by linarith [hr.1]) hr.2
  · simpa using (one_div_le_one_div_of_le (by linarith [hr.1]) hr.1)

lemma inv_continuous_outer {r : ℝ} (hr : 1 ≤ r) :
    ContinuousOn (fun t : ℝ => t⁻¹) (uIcc 1 r) := by
  rw [uIcc_of_le hr]
  exact continuousOn_id.inv₀ (fun t ht => ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1))

lemma inv_mem_inner_collar_open {r : ℝ} (hr : r ∈ Ioo 1 2) :
    r⁻¹ ∈ Ioo (1 / 2 : ℝ) 1 := by
  constructor
  · simpa only [one_div] using one_div_lt_one_div_of_lt (by linarith [hr.1]) hr.2
  · simpa using (one_div_lt_one_div_of_lt (by norm_num) hr.1)

/-- A.e. representatives may be pulled back through inversion: the exceptional set
is the inversion image of a null set away from zero. -/
lemma ae_eq_comp_inv_collar {F : Type*} {f p : ℝ → F}
    (h : f =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 1)] p) :
    (fun r => f r⁻¹) =ᵐ[volume.restrict (Ioo (1 : ℝ) 2)] (fun r => p r⁻¹) := by
  let S := {t : ℝ | t ∈ Ioo (1 / 2 : ℝ) 1 ∧ f t ≠ p t}
  have hS : volume S = 0 := by
    have ha := (ae_restrict_iff' measurableSet_Ioo).mp h
    simpa only [ae_iff, not_imp, S] using ha
  have hd : DifferentiableOn ℝ (fun t : ℝ => t⁻¹) S := by
    intro t ht
    exact (hasDerivAt_inv (by have := ht.1.1; linarith)).differentiableAt.differentiableWithinAt
  have hi := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd hS
  have ha : ∀ᵐ r ∂volume, r ∉ (fun t : ℝ => t⁻¹) '' S := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using hi
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [ha] with r hr
  intro hro
  by_contra hn
  exact hr ⟨r⁻¹, ⟨inv_mem_inner_collar_open hro, hn⟩, inv_inv r⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Radial chain-rule factor for the actual inversion, including orientation reversal. -/
def invertedRadialDeriv (g : ℝ → E) (r : ℝ) : E := -(r ^ 2)⁻¹ • g r⁻¹

omit [CompleteSpace E] in
lemma integral_invertedRadialDeriv (g : ℝ → E) {r : ℝ} (hr : 1 ≤ r) :
    (∫ t in 1..r, invertedRadialDeriv g t) = ∫ t in 1..r⁻¹, g t := by
  simpa only [invertedRadialDeriv, Function.comp_apply, inv_one] using
    integral_deriv_smul_comp_of_deriv_nonpos (g := g) (inv_continuous_outer hr)
      (fun t ht => hasDerivAt_inv (by
        have h : 1 < t := by simpa [min_eq_left hr, max_eq_right hr] using ht.1
        linarith))
      (fun t _ => neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg t)))

omit [CompleteSpace E] in
lemma invertedRadialDeriv_integrable {g : ℝ → E}
    (hg : IntervalIntegrable g volume (1 / 2) 1) :
    IntervalIntegrable (invertedRadialDeriv g) volume 1 2 := by
  have h := integrable_deriv_smul_comp_iff_of_deriv_nonpos (g := g)
    (inv_continuous_outer (by norm_num : (1 : ℝ) ≤ 2))
    (fun t ht => hasDerivAt_inv (by
      have h : (1 : ℝ) < t := by norm_num at ht ⊢; exact ht.1
      linarith))
    (fun t _ => neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg t)))
  exact h.mpr (by simpa using hg.symm)

/-- Reflect the continuous representative, before passing back to arbitrary a.e. values. -/
def invertedRepresentative (f g : ℝ → E) (r : ℝ) : E :=
  representative (by norm_num : (1 / 2 : ℝ) < 1) f g r⁻¹

omit [CompleteSpace E] in
lemma invertedRepresentative_continuousOn (f : ℝ → E) {g : ℝ → E}
    (hg : IntervalIntegrable g volume (1 / 2) 1) :
    ContinuousOn (invertedRepresentative f g) (Icc 1 2) := by
  exact (representative_continuousOn (by norm_num) f hg).comp
    (by simpa using inv_continuous_outer (by norm_num : (1 : ℝ) ≤ 2))
    (fun _ ht => inv_mem_inner_collar ht)

omit [CompleteSpace E] in
lemma invertedRepresentative_primitive (f : ℝ → E) {g : ℝ → E}
    (hg : IntervalIntegrable g volume (1 / 2) 1) {r : ℝ} (hr : r ∈ Icc 1 2) :
    invertedRepresentative f g r = invertedRepresentative f g 1 +
      primitiveFun 1 (invertedRadialDeriv g) r := by
  have h := representative_sub_eq_integral (by norm_num : (1 / 2 : ℝ) < 1)
    f hg (by norm_num : (1 : ℝ) ∈ Icc (1 / 2) 1) (inv_mem_inner_collar hr)
  simp only [invertedRepresentative, inv_one, primitiveFun,
    integral_invertedRadialDeriv g hr.1]
  rw [← h]
  abel

lemma invertedRepresentative_weak (f : ℝ → E) {g : ℝ → E}
    (hg : IntervalIntegrable g volume (1 / 2) 1) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens 1 2)
      (invertedRepresentative f g) (invertedRadialDeriv g) 1 := by
  have hc := TauCeti.hasWeakLineDerivOn_const (μ := volume)
    (Ω := intervalOpens 1 2) (v := 1) (invertedRepresentative f g 1)
  change TauCeti.HasWeakLineDerivOn volume (intervalOpens 1 2)
    (fun _ => invertedRepresentative f g 1) (0 : ℝ → E) 1 at hc
  have hp := hc.add (primitive_weak_deriv (by norm_num : (1 : ℝ) < 2)
    (invertedRadialDeriv_integrable hg))
  simp only [zero_add] at hp
  apply hp.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact (invertedRepresentative_primitive f hg ⟨hr.1.le, hr.2.le⟩).symm

lemma invertedProfile_weak {f g : ℝ → E}
    (hf : TauCeti.HasWeakLineDerivOn volume (intervalOpens (1 / 2) 1) f g 1)
    (hg : IntervalIntegrable g volume (1 / 2) 1) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens 1 2)
      (fun r => f r⁻¹) (invertedRadialDeriv g) 1 := by
  exact (invertedRepresentative_weak f hg).congr_ae
    (ae_eq_comp_inv_collar (representative_ae_eq (by norm_num) hf hg)).symm

lemma invertedProfile_integrable {f g : ℝ → E}
    (hf : TauCeti.HasWeakLineDerivOn volume (intervalOpens (1 / 2) 1) f g 1)
    (hg : IntervalIntegrable g volume (1 / 2) 1) :
    IntervalIntegrable (fun r => f r⁻¹) volume 1 2 := by
  have hi := (invertedRepresentative_continuousOn f hg).intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (1 : ℝ) ≤ 2)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hi ⊢
  exact hi.congr (ae_eq_comp_inv_collar
    (representative_ae_eq (by norm_num) hf hg)).symm

lemma invertedProfile_endpoint {f g : ℝ → E}
    (hf : TauCeti.HasWeakLineDerivOn volume (intervalOpens (1 / 2) 1) f g 1)
    (hg : IntervalIntegrable g volume (1 / 2) 1) :
    representative (by norm_num : (1 : ℝ) < 2)
      (fun r => f r⁻¹) (invertedRadialDeriv g) 1 =
        representative (by norm_num : (1 / 2 : ℝ) < 1) f g 1 := by
  have h := representative_unique (by norm_num) (invertedProfile_weak hf hg)
    (invertedRadialDeriv_integrable hg) (invertedRepresentative_continuousOn f hg)
    (ae_eq_comp_inv_collar (representative_ae_eq (by norm_num) hf hg)).symm
    (by norm_num : (1 : ℝ) ∈ Icc 1 2)
  simpa only [invertedRepresentative, inv_one] using h.symm

end KsIndex.Trace
