module

public import KsIndexLean.CompactPolarJacobi

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma integral_real_weight_conj {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (q : α → ℝ) (f : α → ℂ) (C : ℂ) :
    (∫ x, q x • (C * (starRingEnd ℂ) (f x)) ∂μ) =
      C * (starRingEnd ℂ) (∫ x, q x • f x ∂μ) := by
  rw [← integral_conj, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  ring

/-- The mode equation with geometric normalization and conjugation cancelled.
The three integrals remain separate so no integrability assumption is hidden
in an algebraic integral rewrite. -/
lemma surfaceJacobi_weak_mode_equation_normalized {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (k : ℕ) (n : ℤ) (u : ComplexH1)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v = 0) :
    ((∫ r in Ioo a b, (r * deriv χ r : ℝ) • interiorDiskRadialMode a b u n r) +
      ∫ r in Ioo a b, ((n : ℝ)^2 * χ r / r) • interiorDiskMode hab u n r) -
      (∫ r in Ioo a b, (r * (χ r * KsIndex.Radial.Vrad k r)) • interiorDiskMode hab u n r) = 0 := by
  have h := surfaceJacobi_weak_mode_equation ha hab hb hχ hc hs k n u hu
  have hmid : (∫ r in Ioo a b, (χ r / r : ℝ) •
      (((2 * Real.pi : ℝ) : ℂ) * (n : ℂ)^2 *
        (starRingEnd ℂ) (interiorDiskMode hab u n r))) =
      ∫ r in Ioo a b, ((n : ℝ)^2 * χ r / r) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskMode hab u n r)) := by
    apply integral_congr_ae
    filter_upwards [] with r
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_intCast]
    ring
  rw [hmid, integral_real_weight_conj, integral_real_weight_conj, integral_real_weight_conj] at h
  have hC : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have he : ((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ)
      (((∫ r in Ioo a b, (r * deriv χ r : ℝ) • interiorDiskRadialMode a b u n r) +
        ∫ r in Ioo a b, ((n : ℝ)^2 * χ r / r) • interiorDiskMode hab u n r) -
        (∫ r in Ioo a b, (r * (χ r * KsIndex.Radial.Vrad k r)) • interiorDiskMode hab u n r)) = 0 := by
    simpa only [map_sub, map_add, mul_sub, mul_add] using h
  have hz := (mul_eq_zero.mp he).resolve_left hC
  exact (starRingEnd ℂ).injective (hz.trans (map_zero (starRingEnd ℂ)).symm)

lemma interiorDiskRadialMode_intervalIntegrable {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) (n : ℤ) :
    IntervalIntegrable (interiorDiskRadialMode a b u n) volume a b :=
  ⟨(circleCoefficientCLM n).integrable_comp (interiorDisk_weak_polar ha hab hb u).2.1.1,
    (circleCoefficientCLM n).integrable_comp (interiorDisk_weak_polar ha hab hb u).2.1.2⟩

def interiorDiskModeRHS {a b : ℝ} (hab : a < b) (k : ℕ) (u : ComplexH1) (n : ℤ)
    (r : ℝ) : ℂ :=
  ((n : ℝ)^2 / r - r * KsIndex.Radial.Vrad k r) • interiorDiskMode hab u n r

lemma interiorDiskModeRHS_continuousOn {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (u : ComplexH1) (n : ℤ) :
    ContinuousOn (interiorDiskModeRHS hab k u n) (Icc a b) := by
  have hw : ContinuousOn (fun r : ℝ => (n : ℝ)^2 / r - r * KsIndex.Radial.Vrad k r) (Icc a b) :=
    (continuousOn_const.div continuousOn_id (fun r hr => (ha.trans_le hr.1).ne')).sub
      (continuousOn_id.mul (KsIndex.Radial.continuous_Vrad k).continuousOn)
  exact hw.smul (interiorDiskMode_continuousOn ha hab hb u n)

/-- The radial flux of a weak solution has the expected weak derivative.
This is the distributional radial Jacobi equation, without a centre assumption. -/
lemma surfaceJacobi_radial_flux_weak_deriv {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (n : ℤ) (u : ComplexH1)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v = 0) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (fun r => r • interiorDiskRadialMode a b u n r) (interiorDiskModeRHS hab k u n) 1 := by
  have hfc := interiorDiskMode_continuousOn ha hab hb u n
  have hRc := interiorDiskModeRHS_continuousOn ha hab hb k u n
  have hg := interiorDiskRadialMode_intervalIntegrable ha hab hb u n
  have hflux := hg.continuousOn_smul (continuous_id.continuousOn : ContinuousOn (fun r : ℝ => r) (uIcc a b))
  have hloc := ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mp hflux).locallyIntegrableOn
  have hRloc : LocallyIntegrableOn (interiorDiskModeRHS hab k u n) (Ioo a b) volume := (hRc.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo
  rw [TauCeti.hasWeakLineDerivOn_iff hloc hRloc]
  intro χ hχ hc hs
  have hs' : tsupport χ ⊆ Ioo a b := hs
  have heq := surfaceJacobi_weak_mode_equation_normalized ha hab hb hχ hc hs' k n u hu
  have hcA : ContinuousOn (fun r => ((n : ℝ)^2 * χ r / r) • interiorDiskMode hab u n r)
      (Icc a b) := by
    have hw : ContinuousOn (fun r : ℝ => (n : ℝ)^2 * χ r / r) (Icc a b) :=
      (continuousOn_const.mul hχ.continuous.continuousOn).div continuousOn_id
        (fun r hr => (ha.trans_le hr.1).ne')
    exact hw.smul hfc
  have hcB : ContinuousOn (fun r => (r * (χ r * KsIndex.Radial.Vrad k r)) •
      interiorDiskMode hab u n r) (Icc a b) :=
    (continuousOn_id.mul (hχ.continuous.continuousOn.mul
      (KsIndex.Radial.continuous_Vrad k).continuousOn)).smul hfc
  have hiA : IntegrableOn (fun r => ((n : ℝ)^2 * χ r / r) • interiorDiskMode hab u n r) (Ioo a b) volume := (hcA.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hiB : IntegrableOn (fun r => (r * (χ r * KsIndex.Radial.Vrad k r)) • interiorDiskMode hab u n r) (Ioo a b) volume := (hcB.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hR : (∫ r in Ioo a b, χ r • interiorDiskModeRHS hab k u n r) =
      (∫ r in Ioo a b, ((n : ℝ)^2 * χ r / r) • interiorDiskMode hab u n r) -
      ∫ r in Ioo a b, (r * (χ r * KsIndex.Radial.Vrad k r)) • interiorDiskMode hab u n r := by
    rw [← integral_sub hiA hiB]
    apply integral_congr_ae
    filter_upwards [] with r
    simp only [interiorDiskModeRHS, smul_smul, ← sub_smul]
    congr 1
    ring
  have hl : (∫ r, lineDeriv ℝ χ r 1 • (r • interiorDiskRadialMode a b u n r)) =
      ∫ r in Ioo a b, (r * deriv χ r) • interiorDiskRadialMode a b u n r := by
    simp_rw [lineDeriv_one_eq_deriv, smul_smul]
    have hp : (fun r => (deriv χ r * r) • interiorDiskRadialMode a b u n r) =
        (fun r => (r * deriv χ r) • interiorDiskRadialMode a b u n r) := by
      funext r; rw [mul_comm]
    rw [hp]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    rw [deriv_eq_zero_of_notMem_tsupport (fun hm => hr (hs' hm)), mul_zero, zero_smul]
  have hr : (∫ r, χ r • interiorDiskModeRHS hab k u n r) =
      ∫ r in Ioo a b, χ r • interiorDiskModeRHS hab k u n r := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    rw [image_eq_zero_of_notMem_tsupport (fun hm => hr (hs' hm)), zero_smul]
  rw [hl, hr, hR]
  linear_combination heq

end KsIndex.Trace
