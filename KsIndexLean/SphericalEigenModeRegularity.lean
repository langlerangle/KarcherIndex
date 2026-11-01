module

public import KsIndexLean.SphericalEigenFlux

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

def eigenDiskFluxRepresentative {a b : ℝ} (hab : a < b) (k : ℕ) (lam : ℝ)
    (u : ComplexH1) (n : ℤ) : ℝ → ℂ :=
  representative hab (fun r => r • interiorDiskRadialMode a b u n r)
    (eigenDiskModeRHS hab k lam u n)

def eigenDiskClassicalDerivative {a b : ℝ} (hab : a < b) (k : ℕ) (lam : ℝ)
    (u : ComplexH1) (n : ℤ) (r : ℝ) : ℂ :=
  r⁻¹ • eigenDiskFluxRepresentative hab k lam u n r

lemma eigenDiskFluxRepresentative_continuousOn {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ) :
    ContinuousOn (eigenDiskFluxRepresentative hab k lam u n) (Icc a b) := by
  apply representative_continuousOn hab
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le hab.le] using eigenDiskModeRHS_continuousOn ha hab hb k lam u n

lemma eigenDiskFluxRepresentative_hasDerivAt {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    {r : ℝ} (hr : r ∈ Ioo a b) :
    HasDerivAt (eigenDiskFluxRepresentative hab k lam u n) (eigenDiskModeRHS hab k lam u n r) r :=
  representative_hasDerivAt_of_continuousOn hab _
    (eigenDiskModeRHS_continuousOn ha hab hb k lam u n) hr

lemma eigenDiskClassicalDerivative_continuousOn {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ) :
    ContinuousOn (eigenDiskClassicalDerivative hab k lam u n) (Icc a b) := by
  have hi : ContinuousOn (fun r : ℝ => r⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun r hr => (ha.trans_le hr.1).ne')
  exact hi.smul (eigenDiskFluxRepresentative_continuousOn ha hab hb k lam u n)

lemma eigenDiskClassicalDerivative_ae {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    interiorDiskRadialMode a b u n =ᵐ[volume.restrict (Ioo a b)]
      eigenDiskClassicalDerivative hab k lam u n := by
  have hi : IntervalIntegrable (eigenDiskModeRHS hab k lam u n) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab.le] using eigenDiskModeRHS_continuousOn ha hab hb k lam u n
  have he := representative_ae_eq hab (sphericalEigen_radial_flux_weak_deriv ha hab hb k lam n u hu) hi
  filter_upwards [he, ae_restrict_mem measurableSet_Ioo] with r hr hrI
  have hr0 := (ha.trans hrI.1).ne'
  change r • interiorDiskRadialMode a b u n r = eigenDiskFluxRepresentative hab k lam u n r at hr
  simp only [eigenDiskClassicalDerivative, ← hr, smul_smul, inv_mul_cancel₀ hr0, one_smul]

/-- Interior classical differentiability follows from the continuous flux
representative and the weak radial fundamental theorem of calculus. -/
lemma eigenDiskMode_hasDerivAt {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    {r : ℝ} (hr : r ∈ Ioo a b) :
    HasDerivAt (interiorDiskMode hab u n) (eigenDiskClassicalDerivative hab k lam u n r) r := by
  let g := eigenDiskClassicalDerivative hab k lam u n
  have hg := eigenDiskClassicalDerivative_continuousOn ha hab hb k lam u n
  have hi : IntervalIntegrable g volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab.le] using hg
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hi.mono_set (by
      rw [uIcc_of_le hr.1.le, uIcc_of_le hab.le]
      exact Icc_subset_Icc le_rfl hr.2.le))
    ((hg.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo r hr)
    (hg.continuousAt (Icc_mem_nhds hr.1 hr.2))
  have hde := hd.const_add (interiorDiskMode hab u n a)
  apply hde.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
  have he := interiorDiskMode_sub_eq_integral ha hab hb u n
    (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩) (Ioo_subset_Icc_self ht)
  have hei : (∫ s in a..t, interiorDiskRadialMode a b u n s) = ∫ s in a..t, g s := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1.le, ← restrict_Ioo_eq_restrict_Ioc]
    exact (eigenDiskClassicalDerivative_ae ha hab hb k lam u n hu).filter_mono
      (ae_mono (Measure.restrict_mono (Ioo_subset_Ioo le_rfl ht.2.le) le_rfl))
  rw [hei] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

lemma eigenDiskMode_classical_flux_hasDerivAt {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    {r : ℝ} (hr : r ∈ Ioo a b) :
    HasDerivAt (fun t => t • eigenDiskClassicalDerivative hab k lam u n t)
      (eigenDiskModeRHS hab k lam u n r) r := by
  apply (eigenDiskFluxRepresentative_hasDerivAt ha hab hb k lam u n hr).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
  simp only [eigenDiskClassicalDerivative, smul_smul,
    mul_inv_cancel₀ (ha.trans ht.1).ne', one_smul]


end KsIndex.Trace
