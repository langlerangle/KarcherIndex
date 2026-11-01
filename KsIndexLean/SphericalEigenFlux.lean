module

public import KsIndexLean.SphericalEigenRadial
public import KsIndexLean.InteriorModeRegularity

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

def eigenDiskModeRHS {a b : ℝ} (hab : a < b) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (r : ℝ) : ℂ :=
  ((n : ℝ)^2 / r - r * sphericalEigenRadialCoefficient k lam r) • interiorDiskMode hab u n r

lemma eigenDiskModeRHS_continuousOn {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ) :
    ContinuousOn (eigenDiskModeRHS hab k lam u n) (Icc a b) := by
  have hw : ContinuousOn (fun r : ℝ => (n : ℝ)^2 / r - r * sphericalEigenRadialCoefficient k lam r) (Icc a b) :=
    (continuousOn_const.div continuousOn_id (fun r hr => (ha.trans_le hr.1).ne')).sub
      (continuousOn_id.mul (sphericalEigenRadialCoefficient_smooth k lam).continuous.continuousOn)
  exact hw.smul (interiorDiskMode_continuousOn ha hab hb u n)

/-- The radial flux of a weak solution has the expected weak derivative.
This is the distributional radial Jacobi equation, without a centre assumption. -/
lemma sphericalEigen_radial_flux_weak_deriv {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (lam : ℝ) (n : ℤ) (u : ComplexH1)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (fun r => r • interiorDiskRadialMode a b u n r) (eigenDiskModeRHS hab k lam u n) 1 := by
  have hfc := interiorDiskMode_continuousOn ha hab hb u n
  have hRc := eigenDiskModeRHS_continuousOn ha hab hb k lam u n
  have hg := interiorDiskRadialMode_intervalIntegrable ha hab hb u n
  have hflux := hg.continuousOn_smul (continuous_id.continuousOn : ContinuousOn (fun r : ℝ => r) (uIcc a b))
  have hloc := ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mp hflux).locallyIntegrableOn
  have hRloc : LocallyIntegrableOn (eigenDiskModeRHS hab k lam u n) (Ioo a b) volume := (hRc.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo
  rw [TauCeti.hasWeakLineDerivOn_iff hloc hRloc]
  intro χ hχ hc hs
  have hs' : tsupport χ ⊆ Ioo a b := hs
  have heq := sphericalEigen_weak_mode_equation ha hab hb hχ hc hs' k lam n u hu
  have hcA : ContinuousOn (fun r => ((n : ℝ)^2 * χ r / r) • interiorDiskMode hab u n r)
      (Icc a b) := by
    have hw : ContinuousOn (fun r : ℝ => (n : ℝ)^2 * χ r / r) (Icc a b) :=
      (continuousOn_const.mul hχ.continuous.continuousOn).div continuousOn_id
        (fun r hr => (ha.trans_le hr.1).ne')
    exact hw.smul hfc
  have hcB : ContinuousOn (fun r => (r * (χ r * sphericalEigenRadialCoefficient k lam r)) •
      interiorDiskMode hab u n r) (Icc a b) :=
    (continuousOn_id.mul (hχ.continuous.continuousOn.mul
      (sphericalEigenRadialCoefficient_smooth k lam).continuous.continuousOn)).smul hfc
  have hiA : IntegrableOn (fun r => ((n : ℝ)^2 * χ r / r) • interiorDiskMode hab u n r) (Ioo a b) volume := (hcA.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hiB : IntegrableOn (fun r => (r * (χ r * sphericalEigenRadialCoefficient k lam r)) • interiorDiskMode hab u n r) (Ioo a b) volume := (hcB.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hR : (∫ r in Ioo a b, χ r • eigenDiskModeRHS hab k lam u n r) =
      (∫ r in Ioo a b, ((n : ℝ)^2 * χ r / r) • interiorDiskMode hab u n r) -
      ∫ r in Ioo a b, (r * (χ r * sphericalEigenRadialCoefficient k lam r)) • interiorDiskMode hab u n r := by
    rw [← integral_sub hiA hiB]
    apply integral_congr_ae
    filter_upwards [] with r
    simp only [eigenDiskModeRHS, smul_smul, ← sub_smul]
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
  have hr : (∫ r, χ r • eigenDiskModeRHS hab k lam u n r) =
      ∫ r in Ioo a b, χ r • eigenDiskModeRHS hab k lam u n r := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    rw [image_eq_zero_of_notMem_tsupport (fun hm => hr (hs' hm)), zero_smul]
  rw [hl, hr, hR]
  linear_combination heq


end KsIndex.Trace
