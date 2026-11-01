module

public import KsIndexLean.SphericalEigenBoundaryEquation
public import KsIndexLean.SphericalEigenRadialGreen

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

lemma sphericalEigen_green_eq_mode_integrals {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    (∫ r in a..1, (deriv χ r) • eigenDiskFluxRepresentative ha1 k lam u n r +
      χ r • eigenDiskModeRHS ha1 k lam u n r) =
      ((∫ r in Ioo a 1, (r * deriv χ r : ℝ) • interiorDiskRadialMode a 1 u n r) +
        ∫ r in Ioo a 1, ((n : ℝ)^2 * χ r / r) • interiorDiskMode ha1 u n r) -
        ∫ r in Ioo a 1, (r * (χ r * sphericalEigenRadialCoefficient k lam r)) •
          interiorDiskMode ha1 u n r := by
  have hm := interiorDiskMode_continuousOn ha ha1 le_rfl u n
  have hf := eigenDiskFluxRepresentative_continuousOn ha ha1 le_rfl k lam u n
  have hA : IntegrableOn (fun r => deriv χ r • eigenDiskFluxRepresentative ha1 k lam u n r)
      (Ioo a 1) volume :=
    ((hχ.continuous_deriv (by simp)).continuousOn.smul hf).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hB : IntegrableOn (fun r => ((n : ℝ)^2 * χ r / r) • interiorDiskMode ha1 u n r)
      (Ioo a 1) volume :=
    (((continuousOn_const.mul hχ.continuous.continuousOn).div continuousOn_id
      (fun r hr => (ha.trans_le hr.1).ne')).smul hm).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hC : IntegrableOn (fun r => (r * (χ r * sphericalEigenRadialCoefficient k lam r)) •
      interiorDiskMode ha1 u n r) (Ioo a 1) volume :=
    ((continuousOn_id.mul (hχ.continuous.continuousOn.mul
      (sphericalEigenRadialCoefficient_smooth k lam).continuous.continuousOn)).smul hm).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [intervalIntegral.integral_of_le ha1.le, integral_Ioc_eq_integral_Ioo]
  calc
    _ = ∫ r in Ioo a 1, (deriv χ r • eigenDiskFluxRepresentative ha1 k lam u n r +
        ((n : ℝ)^2 * χ r / r) • interiorDiskMode ha1 u n r) -
        (r * (χ r * sphericalEigenRadialCoefficient k lam r)) • interiorDiskMode ha1 u n r := by
      apply integral_congr_ae
      filter_upwards [] with r
      simp only [eigenDiskModeRHS, Complex.real_smul, Complex.ofReal_sub,
        Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow]
      ring
    _ = _ := by
      have hAB : IntegrableOn (fun r => deriv χ r • eigenDiskFluxRepresentative ha1 k lam u n r +
          ((n : ℝ)^2 * χ r / r) • interiorDiskMode ha1 u n r) (Ioo a 1) volume := hA.add hB
      rw [integral_sub hAB hC, integral_add hA hB]
      congr 2
      apply integral_congr_ae
      filter_upwards [eigenDiskClassicalDerivative_ae ha ha1 le_rfl k lam u n hu,
        ae_restrict_mem measurableSet_Ioo] with r he hr
      rw [he]
      simp only [eigenDiskClassicalDerivative, smul_smul]
      congr 1
      field_simp [(ha.trans hr.1).ne']

lemma sphericalEigen_neumann_flux_zero_of_cutoff {a c : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (hχ1 : χ 1 = 1) :
    eigenDiskNormalMode k lam u n = 0 := by
  have hχa : χ a = 0 := image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl a) (hs h).1)
  rw [sphericalEigen_normalMode_eq_green ha ha1 k lam u n (fun v _ => hu v) hχ hχa hχ1,
    sphericalEigen_green_eq_mode_integrals ha ha1 k lam u n (fun v _ => hu v) hχ]
  exact sphericalEigen_boundary_mode_equation ha ha1 hχ hc hs k lam n u hu

/-- Full Neumann weak testing forces every canonical normal Fourier coefficient
 to vanish, at arbitrary real eigenvalue. -/
theorem sphericalEigen_neumann_flux_zero (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    eigenDiskNormalMode k lam u n = 0 := by
  let χ : ContDiffBump (1 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  apply sphericalEigen_neumann_flux_zero_of_cutoff
    (a := 1 / 2) (c := 2) (by norm_num) (by norm_num) k lam u n hu
    χ.contDiff χ.hasCompactSupport
  · rw [χ.tsupport_eq]
    intro r hr
    have h : |r - 1| ≤ (1 / 4 : ℝ) := by
      simpa only [Metric.mem_closedBall, Real.dist_eq] using hr
    have hh := abs_le.mp h
    constructor <;> linarith [hh.1, hh.2]
  · exact χ.one_of_mem_closedBall (by simp [χ])

/-- A full Neumann eigenfunction with zero Dirichlet trace is zero. -/
theorem sphericalEigen_neumann_zeroTrace_eq_zero (k : ℕ) (lam : ℝ) (u : ComplexH1)
    (hu : ∀ v : ComplexH1, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (ht : diskTraceCLM u = 0) : u = 0 :=
  sphericalEigen_eq_zero_of_boundary_cauchy k lam u (fun v _ => hu v) ht
    (fun n => sphericalEigen_neumann_flux_zero k lam u n hu)

end KsIndex.Trace
