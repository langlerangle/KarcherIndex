module

public import KsIndexLean.KarcherDiskMeasure

@[expose] public section


/-! # Weighted-coordinate integral identities for the Jacobi form

For `k ≥ 2`, the `ρ_k²` weight in `ewAreaMeasure` cancels the inverse-metric
factor in the Dirichlet density. In the potential term it converts `absA²`
to `potV`. Both identities hold as nonnegative extended integrals over `ℂ`;
they do not require finiteness of the integrals. Punctures form a null set,
so cancellation uses the positive conformal factor away from them.

These are coordinate-measure identities. Identifying them with intrinsic
surface integrals additionally uses the chart and measure compatibility
results for the geometric realization. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace KsIndex.KarcherData
variable {k : ℕ}

/-- The punctures lie on the unit circle (`w^(2k) = -1 ⟹ ‖w‖ = 1`), a measure-zero sphere, so the
puncture set is `volume`-null. -/
lemma volume_punctures_zero (hk : 2 ≤ k) : volume (Surface.punctures k) = 0 := by
  have hsub : Surface.punctures k ⊆ Metric.sphere (0 : ℂ) 1 := by
    intro w hw
    have hw' : w ^ (2 * k) = -1 := hw
    have hn : ‖w‖ ^ (2 * k) = 1 := by rw [← norm_pow, hw']; simp
    have h2k : 2 * k ≠ 0 := by omega
    have hnorm : ‖w‖ = 1 := by
      rcases lt_trichotomy ‖w‖ 1 with h | h | h
      · exact absurd hn (by have := pow_lt_one₀ (norm_nonneg w) h h2k; linarith)
      · exact h
      · exact absurd hn (by have := one_lt_pow₀ h h2k; linarith)
    simpa [Metric.mem_sphere, dist_zero_right] using hnorm
  exact measure_mono_null hsub (Measure.addHaar_sphere volume 0 1)

/-- `gradSq f` is measurable for ANY `f : ℂ → ℂ` — it is built from `fderiv`, which is measurable
unconditionally (`measurable_fderiv_apply_const`). No smoothness needed. -/
lemma measurable_gradSq (f : ℂ → ℂ) : Measurable (fun w => Surface.gradSq f w) := by
  unfold Surface.gradSq
  exact ((measurable_fderiv_apply_const (𝕜 := ℝ) (f := f) (1 : ℂ)).norm.pow_const 2).add
    ((measurable_fderiv_apply_const (𝕜 := ℝ) (f := f) Complex.I).norm.pow_const 2)

/-- **Conformal invariance for the coordinate measure:** the geometric Dirichlet integral
`∫ ρ_k⁻²·gradSq f d(ewAreaMeasure)` equals the flat `∫ gradSq f d(vol)`: the `ρ²` area weight
cancels the inverse-metric factor off the (null) punctures. Holds for ANY `f` (`gradSq`
measurability is unconditional, `measurable_gradSq`). -/
lemma lintegral_ewAreaMeasure_invMetricGradSq (hk : 2 ≤ k) (f : ℂ → ℂ) :
    ∫⁻ w, ENNReal.ofReal ((Surface.rho k w ^ 2)⁻¹ * Surface.gradSq f w) ∂(ewAreaMeasure k)
      = ∫⁻ w, ENNReal.ofReal (Surface.gradSq f w) ∂volume := by
  have hmeas : Measurable
      (fun w => ENNReal.ofReal ((Surface.rho k w ^ 2)⁻¹ * Surface.gradSq f w)) :=
    (((measurable_rho k).pow_const 2).inv.mul (measurable_gradSq f)).ennreal_ofReal
  rw [lintegral_ewAreaMeasure hmeas]
  apply lintegral_congr_ae
  have hpn : ∀ᵐ w ∂(volume : Measure ℂ), w ∉ Surface.punctures k :=
    (ae_iff.mpr (by simpa using volume_punctures_zero hk))
  filter_upwards [hpn] with w hw
  have hpos : (0 : ℝ) < Surface.rho k w ^ 2 := rho_sq_pos hk hw
  rw [← ENNReal.ofReal_mul hpos.le, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]

/-- `|A|_k` is measurable (products/quotients of measurable pieces, including `ρ_k`). -/
lemma measurable_absA (k : ℕ) : Measurable (Surface.absA k) := by
  unfold Surface.absA Surface.rho
  fun_prop

/-- **Potential-term integral identity** for the coordinate measure:
`∫ |A|²·|f|² d(ewAreaMeasure) = ∫ potV·|f|² d(vol)`. Against the geometric area measure the
potential coefficient is `|A|²` (= `absA²`); multiplying by the `ρ²` area weight and passing to
flat measure gives `ρ²·absA² = potV` (`absA_sq_mul_rho_sq`) off the null punctures. -/
lemma lintegral_ewAreaMeasure_potential (hk : 2 ≤ k) (f : ℂ → ℂ)
    (hf : Measurable (fun w => ‖f w‖ ^ 2)) :
    ∫⁻ w, ENNReal.ofReal (Surface.absA k w ^ 2 * ‖f w‖ ^ 2) ∂(ewAreaMeasure k)
      = ∫⁻ w, ENNReal.ofReal (Surface.potV k w * ‖f w‖ ^ 2) ∂volume := by
  have hmeas : Measurable (fun w => ENNReal.ofReal (Surface.absA k w ^ 2 * ‖f w‖ ^ 2)) :=
    (((measurable_absA k).pow_const 2).mul hf).ennreal_ofReal
  rw [lintegral_ewAreaMeasure hmeas]
  apply lintegral_congr_ae
  have hpn : ∀ᵐ w ∂(volume : Measure ℂ), w ∉ Surface.punctures k :=
    ae_iff.mpr (by simpa using volume_punctures_zero hk)
  filter_upwards [hpn] with w hw
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Surface.rho k w ^ 2), ← mul_assoc,
    mul_comm (Surface.rho k w ^ 2) (Surface.absA k w ^ 2),
    KsIndex.JacobiFields.absA_sq_mul_rho_sq hk hw]

end KsIndex.KarcherData
