module

public import KsIndexLean.KarcherQuotientArea
public import KsIndexLean.KarcherInfinity
public import KsIndexLean.SphericalInversionMeasure
public import KsIndexLean.KarcherEnergyIntegrability
public import Mathlib.MeasureTheory.Function.Jacobian

@[expose] public section


/-! The EW area density transforms correctly under the inversion used to
join adjacent disk copies. The determinant is the actual real derivative
of circle inversion, including its orientation reversal. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KsIndex.KarcherData

lemma rho_conj (k : ℕ) (z : ℂ) : Surface.rho k ((starRingEnd ℂ) z) = Surface.rho k z := by
  have he : ((starRingEnd ℂ) z) ^ (2*k) + 1 = (starRingEnd ℂ) (z ^ (2*k) + 1) := by simp
  simp only [Surface.rho, Complex.norm_conj, he]

lemma rho_inv {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ≠ 0)
    (hp : z ∉ Surface.punctures k) : Surface.rho k z⁻¹ = ‖z‖ ^ 2 * Surface.rho k z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hden : ‖z ^ (2*k) + 1‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro he
    apply hp
    exact eq_neg_of_add_eq_zero_left he
  have he : z⁻¹ ^ (2*k) + 1 = (z ^ (2*k) + 1) / z ^ (2*k) := by
    rw [inv_pow]
    field_simp
    ring
  unfold Surface.rho
  rw [he, norm_div, norm_pow]
  simp only [norm_inv, inv_pow]
  rw [pow_sub₀ ‖z‖ hn (by omega : 2 ≤ 2*k)]
  field_simp
  ring

lemma rho_sigma {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ≠ 0)
    (hp : z ∉ Surface.punctures k) : Surface.rho k (Bracket.σ z) = ‖z‖ ^ 2 * Surface.rho k z := by
  have he : Bracket.σ z = (starRingEnd ℂ) z⁻¹ := by simp [Bracket.σ]
  rw [he, rho_conj, rho_inv hk hz hp]

lemma ewAreaDensity_sigma_jacobian {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ≠ 0)
    (hp : z ∉ Surface.punctures k) :
    |(fderiv ℝ Bracket.σ z).toLinearMap.det| * Surface.rho k (Bracket.σ z) ^ 2 =
      Surface.rho k z ^ 2 := by
  rw [Spherical.abs_det_sigma hz, rho_sigma hk hz hp]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  field_simp

/-- Change of variables for the EW area density across circle inversion. -/
theorem lintegral_ew_weight_sigma {k : ℕ} (hk : 2 ≤ k) (F : ℂ → ℝ≥0∞) :
    ∫⁻ z, ENNReal.ofReal (Surface.rho k z ^ 2) * F z ∂volume =
      ∫⁻ z, ENNReal.ofReal (Surface.rho k z ^ 2) * F (Bracket.σ z) ∂volume := by
  have hd : ∀ z ∈ ({0}ᶜ : Set ℂ),
      HasFDerivWithinAt Bracket.σ (fderiv ℝ Bracket.σ z) ({0}ᶜ : Set ℂ) z := by
    intro z hz
    exact (SigmaDeriv.hasFDerivAt_sigmaR (by simpa using hz)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn Bracket.σ ({0}ᶜ : Set ℂ) :=
    (Function.LeftInverse.injective Bracket.σ_σ).injOn
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (measurableSet_singleton (0 : ℂ)).compl hd hinj
    (fun z => ENNReal.ofReal (Surface.rho k z ^ 2) * F z)
  rw [Spherical.sigma_image_nonzero] at h
  simp only [restrict_compl_singleton] at h
  refine h.trans ?_
  apply lintegral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℂ), ae_norm_ne_one] with z hz hn
  have hp : z ∉ Surface.punctures k := fun hp => hn (puncture_norm hk hp)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _),
    ewAreaDensity_sigma_jacobian hk hz hp]

/-- Inversion preserves EW area, including neighborhoods crossing the disk boundary. -/
theorem map_ewAreaMeasure_sigma {k : ℕ} (hk : 2 ≤ k) :
    Measure.map Bracket.σ (ewAreaMeasure k) = ewAreaMeasure k := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF Spherical.measurable_sigma]
  rw [lintegral_ewAreaMeasure (F := fun z => F (Bracket.σ z)) (hF.comp Spherical.measurable_sigma),
    lintegral_ewAreaMeasure hF]
  exact (lintegral_ew_weight_sigma hk F).symm

/-- Restricted change of variables; useful on chart neighborhoods. -/
lemma map_ewAreaMeasure_sigma_restrict {k : ℕ} (hk : 2 ≤ k)
    {S : Set ℂ} (hS : MeasurableSet S) :
    Measure.map Bracket.σ ((ewAreaMeasure k).restrict (Bracket.σ ⁻¹' S)) =
      (ewAreaMeasure k).restrict S := by
  rw [← Measure.restrict_map Spherical.measurable_sigma hS, map_ewAreaMeasure_sigma hk]

/-- A disk copy reflected into the exterior carries the same EW area density.
The disk center is sent to infinity geometrically; its totalized planar value
at zero is harmless because that singleton has zero area. -/
lemma map_ewAreaMeasure_sigma_disk {k : ℕ} (hk : 2 ≤ k) :
    Measure.map Bracket.σ ((ewAreaMeasure k).restrict Surface.disk) =
      (ewAreaMeasure k).restrict {z : ℂ | 1 < ‖z‖} := by
  have hz : ∀ᵐ z : ℂ ∂ewAreaMeasure k, z ≠ 0 :=
    by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_eq_eq_singleton, ewAreaMeasure] using
        (withDensity_absolutelyContinuous volume
          (fun z : ℂ => ENNReal.ofReal (Surface.rho k z ^ 2)) (measure_singleton (0 : ℂ)))
  have he : Surface.disk =ᵐ[ewAreaMeasure k] Bracket.σ ⁻¹' {z : ℂ | 1 < ‖z‖} := by
    filter_upwards [hz] with z hz
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, SurfaceForm.mem_disk_iff, Bracket.norm_σ]
    exact propext ((one_lt_inv₀ (norm_pos_iff.mpr hz)).symm)
  rw [Measure.restrict_congr_set he]
  exact map_ewAreaMeasure_sigma_restrict hk (isOpen_lt continuous_const continuous_norm).measurableSet

/-- Conjugation preserves EW area; this is the coordinate change at an odd
copy's infinity center. -/
lemma map_ewAreaMeasure_conj (k : ℕ) :
    Measure.map (starRingEnd ℂ) (ewAreaMeasure k) = ewAreaMeasure k := by
  have hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume :=
    Complex.conjLIE.measurePreserving
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hc.measurable,
    lintegral_ewAreaMeasure (F := fun z => F ((starRingEnd ℂ) z)) (hF.comp hc.measurable),
    lintegral_ewAreaMeasure hF]
  have he := hc.lintegral_comp (((measurable_rho k).pow_const 2).ennreal_ofReal.mul hF)
  simpa only [Pi.mul_apply, rho_conj] using he

lemma map_ewAreaMeasure_conj_disk (k : ℕ) :
    Measure.map (starRingEnd ℂ) ((ewAreaMeasure k).restrict Surface.disk) =
      (ewAreaMeasure k).restrict Surface.disk := by
  have hc : Measurable (starRingEnd ℂ) := Complex.continuous_conj.measurable
  have he : (starRingEnd ℂ) ⁻¹' Surface.disk = Surface.disk := by
    ext z
    simp only [Set.mem_preimage, SurfaceForm.mem_disk_iff, Complex.norm_conj]
  have hs : MeasurableSet Surface.disk := measurableSet_ball
  have hh := Measure.restrict_map (μ := ewAreaMeasure k) hc hs
  rw [he, map_ewAreaMeasure_conj] at hh
  exact hh.symm

end KsIndex.KarcherData
