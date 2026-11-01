module

public import KsIndexLean.WeakSobolevRepresentative
public import KsIndexLean.WeakLocalBootstrap
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

@[expose] public section


/-! Smooth representatives from all-order planar Sobolev regularity.

Polynomial Fourier moments give a single classical smooth representative. Compact
localization connects this to `WeakLocalBootstrap`, and continuous representatives
are then smooth pointwise on the open domain. The local-potential results assume
`LocalMemSobolev` of order one, `LocalPotentialEquation`, and a globally smooth
potential. Applications in surface charts must supply these hypotheses; the
results here concern planar representatives.
-/
noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap BoundedContinuousFunction
namespace KsIndex.Weq
open TemperedDistribution

private lemma inverse_weight_bounds (n : ℕ) (x : ℂ) :
    (1 + ‖x‖ ^ 2) ^ (-(n : ℝ)) ≤ 1 ∧
      ‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-(n : ℝ)) ≤ 1 := by
  have hp : 0 < 1 + ‖x‖ ^ 2 := by positivity
  rw [Real.rpow_neg hp.le, Real.rpow_natCast]
  have hone : 1 ≤ (1 + ‖x‖ ^ 2) ^ n := one_le_pow₀ (by nlinarith)
  constructor
  · exact inv_le_one_of_one_le₀ hone
  · rw [← div_eq_mul_inv, div_le_one (pow_pos hp _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (by nlinarith [sq_nonneg (‖x‖ - 1)]) _

/-- All Sobolev orders give every polynomial moment of the L¹ Fourier representative. -/
theorem fourier_moments_of_all_sobolev {f : 𝓢'(ℂ, ℂ)}
    (hf : ∀ n : ℕ, MemSobolev n 2 f) (v : Lp ℂ 1 (volume : Measure ℂ))
    (hv : 𝓕 f = (v : 𝓢'(ℂ, ℂ))) (n : ℕ) :
    Integrable (fun x : ℂ => ‖x‖ ^ n * ‖v x‖) := by
  have hg : MemSobolev 2 2 (besselPotential ℂ ℂ (2 * (n : ℝ)) f) := by
    rw [memSobolev_besselPotential_iff]
    convert hf (2 * n + 2) using 1
    push_cast
    ring
  obtain ⟨w, hw⟩ := hg.fourier_memL1 (by norm_num [Complex.finrank_real_complex])
  rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply] at hw
  have he : (2 * (n : ℝ)) / 2 = n := by ring
  rw [he] at hw
  let a : ℂ → ℂ := fun x => ((1 + ‖x‖ ^ 2) ^ (-(n : ℝ)) : ℝ)
  have hat : a.HasTemperateGrowth := by dsimp [a]; fun_prop
  have ha : MemLp a ⊤ (volume : Measure ℂ) := by
    apply memLp_top_of_bound hat.1.continuous.aestronglyMeasurable 1
    filter_upwards with x
    dsimp [a]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (inverse_weight_bounds n x).1
  have hdist : ((ha.toLp a) • w : Lp ℂ 1 (volume : Measure ℂ)) =
      (v : 𝓢'(ℂ, ℂ)) := by
    rw [Lp.toTemperedDistribution_smul_eq hat ha, ← hw,
      smulLeftCLM_smulLeftCLM_apply (by fun_prop) hat]
    have hprod : ((fun x : ℂ => (((1 + ‖x‖ ^ 2) ^ (n : ℝ) : ℝ) : ℂ)) * a) =
        fun _ => (1 : ℂ) := by
      ext x
      simp only [Pi.mul_apply, a, ← Complex.ofReal_mul]
      rw [← Real.rpow_add (by positivity)]
      simp
    rw [hprod]
    simpa using hv
  have hinj := LinearMap.ker_eq_bot.mp
    (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := (volume : Measure ℂ)) (p := 1))
  have hlp : ((ha.toLp a) • w : Lp ℂ 1 (volume : Measure ℂ)) = v := hinj hdist
  have hae : (fun x => v x) =ᵐ[volume] fun x => a x * w x := by
    have hh := Lp.coeFn_lpSMul (r := (1 : ENNReal)) (ha.toLp a) w
    rw [hlp] at hh
    filter_upwards [hh, ha.coeFn_toLp] with x hx hax
    simpa [hax, smul_eq_mul] using hx
  apply (L1.integrable_coeFn w).norm.mono'
    ((continuous_norm.pow n).aestronglyMeasurable.mul (Lp.memLp v).aestronglyMeasurable.norm)
  filter_upwards [hae] with x hx
  change ‖‖x‖ ^ n * ‖v x‖‖ ≤ ‖w x‖
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hx, norm_mul]
  dsimp [a]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-(n : ℝ)))]
  calc ‖x‖ ^ n * ((1 + ‖x‖ ^ 2) ^ (-(n : ℝ)) * ‖w x‖) =
      (‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-(n : ℝ))) * ‖w x‖ := by ring
    _ ≤ 1 * ‖w x‖ := mul_le_mul_of_nonneg_right (inverse_weight_bounds n x).2 (norm_nonneg _)
    _ = ‖w x‖ := one_mul _

/-- One bounded smooth representative, simultaneously valid at every derivative order. -/
theorem exists_smooth_ae_eq_of_all_sobolev
    (u : Lp ℂ 2 (volume : Measure ℂ))
    (hu : ∀ n : ℕ, MemSobolev n 2 (u : 𝓢'(ℂ, ℂ))) :
    ∃ g : ℂ →ᵇ ℂ, ContDiff ℝ (⊤ : ℕ∞) (g : ℂ → ℂ) ∧
      (u : ℂ → ℂ) =ᵐ[volume] g := by
  obtain ⟨v, hv⟩ := (hu 2).fourier_memL1 (by norm_num [Complex.finrank_real_complex])
  refine ⟨Real.Lp.fourierTransformInv v, ?_, ?_⟩
  · have h := VectorFourier.contDiff_fourierIntegral (-innerSL ℝ (E := ℂ))
      (N := (⊤ : ℕ∞)) (fun n _ => fourier_moments_of_all_sobolev hu v hv n)
    have he : (Real.Lp.fourierTransformInv v : ℂ → ℂ) =
        VectorFourier.fourierIntegral 𝐞 volume
          (-innerSL ℝ (E := ℂ)).toLinearMap₁₂ (v : ℂ → ℂ) := by
      funext x
      rw [Real.Lp.fourierTransformInv_apply]
      congr 1
    rw [he]
    exact h
  · have he : 𝓕⁻ (v : 𝓢'(ℂ, ℂ)) = (u : 𝓢'(ℂ, ℂ)) := by
      rw [← hv, fourierInv_fourier_eq]
    apply ae_eq_of_integral_contDiff_smul_eq
      ((Lp.memLp u).locallyIntegrable (by norm_num))
      (Real.Lp.fourierTransformInv v).continuous.locallyIntegrable
    intro φ hφ hc
    let ψ : 𝓢(ℂ, ℂ) := (hc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hφ)
    have h := inverseFourier_pairing v ψ
    rw [he, Lp.toTemperedDistribution_apply] at h
    change (∫ x, (φ x : ℂ) • Real.Lp.fourierTransformInv v x) =
      ∫ x, (φ x : ℂ) • u x at h
    simpa only [Complex.real_smul, smul_eq_mul] using h.symm

/-- Smooth representative of every compactly localized weak solution. -/
theorem exists_smooth_cutoff_of_local_potential
    (u : Lp ℂ 2 (volume : Measure ℂ)) {Ω : Set ℂ} {V χ : ℂ → ℂ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (heq : LocalPotentialEquation Ω V (u : 𝓢'(ℂ, ℂ)))
    (hu : LocalMemSobolev Ω 1 (u : 𝓢'(ℂ, ℂ)))
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ Ω) :
    ∃ g : ℂ →ᵇ ℂ, ContDiff ℝ (⊤ : ℕ∞) (g : ℂ → ℂ) ∧
      (fun x => χ x * u x) =ᵐ[volume] g := by
  have hχtop := hχ.continuous.memLp_top_of_hasCompactSupport hc (volume : Measure ℂ)
  let v : Lp ℂ 2 (volume : Measure ℂ) := hχtop.toLp χ • u
  have hv : (v : 𝓢'(ℂ, ℂ)) = smulLeftCLM ℂ χ (u : 𝓢'(ℂ, ℂ)) :=
    Lp.toTemperedDistribution_smul_eq (hc.hasTemperateGrowth hχ) hχtop u
  obtain ⟨g, hg, hag⟩ := exists_smooth_ae_eq_of_all_sobolev v (fun n => by
    rw [hv]
    exact localMemSobolev_all_nat_of_potential hV heq hu n χ hχ hc hs)
  refine ⟨g, hg, ?_⟩
  have hvu : (v : ℂ → ℂ) =ᵐ[volume] fun x => χ x * u x := by
    filter_upwards [Lp.coeFn_lpSMul (r := (2 : ENNReal)) (hχtop.toLp χ) u,
      hχtop.coeFn_toLp] with x hx hχx
    simpa [v, hχx, smul_eq_mul] using hx
  exact hvu.symm.trans hag

/-- Every interior point has a neighborhood with a classical smooth representative. -/
theorem exists_smooth_near_of_local_potential
    (u : Lp ℂ 2 (volume : Measure ℂ)) {Ω : Set ℂ} (hΩ : IsOpen Ω) {V : ℂ → ℂ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (heq : LocalPotentialEquation Ω V (u : 𝓢'(ℂ, ℂ)))
    (hu : LocalMemSobolev Ω 1 (u : 𝓢'(ℂ, ℂ))) {z : ℂ} (hz : z ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ Ω ∧ ∃ g : ℂ →ᵇ ℂ,
      ContDiff ℝ (⊤ : ℕ∞) (g : ℂ → ℂ) ∧
      (u : ℂ → ℂ) =ᵐ[volume.restrict (Metric.ball z r)] g := by
  obtain ⟨r, hr, hs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hz)
  let χ : ContDiffBump z := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hχs : tsupport (χ : ℂ → ℝ) ⊆ Ω := by
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_closedBall (by change r / 2 ≤ r; linarith)).trans hs
  have hcc : HasCompactSupport (fun x => (χ x : ℂ)) :=
    χ.hasCompactSupport.comp_left (map_zero Complex.ofRealCLM)
  have hcs : tsupport (fun x => (χ x : ℂ)) ⊆ Ω :=
    (tsupport_comp_subset (g := Complex.ofRealCLM) (map_zero Complex.ofRealCLM) _).trans hχs
  obtain ⟨g, hg, hag⟩ := exists_smooth_cutoff_of_local_potential u hV heq hu
    (Complex.ofRealCLM.contDiff.comp χ.contDiff) hcc hcs
  refine ⟨r / 4, by positivity, ?_, g, hg, ?_⟩
  · exact (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith))).trans hs
  have hag' := ae_restrict_of_ae (s := Metric.ball z (r / 4)) hag
  filter_upwards [hag', ae_restrict_mem measurableSet_ball] with x hx hxb
  have hχone : χ x = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hxb)
  simpa [hχone] using hx

/-- A continuous representative is smooth on the whole open domain, with no choice
of conflicting representatives on overlapping neighborhoods. -/
theorem contDiffOn_of_continuous_representative_local_potential
    (u : Lp ℂ 2 (volume : Measure ℂ)) {Ω : Set ℂ} (hΩ : IsOpen Ω) {V F : ℂ → ℂ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (heq : LocalPotentialEquation Ω V (u : 𝓢'(ℂ, ℂ)))
    (hu : LocalMemSobolev Ω 1 (u : 𝓢'(ℂ, ℂ)))
    (hF : ContinuousOn F Ω) (ha : (u : ℂ → ℂ) =ᵐ[volume.restrict Ω] F) :
    ContDiffOn ℝ (⊤ : ℕ∞) F Ω := by
  intro z hz
  obtain ⟨r, hr, hs, g, hg, hag⟩ := exists_smooth_near_of_local_potential u hΩ hV heq hu hz
  have ha' : (u : ℂ → ℂ) =ᵐ[volume.restrict (Metric.ball z r)] F :=
    ha.filter_mono (ae_mono (Measure.restrict_mono hs le_rfl))
  have he : Set.EqOn F g (Metric.ball z r) :=
    Measure.eqOn_open_of_ae_eq (ha'.symm.trans hag) Metric.isOpen_ball
      (hF.mono hs) g.continuous.continuousOn
  have hev : F =ᶠ[nhds z] g := by
    filter_upwards [Metric.ball_mem_nhds z hr] with x hx
    exact he hx
  exact (hg.contDiffAt.congr_of_eventuallyEq hev).contDiffWithinAt

end KsIndex.Weq
