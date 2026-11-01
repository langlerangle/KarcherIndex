module

/-
# The tested elliptic equation across a puncture

`tested_identity_across_puncture` assumes that `u : ℂ → ℂ` is globally bounded,
smooth on `ball p r₀ \ {p}`, and satisfies `Δu = -(V * u)` there, with `V`
continuous on the full ball. For every globally smooth, compactly supported
test function `φ` with `tsupport φ ⊆ ball p r₀`, it proves
`∫ u * Δφ = -∫ V * u * φ`. The test need not vanish at `p`.
These are full-plane integrals; changing a value at the single point `p`
does not change them.

The proof first tests with `cut1C ε p * φ`, whose support avoids the puncture,
and applies Green's identity. Expanding the product Laplacian leaves two
cutoff-error terms. The cutoff Laplacian has L¹ norm bounded by a constant
times `1 / Lε ε`, while its gradient has L¹ norm bounded by a constant times
`(ε - ε²) / Lε ε`. Both errors tend to zero along `ε = (n + 2)⁻¹`.
Dominated convergence handles the remaining terms. The module also proves
the Laplacian product rule, measurability off a singleton, and the gradient
bound used in this argument.
-/
public import KsIndexLean.CutLaplacian

@[expose] public section


noncomputable section

open Real Filter Topology MeasureTheory
open scoped ContDiff

namespace KsIndex.PunctureGreen

open KsIndex.PunctureCutoff KsIndex.Surface KsIndex.Green KsIndex.CutLaplacian

/-! ### The Laplacian product rule -/

/-- `Δ(fg) = fΔg + 2(∂₁f∂₁g + ∂_I f∂_I g) + (Δf)g` at a joint `C^∞` point. -/
lemma laplacian_mul {f g : ℂ → ℂ} {w : ℂ} (hf : ContDiffAt ℝ ∞ f w)
    (hg : ContDiffAt ℝ ∞ g w) :
    laplacian (fun z => f z * g z) w
      = f w * laplacian g w
        + 2 * (fderiv ℝ f w 1 * fderiv ℝ g w 1
            + fderiv ℝ f w Complex.I * fderiv ℝ g w Complex.I)
        + laplacian f w * g w := by
  have hf2 : ContDiffAt ℝ 2 f w := hf.of_le two_le_infty
  have hg2 : ContDiffAt ℝ 2 g w := hg.of_le two_le_infty
  -- first derivatives of the product, on a neighbourhood
  have h1 : ∀ v : ℂ, (fun z => fderiv ℝ (fun y => f y * g y) z v)
      =ᶠ[nhds w] fun z => f z * fderiv ℝ g z v + g z * fderiv ℝ f z v := by
    intro v
    filter_upwards [hf2.eventually (by simp), hg2.eventually (by simp)] with z hfz hgz
    rw [fderiv_fun_mul (hfz.differentiableAt (by norm_num))
      (hgz.differentiableAt (by norm_num))]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  -- differentiability of the four ingredient functions at w
  have hdf : DifferentiableAt ℝ f w := hf2.differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ g w := hg2.differentiableAt (by norm_num)
  have hdf' : ∀ v : ℂ, DifferentiableAt ℝ (fun z => fderiv ℝ f z v) w := fun v =>
    ((hf.fderiv_right (m := 1)
      (by simpa using (WithTop.coe_le_coe.mpr (le_top : (1 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
        contDiffAt_const).differentiableAt one_ne_zero
  have hdg' : ∀ v : ℂ, DifferentiableAt ℝ (fun z => fderiv ℝ g z v) w := fun v =>
    ((hg.fderiv_right (m := 1)
      (by simpa using (WithTop.coe_le_coe.mpr (le_top : (1 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
        contDiffAt_const).differentiableAt one_ne_zero
  -- second directional derivative of the product, per direction
  have h2 : ∀ v : ℂ, fderiv ℝ (fun z => fderiv ℝ (fun y => f y * g y) z v) w v
      = f w * fderiv ℝ (fun z => fderiv ℝ g z v) w v
        + 2 * (fderiv ℝ f w v * fderiv ℝ g w v)
        + fderiv ℝ (fun z => fderiv ℝ f z v) w v * g w := by
    intro v
    rw [(h1 v).fderiv_eq]
    have hA : DifferentiableAt ℝ (fun z => f z * fderiv ℝ g z v) w := hdf.mul (hdg' v)
    have hB : DifferentiableAt ℝ (fun z => g z * fderiv ℝ f z v) w := hdg.mul (hdf' v)
    rw [fderiv_fun_add hA hB, fderiv_fun_mul hdf (hdg' v), fderiv_fun_mul hdg (hdf' v)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  simp only [laplacian]
  rw [h2 1, h2 Complex.I]
  ring

/-! ### Measurability off a single point -/

/-- A function continuous off one point is a.e. strongly measurable (for volume on `ℂ`). -/
lemma aestronglyMeasurable_off_singleton {f : ℂ → ℂ} (p : ℂ)
    (hf : ContinuousOn f {p}ᶜ) : AEStronglyMeasurable f (volume : Measure ℂ) := by
  have hrestrict : (volume : Measure ℂ).restrict {p}ᶜ = volume := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have : (volume : Measure ℂ) {p} = 0 := measure_singleton p
    exact (ae_iff.mpr (by simpa using this))
  have h2 : AEStronglyMeasurable f ((volume : Measure ℂ).restrict {p}ᶜ) :=
    hf.aestronglyMeasurable (measurableSet_singleton p).compl
  rwa [hrestrict] at h2

/-! ### Sup bounds for compactly supported continuous data -/

/-- A continuous function with compact support is bounded. -/
lemma exists_bound_of_hasCompactSupport {φ : ℂ → ℂ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w, ‖φ w‖ ≤ C := by
  obtain ⟨C, hC⟩ := hφc.exists_bound_of_continuousOn hφ.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun w => ?_⟩
  by_cases hw : w ∈ tsupport φ
  · exact le_trans (by simpa [Real.norm_eq_abs] using hC w hw) (le_max_left _ _)
  · rw [zero_of_notMem_tsupport hw]
    simpa using le_max_right C 0

/-! ### The gradient of the cutoff: annulus support and the O(ε/L) L¹ bound -/

/-- Off the annulus the cutoff is locally constant, so its derivative vanishes —
including at `p` itself (locally zero on the inner ball). -/
lemma fderiv_cut1_eq_zero_inner {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {p w : ℂ}
    (hw : ‖w - p‖ < ε ^ 2) : fderiv ℝ (cut1 ε p) w = 0 := by
  have hopen : IsOpen {z : ℂ | ‖z - p‖ < ε ^ 2} :=
    isOpen_lt (Continuous.norm (continuous_id.sub continuous_const)) continuous_const
  have hev : cut1 ε p =ᶠ[nhds w] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hw] with z hz
    exact cut1_eq_zero h0 h1 (le_of_lt hz)
  exact fderiv_zero_of_eventually_zero hev

lemma fderiv_cut1_eq_zero_outer {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {p w : ℂ}
    (hw : ε < ‖w - p‖) : fderiv ℝ (cut1 ε p) w = 0 := by
  have hopen : IsOpen {z : ℂ | ε < ‖z - p‖} :=
    isOpen_lt continuous_const (Continuous.norm (continuous_id.sub continuous_const))
  have hev : cut1 ε p =ᶠ[nhds w] fun _ => (1 : ℝ) := by
    filter_upwards [hopen.mem_nhds hw] with z hz
    exact cut1_eq_one h0 h1 (le_of_lt hz)
  rw [hev.fderiv_eq]
  exact fderiv_const_apply 1

/-- The radial dominator for the gradient: `Mψ/(Lr)` on `[ε², ε]`, zero elsewhere. -/
def gradDom (ε : ℝ) (r : ℝ) : ℝ :=
  Set.indicator (Set.Icc (ε ^ 2) ε) (fun r => Mψ * ((Lε ε)⁻¹ * r⁻¹)) r

lemma gradDom_nonneg {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (r : ℝ) : 0 ≤ gradDom ε r := by
  unfold gradDom
  by_cases h : r ∈ Set.Icc (ε ^ 2) ε
  · rw [Set.indicator_of_mem h]
    have hL := (Lε_pos h0 h1).le
    have hr0 : (0 : ℝ) ≤ r := le_trans (pow_pos h0 2).le h.1
    have := Mψ_nonneg
    positivity
  · rw [Set.indicator_of_notMem h]

/-- **Pointwise gradient domination**: `‖fderiv (cut1C) w‖ ≤ gradDom ε ‖w−p‖` everywhere. -/
lemma norm_fderiv_cut1C_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (p w : ℂ) :
    ‖fderiv ℝ (cut1C ε p) w‖ ≤ gradDom ε ‖w - p‖ := by
  have hcoe : ∀ z : ℂ, fderiv ℝ (cut1C ε p) z
      = Complex.ofRealCLM.comp (fderiv ℝ (cut1 ε p) z) := by
    intro z
    have hc : cut1C ε p = ⇑Complex.ofRealCLM ∘ cut1 ε p := rfl
    have hd : DifferentiableAt ℝ (cut1 ε p) z :=
      (((cut1_contDiff h0 h1 p).contDiffAt).of_le two_le_infty).differentiableAt (by norm_num)
    rw [hc, fderiv_comp z Complex.ofRealCLM.differentiableAt hd, ContinuousLinearMap.fderiv]
  have hnorm : ‖fderiv ℝ (cut1C ε p) w‖ ≤ ‖fderiv ℝ (cut1 ε p) w‖ := by
    rw [hcoe w]
    calc ‖Complex.ofRealCLM.comp (fderiv ℝ (cut1 ε p) w)‖
        ≤ ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ)‖ * ‖fderiv ℝ (cut1 ε p) w‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖fderiv ℝ (cut1 ε p) w‖ := by
          gcongr
          exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
            simp [Complex.norm_real]
      _ = ‖fderiv ℝ (cut1 ε p) w‖ := one_mul _
  by_cases hmem : ‖w - p‖ ∈ Set.Icc (ε ^ 2) ε
  · have hw : w ≠ p := by
      intro h; subst h
      simp only [sub_self, norm_zero] at hmem
      nlinarith [hmem.1, pow_pos h0 2]
    refine hnorm.trans ?_
    unfold gradDom
    rw [Set.indicator_of_mem hmem]
    exact norm_fderiv_cut1_le h0 h1 hw
  · rcases not_and_or.mp (Set.mem_Icc.not.mp hmem) with h | h
    · rw [hcoe w, fderiv_cut1_eq_zero_inner h0 h1 (not_le.mp h)]
      simpa using gradDom_nonneg h0 h1 ‖w - p‖
    · rw [hcoe w, fderiv_cut1_eq_zero_outer h0 h1 (not_le.mp h)]
      simpa using gradDom_nonneg h0 h1 ‖w - p‖

lemma gradDom_le_const {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (r : ℝ) :
    gradDom ε r ≤ Mψ * ((Lε ε)⁻¹ * (ε ^ 2)⁻¹) := by
  unfold gradDom
  by_cases h : r ∈ Set.Icc (ε ^ 2) ε
  · rw [Set.indicator_of_mem h]
    have hε2 : 0 < ε ^ 2 := pow_pos h0 2
    have hr0 : 0 < r := lt_of_lt_of_le hε2 h.1
    have hL : 0 < Lε ε := Lε_pos h0 h1
    gcongr
    · exact Mψ_nonneg
    · exact h.1
  · rw [Set.indicator_of_notMem h]
    have := Mψ_nonneg
    have hL := (Lε_pos h0 h1).le
    positivity

lemma integrable_gradDom_comp {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (p : ℂ) :
    Integrable (fun w : ℂ => gradDom ε ‖w - p‖) := by
  have hmeas : Measurable fun w : ℂ => gradDom ε ‖w - p‖ := by
    have hbase : Measurable fun w : ℂ => ‖w - p‖ := (measurable_id.sub_const p).norm
    have hind : Measurable (gradDom ε) :=
      Measurable.indicator (by fun_prop) measurableSet_Icc
    exact hind.comp hbase
  refine Integrable.mono' (g := fun w : ℂ =>
    Set.indicator (Metric.closedBall p ε) (fun _ => Mψ * ((Lε ε)⁻¹ * (ε ^ 2)⁻¹)) w)
    ?_ hmeas.aestronglyMeasurable ?_
  · rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const measure_closedBall_lt_top.ne
  · refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (gradDom_nonneg h0 h1 _)]
    by_cases hball : w ∈ Metric.closedBall p ε
    · rw [Set.indicator_of_mem hball]
      exact gradDom_le_const h0 h1 _
    · rw [Set.indicator_of_notMem hball]
      unfold gradDom
      rw [Set.indicator_of_notMem]
      intro hmem
      exact hball (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hmem.2))

/-- The 1-D radial integral for the gradient: `∫_{Ioi 0} y · gradDom ε y dy = Mψ·(ε−ε²)/L`. -/
lemma integral_smul_gradDom {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ∫ y in Set.Ioi (0 : ℝ), y • gradDom ε y = Mψ * (Lε ε)⁻¹ * (ε - ε ^ 2) := by
  have hε2 : 0 < ε ^ 2 := pow_pos h0 2
  have hε2ε : ε ^ 2 ≤ ε := by nlinarith
  have hsub : Set.Icc (ε ^ 2) ε ⊆ Set.Ioi (0 : ℝ) := fun y hy => lt_of_lt_of_le hε2 hy.1
  have hind : (fun y : ℝ => y • gradDom ε y)
      = Set.indicator (Set.Icc (ε ^ 2) ε) (fun _ => Mψ * (Lε ε)⁻¹) := by
    funext y
    unfold gradDom
    by_cases h : y ∈ Set.Icc (ε ^ 2) ε
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, smul_eq_mul]
      have hy0 : 0 < y := lt_of_lt_of_le hε2 h.1
      field_simp
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, smul_eq_mul, mul_zero]
  rw [hind, setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr hsub,
    setIntegral_const, Real.volume_real_Icc_of_le hε2ε]
  ring

/-- **The O(ε/L) gradient L¹ bound**: `∫ ‖fderiv (cut1C ε p)‖ ≤ 2π·Mψ·(ε−ε²)/L`. -/
theorem integral_norm_fderiv_cut1C_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (p : ℂ) :
    ∫ w : ℂ, ‖fderiv ℝ (cut1C ε p) w‖ ≤ 2 * π * (Mψ * (Lε ε)⁻¹ * (ε - ε ^ 2)) := by
  have hcont : Continuous fun w : ℂ => ‖fderiv ℝ (cut1C ε p) w‖ := by
    have hone : (1 : WithTop ℕ∞) ≤ ∞ := by
      simpa using (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))
    have h1' : ContDiff ℝ 1 (cut1C ε p) := (cut1C_contDiff h0 h1 p).of_le hone
    exact ((h1'.fderiv_right (m := 0) le_rfl).continuous).norm
  have hint : Integrable fun w : ℂ => ‖fderiv ℝ (cut1C ε p) w‖ := by
    refine Integrable.mono' (integrable_gradDom_comp h0 h1 p)
      hcont.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun w => by
      rw [norm_norm]; exact norm_fderiv_cut1C_le h0 h1 p w
  have hmono : ∫ w : ℂ, ‖fderiv ℝ (cut1C ε p) w‖ ≤ ∫ w : ℂ, gradDom ε ‖w - p‖ :=
    integral_mono hint (integrable_gradDom_comp h0 h1 p)
      (fun w => norm_fderiv_cut1C_le h0 h1 p w)
  refine hmono.trans (le_of_eq ?_)
  have htrans : ∫ w : ℂ, gradDom ε ‖w - p‖ = ∫ w : ℂ, gradDom ε ‖w‖ :=
    integral_sub_right_eq_self (fun w : ℂ => gradDom ε ‖w‖) p
  rw [htrans, integral_fun_norm_addHaar (μ := (volume : Measure ℂ)) (gradDom ε)]
  rw [Complex.finrank_real_complex]
  have hvol : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    rw [Measure.real, Complex.volume_ball]
    simp
  rw [hvol]
  have hrad : ∫ y in Set.Ioi (0 : ℝ), y ^ (2 - 1) • gradDom ε y
      = Mψ * (Lε ε)⁻¹ * (ε - ε ^ 2) := by
    simpa using integral_smul_gradDom h0 h1
  rw [hrad]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-! ### Bound for the derivative of a compactly supported smooth function -/

lemma one_le_infty' : (1 : WithTop ℕ∞) ≤ ∞ := by
  simpa using (WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤))

/-- The full derivative of a smooth compactly supported function is bounded. -/
lemma exists_bound_fderiv_of_hasCompactSupport {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w, ‖fderiv ℝ φ w‖ ≤ C := by
  have hcont : Continuous (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 0) (le_trans (by norm_num) one_le_infty')).continuous
  obtain ⟨C, hC⟩ := hφc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun w => ?_⟩
  by_cases hw : w ∈ tsupport φ
  · exact le_trans (hC w hw) (le_max_left _ _)
  · rw [fderiv_zero_of_eventually_zero (eventually_zero_of_notMem_tsupport hw)]
    simpa using le_max_right C 0

/-! ### The per-ε tested identity -/

/-- **The per-ε identity (†)**: testing the equation with `cut1C ε p · φ` and expanding the
product Laplacian.  Each of the three left-hand integrals is separately integrable. -/
lemma eps_identity {p : ℂ} {r₀ : ℝ} {u V : ℂ → ℂ} {B : ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.ball p r₀ \ {p})) (huB : ∀ w, ‖u w‖ ≤ B)
    (hode : ∀ w ∈ Metric.ball p r₀ \ {p}, laplacian u w = -(V w * u w))
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ Metric.ball p r₀)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    (hi1 : Integrable fun w => u w * (cut1C ε p w * laplacian φ w))
    (hi2 : Integrable fun w => u w * (fderiv ℝ (cut1C ε p) w 1 * fderiv ℝ φ w 1
      + fderiv ℝ (cut1C ε p) w Complex.I * fderiv ℝ φ w Complex.I))
    (hi3 : Integrable fun w => u w * (laplacian (cut1C ε p) w * φ w)) :
    (∫ w, u w * (cut1C ε p w * laplacian φ w))
      + 2 * (∫ w, u w * (fderiv ℝ (cut1C ε p) w 1 * fderiv ℝ φ w 1
          + fderiv ℝ (cut1C ε p) w Complex.I * fderiv ℝ φ w Complex.I))
      + (∫ w, u w * (laplacian (cut1C ε p) w * φ w))
      = -∫ w, V w * u w * (cut1C ε p w * φ w) := by
  have hUopen : IsOpen (Metric.ball p r₀ \ {p}) :=
    Metric.isOpen_ball.sdiff isClosed_singleton
  -- the test function χφ
  have hχsm : ContDiff ℝ ∞ (cut1C ε p) := cut1C_contDiff h0 h1 p
  have htest : ContDiff ℝ ∞ (fun w => cut1C ε p w * φ w) := hχsm.mul hφ
  have htestc : HasCompactSupport (fun w => cut1C ε p w * φ w) := by
    refine IsCompact.of_isClosed_subset hφc isClosed_closure
      (closure_minimal ?_ (isClosed_tsupport φ))
    intro w hw
    by_contra hts
    exact hw (show cut1C ε p w * φ w = 0 by rw [zero_of_notMem_tsupport hts, mul_zero])
  have hpnot : p ∉ tsupport (fun w => cut1C ε p w * φ w) := by
    have hopen : IsOpen {z : ℂ | ‖z - p‖ < ε ^ 2} :=
      isOpen_lt (Continuous.norm (continuous_id.sub continuous_const)) continuous_const
    have hzero : ∀ z ∈ {z : ℂ | ‖z - p‖ < ε ^ 2}, cut1C ε p z * φ z = 0 := fun z hz => by
      simp only [cut1C, cut1_eq_zero h0 h1 (le_of_lt hz), Complex.ofReal_zero, zero_mul]
    intro hp
    have : p ∈ closure (Function.support fun w => cut1C ε p w * φ w) := hp
    rw [_root_.mem_closure_iff] at this
    obtain ⟨z, hz1, hz2⟩ := this _ hopen (by simp [pow_pos h0 2])
    exact hz2 (by simpa using hzero z hz1)
  have htestU : tsupport (fun w => cut1C ε p w * φ w) ⊆ Metric.ball p r₀ \ {p} := by
    intro w hw
    refine ⟨?_, ?_⟩
    · refine hφU ?_
      refine closure_minimal ?_ (isClosed_tsupport φ) hw
      intro z hz
      by_contra hts
      exact hz (show cut1C ε p z * φ z = 0 by rw [zero_of_notMem_tsupport hts, mul_zero])
    · intro hwp
      rw [Set.mem_singleton_iff] at hwp
      exact hpnot (hwp ▸ hw)
  -- Green + the equation
  have hgreen := green_identity hUopen hu htest htestc htestU
  have hrhs : ∫ w, laplacian u w * (cut1C ε p w * φ w)
      = -∫ w, V w * u w * (cut1C ε p w * φ w) := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    show laplacian u w * (cut1C ε p w * φ w) = -(V w * u w * (cut1C ε p w * φ w))
    by_cases hw : w ∈ tsupport (fun z => cut1C ε p z * φ z)
    · rw [hode w (htestU hw)]
      ring
    · have h0 : cut1C ε p w * φ w = 0 :=
        zero_of_notMem_tsupport (φ := fun z => cut1C ε p z * φ z) hw
      rw [h0]
      ring
  -- expand the Laplacian of the product
  have hexp : ∀ w : ℂ, u w * laplacian (fun z => cut1C ε p z * φ z) w
      = u w * (cut1C ε p w * laplacian φ w)
        + 2 * (u w * (fderiv ℝ (cut1C ε p) w 1 * fderiv ℝ φ w 1
            + fderiv ℝ (cut1C ε p) w Complex.I * fderiv ℝ φ w Complex.I))
        + u w * (laplacian (cut1C ε p) w * φ w) := by
    intro w
    rw [laplacian_mul hχsm.contDiffAt hφ.contDiffAt]
    ring
  calc (∫ w, u w * (cut1C ε p w * laplacian φ w))
        + 2 * (∫ w, u w * (fderiv ℝ (cut1C ε p) w 1 * fderiv ℝ φ w 1
            + fderiv ℝ (cut1C ε p) w Complex.I * fderiv ℝ φ w Complex.I))
        + (∫ w, u w * (laplacian (cut1C ε p) w * φ w))
      = ∫ w, (u w * (cut1C ε p w * laplacian φ w)
          + 2 * (u w * (fderiv ℝ (cut1C ε p) w 1 * fderiv ℝ φ w 1
              + fderiv ℝ (cut1C ε p) w Complex.I * fderiv ℝ φ w Complex.I))
          + u w * (laplacian (cut1C ε p) w * φ w)) := by
        have hB : Integrable (fun w => 2 * (u w * (fderiv ℝ (cut1C ε p) w 1 * fderiv ℝ φ w 1
            + fderiv ℝ (cut1C ε p) w Complex.I * fderiv ℝ φ w Complex.I))) := hi2.const_mul 2
        have hAB : Integrable (fun w => u w * (cut1C ε p w * laplacian φ w)
            + 2 * (u w * (fderiv ℝ (cut1C ε p) w 1 * fderiv ℝ φ w 1
              + fderiv ℝ (cut1C ε p) w Complex.I * fderiv ℝ φ w Complex.I))) := hi1.add hB
        rw [integral_add hAB hi3, integral_add hi1 hB, integral_const_mul]
    _ = ∫ w, u w * laplacian (fun z => cut1C ε p z * φ z) w :=
        integral_congr_ae (Filter.Eventually.of_forall fun w => (hexp w).symm)
    _ = ∫ w, laplacian u w * (cut1C ε p w * φ w) := hgreen
    _ = -∫ w, V w * u w * (cut1C ε p w * φ w) := hrhs

/-! ### The tested equation across the puncture -/

/-- A globally bounded function, smooth and solving `Δu = -Vu` on the punctured
ball, satisfies the tested equation across the puncture when `V` is continuous
on the full ball. The test is globally smooth with compact support contained
in that ball; it need not vanish at `p`. The integrals are over the full plane. -/
theorem tested_identity_across_puncture {p : ℂ} {r₀ : ℝ} {u V : ℂ → ℂ} {B : ℝ}
    (hu : ContDiffOn ℝ ∞ u (Metric.ball p r₀ \ {p})) (huB : ∀ w, ‖u w‖ ≤ B)
    (hV : ContinuousOn V (Metric.ball p r₀))
    (hode : ∀ w ∈ Metric.ball p r₀ \ {p}, laplacian u w = -(V w * u w))
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ Metric.ball p r₀) :
    ∫ w, u w * laplacian φ w = -∫ w, V w * u w * φ w := by
  have hUopen : IsOpen (Metric.ball p r₀ \ {p}) :=
    Metric.isOpen_ball.sdiff isClosed_singleton
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (huB p)
  obtain ⟨Cφ, hCφ0, hCφ⟩ := exists_bound_of_hasCompactSupport hφ.continuous hφc
  obtain ⟨Cφ', hCφ'0, hCφ'⟩ := exists_bound_fderiv_of_hasCompactSupport hφ hφc
  obtain ⟨CV₀, hCV₀⟩ := hφc.exists_bound_of_continuousOn (hV.mono hφU)
  set CV : ℝ := max CV₀ 0 with hCVdef
  have hCV0 : 0 ≤ CV := le_max_right _ _
  have hCV : ∀ w ∈ tsupport φ, ‖V w‖ ≤ CV := fun w hw =>
    le_trans (hCV₀ w hw) (le_max_left _ _)
  -- continuity of the φ-side data
  have hΔφc : Continuous fun w => laplacian φ w :=
    continuous_iff_continuousAt.mpr fun _ => laplacian_continuousAt hφ.contDiffAt
  have hDphi : ∀ v : ℂ, Continuous fun w => fderiv ℝ φ w v := fun v =>
    (ContinuousLinearMap.apply ℝ ℂ v).continuous.comp
      (hφ.fderiv_right (m := 0) (le_trans (by norm_num) one_le_infty')).continuous
  have huc : ∀ w ∈ Metric.ball p r₀ \ {p}, ContinuousAt u w := fun w hw =>
    (hu.contDiffAt (hUopen.mem_nhds hw)).continuousAt
  have hVuc : ∀ w ∈ Metric.ball p r₀ \ {p}, ContinuousAt (fun z => V z * u z) w := fun w hw =>
    (hV.continuousAt (Metric.isOpen_ball.mem_nhds hw.1)).mul (huc w hw)
  -- the a.e.-measurability engine: `f` continuous on the punctured ball, `h` continuous and
  -- vanishing off `tsupport φ` ⟹ `f·h` is a.e. strongly measurable
  have hAESM : ∀ (f h : ℂ → ℂ), (∀ w ∈ Metric.ball p r₀ \ {p}, ContinuousAt f w) →
      Continuous h → (∀ z, z ∉ tsupport φ → h z = 0) →
      AEStronglyMeasurable (fun w => f w * h w) (volume : Measure ℂ) := by
    intro f h hf hh hh0
    refine aestronglyMeasurable_off_singleton p ?_
    intro w hw
    have hcov : w ∈ Metric.ball p r₀ \ {p} ∨ w ∉ tsupport φ := by
      by_cases hb : w ∈ Metric.ball p r₀
      · exact Or.inl ⟨hb, hw⟩
      · exact Or.inr fun hts => hb (hφU hts)
    rcases hcov with hwU | hwT
    · exact ((hf w hwU).mul hh.continuousAt).continuousWithinAt
    · refine ContinuousAt.continuousWithinAt ?_
      refine (continuousAt_const (y := (0 : ℂ))).congr ?_
      refine (Filter.eventuallyEq_of_mem ((isClosed_tsupport φ).isOpen_compl.mem_nhds hwT)
        fun z hz => ?_).symm
      rw [hh0 z hz, mul_zero]
  -- compact support of real dominators
  have hcsupp : ∀ g : ℂ → ℝ, (∀ z, z ∉ tsupport φ → g z = 0) → HasCompactSupport g := by
    intro g hg
    refine IsCompact.of_isClosed_subset hφc isClosed_closure
      (closure_minimal ?_ (isClosed_tsupport φ))
    intro z hz
    by_contra hts
    exact hz (hg z hts)
  -- the ε sequence
  set εs : ℕ → ℝ := fun n => ((n : ℝ) + 2)⁻¹ with hεsdef
  have hε0 : ∀ n, 0 < εs n := fun n => by
    simp only [hεsdef]
    positivity
  have hε1 : ∀ n, εs n < 1 := fun n => by
    simp only [hεsdef]
    rw [inv_lt_one₀ (by positivity)]
    have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hεtend : Tendsto εs atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    exact h1.inv_tendsto_atTop
  have hLval : ∀ n, Lε (εs n) = Real.log ((n : ℝ) + 2) := by
    intro n
    simp only [hεsdef]
    show -Real.log (((n : ℝ) + 2)⁻¹) = _
    rw [Real.log_inv, neg_neg]
  have hLlim : Tendsto (fun n => (Lε (εs n))⁻¹) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
      Real.tendsto_log_atTop.comp
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    exact h2.inv_tendsto_atTop.congr fun n => by rw [Pi.inv_apply, hLval n]
  -- the cutoff family: basic facts
  have hχcont : ∀ n, Continuous (cut1C (εs n) p) := fun n =>
    (cut1C_contDiff (hε0 n) (hε1 n) p).continuous
  have hχle1 : ∀ n w, ‖cut1C (εs n) p w‖ ≤ 1 := fun n w => by
    show ‖((cut1 (εs n) p w : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cut1_nonneg _ _ _)]
    exact cut1_le_one _ _ _
  have hχlim : ∀ w : ℂ, w ≠ p → Tendsto (fun n => cut1C (εs n) p w) atTop (𝓝 1) := by
    intro w hw
    have hpos : 0 < ‖w - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw)
    have hev : ∀ᶠ n in atTop, cut1C (εs n) p w = 1 := by
      filter_upwards [hεtend.eventually_lt_const hpos] with n hn
      show ((cut1 (εs n) p w : ℝ) : ℂ) = 1
      rw [cut1_eq_one (hε0 n) (hε1 n) (le_of_lt hn), Complex.ofReal_one]
    exact Tendsto.congr' (hev.mono fun n hn => hn.symm) tendsto_const_nhds
  have hae : ∀ᵐ w : ℂ ∂(volume : Measure ℂ), w ≠ p := by
    rw [ae_iff]
    have : {w : ℂ | ¬ w ≠ p} = {p} := by
      ext w
      simp [not_not]
    rw [this]
    exact measure_singleton p
  -- ‖Δχ‖ is integrable and its integral is O(1/L)
  have hΔχcont : ∀ n, Continuous fun w => laplacian (cut1C (εs n) p) w := fun n =>
    continuous_iff_continuousAt.mpr fun _ =>
      laplacian_continuousAt (cut1C_contDiff (hε0 n) (hε1 n) p).contDiffAt
  have hΔχint : ∀ n, Integrable fun w : ℂ => ‖laplacian (cut1C (εs n) p) w‖ := fun n => by
    refine Integrable.mono' (integrable_lapDom_comp (hε0 n) (hε1 n) p)
      (hΔχcont n).norm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun w => by
      rw [norm_norm]; exact norm_laplacian_cut1C_le (hε0 n) (hε1 n) p w
  have hGchiInt : ∀ n, Integrable fun w : ℂ => ‖fderiv ℝ (cut1C (εs n) p) w‖ := fun n => by
    have hone : (1 : WithTop ℕ∞) ≤ ∞ := one_le_infty'
    have h1' : ContDiff ℝ 1 (cut1C (εs n) p) :=
      (cut1C_contDiff (hε0 n) (hε1 n) p).of_le hone
    refine Integrable.mono' (integrable_gradDom_comp (hε0 n) (hε1 n) p)
      ((h1'.fderiv_right (m := 0) le_rfl).continuous.norm.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun w => by
      rw [norm_norm]; exact norm_fderiv_cut1C_le (hε0 n) (hε1 n) p w
  -- the three left-hand integrabilities (per n)
  have hbint1 : Integrable fun w : ℂ => B * ‖laplacian φ w‖ :=
    (hΔφc.norm.const_mul B).integrable_of_hasCompactSupport
      (hcsupp _ fun z hz => by rw [laplacian_zero_of_notMem_tsupport hz, norm_zero, mul_zero])
  have hi1 : ∀ n, Integrable fun w => u w * (cut1C (εs n) p w * laplacian φ w) := by
    intro n
    refine Integrable.mono' hbint1
      (hAESM u _ huc ((hχcont n).mul hΔφc)
        (fun z hz => by rw [laplacian_zero_of_notMem_tsupport hz, mul_zero]) ) ?_
    refine Filter.Eventually.of_forall fun w => ?_
    calc ‖u w * (cut1C (εs n) p w * laplacian φ w)‖
        = ‖u w‖ * (‖cut1C (εs n) p w‖ * ‖laplacian φ w‖) := by rw [norm_mul, norm_mul]
      _ ≤ B * (1 * ‖laplacian φ w‖) := by
          gcongr
          · exact huB w
          · exact hχle1 n w
      _ = B * ‖laplacian φ w‖ := by rw [one_mul]
  have hDchi : ∀ n (v : ℂ), Continuous fun w => fderiv ℝ (cut1C (εs n) p) w v := fun n v =>
    (ContinuousLinearMap.apply ℝ ℂ v).continuous.comp
      (((cut1C_contDiff (hε0 n) (hε1 n) p).of_le one_le_infty').fderiv_right (m := 0)
        le_rfl).continuous
  -- the shared pointwise bound for the gradient cross term
  have hdom2 : ∀ n w, ‖u w * (fderiv ℝ (cut1C (εs n) p) w 1 * fderiv ℝ φ w 1
      + fderiv ℝ (cut1C (εs n) p) w Complex.I * fderiv ℝ φ w Complex.I)‖
      ≤ (B * (2 * Cφ')) * ‖fderiv ℝ (cut1C (εs n) p) w‖ := by
    intro n w
    have e1 : ‖fderiv ℝ (cut1C (εs n) p) w 1‖ ≤ ‖fderiv ℝ (cut1C (εs n) p) w‖ := by
      simpa using (fderiv ℝ (cut1C (εs n) p) w).le_opNorm 1
    have e2 : ‖fderiv ℝ (cut1C (εs n) p) w Complex.I‖ ≤ ‖fderiv ℝ (cut1C (εs n) p) w‖ := by
      simpa [Complex.norm_I] using (fderiv ℝ (cut1C (εs n) p) w).le_opNorm Complex.I
    have e3 : ‖fderiv ℝ φ w 1‖ ≤ Cφ' := by
      refine le_trans (by simpa using (fderiv ℝ φ w).le_opNorm 1) (hCφ' w)
    have e4 : ‖fderiv ℝ φ w Complex.I‖ ≤ Cφ' := by
      refine le_trans (by simpa [Complex.norm_I] using (fderiv ℝ φ w).le_opNorm Complex.I)
        (hCφ' w)
    calc ‖u w * (fderiv ℝ (cut1C (εs n) p) w 1 * fderiv ℝ φ w 1
        + fderiv ℝ (cut1C (εs n) p) w Complex.I * fderiv ℝ φ w Complex.I)‖
        = ‖u w‖ * ‖fderiv ℝ (cut1C (εs n) p) w 1 * fderiv ℝ φ w 1
            + fderiv ℝ (cut1C (εs n) p) w Complex.I * fderiv ℝ φ w Complex.I‖ := norm_mul _ _
      _ ≤ B * (‖fderiv ℝ (cut1C (εs n) p) w 1‖ * ‖fderiv ℝ φ w 1‖
            + ‖fderiv ℝ (cut1C (εs n) p) w Complex.I‖ * ‖fderiv ℝ φ w Complex.I‖) := by
          refine mul_le_mul (huB w) ?_ (norm_nonneg _) hB0
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul, norm_mul]
      _ ≤ B * (‖fderiv ℝ (cut1C (εs n) p) w‖ * Cφ'
            + ‖fderiv ℝ (cut1C (εs n) p) w‖ * Cφ') := by
          refine mul_le_mul_of_nonneg_left ?_ hB0
          exact add_le_add (mul_le_mul e1 e3 (norm_nonneg _) (norm_nonneg _))
            (mul_le_mul e2 e4 (norm_nonneg _) (norm_nonneg _))
      _ = (B * (2 * Cφ')) * ‖fderiv ℝ (cut1C (εs n) p) w‖ := by ring
  have hi2 : ∀ n, Integrable fun w =>
      u w * (fderiv ℝ (cut1C (εs n) p) w 1 * fderiv ℝ φ w 1
        + fderiv ℝ (cut1C (εs n) p) w Complex.I * fderiv ℝ φ w Complex.I) := by
    intro n
    refine Integrable.mono' ((hGchiInt n).const_mul (B * (2 * Cφ')))
      (hAESM u _ huc (((hDchi n 1).mul (hDphi 1)).add ((hDchi n Complex.I).mul (hDphi Complex.I)))
        (fun z hz => by rw [fderiv_zero_of_notMem_tsupport hz]; simp)) ?_
    exact Filter.Eventually.of_forall fun w => hdom2 n w
  have hi3 : ∀ n, Integrable fun w =>
      u w * (laplacian (cut1C (εs n) p) w * φ w) := by
    intro n
    refine Integrable.mono' ((hΔχint n).const_mul (B * Cφ))
      (hAESM u _ huc ((hΔχcont n).mul hφ.continuous)
        (fun z hz => by rw [zero_of_notMem_tsupport hz, mul_zero])) ?_
    refine Filter.Eventually.of_forall fun w => ?_
    calc ‖u w * (laplacian (cut1C (εs n) p) w * φ w)‖
        = ‖u w‖ * (‖laplacian (cut1C (εs n) p) w‖ * ‖φ w‖) := by rw [norm_mul, norm_mul]
      _ ≤ B * (‖laplacian (cut1C (εs n) p) w‖ * Cφ) := by
          gcongr
          · exact huB w
          · exact hCφ w
      _ = (B * Cφ) * ‖laplacian (cut1C (εs n) p) w‖ := by ring
  -- limit 1: `∫ u·χΔφ → ∫ u·Δφ` (dominated convergence)
  have hlim1 : Tendsto (fun n => ∫ w, u w * (cut1C (εs n) p w * laplacian φ w)) atTop
      (𝓝 (∫ w, u w * laplacian φ w)) := by
    refine tendsto_integral_of_dominated_convergence (fun w => B * ‖laplacian φ w‖)
      (fun n => hAESM u _ huc ((hχcont n).mul hΔφc)
        (fun z hz => by rw [laplacian_zero_of_notMem_tsupport hz, mul_zero]))
      hbint1 (fun n => Filter.Eventually.of_forall fun w => ?_) ?_
    · calc ‖u w * (cut1C (εs n) p w * laplacian φ w)‖
          = ‖u w‖ * (‖cut1C (εs n) p w‖ * ‖laplacian φ w‖) := by rw [norm_mul, norm_mul]
        _ ≤ B * (1 * ‖laplacian φ w‖) := by
            gcongr
            · exact huB w
            · exact hχle1 n w
        _ = B * ‖laplacian φ w‖ := by rw [one_mul]
    · filter_upwards [hae] with w hw
      have h := ((hχlim w hw).mul_const (laplacian φ w)).const_mul (u w)
      simpa using h
  -- limit RHS: `∫ V·u·χφ → ∫ V·u·φ` (dominated convergence)
  have hbintG : Integrable fun w : ℂ => (CV * B) * ‖φ w‖ :=
    (hφ.continuous.norm.const_mul _).integrable_of_hasCompactSupport
      (hcsupp _ fun z hz => by rw [zero_of_notMem_tsupport hz, norm_zero, mul_zero])
  have hlimG : Tendsto (fun n => ∫ w, V w * u w * (cut1C (εs n) p w * φ w)) atTop
      (𝓝 (∫ w, V w * u w * φ w)) := by
    refine tendsto_integral_of_dominated_convergence (fun w => (CV * B) * ‖φ w‖)
      (fun n => hAESM (fun z => V z * u z) _ hVuc ((hχcont n).mul hφ.continuous)
        (fun z hz => by rw [zero_of_notMem_tsupport hz, mul_zero])) hbintG
      (fun n => Filter.Eventually.of_forall fun w => ?_) ?_
    · by_cases hts : w ∈ tsupport φ
      · calc ‖V w * u w * (cut1C (εs n) p w * φ w)‖
            = ‖V w‖ * ‖u w‖ * (‖cut1C (εs n) p w‖ * ‖φ w‖) := by
              rw [norm_mul, norm_mul, norm_mul]
          _ ≤ CV * B * (1 * ‖φ w‖) := by
              gcongr
              · exact hCV w hts
              · exact huB w
              · exact hχle1 n w
          _ = CV * B * ‖φ w‖ := by rw [one_mul]
      · rw [zero_of_notMem_tsupport hts]
        simp
    · filter_upwards [hae] with w hw
      have h := ((hχlim w hw).mul_const (φ w)).const_mul (V w * u w)
      simpa using h
  -- limit 3: the O(1/L) term dies
  have hlim3 : Tendsto (fun n => ∫ w, u w * (laplacian (cut1C (εs n) p) w * φ w)) atTop
      (𝓝 0) := by
    have hb : ∀ n, ‖∫ w, u w * (laplacian (cut1C (εs n) p) w * φ w)‖
        ≤ (B * Cφ * (2 * π * Mψ₂)) * (Lε (εs n))⁻¹ := by
      intro n
      calc ‖∫ w, u w * (laplacian (cut1C (εs n) p) w * φ w)‖
          ≤ ∫ w, ‖u w * (laplacian (cut1C (εs n) p) w * φ w)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ w, (B * Cφ) * ‖laplacian (cut1C (εs n) p) w‖ := by
            refine integral_mono (hi3 n).norm ((hΔχint n).const_mul _) fun w => ?_
            calc ‖u w * (laplacian (cut1C (εs n) p) w * φ w)‖
                = ‖u w‖ * (‖laplacian (cut1C (εs n) p) w‖ * ‖φ w‖) := by
                  rw [norm_mul, norm_mul]
              _ ≤ B * (‖laplacian (cut1C (εs n) p) w‖ * Cφ) := by
                  gcongr
                  · exact huB w
                  · exact hCφ w
              _ = (B * Cφ) * ‖laplacian (cut1C (εs n) p) w‖ := by ring
        _ = (B * Cφ) * ∫ w, ‖laplacian (cut1C (εs n) p) w‖ := integral_const_mul _ _
        _ ≤ (B * Cφ) * (2 * π * Mψ₂ * (Lε (εs n))⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hB0 hCφ0)
            exact integral_norm_laplacian_cut1C_le (hε0 n) (hε1 n) p
        _ = (B * Cφ * (2 * π * Mψ₂)) * (Lε (εs n))⁻¹ := by ring
    refine squeeze_zero_norm hb ?_
    have h := hLlim.const_mul (B * Cφ * (2 * π * Mψ₂))
    simpa using h
  -- limit 2: the O(ε/L) gradient cross term dies
  have hlim2 : Tendsto (fun n => ∫ w, u w * (fderiv ℝ (cut1C (εs n) p) w 1 * fderiv ℝ φ w 1
      + fderiv ℝ (cut1C (εs n) p) w Complex.I * fderiv ℝ φ w Complex.I)) atTop (𝓝 0) := by
    have hb : ∀ n, ‖∫ w, u w * (fderiv ℝ (cut1C (εs n) p) w 1 * fderiv ℝ φ w 1
        + fderiv ℝ (cut1C (εs n) p) w Complex.I * fderiv ℝ φ w Complex.I)‖
        ≤ (B * (2 * Cφ') * (2 * π)) * (Mψ * (Lε (εs n))⁻¹ * (εs n - εs n ^ 2)) := by
      intro n
      calc ‖∫ w, u w * (fderiv ℝ (cut1C (εs n) p) w 1 * fderiv ℝ φ w 1
          + fderiv ℝ (cut1C (εs n) p) w Complex.I * fderiv ℝ φ w Complex.I)‖
          ≤ ∫ w, ‖u w * (fderiv ℝ (cut1C (εs n) p) w 1 * fderiv ℝ φ w 1
              + fderiv ℝ (cut1C (εs n) p) w Complex.I * fderiv ℝ φ w Complex.I)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ w, (B * (2 * Cφ')) * ‖fderiv ℝ (cut1C (εs n) p) w‖ := by
            refine integral_mono (hi2 n).norm ((hGchiInt n).const_mul _) fun w => hdom2 n w
        _ = (B * (2 * Cφ')) * ∫ w, ‖fderiv ℝ (cut1C (εs n) p) w‖ := integral_const_mul _ _
        _ ≤ (B * (2 * Cφ')) * (2 * π * (Mψ * (Lε (εs n))⁻¹ * (εs n - εs n ^ 2))) := by
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg hB0 (by linarith))
            exact integral_norm_fderiv_cut1C_le (hε0 n) (hε1 n) p
        _ = (B * (2 * Cφ') * (2 * π)) * (Mψ * (Lε (εs n))⁻¹ * (εs n - εs n ^ 2)) := by ring
    refine squeeze_zero_norm hb ?_
    have hεsq : Tendsto (fun n => εs n - εs n ^ 2) atTop (𝓝 0) := by
      have h := hεtend.sub (hεtend.pow 2)
      simpa using h
    have hprod : Tendsto (fun n => Mψ * (Lε (εs n))⁻¹ * (εs n - εs n ^ 2)) atTop (𝓝 0) := by
      have h := ((hLlim.const_mul Mψ).mul hεsq)
      simpa using h
    have h := hprod.const_mul (B * (2 * Cφ') * (2 * π))
    simpa using h
  -- the per-n identity + limit uniqueness
  have hiden : ∀ n, (∫ w, u w * (cut1C (εs n) p w * laplacian φ w))
      + 2 * (∫ w, u w * (fderiv ℝ (cut1C (εs n) p) w 1 * fderiv ℝ φ w 1
          + fderiv ℝ (cut1C (εs n) p) w Complex.I * fderiv ℝ φ w Complex.I))
      + (∫ w, u w * (laplacian (cut1C (εs n) p) w * φ w))
      = -∫ w, V w * u w * (cut1C (εs n) p w * φ w) := fun n =>
    eps_identity hu huB hode hφ hφc hφU (hε0 n) (hε1 n) (hi1 n) (hi2 n) (hi3 n)
  have hLHS : Tendsto (fun n => (∫ w, u w * (cut1C (εs n) p w * laplacian φ w))
      + 2 * (∫ w, u w * (fderiv ℝ (cut1C (εs n) p) w 1 * fderiv ℝ φ w 1
          + fderiv ℝ (cut1C (εs n) p) w Complex.I * fderiv ℝ φ w Complex.I))
      + (∫ w, u w * (laplacian (cut1C (εs n) p) w * φ w))) atTop
      (𝓝 (∫ w, u w * laplacian φ w)) := by
    have h := (hlim1.add (hlim2.const_mul 2)).add hlim3
    simpa using h
  have hRHS : Tendsto (fun n => -∫ w, V w * u w * (cut1C (εs n) p w * φ w)) atTop
      (𝓝 (-∫ w, V w * u w * φ w)) := hlimG.neg
  exact tendsto_nhds_unique (hLHS.congr fun n => hiden n) hRHS

end KsIndex.PunctureGreen
