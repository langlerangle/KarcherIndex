module

public import KsIndexLean.JacobiWeakTrace
public import KsIndexLean.Bracket
public import KsIndexLean.SlitFluxTest

@[expose] public section


/-!
# Smooth test pairs across the seam

For a globally smooth `ψ` vanishing when `‖w‖ ≤ 1/2` or `2 ≤ ‖w‖`,
`straddlePair` uses `ψ` on the first disk and its pullback by
`σ(w) = 1/conj(w)` on the second, scaled by `phase⁻¹`.
For nonzero `phase`, this choice satisfies the arc0 matching condition
`arcTrace arc0 u.1 = phase • arcTrace arc0 u.2`.

If `ψ` also vanishes on the circle where `0 ≤ Re(w³)`, both arc1 traces
vanish and the pair belongs to `slitTraceDomain 3 phase`. At domain phase
`exp(2παi)`, the second-slot factor is `exp(-2παi)`.
These statements verify the chosen factor; they do not assert its uniqueness
for tests with zero trace.

The concrete `straddleSeed` satisfies the smoothness and vanishing hypotheses,
is positive at `-1`, and is invariant under multiplication by cube roots of
unity. It supplies a nonzero test at the seam.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket

/-! ### Smoothness of the σ-pulled outer half -/

/-- The σ-pulled outer half is globally smooth: near `0` it vanishes
identically (the outer vanishing of `ψ` reflected inward), elsewhere it is a
composition with the smooth reflection. The totalized value `σ 0 = 0` is covered
by the inner vanishing hypothesis. -/
lemma straddle_pull_smooth {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0) :
    ContDiff ℝ ∞ (fun z => ψ (σ z)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · have h0 : ∀ x ∈ Metric.ball (0 : ℂ) (1 / 2), ψ (σ x) = 0 := by
      intro x hx
      rcases eq_or_ne x 0 with rfl | hx0
      · have hσ0 : σ (0 : ℂ) = 0 := by simp [σ]
        rw [hσ0]
        exact h_in 0 (by norm_num)
      · apply h_out
        rw [norm_σ]
        have hxlt : ‖x‖ < 1 / 2 := by
          simpa [Metric.mem_ball, dist_zero_right] using hx
        have hx0' : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
        rw [show (2 : ℝ) = (2⁻¹)⁻¹ by norm_num]
        exact (inv_le_inv₀ (by positivity) hx0').mpr (by linarith)
    exact contDiffAt_const.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds 0 (by norm_num)) h0)
  · exact hs.contDiffAt.comp z (contDiffAt_σ hz)

/-! ### Trace helpers for globally smooth data -/

/-- A globally smooth function vanishing pointwise on an arc has zero trace
there. -/
lemma globalSmoothH1_zeroTrace_of_vanish {A : Set Circle₁} (hA : MeasurableSet A)
    {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hv : ∀ w : Circle₁, w ∈ A → f (w : ℂ) = 0) :
    globalSmoothH1 f hf ∈ zeroTraceDomain A := by
  rw [mem_zeroTraceDomain]
  have h := (globalSmoothH1_trace f hf).filter_mono
    (ae_mono (Measure.restrict_le_self (s := A)))
  filter_upwards [h, ae_restrict_mem hA] with w hw ha
  exact hw.trans (hv w ha)

/-- Two globally smooth functions agreeing at every circle point have the same
arc trace, on every arc. -/
lemma globalSmoothH1_arcTrace_congr (A : Set Circle₁) {f g : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h : ∀ w : Circle₁, f (w : ℂ) = g (w : ℂ)) :
    arcTrace A (globalSmoothH1 f hf) = arcTrace A (globalSmoothH1 g hg) := by
  apply Lp.ext
  have hf' := (globalSmoothH1_trace f hf).filter_mono
    (ae_mono (Measure.restrict_le_self (s := A)))
  have hg' := (globalSmoothH1_trace g hg).filter_mono
    (ae_mono (Measure.restrict_le_self (s := A)))
  have e1 : (arcTrace A (globalSmoothH1 f hf) : Circle₁ → ℂ)
      =ᵐ[circleMeasure.restrict A]
        (diskTraceCLM (globalSmoothH1 f hf) : Circle₁ → ℂ) :=
    boundaryRestrict_coe_ae A _
  have e2 : (arcTrace A (globalSmoothH1 g hg) : Circle₁ → ℂ)
      =ᵐ[circleMeasure.restrict A]
        (diskTraceCLM (globalSmoothH1 g hg) : Circle₁ → ℂ) :=
    boundaryRestrict_coe_ae A _
  filter_upwards [e1, e2, hf', hg'] with w h1 h2 h3 h4
  rw [h1, h3, h w, ← h4, ← h2]

/-! ### The straddling pair -/

/-- The straddling pair: inner half of `ψ` direct on the first copy, outer
half pulled through `σ` on the second, with the `phase⁻¹` prefactor. -/
def straddlePair (phase : ℂ) {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0) : DiskPairH1 :=
  (globalSmoothH1 ψ hs,
    phase⁻¹ • globalSmoothH1 (fun z => ψ (σ z)) (straddle_pull_smooth hs h_in h_out))

/-- **Membership for the chosen inverse-phase factor.** If `ψ` additionally
vanishes on the closed bad sector of the circle (which contains arc1 and the
vertices), the straddling pair lies in the slit trace domain at `phase`. The
arc0 clause is satisfied by the second-slot prefactor `phase⁻¹`. -/
theorem straddlePair_mem_slitTrace (phase : ℂ) (hp : phase ≠ 0) {ψ : ℂ → ℂ}
    (hs : ContDiff ℝ ∞ ψ)
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (h_sector : ∀ w : ℂ, ‖w‖ = 1 → 0 ≤ (w ^ 3).re → ψ w = 0) :
    straddlePair phase hs h_in h_out ∈ slitTraceDomain 3 phase := by
  have hcircle : ∀ w : Circle₁, ψ (σ (w : ℂ)) = ψ (w : ℂ) := fun w => by
    rw [σ_self (mem_sphere_zero_iff_norm.mp w.property)]
  have harc1 : ∀ w : Circle₁, w ∈ boundaryArc 3 1 → ψ (w : ℂ) = 0 := by
    intro w hw
    have hh := (mem_boundaryArc 3 1 w).mp hw
    have hp' : 0 < ((w : ℂ) ^ 3).re := by simpa using hh
    exact h_sector w (mem_sphere_zero_iff_norm.mp w.property) hp'.le
  rw [mem_slitTraceDomain]
  constructor
  · -- arc1: both traces vanish
    have hz1 : globalSmoothH1 ψ hs ∈ zeroTraceDomain (boundaryArc 3 1) :=
      globalSmoothH1_zeroTrace_of_vanish (measurableSet_boundaryArc 3 1) hs harc1
    have hz2 : globalSmoothH1 (fun z => ψ (σ z)) (straddle_pull_smooth hs h_in h_out) ∈
        zeroTraceDomain (boundaryArc 3 1) :=
      globalSmoothH1_zeroTrace_of_vanish (measurableSet_boundaryArc 3 1) _
        (fun w hw => (hcircle w).trans (harc1 w hw))
    have h1 : arcTrace (boundaryArc 3 1) (straddlePair phase hs h_in h_out).1 = 0 := hz1
    have h2 : arcTrace (boundaryArc 3 1) (straddlePair phase hs h_in h_out).2 = 0 := by
      have hz2' : arcTrace (boundaryArc 3 1)
          (globalSmoothH1 (fun z => ψ (σ z)) (straddle_pull_smooth hs h_in h_out)) = 0 := hz2
      change arcTrace (boundaryArc 3 1) (phase⁻¹ •
        globalSmoothH1 (fun z => ψ (σ z)) (straddle_pull_smooth hs h_in h_out)) = 0
      rw [map_smul, hz2', smul_zero]
    rw [h1, h2]
  · -- arc0: the forced-phase computation
    change arcTrace (boundaryArc 3 0) (globalSmoothH1 ψ hs) =
      phase • arcTrace (boundaryArc 3 0) (phase⁻¹ •
        globalSmoothH1 (fun z => ψ (σ z)) (straddle_pull_smooth hs h_in h_out))
    rw [map_smul, smul_smul, mul_inv_cancel₀ hp, one_smul]
    exact globalSmoothH1_arcTrace_congr (boundaryArc 3 0) hs
      (straddle_pull_smooth hs h_in h_out) (fun w => (hcircle w).symm)

/-- The paper specialization: membership at the domain phase `e^{2παi}`. -/
theorem straddlePair_mem_paperSlit (α : ℝ) {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (h_sector : ∀ w : ℂ, ‖w‖ = 1 → 0 ≤ (w ^ 3).re → ψ w = 0) :
    straddlePair (Complex.exp ((2 * Real.pi * α) * Complex.I)) hs h_in h_out ∈
      paperSlitDomain α :=
  straddlePair_mem_slitTrace _ (Complex.exp_ne_zero _) hs h_in h_out h_sector

/-- At domain phase `exp(2παi)`, the second copy is the σ-pullback scaled
by `exp(-2παi)`. This follows from the chosen inverse-phase factor and
`Complex.exp_neg`. -/
lemma straddlePair_snd_phase (α : ℝ) {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0) :
    (straddlePair (Complex.exp ((2 * Real.pi * α) * Complex.I)) hs h_in h_out).2 =
      Complex.exp (-((2 * Real.pi * α) * Complex.I)) •
        globalSmoothH1 (fun z => ψ (σ z)) (straddle_pull_smooth hs h_in h_out) := by
  rw [Complex.exp_neg]
  rfl

/-! ### The model seed: nonvacuousness of the straddling test class -/

/-- The slit flux test localized to the straddling annulus by a `normSq` bump:
supported where `1/4 < normSq w < 4` (i.e. `1/2 < ‖w‖ < 2`) and `Re w³ < 0`. -/
def straddleSeedReal (w : ℂ) : ℝ :=
  expNegInvGlue (Complex.normSq w - 1 / 4) * expNegInvGlue (4 - Complex.normSq w) *
    slitFluxTestReal w

def straddleSeed (w : ℂ) : ℂ := straddleSeedReal w

lemma contDiff_normSq : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq w) := by
  simpa [Complex.normSq_apply] using
    ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))

lemma straddleSeedReal_smooth : ContDiff ℝ ∞ straddleSeedReal :=
  (((expNegInvGlue.contDiff.comp (contDiff_normSq.sub contDiff_const)).mul
    (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_normSq))).mul
      slitFluxTestReal_smooth)

lemma straddleSeed_smooth : ContDiff ℝ ∞ straddleSeed :=
  Complex.ofRealCLM.contDiff.comp straddleSeedReal_smooth

lemma straddleSeed_in (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) : straddleSeed w = 0 := by
  have hn : Complex.normSq w - 1 / 4 ≤ 0 := by
    have h2 : Complex.normSq w = ‖w‖ ^ 2 := by
      rw [Complex.sq_norm]
    nlinarith [norm_nonneg w]
  simp only [straddleSeed, straddleSeedReal, expNegInvGlue.zero_of_nonpos hn,
    zero_mul, Complex.ofReal_zero]

lemma straddleSeed_out (w : ℂ) (hw : 2 ≤ ‖w‖) : straddleSeed w = 0 := by
  have hn : 4 - Complex.normSq w ≤ 0 := by
    have h2 : Complex.normSq w = ‖w‖ ^ 2 := by
      rw [Complex.sq_norm]
    nlinarith
  simp only [straddleSeed, straddleSeedReal, expNegInvGlue.zero_of_nonpos hn,
    mul_zero, zero_mul, Complex.ofReal_zero]

lemma straddleSeed_sector (w : ℂ) (_ : ‖w‖ = 1) (hre : 0 ≤ (w ^ 3).re) :
    straddleSeed w = 0 := by
  have hn : -(w ^ 3).re ≤ 0 := neg_nonpos.mpr hre
  simp only [straddleSeed, straddleSeedReal, slitFluxTestReal,
    expNegInvGlue.zero_of_nonpos hn, mul_zero, Complex.ofReal_zero]

/-- The seed is strictly positive at the interior seam point `−1` (a point of
arc0): the straddling test class is nonempty in a quantitatively visible way. -/
lemma straddleSeedReal_neg_one_pos : 0 < straddleSeedReal (-1) := by
  have h1 : Complex.normSq (-1 : ℂ) = 1 := by simp
  have h3 : (((-1 : ℂ)) ^ 3).re = -1 := by norm_num
  unfold straddleSeedReal slitFluxTestReal
  rw [h1, h3]
  have e1 : (0 : ℝ) < expNegInvGlue (1 - 1 / 4) := expNegInvGlue.pos_of_pos (by norm_num)
  have e2 : (0 : ℝ) < expNegInvGlue (4 - 1) := expNegInvGlue.pos_of_pos (by norm_num)
  have e3 : (0 : ℝ) < expNegInvGlue (-(-1)) := expNegInvGlue.pos_of_pos (by norm_num)
  exact mul_pos (mul_pos e1 e2) e3

/-- The concrete straddling pair built on the seed. -/
def straddleSeedPair (phase : ℂ) : DiskPairH1 :=
  straddlePair phase straddleSeed_smooth straddleSeed_in straddleSeed_out

theorem straddleSeedPair_mem (phase : ℂ) (hp : phase ≠ 0) :
    straddleSeedPair phase ∈ slitTraceDomain 3 phase :=
  straddlePair_mem_slitTrace phase hp straddleSeed_smooth straddleSeed_in
    straddleSeed_out straddleSeed_sector

/-- Rotation invariance of the seed under cube roots of unity. -/
lemma straddleSeedReal_rotation {a : ℂ} (ha : a ^ 3 = 1) (w : ℂ) :
    straddleSeedReal (a * w) = straddleSeedReal w := by
  have hna : Complex.normSq a = 1 := by
    have h1 : ‖a‖ ^ 3 = 1 := by rw [← norm_pow, ha, norm_one]
    have h2 : ‖a‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg a) (by norm_num)).mp h1
    rw [← Complex.sq_norm, h2, one_pow]
  unfold straddleSeedReal slitFluxTestReal
  rw [Complex.normSq_mul, hna, one_mul, mul_pow, ha, one_mul]

end KsIndex.Trace
