module

/-
The class-zero mixed cross pairing `Bd(f₀, v) = −2π κ² ν`.

The Gram argument for `1 ≤ seamNat k true false 0` pairs the radial ground state `f₀ = groundC k`
against the trace-carrying test function `v = vSlitC k δ c`.  Because `f₀` is radial, its Fréchet
derivative has a vanishing tangential component (`fderiv_groundC_tangential`) and a radial component
`gD` (`fderiv_groundC_radial`), so the basis-rotation identity (`GradOrtho.basis_rot`) collapses the
gradient cross density to

  `gradInner f₀ v (r e^{iθ}) = gD(r) · ∂_r v(r e^{iθ})`   (`gradInner_groundC_polar`).

The disk pairing is then a pure polar reduction (`BallPolar.setIntegral_ball_polar`): only the
`ℓ = 0` circular mode of `v` survives the `θ`-integration (`Fm`/`FmD` package the differentiation
under the integral, `FourierMode.Fm_hasDerivAt`), leaving the 1-D pairing

  `Bd(f₀, v) = 2π ∫₀¹ (r g' μ' − r V g μ) dr = 2π · g'(1) · μ(1) = −2π κ² ν`

by the cross-term FTC (`GroundDisk.cross_ftc'`, `μ(1) = ν = nuSlit`).  On the open disk `vSlitC`
agrees with the globally smooth `cutSlitC` (`Bd_vSlitC_eq_cutSlitC`), so all derivative computations
use the smooth extension. Radiality removes the tangential derivative term pointwise;
angular integration then selects the zero circular mode. No mode-sum expansion is needed.

The pairing identity holds for `k ≥ 2` and arbitrary real `δ, c`. Positivity of
`ν = nuSlit k δ c` is a separate result, `nuSlit_pos`, requiring `δ > 0` and
`0 < c ≤ 1/2`; these are the cutoff conditions used for the nonzero Gram pairing.
-/
public import KsIndexLean.VSlit
public import KsIndexLean.GroundDisk
public import KsIndexLean.ModeDiag
public import KsIndexLean.BallPolar
public import KsIndexLean.PolarGrad

@[expose] public section


noncomputable section

open Complex MeasureTheory Set Filter Real
open KsIndex.Surface KsIndex.Radial KsIndex.Parseval KsIndex.FourierMode KsIndex.GradOrtho
  KsIndex.PolarGrad KsIndex.BallPolar KsIndex.SingleDiskBridge
open scoped ContDiff

namespace KsIndex.SingleDisk

variable {k : ℕ} {δ c : ℝ}

/-! ### `ℝ`-valued Fréchet derivatives through `ofReal` -/

/-- The Fréchet derivative of a real-valued function composed with `ofReal` is `ofReal` of the
real derivative. -/
lemma fderiv_ofRealComp_apply {f : ℂ → ℝ} {w : ℂ} (hf : DifferentiableAt ℝ f w) (v : ℂ) :
    fderiv ℝ (fun z => ((f z : ℝ) : ℂ)) w v = ((fderiv ℝ f w v : ℝ) : ℂ) := by
  have h : HasFDerivAt (fun z => ((f z : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ f w)) w :=
    Complex.ofRealCLM.hasFDerivAt.comp w hf.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- The derivative of `cutSlitC` is `ofReal` of the derivative of `cutSlit`. -/
lemma fderiv_cutSlitC_apply (w v : ℂ) :
    fderiv ℝ (cutSlitC k δ c) w v = ((fderiv ℝ (cutSlit k δ c) w v : ℝ) : ℂ) := by
  have hs : DifferentiableAt ℝ (cutSlit k δ c) w :=
    ((contDiff_cutSlit k δ c).differentiable (by simp)).differentiableAt
  unfold cutSlitC
  exact fderiv_ofRealComp_apply hs v

/-! ### The radial and tangential derivatives of the ground state -/

/-- **Radial derivative of the ground state**: along `e^{iθ}` at `r e^{iθ}` (with `r > 0`) it is
`g'(r) = gD k r`, because near `r` the profile is `y ↦ gRad k 0 y`. -/
lemma fderiv_groundC_radial (hk2 : 2 ≤ k) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    fderiv ℝ (groundC k) ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) (Complex.exp ((θ : ℂ) * I))
      = ((gD k r : ℝ) : ℂ) := by
  have hk1 : 1 ≤ k := by omega
  have hC1 : ContDiff ℝ 1 (groundC k) := (contDiff_groundC k).of_le one_le_infty
  have h1 := hasDerivAt_comp_lineMul hC1 (Complex.exp ((θ : ℂ) * I)) r
  have hbase : HasDerivAt (fun y : ℝ => ((gRad k 0 y : ℝ) : ℂ)) ((gD k r : ℝ) : ℂ) r := by
    have h := (Complex.ofRealCLM.hasFDerivAt (x := gRad k 0 r)).comp_hasDerivAt r
      (gRad_hasDerivAt hk2 0 r)
    simpa [Function.comp_def] using h
  have hev : (fun y : ℝ => groundC k ((y : ℂ) * Complex.exp ((θ : ℂ) * I)))
      =ᶠ[nhds r] (fun y => ((gRad k 0 y : ℝ) : ℂ)) := by
    refine Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hr) (fun y hy => ?_)
    simp only [groundC]
    rw [groundR_eq hk1, norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy]
  have h2 : HasDerivAt (fun y : ℝ => groundC k ((y : ℂ) * Complex.exp ((θ : ℂ) * I)))
      ((gD k r : ℝ) : ℂ) r := hbase.congr_of_eventuallyEq hev
  exact h1.unique h2

/-- **Tangential derivative of the ground state vanishes**: the slice `θ' ↦ groundC k (r e^{iθ'})`
is constant (radial), so its `θ`-derivative — the tangential directional derivative — is `0`. -/
lemma fderiv_groundC_tangential (hk2 : 2 ≤ k) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    fderiv ℝ (groundC k) ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) (Complex.exp ((θ : ℂ) * I) * I)
      = 0 := by
  have hk1 : 1 ≤ k := by omega
  have hC1 : ContDiff ℝ 1 (groundC k) := (contDiff_groundC k).of_le one_le_infty
  have hslice := hasDerivAt_sliceθ hC1 r θ
  have hconst : HasDerivAt (slice (groundC k) r) 0 θ := by
    have heqf : slice (groundC k) r = fun _ => ((gRad k 0 |r| : ℝ) : ℂ) := by
      funext θ'
      simp only [slice, groundC]
      rw [groundR_eq hk1, norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [heqf]; exact hasDerivAt_const θ _
  have heq := hslice.unique hconst
  rw [show (r : ℂ) * (Complex.exp ((θ : ℂ) * I) * I)
      = (r : ℝ) • (Complex.exp ((θ : ℂ) * I) * I) from (Complex.real_smul ..).symm, map_smul] at heq
  rcases smul_eq_zero.mp heq with h | h
  · exact absurd h hr
  · exact h

/-- **The gradient cross density against a radial ground state.**  For `r > 0` and any `V`,
`gradInner (groundC k) V (r e^{iθ}) = gD(r) · fderiv V (r e^{iθ}) (e^{iθ})` — the tangential term
drops out. -/
lemma gradInner_groundC_polar (hk2 : 2 ≤ k) {r : ℝ} (hr : 0 < r) (θ : ℝ) (V : ℂ → ℂ) :
    gradInner (groundC k) V ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
      = ((gD k r : ℝ) : ℂ)
        * fderiv ℝ V ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) (Complex.exp ((θ : ℂ) * I)) := by
  rw [gradInner, basis_rot (fderiv ℝ (groundC k) ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))
      (fderiv ℝ V ((r : ℂ) * Complex.exp ((θ : ℂ) * I))) (norm_exp_I_mul θ), mul_one,
    fderiv_groundC_radial hk2 hr θ, fderiv_groundC_tangential hk2 hr.ne' θ]
  simp only [Complex.conj_ofReal, map_zero, zero_mul, add_zero]

/-! ### The real trace and its radial derivative -/

/-- The real `ℓ = 0` boundary/circle trace of `cutSlitC` at radius `r`. -/
def muT (k : ℕ) (δ c : ℝ) (r : ℝ) : ℝ := (Fm (cutSlitC k δ c) 0 r).re

/-- The real radial derivative of the `ℓ = 0` trace. -/
def muDT (k : ℕ) (δ c : ℝ) (r : ℝ) : ℝ := (FmD (cutSlitC k δ c) 0 r).re

/-- The real radial directional derivative of the cut-off at `r e^{iθ}`. -/
def dRcut (k : ℕ) (δ c : ℝ) (r θ : ℝ) : ℝ :=
  fderiv ℝ (cutSlit k δ c) ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) (Complex.exp ((θ : ℂ) * I))

/-- The real gradient cross density of `(groundR, cutSlit)`. -/
def HgrT (k : ℕ) (δ c : ℝ) (w : ℂ) : ℝ :=
  (fderiv ℝ (groundR k) w 1) * (fderiv ℝ (cutSlit k δ c) w 1)
    + (fderiv ℝ (groundR k) w I) * (fderiv ℝ (cutSlit k δ c) w I)

/-- The real potential cross density. -/
def PpotT (k : ℕ) (δ c : ℝ) (w : ℂ) : ℝ := potV k w * groundR k w * cutSlit k δ c w

lemma muT_one (k : ℕ) (δ c : ℝ) : muT k δ c 1 = nuSlit k δ c := by
  rw [muT, Fm_cutSlitC_zero_one, Complex.ofReal_re]

/-- The `ℓ = 0` mode of `cutSlitC` is `ofReal` of `μ`; hence `∫₀^{2π} cutSlit = 2π μ`. -/
lemma intR_cutSlit (r : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, cutSlit k δ c ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
      = 2 * π * muT k δ c r := by
  have hslice : (fun θ : ℝ => slice (cutSlitC k δ c) r θ)
      = fun θ : ℝ => ((cutSlit k δ c ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) : ℝ) : ℂ) := by
    funext θ; simp only [slice, cutSlitC]
  have hFm : Fm (cutSlitC k δ c) 0 r
      = (((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
          cutSlit k δ c ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) : ℝ) : ℂ) := by
    unfold Fm fc
    simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [hslice, intervalIntegral.integral_ofReal]
    push_cast; ring
  have hmu : muT k δ c r
      = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
          cutSlit k δ c ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
    rw [muT, hFm, Complex.ofReal_re]
  rw [hmu, ← mul_assoc, mul_inv_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0), one_mul]

/-- The `ℓ = 0` mode of the radial-derivative field is `ofReal` of `μ'`; hence
`∫₀^{2π} ∂_r cutSlit = 2π μ'`. -/
lemma intR_dRcut (r : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, dRcut k δ c r θ = 2 * π * muDT k δ c r := by
  have hint : (fun θ : ℝ => fderiv ℝ (cutSlitC k δ c) ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
        (Complex.exp ((θ : ℂ) * I)))
      = fun θ : ℝ => ((dRcut k δ c r θ : ℝ) : ℂ) := by
    funext θ; rw [fderiv_cutSlitC_apply]; rfl
  have hFmD : FmD (cutSlitC k δ c) 0 r
      = (((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, dRcut k δ c r θ : ℝ) : ℂ) := by
    unfold FmD fc
    simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [hint, intervalIntegral.integral_ofReal]
    push_cast; ring
  have hmu : muDT k δ c r
      = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, dRcut k δ c r θ := by
    rw [muDT, hFmD, Complex.ofReal_re]
  rw [hmu, ← mul_assoc, mul_inv_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0), one_mul]

/-! ### The pointwise real cross densities in polar form -/

/-- `gradInner (groundC)(cutSlitC)` is `ofReal` of the real gradient cross density. -/
lemma gradInner_gc_apply (w : ℂ) :
    gradInner (groundC k) (cutSlitC k δ c) w = ((HgrT k δ c w : ℝ) : ℂ) := by
  have hg : DifferentiableAt ℝ (groundR k) w :=
    ((contDiff_groundR k).differentiable (by simp)).differentiableAt
  have hs : DifferentiableAt ℝ (cutSlit k δ c) w :=
    ((contDiff_cutSlit k δ c).differentiable (by simp)).differentiableAt
  unfold gradInner groundC cutSlitC
  rw [fderiv_ofRealComp_apply hg 1, fderiv_ofRealComp_apply hs 1,
    fderiv_ofRealComp_apply hg I, fderiv_ofRealComp_apply hs I]
  simp only [Complex.conj_ofReal]
  unfold HgrT
  push_cast; ring

/-- The polar value of the real gradient cross density (for `r > 0`): `HgrT (r e^{iθ}) = gD(r) ·
∂_r cutSlit`. -/
lemma HgrT_polar (hk2 : 2 ≤ k) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    HgrT k δ c ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) = gD k r * dRcut k δ c r θ := by
  have h1 : ((HgrT k δ c ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) : ℝ) : ℂ)
      = ((gD k r * dRcut k δ c r θ : ℝ) : ℂ) := by
    rw [← gradInner_gc_apply, gradInner_groundC_polar hk2 hr θ (cutSlitC k δ c),
      fderiv_cutSlitC_apply]
    push_cast; rfl
  exact_mod_cast h1

/-- The polar value of the real potential cross density: `PpotT (r e^{iθ}) = Vrad(r)·gRad(r)·
cutSlit`. -/
lemma PpotT_polar (hk2 : 2 ≤ k) {r : ℝ} (hr0 : 0 ≤ r) (θ : ℝ) :
    PpotT k δ c ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
      = Vrad k r * gRad k 0 r * cutSlit k δ c ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
  have hnorm : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * I)‖ = r := by
    rw [norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  unfold PpotT
  rw [potV_eq_Vrad, groundR_eq (show (1 : ℕ) ≤ k by omega)]
  simp only [hnorm]

/-! ### The polar reduction of the two disk integrals -/

/-- Continuity of the real gradient cross density. -/
lemma continuous_HgrT : Continuous (HgrT k δ c) := by
  have hgR : Continuous (fun w => fderiv ℝ (groundR k) w) :=
    (contDiff_groundR k).continuous_fderiv (by simp)
  have hcS : Continuous (fun w => fderiv ℝ (cutSlit k δ c) w) :=
    (contDiff_cutSlit k δ c).continuous_fderiv (by simp)
  unfold HgrT
  exact ((hgR.clm_apply continuous_const).mul (hcS.clm_apply continuous_const)).add
    ((hgR.clm_apply continuous_const).mul (hcS.clm_apply continuous_const))

/-- Continuity of the real potential cross density. -/
lemma continuous_PpotT : Continuous (PpotT k δ c) := by
  have hpot : Continuous (potV k) := by
    have : potV k = fun w => Vrad k ‖w‖ := funext fun w => potV_eq_Vrad k w
    rw [this]; exact (continuous_Vrad k).comp continuous_norm
  unfold PpotT
  exact (hpot.mul (contDiff_groundR k).continuous).mul (contDiff_cutSlit k δ c).continuous

/-- **Polar reduction of the gradient term.**  `∫_D gradInner f₀ v = 2π ∫₀¹ r g' μ' dr`. -/
lemma Bd_grad_polar (hk2 : 2 ≤ k) :
    (∫ w in disk, gradInner (groundC k) (cutSlitC k δ c) w)
      = ((2 * π * ∫ r in (0 : ℝ)..1, r * gD k r * muDT k δ c r : ℝ) : ℂ) := by
  have hReal : (∫ w in disk, HgrT k δ c w)
      = 2 * π * ∫ r in (0 : ℝ)..1, r * gD k r * muDT k δ c r := by
    rw [show (disk : Set ℂ) = Metric.ball (0 : ℂ) 1 from rfl,
      setIntegral_ball_polar continuous_HgrT, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun r hr => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hr
    rcases eq_or_lt_of_le hr.1 with h0 | hpos
    · simp [← h0]
    · calc ∫ θ in (0 : ℝ)..2 * π, r * HgrT k δ c ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
          = ∫ θ in (0 : ℝ)..2 * π, (r * gD k r) * dRcut k δ c r θ :=
            intervalIntegral.integral_congr (fun θ _ => by rw [HgrT_polar hk2 hpos θ]; ring)
        _ = (r * gD k r) * ∫ θ in (0 : ℝ)..2 * π, dRcut k δ c r θ := by
            rw [intervalIntegral.integral_const_mul]
        _ = (r * gD k r) * (2 * π * muDT k δ c r) := by rw [intR_dRcut]
        _ = 2 * π * (r * gD k r * muDT k δ c r) := by ring
  have hcongr : (∫ w in disk, gradInner (groundC k) (cutSlitC k δ c) w)
      = ∫ w in disk, ((HgrT k δ c w : ℝ) : ℂ) :=
    setIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun w _ => gradInner_gc_apply w)
  have h2 : (∫ w in disk, ((HgrT k δ c w : ℝ) : ℂ))
      = ((∫ w in disk, HgrT k δ c w : ℝ) : ℂ) := integral_ofReal
  rw [hcongr, h2, hReal]

/-- **Polar reduction of the potential term.**  `∫_D V conj(f₀) v = 2π ∫₀¹ r V g μ dr`. -/
lemma Bd_pot_polar (hk2 : 2 ≤ k) :
    (∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (groundC k w) * cutSlitC k δ c w)
      = ((2 * π * ∫ r in (0 : ℝ)..1, r * Vrad k r * gRad k 0 r * muT k δ c r : ℝ) : ℂ) := by
  have hReal : (∫ w in disk, PpotT k δ c w)
      = 2 * π * ∫ r in (0 : ℝ)..1, r * Vrad k r * gRad k 0 r * muT k δ c r := by
    rw [show (disk : Set ℂ) = Metric.ball (0 : ℂ) 1 from rfl,
      setIntegral_ball_polar continuous_PpotT, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun r hr => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hr
    calc ∫ θ in (0 : ℝ)..2 * π, r * PpotT k δ c ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
        = ∫ θ in (0 : ℝ)..2 * π,
            (r * Vrad k r * gRad k 0 r) * cutSlit k δ c ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
          intervalIntegral.integral_congr (fun θ _ => by rw [PpotT_polar hk2 hr.1 θ]; ring)
      _ = (r * Vrad k r * gRad k 0 r)
            * ∫ θ in (0 : ℝ)..2 * π, cutSlit k δ c ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
          rw [intervalIntegral.integral_const_mul]
      _ = (r * Vrad k r * gRad k 0 r) * (2 * π * muT k δ c r) := by rw [intR_cutSlit]
      _ = 2 * π * (r * Vrad k r * gRad k 0 r * muT k δ c r) := by ring
  have hcongr : (∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (groundC k w) * cutSlitC k δ c w)
      = ∫ w in disk, ((PpotT k δ c w : ℝ) : ℂ) := by
    refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun w _ => ?_)
    simp only [groundC, cutSlitC, Complex.conj_ofReal, PpotT]
    push_cast; ring
  have h2 : (∫ w in disk, ((PpotT k δ c w : ℝ) : ℂ))
      = ((∫ w in disk, PpotT k δ c w : ℝ) : ℂ) := integral_ofReal
  rw [hcongr, h2, hReal]

/-! ### The cross pairing -/

/-- On the open disk, `vSlitC` agrees with the globally smooth `cutSlitC`, so their `Bd`-pairings
against the ground state coincide (`fderiv` is local). -/
lemma Bd_vSlitC_eq_cutSlitC (k : ℕ) (δ c : ℝ) :
    ModeDiag.Bd k (groundC k) (vSlitC k δ c) = ModeDiag.Bd k (groundC k) (cutSlitC k δ c) := by
  unfold ModeDiag.Bd
  have hopen : IsOpen (disk : Set ℂ) := Metric.isOpen_ball
  congr 1
  · refine setIntegral_congr_fun hopen.measurableSet (fun w hw => ?_)
    have hev : vSlitC k δ c =ᶠ[nhds w] cutSlitC k δ c :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hw) (fun y hy => vSlitC_eq_of_mem hy)
    unfold gradInner
    rw [hev.fderiv_eq]
  · refine setIntegral_congr_fun hopen.measurableSet (fun w hw => ?_)
    rw [vSlitC_eq_of_mem hw]

/-- **The cross pairing (smooth form)**: `Bd(f₀, cutSlitC) = −2π κ² ν`. -/
theorem Bd_groundC_cutSlitC (hk2 : 2 ≤ k) (δ c : ℝ) :
    ModeDiag.Bd k (groundC k) (cutSlitC k δ c)
      = ((-(2 * π * kap k ^ 2) * nuSlit k δ c : ℝ) : ℂ) := by
  have hC1 : ContDiff ℝ 1 (cutSlitC k δ c) := (contDiff_cutSlitC k δ c).of_le one_le_infty
  have hgDc : Continuous (gD k) :=
    continuous_iff_continuousAt.mpr fun r => (gD_hasDerivAt hk2 r).continuousAt
  have hgc : Continuous (gRad k 0) :=
    continuous_iff_continuousAt.mpr fun r => (gRad_hasDerivAt hk2 0 r).continuousAt
  have hmuDc : Continuous (muDT k δ c) := Complex.continuous_re.comp (FmD_continuous hC1 0)
  have hmuc : Continuous (muT k δ c) := Complex.continuous_re.comp (Fm_continuous hC1.continuous 0)
  have hi1 : IntervalIntegrable (fun r => r * gD k r * muDT k δ c r) volume 0 1 :=
    ((continuous_id.mul hgDc).mul hmuDc).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun r => r * Vrad k r * gRad k 0 r * muT k δ c r) volume 0 1 :=
    (((continuous_id.mul (continuous_Vrad k)).mul hgc).mul hmuc).intervalIntegrable 0 1
  rw [ModeDiag.Bd, Bd_grad_polar hk2, Bd_pot_polar hk2, ← Complex.ofReal_sub]
  congr 1
  have hcross := cross_ftc' (u := muT k δ c) (u' := muDT k δ c) hk2
    (fun r _ => hasDerivAt_re (Fm_hasDerivAt hC1 0 r)) hmuDc.continuousOn
  rw [muT_one] at hcross
  rw [← mul_sub, ← intervalIntegral.integral_sub hi1 hi2, hcross]
  ring

/-- The class-zero mixed cross pairing: `Bd(f₀, vSlitC) = −2π κ² ν`, where
`ν = nuSlit k δ c`. The identity holds for arbitrary real cutoff parameters;
positivity of `ν` requires the separate hypotheses of `nuSlit_pos`. -/
theorem Bd_groundC_vSlitC (hk2 : 2 ≤ k) (δ c : ℝ) :
    ModeDiag.Bd k (groundC k) (vSlitC k δ c)
      = ((-(2 * π * kap k ^ 2) * nuSlit k δ c : ℝ) : ℂ) := by
  rw [Bd_vSlitC_eq_cutSlitC, Bd_groundC_cutSlitC hk2]

end KsIndex.SingleDisk
