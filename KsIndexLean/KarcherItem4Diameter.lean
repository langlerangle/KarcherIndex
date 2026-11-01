module

public import KsIndexLean.KarcherCenteredChartGeometry
public import KsIndexLean.KarcherRealSymmetries
public import KsIndexLean.KarcherRealConjugation
public import KsIndexLean.KarcherHalfPeriodBoundary

@[expose] public section


/-!
# The distinguished midplane diameter

For `k ≥ 2` and a `PaperHalfPeriodRealization k`, `ewcover_item4_diameter`
identifies the parameter image of the centered immersion's intersection with
`P^{π/(2k)}` at normalized height `π/2`: it is exactly the open unit-disk
diameter at angle `−π/(2k)`, represented by finite parameters.

On a midplane ray `w = r exp(iβ)`, where `cos(kβ) = 0` and `0 ≤ r < 1`,
the real Weierstrass differential has horizontal radial speed
`lambdaR k r = k(1+r^(2k−2))/(1−r^(2k))` and zero vertical component.
Integrating gives horizontal displacement `bigL k r · (cos β, −sin β)`.
Rotation symmetry fixes the horizontal center over parameter zero; positivity
of `bigL` and the height characterization then give both image inclusions.
The result is stated on the intrinsic lift and uses its centered ambient map.
-/
noncomputable section
namespace KsIndex.KarcherData
open Complex

/-- Radial speed of the horizontal EW position along a midplane ray. -/
def lambdaR (k : ℕ) (r : ℝ) : ℝ := (k : ℝ) * (1 + r ^ (2 * k - 2)) / (1 - r ^ (2 * k))

/-- At a midplane angle (`cos kβ = 0`), `exp(2kβ·I) = -1`. -/
lemma exp_two_mul_k_beta (k : ℕ) {β : ℝ} (hkβ : Real.cos ((k : ℝ) * β) = 0) :
    Complex.exp (((2 * (k : ℝ) * β : ℝ) : ℂ) * I) = -1 := by
  have hcos : Real.cos (2 * ((k : ℝ) * β)) = -1 := by rw [Real.cos_two_mul, hkβ]; ring
  have hsin : Real.sin (2 * ((k : ℝ) * β)) = 0 := by rw [Real.sin_two_mul, hkβ]; ring
  have he : Complex.exp (((2 * ((k : ℝ) * β) : ℝ) : ℂ) * I)
      = (Real.cos (2 * ((k : ℝ) * β)) : ℂ) + (Real.sin (2 * ((k : ℝ) * β)) : ℂ) * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [show (2 * (k : ℝ) * β : ℝ) = 2 * ((k : ℝ) * β) from by ring, he, hcos, hsin]
  push_cast; ring

/-- On a midplane ray `w = r e^{iβ}` (`cos kβ = 0`), `w^{2k} = -(r^{2k})` (real, ≤ 0). -/
lemma midplane_pow_two_k {k : ℕ} {r β : ℝ} (hkβ : Real.cos ((k : ℝ) * β) = 0) :
    ((r : ℂ) * Complex.exp ((β : ℂ) * I)) ^ (2 * k) = -((r : ℂ) ^ (2 * k)) := by
  rw [mul_pow, ← Complex.exp_nat_mul]
  have : (↑(2 * k) : ℂ) * ((β : ℂ) * I) = ((2 * (k : ℝ) * β : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, exp_two_mul_k_beta k hkβ, mul_neg_one]

/-- **The midplane radial derivative.** On a midplane ray `w = r e^{iβ}` (`cos kβ = 0`,
`0≤r<1`), the EW real differential sends the radial direction `e^{iβ}` to `λ(r)(cos β, -sin β)` with
zero vertical part. Direct Weierstrass-coefficient algebra. -/
lemma ewRealDifferential_midplane_radial {k : ℕ} (hk : 2 ≤ k) {r β : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hkβ : Real.cos ((k : ℝ) * β) = 0) :
    ewRealDifferential k ((r : ℂ) * Complex.exp ((β : ℂ) * I)) (Complex.exp ((β : ℂ) * I))
      = (lambdaR k r * Real.cos β, -(lambdaR k r) * Real.sin β, 0) := by
  set e : ℂ := Complex.exp ((β : ℂ) * I) with he_def
  have hene : e ≠ 0 := Complex.exp_ne_zero _
  have hk1 : 1 ≤ k := by omega
  -- e^k = sin(kβ)·I   (cos kβ = 0)
  have hek : e ^ k = (Real.sin ((k : ℝ) * β) : ℂ) * I := by
    rw [he_def, ← Complex.exp_nat_mul,
      show (↑k : ℂ) * ((β : ℂ) * I) = (((k : ℝ) * β : ℝ) : ℂ) * I from by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hkβ]
    push_cast; ring
  -- e^(2k) = -1
  have he2k : e ^ (2 * k) = -1 := by
    rw [he_def, ← Complex.exp_nat_mul,
      show (↑(2 * k) : ℂ) * ((β : ℂ) * I) = ((2 * (k : ℝ) * β : ℝ) : ℂ) * I from by push_cast; ring,
      exp_two_mul_k_beta k hkβ]
  -- e^(2k-1) = -e⁻¹
  have he2k1 : e ^ (2 * k - 1) = -e⁻¹ := by
    have hmul : e ^ (2 * k - 1) * e = e ^ (2 * k) := by
      rw [← pow_succ]; congr 1; omega
    rw [he2k] at hmul
    field_simp at hmul ⊢
    linear_combination hmul
  -- real nonzero denominator
  have hden : (1 : ℝ) - r ^ (2 * k) ≠ 0 := by
    have hlt : r ^ (2 * k) < 1 := pow_lt_one₀ hr0 hr1 (by omega)
    linarith
  -- η = k/(1 - r^(2k))  (real)
  have hw2k : ((r : ℂ) * e) ^ (2 * k) = -((r : ℂ) ^ (2 * k)) := by
    rw [he_def]; exact midplane_pow_two_k hkβ
  have hη : etaTarget k ((r : ℂ) * e) = ((k : ℝ) / (1 - r ^ (2 * k)) : ℝ) := by
    rw [etaTarget, hw2k]
    rw [show (1 : ℂ) + -((r : ℂ) ^ (2 * k)) = ((1 - r ^ (2 * k) : ℝ) : ℂ) from by push_cast; ring]
    push_cast; ring
  -- g·e = r^(k-1) sin(kβ) · I   (purely imaginary)
  have hge : gauss k ((r : ℂ) * e) * e = ((r : ℝ) ^ (k - 1) * Real.sin ((k : ℝ) * β) : ℝ) * I := by
    rw [gauss, mul_pow, mul_assoc, ← pow_succ, show k - 1 + 1 = k from by omega, hek]
    push_cast; ring
  -- g²·e = -(r^(2k-2)) · e⁻¹
  have hg2e : (gauss k ((r : ℂ) * e)) ^ 2 * e = -((r ^ (2 * k - 2) : ℝ) : ℂ) * e⁻¹ := by
    rw [gauss, ← pow_mul, mul_pow, mul_assoc, ← pow_succ,
      show (k - 1) * 2 + 1 = 2 * k - 1 from by omega, he2k1,
      show (k - 1) * 2 = 2 * k - 2 from by omega]
    push_cast; ring
  -- reduce the differential to the three real parts
  rw [ewRealDifferential, ContinuousLinearMap.prod_apply, ContinuousLinearMap.prod_apply,
    realCoeffLinear_apply, realCoeffLinear_apply, realCoeffLinear_apply]
  -- coeff_j = phi_j (gauss, etaTarget)
  simp only [coeff1, coeff2, coeff3, Weierstrass.phi1, Weierstrass.phi2, Weierstrass.phi3]
  have hecos : e.re = Real.cos β := by rw [he_def, Complex.exp_ofReal_mul_I_re]
  have hesin : e.im = Real.sin β := by rw [he_def, Complex.exp_ofReal_mul_I_im]
  have heinv : e⁻¹ = (Real.cos β : ℂ) - (Real.sin β : ℂ) * I := by
    rw [he_def, ← Complex.exp_neg,
      show -((β : ℂ) * I) = ((-β : ℝ) : ℂ) * I from by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- x : Re(e·(1-g²)·η) = λ cos β
    change (e * ((1 - gauss k ((r:ℂ)*e) ^ 2) * etaTarget k ((r:ℂ)*e))).re = lambdaR k r * Real.cos β
    rw [show e * ((1 - gauss k ((r:ℂ)*e) ^ 2) * etaTarget k ((r:ℂ)*e))
        = etaTarget k ((r:ℂ)*e) * (e - gauss k ((r:ℂ)*e) ^ 2 * e) from by ring,
      hg2e, hη, heinv]
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.sub_im, hecos, hesin]
    unfold lambdaR
    field_simp
    ring
  · -- y : Re(e·i·(1+g²)·η) = -λ sin β
    change (e * (I * (1 + gauss k ((r:ℂ)*e) ^ 2) * etaTarget k ((r:ℂ)*e))).re
      = -(lambdaR k r) * Real.sin β
    rw [show e * (I * (1 + gauss k ((r:ℂ)*e) ^ 2) * etaTarget k ((r:ℂ)*e))
        = etaTarget k ((r:ℂ)*e) * I * (e + gauss k ((r:ℂ)*e) ^ 2 * e) from by ring,
      hg2e, hη, heinv]
    simp only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.sub_im, hecos, hesin]
    unfold lambdaR
    field_simp
    ring
  · -- z : Re(e·2·g·η) = 0
    change (e * (2 * gauss k ((r:ℂ)*e) * etaTarget k ((r:ℂ)*e))).re = 0
    rw [show e * (2 * gauss k ((r:ℂ)*e) * etaTarget k ((r:ℂ)*e))
        = etaTarget k ((r:ℂ)*e) * 2 * (gauss k ((r:ℂ)*e) * e) from by ring, hge, hη]
    simp only [Complex.ofReal_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, zero_mul, mul_one, sub_zero, add_zero]

/-- `exp(-2π/k · I) ≠ 1` for `k ≥ 2` (the rotation is nontrivial). -/
lemma rotation_root_ne_one {k : ℕ} (hk : 2 ≤ k) :
    Complex.exp ((-2 * Real.pi / k : ℝ) * I) ≠ 1 := by
  intro hcontra
  rw [Complex.exp_eq_one_iff] at hcontra
  obtain ⟨n, hn⟩ := hcontra
  rw [show (↑n : ℂ) * (2 * ↑Real.pi * I) = (2 * ↑Real.pi * ↑n) * I from by ring] at hn
  have hI : ((-2 * Real.pi / k : ℝ) : ℂ) = 2 * ↑Real.pi * ↑n :=
    mul_right_cancel₀ Complex.I_ne_zero hn
  have hr : (-2 * Real.pi / k : ℝ) = 2 * Real.pi * n := by exact_mod_cast hI
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hk0 : (0 : ℝ) < k := by positivity
  have hkn : (k : ℝ) * n = -1 := by field_simp at hr; nlinarith [hr]
  have : (k : ℤ) * n = -1 := by exact_mod_cast hkn
  have hdvd : (k : ℤ) ∣ 1 := ⟨-n, by linarith [this]⟩
  have := Int.le_of_dvd (by norm_num) hdvd
  omega

/-- **The fibre over `w = 0` sits on the horizontal origin.** Its centered horizontal
coordinate is `(0,0)`: `w=0` is fixed by the (nontrivial) full rotation, and the centered
rotation acts as `rotate (exp(-2πi/k))` on the horizontal. -/
lemma centeredLiftAmbient_fibre_zero {k : ℕ} [h : Fact (2 ≤ k)]
    (R : PaperHalfPeriodRealization k) (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = finiteParameter ⟨0, zero_not_puncture h.out⟩) :
    (centeredLiftAmbient R.C R.t q).1 = 0 ∧ (centeredLiftAmbient R.C R.t q).2.1 = 0 := by
  have hfix : R.rotationLift q = q := by
    apply Subtype.ext
    refine Prod.ext ?_ (R.rotationLift_height q)
    change HeightLift.projection (R.rotationLift q) = HeightLift.projection q
    rw [R.rotationLift_projection, hq,
      parameterRotation_finite _ _ ⟨0, zero_not_puncture h.out⟩]
    congr 1
    exact Subtype.ext (by simp)
  have hamb := R.rotationLift_ambient q
  rw [hfix] at hamb
  set a : ℂ := Complex.exp ((-2 * Real.pi / k : ℝ) * Complex.I) with ha_def
  set p : PeriodTarget := projectPeriod (centeredLiftAmbient R.C R.t q) with hp_def
  have hxp : (centeredLiftAmbient R.C R.t q).1 = p.1 := by simp [hp_def, projectPeriod]
  have hyp : (centeredLiftAmbient R.C R.t q).2.1 = p.2.1 := by simp [hp_def, projectPeriod]
  have hfixp : p = PeriodTarget.rotate a p := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · have := congrArg (fun v : AmbientTriple => v.1) hamb; rw [← hxp]; simpa [hp_def] using this
    · have := congrArg (fun v : AmbientTriple => v.2.1) hamb; rw [← hyp]; simpa [hp_def] using this
    · simp [PeriodTarget.rotate]
  have hhoriz : horizC p = a⁻¹ * horizC p := by
    conv_lhs => rw [hfixp]
    rw [horizC_rotate]
  have hzero : horizC p = 0 := by
    have h2 : (1 - a⁻¹) * horizC p = 0 := by linear_combination hhoriz
    rcases mul_eq_zero.mp h2 with hsub | hz
    · exact absurd (sub_eq_zero.mp hsub).symm (by
        rw [inv_eq_one]; exact rotation_root_ne_one h.out)
    · exact hz
  obtain ⟨hx0, hy0⟩ := periodTarget_horiz_eq_zero hzero
  exact ⟨hxp.trans hx0, hyp.trans hy0⟩

/-- Points strictly inside the unit disk are not punctures (punctures lie on `|w| = 1`). -/
lemma disk_not_puncture {k : ℕ} {w : ℂ} (hw : ‖w‖ < 1) : w ∉ Surface.punctures k := by
  intro hp
  have hpe : w ^ (2 * k) = -1 := hp
  have h1 : ‖w‖ ^ (2 * k) = 1 := by
    have h := congrArg norm hpe; rwa [norm_pow, norm_neg, norm_one] at h
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, Nat.mul_zero, pow_zero] at hpe
    exact absurd hpe (by norm_num)
  · have hlt : ‖w‖ ^ (2 * k) < 1 := pow_lt_one₀ (norm_nonneg w) hw (by omega)
    linarith

/-- Radial horizontal arc length `L(r) = ∫₀ʳ λ`. -/
def bigL (k : ℕ) (r : ℝ) : ℝ := ∫ s in (0:ℝ)..r, lambdaR k s

/-- The radial speed `λ` is strictly positive on `[0,1)`. -/
lemma lambdaR_pos {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) : 0 < lambdaR k s := by
  have hden : 0 < 1 - s ^ (2 * k) := by
    have : s ^ (2 * k) < 1 := pow_lt_one₀ hs0 hs1 (by omega)
    linarith
  have hnum : 0 < (k : ℝ) * (1 + s ^ (2 * k - 2)) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hpn : (0 : ℝ) ≤ s ^ (2 * k - 2) := pow_nonneg hs0 _
    exact mul_pos hk0 (by linarith)
  exact div_pos hnum hden

/-- `λ` is continuous on `[0,r]` for `r < 1` (the denominator stays positive). -/
lemma lambdaR_continuousOn {k : ℕ} (hk : 2 ≤ k) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (lambdaR k) (Set.uIcc 0 r) := by
  rw [Set.uIcc_of_le hr0]
  apply ContinuousOn.div
  · exact (continuous_const.mul (continuous_const.add (continuous_pow _))).continuousOn
  · exact (continuous_const.sub (continuous_pow _)).continuousOn
  · intro s hs
    have hs1' : s < 1 := lt_of_le_of_lt hs.2 hr1
    have : s ^ (2 * k) < 1 := pow_lt_one₀ hs.1 hs1' (by omega)
    linarith

/-- `L(r) > 0` for `0 < r < 1`. -/
lemma bigL_pos {k : ℕ} (hk : 2 ≤ k) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : 0 < bigL k r := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (lambdaR_continuousOn hk hr0.le hr1).intervalIntegrable
  · intro s hs
    exact lambdaR_pos hk hs.1.le (lt_trans hs.2 hr1)
  · exact hr0

/-- **Radial horizontal displacement.** Along a midplane ray `w = r e^{iβ}` (`cos kβ = 0`,
`0 ≤ r < 1`), the horizontal part of the EW integral displacement from `w = 0` is
`L(r) (cos β, -sin β)`. Pure statement about `descendedIntegral`; the additive center is handled by
`centeredLiftAmbient_fibre_zero` below. Proof: primitives on the open unit disk (`isExactOn_ball`), then the
real fundamental theorem of calculus per component with `ewRealDifferential_midplane_radial`. -/
lemma descendedIntegral_midplane_horizontal {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k)
    {r β : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hkβ : Real.cos ((k : ℝ) * β) = 0)
    (w w0 : PuncturedPlane k) (hw : w.val = (r : ℂ) * Complex.exp ((β : ℂ) * I))
    (hw0 : w0.val = 0) :
    (descendedIntegral hk b w).1 - (descendedIntegral hk b w0).1 = bigL k r * Real.cos β ∧
    (descendedIntegral hk b w).2.1 - (descendedIntegral hk b w0).2.1
      = -(bigL k r) * Real.sin β := by
  set e : ℂ := Complex.exp ((β : ℂ) * I) with he_def
  have hene : ‖e‖ = 1 := by rw [he_def]; exact Complex.norm_exp_ofReal_mul_I β
  -- primitives of the three coefficients on the whole open unit disk
  have havoid : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ∉ Surface.punctures k := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact disk_not_puncture hz
  have hd₁ : DifferentiableOn ℂ (coeff1 k) (Metric.ball 0 1) :=
    fun z hz => (differentiableAt_coeff1 (havoid z hz)).differentiableWithinAt
  have hd₂ : DifferentiableOn ℂ (coeff2 k) (Metric.ball 0 1) :=
    fun z hz => (differentiableAt_coeff2 (havoid z hz)).differentiableWithinAt
  have hd₃ : DifferentiableOn ℂ (coeff3 k) (Metric.ball 0 1) :=
    fun z hz => (differentiableAt_coeff3 (havoid z hz)).differentiableWithinAt
  obtain ⟨F₁, hF₁0, hdF₁⟩ := hd₁.isExactOn_ball.with_val_at (0 : ℂ) 0
  obtain ⟨F₂, hF₂0, hdF₂⟩ := hd₂.isExactOn_ball.with_val_at (0 : ℂ) 0
  obtain ⟨F₃, hF₃0, hdF₃⟩ := hd₃.isExactOn_ball.with_val_at (0 : ℂ) 0
  -- endpoints are in the disk
  have hw_mem : w.val ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, hw, norm_mul, hene, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr0]
    exact hr1
  have hw0_mem : w0.val ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, hw0]; simp
  -- local-primitive increment of the descended integral
  have hLP := descendedIntegral_eq_local_primitives hk b w0 w (convex_ball 0 1) havoid hw0_mem
    hw_mem F₁ F₂ F₃ hdF₁ hdF₂ hdF₃
  have e1 : (descendedIntegral hk b w).1
      = (descendedIntegral hk b w0).1 + (F₁ w.val - F₁ w0.val).re := by
    rw [hLP]; simp [projectPeriod]
  have e2 : (descendedIntegral hk b w).2.1
      = (descendedIntegral hk b w0).2.1 + (F₂ w.val - F₂ w0.val).re := by
    rw [hLP]; simp [projectPeriod]
  -- the per-component FTC along the ray
  have key1 : (F₁ w.val - F₁ w0.val).re = bigL k r * Real.cos β := by
    rw [Complex.sub_re, hw, hw0]
    have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) r,
        HasDerivAt (fun u : ℝ => (F₁ ((u : ℂ) * e)).re) (lambdaR k s * Real.cos β) s := by
      intro s hs
      rw [Set.uIcc_of_le hr0] at hs
      have hs0 : 0 ≤ s := hs.1
      have hs1 : s < 1 := lt_of_le_of_lt hs.2 hr1
      have hmem : (s : ℂ) * e ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, norm_mul, hene, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hs0]
        exact hs1
      have hray : HasDerivAt (fun u : ℝ => (u : ℂ) * e) e s := by
        simpa using Complex.ofRealCLM.hasDerivAt.mul_const e
      have hfd : HasFDerivAt (realPrimitive F₁ F₂ F₃)
          (ewRealDifferential k ((s : ℂ) * e)) ((s : ℂ) * e) :=
        hasFDerivAt_realPrimitive (hdF₁ _ hmem) (hdF₂ _ hmem) (hdF₃ _ hmem)
      have hcomp : HasDerivAt (fun u : ℝ => realPrimitive F₁ F₂ F₃ ((u : ℂ) * e))
          (ewRealDifferential k ((s : ℂ) * e) e) s := by
        simpa [Function.comp_def] using
          HasFDerivAt.comp_hasDerivAt (x := s) (f := fun u : ℝ => (u : ℂ) * e) hfd hray
      have hstep1 : ewRealDifferential k ((s : ℂ) * e) e
          = (lambdaR k s * Real.cos β, -(lambdaR k s) * Real.sin β, 0) := by
        rw [he_def]; exact ewRealDifferential_midplane_radial hk hs0 hs1 hkβ
      rw [hstep1] at hcomp
      exact (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt (x := s) hcomp
    have hint : IntervalIntegrable (fun s => lambdaR k s * Real.cos β) MeasureTheory.volume 0 r :=
      ((lambdaR_continuousOn hk hr0 hr1).mul continuousOn_const).intervalIntegrable
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simp only [Complex.ofReal_zero, zero_mul] at hftc
    rw [← hftc, intervalIntegral.integral_mul_const]
    rfl
  have key2 : (F₂ w.val - F₂ w0.val).re = -(bigL k r) * Real.sin β := by
    rw [Complex.sub_re, hw, hw0]
    have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) r,
        HasDerivAt (fun u : ℝ => (F₂ ((u : ℂ) * e)).re) (-(lambdaR k s) * Real.sin β) s := by
      intro s hs
      rw [Set.uIcc_of_le hr0] at hs
      have hs0 : 0 ≤ s := hs.1
      have hs1 : s < 1 := lt_of_le_of_lt hs.2 hr1
      have hmem : (s : ℂ) * e ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, norm_mul, hene, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hs0]
        exact hs1
      have hray : HasDerivAt (fun u : ℝ => (u : ℂ) * e) e s := by
        simpa using Complex.ofRealCLM.hasDerivAt.mul_const e
      have hfd : HasFDerivAt (realPrimitive F₁ F₂ F₃)
          (ewRealDifferential k ((s : ℂ) * e)) ((s : ℂ) * e) :=
        hasFDerivAt_realPrimitive (hdF₁ _ hmem) (hdF₂ _ hmem) (hdF₃ _ hmem)
      have hcomp : HasDerivAt (fun u : ℝ => realPrimitive F₁ F₂ F₃ ((u : ℂ) * e))
          (ewRealDifferential k ((s : ℂ) * e) e) s := by
        simpa [Function.comp_def] using
          HasFDerivAt.comp_hasDerivAt (x := s) (f := fun u : ℝ => (u : ℂ) * e) hfd hray
      have hstep1 : ewRealDifferential k ((s : ℂ) * e) e
          = (lambdaR k s * Real.cos β, -(lambdaR k s) * Real.sin β, 0) := by
        rw [he_def]; exact ewRealDifferential_midplane_radial hk hs0 hs1 hkβ
      rw [hstep1] at hcomp
      exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt.comp_hasDerivAt (x := s) hcomp
    have hint : IntervalIntegrable (fun s => -(lambdaR k s) * Real.sin β)
        MeasureTheory.volume 0 r :=
      (((lambdaR_continuousOn hk hr0 hr1).neg).mul continuousOn_const).intervalIntegrable
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simp only [Complex.ofReal_zero, zero_mul] at hftc
    rw [← hftc,
      show (fun s => -(lambdaR k s) * Real.sin β) = (fun s => lambdaR k s * (-Real.sin β)) from by
        funext s; ring,
      intervalIntegral.integral_mul_const]
    change bigL k r * (-Real.sin β) = -(bigL k r) * Real.sin β
    ring
  exact ⟨by rw [e1, key1]; ring, by rw [e2, key2]; ring⟩

/-- The centered ambient horizontal coordinates equal the center `R.t` plus the EW integral's
horizontal parts (for the `x`-coordinate; the `y`-coordinate has no center shift). -/
lemma centeredLiftAmbient_horiz_descended {k : ℕ} [h : Fact (2 ≤ k)]
    (R : PaperHalfPeriodRealization k) (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : HeightLift.projection q = finiteParameter w) :
    (centeredLiftAmbient R.C R.t q).1
        = R.t + (descendedIntegral h.out (reflectionBasepoint k) w).1 ∧
    (centeredLiftAmbient R.C R.t q).2.1
        = (descendedIntegral h.out (reflectionBasepoint k) w).2.1 := by
  refine ⟨?_, ?_⟩
  · change R.t + (HeightLift.ambient q).1 = _
    congr 1
    change (extendedEWMap h.out (reflectionBasepoint k) R.C (HeightLift.projection q)).1 = _
    rw [hq, extendedEWMap_finite]
  · change (HeightLift.ambient q).2.1 = _
    change (extendedEWMap h.out (reflectionBasepoint k) R.C (HeightLift.projection q)).2.1 = _
    rw [hq, extendedEWMap_finite]

/-- **Step 3 (bridge) — centered horizontal over a midplane ray.** For the actual centered
immersion, the horizontal coordinate over a midplane-ray parameter `w = r e^{iβ}`
(`cos kβ = 0`, `0 ≤ r < 1`) is `L(r) (cos β, -sin β)`. The `w=0` fibre pins the center,
and the `descendedIntegral` displacement supplies the radial length. -/
lemma centeredLiftAmbient_midplane_horizontal {k : ℕ} [h : Fact (2 ≤ k)]
    (R : PaperHalfPeriodRealization k) (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    {r β : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hkβ : Real.cos ((k : ℝ) * β) = 0)
    (w : PuncturedPlane k) (hw : w.val = (r : ℂ) * Complex.exp ((β : ℂ) * I))
    (hq : HeightLift.projection q = finiteParameter w) :
    (centeredLiftAmbient R.C R.t q).1 = bigL k r * Real.cos β ∧
    (centeredLiftAmbient R.C R.t q).2.1 = -(bigL k r) * Real.sin β := by
  set w0 : PuncturedPlane k := ⟨0, zero_not_puncture h.out⟩ with hw0def
  obtain ⟨q0, hq0⟩ :=
    exists_halfPeriod_over_disk h.out (reflectionBasepoint k) w0 rfl R.C (by simp [hw0def])
  obtain ⟨hz1, hz2⟩ := centeredLiftAmbient_fibre_zero R q0.val hq0
  obtain ⟨hq0_1, hq0_2⟩ := centeredLiftAmbient_horiz_descended R q0.val w0 hq0
  obtain ⟨hq_1, hq_2⟩ := centeredLiftAmbient_horiz_descended R q w hq
  rw [hq0_1] at hz1
  rw [hq0_2] at hz2
  obtain ⟨hA1, hA2⟩ :=
    descendedIntegral_midplane_horizontal h.out (reflectionBasepoint k) hr0 hr1 hkβ w w0 hw rfl
  refine ⟨?_, ?_⟩
  · rw [hq_1]; linarith [hz1, hA1]
  · rw [hq_2]; linarith [hz2, hA2]

/-- **Plane condition and angle.** For horizontal coordinates `(x, y) = (L cos β, -L sin β)`, the
asymptotic-plane condition `y cos θ = x sin θ` is equivalent to `L sin(β + θ) = 0`. -/
lemma plane_cond_iff {L β θ : ℝ} :
    -L * Real.sin β * Real.cos θ = L * Real.cos β * Real.sin θ ↔ L * Real.sin (β + θ) = 0 := by
  rw [Real.sin_add]
  constructor <;> intro h <;> linear_combination -h

/-- **Midplane height characterization.** On the `[0,π]` representative over a finite
parameter `w`, the normalized height `z = height q + π` equals `π/2` iff `w^k` is purely imaginary
(`(w^k).re = 0`) and `‖w‖ < 1` — the midplane slice. -/
lemma midplane_iff {k : ℕ} (hk : 2 ≤ k) (b w : PuncturedPlane k) (hb : b.val = 1)
    (C : PeriodTarget) (q : PeriodicEWCarrier hk b C)
    (hq : HeightLift.projection q = finiteParameter w)
    (hz : HeightLift.height q + Real.pi ∈ Set.Icc 0 Real.pi) :
    HeightLift.height q + Real.pi = Real.pi / 2 ↔ (w.val ^ k).re = 0 ∧ ‖w.val‖ < 1 := by
  have hcos := cos_lift_height_shift hk b w hb C q hq
  have hcayne : ‖heightCayley k w.val‖ ≠ 0 := norm_ne_zero_iff.mpr (heightCayley_ne_zero w.property)
  have hnsq : 0 < Complex.normSq (1 - I * w.val ^ k) :=
    Complex.normSq_pos.mpr (height_factors_ne w.property).2
  have hcos0 : Real.cos (HeightLift.height q + Real.pi) = 0 ↔ (w.val ^ k).re = 0 := by
    rw [hcos, div_eq_zero_iff]
    simp only [hcayne, or_false, neg_eq_zero]
    rw [heightCayley_im, div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact absurd h (ne_of_gt hnsq)
    · intro h; left; rw [h]; ring
  constructor
  · intro hzeq
    refine ⟨hcos0.mp (by rw [hzeq, Real.cos_pi_div_two]), ?_⟩
    have hsin : 0 < Real.sin (HeightLift.height q + Real.pi) := by
      rw [hzeq, Real.sin_pi_div_two]; norm_num
    exact (sin_lift_height_shift_pos_iff hk b w hb C q hq).mp hsin
  · rintro ⟨hre, _⟩
    have hcz : Real.cos (HeightLift.height q + Real.pi) = 0 := hcos0.mpr hre
    have hpi2 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
    have heq : Real.cos (HeightLift.height q + Real.pi) = Real.cos (Real.pi / 2) := by
      rw [hcz, Real.cos_pi_div_two]
    exact Real.strictAntiOn_cos.injOn hz hpi2 heq

/-- **Item (4) — the distinguished midplane diameter** (`ewcover` item (4), ksindexi.tex:1035–1040,
quoted from [Karcher]; here for `k ≥ 2`, extending the paper's `k ≥ 3` range).
`ewcover_k(P^{π/(2k)} ∩ {z = π/2}) = {t e^{-iπ/(2k)} : t ∈ (-1,1)}`: the parameter image of the
surface points on the asymptotic plane `P^{π/(2k)}` at the midplane height `z = π/2` is exactly the
open disk diameter at angle `-π/(2k)`. The surface point is our intrinsic lift `q`, its image is
`HeightLift.projection q`, and the ambient coordinates are the actual centered immersion
`centeredLiftAmbient`. This is an intrinsic immersion statement and does not use an embeddedness theorem. -/
theorem ewcover_item4_diameter {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k) :
    HeightLift.projection ''
        {q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C |
          (centeredLiftAmbient R.C R.t q).2.1 * Real.cos (Real.pi / (2 * (k : ℝ)))
            = (centeredLiftAmbient R.C R.t q).1 * Real.sin (Real.pi / (2 * (k : ℝ)))
          ∧ HeightLift.height q + Real.pi = Real.pi / 2}
      = finiteParameter '' {w : PuncturedPlane k |
          ∃ t : ℝ, -1 < t ∧ t < 1 ∧
            w.val = (t : ℂ) * Complex.exp ((-Real.pi / (2 * (k : ℝ)) : ℝ) * I)} := by
  have hkR : (0 : ℝ) < (k : ℝ) := by have := h.out; positivity
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  set θ : ℝ := Real.pi / (2 * (k : ℝ)) with hθdef
  have hkθ : (k : ℝ) * θ = Real.pi / 2 := by rw [hθdef]; field_simp
  have hcoskθ : Real.cos ((k : ℝ) * θ) = 0 := by rw [hkθ, Real.cos_pi_div_two]
  apply Set.Subset.antisymm
  · -- ⊆ : a surface point on the plane at z = π/2 maps to a diameter point
    rintro p ⟨q, ⟨hplane, hz⟩, rfl⟩
    have hsin1 : Real.sin (HeightLift.height q + Real.pi) = 1 := by rw [hz, Real.sin_pi_div_two]
    have hne : HeightLift.projection q ≠ infinityParameter k := by
      intro hi
      have := sin_lift_height_infinity R.C R.hC q hi
      rw [hsin1] at this; norm_num at this
    rcases parameterSphere_cases (HeightLift.projection q) with hi | ⟨w, hw⟩
    · exact absurd hi hne
    · have hq : HeightLift.projection q = finiteParameter w := hw.symm
      have hzIcc : HeightLift.height q + Real.pi ∈ Set.Icc 0 Real.pi := by
        rw [hz]; exact ⟨by positivity, by linarith [Real.pi_pos]⟩
      obtain ⟨hre, hnorm⟩ := (midplane_iff h.out (reflectionBasepoint k) w rfl R.C q hq hzIcc).mp hz
      refine ⟨w, ?_, hq.symm⟩
      rcases eq_or_ne w.val 0 with hw0 | hwne
      · exact ⟨0, by norm_num, by norm_num, by rw [hw0]; push_cast; ring⟩
      · set r : ℝ := ‖w.val‖ with hr
        set β : ℝ := Complex.arg w.val with hβ
        have hr0 : 0 < r := by rw [hr]; exact norm_pos_iff.mpr hwne
        have hrlt : r < 1 := hnorm
        have hwpolar : w.val = (r : ℂ) * Complex.exp ((β : ℂ) * I) :=
          (Complex.norm_mul_exp_arg_mul_I w.val).symm
        have hwkre : (w.val ^ k).re = r ^ k * Real.cos ((k : ℝ) * β) := by
          rw [hwpolar, mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul,
            show (↑k : ℂ) * ((β : ℂ) * I) = (((k : ℝ) * β : ℝ) : ℂ) * I from by push_cast; ring,
            Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
          ring
        have hkβ : Real.cos ((k : ℝ) * β) = 0 := by
          have hrk : (0 : ℝ) < r ^ k := by positivity
          rw [hwkre] at hre
          exact (mul_eq_zero.mp hre).resolve_left (ne_of_gt hrk)
        obtain ⟨hx, hy⟩ :=
          centeredLiftAmbient_midplane_horizontal R q hr0.le hrlt hkβ w hwpolar hq
        rw [hx, hy] at hplane
        have hsinbθ : bigL k r * Real.sin (β + θ) = 0 := plane_cond_iff.mp hplane
        have hL : 0 < bigL k r := bigL_pos h.out hr0 hrlt
        have hsin0 : Real.sin (β + θ) = 0 := (mul_eq_zero.mp hsinbθ).resolve_left (ne_of_gt hL)
        have hcosbθ : Real.cos (β + θ) = 1 ∨ Real.cos (β + θ) = -1 :=
          Real.sin_eq_zero_iff_cos_eq.mp hsin0
        have habs : |Real.cos (β + θ)| = 1 := by rcases hcosbθ with hc | hc <;> rw [hc] <;> norm_num
        have habst : |r * Real.cos (β + θ)| < 1 := by
          rw [abs_mul, habs, mul_one, abs_of_pos hr0]; exact hrlt
        have hwt : w.val
            = (↑(r * Real.cos (β + θ)) : ℂ) * Complex.exp ((-Real.pi / (2 * (k : ℝ)) : ℝ) * I) := by
          have hexpβ : Complex.exp ((β : ℂ) * I)
              = (↑(Real.cos (β + θ)) : ℂ) * Complex.exp ((-Real.pi / (2 * (k : ℝ)) : ℝ) * I) := by
            rw [show (β : ℂ) * I
                = ((β + θ : ℝ) : ℂ) * I + ((-Real.pi / (2 * (k : ℝ)) : ℝ) : ℂ) * I from by
                  rw [hθdef]; push_cast; ring,
              Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hsin0]
            push_cast; ring
          rw [hwpolar, hexpβ]; push_cast; ring
        exact ⟨r * Real.cos (β + θ), (abs_lt.mp habst).1, (abs_lt.mp habst).2, hwt⟩
  · -- ⊇ : every diameter point is realized by a plane point at z = π/2
    rintro p ⟨w, ⟨t, ht1, ht2, hwt⟩, rfl⟩
    have hnorm : ‖w.val‖ < 1 := by
      rw [hwt, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      exact abs_lt.mpr ⟨ht1, ht2⟩
    have hval : (k : ℝ) * (-Real.pi / (2 * (k : ℝ))) = -(Real.pi / 2) := by field_simp
    have hre : (w.val ^ k).re = 0 := by
      rw [hwt, mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul,
        show (↑k : ℂ) * (((-Real.pi / (2 * (k : ℝ)) : ℝ) : ℂ) * I)
            = (((k : ℝ) * (-Real.pi / (2 * (k : ℝ))) : ℝ) : ℂ) * I from by push_cast; ring,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, hval,
        Real.cos_neg, Real.cos_pi_div_two]
      ring
    obtain ⟨q, hq⟩ :=
      exists_halfPeriod_over_disk h.out (reflectionBasepoint k) w rfl R.C (le_of_lt hnorm)
    refine ⟨q.val, ⟨?_, ?_⟩, hq⟩
    · -- on the plane
      by_cases ht0 : 0 ≤ t
      · -- t ≥ 0 : w = t e^{-iθ}, β = -θ
        have hkβ : Real.cos ((k : ℝ) * (-Real.pi / (2 * (k : ℝ)))) = 0 := by
          rw [show (k : ℝ) * (-Real.pi / (2 * (k : ℝ))) = -(Real.pi / 2) from by field_simp,
            Real.cos_neg, Real.cos_pi_div_two]
        obtain ⟨hx, hy⟩ :=
          centeredLiftAmbient_midplane_horizontal R q.val ht0 ht2 hkβ w hwt hq
        rw [hx, hy]
        exact plane_cond_iff.mpr (by
          rw [show (-Real.pi / (2 * (k : ℝ))) + θ = 0 from by rw [hθdef]; ring, Real.sin_zero,
            mul_zero])
      · -- t < 0 : w = |t| e^{i(π-θ)}, β = π - θ
        rw [not_le] at ht0
        have hr0 : (0 : ℝ) ≤ -t := by linarith
        have hr1 : -t < 1 := by linarith
        have hwpolar : w.val
            = (↑(-t) : ℂ) * Complex.exp (((Real.pi - Real.pi / (2 * (k : ℝ))) : ℝ) * I) := by
          rw [hwt, show ((Real.pi - Real.pi / (2 * (k : ℝ))) : ℝ) * I
              = (Real.pi : ℝ) * I + ((-Real.pi / (2 * (k : ℝ))) : ℝ) * I from by push_cast; ring,
            Complex.exp_add, Complex.exp_pi_mul_I]
          push_cast; ring
        have hkβ : Real.cos ((k : ℝ) * (Real.pi - Real.pi / (2 * (k : ℝ)))) = 0 := by
          rw [show (k : ℝ) * (Real.pi - Real.pi / (2 * (k : ℝ)))
              = (k : ℝ) * Real.pi - Real.pi / 2 from by field_simp,
            Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, zero_add,
            Real.sin_nat_mul_pi]
        obtain ⟨hx, hy⟩ :=
          centeredLiftAmbient_midplane_horizontal R q.val hr0 hr1 hkβ w hwpolar hq
        rw [hx, hy]
        exact plane_cond_iff.mpr (by
          rw [show (Real.pi - Real.pi / (2 * (k : ℝ))) + θ = Real.pi from by rw [hθdef]; ring,
            Real.sin_pi, mul_zero])
    · exact (midplane_iff h.out (reflectionBasepoint k) w rfl R.C q.val hq q.property).mpr
        ⟨hre, hnorm⟩

end KsIndex.KarcherData
