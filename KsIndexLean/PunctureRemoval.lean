module

/-
# Removing a point from weak equations and weak derivatives

Logarithmic cutoffs turn a smooth compactly supported test on an open chart `Ω`
into a test supported away from `z₀`. Their Dirichlet energy tends to zero;
Cauchy–Schwarz controls the cutoff-gradient error, while dominated convergence
recovers the original test integral.

`isWeakSolOn_of_punctured_tests` extends the weak equation `Δu + V·u = 0`
from tests avoiding `z₀` to all tests on `Ω`. It assumes a full-chart `W1p` element
and a measurable potential bounded on each compact subset of the chart.

Separately, `hasWeakFDerivOn_puncture_extend` extends the weak-derivative identity
from the punctured chart, assuming both the value and proposed gradient are in
`L²` on the full chart. `exists_w1p_of_punctured_jet` packages this identity as a
`W1p` element whose value and gradient agree almost everywhere with those data.
These conclusions concern weak identities and Sobolev representatives.
-/
public import KsIndexLean.LogCutoff
public import KsIndexLean.SmoothMultiplierTest

@[expose] public section


noncomputable section
open MeasureTheory TopologicalSpace Topology
namespace KsIndex.PunctureRemoval
open KsIndex.LogCutoff

/-- The punctured chart, as `Opens`. -/
def puncturedOpens (Ω : Opens ℂ) (z₀ : ℂ) : Opens ℂ :=
  ⟨Ω.carrier \ {z₀}, Ω.isOpen.sdiff isClosed_singleton⟩

/-- The assertion that `u` weak-solves `Δu + V·u = 0` on `Ω` — the explicit
componentwise integrand (`∂ₓ = (gradient).re`, `∂ᵧ = (gradient).im`), quantified
over smooth compactly supported tests with closed support in `S ⊆ Ω.carrier`
(the set parameter lets the SAME definition express the punctured-test
hypothesis and the full conclusion). -/
def IsWeakSolOnSet (V : ℂ → ℝ) (Ω : Opens ℂ) (S : Set ℂ)
    (u : TauCeti.W1p (volume : Measure ℂ) Ω 2) : Prop :=
  ∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ S →
    ∫ x in Ω.carrier,
      ((TauCeti.W1p.gradient u x).re * fderiv ℝ φ x 1
        + (TauCeti.W1p.gradient u x).im * fderiv ℝ φ x Complex.I
        - V x * TauCeti.W1p.value u x * φ x) ∂(volume : Measure ℂ) = 0

/-- The weak equation with tests supported in all of `Ω`. -/
abbrev IsWeakSolOn (V : ℂ → ℝ) (Ω : Opens ℂ)
    (u : TauCeti.W1p (volume : Measure ℂ) Ω 2) : Prop :=
  IsWeakSolOnSet V Ω Ω.carrier u

/-! ### The punctured-test package -/

variable {ε : ℝ} {z₀ : ℂ}

/-- The cutoff's closed support avoids the open inner ball. -/
lemma tsupport_logCutoff_disjoint (hε : 0 < ε) (hε1 : ε < 1) :
    Disjoint (tsupport (logCutoff ε z₀)) (Metric.ball z₀ (ε ^ 2)) := by
  rw [Set.disjoint_right]
  intro z hz hts
  have hz' : logCutoff ε z₀ z = 0 ∧ ∀ᶠ w in nhds z, logCutoff ε z₀ w = 0 := by
    constructor
    · exact logCutoff_eq_zero z₀ hε hε1
        (le_of_lt (by simpa [dist_eq_norm] using Metric.mem_ball.mp hz))
    · filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      exact logCutoff_eq_zero z₀ hε hε1
        (le_of_lt (by simpa [dist_eq_norm] using Metric.mem_ball.mp hw))
  exact (notMem_tsupport_iff_eventuallyEq.mpr hz'.2) hts

/-- **The punctured-test package.**  For a test `φ` on `Ω` and `0 < ε < 1`, the
product `φ · logCutoff ε z₀` is a test whose closed support lies in
`Ω.carrier \ {z₀}` (indeed avoids `ball z₀ ε²`), smooth and compactly
supported. -/
lemma punctured_test (hε : 0 < ε) (hε1 : ε < 1) {Ω : Opens ℂ} {φ : ℂ → ℝ}
    (hφs : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω.carrier) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => φ z * logCutoff ε z₀ z)
      ∧ HasCompactSupport (fun z => φ z * logCutoff ε z₀ z)
      ∧ tsupport (fun z => φ z * logCutoff ε z₀ z) ⊆ Ω.carrier \ {z₀} := by
  refine ⟨hφs.mul (contDiff_logCutoff z₀ hε hε1), hφc.mul_right, ?_⟩
  intro z hz
  have h1 : z ∈ tsupport φ := tsupport_mul_subset_left hz
  have h2 : z ∈ tsupport (logCutoff ε z₀) := tsupport_mul_subset_right hz
  refine ⟨hφΩ h1, fun hzz => ?_⟩
  rw [Set.mem_singleton_iff] at hzz
  subst hzz
  exact Set.disjoint_left.mp (tsupport_logCutoff_disjoint hε hε1) h2
    (Metric.mem_ball_self (pow_pos hε 2))

/-! ### The Cauchy–Schwarz estimate: the cutoff-gradient pairing vanishes

`|∫ φ·⟨∇u, ∇ψ_ε⟩| ≤ 2·Mφ·(∫‖∇u‖²)^{1/2}·(∫‖∇ψ_ε‖²)^{1/2}`, and the last factor
is controlled by the cutoff energy bound `energy_logCutoff_le → 0`.  This is the
critical estimate of the paper's log-cutoff argument. -/

/-- A continuous compactly supported real function is globally bounded. -/
lemma exists_bound_of_continuous_compactSupport {f : ℂ → ℝ}
    (hc : Continuous f) (hs : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hc
  exact ⟨max M 0, le_max_right _ _,
    fun x => le_trans (by simpa using hM x) (le_max_left _ _)⟩

/-- The cutoff's gradient has compact support (inside the closed annulus). -/
lemma hasCompactSupport_fderiv_logCutoff (hε : 0 < ε) (hε1 : ε < 1) :
    HasCompactSupport (fderiv ℝ (logCutoff ε z₀)) := by
  apply HasCompactSupport.intro (isCompact_closedBall z₀ ε)
  intro z hz
  have h : ε < ‖z - z₀‖ := by
    have := Metric.mem_closedBall.not.mp hz
    push Not at this
    simpa [dist_eq_norm] using this
  exact fderiv_logCutoff_outer z₀ hε hε1 h

/-- The cutoff's gradient is continuous. -/
lemma continuous_fderiv_logCutoff (hε : 0 < ε) (hε1 : ε < 1) :
    Continuous (fderiv ℝ (logCutoff ε z₀)) :=
  (contDiff_logCutoff z₀ hε hε1).continuous_fderiv (by simp)

/-- The squared operator-norm of the cutoff gradient is `MemLp 1`, with set
integral over any `S` at most the global cutoff energy bound. -/
lemma setIntegral_fderiv_logCutoff_sq_le (hε : 0 < ε) (hε1 : ε < 1)
    {C : ℝ} (hC : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C) (S : Set ℂ) :
    ∫ z in S, ‖fderiv ℝ (logCutoff ε z₀) z‖ ^ 2
      ≤ 2 * Real.pi * C ^ 2 / (-Real.log ε) := by
  have hcont : Continuous fun z => ‖fderiv ℝ (logCutoff ε z₀) z‖ ^ 2 :=
    ((continuous_fderiv_logCutoff hε hε1).norm.pow 2)
  have hcs : HasCompactSupport fun z => ‖fderiv ℝ (logCutoff ε z₀) z‖ ^ 2 := by
    apply (hasCompactSupport_fderiv_logCutoff hε hε1).comp_left (g := fun L => ‖L‖ ^ 2)
    simp
  have hint : MeasureTheory.Integrable
      (fun z => ‖fderiv ℝ (logCutoff ε z₀) z‖ ^ 2) := hcont.integrable_of_hasCompactSupport hcs
  calc ∫ z in S, ‖fderiv ℝ (logCutoff ε z₀) z‖ ^ 2
      ≤ ∫ z : ℂ, ‖fderiv ℝ (logCutoff ε z₀) z‖ ^ 2 :=
        MeasureTheory.setIntegral_le_integral hint
          (Filter.Eventually.of_forall fun z => by positivity)
    _ ≤ 2 * Real.pi * C ^ 2 / (-Real.log ε) := energy_logCutoff_le z₀ hε hε1 hC

/-- **The Cauchy–Schwarz pairing estimate**: the cutoff-gradient
pairing against the solution's gradient is controlled by the square root of the
cutoff energy bound — the critical estimate of the log-cutoff argument. -/
lemma cutoff_pairing_bound {Ω : Opens ℂ}
    (u : TauCeti.W1p (volume : Measure ℂ) Ω 2) (hε : 0 < ε) (hε1 : ε < 1)
    {C : ℝ} (hC : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C)
    {φ : ℂ → ℝ} {Mφ : ℝ} (hMφ0 : 0 ≤ Mφ) (hMφ : ∀ x, |φ x| ≤ Mφ) :
    |∫ x in Ω.carrier, φ x *
        ((TauCeti.W1p.gradient u x).re * fderiv ℝ (logCutoff ε z₀) x 1
          + (TauCeti.W1p.gradient u x).im * fderiv ℝ (logCutoff ε z₀) x Complex.I)|
      ≤ 2 * Mφ * (∫ x in Ω.carrier, ‖TauCeti.W1p.gradient u x‖ ^ 2) ^ ((1:ℝ)/2)
          * (2 * Real.pi * C ^ 2 / (-Real.log ε)) ^ ((1:ℝ)/2) := by
  have hlog : Real.log ε < 0 := Real.log_neg hε hε1
  -- MemLp data for the two Cauchy–Schwarz factors
  have hgmem : MeasureTheory.MemLp (fun x => ‖TauCeti.W1p.gradient u x‖) 2
      ((volume : Measure ℂ).restrict Ω.carrier) :=
    (MeasureTheory.Lp.memLp (TauCeti.W1p.gradient u)).norm
  have hDmem : MeasureTheory.MemLp (fun x => ‖fderiv ℝ (logCutoff ε z₀) x‖) 2
      ((volume : Measure ℂ).restrict Ω.carrier) :=
    (((continuous_fderiv_logCutoff hε hε1).norm.memLp_of_hasCompactSupport
      (hasCompactSupport_fderiv_logCutoff hε hε1).norm)).restrict _
  -- pointwise bound: |φ·(g.re·D1 + g.im·DI)| ≤ (2Mφ)·(‖g‖·‖D‖)
  have hpt : ∀ x : ℂ, |φ x *
      ((TauCeti.W1p.gradient u x).re * fderiv ℝ (logCutoff ε z₀) x 1
        + (TauCeti.W1p.gradient u x).im * fderiv ℝ (logCutoff ε z₀) x Complex.I)|
      ≤ 2 * Mφ * (‖TauCeti.W1p.gradient u x‖ * ‖fderiv ℝ (logCutoff ε z₀) x‖) := by
    intro x
    set g := TauCeti.W1p.gradient u x
    set D := fderiv ℝ (logCutoff ε z₀) x
    have h1 : |D 1| ≤ ‖D‖ := by
      simpa using D.le_opNorm (1 : ℂ)
    have hI : |D Complex.I| ≤ ‖D‖ := by
      simpa [Complex.norm_I] using D.le_opNorm Complex.I
    have hre : |g.re| ≤ ‖g‖ := RCLike.abs_re_le_norm g
    have him : |g.im| ≤ ‖g‖ := RCLike.abs_im_le_norm g
    calc |φ x * (g.re * D 1 + g.im * D Complex.I)|
        = |φ x| * |g.re * D 1 + g.im * D Complex.I| := abs_mul _ _
      _ ≤ Mφ * (|g.re| * |D 1| + |g.im| * |D Complex.I|) := by
          apply mul_le_mul (hMφ x) ((abs_add_le _ _).trans (by rw [abs_mul, abs_mul]))
            (abs_nonneg _) hMφ0
      _ ≤ Mφ * (‖g‖ * ‖D‖ + ‖g‖ * ‖D‖) := by
          apply mul_le_mul_of_nonneg_left _ hMφ0
          exact add_le_add (mul_le_mul hre h1 (abs_nonneg _) (norm_nonneg _))
            (mul_le_mul him hI (abs_nonneg _) (norm_nonneg _))
      _ = 2 * Mφ * (‖g‖ * ‖D‖) := by ring
  -- the product ‖g‖·‖D‖ is integrable (L²·L²)
  have hprod : MeasureTheory.Integrable
      (fun x => ‖TauCeti.W1p.gradient u x‖ * ‖fderiv ℝ (logCutoff ε z₀) x‖)
      ((volume : Measure ℂ).restrict Ω.carrier) :=
    hgmem.integrable_mul hDmem
  -- |∫| ≤ ∫|·| ≤ 2Mφ·∫‖g‖‖D‖
  have hstep1 : |∫ x in Ω.carrier, φ x *
      ((TauCeti.W1p.gradient u x).re * fderiv ℝ (logCutoff ε z₀) x 1
        + (TauCeti.W1p.gradient u x).im * fderiv ℝ (logCutoff ε z₀) x Complex.I)|
      ≤ 2 * Mφ * ∫ x in Ω.carrier,
          ‖TauCeti.W1p.gradient u x‖ * ‖fderiv ℝ (logCutoff ε z₀) x‖ := by
    calc |∫ x in Ω.carrier, _| ≤ ∫ x in Ω.carrier, |φ x *
          ((TauCeti.W1p.gradient u x).re * fderiv ℝ (logCutoff ε z₀) x 1
            + (TauCeti.W1p.gradient u x).im * fderiv ℝ (logCutoff ε z₀) x Complex.I)| :=
        MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ x in Ω.carrier, 2 * Mφ *
            (‖TauCeti.W1p.gradient u x‖ * ‖fderiv ℝ (logCutoff ε z₀) x‖) := by
          apply MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => abs_nonneg _)
            (hprod.const_mul _)
            (Filter.Eventually.of_forall fun x => hpt x)
      _ = 2 * Mφ * ∫ x in Ω.carrier,
            ‖TauCeti.W1p.gradient u x‖ * ‖fderiv ℝ (logCutoff ε z₀) x‖ :=
          MeasureTheory.integral_const_mul _ _
  -- Hölder (p = q = 2)
  have hholder : (∫ x in Ω.carrier,
        ‖TauCeti.W1p.gradient u x‖ * ‖fderiv ℝ (logCutoff ε z₀) x‖)
      ≤ (∫ x in Ω.carrier, ‖TauCeti.W1p.gradient u x‖ ^ (2:ℝ)) ^ ((1:ℝ)/2)
        * (∫ x in Ω.carrier, ‖fderiv ℝ (logCutoff ε z₀) x‖ ^ (2:ℝ)) ^ ((1:ℝ)/2) := by
    have h2 : ENNReal.ofReal (2:ℝ) = 2 := by simp
    have hgmem2 : MeasureTheory.MemLp (fun x => ‖TauCeti.W1p.gradient u x‖)
        (ENNReal.ofReal (2:ℝ)) ((volume : Measure ℂ).restrict Ω.carrier) := by
      rw [h2]; exact hgmem
    have hDmem2 : MeasureTheory.MemLp (fun x => ‖fderiv ℝ (logCutoff ε z₀) x‖)
        (ENNReal.ofReal (2:ℝ)) ((volume : Measure ℂ).restrict Ω.carrier) := by
      rw [h2]; exact hDmem
    exact MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun x => norm_nonneg _)
      (Filter.Eventually.of_forall fun x => norm_nonneg _)
      hgmem2 hDmem2
  -- rpow-2 → pow-2 and the energy bound on the second factor
  have hr2 : ∀ r : ℝ, 0 ≤ r → r ^ (2:ℝ) = r ^ 2 := fun r _ => by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hcong1 : (∫ x in Ω.carrier, ‖TauCeti.W1p.gradient u x‖ ^ (2:ℝ))
      = ∫ x in Ω.carrier, ‖TauCeti.W1p.gradient u x‖ ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    exact hr2 _ (norm_nonneg _)
  have hcong2 : (∫ x in Ω.carrier, ‖fderiv ℝ (logCutoff ε z₀) x‖ ^ (2:ℝ))
      = ∫ x in Ω.carrier, ‖fderiv ℝ (logCutoff ε z₀) x‖ ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    exact hr2 _ (norm_nonneg _)
  have henergy : (∫ x in Ω.carrier, ‖fderiv ℝ (logCutoff ε z₀) x‖ ^ 2) ^ ((1:ℝ)/2)
      ≤ (2 * Real.pi * C ^ 2 / (-Real.log ε)) ^ ((1:ℝ)/2) := by
    apply Real.rpow_le_rpow
      (MeasureTheory.integral_nonneg fun x => by positivity)
      (setIntegral_fderiv_logCutoff_sq_le hε hε1 hC _) (by norm_num)
  -- assemble
  calc |∫ x in Ω.carrier, φ x *
        ((TauCeti.W1p.gradient u x).re * fderiv ℝ (logCutoff ε z₀) x 1
          + (TauCeti.W1p.gradient u x).im * fderiv ℝ (logCutoff ε z₀) x Complex.I)|
      ≤ 2 * Mφ * ∫ x in Ω.carrier,
          ‖TauCeti.W1p.gradient u x‖ * ‖fderiv ℝ (logCutoff ε z₀) x‖ := hstep1
    _ ≤ 2 * Mφ * ((∫ x in Ω.carrier, ‖TauCeti.W1p.gradient u x‖ ^ 2) ^ ((1:ℝ)/2)
          * (∫ x in Ω.carrier, ‖fderiv ℝ (logCutoff ε z₀) x‖ ^ 2) ^ ((1:ℝ)/2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← hcong1, ← hcong2]
        exact hholder
    _ ≤ 2 * Mφ * ((∫ x in Ω.carrier, ‖TauCeti.W1p.gradient u x‖ ^ 2) ^ ((1:ℝ)/2)
          * (2 * Real.pi * C ^ 2 / (-Real.log ε)) ^ ((1:ℝ)/2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left henergy
          (Real.rpow_nonneg (MeasureTheory.integral_nonneg fun x => by positivity) _)
    _ = 2 * Mφ * (∫ x in Ω.carrier, ‖TauCeti.W1p.gradient u x‖ ^ 2) ^ ((1:ℝ)/2)
          * (2 * Real.pi * C ^ 2 / (-Real.log ε)) ^ ((1:ℝ)/2) := by ring

/-! ### Integrability of the test integrand -/

/-- The real/imaginary components of the gradient are `MemLp 2`. -/
lemma memLp_gradient_re {Ω : Opens ℂ} (u : TauCeti.W1p (volume : Measure ℂ) Ω 2) :
    MeasureTheory.MemLp (fun x => (TauCeti.W1p.gradient u x).re) 2
      ((volume : Measure ℂ).restrict Ω.carrier) := by
  refine MeasureTheory.MemLp.of_le (g := fun x => ‖TauCeti.W1p.gradient u x‖)
    (MeasureTheory.Lp.memLp (TauCeti.W1p.gradient u)).norm
    ((Complex.measurable_re.comp_aemeasurable
      (MeasureTheory.Lp.aestronglyMeasurable _).aemeasurable).aestronglyMeasurable) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (norm_nonneg _)]
  exact Complex.abs_re_le_norm _

/-- The imaginary-part analogue. -/
lemma memLp_gradient_im {Ω : Opens ℂ} (u : TauCeti.W1p (volume : Measure ℂ) Ω 2) :
    MeasureTheory.MemLp (fun x => (TauCeti.W1p.gradient u x).im) 2
      ((volume : Measure ℂ).restrict Ω.carrier) := by
  refine MeasureTheory.MemLp.of_le (g := fun x => ‖TauCeti.W1p.gradient u x‖)
    (MeasureTheory.Lp.memLp (TauCeti.W1p.gradient u)).norm
    ((Complex.measurable_im.comp_aemeasurable
      (MeasureTheory.Lp.aestronglyMeasurable _).aemeasurable).aestronglyMeasurable) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (norm_nonneg _)]
  exact Complex.abs_im_le_norm _

/-- A test's directional derivative is `MemLp 2` (continuous, compact support). -/
lemma memLp_fderiv_test {Ω : Opens ℂ} {φ : ℂ → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (v : ℂ) :
    MeasureTheory.MemLp (fun x => fderiv ℝ φ x v) 2
      ((volume : Measure ℂ).restrict Ω.carrier) := by
  have hcont : Continuous fun x => fderiv ℝ φ x v :=
    (hφs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport fun x => fderiv ℝ φ x v := by
    apply (hφc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v)
    simp
  exact (hcont.memLp_of_hasCompactSupport hcs).restrict _

/-- **Integrability of the test integrand** (the DCT dominator's heart): with the
potential bounded on the test's support, each term of the weak-equation integrand is an
`L²·L²` product. -/
lemma integrable_testIntegrand {Ω : Opens ℂ}
    (u : TauCeti.W1p (volume : Measure ℂ) Ω 2) {V : ℂ → ℝ} (hVm : Measurable V)
    {φ : ℂ → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    {Cv : ℝ} (hCv0 : 0 ≤ Cv) (hCv : ∀ x ∈ tsupport φ, |V x| ≤ Cv) :
    MeasureTheory.Integrable (fun x =>
        (TauCeti.W1p.gradient u x).re * fderiv ℝ φ x 1
          + (TauCeti.W1p.gradient u x).im * fderiv ℝ φ x Complex.I
          - V x * TauCeti.W1p.value u x * φ x)
      ((volume : Measure ℂ).restrict Ω.carrier) := by
  have ha : MeasureTheory.Integrable (fun x =>
      (TauCeti.W1p.gradient u x).re * fderiv ℝ φ x 1)
      ((volume : Measure ℂ).restrict Ω.carrier) :=
    (memLp_gradient_re u).integrable_mul (memLp_fderiv_test hφs hφc 1)
  have hb : MeasureTheory.Integrable (fun x =>
      (TauCeti.W1p.gradient u x).im * fderiv ℝ φ x Complex.I)
      ((volume : Measure ℂ).restrict Ω.carrier) :=
    (memLp_gradient_im u).integrable_mul (memLp_fderiv_test hφs hφc Complex.I)
  have hVφ : MeasureTheory.MemLp (fun x => V x * φ x) 2
      ((volume : Measure ℂ).restrict Ω.carrier) := by
    have hφ2 : MeasureTheory.MemLp (fun x => Cv * φ x) 2
        ((volume : Measure ℂ).restrict Ω.carrier) :=
      ((hφs.continuous.memLp_of_hasCompactSupport hφc).restrict _).const_mul Cv
    apply MeasureTheory.MemLp.of_le hφ2
      ((hVm.aestronglyMeasurable).mul hφs.continuous.aestronglyMeasurable)
    filter_upwards with x
    simp only [Real.norm_eq_abs, Pi.mul_apply]
    rw [abs_mul, abs_mul, abs_of_nonneg hCv0]
    by_cases hx : x ∈ tsupport φ
    · exact mul_le_mul_of_nonneg_right (hCv x hx) (abs_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have hc : MeasureTheory.Integrable (fun x =>
      V x * TauCeti.W1p.value u x * φ x)
      ((volume : Measure ℂ).restrict Ω.carrier) := by
    have h1 : MeasureTheory.Integrable (fun x =>
        TauCeti.W1p.value u x * (V x * φ x))
        ((volume : Measure ℂ).restrict Ω.carrier) :=
      (MeasureTheory.Lp.memLp (TauCeti.W1p.value u)).integrable_mul hVφ
    have h2 : (fun x => V x * TauCeti.W1p.value u x * φ x)
        = fun x => TauCeti.W1p.value u x * (V x * φ x) := by
      funext x; ring
    rw [h2]
    exact h1
  exact (ha.add hb).sub hc

/-! ### The cutoff sequence and the dominated-convergence limit -/

/-- The cutoff scale sequence `ε_n = 1/(n+2)`. -/
def εseq (n : ℕ) : ℝ := 1 / (n + 2)

lemma εseq_pos (n : ℕ) : 0 < εseq n := by unfold εseq; positivity

lemma εseq_lt_one (n : ℕ) : εseq n < 1 := by
  unfold εseq
  rw [div_lt_one (by positivity)]
  have : (0:ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- `−log ε_n = log (n+2) → ∞`. -/
lemma tendsto_neg_log_εseq :
    Filter.Tendsto (fun n => -Real.log (εseq n)) Filter.atTop Filter.atTop := by
  have h : ∀ n : ℕ, -Real.log (εseq n) = Real.log ((n : ℝ) + 2) := by
    intro n
    unfold εseq
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one]
    ring
  simp only [h]
  apply Real.tendsto_log_atTop.comp
  apply Filter.tendsto_atTop_add_const_right
  exact tendsto_natCast_atTop_atTop

/-- **The dominated-convergence limit**: multiplying an integrable integrand by
the expanding cutoffs converges to the full integral (pointwise the cutoff is
eventually `1` away from the center; domination by `|H|`). -/
lemma tendsto_cutoff_mul_integral {Ω : Opens ℂ} (z₀ : ℂ) {H : ℂ → ℝ}
    (hH : MeasureTheory.Integrable H ((volume : Measure ℂ).restrict Ω.carrier)) :
    Filter.Tendsto (fun n => ∫ x in Ω.carrier, logCutoff (εseq n) z₀ x * H x)
      Filter.atTop (𝓝 (∫ x in Ω.carrier, H x)) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun x => |H x|)
  · intro n
    exact ((contDiff_logCutoff z₀ (εseq_pos n) (εseq_lt_one n)).continuous
      |>.aestronglyMeasurable).mul hH.aestronglyMeasurable
  · exact hH.abs
  · intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_of_le_one_left (abs_nonneg _)
    rw [abs_of_nonneg (logCutoff_nonneg z₀ x)]
    exact logCutoff_le_one z₀ x
  · have hz : ((volume : Measure ℂ).restrict Ω.carrier) {z₀} = 0 :=
      le_antisymm ((Measure.restrict_apply_le _ _).trans
        (by simp [measure_singleton])) bot_le
    have hae : ∀ᵐ x ∂((volume : Measure ℂ).restrict Ω.carrier), x ≠ z₀ := by
      rw [MeasureTheory.ae_iff]
      convert hz using 2
      simp
    filter_upwards [hae] with x hx
    have hr : 0 < ‖x - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖x - z₀‖)
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have hεn : εseq n ≤ ‖x - z₀‖ := by
      unfold εseq
      rw [div_le_iff₀ (by positivity)]
      have h1 : 1 / ‖x - z₀‖ < (N : ℝ) := hN
      have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
      rw [div_lt_iff₀ hr] at h1
      nlinarith [hr]
    rw [logCutoff_eq_one z₀ (εseq_pos n) (εseq_lt_one n) hεn, one_mul]

/-! ### Extension of the weak equation -/

/-- For a measurable potential bounded on compact subsets of the chart, a full-chart
`H¹` function that weak-solves
against every test supported away from a point weak-solves against every test —
the puncture is removable for the weak equation.  Mechanism: test against
`φ·ψ_n` (`punctured_test`), split by the product rule, send `n → ∞`: the
cutoff side converges to the full identity (dominated convergence), the
gradient-pairing side vanishes (Cauchy–Schwarz against the cutoff energy). -/
theorem isWeakSolOn_of_punctured_tests {Ω : Opens ℂ} {V : ℂ → ℝ}
    (hV : ∀ K, K ⊆ Ω.carrier → IsCompact K → ∃ Cv, ∀ x ∈ K, |V x| ≤ Cv)
    (hVm : Measurable V) (u : TauCeti.W1p (volume : Measure ℂ) Ω 2)
    (h : IsWeakSolOnSet V Ω (Ω.carrier \ {z₀}) u) :
    IsWeakSolOn V Ω u := by
  intro φ hφs hφc hφΩ
  -- bounds and integrability data
  obtain ⟨Cv, hCv⟩ := hV (tsupport φ) hφΩ hφc
  have hCv' : ∀ x ∈ tsupport φ, |V x| ≤ max Cv 0 :=
    fun x hx => (hCv x hx).trans (le_max_left _ _)
  obtain ⟨Mφ, hMφ0, hMφ⟩ :=
    exists_bound_of_continuous_compactSupport hφs.continuous hφc
  obtain ⟨C, hC0, hC⟩ := exists_transition_deriv_bound
  have hH : MeasureTheory.Integrable (fun x =>
      (TauCeti.W1p.gradient u x).re * fderiv ℝ φ x 1
        + (TauCeti.W1p.gradient u x).im * fderiv ℝ φ x Complex.I
        - V x * TauCeti.W1p.value u x * φ x)
      ((volume : Measure ℂ).restrict Ω.carrier) :=
    integrable_testIntegrand u hVm hφs hφc (le_max_right Cv 0) hCv'
  -- abbreviations (plain functions, no new defs)
  set H : ℂ → ℝ := fun x =>
    (TauCeti.W1p.gradient u x).re * fderiv ℝ φ x 1
      + (TauCeti.W1p.gradient u x).im * fderiv ℝ φ x Complex.I
      - V x * TauCeti.W1p.value u x * φ x with hHdef
  set P : ℕ → ℂ → ℝ := fun n x =>
    (TauCeti.W1p.gradient u x).re * fderiv ℝ (logCutoff (εseq n) z₀) x 1
      + (TauCeti.W1p.gradient u x).im * fderiv ℝ (logCutoff (εseq n) z₀) x Complex.I
    with hPdef
  -- the n-th punctured-test identity
  have hvanish : ∀ n : ℕ, (∫ x in Ω.carrier,
      ((TauCeti.W1p.gradient u x).re
          * fderiv ℝ (fun y => φ y * logCutoff (εseq n) z₀ y) x 1
        + (TauCeti.W1p.gradient u x).im
          * fderiv ℝ (fun y => φ y * logCutoff (εseq n) z₀ y) x Complex.I
        - V x * TauCeti.W1p.value u x * (φ x * logCutoff (εseq n) z₀ x))) = 0 := by
    intro n
    obtain ⟨hs, hc, hts⟩ :=
      punctured_test (εseq_pos n) (εseq_lt_one n) (Ω := Ω) hφs hφc hφΩ
    exact h _ hs hc hts
  -- the pointwise product-rule split
  have hsplit : ∀ n : ℕ, ∀ x : ℂ,
      (TauCeti.W1p.gradient u x).re
          * fderiv ℝ (fun y => φ y * logCutoff (εseq n) z₀ y) x 1
        + (TauCeti.W1p.gradient u x).im
          * fderiv ℝ (fun y => φ y * logCutoff (εseq n) z₀ y) x Complex.I
        - V x * TauCeti.W1p.value u x * (φ x * logCutoff (εseq n) z₀ x)
      = logCutoff (εseq n) z₀ x * H x + φ x * P n x := by
    intro n x
    have hdφ : DifferentiableAt ℝ φ x :=
      (hφs.differentiable (by simp)).differentiableAt
    have hdψ : DifferentiableAt ℝ (logCutoff (εseq n) z₀) x :=
      ((contDiff_logCutoff z₀ (εseq_pos n) (εseq_lt_one n)).differentiable
        (by simp)).differentiableAt
    have hD := fderiv_mul (𝕜 := ℝ) hdφ hdψ
    rw [show (fun y => φ y * logCutoff (εseq n) z₀ y)
        = φ * logCutoff (εseq n) z₀ from rfl, hD]
    simp only [add_apply, FunLike.coe_smul,
      Pi.smul_apply, smul_eq_mul, hHdef, hPdef]
    ring
  -- integrability of the two split pieces
  have hψHint : ∀ n : ℕ, MeasureTheory.Integrable
      (fun x => logCutoff (εseq n) z₀ x * H x)
      ((volume : Measure ℂ).restrict Ω.carrier) := by
    intro n
    apply MeasureTheory.Integrable.mono' hH.abs
      (((contDiff_logCutoff z₀ (εseq_pos n) (εseq_lt_one n)).continuous
        |>.aestronglyMeasurable).mul hH.aestronglyMeasurable)
    filter_upwards with x
    simp only [Pi.mul_apply, Real.norm_eq_abs]
    rw [abs_mul]
    apply mul_le_of_le_one_left (abs_nonneg _)
    rw [abs_of_nonneg (logCutoff_nonneg z₀ x)]
    exact logCutoff_le_one z₀ x
  have hPint : ∀ n : ℕ, MeasureTheory.Integrable (fun x => P n x)
      ((volume : Measure ℂ).restrict Ω.carrier) := by
    intro n
    have hmem : ∀ v : ℂ, MeasureTheory.MemLp
        (fun x => fderiv ℝ (logCutoff (εseq n) z₀) x v) 2
        ((volume : Measure ℂ).restrict Ω.carrier) := by
      intro v
      have hcont : Continuous fun x => fderiv ℝ (logCutoff (εseq n) z₀) x v :=
        (continuous_fderiv_logCutoff (εseq_pos n) (εseq_lt_one n)).clm_apply
          continuous_const
      have hcs : HasCompactSupport fun x => fderiv ℝ (logCutoff (εseq n) z₀) x v := by
        apply (hasCompactSupport_fderiv_logCutoff (εseq_pos n)
          (εseq_lt_one n)).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v)
        simp
      exact (hcont.memLp_of_hasCompactSupport hcs).restrict _
    rw [hPdef]
    exact ((memLp_gradient_re u).integrable_mul (hmem 1)).add
      ((memLp_gradient_im u).integrable_mul (hmem Complex.I))
  have hφPint : ∀ n : ℕ, MeasureTheory.Integrable (fun x => φ x * P n x)
      ((volume : Measure ℂ).restrict Ω.carrier) := by
    intro n
    apply MeasureTheory.Integrable.mono' ((hPint n).abs.const_mul Mφ)
      (hφs.continuous.aestronglyMeasurable.mul (hPint n).aestronglyMeasurable)
    filter_upwards with x
    simp only [Pi.mul_apply, Real.norm_eq_abs]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hMφ x) (abs_nonneg _)
  -- the linear relation: ∫ψₙH = −∫φPₙ
  have hlin : ∀ n : ℕ, (∫ x in Ω.carrier, logCutoff (εseq n) z₀ x * H x)
      = -∫ x in Ω.carrier, φ x * P n x := by
    intro n
    have h0 := hvanish n
    rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (hsplit n))] at h0
    rw [MeasureTheory.integral_add (hψHint n) (hφPint n)] at h0
    linarith
  -- the B-side vanishes (Cauchy–Schwarz + energy → 0)
  have hBtendsto : Filter.Tendsto (fun n => ∫ x in Ω.carrier, φ x * P n x)
      Filter.atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n =>
      2 * Mφ * (∫ x in Ω.carrier, ‖TauCeti.W1p.gradient u x‖ ^ 2) ^ ((1:ℝ)/2)
        * (2 * Real.pi * C ^ 2 / (-Real.log (εseq n))) ^ ((1:ℝ)/2))
    · intro n
      rw [Real.norm_eq_abs]
      have := cutoff_pairing_bound (z₀ := z₀) u (εseq_pos n) (εseq_lt_one n)
        hC hMφ0 hMφ
      calc |∫ x in Ω.carrier, φ x * P n x| = |∫ x in Ω.carrier, φ x *
            ((TauCeti.W1p.gradient u x).re * fderiv ℝ (logCutoff (εseq n) z₀) x 1
              + (TauCeti.W1p.gradient u x).im
                * fderiv ℝ (logCutoff (εseq n) z₀) x Complex.I)| := by rw [hPdef]
        _ ≤ _ := this
    · have hinner : Filter.Tendsto
          (fun n => 2 * Real.pi * C ^ 2 / (-Real.log (εseq n)))
          Filter.atTop (𝓝 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_neg_log_εseq
      have hrpow : Filter.Tendsto
          (fun n => (2 * Real.pi * C ^ 2 / (-Real.log (εseq n))) ^ ((1:ℝ)/2))
          Filter.atTop (𝓝 0) := by
        have hcont : ContinuousAt (fun y : ℝ => y ^ ((1:ℝ)/2)) 0 :=
          Real.continuousAt_rpow_const 0 _ (Or.inr (by norm_num))
        have := hcont.tendsto.comp hinner
        simpa [Function.comp_def,
          Real.zero_rpow (by norm_num : ((1:ℝ)/2) ≠ 0)] using this
      have := hrpow.const_mul
        (2 * Mφ * (∫ x in Ω.carrier, ‖TauCeti.W1p.gradient u x‖ ^ 2) ^ ((1:ℝ)/2))
      simpa using this
  -- assemble: two limits of the same sequence
  have hAtendsto := tendsto_cutoff_mul_integral (Ω := Ω) z₀ hH
  have hNeg : Filter.Tendsto (fun n => ∫ x in Ω.carrier, logCutoff (εseq n) z₀ x * H x)
      Filter.atTop (𝓝 0) := by
    have := hBtendsto.neg
    simp only [neg_zero] at this
    apply this.congr
    intro n
    rw [hlin n]
  have := tendsto_nhds_unique hAtendsto hNeg
  rw [hHdef] at this
  exact this

/-! ### Extension of the weak derivative through the puncture

The same cutoff argument in the bundled-test (`𝓓`) setting of TauCeti's sealed
weak-derivative API: full-chart `L²` data for both value and gradient plus the
punctured weak-derivative property give the full-chart property, per direction.
`W1p.mk` then packages the extended jet. -/

section E6
open KsIndex.Trace
open scoped Distributions

/-- `L²` on the restricted measure gives local integrability on the open set. -/
lemma locallyIntegrableOn_of_memLp_two {E' : Type*} [NormedAddCommGroup E']
    {Ω : Opens ℂ} {f : ℂ → E'}
    (hf : MeasureTheory.MemLp f 2 ((volume : Measure ℂ).restrict Ω.carrier)) :
    MeasureTheory.LocallyIntegrableOn f Ω.carrier (volume : Measure ℂ) := by
  refine (MeasureTheory.locallyIntegrableOn_iff
    Ω.isOpen.isLocallyClosed).mpr fun K hK hKc => ?_
  have h1 := hf.mono_measure (Measure.restrict_mono hK le_rfl)
  have : MeasureTheory.IsFiniteMeasure ((volume : Measure ℂ).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
  exact h1.integrable (by norm_num)

/-- The direction-evaluated inner jet is `MemLp 2`. -/
lemma memLp_inner_const {Ω : Opens ℂ} {g : ℂ → ℂ}
    (hg : MeasureTheory.MemLp g 2 ((volume : Measure ℂ).restrict Ω.carrier))
    (v : ℂ) :
    MeasureTheory.MemLp (fun x => (innerSL ℝ (g x)) v) 2
      ((volume : Measure ℂ).restrict Ω.carrier) := by
  refine MeasureTheory.MemLp.of_le (g := fun x => ‖g x‖ * ‖v‖)
    (hg.norm.mul_const ‖v‖)
    (((innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).flip v).continuous.comp_aestronglyMeasurable
      hg.aestronglyMeasurable) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm (g x) v).trans (le_abs_self _)

/-- The scalar Cauchy–Schwarz bound: the cutoff-gradient pairing against an
`L²` scalar is controlled by the energy factor (direction `v` riding along). -/
lemma cutoff_scalar_pairing_bound {Ω : Opens ℂ} {w : ℂ → ℝ}
    (hw : MeasureTheory.MemLp w 2 ((volume : Measure ℂ).restrict Ω.carrier))
    (hε : 0 < ε) (hε1 : ε < 1)
    {C : ℝ} (hC : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C)
    {φ : ℂ → ℝ} {Mφ : ℝ} (hMφ0 : 0 ≤ Mφ) (hMφ : ∀ x, |φ x| ≤ Mφ) (v : ℂ) :
    |∫ x in Ω.carrier, φ x * (fderiv ℝ (logCutoff ε z₀) x v * w x)|
      ≤ Mφ * ‖v‖ * (∫ x in Ω.carrier, w x ^ 2) ^ ((1:ℝ)/2)
          * (2 * Real.pi * C ^ 2 / (-Real.log ε)) ^ ((1:ℝ)/2) := by
  have hDmem : MeasureTheory.MemLp (fun x => ‖fderiv ℝ (logCutoff ε z₀) x‖) 2
      ((volume : Measure ℂ).restrict Ω.carrier) :=
    (((continuous_fderiv_logCutoff hε hε1).norm.memLp_of_hasCompactSupport
      (hasCompactSupport_fderiv_logCutoff hε hε1).norm)).restrict _
  have hwabs : MeasureTheory.MemLp (fun x => |w x|) 2
      ((volume : Measure ℂ).restrict Ω.carrier) := by
    simpa [Real.norm_eq_abs] using hw.norm
  have hpt : ∀ x : ℂ, |φ x * (fderiv ℝ (logCutoff ε z₀) x v * w x)|
      ≤ Mφ * ‖v‖ * (‖fderiv ℝ (logCutoff ε z₀) x‖ * |w x|) := by
    intro x
    have h1 : |fderiv ℝ (logCutoff ε z₀) x v|
        ≤ ‖fderiv ℝ (logCutoff ε z₀) x‖ * ‖v‖ := by
      simpa using (fderiv ℝ (logCutoff ε z₀) x).le_opNorm v
    calc |φ x * (fderiv ℝ (logCutoff ε z₀) x v * w x)|
        = |φ x| * (|fderiv ℝ (logCutoff ε z₀) x v| * |w x|) := by
          rw [abs_mul, abs_mul]
      _ ≤ Mφ * ((‖fderiv ℝ (logCutoff ε z₀) x‖ * ‖v‖) * |w x|) := by
          apply mul_le_mul (hMφ x)
            (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
            (by positivity) hMφ0
      _ = Mφ * ‖v‖ * (‖fderiv ℝ (logCutoff ε z₀) x‖ * |w x|) := by ring
  have hprod : MeasureTheory.Integrable
      (fun x => ‖fderiv ℝ (logCutoff ε z₀) x‖ * |w x|)
      ((volume : Measure ℂ).restrict Ω.carrier) := hDmem.integrable_mul hwabs
  have hstep1 : |∫ x in Ω.carrier, φ x * (fderiv ℝ (logCutoff ε z₀) x v * w x)|
      ≤ Mφ * ‖v‖ * ∫ x in Ω.carrier,
          ‖fderiv ℝ (logCutoff ε z₀) x‖ * |w x| := by
    calc |∫ x in Ω.carrier, φ x * (fderiv ℝ (logCutoff ε z₀) x v * w x)|
        ≤ ∫ x in Ω.carrier,
            |φ x * (fderiv ℝ (logCutoff ε z₀) x v * w x)| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ x in Ω.carrier, Mφ * ‖v‖ *
            (‖fderiv ℝ (logCutoff ε z₀) x‖ * |w x|) := by
          apply MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => abs_nonneg _)
            (hprod.const_mul _)
            (Filter.Eventually.of_forall fun x => hpt x)
      _ = Mφ * ‖v‖ * ∫ x in Ω.carrier,
            ‖fderiv ℝ (logCutoff ε z₀) x‖ * |w x| :=
          MeasureTheory.integral_const_mul _ _
  have h2 : ENNReal.ofReal (2:ℝ) = 2 := by simp
  have hDmem2 : MeasureTheory.MemLp (fun x => ‖fderiv ℝ (logCutoff ε z₀) x‖)
      (ENNReal.ofReal (2:ℝ)) ((volume : Measure ℂ).restrict Ω.carrier) := by
    rw [h2]; exact hDmem
  have hwmem2 : MeasureTheory.MemLp (fun x => |w x|)
      (ENNReal.ofReal (2:ℝ)) ((volume : Measure ℂ).restrict Ω.carrier) := by
    rw [h2]; exact hwabs
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x : ℂ => norm_nonneg
      (fderiv ℝ (logCutoff ε z₀) x))
    (Filter.Eventually.of_forall fun x : ℂ => abs_nonneg (w x))
    hDmem2 hwmem2
  have hr2 : ∀ r : ℝ, 0 ≤ r → r ^ (2:ℝ) = r ^ 2 := fun r _ => by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hcongD : (∫ x in Ω.carrier, ‖fderiv ℝ (logCutoff ε z₀) x‖ ^ (2:ℝ))
      = ∫ x in Ω.carrier, ‖fderiv ℝ (logCutoff ε z₀) x‖ ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x =>
      hr2 _ (norm_nonneg _))
  have hcongw : (∫ x in Ω.carrier, |w x| ^ (2:ℝ))
      = ∫ x in Ω.carrier, w x ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only []
      rw [hr2 _ (abs_nonneg _), sq_abs])
  have henergy : (∫ x in Ω.carrier, ‖fderiv ℝ (logCutoff ε z₀) x‖ ^ 2) ^ ((1:ℝ)/2)
      ≤ (2 * Real.pi * C ^ 2 / (-Real.log ε)) ^ ((1:ℝ)/2) :=
    Real.rpow_le_rpow (MeasureTheory.integral_nonneg fun x => by positivity)
      (setIntegral_fderiv_logCutoff_sq_le hε hε1 hC _) (by norm_num)
  calc |∫ x in Ω.carrier, φ x * (fderiv ℝ (logCutoff ε z₀) x v * w x)|
      ≤ Mφ * ‖v‖ * ∫ x in Ω.carrier,
          ‖fderiv ℝ (logCutoff ε z₀) x‖ * |w x| := hstep1
    _ ≤ Mφ * ‖v‖ * ((∫ x in Ω.carrier, w x ^ 2) ^ ((1:ℝ)/2)
          * (∫ x in Ω.carrier, ‖fderiv ℝ (logCutoff ε z₀) x‖ ^ 2) ^ ((1:ℝ)/2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc (∫ x in Ω.carrier, ‖fderiv ℝ (logCutoff ε z₀) x‖ * |w x|)
            ≤ (∫ x in Ω.carrier, ‖fderiv ℝ (logCutoff ε z₀) x‖ ^ (2:ℝ)) ^ ((1:ℝ)/2)
              * (∫ x in Ω.carrier, |w x| ^ (2:ℝ)) ^ ((1:ℝ)/2) := hholder
          _ = (∫ x in Ω.carrier, ‖fderiv ℝ (logCutoff ε z₀) x‖ ^ 2) ^ ((1:ℝ)/2)
              * (∫ x in Ω.carrier, w x ^ 2) ^ ((1:ℝ)/2) := by
                rw [hcongD, hcongw]
          _ = (∫ x in Ω.carrier, w x ^ 2) ^ ((1:ℝ)/2)
              * (∫ x in Ω.carrier, ‖fderiv ℝ (logCutoff ε z₀) x‖ ^ 2) ^ ((1:ℝ)/2) := by
                ring
    _ ≤ Mφ * ‖v‖ * ((∫ x in Ω.carrier, w x ^ 2) ^ ((1:ℝ)/2)
          * (2 * Real.pi * C ^ 2 / (-Real.log ε)) ^ ((1:ℝ)/2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left henergy
          (Real.rpow_nonneg (MeasureTheory.integral_nonneg fun x => by positivity) _)
    _ = Mφ * ‖v‖ * (∫ x in Ω.carrier, w x ^ 2) ^ ((1:ℝ)/2)
          * (2 * Real.pi * C ^ 2 / (-Real.log ε)) ^ ((1:ℝ)/2) := by ring

/-- The weak-derivative property extends through the
puncture at the jet level — full-chart `L²` data for both value and gradient plus the punctured `HasWeakFDerivOn` give the full-chart
`HasWeakFDerivOn`; `W1p.mk` then packages the extended jet. -/
theorem hasWeakFDerivOn_puncture_extend {Ω : Opens ℂ} {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : MeasureTheory.MemLp u 2 ((volume : Measure ℂ).restrict Ω.carrier))
    (hg : MeasureTheory.MemLp g 2 ((volume : Measure ℂ).restrict Ω.carrier))
    (h : TauCeti.HasWeakFDerivOn (volume : Measure ℂ) (puncturedOpens Ω z₀) u
      fun x => innerSL ℝ (g x)) :
    TauCeti.HasWeakFDerivOn (volume : Measure ℂ) Ω u fun x => innerSL ℝ (g x) := by
  rw [TauCeti.hasWeakFDerivOn_iff] at h ⊢
  intro v
  have hident := (TauCeti.hasWeakLineDerivOn_iff_testFunction.mp (h v)).2.2.2
  refine TauCeti.hasWeakLineDerivOn_iff_testFunction.mpr
    ⟨inferInstance, locallyIntegrableOn_of_memLp_two hu,
      locallyIntegrableOn_of_memLp_two (memLp_inner_const hg v), ?_⟩
  intro φ
  obtain ⟨Mφ, hMφ0, hMφ⟩ := exists_bound_of_continuous_compactSupport
    φ.contDiff.continuous φ.hasCompactSupport
  obtain ⟨C, hC0, hC⟩ := exists_transition_deriv_bound
  set u' : ℂ → ℝ := fun x => (innerSL ℝ (g x)) v with hu'def
  have hLD : ∀ x : ℂ, lineDeriv ℝ (φ : ℂ → ℝ) x v = fderiv ℝ (φ : ℂ → ℝ) x v :=
    fun x => (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv
  have hoffφ : ∀ x : ℂ, x ∉ Ω.carrier → (φ : ℂ → ℝ) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hts => hx (φ.tsupport_subset hts)
  have hoffD : ∀ x : ℂ, x ∉ Ω.carrier → fderiv ℝ (φ : ℂ → ℝ) x = 0 := fun x hx =>
    fderiv_of_notMem_tsupport ℝ fun hts => hx (φ.tsupport_subset hts)
  have hψcd : ∀ n : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (logCutoff (εseq n) z₀) Ω.carrier :=
    fun n => (contDiff_logCutoff z₀ (εseq_pos n) (εseq_lt_one n)).contDiffOn
  -- the punctured cutoff tests
  have hξts : ∀ n : ℕ,
      tsupport (smoothMultiplierTest (logCutoff (εseq n) z₀) (hψcd n) φ : ℂ → ℝ)
        ⊆ (puncturedOpens Ω z₀).carrier := by
    intro n z hz
    have h1 : z ∈ tsupport (φ : ℂ → ℝ) := tsupport_mul_subset_right hz
    have h2 : z ∈ tsupport (logCutoff (εseq n) z₀) := tsupport_mul_subset_left hz
    refine ⟨φ.tsupport_subset h1, fun hzz => ?_⟩
    rw [Set.mem_singleton_iff] at hzz
    subst hzz
    exact Set.disjoint_left.mp
      (tsupport_logCutoff_disjoint (εseq_pos n) (εseq_lt_one n)) h2
      (Metric.mem_ball_self (pow_pos (εseq_pos n) 2))
  have hidn : ∀ n : ℕ,
      (∫ x, lineDeriv ℝ
          (smoothMultiplierTest (logCutoff (εseq n) z₀) (hψcd n) φ : ℂ → ℝ) x v
          • u x ∂(volume : Measure ℂ))
        = -∫ x, (smoothMultiplierTest (logCutoff (εseq n) z₀) (hψcd n) φ : ℂ → ℝ) x
          • u' x ∂(volume : Measure ℂ) := by
    intro n
    exact hident ⟨smoothMultiplierTest (logCutoff (εseq n) z₀) (hψcd n) φ,
      (smoothMultiplierTest (logCutoff (εseq n) z₀) (hψcd n) φ).contDiff,
      (smoothMultiplierTest (logCutoff (εseq n) z₀) (hψcd n) φ).hasCompactSupport,
      hξts n⟩
  -- integrability of the pieces
  have hAPint : MeasureTheory.Integrable (fun x => fderiv ℝ (φ : ℂ → ℝ) x v * u x)
      ((volume : Measure ℂ).restrict Ω.carrier) :=
    (memLp_fderiv_test φ.contDiff φ.hasCompactSupport v).integrable_mul hu
  have hφmem : MeasureTheory.MemLp (fun x => (φ : ℂ → ℝ) x) 2
      ((volume : Measure ℂ).restrict Ω.carrier) :=
    (φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).restrict _
  have hφu'int : MeasureTheory.Integrable (fun x => (φ : ℂ → ℝ) x * u' x)
      ((volume : Measure ℂ).restrict Ω.carrier) :=
    hφmem.integrable_mul (memLp_inner_const hg v)
  have hAn_int : ∀ n : ℕ, MeasureTheory.Integrable
      (fun x => logCutoff (εseq n) z₀ x * (fderiv ℝ (φ : ℂ → ℝ) x v * u x))
      ((volume : Measure ℂ).restrict Ω.carrier) := by
    intro n
    apply MeasureTheory.Integrable.mono' hAPint.abs
      (((contDiff_logCutoff z₀ (εseq_pos n) (εseq_lt_one n)).continuous
        |>.aestronglyMeasurable).mul hAPint.aestronglyMeasurable)
    filter_upwards with x
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    apply mul_le_of_le_one_left (by positivity)
    rw [abs_of_nonneg (logCutoff_nonneg z₀ x)]
    exact logCutoff_le_one z₀ x
  have hBn_int : ∀ n : ℕ, MeasureTheory.Integrable
      (fun x => (φ : ℂ → ℝ) x * (fderiv ℝ (logCutoff (εseq n) z₀) x v * u x))
      ((volume : Measure ℂ).restrict Ω.carrier) := by
    intro n
    have hDv : MeasureTheory.MemLp
        (fun x => fderiv ℝ (logCutoff (εseq n) z₀) x v) 2
        ((volume : Measure ℂ).restrict Ω.carrier) := by
      have hcont : Continuous fun x => fderiv ℝ (logCutoff (εseq n) z₀) x v :=
        (continuous_fderiv_logCutoff (εseq_pos n) (εseq_lt_one n)).clm_apply
          continuous_const
      have hcs : HasCompactSupport
          fun x => fderiv ℝ (logCutoff (εseq n) z₀) x v := by
        apply (hasCompactSupport_fderiv_logCutoff (εseq_pos n)
          (εseq_lt_one n)).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v)
        simp
      exact (hcont.memLp_of_hasCompactSupport hcs).restrict _
    have hDu : MeasureTheory.Integrable
        (fun x => fderiv ℝ (logCutoff (εseq n) z₀) x v * u x)
        ((volume : Measure ℂ).restrict Ω.carrier) := hDv.integrable_mul hu
    apply MeasureTheory.Integrable.mono' (hDu.abs.const_mul Mφ)
      (φ.contDiff.continuous.aestronglyMeasurable.mul hDu.aestronglyMeasurable)
    filter_upwards with x
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hMφ x) (by positivity)
  have hRn_int : ∀ n : ℕ, MeasureTheory.Integrable
      (fun x => logCutoff (εseq n) z₀ x * ((φ : ℂ → ℝ) x * u' x))
      ((volume : Measure ℂ).restrict Ω.carrier) := by
    intro n
    apply MeasureTheory.Integrable.mono' hφu'int.abs
      (((contDiff_logCutoff z₀ (εseq_pos n) (εseq_lt_one n)).continuous
        |>.aestronglyMeasurable).mul hφu'int.aestronglyMeasurable)
    filter_upwards with x
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    apply mul_le_of_le_one_left (by positivity)
    rw [abs_of_nonneg (logCutoff_nonneg z₀ x)]
    exact logCutoff_le_one z₀ x
  -- the identity in set-integral split form: A n + B n = − R n
  have hsplitid : ∀ n : ℕ,
      (∫ x in Ω.carrier, logCutoff (εseq n) z₀ x * (fderiv ℝ (φ : ℂ → ℝ) x v * u x))
        + ∫ x in Ω.carrier, (φ : ℂ → ℝ) x
            * (fderiv ℝ (logCutoff (εseq n) z₀) x v * u x)
      = -∫ x in Ω.carrier, logCutoff (εseq n) z₀ x * ((φ : ℂ → ℝ) x * u' x) := by
    intro n
    have h0 := hidn n
    have hLHS : (∫ x, lineDeriv ℝ
        (smoothMultiplierTest (logCutoff (εseq n) z₀) (hψcd n) φ : ℂ → ℝ) x v
        • u x ∂(volume : Measure ℂ))
        = (∫ x in Ω.carrier,
            logCutoff (εseq n) z₀ x * (fderiv ℝ (φ : ℂ → ℝ) x v * u x))
          + ∫ x in Ω.carrier, (φ : ℂ → ℝ) x
              * (fderiv ℝ (logCutoff (εseq n) z₀) x v * u x) := by
      have hptw : ∀ x : ℂ, lineDeriv ℝ
          (smoothMultiplierTest (logCutoff (εseq n) z₀) (hψcd n) φ : ℂ → ℝ) x v
          • u x
          = logCutoff (εseq n) z₀ x * (fderiv ℝ (φ : ℂ → ℝ) x v * u x)
            + (φ : ℂ → ℝ) x * (fderiv ℝ (logCutoff (εseq n) z₀) x v * u x) := by
        intro x
        rw [lineDeriv_smoothMultiplierTest (hψcd n) φ x v, smul_eq_mul, hLD x]
        ring
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)]
      rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Ω.carrier) (fun x hx => by rw [hoffφ x hx, hoffD x hx]; simp)]
      exact MeasureTheory.integral_add (hAn_int n) (hBn_int n)
    have hRHS : (∫ x, (smoothMultiplierTest (logCutoff (εseq n) z₀) (hψcd n) φ
        : ℂ → ℝ) x • u' x ∂(volume : Measure ℂ))
        = ∫ x in Ω.carrier, logCutoff (εseq n) z₀ x * ((φ : ℂ → ℝ) x * u' x) := by
      have hptw : ∀ x : ℂ, (smoothMultiplierTest (logCutoff (εseq n) z₀)
          (hψcd n) φ : ℂ → ℝ) x • u' x
          = logCutoff (εseq n) z₀ x * ((φ : ℂ → ℝ) x * u' x) := by
        intro x
        change (logCutoff (εseq n) z₀ x * (φ : ℂ → ℝ) x) • u' x = _
        rw [smul_eq_mul]
        ring
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)]
      exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Ω.carrier) (fun x hx => by rw [hoffφ x hx]; simp)).symm
    rw [hLHS, hRHS] at h0
    exact h0
  -- the three limits
  have hAlim := tendsto_cutoff_mul_integral (Ω := Ω) z₀ hAPint
  have hRlim := tendsto_cutoff_mul_integral (Ω := Ω) z₀ hφu'int
  have hBlim : Filter.Tendsto (fun n => ∫ x in Ω.carrier, (φ : ℂ → ℝ) x
      * (fderiv ℝ (logCutoff (εseq n) z₀) x v * u x))
      Filter.atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n =>
      Mφ * ‖v‖ * (∫ x in Ω.carrier, u x ^ 2) ^ ((1:ℝ)/2)
        * (2 * Real.pi * C ^ 2 / (-Real.log (εseq n))) ^ ((1:ℝ)/2))
    · intro n
      rw [Real.norm_eq_abs]
      exact cutoff_scalar_pairing_bound (z₀ := z₀) hu (εseq_pos n)
        (εseq_lt_one n) hC hMφ0 hMφ v
    · have hinner : Filter.Tendsto
          (fun n => 2 * Real.pi * C ^ 2 / (-Real.log (εseq n)))
          Filter.atTop (𝓝 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_neg_log_εseq
      have hrpow : Filter.Tendsto
          (fun n => (2 * Real.pi * C ^ 2 / (-Real.log (εseq n))) ^ ((1:ℝ)/2))
          Filter.atTop (𝓝 0) := by
        have hcont : ContinuousAt (fun y : ℝ => y ^ ((1:ℝ)/2)) 0 :=
          Real.continuousAt_rpow_const 0 _ (Or.inr (by norm_num))
        have := hcont.tendsto.comp hinner
        simpa [Function.comp_def,
          Real.zero_rpow (by norm_num : ((1:ℝ)/2) ≠ 0)] using this
      have := hrpow.const_mul
        (Mφ * ‖v‖ * (∫ x in Ω.carrier, u x ^ 2) ^ ((1:ℝ)/2))
      simpa using this
  -- assemble: A n = −R n − B n, limits force the full identity
  have hgoal_set : (∫ x in Ω.carrier, fderiv ℝ (φ : ℂ → ℝ) x v * u x)
      = -∫ x in Ω.carrier, (φ : ℂ → ℝ) x * u' x := by
    have hAlt : Filter.Tendsto
        (fun n => ∫ x in Ω.carrier,
          logCutoff (εseq n) z₀ x * (fderiv ℝ (φ : ℂ → ℝ) x v * u x))
        Filter.atTop
        (𝓝 (-∫ x in Ω.carrier, (φ : ℂ → ℝ) x * u' x)) := by
      have h1 : Filter.Tendsto (fun n =>
          (-∫ x in Ω.carrier, logCutoff (εseq n) z₀ x * ((φ : ℂ → ℝ) x * u' x))
            - ∫ x in Ω.carrier, (φ : ℂ → ℝ) x
                * (fderiv ℝ (logCutoff (εseq n) z₀) x v * u x))
          Filter.atTop
          (𝓝 ((-∫ x in Ω.carrier, (φ : ℂ → ℝ) x * u' x) - 0)) :=
        (hRlim.neg).sub hBlim
      rw [sub_zero] at h1
      apply h1.congr
      intro n
      have := hsplitid n
      linarith
    exact tendsto_nhds_unique hAlim hAlt
  -- globalize
  have hL : (∫ x, lineDeriv ℝ (φ : ℂ → ℝ) x v • u x ∂(volume : Measure ℂ))
      = ∫ x in Ω.carrier, fderiv ℝ (φ : ℂ → ℝ) x v * u x := by
    have hptw : ∀ x : ℂ, lineDeriv ℝ (φ : ℂ → ℝ) x v • u x
        = fderiv ℝ (φ : ℂ → ℝ) x v * u x := fun x => by
      rw [hLD x, smul_eq_mul]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Ω.carrier) (fun x hx => by rw [hoffD x hx]; simp)).symm
  have hR : (∫ x, (φ : ℂ → ℝ) x • u' x ∂(volume : Measure ℂ))
      = ∫ x in Ω.carrier, (φ : ℂ → ℝ) x * u' x := by
    have hptw : ∀ x : ℂ, (φ : ℂ → ℝ) x • u' x = (φ : ℂ → ℝ) x * u' x :=
      fun x => smul_eq_mul _ _
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Ω.carrier) (fun x hx => by rw [hoffφ x hx]; simp)).symm
  rw [hL, hR]
  exact hgoal_set

/-- A punctured weak jet with
full-chart `L²` data yields a `W1p` element on the full chart whose value and
gradient agree a.e. with the data — `W1p.mk` applied to the extended property. -/
theorem exists_w1p_of_punctured_jet {Ω : Opens ℂ} {u : ℂ → ℝ} {g : ℂ → ℂ}
    (hu : MeasureTheory.MemLp u 2 ((volume : Measure ℂ).restrict Ω.carrier))
    (hg : MeasureTheory.MemLp g 2 ((volume : Measure ℂ).restrict Ω.carrier))
    (h : TauCeti.HasWeakFDerivOn (volume : Measure ℂ) (puncturedOpens Ω z₀) u
      fun x => innerSL ℝ (g x)) :
    ∃ û : TauCeti.W1p (volume : Measure ℂ) Ω 2,
      (TauCeti.W1p.value û : ℂ → ℝ)
          =ᵐ[(volume : Measure ℂ).restrict Ω.carrier] u
        ∧ (TauCeti.W1p.gradient û : ℂ → ℂ)
            =ᵐ[(volume : Measure ℂ).restrict Ω.carrier] g := by
  have hfull := hasWeakFDerivOn_puncture_extend hu hg h
  have hmk : TauCeti.HasWeakFDerivOn (volume : Measure ℂ) Ω
      (MeasureTheory.MemLp.toLp u hu)
      fun x => innerSL ℝ ((MeasureTheory.MemLp.toLp g hg : ℂ → ℂ) x) := by
    rw [TauCeti.hasWeakFDerivOn_iff]
    intro v
    have h1 := (hfull.hasWeakLineDerivOn v).congr_ae
      (MeasureTheory.MemLp.coeFn_toLp hu).symm
    apply h1.congr_ae_deriv
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp hg] with x hx
    rw [hx]
  refine ⟨TauCeti.W1p.mk (hu.toLp u) (hg.toLp g) hmk, ?_, ?_⟩
  · rw [TauCeti.W1p.value_mk]
    exact MeasureTheory.MemLp.coeFn_toLp hu
  · rw [TauCeti.W1p.gradient_mk]
    exact MeasureTheory.MemLp.coeFn_toLp hg

end E6

end KsIndex.PunctureRemoval
