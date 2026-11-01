module

public import KsIndexLean.ZeroJoinDirichlet
public import KsIndexLean.DilationContinuity
public import KsIndexLean.MollificationSupport
public import KsIndexLean.MollifiedReflectionDerivative
public import KsIndexLean.L2MeasureRestriction

@[expose] public section


/-!
# Mollification followed by dilation for Dirichlet approximation

Let `rₙ` be the shrinking mollifier radius and `cₙ = (1 + rₙ)²`. The
approximants are `z ↦ compactMollify (shrinkingMollifier n) u (cₙ • z)`.
Mollification gives smoothness before dilation, so the classical chain rule
computes their derivatives.

If `u` vanishes outside the closed unit disk, each approximant vanishes on
the full `rₙ / (2 (1 + rₙ))` neighborhood of the unit circle, and on its
closed exterior. The neighborhood covers all circle points uniformly.

For compactly supported `u ∈ L²`, the values converge to `u` in L².
For `u ∈ L²` and a global weak derivative `J` whose directional components are in L²
and compactly supported, the classical derivatives converge to `J` in L²
in each fixed direction. These convergence statements have separate support
hypotheses. The proofs combine mollification convergence with continuity of
dilation; the derivative scaling cancels the L² dilation factor in the
mollification-error term.
-/

open Set MeasureTheory Filter Topology Metric
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket

/-- The per-n dilation factor: `(1 + rOut n)²` for the shrinking mollifier. -/
def dilationFactor (n : ℕ) : ℝ := (1 + (shrinkingMollifier n).rOut) ^ 2

lemma one_le_dilationFactor (n : ℕ) : 1 ≤ dilationFactor n := by
  have h := (shrinkingMollifier n).rOut_pos
  simp only [dilationFactor]
  nlinarith

lemma dilationFactor_tendsto : Tendsto dilationFactor atTop (𝓝 1) := by
  have h := shrinkingMollifier_radius
  have hh : Tendsto (fun n => (1 + (shrinkingMollifier n).rOut) ^ 2) atTop
      (𝓝 ((1 + 0) ^ 2)) := (tendsto_const_nhds.add h).pow 2
  have he : dilationFactor = fun n => (1 + (shrinkingMollifier n).rOut) ^ 2 := rfl
  rw [he]
  simpa using hh

/-- Classical chain rule for a dilation of a smooth function. -/
lemma fderiv_comp_dilation {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (r : ℝ) (z : ℂ) :
    fderiv ℝ (fun w => f (r • w)) z = r • fderiv ℝ f (r • z) := by
  have hd : DifferentiableAt ℝ f (r • z) :=
    (hf.differentiable (by norm_num)).differentiableAt
  have hs : DifferentiableAt ℝ (fun w : ℂ => r • w) z :=
    (differentiable_id.const_smul r).differentiableAt
  rw [show (fun w => f (r • w)) = f ∘ (fun w : ℂ => r • w) from rfl,
      fderiv_comp z hd hs]
  have hfs : fderiv ℝ (fun w : ℂ => r • w) z =
      r • ContinuousLinearMap.id ℝ ℂ := by
    have hco : (fun w : ℂ => r • w) =
        ⇑(r • ContinuousLinearMap.id ℝ ℂ) := by
      ext w
      simp
    rw [hco]
    exact (r • ContinuousLinearMap.id ℝ ℂ).fderiv
  ext d
  simp [hfs]

/-- Smoothness of the dilated mollification. -/
lemma contDiff_dilated_mollify (φ : ContDiffBump (0 : ℂ)) {u : ℂ → ℂ}
    (hu : MemLp u 2 volume) (r : ℝ) :
    ContDiff ℝ ∞ (fun z => compactMollify φ u (r • z)) :=
  (compactMollify_smooth φ hu).comp (contDiff_const_smul r)

/-- **Uniform circle-neighborhood vanishing:**
if the input vanishes outside the closed unit disk, its mollification at
radius `rOut` vanishes on `‖z‖ > 1 + rOut`, so the `(1+rOut)²`-dilated
mollification vanishes on the full `rOut/(2(1+rOut))`-neighborhood of the
whole circle. One region covers the arc, the endpoints, and the punctures. -/
theorem dilated_mollify_vanish_near_circle (n : ℕ) {u : ℂ → ℂ}
    (hu : ∀ z : ℂ, 1 < ‖z‖ → u z = 0) :
    ∀ w p : ℂ, ‖p‖ = 1 →
      ‖w - p‖ < (shrinkingMollifier n).rOut / (2 * (1 + (shrinkingMollifier n).rOut)) →
      compactMollify (shrinkingMollifier n) u (dilationFactor n • w) = 0 := by
  intro w p hp hw
  set r := (shrinkingMollifier n).rOut with hrdef
  have hr : 0 < r := (shrinkingMollifier n).rOut_pos
  have hsub : tsupport u ⊆ Metric.closedBall 0 1 := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    exact hz (hu z (not_le.mp h))
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  have hth := compactMollify_tsupport_subset (shrinkingMollifier n) u hm
  have hball : dilationFactor n • w ∈ Metric.closedBall (0 : ℂ) (r + 1) := by
    have h1 : cthickening r (tsupport u) ⊆
        cthickening r (Metric.closedBall (0 : ℂ) 1) := cthickening_subset_of_subset r hsub
    have h2 := h1 hth
    rwa [cthickening_closedBall hr.le zero_le_one] at h2
  have hwn : 1 - r / (2 * (1 + r)) < ‖w‖ := by
    have h3 := norm_sub_norm_le p w
    rw [hp, norm_sub_rev] at h3
    linarith
  have h1r : (0 : ℝ) < 1 + r := by linarith
  have hwlow : 1 / (1 + r) < ‖w‖ := by
    have hkey : 1 / (1 + r) < 1 - r / (2 * (1 + r)) := by
      rw [div_lt_iff₀ h1r, sub_mul, div_mul_eq_mul_div, mul_comm (2 : ℝ) (1 + r),
        mul_div_assoc]
      have : r * ((1 + r) / ((1 + r) * 2)) = r / 2 := by
        field_simp
      rw [one_mul, this]
      linarith
    linarith
  have hcw : ‖dilationFactor n • w‖ = (1 + r) ^ 2 * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    congr 1
    rw [abs_of_pos (lt_of_lt_of_le one_pos (one_le_dilationFactor n))]
    rfl
  have hgt : 1 + r < ‖dilationFactor n • w‖ := by
    rw [hcw]
    have hsq : (1 + r) ^ 2 * (1 / (1 + r)) = 1 + r := by
      field_simp
    calc 1 + r = (1 + r) ^ 2 * (1 / (1 + r)) := hsq.symm
      _ < (1 + r) ^ 2 * ‖w‖ := by
          apply mul_lt_mul_of_pos_left hwlow
          positivity
  have hmem := hball
  simp only [Metric.mem_closedBall, dist_zero_right] at hmem
  linarith

/-- The dilated mollification vanishes on the closed exterior of the disk:
`‖cₙ • w‖ = (1+r)²‖w‖ > 1 + r` for `‖w‖ ≥ 1`, outside the thickened
support. -/
theorem dilated_mollify_vanish_exterior (n : ℕ) {u : ℂ → ℂ}
    (hu : ∀ z : ℂ, 1 < ‖z‖ → u z = 0) :
    ∀ w : ℂ, 1 ≤ ‖w‖ →
      compactMollify (shrinkingMollifier n) u (dilationFactor n • w) = 0 := by
  intro w hw
  set r := (shrinkingMollifier n).rOut with hrdef
  have hr : 0 < r := (shrinkingMollifier n).rOut_pos
  have hsub : tsupport u ⊆ Metric.closedBall 0 1 := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    exact hz (hu z (not_le.mp h))
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  have hth := compactMollify_tsupport_subset (shrinkingMollifier n) u hm
  have hball : dilationFactor n • w ∈ Metric.closedBall (0 : ℂ) (r + 1) := by
    have h1 : cthickening r (tsupport u) ⊆
        cthickening r (Metric.closedBall (0 : ℂ) 1) :=
      cthickening_subset_of_subset r hsub
    have h2 := h1 hth
    rwa [cthickening_closedBall hr.le zero_le_one] at h2
  have hcw : ‖dilationFactor n • w‖ = (1 + r) ^ 2 * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    congr 1
    rw [abs_of_pos (lt_of_lt_of_le one_pos (one_le_dilationFactor n))]
    rfl
  have hmem := hball
  simp only [Metric.mem_closedBall, dist_zero_right] at hmem
  rw [hcw] at hmem
  nlinarith

/-- L² convergence of the dilated mollifications to the original (values):
`|cₙ|⁻¹`-contractivity handles the mollification error, and L² continuity of
dilation handles the dilated limit. -/
theorem tendsto_dilated_mollify_value {u : ℂ → ℂ}
    (hu : MemLp u 2 volume) (hc : HasCompactSupport u) :
    Tendsto (fun n => eLpNorm
        (fun z => compactMollify (shrinkingMollifier n) u (dilationFactor n • z) - u z)
        2 volume) atTop (𝓝 0) := by
  have hcn0 : ∀ n, dilationFactor n ≠ 0 := fun n =>
    (lt_of_lt_of_le one_pos (one_le_dilationFactor n)).ne'
  have hmoll : Tendsto (fun n =>
      eLpNorm (compactMollify (shrinkingMollifier n) u - u) 2 volume)
      atTop (𝓝 0) := by
    have ht := compactMollify_tendsto shrinkingMollifier_radius hu hc
    rwa [Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      _ (fun n => compactMollify_memLp _ hu hc) _ hu] at ht
  have hdil := tendsto_eLpNorm_dilation_sub hu one_le_dilationFactor
    dilationFactor_tendsto
  have hsum : Tendsto (fun n =>
      eLpNorm (compactMollify (shrinkingMollifier n) u - u) 2 volume +
        eLpNorm (fun z => u (dilationFactor n • z) - u z) 2 volume)
      atTop (𝓝 0) := by
    simpa using hmoll.add hdil
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · exact Eventually.of_forall fun n => zero_le
  · apply Eventually.of_forall
    intro n
    have hMu : AEStronglyMeasurable
        (compactMollify (shrinkingMollifier n) u - u) volume :=
      ((compactMollify_smooth _ hu).continuous.aestronglyMeasurable).sub hu.aestronglyMeasurable
    have hsplit : (fun z =>
        compactMollify (shrinkingMollifier n) u (dilationFactor n • z) - u z) =
        (fun z => (compactMollify (shrinkingMollifier n) u - u)
            (dilationFactor n • z)) +
          fun z => u (dilationFactor n • z) - u z := by
      funext z
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [hsplit]
    have h1m : AEStronglyMeasurable (fun z =>
        (compactMollify (shrinkingMollifier n) u - u) (dilationFactor n • z))
        volume := by
      have := hMu.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℂ)) (hcn0 n))
      simpa [Function.comp_def] using this
    have h2m : AEStronglyMeasurable
        (fun z => u (dilationFactor n • z) - u z) volume := by
      have hu1 := hu.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℂ)) (hcn0 n))
      exact (show AEStronglyMeasurable (fun z => u (dilationFactor n • z)) volume by
        simpa [Function.comp_def] using hu1).sub hu.aestronglyMeasurable
    calc eLpNorm ((fun z => (compactMollify (shrinkingMollifier n) u - u)
            (dilationFactor n • z)) +
          fun z => u (dilationFactor n • z) - u z) 2 volume
        ≤ eLpNorm (fun z => (compactMollify (shrinkingMollifier n) u - u)
              (dilationFactor n • z)) 2 volume +
          eLpNorm (fun z => u (dilationFactor n • z) - u z) 2 volume :=
          eLpNorm_add_le (by norm_num)
      _ ≤ eLpNorm (compactMollify (shrinkingMollifier n) u - u) 2 volume +
          eLpNorm (fun z => u (dilationFactor n • z) - u z) 2 volume := by
          gcongr
          rw [eLpNorm_comp_smul hMu (hcn0 n)]
          calc ENNReal.ofReal |dilationFactor n|⁻¹ *
                eLpNorm (compactMollify (shrinkingMollifier n) u - u) 2 volume
              ≤ 1 * eLpNorm (compactMollify (shrinkingMollifier n) u - u)
                  2 volume := by
                gcongr
                rw [← ENNReal.ofReal_one]
                apply ENNReal.ofReal_le_ofReal
                rw [abs_of_pos (lt_of_lt_of_le one_pos (one_le_dilationFactor n))]
                exact inv_le_one_of_one_le₀ (one_le_dilationFactor n)
            _ = eLpNorm (compactMollify (shrinkingMollifier n) u - u) 2 volume :=
                one_mul _

lemma dilationFactor_le_four (n : ℕ) : dilationFactor n ≤ 4 := by
  have h1 : (shrinkingMollifier n).rOut ≤ 1 := by
    simp only [shrinkingMollifier]
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have h0 := (shrinkingMollifier n).rOut_pos
  simp only [dilationFactor]
  nlinarith

/-- L² convergence of the classical jets of the dilated mollifications to the
weak jet, per direction. The chain rule (`fderiv_comp_dilation`) plus the
mollified-derivative identification (`compactMollify_fderiv`) turn the
jet into `cₙ • Mₙ(J·d)(cₙ•z)`; the three-term split then converges with the
`cₙ`/`|cₙ|⁻¹` scaling cancelling exactly on the mollification term. -/
theorem tendsto_dilated_mollify_jet {u : ℂ → ℂ} {J : ℂ → ℂ →L[ℝ] ℂ}
    (hu : MemLp u 2 volume)
    (hJ : ∀ d, MemLp (fun z => J z d) 2 volume)
    (hcJ : ∀ d, HasCompactSupport (fun z => J z d))
    (hw : TauCeti.HasWeakFDerivOn volume ⊤ u J) (d : ℂ) :
    Tendsto (fun n => eLpNorm
        (fun z => fderiv ℝ
            (fun w => compactMollify (shrinkingMollifier n) u (dilationFactor n • w)) z d
          - J z d)
        2 volume) atTop (𝓝 0) := by
  have hcpos : ∀ n, (0 : ℝ) < dilationFactor n := fun n =>
    lt_of_lt_of_le one_pos (one_le_dilationFactor n)
  have hcn0 : ∀ n, dilationFactor n ≠ 0 := fun n => (hcpos n).ne'
  set A : ℕ → ℂ → ℂ :=
    fun n => compactMollify (shrinkingMollifier n) (fun w => J w d) with hAdef
  have hAsm : ∀ n, AEStronglyMeasurable (A n - fun z => J z d) volume := fun n =>
    ((compactMollify_smooth _ (hJ d)).continuous.aestronglyMeasurable).sub (hJ d).aestronglyMeasurable
  -- identify the classical jet
  have hjet : ∀ n, (fun z => fderiv ℝ
      (fun w => compactMollify (shrinkingMollifier n) u (dilationFactor n • w)) z d
        - J z d) =
      fun z => dilationFactor n • (A n (dilationFactor n • z)) - J z d := by
    intro n
    funext z
    rw [fderiv_comp_dilation (compactMollify_smooth _ hu) (dilationFactor n) z]
    simp only [smul_apply, hAdef]
    rw [compactMollify_fderiv _ hu hw d]
  -- the three error terms
  have hmoll : Tendsto (fun n => eLpNorm (A n - fun z => J z d) 2 volume)
      atTop (𝓝 0) := by
    have ht := compactMollify_tendsto shrinkingMollifier_radius (hJ d) (hcJ d)
    rwa [Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      _ (fun n => compactMollify_memLp _ (hJ d) (hcJ d)) _ (hJ d)] at ht
  have hdil := tendsto_eLpNorm_dilation_sub (hJ d) one_le_dilationFactor
    dilationFactor_tendsto
  have hdil4 : Tendsto (fun n => ENNReal.ofReal 4 *
      eLpNorm (fun z => J (dilationFactor n • z) d - J z d) 2 volume)
      atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal 4) hdil
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have hscal : Tendsto (fun n => ‖dilationFactor n - 1‖ₑ *
      eLpNorm (fun z => J z d) 2 volume) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => dilationFactor n - 1) atTop (𝓝 0) := by
      have := dilationFactor_tendsto.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
      simpa using this
    have h2 : Tendsto (fun n => ‖dilationFactor n - 1‖ₑ) atTop (𝓝 0) := by
      have := (continuous_enorm.tendsto (0 : ℝ)).comp h1
      simpa [Function.comp_def] using this
    have := ENNReal.Tendsto.mul_const h2 (Or.inr (hJ d).eLpNorm_lt_top.ne)
    simpa using this
  have hsum : Tendsto (fun n =>
      eLpNorm (A n - fun z => J z d) 2 volume +
        (ENNReal.ofReal 4 *
            eLpNorm (fun z => J (dilationFactor n • z) d - J z d) 2 volume +
          ‖dilationFactor n - 1‖ₑ * eLpNorm (fun z => J z d) 2 volume))
      atTop (𝓝 0) := by
    simpa using hmoll.add (hdil4.add hscal)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · exact Eventually.of_forall fun n => zero_le
  · apply Eventually.of_forall
    intro n
    rw [hjet n]
    -- three-way split of the integrand
    have hsplit : (fun z => dilationFactor n • (A n (dilationFactor n • z)) - J z d) =
        (fun z => dilationFactor n •
            ((A n - fun w => J w d) (dilationFactor n • z))) +
          ((fun z => dilationFactor n •
              (J (dilationFactor n • z) d - J z d)) +
            fun z => (dilationFactor n - 1) • J z d) := by
      funext z
      simp only [Pi.add_apply, Pi.sub_apply, smul_sub, sub_smul, one_smul]
      ring
    rw [hsplit]
    have hq := Measure.quasiMeasurePreserving_smul
      (μ := (volume : Measure ℂ)) (hcn0 n)
    have h1m : AEStronglyMeasurable (fun z => dilationFactor n •
        ((A n - fun w => J w d) (dilationFactor n • z))) volume := by
      have hcomp : AEStronglyMeasurable
          (fun z => (A n - fun w => J w d) (dilationFactor n • z)) volume := by
        simpa [Function.comp_def] using (hAsm n).comp_quasiMeasurePreserving hq
      simpa [Pi.smul_def] using hcomp.const_smul (dilationFactor n)
    have hJc : AEStronglyMeasurable
        (fun z => J (dilationFactor n • z) d) volume := by
      have := (hJ d).aestronglyMeasurable.comp_quasiMeasurePreserving hq
      simpa [Function.comp_def] using this
    have h2m : AEStronglyMeasurable (fun z => dilationFactor n •
        (J (dilationFactor n • z) d - J z d)) volume := by
      simpa [Pi.smul_def, Pi.sub_def] using
        (hJc.sub (hJ d).aestronglyMeasurable).const_smul (dilationFactor n)
    have h3m : AEStronglyMeasurable
        (fun z => (dilationFactor n - 1) • J z d) volume := by
      simpa [Pi.smul_def] using (hJ d).aestronglyMeasurable.const_smul (dilationFactor n - 1)
    calc eLpNorm _ 2 volume
        ≤ eLpNorm (fun z => dilationFactor n •
              ((A n - fun w => J w d) (dilationFactor n • z))) 2 volume +
          eLpNorm ((fun z => dilationFactor n •
              (J (dilationFactor n • z) d - J z d)) +
            fun z => (dilationFactor n - 1) • J z d) 2 volume :=
          eLpNorm_add_le (by norm_num)
      _ ≤ eLpNorm (fun z => dilationFactor n •
              ((A n - fun w => J w d) (dilationFactor n • z))) 2 volume +
          (eLpNorm (fun z => dilationFactor n •
              (J (dilationFactor n • z) d - J z d)) 2 volume +
            eLpNorm (fun z => (dilationFactor n - 1) • J z d) 2 volume) := by
          gcongr
          exact eLpNorm_add_le (by norm_num)
      _ ≤ eLpNorm (A n - fun z => J z d) 2 volume +
          (ENNReal.ofReal 4 *
              eLpNorm (fun z => J (dilationFactor n • z) d - J z d) 2 volume +
            ‖dilationFactor n - 1‖ₑ * eLpNorm (fun z => J z d) 2 volume) := by
          gcongr
          · -- exact cancellation: ‖c‖ₑ · ofReal|c|⁻¹ = 1
            have hfe : (fun z => dilationFactor n •
                ((A n - fun w => J w d) (dilationFactor n • z))) =
                dilationFactor n • (fun z =>
                  (A n - fun w => J w d) (dilationFactor n • z)) := rfl
            rw [hfe, eLpNorm_const_smul, eLpNorm_comp_smul (hAsm n) (hcn0 n),
              ← mul_assoc]
            have hone : ‖dilationFactor n‖ₑ * ENNReal.ofReal |dilationFactor n|⁻¹
                = 1 := by
              rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (abs_nonneg _),
                mul_inv_cancel₀ (abs_ne_zero.mpr (hcn0 n)), ENNReal.ofReal_one]
            rw [hone, one_mul]
          · -- ‖c‖ₑ ≤ ofReal 4
            have hfe : (fun z => dilationFactor n •
                (J (dilationFactor n • z) d - J z d)) =
                dilationFactor n • (fun z =>
                  J (dilationFactor n • z) d - J z d) := rfl
            rw [hfe, eLpNorm_const_smul]
            gcongr
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal
              (by rw [abs_of_pos (hcpos n)]; exact dilationFactor_le_four n)
          · have hfe : (fun z => (dilationFactor n - 1) • J z d) =
                (dilationFactor n - 1) • (fun z => J z d) := rfl
            rw [hfe, eLpNorm_const_smul]

end KsIndex.Trace
