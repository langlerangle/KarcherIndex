module

/-
KsIndexLean — Smoothness and derivative estimates for the amplitude root `s = √sinc`.

Near the junction the test-field amplitude is `√(sin x) = √x · s(x)` with `s = √sinc`; after the
Fresnel substitution `x = t²` the peeled amplitude of `fresnel_peel` is built from `s(t²)` and the
collar cut.  The estimates on `s` used by the junction amplitude hold on `[0,1]`:

* smoothness of `Real.sinc` through the removable singularity — analyticity at `0` via the
  `dslope` power series (`sinc = dslope sin 0`), analyticity elsewhere as a quotient;
* closed forms for `sinc′`, `sinc″` off the origin, and the FTC numerator identities
  `sin y − y cos y = ∫₀^y t sin t` and `2 sin y − 2y cos y − y² sin y = ∫₀^y −t² cos t`,
  giving the uniform bounds `|sinc′ y| ≤ y/3` (all `y ≥ 0`) and `|sinc″ y| ≤ 1/3`
  (the bound at `y = 0` by continuity along `𝓝[>] 0` — no value computation at the origin);
* the floor `sinc ≥ 5/6` on `[0,1]` (from `sin y > y − y³/6`), hence `s ≥ 5/6` there;
* the derivative package for `s`: `HasDerivAt s (ds y) y` and `HasDerivAt ds (d2s y) y` with
  `ds = sinc′/(2s)`, `d2s = sinc″/(2s) − (sinc′)²/(4s³)`, and the bounds
  `|ds y| ≤ y/5`, `|d2s y| ≤ 1/2` on `[0,1]`.

The bound `|ds y| ≤ y/5` records linear vanishing at the origin. Together with the chain rule
for `s(t²)`, it controls the contribution of this factor to the junction amplitude derivatives.
The functions `ds` and `d2s` are defined on all of ℝ; their identification as derivatives of
`s` and `ds` is proved here for points in `[0,1]`.
-/
public import Mathlib

@[expose] public section


noncomputable section

open Real Set Filter MeasureTheory intervalIntegral Topology

namespace KsIndex.SincKit

/-! ### A division estimate -/

/-- `|a/b| ≤ c/d` from `|a| ≤ c` and `0 < d ≤ b`, via `mul_le_mul` on inverses. -/
lemma abs_div_le {a b c d : ℝ} (ha : |a| ≤ c) (hd : 0 < d) (hdb : d ≤ b) :
    |a / b| ≤ c / d := by
  have hb : 0 < b := lt_of_lt_of_le hd hdb
  rw [abs_div, abs_of_pos hb, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul ha (inv_anti₀ hd hdb) (inv_nonneg.mpr hb.le)
    (le_trans (abs_nonneg a) ha)

/-! ### Analyticity and smoothness of `sinc` -/

/-- `sinc` is analytic everywhere: at `0` via the `dslope` power series of `sin`, elsewhere as
the quotient `sin y / y`. -/
lemma analyticAt_sinc (y : ℝ) : AnalyticAt ℝ Real.sinc y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [Real.sinc_eq_dslope]
    obtain ⟨p, hp⟩ := Real.analyticAt_sin (x := (0 : ℝ))
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hdiv : AnalyticAt ℝ (Real.sin / id) y :=
      Real.analyticAt_sin.div analyticAt_id hy
    refine hdiv.congr ?_
    filter_upwards [eventually_ne_nhds hy] with t ht
    simp [Pi.div_apply, Real.sinc_of_ne_zero ht]

lemma contDiff_sinc : ContDiff ℝ 2 Real.sinc :=
  contDiff_iff_contDiffAt.mpr fun y => (analyticAt_sinc y).contDiffAt

lemma hasDerivAt_sinc (y : ℝ) : HasDerivAt Real.sinc (deriv Real.sinc y) y :=
  (analyticAt_sinc y).differentiableAt.hasDerivAt

lemma analyticAt_dsinc (y : ℝ) : AnalyticAt ℝ (deriv Real.sinc) y :=
  (analyticAt_sinc y).deriv

lemma hasDerivAt_dsinc (y : ℝ) :
    HasDerivAt (deriv Real.sinc) (deriv (deriv Real.sinc) y) y :=
  (analyticAt_dsinc y).differentiableAt.hasDerivAt

lemma continuous_dsinc : Continuous (deriv Real.sinc) :=
  continuous_iff_continuousAt.mpr fun y => (analyticAt_dsinc y).continuousAt

lemma continuous_d2sinc : Continuous (deriv (deriv Real.sinc)) :=
  continuous_iff_continuousAt.mpr fun y => ((analyticAt_dsinc y).deriv).continuousAt

/-! ### Closed forms off the origin -/

/-- `sinc′ y = (y cos y − sin y)/y²` for `y ≠ 0`. -/
lemma deriv_sinc_of_ne {y : ℝ} (hy : y ≠ 0) :
    deriv Real.sinc y = (Real.cos y * y - Real.sin y) / y ^ 2 := by
  have hev : (fun t : ℝ => Real.sin t / t) =ᶠ[nhds y] Real.sinc := by
    filter_upwards [eventually_ne_nhds hy] with t ht
    rw [Real.sinc_of_ne_zero ht]
  rw [← hev.deriv_eq]
  have h : HasDerivAt (fun t : ℝ => Real.sin t / t)
      ((Real.cos y * y - Real.sin y * 1) / y ^ 2) y :=
    (Real.hasDerivAt_sin y).div (hasDerivAt_id y) hy
  rw [h.deriv]
  ring

/-- `sinc″ y = (2 sin y − 2y cos y − y² sin y)/y³` for `y ≠ 0`. -/
lemma deriv2_sinc_of_ne {y : ℝ} (hy : y ≠ 0) :
    deriv (deriv Real.sinc) y
      = (2 * Real.sin y - 2 * y * Real.cos y - y ^ 2 * Real.sin y) / y ^ 3 := by
  have hev : (fun t : ℝ => (Real.cos t * t - Real.sin t) / t ^ 2)
      =ᶠ[nhds y] deriv Real.sinc := by
    filter_upwards [eventually_ne_nhds hy] with t ht
    rw [deriv_sinc_of_ne ht]
  rw [← hev.deriv_eq]
  have hnum : HasDerivAt (fun t : ℝ => Real.cos t * t - Real.sin t)
      (-Real.sin y * y + Real.cos y * 1 - Real.cos y) y :=
    ((Real.hasDerivAt_cos y).mul (hasDerivAt_id y)).sub (Real.hasDerivAt_sin y)
  have hden : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by
    simpa using hasDerivAt_pow 2 y
  have h : HasDerivAt (fun t : ℝ => (Real.cos t * t - Real.sin t) / t ^ 2)
      (((-Real.sin y * y + Real.cos y * 1 - Real.cos y) * y ^ 2
        - (Real.cos y * y - Real.sin y) * (2 * y)) / (y ^ 2) ^ 2) y :=
    hnum.div hden (pow_ne_zero 2 hy)
  rw [h.deriv]
  field_simp
  ring

/-! ### The FTC numerator identities and bounds -/

/-- `sin y − y cos y = ∫₀^y t sin t`. -/
lemma sin_sub_mul_cos_eq (y : ℝ) :
    Real.sin y - y * Real.cos y = ∫ t in (0:ℝ)..y, t * Real.sin t := by
  have h : ∀ t ∈ Set.uIcc (0:ℝ) y,
      HasDerivAt (fun u : ℝ => Real.sin u - u * Real.cos u) (t * Real.sin t) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => u * Real.cos u)
        (1 * Real.cos t + t * -Real.sin t) t :=
      (hasDerivAt_id t).mul (Real.hasDerivAt_cos t)
    have h2 := (Real.hasDerivAt_sin t).sub h1
    have heq : Real.cos t - (1 * Real.cos t + t * -Real.sin t) = t * Real.sin t := by ring
    rw [heq] at h2
    exact h2
  rw [integral_eq_sub_of_hasDerivAt h
    ((continuous_id.mul Real.continuous_sin).intervalIntegrable _ _)]
  simp

/-- The first-derivative numerator bound: `|sin y − y cos y| ≤ y³/3` for `y ≥ 0`. -/
lemma abs_sin_sub_mul_cos_le {y : ℝ} (hy : 0 ≤ y) :
    |Real.sin y - y * Real.cos y| ≤ y ^ 3 / 3 := by
  rw [sin_sub_mul_cos_eq, ← Real.norm_eq_abs]
  have hle : ‖∫ t in (0:ℝ)..y, t * Real.sin t‖ ≤ ∫ t in (0:ℝ)..y, t ^ 2 := by
    refine intervalIntegral.norm_integral_le_of_norm_le hy
      (Filter.Eventually.of_forall fun t ht => ?_)
      ((continuousOn_id.pow 2).intervalIntegrable)
    have ht0 : 0 ≤ t := le_of_lt ht.1
    calc ‖t * Real.sin t‖ = |t| * |Real.sin t| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |t| * |t| := by
          exact mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (abs_nonneg t)
      _ = t ^ 2 := by rw [abs_of_nonneg ht0]; ring
  calc ‖∫ t in (0:ℝ)..y, t * Real.sin t‖ ≤ ∫ t in (0:ℝ)..y, t ^ 2 := hle
    _ = y ^ 3 / 3 := by rw [integral_pow]; norm_num

/-- The second-derivative numerator identity:
`2 sin y − 2y cos y − y² sin y = ∫₀^y −(t² cos t)`. -/
lemma second_numerator_eq (y : ℝ) :
    2 * Real.sin y - 2 * y * Real.cos y - y ^ 2 * Real.sin y
      = ∫ t in (0:ℝ)..y, -(t ^ 2 * Real.cos t) := by
  have h : ∀ t ∈ Set.uIcc (0:ℝ) y,
      HasDerivAt
        (fun u : ℝ => 2 * Real.sin u - 2 * u * Real.cos u - u ^ 2 * Real.sin u)
        (-(t ^ 2 * Real.cos t)) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => 2 * Real.sin u) (2 * Real.cos t) t :=
      (Real.hasDerivAt_sin t).const_mul 2
    have h2 : HasDerivAt (fun u : ℝ => 2 * u * Real.cos u)
        (2 * 1 * Real.cos t + 2 * t * -Real.sin t) t := by
      have hid : HasDerivAt (fun u : ℝ => 2 * u) (2 * 1) t := (hasDerivAt_id t).const_mul 2
      exact hid.mul (Real.hasDerivAt_cos t)
    have hp : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h3 : HasDerivAt (fun u : ℝ => u ^ 2 * Real.sin u)
        (2 * t * Real.sin t + t ^ 2 * Real.cos t) t := hp.mul (Real.hasDerivAt_sin t)
    have h4 := (h1.sub h2).sub h3
    have heq : 2 * Real.cos t - (2 * 1 * Real.cos t + 2 * t * -Real.sin t)
        - (2 * t * Real.sin t + t ^ 2 * Real.cos t) = -(t ^ 2 * Real.cos t) := by ring
    rw [heq] at h4
    exact h4
  rw [integral_eq_sub_of_hasDerivAt h
    ((((continuous_pow 2).mul Real.continuous_cos).neg).intervalIntegrable _ _)]
  simp

/-- The second-derivative numerator bound for `y ≥ 0`. -/
lemma abs_second_numerator_le {y : ℝ} (hy : 0 ≤ y) :
    |2 * Real.sin y - 2 * y * Real.cos y - y ^ 2 * Real.sin y| ≤ y ^ 3 / 3 := by
  rw [second_numerator_eq, ← Real.norm_eq_abs]
  have hle : ‖∫ t in (0:ℝ)..y, -(t ^ 2 * Real.cos t)‖ ≤ ∫ t in (0:ℝ)..y, t ^ 2 := by
    refine intervalIntegral.norm_integral_le_of_norm_le hy
      (Filter.Eventually.of_forall fun t ht => ?_)
      ((continuousOn_id.pow 2).intervalIntegrable)
    have ht0 : 0 ≤ t := le_of_lt ht.1
    calc ‖-(t ^ 2 * Real.cos t)‖ = |t ^ 2| * |Real.cos t| := by
          rw [Real.norm_eq_abs, abs_neg, abs_mul]
      _ ≤ |t ^ 2| * 1 := by
          exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one t) (abs_nonneg _)
      _ = t ^ 2 := by rw [mul_one, abs_of_nonneg (sq_nonneg t)]
  calc ‖∫ t in (0:ℝ)..y, -(t ^ 2 * Real.cos t)‖ ≤ ∫ t in (0:ℝ)..y, t ^ 2 := hle
    _ = y ^ 3 / 3 := by rw [integral_pow]; norm_num

/-! ### The derivative bounds for `sinc` -/

lemma abs_deriv_sinc_le_of_pos {y : ℝ} (h0 : 0 < y) : |deriv Real.sinc y| ≤ y / 3 := by
  rw [deriv_sinc_of_ne h0.ne']
  have hN : |Real.cos y * y - Real.sin y| ≤ y ^ 3 / 3 := by
    rw [show Real.cos y * y - Real.sin y = -(Real.sin y - y * Real.cos y) by ring, abs_neg]
    exact abs_sin_sub_mul_cos_le h0.le
  have h2 : (0:ℝ) < y ^ 2 := by positivity
  calc |(Real.cos y * y - Real.sin y) / y ^ 2| ≤ (y ^ 3 / 3) / y ^ 2 :=
        abs_div_le hN h2 le_rfl
    _ = y / 3 := by
        field_simp

/-- `sinc′ 0 = 0` — by squeezing `|sinc′ y| ≤ y/3` along `𝓝[>] 0`, no value computation. -/
lemma deriv_sinc_zero : deriv Real.sinc 0 = 0 := by
  have hlim : Filter.Tendsto (fun t : ℝ => |deriv Real.sinc t|) (nhdsWithin 0 (Set.Ioi 0))
      (nhds |deriv Real.sinc 0|) :=
    (continuous_dsinc.abs.continuousAt).continuousWithinAt
  have hlin : Filter.Tendsto (fun t : ℝ => t / 3) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (0:ℝ)) := by
    have h : Filter.Tendsto (fun t : ℝ => t / 3) (nhds 0) (nhds ((0:ℝ) / 3)) :=
      (continuous_id.div_const (3:ℝ)).tendsto 0
    rw [zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hbnd : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), |deriv Real.sinc t| ≤ t / 3 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact abs_deriv_sinc_le_of_pos ht
  have hle : |deriv Real.sinc 0| ≤ 0 := le_of_tendsto_of_tendsto hlim hlin hbnd
  exact abs_nonpos_iff.mp hle

/-- The linear bound `|sinc′ y| ≤ y/3`, all `y ≥ 0`. -/
lemma abs_deriv_sinc_le {y : ℝ} (h0 : 0 ≤ y) : |deriv Real.sinc y| ≤ y / 3 := by
  rcases h0.eq_or_lt with rfl | h
  · simp [deriv_sinc_zero]
  · exact abs_deriv_sinc_le_of_pos h

lemma abs_deriv2_sinc_le_of_pos {y : ℝ} (h0 : 0 < y) :
    |deriv (deriv Real.sinc) y| ≤ 1 / 3 := by
  rw [deriv2_sinc_of_ne h0.ne']
  have h3 : (0:ℝ) < y ^ 3 := by positivity
  calc |(2 * Real.sin y - 2 * y * Real.cos y - y ^ 2 * Real.sin y) / y ^ 3|
      ≤ (y ^ 3 / 3) / y ^ 3 := abs_div_le (abs_second_numerator_le h0.le) h3 le_rfl
    _ = 1 / 3 := by
        field_simp

/-- The uniform bound `|sinc″ y| ≤ 1/3`, all `y ≥ 0` (at `0` by continuity). -/
lemma abs_deriv2_sinc_le {y : ℝ} (h0 : 0 ≤ y) : |deriv (deriv Real.sinc) y| ≤ 1 / 3 := by
  rcases h0.eq_or_lt with rfl | h
  · have hlim : Filter.Tendsto (fun t : ℝ => |deriv (deriv Real.sinc) t|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds |deriv (deriv Real.sinc) 0|) :=
      (continuous_d2sinc.abs.continuousAt).continuousWithinAt
    have hbnd : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
        |deriv (deriv Real.sinc) t| ≤ 1 / 3 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact abs_deriv2_sinc_le_of_pos ht
    exact le_of_tendsto hlim hbnd
  · exact abs_deriv2_sinc_le_of_pos h

/-! ### The floor on `[0,1]` -/

/-- `sinc ≥ 5/6` on `[0,1]` (from `sin y > y − y³/6`). -/
lemma sinc_ge {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : 5 / 6 ≤ Real.sinc y := by
  rcases h0.eq_or_lt with rfl | h
  · rw [Real.sinc_zero]; norm_num
  · rw [Real.sinc_of_ne_zero h.ne']
    rw [le_div_iff₀ h]
    have hs := Real.sin_gt_sub_cube h
    nlinarith [hs, mul_nonneg (mul_nonneg h.le (sub_nonneg.mpr h1))
      (by linarith : (0:ℝ) ≤ 1 + y)]

/-! ### The amplitude root `s` and its derivative package -/

/-- The amplitude root `s = √sinc`. -/
def s (y : ℝ) : ℝ := Real.sqrt (Real.sinc y)

/-- Formula for the first derivative of `s`, justified on `[0,1]` by `hasDerivAt_s`. -/
def ds (y : ℝ) : ℝ := deriv Real.sinc y / (2 * s y)

/-- Formula for the second derivative of `s`, justified on `[0,1]` by `hasDerivAt_ds`. -/
def d2s (y : ℝ) : ℝ :=
  deriv (deriv Real.sinc) y / (2 * s y) - deriv Real.sinc y ^ 2 / (4 * s y ^ 3)

lemma s_nonneg (y : ℝ) : 0 ≤ s y := Real.sqrt_nonneg _

lemma s_le_one (y : ℝ) : s y ≤ 1 :=
  (Real.sqrt_le_sqrt (Real.sinc_le_one y)).trans_eq Real.sqrt_one

/-- `s ≥ 5/6` on `[0,1]`. -/
lemma s_ge {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : 5 / 6 ≤ s y := by
  have h := sinc_ge h0 h1
  calc (5:ℝ) / 6 ≤ Real.sqrt (5 / 6) := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]
        norm_num
    _ ≤ s y := Real.sqrt_le_sqrt h

/-- `s² = sinc` on `[0,1]`. -/
lemma sq_s {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : s y ^ 2 = Real.sinc y := by
  rw [s, Real.sq_sqrt]
  linarith [sinc_ge h0 h1]

lemma s_pos {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : 0 < s y :=
  lt_of_lt_of_le (by norm_num) (s_ge h0 h1)

/-- The derivative of `s` on `[0,1]`. -/
lemma hasDerivAt_s {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : HasDerivAt s (ds y) y := by
  have hpos : 0 < Real.sinc y := lt_of_lt_of_le (by norm_num) (sinc_ge h0 h1)
  have h := (Real.hasDerivAt_sqrt hpos.ne').comp y (hasDerivAt_sinc y)
  have heq : 1 / (2 * Real.sqrt (Real.sinc y)) * deriv Real.sinc y = ds y := by
    simp only [ds, s]
    ring
  rw [heq] at h
  exact h

/-- The bound `|ds y| ≤ y/5` on `[0,1]` — linear vanishing at the junction. -/
lemma abs_ds_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : |ds y| ≤ y / 5 := by
  have hs5 : (5:ℝ) / 6 ≤ s y := s_ge h0 h1
  have hden : (5:ℝ) / 3 ≤ 2 * s y := by linarith
  calc |ds y| = |deriv Real.sinc y / (2 * s y)| := rfl
    _ ≤ (y / 3) / (5 / 3) := abs_div_le (abs_deriv_sinc_le h0) (by norm_num) hden
    _ = y / 5 := by ring

/-- The derivative of `ds` on `[0,1]`. -/
lemma hasDerivAt_ds {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : HasDerivAt ds (d2s y) y := by
  have hσ : s y ≠ 0 := (s_pos h0 h1).ne'
  have hne : 2 * s y ≠ 0 := mul_ne_zero two_ne_zero hσ
  have hd := (hasDerivAt_s h0 h1).const_mul (2:ℝ)
  have h := (hasDerivAt_dsinc y).div hd hne
  have heq : (deriv (deriv Real.sinc) y * (2 * s y) - deriv Real.sinc y * (2 * ds y))
      / (2 * s y) ^ 2 = d2s y := by
    simp only [ds, d2s]
    field_simp
    ring
  rw [heq] at h
  exact h

/-- The bound `|d2s y| ≤ 1/2` on `[0,1]`. -/
lemma abs_d2s_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : |d2s y| ≤ 1 / 2 := by
  have hs5 : (5:ℝ) / 6 ≤ s y := s_ge h0 h1
  have hden1 : (5:ℝ) / 3 ≤ 2 * s y := by linarith
  have hcube : ((5:ℝ) / 6) ^ 3 ≤ s y ^ 3 := pow_le_pow_left₀ (by norm_num) hs5 3
  have hden2 : (125:ℝ) / 54 ≤ 4 * s y ^ 3 := by nlinarith [hcube]
  have e1 : |deriv (deriv Real.sinc) y / (2 * s y)| ≤ (1 / 3) / (5 / 3) :=
    abs_div_le (abs_deriv2_sinc_le h0) (by norm_num) hden1
  have e2 : |deriv Real.sinc y ^ 2 / (4 * s y ^ 3)| ≤ (1 / 9) / (125 / 54) := by
    refine abs_div_le ?_ (by norm_num) hden2
    have h13 : |deriv Real.sinc y| ≤ 1 / 3 := (abs_deriv_sinc_le h0).trans (by linarith)
    calc |deriv Real.sinc y ^ 2| = |deriv Real.sinc y| ^ 2 := by rw [abs_pow]
      _ ≤ (1 / 3) ^ 2 := by
          exact pow_le_pow_left₀ (abs_nonneg _) h13 2
      _ = 1 / 9 := by norm_num
  have habs : |deriv (deriv Real.sinc) y / (2 * s y)
      - deriv Real.sinc y ^ 2 / (4 * s y ^ 3)|
      ≤ |deriv (deriv Real.sinc) y / (2 * s y)|
        + |deriv Real.sinc y ^ 2 / (4 * s y ^ 3)| := by
    calc |deriv (deriv Real.sinc) y / (2 * s y)
        - deriv Real.sinc y ^ 2 / (4 * s y ^ 3)|
        = |deriv (deriv Real.sinc) y / (2 * s y)
          + -(deriv Real.sinc y ^ 2 / (4 * s y ^ 3))| := by rw [sub_eq_add_neg]
      _ ≤ |deriv (deriv Real.sinc) y / (2 * s y)|
          + |-(deriv Real.sinc y ^ 2 / (4 * s y ^ 3))| := abs_add_le _ _
      _ = |deriv (deriv Real.sinc) y / (2 * s y)|
          + |deriv Real.sinc y ^ 2 / (4 * s y ^ 3)| := by rw [abs_neg]
  calc |d2s y| = |deriv (deriv Real.sinc) y / (2 * s y)
      - deriv Real.sinc y ^ 2 / (4 * s y ^ 3)| := rfl
    _ ≤ |deriv (deriv Real.sinc) y / (2 * s y)|
        + |deriv Real.sinc y ^ 2 / (4 * s y ^ 3)| := habs
    _ ≤ (1 / 3) / (5 / 3) + (1 / 9) / (125 / 54) := add_le_add e1 e2
    _ ≤ 1 / 2 := by norm_num

end KsIndex.SincKit
