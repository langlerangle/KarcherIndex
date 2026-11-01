module

/-
# Matching test traces and cancellation of paired seam fluxes

At a point of `seamArc k m n`, an `IsSmooth` test family has a common
interior trace on copies `n` and `n+1`, equal to `φ n w`. The receiving
copy's raw circle value need not equal that trace: neither trace lemma
assumes `SeamVal` for the test family. The proof uses continuity of the
glued function and reflection through the unit circle.

For `u` satisfying `IsSmooth` and `SeamVal`, the two outward-radial
`fderivWithin` derivatives are opposite by `seam_radial_scalar`. Multiplying
both by any common trace value therefore gives zero total flux. The final
lemma proves the conjugated version used for a form conjugate-linear in
its first argument. Both statements are pointwise; integration by parts
and assembly of boundary integrals are handled by their consumers.
-/
public import KsIndexLean.SeamNormal

@[expose] public section


open Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace KsIndex.FaithfulInjection

open KsIndex.Surface KsIndex.SeamNormal

variable {k m : ℕ} {u φ : ZMod (2 * m) → ℂ → ℂ}

/-- The receiving copy's interior trace equals the giving value `φ n w`.
This requires only `IsSmooth`, not `SeamVal` for the test family. Reflection
through the unit circle identifies the interior limit with the continuous
glued function's exterior limit. -/
lemma seam_test_trace_match (hφ : IsSmooth k m φ) {n : ZMod (2 * m)} {w : ℂ}
    (hw : w ∈ seamArc k m n) :
    Tendsto (φ (n + 1)) (𝓝[disk] w) (𝓝 (φ n w)) := by
  have hnorm : ‖w‖ = 1 := norm_eq_one_of_mem_seamArc hw
  have hw0 : w ≠ 0 := by rintro rfl; simp at hnorm
  have hσw : (1 : ℂ) / (starRingEnd ℂ) w = w := sigma_fix_circle hnorm
  -- `glue φ n` is continuous at the seam point, with interior value `φ n w`.
  have hglue_val : glue φ n w = φ n w := by unfold glue; rw [if_pos (le_of_eq hnorm)]
  have hg : Tendsto (glue φ n) (𝓝 w) (𝓝 (φ n w)) := by
    have := (hφ.2.1 n w hw).continuousAt.tendsto
    rwa [hglue_val] at this
  -- `σ` is continuous at `w` and fixes it, so it maps the interior filter into `𝓝 w`.
  have hσ_tendsto : Tendsto (fun z => (1 : ℂ) / (starRingEnd ℂ) z) (𝓝[disk] w) (𝓝 w) := by
    have h2 : Tendsto (fun z => (1 : ℂ) / (starRingEnd ℂ) z) (𝓝 w) (𝓝 w) := by
      simpa only [hσw] using (hasFDerivAt_sigma hw0).continuousAt.tendsto
    exact h2.mono_left nhdsWithin_le_nhds
  have hcomp : Tendsto (fun z => glue φ n ((1 : ℂ) / (starRingEnd ℂ) z)) (𝓝[disk] w)
      (𝓝 (φ n w)) := hg.comp hσ_tendsto
  -- On the interior, near `w`, that composite is exactly `φ (n+1)` (involution + exterior branch).
  have hnear : {z : ℂ | (1 : ℝ) / 2 < ‖z‖} ∈ 𝓝 w := by
    refine (isOpen_lt continuous_const continuous_norm).mem_nhds ?_
    have : (1 : ℝ) / 2 < ‖w‖ := by rw [hnorm]; norm_num
    exact this
  have heq : (fun z => glue φ n ((1 : ℂ) / (starRingEnd ℂ) z)) =ᶠ[𝓝[disk] w] φ (n + 1) := by
    filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with z hz2 hzd
    have hz2' : (1 : ℝ) / 2 < ‖z‖ := hz2
    have hz1 : ‖z‖ < 1 := by rw [disk, Metric.mem_ball, dist_zero_right] at hzd; exact hzd
    have hzpos : (0 : ℝ) < ‖z‖ := by linarith
    have hnormσ : ‖(1 : ℂ) / (starRingEnd ℂ) z‖ = ‖z‖⁻¹ := by
      rw [norm_div, norm_one, Complex.norm_conj, one_div]
    have hσgt : 1 < ‖(1 : ℂ) / (starRingEnd ℂ) z‖ := by
      rw [hnormσ]; exact (one_lt_inv₀ hzpos).mpr hz1
    have hbranch : glue φ n ((1 : ℂ) / (starRingEnd ℂ) z) = φ (n + 1) z := by
      unfold glue; rw [if_neg (not_le.mpr hσgt), sigma_involutive z]
    exact hbranch
  exact hcomp.congr' heq

/-- The giving copy's interior trace is its own seam value `φ n w`.
The glued function agrees with that copy on the closed disk and is continuous
at the seam point. -/
lemma seam_giving_trace (hφ : IsSmooth k m φ) {n : ZMod (2 * m)} {w : ℂ}
    (hw : w ∈ seamArc k m n) :
    Tendsto (φ n) (𝓝[disk] w) (𝓝 (φ n w)) := by
  have hnorm : ‖w‖ = 1 := norm_eq_one_of_mem_seamArc hw
  have hglue_val : glue φ n w = φ n w := by unfold glue; rw [if_pos (le_of_eq hnorm)]
  have hg : Tendsto (glue φ n) (𝓝[disk] w) (𝓝 (φ n w)) := by
    have := (hφ.2.1 n w hw).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := disk))
    rwa [hglue_val] at this
  have heq : glue φ n =ᶠ[𝓝[disk] w] φ n := by
    filter_upwards [self_mem_nhdsWithin] with z hzd
    have hz1 : ‖z‖ < 1 := by rw [disk, Metric.mem_ball, dist_zero_right] at hzd; exact hzd
    unfold glue; rw [if_pos (le_of_lt hz1)]
  exact hg.congr' heq

/-- The paired outward-radial fluxes cancel for any common trace value `t`.
The assumptions are `IsSmooth` and `SeamVal` for `u`; the derivatives are
`fderivWithin` on the closed disk. The result follows from their opposite
signs in `seam_radial_scalar`. -/
lemma seam_flux_pointwise_cancel (hu : IsSmooth k m u) (hsv : SeamVal k u)
    {n : ZMod (2 * m)} {w : ℂ} (hw : w ∈ seamArc k m n) (t : ℂ) :
    fderivWithin ℝ (u n) (Metric.closedBall 0 1) w w * t
      + fderivWithin ℝ (u (n + 1)) (Metric.closedBall 0 1) w w * t = 0 := by
  rw [seam_radial_scalar hu hsv hw]; ring

/-- Conjugating both outward-radial derivatives preserves the cancellation.
This is the pointwise flux expression for a form conjugate-linear in its
first argument, multiplied by the common test trace `t`. -/
lemma seam_flux_pointwise_cancel_conj (hu : IsSmooth k m u) (hsv : SeamVal k u)
    {n : ZMod (2 * m)} {w : ℂ} (hw : w ∈ seamArc k m n) (t : ℂ) :
    (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1) w w) * t
      + (starRingEnd ℂ) (fderivWithin ℝ (u (n + 1)) (Metric.closedBall 0 1) w w) * t = 0 := by
  rw [seam_radial_scalar hu hsv hw, map_neg]; ring

end KsIndex.FaithfulInjection
