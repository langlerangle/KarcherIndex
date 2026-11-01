module

/-
Seam-normal derivatives under inversion reflection.

At a seam point `w` with `‖w‖ = 1`, `IsSmooth k m u` gives a single Fréchet derivative
`D := fderiv ℝ (glue u n) w`. The giving copy has within-derivative `D` on the closed disk.
With the additional value-matching hypothesis `SeamVal k u`, the reflected receiving copy
has within-derivative `D` on the closed exterior, and the receiving copy in its own chart
has within-derivative `D ∘ dSigma w` on the closed disk.

The reflection `σ(w) = 1 / conj(w)` fixes the unit circle and reverses radial directions.
Consequently the two copies' radial derivatives are opposite, the identity needed for
cancellation of seam fluxes. This file proves the pointwise derivative identity, not an
integrated flux formula.

The distinction between smooth gluing and receiving-copy value matching was identified
in Xi's statement review: `glue` takes the giving copy's values on the circle, so smoothness
of `glue` alone does not constrain the receiving copy's raw boundary values.
-/
public import KsIndexLean.Surface
public import KsIndexLean.SigmaDeriv

@[expose] public section


open Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace KsIndex.SeamNormal

open KsIndex.Surface

variable {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}

/-- A seam point lies on the unit circle. -/
lemma norm_eq_one_of_mem_seamArc {n : ZMod (2 * m)} {w : ℂ} (hw : w ∈ seamArc k m n) :
    ‖w‖ = 1 := by
  have h := hw
  simp only [seamArc, arc, Set.mem_setOf_eq] at h
  exact h.1

/-- **Giving-copy derivative**: the giving copy's within-derivative on the closed disk equals `glue`'s
Fréchet derivative.  Needs `IsSmooth` only — `glue u n = u n` on `closedBall 0 1` is a global
definitional equality. -/
lemma seam_fderivWithin_inside (hu : IsSmooth k m u) {n : ZMod (2 * m)} {w : ℂ}
    (hw : w ∈ seamArc k m n) :
    HasFDerivWithinAt (u n) (fderiv ℝ (glue u n) w) (Metric.closedBall 0 1) w := by
  have hnorm : ‖w‖ = 1 := norm_eq_one_of_mem_seamArc hw
  have hwmem : w ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hnorm]
  have hcd : ContDiffAt ℝ ∞ (glue u n) w := hu.2.1 n w hw
  have hfd : HasFDerivAt (glue u n) (fderiv ℝ (glue u n) w) w :=
    (hcd.differentiableAt (by norm_num)).hasFDerivAt
  have hEq : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, u n z = glue u n z := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    simp only [glue, if_pos hz]
  exact hfd.hasFDerivWithinAt.congr hEq (hEq w hwmem)

/-- `σ = 1/w̄` fixes the unit circle pointwise. -/
lemma sigma_fix_circle {w : ℂ} (hw : ‖w‖ = 1) : (1 : ℂ) / (starRingEnd ℂ) w = w := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  rw [one_div]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [Complex.conj_mul', hw]; norm_num

/-- The seam arc is relatively open in the circle: near a seam point, every circle point is
still on the arc (the sign condition `(−1)^j (z^k).re < 0` is an open condition in `ℂ`). -/
lemma seamArc_openness {n : ZMod (2 * m)} {w : ℂ} (hw : w ∈ seamArc k m n) :
    ∃ ε > 0, ∀ z : ℂ, ‖z‖ = 1 → ‖z - w‖ < ε → z ∈ seamArc k m n := by
  have hopen : IsOpen {z : ℂ | (-1 : ℝ) ^ (parity m (n + 1)).val * (z ^ k).re < 0} := by
    apply isOpen_lt _ continuous_const
    fun_prop
  have hwin : w ∈ {z : ℂ | (-1 : ℝ) ^ (parity m (n + 1)).val * (z ^ k).re < 0} := by
    have h := hw; simp only [seamArc, arc, Set.mem_setOf_eq] at h; exact h.2
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen w hwin
  refine ⟨ε, hε, fun z hz1 hzd => ?_⟩
  simp only [seamArc, arc, Set.mem_setOf_eq]
  refine ⟨hz1, hsub ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]; exact hzd

/-- **Reflected receiving-copy derivative**: on the closed exterior `(ball 0 1)ᶜ`, the reflected receiving copy
`u (n+1) ∘ σ` has `glue`'s Fréchet derivative.  Needs `IsSmooth` AND `SeamVal`: the exterior part
`glue = u(n+1)∘σ` is definitional, but at the circle boundary `glue = u n`, and matching that to
`u(n+1)∘σ = u(n+1)` requires `SeamVal` (the receiving value `u(n+1) w` is otherwise the free
boundary value, not determined by smoothness of `glue` alone). -/
lemma seam_fderivWithin_outside (hu : IsSmooth k m u) (hsv : SeamVal k u) {n : ZMod (2 * m)}
    {w : ℂ} (hw : w ∈ seamArc k m n) :
    HasFDerivWithinAt (fun z => u (n + 1) (1 / (starRingEnd ℂ) z)) (fderiv ℝ (glue u n) w)
      (Metric.ball 0 1)ᶜ w := by
  have hnorm : ‖w‖ = 1 := norm_eq_one_of_mem_seamArc hw
  have hcd : ContDiffAt ℝ ∞ (glue u n) w := hu.2.1 n w hw
  have hfd : HasFDerivAt (glue u n) (fderiv ℝ (glue u n) w) w :=
    (hcd.differentiableAt (by norm_num)).hasFDerivAt
  obtain ⟨ε, hε, harc⟩ := seamArc_openness hw
  have hσw : (1 : ℂ) / (starRingEnd ℂ) w = w := sigma_fix_circle hnorm
  have hee : (fun z => u (n + 1) (1 / (starRingEnd ℂ) z))
      =ᶠ[𝓝[(Metric.ball (0 : ℂ) 1)ᶜ] w] glue u n := by
    have hb : Metric.ball w ε ∈ 𝓝[(Metric.ball (0 : ℂ) 1)ᶜ] w :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds w hε)
    filter_upwards [hb, self_mem_nhdsWithin] with z hzb hzc
    have hz1 : 1 ≤ ‖z‖ := by
      rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at hzc; exact hzc
    have hzd : ‖z - w‖ < ε := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hzb
    rcases eq_or_lt_of_le hz1 with heq | hlt
    · have hzarc : z ∈ seamArc k m n := harc z heq.symm hzd
      have hσz : (1 : ℂ) / (starRingEnd ℂ) z = z := sigma_fix_circle heq.symm
      change u (n + 1) (1 / (starRingEnd ℂ) z) = glue u n z
      rw [hσz]; unfold glue; rw [if_pos (le_of_eq heq.symm)]; exact hsv n z hzarc
    · change u (n + 1) (1 / (starRingEnd ℂ) z) = glue u n z
      unfold glue; rw [if_neg (not_le.mpr hlt)]
  refine hfd.hasFDerivWithinAt.congr_of_eventuallyEq hee ?_
  show u (n + 1) (1 / (starRingEnd ℂ) w) = glue u n w
  rw [hσw]; unfold glue; rw [if_pos (le_of_eq hnorm)]; exact hsv n w hw

/-! ### The reflection's derivative as a named map, and its involution -/

/-- The real-linear derivative map for inversion reflection `σ = 1/w̄`, identified at `w ≠ 0` below. -/
def dSigma (w : ℂ) : ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.toSpanSingleton ℂ (-(((starRingEnd ℂ) w) ^ 2)⁻¹)).restrictScalars ℝ).comp
    (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ)

/-- `σ = 1/w̄` has Fréchet derivative `dSigma w` at `w ≠ 0` (from `SigmaDeriv`). -/
lemma hasFDerivAt_sigma {w : ℂ} (hw : w ≠ 0) :
    HasFDerivAt (fun z : ℂ => 1 / (starRingEnd ℂ) z) (dSigma w) w :=
  KsIndex.SigmaDeriv.hasFDerivAt_sigmaR hw

lemma dSigma_apply (w h : ℂ) : dSigma w h = -(((starRingEnd ℂ) w) ^ 2)⁻¹ * (starRingEnd ℂ) h := by
  simp only [dSigma, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, smul_eq_mul]
  ring

/-- On the unit circle the radial component of `dSigma` flips: `dSigma w w = −w`. -/
lemma dSigma_radial {w : ℂ} (hw : ‖w‖ = 1) : dSigma w w = -w := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  rw [← (hasFDerivAt_sigma hw0).fderiv]
  exact KsIndex.SigmaDeriv.fderiv_sigmaR_radial hw

/-- `σ = 1/w̄` is an involution: `σ (σ z) = z` (even at `0`, where both sides are `0`). -/
lemma sigma_involutive (z : ℂ) :
    (1 : ℂ) / (starRingEnd ℂ) ((1 : ℂ) / (starRingEnd ℂ) z) = z := by
  rw [one_div, one_div, map_inv₀, Complex.conj_conj, inv_inv]

/-! ### The receiving copy's own-chart within-derivative and radial derivative -/

/-- **Receiving-copy derivative**: the receiving copy `u (n+1)` has within-derivative `D ∘ dσ_w` on the closed disk,
`D = fderiv (glue u n) w`.  Via `u (n+1) = (u(n+1)∘σ)∘σ` (σ involutive) and the chain rule; the
`z = 0` gap in `MapsTo σ` is avoided by working on a punctured neighborhood `{½ < ‖z‖}` of the
seam point and lifting with `hasFDerivWithinAt_inter`. -/
lemma seam_fderivWithin_recv (hu : IsSmooth k m u) (hsv : SeamVal k u) {n : ZMod (2 * m)}
    {w : ℂ} (hw : w ∈ seamArc k m n) :
    HasFDerivWithinAt (u (n + 1)) ((fderiv ℝ (glue u n) w).comp (dSigma w))
      (Metric.closedBall 0 1) w := by
  have hnorm : ‖w‖ = 1 := norm_eq_one_of_mem_seamArc hw
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; norm_num at hnorm
  have hσw : (1 : ℂ) / (starRingEnd ℂ) w = w := sigma_fix_circle hnorm
  have hUnhds : {z : ℂ | (1 : ℝ) / 2 < ‖z‖} ∈ 𝓝 w := by
    refine (isOpen_lt continuous_const continuous_norm).mem_nhds ?_
    simp only [Set.mem_setOf_eq, hnorm]; norm_num
  have hf : HasFDerivWithinAt (fun z => 1 / (starRingEnd ℂ) z) (dSigma w)
      (Metric.closedBall 0 1 ∩ {z | (1 : ℝ) / 2 < ‖z‖}) w :=
    (hasFDerivAt_sigma hw0).hasFDerivWithinAt
  have hg : HasFDerivWithinAt (fun z => u (n + 1) (1 / (starRingEnd ℂ) z)) (fderiv ℝ (glue u n) w)
      (Metric.ball 0 1)ᶜ ((fun z => 1 / (starRingEnd ℂ) z) w) := by
    change HasFDerivWithinAt _ _ _ (1 / (starRingEnd ℂ) w)
    rw [hσw]; exact seam_fderivWithin_outside hu hsv hw
  have hst : Set.MapsTo (fun z => 1 / (starRingEnd ℂ) z)
      (Metric.closedBall 0 1 ∩ {z | (1 : ℝ) / 2 < ‖z‖}) (Metric.ball 0 1)ᶜ := by
    rintro z ⟨hz1, hz2⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hz1
    simp only [Set.mem_setOf_eq] at hz2
    have hzpos : (0 : ℝ) < ‖z‖ := by linarith
    have hnormσ : ‖(1 : ℂ) / (starRingEnd ℂ) z‖ = ‖z‖⁻¹ := by
      rw [norm_div, norm_one, Complex.norm_conj, one_div]
    rw [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt, hnormσ]
    exact (one_le_inv₀ hzpos).mpr hz1
  have hcomp := HasFDerivWithinAt.comp w hg hf hst
  have hfun : (fun z => u (n + 1) (1 / (starRingEnd ℂ) z)) ∘ (fun z => 1 / (starRingEnd ℂ) z)
      = u (n + 1) := by
    funext z; simp only [Function.comp_apply]; rw [sigma_involutive z]
  rw [hfun] at hcomp
  exact (hasFDerivWithinAt_inter hUnhds).mp hcomp

/-- **Opposite radial derivatives**: on the closed disk the
receiving copy's radial derivative is MINUS the giving copy's — `∂_ν u(n+1) = −∂_ν u n`. -/
lemma seam_radial_scalar (hu : IsSmooth k m u) (hsv : SeamVal k u) {n : ZMod (2 * m)}
    {w : ℂ} (hw : w ∈ seamArc k m n) :
    fderivWithin ℝ (u (n + 1)) (Metric.closedBall 0 1) w w
      = - fderivWithin ℝ (u n) (Metric.closedBall 0 1) w w := by
  have hnorm : ‖w‖ = 1 := norm_eq_one_of_mem_seamArc hw
  have hwmem : w ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hnorm]
  have hud : UniqueDiffWithinAt ℝ (Metric.closedBall (0 : ℂ) 1) w :=
    uniqueDiffOn_convex (convex_closedBall 0 1)
      (by rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
          exact ⟨0, Metric.mem_ball_self (by norm_num)⟩) w hwmem
  rw [(seam_fderivWithin_recv hu hsv hw).fderivWithin hud,
    (seam_fderivWithin_inside hu hw).fderivWithin hud,
    ContinuousLinearMap.comp_apply, dSigma_radial hnorm, map_neg]

end KsIndex.SeamNormal
