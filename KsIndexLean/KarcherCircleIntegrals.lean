module

/-
Coefficient integrals on sufficiently small circles about a Karcher puncture.
Positive radius and circleMap on [0,2π] mean counterclockwise orientation, hence
+2πi. The corresponding winding number around the center is +1.
This file proves neither an arbitrary-loop formula nor a global period group.
-/
public import KsIndexLean.KarcherResidues
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section


noncomputable section
open Complex Filter Metric Set
open scoped Topology
namespace KsIndex.KarcherData

/-- Isolation comes from the actual nonzero denominator derivative, not an assumption. -/
lemma exists_puncture_isolation {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) :
    ∃ ε > 0, ∀ w : ℂ, dist w z < ε → w ≠ z → w ∉ Surface.punctures k := by
  have he : ∀ᶠ w in 𝓝[≠] z, denominator k w ≠ 0 :=
    (hasDerivAt_denominator k z).eventually_ne (denominatorDeriv_ne_zero hk hz)
  rcases Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp he) with ⟨ε, hε, he⟩
  refine ⟨ε, hε, fun w hw hwz hp => ?_⟩
  have hn := he hw hwz
  apply hn
  change 1 + w ^ (2 * k) = 0
  rw [show w ^ (2 * k) = -1 from hp]
  ring

/-- A punctured limit and actual off-center differentiability imply the circle formula.
The countable-exception Cauchy formula needs only continuity at the filled center. -/
lemma circle_integral_of_residue_limit {f : ℂ → ℂ} {z A : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : ∀ w ∈ closedBall z r, w ≠ z → DifferentiableAt ℂ f w)
    (hlim : Tendsto (fun w => (w - z) * f w) (𝓝[≠] z) (𝓝 A)) :
    CircleIntegrable f z r ∧ circleIntegral f z r = (2 * Real.pi * I) * A := by
  classical
  let G : ℂ → ℂ := Function.update (fun w => (w - z) * f w) z A
  have hne : ∀ w ∈ sphere z r, w ≠ z := by
    intro w hw he
    subst w
    have heq : (0 : ℝ) = r := by simpa using hw
    exact hr.ne heq
  have hGc : ContinuousOn G (closedBall z r) := by
    intro w hw
    rcases eq_or_ne w z with rfl | hwz
    · exact (continuousAt_update_same.mpr hlim).continuousWithinAt
    · apply ContinuousAt.continuousWithinAt
      apply (continuousAt_update_of_ne hwz).mpr
      exact (continuousAt_id.sub continuousAt_const).mul (hd w hw hwz).continuousAt
  have hGd : ∀ w ∈ ball z r \ {z}, DifferentiableAt ℂ G w := by
    intro w hw
    have hwz : w ≠ z := hw.2
    apply (((differentiableAt_id.sub (differentiableAt_const z)).mul
      (hd w (ball_subset_closedBall hw.1) hwz))).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hwz] with v hv
    exact Function.update_of_ne hv _ _
  have hC := Complex.circleIntegral_div_sub_of_differentiable_on_off_countable
    (Set.countable_singleton z) (mem_ball_self hr) hGc hGd
  have hGa : G z = A := by simp [G]
  rw [hGa] at hC
  refine ⟨ContinuousOn.circleIntegrable hr.le (fun w hw =>
    (hd w (sphere_subset_closedBall hw) (hne w hw)).continuousAt.continuousWithinAt), ?_⟩
  calc
    circleIntegral f z r = circleIntegral (fun w => G w / (w - z)) z r := by
      apply circleIntegral.integral_congr hr.le
      intro w hw
      dsimp [G]
      rw [Function.update_of_ne (hne w hw)]
      exact (mul_div_cancel_left₀ (f w) (sub_ne_zero.mpr (hne w hw))).symm
    _ = (2 * Real.pi * I) * A := hC

/-- The three coefficient integrals, with a common radius bound isolating the central puncture. -/
theorem exists_small_circle_integrals {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) :
    ∃ ε > 0, ∀ r : ℝ, 0 < r → r < ε →
      (CircleIntegrable (coeff1 k) z r ∧
        circleIntegral (coeff1 k) z r = (2 * Real.pi * I) * (-(z.re : ℂ))) ∧
      (CircleIntegrable (coeff2 k) z r ∧
        circleIntegral (coeff2 k) z r = (2 * Real.pi * I) * (z.im : ℂ)) ∧
      (CircleIntegrable (coeff3 k) z r ∧
        circleIntegral (coeff3 k) z r = (2 * Real.pi * I) * (1 / z ^ k)) := by
  obtain ⟨ε, hε, hi⟩ := exists_puncture_isolation hk hz
  refine ⟨ε, hε, fun r hr hrε => ?_⟩
  have hp : ∀ w ∈ closedBall z r, w ≠ z → w ∉ Surface.punctures k := by
    intro w hw hwz
    exact hi w ((mem_closedBall.mp hw).trans_lt hrε) hwz
  exact ⟨circle_integral_of_residue_limit hr
      (fun w hw hwz => differentiableAt_coeff1 (hp w hw hwz)) (residue1_limit hk hz),
    circle_integral_of_residue_limit hr
      (fun w hw hwz => differentiableAt_coeff2 (hp w hw hwz)) (residue2_limit hk hz),
    circle_integral_of_residue_limit hr
      (fun w hw hwz => differentiableAt_coeff3 (hp w hw hwz)) (residue3_limit hk hz)⟩

/-- Real parts of actual counterclockwise integrals, not merely residue expressions. -/
theorem exists_small_circle_real_integrals {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) :
    ∃ ε > 0, ∀ r : ℝ, 0 < r → r < ε →
      CircleIntegrable (coeff1 k) z r ∧ CircleIntegrable (coeff2 k) z r ∧
      CircleIntegrable (coeff3 k) z r ∧
      (circleIntegral (coeff1 k) z r).re = 0 ∧
      (circleIntegral (coeff2 k) z r).re = 0 ∧
      ((circleIntegral (coeff3 k) z r).re = -(2 * Real.pi) ∨
        (circleIntegral (coeff3 k) z r).re = 2 * Real.pi) := by
  obtain ⟨ε, hε, hc⟩ := exists_small_circle_integrals hk hz
  refine ⟨ε, hε, fun r hr hrε => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hc r hr hrε
  refine ⟨h1.1, h2.1, h3.1, ?_, ?_, ?_⟩
  · rw [h1.2]; exact residue1_real_factor z
  · rw [h2.2]; exact residue2_real_factor z
  · rw [h3.2]; exact residue3_real_factor hz

end KsIndex.KarcherData
