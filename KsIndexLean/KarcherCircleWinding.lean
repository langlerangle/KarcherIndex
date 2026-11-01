module

public import KsIndexLean.CircleWinding
public import KsIndexLean.KarcherCircleIntegrals

@[expose] public section


/-! Transfer of the proved Karcher small-circle integrals to certified chains.
The common radius also certifies avoidance of all punctures and winding 1/0. -/
open Set Metric
open scoped Topology
noncomputable section
namespace KsIndex.KarcherData
open Piecewise

lemma exists_small_circle_chain_winding {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) :
    ∃ ε > 0, ∀ r : ℝ, 0 < r → r < ε →
      ∃ hA : ∀ w ∈ Surface.punctures k, (circleChain z r).Avoids w,
        (circleChain z r).winding (circleChain_closed z r) z (hA z hz) = 1 ∧
        ∀ w, ∀ hw : w ∈ Surface.punctures k, w ≠ z →
          (circleChain z r).winding (circleChain_closed z r) w (hA w hw) = 0 := by
  obtain ⟨ε, hε, hi⟩ := exists_puncture_isolation hk hz
  refine ⟨ε, hε, fun r hr hrε => ?_⟩
  have hout : ∀ w ∈ Surface.punctures k, w ≠ z → r < dist w z := by
    intro w hw hwz
    exact hrε.trans_le (le_of_not_gt (fun hlt => hi w hlt hwz hw))
  have hA : ∀ w ∈ Surface.punctures k, (circleChain z r).Avoids w := by
    intro w hw
    by_cases hwz : w = z
    · subst w
      exact circleChain_avoids_inside hr (by simpa using hr)
    · exact circleChain_avoids_outside hr (hout w hw hwz)
  refine ⟨hA, ?_, ?_⟩
  · exact circleChain_winding_center z hr
  · intro w hw hwz
    exact circleChain_winding_outside hr (hout w hw hwz)

/-- Actual contour values and integrability, transferred from the direct circle-integral proof. -/
theorem exists_small_circle_chain_integrals {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) :
    ∃ ε > 0, ∀ r : ℝ, 0 < r → r < ε →
      ((circleChain z r).Integrable (coeff1 k) ∧
        (circleChain z r).contour (coeff1 k) = (2 * Real.pi * Complex.I) * (-(z.re : ℂ))) ∧
      ((circleChain z r).Integrable (coeff2 k) ∧
        (circleChain z r).contour (coeff2 k) = (2 * Real.pi * Complex.I) * (z.im : ℂ)) ∧
      ((circleChain z r).Integrable (coeff3 k) ∧
        (circleChain z r).contour (coeff3 k) = (2 * Real.pi * Complex.I) * (1 / z ^ k)) := by
  obtain ⟨ε, hε, hi⟩ := exists_small_circle_integrals hk hz
  refine ⟨ε, hε, fun r hr hrε => ?_⟩
  simpa only [circleChain_integrable_iff, circleChain_contour] using hi r hr hrε

/-- A common positive radius bound supplies winding and all three coefficient integrals.
These data combine puncture isolation with the direct circle-integral computation. -/
theorem exists_small_circle_chain_data {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) :
    ∃ ε > 0, ∀ r : ℝ, 0 < r → r < ε →
      (∃ hA : ∀ w ∈ Surface.punctures k, (circleChain z r).Avoids w,
        (circleChain z r).winding (circleChain_closed z r) z (hA z hz) = 1 ∧
        ∀ w, ∀ hw : w ∈ Surface.punctures k, w ≠ z →
          (circleChain z r).winding (circleChain_closed z r) w (hA w hw) = 0) ∧
      ((circleChain z r).Integrable (coeff1 k) ∧
        (circleChain z r).contour (coeff1 k) = (2 * Real.pi * Complex.I) * (-(z.re : ℂ))) ∧
      ((circleChain z r).Integrable (coeff2 k) ∧
        (circleChain z r).contour (coeff2 k) = (2 * Real.pi * Complex.I) * (z.im : ℂ)) ∧
      ((circleChain z r).Integrable (coeff3 k) ∧
        (circleChain z r).contour (coeff3 k) = (2 * Real.pi * Complex.I) * (1 / z ^ k)) := by
  obtain ⟨εw, hw, hW⟩ := exists_small_circle_chain_winding hk hz
  obtain ⟨εi, hi, hI⟩ := exists_small_circle_chain_integrals hk hz
  refine ⟨min εw εi, lt_min hw hi, fun r hr hε => ?_⟩
  exact ⟨hW r hr (hε.trans_le (min_le_left _ _)),
    hI r hr (hε.trans_le (min_le_right _ _))⟩

theorem exists_small_circle_chain_real_integrals {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) :
    ∃ ε > 0, ∀ r : ℝ, 0 < r → r < ε →
      (circleChain z r).Integrable (coeff1 k) ∧ (circleChain z r).Integrable (coeff2 k) ∧
      (circleChain z r).Integrable (coeff3 k) ∧
      ((circleChain z r).contour (coeff1 k)).re = 0 ∧
      ((circleChain z r).contour (coeff2 k)).re = 0 ∧
      (((circleChain z r).contour (coeff3 k)).re = -(2 * Real.pi) ∨
        ((circleChain z r).contour (coeff3 k)).re = 2 * Real.pi) := by
  obtain ⟨ε, hε, hi⟩ := exists_small_circle_real_integrals hk hz
  refine ⟨ε, hε, fun r hr hrε => ?_⟩
  simpa only [circleChain_integrable_iff, circleChain_contour] using hi r hr hrε

end KsIndex.KarcherData
