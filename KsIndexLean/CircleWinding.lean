module

public import KsIndexLean.ContourChainOperations
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section


/-! Circle parametrizations as chains, with winding one inside and zero outside
for positive radius. -/
open Set Metric MeasureTheory
open scoped Topology
noncomputable section

namespace KsIndex.Piecewise

/-- The circle parametrization with its derivative; positive radius gives a
counterclockwise circle. -/
def circlePiece (c : ℂ) (r : ℝ) : Piece where
  a := 0
  b := 2 * Real.pi
  lt := Real.two_pi_pos
  curve := circleMap c r
  velocity := fun t => circleMap 0 r t * Complex.I
  continuous_curve := (continuous_circleMap c r).continuousOn
  continuous_velocity := ((continuous_circleMap 0 r).mul_const Complex.I).continuousOn
  derivative := fun t _ => (hasDerivAt_circleMap c r t).hasDerivWithinAt

def circleChain (c : ℂ) (r : ℝ) : Chain := Chain.singleton (circlePiece c r)

lemma circleChain_closed (c : ℂ) (r : ℝ) : (circleChain c r).IsClosed := by
  change circleMap c r (2 * Real.pi) = circleMap c r 0
  simpa only [zero_add] using periodic_circleMap c r 0

lemma circlePiece_contour (c : ℂ) (r : ℝ) (f : ℂ → ℂ) :
    (circlePiece c r).contour f = circleIntegral f c r := by
  simp only [Piece.contour, circlePiece, circleIntegral, deriv_circleMap, smul_eq_mul]
lemma circleChain_contour (c : ℂ) (r : ℝ) (f : ℂ → ℂ) :
    (circleChain c r).contour f = circleIntegral f c r := by
  rw [circleChain, Chain.singleton_contour, circlePiece_contour]
lemma circlePiece_integrable_iff (c : ℂ) (r : ℝ) (f : ℂ → ℂ) :
    (circlePiece c r).Integrable f ↔ CircleIntegrable f c r := by
  rw [circleIntegrable_iff r]
  simp only [Piece.Integrable, circlePiece, deriv_circleMap, smul_eq_mul]
lemma circleChain_integrable_iff (c : ℂ) (r : ℝ) (f : ℂ → ℂ) :
    (circleChain c r).Integrable f ↔ CircleIntegrable f c r := by
  change (∀ _ : Fin 1, (circlePiece c r).Integrable f) ↔ _
  simp only [forall_const, circlePiece_integrable_iff]

lemma circleChain_avoids_of_dist_ne {c z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : dist z c ≠ r) : (circleChain c r).Avoids z := by
  intro i t _ ht
  have hs := mem_sphere.mp (circleMap_mem_sphere c hr.le t)
  exact hz (ht ▸ hs)
lemma circleChain_avoids_inside {c z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : dist z c < r) : (circleChain c r).Avoids z :=
  circleChain_avoids_of_dist_ne hr hz.ne
lemma circleChain_avoids_outside {c z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : r < dist z c) : (circleChain c r).Avoids z :=
  circleChain_avoids_of_dist_ne hr hz.ne'

/-- The chain winding equals one inside a positive-radius circle, as determined
by Mathlib's reciprocal contour integral. -/
lemma circleChain_winding_inside {c z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : dist z c < r) :
    (circleChain c r).winding (circleChain_closed c r) z
      (circleChain_avoids_inside hr hz) = 1 := by
  apply Chain.winding_eq_of_integral
  rw [Chain.logIntegral, circleChain_contour,
    circleIntegral.integral_sub_inv_of_mem_ball hz]
  simp
lemma circleChain_winding_center (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (circleChain c r).winding (circleChain_closed c r) c
      (circleChain_avoids_inside hr (by simpa using hr)) = 1 :=
  circleChain_winding_inside hr (by simpa using hr)

lemma circleIntegral_reciprocal_outside {c z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : r < dist z c) : circleIntegral (fun w => (w - z)⁻¹) c r = 0 := by
  have hn : ∀ w ∈ closedBall c r, w - z ≠ 0 := by
    intro w hw he
    have hwz := sub_eq_zero.mp he
    subst w
    exact (not_le_of_gt hz) (mem_closedBall.mp hw)
  have hd : ∀ w ∈ closedBall c r, DifferentiableAt ℂ (fun w => (w - z)⁻¹) w :=
    fun w hw => (differentiableAt_id.sub_const z).inv (hn w hw)
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
    Set.countable_empty (fun w hw => (hd w hw).continuousAt.continuousWithinAt)
    (fun w hw => hd w (ball_subset_closedBall hw.1))
lemma circleChain_winding_outside {c z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : r < dist z c) :
    (circleChain c r).winding (circleChain_closed c r) z
      (circleChain_avoids_outside hr hz) = 0 := by
  apply Chain.winding_eq_of_integral
  rw [Chain.logIntegral, circleChain_contour, circleIntegral_reciprocal_outside hr hz]
  simp

end KsIndex.Piecewise
