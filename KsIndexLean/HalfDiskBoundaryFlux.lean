module

public import KsIndexLean.ClassicalHalfDiskJacobi
public import KsIndexLean.NullityGreen

@[expose] public section


/-! Boundary flux cancellation for classical half-period fields, before
assuming any global finite-energy or reflected regularity statement. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace.ClassicalHalfDiskJacobi
open KsIndex.Surface KsIndex.PunctureCutoff
variable {k : ℕ} {b : Bool} (u : ClassicalHalfDiskJacobi k b)

/-- Either pure boundary condition kills the diagonal Green flux away from
punctures, using the actual one-sided derivative on the closed disk. -/
lemma diagonal_boundary_flux_zero {w : ℂ} (hw : ‖w‖ = 1) (hp : w ∉ punctures k) :
    (starRingEnd ℂ) (fderivWithin ℝ u.value (Metric.closedBall (0 : ℂ) 1) w w) * u.value w = 0 := by
  obtain ⟨F, hF, hs, hb⟩ := u.boundary w hw hp
  have hv : u.value w = F w := hs.self_of_nhds hw.le
  rw [KsIndex.NullityDecomp.fderivWithin_closedBall_of_extension hw hF hs, hv]
  cases b with
  | false => change F w = 0 at hb; rw [hb, mul_zero]
  | true => change fderiv ℝ F w w = 0 at hb; rw [hb, map_zero, zero_mul]

/-- The cutoff makes the flux vanish also at the deleted circle points,
without imposing any value or derivative there. -/
theorem cutoff_boundary_flux_zero (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    {w : ℂ} (hw : ‖w‖ = 1) :
    (starRingEnd ℂ) (fderivWithin ℝ u.value (Metric.closedBall (0 : ℂ) 1) w w) *
      (((cutP k ε w) ^ 2 : ℂ) * u.value w) = 0 := by
  by_cases hp : w ∈ punctures k
  · have hc : cutP k ε w = 0 := cutP_eq_zero hk h0 h1 ⟨w, hp, by simpa only [sub_self, norm_zero] using sq_nonneg ε⟩
    simp [hc]
  · calc
      _ = ((cutP k ε w) ^ 2 : ℂ) *
          ((starRingEnd ℂ) (fderivWithin ℝ u.value (Metric.closedBall (0 : ℂ) 1) w w) * u.value w) := by ring
      _ = 0 := by rw [u.diagonal_boundary_flux_zero hw hp, mul_zero]

end KsIndex.Trace.ClassicalHalfDiskJacobi
