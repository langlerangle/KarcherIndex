module

public import KsIndexLean.SphericalJoinedEnergy

@[expose] public section


open MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1

/-- Canonical squared H1 quantity of the joined value and its assembled tangent field. -/
def sphereJoinedH1Squared (u v : ComplexH1) : ℝ :=
  (∫⁻ p, ENNReal.ofReal (‖sphereJoinedValue u v p‖ ^ 2)
    ∂(volume : Measure Ambient).toSphere).toReal + sphereJoinedEnergy u v

theorem sphereJoinedH1Squared_comparison (u v : ComplexH1) :
    ‖u‖ ^ 2 + ‖v‖ ^ 2 ≤ sphereJoinedH1Squared u v ∧
      sphereJoinedH1Squared u v ≤ 4 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have hm := sphereJoinedValue_mass_real_comparison u v
  rw [sphereJoinedH1Squared, sphereJoinedEnergy_eq,
    coordinate_graph_norm_sq u, coordinate_graph_norm_sq v]
  constructor
  · linarith [hm.1]
  · nlinarith [hm.2, sq_nonneg ‖dxLp u‖, sq_nonneg ‖dyLp u‖,
      sq_nonneg ‖dxLp v‖, sq_nonneg ‖dyLp v‖]

lemma sphereJoinedH1Squared_nonneg (u v : ComplexH1) : 0 ≤ sphereJoinedH1Squared u v :=
  (add_nonneg (sq_nonneg _) (sq_nonneg _)).trans (sphereJoinedH1Squared_comparison u v).1

/-- Integral-based H1 size; a normed quotient structure is a separate construction. -/
def sphereJoinedH1Size (u v : ComplexH1) : ℝ := Real.sqrt (sphereJoinedH1Squared u v)

theorem sphereJoinedH1Size_comparison (u v : ComplexH1) :
    Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2) ≤ sphereJoinedH1Size u v ∧
      sphereJoinedH1Size u v ≤ 2 * Real.sqrt (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have h := sphereJoinedH1Squared_comparison u v
  have hsq := Real.sq_sqrt (sphereJoinedH1Squared_nonneg u v)
  have hd := Real.sq_sqrt (add_nonneg (sq_nonneg ‖u‖) (sq_nonneg ‖v‖))
  unfold sphereJoinedH1Size
  constructor
  · exact Real.sqrt_le_sqrt h.1
  · nlinarith [h.2, Real.sqrt_nonneg (sphereJoinedH1Squared u v),
      Real.sqrt_nonneg (‖u‖ ^ 2 + ‖v‖ ^ 2)]

lemma sphereJoinedH1Squared_eq_zero_iff (u v : ComplexH1) :
    sphereJoinedH1Squared u v = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have hc := (sphereJoinedH1Squared_comparison u v).1
    rw [h] at hc
    have hu : ‖u‖ = 0 := by nlinarith [norm_nonneg u, sq_nonneg ‖v‖]
    have hv : ‖v‖ = 0 := by nlinarith [norm_nonneg v, sq_nonneg ‖u‖]
    exact ⟨norm_eq_zero.mp hu, norm_eq_zero.mp hv⟩
  · rintro ⟨rfl, rfl⟩
    have h := (sphereJoinedH1Squared_comparison (0 : ComplexH1) 0).2
    have hn := sphereJoinedH1Squared_nonneg (0 : ComplexH1) 0
    simpa using le_antisymm (by simpa using h) hn

end KsIndex.Spherical
