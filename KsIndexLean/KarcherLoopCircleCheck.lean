module

public import KsIndexLean.KarcherLoopFormula
public import KsIndexLean.KarcherCircleWinding

@[expose] public section


/-! Small-circle contour values from the loop formula and the explicit winding-sum collapse.
The results agree with the direct circle-integral calculation on the same radius. -/
noncomputable section
namespace KsIndex.KarcherData
open Piecewise

lemma karcherWindingSum_eq_single {k : ℕ} (hk : 2 ≤ k) (C : Chain) (hc : C.IsClosed)
    (hA : ∀ w ∈ Surface.punctures k, C.Avoids w) (z : ℂ) (hz : z ∈ Surface.punctures k)
    (hcenter : C.winding hc z (hA z hz) = 1)
    (hother : ∀ w, ∀ hw : w ∈ Surface.punctures k, w ≠ z →
      C.winding hc w (hA w hw) = 0) (R : ℂ → ℂ) :
    karcherWindingSum hk C hc hA R = R z := by
  apply C.residueWindingSum_eq_single hc (punctureFinset k) R
    (avoids_punctureFinset hk C hA) z ((mem_punctureFinset hk).mpr hz) hcenter
  intro w hw hne
  exact hother w ((mem_punctureFinset hk).mp hw) hne

/-- The winding sums collapse to the central residues. Contour values follow from the loop
formula; the circleIntegral values follow from the direct circle calculation and contour bridge. -/
theorem exists_small_circle_loop_formula_check {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) :
    ∃ ε > 0, ∀ r : ℝ, 0 < r → r < ε →
      ∃ hA : ∀ w ∈ Surface.punctures k, (circleChain z r).Avoids w,
        karcherWindingSum hk (circleChain z r) (circleChain_closed z r) hA
          (fun w => -(w.re : ℂ)) = -(z.re : ℂ) ∧
        karcherWindingSum hk (circleChain z r) (circleChain_closed z r) hA
          (fun w => (w.im : ℂ)) = (z.im : ℂ) ∧
        karcherWindingSum hk (circleChain z r) (circleChain_closed z r) hA
          (fun w => 1 / w ^ k) = 1 / z ^ k ∧
        ((circleChain z r).Integrable (coeff1 k) ∧
          (circleChain z r).contour (coeff1 k) = (2 * Real.pi * Complex.I) * (-(z.re : ℂ)) ∧
          circleIntegral (coeff1 k) z r = (2 * Real.pi * Complex.I) * (-(z.re : ℂ))) ∧
        ((circleChain z r).Integrable (coeff2 k) ∧
          (circleChain z r).contour (coeff2 k) = (2 * Real.pi * Complex.I) * (z.im : ℂ) ∧
          circleIntegral (coeff2 k) z r = (2 * Real.pi * Complex.I) * (z.im : ℂ)) ∧
        ((circleChain z r).Integrable (coeff3 k) ∧
          (circleChain z r).contour (coeff3 k) = (2 * Real.pi * Complex.I) * (1 / z ^ k) ∧
          circleIntegral (coeff3 k) z r = (2 * Real.pi * Complex.I) * (1 / z ^ k)) := by
  obtain ⟨ε, hε, hdata⟩ := exists_small_circle_chain_data hk hz
  refine ⟨ε, hε, fun r hr hrε => ?_⟩
  obtain ⟨⟨hA, hcenter, hother⟩, hP1, hP2, hP3⟩ := hdata r hr hrε
  have hsum (R : ℂ → ℂ) :
      karcherWindingSum hk (circleChain z r) (circleChain_closed z r) hA R = R z :=
    karcherWindingSum_eq_single hk _ _ hA z hz hcenter hother R
  -- These contour equalities use the loop formula and finite-sum collapse.
  have hloop1 := coeff1_loop_formula hk (circleChain z r) (circleChain_closed z r) hA
  have hloop2 := coeff2_loop_formula hk (circleChain z r) (circleChain_closed z r) hA
  have hloop3 := coeff3_loop_formula hk (circleChain z r) (circleChain_closed z r) hA
  rw [hsum] at hloop1 hloop2 hloop3
  refine ⟨hA, hsum _, hsum _, hsum _, ⟨?_, hloop1, ?_⟩,
    ⟨?_, hloop2, ?_⟩, ⟨?_, hloop3, ?_⟩⟩
  · exact coeff1_chain_integrable hk _ hA
  · rw [← circleChain_contour]
    exact hP1.2
  · exact coeff2_chain_integrable hk _ hA
  · rw [← circleChain_contour]
    exact hP2.2
  · exact coeff3_chain_integrable hk _ hA
  · rw [← circleChain_contour]
    exact hP3.2

end KsIndex.KarcherData
