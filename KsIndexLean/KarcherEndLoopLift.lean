module

public import KsIndexLean.KarcherFiniteDeckCovering
public import KsIndexLean.KarcherPieceLift
public import KsIndexLean.KarcherLoopCircleCheck

@[expose] public section


/-! Endpoint displacement of actual lifted small circles around EW ends. -/
noncomputable section
open Set
namespace KsIndex.KarcherData
open Piecewise

/-- A closed contour piece with integer vertical period has the corresponding
 deck displacement under its actual partial-integral lift. -/
lemma pieceLift_finish_eq_deck_start {k : ℕ} (hk : 2 ≤ k)
    (base : PuncturedPlane k) (C : PeriodTarget) (p : Piece)
    (hA : ∀ w ∈ Surface.punctures k, p.Avoids w)
    (hc : p.finish = p.start) (n : ℤ)
    (hp : (p.contour (coeff3 k)).re = (2 * Real.pi) * (n : ℝ))
    (z : ℝ) (hz : (z : AddCircle (2 * Real.pi)) =
      (descendedIntegral hk base ⟨p.start, fun hw => p.start_ne (hA _ hw) rfl⟩).2.2) :
    pieceLift hk base C p hA z hz ⟨p.b, p.lt.le, le_rfl⟩ =
      HeightLift.deck n (pieceLift hk base C p hA z hz ⟨p.a, le_rfl, p.lt.le⟩) := by
  apply Subtype.ext
  apply Prod.ext
  · change finiteParameter _ = finiteParameter _
    apply congrArg finiteParameter
    exact Subtype.ext hc
  · change z + (p.contour (coeff3 k)).re =
      (z + (p.partialContour (coeff3 k) p.a).re) + (n : ℝ) * (2 * Real.pi)
    rw [p.partialContour_start, Complex.zero_re, add_zero, hp, mul_comm (2 * Real.pi)]

/-- Every sufficiently small counterclockwise circle around an end lifts with
 precisely one positive or negative full-period displacement. -/
theorem exists_small_circle_deck_displacement {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k) :
    ∃ ε > 0, ∀ r : ℝ, 0 < r → r < ε →
      ∃ hA : ∀ v ∈ Surface.punctures k, (circlePiece w r).Avoids v,
        ∀ (base : PuncturedPlane k) (C : PeriodTarget) (z : ℝ)
          (hz : (z : AddCircle (2 * Real.pi)) =
            (descendedIntegral hk base
              ⟨(circlePiece w r).start, fun hv => (circlePiece w r).start_ne (hA _ hv) rfl⟩).2.2),
          pieceLift hk base C (circlePiece w r) hA z hz
            ⟨(circlePiece w r).b, (circlePiece w r).lt.le, le_rfl⟩ =
          HeightLift.deck (endSign k w)
            (pieceLift hk base C (circlePiece w r) hA z hz
              ⟨(circlePiece w r).a, le_rfl, (circlePiece w r).lt.le⟩) := by
  obtain ⟨ε, hε, he⟩ := exists_small_circle_loop_formula_check hk hw
  refine ⟨ε, hε, ?_⟩
  intro r hr hre
  obtain ⟨hA, _, _, _, _, _, h3⟩ := he r hr hre
  have hP : ∀ v ∈ Surface.punctures k, (circlePiece w r).Avoids v :=
    fun v hv => hA v hv 0
  refine ⟨hP, ?_⟩
  intro base C z hz
  apply pieceLift_finish_eq_deck_start hk base C _ hP (circleChain_closed w r)
  rw [circlePiece_contour, h3.2.2, residue3_real_endSign hw]

/-- Passage to the finite quotient retains the signed cyclic displacement. -/
lemma pieceLift_quotient_finish {k m : ℕ} [NeZero m] (hk : 2 ≤ k)
    (base : PuncturedPlane k) (C : PeriodTarget) (p : Piece)
    (hA : ∀ w ∈ Surface.punctures k, p.Avoids w)
    (hc : p.finish = p.start) (n : ℤ)
    (hp : (p.contour (coeff3 k)).re = (2 * Real.pi) * (n : ℝ))
    (z : ℝ) (hz : (z : AddCircle (2 * Real.pi)) =
      (descendedIntegral hk base ⟨p.start, fun hw => p.start_ne (hA _ hw) rfl⟩).2.2) :
    HeightLift.periodQuotientMap m (pieceLift hk base C p hA z hz ⟨p.b, p.lt.le, le_rfl⟩) =
      HeightLift.cyclicDeck (n : ZMod m)
        (HeightLift.periodQuotientMap m (pieceLift hk base C p hA z hz ⟨p.a, le_rfl, p.lt.le⟩)) := by
  rw [pieceLift_finish_eq_deck_start hk base C p hA hc n hp z hz,
    HeightLift.cyclicDeck_intCast, HeightLift.periodDeck_mk]

/-- The signed end shift returns a quotient point precisely at multiples
of m; thus its cyclic permutation has order exactly m. -/
lemma endShift_return_iff {P : Type*} {F : P → PeriodTarget} {m : ℕ} [NeZero m]
    (k : ℕ) (w : ℂ) (n : ℤ) (x : HeightLift.PeriodQuotient F m) :
    HeightLift.cyclicDeck ((n * endSign k w : ℤ) : ZMod m) x = x ↔ (m : ℤ) ∣ n := by
  have he : HeightLift.periodDeck m (n * endSign k w) x = x ↔
      ((n * endSign k w : ℤ) : ZMod m) = 0 := by
    simpa only [HeightLift.periodDeck_zero, Int.cast_zero] using
      HeightLift.periodDeck_eq_iff m x (n * endSign k w) 0
  rw [HeightLift.cyclicDeck_intCast, he, ZMod.intCast_zmod_eq_zero_iff_dvd]
  unfold endSign
  split_ifs <;> simp

end KsIndex.KarcherData
