module

public import KsIndexLean.KarcherAxisExclusion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

@[expose] public section


/-! Exact ambient positions of the EW pole fibers. -/
noncomputable section
namespace KsIndex.KarcherData
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

lemma sin_height_zero_fiber (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = finiteParameter ⟨0, zero_not_puncture h.out⟩) :
    Real.sin (HeightLift.height q + Real.pi) = 1 := by
  have hs := sin_lift_height_shift h.out (reflectionBasepoint k)
    ⟨0, zero_not_puncture h.out⟩ rfl R.C q hq
  have hk : k ≠ 0 := by have := h.out; omega
  simpa [heightCayley, hk] using hs

/-- Every point of the immersion on the axis has half-integer height. -/
theorem axis_height_half_integer
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (ha : R.OnVerticalAxis q) :
    ∃ n : ℤ, HeightLift.height q + Real.pi = ((n : ℝ) + 1 / 2) * Real.pi := by
  have hc : Real.cos (HeightLift.height q + Real.pi) = 0 := by
    apply Real.cos_eq_zero_iff_sin_eq.mpr
    rcases (R.onVerticalAxis_iff_poles q).mp ha with hz | hi
    · exact Or.inl (R.sin_height_zero_fiber q hz)
    · exact Or.inr (sin_lift_height_infinity R.C R.hC q hi)
  obtain ⟨n, hn⟩ := Real.cos_eq_zero_iff.mp hc
  exact ⟨n, by rw [hn]; ring⟩

/-- The zero-parameter representative of the closed half period has height π/2. -/
theorem exists_axis_center :
    ∃ q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C,
      R.OnVerticalAxis q ∧ HeightLift.height q + Real.pi = Real.pi / 2 := by
  obtain ⟨q, hq⟩ := exists_halfPeriod_over_disk h.out (reflectionBasepoint k)
    ⟨0, zero_not_puncture h.out⟩ rfl R.C (by simp)
  refine ⟨q.val, centeredLiftAmbient_fibre_zero R q.val hq, ?_⟩
  have hc : Real.cos (HeightLift.height q.val + Real.pi) = 0 :=
    Real.cos_eq_zero_iff_sin_eq.mpr (Or.inl (R.sin_height_zero_fiber q.val hq))
  apply Real.strictAntiOn_cos.injOn q.property
    (show Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi from ⟨by positivity, by linarith [Real.pi_pos]⟩)
  rw [hc, Real.cos_pi_div_two]

lemma axis_deck (n : ℤ) (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (ha : R.OnVerticalAxis q) : R.OnVerticalAxis (HeightLift.deck n q) := ha

/-- Each of the paper's half-integer axis points actually occurs. -/
theorem exists_axis_half_integer (n : ℤ) :
    ∃ q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C,
      R.OnVerticalAxis q ∧ HeightLift.height q + Real.pi = ((n : ℝ) + 1 / 2) * Real.pi := by
  obtain ⟨q, ha, hh⟩ := R.exists_axis_center
  rcases Int.emod_two_eq_zero_or_one n with hn | hn
  · refine ⟨HeightLift.deck (n / 2) q, R.axis_deck _ q ha, ?_⟩
    have he : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) := by
      exact_mod_cast (show n = 2 * (n / 2) by omega)
    rw [HeightLift.height_deck, he]
    linarith
  · let q' := lowerSeamLift R.C R.hC q
    have ha' : R.OnVerticalAxis q' := (R.onVerticalAxis_lowerSeam q).mpr ha
    refine ⟨HeightLift.deck (n / 2 + 1) q', R.axis_deck _ q' ha', ?_⟩
    have he : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) + 1 := by
      exact_mod_cast (show n = 2 * (n / 2) + 1 by omega)
    have hh' := lowerSeamLift_height R.C R.hC q
    rw [HeightLift.height_deck, he]
    push_cast
    change HeightLift.height q' + _ + _ = _
    change HeightLift.height q' + Real.pi = _ at hh'
    linarith

/-- The axis intersection of the actual ambient image is precisely the
half-integer π lattice asserted in the cylindrical picture. -/
theorem ambient_axis_image :
    centeredLiftAmbient R.C R.t '' {q | R.OnVerticalAxis q} =
      Set.range (fun n : ℤ => ((0 : ℝ), (0 : ℝ), ((n : ℝ) + 1 / 2) * Real.pi)) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨n, hn⟩ := R.axis_height_half_integer q hq
    refine ⟨n, ?_⟩
    apply Prod.ext hq.1.symm
    exact Prod.ext hq.2.symm hn.symm
  · rintro ⟨n, rfl⟩
    obtain ⟨q, ha, hh⟩ := R.exists_axis_half_integer n
    refine ⟨q, ha, ?_⟩
    exact Prod.ext ha.1 (Prod.ext ha.2 hh)

/-- In the closed half period, removing the disk center removes exactly the
preimage of the ambient point (0,0,π/2). -/
theorem halfPeriod_center_iff (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    (R.diskMap q).val.val = 0 ↔
      centeredLiftAmbient R.C R.t q.val = ((0 : ℝ), (0 : ℝ), Real.pi / 2) := by
  have hp := R.projection_agrees q
  constructor
  · intro hz
    have hq : HeightLift.projection q.val = finiteParameter ⟨0, zero_not_puncture h.out⟩ := by
      rw [← hp]
      congr 1
      exact Subtype.ext hz
    have ha := centeredLiftAmbient_fibre_zero R q.val hq
    have hc : Real.cos (HeightLift.height q.val + Real.pi) = 0 :=
      Real.cos_eq_zero_iff_sin_eq.mpr (Or.inl (R.sin_height_zero_fiber q.val hq))
    have hh : HeightLift.height q.val + Real.pi = Real.pi / 2 := by
      apply Real.strictAntiOn_cos.injOn q.property
        (show Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi from
          ⟨by positivity, by linarith [Real.pi_pos]⟩)
      rw [hc, Real.cos_pi_div_two]
    exact Prod.ext ha.1 (Prod.ext ha.2 hh)
  · intro he
    have ha : R.OnVerticalAxis q.val :=
      ⟨congrArg Prod.fst he, congrArg (fun p : AmbientTriple => p.2.1) he⟩
    exact R.axis_finite q.val (R.diskMap q).val hp.symm ha

end PaperHalfPeriodRealization
end KsIndex.KarcherData
