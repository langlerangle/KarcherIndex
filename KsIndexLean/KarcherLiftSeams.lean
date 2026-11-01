module

public import KsIndexLean.KarcherHalfPeriodBoundary

@[expose] public section


/-! The two actual reflected seams of the normalized half-period. -/
noncomputable section
namespace KsIndex.KarcherData

/-- The global seam identity with the fixed basepoint's offset discharged. -/
lemma based_seam_identity {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C)) (p : ParameterSphere k) :
    extendedEWMap h.out (reflectionBasepoint k) C (parameterSeamReflection h.out p) =
      PeriodTarget.reflZ (extendedEWMap h.out (reflectionBasepoint k) C p) := by
  have he := extendedEWMap_seamReflection (reflectionBasepoint k)
    (by simp [reflectionBasepoint]) C hF p
  have hb : (⟨(starRingEnd ℂ (reflectionBasepoint k).val)⁻¹,
      inverse_conjugate_not_puncture (reflectionBasepoint k).property⟩ : PuncturedPlane k) =
      reflectionBasepoint k := by
    apply Subtype.ext
    simp [reflectionBasepoint]
  rwa [hb, descendedIntegral_self, zero_add] at he

/-- Reflection in normalized height π; raw height changes sign. -/
def upperSeamLift {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C))
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) C) :
    PeriodicEWCarrier h.out (reflectionBasepoint k) C :=
  ⟨(parameterSeamReflection h.out (HeightLift.projection q), -HeightLift.height q), by
    rw [based_seam_identity C hF]
    change ((-HeightLift.height q : ℝ) : AddCircle (2 * Real.pi)) =
      -(extendedEWMap h.out (reflectionBasepoint k) C (HeightLift.projection q)).2.2
    rw [AddCircle.coe_neg]
    exact congrArg Neg.neg q.property⟩

lemma upperSeamLift_projection {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C))
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) C) :
    HeightLift.projection (upperSeamLift C hF q) = parameterSeamReflection h.out (HeightLift.projection q) := rfl

lemma upperSeamLift_height {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C))
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) C) :
    HeightLift.height (upperSeamLift C hF q) + Real.pi =
      2 * Real.pi - (HeightLift.height q + Real.pi) := by
  change -HeightLift.height q + Real.pi = _
  ring

lemma upperSeamLift_involutive {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C)) :
    Function.Involutive (upperSeamLift C hF) := by
  intro q
  apply Subtype.ext
  apply Prod.ext
  · exact parameterSeamReflection_involutive h.out (HeightLift.projection q)
  · exact neg_neg (HeightLift.height q)

/-- Reflection in normalized height zero differs by one whole deck period. -/
def lowerSeamLift {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C))
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) C) :=
  HeightLift.deck (-1) (upperSeamLift C hF q)

lemma lowerSeamLift_height {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C))
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) C) :
    HeightLift.height (lowerSeamLift C hF q) + Real.pi = -(HeightLift.height q + Real.pi) := by
  change -HeightLift.height q + ((-1 : ℤ) : ℝ) * (2 * Real.pi) + Real.pi = _
  push_cast
  ring

lemma continuous_upperSeamLift {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C)) :
    Continuous (upperSeamLift C hF) := by
  apply Continuous.subtype_mk
  exact ((continuous_parameterSeamReflection h.out).comp HeightLift.continuous_projection).prodMk
    HeightLift.continuous_height.neg

lemma lowerSeamLift_involutive {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C)) :
    Function.Involutive (lowerSeamLift C hF) := by
  intro q
  apply Subtype.ext
  apply Prod.ext
  · exact parameterSeamReflection_involutive h.out (HeightLift.projection q)
  · change -(-HeightLift.height q + ((-1 : ℤ) : ℝ) * (2 * Real.pi)) +
      ((-1 : ℤ) : ℝ) * (2 * Real.pi) = HeightLift.height q
    ring

lemma continuous_lowerSeamLift {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C)) :
    Continuous (lowerSeamLift C hF) :=
  (HeightLift.continuous_deck (-1)).comp (continuous_upperSeamLift C hF)

lemma parameterSeamReflection_circle {k : ℕ} (hk : 2 ≤ k)
    (w : PuncturedPlane k) (hw : ‖w.val‖ = 1) :
    parameterSeamReflection hk (finiteParameter w) = finiteParameter w := by
  have hn : w.val ≠ 0 := by intro he; simp [he] at hw
  rw [parameterSeamReflection_finite hk w hn (inverse_conjugate_not_puncture w.property)]
  congr 1
  apply Subtype.ext
  change (starRingEnd ℂ w.val)⁻¹ = w.val
  rw [← Complex.inv_eq_conj hw, inv_inv]

/-- On either boundary height, the parameter seam reflection fixes the parameter. -/
lemma seam_parameter_fixed_at_boundary {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C))
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) C)
    (hz : HeightLift.height q + Real.pi = 0 ∨ HeightLift.height q + Real.pi = Real.pi) :
    parameterSeamReflection h.out (HeightLift.projection q) = HeightLift.projection q := by
  have hi : HeightLift.height q + Real.pi ∈ Set.Icc 0 Real.pi := by
    rcases hz with hz | hz <;> rw [hz] <;> constructor <;> linarith [Real.pi_pos]
  obtain ⟨w, hw⟩ := halfPeriod_disk_parameter C hF ⟨q, hi⟩
  have hs : Real.sin (HeightLift.height q + Real.pi) = 0 := by
    rcases hz with hz | hz <;> rw [hz] <;> simp
  have hn := (sin_lift_height_shift_zero_iff h.out (reflectionBasepoint k) w.val rfl C q hw.symm).mp hs
  rw [← hw]
  exact parameterSeamReflection_circle h.out w.val hn

lemma upperSeamLift_fixed_iff {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C))
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) C) :
    upperSeamLift C hF q = q ↔ HeightLift.height q + Real.pi = Real.pi := by
  constructor
  · intro he
    have hh := congrArg HeightLift.height he
    change -HeightLift.height q = HeightLift.height q at hh
    linarith
  · intro hz
    apply Subtype.ext
    apply Prod.ext
    · exact seam_parameter_fixed_at_boundary C hF q (Or.inr hz)
    · change -HeightLift.height q = HeightLift.height q
      linarith

lemma lowerSeamLift_fixed_iff {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C))
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) C) :
    lowerSeamLift C hF q = q ↔ HeightLift.height q + Real.pi = 0 := by
  constructor
  · intro he
    have hh := lowerSeamLift_height C hF q
    rw [he] at hh
    linarith
  · intro hz
    apply Subtype.ext
    apply Prod.ext
    · exact seam_parameter_fixed_at_boundary C hF q (Or.inl hz)
    · change -HeightLift.height q + ((-1 : ℤ) : ℝ) * (2 * Real.pi) = HeightLift.height q
      push_cast
      linarith

/-- Apply the paper's vertical shift and an arbitrary real horizontal center.
The center can subsequently be chosen by the proved normalization theorem. -/
def centeredLiftAmbient {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget) (t : ℝ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) C) : AmbientTriple :=
  (t + (HeightLift.ambient q).1, (HeightLift.ambient q).2.1, HeightLift.height q + Real.pi)

lemma centeredLiftAmbient_upperSeam {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C)) (t : ℝ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) C) :
    centeredLiftAmbient C t (upperSeamLift C hF q) =
      ((centeredLiftAmbient C t q).1, (centeredLiftAmbient C t q).2.1,
        2 * Real.pi - (centeredLiftAmbient C t q).2.2) := by
  apply Prod.ext
  · change t + (extendedEWMap h.out (reflectionBasepoint k) C
        (parameterSeamReflection h.out (HeightLift.projection q))).1 = _
    rw [based_seam_identity C hF]
    rfl
  · apply Prod.ext
    · change (extendedEWMap h.out (reflectionBasepoint k) C
        (parameterSeamReflection h.out (HeightLift.projection q))).2.1 = _
      rw [based_seam_identity C hF]
      rfl
    · exact upperSeamLift_height C hF q

lemma centeredLiftAmbient_lowerSeam {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C)) (t : ℝ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) C) :
    centeredLiftAmbient C t (lowerSeamLift C hF q) =
      ((centeredLiftAmbient C t q).1, (centeredLiftAmbient C t q).2.1,
        -(centeredLiftAmbient C t q).2.2) := by
  apply Prod.ext
  · change t + (extendedEWMap h.out (reflectionBasepoint k) C
        (parameterSeamReflection h.out (HeightLift.projection q))).1 = _
    rw [based_seam_identity C hF]
    rfl
  · apply Prod.ext
    · change (extendedEWMap h.out (reflectionBasepoint k) C
        (parameterSeamReflection h.out (HeightLift.projection q))).2.1 = _
      rw [based_seam_identity C hF]
      rfl
    · exact lowerSeamLift_height C hF q

/-- The real normalized immersion projects to the same translated EW map
 used by positional normalization; this is equality, not a separate model. -/
lemma project_centeredLiftAmbient {k : ℕ} [h : Fact (2 ≤ k)] (C : PeriodTarget) (t : ℝ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) C) :
    projectPeriod (centeredLiftAmbient C t q) =
      (t, 0, (Real.pi : AddCircle (2 * Real.pi))) +
        extendedEWMap h.out (reflectionBasepoint k) C (HeightLift.projection q) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change _ = 0 + _
      rw [zero_add]
      rfl
    · change ((HeightLift.height q + Real.pi : ℝ) : AddCircle (2 * Real.pi)) =
        (Real.pi : AddCircle (2 * Real.pi)) +
          (extendedEWMap h.out (reflectionBasepoint k) C (HeightLift.projection q)).2.2
      rw [AddCircle.coe_add]
      exact (congrArg (fun z : AddCircle (2 * Real.pi) => z + Real.pi) q.property).trans (add_comm _ _)

end KsIndex.KarcherData
