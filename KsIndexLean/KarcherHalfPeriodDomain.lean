module

public import KsIndexLean.KarcherHeightCayley

@[expose] public section


/-! The paper's closed half-period, with the required vertical π shift. -/
noncomputable section
namespace KsIndex.KarcherData
open Set
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The raw basepoint-1 height is shifted by π to match the paper. -/
def PaperHalfPeriod {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) (C : PeriodTarget) :=
  {q : PeriodicEWCarrier hk b C // HeightLift.height q + Real.pi ∈ Icc 0 Real.pi}

/-- No two intrinsic points of the closed half-period have the same parameter. -/
theorem halfPeriod_projection_injective {k : ℕ} (hk : 2 ≤ k)
    (b : PuncturedPlane k) (C : PeriodTarget) :
    Function.Injective (fun q : PaperHalfPeriod hk b C => HeightLift.projection q.val) := by
  intro q r hp
  have he : (HeightLift.height q.val : AddCircle (2 * Real.pi)) = HeightLift.height r.val := by
    exact q.val.property.trans ((congrArg (fun p => (extendedEWMap hk b C p).2.2) hp).trans
      r.val.property.symm)
  have hq : HeightLift.height q.val ∈ Ico (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    have := q.property; constructor <;> linarith [this.1, this.2, Real.pi_pos]
  have hr : HeightLift.height r.val ∈ Ico (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    have := r.property; constructor <;> linarith [this.1, this.2, Real.pi_pos]
  have hz := (AddCircle.coe_eq_coe_iff_of_mem_Ico hq hr).mp he
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hp hz

/-- Every finite parameter in the disk has a representative in the closed half-period. -/
theorem exists_halfPeriod_over_disk {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (hb : b.val = 1) (C : PeriodTarget) (hw : ‖w.val‖ ≤ 1) :
    ∃ q : PaperHalfPeriod hk b C, HeightLift.projection q.val = finiteParameter w := by
  let z := AddCircle.equivIco (2 * Real.pi) (-Real.pi)
    (extendedEWMap hk b C (finiteParameter w)).2.2
  let q : PeriodicEWCarrier hk b C := ⟨(finiteParameter w, z.val), AddCircle.coe_equivIco⟩
  have hz : HeightLift.height q + Real.pi ∈ Ico 0 (2 * Real.pi) := by
    have hh := z.property
    change z.val + Real.pi ∈ Ico 0 (2 * Real.pi)
    constructor <;> linarith [hh.1, hh.2]
  have hs : 0 ≤ Real.sin (HeightLift.height q + Real.pi) := by
    rcases lt_or_eq_of_le hw with hlt | heq
    · exact ((sin_lift_height_shift_pos_iff hk b w hb C q rfl).mpr hlt).le
    · exact le_of_eq ((sin_lift_height_shift_zero_iff hk b w hb C q rfl).mpr heq).symm
  have hu : HeightLift.height q + Real.pi ≤ Real.pi := by
    by_contra hn
    have hp : 0 < HeightLift.height q + Real.pi - Real.pi := by linarith
    have hlt : HeightLift.height q + Real.pi - Real.pi < Real.pi := by linarith [hz.2]
    have ht := Real.sin_pos_of_pos_of_lt_pi hp hlt
    rw [Real.sin_sub_pi] at ht
    linarith
  exact ⟨⟨q, hz.1, hu⟩, rfl⟩

/-- Every finite point in the closed half-period projects into the closed disk. -/
theorem halfPeriod_finite_norm_le {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (hb : b.val = 1) (C : PeriodTarget)
    (q : PaperHalfPeriod hk b C)
    (hq : HeightLift.projection q.val = finiteParameter w) : ‖w.val‖ ≤ 1 := by
  have hs := Real.sin_nonneg_of_mem_Icc q.property
  rcases lt_or_eq_of_le hs with hp | hz
  · exact ((sin_lift_height_shift_pos_iff hk b w hb C q.val hq).mp hp).le
  · exact le_of_eq ((sin_lift_height_shift_zero_iff hk b w hb C q.val hq).mp hz.symm)

/-- Each punctured closed-disk parameter has exactly one intrinsic point in
 the paper's closed half-period. Exclusion of points over infinity is separate. -/
theorem existsUnique_halfPeriod_over_disk {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (hb : b.val = 1) (C : PeriodTarget) (hw : ‖w.val‖ ≤ 1) :
    ∃! q : PaperHalfPeriod hk b C, HeightLift.projection q.val = finiteParameter w := by
  obtain ⟨q, hq⟩ := exists_halfPeriod_over_disk hk b w hb C hw
  exact ⟨q, hq, fun r hr => halfPeriod_projection_injective hk b C (hr.trans hq.symm)⟩

/-- Global seam reflection forces the shifted sine to be -1 above infinity. -/
theorem sin_lift_height_infinity {k : ℕ} [h : Fact (2 ≤ k)]
    (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C))
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) C)
    (hq : HeightLift.projection q = infinityParameter k) :
    Real.sin (HeightLift.height q + Real.pi) = -1 := by
  let w : PuncturedPlane k := ⟨0, zero_not_puncture h.out⟩
  have he := extendedEWMap_seamReflection (reflectionBasepoint k)
    (by simp [reflectionBasepoint]) C hF (infinityParameter k)
  have hb : (⟨(starRingEnd ℂ (reflectionBasepoint k).val)⁻¹,
      inverse_conjugate_not_puncture (reflectionBasepoint k).property⟩ : PuncturedPlane k) =
      reflectionBasepoint k := by
    apply Subtype.ext
    simp [reflectionBasepoint]
  rw [hb, descendedIntegral_self, zero_add, parameterSeamReflection_infinity] at he
  have hz : ((-HeightLift.height q : ℝ) : AddCircle (2 * Real.pi)) =
      (extendedEWMap h.out (reflectionBasepoint k) C (finiteParameter w)).2.2 := by
    rw [he]
    change ((-HeightLift.height q : ℝ) : AddCircle (2 * Real.pi)) =
      -(extendedEWMap h.out (reflectionBasepoint k) C (infinityParameter k)).2.2
    rw [AddCircle.coe_neg, ← hq]
    exact congrArg Neg.neg q.property
  let r : PeriodicEWCarrier h.out (reflectionBasepoint k) C :=
    ⟨(finiteParameter w, -HeightLift.height q), hz⟩
  have hs := sin_lift_height_shift h.out (reflectionBasepoint k) w rfl C r rfl
  have hk : k ≠ 0 := by have := h.out; omega
  simp only [w, heightCayley, zero_pow hk, mul_zero, add_zero, sub_zero,
    div_one, Complex.one_re, norm_one] at hs
  change Real.sin (-HeightLift.height q + Real.pi) = 1 at hs
  rw [Real.sin_add_pi, Real.sin_neg, neg_neg] at hs
  rw [Real.sin_add_pi, hs]

/-- No point over infinity belongs to the paper's closed half-period. -/
theorem halfPeriod_ne_infinity {k : ℕ} [h : Fact (2 ≤ k)]
    (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C))
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) C) :
    HeightLift.projection q.val ≠ infinityParameter k := by
  intro he
  have hn := Real.sin_nonneg_of_mem_Icc q.property
  rw [sin_lift_height_infinity C hF q.val he] at hn
  norm_num at hn

/-- The target is the actual finite punctured closed unit disk. -/
def PuncturedClosedDisk (k : ℕ) := {w : PuncturedPlane k // ‖w.val‖ ≤ 1}

/-- Every point of the full half-period has a finite disk parameter. -/
theorem halfPeriod_disk_parameter {k : ℕ} [h : Fact (2 ≤ k)]
    (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C))
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) C) :
    ∃ w : PuncturedClosedDisk k, finiteParameter w.val = HeightLift.projection q.val := by
  rcases parameterSphere_cases (HeightLift.projection q.val) with hi | ⟨w, hw⟩
  · exact (halfPeriod_ne_infinity C hF q hi).elim
  · exact ⟨⟨w, halfPeriod_finite_norm_le h.out (reflectionBasepoint k) w rfl C q hw.symm⟩, hw⟩

/-- The actual parameter projection restricts to a bijection from the paper's
 closed half-period to the punctured closed disk, including both boundary levels. -/
theorem exists_halfPeriod_disk_bijection {k : ℕ} [h : Fact (2 ≤ k)]
    (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out (reflectionBasepoint k) C)) :
    ∃ f : PaperHalfPeriod h.out (reflectionBasepoint k) C → PuncturedClosedDisk k,
      (∀ q, finiteParameter (f q).val = HeightLift.projection q.val) ∧ Function.Bijective f := by
  choose f hf using halfPeriod_disk_parameter C hF
  refine ⟨f, hf, ?_, ?_⟩
  · intro q r he
    apply halfPeriod_projection_injective h.out (reflectionBasepoint k) C
    exact (hf q).symm.trans ((congrArg (fun w : PuncturedClosedDisk k => finiteParameter w.val) he).trans (hf r))
  · intro w
    obtain ⟨q, hq⟩ := exists_halfPeriod_over_disk h.out (reflectionBasepoint k) w.val rfl C w.property
    refine ⟨q, ?_⟩
    apply Subtype.ext
    exact finiteParameter_injective k ((hf q).trans hq)

/-- Connectedness and the closed half-period bijection hold for one and the
 same actual continuous EW extension. -/
theorem exists_connected_halfPeriod_disk_bijection {k : ℕ} [h : Fact (2 ≤ k)] :
    ∃ C : PeriodTarget, Continuous (extendedEWMap h.out (reflectionBasepoint k) C) ∧
      PathConnectedSpace (PeriodicEWCarrier h.out (reflectionBasepoint k) C) ∧
      ∃ f : PaperHalfPeriod h.out (reflectionBasepoint k) C → PuncturedClosedDisk k,
        (∀ q, finiteParameter (f q).val = HeightLift.projection q.val) ∧ Function.Bijective f := by
  obtain ⟨C, hC, hc⟩ := exists_pathConnected_periodicEW (reflectionBasepoint k)
  exact ⟨C, hC, hc, exists_halfPeriod_disk_bijection C hC⟩

end KsIndex.KarcherData
