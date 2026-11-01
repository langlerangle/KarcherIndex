module

public import KsIndexLean.KarcherDiskCopyCoverage

@[expose] public section


/-! Exact fibers of the ordered disk maps on the infinite periodic carrier. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma evenDiskPoint_eq_iff (R : PaperHalfPeriodRealization k) (j l : ℤ)
    (w v : PuncturedClosedDisk k) :
    R.evenDiskPoint j w = R.evenDiskPoint l v ↔ j = l ∧ w = v := by
  constructor
  · intro he
    have hv : w = v := Subtype.ext (finiteParameter_injective k (by
      simpa only [evenDiskPoint_projection] using congrArg HeightLift.projection he))
    subst v
    have hh := congrArg HeightLift.height he
    simp only [evenDiskPoint, HeightLift.height_deck] at hh
    have hj : (j : ℝ) = l := by nlinarith [Real.pi_pos]
    exact ⟨by exact_mod_cast hj, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma oddDiskPoint_eq_iff (R : PaperHalfPeriodRealization k) (j l : ℤ)
    (w v : PuncturedClosedDisk k) :
    R.oddDiskPoint j w = R.oddDiskPoint l v ↔ j = l ∧ w = v := by
  constructor
  · intro he
    have hp := congrArg HeightLift.projection he
    simp only [oddDiskPoint_projection] at hp
    have hv : w = v := Subtype.ext (finiteParameter_injective k
      ((parameterSeamReflection_involutive h.out).injective hp))
    subst v
    have hh := congrArg HeightLift.height he
    simp only [oddDiskPoint, HeightLift.height_deck] at hh
    have hj : (j : ℝ) = l := by nlinarith [Real.pi_pos]
    exact ⟨by exact_mod_cast hj, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Opposite-parity copies intersect only on the two adjacent seam families. -/
theorem evenDiskPoint_eq_odd_iff (R : PaperHalfPeriodRealization k) (j l : ℤ)
    (w v : PuncturedClosedDisk k) :
    R.evenDiskPoint j w = R.oddDiskPoint l v ↔
      w = v ∧ ((j = l ∧ w.val.val ∈ Surface.arc k 1) ∨
        (j = l + 1 ∧ w.val.val ∈ Surface.arc k 0)) := by
  constructor
  · intro he
    have hj := R.evenDiskPoint_height_mem j w
    have hl := R.oddDiskPoint_height_mem l v
    rw [← he] at hl
    have hlj : (l : ℝ) ≤ j := by
      nlinarith [hj.2, hl.1, Real.pi_pos]
    have hjl : (j : ℝ) ≤ l + 1 := by
      nlinarith [hj.1, hl.2, Real.pi_pos]
    have hlj' : l ≤ j := by exact_mod_cast hlj
    have hjl' : j ≤ l + 1 := by exact_mod_cast hjl
    have hcase : j = l ∨ j = l + 1 := by omega
    rcases hcase with rfl | rfl
    · have hzw : HeightLift.height (R.baseDiskPoint w) + Real.pi = Real.pi := by
        have hh := R.evenDiskPoint_height j w
        nlinarith [hj.2, hl.1]
      have haw : w.val.val ∈ Surface.arc k 1 :=
        (halfPeriod_height_pi_iff_arc h.out (reflectionBasepoint k) w.val rfl R.C
          (R.diskHomeomorph.symm w) (R.baseDiskPoint_projection w)).mp hzw
      have hv : w = v := R.oddDiskPoint_injective j
        (((R.even_odd_seam_iff j w).mpr haw).symm.trans he)
      exact ⟨hv, Or.inl ⟨rfl, haw⟩⟩
    · have hzw : HeightLift.height (R.baseDiskPoint w) + Real.pi = 0 := by
        have hh := R.evenDiskPoint_height (l + 1) w
        push_cast at hh hj hl
        nlinarith [hj.1, hl.2]
      have haw : w.val.val ∈ Surface.arc k 0 :=
        (halfPeriod_height_zero_iff_arc h.out (reflectionBasepoint k) w.val rfl R.C
          (R.diskHomeomorph.symm w) (R.baseDiskPoint_projection w)).mp hzw
      have hv : w = v := R.oddDiskPoint_injective l
        (((R.odd_even_seam_iff l w).mpr haw).trans he)
      exact ⟨hv, Or.inr ⟨rfl, haw⟩⟩
  · rintro ⟨rfl, (⟨rfl, ha⟩ | ⟨rfl, ha⟩)⟩
    · exact (R.even_odd_seam_iff _ _).mpr ha
    · exact ((R.odd_even_seam_iff _ _).mpr ha).symm

end KsIndex.KarcherData.PaperHalfPeriodRealization
