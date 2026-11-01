module

public import KsIndexLean.KarcherUpperSeamFormula

@[expose] public section


/-! The complementary seam band and its actual reflected parameter expression. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

def lowerSeamBand (R : PaperHalfPeriodRealization k) (j : ℤ) :
    Set (PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :=
  {q | HeightLift.height q + Real.pi ∈ Ioo
    ((j : ℝ) * (2 * Real.pi) + Real.pi) ((j : ℝ) * (2 * Real.pi) + 3 * Real.pi)}

lemma lowerSeamBand_eq_strip (R : PaperHalfPeriodRealization k) (j : ℤ) :
    R.lowerSeamBand j = HeightLift.strip ((j : ℝ) * (2 * Real.pi)) := by
  ext q
  change (_ < HeightLift.height q + Real.pi ∧ HeightLift.height q + Real.pi < _) ↔
    (_ < HeightLift.height q ∧ HeightLift.height q < _)
  constructor <;> intro hq <;> constructor <;> linarith [hq.1, hq.2]

lemma isOpen_lowerSeamBand (R : PaperHalfPeriodRealization k) (j : ℤ) :
    IsOpen (R.lowerSeamBand j) := by
  rw [lowerSeamBand_eq_strip]
  exact HeightLift.isOpen_strip _

lemma lowerSeamBand_projection_injective (R : PaperHalfPeriodRealization k) (j : ℤ) :
    Set.InjOn HeightLift.projection (R.lowerSeamBand j) := by
  intro q hq r hr he
  rw [lowerSeamBand_eq_strip] at hq hr
  have hh : (HeightLift.stripHomeomorph R.hC _)
      (⟨q,hq⟩ : HeightLift.strip ((j : ℝ) * (2 * Real.pi))) =
      (HeightLift.stripHomeomorph R.hC _) ⟨r,hr⟩ := Subtype.ext he
  exact congrArg Subtype.val ((HeightLift.stripHomeomorph R.hC _).injective hh)

lemma lowerSeamBand_copies (R : PaperHalfPeriodRealization k) (j : ℤ)
    {q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C}
    (hq : q ∈ R.lowerSeamBand j) :
    ∃ w : PuncturedClosedDisk k, q = R.oddDiskPoint j w ∨ q = R.evenDiskPoint (j+1) w := by
  obtain ⟨l, w, rfl | rfl⟩ := R.diskCopies_cover q
  · have hb := R.evenDiskPoint_height_mem l w
    have hl : (j : ℝ) < (l : ℝ) := by nlinarith [hq.1, hb.2, Real.pi_pos]
    have hu : (l : ℝ) < (j : ℝ) + 2 := by nlinarith [hq.2, hb.1, Real.pi_pos]
    have hl' : j < l := by exact_mod_cast hl
    have hu' : l < j + 2 := by exact_mod_cast hu
    have he : l = j+1 := by omega
    rw [he]
    exact ⟨w, Or.inr rfl⟩
  · have hb := R.oddDiskPoint_height_mem l w
    have hl : (j : ℝ) - 1 < (l : ℝ) := by nlinarith [hq.1, hb.2, Real.pi_pos]
    have hu : (l : ℝ) < (j : ℝ) + 1 := by nlinarith [hq.2, hb.1, Real.pi_pos]
    have hl' : j - 1 < l := by exact_mod_cast hl
    have hu' : l < j + 1 := by exact_mod_cast hu
    have he : l = j := by omega
    subst l
    exact ⟨w, Or.inl rfl⟩

lemma odd_mem_lowerSeamBand_iff_even (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.oddDiskPoint j w ∈ R.lowerSeamBand j ↔ R.evenDiskPoint (j+1) w ∈ R.lowerSeamBand j := by
  change (_ < HeightLift.height (R.oddDiskPoint j w) + Real.pi ∧
      HeightLift.height (R.oddDiskPoint j w) + Real.pi < _) ↔
    (_ < HeightLift.height (R.evenDiskPoint (j+1) w) + Real.pi ∧
      HeightLift.height (R.evenDiskPoint (j+1) w) + Real.pi < _)
  rw [evenDiskPoint_height, oddDiskPoint_height]
  push_cast
  constructor <;> intro hw <;> constructor <;> linarith [hw.1, hw.2]

lemma odd_eq_even_on_circle_in_band (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ = 1)
    (hb : R.evenDiskPoint (j+1) w ∈ R.lowerSeamBand j) :
    R.oddDiskPoint j w = R.evenDiskPoint (j+1) w := by
  apply R.lowerSeamBand_projection_injective j
    ((R.odd_mem_lowerSeamBand_iff_even j w).mpr hb) hb
  rw [evenDiskPoint_projection, oddDiskPoint_projection,
    parameterSeamReflection_circle h.out w.val hw]

lemma lowerSeamBand_glue_formula (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (z : PuncturedPlane k) (hq : q ∈ R.lowerSeamBand j)
    (hp : parameterSeamReflection h.out (HeightLift.projection q) = finiteParameter z) :
    f (HeightLift.periodQuotientMap m q) =
      Surface.glue (encodeDiskFunction (R.diskFunctionPullback f))
        (oddCopyIndex (j : ZMod m)) z.val := by
  obtain ⟨w, rfl | rfl⟩ := R.lowerSeamBand_copies j hq
  · rw [oddDiskPoint_projection, parameterSeamReflection_involutive] at hp
    have he : w.val = z := finiteParameter_injective k hp
    rw [← he, Surface.glue, if_pos w.property]
    exact (R.encoded_oddPoint f j w).symm
  · rw [evenDiskPoint_projection] at hp
    have hp' : HeightLift.projection (R.oddDiskPoint j w) = finiteParameter z := by
      rw [oddDiskPoint_projection]; exact hp
    obtain ⟨hw0, hz⟩ := R.oddPoint_finite_parameter j w z hp'
    by_cases hn : ‖z.val‖ ≤ 1
    · have hmul : ‖z.val‖ * ‖w.val.val‖ = 1 := by
        rw [hz, norm_inv, Complex.norm_conj]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)
      have hw1 : ‖w.val.val‖ = 1 := by nlinarith [w.property, norm_nonneg z.val, norm_nonneg w.val.val]
      have hew := R.odd_eq_even_on_circle_in_band j w hw1 hq
      have hez : w.val = z := by
        rw [parameterSeamReflection_circle h.out w.val hw1] at hp
        exact finiteParameter_injective k hp
      rw [← hez, Surface.glue, if_pos w.property, ← hew]
      exact (R.encoded_oddPoint f j w).symm
    · have hz' : 1 / starRingEnd ℂ z.val = w.val.val := by
        rw [hz, map_inv₀, starRingEnd_self_apply, one_div, inv_inv]
      rw [Surface.glue, if_neg hn, oddCopyIndex_succ, hz']
      have hi : (j : ZMod m) + 1 = ((j+1 : ℤ) : ZMod m) := by push_cast; rfl
      rw [hi]
      exact (R.encoded_evenPoint f (j+1) w).symm

lemma seamBands_cover (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    ∃ j : ℤ, q ∈ R.upperSeamBand j ∨ q ∈ R.lowerSeamBand j := by
  obtain ⟨j, w, rfl | rfl⟩ := R.diskCopies_cover q
  · have hb := R.evenDiskPoint_height_mem j w
    by_cases ht : (j : ℝ) * (2 * Real.pi) < HeightLift.height (R.evenDiskPoint j w) + Real.pi
    · refine ⟨j, Or.inl ⟨ht, ?_⟩⟩
      linarith [hb.2, Real.pi_pos]
    · refine ⟨j-1, Or.inr ?_⟩
      change ((j-1 : ℤ) : ℝ) * (2 * Real.pi) + Real.pi < _ ∧
        _ < ((j-1 : ℤ) : ℝ) * (2 * Real.pi) + 3 * Real.pi
      push_cast
      constructor <;> linarith [hb.1, hb.2, Real.pi_pos]
  · have hb := R.oddDiskPoint_height_mem j w
    by_cases ht : HeightLift.height (R.oddDiskPoint j w) + Real.pi < (j : ℝ) * (2 * Real.pi) + 2 * Real.pi
    · refine ⟨j, Or.inl ⟨?_, ht⟩⟩
      linarith [hb.1, Real.pi_pos]
    · refine ⟨j, Or.inr ⟨?_, ?_⟩⟩ <;> linarith [hb.1, hb.2, Real.pi_pos]

end KsIndex.KarcherData.PaperHalfPeriodRealization
