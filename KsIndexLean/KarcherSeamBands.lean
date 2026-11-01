module

public import KsIndexLean.KarcherDiskFunctions
public import KsIndexLean.KarcherPeriodProjectionSmooth

@[expose] public section


/-! The two adjacent disks in an open full-period band around an upper seam. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- An open band centered on the seam between even copy j and odd copy j. -/
def upperSeamBand (R : PaperHalfPeriodRealization k) (j : ℤ) :
    Set (PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :=
  {q | HeightLift.height q + Real.pi ∈
    Ioo ((j : ℝ) * (2 * Real.pi)) ((j : ℝ) * (2 * Real.pi) + 2 * Real.pi)}

lemma upperSeamBand_eq_strip (R : PaperHalfPeriodRealization k) (j : ℤ) :
    R.upperSeamBand j = HeightLift.strip ((j : ℝ) * (2 * Real.pi) - Real.pi) := by
  ext q
  change (_ < HeightLift.height q + Real.pi ∧ HeightLift.height q + Real.pi < _) ↔
    (_ < HeightLift.height q ∧ HeightLift.height q < _)
  constructor <;> intro hq <;> constructor <;> linarith [hq.1, hq.2]

lemma isOpen_upperSeamBand (R : PaperHalfPeriodRealization k) (j : ℤ) :
    IsOpen (R.upperSeamBand j) := by
  rw [upperSeamBand_eq_strip]
  exact HeightLift.isOpen_strip _

lemma upperSeamBand_projection_injective (R : PaperHalfPeriodRealization k) (j : ℤ) :
    Set.InjOn HeightLift.projection (R.upperSeamBand j) := by
  intro q hq r hr he
  rw [upperSeamBand_eq_strip] at hq hr
  have hh : (HeightLift.stripHomeomorph R.hC _)
      (⟨q,hq⟩ : HeightLift.strip ((j : ℝ) * (2 * Real.pi) - Real.pi)) =
      (HeightLift.stripHomeomorph R.hC _) ⟨r,hr⟩ := Subtype.ext he
  exact congrArg Subtype.val ((HeightLift.stripHomeomorph R.hC _).injective hh)

lemma upperSeamBand_copies (R : PaperHalfPeriodRealization k) (j : ℤ)
    {q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C}
    (hq : q ∈ R.upperSeamBand j) :
    ∃ w : PuncturedClosedDisk k, q = R.evenDiskPoint j w ∨ q = R.oddDiskPoint j w := by
  obtain ⟨l, w, rfl | rfl⟩ := R.diskCopies_cover q
  · have hb := R.evenDiskPoint_height_mem l w
    have hl : (j : ℝ) - 1 < (l : ℝ) := by nlinarith [hq.1, hb.2, Real.pi_pos]
    have hu : (l : ℝ) < (j : ℝ) + 1 := by nlinarith [hq.2, hb.1, Real.pi_pos]
    have hl' : j - 1 < l := by exact_mod_cast hl
    have hu' : l < j + 1 := by exact_mod_cast hu
    have he : l = j := by omega
    subst l
    exact ⟨w, Or.inl rfl⟩
  · have hb := R.oddDiskPoint_height_mem l w
    have hl : (j : ℝ) - 1 < (l : ℝ) := by nlinarith [hq.1, hb.2, Real.pi_pos]
    have hu : (l : ℝ) < (j : ℝ) + 1 := by nlinarith [hq.2, hb.1, Real.pi_pos]
    have hl' : j - 1 < l := by exact_mod_cast hl
    have hu' : l < j + 1 := by exact_mod_cast hu
    have he : l = j := by omega
    subst l
    exact ⟨w, Or.inr rfl⟩

lemma even_mem_upperSeamBand_iff_odd (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.evenDiskPoint j w ∈ R.upperSeamBand j ↔ R.oddDiskPoint j w ∈ R.upperSeamBand j := by
  change (_ < HeightLift.height (R.evenDiskPoint j w) + Real.pi ∧
      HeightLift.height (R.evenDiskPoint j w) + Real.pi < _) ↔
    (_ < HeightLift.height (R.oddDiskPoint j w) + Real.pi ∧
      HeightLift.height (R.oddDiskPoint j w) + Real.pi < _)
  rw [evenDiskPoint_height, oddDiskPoint_height]
  constructor <;> intro hw <;> constructor <;> linarith [hw.1, hw.2]

lemma even_eq_odd_on_circle_in_band (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ = 1)
    (hb : R.oddDiskPoint j w ∈ R.upperSeamBand j) :
    R.evenDiskPoint j w = R.oddDiskPoint j w := by
  apply R.upperSeamBand_projection_injective j
    ((R.even_mem_upperSeamBand_iff_odd j w).mpr hb) hb
  rw [evenDiskPoint_projection, oddDiskPoint_projection,
    parameterSeamReflection_circle h.out w.val hw]

end KsIndex.KarcherData.PaperHalfPeriodRealization
