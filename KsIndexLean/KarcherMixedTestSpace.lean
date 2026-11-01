module

public import KsIndexLean.KarcherNeumannCoreCharacter
public import KsIndexLean.KarcherNeumannTestSpace
public import KsIndexLean.NullityGreen

@[expose] public section


/-! Compact mixed (Zaremba) **core** test fields on the closed geometric half period: a Neumann
closed-disk test whose coordinate additionally vanishes in a neighborhood of the height-0
Dirichlet slit (Neumann-free on the height-π arc). This neighborhood vanishing is *stronger* than
a zero boundary trace. For a supplied `PaperHalfPeriodRealization k` with `k ≥ 2`, this file
constructs the test submodule, maps its rotation-character tests into the natural disk core,
and realizes natural-core character tests with equality of coordinates on the open disk.
The full weak-domain index identification is a separate density/seam result; no index equality
is proved in this file. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SingleDisk KsIndex.Trace KsIndex.FormIndex
  KsIndex.Bracket KsIndex.NullityDecomp
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Compact mixed (Zaremba) core test field: a Neumann closed-disk test whose coordinate also
vanishes in a neighborhood of the arc-0 Dirichlet slit. -/
def IsMixedTest (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) : Prop :=
  R.IsNeumannTest f ∧ SuppAwaySet (slit k) (R.halfPeriodCoordinate f)

lemma isMixedTest_zero (R : PaperHalfPeriodRealization k) : R.IsMixedTest 0 := by
  refine ⟨R.isNeumannTest_zero, 1, one_pos, fun w _ => ?_⟩
  rw [show R.halfPeriodCoordinate 0 = 0 from R.halfPeriodCoordinateLM.map_zero]
  rfl

lemma IsMixedTest.add {R : PaperHalfPeriodRealization k}
    {f g : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ}
    (hf : R.IsMixedTest f) (hg : R.IsMixedTest g) : R.IsMixedTest (f + g) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  obtain ⟨ε₁, h₁, hf2⟩ := hf.2
  obtain ⟨ε₂, h₂, hg2⟩ := hg.2
  refine ⟨min ε₁ ε₂, lt_min h₁ h₂, fun w ⟨p, hp, hwp⟩ => ?_⟩
  rw [R.halfPeriodCoordinate_add f g w,
    hf2 w ⟨p, hp, lt_of_lt_of_le hwp (min_le_left _ _)⟩,
    hg2 w ⟨p, hp, lt_of_lt_of_le hwp (min_le_right _ _)⟩, add_zero]

lemma IsMixedTest.smul {R : PaperHalfPeriodRealization k}
    {f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ}
    (hf : R.IsMixedTest f) (a : ℂ) : R.IsMixedTest (a • f) := by
  refine ⟨hf.1.smul a, ?_⟩
  obtain ⟨ε, hε, hf2⟩ := hf.2
  refine ⟨ε, hε, fun w hw => ?_⟩
  rw [R.halfPeriodCoordinate_smul a f w, hf2 w hw, smul_zero]

/-- Actual compact smooth mixed (Zaremba) core test fields. -/
def mixedTests (R : PaperHalfPeriodRealization k) :
    Submodule ℂ (PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) where
  carrier := {f | R.IsMixedTest f}
  zero_mem' := R.isMixedTest_zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun a _ hf => hf.smul a

/-- Mixed core tests in the actual geometric rotation character. -/
def mixedCharacterTests (R : PaperHalfPeriodRealization k) (j : ℕ) :=
  R.mixedTests ⊓ R.halfPeriodTestCharacter j

/-- The coordinate of a mixed core test lands in the Zaremba natural disk space `NatCc k true false`
(Neumann on arc 1, Dirichlet on arc 0). -/
lemma mixedTest_to_nat (R : PaperHalfPeriodRealization k)
    {f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ}
    (hf : R.IsMixedTest f) : R.halfPeriodCoordinate f ∈ NatCc k true false := by
  obtain ⟨hsm, harc1, _, hout, hP⟩ := mem_NatCc.mp (R.neumannTest_to_nat hf.1)
  exact mem_NatCc.mpr ⟨hsm, harc1, hf.2, hout, hP⟩

lemma mixedCharacter_coordinate_mem (R : PaperHalfPeriodRealization k) (j : ℕ)
    {f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ}
    (hf : f ∈ R.mixedCharacterTests j) :
    R.halfPeriodCoordinate f ∈ NatCc k true false ⊓ Erot1 k j :=
  ⟨R.mixedTest_to_nat hf.1, R.halfPeriodCoordinate_mem_Erot1 j hf.2⟩

/-- Mixed core realization of a natural Zaremba character test, preserving the exact rotation
character and the coordinate's interior values (hence its form value). -/
lemma exists_mixedTest_character_of_nat (R : PaperHalfPeriodRealization k)
    (j : ℕ) {g : ℂ → ℂ} (hg : g ∈ NatCc k true false)
    (hchar : ∀ z ∈ disk, g (planeRotation (-(2 * Real.pi) / k) z) = zeta k ^ j * g z) :
    ∃ f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ,
      R.IsMixedTest f ∧ EqOn g (R.halfPeriodCoordinate f) disk ∧
      ∀ q, f (R.halfPeriodRotation q) = zeta k ^ j * f q := by
  obtain ⟨G, hG, hsm, he, hB, hP⟩ :=
    exists_closed_representative (by have := h.out; omega : 1 ≤ k) hg
  have hc : ∀ z ∈ disk, G (planeRotation (-(2 * Real.pi) / k) z) = zeta k ^ j * G z := by
    intro z hz
    have hr : planeRotation (-(2 * Real.pi) / k) z ∈ disk := by
      rw [mem_disk_iff, (planeRotation _).norm_map]; exact mem_disk_iff.mp hz
    rw [← he hr, ← he hz]; exact hchar z hz
  have hNeu : R.IsNeumannTest (R.halfPeriodOfCoordinate G) :=
    R.neumannTest_of_closed_representative G hG hsm hB hP
  have heq : EqOn g (R.halfPeriodCoordinate (R.halfPeriodOfCoordinate G)) disk := by
    intro z hz
    exact (he hz).trans (R.halfPeriodCoordinate_ofCoordinate G (mem_disk_iff.mp hz).le
      (punctures_notMem_disk (k := k) (by have := h.out; omega) hz)).symm
  obtain ⟨ε, hε, hg0⟩ := (mem_NatCc.mp hg).2.2.1
  have harc0 : SuppAwaySet (slit k) (R.halfPeriodCoordinate (R.halfPeriodOfCoordinate G)) := by
    refine ⟨ε / 2, by positivity, fun w hw => ?_⟩
    by_cases hn : ‖w‖ ≤ 1 ∧ w ∉ punctures k
    · rw [R.halfPeriodCoordinate_ofCoordinate G hn.1 hn.2]
      exact C1rep_vanishes_near hε hG (fun x hx => he hx) hg0 hn.1 hw
    · unfold halfPeriodCoordinate
      split_ifs
      rfl
  exact ⟨R.halfPeriodOfCoordinate G, ⟨hNeu, harc0⟩, heq,
    R.halfPeriodOfCoordinate_character j G
      (continuous_disk_character_closed _ _ hG hc)⟩

/-- The representative theorem consumes the Zaremba natural-core rotation submodule directly. -/
lemma exists_mixedTest_of_nat_character (R : PaperHalfPeriodRealization k)
    (j : ℕ) {g : ℂ → ℂ} (hg : g ∈ NatCc k true false ⊓ Erot1 k j) :
    ∃ f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ,
      R.IsMixedTest f ∧ EqOn g (R.halfPeriodCoordinate f) disk ∧
      ∀ q, f (R.halfPeriodRotation q) = zeta k ^ j * f q := by
  apply R.exists_mixedTest_character_of_nat j hg.1
  intro z hz
  have he := congrFun (Module.End.mem_eigenspace_iff.mp hg.2) z
  simpa only [KsIndex.SingleDiskBridge.rot1_apply, Pi.smul_apply, smul_eq_mul,
    planeRotation_apply, KsIndex.SurfaceSym.rotUnit, Circle.coe_exp] using he

end KsIndex.KarcherData.PaperHalfPeriodRealization
