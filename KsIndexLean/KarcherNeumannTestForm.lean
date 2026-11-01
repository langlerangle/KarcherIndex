module

public import KsIndexLean.KarcherHalfPeriodChartForm
public import KsIndexLean.KarcherNeumannCoreCharacter

@[expose] public section


/-! Form-preserving realization of natural Neumann character tests by actual
half-period fields. The form is the immersion chart integral. -/
noncomputable section
open Set
open KsIndex.Surface KsIndex.SingleDisk KsIndex.FormIndex
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Jacobi chart integral of an actual closed-half-period scalar field. -/
def halfPeriodTestJacobiQ (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) : ℝ :=
  R.halfPeriodChartJacobiQ (R.halfPeriodCoordinate f)

lemma halfPeriodTestJacobiQ_eq (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) :
    R.halfPeriodTestJacobiQ f = SingleDiskBridge.Qd k (R.halfPeriodCoordinate f) :=
  R.halfPeriodChartJacobiQ_eq _

/-- The geometric representative retains the original natural test's form
value and exact rotation character, not merely its class in a quotient. -/
theorem exists_neumannTest_character_form (R : PaperHalfPeriodRealization k)
    (j : ℕ) {g : ℂ → ℂ} (hg : g ∈ NatCc k true true ⊓ Erot1 k j) :
    ∃ f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ,
      R.IsNeumannTest f ∧ EqOn g (R.halfPeriodCoordinate f) disk ∧
      (∀ q, f (R.halfPeriodRotation q) = zeta k ^ j * f q) ∧
      R.halfPeriodTestJacobiQ f = SingleDiskBridge.Qd k g := by
  obtain ⟨f,hf,he,hc⟩ := R.exists_neumannTest_of_nat_character j hg
  refine ⟨f,hf,he,hc,?_⟩
  rw [halfPeriodTestJacobiQ_eq,SingleDiskBridge.Qd,
    ← dirichletG_congr_disk (fun z hz => he hz),
    ← potentialG_congr_disk (fun z hz => he hz)]
  rfl

end KsIndex.KarcherData.PaperHalfPeriodRealization
