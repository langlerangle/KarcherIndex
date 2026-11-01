module

public import KsIndexLean.KarcherNeumannIndex
public import KsIndexLean.KarcherDirichletIndex
public import KsIndexLean.NaturalCoreIndexDecomposition

@[expose] public section


/-! Unrestricted half-period indices on actual geometric test domains.
These are defined by the geometric forms, not by character sums. -/
noncomputable section
open Set
open KsIndex.Surface KsIndex.SingleDisk KsIndex.SingleDiskBridge KsIndex.FormIndex
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Compact smooth Neumann tests on the entire geometric half-period. -/
def halfPeriodNeumannTotalIndex (R : PaperHalfPeriodRealization k) : ℕ∞ :=
  formIndex R.halfPeriodIntegralJacobiQ R.neumannTests

/-- Compact smooth Dirichlet tests on the open geometric half-period. -/
def halfPeriodDirichletTotalIndex (R : PaperHalfPeriodRealization k) : ℕ∞ :=
  formIndex R.openHalfPeriodIntegralJacobiQ R.dirichletTests

/-- Natural raw boundary values contribute no additional negative directions. -/
theorem halfPeriodNeumannTotalIndex_eq_diskCore (R : PaperHalfPeriodRealization k) :
    R.halfPeriodNeumannTotalIndex = formIndex (Qd k) (NatCc k true true) := by
  let D := NatCc k true true
  let E := D.map diskInteriorRestriction
  have hn : formIndex (Qd k) D = formIndex (diskInteriorJacobiQ k) E := by
    apply formIndex_transport_surj diskInteriorRestriction
    · intro g hg
      exact Submodule.mem_map.mpr ⟨g,hg,rfl⟩
    · intro u hu
      exact Submodule.mem_map.mp hu
    · intro g hg
      exact (diskInteriorJacobiQ_restrict k g).symm
    · exact diskInteriorJacobiQ_zero k
  have hg : formIndex R.halfPeriodIntegralJacobiQ (R.neumannTests) =
      formIndex (diskInteriorJacobiQ k) E := by
    apply formIndex_transport_surj R.halfPeriodInteriorLM
    · intro f hf
      exact Submodule.mem_map.mpr
        ⟨R.halfPeriodCoordinate f,R.neumannTest_to_nat hf,rfl⟩
    · intro u hu
      obtain ⟨g,hg,rfl⟩ := Submodule.mem_map.mp hu
      obtain ⟨f,hf,he⟩ := R.exists_neumannTest_of_nat hg
      refine ⟨f,hf,?_⟩
      funext z
      exact (he z.property).symm
    · intro f hf
      exact (R.halfPeriodIntegralJacobiQ_eq f).trans
        (diskInteriorJacobiQ_restrict k (R.halfPeriodCoordinate f)).symm
    · exact diskInteriorJacobiQ_zero k
  exact hg.trans hn.symm

/-- Coordinate transport of the unrestricted compact Dirichlet test index. -/
theorem halfPeriodDirichletTotalIndex_eq_diskCore (R : PaperHalfPeriodRealization k) :
    R.halfPeriodDirichletTotalIndex = formIndex (Qd k) (NatCc k false false) := by
  apply formIndex_transport_surj R.openHalfPeriodCoordinateLM
  · intro f hf
    exact hf
  · intro g hg
    let f : R.OpenHalfPeriod → ℂ := fun q => g (R.openDiskHomeomorph q).val
    have he : R.openHalfPeriodCoordinate f = g := R.openHalfPeriodCoordinate_of_nat hg
    refine ⟨f,?_,he⟩
    change R.openHalfPeriodCoordinate f ∈ NatCc k false false
    rw [he]
    exact hg
  · intro f hf
    exact R.openHalfPeriodIntegralJacobiQ_eq f
  · exact Qd_zero k

/-- Unrestricted Neumann half-period index, with no character restriction. -/
theorem halfPeriodNeumannTotalIndex_eq (R : PaperHalfPeriodRealization k) (hk : 3 ≤ k) :
    R.halfPeriodNeumannTotalIndex = (2 * k - 3 : ℕ) := by
  rw [halfPeriodNeumannTotalIndex_eq_diskCore, Trace.natCc_neumann_index hk]

/-- Unrestricted Dirichlet half-period index. -/
theorem halfPeriodDirichletTotalIndex_eq (R : PaperHalfPeriodRealization k) (hk : 3 ≤ k) :
    R.halfPeriodDirichletTotalIndex = 0 := by
  rw [halfPeriodDirichletTotalIndex_eq_diskCore, Trace.natCc_dirichlet_index hk]

end KsIndex.KarcherData.PaperHalfPeriodRealization
