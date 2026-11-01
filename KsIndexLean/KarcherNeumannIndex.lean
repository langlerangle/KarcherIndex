module

public import KsIndexLean.KarcherNeumannTestSpace

@[expose] public section


/-! The Morse index of actual compact Neumann character tests equals the
natural disk-core index. Open-disk restriction removes raw boundary freedom. -/
noncomputable section
open Set
open KsIndex.Surface KsIndex.SingleDisk KsIndex.SingleDiskBridge KsIndex.FormIndex
namespace KsIndex

/-- Restriction to the actual open disk. -/
def diskInteriorRestriction : (ℂ → ℂ) →ₗ[ℂ] (disk → ℂ) where
  toFun f z := f z.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Disk form evaluated on the zero extension; exterior and boundary values
are immaterial to the two disk integrals. -/
def diskInteriorJacobiQ (k : ℕ) (u : disk → ℂ) : ℝ :=
  Qd k (zeroExtendSet disk u)

lemma diskInteriorJacobiQ_restrict (k : ℕ) (f : ℂ → ℂ) :
    diskInteriorJacobiQ k (diskInteriorRestriction f) = Qd k f := by
  have he : ∀ z ∈ disk, zeroExtendSet disk (diskInteriorRestriction f) z = f z := by
    intro z hz
    simp [zeroExtendSet,hz,diskInteriorRestriction]
  unfold diskInteriorJacobiQ Qd
  rw [dirichletG_congr_disk he,potentialG_congr_disk he]

lemma diskInteriorJacobiQ_zero (k : ℕ) : diskInteriorJacobiQ k 0 = 0 := by
  have he := diskInteriorJacobiQ_restrict k 0
  rw [map_zero,Qd_zero] at he
  exact he

namespace KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]
open scoped KarcherData.QuotientArea KarcherData.HalfPeriodArea

/-- Index on genuine compact smooth geometric tests in a fixed character. -/
def halfPeriodNeumannIndex (R : PaperHalfPeriodRealization k) (j : ℕ) : ℕ∞ :=
  formIndex R.halfPeriodIntegralJacobiQ (R.neumannCharacterTests j)

/-- Raw natural boundary values contribute no extra negative directions. -/
theorem halfPeriodNeumannIndex_eq_seamNat (R : PaperHalfPeriodRealization k) (j : ℕ) :
    R.halfPeriodNeumannIndex j = seamNat k true true j := by
  let D := NatCc k true true ⊓ Erot1 k j
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
  have hg : formIndex R.halfPeriodIntegralJacobiQ (R.neumannCharacterTests j) =
      formIndex (diskInteriorJacobiQ k) E := by
    apply formIndex_transport_surj R.halfPeriodInteriorLM
    · intro f hf
      exact Submodule.mem_map.mpr
        ⟨R.halfPeriodCoordinate f,R.neumannCharacter_coordinate_mem j hf,rfl⟩
    · intro u hu
      obtain ⟨g,hg,rfl⟩ := Submodule.mem_map.mp hu
      obtain ⟨f,hf,he,hc⟩ := R.exists_neumannTest_of_nat_character j hg
      refine ⟨f,⟨hf,hc⟩,?_⟩
      funext z
      exact (he z.property).symm
    · intro f hf
      exact (R.halfPeriodIntegralJacobiQ_eq f).trans
        (diskInteriorJacobiQ_restrict k (R.halfPeriodCoordinate f)).symm
    · exact diskInteriorJacobiQ_zero k
  exact hg.trans hn.symm

end KarcherData.PaperHalfPeriodRealization
end KsIndex
