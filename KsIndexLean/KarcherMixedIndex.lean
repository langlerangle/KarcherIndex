module

public import KsIndexLean.KarcherMixedTestSpace
public import KsIndexLean.KarcherNeumannIndex
public import KsIndexLean.HemisphereMixedWeakIndex

@[expose] public section


/-! The Morse index of actual compact mixed (Zaremba) core tests of the
geometric half period equals the natural Zaremba disk-core index `seamNat k true false`, hence the
variational index on the actual single lower hemisphere. This is the index half of the paper's
`DN-form-equiv`; the displayed negative-eigenvalue sum is recovered from this variational index
through the weak-domain spectral identification. -/
noncomputable section
open Set
open KsIndex.Surface KsIndex.SingleDisk KsIndex.SingleDiskBridge KsIndex.FormIndex
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]
open scoped KarcherData.QuotientArea KarcherData.HalfPeriodArea

/-- Index on genuine compact smooth geometric mixed (Zaremba) core tests in a fixed character. -/
def halfPeriodMixedIndex (R : PaperHalfPeriodRealization k) (j : ℕ) : ℕ∞ :=
  formIndex R.halfPeriodIntegralJacobiQ (R.mixedCharacterTests j)

/-- Raw natural boundary values on the free (Neumann) arc contribute no extra negative
directions. -/
theorem halfPeriodMixedIndex_eq_seamNat (R : PaperHalfPeriodRealization k) (j : ℕ) :
    R.halfPeriodMixedIndex j = seamNat k true false j := by
  let D := NatCc k true false ⊓ Erot1 k j
  let E := D.map diskInteriorRestriction
  have hn : formIndex (Qd k) D = formIndex (diskInteriorJacobiQ k) E := by
    apply formIndex_transport_surj diskInteriorRestriction
    · intro g hg
      exact Submodule.mem_map.mpr ⟨g, hg, rfl⟩
    · intro u hu
      exact Submodule.mem_map.mp hu
    · intro g hg
      exact (diskInteriorJacobiQ_restrict k g).symm
    · exact diskInteriorJacobiQ_zero k
  have hg : formIndex R.halfPeriodIntegralJacobiQ (R.mixedCharacterTests j) =
      formIndex (diskInteriorJacobiQ k) E := by
    apply formIndex_transport_surj R.halfPeriodInteriorLM
    · intro f hf
      exact Submodule.mem_map.mpr
        ⟨R.halfPeriodCoordinate f, R.mixedCharacter_coordinate_mem j hf, rfl⟩
    · intro u hu
      obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hu
      obtain ⟨f, hf, he, hc⟩ := R.exists_mixedTest_of_nat_character j hg
      refine ⟨f, ⟨hf, hc⟩, ?_⟩
      funext z
      exact (he z.property).symm
    · intro f hf
      exact (R.halfPeriodIntegralJacobiQ_eq f).trans
        (diskInteriorJacobiQ_restrict k (R.halfPeriodCoordinate f)).symm
    · exact diskInteriorJacobiQ_zero k
  exact hg.trans hn.symm

/-- The compact mixed (Zaremba) core index of the geometric half period
equals the variational index on the actual single lower hemisphere. -/
theorem halfPeriod_mixed_hemisphere_index (R : PaperHalfPeriodRealization k) (j : ℕ) :
    R.halfPeriodMixedIndex j = Spherical.hemisphereMixedWeakIndex k j true false := by
  rw [R.halfPeriodMixedIndex_eq_seamNat,
    Spherical.hemisphereMixedWeakIndex_eq_seamNat h.out]

end KsIndex.KarcherData.PaperHalfPeriodRealization
