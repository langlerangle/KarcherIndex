module

public import KsIndexLean.KarcherOpenHalfPeriod
public import KsIndexLean.PureDirichletCompactCore

@[expose] public section


/-! Dirichlet compact test fields on the actual open half-period have exactly
the natural disk-core support and smoothness conditions. -/
noncomputable section
open Set Topology
open scoped ContDiff
open KsIndex.Surface
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

def openHalfPeriodCoordinate (R : PaperHalfPeriodRealization k)
    (f : R.OpenHalfPeriod → ℂ) : ℂ → ℂ :=
  zeroExtendSet disk (f ∘ R.openDiskHomeomorph.symm)

lemma openHalfPeriodCoordinate_mem_NatCc_iff (R : PaperHalfPeriodRealization k)
    (f : R.OpenHalfPeriod → ℂ) :
    R.openHalfPeriodCoordinate f ∈ SingleDisk.NatCc k false false ↔
      HasCompactSupport f ∧ ContDiffOn ℝ ∞ (R.openHalfPeriodCoordinate f) disk := by
  have he := SingleDisk.zeroExtendSet_mem_NatCc_DD_iff
    (k := k) (by have := h.out; omega) (f ∘ R.openDiskHomeomorph.symm)
  change _ ↔ _ at he
  rw [show R.openHalfPeriodCoordinate f =
    zeroExtendSet disk (f ∘ R.openDiskHomeomorph.symm) from rfl, he]
  constructor
  · rintro ⟨hf,hsm⟩
    have hh := hf.comp_homeomorph R.openDiskHomeomorph
    have hh' : HasCompactSupport f := by
      simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using hh
    exact ⟨hh',hsm⟩
  · rintro ⟨hf,hsm⟩
    exact ⟨hf.comp_homeomorph R.openDiskHomeomorph.symm,hsm⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
