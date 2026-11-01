module

public import KsIndexLean.KarcherDirichletCore

@[expose] public section


/-! Compact smooth test fields on the open geometric half-period and their
full linear correspondence with the pure Dirichlet disk core. -/
noncomputable section
open Set Topology
open scoped ContDiff
open KsIndex.Surface KsIndex.SingleDisk
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

def openHalfPeriodCoordinateLM (R : PaperHalfPeriodRealization k) :
    (R.OpenHalfPeriod → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun := R.openHalfPeriodCoordinate
  map_add' f g := by
    funext z
    by_cases hz : z ∈ disk <;> simp [openHalfPeriodCoordinate,zeroExtendSet,hz]
  map_smul' a f := by
    funext z
    by_cases hz : z ∈ disk <;> simp [openHalfPeriodCoordinate,zeroExtendSet,hz]

def dirichletTests (R : PaperHalfPeriodRealization k) :
    Submodule ℂ (R.OpenHalfPeriod → ℂ) :=
  (NatCc k false false).comap R.openHalfPeriodCoordinateLM

lemma mem_dirichletTests (R : PaperHalfPeriodRealization k) (f : R.OpenHalfPeriod → ℂ) :
    f ∈ R.dirichletTests ↔
      HasCompactSupport f ∧ ContDiffOn ℝ ∞ (R.openHalfPeriodCoordinate f) disk :=
  R.openHalfPeriodCoordinate_mem_NatCc_iff f

lemma openHalfPeriodCoordinate_apply (R : PaperHalfPeriodRealization k)
    (f : R.OpenHalfPeriod → ℂ) (z : disk) :
    R.openHalfPeriodCoordinate f z.val = f (R.openDiskHomeomorph.symm z) := by
  simp [openHalfPeriodCoordinate,zeroExtendSet,z.property]

lemma openHalfPeriodCoordinate_injective (R : PaperHalfPeriodRealization k) :
    Function.Injective R.openHalfPeriodCoordinate := by
  intro f g he
  funext q
  have hh := congrFun he (R.openDiskHomeomorph q).val
  simpa only [openHalfPeriodCoordinate_apply,Homeomorph.symm_apply_apply] using hh

lemma openHalfPeriodCoordinate_of_nat (R : PaperHalfPeriodRealization k)
    {g : ℂ → ℂ} (hg : g ∈ NatCc k false false) :
    R.openHalfPeriodCoordinate (fun q => g (R.openDiskHomeomorph q).val) = g := by
  funext z
  by_cases hz : z ∈ disk
  · simp [openHalfPeriodCoordinate,zeroExtendSet,hz]
  · have hg0 : g z = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hz (dd_tsupport_subset_disk hg ht))
    simp [openHalfPeriodCoordinate,zeroExtendSet,hz,hg0]

/-- All compact smooth Dirichlet tests, not just a dense subclass, correspond. -/
def dirichletTestEquiv (R : PaperHalfPeriodRealization k) :
    R.dirichletTests ≃ₗ[ℂ] NatCc k false false where
  toFun f := ⟨R.openHalfPeriodCoordinate f.val,f.property⟩
  invFun g := ⟨fun q => g.val (R.openDiskHomeomorph q).val,by
    change R.openHalfPeriodCoordinate _ ∈ NatCc k false false
    rw [R.openHalfPeriodCoordinate_of_nat g.property]
    exact g.property⟩
  left_inv f := by
    apply Subtype.ext
    funext q
    exact (R.openHalfPeriodCoordinate_apply f.val (R.openDiskHomeomorph q)).trans
      (congrArg f.val (R.openDiskHomeomorph.symm_apply_apply q))
  right_inv g := Subtype.ext (R.openHalfPeriodCoordinate_of_nat g.property)
  map_add' f g := Subtype.ext (R.openHalfPeriodCoordinateLM.map_add f.val g.val)
  map_smul' a f := Subtype.ext (R.openHalfPeriodCoordinateLM.map_smul a f.val)

end KsIndex.KarcherData.PaperHalfPeriodRealization
