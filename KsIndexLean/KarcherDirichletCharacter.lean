module

public import KsIndexLean.KarcherDirichletTestSpace
public import KsIndexLean.KarcherDiskRotation
public import KsIndexLean.SingleDiskBridge

@[expose] public section


/-! Actual rotation characters on compact smooth open-half-period tests. -/
noncomputable section
open Set
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SingleDisk KsIndex.FormIndex
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Restriction of the actual surface rotation to the open height interval. -/
def openHalfPeriodRotation (R : PaperHalfPeriodRealization k) (q : R.OpenHalfPeriod) :
    R.OpenHalfPeriod :=
  ⟨R.halfPeriodRotation q.val,by
    change HeightLift.height (R.rotationLift q.val.val) + Real.pi ∈ Ioo 0 Real.pi
    rw [R.rotationLift_height]
    exact q.property⟩

lemma openHalfPeriodRotation_coordinate (R : PaperHalfPeriodRealization k)
    (q : R.OpenHalfPeriod) :
    (R.openDiskHomeomorph (R.openHalfPeriodRotation q)).val =
      (SurfaceSym.rotUnit k : ℂ) * (R.openDiskHomeomorph q).val := by
  have hh := R.diskRotation_coordinate (R.diskHomeomorph q.val)
  simpa only [diskRotation,Homeomorph.symm_apply_apply,SurfaceSym.rotUnit,
    Circle.coe_exp,neg_mul,openDiskHomeomorph,Topology.IsEmbedding.toHomeomorphOfSurjective_apply,
    openDiskMap,openHalfPeriodRotation] using hh

lemma openHalfPeriodCoordinate_character_iff (R : PaperHalfPeriodRealization k)
    (j : ℕ) (f : R.OpenHalfPeriod → ℂ) :
    R.openHalfPeriodCoordinate f ∈ Erot1 k j ↔
      ∀ q, f (R.openHalfPeriodRotation q) = zeta k ^ j * f q := by
  let a : ℂ := SurfaceSym.rotUnit k
  have ha : ‖a‖ = 1 := Circle.norm_coe _
  have hd (z : ℂ) : a*z ∈ disk ↔ z ∈ disk := by
    simp only [mem_disk_iff,norm_mul,ha,one_mul]
  constructor
  · intro hf q
    have he := congrFun (Module.End.mem_eigenspace_iff.mp hf)
      (R.openDiskHomeomorph q).val
    change R.openHalfPeriodCoordinate f (a*(R.openDiskHomeomorph q).val) =
      zeta k ^ j * R.openHalfPeriodCoordinate f (R.openDiskHomeomorph q).val at he
    rw [← R.openHalfPeriodRotation_coordinate q] at he
    simpa only [openHalfPeriodCoordinate_apply,Homeomorph.symm_apply_apply] using he
  · intro hf
    apply Module.End.mem_eigenspace_iff.mpr
    funext z
    change R.openHalfPeriodCoordinate f (a*z) = zeta k ^ j * R.openHalfPeriodCoordinate f z
    by_cases hz : z ∈ disk
    · let w : disk := ⟨z,hz⟩
      have hr := R.openHalfPeriodRotation_coordinate (R.openDiskHomeomorph.symm w)
      have hr' : (R.openDiskHomeomorph
          (R.openHalfPeriodRotation (R.openDiskHomeomorph.symm w))).val = a*z := by
        simpa only [Homeomorph.apply_symm_apply] using hr
      rw [← hr',R.openHalfPeriodCoordinate_apply,Homeomorph.symm_apply_apply]
      exact (hf _).trans (congrArg (fun v => zeta k ^ j * v)
        (R.openHalfPeriodCoordinate_apply f w).symm)
    · have haz := fun hh => hz ((hd z).mp hh)
      simp only [openHalfPeriodCoordinate,zeroExtendSet,dite_eq_right hz,
        dite_eq_right haz,mul_zero]

/-- Compact smooth Dirichlet tests in the actual geometric rotation class. -/
def dirichletCharacterTests (R : PaperHalfPeriodRealization k) (j : ℕ) :
    Submodule ℂ (R.OpenHalfPeriod → ℂ) :=
  (NatCc k false false ⊓ Erot1 k j).comap R.openHalfPeriodCoordinateLM

lemma mem_dirichletCharacterTests (R : PaperHalfPeriodRealization k) (j : ℕ)
    (f : R.OpenHalfPeriod → ℂ) :
    f ∈ R.dirichletCharacterTests j ↔ f ∈ R.dirichletTests ∧
      ∀ q, f (R.openHalfPeriodRotation q) = zeta k ^ j * f q := by
  change (R.openHalfPeriodCoordinate f ∈ NatCc k false false ∧
    R.openHalfPeriodCoordinate f ∈ Erot1 k j) ↔ _
  rw [R.openHalfPeriodCoordinate_character_iff]
  rfl

end KsIndex.KarcherData.PaperHalfPeriodRealization
