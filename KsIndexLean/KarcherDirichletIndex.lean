module

public import KsIndexLean.KarcherDirichletCharacter
public import KsIndexLean.KarcherHalfPeriodIntegralForm
public import KsIndexLean.KarcherHalfPeriodClassicalInverse
public import KsIndexLean.HemisphereWeakIndex

@[expose] public section


/-! Geometric Dirichlet index on the open half-period. Compactly supported
fields are extended by zero to the closed half-period for area integration. -/
noncomputable section
open Set
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SingleDisk KsIndex.SingleDiskBridge
open KsIndex.FormIndex
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

def openHalfPeriodExtension (R : PaperHalfPeriodRealization k) (f : R.OpenHalfPeriod → ℂ) :=
  R.halfPeriodOfCoordinate (R.openHalfPeriodCoordinate f)

lemma openHalfPeriodExtension_apply (R : PaperHalfPeriodRealization k)
    (f : R.OpenHalfPeriod → ℂ) (q : R.OpenHalfPeriod) :
    R.openHalfPeriodExtension f q.val = f q := by
  have he : (R.openDiskHomeomorph q).val = (R.diskHomeomorph q.val).val.val := by
    simp only [openDiskHomeomorph,Topology.IsEmbedding.toHomeomorphOfSurjective_apply,
      openDiskMap]
  change R.openHalfPeriodCoordinate f (R.diskHomeomorph q.val).val.val = f q
  rw [← he,R.openHalfPeriodCoordinate_apply,Homeomorph.symm_apply_apply]

lemma openHalfPeriodExtension_boundary (R : PaperHalfPeriodRealization k)
    (f : R.OpenHalfPeriod → ℂ)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C)
    (hq : ¬ HeightLift.height q.val + Real.pi ∈ Ioo 0 Real.pi) :
    R.openHalfPeriodExtension f q = 0 := by
  have hz : (R.diskHomeomorph q).val.val ∉ disk := by
    intro hd
    exact hq ((R.diskHomeomorph_interior_iff q).mp (mem_disk_iff.mp hd))
  simp only [openHalfPeriodExtension,halfPeriodOfCoordinate,openHalfPeriodCoordinate,
    zeroExtendSet,dite_eq_right hz]

def openHalfPeriodIntegralJacobiQ (R : PaperHalfPeriodRealization k)
    (f : R.OpenHalfPeriod → ℂ) : ℝ :=
  R.halfPeriodIntegralJacobiQ (R.openHalfPeriodExtension f)

lemma openHalfPeriodIntegralJacobiQ_eq (R : PaperHalfPeriodRealization k)
    (f : R.OpenHalfPeriod → ℂ) :
    R.openHalfPeriodIntegralJacobiQ f = Qd k (R.openHalfPeriodCoordinate f) := by
  rw [openHalfPeriodIntegralJacobiQ,halfPeriodIntegralJacobiQ_eq]
  have he : ∀ z ∈ disk,
      R.halfPeriodCoordinate (R.openHalfPeriodExtension f) z =
        R.openHalfPeriodCoordinate f z := by
    intro z hz
    exact R.halfPeriodCoordinate_ofCoordinate _ (mem_disk_iff.mp hz).le
      (punctures_notMem_disk (k := k) (by have := h.out; omega) hz)
  unfold Qd
  rw [dirichletG_congr_disk he,potentialG_congr_disk he]

def halfPeriodDirichletIndex (R : PaperHalfPeriodRealization k) (j : ℕ) : ℕ∞ :=
  formIndex R.openHalfPeriodIntegralJacobiQ (R.dirichletCharacterTests j)

theorem halfPeriodDirichletIndex_eq_seamNat (R : PaperHalfPeriodRealization k) (j : ℕ) :
    R.halfPeriodDirichletIndex j = seamNat k false false j := by
  apply formIndex_transport_surj R.openHalfPeriodCoordinateLM
  · intro f hf
    exact hf
  · intro g hg
    let f : R.OpenHalfPeriod → ℂ := fun q => g (R.openDiskHomeomorph q).val
    have he : R.openHalfPeriodCoordinate f = g := R.openHalfPeriodCoordinate_of_nat hg.1
    refine ⟨f,?_,he⟩
    change R.openHalfPeriodCoordinate f ∈ NatCc k false false ⊓ Erot1 k j
    rw [he]
    exact hg
  · intro f hf
    exact R.openHalfPeriodIntegralJacobiQ_eq f
  · exact Qd_zero k

theorem halfPeriod_dirichlet_hemisphere_index (R : PaperHalfPeriodRealization k) (j : ℕ) :
    R.halfPeriodDirichletIndex j = Spherical.hemisphereWeakIndex k j false := by
  rw [R.halfPeriodDirichletIndex_eq_seamNat,
    Spherical.hemisphereWeakIndex_eq_seamNat h.out]

end KsIndex.KarcherData.PaperHalfPeriodRealization
