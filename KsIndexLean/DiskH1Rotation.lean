module

public import KsIndexLean.DiskTrace
public import KsIndexLean.RotationEnergy

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma disk_eq_rotationAnnulus : disk = rotationAnnulus (-1) 1 := by
  ext z
  change dist z 0 < 1 ↔ -1 < ‖z‖ ∧ ‖z‖ < 1
  rw [dist_zero_right]
  exact ⟨fun h => ⟨by linarith [norm_nonneg z], h⟩, And.right⟩

lemma annulusOpens_eq_rotationAnnulus (a b : ℝ) : annulusOpens a b = rotationAnnulus a b := rfl

lemma measurePreserving_planeRotation_disk (θ : ℝ) :
    MeasurePreserving (planeRotation θ) (volume.restrict (disk : Set ℂ))
      (volume.restrict (disk : Set ℂ)) := by
  rw [disk_eq_rotationAnnulus]
  exact measurePreserving_planeRotation_annulus θ (-1) 1

def diskLpRotation (θ : ℝ) : L2C →ₗᵢ[ℂ] L2C :=
  Lp.compMeasurePreservingₗᵢ ℂ (planeRotation θ) (measurePreserving_planeRotation_disk θ)

lemma diskLpRotation_coe_ae (θ : ℝ) (f : L2C) :
    (diskLpRotation θ f : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f ∘ planeRotation θ :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_planeRotation_disk θ)

lemma rotatedColumn_memLp (θ : ℝ) (u : ComplexH1) (v : ℂ) :
    MemLp (fun z => Dxy (dxLp u) (dyLp u) (planeRotation θ z) (planeRotation θ v))
      2 (volume.restrict (disk : Set ℂ)) := by
  have hm : volume.restrict (rotationAnnulus (-1) 1 : Set ℂ) =
      volume.restrict (disk : Set ℂ) := congrArg (fun Ω : TopologicalSpace.Opens ℂ =>
        volume.restrict (Ω : Set ℂ)) disk_eq_rotationAnnulus.symm
  have hx := (Lp.memLp (dxLp u)).mono_measure hm.le
  have hy := (Lp.memLp (dyLp u)).mono_measure hm.le
  exact (memLp_rotated_derivative θ (-1) 1
    (U := Dxy (dxLp u) (dyLp u)) (by simpa using hx) (by simpa using hy) v).mono_measure hm.ge

def rotatedColumn (θ : ℝ) (u : ComplexH1) (v : ℂ) : L2C :=
  (rotatedColumn_memLp θ u v).toLp _

lemma rotatedColumn_coe_ae (θ : ℝ) (u : ComplexH1) (v : ℂ) :
    (rotatedColumn θ u v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => Dxy (dxLp u) (dyLp u) (planeRotation θ z) (planeRotation θ v)) :=
  MemLp.coeFn_toLp _

lemma rotated_hasJet (θ : ℝ) (u : ComplexH1) :
    HasComplexH1Jet (diskLpRotation θ (valueCLM u))
      (rotatedColumn θ u 1) (rotatedColumn θ u Complex.I) := by
  have hw := carrier_hasJet u
  unfold HasComplexH1Jet at hw ⊢
  have hr := (weakFDeriv_planeRotation θ (-1) 1
    (hw.mono disk_eq_rotationAnnulus.ge)).mono disk_eq_rotationAnnulus.le
  apply (hr.congr_ae (diskLpRotation_coe_ae θ (valueCLM u)).symm).congr_ae_deriv
  filter_upwards [rotatedColumn_coe_ae θ u 1, rotatedColumn_coe_ae θ u Complex.I]
    with z hx hy
  ext v
  rw [Dxy_apply, hx, hy]
  exact realLinear_coordinates
    ((Dxy (dxLp u) (dyLp u) (planeRotation θ z)).comp
      (planeRotation θ).toContinuousLinearEquiv.toContinuousLinearMap) v

def diskH1Rotation (θ : ℝ) (u : ComplexH1) : ComplexH1 :=
  reconstruct (diskLpRotation θ (valueCLM u)) (rotatedColumn θ u 1)
    (rotatedColumn θ u Complex.I) (rotated_hasJet θ u)

lemma diskH1Rotation_value (θ : ℝ) (u : ComplexH1) :
    valueCLM (diskH1Rotation θ u) = diskLpRotation θ (valueCLM u) :=
  reconstruct_value _ _ _ _

lemma diskH1Rotation_coordinates (θ : ℝ) (u : ComplexH1) :
    dxLp (diskH1Rotation θ u) = rotatedColumn θ u 1 ∧
    dyLp (diskH1Rotation θ u) = rotatedColumn θ u Complex.I := by
  apply jet_derivatives_unique (h' := rotated_hasJet θ u)
  rw [← diskH1Rotation_value]
  exact carrier_hasJet _

lemma diskH1Rotation_add (θ : ℝ) (u v : ComplexH1) :
    diskH1Rotation θ (u + v) = diskH1Rotation θ u + diskH1Rotation θ v := by
  apply valueCLM_injective
  simp only [diskH1Rotation_value, map_add]

lemma diskH1Rotation_smul (θ : ℝ) (c : ℂ) (u : ComplexH1) :
    diskH1Rotation θ (c • u) = c • diskH1Rotation θ u := by
  apply valueCLM_injective
  simp only [diskH1Rotation_value, map_smul]

end KsIndex.Trace
