module

public import KsIndexLean.SphericalH1Comparison
public import KsIndexLean.SphericalSlitPhase
public import Mathlib.Analysis.Normed.Module.TransferInstance

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- The ordinary matching subtype is equivalent to the phase-one transmission kernel. -/
def transmissionMatchingEquiv (A : Set Circle₁) : transmissionDomain A 1 ≃ MatchingDiskPair A where
  toFun p := ⟨p.val, by simpa using (mem_transmissionDomain A 1 p.val).mp p.property⟩
  invFun p := ⟨p.val, (mem_transmissionDomain A 1 p.val).mpr (by simpa using p.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coordinates in the closed disk transmission kernel. -/
def sphereTransmissionEquiv (A : Set Circle₁) (hA : IsOpen A) :
    SphereChartSpace A hA ≃ transmissionDomain A 1 :=
  (matchingDiskPairEquiv A hA).symm.trans (transmissionMatchingEquiv A).symm

instance sphereChartNormedAddCommGroup (A : Set Circle₁) (hA : IsOpen A) :
    NormedAddCommGroup (SphereChartSpace A hA) :=
  (sphereTransmissionEquiv A hA).normedAddCommGroup

instance sphereChartModule (A : Set Circle₁) (hA : IsOpen A) :
    Module ℂ (SphereChartSpace A hA) :=
  (sphereTransmissionEquiv A hA).addEquiv.module ℂ

instance sphereChartNormedSpace (A : Set Circle₁) (hA : IsOpen A) :
    NormedSpace ℂ (SphereChartSpace A hA) :=
  (sphereTransmissionEquiv A hA).addEquiv.normedSpace ℂ

/-- A linear equivalence to the phase-one transmission domain. -/
def sphereTransmissionLinearEquiv (A : Set Circle₁) (hA : IsOpen A) :
    SphereChartSpace A hA ≃ₗ[ℂ] transmissionDomain A 1 :=
  (sphereTransmissionEquiv A hA).addEquiv.linearEquiv ℂ

lemma sphereTransmission_norm (A : Set Circle₁) (hA : IsOpen A) (q : SphereChartSpace A hA) :
    ‖sphereTransmissionLinearEquiv A hA q‖ = ‖q‖ := rfl

/-- The transported norm is the disk product norm, not defined as an area integral. -/
def sphereTransmissionLinearIsometryEquiv (A : Set Circle₁) (hA : IsOpen A) :
    SphereChartSpace A hA ≃ₗᵢ[ℂ] transmissionDomain A 1 where
  toLinearEquiv := sphereTransmissionLinearEquiv A hA
  norm_map' := sphereTransmission_norm A hA

lemma sphereTransmission_matchingPair {A : Set Circle₁} (hA : IsOpen A) (p : MatchingDiskPair A) :
    (sphereTransmissionLinearEquiv A hA (matchingPairClass hA p)).val = p.val := by
  change ((transmissionMatchingEquiv A).symm
    ((matchingDiskPairEquiv A hA).symm (matchingPairClass hA p))).val = p.val
  rw [show matchingPairClass hA p = matchingDiskPairEquiv A hA p from rfl,
    Equiv.symm_apply_apply]
  rfl

lemma sphereChart_norm_matchingPair {A : Set Circle₁} (hA : IsOpen A) (p : MatchingDiskPair A) :
    ‖matchingPairClass hA p‖ = max ‖p.val.1‖ ‖p.val.2‖ := by
  rw [← sphereTransmission_norm A hA]
  change ‖(sphereTransmissionLinearEquiv A hA (matchingPairClass hA p)).val‖ = _
  rw [sphereTransmission_matchingPair]
  rfl

instance sphereChartCompleteSpace (A : Set Circle₁) (hA : IsOpen A) :
    CompleteSpace (SphereChartSpace A hA) := by
  let : CompleteSpace (transmissionDomain A 1) :=
    (isClosed_transmissionDomain A 1).completeSpace_coe
  exact (sphereTransmissionLinearIsometryEquiv A hA).toIsometryEquiv.completeSpace

lemma sphereTransmission_val_chartDiskPair {A : Set Circle₁} (hA : IsOpen A)
    (q : SphereChartSpace A hA) :
    (sphereTransmissionLinearEquiv A hA q).val = (chartDiskPair hA q).val := rfl

lemma chartDiskPair_val_add {A : Set Circle₁} (hA : IsOpen A) (q r : SphereChartSpace A hA) :
    (chartDiskPair hA (q + r)).val = (chartDiskPair hA q).val + (chartDiskPair hA r).val := by
  have h := congrArg Subtype.val ((sphereTransmissionLinearEquiv A hA).map_add q r)
  simpa only [sphereTransmission_val_chartDiskPair, Submodule.coe_add] using h

lemma chartDiskPair_val_smul {A : Set Circle₁} (hA : IsOpen A) (c : ℂ)
    (q : SphereChartSpace A hA) :
    (chartDiskPair hA (c • q)).val = c • (chartDiskPair hA q).val := by
  have h := congrArg Subtype.val ((sphereTransmissionLinearEquiv A hA).map_smul c q)
  simpa only [sphereTransmission_val_chartDiskPair, Submodule.coe_smul] using h

end KsIndex.Spherical
