module

public import KsIndexLean.SphericalSignedForms
public import KsIndexLean.ReflectionCoreTrace

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.SingleDisk

lemma joinedDiskValue_signed_agrees (b : Bool) (u : ComplexH1) (f : ℂ → ℂ)
    (hf : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict disk] f) :
    joinedDiskValue u (sgn b • u) 1 =ᵐ[volume] refl (sgn b) f := by
  have hu := (ae_restrict_iff' disk.isOpen.measurableSet).mp hf
  have hv : (fun z => valueCLM (sgn b • u) z) =ᵐ[volume.restrict disk]
      (fun z => sgn b * valueCLM u z) := by
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul (sgn b) (valueCLM u)] with z hz
    exact hz
  have hs := (ae_restrict_iff' disk.isOpen.measurableSet).mp hv
  filter_upwards [hu, ae_comp_sigma hu, ae_comp_sigma hs, ae_norm_ne_one] with z hz hi hsi hn
  simp only [joinedDiskValue_sigma_formula, one_smul, SingleDisk.refl]
  by_cases h : ‖z‖ ≤ 1
  · simp only [ite_eq_left h]
    exact hz (SurfaceForm.mem_disk_iff.mpr (lt_of_le_of_ne h hn))
  · have hp : 0 < ‖z‖ := lt_trans zero_lt_one (lt_of_not_ge h)
    have hd : Bracket.σ z ∈ disk := by
      apply SurfaceForm.mem_disk_iff.mpr
      rw [Bracket.norm_σ]
      exact (inv_lt_one₀ hp).mpr (lt_of_not_ge h)
    simp only [ite_eq_right h]
    exact (hsi hd).trans (congrArg (fun w : ℂ => sgn b * w) (hi hd))

def reflectionCoreToSignedSphere {k : ℕ} (hk : 1 ≤ k) (b1 b0 : Bool) :
    SingleCc k b1 b0 →ₗ[ℂ] sphericalSignedDomain k b1 b0 :=
  (mixedSignedSphereLinearIsometryEquiv k b1 b0).toLinearEquiv.toLinearMap.comp
    (reflectionCoreToMixed hk b1 b0)

lemma reflectionCoreToSignedSphere_coordinates {k : ℕ} (hk : 1 ≤ k) (b1 b0 : Bool)
    (f : SingleCc k b1 b0) :
    sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
      (reflectionCoreToSignedSphere hk b1 b0 f).val = signedDiskPair b1 (reflectionCoreH1 hk f) :=
  mixedToSignedSphere_coordinates k b1 b0 (reflectionCoreToMixed hk b1 b0 f)

/-- The spherical representative agrees almost everywhere in the plane chart
with the signed smooth reflection formula. -/
lemma reflectionCoreToSignedSphere_chart_ae {k : ℕ} (hk : 1 ≤ k) (b1 b0 : Bool)
    (f : SingleCc k b1 b0) :
    (fun z => sphereChartValue (isOpen_boundaryArc k 1)
      (reflectionCoreToSignedSphere hk b1 b0 f).val (sphereChart z)) =ᵐ[volume]
        refl (sgn b1) f.val := by
  change (fun z => sphereJoinedValue (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
    (reflectionCoreToSignedSphere hk b1 b0 f).val).1
    (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
    (reflectionCoreToSignedSphere hk b1 b0 f).val).2 (sphereChart z)) =ᵐ[_] _
  simp only [reflectionCoreToSignedSphere_coordinates, signedDiskPair, sphereJoinedValue_north]
  exact joinedDiskValue_signed_agrees b1 (reflectionCoreH1 hk f) f.val
    (reflectionCoreH1_value_ae hk f)

lemma reflectionCoreToSignedSphere_form {k : ℕ} (hk : 2 ≤ k) (b1 b0 : Bool)
    (f : SingleCc k b1 b0) :
    sphereChartJacobi (isOpen_boundaryArc k 1) (surfacePotential k)
      (reflectionCoreToSignedSphere (by omega) b1 b0 f).val
      (reflectionCoreToSignedSphere (by omega) b1 b0 f).val =
        2 * (SingleDiskBridge.Qd k f.val : ℂ) := by
  simp only [sphereChartJacobi, reflectionCoreToSignedSphere_coordinates, signedDiskPair,
    weakJacobi_unit_smul (surfacePotential k) (sgn b1) (norm_sgn b1)]
  have hf := reflectionCoreToMixed_form hk b1 b0 f
  change weakJacobi (surfacePotential k) (reflectionCoreH1 (by omega) f)
    (reflectionCoreH1 (by omega) f) = (SingleDiskBridge.Qd k f.val : ℂ) at hf
  rw [hf]
  ring

end KsIndex.Spherical
