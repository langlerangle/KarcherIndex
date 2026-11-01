module

public import KsIndexLean.SphericalWeakRotation
public import KsIndexLean.SphericalRotationAE

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

lemma sigma_planeRotation (θ : ℝ) (z : ℂ) :
    Bracket.σ (planeRotation θ z) = planeRotation θ (Bracket.σ z) := by
  have hc := Complex.inv_eq_conj (Complex.norm_exp_ofReal_mul_I θ)
  simp only [Bracket.σ, planeRotation_apply, map_mul, one_div, mul_inv_rev, ← hc,
    inv_inv]
  exact mul_comm _ _

lemma sphereJoinedValue_rotation (θ : ℝ) (u v : ComplexH1) :
    sphereJoinedValue (diskRotation θ u) (diskRotation θ v) =ᵐ[
      (volume : Measure Ambient).toSphere]
      (fun p => sphereJoinedValue u v (rotateSphere θ p)) := by
  apply (sphere_ae_eq_iff_north _ _).mpr
  have hu := (ae_restrict_iff' disk.isOpen.measurableSet).mp (diskRotation_value_ae θ u)
  have hv := (ae_restrict_iff' disk.isOpen.measurableSet).mp (diskRotation_value_ae θ v)
  filter_upwards [hu, ae_comp_sigma hv, ae_norm_ne_one] with z hz hi hn
  simp only [rotateSphere_sphereChart, sphereJoinedValue_north,
    joinedDiskValue_sigma_formula, one_smul, (planeRotation θ).norm_map]
  by_cases h : ‖z‖ ≤ 1
  · have hd : z ∈ disk := SurfaceForm.mem_disk_iff.mpr (lt_of_le_of_ne h hn)
    simp only [ite_eq_left h]
    exact hz hd
  · have hpos : 0 < ‖z‖ := lt_trans zero_lt_one (lt_of_not_ge h)
    have hd : Bracket.σ z ∈ disk := by
      apply SurfaceForm.mem_disk_iff.mpr
      rw [Bracket.norm_σ]
      exact (inv_lt_one₀ hpos).mpr (lt_of_not_ge h)
    simp only [ite_eq_right h, sigma_planeRotation]
    exact hi hd

lemma sphereChartRotation_value_ae {A : Set Circle₁} (hA : IsOpen A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) (q : SphereChartSpace A hA) :
    sphereChartValue hA (sphereChartRotationLI hA θ hθ q) =ᵐ[
      (volume : Measure Ambient).toSphere]
      (fun p => sphereChartValue hA q (rotateSphere θ p)) := by
  change sphereJoinedValue (sphereDiskCoordinatesCLM hA
    (sphereChartRotationLI hA θ hθ q)).1 (sphereDiskCoordinatesCLM hA
    (sphereChartRotationLI hA θ hθ q)).2 =ᵐ[_] _
  rw [sphereChartRotation_coordinates]
  exact sphereJoinedValue_rotation θ _ _

end KsIndex.Spherical
