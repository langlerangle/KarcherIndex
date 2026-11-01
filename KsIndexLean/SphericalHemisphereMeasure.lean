module

public import KsIndexLean.SphericalSouthJacobi

@[expose] public section


open Set MeasureTheory
open scoped Pointwise
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1

lemma sphereChart_disk_eq_lower : sphereChart '' (disk : Set ℂ) = {p : Sphere | p.val 2 < 0} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (stereoPoint_lower_iff z).mpr (SurfaceForm.mem_disk_iff.mp hz)
  · intro hp
    have hn : p.val 2 ≠ 1 := by change p.val 2 < 0 at hp; linarith
    obtain ⟨z, rfl⟩ := (Set.ext_iff.mp range_sphereChart p).mpr hn
    exact ⟨z, SurfaceForm.mem_disk_iff.mpr ((stereoPoint_lower_iff z).mp hp), rfl⟩

lemma southChart_disk_eq_upper : southChart '' (disk : Set ℂ) = {p : Sphere | 0 < p.val 2} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    have h := (stereoPoint_lower_iff z).mpr (SurfaceForm.mem_disk_iff.mp hz)
    change 0 < -(stereoPoint z 2)
    linarith
  · intro hp
    have hr : (reflectSphere p).val 2 < 0 := by
      change -p.val 2 < 0
      exact neg_neg_of_pos hp
    obtain ⟨z, hz, he⟩ := (Set.ext_iff.mp sphereChart_disk_eq_lower (reflectSphere p)).mpr hr
    refine ⟨z, hz, ?_⟩
    rw [southChart, he, reflectSphere_involutive p]

lemma measurable_sphere_equator : MeasurableSet {p : Sphere | p.val 2 = 0} := by
  apply isClosed_eq _ continuous_const |>.measurableSet
  fun_prop

lemma sphere_equator_null :
    (volume : Measure Ambient).toSphere {p : Sphere | p.val 2 = 0} = 0 := by
  have hz : (volume : Measure (Fin 3 → ℝ)) {p | p 2 = 0} = 0 :=
    Measure.pi_hyperplane (fun _ => (volume : Measure ℝ)) 2 0
  have hv := volume_preserving_ambient_coordinates.quasiMeasurePreserving.preimage_null hz
  have hn : volume (Set.Ioo (0 : ℝ) 1 •
      (Subtype.val '' {p : Sphere | p.val 2 = 0})) = 0 := by
    apply measure_mono_null _ hv
    rintro x ⟨r, hr, w, ⟨p, hp, rfl⟩, rfl⟩
    change r * p.val 2 = 0
    rw [hp, mul_zero]
  rw [Measure.toSphere_apply' _ measurable_sphere_equator, hn, mul_zero]

lemma canonicalArea_lower_compl :
    (volume : Measure Ambient).toSphere.restrict (sphereChart '' (disk : Set ℂ))ᶜ =
      (volume : Measure Ambient).toSphere.restrict (southChart '' (disk : Set ℂ)) := by
  apply Measure.restrict_congr_set
  have he : ∀ᵐ p ∂(volume : Measure Ambient).toSphere, p.val 2 ≠ 0 := by
    simpa only [ae_iff, not_not] using sphere_equator_null
  rw [sphereChart_disk_eq_lower, southChart_disk_eq_upper]
  filter_upwards [he] with p hp
  apply propext
  simp only [mem_compl_iff, mem_ofPred_eq, not_lt]
  exact ⟨fun h => lt_of_le_of_ne h hp.symm, le_of_lt⟩

end KsIndex.Spherical
