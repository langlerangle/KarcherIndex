module

public import KsIndexLean.BoundedSphereChartCover
public import KsIndexLean.ComplementarySeamChart

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

lemma stereoPoint_nonpos_iff (z : ℂ) : stereoPoint z 2 ≤ 0 ↔ ‖z‖ ≤ 1 := by
  have hd : 0 < 1 + ‖z‖ ^ 2 := by positivity
  change (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2) ≤ 0 ↔ ‖z‖ ≤ 1
  rw [div_le_iff₀ hd]
  constructor <;> intro h <;> nlinarith [norm_nonneg z]

/-- A genuine function on the actual sphere, from the two disk representatives. -/
def sphereJoinedValue (u v : ComplexH1) (p : Sphere) : ℂ :=
  if p.val 2 ≤ 0 then valueCLM u (stereoCoord p.val)
  else valueCLM v (stereoCoord (reflectSphere p).val)

lemma sphereJoinedValue_north (u v : ComplexH1) (z : ℂ) :
    sphereJoinedValue u v (sphereChart z) = joinedDiskValue u v 1 z := by
  rw [sphereJoinedValue, joinedDiskValue_sigma_formula]
  change (if stereoPoint z 2 ≤ 0 then valueCLM u (stereoCoord (stereoPoint z))
    else valueCLM v (stereoCoord (southChart z).val)) = _
  simp only [stereoPoint_nonpos_iff, stereoCoord_stereoPoint]
  by_cases h : ‖z‖ ≤ 1
  · simp only [h, ite_true]
  · have hz : z ≠ 0 := by intro hz; simp [hz] at h
    simp only [h, ite_false, stereoCoord_southChart hz, one_smul]

lemma sphereJoinedValue_south (u v : ComplexH1) {z : ℂ} (hn : ‖z‖ ≠ 1) :
    sphereJoinedValue u v (southChart z) = joinedDiskValue v u 1 z := by
  rw [sphereJoinedValue, joinedDiskValue_sigma_formula]
  change (if -stereoPoint z 2 ≤ 0 then valueCLM u (stereoCoord (southChart z).val)
    else valueCLM v (stereoCoord (reflectSphere (reflectSphere (sphereChart z))).val)) = _
  rw [reflectSphere_involutive (sphereChart z)]
  change (if -stereoPoint z 2 ≤ 0 then valueCLM u (stereoCoord (southChart z).val)
    else valueCLM v (stereoCoord (stereoPoint z))) = _
  rw [stereoCoord_stereoPoint]
  rcases lt_or_gt_of_ne hn with h | h
  · have ht : stereoPoint z 2 < 0 := (stereoPoint_lower_iff z).mpr h
    rw [ite_eq_right (by linarith), ite_eq_left h.le]
  · have ht : ¬ stereoPoint z 2 ≤ 0 := by
      rw [stereoPoint_nonpos_iff]
      exact not_le.mpr h
    have hz : z ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one h)
    rw [ite_eq_left (by linarith), ite_eq_right (not_le.mpr h),
      stereoCoord_southChart hz, one_smul]

lemma sphereJoinedValue_south_ae (u v : ComplexH1) :
    (fun z => sphereJoinedValue u v (southChart z)) =ᵐ[volume] joinedDiskValue v u 1 := by
  filter_upwards [ae_norm_ne_one] with z hz
  exact sphereJoinedValue_south u v hz

end KsIndex.Spherical
