module

public import KsIndexLean.SphericalTangentTransition
public import KsIndexLean.PolarJetInverse

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1 KsIndex.Trace

lemma reflectAmbient_involutive (p : Ambient) : reflectAmbient (reflectAmbient p) = p := by
  ext i
  fin_cases i <;> simp [reflectAmbient]

lemma reflectAmbient_inner_left (u v : Ambient) :
    inner ℝ (reflectAmbient u) v = inner ℝ u (reflectAmbient v) := by
  have h := reflectAmbient_inner u (reflectAmbient v)
  simpa only [reflectAmbient_involutive] using h

lemma joinedDiskJet_eq_coordinates (u v : ComplexH1) (c : ℂ) {z : ℂ}
    (hz : z ≠ 0) (hn : ‖z‖ ≤ 1) :
    joinedDiskJet u v c z = Dxy (dxLp u) (dyLp u) z := by
  have he := reconstructedJet_polar_inverse (Dxy (dxLp u) (dyLp u)) hz
  simpa only [joinedDiskJet, reconstructedJet, reconstructedX, reconstructedY,
    joinedDiskRadial, joinedDiskAngular, radialJoin, ite_eq_left hn,
    diskRadialRaw, diskAngularRaw] using he

/-- Pointwise representation of the glued jet off the polar origin and equator. -/
lemma sphereJoinedGradient_represents_joinedJet (u v : ComplexH1) {z : ℂ}
    (hz : z ≠ 0) (hn : ‖z‖ ≠ 1) (w : ℂ) :
    (inner ℝ (sphereJoinedGradient u v (sphereChart z)).1
      (fderiv ℝ stereoPoint z w) : ℂ) +
    Complex.I * (inner ℝ (sphereJoinedGradient u v (sphereChart z)).2
      (fderiv ℝ stereoPoint z w) : ℂ) = joinedDiskJet u v 1 z w := by
  rcases lt_or_gt_of_ne hn with h | h
  · rw [sphereJoinedGradient_north_disk u v (SurfaceForm.mem_disk_iff.mpr h),
      joinedDiskJet_eq_coordinates u v 1 hz h.le]
    exact complexGradientLift_represents z (dxCLM u z) (dyCLM u z) w
  · have hs : KsIndex.Bracket.σ z ≠ 0 := by simp [KsIndex.Bracket.σ, hz]
    have hi : ‖KsIndex.Bracket.σ z‖ < 1 := by
      rw [KsIndex.Bracket.norm_σ]
      exact (inv_lt_one₀ (norm_pos_iff.mpr hz)).mpr h
    have hp : ¬ (sphereChart z).val 2 ≤ 0 := by
      change ¬ stereoPoint z 2 ≤ 0
      rw [stereoPoint_nonpos_iff]
      exact not_le.mpr h
    have he : reflectSphere (sphereChart z) = sphereChart (KsIndex.Bracket.σ z) :=
      southChart_eq_sigma hz
    rw [sphereJoinedGradient, ite_eq_right hp, southWeakGradient, he,
      sphereWeakGradient_pullback]
    simp only [reflectAmbient_inner_left, ← stereoPoint_sigma_tangent hz w]
    have hr := congrArg (fun L : ℂ →L[ℝ] ℂ => L w)
      (joinedDiskJet_reflection v u (by norm_num : (1 : ℂ) ≠ 0) hz hn)
    simp only [inv_one, one_smul, ContinuousLinearMap.comp_apply,
      joinedDiskJet_eq_coordinates v u 1 hs hi.le] at hr
    rw [← hr]
    exact complexGradientLift_represents (KsIndex.Bracket.σ z)
      (dxCLM v (KsIndex.Bracket.σ z)) (dyCLM v (KsIndex.Bracket.σ z)) _

lemma sphereJoinedGradient_represents_joinedJet_ae (u v : ComplexH1) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ w : ℂ,
      (inner ℝ (sphereJoinedGradient u v (sphereChart z)).1
        (fderiv ℝ stereoPoint z w) : ℂ) +
      Complex.I * (inner ℝ (sphereJoinedGradient u v (sphereChart z)).2
        (fderiv ℝ stereoPoint z w) : ℂ) = joinedDiskJet u v 1 z w := by
  filter_upwards [volume.ae_ne (0 : ℂ), ae_norm_ne_one] with z hz hn
  exact sphereJoinedGradient_represents_joinedJet u v hz hn

lemma sphereJoinedGradient_reflect (u v : ComplexH1) (p : Sphere) (hp : p.val 2 ≠ 0) :
    sphereJoinedGradient u v (reflectSphere p) =
      (reflectAmbient (sphereJoinedGradient v u p).1,
        reflectAmbient (sphereJoinedGradient v u p).2) := by
  have he : (reflectSphere p).val 2 = -p.val 2 := rfl
  rcases lt_or_gt_of_ne hp with h | h
  · simp [sphereJoinedGradient, he, h.le, not_le.mpr (neg_pos.mpr h),
      southWeakGradient, reflectSphere_involutive p]
  · simp [sphereJoinedGradient, he, not_le.mpr h, (neg_nonpos.mpr h.le),
      southWeakGradient, reflectAmbient_involutive]

lemma sphereJoinedGradient_south_joinedJet_ae (u v : ComplexH1) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ w : ℂ,
      (inner ℝ (sphereJoinedGradient u v (southChart z)).1
        (fderiv ℝ (fun a => (southChart a).val) z w) : ℂ) +
      Complex.I * (inner ℝ (sphereJoinedGradient u v (southChart z)).2
        (fderiv ℝ (fun a => (southChart a).val) z w) : ℂ) = joinedDiskJet v u 1 z w := by
  filter_upwards [sphereJoinedGradient_represents_joinedJet_ae v u, ae_norm_ne_one]
    with z hz hn
  intro w
  have hp : (sphereChart z).val 2 ≠ 0 := by
    change stereoPoint z 2 ≠ 0
    exact fun h => hn ((stereoPoint_equator_iff z).mp h)
  rw [southChart, sphereJoinedGradient_reflect u v (sphereChart z) hp]
  simpa only [fderiv_southPoint_apply, reflectAmbient_inner] using hz w

/-- With matching traces, the assembled field represents a genuine weak chart derivative. -/
theorem sphereJoinedGradient_north_weak {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (hm : arcTrace A u = arcTrace A v) :
    ∃ J, TauCeti.HasWeakFDerivOn volume (extendedSeamDomain A hA)
      (fun z => sphereJoinedValue u v (sphereChart z)) J ∧
      ∀ᵐ z ∂volume.restrict (extendedSeamDomain A hA : Set ℂ), ∀ w : ℂ,
        (inner ℝ (sphereJoinedGradient u v (sphereChart z)).1
          (fderiv ℝ stereoPoint z w) : ℂ) +
        Complex.I * (inner ℝ (sphereJoinedGradient u v (sphereChart z)).2
          (fderiv ℝ stereoPoint z w) : ℂ) = J z w := by
  refine ⟨joinedDiskJet u v 1, sphereJoinedValue_north_weak hA u v hm, ?_⟩
  exact (sphereJoinedGradient_represents_joinedJet_ae u v).filter_mono
    (ae_mono Measure.restrict_le_self)

theorem sphereJoinedGradient_south_weak {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (hm : arcTrace A u = arcTrace A v) :
    ∃ J, TauCeti.HasWeakFDerivOn volume (extendedSeamDomain A hA)
      (fun z => sphereJoinedValue u v (southChart z)) J ∧
      ∀ᵐ z ∂volume.restrict (extendedSeamDomain A hA : Set ℂ), ∀ w : ℂ,
        (inner ℝ (sphereJoinedGradient u v (southChart z)).1
          (fderiv ℝ (fun a => (southChart a).val) z w) : ℂ) +
        Complex.I * (inner ℝ (sphereJoinedGradient u v (southChart z)).2
          (fderiv ℝ (fun a => (southChart a).val) z w) : ℂ) = J z w := by
  refine ⟨joinedDiskJet v u 1, sphereJoinedValue_south_weak hA u v hm, ?_⟩
  exact (sphereJoinedGradient_south_joinedJet_ae u v).filter_mono
    (ae_mono Measure.restrict_le_self)

end KsIndex.Spherical
