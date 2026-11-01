module

public import KsIndexLean.HemisphereClassicalWeakEigen
public import KsIndexLean.GroundStateInteriorRigidity

@[expose] public section


/-! Pointwise classification of smooth classical Dirichlet Jacobi fields on the
closed lower hemisphere. Vanishing ground-state flux gives interior rigidity;
continuity then extends the classification to the equator. -/
noncomputable section
open Set Filter Topology Metric MeasureTheory
open scoped ContDiff
namespace KsIndex.Spherical
open KsIndex.WeakH1 KsIndex.Trace KsIndex.ModeDiag KsIndex.JacobiMode

/-- Classical zero Dirichlet fields are multiples of the radial mode on the
entire closed coordinate disk, not merely almost everywhere. -/
theorem hemisphere_classical_kernel_chart {k : ℕ} (hk : 2 ≤ k)
    (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p)
    (hb : ∀ p : Sphere, p.val 2 = 0 → f p = 0)
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ),
      sphericalChartJacobiOperator k (f ∘ sphereChart) z = 0) :
    ∃ c : ℂ, ∀ z ∈ closedBall (0 : ℂ) 1, f (sphereChart z) = c * modeU k 0 z := by
  have hw : ∀ v ∈ zeroTraceDomain Set.univ,
      weakJacobi (surfacePotential k) (hemisphereGermH1 f hf) v = 0 := by
    intro v hv
    simpa only [Complex.ofReal_zero, zero_mul] using
      hemisphere_classical_weak_eigen k 0 f hf (by simpa using he) v hv
  have htrace := hemisphereGermH1_zeroTrace f hf hb
  have he0 : (weakJacobi (surfacePotential k) (hemisphereGermH1 f hf)
      (hemisphereGermH1 f hf)).re = 0 := by
    rw [hw _ htrace, Complex.zero_re]
  obtain ⟨c, hopen⟩ := KsIndex.GroundState.radial_ground_smooth_kernel hk
    (hemisphereGermData f hf) htrace he0
  refine ⟨c, ?_⟩
  exact Set.EqOn.of_subset_closure hopen (hemisphere_germs_chart_continuousOn f hf)
    (continuous_const.mul (modeU_contDiff (by omega) 0).continuous).continuousOn
    ball_subset_closedBall (by
      change closedBall (0 : ℂ) 1 ⊆ closure (ball (0 : ℂ) 1)
      rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)])

/-- The pointwise classification in intrinsic spherical coordinates. -/
theorem hemisphere_classical_kernel_span {k : ℕ} (hk : 2 ≤ k)
    (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p)
    (hb : ∀ p : Sphere, p.val 2 = 0 → f p = 0)
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ),
      sphericalChartJacobiOperator k (f ∘ sphereChart) z = 0) :
    ∃ c : ℂ, ∀ p : Sphere, p.val 2 ≤ 0 → f p = c * modeU k 0 (stereoCoord p.val) := by
  obtain ⟨c, hc⟩ := hemisphere_classical_kernel_chart hk f hf hb he
  refine ⟨c, fun p hp => ?_⟩
  have hz : stereoCoord p.val ∈ closedBall (0 : ℂ) 1 := by
    simpa [mem_closedBall, dist_zero_right] using stereoCoord_norm_le_one hp
  have h := hc (stereoCoord p.val) hz
  have hi : sphereChart (stereoCoord p.val) = p :=
    Subtype.ext (stereoPoint_stereoCoord p (by linarith))
  simpa only [hi] using h
/-- A classical zero Dirichlet field is pointwise invariant under every
rotation about the vertical axis on the closed lower hemisphere. -/
theorem hemisphere_classical_kernel_rotation {k : ℕ} (hk : 2 ≤ k)
    (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p)
    (hb : ∀ p : Sphere, p.val 2 = 0 → f p = 0)
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ),
      sphericalChartJacobiOperator k (f ∘ sphereChart) z = 0)
    (θ : ℝ) (p : Sphere) (hp : p.val 2 ≤ 0) : f (rotateSphere θ p) = f p := by
  obtain ⟨c, hc⟩ := hemisphere_classical_kernel_chart hk f hf hb he
  have hz : stereoCoord p.val ∈ closedBall (0 : ℂ) 1 := by
    simpa [mem_closedBall, dist_zero_right] using stereoCoord_norm_le_one hp
  have hr : planeRotation θ (stereoCoord p.val) ∈ closedBall (0 : ℂ) 1 := by
    simpa only [mem_closedBall, dist_zero_right, (planeRotation θ).norm_map] using hz
  have hi : sphereChart (stereoCoord p.val) = p :=
    Subtype.ext (stereoPoint_stereoCoord p (by linarith))
  rw [← hi, rotateSphere_sphereChart, hc _ hr, hc _ hz]
  simp only [modeU, pow_zero, mul_one, (planeRotation θ).norm_map]
/-- The explicit vertical mode has smooth ambient germs at every point of the
closed lower hemisphere. -/
lemma spherical_radial_mode_germs {k : ℕ} (hk : 2 ≤ k) :
    ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm
      (fun q => modeU k 0 (stereoCoord q.val)) p := by
  have hG := modeU_contDiff (by omega : 1 ≤ k) 0
  apply closedHemisphere_smooth_of_coordinate hG.contDiffOn
  intro w _
  exact ⟨_, hG.contDiffAt, Eventually.of_forall (fun _ _ => rfl)⟩

/-- The explicit vertical mode is nonzero in the interior. -/
lemma spherical_radial_mode_nonzero {k : ℕ} (hk : 2 ≤ k) :
    ∃ z ∈ (WeakH1.disk : Set ℂ),
      modeU k 0 (stereoCoord (sphereChart z).val) ≠ 0 := by
  refine ⟨0, by simp [WeakH1.disk], ?_⟩
  rw [show stereoCoord (sphereChart (0 : ℂ)).val = 0 from stereoCoord_stereoPoint 0]
  intro hz
  have hpow : 2 * k - 2 ≠ 0 := by omega
  simp only [modeU, Radial.gRad, CharP.cast_eq_zero, Radial.kap, zero_add, zero_sub,
    neg_sub, norm_zero, ne_eq, hpow, not_false_eq_true, zero_pow, mul_zero, add_zero,
    div_one, Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one,
    pow_zero, mul_one] at hz
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hr := congrArg Complex.re hz
  simp at hr
  linarith

/-- Simplicity of the classical zero kernel, with the scalar determined
uniquely by the function restricted to the closed hemisphere. -/
theorem hemisphere_classical_kernel_unique {k : ℕ} (hk : 2 ≤ k)
    (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p)
    (hb : ∀ p : Sphere, p.val 2 = 0 → f p = 0)
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ),
      sphericalChartJacobiOperator k (f ∘ sphereChart) z = 0) :
    ∃! c : ℂ, ∀ p : Sphere, p.val 2 ≤ 0 → f p = c * modeU k 0 (stereoCoord p.val) := by
  obtain ⟨c, hc⟩ := hemisphere_classical_kernel_span hk f hf hb he
  refine ⟨c, hc, ?_⟩
  intro d hd
  obtain ⟨z, hz, hn⟩ := spherical_radial_mode_nonzero hk
  have hp : (sphereChart z).val 2 ≤ 0 := by
    apply sphereChart_closed_lower
    exact le_of_lt (by simpa [WeakH1.disk, mem_ball, dist_zero_right] using hz)
  exact mul_right_cancel₀ hn ((hd _ hp).symm.trans (hc _ hp))

/-- Classical Dirichlet eigenvalues, defined by the spherical differential
operator and local ambient smoothness up to the equator. Nontriviality is
required on the open hemisphere; values outside the hemisphere are irrelevant. -/
def classicalHemisphereDirichletEigenvalues (k : ℕ) : Set ℝ :=
  {lam | ∃ f : Sphere → ℂ,
    (∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p) ∧
    (∀ p : Sphere, p.val 2 = 0 → f p = 0) ∧
    (∃ z ∈ (WeakH1.disk : Set ℂ), f (sphereChart z) ≠ 0) ∧
    ∀ z ∈ (WeakH1.disk : Set ℂ),
      sphericalChartJacobiOperator k (f ∘ sphereChart) z = -(lam : ℂ) * f (sphereChart z)}

/-- Zero is the least classical Dirichlet eigenvalue. The lower bound uses
the positive-ground-state form argument; the witness is the explicit vertical field. -/
theorem classicalHemisphereDirichlet_zero_isLeast {k : ℕ} (hk : 3 ≤ k) :
    IsLeast (classicalHemisphereDirichletEigenvalues k) 0 := by
  constructor
  · refine ⟨fun p => modeU k 0 (stereoCoord p.val),
      spherical_radial_mode_germs (by omega),
      spherical_radial_mode_equator (by omega),
      spherical_radial_mode_nonzero (by omega), ?_⟩
    intro z hz
    have heq : (fun p : Sphere => modeU k 0 (stereoCoord p.val)) ∘ sphereChart =
        modeU k 0 := by
      funext w
      simp only [Function.comp_apply, sphereChart, stereoCoord_stereoPoint]
    rw [heq, sphericalChartJacobiOperator_mode_zero (by omega), Complex.ofReal_zero,
      neg_zero, zero_mul]
  · rintro lam ⟨f, hf, hb, hne, he⟩
    exact hemisphere_classical_dirichlet_nonnegative hk lam f hf hb hne he
end KsIndex.Spherical
