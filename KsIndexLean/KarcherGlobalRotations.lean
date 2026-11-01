module

public import KsIndexLean.KarcherGlobalReflections
public import KsIndexLean.SphericalRotation

@[expose] public section


/-! Global rotation and screw identities on the actual EW parameter surface. -/
noncomputable section
open scoped KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData

lemma root_rotation_not_puncture {k : ℕ} {a z : ℂ} (ha : a ^ (2 * k) = 1)
    (hz : z ∉ Surface.punctures k) : a * z ∉ Surface.punctures k := by
  intro hp
  apply hz
  simpa only [Surface.punctures, Set.mem_ofPred_eq, mul_pow, ha, one_mul] using hp

/-- Rotation of the sphere restricted to the punctured carrier. -/
def parameterRotation {k : ℕ} (θ : ℝ) (ha : (Complex.exp (θ * Complex.I)) ^ (2 * k) = 1)
    (p : ParameterSphere k) : ParameterSphere k :=
  ⟨Spherical.rotateSphere θ p.val, by
    rcases parameterSphere_cases p with rfl | ⟨w, rfl⟩
    · rintro ⟨z, _, he⟩
      have hh := congrArg (fun q : Spherical.Sphere => q.val 2) he
      rw [Spherical.rotateSphere_height] at hh
      exact Spherical.stereoPoint_third_ne_one z (hh.trans infinitySphereChart_zero_height)
    · rintro ⟨z, hz, he⟩
      have he' : z = Complex.exp (θ * Complex.I) * w.val := by
        apply Spherical.sphereChart_injective
        exact he.trans (Spherical.rotateSphere_sphereChart θ w.val)
      exact root_rotation_not_puncture ha w.property (he' ▸ hz)⟩

lemma continuous_parameterRotation {k : ℕ} (θ : ℝ)
    (ha : (Complex.exp (θ * Complex.I)) ^ (2 * k) = 1) :
    Continuous (parameterRotation θ ha) :=
  (Spherical.continuous_rotateSphere θ |>.comp continuous_subtype_val).subtype_mk _

lemma parameterRotation_finite {k : ℕ} (θ : ℝ)
    (ha : (Complex.exp (θ * Complex.I)) ^ (2 * k) = 1) (w : PuncturedPlane k) :
    parameterRotation θ ha (finiteParameter w) =
      finiteParameter ⟨Complex.exp (θ * Complex.I) * w.val,
        root_rotation_not_puncture ha w.property⟩ :=
  Subtype.ext (Spherical.rotateSphere_sphereChart θ w.val)

lemma parameterRotation_infinity {k : ℕ} (θ : ℝ)
    (ha : (Complex.exp (θ * Complex.I)) ^ (2 * k) = 1) :
    parameterRotation θ ha (infinityParameter k) = infinityParameter k := by
  apply Subtype.ext
  apply north_unique
  exact infinitySphereChart_zero_height

lemma root_double_of_neg_one {k : ℕ} {a : ℂ} (ha : a ^ k = -1) : a ^ (2 * k) = 1 := by
  rw [two_mul, pow_add, ha]
  norm_num

/-- The screw parameter action, rotation after seam reflection; globally defined at both poles. -/
def parameterScrew {k : ℕ} (hk : 2 ≤ k) (θ : ℝ)
    (ha : (Complex.exp (θ * Complex.I)) ^ k = -1) : ParameterSphere k → ParameterSphere k :=
  parameterRotation θ (root_double_of_neg_one ha) ∘ parameterSeamReflection hk

lemma continuous_parameterScrew {k : ℕ} (hk : 2 ≤ k) (θ : ℝ)
    (ha : (Complex.exp (θ * Complex.I)) ^ k = -1) : Continuous (parameterScrew hk θ ha) :=
  (continuous_parameterRotation θ _).comp (continuous_parameterSeamReflection hk)

lemma parameterScrew_finite {k : ℕ} (hk : 2 ≤ k) (θ : ℝ)
    (ha : (Complex.exp (θ * Complex.I)) ^ k = -1) (w : PuncturedPlane k) (hw0 : w.val ≠ 0) :
    parameterScrew hk θ ha (finiteParameter w) =
      finiteParameter ⟨Complex.exp (θ * Complex.I) * (starRingEnd ℂ w.val)⁻¹,
        root_rotation_not_puncture (root_double_of_neg_one ha)
          (inverse_conjugate_not_puncture w.property)⟩ := by
  unfold parameterScrew
  simp only [Function.comp_apply]
  rw [parameterSeamReflection_finite hk w hw0 (inverse_conjugate_not_puncture w.property)]
  exact parameterRotation_finite θ _ _

lemma continuous_periodRotate (a : ℂ) : Continuous (PeriodTarget.rotate a) := by
  unfold PeriodTarget.rotate
  fun_prop

/-- Global rotation identity, including infinity, with its based displacement explicit. -/
theorem extendedEWMap_rotation {k : ℕ} [h : Fact (2 ≤ k)]
    (θ : ℝ) (ha : (Complex.exp (θ * Complex.I)) ^ k = 1)
    (b : PuncturedPlane k) (C : PeriodTarget) (hF : Continuous (extendedEWMap h.out b C)) :
    let ha2 : (Complex.exp (θ * Complex.I)) ^ (2 * k) = 1 := by
      rw [two_mul, pow_add, ha, one_mul]
    ∀ p, extendedEWMap h.out b C (parameterRotation θ ha2 p) =
      descendedIntegral h.out b
        ⟨Complex.exp (θ * Complex.I) * b.val, root_rotation_not_puncture ha2 b.property⟩ +
      PeriodTarget.rotate (Complex.exp (θ * Complex.I)) (extendedEWMap h.out b C p) := by
  have ha2 : (Complex.exp (θ * Complex.I)) ^ (2 * k) = 1 := by
    rw [two_mul, pow_add, ha, one_mul]
  dsimp only
  apply extendedEWMap_affine_equivariance b C _ _ _ hF
    (continuous_parameterRotation θ _) (continuous_periodRotate _)
  intro w _
  rw [parameterRotation_finite]
  erw [extendedEWMap_finite, descendedIntegral_basepoint h.out b
    ⟨Complex.exp (θ * Complex.I) * b.val, root_rotation_not_puncture ha2 b.property⟩]
  rw [descendedIntegral_smul h.out ha]

/-- Global screw identity. Its vertical additive displacement is deliberately not
identified with π by the finite difference identity. -/
theorem extendedEWMap_screw {k : ℕ} [h : Fact (2 ≤ k)]
    (θ : ℝ) (ha : (Complex.exp (θ * Complex.I)) ^ k = -1)
    (b : PuncturedPlane k) (hb0 : b.val ≠ 0) (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out b C)) :
    ∀ p, extendedEWMap h.out b C (parameterScrew h.out θ ha p) =
      descendedIntegral h.out b
        ⟨Complex.exp (θ * Complex.I) * (starRingEnd ℂ b.val)⁻¹,
          root_rotation_not_puncture (root_double_of_neg_one ha)
            (inverse_conjugate_not_puncture b.property)⟩ +
      PeriodTarget.rotate (Complex.exp (θ * Complex.I)) (extendedEWMap h.out b C p) := by
  apply extendedEWMap_of_based_equivariance b hb0 C
    (fun w => ⟨Complex.exp (θ * Complex.I) * (starRingEnd ℂ w.val.val)⁻¹,
      root_rotation_not_puncture (root_double_of_neg_one ha)
        (inverse_conjugate_not_puncture w.val.property)⟩)
    (parameterScrew h.out θ ha) _ hF
    (continuous_parameterScrew h.out θ ha) (continuous_periodRotate _)
  · intro w
    exact parameterScrew_finite h.out θ ha w.val w.property
  · intro w
    exact descendedIntegral_screwMap h.out ha b w.val hb0 w.property _ _

/-- The paper's full rotation angle has the required k-th root identity. -/
lemma paper_rotation_root {k : ℕ} (hk : 2 ≤ k) :
    (Complex.exp ((-2 * Real.pi / k : ℝ) * Complex.I)) ^ k = 1 := by
  rw [← Complex.exp_nat_mul]
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have he : (k : ℂ) * ((-2 * Real.pi / k : ℝ) * Complex.I) =
      -(2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp [hk0]
  rw [he, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

/-- The paper's half-angle parameter has k-th power -1. -/
lemma paper_screw_root {k : ℕ} (hk : 2 ≤ k) :
    (Complex.exp ((-Real.pi / k : ℝ) * Complex.I)) ^ k = -1 := by
  rw [← Complex.exp_nat_mul]
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have he : (k : ℂ) * ((-Real.pi / k : ℝ) * Complex.I) =
      -((Real.pi : ℂ) * Complex.I) := by
    push_cast
    field_simp [hk0]
  rw [he, Complex.exp_neg_pi_mul_I]

lemma parameterScrew_zero {k : ℕ} (hk : 2 ≤ k) (θ : ℝ)
    (ha : (Complex.exp (θ * Complex.I)) ^ k = -1) :
    parameterScrew hk θ ha (finiteParameter ⟨0, zero_not_puncture hk⟩) = infinityParameter k := by
  unfold parameterScrew
  simp only [Function.comp_apply, parameterSeamReflection_zero, parameterRotation_infinity]

lemma parameterScrew_infinity {k : ℕ} (hk : 2 ≤ k) (θ : ℝ)
    (ha : (Complex.exp (θ * Complex.I)) ^ k = -1) :
    parameterScrew hk θ ha (infinityParameter k) =
      finiteParameter ⟨0, zero_not_puncture hk⟩ := by
  unfold parameterScrew
  simp only [Function.comp_apply, parameterSeamReflection_infinity]
  simpa only [mul_zero] using parameterRotation_finite θ (root_double_of_neg_one ha)
    (⟨0, zero_not_puncture hk⟩ : PuncturedPlane k)

end KsIndex.KarcherData
