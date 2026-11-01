module

public import KsIndexLean.KarcherNormalization

@[expose] public section


/-! Composition and reversing relations of the actual global parameter maps. -/
noncomputable section
open scoped KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData

local instance {k : ℕ} : T2Space (ParameterSphere k) := inferInstanceAs
  (T2Space {p : Spherical.Sphere // p ∉ Spherical.sphereChart '' Surface.punctures k})

lemma phase_add (θ φ : ℝ) : Complex.exp ((θ + φ : ℝ) * Complex.I) =
    Complex.exp (θ * Complex.I) * Complex.exp (φ * Complex.I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]

lemma phase_neg (θ : ℝ) : Complex.exp ((-θ : ℝ) * Complex.I) = (Complex.exp (θ * Complex.I))⁻¹ := by
  rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg]

lemma phase_conjugate (θ : ℝ) : starRingEnd ℂ (Complex.exp (θ * Complex.I)) =
    Complex.exp ((-θ : ℝ) * Complex.I) := by
  rw [← Complex.exp_conj]
  simp

lemma phase_root_add {n : ℕ} {θ φ : ℝ}
    (hθ : Complex.exp (θ * Complex.I) ^ n = 1)
    (hφ : Complex.exp (φ * Complex.I) ^ n = 1) :
    Complex.exp ((θ + φ : ℝ) * Complex.I) ^ n = 1 := by
  rw [phase_add, mul_pow, hθ, hφ, one_mul]

lemma phase_root_neg {n : ℕ} {θ : ℝ} (hθ : Complex.exp (θ * Complex.I) ^ n = 1) :
    Complex.exp ((-θ : ℝ) * Complex.I) ^ n = 1 := by
  rw [phase_neg, inv_pow, hθ, inv_one]

lemma phase_half_root_neg {n : ℕ} {θ : ℝ} (hθ : Complex.exp (θ * Complex.I) ^ n = -1) :
    Complex.exp ((-θ : ℝ) * Complex.I) ^ n = -1 := by
  rw [phase_neg, inv_pow, hθ]
  norm_num

/-- The global rotations compose by adding their parameter angles. -/
theorem parameterRotation_add {k : ℕ} [Fact (2 ≤ k)] (θ φ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ (2 * k) = 1)
    (hφ : Complex.exp (φ * Complex.I) ^ (2 * k) = 1) :
    parameterRotation θ hθ ∘ parameterRotation φ hφ =
      parameterRotation (θ + φ) (phase_root_add hθ hφ) := by
  apply parameter_eq_of_finite_nonzero
    ((continuous_parameterRotation θ hθ).comp (continuous_parameterRotation φ hφ))
    (continuous_parameterRotation _ _)
  intro w _
  simp only [Function.comp_apply]
  erw [parameterRotation_finite, parameterRotation_finite, parameterRotation_finite]
  congr 1
  apply Subtype.ext
  change Complex.exp (θ * Complex.I) * (Complex.exp (φ * Complex.I) * w.val) =
    Complex.exp ((θ + φ : ℝ) * Complex.I) * w.val
  rw [phase_add, mul_assoc]

/-- Rotation commutes with seam reflection globally, including the exchanged poles. -/
theorem parameterRotation_seam_commute {k : ℕ} (hk : 2 ≤ k) (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ (2 * k) = 1) (p : ParameterSphere k) :
    parameterRotation θ hθ (parameterSeamReflection hk p) =
      parameterSeamReflection hk (parameterRotation θ hθ p) :=
  Subtype.ext (Spherical.rotateSphere_reflect θ p.val)

/-- Conjugation reverses the direction of a global rotation. -/
theorem parameterConjugation_rotation {k : ℕ} [Fact (2 ≤ k)] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ (2 * k) = 1) :
    parameterConjugation ∘ parameterRotation θ hθ =
      parameterRotation (-θ) (phase_root_neg hθ) ∘ parameterConjugation := by
  apply parameter_eq_of_finite_nonzero
    ((continuous_parameterConjugation k).comp (continuous_parameterRotation θ hθ))
    ((continuous_parameterRotation _ _).comp (continuous_parameterConjugation k))
  intro w _
  simp only [Function.comp_apply]
  erw [parameterRotation_finite, parameterConjugation_finite,
    parameterConjugation_finite, parameterRotation_finite]
  congr 1
  apply Subtype.ext
  change starRingEnd ℂ (Complex.exp (θ * Complex.I) * w.val) =
    Complex.exp ((-θ : ℝ) * Complex.I) * starRingEnd ℂ w.val
  rw [map_mul, phase_conjugate]

lemma parameterConjugation_seam_commute {k : ℕ} (hk : 2 ≤ k) (p : ParameterSphere k) :
    parameterConjugation (parameterSeamReflection hk p) =
      parameterSeamReflection hk (parameterConjugation p) := by
  apply Subtype.ext
  apply Subtype.ext
  ext i
  fin_cases i <;> rfl

/-- Squaring the screw is the full rotation at twice its parameter angle. -/
theorem parameterScrew_square {k : ℕ} [h : Fact (2 ≤ k)] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = -1) (p : ParameterSphere k) :
    parameterScrew h.out θ hθ (parameterScrew h.out θ hθ p) =
      parameterRotation (θ + θ)
        (phase_root_add (root_double_of_neg_one hθ) (root_double_of_neg_one hθ)) p := by
  unfold parameterScrew
  simp only [Function.comp_apply]
  rw [← parameterRotation_seam_commute,
    parameterSeamReflection_involutive]
  exact congrFun (parameterRotation_add θ θ _ _) p

/-- Conjugation reverses the screw's parameter angle. -/
theorem parameterConjugation_screw {k : ℕ} [h : Fact (2 ≤ k)] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = -1) (p : ParameterSphere k) :
    parameterConjugation (parameterScrew h.out θ hθ p) =
      parameterScrew h.out (-θ) (phase_half_root_neg hθ) (parameterConjugation p) := by
  unfold parameterScrew
  simp only [Function.comp_apply]
  rw [show parameterConjugation (parameterRotation θ _ (parameterSeamReflection h.out p)) =
      parameterRotation (-θ) _ (parameterConjugation (parameterSeamReflection h.out p)) from
    congrFun (parameterConjugation_rotation θ _) (parameterSeamReflection h.out p)]
  rw [parameterConjugation_seam_commute]

lemma parameterRotation_zero {k : ℕ} [Fact (2 ≤ k)]
    (h0 : Complex.exp ((0 : ℝ) * Complex.I) ^ (2 * k) = 1) :
    parameterRotation 0 h0 = id := by
  apply parameter_eq_of_finite_nonzero (continuous_parameterRotation _ _) continuous_id
  intro w _
  rw [parameterRotation_finite]
  change finiteParameter _ = finiteParameter w
  congr 1
  apply Subtype.ext
  simp

/-- Reversing the rotation angle gives its actual global inverse. -/
theorem parameterRotation_neg_cancel {k : ℕ} [Fact (2 ≤ k)] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ (2 * k) = 1) (p : ParameterSphere k) :
    parameterRotation θ hθ (parameterRotation (-θ) (phase_root_neg hθ) p) = p := by
  have he := congrFun (parameterRotation_add (k := k) θ (-θ) hθ (phase_root_neg hθ)) p
  simpa only [add_neg_cancel, parameterRotation_zero, Function.comp_apply, id_eq] using he

/-- Reversing the screw angle gives its actual global inverse, not another
unrelated screw with the same differential. -/
theorem parameterScrew_neg_cancel {k : ℕ} [h : Fact (2 ≤ k)] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = -1) (p : ParameterSphere k) :
    parameterScrew h.out θ hθ
      (parameterScrew h.out (-θ) (phase_half_root_neg hθ) p) = p := by
  unfold parameterScrew
  simp only [Function.comp_apply]
  rw [← parameterRotation_seam_commute, parameterSeamReflection_involutive]
  exact parameterRotation_neg_cancel θ _ p

end KsIndex.KarcherData
