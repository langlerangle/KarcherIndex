module

public import KsIndexLean.KarcherInfinity
public import KsIndexLean.KarcherRealDifferential

@[expose] public section


/-! Normalized primitives of the EW differential across the regular point at infinity.
This module constructs the local immersion. `KarcherInfinityIdentification`
identifies it with the descended integral on the connected punctured overlap,
up to a single constant in the period quotient. -/
noncomputable section
open scoped ContDiff
namespace KsIndex.KarcherData

lemma not_puncture_of_norm_lt_one {k : ℕ} (hk : 2 ≤ k) {v : ℂ}
    (hv : ‖v‖ < 1) : v ∉ Surface.punctures k := by
  intro hp
  rw [puncture_norm hk hp] at hv
  exact (lt_irrefl _ hv)

/-- The real differential in the holomorphic coordinate `v = 1/w`. -/
def infinityRealDifferential (k : ℕ) (v : ℂ) : ℂ →L[ℝ] (ℝ × ℝ × ℝ) :=
  (realCoeffLinear (coeff1 k v)).prod
    ((realCoeffLinear (-coeff2 k v)).prod (realCoeffLinear (-coeff3 k v)))

lemma infinityRealDifferential_metric {k : ℕ} (hk : 2 ≤ k) (v d : ℂ) :
    euclideanSq (infinityRealDifferential k v d) = Surface.rho k v ^ 2 * ‖d‖ ^ 2 := by
  simpa only [euclideanSq, infinityRealDifferential, ewRealDifferential,
    ContinuousLinearMap.prod_apply, realCoeffLinear_apply, mul_neg, Complex.neg_re, neg_sq] using ewRealDifferential_metric hk v d

lemma infinityRealDifferential_injective {k : ℕ} (hk : 2 ≤ k) {v : ℂ}
    (hv : v ∉ Surface.punctures k) : Function.Injective (infinityRealDifferential k v) := by
  intro d e he
  apply ewRealDifferential_injective hk hv
  simpa only [infinityRealDifferential, ewRealDifferential, ContinuousLinearMap.prod_apply,
    realCoeffLinear_apply, mul_neg, Complex.neg_re, Prod.mk.injEq, neg_inj] using he

/-- All three coefficients have normalized holomorphic primitives on the whole unit disk.
The sign changes include the derivative of inversion; zero is not an end puncture. -/
theorem exists_infinity_primitives {k : ℕ} (hk : 2 ≤ k) :
    ∃ F₁ F₂ F₃ : ℂ → ℂ,
      F₁ 0 = 0 ∧ F₂ 0 = 0 ∧ F₃ 0 = 0 ∧
      (∀ v ∈ Metric.ball (0 : ℂ) 1, HasDerivAt F₁ (coeff1 k v) v) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) 1, HasDerivAt F₂ (-coeff2 k v) v) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) 1, HasDerivAt F₃ (-coeff3 k v) v) := by
  have ha : ∀ v ∈ Metric.ball (0 : ℂ) 1, v ∉ Surface.punctures k := by
    intro v hv
    exact not_puncture_of_norm_lt_one hk (by simpa using hv)
  have h₁ : DifferentiableOn ℂ (coeff1 k) (Metric.ball (0 : ℂ) 1) :=
    fun v hv => (differentiableAt_coeff1 (ha v hv)).differentiableWithinAt
  have h₂ : DifferentiableOn ℂ (fun v => -coeff2 k v) (Metric.ball (0 : ℂ) 1) :=
    fun v hv => (differentiableAt_coeff2 (ha v hv)).neg.differentiableWithinAt
  have h₃ : DifferentiableOn ℂ (fun v => -coeff3 k v) (Metric.ball (0 : ℂ) 1) :=
    fun v hv => (differentiableAt_coeff3 (ha v hv)).neg.differentiableWithinAt
  obtain ⟨F₁, hF₁, hd₁⟩ := h₁.isExactOn_ball.with_val_at 0 0
  obtain ⟨F₂, hF₂, hd₂⟩ := h₂.isExactOn_ball.with_val_at 0 0
  obtain ⟨F₃, hF₃, hd₃⟩ := h₃.isExactOn_ball.with_val_at 0 0
  exact ⟨F₁, F₂, F₃, hF₁, hF₂, hF₃, hd₁, hd₂, hd₃⟩

lemma hasFDerivAt_infinity_realPrimitive {k : ℕ} {v : ℂ} {F₁ F₂ F₃ : ℂ → ℂ}
    (h₁ : HasDerivAt F₁ (coeff1 k v) v)
    (h₂ : HasDerivAt F₂ (-coeff2 k v) v)
    (h₃ : HasDerivAt F₃ (-coeff3 k v) v) :
    HasFDerivAt (realPrimitive F₁ F₂ F₃) (infinityRealDifferential k v) v := by
  exact (Complex.reCLM.hasFDerivAt.comp v (h₁.hasFDerivAt.restrictScalars ℝ)).prodMk
    ((Complex.reCLM.hasFDerivAt.comp v (h₂.hasFDerivAt.restrictScalars ℝ)).prodMk
      (Complex.reCLM.hasFDerivAt.comp v (h₃.hasFDerivAt.restrictScalars ℝ)))

/-- Finite-chart primitives pulled back through inversion have exactly this real
differential. This theorem is a differential identity on the overlap; the
identity of integrated maps is supplied by `infinity_primitive_identification`. -/
lemma hasFDerivAt_realPrimitive_chartInversion {k : ℕ} (hk : 2 ≤ k)
    {v : ℂ} (hv : v ≠ 0) {F₁ F₂ F₃ : ℂ → ℂ}
    (h₁ : HasDerivAt F₁ (coeff1 k v⁻¹) v⁻¹)
    (h₂ : HasDerivAt F₂ (coeff2 k v⁻¹) v⁻¹)
    (h₃ : HasDerivAt F₃ (coeff3 k v⁻¹) v⁻¹) :
    HasFDerivAt (fun z => realPrimitive F₁ F₂ F₃ z⁻¹)
      (infinityRealDifferential k v) v := by
  have hi := hasDerivAt_chartInversion hv
  apply hasFDerivAt_infinity_realPrimitive
  · convert h₁.comp v hi using 1 <;> first | rfl | simp only [coeff1_inv_pullback hk hv]
  · convert h₂.comp v hi using 1 <;> first | rfl | simp only [coeff2_inv_pullback hk hv]
  · convert h₃.comp v hi using 1 <;> first | rfl | simp only [coeff3_inv_pullback hk hv]

/-- A smooth normalized immersion across the regular infinity point, on a disk
of radius strictly less than one. No identification with the descended map is
assumed or claimed here. -/
theorem exists_smooth_infinity_primitive {k : ℕ} (hk : 2 ≤ k) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ X : ℂ → ℝ × ℝ × ℝ,
      X 0 = 0 ∧ ContDiffOn ℝ ∞ X (Metric.ball (0 : ℂ) r) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r,
        HasFDerivAt X (infinityRealDifferential k v) v) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, Function.Injective (infinityRealDifferential k v)) := by
  obtain ⟨F₁, F₂, F₃, hF₁, hF₂, hF₃, hd₁, hd₂, hd₃⟩ := exists_infinity_primitives hk
  have hc (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1)) :
      ContDiffOn ℝ ∞ (fun v => (F v).re) (Metric.ball (0 : ℂ) 1) := by
    exact Complex.reCLM.contDiff.comp_contDiffOn
      ((hF.contDiffOn Metric.isOpen_ball).restrict_scalars ℝ)
  have hc₁ := hc F₁ (fun v hv => (hd₁ v hv).differentiableAt.differentiableWithinAt)
  have hc₂ := hc F₂ (fun v hv => (hd₂ v hv).differentiableAt.differentiableWithinAt)
  have hc₃ := hc F₃ (fun v hv => (hd₃ v hv).differentiableAt.differentiableWithinAt)
  have hsub : Metric.ball (0 : ℂ) (1 / 2 : ℝ) ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.ball_subset_ball (by norm_num)
  refine ⟨1 / 2, by norm_num, by norm_num, realPrimitive F₁ F₂ F₃, ?_,
    (hc₁.prodMk (hc₂.prodMk hc₃)).mono hsub, ?_, ?_⟩
  · simp [realPrimitive, hF₁, hF₂, hF₃]
  · intro v hv
    exact hasFDerivAt_infinity_realPrimitive (hd₁ v (hsub hv))
      (hd₂ v (hsub hv)) (hd₃ v (hsub hv))
  · intro v hv
    exact infinityRealDifferential_injective hk
      (not_puncture_of_norm_lt_one hk (by simpa using hsub hv))

end KsIndex.KarcherData
