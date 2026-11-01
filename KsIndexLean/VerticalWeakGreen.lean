module

public import KsIndexLean.NaturalCoreGreenData
public import KsIndexLean.D5DensityAssembly

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The constant one in the actual, unnormalized boundary L2 space. -/
def circleOneL2 : Lp ℂ 2 circleMeasure :=
  (memLp_const (1 : ℂ)).toLp (fun _ : Circle₁ => (1 : ℂ))

lemma circleIntegral_eq_inner_one (f : Lp ℂ 2 circleMeasure) :
    (∫ w, f w ∂circleMeasure) = inner ℂ circleOneL2 f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have ho : (circleOneL2 : Circle₁ → ℂ) =ᵐ[circleMeasure] (fun _ => (1 : ℂ)) :=
    MemLp.coeFn_toLp _
  filter_upwards [ho] with w hw
  simp only [RCLike.inner_apply, hw, map_one, mul_one]

lemma continuous_circleIntegral :
    Continuous (fun f : Lp ℂ 2 circleMeasure => ∫ w, f w ∂circleMeasure) := by
  have he : (fun f : Lp ℂ 2 circleMeasure => ∫ w, f w ∂circleMeasure) =
      (fun f => inner ℂ circleOneL2 f) := funext circleIntegral_eq_inner_one
  rw [he]
  exact continuous_const.inner continuous_id

lemma continuous_weakJacobi_fixed_left (V : BoundedRealPotential) (u : ComplexH1) :
    Continuous (fun v : ComplexH1 => weakJacobi V u v) := by
  have h := (continuous_weakJacobi V).comp
    (Continuous.prodMk_right (Y := ComplexH1) u)
  simpa only [Function.comp_def] using h

/-- The dense natural-core identity extends to every actual mixed-character
weak test. This is a use of density of test functions, not kernel regularity. -/
lemma verticalThree_mixed_weak_green {k : ℕ} (hk : 1 ≤ k) (r : ℕ) (b1 b0 : Bool)
    (v : mixedCharacterDomain k r b1 b0) :
    weakJacobi (surfacePotential 3) verticalThreeH1 v =
      (2 : ℂ) * ∫ w : Circle₁, diskTraceCLM v w ∂circleMeasure := by
  have hc1 : Continuous (fun v : mixedCharacterDomain k r b1 b0 =>
      weakJacobi (surfacePotential 3) verticalThreeH1 v) :=
    (continuous_weakJacobi_fixed_left (surfacePotential 3) verticalThreeH1).comp
      continuous_subtype_val
  have hc2 : Continuous (fun v : mixedCharacterDomain k r b1 b0 =>
      (2 : ℂ) * ∫ w : Circle₁, diskTraceCLM v w ∂circleMeasure) :=
    continuous_const.mul (continuous_circleIntegral.comp
      (diskTraceCLM.continuous.comp continuous_subtype_val))
  have he := (naturalCharacterToMixed_denseRange hk r b1 b0).equalizer hc1 hc2 (by
    funext f
    exact verticalThree_naturalCore_green hk ⟨f.val, f.property.1⟩)
  exact congrFun he v

lemma mem_trivial_NN_sector (v : ComplexH1) : v ∈ mixedCharacterDomain 1 0 true true := by
  constructor
  · simp [mixedTraceDomain_NN]
  · simp only [pow_zero]
    apply weakCharacter_of_value_eq v _ _ (Filter.EventuallyEq.rfl)
    intro z
    rw [one_mul, planeRotation_apply]
    have he : Complex.exp (((-(2 * Real.pi) / ((1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
      have hx : (((-(2 * Real.pi) / ((1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) =
          -(2 * Real.pi * Complex.I) := by push_cast; ring
      rw [hx, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    rw [he, one_mul]

/-- Full unrestricted H1 vertical Green identity. -/
lemma verticalThree_weak_green (v : ComplexH1) :
    weakJacobi (surfacePotential 3) verticalThreeH1 v =
      (2 : ℂ) * ∫ w : Circle₁, diskTraceCLM v w ∂circleMeasure :=
  verticalThree_mixed_weak_green (k := 1) (by decide) 0 true true
    ⟨v, mem_trivial_NN_sector v⟩

/-- The vertical field is genuinely weak-Dirichlet harmonic against every
zero-trace test, not just the smooth core. -/
lemma verticalThree_dirichlet_weak (v : zeroTraceDomain Set.univ) :
    weakJacobi (surfacePotential 3) verticalThreeH1 v = 0 := by
  rw [verticalThree_weak_green]
  have ht := (mem_zeroTraceDomain Set.univ v.val).mp v.property
  rw [Measure.restrict_univ] at ht
  rw [integral_congr_ae ht]
  simp

end KsIndex.Trace
