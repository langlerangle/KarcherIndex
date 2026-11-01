module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section


/-! Circle Sobolev spaces in weighted Fourier coordinates.
An element stores b_n = (1+|n|)^s a_n in ℓ². The physical Fourier
coefficient is a_n, recovered by division by the strictly positive weight.
This representation includes negative orders and inherits completeness from ℓ².
The squared norm therefore uses weight `(1+|n|)^(2s)`, whereas the paper
uses `(1+n²)^s`. These are equivalent Sobolev norm conventions, not identical
numerical norms. At half order the weights are `1+|n|` and `√(1+n²)`.
-/
noncomputable section
namespace KsIndex.CircleSobolev

/-- The positive Fourier multiplier used to define the Sobolev norm. -/
def weight (s : ℝ) (n : ℤ) : ℝ := (1 + |(n : ℝ)|) ^ s

lemma weight_pos (s : ℝ) (n : ℤ) : 0 < weight s n :=
  Real.rpow_pos_of_pos (by positivity) s

/-- Weighted coordinates for H^s; use `coeff s` to recover Fourier coefficients. -/
abbrev Space (_s : ℝ) := lp (fun _ : ℤ => ℂ) 2

/-- Physical Fourier coefficient, as opposed to the stored weighted coordinate. -/
def coeff (s : ℝ) (u : Space s) (n : ℤ) : ℂ :=
  (weight s n : ℂ)⁻¹ * u n

lemma weight_mul_coeff (s : ℝ) (u : Space s) (n : ℤ) :
    (weight s n : ℂ) * coeff s u n = u n := by
  have hw : (weight s n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos s n).ne'
  simp [coeff, hw]

lemma norm_sq_coordinate (s : ℝ) (u : Space s) (n : ℤ) :
    ‖u n‖ ^ 2 = weight s n ^ 2 * ‖coeff s u n‖ ^ 2 := by
  conv_lhs => rw [← weight_mul_coeff s u n]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos s n), mul_pow]

/-- The squared Hilbert norm is the sum of the weighted squared coefficients. -/
theorem hasSum_weighted_sq (s : ℝ) (u : Space s) :
    HasSum (fun n : ℤ => weight s n ^ 2 * ‖coeff s u n‖ ^ 2) (‖u‖ ^ 2) := by
  have h := lp.hasSum_norm (show (0 : ℝ) < (2 : ENNReal).toReal by norm_num) u
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_sq_coordinate s u] using h

/-- Evaluation of a physical coefficient is complex-linear. -/
def coeffLinear (s : ℝ) (n : ℤ) : Space s →ₗ[ℂ] ℂ where
  toFun u := coeff s u n
  map_add' u v := by simp [coeff, mul_add]
  map_smul' c u := by simp [coeff, mul_left_comm]

/-- Mean zero is a subspace, not a quotient. -/
def dotted (s : ℝ) : Submodule ℂ (Space s) := (coeffLinear s 0).ker

@[simp] lemma mem_dotted (s : ℝ) (u : Space s) :
    u ∈ dotted s ↔ coeff s u 0 = 0 := Iff.rfl

/-- Coefficient support in the paper's congruence class -j+kℤ. -/
def character (s : ℝ) (j k : ℤ) : Submodule ℂ (Space s) :=
  ⨅ (n : ℤ) (_ : ¬ ∃ m : ℤ, n = -j + k * m), (coeffLinear s n).ker

lemma mem_character (s : ℝ) (j k : ℤ) (u : Space s) :
    u ∈ character s j k ↔
      ∀ n : ℤ, (¬ ∃ m : ℤ, n = -j + k * m) → coeff s u n = 0 := by
  simp only [character, Submodule.mem_iInf, LinearMap.mem_ker]
  rfl

/-- The squared weight is the exponent 2s used in the paper. -/
lemma weight_sq (s : ℝ) (n : ℤ) :
    weight s n ^ 2 = (1 + |(n : ℝ)|) ^ (2 * s) := by
  rw [weight, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 1 + |(n : ℝ)|)]
  congr 1
  ring

/-- Every sequence satisfying the weighted square-summability condition is represented. -/
def ofCoefficients (s : ℝ) (a : ℤ → ℂ)
    (ha : Summable (fun n => weight s n ^ 2 * ‖a n‖ ^ 2)) : Space s :=
  ⟨fun n => (weight s n : ℂ) * a n, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos s _), mul_pow] using ha⟩

@[simp] theorem coeff_ofCoefficients (s : ℝ) (a : ℤ → ℂ)
    (ha : Summable (fun n => weight s n ^ 2 * ‖a n‖ ^ 2)) (n : ℤ) :
    coeff s (ofCoefficients s a ha) n = a n := by
  have hw : (weight s n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos s n).ne'
  simp [coeff, ofCoefficients, hw]

theorem coeff_injective (s : ℝ) : Function.Injective (coeff s) := by
  intro u v huv
  apply Subtype.ext
  funext n
  calc u n = (weight s n : ℂ) * coeff s u n := (weight_mul_coeff s u n).symm
       _ = (weight s n : ℂ) * coeff s v n := by rw [huv]
       _ = v n := weight_mul_coeff s v n

/-- Exact membership characterization, including all negative orders. -/
theorem exists_coeff_iff (s : ℝ) (a : ℤ → ℂ) :
    (∃ u : Space s, coeff s u = a) ↔
      Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (2 * s) * ‖a n‖ ^ 2) := by
  constructor
  · rintro ⟨u, rfl⟩
    simpa only [weight_sq] using (hasSum_weighted_sq s u).summable
  · intro ha
    have ha' : Summable (fun n => weight s n ^ 2 * ‖a n‖ ^ 2) := by
      simpa only [weight_sq] using ha
    exact ⟨ofCoefficients s a ha', funext (coeff_ofCoefficients s a ha')⟩

/-- The norm is the square root of the paper's weighted sum. -/
theorem norm_eq_sqrt_tsum (s : ℝ) (u : Space s) :
    ‖u‖ = Real.sqrt (∑' n : ℤ, (1 + |(n : ℝ)|) ^ (2 * s) * ‖coeff s u n‖ ^ 2) := by
  have h := (hasSum_weighted_sq s u).tsum_eq
  simp only [weight_sq] at h
  rw [h, Real.sqrt_sq (norm_nonneg u)]

lemma weight_neg (s : ℝ) (n : ℤ) : weight (-s) n = (weight s n)⁻¹ := by
  exact Real.rpow_neg (by positivity) s

/-- Opposite orders pair by the ordinary inner product of weighted coordinates. -/
def coefficientDuality (s : ℝ) (u : Space (-s)) (v : Space s) : ℂ := inner ℂ u v

lemma coeff_product (s : ℝ) (u : Space (-s)) (v : Space s) (n : ℤ) :
    starRingEnd ℂ (coeff (-s) u n) * coeff s v n =
      starRingEnd ℂ (u n) * v n := by
  have hw : (weight s n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos s n).ne'
  simp only [coeff, weight_neg, Complex.ofReal_inv, inv_inv, map_mul,
    Complex.conj_ofReal]
  field_simp

/-- The Fourier coefficientDuality series converges (not just a totalized tsum). -/
theorem summable_coefficientDuality (s : ℝ) (u : Space (-s)) (v : Space s) :
    Summable (fun n => starRingEnd ℂ (coeff (-s) u n) * coeff s v n) := by
  simp_rw [coeff_product]
  simpa only [RCLike.inner_apply'] using
    (lp.summable_inner (𝕜 := ℂ) u v)

theorem coefficientDuality_eq_tsum (s : ℝ) (u : Space (-s)) (v : Space s) :
    coefficientDuality s u v = ∑' n, starRingEnd ℂ (coeff (-s) u n) * coeff s v n := by
  simp only [coeff_product]
  change (∑' n, inner ℂ (u n) (v n)) = _
  simp only [RCLike.inner_apply']

theorem norm_coefficientDuality_le (s : ℝ) (u : Space (-s)) (v : Space s) :
    ‖coefficientDuality s u v‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v

/-- The bounded pairing, conjugate-linear in its first argument. -/
def coefficientDualityCLM (s : ℝ) : Space (-s) →L⋆[ℂ] Space s →L[ℂ] ℂ := innerSL ℂ

@[simp] theorem coefficientDualityCLM_apply (s : ℝ) (u : Space (-s)) (v : Space s) :
    coefficientDualityCLM s u v = coefficientDuality s u v := rfl

theorem coefficientDuality_smul_left (s : ℝ) (c : ℂ) (u : Space (-s)) (v : Space s) :
    coefficientDuality s (c • u) v = starRingEnd ℂ c * coefficientDuality s u v :=
  inner_smul_left _ _ _

theorem coefficientDuality_smul_right (s : ℝ) (c : ℂ) (u : Space (-s)) (v : Space s) :
    coefficientDuality s u (c • v) = c * coefficientDuality s u v := inner_smul_right _ _ _

/-- Absolute convergence of the Fourier coefficientDuality series. -/
theorem summable_norm_coefficientDuality (s : ℝ) (u : Space (-s)) (v : Space s) :
    Summable (fun n => ‖starRingEnd ℂ (coeff (-s) u n) * coeff s v n‖) :=
  (summable_coefficientDuality s u v).norm

/-- Arclength-normalized duality. The paper uses the unnormalized L² pairing;
its coefficient series therefore carries the factor 2π. Integral agreement
requires the separate L² realization theorem. -/
def duality (s : ℝ) (u : Space (-s)) (v : Space s) : ℂ :=
  (2 * Real.pi : ℂ) * coefficientDuality s u v

theorem duality_eq_tsum (s : ℝ) (u : Space (-s)) (v : Space s) :
    duality s u v = (2 * Real.pi : ℂ) *
      ∑' n, starRingEnd ℂ (coeff (-s) u n) * coeff s v n := by
  rw [duality, coefficientDuality_eq_tsum]

theorem norm_duality_le (s : ℝ) (u : Space (-s)) (v : Space s) :
    ‖duality s u v‖ ≤ (2 * Real.pi) * (‖u‖ * ‖v‖) := by
  rw [duality, norm_mul]
  have hc : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    norm_cast
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc]
  exact mul_le_mul_of_nonneg_left (norm_coefficientDuality_le s u v)
    (by positivity)

lemma weight_mono {s t : ℝ} (h : t ≤ s) (n : ℤ) : weight t n ≤ weight s n :=
  Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (n : ℝ)]) h

lemma norm_reweight_le {s t : ℝ} (h : t ≤ s) (u : Space s) (n : ℤ) :
    ‖(weight t n : ℂ) * coeff s u n‖ ≤ ‖u n‖ := by
  calc
    ‖(weight t n : ℂ) * coeff s u n‖ = weight t n * ‖coeff s u n‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos t n)]
    _ ≤ weight s n * ‖coeff s u n‖ :=
      mul_le_mul_of_nonneg_right (weight_mono h n) (norm_nonneg _)
    _ = ‖u n‖ := by
      rw [← weight_mul_coeff s u n, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (weight_pos s n)]

/-- Natural order inclusion: preserve physical coefficients, reweight coordinates. -/
def inclusion {s t : ℝ} (h : t ≤ s) (u : Space s) : Space t :=
  ⟨fun n => (weight t n : ℂ) * coeff s u n,
    (lp.memℓp u).mono' (norm_reweight_le h u)⟩

@[simp] theorem coeff_inclusion {s t : ℝ} (h : t ≤ s) (u : Space s) (n : ℤ) :
    coeff t (inclusion h u) n = coeff s u n := by
  have hw : (weight t n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos t n).ne'
  simp [coeff, inclusion, hw]

theorem norm_inclusion_le {s t : ℝ} (h : t ≤ s) (u : Space s) :
    ‖inclusion h u‖ ≤ ‖u‖ :=
  lp.norm_mono (by norm_num) (norm_reweight_le h u)

/-- The natural inclusion is a bounded complex-linear map. -/
def inclusionCLM {s t : ℝ} (h : t ≤ s) : Space s →L[ℂ] Space t :=
  LinearMap.mkContinuous
    { toFun := inclusion h
      map_add' := fun u v => by
        apply Subtype.ext
        funext n
        change (weight t n : ℂ) * coeff s (u + v) n =
          (weight t n : ℂ) * coeff s u n + (weight t n : ℂ) * coeff s v n
        simp [coeff, mul_add]
      map_smul' := fun c u => by
        apply Subtype.ext
        funext n
        simp [inclusion, coeff, mul_left_comm, Pi.smul_apply] }
    1 (fun u => by simpa using norm_inclusion_le h u)

theorem inclusion_injective {s t : ℝ} (h : t ≤ s) : Function.Injective (inclusion h) := by
  intro u v huv
  apply coeff_injective s
  funext n
  have hh := congrArg (fun w => coeff t w n) huv
  simpa only [coeff_inclusion] using hh

end KsIndex.CircleSobolev



