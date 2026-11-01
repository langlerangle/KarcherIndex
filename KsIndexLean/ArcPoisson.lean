module

/-
# Poisson kernel, separated-support value estimate, and monomial reproduction

`poissonKer r t = (1-r²)/(1-2r cos t+r²)` is nonnegative for `0 ≤ r < 1`.
For `0 < r < 1`, `0 < d ≤ π`, and `cos t ≤ cos d`, its value is bounded by
`(1-r²)/(2r(1-cos d))`.

The normalized Poisson integral `poissonExt` inherits this bound for continuous
boundary data whose nonzero values satisfy the same angular separation from the
evaluation point. The estimate retains the factor `1/(2r)`; on a collar with
radius bounded away from zero it gives smallness proportional to `1-r²`.

The two-sided geometric series gives the Fourier expansion of the kernel.
Integration against a single boundary mode then proves
`poissonExt (exp(iℓ·)) w = ‖w‖^|ℓ| exp(iℓ arg w)` for `‖w‖ < 1`.
-/
public import Mathlib

@[expose] public section


noncomputable section

open Real Set Filter MeasureTheory intervalIntegral Topology

namespace KsIndex.ArcPoisson

/-! ### The Poisson kernel -/

/-- The Poisson kernel `P_r(t) = (1 − r²)/(1 − 2r cos t + r²)`. -/
def poissonKer (r t : ℝ) : ℝ := (1 - r ^ 2) / (1 - 2 * r * Real.cos t + r ^ 2)

/-- The denominator is positive for `0 ≤ r < 1` (it is `(1−r)² + 2r(1−cos t)`). -/
lemma poissonKer_denom_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    0 < 1 - 2 * r * Real.cos t + r ^ 2 := by
  have h1 : 1 - 2 * r * Real.cos t + r ^ 2 = (1 - r) ^ 2 + 2 * r * (1 - Real.cos t) := by ring
  rw [h1]
  have hsq : 0 < (1 - r) ^ 2 := pow_pos (by linarith) 2
  have hother : 0 ≤ 2 * r * (1 - Real.cos t) :=
    mul_nonneg (by linarith) (by linarith [Real.cos_le_one t])
  linarith

lemma cos_lt_one_of_pos_le_pi {d : ℝ} (hd0 : 0 < d) (hdπ : d ≤ π) : Real.cos d < 1 := by
  have h := Real.strictAntiOn_cos (Set.mem_Icc.mpr ⟨le_refl 0, Real.pi_pos.le⟩)
    (Set.mem_Icc.mpr ⟨hd0.le, hdπ⟩) hd0
  rwa [Real.cos_zero] at h

lemma poissonKer_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) : 0 ≤ poissonKer r t := by
  unfold poissonKer
  apply div_nonneg _ (poissonKer_denom_pos hr0 hr1 t).le
  nlinarith [mul_nonneg hr0 hr0]

/-- For `0 < d ≤ π`, `cos t ≤ cos d`, and `0 < r < 1`,
`P_r(t) ≤ (1−r²)/(2r(1−cos d))`. -/
lemma poissonKer_le {r t d : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hd0 : 0 < d) (hdπ : d ≤ π)
    (ht : Real.cos t ≤ Real.cos d) :
    poissonKer r t ≤ (1 - r ^ 2) / (2 * r * (1 - Real.cos d)) := by
  have hcosd : Real.cos d < 1 := cos_lt_one_of_pos_le_pi hd0 hdπ
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have h2r : (0 : ℝ) < 1 + r := by linarith
  have ha : (0 : ℝ) ≤ 1 - r ^ 2 := le_of_lt (by nlinarith [mul_pos h1r h2r])
  have hc : (0 : ℝ) < 2 * r * (1 - Real.cos d) := by
    have : 0 < 1 - Real.cos d := by linarith
    positivity
  have hcb : 2 * r * (1 - Real.cos d) ≤ 1 - 2 * r * Real.cos t + r ^ 2 := by
    have h1 : 1 - 2 * r * Real.cos t + r ^ 2 = (1 - r) ^ 2 + 2 * r * (1 - Real.cos t) := by ring
    rw [h1]
    nlinarith [sq_nonneg (1 - r), mul_le_mul_of_nonneg_left ht (by linarith : (0 : ℝ) ≤ 2 * r)]
  unfold poissonKer
  exact div_le_div_of_nonneg_left ha hc hcb

lemma continuous_poissonKer {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : Continuous (poissonKer r) := by
  unfold poissonKer
  apply Continuous.div continuous_const
  · fun_prop
  · intro t; exact (poissonKer_denom_pos hr0 hr1 t).ne'

/-! ### The Poisson extension and its value bound -/

/-- The Poisson (harmonic) extension of a boundary trace `f` into the disk. -/
def poissonExt (f : ℝ → ℂ) (w : ℂ) : ℂ :=
  (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, (poissonKer ‖w‖ (Complex.arg w - φ) : ℂ) * f φ

/-- For continuous boundary data, `0 < ‖w‖ < 1`, and `0 < d ≤ π`, angular
separation at every nonzero boundary value bounds the extension by
`(2π)⁻¹ (1-‖w‖²)/(2‖w‖(1-cos d))` times the integral of `‖f‖` over one period. -/
theorem norm_poissonExt_le {f : ℝ → ℂ} (hf : Continuous f) {d : ℝ} (hd0 : 0 < d) (hdπ : d ≤ π)
    {w : ℂ} (hw0 : 0 < ‖w‖) (hw1 : ‖w‖ < 1)
    (hmargin : ∀ φ, f φ ≠ 0 → Real.cos (Complex.arg w - φ) ≤ Real.cos d) :
    ‖poissonExt f w‖
      ≤ (2 * π)⁻¹ * ((1 - ‖w‖ ^ 2) / (2 * ‖w‖ * (1 - Real.cos d)))
          * ∫ φ in (0 : ℝ)..2 * π, ‖f φ‖ := by
  set C : ℝ := (1 - ‖w‖ ^ 2) / (2 * ‖w‖ * (1 - Real.cos d)) with hC
  have hcosd : Real.cos d < 1 := cos_lt_one_of_pos_le_pi hd0 hdπ
  have hw1r : (0 : ℝ) < 1 - ‖w‖ := by linarith
  have hw2r : (0 : ℝ) < 1 + ‖w‖ := by linarith
  have hCnn : 0 ≤ C := by
    rw [hC]
    have hnum : (0 : ℝ) ≤ 1 - ‖w‖ ^ 2 := le_of_lt (by nlinarith [mul_pos hw1r hw2r])
    have hden : (0 : ℝ) < 2 * ‖w‖ * (1 - Real.cos d) :=
      mul_pos (mul_pos (by norm_num) hw0) (by linarith)
    exact div_nonneg hnum hden.le
  have hkc : Continuous (fun φ : ℝ => poissonKer ‖w‖ (Complex.arg w - φ)) :=
    (continuous_poissonKer hw0.le hw1).comp (continuous_const.sub continuous_id)
  have hintg : Continuous
      (fun φ : ℝ => (poissonKer ‖w‖ (Complex.arg w - φ) : ℂ) * f φ) :=
    (Complex.continuous_ofReal.comp hkc).mul hf
  have hptbd : ∀ φ, ‖(poissonKer ‖w‖ (Complex.arg w - φ) : ℂ) * f φ‖ ≤ C * ‖f φ‖ := by
    intro φ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (poissonKer_nonneg hw0.le hw1 _)]
    rcases eq_or_ne (f φ) 0 with hf0 | hf0
    · rw [hf0, norm_zero, mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right (poissonKer_le hw0 hw1 hd0 hdπ (hmargin φ hf0)) (norm_nonneg _)
  unfold poissonExt
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ‖∫ φ in (0 : ℝ)..2 * π, (poissonKer ‖w‖ (Complex.arg w - φ) : ℂ) * f φ‖
      ≤ ∫ φ in (0 : ℝ)..2 * π, ‖(poissonKer ‖w‖ (Complex.arg w - φ) : ℂ) * f φ‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by positivity)
    _ ≤ ∫ φ in (0 : ℝ)..2 * π, C * ‖f φ‖ :=
        intervalIntegral.integral_mono_on (by positivity)
          (hintg.norm.intervalIntegrable _ _)
          ((continuous_const.mul hf.norm).intervalIntegrable _ _)
          (fun φ _ => hptbd φ)
    _ = C * ∫ φ in (0 : ℝ)..2 * π, ‖f φ‖ := intervalIntegral.integral_const_mul _ _

/-! ### Mode expansion and monomial reproduction -/

open Complex

/-- Fourier orthogonality on the circle: `∫₀^{2π} e^{i j φ} dφ = 2π·[j=0]`. -/
lemma integral_exp_int_mul (j : ℤ) :
    ∫ φ in (0:ℝ)..2*π, Complex.exp (↑j * ↑φ * I) = if j = 0 then (2*π : ℂ) else 0 := by
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl]
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero]
    rw [intervalIntegral.integral_const, Complex.real_smul]
    push_cast; ring
  · rw [if_neg hj]
    have hc : (↑j : ℂ) * I ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false]
      exact_mod_cast hj
    have hrw : (fun φ : ℝ => Complex.exp (↑j * ↑φ * I))
        = (fun φ : ℝ => Complex.exp ((↑j * I) * ↑φ)) := by
      funext φ; ring_nf
    rw [hrw, integral_exp_mul_complex hc]
    have h2pi : Complex.exp ((↑j * I) * ↑(2*π)) = 1 := by
      rw [show ((↑j:ℂ) * I) * ↑(2*π) = ↑j * (2 * ↑π * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I j
    rw [h2pi]
    simp

/-- The **ℤ two-sided geometric identity**: `∑_{m∈ℤ} r^{|m|} e^{i m t} = P_r(t)`. -/
lemma hasSum_poissonKer {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    HasSum (fun m : ℤ => (r : ℂ) ^ m.natAbs * Complex.exp (↑m * ↑t * I))
      ((poissonKer r t : ℂ)) := by
  set z : ℂ := (r : ℂ) * Complex.exp (↑t * I) with hz_def
  have hznorm : ‖z‖ = r := by
    rw [hz_def, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hr0]
  have hz1 : ‖z‖ < 1 := by rw [hznorm]; exact hr1
  have hzc : (starRingEnd ℂ) z = (r : ℂ) * Complex.exp (-(↑t * I)) := by
    rw [hz_def, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I, mul_neg]
  have hzcnorm : ‖(starRingEnd ℂ) z‖ < 1 := by rw [norm_conj]; exact hz1
  have hpos : ∀ n : ℕ,
      (r : ℂ) ^ ((↑n : ℤ).natAbs) * Complex.exp (↑(↑n : ℤ) * ↑t * I) = z ^ n := by
    intro n
    rw [Int.natAbs_natCast, hz_def, mul_pow, ← Complex.exp_nat_mul]
    congr 2
    push_cast; ring
  have hneg : ∀ n : ℕ,
      (r : ℂ) ^ ((-(↑n + 1) : ℤ).natAbs) * Complex.exp (↑(-(↑n + 1) : ℤ) * ↑t * I)
        = (starRingEnd ℂ) z * ((starRingEnd ℂ) z) ^ n := by
    intro n
    have hna : (-(↑n + 1) : ℤ).natAbs = n + 1 := by
      rw [show (-(↑n + 1) : ℤ) = -(↑(n+1) : ℤ) by push_cast; ring, Int.natAbs_neg,
        Int.natAbs_natCast]
    rw [hna, ← pow_succ', hzc, mul_pow, ← Complex.exp_nat_mul]
    congr 2
    push_cast; ring
  have h1 : HasSum (fun n : ℕ =>
      (r : ℂ) ^ ((↑n : ℤ).natAbs) * Complex.exp (↑(↑n : ℤ) * ↑t * I)) (1 - z)⁻¹ := by
    simpa only [hpos] using hasSum_geometric_of_norm_lt_one hz1
  have h2 : HasSum (fun n : ℕ =>
      (r : ℂ) ^ ((-(↑n + 1) : ℤ).natAbs) * Complex.exp (↑(-(↑n + 1) : ℤ) * ↑t * I))
      ((starRingEnd ℂ) z * (1 - (starRingEnd ℂ) z)⁻¹) := by
    have hg := (hasSum_geometric_of_norm_lt_one hzcnorm).mul_left ((starRingEnd ℂ) z)
    simpa only [hneg] using hg
  have hz1ne : (1 : ℂ) - z ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h] at hz1; simp at hz1
  have hzc1ne : (1 : ℂ) - (starRingEnd ℂ) z ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h] at hzcnorm; simp at hzcnorm
  have hzz : z * (starRingEnd ℂ) z = (r : ℂ) ^ 2 := by
    rw [hzc, hz_def]
    rw [show (r : ℂ) * Complex.exp (↑t * I) * ((r : ℂ) * Complex.exp (-(↑t * I)))
          = (r : ℂ) ^ 2 * (Complex.exp (↑t * I) * Complex.exp (-(↑t * I))) by ring,
        ← Complex.exp_add]
    rw [show (↑t * I) + (-(↑t * I)) = 0 by ring, Complex.exp_zero, mul_one]
  have hsum : z + (starRingEnd ℂ) z = ((2 * r * Real.cos t : ℝ) : ℂ) := by
    rw [Complex.add_conj]
    have hre : z.re = r * Real.cos t := by
      rw [hz_def, Complex.exp_mul_I]
      simp [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
        Complex.I_re, Complex.I_im]
    rw [hre]; push_cast; ring
  have key : (1 - z)⁻¹ + (starRingEnd ℂ) z * (1 - (starRingEnd ℂ) z)⁻¹
      = (1 - z * (starRingEnd ℂ) z) / ((1 - z) * (1 - (starRingEnd ℂ) z)) := by
    field_simp
    ring
  have hden : (1 - z) * (1 - (starRingEnd ℂ) z) = ((1 - 2*r*Real.cos t + r^2 : ℝ) : ℂ) := by
    have he : (1 - z) * (1 - (starRingEnd ℂ) z)
        = 1 - (z + (starRingEnd ℂ) z) + z * (starRingEnd ℂ) z := by ring
    rw [he, hsum, hzz]; push_cast; ring
  have hnum : 1 - z * (starRingEnd ℂ) z = ((1 - r^2 : ℝ) : ℂ) := by
    rw [hzz]; push_cast; ring
  have hval : (1 - z)⁻¹ + (starRingEnd ℂ) z * (1 - (starRingEnd ℂ) z)⁻¹ = (poissonKer r t : ℂ) := by
    rw [key, hnum, hden, ← Complex.ofReal_div]
    simp only [poissonKer]
  rw [← hval]
  exact HasSum.of_nat_of_neg_add_one h1 h2

/-- Two-sided geometric summability of `m ↦ r^{|m|}` for `0 ≤ r < 1`. -/
lemma summable_r_natAbs {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun m : ℤ => r ^ m.natAbs) := by
  have hrnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have ha : HasSum (fun n : ℕ => r ^ ((↑n : ℤ).natAbs)) (1 - r)⁻¹ := by
    simpa only [Int.natAbs_natCast] using hasSum_geometric_of_norm_lt_one hrnorm
  have hb : HasSum (fun n : ℕ => r ^ ((-(↑n + 1) : ℤ).natAbs)) (r * (1 - r)⁻¹) := by
    have hg := (hasSum_geometric_of_norm_lt_one hrnorm).mul_left r
    have hrw : ∀ n : ℕ, r ^ ((-(↑n + 1) : ℤ).natAbs) = r * r ^ n := by
      intro n
      rw [show (-(↑n + 1) : ℤ).natAbs = n + 1 by
        rw [show (-(↑n + 1) : ℤ) = -(↑(n+1) : ℤ) by push_cast; ring, Int.natAbs_neg,
          Int.natAbs_natCast], pow_succ']
    simpa only [hrw] using hg
  exact (HasSum.of_nat_of_neg_add_one (f := fun m : ℤ => r ^ m.natAbs) ha hb).summable

/-- The `m`-th mode of the Poisson kernel integrand against `e^{iℓφ}`. -/
noncomputable def gTerm (r θ : ℝ) (ℓ m : ℤ) (φ : ℝ) : ℂ :=
  (r : ℂ) ^ m.natAbs * Complex.exp (↑m * ↑(θ - φ) * I) * Complex.exp (↑ℓ * ↑φ * I)

lemma continuous_gTerm (r θ : ℝ) (ℓ m : ℤ) : Continuous (gTerm r θ ℓ m) := by
  unfold gTerm
  fun_prop

lemma norm_gTerm {r : ℝ} (hr0 : 0 ≤ r) (θ : ℝ) (ℓ m : ℤ) (φ : ℝ) :
    ‖gTerm r θ ℓ m φ‖ = r ^ m.natAbs := by
  unfold gTerm
  rw [norm_mul, norm_mul]
  have e1 : ‖Complex.exp (↑m * ↑(θ - φ) * I)‖ = 1 := by
    rw [Complex.norm_exp]; simp [Complex.mul_im]
  have e2 : ‖Complex.exp (↑ℓ * ↑φ * I)‖ = 1 := by
    rw [Complex.norm_exp]; simp [Complex.mul_im]
  rw [e1, e2, mul_one, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]

/-- The mode expansion of the kernel integrand: `∑_m gTerm = P_r(θ-φ)·e^{iℓφ}`. -/
lemma hasSum_gTerm {r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ℓ : ℤ) (φ : ℝ) :
    HasSum (fun m : ℤ => gTerm r θ ℓ m φ)
      ((↑(poissonKer r (θ - φ)) : ℂ) * Complex.exp (↑ℓ * ↑φ * I)) := by
  have h := (hasSum_poissonKer hr0 hr1 (θ - φ)).mul_right (Complex.exp (↑ℓ * ↑φ * I))
  simpa only [gTerm] using h

/-- In the open disk, the Poisson extension of `e^{iℓφ}` is `r^{|ℓ|} e^{iℓθ}`. -/
lemma poissonExt_monomial {w : ℂ} (hw1 : ‖w‖ < 1) (ℓ : ℤ) :
    poissonExt (fun φ => Complex.exp (↑ℓ * ↑φ * I)) w
      = ((‖w‖ ^ ℓ.natAbs : ℝ) : ℂ) * Complex.exp (↑ℓ * ↑(Complex.arg w) * I) := by
  unfold poissonExt
  set r := ‖w‖ with hr_def
  set θ := Complex.arg w with hθ_def
  have hr0 : 0 ≤ r := by rw [hr_def]; exact norm_nonneg w
  have hle : (0 : ℝ) ≤ 2 * π := by positivity
  -- the mode-integral value
  have hmode : ∀ m : ℤ, (∫ φ in (0:ℝ)..2*π, gTerm r θ ℓ m φ)
      = (r : ℂ) ^ m.natAbs * Complex.exp (↑m * ↑θ * I) * (if ℓ - m = 0 then (2*π : ℂ) else 0) := by
    intro m
    have hGrw : ∀ φ : ℝ, gTerm r θ ℓ m φ
        = ((r : ℂ) ^ m.natAbs * Complex.exp (↑m * ↑θ * I)) * Complex.exp (↑(ℓ - m) * ↑φ * I) := by
      intro φ
      unfold gTerm
      rw [Complex.ofReal_sub]
      rw [show ((↑m:ℂ) * (↑θ - ↑φ) * I) = (↑m * ↑θ * I) + (-(↑m * ↑φ * I)) by ring, Complex.exp_add]
      rw [show ((↑(ℓ - m):ℂ) * ↑φ * I) = (-(↑m * ↑φ * I)) + (↑ℓ * ↑φ * I) by push_cast; ring,
        Complex.exp_add]
      ring
    simp_rw [hGrw]
    rw [intervalIntegral.integral_const_mul, integral_exp_int_mul]
  -- dominated-convergence interchange
  have hDCT := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc (0:ℝ) (2*π)))
    (F := gTerm r θ ℓ)
    (f := fun φ => (↑(poissonKer r (θ - φ)) : ℂ) * Complex.exp (↑ℓ * ↑φ * I))
    (bound := fun m _ => r ^ m.natAbs)
    (fun m => (continuous_gTerm r θ ℓ m).aestronglyMeasurable)
    (fun m => Filter.Eventually.of_forall (fun φ => le_of_eq (norm_gTerm hr0 θ ℓ m φ)))
    (Filter.Eventually.of_forall (fun _ => summable_r_natAbs hr0 hw1))
    (integrable_const _)
    (Filter.Eventually.of_forall (fun φ => hasSum_gTerm hr0 hw1 ℓ φ))
  -- convert the μ-integrals back to interval integrals
  have hconv : ∀ h : ℝ → ℂ,
      (∫ φ, h φ ∂(volume.restrict (Set.Ioc (0:ℝ) (2*π)))) = ∫ φ in (0:ℝ)..2*π, h φ :=
    fun h => (intervalIntegral.integral_of_le hle).symm
  rw [hconv, show (fun m => ∫ φ, gTerm r θ ℓ m φ ∂(volume.restrict (Set.Ioc (0:ℝ) (2*π))))
      = (fun m => ∫ φ in (0:ℝ)..2*π, gTerm r θ ℓ m φ) from funext (fun m => hconv _)] at hDCT
  simp only [hmode] at hDCT
  -- single-support of the delta family
  have hdelta : HasSum
      (fun m : ℤ => (r : ℂ) ^ m.natAbs * Complex.exp (↑m * ↑θ * I)
        * (if ℓ - m = 0 then (2*π : ℂ) else 0))
      ((r : ℂ) ^ ℓ.natAbs * Complex.exp (↑ℓ * ↑θ * I)
        * (if ℓ - ℓ = 0 then (2*π : ℂ) else 0)) :=
    hasSum_single ℓ (fun m hm => by rw [if_neg (by omega : ℓ - m ≠ 0), mul_zero])
  have hval2 : (∫ φ in (0:ℝ)..2*π, (↑(poissonKer r (θ - φ)) : ℂ) * Complex.exp (↑ℓ * ↑φ * I))
      = (r : ℂ) ^ ℓ.natAbs * Complex.exp (↑ℓ * ↑θ * I) * (2*π : ℂ) := by
    rw [HasSum.unique hDCT hdelta]; simp
  rw [hval2]
  have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Complex.ofReal_pow]
  push_cast
  field_simp

end KsIndex.ArcPoisson
