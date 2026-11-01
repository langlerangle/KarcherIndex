module

public import KsIndexLean.CircleSobolevL2
public import KsIndexLean.SurfaceSym
public import KsIndexLean.BoundaryRotation

@[expose] public section


/-! Fourier response to angular translation, retaining the sign of precomposition. -/
noncomputable section
open MeasureTheory
open scoped Real
namespace KsIndex.Trace
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

lemma fourier_argument_add (n : ℤ) (x a : AddCircle (2 * Real.pi)) :
    fourier n (x + a) = fourier n x * fourier n a := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- Positive angular precomposition multiplies mode n by exp(i n θ). -/
theorem fourierCoeff_translate (f : AddCircle (2 * Real.pi) → ℂ)
    (a : AddCircle (2 * Real.pi)) (n : ℤ) :
    fourierCoeff (fun x => f (x + a)) n = fourier n a * fourierCoeff f n := by
  have hp : fourier n a * fourier (-n) a = 1 := by
    rw [← fourier_add, add_neg_cancel, fourier_zero]
  have he : ∀ x : AddCircle (2 * Real.pi),
      fourier (-n) x * f (x + a) =
        fourier n a * (fourier (-n) (x + a) * f (x + a)) := by
    intro x
    rw [fourier_argument_add]
    calc
      _ = (fourier n a * fourier (-n) a) * (fourier (-n) x * f (x + a)) := by rw [hp, one_mul]
      _ = _ := by ring
  simp only [fourierCoeff, smul_eq_mul]
  simp_rw [he]
  rw [integral_const_mul, integral_add_right_eq_self
    (fun x : AddCircle (2 * Real.pi) => fourier (-n) x * f x) a]

lemma fourierCircleHomeomorph_add (x : AddCircle (2 * Real.pi)) (θ : ℝ) :
    fourierCircleHomeomorph (x + (θ : AddCircle (2 * Real.pi))) =
      circleRotate θ (fourierCircleHomeomorph x) := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    change fourierCircleHomeomorph ((x + θ : ℝ) : AddCircle (2 * Real.pi)) = _
    rw [fourierCircleHomeomorph_coe, fourierCircleHomeomorph_coe,
      circleRotate_circleParam, add_comm x θ]

lemma fourierCoeff_geometric_pullback (f : Circle₁ → ℂ) (n : ℤ) :
    fourierCoeff (fun x => f (fourierCircleHomeomorph x)) n = circleFourierCoeff f n := by
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, circleFourierCoeff,
    fourierCoeffOn_eq_integral]
  simp only [zero_add, sub_zero, fourierCircleHomeomorph_coe]
  simp only [fourier_coe_apply, sub_zero]

/-- Exact Fourier covariance under the existing geometric rotation. -/
theorem circleFourierCoeff_rotate (f : Circle₁ → ℂ) (θ : ℝ) (n : ℤ) :
    circleFourierCoeff (fun w => f (circleRotate θ w)) n =
      fourier n (θ : AddCircle (2 * Real.pi)) * circleFourierCoeff f n := by
  rw [← fourierCoeff_geometric_pullback, ← fourierCoeff_geometric_pullback f]
  have he : (fun x : AddCircle (2 * Real.pi) => f (circleRotate θ (fourierCircleHomeomorph x))) =
      (fun x => f (fourierCircleHomeomorph (x + (θ : AddCircle (2 * Real.pi))))) := by
    funext x
    rw [fourierCircleHomeomorph_add]
  rw [he]
  exact fourierCoeff_translate (fun x => f (fourierCircleHomeomorph x)) _ n

/-- The model's rotUnit uses the negative angle, giving ζ^(-n) on coefficients. -/
lemma fourier_rotUnit_angle (k : ℕ) (hk : 0 < k) (n : ℤ) :
    fourier n ((-(2 * Real.pi) / k : ℝ) : AddCircle (2 * Real.pi)) =
      KsIndex.FormIndex.zeta k ^ (-n) := by
  rw [fourier_coe_apply, KsIndex.FormIndex.zeta, ← Complex.exp_int_mul]
  congr 1
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

lemma circleRotate_rotUnit_coe (k : ℕ) (w : Circle₁) :
    (circleRotate (-(2 * Real.pi) / k) w : ℂ) =
      (KsIndex.SurfaceSym.rotUnit k : ℂ) * (w : ℂ) := rfl

theorem circleFourierCoeff_rotUnit (k : ℕ) (hk : 0 < k) (f : Circle₁ → ℂ) (n : ℤ) :
    circleFourierCoeff (fun w => f (circleRotate (-(2 * Real.pi) / k) w)) n =
      KsIndex.FormIndex.zeta k ^ (-n) * circleFourierCoeff f n := by
  rw [circleFourierCoeff_rotate, fourier_rotUnit_angle k hk]

lemma zeta_neg_eq_iff (k : ℕ) (hk : 0 < k) (j n : ℤ) :
    KsIndex.FormIndex.zeta k ^ (-n) = KsIndex.FormIndex.zeta k ^ j ↔
      ∃ m : ℤ, n = -j + (k : ℤ) * m := by
  have hz : KsIndex.FormIndex.zeta k ≠ 0 := Complex.exp_ne_zero _
  rw [← div_eq_one_iff_eq (zpow_ne_zero j hz), ← zpow_sub₀ hz,
    (KsIndex.FormIndex.zeta_prim hk).zpow_eq_one_iff_dvd]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    nlinarith
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    nlinarith

theorem circleFourierCLE_boundaryRotation (θ : ℝ) (f : Lp ℂ 2 circleMeasure) (n : ℤ) :
    circleFourierCLE (boundaryRotation θ f) n =
      fourier n (θ : AddCircle (2 * Real.pi)) * circleFourierCLE f n := by
  rw [circleFourierCLE_apply, circleFourierCLE_apply]
  rw [congrFun (circleFourierCoeff_congr_ae (boundaryRotation_coe_ae θ f)) n]
  exact circleFourierCoeff_rotate f θ n

/-- The paper's negative congruence class is equivalent to the actual boundary-rotation equation. -/
theorem boundaryRotation_eigen_iff_support (k : ℕ) (hk : 0 < k) (j : ℤ)
    (f : Lp ℂ 2 circleMeasure) :
    boundaryRotation (-(2 * Real.pi) / k) f = KsIndex.FormIndex.zeta k ^ j • f ↔
      ∀ n : ℤ, (¬ ∃ m : ℤ, n = -j + (k : ℤ) * m) → circleFourierCoeff f n = 0 := by
  constructor
  · intro he n hn
    have h := congrArg (fun g : Lp ℂ 2 circleMeasure => circleFourierCLE g n) he
    rw [circleFourierCLE_boundaryRotation, fourier_rotUnit_angle k hk,
      map_smul] at h
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, circleFourierCLE_apply] at h
    have hz : KsIndex.FormIndex.zeta k ^ (-n) ≠ KsIndex.FormIndex.zeta k ^ j :=
      fun hz => hn ((zeta_neg_eq_iff k hk j n).mp hz)
    exact (mul_eq_zero.mp (show (KsIndex.FormIndex.zeta k ^ (-n) -
      KsIndex.FormIndex.zeta k ^ j) * circleFourierCoeff f n = 0 by
      rw [sub_mul, h, sub_self])).resolve_left (sub_ne_zero.mpr hz)
  · intro hf
    apply circleFourierCLE.injective
    apply Subtype.ext
    funext n
    rw [circleFourierCLE_boundaryRotation, fourier_rotUnit_angle k hk, map_smul]
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, circleFourierCLE_apply]
    by_cases hn : ∃ m : ℤ, n = -j + (k : ℤ) * m
    · rw [(zeta_neg_eq_iff k hk j n).mpr hn]
    · rw [hf n hn, mul_zero, mul_zero]

end KsIndex.Trace

namespace KsIndex.CircleSobolev
open KsIndex.Trace

/-- The coefficient character space agrees with geometric rotation on every
nonnegative-order Sobolev realization, including the half-order trace space. -/
theorem mem_character_iff_boundaryRotation {s : ℝ} (hs : 0 ≤ s)
    (k : ℕ) (hk : 0 < k) (j : ℤ) (u : Space s) :
    u ∈ character s j (k : ℤ) ↔
      boundaryRotation (-(2 * Real.pi) / k) (toL2 hs u) =
        KsIndex.FormIndex.zeta k ^ j • toL2 hs u := by
  rw [mem_character, boundaryRotation_eigen_iff_support k hk j]
  simp only [fourierCoeff_toL2]

end KsIndex.CircleSobolev
