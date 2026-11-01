module

public import KsIndexLean.ComplexAngularTests
public import KsIndexLean.CircleFourierTransport

@[expose] public section


/-! Smooth ambient extensions of every circle Fourier character. -/
noncomputable section
open MeasureTheory ComplexConjugate
open scoped ContDiff
namespace KsIndex.Trace

/-- Negative modes use conjugate polynomials, avoiding a singularity at zero. -/
def fourierAmbient : ℤ → ℂ → ℂ
  | .ofNat m => fun z => z ^ m
  | .negSucc m => fun z => conj z ^ (m + 1)

lemma contDiff_fourierAmbient (n : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (fourierAmbient n) := by
  cases n with
  | ofNat m => exact contDiff_id.pow m
  | negSucc m => exact Complex.conjCLE.contDiff.pow (m + 1)

lemma angular_pow (m : ℕ) (z : ℂ) :
    fderiv ℝ (fun w : ℂ => w ^ m) z (z * Complex.I) =
      (m : ℂ) * Complex.I * z ^ m := by
  rw [fderiv_pow_ring]
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    nsmul_eq_mul, smul_eq_mul]
  cases m with
  | zero => simp
  | succ m => simp only [Nat.add_sub_cancel, pow_succ]; ring

lemma angular_conj_pow (m : ℕ) (z : ℂ) :
    fderiv ℝ (fun w : ℂ => conj w ^ m) z (z * Complex.I) =
      -(m : ℂ) * Complex.I * conj z ^ m := by
  change fderiv ℝ (fun w : ℂ => Complex.conjCLE w ^ m) z (z * Complex.I) = _
  rw [(Complex.conjCLE.hasFDerivAt.pow m).fderiv]
  change (m • conj z ^ (m - 1)) * conj (z * Complex.I) = _
  simp only [map_mul, Complex.conj_I, nsmul_eq_mul]
  cases m with
  | zero => simp
  | succ m => simp only [Nat.add_sub_cancel, pow_succ]; ring

/-- Exact eigen-equation, valid on the whole plane for these ambient extensions. -/
theorem angular_fourierAmbient (n : ℤ) (z : ℂ) :
    fderiv ℝ (fourierAmbient n) z (z * Complex.I) =
      (n : ℂ) * Complex.I * fourierAmbient n z := by
  cases n with
  | ofNat m => exact angular_pow m z
  | negSucc m => simpa only [fourierAmbient, Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
      using angular_conj_pow (m + 1) z

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

lemma fourier_one_circleParam (θ : ℝ) :
    fourier 1 (θ : AddCircle (2 * Real.pi)) = (circleParam θ : ℂ) := by
  rw [fourier_coe_apply, circleParam_coe]
  congr 1
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

lemma fourier_nat_circleParam (m : ℕ) (θ : ℝ) :
    fourier (m : ℤ) (θ : AddCircle (2 * Real.pi)) = (circleParam θ : ℂ) ^ m := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [Nat.cast_add, Nat.cast_one, fourier_add, hm, fourier_one_circleParam, pow_succ]

/-- The smooth ambient tests restrict to the actual Fourier characters. -/
theorem fourierAmbient_circleParam (n : ℤ) (θ : ℝ) :
    fourierAmbient n (circleParam θ) = fourier n (θ : AddCircle (2 * Real.pi)) := by
  cases n with
  | ofNat m => exact (fourier_nat_circleParam m θ).symm
  | negSucc m =>
    change conj (circleParam θ : ℂ) ^ (m + 1) = fourier (-((m + 1 : ℕ) : ℤ)) _
    rw [fourier_neg, fourier_nat_circleParam, map_pow]

end KsIndex.Trace
