module

/-
Jacobi potentials in the end coordinate `ζ ↦ p + ζ^m`.

`generalEndPotential k p m` multiplies the pulled-back potential by the
covering weight `m² · (normSq ζ)^(m−1)`. For `k ≥ 2` it is smooth on all
of `ℂ`, including `ζ = 0`. The value there is zero when `m ≥ 2`; when
`m = 1` and `‖p‖ = 1`, it is `2(k−1)²`.

`endPotential` is the `k = 3` specialization written using the norm. At a
puncture its `m = 1` value is therefore eight. These are coefficients for
the real Laplacian, four times the paper's Wirtinger coefficient `(k−1)²/2`.
-/
public import KsIndexLean.SurfacePotentialFacts

@[expose] public section


noncomputable section
namespace KsIndex.EndChart
open KsIndex.Surface

/-- The flat end-chart potential for arbitrary k, with the covering Jacobian. -/
def generalEndPotential (k : ℕ) (p : ℂ) (m : ℕ) (ζ : ℂ) : ℝ :=
  (m : ℝ) ^ 2 * Complex.normSq ζ ^ (m - 1) * potV k (p + ζ ^ m)

lemma contDiff_generalEndPotential {k : ℕ} (hk : 2 ≤ k) (p : ℂ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (generalEndPotential k p m) :=
  (contDiff_const.mul (contDiff_normSq.pow (m - 1))).mul
    ((contDiff_potV hk).comp (contDiff_const.add (contDiff_id.pow m)))

lemma generalEndPotential_zero_of_two_le (k : ℕ) (p : ℂ) {m : ℕ} (hm : 2 ≤ m) :
    generalEndPotential k p m 0 = 0 := by
  simp [generalEndPotential, zero_pow (by omega : m - 1 ≠ 0)]

/-- The flat Laplacian coefficient is four times the Wirtinger coefficient. -/
lemma generalEndPotential_one_at_zero (k : ℕ) {p : ℂ} (hp : ‖p‖ = 1) :
    generalEndPotential k p 1 0 = 2 * ((k : ℝ) - 1) ^ 2 := by
  simp [generalEndPotential, potV, hp]
  ring

/-- The end-chart transformed potential (div-grad spelling, Jacobian explicit). -/
def endPotential (p : ℂ) (m : ℕ) (ζ : ℂ) : ℝ :=
  (m : ℝ) ^ 2 * ‖ζ‖ ^ (2 * (m - 1)) * potV 3 (p + ζ ^ m)

lemma generalEndPotential_three (p : ℂ) (m : ℕ) :
    generalEndPotential 3 p m = endPotential p m := by
  funext ζ
  simp only [generalEndPotential, endPotential, pow_mul, Complex.sq_norm]

/-- **Smoothness through the puncture:** the
transformed potential is `C^∞` everywhere — the Jacobian's even power is a
`normSq`-polynomial and `potV 3` is globally smooth. -/
lemma contDiff_endPotential (p : ℂ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (endPotential p m) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun ζ : ℂ => ‖ζ‖ ^ (2 * (m - 1)) := by
    have heq : (fun ζ : ℂ => ‖ζ‖ ^ (2 * (m - 1)))
        = fun ζ : ℂ => Complex.normSq ζ ^ (m - 1) := by
      funext ζ
      rw [pow_mul, Complex.sq_norm]
    rw [heq]
    exact contDiff_normSq.pow _
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun ζ : ℂ => potV 3 (p + ζ ^ m) :=
    contDiff_potV_three.comp (contDiff_const.add (contDiff_id.pow m))
  exact (contDiff_const.mul h1).mul h2

/-- The value at the puncture vanishes for `m ≥ 2`. -/
lemma endPotential_zero_of_two_le (p : ℂ) {m : ℕ} (hm : 2 ≤ m) :
    endPotential p m 0 = 0 := by
  unfold endPotential
  rw [norm_zero, zero_pow (by omega : 2 * (m - 1) ≠ 0)]
  ring

/-- Punctures sit on the unit circle. -/
lemma norm_eq_one_of_mem_punctures {p : ℂ} (hp : p ∈ punctures 3) : ‖p‖ = 1 := by
  have h6 : ‖p‖ ^ 6 = 1 := by
    have := congrArg norm hp
    simpa [norm_pow] using this
  nlinarith [norm_nonneg p, sq_nonneg (‖p‖ - 1), sq_nonneg (‖p‖ + 1),
    sq_nonneg (‖p‖ ^ 2 - 1), sq_nonneg (‖p‖ ^ 2 + 1), sq_nonneg (‖p‖ ^ 3 - 1)]

/-- The `m = 1` value at the puncture is `2(3−1)² = 8` — the real-Laplacian
coefficient (the paper's `(k−1)²/2` is the Wirtinger spelling). -/
lemma endPotential_one_at_zero {p : ℂ} (hp : p ∈ punctures 3) :
    endPotential p 1 0 = 8 := by
  unfold endPotential
  have hnorm : ‖p‖ = 1 := norm_eq_one_of_mem_punctures hp
  have hNS : Complex.normSq p = 1 := by
    have := Complex.sq_norm p
    rw [hnorm] at this
    simpa using this.symm
  simp only [Nat.cast_one, one_pow, norm_zero, Nat.sub_self, mul_zero, pow_zero,
    mul_one, one_mul, pow_one, add_zero]
  rw [potV_three_eq, hNS]
  norm_num

end KsIndex.EndChart
