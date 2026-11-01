module

/-
Smoothness and inversion symmetry of the flat-chart Jacobi potential.

For every `k ≥ 2`, `potV k` is smooth on all of `ℂ`: its even norm powers
can be expressed using the smooth function `Complex.normSq`, and its
denominator is positive. The specialization at `k = 3` has the formula
`potV 3 w = 32‖w‖²/(‖w‖⁴+1)²` and is also smooth on the open disk.

For `z ≠ 0`, the Jacobian-weighted pullback under the circle inversion
`z ↦ 1 / z̄` equals the same potential:
`‖z‖⁻⁴ · potV 3 (1 / z̄) = potV 3 z`.
This is the coefficient identity used when reflecting the equation across
boundary arcs.
-/
public import KsIndexLean.Surface

@[expose] public section


noncomputable section
namespace KsIndex.Surface

/-- `potV 3` in `normSq` form: `32·|w|²/((|w|²)²+1)²`. -/
lemma potV_three_eq (w : ℂ) :
    potV 3 w = 32 * Complex.normSq w / (Complex.normSq w ^ 2 + 1) ^ 2 := by
  have h2 : ‖w‖ ^ 2 = Complex.normSq w := Complex.sq_norm w
  have h4 : ‖w‖ ^ 4 = Complex.normSq w ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2]
  unfold potV
  norm_num [h2, h4]

/-- `Complex.normSq` is `C^∞` (it is `re·re + im·im`). -/
lemma contDiff_normSq : ContDiff ℝ (⊤ : ℕ∞) Complex.normSq := by
  have h : (Complex.normSq : ℂ → ℝ) = fun z => z.re * z.re + z.im * z.im := by
    funext z; exact Complex.normSq_apply z
  rw [h]
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

/-- The flat Jacobi potential is smooth for every admissible number of ends.
Writing its even powers through `normSq` avoids differentiating the norm at zero. -/
theorem contDiff_potV {k : ℕ} (hk : 2 ≤ k) :
    ContDiff ℝ (⊤ : ℕ∞) (potV k) := by
  have hfun : potV k = fun w =>
      8 * ((k : ℝ) - 1) ^ 2 * Complex.normSq w ^ (k - 2) /
        (Complex.normSq w ^ (k - 1) + 1) ^ 2 := by
    funext w
    have h₁ : 2 * k - 4 = 2 * (k - 2) := by omega
    have h₂ : 2 * k - 2 = 2 * (k - 1) := by omega
    simp only [potV, h₁, h₂, pow_mul, Complex.sq_norm]
  rw [hfun]
  exact (contDiff_const.mul (contDiff_normSq.pow (k - 2))).div
    (((contDiff_normSq.pow (k - 1)).add contDiff_const).pow 2)
    (fun w => by have hn := Complex.normSq_nonneg w; positivity)

/-- The flat-chart Jacobi potential `potV 3` is `C^∞` on all of `ℂ`
(the denominator `(|w|⁴+1)²` never vanishes). -/
theorem contDiff_potV_three : ContDiff ℝ (⊤ : ℕ∞) (potV 3) := by
  have hfun : potV 3 = fun w => 32 * Complex.normSq w / (Complex.normSq w ^ 2 + 1) ^ 2 := by
    funext w; exact potV_three_eq w
  rw [hfun]
  refine ContDiff.div (contDiff_const.mul contDiff_normSq)
    (((contDiff_normSq.pow 2).add contDiff_const).pow 2) fun w => ?_
  have h0 : (0 : ℝ) ≤ Complex.normSq w := Complex.normSq_nonneg w
  positivity

/-- Smoothness of `potV 3` restricted to the open disk. -/
theorem contDiffOn_potV_three : ContDiffOn ℝ (⊤ : ℕ∞) (potV 3) disk :=
  contDiff_potV_three.contDiffOn

/-- Away from zero, the Jacobian-weighted pullback of `potV 3` under the
circle inversion `z ↦ 1 / z̄` is `potV 3` itself. -/
theorem potV_three_inversion {z : ℂ} (hz : z ≠ 0) :
    (‖z‖ ^ 4)⁻¹ * potV 3 (1 / (starRingEnd ℂ) z) = potV 3 z := by
  have hN0 : (0 : ℝ) < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hN : Complex.normSq z ≠ 0 := ne_of_gt hN0
  have h4 : ‖z‖ ^ 4 = Complex.normSq z ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.sq_norm]
  have hinv : Complex.normSq (1 / (starRingEnd ℂ) z) = (Complex.normSq z)⁻¹ := by
    rw [one_div, Complex.normSq_inv, Complex.normSq_conj]
  rw [potV_three_eq, potV_three_eq, h4, hinv]
  have hd1 : ((Complex.normSq z)⁻¹ ^ 2 + 1) ≠ 0 := by positivity
  have hd2 : (Complex.normSq z ^ 2 + 1) ≠ 0 := by positivity
  field_simp
  ring

end KsIndex.Surface
