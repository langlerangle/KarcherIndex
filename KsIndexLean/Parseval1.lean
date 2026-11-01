module

/-
Parseval's identity on `[0, 2π]` and the Fourier derivative rule.

The Parseval theorem assumes global continuity of `g : ℝ → ℂ`, with no periodicity
hypothesis. The derivative rule assumes a continuous derivative and `2π`-periodicity.

`fc g ℓ = (2π)⁻¹ ∫₀^{2π} g(θ) e^{−iℓθ} dθ` is the coefficient of `e^{iℓθ}`.

* `fc_eq_fourierCoeffOn` — it is Mathlib's `fourierCoeffOn` on `[0, 2π]`;
* `hasSum_sq_fc` — **Parseval**: `∑_ℓ |fc g ℓ|² = (2π)⁻¹ ∫₀^{2π} |g|²` for continuous `g`
  (Mathlib `hasSum_sq_fourierCoeffOn`; `MemLp` on `(0,2π]` from continuity on `[0,2π]`);
* `fc_deriv` — `fc g' ℓ = iℓ · fc g ℓ` for `C¹` periodic `g` (Mathlib `fourierCoeffOn_of_hasDerivAt`,
  the boundary term vanishing by periodicity; `ℓ = 0` by the FTC).

Route credit: the same composition (Mathlib's `L²(AddCircle)` Parseval + a periodic-function
transfer) was worked out for the `n`-torus by Tor's TorusNash project
(`TorusSobolev.parseval_stdFourierCoeff`, commit c2b4e94, Aristotle-proved); here the one-variable
case is taken directly from Mathlib's interval-form lemmas on our pin.
-/
public import Mathlib

@[expose] public section


noncomputable section

open Real MeasureTheory intervalIntegral Set
open scoped ContDiff

namespace KsIndex.Parseval

/-- The Fourier coefficient of `e^{iℓθ}`: `fc g ℓ = (2π)⁻¹ ∫₀^{2π} g(θ) e^{−iℓθ} dθ`. -/
def fc (g : ℝ → ℂ) (ℓ : ℤ) : ℂ :=
  (2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, g θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ)

lemma two_pi_pos' : (0 : ℝ) < 2 * π := by positivity

/-- `fc` is Mathlib's `fourierCoeffOn` on `[0, 2π]`. -/
lemma fc_eq_fourierCoeffOn (g : ℝ → ℂ) (ℓ : ℤ) : fc g ℓ = fourierCoeffOn two_pi_pos' g ℓ := by
  haveI : Fact ((0 : ℝ) < 2 * π - 0) := ⟨by simp; positivity⟩
  rw [fourierCoeffOn_eq_integral, fc]
  simp only [sub_zero, one_div, smul_eq_mul]
  congr 1
  refine integral_congr fun x _ => ?_
  rw [fourier_coe_apply, mul_comm]
  congr 2
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  push_cast
  field_simp
  ring

lemma memLp_of_continuous {g : ℝ → ℂ} (hg : Continuous g) :
    MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg.continuousOn : ContinuousOn g (Icc 0 (2 * π)))
  refine MemLp.of_bound hg.aestronglyMeasurable M ?_
  exact (ae_restrict_iff' measurableSet_Ioc).2
    (Filter.Eventually.of_forall fun x hx => hM x (Ioc_subset_Icc_self hx))

/-- **Parseval** for globally continuous `g`, integrated over `[0, 2π]`:
`∑_ℓ ‖fc g ℓ‖² = (2π)⁻¹ ∫₀^{2π} ‖g‖²`. No periodicity is required. -/
theorem hasSum_sq_fc {g : ℝ → ℂ} (hg : Continuous g) :
    HasSum (fun ℓ : ℤ => ‖fc g ℓ‖ ^ 2)
      ((2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖g θ‖ ^ 2) := by
  have h := hasSum_sq_fourierCoeffOn two_pi_pos' (memLp_of_continuous hg)
  simp only [sub_zero, smul_eq_mul] at h
  simpa only [fc_eq_fourierCoeffOn] using h

/-- **The derivative rule**: for `C¹` `2π`-periodic `g`, `fc g' ℓ = iℓ · fc g ℓ`. -/
theorem fc_deriv {g g' : ℝ → ℂ} (hd : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g')
    (hper : Function.Periodic g (2 * π)) (ℓ : ℤ) :
    fc g' ℓ = Complex.I * (ℓ : ℂ) * fc g ℓ := by
  have hend : g (2 * π) = g 0 := by simpa using hper 0
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · -- `ℓ = 0`: `∫₀^{2π} g' = g(2π) − g(0) = 0`
    simp only [Int.cast_zero, mul_zero, zero_mul, fc, neg_zero, Complex.exp_zero, mul_one]
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hg'.intervalIntegrable _ _), hend, sub_self,
      mul_zero]
  · have h := fourierCoeffOn_of_hasDerivAt two_pi_pos' hℓ (fun x _ => hd x)
      (hg'.intervalIntegrable _ _)
    rw [hend, sub_self, mul_zero, zero_sub, ← fc_eq_fourierCoeffOn, ← fc_eq_fourierCoeffOn] at h
    push_cast at h
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    have hℓ' : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
    rw [h]
    field_simp
    ring

end KsIndex.Parseval
