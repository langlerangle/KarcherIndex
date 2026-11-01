module

/-
Poisson–Fourier expansion for bounded continuous boundary data.

For a globally continuous `f : ℝ → ℂ` with a global bound `‖f φ‖ ≤ B`,
`hasSum_poissonExt` gives, at each `w` with `‖w‖ < 1`,

  `poissonExt f w = Σ_m ‖w‖^{|m|} · exp(i m arg w) · f̂(m)`,
  `f̂(m) = (2π)⁻¹ ∫₀^{2π} exp(−i m φ) f(φ) dφ`.

No periodicity of `f` is assumed. The statement is a `HasSum` identity at each
interior point, including the origin; it does not assert boundary convergence,
uniform convergence or termwise differentiation.

The proof extends the monomial reproduction argument of `ArcPoisson`: expand
the kernel into integer modes, dominate each mode by `‖w‖^{|m|} · B`, and interchange
summation and integration by dominated convergence. The geometric bound is summable
because `‖w‖ < 1`. Coefficient integrals remain explicit; their evaluation and
reindexing onto a character-class progression are separate results.
-/
public import KsIndexLean.ArcPoisson

@[expose] public section


noncomputable section

open Real Set Filter MeasureTheory intervalIntegral Topology Complex

namespace KsIndex.ArcPoissonSeries

open KsIndex.ArcPoisson

/-- The `m`-th kernel mode against a boundary trace `f`: `‖w‖^{|m|}·e^{im(θ−φ)}·f(φ)`. -/
def kMode (s θ : ℝ) (f : ℝ → ℂ) (m : ℤ) (φ : ℝ) : ℂ :=
  ((s ^ m.natAbs : ℝ) : ℂ) * Complex.exp (↑m * ↑(θ - φ) * Complex.I) * f φ

lemma continuous_kMode (s θ : ℝ) {f : ℝ → ℂ} (hf : Continuous f) (m : ℤ) :
    Continuous (kMode s θ f m) := by
  unfold kMode
  exact (continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))).mul hf

lemma norm_kMode_le {s : ℝ} (hs0 : 0 ≤ s) (θ : ℝ) {f : ℝ → ℂ} {B : ℝ} (hB : ∀ φ, ‖f φ‖ ≤ B)
    (m : ℤ) (φ : ℝ) : ‖kMode s θ f m φ‖ ≤ s ^ m.natAbs * B := by
  unfold kMode
  rw [norm_mul, norm_mul]
  have he : ‖Complex.exp (↑m * ↑(θ - φ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]; simp [Complex.mul_im]
  rw [he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hB φ) (by positivity)

/-- The mode sums to the kernel times the trace (kernel expansion, `mul_right`). -/
lemma hasSum_kMode {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (θ : ℝ) (f : ℝ → ℂ) (φ : ℝ) :
    HasSum (fun m : ℤ => kMode s θ f m φ) ((poissonKer s (θ - φ) : ℂ) * f φ) := by
  have h := (hasSum_poissonKer hs0 hs1 (θ - φ)).mul_right (f φ)
  refine h.congr_fun (fun m => ?_)
  unfold kMode
  rw [Complex.ofReal_pow]

/-- The Poisson–Fourier series at an interior point, for globally bounded continuous `f`:
`poissonExt f w = Σ_m ‖w‖^{|m|}·e^{im·arg w}·f̂(m)`. No periodicity is assumed. -/
theorem hasSum_poissonExt {f : ℝ → ℂ} (hf : Continuous f) {B : ℝ} (hB : ∀ φ, ‖f φ‖ ≤ B)
    {w : ℂ} (hw1 : ‖w‖ < 1) :
    HasSum (fun m : ℤ => ((‖w‖ ^ m.natAbs : ℝ) : ℂ)
        * Complex.exp (↑m * ↑(Complex.arg w) * Complex.I)
        * ((2 * π)⁻¹ * ∫ φ in (0:ℝ)..2 * π, Complex.exp (-↑m * ↑φ * Complex.I) * f φ))
      (poissonExt f w) := by
  set s := ‖w‖ with hs_def
  set θ := Complex.arg w with hθ_def
  have hs0 : 0 ≤ s := norm_nonneg w
  have hle : (0 : ℝ) ≤ 2 * π := by positivity
  -- the mode-integral value: `∫₀^{2π} kMode = ‖w‖^{|m|} e^{imθ} · (∫ e^{−imφ} f)`
  have hint : ∀ m : ℤ, (∫ φ in (0:ℝ)..2 * π, kMode s θ f m φ)
      = ((s ^ m.natAbs : ℝ) : ℂ) * Complex.exp (↑m * ↑θ * Complex.I)
        * ∫ φ in (0:ℝ)..2 * π, Complex.exp (-↑m * ↑φ * Complex.I) * f φ := by
    intro m
    have hrw : ∀ φ : ℝ, kMode s θ f m φ
        = (((s ^ m.natAbs : ℝ) : ℂ) * Complex.exp (↑m * ↑θ * Complex.I))
          * (Complex.exp (-↑m * ↑φ * Complex.I) * f φ) := by
      intro φ
      unfold kMode
      rw [Complex.ofReal_sub,
        show ((↑m : ℂ) * (↑θ - ↑φ) * Complex.I)
          = (↑m * ↑θ * Complex.I) + (-↑m * ↑φ * Complex.I) by ring, Complex.exp_add]
      ring
    simp_rw [hrw]
    rw [intervalIntegral.integral_const_mul]
  -- dominated-convergence interchange
  have hDCT := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc (0:ℝ) (2 * π)))
    (F := kMode s θ f)
    (f := fun φ => (poissonKer s (θ - φ) : ℂ) * f φ)
    (bound := fun m _ => s ^ m.natAbs * B)
    (fun m => (continuous_kMode s θ hf m).aestronglyMeasurable)
    (fun m => Filter.Eventually.of_forall (fun φ => norm_kMode_le hs0 θ hB m φ))
    (Filter.Eventually.of_forall (fun _ => (summable_r_natAbs hs0 hw1).mul_right B))
    (integrable_const _)
    (Filter.Eventually.of_forall (fun φ => hasSum_kMode hs0 hw1 θ f φ))
  -- convert μ-integrals to interval integrals
  have hconv : ∀ g : ℝ → ℂ,
      (∫ φ, g φ ∂(volume.restrict (Set.Ioc (0:ℝ) (2 * π)))) = ∫ φ in (0:ℝ)..2 * π, g φ :=
    fun g => (intervalIntegral.integral_of_le hle).symm
  -- convert the summand integrals first, then the value integral unambiguously
  rw [show (fun m => ∫ φ, kMode s θ f m φ ∂(volume.restrict (Set.Ioc (0:ℝ) (2 * π))))
        = (fun m => ∫ φ in (0:ℝ)..2 * π, kMode s θ f m φ) from funext (fun m => hconv _)] at hDCT
  rw [hconv] at hDCT
  simp only [hint] at hDCT
  -- poissonExt as `(2π)⁻¹·∫ Ker·f`
  have hpe : poissonExt f w
      = ((2 * π)⁻¹ : ℂ) * ∫ φ in (0:ℝ)..2 * π, (poissonKer s (θ - φ) : ℂ) * f φ := by
    unfold poissonExt
    rw [← hs_def, ← hθ_def]
    push_cast; ring
  -- rescale by `(2π)⁻¹`
  have hfinal := hDCT.mul_left ((2 * π)⁻¹ : ℂ)
  rw [hpe]
  exact hfinal.congr_fun (fun m => by push_cast; ring)

end KsIndex.ArcPoissonSeries
