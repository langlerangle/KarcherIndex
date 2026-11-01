module

/-
KsIndexLean — EndFieldDomain: sign crossing at punctures of the six-ended surface.

The small local sign fact at a puncture of Ξ₃: since `p ∈ punctures 3` means `p⁶ = −1`,
the cube `p³` is a square root of `−1`, hence `Re(p³) = 0` and `Im(p³) = ±1`.  The angular
derivative of `Re(w³)` along the unit circle at `p` is therefore `∓3 ≠ 0`, so `Re(w³)` crosses
zero transversally at `p` — the two arcs incident to `p` carry opposite sign of `Re(w³)`
(opposite arc families).  The explicit sine formula supplies the sign crossing; continuity and
`Re(p³) = 0` alone would not suffice.
-/
public import KsIndexLean.Surface
public import KsIndexLean.EndChartPotential

@[expose] public section


noncomputable section
open Complex
namespace KsIndex.EndField
open KsIndex.Surface

/-- At a puncture of `Ξ₃`, the cube squares to `−1`. -/
lemma cube_sq_of_puncture {p : ℂ} (hp : p ∈ punctures 3) : (p ^ 3) ^ 2 = -1 := by
  have h : p ^ (2 * 3) = -1 := hp
  calc (p ^ 3) ^ 2 = p ^ (2 * 3) := by ring
    _ = -1 := h

/-- Hence `Re(p³) = 0` and `Im(p³)² = 1` — the cube is `±i`. -/
lemma cube_re_im {p : ℂ} (hp : p ∈ punctures 3) :
    (p ^ 3).re = 0 ∧ (p ^ 3).im ^ 2 = 1 := by
  have h2 : (p ^ 3) ^ 2 = -1 := cube_sq_of_puncture hp
  set z : ℂ := p ^ 3 with hz
  have hr : z.re * z.re - z.im * z.im = -1 := by
    have := congrArg Complex.re h2
    rwa [sq, Complex.mul_re, show ((-1 : ℂ)).re = -1 from by simp] at this
  have hi : z.re * z.im + z.im * z.re = 0 := by
    have := congrArg Complex.im h2
    rwa [sq, Complex.mul_im, show ((-1 : ℂ)).im = 0 from by simp] at this
  have hmul : z.re * z.im = 0 := by linear_combination hi / 2
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exfalso; nlinarith [hr, h, sq_nonneg z.re]
  refine ⟨hre0, ?_⟩
  nlinarith [hr, hre0]

/-- The imaginary part of `p³` is nonzero (`±1`) — the transversality that makes the zero
of `Re(w³)` at `p` a genuine sign crossing. -/
lemma cube_im_ne {p : ℂ} (hp : p ∈ punctures 3) : (p ^ 3).im ≠ 0 := by
  intro h
  have := (cube_re_im hp).2
  rw [h] at this
  norm_num at this

/-- **The sign of `Re(w³)` along the unit circle through `p`.**  For `w = p·e^{iθ}`,
`Re(w³) = −Im(p³)·sin(3θ)`, so (with `Im(p³) = ±1 ≠ 0`) the sign is that of `∓sin(3θ)`:
it crosses zero transversally at `θ = 0` and is opposite for small `θ > 0` vs `θ < 0` — the two
arcs incident to `p` carry opposite sign of `Re(w³)`. -/
lemma reCube_circle {p : ℂ} (hp : p ∈ punctures 3) (θ : ℝ) :
    ((p * Complex.exp ((θ : ℂ) * Complex.I)) ^ 3).re = -(p ^ 3).im * Real.sin (3 * θ) := by
  have hre : (p ^ 3).re = 0 := (cube_re_im hp).1
  have hexp : (p * Complex.exp ((θ : ℂ) * Complex.I)) ^ 3
      = p ^ 3 * Complex.exp (((3 * θ : ℝ) : ℂ) * Complex.I) := by
    have hc : ((3 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I) = ((3 * θ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [mul_pow, ← Complex.exp_nat_mul, hc]
  rw [hexp, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, hre]
  ring

/-- Circle points through `p` stay on the unit circle: `‖p·e^{iθ}‖ = 1`. -/
lemma norm_circlePt {p : ℂ} (hp : p ∈ punctures 3) (θ : ℝ) :
    ‖p * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
  rw [norm_mul, KsIndex.EndChart.norm_eq_one_of_mem_punctures hp, one_mul,
    Complex.norm_exp_ofReal_mul_I]

/-- **Arc-family membership of a circle point through `p`.**  `p·e^{iθ} ∈ arc 3 j` iff the
sign test `(−1)^j·(−Im(p³)·sin 3θ) < 0` holds — so the arc family is governed by `sin 3θ`
(with `Im(p³) = ±1`), crossing at `θ = 0`. -/
lemma circlePt_mem_arc {p : ℂ} (hp : p ∈ punctures 3) (j : ℕ) (θ : ℝ) :
    p * Complex.exp ((θ : ℂ) * Complex.I) ∈ arc 3 j
      ↔ (-1 : ℝ) ^ j * (-(p ^ 3).im * Real.sin (3 * θ)) < 0 := by
  simp only [arc, Set.mem_ofPred_eq, norm_circlePt hp, reCube_circle hp, and_iff_right]

end KsIndex.EndField
