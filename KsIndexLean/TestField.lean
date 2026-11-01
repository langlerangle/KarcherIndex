module

/-
KsIndexLean — The test-field coefficient and Catalan-series identities.

Paper reference: [ksindexi] Lemma `test-field` (Section 3, "Lower bound"):
with h(x) = √(cos x) for |x| < π/2 (and 0 otherwise), and
v(θ) = h(θ̲)·e^{-iθ̲/2} using θ̲ ∈ (-π,π],
one has  |v̂(0)|² = 1/8,  |v̂(1)|² = 1/32,  and for every a ∈ (0,1)

    ∑_{ℓ ∈ ℤ} |ℓ + a| · |v̂(ℓ)|²  =  1/4     (independently of a).

The calculations here use the evenness of h and the real interval integral

    g ξ  =  2 ∫_{0}^{π/2} √(cos x) · cos (ξ x) dx        ( =  2π·ĥ(ξ) ),

and the coefficient sequence  c ℓ = g(ℓ + 1/2) / (2π)  ( = v̂(ℓ), real).

Proof outline (following the paper):
  L1  g_half            g(1/2) = π/√2                    [substitution to ∫√(1-u²)]
  L2  g_neg             g(-ξ) = g(ξ)                     [cos even in ξ]
  L3  g_recursion       (ξ+3/2)·g(ξ+1) = (3/2-ξ)·g(ξ-1) [angle addition + IBP]
  L4  g_three_halves    g(3/2) = g(1/2)/2
  L5  g_five_halves     g(5/2) = 0  ⟹  c(2q+2) = 0      [induction via L3]
  L6  g_odd_catalan     g(2q+3/2) = (-1)^q·C_q·4^{-q}·g(3/2)   [induction via L3]
  L7  pairing           ℓ ≥ 0, a ∈ (0,1) ⟹ |ℓ+a| + |-ℓ-1+a| = 2ℓ+1
  L8  telescope         ∑_{q≥0} (4q+3)·C_q²/16^q = 4    [telescoping in b_q = binom(2q,q)²/16^q]
  L9  centralBinom_div_four_pow_tendsto_zero             [W_q² ≤ 1/(2q+1) by induction]
  L10 main              assembly

The actual periodic field and its Fourier identification are proved in
`ArcField` and `ArcFieldFc.fc_vF`. Weighted summability is supplied here by
`summable_abs_mul_sq`; `ArcSpace.cC_mem_ArcDom` combines it with the
sign-multiplier constraint to prove membership in the single-arc domain.
-/
public import Mathlib

@[expose] public section


noncomputable section

namespace KsIndex.TestField

open Real intervalIntegral Filter Topology

/-- `g ξ = 2∫₀^{π/2} √(cos x)·cos(ξx) dx`; this is `2π·ĥ(ξ)` for the paper's
even bump `h = √cos · 𝟙_{(-π/2,π/2)}`. -/
def g (ξ : ℝ) : ℝ := 2 * ∫ x in (0 : ℝ)..(π/2), Real.sqrt (Real.cos x) * Real.cos (ξ * x)

/-- The Fourier coefficients of the paper's test field `v`: `c ℓ = v̂(ℓ) = ĥ(ℓ + 1/2)`. -/
def c (ℓ : ℤ) : ℝ := g ((ℓ : ℝ) + 1/2) / (2 * π)

/-! ### Elementary values and symmetries -/

/-- L1: `g(1/2) = π/√2`, by the substitution `u = √2·sin(x/2)` reducing to
`∫₀¹ √(1-u²) du = π/4`. -/
theorem g_half : g (1/2) = π / Real.sqrt 2 := by
  have hm : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  -- The half-angle identity `cos x = 1 - (√2·sin(x/2))²`.
  have hid : ∀ x : ℝ, Real.cos x = 1 - (Real.sqrt 2 * Real.sin (1/2 * x)) ^ 2 := by
    intro x
    have h := Real.cos_two_mul' (1/2 * x)
    rw [show (2 : ℝ) * (1/2 * x) = x by ring] at h
    rw [h]
    have hpyth := Real.sin_sq_add_cos_sq (1/2 * x)
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [mul_pow, h2]
    linarith
  -- The substitution `u = √2·sin(x/2)`.
  have hsub : ∫ x in (0:ℝ)..(π/2),
        ((fun u => Real.sqrt 2 * Real.sqrt (1 - u ^ 2))
          ∘ (fun x => Real.sqrt 2 * Real.sin (1/2 * x))) x
          * (Real.sqrt 2 / 2 * Real.cos (1/2 * x))
      = ∫ u in (Real.sqrt 2 * Real.sin (1/2 * 0))..(Real.sqrt 2 * Real.sin (1/2 * (π/2))),
          Real.sqrt 2 * Real.sqrt (1 - u ^ 2) := by
    apply intervalIntegral.integral_comp_mul_deriv
    · intro x _
      have h0 : HasDerivAt (fun y : ℝ => 1/2 * y) (1/2 * 1) x :=
        (hasDerivAt_id x).const_mul (1/2 : ℝ)
      have h := (h0.sin).const_mul (Real.sqrt 2)
      have hv : Real.sqrt 2 * (Real.cos (1/2 * x) * (1/2 * 1))
          = Real.sqrt 2 / 2 * Real.cos (1/2 * x) := by ring
      rw [hv] at h
      exact h
    · fun_prop
    · fun_prop
  -- Pointwise, the integrand of `g (1/2)` is the substitution integrand.
  have hpoint : ∀ x : ℝ, Real.sqrt (Real.cos x) * Real.cos (1/2 * x)
      = ((fun u => Real.sqrt 2 * Real.sqrt (1 - u ^ 2))
          ∘ (fun x => Real.sqrt 2 * Real.sin (1/2 * x))) x
          * (Real.sqrt 2 / 2 * Real.cos (1/2 * x)) := by
    intro x
    simp only [Function.comp_apply]
    rw [← hid x]
    linear_combination (-(Real.sqrt (Real.cos x) * Real.cos (1/2 * x)) / 2) * hm
  -- Endpoints.
  have e0 : Real.sqrt 2 * Real.sin (1/2 * 0) = 0 := by simp
  have e1 : Real.sqrt 2 * Real.sin (1/2 * (π/2)) = 1 := by
    rw [show (1/2 : ℝ) * (π/2) = π/4 by ring, Real.sin_pi_div_four]
    linear_combination hm / 2
  -- The quarter-disk integral, from Mathlib's `∫_{-1}^{1} √(1-x²) = π/2` by evenness.
  have hquarter : ∫ u in (0:ℝ)..1, Real.sqrt (1 - u ^ 2) = π / 4 := by
    have hcont : Continuous fun u : ℝ => Real.sqrt (1 - u ^ 2) := by fun_prop
    have hsplit : (∫ u in (-1:ℝ)..0, Real.sqrt (1 - u ^ 2))
          + ∫ u in (0:ℝ)..1, Real.sqrt (1 - u ^ 2)
        = ∫ u in (-1:ℝ)..1, Real.sqrt (1 - u ^ 2) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    have hrefl : (∫ u in (-1:ℝ)..0, Real.sqrt (1 - u ^ 2))
        = ∫ u in (0:ℝ)..1, Real.sqrt (1 - u ^ 2) := by
      have h := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := (1:ℝ))
        (fun u => Real.sqrt (1 - u ^ 2))
      simp only [neg_zero, neg_sq] at h
      exact h.symm
    rw [hrefl] at hsplit
    rw [integral_sqrt_one_sub_sq] at hsplit
    linarith
  -- Assembly.
  unfold g
  rw [intervalIntegral.integral_congr fun x _ => hpoint x, hsub, e0, e1,
      intervalIntegral.integral_const_mul, hquarter,
      eq_div_iff (by positivity : Real.sqrt 2 ≠ 0)]
  linear_combination (π / 2) * hm

/-- L2: `g` is even (the integrand is even in `ξ`). -/
theorem g_neg (ξ : ℝ) : g (-ξ) = g ξ := by
  unfold g
  simp only [neg_mul, Real.cos_neg]

/-- Shift-parity of the coefficients (paper eq. `test-field-shift-parity`):
`c(-ℓ-1) = c ℓ`. Immediate from `g_neg`. -/
theorem c_reflect (ℓ : ℤ) : c (-ℓ - 1) = c ℓ := by
  unfold c
  rw [show ((-ℓ - 1 : ℤ) : ℝ) + 1/2 = -((ℓ : ℝ) + 1/2) by push_cast; ring, g_neg]

/-- `|v̂(0)|² = 1/8`. -/
theorem c_zero_sq : c 0 ^ 2 = 1/8 := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hc : c 0 = 1 / (2 * Real.sqrt 2) := by
    simp only [c, Int.cast_zero, zero_add, g_half]
    field_simp
  rw [hc, div_pow, one_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-! ### The three-term recursion -/

/-- L3, the engine of the lemma: for every real `ξ`,
`(ξ + 3/2)·g(ξ+1) = (3/2 - ξ)·g(ξ-1)`.

Paper proof: write `2cos x·cos ξx = cos((ξ-1)x) + cos((ξ+1)x)` to get
`ξ·g(ξ-1) + ξ·g(ξ+1) = 4∫₀^{π/2}(cos x)^{3/2}·ξcos ξx dx`, integrate by parts
(boundary terms vanish since `(cos)^{3/2}` and its derivative
`-(3/2)√(cos)·sin` are continuous on `[0, π/2]` and vanish at `π/2`), and
expand `sin x·sin ξx` by angle addition again. -/
theorem g_recursion (ξ : ℝ) :
    (ξ + 3/2) * g (ξ + 1) = (3/2 - ξ) * g (ξ - 1) := by
  have hπ : (0 : ℝ) ≤ π / 2 := by positivity
  -- Continuity of every integrand in sight.
  have hcontp : Continuous fun x : ℝ => Real.sqrt (Real.cos x) * Real.cos ((ξ + 1) * x) := by
    fun_prop
  have hcontm : Continuous fun x : ℝ => Real.sqrt (Real.cos x) * Real.cos ((ξ - 1) * x) := by
    fun_prop
  have hcontA : Continuous fun x : ℝ =>
      Real.sqrt (Real.cos x) * (Real.cos x * Real.cos (ξ * x)) := by fun_prop
  have hcontB : Continuous fun x : ℝ =>
      Real.sqrt (Real.cos x) * (Real.sin x * Real.sin (ξ * x)) := by fun_prop
  have hcontD : Continuous fun x : ℝ =>
      ξ * (Real.sqrt (Real.cos x) * (Real.cos x * Real.cos (ξ * x)))
        - 3/2 * (Real.sqrt (Real.cos x) * (Real.sin x * Real.sin (ξ * x))) := by fun_prop
  -- The boundary function `F = cos·√cos·sin(ξ·)` and its derivative on `(0, π/2)`.
  have hF : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2),
      HasDerivAt (fun y => Real.cos y * Real.sqrt (Real.cos y) * Real.sin (ξ * y))
        (ξ * (Real.sqrt (Real.cos x) * (Real.cos x * Real.cos (ξ * x)))
          - 3/2 * (Real.sqrt (Real.cos x) * (Real.sin x * Real.sin (ξ * x)))) x := by
    intro x hx
    have hcos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos, hx.1], hx.2⟩
    have hs : Real.sqrt (Real.cos x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hcos)
    have hsq : Real.sqrt (Real.cos x) * Real.sqrt (Real.cos x) = Real.cos x :=
      Real.mul_self_sqrt hcos.le
    have hcosd : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x
    have hsqrtd : HasDerivAt (fun y => Real.sqrt (Real.cos y))
        (1 / (2 * Real.sqrt (Real.cos x)) * -Real.sin x) x := by
      have h := (Real.hasDerivAt_sqrt (ne_of_gt hcos)).comp x hcosd
      simpa [Function.comp_def] using h
    have hprod : HasDerivAt (fun y => Real.cos y * Real.sqrt (Real.cos y))
        (-Real.sin x * Real.sqrt (Real.cos x)
          + Real.cos x * (1 / (2 * Real.sqrt (Real.cos x)) * -Real.sin x)) x :=
      hcosd.mul hsqrtd
    have hsind : HasDerivAt (fun y => Real.sin (ξ * y)) (Real.cos (ξ * x) * (ξ * 1)) x :=
      ((hasDerivAt_id x).const_mul ξ).sin
    have h := hprod.mul hsind
    have hval : (-Real.sin x * Real.sqrt (Real.cos x)
          + Real.cos x * (1 / (2 * Real.sqrt (Real.cos x)) * -Real.sin x)) * Real.sin (ξ * x)
          + Real.cos x * Real.sqrt (Real.cos x) * (Real.cos (ξ * x) * (ξ * 1))
        = ξ * (Real.sqrt (Real.cos x) * (Real.cos x * Real.cos (ξ * x)))
          - 3/2 * (Real.sqrt (Real.cos x) * (Real.sin x * Real.sin (ξ * x))) := by
      field_simp
      linear_combination (Real.sin (ξ * x) * Real.sin x) * hsq
    rw [hval] at h
    exact h
  -- FTC: the derivative integrates to `F(π/2) - F(0) = 0`.
  have hFTC : ∫ x in (0:ℝ)..(π/2),
      (ξ * (Real.sqrt (Real.cos x) * (Real.cos x * Real.cos (ξ * x)))
        - 3/2 * (Real.sqrt (Real.cos x) * (Real.sin x * Real.sin (ξ * x)))) = 0 := by
    have hcontF : ContinuousOn
        (fun y => Real.cos y * Real.sqrt (Real.cos y) * Real.sin (ξ * y))
        (Set.Icc (0:ℝ) (π/2)) := Continuous.continuousOn (by fun_prop)
    have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hπ hcontF
      (fun x hx => (hF x hx).hasDerivWithinAt) (hcontD.intervalIntegrable _ _)
    rw [h]
    simp [Real.cos_pi_div_two]
  -- Split the integral into the two `g`-values via product-to-sum identities.
  have hA : (∫ x in (0:ℝ)..(π/2), Real.sqrt (Real.cos x) * (Real.cos x * Real.cos (ξ * x)))
      = (g (ξ + 1) + g (ξ - 1)) / 4 := by
    have hpt : ∀ x : ℝ, Real.sqrt (Real.cos x) * (Real.cos x * Real.cos (ξ * x))
        = (Real.sqrt (Real.cos x) * Real.cos ((ξ + 1) * x)
            + Real.sqrt (Real.cos x) * Real.cos ((ξ - 1) * x)) / 2 := by
      intro x
      rw [show (ξ + 1) * x = ξ * x + x by ring, show (ξ - 1) * x = ξ * x - x by ring,
          Real.cos_add, Real.cos_sub]
      ring
    rw [intervalIntegral.integral_congr fun x _ => hpt x, intervalIntegral.integral_div,
        intervalIntegral.integral_add (hcontp.intervalIntegrable _ _)
          (hcontm.intervalIntegrable _ _)]
    unfold g
    ring
  have hB : (∫ x in (0:ℝ)..(π/2), Real.sqrt (Real.cos x) * (Real.sin x * Real.sin (ξ * x)))
      = (g (ξ - 1) - g (ξ + 1)) / 4 := by
    have hpt : ∀ x : ℝ, Real.sqrt (Real.cos x) * (Real.sin x * Real.sin (ξ * x))
        = (Real.sqrt (Real.cos x) * Real.cos ((ξ - 1) * x)
            - Real.sqrt (Real.cos x) * Real.cos ((ξ + 1) * x)) / 2 := by
      intro x
      rw [show (ξ + 1) * x = ξ * x + x by ring, show (ξ - 1) * x = ξ * x - x by ring,
          Real.cos_add, Real.cos_sub]
      ring
    rw [intervalIntegral.integral_congr fun x _ => hpt x, intervalIntegral.integral_div,
        intervalIntegral.integral_sub (hcontm.intervalIntegrable _ _)
          (hcontp.intervalIntegrable _ _)]
    unfold g
    ring
  rw [intervalIntegral.integral_sub ((hcontA.intervalIntegrable _ _).const_mul ξ)
        ((hcontB.intervalIntegrable _ _).const_mul (3/2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hA, hB] at hFTC
  linear_combination 4 * hFTC

/-- Half-integer specialization (`ξ := ℓ + 1/2`):
`(ℓ+2)·g(ℓ+3/2) = (1-ℓ)·g(ℓ-1/2)`. -/
theorem g_recursion_half (ℓ : ℤ) :
    ((ℓ : ℝ) + 2) * g ((ℓ : ℝ) + 3/2) = (1 - (ℓ : ℝ)) * g ((ℓ : ℝ) - 1/2) := by
  have h := g_recursion ((ℓ : ℝ) + 1/2)
  rw [show (ℓ : ℝ) + 1/2 + 3/2 = (ℓ : ℝ) + 2 by ring,
      show (ℓ : ℝ) + 1/2 + 1 = (ℓ : ℝ) + 3/2 by ring,
      show (3 : ℝ)/2 - ((ℓ : ℝ) + 1/2) = 1 - (ℓ : ℝ) by ring,
      show (ℓ : ℝ) + 1/2 - 1 = (ℓ : ℝ) - 1/2 by ring] at h
  exact h

/-! ### Consequences of the recursion -/

/-- L4: `g(3/2) = g(1/2)/2`, hence `|v̂(1)|² = 1/32`. -/
theorem g_three_halves : g (3/2) = g (1/2) / 2 := by
  have h := g_recursion_half 0
  simp only [Int.cast_zero, zero_add, zero_sub, sub_zero] at h
  rw [g_neg] at h
  linarith

theorem c_one_sq : c 1 ^ 2 = 1/32 := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hc : c 1 = 1 / (4 * Real.sqrt 2) := by
    simp only [c, Int.cast_one]
    rw [show (1 : ℝ) + 1/2 = 3/2 by norm_num, g_three_halves, g_half]
    field_simp
    ring
  rw [hc, div_pow, one_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- L5a: `g(5/2) = 0` (the recursion at `ℓ = 1` has factor `1 - ℓ = 0`). -/
theorem g_five_halves : g (5/2) = 0 := by
  have h := g_recursion_half 1
  simp only [Int.cast_one] at h
  norm_num at h
  linarith

/-- `g`-level form of L5b, by induction along the recursion. -/
theorem g_even_eq_zero (q : ℕ) : g (2 * (q : ℝ) + 5/2) = 0 := by
  induction q with
  | zero => simpa using g_five_halves
  | succ n ih =>
    have h := g_recursion_half (2 * (n : ℤ) + 3)
    push_cast at h
    rw [show 2 * (n : ℝ) + 3 + 3/2 = 2 * ((n : ℝ) + 1) + 5/2 by ring,
        show 2 * (n : ℝ) + 3 - 1/2 = 2 * (n : ℝ) + 5/2 by ring,
        ih, mul_zero] at h
    have hcoef : 2 * (n : ℝ) + 3 + 2 ≠ 0 := by positivity
    push_cast
    exact (mul_eq_zero.mp h).resolve_left hcoef

/-- L5b: all even coefficients from 2 on vanish: `v̂(2q+2) = 0`. -/
theorem c_even_eq_zero (q : ℕ) : c (2 * (q : ℤ) + 2) = 0 := by
  unfold c
  rw [show ((2 * (q : ℤ) + 2 : ℤ) : ℝ) + 1/2 = 2 * (q : ℝ) + 5/2 by push_cast; ring,
      g_even_eq_zero, zero_div]

/-- The Catalan-number ratio `(n+2)·C_{n+1} = 2(2n+1)·C_n`, obtained by
cancelling `n+1` between `succ_mul_catalan_eq_centralBinom` (twice) and
`Nat.succ_mul_centralBinom_succ`. -/
theorem catalan_succ_ratio (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  refine Nat.eq_of_mul_eq_mul_left n.succ_pos ?_
  calc (n + 1) * ((n + 2) * catalan (n + 1))
      = (n + 1 + 1) * catalan (n + 1) * (n + 1) := by ring
    _ = Nat.centralBinom (n + 1) * (n + 1) := by rw [succ_mul_catalan_eq_centralBinom]
    _ = (n + 1) * Nat.centralBinom (n + 1) := by ring
    _ = 2 * (2 * n + 1) * Nat.centralBinom n := Nat.succ_mul_centralBinom_succ n
    _ = 2 * (2 * n + 1) * ((n + 1) * catalan n) := by rw [succ_mul_catalan_eq_centralBinom]
    _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by ring

/-- L6: the Catalan closed form (paper eq. (iii)):
`g(2q + 3/2) = (-1)^q · C_q · 4^{-q} · g(3/2)`, `C_q = catalan q`. -/
theorem g_odd_catalan (q : ℕ) :
    g (2 * (q : ℝ) + 3/2) = (-1) ^ q * (catalan q : ℝ) / 4 ^ q * g (3/2) := by
  induction q with
  | zero => norm_num [catalan_zero]
  | succ n ih =>
    have h := g_recursion_half (2 * (n : ℤ) + 2)
    push_cast at h
    rw [show 2 * (n : ℝ) + 2 + 3/2 = 2 * ((n : ℝ) + 1) + 3/2 by ring,
        show 2 * (n : ℝ) + 2 - 1/2 = 2 * (n : ℝ) + 3/2 by ring,
        ih] at h
    have hcoef : 2 * (n : ℝ) + 2 + 2 ≠ 0 := by positivity
    have hratio : ((n : ℝ) + 2) * (catalan (n + 1) : ℝ)
        = 2 * (2 * (n : ℝ) + 1) * (catalan n : ℝ) := by
      exact_mod_cast catalan_succ_ratio n
    push_cast
    refine mul_left_cancel₀ hcoef ?_
    rw [h]
    linear_combination (2 * (-1) ^ n * g (3/2) / 4 ^ (n + 1)) * hratio

/-- Hence `|v̂(2q+1)|² = C_q² / (32·16^q)`. -/
theorem c_odd_sq (q : ℕ) :
    c (2 * (q : ℤ) + 1) ^ 2 = (catalan q : ℝ) ^ 2 / (32 * 16 ^ q) := by
  have hc : c (2 * (q : ℤ) + 1) = (-1) ^ q * (catalan q : ℝ) / 4 ^ q * c 1 := by
    unfold c
    rw [show ((2 * (q : ℤ) + 1 : ℤ) : ℝ) + 1/2 = 2 * (q : ℝ) + 3/2 by push_cast; ring,
        show ((1 : ℤ) : ℝ) + 1/2 = 3/2 by norm_num, g_odd_catalan]
    ring
  have h1 : ((-1 : ℝ) ^ q) ^ 2 = 1 := by rw [pow_right_comm]; norm_num
  have h4 : ((4 : ℝ) ^ q) ^ 2 = 16 ^ q := by rw [pow_right_comm]; norm_num
  rw [hc, mul_pow, c_one_sq, div_pow, mul_pow, h1, one_mul, h4]
  ring

/-! ### The sum -/

/-- L7 (pairing): for `ℓ ≥ 0` and `a ∈ (0,1)`,
`|ℓ + a| + |(-ℓ - 1) + a| = 2ℓ + 1`.  This is where all `a`-dependence dies. -/
theorem pairing (ℓ : ℕ) {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    |(ℓ : ℝ) + a| + |(-(ℓ : ℝ) - 1) + a| = 2 * ℓ + 1 := by
  obtain ⟨ha0, ha1⟩ := ha
  have hℓ : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
  rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
  ring

/-- L9 (decay of normalized central binomials): `binom(2q,q)/4^q → 0`.
Route: `W_q := binom(2q,q)/4^q` satisfies `W_q² ≤ 1/(2q+1)` (induction,
`norm_num`-friendly), then squeeze. -/
theorem centralBinom_div_four_pow_tendsto_zero :
    Tendsto (fun q : ℕ => (Nat.centralBinom q : ℝ) / 4 ^ q) atTop (𝓝 0) := by
  -- Cleared-denominator form of `W_q² ≤ 1/(2q+1)`, by induction.
  have hWsq : ∀ q : ℕ, (Nat.centralBinom q : ℝ) ^ 2 * (2 * (q : ℝ) + 1) ≤ 16 ^ q := by
    intro q
    induction q with
    | zero => norm_num [Nat.centralBinom_zero]
    | succ n ih =>
      have h1 : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
          = 2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ n
      have h1sq : ((n : ℝ) + 1) ^ 2 * (Nat.centralBinom (n + 1) : ℝ) ^ 2
          = 4 * (2 * (n : ℝ) + 1) ^ 2 * (Nat.centralBinom n : ℝ) ^ 2 := by
        linear_combination (((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
          + 2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ)) * h1
      have hstep : ((n : ℝ) + 1) ^ 2
            * ((Nat.centralBinom (n + 1) : ℝ) ^ 2 * (2 * ((n : ℝ) + 1) + 1))
          ≤ ((n : ℝ) + 1) ^ 2 * 16 ^ (n + 1) := by
        have e1 : ((n : ℝ) + 1) ^ 2
              * ((Nat.centralBinom (n + 1) : ℝ) ^ 2 * (2 * ((n : ℝ) + 1) + 1))
            = 4 * (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 1)
              * ((Nat.centralBinom n : ℝ) ^ 2 * (2 * (n : ℝ) + 1)) := by
          linear_combination (2 * ((n : ℝ) + 1) + 1) * h1sq
        have c1 : (0 : ℝ) ≤ 4 * (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 1) := by positivity
        have e2 : (0 : ℝ) ≤ 16 ^ n := by positivity
        rw [e1]
        calc 4 * (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 1)
              * ((Nat.centralBinom n : ℝ) ^ 2 * (2 * (n : ℝ) + 1))
            ≤ 4 * (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 1) * 16 ^ n :=
              mul_le_mul_of_nonneg_left ih c1
          _ ≤ ((n : ℝ) + 1) ^ 2 * 16 ^ (n + 1) := by
              nlinarith [e2, pow_succ (16 : ℝ) n]
      have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
      have hfin := le_of_mul_le_mul_left hstep hpos
      push_cast
      exact hfin
  -- Squeeze `0 ≤ W_q ≤ √(1/(2q+1))`.
  have hW0 : ∀ q : ℕ, 0 ≤ (Nat.centralBinom q : ℝ) / 4 ^ q := fun q => by positivity
  have hle : ∀ q : ℕ, (Nat.centralBinom q : ℝ) / 4 ^ q
      ≤ Real.sqrt (1 / (2 * (q : ℝ) + 1)) := by
    intro q
    rw [Real.le_sqrt (hW0 q) (by positivity), div_pow,
        show ((4 : ℝ) ^ q) ^ 2 = 16 ^ q by rw [pow_right_comm]; norm_num,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    exact hWsq q
  have hden : Tendsto (fun q : ℕ => 2 * (q : ℝ) + 1) atTop atTop := by
    refine tendsto_atTop_mono (fun q : ℕ => ?_) tendsto_natCast_atTop_atTop
    have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    linarith
  have hfrac : Tendsto (fun q : ℕ => 1 / (2 * (q : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hden
  have hsqrt : Tendsto (fun q : ℕ => Real.sqrt (1 / (2 * (q : ℝ) + 1))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hfrac
    simpa [Function.comp_def, Real.sqrt_zero] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsqrt hW0 hle

/-- L8 (the telescope, paper's final display): `∑_{q≥0} (4q+3)·C_q²/16^q = 4`.
Route: `(4q+3)·C_q² = 4·binom(2q,q)² - binom(2q+2,q+1)²/4`… i.e. with
`b_q := binom(2q,q)²/16^q` the summand is `4(b_q - b_{q+1})`; telescoping plus
L9 gives `4·b_0 = 4`. -/
theorem catalan_telescope_hasSum :
    HasSum (fun q : ℕ => (4 * (q : ℝ) + 3) * (catalan q : ℝ) ^ 2 / 16 ^ q) 4 := by
  have hcb : ∀ q : ℕ, (Nat.centralBinom q : ℝ) = ((q : ℝ) + 1) * (catalan q : ℝ) := by
    intro q; exact_mod_cast (succ_mul_catalan_eq_centralBinom q).symm
  have hu : ∀ q : ℕ, (Nat.centralBinom (q + 1) : ℝ)
      = 2 * (2 * (q : ℝ) + 1) * (catalan q : ℝ) := by
    intro q
    have hne : ((q : ℝ) + 1) ≠ 0 := by positivity
    have h1 : ((q : ℝ) + 1) * (Nat.centralBinom (q + 1) : ℝ)
        = 2 * (2 * (q : ℝ) + 1) * (Nat.centralBinom q : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ q
    refine mul_left_cancel₀ hne ?_
    rw [h1, hcb q]; ring
  set B : ℕ → ℝ := fun q => (Nat.centralBinom q : ℝ) ^ 2 / 16 ^ q with hB
  have key : ∀ q : ℕ,
      (4 * (q : ℝ) + 3) * (catalan q : ℝ) ^ 2 / 16 ^ q = 4 * (B q - B (q + 1)) := by
    intro q
    have hP : ((16 : ℝ) ^ q) ≠ 0 := by positivity
    simp only [hB]
    rw [pow_succ, hcb q, hu q]
    field_simp
    ring
  have hf0 : ∀ q : ℕ, 0 ≤ (4 * (q : ℝ) + 3) * (catalan q : ℝ) ^ 2 / 16 ^ q := by
    intro q; positivity
  have hB0 : B 0 = 1 := by simp [hB, Nat.centralBinom_zero]
  have hBnn : ∀ n : ℕ, 0 ≤ B n := by intro n; simp only [hB]; positivity
  have hpartial : ∀ n : ℕ,
      ∑ i ∈ Finset.range n, (4 * (i : ℝ) + 3) * (catalan i : ℝ) ^ 2 / 16 ^ i
      = 4 * (1 - B n) := by
    intro n
    rw [Finset.sum_congr rfl fun i _ => key i, ← Finset.mul_sum,
        Finset.sum_range_sub' B, hB0]
  have hsum : Summable (fun q : ℕ => (4 * (q : ℝ) + 3) * (catalan q : ℝ) ^ 2 / 16 ^ q) :=
    summable_of_sum_range_le (c := 4) hf0 fun n => by rw [hpartial n]; nlinarith [hBnn n]
  have hBtend : Tendsto B atTop (𝓝 0) := by
    have hBW : B = fun q : ℕ => ((Nat.centralBinom q : ℝ) / 4 ^ q) ^ 2 := by
      funext q
      simp only [hB]
      rw [div_pow, show ((4 : ℝ) ^ q) ^ 2 = 16 ^ q by rw [pow_right_comm]; norm_num]
    rw [hBW]
    have h := centralBinom_div_four_pow_tendsto_zero.pow 2
    norm_num at h
    exact h
  have hlim : Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n, (4 * (i : ℝ) + 3) * (catalan i : ℝ) ^ 2 / 16 ^ i)
      atTop (𝓝 4) := by
    simp only [hpartial]
    have h4 : Tendsto (fun n : ℕ => 4 * (1 - B n)) atTop (𝓝 (4 * (1 - 0))) :=
      (tendsto_const_nhds.sub hBtend).const_mul 4
    norm_num at h4
    exact h4
  have h4 : ∑' q : ℕ, (4 * (q : ℝ) + 3) * (catalan q : ℝ) ^ 2 / 16 ^ q = 4 :=
    tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlim
  have h := hsum.hasSum
  rw [h4] at h
  exact h

theorem catalan_telescope :
    ∑' q : ℕ, (4 * (q : ℝ) + 3) * (catalan q : ℝ) ^ 2 / 16 ^ q = 4 :=
  catalan_telescope_hasSum.tsum_eq

/-- The `ℕ`-side master sum `∑_{n≥0} (2n+1)·c(n)² = 1/4`: the even positions
contribute only `n = 0` (giving `1·(1/8)`), and the odd positions are the
Catalan telescope scaled by `1/32` (giving `1/8`). -/
theorem hasSum_two_mul_add_one_mul_sq :
    HasSum (fun n : ℕ => (2 * (n : ℝ) + 1) * c (n : ℤ) ^ 2) (1/4) := by
  have heven : HasSum
      (fun k : ℕ => (2 * ((2 * k : ℕ) : ℝ) + 1) * c ((2 * k : ℕ) : ℤ) ^ 2) (1/8) := by
    have hvanish : ∀ k : ℕ, k ≠ 0 →
        (2 * ((2 * k : ℕ) : ℝ) + 1) * c ((2 * k : ℕ) : ℤ) ^ 2 = 0 := by
      intro k hk
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      rw [show ((2 * (q + 1) : ℕ) : ℤ) = 2 * (q : ℤ) + 2 by push_cast; ring,
          c_even_eq_zero]
      ring
    have h0 : (2 * ((2 * 0 : ℕ) : ℝ) + 1) * c ((2 * 0 : ℕ) : ℤ) ^ 2 = 1/8 := by
      norm_num [c_zero_sq]
    have h := hasSum_single
      (f := fun k : ℕ => (2 * ((2 * k : ℕ) : ℝ) + 1) * c ((2 * k : ℕ) : ℤ) ^ 2) 0 hvanish
    simpa only [h0] using h
  have hodd : HasSum
      (fun k : ℕ => (2 * ((2 * k + 1 : ℕ) : ℝ) + 1) * c ((2 * k + 1 : ℕ) : ℤ) ^ 2) (1/8) := by
    have hfun : (fun k : ℕ => (2 * ((2 * k + 1 : ℕ) : ℝ) + 1) * c ((2 * k + 1 : ℕ) : ℤ) ^ 2)
        = fun k : ℕ => 1/32 * ((4 * (k : ℝ) + 3) * (catalan k : ℝ) ^ 2 / 16 ^ k) := by
      funext k
      rw [show ((2 * k + 1 : ℕ) : ℤ) = 2 * (k : ℤ) + 1 by push_cast; ring, c_odd_sq]
      push_cast
      ring
    rw [hfun, show (1 : ℝ)/8 = 1/32 * 4 by norm_num]
    exact catalan_telescope_hasSum.mul_left (1/32)
  rw [show (1 : ℝ)/4 = 1/8 + 1/8 by norm_num]
  exact HasSum.even_add_odd heven hodd

/-- The full `ℤ`-indexed sum, as a `HasSum`: split `ℤ` into `ℓ = n ≥ 0` and
`ℓ = -n-1`, dominate both halves by the master sequence `(2n+1)·c(n)²`
(using `c_reflect` on the negative side), and let the pairing identity
`|n+a| + |-n-1+a| = 2n+1` erase all `a`-dependence. -/
theorem hasSum_abs_mul_sq {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    HasSum (fun ℓ : ℤ => |(ℓ : ℝ) + a| * c ℓ ^ 2) (1/4) := by
  obtain ⟨ha0, ha1⟩ := ha
  -- Summability of the nonnegative half, by comparison.
  have hS₁ : Summable (fun n : ℕ => |((n : ℤ) : ℝ) + a| * c (n : ℤ) ^ 2) := by
    refine hasSum_two_mul_add_one_mul_sq.summable.of_nonneg_of_le
      (fun n => by positivity) fun n => ?_
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    refine mul_le_mul_of_nonneg_right (abs_le.mpr ⟨?_, ?_⟩) (by positivity) <;>
      push_cast <;> linarith
  -- Summability of the negative half, by `c_reflect` and comparison.
  have hS₂ : Summable
      (fun n : ℕ => |((-((n : ℤ) + 1) : ℤ) : ℝ) + a| * c (-((n : ℤ) + 1)) ^ 2) := by
    refine hasSum_two_mul_add_one_mul_sq.summable.of_nonneg_of_le
      (fun n => by positivity) fun n => ?_
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [show -((n : ℤ) + 1) = -(n : ℤ) - 1 by ring, c_reflect]
    refine mul_le_mul_of_nonneg_right (abs_le.mpr ⟨?_, ?_⟩) (by positivity) <;>
      push_cast <;> linarith
  have h₁ := hS₁.hasSum
  have h₂ := hS₂.hasSum
  -- The two half-sums add up to the master sum `1/4`, by the pairing identity.
  have hfun : (fun n : ℕ => |((n : ℤ) : ℝ) + a| * c (n : ℤ) ^ 2
        + |((-((n : ℤ) + 1) : ℤ) : ℝ) + a| * c (-((n : ℤ) + 1)) ^ 2)
      = fun n : ℕ => (2 * (n : ℝ) + 1) * c (n : ℤ) ^ 2 := by
    funext n
    rw [show -((n : ℤ) + 1) = -(n : ℤ) - 1 by ring, c_reflect]
    have hp := pairing n (Set.mem_Ioo.mpr ⟨ha0, ha1⟩)
    push_cast
    linear_combination (c (n : ℤ) ^ 2) * hp
  have hAB : (∑' n : ℕ, |((n : ℤ) : ℝ) + a| * c (n : ℤ) ^ 2)
      + (∑' n : ℕ, |((-((n : ℤ) + 1) : ℤ) : ℝ) + a| * c (-((n : ℤ) + 1)) ^ 2) = 1/4 := by
    have hadd : HasSum (fun n : ℕ => |((n : ℤ) : ℝ) + a| * c (n : ℤ) ^ 2
          + |((-((n : ℤ) + 1) : ℤ) : ℝ) + a| * c (-((n : ℤ) + 1)) ^ 2)
        ((∑' n : ℕ, |((n : ℤ) : ℝ) + a| * c (n : ℤ) ^ 2)
          + ∑' n : ℕ, |((-((n : ℤ) + 1) : ℤ) : ℝ) + a| * c (-((n : ℤ) + 1)) ^ 2) :=
      h₁.add h₂
    rw [hfun] at hadd
    exact hadd.unique hasSum_two_mul_add_one_mul_sq
  have hint : HasSum (fun ℓ : ℤ => |(ℓ : ℝ) + a| * c ℓ ^ 2)
      ((∑' n : ℕ, |((n : ℤ) : ℝ) + a| * c (n : ℤ) ^ 2)
        + ∑' n : ℕ, |((-((n : ℤ) + 1) : ℤ) : ℝ) + a| * c (-((n : ℤ) + 1)) ^ 2) :=
    HasSum.of_nat_of_neg_add_one h₁ h₂
  rw [hAB] at hint
  exact hint

/-- Weighted summability of the coefficient sequence. The additional
arc-support constraint is supplied by `ArcSpace.cC_mem_ArcDom`. -/
theorem summable_abs_mul_sq {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    Summable (fun ℓ : ℤ => |(ℓ : ℝ) + a| * c ℓ ^ 2) :=
  (hasSum_abs_mul_sq ha).summable

/-- **L10, the test-field lemma** ([ksindexi] Lemma `test-field`):
for every `a ∈ (0,1)`,
`∑_{ℓ∈ℤ} |ℓ + a| · |v̂(ℓ)|² = 1/4`, independently of `a`. -/
theorem test_field {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    ∑' ℓ : ℤ, |(ℓ : ℝ) + a| * c ℓ ^ 2 = 1/4 :=
  (hasSum_abs_mul_sq ha).tsum_eq

end KsIndex.TestField
