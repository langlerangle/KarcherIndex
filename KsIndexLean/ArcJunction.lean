module

/-
KsIndexLean — Junction decomposition of the cutoff Fourier coefficients.

For `0 < η ≤ 1/4`, the junction field `fJ η` vanishes outside two intervals
of width `πη` next to `-π/2` and `π/2` within the principal window `[-π,π]`.
The bound `2η ≤ sin (πη)` ensures that the intervening central interval
contributes zero; the two outer intervals vanish because the cosine is
nonpositive.

The substitutions `θ = π/2-x` and `θ = x-π/2` give the exact decomposition
`fc (fJ η) ℓ = (2π)⁻¹ * (exp (iξπ/2) * Jm η ξ + exp (-iξπ/2) * Jp η ξ)`,
where `ξ = ℓ+1/2` and `Jp`, `Jm` integrate
`sqrt (sin x) * wJ η x * exp (±iξx)` over `0..πη`.

Each one-sided integral has norm at most `πη * sqrt (πη)` for every real
frequency and every positive `η`. Combining these bounds with the
decomposition proves `‖fc (fJ η) ℓ‖ ≤ 2η√η` for all integer `ℓ` when
`0 < η ≤ 1/4`. Decay in the frequency is established separately.
-/
public import KsIndexLean.ArcFieldFc
public import KsIndexLean.JunctionCut

@[expose] public section


noncomputable section

open Real Set Filter MeasureTheory intervalIntegral Topology
open KsIndex.ArcField KsIndex.JunctionCut

namespace KsIndex.ArcJunction

/-! ### The collar-width bound `sin(πη) ≥ 2η` -/

/-- For `0 < η ≤ 1/4`: `2η ≤ sin(πη)` (from `sin y > y − y³/6`). -/
lemma two_eta_le_sin_pi_eta {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1/4) :
    2 * η ≤ Real.sin (π * η) := by
  have h1 := Real.sin_gt_sub_cube (by positivity : (0:ℝ) < π * η)
  have hπ1 : 3.14 < π := Real.pi_gt_d2
  have hπ2 : π < 3.15 := Real.pi_lt_d2
  have hsq : π ^ 2 ≤ 3.15 ^ 2 := by nlinarith [Real.pi_pos]
  have hcube : π ^ 3 ≤ 32 := by nlinarith [Real.pi_pos, hsq]
  have hη2 : η ^ 2 ≤ 1 / 16 := by nlinarith
  have hkey : π ^ 3 * η ^ 2 ≤ 2 :=
    le_trans (mul_le_mul hcube hη2 (sq_nonneg η) (by norm_num)) (by norm_num)
  nlinarith [h1, hπ1, mul_le_mul_of_nonneg_right hkey hη0.le, hη0]

/-! ### The one-sided junction integrals -/

/-- `J₊(η, ξ) = ∫₀^{πη} √(sin x)·wJ η x·e^{+iξx} dx`. -/
def Jp (η ξ : ℝ) : ℂ :=
  ∫ x in (0:ℝ)..(π * η), (Real.sqrt (Real.sin x) : ℂ) * (wJ η x : ℂ)
    * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))

/-- `J₋(η, ξ) = ∫₀^{πη} √(sin x)·wJ η x·e^{−iξx} dx`. -/
def Jm (η ξ : ℝ) : ℂ :=
  ∫ x in (0:ℝ)..(π * η), (Real.sqrt (Real.sin x) : ℂ) * (wJ η x : ℂ)
    * Complex.exp (-(Complex.I * (ξ : ℂ) * (x : ℂ)))

lemma continuous_Jp_integrand (η ξ : ℝ) :
    Continuous (fun x : ℝ => (Real.sqrt (Real.sin x) : ℂ) * (wJ η x : ℂ)
      * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))) := by
  refine ((Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp Real.continuous_sin)).mul
    (Complex.continuous_ofReal.comp (continuous_wJ η))).mul
    (Complex.continuous_exp.comp ?_)
  exact continuous_const.mul Complex.continuous_ofReal

lemma continuous_Jm_integrand (η ξ : ℝ) :
    Continuous (fun x : ℝ => (Real.sqrt (Real.sin x) : ℂ) * (wJ η x : ℂ)
      * Complex.exp (-(Complex.I * (ξ : ℂ) * (x : ℂ)))) := by
  refine ((Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp Real.continuous_sin)).mul
    (Complex.continuous_ofReal.comp (continuous_wJ η))).mul
    (Complex.continuous_exp.comp ?_)
  exact (continuous_const.mul Complex.continuous_ofReal).neg

/-! ### The window form and the five-piece split -/

/-- The `fc`-integrand of `fJ` in the closed window: amplitude `hAmp·(1 − wCol)` at the
`(ℓ + 1/2)`-frequency. -/
lemma window_integrand_fJ (η : ℝ) (ℓ : ℤ) {θ : ℝ} (h : θ ∈ Set.Icc (-π) π) :
    fJ η θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ)
      = (hAmp θ : ℂ) * (1 - (wCol η θ : ℂ))
        * Complex.exp (-(((ℓ : ℂ) + 1/2) * θ) * Complex.I) := by
  simp only [fJ]
  rw [vF_eq_on_Icc h]
  rw [show (hAmp θ : ℂ) * Complex.exp (-Complex.I * (θ:ℂ) / 2) * (1 - (wCol η θ : ℂ))
        * Complex.exp (-(ℓ : ℂ) * Complex.I * θ)
      = (hAmp θ : ℂ) * (1 - (wCol η θ : ℂ))
        * (Complex.exp (-Complex.I * (θ:ℂ) / 2) * Complex.exp (-(ℓ : ℂ) * Complex.I * θ))
      by ring, ← Complex.exp_add]
  congr 2
  ring

/-- The exponential character is `2π`-periodic. -/
lemma exp_char_periodic (ℓ : ℤ) (θ : ℝ) :
    Complex.exp (-(ℓ : ℂ) * Complex.I * ((θ + 2 * π : ℝ) : ℂ))
      = Complex.exp (-(ℓ : ℂ) * Complex.I * (θ : ℂ)) := by
  rw [show -(ℓ : ℂ) * Complex.I * ((θ + 2 * π : ℝ) : ℂ)
      = -(ℓ : ℂ) * Complex.I * (θ : ℂ) + ((-ℓ : ℤ) : ℂ) * (2 * (π : ℂ) * Complex.I) by
      push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Window shift for any `2π`-periodic function. -/
lemma fc_eq_window (g : ℝ → ℂ) (hg : Function.Periodic g (2 * π)) (ℓ : ℤ) :
    Parseval.fc g ℓ
      = (2 * π : ℝ)⁻¹ * ∫ θ in (-π : ℝ)..π, g θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ) := by
  simp only [Parseval.fc]
  congr 1
  have hper : Function.Periodic
      (fun θ : ℝ => g θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ)) (2 * π) := by
    intro θ
    show g (θ + 2 * π) * Complex.exp (-(ℓ : ℂ) * Complex.I * ((θ + 2 * π : ℝ) : ℂ))
        = g θ * Complex.exp (-(ℓ : ℂ) * Complex.I * (θ : ℂ))
    rw [hg θ, exp_char_periodic]
  have h := hper.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at h
  exact h

/-- Only the two junction windows contribute to the integral. -/
lemma window_split (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) (ℓ : ℤ) :
    (∫ θ in (-π : ℝ)..π, fJ η θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ))
      = (∫ θ in (-(π/2) : ℝ)..(-(π/2) + π * η),
          fJ η θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ))
        + ∫ θ in (π/2 - π * η : ℝ)..(π/2),
            fJ η θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ) := by
  have hπ := Real.pi_pos
  set F : ℝ → ℂ := fun θ => fJ η θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ) with hFdef
  have hFc : Continuous F := by
    refine (continuous_fJ η).mul (Complex.continuous_exp.comp ?_)
    exact continuous_const.mul Complex.continuous_ofReal
  have hint : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b =>
    hFc.intervalIntegrable a b
  -- the five-piece split
  have h1 : (∫ θ in (-π : ℝ)..(-(π/2)), F θ) + ∫ θ in (-(π/2) : ℝ)..π, F θ
      = ∫ θ in (-π : ℝ)..π, F θ := integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have h2 : (∫ θ in (-(π/2) : ℝ)..(-(π/2) + π * η), F θ)
      + ∫ θ in (-(π/2) + π * η : ℝ)..π, F θ
      = ∫ θ in (-(π/2) : ℝ)..π, F θ := integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have h3 : (∫ θ in (-(π/2) + π * η : ℝ)..(π/2 - π * η), F θ)
      + ∫ θ in (π/2 - π * η : ℝ)..π, F θ
      = ∫ θ in (-(π/2) + π * η : ℝ)..π, F θ :=
    integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have h4 : (∫ θ in (π/2 - π * η : ℝ)..(π/2), F θ) + ∫ θ in (π/2 : ℝ)..π, F θ
      = ∫ θ in (π/2 - π * η : ℝ)..π, F θ :=
    integral_add_adjacent_intervals (hint _ _) (hint _ _)
  -- the three vanishing pieces
  have hz1 : (∫ θ in (-π : ℝ)..(-(π/2)), F θ) = 0 := by
    calc (∫ θ in (-π : ℝ)..(-(π/2)), F θ) = ∫ _ in (-π : ℝ)..(-(π/2)), (0:ℂ) := by
          refine intervalIntegral.integral_congr fun θ hθ => ?_
          rw [Set.uIcc_of_le (by linarith : (-π : ℝ) ≤ -(π/2))] at hθ
          have hcos : Real.cos θ ≤ 0 := by
            rw [← Real.cos_neg]
            exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [hθ.2])
              (by linarith [hθ.1])
          simp only [hFdef, fJ_eq_zero_of_nonpos hcos, zero_mul]
      _ = 0 := intervalIntegral.integral_zero
  have hz3 : (∫ θ in (-(π/2) + π * η : ℝ)..(π/2 - π * η), F θ) = 0 := by
    calc (∫ θ in (-(π/2) + π * η : ℝ)..(π/2 - π * η), F θ)
        = ∫ _ in (-(π/2) + π * η : ℝ)..(π/2 - π * η), (0:ℂ) := by
          refine intervalIntegral.integral_congr fun θ hθ => ?_
          rw [Set.uIcc_of_le (by nlinarith : (-(π/2) + π * η : ℝ) ≤ π/2 - π * η)] at hθ
          have habs : |θ| ≤ π/2 - π * η := abs_le.mpr ⟨by linarith [hθ.1], hθ.2⟩
          have hcos : 2 * η ≤ Real.cos θ := by
            have hm : Real.cos (π/2 - π * η) ≤ Real.cos |θ| :=
              Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ)
                (by nlinarith) habs
            rw [Real.cos_abs] at hm
            rw [Real.cos_pi_div_two_sub] at hm
            exact le_trans (two_eta_le_sin_pi_eta hη0 hη) hm
          simp only [hFdef, fJ_eq_zero_of_ge hη0 hcos, zero_mul]
      _ = 0 := intervalIntegral.integral_zero
  have hz5 : (∫ θ in (π/2 : ℝ)..π, F θ) = 0 := by
    calc (∫ θ in (π/2 : ℝ)..π, F θ) = ∫ _ in (π/2 : ℝ)..π, (0:ℂ) := by
          refine intervalIntegral.integral_congr fun θ hθ => ?_
          rw [Set.uIcc_of_le (by linarith : (π/2 : ℝ) ≤ π)] at hθ
          have hcos : Real.cos θ ≤ 0 :=
            Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2])
          simp only [hFdef, fJ_eq_zero_of_nonpos hcos, zero_mul]
      _ = 0 := intervalIntegral.integral_zero
  rw [← h1, hz1, zero_add, ← h2, ← h3, hz3, zero_add, ← h4, hz5, add_zero]

/-! ### The junction change of variables -/

/-- Right junction (`θ = π/2 − x`): the window integral is `e^{−iξπ/2}·J₊`. -/
lemma window_plus_eq (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) (ℓ : ℤ) :
    (∫ θ in (π/2 - π * η : ℝ)..(π/2), fJ η θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ))
      = Complex.exp (-(((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)
        * Jp η ((ℓ : ℝ) + 1/2) := by
  have hπ := Real.pi_pos
  -- the substituted integral
  have hsub := intervalIntegral.integral_comp_sub_left
    (f := fun θ : ℝ => fJ η θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ))
    (a := (0:ℝ)) (b := π * η) (π/2)
  rw [sub_zero] at hsub
  rw [← hsub]
  -- pointwise identification with the J₊ integrand
  rw [show Complex.exp (-(((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I) * Jp η ((ℓ : ℝ) + 1/2)
      = ∫ x in (0:ℝ)..(π * η),
          Complex.exp (-(((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)
            * ((Real.sqrt (Real.sin x) : ℂ) * (wJ η x : ℂ)
              * Complex.exp (Complex.I * (((ℓ : ℝ) + 1/2 : ℝ) : ℂ) * (x : ℂ))) from
    (intervalIntegral.integral_const_mul _ _).symm]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ π * η)] at hx
  have hxπη : x ≤ π * η := hx.2
  have hx0 : 0 ≤ x := hx.1
  have hmem : π/2 - x ∈ Set.Icc (-π) π := by
    constructor <;> nlinarith
  rw [window_integrand_fJ η ℓ hmem]
  have hsin0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by nlinarith)
  have hamp : hAmp (π/2 - x) = Real.sqrt (Real.sin x) := by
    rw [hAmp_eq_sqrt (by rw [Real.cos_pi_div_two_sub]; exact hsin0), Real.cos_pi_div_two_sub]
  have hcut : (1 : ℂ) - (wCol η (π/2 - x) : ℂ) = (wJ η x : ℂ) := by
    rw [show (1 : ℂ) - (wCol η (π/2 - x) : ℂ) = ((1 - wCol η (π/2 - x) : ℝ) : ℂ) by push_cast; ring,
      wJ_eq_sub_right_junction]
  have hphase : Complex.exp (-(((ℓ : ℂ) + 1/2) * ((π/2 - x : ℝ) : ℂ)) * Complex.I)
      = Complex.exp (-(((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)
        * Complex.exp (Complex.I * (((ℓ : ℝ) + 1/2 : ℝ) : ℂ) * (x : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hamp, hcut, hphase]
  ring

/-- Left junction (`θ = x − π/2`): the window integral is `e^{+iξπ/2}·J₋`. -/
lemma window_minus_eq (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) (ℓ : ℤ) :
    (∫ θ in (-(π/2) : ℝ)..(-(π/2) + π * η),
        fJ η θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ))
      = Complex.exp ((((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)
        * Jm η ((ℓ : ℝ) + 1/2) := by
  have hπ := Real.pi_pos
  have hsub := intervalIntegral.integral_comp_add_right
    (f := fun θ : ℝ => fJ η θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ))
    (a := (0:ℝ)) (b := π * η) (-(π/2))
  rw [zero_add] at hsub
  rw [show (-(π/2) + π * η : ℝ) = π * η + -(π/2) by ring, ← hsub]
  rw [show Complex.exp ((((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I) * Jm η ((ℓ : ℝ) + 1/2)
      = ∫ x in (0:ℝ)..(π * η),
          Complex.exp ((((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)
            * ((Real.sqrt (Real.sin x) : ℂ) * (wJ η x : ℂ)
              * Complex.exp (-(Complex.I * (((ℓ : ℝ) + 1/2 : ℝ) : ℂ) * (x : ℂ)))) from
    (intervalIntegral.integral_const_mul _ _).symm]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ π * η)] at hx
  have hxπη : x ≤ π * η := hx.2
  have hx0 : 0 ≤ x := hx.1
  have hmem : x + -(π/2) ∈ Set.Icc (-π) π := by
    constructor <;> nlinarith
  rw [window_integrand_fJ η ℓ hmem]
  have hsin0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by nlinarith)
  have hamp : hAmp (x + -(π/2)) = Real.sqrt (Real.sin x) := by
    have hc : Real.cos (x + -(π/2)) = Real.sin x := by
      rw [show x + -(π/2) = -(π/2 - x) by ring, Real.cos_neg, Real.cos_pi_div_two_sub]
    rw [hAmp_eq_sqrt (by rw [hc]; exact hsin0), hc]
  have hcut : (1 : ℂ) - (wCol η (x + -(π/2)) : ℂ) = (wJ η x : ℂ) := by
    rw [show (1 : ℂ) - (wCol η (x + -(π/2)) : ℂ)
        = ((1 - wCol η (x - π/2) : ℝ) : ℂ) by
        rw [show x + -(π/2) = x - π/2 by ring]; push_cast; ring,
      wJ_eq_sub_left_junction]
  have hphase : Complex.exp (-(((ℓ : ℂ) + 1/2) * ((x + -(π/2) : ℝ) : ℂ)) * Complex.I)
      = Complex.exp ((((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)
        * Complex.exp (-(Complex.I * (((ℓ : ℝ) + 1/2 : ℝ) : ℂ) * (x : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hamp, hcut, hphase]
  ring

/-- **The junction decomposition.**  For `0 < η ≤ 1/4` and every `ℓ`,
`fc (fJ η) ℓ = (2π)⁻¹·(e^{+iξπ/2}·J₋ + e^{−iξπ/2}·J₊)` with `ξ = ℓ + 1/2`. -/
theorem fc_fJ_eq (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) (ℓ : ℤ) :
    Parseval.fc (fJ η) ℓ
      = (2 * π : ℝ)⁻¹
        * (Complex.exp ((((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I) * Jm η ((ℓ : ℝ) + 1/2)
          + Complex.exp (-(((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)
            * Jp η ((ℓ : ℝ) + 1/2)) := by
  rw [fc_eq_window (fJ η) (fJ_periodic η) ℓ, window_split η hη0 hη ℓ,
    window_plus_eq η hη0 hη ℓ, window_minus_eq η hη0 hη ℓ]

/-! ### The head bound -/

/-- The one-sided integrals obey the constant-amplitude bound `‖J±‖ ≤ πη·√(πη)`. -/
lemma norm_Jp_le (η ξ : ℝ) (hη0 : 0 < η) : ‖Jp η ξ‖ ≤ π * η * Real.sqrt (π * η) := by
  have hπη : (0:ℝ) ≤ π * η := by positivity
  have hbd : ∀ x ∈ Set.Icc (0:ℝ) (π * η),
      ‖(Real.sqrt (Real.sin x) : ℂ) * (wJ η x : ℂ)
        * Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))‖ ≤ Real.sqrt (π * η) := by
    intro x hx
    have hs : Real.sqrt (Real.sin x) ≤ Real.sqrt (π * η) := by
      refine Real.sqrt_le_sqrt (le_trans ?_ hx.2)
      calc Real.sin x ≤ |Real.sin x| := le_abs_self _
        _ ≤ |x| := Real.abs_sin_le_abs
        _ = x := abs_of_nonneg hx.1
    have hexp1 : ‖Complex.exp (Complex.I * (ξ : ℂ) * (x : ℂ))‖ = 1 := by
      rw [show Complex.I * (ξ : ℂ) * (x : ℂ) = ((ξ * x : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, norm_mul, hexp1, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (wJ_mem η x).1]
    calc Real.sqrt (Real.sin x) * wJ η x ≤ Real.sqrt (π * η) * 1 :=
          mul_le_mul hs (wJ_mem η x).2 (wJ_mem η x).1 (Real.sqrt_nonneg _)
      _ = Real.sqrt (π * η) := mul_one _
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := Real.sqrt (π * η)) (fun x hx => hbd x (by
      rw [Set.uIoc_of_le hπη] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩))
  calc ‖Jp η ξ‖ ≤ Real.sqrt (π * η) * |π * η - 0| := h
    _ = π * η * Real.sqrt (π * η) := by rw [sub_zero, abs_of_nonneg hπη]; ring

lemma norm_Jm_le (η ξ : ℝ) (hη0 : 0 < η) : ‖Jm η ξ‖ ≤ π * η * Real.sqrt (π * η) := by
  have hπη : (0:ℝ) ≤ π * η := by positivity
  have hbd : ∀ x ∈ Set.Icc (0:ℝ) (π * η),
      ‖(Real.sqrt (Real.sin x) : ℂ) * (wJ η x : ℂ)
        * Complex.exp (-(Complex.I * (ξ : ℂ) * (x : ℂ)))‖ ≤ Real.sqrt (π * η) := by
    intro x hx
    have hs : Real.sqrt (Real.sin x) ≤ Real.sqrt (π * η) := by
      refine Real.sqrt_le_sqrt (le_trans ?_ hx.2)
      calc Real.sin x ≤ |Real.sin x| := le_abs_self _
        _ ≤ |x| := Real.abs_sin_le_abs
        _ = x := abs_of_nonneg hx.1
    have hexp1 : ‖Complex.exp (-(Complex.I * (ξ : ℂ) * (x : ℂ)))‖ = 1 := by
      rw [show -(Complex.I * (ξ : ℂ) * (x : ℂ)) = ((-(ξ * x) : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, norm_mul, hexp1, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (wJ_mem η x).1]
    calc Real.sqrt (Real.sin x) * wJ η x ≤ Real.sqrt (π * η) * 1 :=
          mul_le_mul hs (wJ_mem η x).2 (wJ_mem η x).1 (Real.sqrt_nonneg _)
      _ = Real.sqrt (π * η) := mul_one _
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := Real.sqrt (π * η)) (fun x hx => hbd x (by
      rw [Set.uIoc_of_le hπη] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩))
  calc ‖Jm η ξ‖ ≤ Real.sqrt (π * η) * |π * η - 0| := h
    _ = π * η * Real.sqrt (π * η) := by rw [sub_zero, abs_of_nonneg hπη]; ring

/-- **The head bound** — `‖fc (fJ η) ℓ‖ ≤ 2·η·√η` for every `ℓ` (`0 < η ≤ 1/4`). -/
theorem norm_fc_fJ_le_head (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) (ℓ : ℤ) :
    ‖Parseval.fc (fJ η) ℓ‖ ≤ 2 * η * Real.sqrt η := by
  have hπ := Real.pi_pos
  have hπ2 : π < 3.15 := Real.pi_lt_d2
  rw [fc_fJ_eq η hη0 hη ℓ]
  have hpre1 : ‖Complex.exp ((((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)‖ = 1 := by
    rw [show (((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I
        = (((((ℓ:ℝ) + 1/2) * (π/2) : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hpre2 : ‖Complex.exp (-(((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)‖ = 1 := by
    rw [show -(((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I
        = ((-(((ℓ:ℝ) + 1/2) * (π/2)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hJ : ‖Complex.exp ((((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I) * Jm η ((ℓ : ℝ) + 1/2)
      + Complex.exp (-(((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I) * Jp η ((ℓ : ℝ) + 1/2)‖
      ≤ 2 * (π * η * Real.sqrt (π * η)) := by
    calc ‖_ + _‖ ≤ ‖Complex.exp ((((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)
            * Jm η ((ℓ : ℝ) + 1/2)‖
          + ‖Complex.exp (-(((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)
            * Jp η ((ℓ : ℝ) + 1/2)‖ := norm_add_le _ _
      _ = ‖Jm η ((ℓ : ℝ) + 1/2)‖ + ‖Jp η ((ℓ : ℝ) + 1/2)‖ := by
          rw [norm_mul, norm_mul, hpre1, hpre2, one_mul, one_mul]
      _ ≤ π * η * Real.sqrt (π * η) + π * η * Real.sqrt (π * η) :=
          add_le_add (norm_Jm_le η _ hη0) (norm_Jp_le η _ hη0)
      _ = 2 * (π * η * Real.sqrt (π * η)) := by ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹)]
  calc (2 * π)⁻¹ * ‖_ + _‖ ≤ (2 * π)⁻¹ * (2 * (π * η * Real.sqrt (π * η))) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = η * Real.sqrt (π * η) := by field_simp
    _ ≤ η * (2 * Real.sqrt η) := by
        refine mul_le_mul_of_nonneg_left ?_ hη0.le
        rw [show π * η = π * η from rfl, Real.sqrt_mul hπ.le,
          show (2 : ℝ) * Real.sqrt η = Real.sqrt 4 * Real.sqrt η by
            rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]]
        exact mul_le_mul_of_nonneg_right
          (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg η)
    _ = 2 * η * Real.sqrt η := by ring

end KsIndex.ArcJunction
