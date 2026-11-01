module

/-
# Radial Jacobi modes, energy identities and regular-solution classification

For `k ≥ 2`, set `κ = k - 1`. The integer-frequency radial solution is
`uRad k ℓ r = r^ℓ * ((ℓ + κ) + (ℓ - κ) * r^(2k-2)) / (1 + r^(2k-2))`.
The profile and its derivatives are rational functions of `r`; `uRad_ode`
proves `(r u')' = ℓ² u/r - r Vrad u` away from zero. The final lemmas
`uRad_exp_eq` and `Vrad_exp_eq` identify the solution and potential with
the paper's hyperbolic expressions under `r = exp t`.

For positive integer frequency and a real function with derivative on
`[0,1]`, continuous derivative there and `f 0 = 0`, `qMode_eq` proves

`∫_0^1 (r f'² + ℓ² f²/r - r Vrad f²)
  = ∫_0^1 Rm + sigma k ℓ * f(1)²`,

where `Rm` is nonnegative and `sigma k ℓ = (ℓ² - κ²) / ℓ`.
`qMode_ge` gives the resulting lower bound by the boundary term. At zero
frequency, `qMode_zero_nonneg` instead assumes `f 1 = 0`; its proof
controls the boundary term where the profile
`κ * (1 - r^(2k-2)) / (1 + r^(2k-2))` vanishes. Splitting into real and
imaginary parts gives the two complex-valued inequalities.

`eq_const_mul_uRad` classifies real integer-mode solutions on `(0,1)`
whose value and specified derivative extend continuously to `[0,1)`:
they are constant multiples of `uRad` on `[0,1)`. This is a centre-regular
counterpart of the paper's ODE proposition, not its full arbitrary-real-
frequency bounded-cylinder statement. `FiniteEnergyRadialClassification`
supplies the integer-mode result used for weak H¹ solutions.
-/
public import KsIndexLean.Surface

@[expose] public section


noncomputable section

namespace KsIndex.Radial

open Real Set Filter Topology MeasureTheory intervalIntegral

/-- `κ = k − 1`. -/
def kap (k : ℕ) : ℝ := (k : ℝ) - 1

/-- The profile `g(r) = ((ℓ+κ) + (ℓ−κ) r^{2k−2})/(r^{2k−2} + 1)`; the mode is `u = r^ℓ g`. -/
def gRad (k ℓ : ℕ) (r : ℝ) : ℝ :=
  (((ℓ : ℝ) + kap k) + ((ℓ : ℝ) - kap k) * r ^ (2 * k - 2)) / (r ^ (2 * k - 2) + 1)

/-- `g'(r) = −(2k−2)² r^{2k−3}/(r^{2k−2}+1)²` (independent of `ℓ`). -/
def gD (k : ℕ) (r : ℝ) : ℝ :=
  -(2 * (k : ℝ) - 2) ^ 2 * r ^ (2 * k - 3) / (r ^ (2 * k - 2) + 1) ^ 2

/-- `g''(r)`. -/
def gDD (k : ℕ) (r : ℝ) : ℝ :=
  -(2 * (k : ℝ) - 2) ^ 2 * r ^ (2 * k - 4) *
      ((2 * (k : ℝ) - 3) - (2 * (k : ℝ) - 1) * r ^ (2 * k - 2)) / (r ^ (2 * k - 2) + 1) ^ 3

/-- The radial Jacobi potential `V(r) = 8κ² r^{2k−4}/(r^{2k−2}+1)²`
(`= Surface.potV k w` at `r = ‖w‖`, see `potV_eq_Vrad`). -/
def Vrad (k : ℕ) (r : ℝ) : ℝ := 8 * kap k ^ 2 * r ^ (2 * k - 4) / (r ^ (2 * k - 2) + 1) ^ 2

/-- The mode `u_{k,ℓ}` in the radial variable: `uRad k ℓ r = r^ℓ g(r)`. -/
def uRad (k ℓ : ℕ) (r : ℝ) : ℝ := r ^ ℓ * gRad k ℓ r

/-- `u'(r)`, valid for `r ≠ 0`: `ℓ u/r + r^ℓ g'`. -/
def uD (k ℓ : ℕ) (r : ℝ) : ℝ := (ℓ : ℝ) * uRad k ℓ r / r + r ^ ℓ * gD k r

/-- The DtN symbol `σ_k(ℓ) = (ℓ² − κ²)/ℓ` ([ksindexi] `DtN-momentum`), for `ℓ ≥ 1`. -/
def sigma (k ℓ : ℕ) : ℝ := ((ℓ : ℝ) ^ 2 - kap k ^ 2) / ℓ

lemma potV_eq_Vrad (k : ℕ) (w : ℂ) : Surface.potV k w = Vrad k ‖w‖ := rfl

/-! ### Elementary facts -/

lemma pow_even_nonneg (k : ℕ) (r : ℝ) : 0 ≤ r ^ (2 * k - 2) := by
  rw [show 2 * k - 2 = 2 * (k - 1) by omega, pow_mul]; positivity

lemma denom_pos (k : ℕ) (r : ℝ) : 0 < r ^ (2 * k - 2) + 1 := by
  linarith [pow_even_nonneg k r]

lemma kap_pos (hk : 2 ≤ k) : 0 < kap k := by
  unfold kap; have : (2 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

lemma cast_two_k_sub_two (hk : 2 ≤ k) : ((2 * k - 2 : ℕ) : ℝ) = 2 * (k : ℝ) - 2 := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring

lemma cast_two_k_sub_three (hk : 2 ≤ k) : ((2 * k - 3 : ℕ) : ℝ) = 2 * (k : ℝ) - 3 := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring

/-! ### Derivatives of the profile -/

lemma gRad_hasDerivAt (hk : 2 ≤ k) (ℓ : ℕ) (r : ℝ) : HasDerivAt (gRad k ℓ) (gD k r) r := by
  have hden : r ^ (2 * k - 2) + 1 ≠ 0 := (denom_pos k r).ne'
  have h1 : HasDerivAt (fun r : ℝ => ((ℓ : ℝ) + kap k) + ((ℓ : ℝ) - kap k) * r ^ (2 * k - 2))
      (((ℓ : ℝ) - kap k) * (((2 * k - 2 : ℕ) : ℝ) * r ^ (2 * k - 2 - 1))) r :=
    ((hasDerivAt_pow _ r).const_mul _).const_add _
  have h2 : HasDerivAt (fun r : ℝ => r ^ (2 * k - 2) + 1)
      (((2 * k - 2 : ℕ) : ℝ) * r ^ (2 * k - 2 - 1)) r :=
    (hasDerivAt_pow _ r).add_const _
  refine (h1.div h2 hden).congr_deriv ?_
  rw [gD, show 2 * k - 2 - 1 = 2 * k - 3 by omega, cast_two_k_sub_two hk, kap]
  field_simp
  ring

lemma gD_hasDerivAt (hk : 2 ≤ k) (r : ℝ) : HasDerivAt (gD k) (gDD k r) r := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 2 := ⟨k - 2, by omega⟩
  have hden : (r ^ (2 * (q + 2) - 2) + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (denom_pos _ r).ne'
  have h1 : HasDerivAt (fun r : ℝ => -(2 * ((q + 2 : ℕ) : ℝ) - 2) ^ 2 * r ^ (2 * (q + 2) - 3))
      (-(2 * ((q + 2 : ℕ) : ℝ) - 2) ^ 2 *
        (((2 * (q + 2) - 3 : ℕ) : ℝ) * r ^ (2 * (q + 2) - 3 - 1))) r :=
    (hasDerivAt_pow _ r).const_mul _
  have h2 : HasDerivAt (fun r : ℝ => (r ^ (2 * (q + 2) - 2) + 1) ^ 2)
      (↑(2 : ℕ) * (r ^ (2 * (q + 2) - 2) + 1) ^ (2 - 1) *
        (((2 * (q + 2) - 2 : ℕ) : ℝ) * r ^ (2 * (q + 2) - 2 - 1))) r :=
    ((hasDerivAt_pow _ r).add_const _).pow 2
  refine (h1.div h2 hden).congr_deriv ?_
  rw [gDD]
  have e1 : 2 * (q + 2) - 2 = 2 * q + 2 := by omega
  have e2 : 2 * (q + 2) - 3 = 2 * q + 1 := by omega
  have e3 : 2 * (q + 2) - 4 = 2 * q := by omega
  have e4 : 2 * (q + 2) - 3 - 1 = 2 * q := by omega
  have e5 : 2 * (q + 2) - 2 - 1 = 2 * q + 1 := by omega
  simp only [e1, e2, e3, e4, e5]
  have hne : r ^ (2 * q + 2) + 1 ≠ 0 := by rw [← e1]; exact (denom_pos _ r).ne'
  push_cast
  field_simp
  ring

/-- The radial ODE satisfied by the profile `g`:
`(2ℓ+1) r g' + r² g'' + r² V g = 0` (equivalent to `(r u')' = ℓ² u/r − r V u` for `u = r^ℓ g`). -/
lemma gRad_ode (hk : 2 ≤ k) (ℓ : ℕ) (r : ℝ) :
    (2 * (ℓ : ℝ) + 1) * r * gD k r + r ^ 2 * gDD k r + r ^ 2 * Vrad k r * gRad k ℓ r = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, k = q + 2 := ⟨k - 2, by omega⟩
  unfold gD gDD Vrad gRad kap
  have e1 : 2 * (q + 2) - 2 = 2 * q + 2 := by omega
  have e2 : 2 * (q + 2) - 3 = 2 * q + 1 := by omega
  have e3 : 2 * (q + 2) - 4 = 2 * q := by omega
  simp only [e1, e2, e3]
  have hne : r ^ (2 * q + 2) + 1 ≠ 0 := by rw [← e1]; exact (denom_pos _ r).ne'
  push_cast
  field_simp
  ring

/-- `g''` expressed through `g'` and `g` via the ODE (for `r ≠ 0`). -/
lemma gDD_eq (hk : 2 ≤ k) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0) :
    gDD k r = -((2 * (ℓ : ℝ) + 1) * r * gD k r + r ^ 2 * Vrad k r * gRad k ℓ r) / r ^ 2 := by
  have h := gRad_ode hk ℓ r
  rw [eq_div_iff (pow_ne_zero 2 hr)]
  linear_combination h

lemma cast_mul_pow_pred (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0) :
    (ℓ : ℝ) * r ^ (ℓ - 1) = ℓ * r ^ ℓ / r := by
  cases ℓ with
  | zero => simp
  | succ n =>
    rw [Nat.cast_succ]
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp

lemma uRad_hasDerivAt (hk : 2 ≤ k) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (uRad k ℓ) (uD k ℓ r) r := by
  refine ((hasDerivAt_pow ℓ r).mul (gRad_hasDerivAt hk ℓ r)).congr_deriv ?_
  rw [uD, uRad, cast_mul_pow_pred ℓ hr]
  ring

/-- **The explicit mode solves the mode-`ℓ` equation** `(r u')' = ℓ² u/r − r V u` on `r ≠ 0`
([ksindexi] Prop `ode`, existence half, in the radial variable). -/
lemma uRad_ode (hk : 2 ≤ k) (ℓ : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun r => r * uD k ℓ r)
      ((ℓ : ℝ) ^ 2 * uRad k ℓ r / r - r * Vrad k r * uRad k ℓ r) r := by
  have hfun : (fun r => (ℓ : ℝ) * uRad k ℓ r + r ^ (ℓ + 1) * gD k r) =ᶠ[𝓝 r]
      (fun r => r * uD k ℓ r) := by
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx
    rw [uD]
    field_simp
    ring
  have h := ((uRad_hasDerivAt hk ℓ hr).const_mul (ℓ : ℝ)).add
    ((hasDerivAt_pow (ℓ + 1) r).mul (gD_hasDerivAt hk r))
  refine (h.congr_of_eventuallyEq hfun.symm).congr_deriv ?_
  rw [gDD_eq hk ℓ hr, uD, uRad]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-! ### Boundary values and positivity -/

lemma gRad_one (_hk : 2 ≤ k) (ℓ : ℕ) : gRad k ℓ 1 = ℓ := by
  unfold gRad; simp; ring

lemma gD_one (_hk : 2 ≤ k) : gD k 1 = -(kap k) ^ 2 := by
  unfold gD kap; simp; ring

lemma uRad_one (hk : 2 ≤ k) (ℓ : ℕ) : uRad k ℓ 1 = ℓ := by
  rw [uRad, one_pow, one_mul, gRad_one hk]

lemma gRad_zero (_hk : 2 ≤ k) (ℓ : ℕ) : gRad k ℓ 0 = ℓ + kap k := by
  unfold gRad
  rw [zero_pow (by omega)]; simp

lemma gD_zero (_hk : 2 ≤ k) : gD k 0 = 0 := by
  unfold gD
  rw [zero_pow (by omega)]; simp

lemma gRad_pos (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 < gRad k ℓ r := by
  unfold gRad kap
  have hs0 : 0 ≤ r ^ (2 * k - 2) := pow_nonneg hr0 _
  have hs1 : r ^ (2 * k - 2) ≤ 1 := pow_le_one₀ hr0 hr1
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  apply div_pos _ (by linarith)
  nlinarith

lemma gRad_zero_pos (hk : 2 ≤ k) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : 0 < gRad k 0 r := by
  unfold gRad kap
  have hs0 : 0 ≤ r ^ (2 * k - 2) := pow_nonneg hr0 _
  have hs1 : r ^ (2 * k - 2) < 1 := pow_lt_one₀ hr0 hr1 (by omega)
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  apply div_pos _ (by linarith)
  push_cast
  nlinarith

lemma gRad_zero_one (hk : 2 ≤ k) : gRad k 0 1 = 0 := by
  rw [gRad_one hk]; simp

/-! ### The ground-state identity, pointwise form -/

/-- The mode-`ℓ` integrand `r f'² + ℓ² f²/r − r V f²` (the per-mode Jacobi form density in the
radial variable; `lhs` for "left-hand side"). -/
def lhs (k ℓ : ℕ) (f f' : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * f' r ^ 2 + (ℓ : ℝ) ^ 2 * (f r ^ 2 / r) - r * Vrad k r * f r ^ 2

/-- `W = r g f' − (ℓ g + r g') f` — up to the factor `r^{1−ℓ}`, the Wronskian `u f' − f u'` of
`f` with the mode `u = r^ℓ g`. -/
def Wg (k ℓ : ℕ) (f f' : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * gRad k ℓ r * f' r - ((ℓ : ℝ) * gRad k ℓ r + r * gD k r) * f r

/-- The nonnegative remainder `W²/(r g²)` (`= r u² ((f/u)')²`). -/
def Rm (k ℓ : ℕ) (f f' : ℝ → ℝ) (r : ℝ) : ℝ := Wg k ℓ f f' r ^ 2 / (r * gRad k ℓ r ^ 2)

/-- The boundary function `B = ℓ f² + r (g'/g) f²` (`= r (u'/u) f²`). -/
def Bd (k ℓ : ℕ) (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  (ℓ : ℝ) * f r ^ 2 + r * gD k r * f r ^ 2 / gRad k ℓ r

lemma Rm_nonneg (k ℓ : ℕ) (f f' : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ Rm k ℓ f f' r :=
  div_nonneg (sq_nonneg _) (mul_nonneg hr (sq_nonneg _))

/-- **Pointwise ground-state identity**: `B' = lhs − Rm` wherever `r ≠ 0`, `g(r) ≠ 0`. -/
lemma Bd_hasDerivAt (hk : 2 ≤ k) (ℓ : ℕ) {f f' : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0)
    (hg : gRad k ℓ r ≠ 0) (hf : HasDerivAt f (f' r) r) :
    HasDerivAt (Bd k ℓ f) (lhs k ℓ f f' r - Rm k ℓ f f' r) r := by
  have h1 : HasDerivAt (fun r => (ℓ : ℝ) * f r ^ 2)
      ((ℓ : ℝ) * (↑(2 : ℕ) * f r ^ (2 - 1) * f' r)) r := (hf.pow 2).const_mul _
  have h2 := (((hasDerivAt_id' r).mul (gD_hasDerivAt hk r)).mul (hf.pow 2)).div
    (gRad_hasDerivAt hk ℓ r) hg
  refine (h1.add h2).congr_deriv ?_
  rw [lhs, Rm, Wg, gDD_eq hk ℓ hr]
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.mul_apply, Pi.pow_apply]
  field_simp
  ring

/-! ### The ground-state identity, integrated: `ℓ ≥ 1` -/

/-- `f²/r` is continuous on `[0,1]` when `f ∈ C¹` and `f(0) = 0`. -/
lemma continuousOn_sq_div {f f' : ℝ → ℝ} (hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt f (f' r) r)
    (hf0 : f 0 = 0) : ContinuousOn (fun r => f r ^ 2 / r) (Icc 0 1) := by
  intro r hr
  rcases eq_or_lt_of_le hr.1 with h0 | h0
  · subst h0
    rw [← continuousWithinAt_sdiff_self]
    have hslope : Tendsto (fun x => f x / x) (𝓝[≠] (0:ℝ)) (𝓝 (f' 0)) := by
      have := hasDerivAt_iff_tendsto_slope.mp (hf 0 (by simp))
      refine this.congr (fun x => ?_)
      rw [slope_def_field, hf0]; simp
    have hf0' : Tendsto f (𝓝[≠] (0:ℝ)) (𝓝 0) := by
      have := (hf 0 (by simp)).continuousAt.tendsto
      rw [hf0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hmono : 𝓝[Icc (0:ℝ) 1 \ {0}] 0 ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (fun x hx => hx.2)
    have key : Tendsto (fun x => f x / x * f x) (𝓝[Icc (0:ℝ) 1 \ {0}] 0) (𝓝 (f' 0 * 0)) :=
      (hslope.mono_left hmono).mul (hf0'.mono_left hmono)
    rw [mul_zero] at key
    change Tendsto (fun r => f r ^ 2 / r) (𝓝[Icc (0:ℝ) 1 \ {0}] 0) (𝓝 ((fun r => f r ^ 2 / r) 0))
    have h00 : (fun r => f r ^ 2 / r) 0 = 0 := by simp [hf0]
    rw [h00]
    exact key.congr (fun x => by ring)
  · exact (((hf r hr).continuousAt.pow 2).div continuousAt_id h0.ne').continuousWithinAt

lemma continuous_Vrad (k : ℕ) : Continuous (Vrad k) := by
  unfold Vrad
  exact Continuous.div (by fun_prop) (by fun_prop) (fun r => pow_ne_zero 2 (denom_pos k r).ne')

lemma lhs_continuousOn_aux {k ℓ : ℕ} {f f' : ℝ → ℝ} (hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt f (f' r) r)
    (hf' : ContinuousOn f' (Icc 0 1))
    (hdiv : ContinuousOn (fun r => (ℓ : ℝ) ^ 2 * (f r ^ 2 / r)) (Icc 0 1)) :
    ContinuousOn (lhs k ℓ f f') (Icc 0 1) := by
  have hfc : ContinuousOn f (Icc 0 1) := fun r hr => (hf r hr).continuousAt.continuousWithinAt
  exact ((continuousOn_id.mul (hf'.pow 2)).add hdiv).sub
    ((continuousOn_id.mul (continuous_Vrad k).continuousOn).mul (hfc.pow 2))

lemma lhs_continuousOn {k ℓ : ℕ} (hℓ : 1 ≤ ℓ) {f f' : ℝ → ℝ}
    (hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt f (f' r) r) (hf' : ContinuousOn f' (Icc 0 1))
    (hf0 : f 0 = 0) : ContinuousOn (lhs k ℓ f f') (Icc 0 1) :=
  lhs_continuousOn_aux hf hf' (continuousOn_const.mul (continuousOn_sq_div hf hf0))

lemma lhs_zero_eq (k : ℕ) (f f' : ℝ → ℝ) :
    lhs k 0 f f' = fun r => r * f' r ^ 2 - r * Vrad k r * f r ^ 2 := by
  funext r; simp [lhs]

lemma lhs_zero_continuousOn {k : ℕ} {f f' : ℝ → ℝ}
    (hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt f (f' r) r) (hf' : ContinuousOn f' (Icc 0 1)) :
    ContinuousOn (lhs k 0 f f') (Icc 0 1) :=
  lhs_continuousOn_aux hf hf'
    (by simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 1)))

lemma Bd_continuousAt (hk : 2 ≤ k) (ℓ : ℕ) {f f' : ℝ → ℝ} {r : ℝ} (hg : gRad k ℓ r ≠ 0)
    (hf : HasDerivAt f (f' r) r) : ContinuousAt (Bd k ℓ f) r :=
  (continuousAt_const.mul (hf.continuousAt.pow 2)).add
    (((continuousAt_id.mul (gD_hasDerivAt hk r).continuousAt).mul (hf.continuousAt.pow 2)).div
      (gRad_hasDerivAt hk ℓ r).continuousAt hg)

lemma Bd_zero_eq (k ℓ : ℕ) {f : ℝ → ℝ} (hf0 : f 0 = 0) : Bd k ℓ f 0 = 0 := by
  simp [Bd, hf0]

lemma Bd_one_eq (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) (f : ℝ → ℝ) : Bd k ℓ f 1 = sigma k ℓ * f 1 ^ 2 := by
  rw [Bd, sigma, gRad_one hk, gD_one hk]
  have : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
  field_simp
  ring

/-- The FTC step shared by `qMode_eq` and `qMode_zero_nonneg`: if `B` is continuous on `[0,1]`
and `g ≠ 0` on `(0,1)`, then `∫_0^1 lhs = ∫_0^1 Rm + B(1) − B(0)`, and `Rm` is integrable. -/
lemma qMode_ftc (hk : 2 ≤ k) (ℓ : ℕ) {f f' : ℝ → ℝ}
    (hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt f (f' r) r)
    (hlc : ContinuousOn (lhs k ℓ f f') (Icc 0 1))
    (hg : ∀ r ∈ Ioo (0:ℝ) 1, gRad k ℓ r ≠ 0)
    (hBc : ContinuousOn (Bd k ℓ f) (Icc 0 1)) :
    IntervalIntegrable (Rm k ℓ f f') volume 0 1 ∧
      ∫ r in (0:ℝ)..1, lhs k ℓ f f' r =
        (∫ r in (0:ℝ)..1, Rm k ℓ f f' r) + Bd k ℓ f 1 - Bd k ℓ f 0 := by
  have hlint : IntervalIntegrable (lhs k ℓ f f') volume 0 1 :=
    hlc.intervalIntegrable_of_Icc zero_le_one
  set P : ℝ → ℝ := fun x => (∫ t in (0:ℝ)..x, lhs k ℓ f f' t) - Bd k ℓ f x with hP
  have hPcont : ContinuousOn P (Icc 0 1) := by
    refine ContinuousOn.sub ?_ hBc
    have := intervalIntegral.continuousOn_primitive_interval
      (μ := volume) (f := lhs k ℓ f f') (a := 0) (b := 1)
      (by rw [uIcc_of_le zero_le_one]; exact hlc.integrableOn_Icc)
    rwa [uIcc_of_le zero_le_one] at this
  have hPderiv : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt P (Rm k ℓ f f' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun u => ∫ t in (0:ℝ)..u, lhs k ℓ f f' t) (lhs k ℓ f f' x) x :=
      intervalIntegral.integral_hasDerivAt_right
        (hlint.mono_set (by
          rw [uIcc_of_le hx.1.le, uIcc_of_le zero_le_one]
          exact Icc_subset_Icc le_rfl hx.2.le))
        ((hlc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx)
        (hlc.continuousAt (Icc_mem_nhds hx.1 hx.2))
    have h2 := Bd_hasDerivAt hk ℓ hx.1.ne' (hg x hx) (hf x (Ioo_subset_Icc_self hx))
    exact (h1.sub h2).congr_deriv (by ring)
  have hRnn : ∀ x ∈ Ioo (0:ℝ) 1, 0 ≤ Rm k ℓ f f' x := fun x hx => Rm_nonneg k ℓ f f' hx.1.le
  have hRint : IntervalIntegrable (Rm k ℓ f f') volume 0 1 := by
    refine intervalIntegrable_deriv_of_nonneg (g := P) ?_ ?_ ?_
    · rwa [uIcc_of_le zero_le_one]
    · simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using hPderiv
    · simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one] using hRnn
  refine ⟨hRint, ?_⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hPcont
    (fun x hx => (hPderiv x hx).hasDerivWithinAt) hRint
  rw [hFTC]
  simp only [hP, intervalIntegral.integral_same]
  ring

/-- **Ground-state identity, mode `ℓ ≥ 1`** (`f ∈ C¹[0,1]`, `f(0) = 0`):
`∫_0^1 (r f'² + ℓ² f²/r − r V f²) dr = ∫_0^1 Rm + σ_k(ℓ) f(1)²`, with `Rm ≥ 0`. -/
theorem qMode_eq (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) {f f' : ℝ → ℝ}
    (hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt f (f' r) r) (hf' : ContinuousOn f' (Icc 0 1))
    (hf0 : f 0 = 0) :
    ∫ r in (0:ℝ)..1, lhs k ℓ f f' r =
      (∫ r in (0:ℝ)..1, Rm k ℓ f f' r) + sigma k ℓ * f 1 ^ 2 := by
  have hg : ∀ r ∈ Icc (0:ℝ) 1, gRad k ℓ r ≠ 0 := fun r hr => (gRad_pos hk hℓ hr.1 hr.2).ne'
  have hBc : ContinuousOn (Bd k ℓ f) (Icc 0 1) :=
    fun r hr => (Bd_continuousAt hk ℓ (hg r hr) (hf r hr)).continuousWithinAt
  obtain ⟨-, h⟩ := qMode_ftc hk ℓ hf (lhs_continuousOn hℓ hf hf' hf0)
    (fun r hr => hg r (Ioo_subset_Icc_self hr)) hBc
  rw [h, Bd_zero_eq k ℓ hf0, Bd_one_eq hk hℓ]
  ring

lemma integral_Rm_nonneg (k ℓ : ℕ) (f f' : ℝ → ℝ) : 0 ≤ ∫ r in (0:ℝ)..1, Rm k ℓ f f' r :=
  intervalIntegral.integral_nonneg zero_le_one (fun u hu => Rm_nonneg k ℓ f f' hu.1)

/-- **The mode form dominates the DtN form of the trace**: `σ_k(ℓ) f(1)² ≤ ∫_0^1 lhs`. -/
theorem qMode_ge (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) {f f' : ℝ → ℝ}
    (hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt f (f' r) r) (hf' : ContinuousOn f' (Icc 0 1))
    (hf0 : f 0 = 0) :
    sigma k ℓ * f 1 ^ 2 ≤ ∫ r in (0:ℝ)..1, lhs k ℓ f f' r := by
  rw [qMode_eq hk hℓ hf hf' hf0]
  linarith [integral_Rm_nonneg k ℓ f f']

/-! ### Mode `ℓ = 0`, Dirichlet: nonnegativity -/

lemma gRad_zero_ge (hk : 2 ≤ k) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    kap k * (1 - r) / 2 ≤ gRad k 0 r := by
  unfold gRad
  have hs0 : 0 ≤ r ^ (2 * k - 2) := pow_nonneg hr0 _
  have hsr : r ^ (2 * k - 2) ≤ r := by
    calc r ^ (2 * k - 2) ≤ r ^ 1 := pow_le_pow_of_le_one hr0 hr1 (by omega)
      _ = r := pow_one r
  have hκ := kap_pos hk
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  push_cast
  nlinarith [mul_nonneg hκ.le (sub_nonneg.2 hsr),
    mul_nonneg (mul_nonneg hκ.le (sub_nonneg.2 hsr)) hs0,
    mul_nonneg hκ.le (sq_nonneg (1 - r ^ (2 * k - 2)))]

lemma abs_gD_le (hk : 2 ≤ k) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |gD k r| ≤ (2 * (k : ℝ) - 2) ^ 2 := by
  unfold gD
  rw [abs_div, abs_of_pos (pow_pos (denom_pos k r) 2), abs_mul, abs_neg,
    abs_of_nonneg (sq_nonneg _), abs_of_nonneg (pow_nonneg hr0 _),
    div_le_iff₀ (pow_pos (denom_pos k r) 2)]
  have h1 : r ^ (2 * k - 3) ≤ 1 := pow_le_one₀ hr0 hr1
  have h2 : 1 ≤ (r ^ (2 * k - 2) + 1) ^ 2 := by nlinarith [pow_even_nonneg k r]
  nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (2 * (k : ℝ) - 2)),
    mul_le_mul_of_nonneg_left h2 (sq_nonneg (2 * (k : ℝ) - 2))]

/-- **Dirichlet mode `ℓ = 0` is nonnegative** (`f ∈ C¹[0,1]`, `f(1) = 0`):
`0 ≤ ∫_0^1 (r f'² − r V f²) dr`.  The ground state `u_{k,0}` vanishes at `r = 1`, so the
boundary function `B = r (g'/g) f²` has a removable singularity there, handled by the bound
`|B| ≤ C (1 − r)`. -/
theorem qMode_zero_nonneg (hk : 2 ≤ k) {f f' : ℝ → ℝ}
    (hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt f (f' r) r) (hf' : ContinuousOn f' (Icc 0 1))
    (hf1 : f 1 = 0) : 0 ≤ ∫ r in (0:ℝ)..1, lhs k 0 f f' r := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf'
  have hfb : ∀ r ∈ Icc (0:ℝ) 1, |f r| ≤ M * (1 - r) := by
    intro r hr
    have := norm_image_sub_le_of_norm_deriv_le_segment' (a := r) (b := 1) (f := f) (f' := f')
      (C := M) (fun x hx => (hf x ⟨hr.1.trans hx.1, hx.2⟩).hasDerivWithinAt)
      (fun x hx => hM x ⟨hr.1.trans hx.1, hx.2.le⟩) 1 (right_mem_Icc.2 hr.2)
    rwa [hf1, zero_sub, norm_neg, Real.norm_eq_abs] at this
  have hκ := kap_pos hk
  set C : ℝ := 2 * (2 * (k : ℝ) - 2) ^ 2 * M ^ 2 / kap k with hC
  have hC0 : 0 ≤ C := div_nonneg (by positivity) hκ.le
  have hbound : ∀ r ∈ Icc (0:ℝ) 1, |Bd k 0 f r| ≤ C * (1 - r) := by
    intro r hr
    rcases eq_or_lt_of_le hr.2 with h1 | h1
    · subst h1; simp [Bd, hf1]
    · have hg := gRad_zero_pos hk hr.1 h1
      have hgl := gRad_zero_ge hk hr.1 hr.2
      have hfr := hfb r hr
      have hgd := abs_gD_le hk hr.1 hr.2
      have h1r : 0 < 1 - r := by linarith
      have hB : Bd k 0 f r = r * gD k r * f r ^ 2 / gRad k 0 r := by simp [Bd]
      rw [hB, abs_div, abs_of_pos hg, abs_mul, abs_mul, abs_of_nonneg hr.1,
        abs_of_nonneg (sq_nonneg (f r)), div_le_iff₀ hg]
      have hf2 : f r ^ 2 ≤ (M * (1 - r)) ^ 2 := by
        rw [← sq_abs (f r)]; exact pow_le_pow_left₀ (abs_nonneg _) hfr 2
      calc r * |gD k r| * f r ^ 2 ≤ 1 * (2 * (k : ℝ) - 2) ^ 2 * (M * (1 - r)) ^ 2 :=
            mul_le_mul (mul_le_mul hr.2 hgd (abs_nonneg _) zero_le_one) hf2 (sq_nonneg _)
              (by positivity)
        _ = C * (1 - r) * (kap k * (1 - r) / 2) := by rw [hC]; field_simp; try ring
        _ ≤ C * (1 - r) * gRad k 0 r :=
            mul_le_mul_of_nonneg_left hgl (mul_nonneg hC0 h1r.le)
  have hBc : ContinuousOn (Bd k 0 f) (Icc 0 1) := by
    intro r hr
    rcases eq_or_lt_of_le hr.2 with h1 | h1
    · subst h1
      have hB1 : Bd k 0 f 1 = 0 := by simp [Bd, hf1]
      change Tendsto (Bd k 0 f) (𝓝[Icc 0 1] 1) (𝓝 (Bd k 0 f 1))
      rw [hB1]
      refine squeeze_zero_norm' (a := fun x => C * (1 - x))
        (eventually_nhdsWithin_of_forall (fun x hx => ?_)) ?_
      · simpa only [Real.norm_eq_abs] using hbound x hx
      · have : Tendsto (fun x : ℝ => C * (1 - x)) (𝓝 1) (𝓝 (C * (1 - 1))) :=
          (continuous_const.mul (continuous_const.sub continuous_id)).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
    · exact (Bd_continuousAt hk 0 (gRad_zero_pos hk hr.1 h1).ne' (hf r hr)).continuousWithinAt
  obtain ⟨-, h⟩ := qMode_ftc hk 0 hf (lhs_zero_continuousOn hf hf')
    (fun r hr => (gRad_zero_pos hk hr.1.le hr.2).ne') hBc
  rw [h]
  have hB0 : Bd k 0 f 0 = 0 := by simp [Bd]
  have hB1 : Bd k 0 f 1 = 0 := by simp [Bd, hf1]
  rw [hB0, hB1]
  linarith [integral_Rm_nonneg k 0 f f']

/-! ### Classification of regular solutions (Prop `ode`, disk form) -/

lemma gRad_pos_Ioo (hk : 2 ≤ k) (ℓ : ℕ) {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) : 0 < gRad k ℓ r := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | h
  · exact gRad_zero_pos hk hr.1.le hr.2
  · exact gRad_pos hk h hr.1.le hr.2.le

lemma uRad_continuousOn (hk : 2 ≤ k) (ℓ : ℕ) (s : Set ℝ) : ContinuousOn (uRad k ℓ) s :=
  fun r _ => ((hasDerivAt_pow ℓ r).mul (gRad_hasDerivAt hk ℓ r)).continuousAt.continuousWithinAt

/-- Abel-type identity: along a solution `f` of the mode-`ℓ` equation, `A := r^ℓ W` has zero
derivative. -/
lemma A_hasDerivAt_zero (hk : 2 ≤ k) (ℓ : ℕ) {f f' : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0)
    (hd : HasDerivAt f (f' r) r)
    (hode : HasDerivAt (fun r => r * f' r) ((ℓ : ℝ) ^ 2 * f r / r - r * Vrad k r * f r) r) :
    HasDerivAt (fun r => r ^ ℓ * Wg k ℓ f f' r) 0 r := by
  have e : Wg k ℓ f f' =
      fun r => (r * f' r) * gRad k ℓ r - ((ℓ : ℝ) * gRad k ℓ r + r * gD k r) * f r := by
    funext r; rw [Wg]; ring
  have hW : HasDerivAt (Wg k ℓ f f')
      (((ℓ : ℝ) ^ 2 * f r / r - r * Vrad k r * f r) * gRad k ℓ r + (r * f' r) * gD k r -
        (((ℓ : ℝ) * gD k r + (1 * gD k r + r * gDD k r)) * f r +
          ((ℓ : ℝ) * gRad k ℓ r + r * gD k r) * f' r)) r := by
    rw [e]
    exact (hode.mul (gRad_hasDerivAt hk ℓ r)).sub
      ((((gRad_hasDerivAt hk ℓ r).const_mul (ℓ : ℝ)).add
        ((hasDerivAt_id' r).mul (gD_hasDerivAt hk r))).mul hd)
  refine ((hasDerivAt_pow ℓ r).mul hW).congr_deriv ?_
  rw [gDD_eq hk ℓ hr, Wg, cast_mul_pow_pred ℓ hr]
  field_simp
  ring

lemma Wg_eq_zero (hk : 2 ≤ k) (ℓ : ℕ) {f f' : ℝ → ℝ}
    (hfc : ContinuousOn f (Ico 0 1)) (hf'c : ContinuousOn f' (Ico 0 1))
    (hd : ∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt f (f' r) r)
    (hode : ∀ r ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun r => r * f' r) ((ℓ : ℝ) ^ 2 * f r / r - r * Vrad k r * f r) r) :
    ∀ r ∈ Ioo (0:ℝ) 1, Wg k ℓ f f' r = 0 := by
  set A : ℝ → ℝ := fun r => r ^ ℓ * Wg k ℓ f f' r with hA
  have hAd : ∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt A 0 r :=
    fun r hr => A_hasDerivAt_zero hk ℓ hr.1.ne' (hd r hr) (hode r hr)
  have hconst : ∀ x ∈ Ioo (0:ℝ) 1, ∀ y ∈ Ioo (0:ℝ) 1, A x = A y := fun x hx y hy =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun z hz => (hAd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hAd z hz).deriv) hx hy
  have hAc : ContinuousOn A (Ico 0 1) := by
    have hg : ContinuousOn (gRad k ℓ) (Ico 0 1) :=
      fun r _ => (gRad_hasDerivAt hk ℓ r).continuousAt.continuousWithinAt
    have hgD : ContinuousOn (gD k) (Ico 0 1) :=
      fun r _ => (gD_hasDerivAt hk r).continuousAt.continuousWithinAt
    change ContinuousOn (fun r => r ^ ℓ *
      (r * gRad k ℓ r * f' r - ((ℓ : ℝ) * gRad k ℓ r + r * gD k r) * f r)) (Ico 0 1)
    exact (continuousOn_id.pow ℓ).mul (((continuousOn_id.mul hg).mul hf'c).sub
      (((continuousOn_const.mul hg).add (continuousOn_id.mul hgD)).mul hfc))
  have hA0 : A 0 = 0 := by cases ℓ <;> simp [hA, Wg]
  intro r hr
  have hAr : A r = 0 := by
    haveI : (𝓝[Ioo (0:ℝ) 1] 0).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]; infer_instance
    have h1 : Tendsto A (𝓝[Ioo 0 1] 0) (𝓝 (A 0)) :=
      (hAc 0 (by simp)).tendsto.mono_left (nhdsWithin_mono _ Ioo_subset_Ico_self)
    have h2 : Tendsto A (𝓝[Ioo 0 1] 0) (𝓝 (A r)) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall (fun y hy => hconst r hr y hy))
    rw [← hA0]; exact tendsto_nhds_unique h2 h1
  exact (mul_eq_zero.mp hAr).resolve_left (pow_ne_zero _ hr.1.ne')

/-- A real integer-mode solution of `(r f')' = ℓ² f/r − r V f` on `(0,1)`,
with `f` and its specified derivative continuous on `[0,1)`, is a constant
multiple of `uRad k ℓ` on `[0,1)`, for `k ≥ 2`. -/
theorem eq_const_mul_uRad (hk : 2 ≤ k) (ℓ : ℕ) {f f' : ℝ → ℝ}
    (hfc : ContinuousOn f (Ico 0 1)) (hf'c : ContinuousOn f' (Ico 0 1))
    (hd : ∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt f (f' r) r)
    (hode : ∀ r ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun r => r * f' r) ((ℓ : ℝ) ^ 2 * f r / r - r * Vrad k r * f r) r) :
    ∃ c : ℝ, ∀ r ∈ Ico (0:ℝ) 1, f r = c * uRad k ℓ r := by
  have hW := Wg_eq_zero hk ℓ hfc hf'c hd hode
  have hu : ∀ r ∈ Ioo (0:ℝ) 1, uRad k ℓ r ≠ 0 := fun r hr => by
    rw [uRad]; exact mul_ne_zero (pow_ne_zero _ hr.1.ne') (gRad_pos_Ioo hk ℓ hr).ne'
  set φ : ℝ → ℝ := fun r => f r / uRad k ℓ r with hφ
  have hφd : ∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt φ 0 r := by
    intro r hr
    refine ((hd r hr).div (uRad_hasDerivAt hk ℓ hr.1.ne') (hu r hr)).congr_deriv ?_
    have h0 : f' r * uRad k ℓ r - f r * uD k ℓ r = 0 := by
      have hr0 : r ≠ 0 := hr.1.ne'
      have : r * (f' r * uRad k ℓ r - f r * uD k ℓ r) = r ^ ℓ * Wg k ℓ f f' r := by
        rw [uD, uRad, Wg]; field_simp; try ring
      rw [hW r hr, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hr0
    rw [h0, zero_div]
  have hφconst : ∀ x ∈ Ioo (0:ℝ) 1, ∀ y ∈ Ioo (0:ℝ) 1, φ x = φ y := fun x hx y hy =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun z hz => (hφd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hφd z hz).deriv) hx hy
  have hfu : ∀ y ∈ Ioo (0:ℝ) 1, f y = φ (1 / 2) * uRad k ℓ y := fun y hy => by
    rw [← hφconst y hy (1 / 2) (by norm_num), hφ]
    exact (div_mul_cancel₀ (f y) (hu y hy)).symm
  refine ⟨φ (1 / 2), fun r hr => ?_⟩
  rcases eq_or_lt_of_le hr.1 with h0 | h0
  · subst h0
    have huc : ContinuousOn (fun y => φ (1 / 2) * uRad k ℓ y) (Ico 0 1) :=
      continuousOn_const.mul (uRad_continuousOn hk ℓ _)
    haveI : (𝓝[Ioo (0:ℝ) 1] 0).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]; infer_instance
    have h1 : Tendsto f (𝓝[Ioo 0 1] 0) (𝓝 (f 0)) :=
      (hfc 0 (by simp)).tendsto.mono_left (nhdsWithin_mono _ Ioo_subset_Ico_self)
    have h2 : Tendsto f (𝓝[Ioo 0 1] 0) (𝓝 (φ (1 / 2) * uRad k ℓ 0)) :=
      ((huc 0 (by simp)).tendsto.mono_left (nhdsWithin_mono _ Ioo_subset_Ico_self)).congr'
        (eventually_nhdsWithin_of_forall (fun y hy => (hfu y hy).symm))
    exact tendsto_nhds_unique h1 h2
  · exact hfu r ⟨h0, hr.2⟩

/-! ### Complex-valued corollaries

The functions on the disk are `ℂ`-valued; after separating variables in polar coordinates each
Fourier mode is a path `f : ℝ → ℂ` in the radial variable.  The complex Jacobi density
`r ‖f'‖² + ℓ² ‖f‖²/r − r V ‖f‖²` splits over `f = Re f + i Im f` with no cross terms, so the
real results apply summand-by-summand. -/

lemma norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- The real part of a complex path carries the real part of the derivative. -/
lemma hasDerivAt_re {f : ℝ → ℂ} {c : ℂ} {x : ℝ} (hf : HasDerivAt f c x) :
    HasDerivAt (fun t => (f t).re) c.re x := by
  have h := (Complex.reCLM.hasFDerivAt (x := f x)).comp_hasDerivAt x hf
  simp only [Function.comp_def, Complex.reCLM_apply] at h
  exact h

lemma hasDerivAt_im {f : ℝ → ℂ} {c : ℂ} {x : ℝ} (hf : HasDerivAt f c x) :
    HasDerivAt (fun t => (f t).im) c.im x := by
  have h := (Complex.imCLM.hasFDerivAt (x := f x)).comp_hasDerivAt x hf
  simp only [Function.comp_def, Complex.imCLM_apply] at h
  exact h

/-- The complex mode-`ℓ` integrand `r ‖f'‖² + ℓ² ‖f‖²/r − r V ‖f‖²`. -/
def lhsC (k ℓ : ℕ) (f f' : ℝ → ℂ) (r : ℝ) : ℝ :=
  r * ‖f' r‖ ^ 2 + (ℓ : ℝ) ^ 2 * (‖f r‖ ^ 2 / r) - r * Vrad k r * ‖f r‖ ^ 2

/-- `lhsC` splits with no cross terms over the real and imaginary parts. -/
lemma lhsC_eq (k ℓ : ℕ) (f f' : ℝ → ℂ) :
    lhsC k ℓ f f' = fun r =>
      lhs k ℓ (fun t => (f t).re) (fun t => (f' t).re) r
        + lhs k ℓ (fun t => (f t).im) (fun t => (f' t).im) r := by
  funext r
  simp only [lhsC, lhs, norm_sq_eq]
  ring

/-- **Complex DtN domination, mode `ℓ ≥ 1`**: `σ_k(ℓ) ‖f(1)‖² ≤ ∫_0^1 (r‖f'‖² + ℓ²‖f‖²/r − rV‖f‖²)`. -/
theorem qMode_ge_complex (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) {f f' : ℝ → ℂ}
    (hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt f (f' r) r) (hf' : ContinuousOn f' (Icc 0 1))
    (hf0 : f 0 = 0) :
    sigma k ℓ * ‖f 1‖ ^ 2 ≤ ∫ r in (0:ℝ)..1, lhsC k ℓ f f' r := by
  have hfRe : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt (fun t => (f t).re) ((f' r).re) r :=
    fun r hr => hasDerivAt_re (hf r hr)
  have hfIm : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt (fun t => (f t).im) ((f' r).im) r :=
    fun r hr => hasDerivAt_im (hf r hr)
  have hf'Re : ContinuousOn (fun r => (f' r).re) (Icc 0 1) :=
    Complex.continuous_re.comp_continuousOn hf'
  have hf'Im : ContinuousOn (fun r => (f' r).im) (Icc 0 1) :=
    Complex.continuous_im.comp_continuousOn hf'
  have h0Re : (f 0).re = 0 := by simp [hf0]
  have h0Im : (f 0).im = 0 := by simp [hf0]
  have gRe := qMode_ge hk hℓ hfRe hf'Re h0Re
  have gIm := qMode_ge hk hℓ hfIm hf'Im h0Im
  have intRe : IntervalIntegrable
      (lhs k ℓ (fun t => (f t).re) (fun t => (f' t).re)) volume 0 1 :=
    (lhs_continuousOn hℓ hfRe hf'Re h0Re).intervalIntegrable_of_Icc zero_le_one
  have intIm : IntervalIntegrable
      (lhs k ℓ (fun t => (f t).im) (fun t => (f' t).im)) volume 0 1 :=
    (lhs_continuousOn hℓ hfIm hf'Im h0Im).intervalIntegrable_of_Icc zero_le_one
  rw [lhsC_eq, intervalIntegral.integral_add intRe intIm, norm_sq_eq, mul_add]
  linarith [gRe, gIm]

/-- **Complex Dirichlet mode `ℓ = 0` nonnegativity** (`f(1) = 0`):
`0 ≤ ∫_0^1 (r‖f'‖² − rV‖f‖²)`. -/
theorem qMode_zero_nonneg_complex (hk : 2 ≤ k) {f f' : ℝ → ℂ}
    (hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt f (f' r) r) (hf' : ContinuousOn f' (Icc 0 1))
    (hf1 : f 1 = 0) :
    0 ≤ ∫ r in (0:ℝ)..1, lhsC k 0 f f' r := by
  have hfRe : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt (fun t => (f t).re) ((f' r).re) r :=
    fun r hr => hasDerivAt_re (hf r hr)
  have hfIm : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt (fun t => (f t).im) ((f' r).im) r :=
    fun r hr => hasDerivAt_im (hf r hr)
  have hf'Re : ContinuousOn (fun r => (f' r).re) (Icc 0 1) :=
    Complex.continuous_re.comp_continuousOn hf'
  have hf'Im : ContinuousOn (fun r => (f' r).im) (Icc 0 1) :=
    Complex.continuous_im.comp_continuousOn hf'
  have gRe := qMode_zero_nonneg hk hfRe hf'Re (by simp [hf1])
  have gIm := qMode_zero_nonneg hk hfIm hf'Im (by simp [hf1])
  have intRe : IntervalIntegrable
      (lhs k 0 (fun t => (f t).re) (fun t => (f' t).re)) volume 0 1 :=
    (lhs_zero_continuousOn hfRe hf'Re).intervalIntegrable_of_Icc zero_le_one
  have intIm : IntervalIntegrable
      (lhs k 0 (fun t => (f t).im) (fun t => (f' t).im)) volume 0 1 :=
    (lhs_zero_continuousOn hfIm hf'Im).intervalIntegrable_of_Icc zero_le_one
  rw [lhsC_eq, intervalIntegral.integral_add intRe intIm]
  linarith [gRe, gIm]

/-- The disk profile equals the paper's hyperbolic expression at r=exp(t). -/
lemma uRad_exp_eq (hk : 2 ≤ k) (ℓ : ℕ) (t : ℝ) :
    uRad k ℓ (Real.exp t) =
      ((ℓ : ℝ) - kap k * Real.tanh (kap k * t)) * Real.exp ((ℓ : ℝ) * t) := by
  have hs : (Real.exp t) ^ (2 * k - 2) = (Real.exp (kap k * t)) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    rw [cast_two_k_sub_two hk]
    unfold kap
    push_cast
    ring
  have he := Real.exp_pos (kap k * t)
  rw [uRad, gRad, hs, ← Real.exp_nat_mul, Real.tanh_eq, Real.exp_neg]
  field_simp
  ring

/-- The rescaled disk potential is the paper's cylindrical sech-squared potential. -/
lemma Vrad_exp_eq (hk : 2 ≤ k) (t : ℝ) :
    (Real.exp t) ^ 2 * Vrad k (Real.exp t) =
      2 * kap k ^ 2 / (Real.cosh (kap k * t)) ^ 2 := by
  have hs : (Real.exp t) ^ (2 * k - 2) = (Real.exp (kap k * t)) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    rw [cast_two_k_sub_two hk]
    unfold kap
    push_cast
    ring
  have hpow : (Real.exp t) ^ 2 * (Real.exp t) ^ (2 * k - 4) =
      (Real.exp t) ^ (2 * k - 2) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (Real.exp t) ^ 2 * Vrad k (Real.exp t) =
        8 * kap k ^ 2 * ((Real.exp t) ^ 2 * (Real.exp t) ^ (2 * k - 4)) /
          ((Real.exp t) ^ (2 * k - 2) + 1) ^ 2 := by unfold Vrad; ring
    _ = 8 * kap k ^ 2 * (Real.exp (kap k * t)) ^ 2 /
          ((Real.exp (kap k * t)) ^ 2 + 1) ^ 2 := by rw [hpow, hs]
    _ = 2 * kap k ^ 2 / (Real.cosh (kap k * t)) ^ 2 := by
      have he := Real.exp_pos (kap k * t)
      rw [Real.cosh_eq, Real.exp_neg]
      field_simp
      ring

end KsIndex.Radial
