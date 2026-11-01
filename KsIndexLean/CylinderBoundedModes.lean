module

/-
# Bounded cylinder modes for real spectral parameters

For `k ≥ 3`, `μ ≥ 0` and `κ = k - 1`, the bounded rotationally invariant
classical solutions of `cylop_k u = μ² u` on the open half cylinder are
constant multiples of

`uCyl k μ t = (μ - κ tanh(κt)) exp(μt)`.

Here `cylop_k = ∂²_t + ∂²_θ + Vcyl k`, with
`Vcyl k t = 2κ² / cosh(κt)²`. Rotational invariance reduces the equation
to `u″ = (μ² - Vcyl k)u`. This is the bounded-solution classification of
[ksindexi, Proposition `ode`], for real and complex valued solutions.

`IsCylSolOn` carries a scalar solution and its first derivative explicitly.
`IsCylopEigenOn` carries the four partial derivatives in the classical
slice equation. The open-domain results assume the equation only for
`t < 0`. The closed-domain results additionally assume boundedness and
rotational invariance on `t ≤ 0`, and one-sided continuity at zero of the
slice `θ = 0`; they require no derivative of the unknown solution there.
Rotational invariance makes the functions periodic in the angular variable.

The proof uses Cauchy uniqueness and two explicit independent solutions.
The companion is `uCyl k (-μ)` when `μ > 0` and `μ ≠ κ`; at `μ = 0`
and `μ = κ` it is respectively `κt tanh(κt) - 1` and
`sinh(κt) + κt / cosh(κt)`. Their Wronskians are evaluated at zero,
where the model solutions are globally defined. Matching Cauchy data at
the interior point `t = -1` expresses any solution in this basis;
boundedness excludes the unbounded companion. Complex solutions are
classified by applying the real result to their real and imaginary parts.

Unlike the centre-regular or finite-energy integer-mode classifications,
this argument applies to arbitrary nonnegative real frequencies and uses
boundedness of a classical solution. `uCyl_eq_uRad_exp` identifies the
integer modes with `RadialMode` under `r = exp t`. The classification
statements use `k ≥ 3`, while their scalar estimates require only `k ≥ 2`.
-/
public import KsIndexLean.RadialMode
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section


noncomputable section

namespace KsIndex.Radial

open Real Set Filter Topology
open scoped NNReal

/-! ### The cylinder data -/

/-- The Pöschl–Teller potential `V(t) = 2κ² sech²(κt)` of `cylop_k`
([ksindexi] tex 1430–1438). -/
def Vcyl (k : ℕ) (t : ℝ) : ℝ := 2 * kap k ^ 2 / Real.cosh (kap k * t) ^ 2

/-- The paper's mode `u_{k,μ}(t) = (μ − κ tanh κt) e^{μt}`, defined for every
real `μ`; the instance with `μ ↦ −μ` is the generic second solution. -/
def uCyl (k : ℕ) (μ : ℝ) (t : ℝ) : ℝ :=
  (μ - kap k * Real.tanh (kap k * t)) * Real.exp (μ * t)

/-- The derivative of `uCyl`. -/
def uCylD (k : ℕ) (μ : ℝ) (t : ℝ) : ℝ :=
  (μ * (μ - kap k * Real.tanh (kap k * t)) - kap k ^ 2 / Real.cosh (kap k * t) ^ 2) *
    Real.exp (μ * t)

/-- The paper's unbounded companion at `μ = 0`:
`u_{k,0′}(t) = κt·tanh(κt) − 1`. -/
def uZeroPrime (k : ℕ) (t : ℝ) : ℝ := kap k * t * Real.tanh (kap k * t) - 1

/-- The derivative of `uZeroPrime`. -/
def uZeroPrimeD (k : ℕ) (t : ℝ) : ℝ :=
  kap k * Real.tanh (kap k * t) + kap k ^ 2 * t / Real.cosh (kap k * t) ^ 2

/-- The paper's unbounded companion at `μ = κ = k − 1`:
`u_{k,(k−1)′}(t) = sinh(κt) + κt·sech(κt)`. -/
def uKapPrime (k : ℕ) (t : ℝ) : ℝ :=
  Real.sinh (kap k * t) + kap k * t / Real.cosh (kap k * t)

/-- The derivative of `uKapPrime`. -/
def uKapPrimeD (k : ℕ) (t : ℝ) : ℝ :=
  kap k * Real.cosh (kap k * t) + kap k / Real.cosh (kap k * t) -
    kap k ^ 2 * t * Real.sinh (kap k * t) / Real.cosh (kap k * t) ^ 2

/-- A classical solution pair of the rotationally invariant `cylop_k`
eigenequation `u″ = (μ² − V)u` on a set, with the first derivative carried
explicitly. -/
structure IsCylSolOn (k : ℕ) (μ : ℝ) (u u' : ℝ → ℝ) (s : Set ℝ) : Prop where
  deriv_fst : ∀ t ∈ s, HasDerivAt u (u' t) t
  deriv_snd : ∀ t ∈ s, HasDerivAt u' ((μ ^ 2 - Vcyl k t) * u t) t

/-! ### Hyperbolic preliminaries -/

/-- The derivative of `Real.tanh`. -/
lemma hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h : HasDerivAt (fun y => Real.sinh y / Real.cosh y) (1 / Real.cosh x ^ 2) x :=
    ((Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne').congr_deriv
      (by linear_combination (1 / Real.cosh x ^ 2) * Real.cosh_sq_sub_sinh_sq x)
  have hfeq : (fun y => Real.sinh y / Real.cosh y) =ᶠ[nhds x] Real.tanh :=
    Filter.Eventually.of_forall fun y => (Real.tanh_eq_sinh_div_cosh y).symm
  exact hfeq.hasDerivAt_iff.mp h

/-- The derivative of `t ↦ tanh (a t)`. -/
lemma hasDerivAt_tanh_comp (a x : ℝ) :
    HasDerivAt (fun t => Real.tanh (a * t)) (a / Real.cosh (a * x) ^ 2) x :=
  ((hasDerivAt_tanh (a * x)).comp x ((hasDerivAt_id x).const_mul a)).congr_deriv (by ring)

/-- The derivative of `t ↦ cosh (a t)`. -/
lemma hasDerivAt_cosh_comp (a x : ℝ) :
    HasDerivAt (fun t => Real.cosh (a * t)) (a * Real.sinh (a * x)) x :=
  ((Real.hasDerivAt_cosh (a * x)).comp x ((hasDerivAt_id x).const_mul a)).congr_deriv (by ring)

/-- The derivative of `t ↦ sinh (a t)`. -/
lemma hasDerivAt_sinh_comp (a x : ℝ) :
    HasDerivAt (fun t => Real.sinh (a * t)) (a * Real.cosh (a * x)) x :=
  ((Real.hasDerivAt_sinh (a * x)).comp x ((hasDerivAt_id x).const_mul a)).congr_deriv (by ring)

/-- The derivative of `t ↦ exp (a t)`. -/
lemma hasDerivAt_exp_mul (a x : ℝ) :
    HasDerivAt (fun t => Real.exp (a * t)) (a * Real.exp (a * x)) x :=
  ((Real.hasDerivAt_exp (a * x)).comp x ((hasDerivAt_id x).const_mul a)).congr_deriv (by ring)

/-- The derivative of `t ↦ cosh (a t) ^ 2`. -/
lemma hasDerivAt_cosh_sq (a x : ℝ) :
    HasDerivAt (fun t => Real.cosh (a * t) ^ 2)
      (2 * a * Real.sinh (a * x) * Real.cosh (a * x)) x :=
  ((hasDerivAt_cosh_comp a x).pow 2).congr_deriv (by push_cast; ring)

/-- `tanh` as a rational function of `exp`. -/
lemma tanh_eq_exp_form (x : ℝ) :
    Real.tanh x = (Real.exp x * Real.exp x - 1) / (Real.exp x * Real.exp x + 1) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h1 : Real.exp x ≠ 0 := Real.exp_ne_zero x
  have h2 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  have h3 : (0 : ℝ) < Real.exp x * Real.exp x + 1 := by positivity
  rw [h2]
  field_simp

/-- `tanh → −1` at `−∞`. -/
lemma tendsto_tanh_atBot : Tendsto Real.tanh atBot (𝓝 (-1)) := by
  have hy : Tendsto (fun x : ℝ => Real.exp x * Real.exp x) atBot (𝓝 0) := by
    simpa using Real.tendsto_exp_atBot.mul Real.tendsto_exp_atBot
  have hnum : Tendsto (fun x : ℝ => Real.exp x * Real.exp x - 1) atBot (𝓝 (0 - 1)) :=
    hy.sub_const 1
  have hden : Tendsto (fun x : ℝ => Real.exp x * Real.exp x + 1) atBot (𝓝 (0 + 1)) :=
    hy.add_const 1
  have h := hnum.div hden (by norm_num)
  have heq : ((0 : ℝ) - 1) / (0 + 1) = -1 := by norm_num
  rw [heq] at h
  exact h.congr fun x => (tanh_eq_exp_form x).symm

/-! ### The four model solutions -/

lemma uCyl_hasDerivAt (k : ℕ) (μ t : ℝ) :
    HasDerivAt (uCyl k μ) (uCylD k μ t) t := by
  have hpre : HasDerivAt (fun s => μ - kap k * Real.tanh (kap k * s))
      (-(kap k ^ 2 / Real.cosh (kap k * t) ^ 2)) t :=
    (((hasDerivAt_tanh_comp (kap k) t).const_mul (kap k)).const_sub μ).congr_deriv (by ring)
  have h := hpre.mul (hasDerivAt_exp_mul μ t)
  exact h.congr_deriv (by simp only [uCylD]; ring)

lemma uCylD_hasDerivAt (k : ℕ) (μ t : ℝ) :
    HasDerivAt (uCylD k μ) ((μ ^ 2 - Vcyl k t) * uCyl k μ t) t := by
  have hc : Real.cosh (kap k * t) ≠ 0 := (Real.cosh_pos _).ne'
  have h1 : HasDerivAt (fun s => μ * (μ - kap k * Real.tanh (kap k * s)))
      (μ * -(kap k ^ 2 / Real.cosh (kap k * t) ^ 2)) t :=
    ((((hasDerivAt_tanh_comp (kap k) t).const_mul (kap k)).const_sub μ).const_mul μ).congr_deriv
      (by ring)
  have h2 : HasDerivAt (fun s => kap k ^ 2 / Real.cosh (kap k * s) ^ 2)
      ((0 * Real.cosh (kap k * t) ^ 2 -
        kap k ^ 2 * (2 * kap k * Real.sinh (kap k * t) * Real.cosh (kap k * t))) /
        (Real.cosh (kap k * t) ^ 2) ^ 2) t :=
    (hasDerivAt_const t (kap k ^ 2)).div (hasDerivAt_cosh_sq (kap k) t) (pow_ne_zero 2 hc)
  have hA : HasDerivAt
      (fun s => μ * (μ - kap k * Real.tanh (kap k * s)) - kap k ^ 2 / Real.cosh (kap k * s) ^ 2)
      (μ * -(kap k ^ 2 / Real.cosh (kap k * t) ^ 2) -
        (0 * Real.cosh (kap k * t) ^ 2 -
          kap k ^ 2 * (2 * kap k * Real.sinh (kap k * t) * Real.cosh (kap k * t))) /
          (Real.cosh (kap k * t) ^ 2) ^ 2) t := h1.sub h2
  have h := hA.mul (hasDerivAt_exp_mul μ t)
  exact h.congr_deriv (by
    simp only [uCyl, Vcyl]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    all_goals ring)

/-- `uCyl` solves the equation globally, as a solution pair. -/
lemma uCyl_isCylSolOn (k : ℕ) (μ : ℝ) (s : Set ℝ) :
    IsCylSolOn k μ (uCyl k μ) (uCylD k μ) s :=
  ⟨fun t _ => uCyl_hasDerivAt k μ t, fun t _ => uCylD_hasDerivAt k μ t⟩

lemma uZeroPrime_hasDerivAt (k : ℕ) (t : ℝ) :
    HasDerivAt (uZeroPrime k) (uZeroPrimeD k t) t := by
  have h1 : HasDerivAt (fun s : ℝ => kap k * s) (kap k) t := by
    simpa using (hasDerivAt_id t).const_mul (kap k)
  have h := (h1.mul (hasDerivAt_tanh_comp (kap k) t)).sub_const 1
  exact h.congr_deriv (by simp only [uZeroPrimeD]; ring)

lemma uZeroPrimeD_hasDerivAt (k : ℕ) (t : ℝ) :
    HasDerivAt (uZeroPrimeD k) ((0 ^ 2 - Vcyl k t) * uZeroPrime k t) t := by
  have hc : Real.cosh (kap k * t) ≠ 0 := (Real.cosh_pos _).ne'
  have h1 : HasDerivAt (fun s => kap k * Real.tanh (kap k * s))
      (kap k ^ 2 / Real.cosh (kap k * t) ^ 2) t :=
    ((hasDerivAt_tanh_comp (kap k) t).const_mul (kap k)).congr_deriv (by ring)
  have ha : HasDerivAt (fun s : ℝ => kap k ^ 2 * s) (kap k ^ 2) t := by
    simpa using (hasDerivAt_id t).const_mul (kap k ^ 2)
  have h2 : HasDerivAt (fun s => kap k ^ 2 * s / Real.cosh (kap k * s) ^ 2)
      ((kap k ^ 2 * Real.cosh (kap k * t) ^ 2 -
        kap k ^ 2 * t * (2 * kap k * Real.sinh (kap k * t) * Real.cosh (kap k * t))) /
        (Real.cosh (kap k * t) ^ 2) ^ 2) t :=
    ha.div (hasDerivAt_cosh_sq (kap k) t) (pow_ne_zero 2 hc)
  have h := h1.add h2
  exact h.congr_deriv (by
    simp only [uZeroPrime, Vcyl]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    all_goals ring)

lemma uZeroPrime_isCylSolOn (k : ℕ) (s : Set ℝ) :
    IsCylSolOn k 0 (uZeroPrime k) (uZeroPrimeD k) s :=
  ⟨fun t _ => uZeroPrime_hasDerivAt k t, fun t _ => uZeroPrimeD_hasDerivAt k t⟩

lemma uKapPrime_hasDerivAt (k : ℕ) (t : ℝ) :
    HasDerivAt (uKapPrime k) (uKapPrimeD k t) t := by
  have hc : Real.cosh (kap k * t) ≠ 0 := (Real.cosh_pos _).ne'
  have ha : HasDerivAt (fun s : ℝ => kap k * s) (kap k) t := by
    simpa using (hasDerivAt_id t).const_mul (kap k)
  have h2 : HasDerivAt (fun s => kap k * s / Real.cosh (kap k * s))
      ((kap k * Real.cosh (kap k * t) -
        kap k * t * (kap k * Real.sinh (kap k * t))) / Real.cosh (kap k * t) ^ 2) t :=
    ha.div (hasDerivAt_cosh_comp (kap k) t) hc
  have h := (hasDerivAt_sinh_comp (kap k) t).add h2
  exact h.congr_deriv (by
    simp only [uKapPrimeD]
    field_simp
    all_goals ring)

lemma uKapPrimeD_hasDerivAt (k : ℕ) (t : ℝ) :
    HasDerivAt (uKapPrimeD k) ((kap k ^ 2 - Vcyl k t) * uKapPrime k t) t := by
  have hc : Real.cosh (kap k * t) ≠ 0 := (Real.cosh_pos _).ne'
  have ha : HasDerivAt (fun s : ℝ => kap k ^ 2 * s) (kap k ^ 2) t := by
    simpa using (hasDerivAt_id t).const_mul (kap k ^ 2)
  have h1 : HasDerivAt (fun s => kap k * Real.cosh (kap k * s))
      (kap k ^ 2 * Real.sinh (kap k * t)) t :=
    ((hasDerivAt_cosh_comp (kap k) t).const_mul (kap k)).congr_deriv (by ring)
  have h2 : HasDerivAt (fun s => kap k / Real.cosh (kap k * s))
      (-(kap k ^ 2 * Real.sinh (kap k * t)) / Real.cosh (kap k * t) ^ 2) t :=
    (((hasDerivAt_const t (kap k)).div (hasDerivAt_cosh_comp (kap k) t) hc).congr_deriv
      (by ring))
  have hd0 : Real.cosh (kap k * t) ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have h3 : HasDerivAt
      (fun s => kap k ^ 2 * s * Real.sinh (kap k * s) / Real.cosh (kap k * s) ^ 2)
      (((kap k ^ 2 * Real.sinh (kap k * t) + kap k ^ 2 * t * (kap k * Real.cosh (kap k * t))) *
          Real.cosh (kap k * t) ^ 2 -
        kap k ^ 2 * t * Real.sinh (kap k * t) *
          (2 * kap k * Real.sinh (kap k * t) * Real.cosh (kap k * t))) /
        (Real.cosh (kap k * t) ^ 2) ^ 2) t :=
    (ha.mul (hasDerivAt_sinh_comp (kap k) t)).div (hasDerivAt_cosh_sq (kap k) t) hd0
  have h12 : HasDerivAt
      (fun s => kap k * Real.cosh (kap k * s) + kap k / Real.cosh (kap k * s))
      (kap k ^ 2 * Real.sinh (kap k * t) +
        -(kap k ^ 2 * Real.sinh (kap k * t)) / Real.cosh (kap k * t) ^ 2) t := h1.add h2
  have h := h12.sub h3
  exact h.congr_deriv (by
    unfold uKapPrime Vcyl
    have hc2 : Real.cosh (kap k * t) ^ 2 = Real.sinh (kap k * t) ^ 2 + 1 := Real.cosh_sq _
    field_simp
    linear_combination (-(2 * kap k ^ 3 * t)) * hc2)

lemma uKapPrime_isCylSolOn (k : ℕ) (s : Set ℝ) :
    IsCylSolOn k (kap k) (uKapPrime k) (uKapPrimeD k) s :=
  ⟨fun t _ => uKapPrime_hasDerivAt k t, fun t _ => uKapPrimeD_hasDerivAt k t⟩

/-! ### Boundedness of `u_{k,μ}` and values at `t = 0` -/

/-- `u_{k,μ}` is bounded on the half line (for `μ ≥ 0` and `1 ≤ k`). -/
lemma uCyl_bounded (k : ℕ) (hk : 1 ≤ k) {μ : ℝ} (hμ : 0 ≤ μ) :
    ∀ t ≤ (0 : ℝ), |uCyl k μ t| ≤ μ + kap k := by
  intro t ht
  have hκ : (0 : ℝ) ≤ kap k := by
    unfold kap
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h1 : |μ - kap k * Real.tanh (kap k * t)| ≤ μ + kap k := by
    have ht1 : |Real.tanh (kap k * t)| < 1 := Real.abs_tanh_lt_one _
    calc |μ - kap k * Real.tanh (kap k * t)|
        ≤ |μ| + |kap k * Real.tanh (kap k * t)| := abs_sub _ _
      _ = μ + kap k * |Real.tanh (kap k * t)| := by
          rw [abs_of_nonneg hμ, abs_mul, abs_of_nonneg hκ]
      _ ≤ μ + kap k * 1 := by nlinarith
      _ = μ + kap k := by ring
  have h2 : Real.exp (μ * t) ≤ 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc |uCyl k μ t| = |μ - kap k * Real.tanh (kap k * t)| * Real.exp (μ * t) := by
        rw [uCyl, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ (μ + kap k) * 1 := by
        apply mul_le_mul h1 h2 (Real.exp_pos _).le
        linarith [abs_nonneg (μ - kap k * Real.tanh (kap k * t))]
    _ = μ + kap k := by ring

@[simp] lemma uCyl_zero_val (k : ℕ) (μ : ℝ) : uCyl k μ 0 = μ := by
  simp [uCyl, Real.tanh_zero]

@[simp] lemma uCylD_zero_val (k : ℕ) (μ : ℝ) : uCylD k μ 0 = μ ^ 2 - kap k ^ 2 := by
  simp [uCylD, Real.tanh_zero, Real.cosh_zero]
  ring

@[simp] lemma uZeroPrime_zero_val (k : ℕ) : uZeroPrime k 0 = -1 := by
  simp [uZeroPrime]

@[simp] lemma uZeroPrimeD_zero_val (k : ℕ) : uZeroPrimeD k 0 = 0 := by
  simp [uZeroPrimeD, Real.tanh_zero]

@[simp] lemma uKapPrime_zero_val (k : ℕ) : uKapPrime k 0 = 0 := by
  simp [uKapPrime]

@[simp] lemma uKapPrimeD_zero_val (k : ℕ) : uKapPrimeD k 0 = 2 * kap k := by
  simp [uKapPrimeD, Real.cosh_zero]
  ring

/-! ### Unboundedness of the companion solutions on the half line -/

/-- Convert a `|f| → ∞` statement at `−∞` into unboundedness witnesses in `Iio 0`. -/
lemma exists_lt_of_tendsto_abs_atTop {f : ℝ → ℝ}
    (h : Tendsto (fun t => |f t|) atBot atTop) (C : ℝ) : ∃ t < (0 : ℝ), C < |f t| := by
  have h1 : ∀ᶠ t in (atBot : Filter ℝ), C < |f t| := h.eventually_gt_atTop C
  have h2 : ∀ᶠ t in (atBot : Filter ℝ), t < 0 := eventually_lt_atBot 0
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  exact ⟨t, ht2, ht1⟩

lemma tendsto_kapMul_atBot (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun t : ℝ => kap k * t) atBot atBot :=
  (tendsto_const_mul_atBot_of_pos (kap_pos hk)).mpr tendsto_id

lemma tendsto_tanh_kapMul (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun t : ℝ => Real.tanh (kap k * t)) atBot (𝓝 (-1)) :=
  tendsto_tanh_atBot.comp (tendsto_kapMul_atBot k hk)

/-- The generic second solution `u_{k,−μ}` is unbounded on the half line
(`0 < μ`, `μ ≠ κ`). -/
lemma uCyl_neg_unbounded (k : ℕ) (hk : 2 ≤ k) {μ : ℝ} (hμ : 0 < μ) (hne : μ ≠ kap k) :
    ∀ C, ∃ t < (0 : ℝ), C < |uCyl k (-μ) t| := by
  have hκ : 0 < kap k := kap_pos hk
  have hpre : Tendsto (fun t => -μ - kap k * Real.tanh (kap k * t)) atBot
      (𝓝 (-μ - kap k * (-1))) :=
    ((tendsto_tanh_kapMul k hk).const_mul (kap k)).const_sub (-μ)
  have hexp : Tendsto (fun t : ℝ => Real.exp (-μ * t)) atBot atTop :=
    Real.tendsto_exp_atTop.comp
      ((tendsto_const_mul_atTop_of_neg (by linarith : -μ < 0)).mpr tendsto_id)
  intro C
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hL : (0 : ℝ) < -μ - kap k * (-1) := by linarith
    have hprod : Tendsto (fun t => (-μ - kap k * Real.tanh (kap k * t)) * Real.exp (-μ * t))
        atBot atTop := Filter.Tendsto.pos_mul_atTop hL hpre hexp
    exact exists_lt_of_tendsto_abs_atTop (tendsto_abs_atTop_atTop.comp hprod) C
  · have hL : -μ - kap k * (-1) < 0 := by linarith
    have hprod : Tendsto (fun t => (-μ - kap k * Real.tanh (kap k * t)) * Real.exp (-μ * t))
        atBot atBot := Filter.Tendsto.neg_mul_atTop hL hpre hexp
    exact exists_lt_of_tendsto_abs_atTop (tendsto_abs_atBot_atTop.comp hprod) C

/-- The paper's `u_{k,0′}` is unbounded on the half line. -/
lemma uZeroPrime_unbounded (k : ℕ) (hk : 2 ≤ k) :
    ∀ C, ∃ t < (0 : ℝ), C < |uZeroPrime k t| := by
  have hneg : Tendsto (fun t : ℝ => -(kap k * t)) atBot atTop :=
    tendsto_neg_atBot_atTop.comp (tendsto_kapMul_atBot k hk)
  have hnegtanh : Tendsto (fun t : ℝ => -Real.tanh (kap k * t)) atBot (𝓝 1) := by
    simpa using (tendsto_tanh_kapMul k hk).neg
  have hprod : Tendsto (fun t => (-Real.tanh (kap k * t)) * (-(kap k * t))) atBot atTop :=
    Filter.Tendsto.pos_mul_atTop one_pos hnegtanh hneg
  have hprod' : Tendsto (fun t => kap k * t * Real.tanh (kap k * t)) atBot atTop :=
    hprod.congr fun t => by ring
  have hfin : Tendsto (fun t => kap k * t * Real.tanh (kap k * t) - 1) atBot atTop :=
    (tendsto_atTop_add_const_right atBot (-1 : ℝ) hprod').congr fun t => by ring
  intro C
  exact exists_lt_of_tendsto_abs_atTop (tendsto_abs_atTop_atTop.comp hfin) C

/-- `sinh → +∞` at `+∞`. -/
lemma tendsto_sinh_atTop : Tendsto Real.sinh atTop atTop := by
  have hsmall : Tendsto (fun y : ℝ => -Real.exp (-y)) atTop (𝓝 (-0)) :=
    (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).neg
  rw [neg_zero] at hsmall
  have hdiff : Tendsto (fun y : ℝ => -Real.exp (-y) + Real.exp y) atTop atTop :=
    hsmall.add_atTop Real.tendsto_exp_atTop
  have hdiff' : Tendsto (fun y : ℝ => (Real.exp y - Real.exp (-y)) / 2) atTop atTop :=
    (hdiff.congr fun y => by ring).atTop_div_const two_pos
  exact hdiff'.congr fun y => (Real.sinh_eq y).symm

/-- The paper's `u_{k,(k−1)′}` is unbounded on the half line. -/
lemma uKapPrime_unbounded (k : ℕ) (hk : 2 ≤ k) :
    ∀ C, ∃ t < (0 : ℝ), C < |uKapPrime k t| := by
  have hκ : 0 < kap k := kap_pos hk
  have hneg : Tendsto (fun t : ℝ => -(kap k * t)) atBot atTop :=
    tendsto_neg_atBot_atTop.comp (tendsto_kapMul_atBot k hk)
  -- the sech tail: κt / cosh (κt) → 0 at −∞
  have hxexp : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have htail0 : Tendsto (fun t : ℝ => 2 * (-(kap k * t) * Real.exp (-(-(kap k * t)))))
      atBot (𝓝 0) := by
    simpa using ((hxexp.comp hneg).const_mul 2)
  have htail : Tendsto (fun t : ℝ => kap k * t / Real.cosh (kap k * t)) atBot (𝓝 0) := by
    have habs : ∀ᶠ t in (atBot : Filter ℝ), |kap k * t / Real.cosh (kap k * t)| ≤
        2 * (-(kap k * t) * Real.exp (-(-(kap k * t)))) := by
      filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
      have hc : (0 : ℝ) < Real.cosh (kap k * t) := Real.cosh_pos _
      have hb : Real.exp (-(kap k * t)) / 2 ≤ Real.cosh (kap k * t) := by
        rw [Real.cosh_eq]
        have := Real.exp_pos (kap k * t)
        linarith
      have hnn : 0 ≤ -(kap k * t) := by nlinarith [kap_pos hk]
      rw [abs_div, abs_of_pos hc, abs_of_nonpos (by nlinarith [kap_pos hk] : kap k * t ≤ 0)]
      rw [div_le_iff₀ hc, neg_neg]
      have h2 : Real.exp (kap k * t) * Real.cosh (kap k * t) ≥
          Real.exp (kap k * t) * (Real.exp (-(kap k * t)) / 2) := by
        apply mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      have h3 : Real.exp (kap k * t) * Real.exp (-(kap k * t)) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (kap k * t)]
    have hnonneg : ∀ᶠ t in (atBot : Filter ℝ),
        0 ≤ |kap k * t / Real.cosh (kap k * t)| :=
      Filter.Eventually.of_forall fun t => abs_nonneg _
    have habs0 : Tendsto (fun t => |kap k * t / Real.cosh (kap k * t)|) atBot (𝓝 0) :=
      squeeze_zero' hnonneg habs htail0
    exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs0
  -- sinh (κt) → −∞ at −∞
  have hnegsinh : Tendsto (fun t : ℝ => -Real.sinh (kap k * t)) atBot atTop :=
    (tendsto_sinh_atTop.comp hneg).congr fun t => by
      simp [Function.comp, Real.sinh_neg]
  have hsum : Tendsto (fun t : ℝ =>
      -(kap k * t / Real.cosh (kap k * t)) + -Real.sinh (kap k * t)) atBot atTop :=
    (htail.neg.congr fun t => rfl).add_atTop hnegsinh
  have hfin : Tendsto (uKapPrime k) atBot atBot := by
    have h := tendsto_neg_atTop_atBot.comp hsum
    refine h.congr fun t => ?_
    simp only [Function.comp, uKapPrime]
    ring
  intro C
  exact exists_lt_of_tendsto_abs_atTop (tendsto_abs_atBot_atTop.comp hfin) C

/-! ### Cauchy uniqueness for the scalar system

The scalar equation is written as a first-order system on `ℝ × ℝ`.
A continuous coefficient is bounded on each compact interval, providing
the Lipschitz bound used by Cauchy uniqueness. -/

lemma cylSystem_lipschitz (p q : ℝ) (K : ℝ≥0) (hp : ‖p‖ ≤ K) (hq : ‖q‖ ≤ K) :
    LipschitzWith K (fun x : ℝ × ℝ => (p • x.2, q • x.1)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [Prod.dist_eq, dist_smul₀]
  apply max_le
  · exact mul_le_mul hp (le_max_right _ _) dist_nonneg K.coe_nonneg
  · exact mul_le_mul hq (le_max_left _ _) dist_nonneg K.coe_nonneg

/-- Uniqueness for the scalar second-order system on a closed interval, from
vanishing Cauchy data at an interior point.  The coefficient `q` need only be
continuous. -/
lemma cylSystem_zero_of_cauchy {a b t₀ : ℝ} (q : ℝ → ℝ) (hq : ContinuousOn q (Icc a b))
    (u u' : ℝ → ℝ) (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn u' (Icc a b))
    (hdu : ∀ t ∈ Ioo a b, HasDerivAt u (u' t) t)
    (hdu' : ∀ t ∈ Ioo a b, HasDerivAt u' (q t * u t) t)
    (ht : t₀ ∈ Ioo a b) (h0 : u t₀ = 0) (h0' : u' t₀ = 0) :
    ∀ t ∈ Icc a b, u t = 0 ∧ u' t = 0 := by
  obtain ⟨Q, hQ⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  let K : ℝ≥0 := ⟨max 1 Q, le_trans zero_le_one (le_max_left _ _)⟩
  have hl (t : ℝ) (htm : t ∈ Ioo a b) :
      LipschitzOnWith K (fun x : ℝ × ℝ => ((1 : ℝ) • x.2, q t • x.1)) Set.univ := by
    apply (cylSystem_lipschitz 1 (q t) K ?_ ?_).lipschitzOnWith
    · simp only [norm_one]
      exact_mod_cast le_max_left 1 Q
    · exact (hQ t (Ioo_subset_Icc_self htm)).trans (by exact_mod_cast le_max_right 1 Q)
  have he := ODE_solution_unique_of_mem_Icc hl ht (hu.prodMk hu')
    (fun t htm => (((hdu t htm).congr_deriv (one_smul ℝ (u' t)).symm).prodMk
      (hdu' t htm)))
    (fun _ _ => Set.mem_univ _)
    (continuousOn_const : ContinuousOn (fun _ : ℝ => ((0 : ℝ), (0 : ℝ))) (Icc a b))
    (fun t _ => by
      have hz : ((1 : ℝ) • ((0 : ℝ), (0 : ℝ)).2, q t • ((0 : ℝ), (0 : ℝ)).1) =
          ((0 : ℝ), (0 : ℝ)) := by
        simp
      rw [hz]
      exact hasDerivAt_const t ((0 : ℝ), (0 : ℝ)))
    (fun _ _ => Set.mem_univ _) (by simp [h0, h0'])
  intro t htm
  have h := he htm
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩


/-! ### The constant Wronskian -/

/-- The Wronskian `u v′ − v u′` of two solution pairs. -/
def wronsk (u u' v v' : ℝ → ℝ) (t : ℝ) : ℝ := u t * v' t - v t * u' t

lemma wronsk_hasDerivAt {k : ℕ} {μ : ℝ} {u u' v v' : ℝ → ℝ} {t : ℝ}
    (hu : HasDerivAt u (u' t) t) (hu' : HasDerivAt u' ((μ ^ 2 - Vcyl k t) * u t) t)
    (hv : HasDerivAt v (v' t) t) (hv' : HasDerivAt v' ((μ ^ 2 - Vcyl k t) * v t) t) :
    HasDerivAt (wronsk u u' v v') 0 t := by
  have h : HasDerivAt (wronsk u u' v v')
      (u' t * v' t + u t * ((μ ^ 2 - Vcyl k t) * v t) -
        (v' t * u' t + v t * ((μ ^ 2 - Vcyl k t) * u t))) t := (hu.mul hv').sub (hv.mul hu')
  exact h.congr_deriv (by ring)

/-- For two global solutions the Wronskian is constant; we normalise at `t = 0`,
where the model solutions have elementary values. -/
lemma wronsk_eq_wronsk_zero {k : ℕ} {μ : ℝ} {u u' v v' : ℝ → ℝ}
    (hu : IsCylSolOn k μ u u' univ) (hv : IsCylSolOn k μ v v' univ) (t : ℝ) :
    wronsk u u' v v' t = wronsk u u' v v' 0 := by
  have hd : ∀ x : ℝ, HasDerivAt (wronsk u u' v v') 0 x := fun x =>
    wronsk_hasDerivAt (hu.deriv_fst x trivial) (hu.deriv_snd x trivial)
      (hv.deriv_fst x trivial) (hv.deriv_snd x trivial)
  exact is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) t 0

/-! ### The span argument -/

/-- A solution on the open half line whose Cauchy data vanish at `t₀ = −1`
vanishes identically there.  (The basepoint is interior: the unknown solution
is never differentiated at `t = 0`.) -/
lemma solution_zero_of_cauchy_at_base {k : ℕ} {μ : ℝ} {w w' : ℝ → ℝ}
    (hw : IsCylSolOn k μ w w' (Iio 0))
    (h0 : w (-1) = 0) (h0' : w' (-1) = 0) : ∀ t < (0 : ℝ), w t = 0 := by
  intro t ht
  set a : ℝ := min t (-1) - 1 with ha
  set b : ℝ := max t (-1) / 2 with hb
  have hmaxneg : max t (-1) < 0 := by
    rcases max_cases t (-1) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · exact ht
    · norm_num
  have hb0 : b < 0 := by rw [hb]; linarith
  have hIcc : Icc a b ⊆ Iio 0 := fun x hx => lt_of_le_of_lt hx.2 hb0
  have hIoo : Ioo a b ⊆ Iio 0 := fun x hx => hIcc (Ioo_subset_Icc_self hx)
  have htm : t ∈ Icc a b := by
    constructor
    · have h1 : min t (-1) ≤ t := min_le_left _ _
      rw [ha]; linarith
    · rcases le_or_gt t (-1) with h | h
      · rw [hb, max_eq_right h]; linarith
      · rw [hb, max_eq_left h.le]; linarith
  have ht₀ : (-1:ℝ) ∈ Ioo a b := by
    constructor
    · have h1 : min t (-1) ≤ -1 := min_le_right _ _
      rw [ha]; linarith
    · rcases le_or_gt t (-1) with h | h
      · rw [hb, max_eq_right h]; norm_num
      · rw [hb, max_eq_left h.le]; linarith
  have hVc : Continuous (Vcyl k) := by
    apply continuous_const.div
    · exact (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).pow 2
    · exact fun s => pow_ne_zero 2 (Real.cosh_pos _).ne'
  have hq : ContinuousOn (fun s => μ ^ 2 - Vcyl k s) (Icc a b) :=
    (continuous_const.sub hVc).continuousOn
  have hcu : ContinuousOn w (Icc a b) := fun x hx =>
    ((hw.deriv_fst x (hIcc hx)).continuousAt).continuousWithinAt
  have hcu' : ContinuousOn w' (Icc a b) := fun x hx =>
    ((hw.deriv_snd x (hIcc hx)).continuousAt).continuousWithinAt
  have hzero := cylSystem_zero_of_cauchy (fun s => μ ^ 2 - Vcyl k s) hq w w' hcu hcu'
    (fun s hs => hw.deriv_fst s (hIoo hs)) (fun s hs => hw.deriv_snd s (hIoo hs))
    ht₀ h0 h0'
  exact (hzero t htm).1

/-- The span engine: a bounded solution on the open half line is a multiple of
a bounded global solution `u₁`, given a second global solution `u₂`
which is unbounded on the half line and has nonvanishing Wronskian against `u₁`. -/
lemma bounded_solution_eq_smul {k : ℕ} {μ : ℝ} {u₁ u₁' u₂ u₂' : ℝ → ℝ}
    (h₁ : IsCylSolOn k μ u₁ u₁' univ) (h₂ : IsCylSolOn k μ u₂ u₂' univ)
    (hW : wronsk u₁ u₁' u₂ u₂' 0 ≠ 0)
    (h₁b : ∃ C, ∀ t ≤ (0 : ℝ), |u₁ t| ≤ C)
    (h₂u : ∀ C, ∃ t < (0 : ℝ), C < |u₂ t|)
    {w w' : ℝ → ℝ} (hw : IsCylSolOn k μ w w' (Iio 0))
    (hwb : ∃ C, ∀ t < (0 : ℝ), |w t| ≤ C) :
    ∃ c, ∀ t < (0 : ℝ), w t = c * u₁ t := by
  have hWt : ∀ t, wronsk u₁ u₁' u₂ u₂' t = wronsk u₁ u₁' u₂ u₂' 0 := fun t =>
    wronsk_eq_wronsk_zero h₁ h₂ t
  have hW1 : u₁ (-1) * u₂' (-1) - u₂ (-1) * u₁' (-1) = wronsk u₁ u₁' u₂ u₂' 0 := hWt (-1)
  set W := wronsk u₁ u₁' u₂ u₂' 0 with hWdef
  set aa := (w (-1) * u₂' (-1) - w' (-1) * u₂ (-1)) / W with haa
  set bb := (u₁ (-1) * w' (-1) - u₁' (-1) * w (-1)) / W with hbb
  set z : ℝ → ℝ := fun t => w t - aa * u₁ t - bb * u₂ t with hz
  set z' : ℝ → ℝ := fun t => w' t - aa * u₁' t - bb * u₂' t with hz'
  have hzsol : IsCylSolOn k μ z z' (Iio 0) := by
    constructor
    · intro t htl
      exact ((hw.deriv_fst t htl).sub ((h₁.deriv_fst t trivial).const_mul aa)).sub
        ((h₂.deriv_fst t trivial).const_mul bb)
    · intro t htl
      have h := ((hw.deriv_snd t htl).sub ((h₁.deriv_snd t trivial).const_mul aa)).sub
        ((h₂.deriv_snd t trivial).const_mul bb)
      exact h.congr_deriv (by simp only [hz]; ring)
  have h0 : z (-1) = 0 := by
    simp only [hz, haa, hbb]
    field_simp
    linear_combination (-(w (-1))) * hW1
  have h0' : z' (-1) = 0 := by
    simp only [hz', haa, hbb]
    field_simp
    linear_combination (-(w' (-1))) * hW1
  have hzero : ∀ t < (0 : ℝ), z t = 0 := solution_zero_of_cauchy_at_base hzsol h0 h0'
  by_cases hbb0 : bb = 0
  · refine ⟨aa, fun t ht => ?_⟩
    have hzt := hzero t ht
    simp only [hz, hbb0, zero_mul, sub_zero] at hzt
    linarith
  · exfalso
    obtain ⟨Cw, hCw⟩ := hwb
    obtain ⟨C1, hC1⟩ := h₁b
    have hC1nn : 0 ≤ C1 := le_trans (abs_nonneg _) (hC1 0 le_rfl)
    obtain ⟨t, ht, hgt⟩ := h₂u ((Cw + |aa| * C1) / |bb|)
    have key : |bb| * |u₂ t| ≤ Cw + |aa| * C1 := by
      have hbu : bb * u₂ t = w t - aa * u₁ t := by
        have hzt := hzero t ht
        simp only [hz] at hzt
        linarith
      calc |bb| * |u₂ t| = |bb * u₂ t| := (abs_mul _ _).symm
        _ = |w t - aa * u₁ t| := by rw [hbu]
        _ ≤ |w t| + |aa * u₁ t| := abs_sub _ _
        _ ≤ Cw + |aa| * C1 := by
            rw [abs_mul]
            have h1 := hCw t ht
            have h2 := hC1 t ht.le
            have h3 := mul_le_mul_of_nonneg_left h2 (abs_nonneg aa)
            linarith
    have hpos : 0 < |bb| := abs_pos.mpr hbb0
    have hlt := (div_lt_iff₀ hpos).mp hgt
    nlinarith [key]

/-! ### The classification -/

/-- [ksindexi] Proposition `ode`, classification half: every bounded solution
of the radial equation on the open half line is a constant multiple of
`u_{k,μ}`.  Stated for `3 ≤ k` as in the paper (the proof uses only `2 ≤ k`,
i.e. `κ > 0`). -/
theorem ode_classification (k : ℕ) (hk : 3 ≤ k) {μ : ℝ} (hμ : 0 ≤ μ)
    {w w' : ℝ → ℝ} (hw : IsCylSolOn k μ w w' (Iio 0))
    (hwb : ∃ C, ∀ t < (0 : ℝ), |w t| ≤ C) :
    ∃ c, ∀ t < (0 : ℝ), w t = c * uCyl k μ t := by
  have hk2 : 2 ≤ k := by omega
  have hκ : 0 < kap k := kap_pos hk2
  have h₁b : ∃ C, ∀ t ≤ (0 : ℝ), |uCyl k μ t| ≤ C :=
    ⟨μ + kap k, uCyl_bounded k (by omega) hμ⟩
  rcases eq_or_lt_of_le hμ with hμ0 | hμpos
  · -- the exceptional parameter μ = 0: companion u_{k,0′}
    subst hμ0
    have hWval : wronsk (uCyl k 0) (uCylD k 0) (uZeroPrime k) (uZeroPrimeD k) 0 =
        -(kap k ^ 2) := by
      simp [wronsk]
    have hW : wronsk (uCyl k 0) (uCylD k 0) (uZeroPrime k) (uZeroPrimeD k) 0 ≠ 0 := by
      rw [hWval]
      exact neg_ne_zero.mpr (pow_ne_zero 2 hκ.ne')
    exact bounded_solution_eq_smul (uCyl_isCylSolOn k 0 univ) (uZeroPrime_isCylSolOn k univ)
      hW h₁b (uZeroPrime_unbounded k hk2) hw hwb
  rcases eq_or_ne μ (kap k) with hμκ | hμκ
  · -- the exceptional parameter μ = κ: companion u_{k,(k−1)′}
    subst hμκ
    have hWval : wronsk (uCyl k (kap k)) (uCylD k (kap k)) (uKapPrime k) (uKapPrimeD k) 0 =
        2 * kap k ^ 2 := by
      simp [wronsk]
      ring
    have hW : wronsk (uCyl k (kap k)) (uCylD k (kap k)) (uKapPrime k) (uKapPrimeD k) 0 ≠ 0 := by
      rw [hWval]
      positivity
    exact bounded_solution_eq_smul (uCyl_isCylSolOn k (kap k) univ)
      (uKapPrime_isCylSolOn k univ) hW h₁b (uKapPrime_unbounded k hk2) hw hwb
  · -- the generic parameter: companion u_{k,−μ}
    have h₂ : IsCylSolOn k μ (uCyl k (-μ)) (uCylD k (-μ)) univ := by
      constructor
      · exact fun t _ => uCyl_hasDerivAt k (-μ) t
      · exact fun t _ => (uCylD_hasDerivAt k (-μ) t).congr_deriv (by ring)
    have hsq : μ ^ 2 - kap k ^ 2 ≠ 0 := by
      intro h
      have h2 : (μ - kap k) * (μ + kap k) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact hμκ (by linarith)
      · nlinarith
    have hWval : wronsk (uCyl k μ) (uCylD k μ) (uCyl k (-μ)) (uCylD k (-μ)) 0 =
        2 * μ * (μ ^ 2 - kap k ^ 2) := by
      simp [wronsk]
      ring
    have hW : wronsk (uCyl k μ) (uCylD k μ) (uCyl k (-μ)) (uCylD k (-μ)) 0 ≠ 0 := by
      rw [hWval]
      exact mul_ne_zero (mul_ne_zero two_ne_zero hμpos.ne') hsq
    exact bounded_solution_eq_smul (uCyl_isCylSolOn k μ univ) h₂ hW h₁b
      (uCyl_neg_unbounded k hk2 hμpos hμκ) hw hwb

/-- [ksindexi] Proposition `ode` (open scalar form): for `k ≥ 3` and real
`μ ≥ 0`, the bounded solutions of the radial equation on the open half line
are exactly the constant multiples of `u_{k,μ}`. -/
theorem ode_bounded_solution_iff (k : ℕ) (hk : 3 ≤ k) {μ : ℝ} (hμ : 0 ≤ μ) (w : ℝ → ℝ) :
    ((∃ w', IsCylSolOn k μ w w' (Iio 0)) ∧ ∃ C, ∀ t < (0 : ℝ), |w t| ≤ C) ↔
      ∃ c, ∀ t < (0 : ℝ), w t = c * uCyl k μ t := by
  constructor
  · rintro ⟨⟨w', hw⟩, hwb⟩
    exact ode_classification k hk hμ hw hwb
  · rintro ⟨c, hc⟩
    refine ⟨⟨fun t => c * uCylD k μ t, ?_, ?_⟩, ?_⟩
    · intro t ht
      have hev : (fun s => c * uCyl k μ s) =ᶠ[nhds t] w := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        exact (hc s hs).symm
      exact (((uCyl_hasDerivAt k μ t).const_mul c).congr_of_eventuallyEq hev.symm)
    · intro t ht
      have hwt := hc t ht
      exact ((uCylD_hasDerivAt k μ t).const_mul c).congr_deriv (by rw [hwt]; ring)
    · refine ⟨|c| * (μ + kap k), fun t ht => ?_⟩
      rw [hc t ht, abs_mul]
      exact mul_le_mul_of_nonneg_left (uCyl_bounded k (by omega) hμ t ht.le) (abs_nonneg c)

/-- [ksindexi] Proposition `ode` (closed form, the paper's `(−∞,0]`): a
solution on the open half line which is continuous up to `t = 0` from the left
and bounded on the closed half line is a constant multiple of `u_{k,μ}` on all
of `(−∞,0]`.  The extension to the endpoint uses only one-sided continuity;
no derivative of the unknown solution at `0` is assumed. -/
theorem ode_classification_closed (k : ℕ) (hk : 3 ≤ k) {μ : ℝ} (hμ : 0 ≤ μ)
    {w w' : ℝ → ℝ} (hw : IsCylSolOn k μ w w' (Iio 0))
    (hwc : ContinuousWithinAt w (Iio 0) 0)
    (hwb : ∃ C, ∀ t ≤ (0 : ℝ), |w t| ≤ C) :
    ∃ c, ∀ t ≤ (0 : ℝ), w t = c * uCyl k μ t := by
  obtain ⟨C, hC⟩ := hwb
  obtain ⟨c, hc⟩ := ode_classification k hk hμ hw ⟨C, fun t ht => hC t ht.le⟩
  refine ⟨c, fun t ht => ?_⟩
  rcases lt_or_eq_of_le ht with hlt | heq
  · exact hc t hlt
  · subst heq
    have h1 : Tendsto w (nhdsWithin 0 (Iio 0)) (nhds (w 0)) := hwc
    have hmodel : Tendsto (fun s => c * uCyl k μ s) (nhdsWithin (0 : ℝ) (Iio 0))
        (nhds (c * uCyl k μ 0)) :=
      (Filter.Tendsto.const_mul c (uCyl_hasDerivAt k μ 0).continuousAt).mono_left
        nhdsWithin_le_nhds
    have hev : (fun s => c * uCyl k μ s) =ᶠ[nhdsWithin (0 : ℝ) (Iio 0)] w := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hc s hs).symm
    have h2 : Tendsto w (nhdsWithin (0 : ℝ) (Iio 0)) (nhds (c * uCyl k μ 0)) :=
      hmodel.congr' hev
    exact tendsto_nhds_unique h1 h2

/-! ### The cylinder operator and rotational invariance -/

/-- The classical eigenvalue equation `cylop_k u = λ u` on a strip `s × ℝ` of
the cylinder, in slice form with all four partial derivatives carried
explicitly ([ksindexi] tex 1418–1438: `cylop_k = ∂²_t + ∂²_θ + V`).  For a
`2π`-periodic function this is the equation on `s × S¹`; a rotationally
invariant function is automatically periodic. -/
structure IsCylopEigenOn (k : ℕ) (lam : ℝ) (u ut utt uθ uθθ : ℝ → ℝ → ℝ)
    (s : Set ℝ) : Prop where
  deriv_t : ∀ θ : ℝ, ∀ t ∈ s, HasDerivAt (fun t' => u t' θ) (ut t θ) t
  deriv_tt : ∀ θ : ℝ, ∀ t ∈ s, HasDerivAt (fun t' => ut t' θ) (utt t θ) t
  deriv_th : ∀ t ∈ s, ∀ θ : ℝ, HasDerivAt (fun θ' => u t θ') (uθ t θ) θ
  deriv_thth : ∀ t ∈ s, ∀ θ : ℝ, HasDerivAt (fun θ' => uθ t θ') (uθθ t θ) θ
  eigen : ∀ t ∈ s, ∀ θ : ℝ, utt t θ + uθθ t θ + Vcyl k t * u t θ = lam * u t θ

/-- A rotationally invariant eigenfunction of `cylop_k` restricts on the slice
`θ = 0` to a solution of the radial ODE: the angular derivatives of an
invariant function vanish by uniqueness of derivatives. -/
lemma IsCylopEigenOn.isCylSolOn_of_invariant {k : ℕ} {μ : ℝ}
    {u ut utt uθ uθθ : ℝ → ℝ → ℝ} {s : Set ℝ}
    (h : IsCylopEigenOn k (μ ^ 2) u ut utt uθ uθθ s)
    (hinv : ∀ t ∈ s, ∀ θ θ', u t θ = u t θ') :
    IsCylSolOn k μ (fun t => u t 0) (fun t => ut t 0) s := by
  have huθ : ∀ t ∈ s, ∀ θ : ℝ, uθ t θ = 0 := by
    intro t ht θ
    have hconst : HasDerivAt (fun θ' : ℝ => u t θ') (0 : ℝ) θ :=
      (hasDerivAt_const θ (u t θ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun θ' => hinv t ht θ' θ)
    exact (h.deriv_th t ht θ).unique hconst
  have huθθ : ∀ t ∈ s, ∀ θ : ℝ, uθθ t θ = 0 := by
    intro t ht θ
    have hconst : HasDerivAt (fun θ' : ℝ => uθ t θ') (0 : ℝ) θ :=
      (hasDerivAt_const θ (0 : ℝ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun θ' => huθ t ht θ')
    exact (h.deriv_thth t ht θ).unique hconst
  constructor
  · exact fun t ht => h.deriv_t 0 t ht
  · intro t ht
    have heig := h.eigen t ht 0
    rw [huθθ t ht 0] at heig
    have hval : utt t 0 = (μ ^ 2 - Vcyl k t) * u t 0 := by linear_combination heig
    exact hval ▸ h.deriv_tt 0 t ht

/-- [ksindexi] Proposition `ode`, open-cylinder form: for integer `k ≥ 3` and real
`μ ≥ 0`, every bounded rotationally invariant solution of `cylop_k u = μ² u`
on the open half cylinder is a constant multiple of `u_{k,μ}`.  Together with
`smul_uCyl_isCylopEigen` (the easy inclusion), the bounded invariant solution
space is exactly the span of `u_{k,μ}`. -/
theorem ode_proposition (k : ℕ) (hk : 3 ≤ k) {μ : ℝ} (hμ : 0 ≤ μ)
    {u ut utt uθ uθθ : ℝ → ℝ → ℝ}
    (hinv : ∀ t < (0 : ℝ), ∀ θ θ', u t θ = u t θ')
    (heig : IsCylopEigenOn k (μ ^ 2) u ut utt uθ uθθ (Iio 0))
    (hub : ∃ C, ∀ t < (0 : ℝ), ∀ θ : ℝ, |u t θ| ≤ C) :
    ∃ c, ∀ t < (0 : ℝ), ∀ θ : ℝ, u t θ = c * uCyl k μ t := by
  obtain ⟨C, hC⟩ := hub
  obtain ⟨c, hc⟩ := ode_classification k hk hμ (heig.isCylSolOn_of_invariant hinv)
    ⟨C, fun t ht => hC t ht 0⟩
  exact ⟨c, fun t ht θ => (hinv t ht θ 0).trans (hc t ht)⟩

/-- The easy inclusion of [ksindexi] Proposition `ode`: each constant multiple
of `u_{k,μ}` is a bounded rotationally invariant eigenfunction of `cylop_k`
on the half cylinder. -/
theorem smul_uCyl_isCylopEigen (k : ℕ) (hk : 3 ≤ k) {μ : ℝ} (hμ : 0 ≤ μ) (c : ℝ) :
    IsCylopEigenOn k (μ ^ 2) (fun t _ => c * uCyl k μ t) (fun t _ => c * uCylD k μ t)
      (fun t _ => c * ((μ ^ 2 - Vcyl k t) * uCyl k μ t)) (fun _ _ => 0) (fun _ _ => 0)
      (Iio 0) ∧
      ∃ C, ∀ t < (0 : ℝ), ∀ _θ : ℝ, |c * uCyl k μ t| ≤ C := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact fun θ t _ => (uCyl_hasDerivAt k μ t).const_mul c
    · exact fun θ t _ => (uCylD_hasDerivAt k μ t).const_mul c
    · exact fun t _ θ => hasDerivAt_const θ _
    · exact fun t _ θ => hasDerivAt_const θ _
    · intro t _ θ
      ring
  · refine ⟨|c| * (μ + kap k), fun t ht _ => ?_⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (uCyl_bounded k (by omega) hμ t ht.le) (abs_nonneg c)


/-! ### Consistency with the integer-mode disk tier -/

/-- On integer modes the cylinder solution is the `RadialMode` disk solution
read through `r = e^t`: `u_{k,ℓ}(t) = uRad k ℓ (e^t)`.  This ties the
real-parameter tier of this file to the integer-mode tier consumed by the
Fourier analysis (`RadialMode`, `FiniteEnergyRadialClassification`). -/
lemma uCyl_eq_uRad_exp (k : ℕ) (hk : 2 ≤ k) (ℓ : ℕ) (t : ℝ) :
    uCyl k ℓ t = uRad k ℓ (Real.exp t) := by
  have hE : Real.exp t ^ (2 * k - 2) = Real.exp (kap k * t) * Real.exp (kap k * t) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, cast_two_k_sub_two hk]
    congr 1
    unfold kap
    ring
  have hpow : Real.exp t ^ ℓ = Real.exp ((ℓ : ℝ) * t) := by
    rw [← Real.exp_nat_mul]
  have hden : Real.exp (kap k * t) * Real.exp (kap k * t) + 1 ≠ 0 := by positivity
  unfold uCyl uRad gRad
  rw [tanh_eq_exp_form, hE, hpow]
  field_simp
  ring

/-- [ksindexi] Proposition `ode` on the closed half cylinder `(−∞,0] × S¹`:
the hypotheses ask for the equation only on the open interior together with
one-sided continuity of the slice at `t = 0`, boundedness on the closed half
cylinder, and rotational invariance there. No endpoint derivative is required. -/
theorem ode_proposition_closed (k : ℕ) (hk : 3 ≤ k) {μ : ℝ} (hμ : 0 ≤ μ)
    {u ut utt uθ uθθ : ℝ → ℝ → ℝ}
    (hinv : ∀ t ≤ (0 : ℝ), ∀ θ θ', u t θ = u t θ')
    (heig : IsCylopEigenOn k (μ ^ 2) u ut utt uθ uθθ (Iio 0))
    (hwc : ContinuousWithinAt (fun t => u t 0) (Iio 0) 0)
    (hub : ∃ C, ∀ t ≤ (0 : ℝ), ∀ θ : ℝ, |u t θ| ≤ C) :
    ∃ c, ∀ t ≤ (0 : ℝ), ∀ θ : ℝ, u t θ = c * uCyl k μ t := by
  obtain ⟨C, hC⟩ := hub
  obtain ⟨c, hc⟩ := ode_classification_closed k hk hμ
    (heig.isCylSolOn_of_invariant fun t ht => hinv t ht.le)
    hwc ⟨C, fun t ht => hC t ht 0⟩
  exact ⟨c, fun t ht θ => (hinv t ht θ 0).trans (hc t ht)⟩

/-! ### Complex-valued wrappers

The paper's function spaces are over ℂ ([ksindexi] tex 793–799, 549–550), so
the source proposition classifies COMPLEX bounded invariant solutions, with a
complex spanning constant.  The real tier above is the analytic engine; the
wrappers below split a complex solution into its components, classify each,
and reconstruct `c : ℂ`.  No energy or centre-regularity assumption enters. -/

lemma hasDerivAt_complex_re {f : ℝ → ℂ} {v : ℂ} {t : ℝ} (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => (f s).re) v.re t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf

lemma hasDerivAt_complex_im {f : ℝ → ℂ} {v : ℂ} {t : ℝ} (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => (f s).im) v.im t :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf

lemma hasDerivAt_ofReal_comp {f : ℝ → ℝ} {v t : ℝ} (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => ((f s : ℝ) : ℂ)) ((v : ℝ) : ℂ) t :=
  Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hf

/-- Complex-valued classical solution pair of the mode equation. -/
structure IsCylSolOnC (k : ℕ) (μ : ℝ) (u u' : ℝ → ℂ) (s : Set ℝ) : Prop where
  deriv_fst : ∀ t ∈ s, HasDerivAt u (u' t) t
  deriv_snd : ∀ t ∈ s, HasDerivAt u' (((μ ^ 2 - Vcyl k t : ℝ) : ℂ) * u t) t

lemma IsCylSolOnC.re {k : ℕ} {μ : ℝ} {u u' : ℝ → ℂ} {s : Set ℝ}
    (h : IsCylSolOnC k μ u u' s) :
    IsCylSolOn k μ (fun t => (u t).re) (fun t => (u' t).re) s := by
  constructor
  · exact fun t ht => hasDerivAt_complex_re (h.deriv_fst t ht)
  · intro t ht
    have hd := hasDerivAt_complex_re (h.deriv_snd t ht)
    rwa [Complex.re_ofReal_mul] at hd

lemma IsCylSolOnC.im {k : ℕ} {μ : ℝ} {u u' : ℝ → ℂ} {s : Set ℝ}
    (h : IsCylSolOnC k μ u u' s) :
    IsCylSolOn k μ (fun t => (u t).im) (fun t => (u' t).im) s := by
  constructor
  · exact fun t ht => hasDerivAt_complex_im (h.deriv_fst t ht)
  · intro t ht
    have hd := hasDerivAt_complex_im (h.deriv_snd t ht)
    rwa [Complex.im_ofReal_mul] at hd

/-- [ksindexi] Proposition `ode`, complex scalar form (open): every bounded
complex solution of the radial equation on the open half line is a complex
constant multiple of `u_{k,μ}`. -/
theorem ode_classificationC (k : ℕ) (hk : 3 ≤ k) {μ : ℝ} (hμ : 0 ≤ μ)
    {w w' : ℝ → ℂ} (hw : IsCylSolOnC k μ w w' (Iio 0))
    (hwb : ∃ C, ∀ t < (0 : ℝ), ‖w t‖ ≤ C) :
    ∃ c : ℂ, ∀ t < (0 : ℝ), w t = c * (uCyl k μ t : ℂ) := by
  obtain ⟨C, hC⟩ := hwb
  obtain ⟨c₁, h₁⟩ := ode_classification k hk hμ hw.re
    ⟨C, fun t ht => (Complex.abs_re_le_norm _).trans (hC t ht)⟩
  obtain ⟨c₂, h₂⟩ := ode_classification k hk hμ hw.im
    ⟨C, fun t ht => (Complex.abs_im_le_norm _).trans (hC t ht)⟩
  refine ⟨Complex.mk c₁ c₂, fun t ht => ?_⟩
  apply Complex.ext
  · simpa [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using h₁ t ht
  · simpa [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using h₂ t ht

/-- [ksindexi] Proposition `ode`, complex scalar form (closed). -/
theorem ode_classification_closedC (k : ℕ) (hk : 3 ≤ k) {μ : ℝ} (hμ : 0 ≤ μ)
    {w w' : ℝ → ℂ} (hw : IsCylSolOnC k μ w w' (Iio 0))
    (hwc : ContinuousWithinAt w (Iio 0) 0)
    (hwb : ∃ C, ∀ t ≤ (0 : ℝ), ‖w t‖ ≤ C) :
    ∃ c : ℂ, ∀ t ≤ (0 : ℝ), w t = c * (uCyl k μ t : ℂ) := by
  obtain ⟨C, hC⟩ := hwb
  obtain ⟨c, hc⟩ := ode_classificationC k hk hμ hw ⟨C, fun t ht => hC t ht.le⟩
  refine ⟨c, fun t ht => ?_⟩
  rcases lt_or_eq_of_le ht with hlt | heq
  · exact hc t hlt
  · subst heq
    have h1 : Tendsto w (nhdsWithin 0 (Iio 0)) (nhds (w 0)) := hwc
    have hmodel : Tendsto (fun s => c * ((uCyl k μ s : ℝ) : ℂ))
        (nhdsWithin (0 : ℝ) (Iio 0)) (nhds (c * ((uCyl k μ 0 : ℝ) : ℂ))) := by
      have hco : Tendsto (fun s => ((uCyl k μ s : ℝ) : ℂ)) (nhds (0 : ℝ))
          (nhds ((uCyl k μ 0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp (uCyl_hasDerivAt k μ 0).continuousAt
      exact (hco.const_mul c).mono_left nhdsWithin_le_nhds
    have hev : (fun s => c * ((uCyl k μ s : ℝ) : ℂ)) =ᶠ[nhdsWithin (0 : ℝ) (Iio 0)] w := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hc s hs).symm
    exact tendsto_nhds_unique h1 (hmodel.congr' hev)

/-- The complex classical slice-form `cylop_k` eigenequation. -/
structure IsCylopEigenOnC (k : ℕ) (lam : ℝ) (u ut utt uθ uθθ : ℝ → ℝ → ℂ)
    (s : Set ℝ) : Prop where
  deriv_t : ∀ θ : ℝ, ∀ t ∈ s, HasDerivAt (fun t' => u t' θ) (ut t θ) t
  deriv_tt : ∀ θ : ℝ, ∀ t ∈ s, HasDerivAt (fun t' => ut t' θ) (utt t θ) t
  deriv_th : ∀ t ∈ s, ∀ θ : ℝ, HasDerivAt (fun θ' => u t θ') (uθ t θ) θ
  deriv_thth : ∀ t ∈ s, ∀ θ : ℝ, HasDerivAt (fun θ' => uθ t θ') (uθθ t θ) θ
  eigen : ∀ t ∈ s, ∀ θ : ℝ,
    utt t θ + uθθ t θ + ((Vcyl k t : ℝ) : ℂ) * u t θ = ((lam : ℝ) : ℂ) * u t θ

/-- A rotationally invariant complex eigenfunction restricts on the slice
`θ = 0` to a complex solution of the radial ODE. -/
lemma IsCylopEigenOnC.isCylSolOnC_of_invariant {k : ℕ} {μ : ℝ}
    {u ut utt uθ uθθ : ℝ → ℝ → ℂ} {s : Set ℝ}
    (h : IsCylopEigenOnC k (μ ^ 2) u ut utt uθ uθθ s)
    (hinv : ∀ t ∈ s, ∀ θ θ', u t θ = u t θ') :
    IsCylSolOnC k μ (fun t => u t 0) (fun t => ut t 0) s := by
  have huθ : ∀ t ∈ s, ∀ θ : ℝ, uθ t θ = 0 := by
    intro t ht θ
    have hconst : HasDerivAt (fun θ' : ℝ => u t θ') (0 : ℂ) θ :=
      (hasDerivAt_const θ (u t θ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun θ' => hinv t ht θ' θ)
    exact (h.deriv_th t ht θ).unique hconst
  have huθθ : ∀ t ∈ s, ∀ θ : ℝ, uθθ t θ = 0 := by
    intro t ht θ
    have hconst : HasDerivAt (fun θ' : ℝ => uθ t θ') (0 : ℂ) θ :=
      (hasDerivAt_const θ (0 : ℂ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun θ' => huθ t ht θ')
    exact (h.deriv_thth t ht θ).unique hconst
  constructor
  · exact fun t ht => h.deriv_t 0 t ht
  · intro t ht
    have heig := h.eigen t ht 0
    rw [huθθ t ht 0] at heig
    have hval : utt t 0 = ((μ ^ 2 - Vcyl k t : ℝ) : ℂ) * u t 0 := by
      push_cast
      push_cast at heig
      linear_combination heig
    exact hval ▸ h.deriv_tt 0 t ht

/-- [ksindexi] Proposition `ode`, complex open-cylinder form. -/
theorem ode_propositionC (k : ℕ) (hk : 3 ≤ k) {μ : ℝ} (hμ : 0 ≤ μ)
    {u ut utt uθ uθθ : ℝ → ℝ → ℂ}
    (hinv : ∀ t < (0 : ℝ), ∀ θ θ', u t θ = u t θ')
    (heig : IsCylopEigenOnC k (μ ^ 2) u ut utt uθ uθθ (Iio 0))
    (hub : ∃ C, ∀ t < (0 : ℝ), ∀ θ : ℝ, ‖u t θ‖ ≤ C) :
    ∃ c : ℂ, ∀ t < (0 : ℝ), ∀ θ : ℝ, u t θ = c * (uCyl k μ t : ℂ) := by
  obtain ⟨C, hC⟩ := hub
  obtain ⟨c, hc⟩ := ode_classificationC k hk hμ (heig.isCylSolOnC_of_invariant hinv)
    ⟨C, fun t ht => hC t ht 0⟩
  exact ⟨c, fun t ht θ => (hinv t ht θ 0).trans (hc t ht)⟩

/-- [ksindexi] Proposition `ode`, complex closed-cylinder form with one-sided continuity. -/
theorem ode_proposition_closedC (k : ℕ) (hk : 3 ≤ k) {μ : ℝ} (hμ : 0 ≤ μ)
    {u ut utt uθ uθθ : ℝ → ℝ → ℂ}
    (hinv : ∀ t ≤ (0 : ℝ), ∀ θ θ', u t θ = u t θ')
    (heig : IsCylopEigenOnC k (μ ^ 2) u ut utt uθ uθθ (Iio 0))
    (hwc : ContinuousWithinAt (fun t => u t 0) (Iio 0) 0)
    (hub : ∃ C, ∀ t ≤ (0 : ℝ), ∀ θ : ℝ, ‖u t θ‖ ≤ C) :
    ∃ c : ℂ, ∀ t ≤ (0 : ℝ), ∀ θ : ℝ, u t θ = c * (uCyl k μ t : ℂ) := by
  obtain ⟨C, hC⟩ := hub
  obtain ⟨c, hc⟩ := ode_classification_closedC k hk hμ
    (heig.isCylSolOnC_of_invariant fun t ht => hinv t ht.le)
    hwc ⟨C, fun t ht => hC t ht 0⟩
  exact ⟨c, fun t ht θ => (hinv t ht θ 0).trans (hc t ht)⟩

/-- The easy inclusion, complex form: every complex multiple of `u_{k,μ}` is a
bounded rotationally invariant eigenfunction of `cylop_k`. -/
theorem smul_uCyl_isCylopEigenC (k : ℕ) (hk : 3 ≤ k) {μ : ℝ} (hμ : 0 ≤ μ) (c : ℂ) :
    IsCylopEigenOnC k (μ ^ 2) (fun t _ => c * (uCyl k μ t : ℂ))
      (fun t _ => c * (uCylD k μ t : ℂ))
      (fun t _ => c * (((μ ^ 2 - Vcyl k t) * uCyl k μ t : ℝ) : ℂ))
      (fun _ _ => 0) (fun _ _ => 0) (Iio 0) ∧
      ∃ C, ∀ t < (0 : ℝ), ∀ _θ : ℝ, ‖c * (uCyl k μ t : ℂ)‖ ≤ C := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact fun θ t _ => (hasDerivAt_ofReal_comp (uCyl_hasDerivAt k μ t)).const_mul c
    · exact fun θ t _ => (hasDerivAt_ofReal_comp (uCylD_hasDerivAt k μ t)).const_mul c
    · exact fun t _ θ => hasDerivAt_const θ _
    · exact fun t _ θ => hasDerivAt_const θ _
    · intro t _ θ
      push_cast
      ring
  · refine ⟨‖c‖ * (μ + kap k), fun t ht _ => ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (uCyl_bounded k (by omega) hμ t ht.le) (norm_nonneg c)

end KsIndex.Radial
