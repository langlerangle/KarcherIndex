module

public import Mathlib

@[expose] public section


/-! Fourier-integral recurrence for endpoint-adapted arc trial functions.
For positive β, the recurrence reduces integer-frequency coefficients of
cos(x)^β on [-π/2,π/2] to two initial integrals. No numerical bound for these
integrals or spectral certificate is asserted here.
-/
noncomputable section
namespace KsIndex.PowerArc
open Real intervalIntegral Filter Topology

def g (β ξ : ℝ) : ℝ :=
  2 * ∫ x in (0 : ℝ)..(π / 2), (Real.cos x) ^ β * Real.cos (ξ * x)

theorem g_neg (β ξ : ℝ) : g β (-ξ) = g β ξ := by
  simp [g, neg_mul, Real.cos_neg]

theorem g_recursion {β : ℝ} (hβ : 0 < β) (ξ : ℝ) :
    (ξ + (β + 1)) * g β (ξ + 1) = ((β + 1) - ξ) * g β (ξ - 1) := by
  have hpow : Continuous fun x : ℝ => (Real.cos x) ^ β :=
    (Real.continuous_rpow_const hβ.le).comp Real.continuous_cos
  have hpow1 : Continuous fun x : ℝ => (Real.cos x) ^ (β + 1) :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ β + 1)).comp Real.continuous_cos
  have hπ : (0 : ℝ) ≤ π / 2 := by positivity
  -- Continuity of every integrand in sight.
  have hcontp : Continuous fun x : ℝ => (Real.cos x) ^ β * Real.cos ((ξ + 1) * x) := by
    fun_prop
  have hcontm : Continuous fun x : ℝ => (Real.cos x) ^ β * Real.cos ((ξ - 1) * x) := by
    fun_prop
  have hcontA : Continuous fun x : ℝ =>
      (Real.cos x) ^ β * (Real.cos x * Real.cos (ξ * x)) := by fun_prop
  have hcontB : Continuous fun x : ℝ =>
      (Real.cos x) ^ β * (Real.sin x * Real.sin (ξ * x)) := by fun_prop
  have hcontD : Continuous fun x : ℝ =>
      ξ * ((Real.cos x) ^ β * (Real.cos x * Real.cos (ξ * x)))
        - (β + 1) * ((Real.cos x) ^ β * (Real.sin x * Real.sin (ξ * x))) := by fun_prop
  -- The boundary function `F = cos^(β+1)·sin(ξ·)` and its derivative on `(0, π/2)`.
  have hF : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2),
      HasDerivAt (fun y => (Real.cos y) ^ (β + 1) * Real.sin (ξ * y))
        (ξ * ((Real.cos x) ^ β * (Real.cos x * Real.cos (ξ * x)))
          - (β + 1) * ((Real.cos x) ^ β * (Real.sin x * Real.sin (ξ * x)))) x := by
    intro x hx
    have hcos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos, hx.1], hx.2⟩
    have hd := ((Real.hasDerivAt_cos x).rpow_const
      (p := β + 1) (Or.inl hcos.ne')).mul
      (((hasDerivAt_id x).const_mul ξ).sin)
    have hp : (Real.cos x) ^ (β + 1) = (Real.cos x) ^ β * Real.cos x := by
      rw [Real.rpow_add hcos, Real.rpow_one]
    convert! hd using 1
    simp only [show β + 1 - 1 = β by ring, hp, id_eq]
    ring
  -- FTC: the derivative integrates to `F(π/2) - F(0) = 0`.
  have hFTC : ∫ x in (0:ℝ)..(π/2),
      (ξ * ((Real.cos x) ^ β * (Real.cos x * Real.cos (ξ * x)))
        - (β + 1) * ((Real.cos x) ^ β * (Real.sin x * Real.sin (ξ * x)))) = 0 := by
    have hcontF : ContinuousOn
        (fun y => (Real.cos y) ^ (β + 1) * Real.sin (ξ * y))
        (Set.Icc (0:ℝ) (π/2)) := Continuous.continuousOn (by fun_prop)
    have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hπ hcontF
      (fun x hx => (hF x hx).hasDerivWithinAt) (hcontD.intervalIntegrable _ _)
    rw [h]
    simp [Real.cos_pi_div_two, Real.zero_rpow (show β + 1 ≠ 0 by linarith)]
  -- Split the integral into the two `g`-values via product-to-sum identities.
  have hA : (∫ x in (0:ℝ)..(π/2), (Real.cos x) ^ β * (Real.cos x * Real.cos (ξ * x)))
      = (g β (ξ + 1) + g β (ξ - 1)) / 4 := by
    have hpt : ∀ x : ℝ, (Real.cos x) ^ β * (Real.cos x * Real.cos (ξ * x))
        = ((Real.cos x) ^ β * Real.cos ((ξ + 1) * x)
            + (Real.cos x) ^ β * Real.cos ((ξ - 1) * x)) / 2 := by
      intro x
      rw [show (ξ + 1) * x = ξ * x + x by ring, show (ξ - 1) * x = ξ * x - x by ring,
          Real.cos_add, Real.cos_sub]
      ring
    rw [intervalIntegral.integral_congr fun x _ => hpt x, intervalIntegral.integral_div,
        intervalIntegral.integral_add (hcontp.intervalIntegrable _ _)
          (hcontm.intervalIntegrable _ _)]
    unfold g
    ring
  have hB : (∫ x in (0:ℝ)..(π/2), (Real.cos x) ^ β * (Real.sin x * Real.sin (ξ * x)))
      = (g β (ξ - 1) - g β (ξ + 1)) / 4 := by
    have hpt : ∀ x : ℝ, (Real.cos x) ^ β * (Real.sin x * Real.sin (ξ * x))
        = ((Real.cos x) ^ β * Real.cos ((ξ - 1) * x)
            - (Real.cos x) ^ β * Real.cos ((ξ + 1) * x)) / 2 := by
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
        ((hcontB.intervalIntegrable _ _).const_mul ((β + 1))),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hA, hB] at hFTC
  linear_combination 4 * hFTC


theorem g_step_two {β : ℝ} (hβ : 0 < β) (ξ : ℝ) :
    (ξ + β + 2) * g β (ξ + 2) = (β - ξ) * g β ξ := by
  have h := g_recursion hβ (ξ + 1)
  convert! h using 1 <;> ring_nf

/-- The discrete primitive for the leading weighted square tail. -/
def energyPrimitive (β ξ : ℝ) : ℝ := ((ξ + β) * g β ξ) ^ 2 / (4 * β)

lemma energyPrimitive_nonneg {β : ℝ} (hβ : 0 < β) (ξ : ℝ) :
    0 ≤ energyPrimitive β ξ := div_nonneg (sq_nonneg _) (by positivity)

/-- Exact telescoping identity; no asymptotic approximation is used. -/
theorem energyPrimitive_step {β : ℝ} (hβ : 0 < β) (ξ : ℝ) :
    energyPrimitive β ξ - energyPrimitive β (ξ + 2) = ξ * g β ξ ^ 2 := by
  unfold energyPrimitive
  rw [show ξ + 2 + β = ξ + β + 2 by ring, g_step_two hβ ξ]
  field_simp
  ring

theorem weighted_sum_range {β : ℝ} (hβ : 0 < β) (r : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (r + 2 * n) * g β (r + 2 * n) ^ 2) =
      energyPrimitive β r - energyPrimitive β (r + 2 * N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h := energyPrimitive_step hβ (r + 2 * N)
    push_cast
    rw [show r + 2 * ((N : ℝ) + 1) = (r + 2 * N) + 2 by ring]
    linarith

/-- A proved bound on the entire leading-energy tail from any nonnegative
starting frequency. -/
theorem weighted_summable_and_bound {β : ℝ} (hβ : 0 < β) {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun n : ℕ => (r + 2 * n) * g β (r + 2 * n) ^ 2) ∧
      (∑' n : ℕ, (r + 2 * n) * g β (r + 2 * n) ^ 2) ≤ energyPrimitive β r := by
  have hnonneg : ∀ n : ℕ, 0 ≤ (r + 2 * n) * g β (r + 2 * n) ^ 2 := by
    intro n
    positivity
  have hbound : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, (r + 2 * n) * g β (r + 2 * n) ^ 2) ≤
        energyPrimitive β r := by
    intro N
    rw [weighted_sum_range hβ]
    exact sub_le_self _ (energyPrimitive_nonneg hβ _)
  exact ⟨summable_of_sum_range_le hnonneg hbound,
    Real.tsum_le_of_sum_range_le hnonneg hbound⟩

private lemma limit_zero_of_antitone_harmonic {t : ℕ → ℝ}
    (ht : ∀ n, 0 ≤ t n) (ha : Antitone t)
    (hs : Summable (fun n => t n / (n + 1))) :
    Tendsto t atTop (𝓝 0) := by
  have hb : BddBelow (Set.range t) := ⟨0, by rintro _ ⟨n, rfl⟩; exact ht n⟩
  have hl : 0 ≤ ⨅ n, t n := le_ciInf ht
  have he : (⨅ n, t n) = 0 := by
    by_contra h
    have hp : 0 < ⨅ n, t n := lt_of_le_of_ne hl (Ne.symm h)
    have hsum : Summable (fun n : ℕ => (⨅ n, t n) / (n + 1)) := by
      apply hs.of_nonneg_of_le
      · intro n
        positivity
      · intro n
        exact div_le_div_of_nonneg_right (ciInf_le hb n) (by positivity)
    have hsum1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
      have hh := hsum.mul_left (⨅ n, t n)⁻¹
      simpa only [← mul_div_assoc, inv_mul_cancel₀ hp.ne'] using hh
    have hsum0 : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
      apply (summable_nat_add_iff 1).mp
      simpa only [Nat.cast_add, Nat.cast_one] using hsum1
    exact not_summable_one_div_natCast hsum0
  simpa only [he] using tendsto_atTop_ciInf ha hb

lemma energyPrimitive_div_le {β r : ℝ} (hβ : 0 < β) (hr : 1 ≤ r) (n : ℕ) :
    energyPrimitive β (r + 2 * n) / (n + 1) ≤
      ((r + β + 2) ^ 2 / (4 * β)) *
        ((r + 2 * n) * g β (r + 2 * n) ^ 2) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : r + 2 * n + β ≤ (r + β + 2) * (n + 1) := by nlinarith
  have h2 : r + 2 * n + β ≤ (r + β + 2) * (r + 2 * n) := by nlinarith
  have hprod := mul_le_mul h1 h2 (by positivity : 0 ≤ r + 2 * n + β)
    (by positivity : 0 ≤ (r + β + 2) * (n + 1))
  have hsq : (r + 2 * n + β) ^ 2 ≤
      (r + β + 2) ^ 2 * (n + 1) * (r + 2 * n) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg (g β (r + 2 * n)))
  unfold energyPrimitive
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)]
  apply (div_le_iff₀ (by positivity : 0 < 4 * β)).mpr
  have hid : (r + β + 2) ^ 2 / (4 * β) *
      ((r + 2 * n) * g β (r + 2 * n) ^ 2) * (n + 1) * (4 * β) =
      (r + β + 2) ^ 2 * (n + 1) * (r + 2 * n) * g β (r + 2 * n) ^ 2 := by
    field_simp
  rw [hid, mul_pow]
  exact hmul

theorem energyPrimitive_tendsto_zero {β r : ℝ} (hβ : 0 < β) (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => energyPrimitive β (r + 2 * n)) atTop (𝓝 0) := by
  apply limit_zero_of_antitone_harmonic
  · intro n
    exact energyPrimitive_nonneg hβ _
  · apply antitone_nat_of_succ_le
    intro n
    have h := energyPrimitive_step hβ (r + 2 * n)
    have hh : 0 ≤ (r + 2 * n) * g β (r + 2 * n) ^ 2 := by positivity
    push_cast
    rw [show r + 2 * ((n : ℝ) + 1) = (r + 2 * n) + 2 by ring]
    linarith
  · have hs := ((weighted_summable_and_bound hβ (by linarith : 0 ≤ r)).1).mul_left
      ((r + β + 2) ^ 2 / (4 * β))
    exact hs.of_nonneg_of_le (fun n => div_nonneg (energyPrimitive_nonneg hβ _)
      (by positivity)) (energyPrimitive_div_le hβ hr)

/-- Exact infinite leading-energy tail. This avoids estimating a slowly
convergent positive tail by truncation. -/
theorem weighted_tsum_eq {β r : ℝ} (hβ : 0 < β) (hr : 1 ≤ r) :
    (∑' n : ℕ, (r + 2 * n) * g β (r + 2 * n) ^ 2) = energyPrimitive β r := by
  have hs := (weighted_summable_and_bound hβ (by linarith : 0 ≤ r)).1
  have ht := (tendsto_const_nhds (x := energyPrimitive β r)).sub
    (energyPrimitive_tendsto_zero hβ hr)
  have hlim : Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range N, (r + 2 * n) * g β (r + 2 * n) ^ 2)
      atTop (𝓝 (energyPrimitive β r)) := by
    simpa only [weighted_sum_range hβ, sub_zero] using ht
  exact tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hlim

/-- Mixed products have a discrete primitive as well. The weight is a
weighted average of the two frequencies. -/
def mixedPrimitive (β γ ξ η : ℝ) : ℝ :=
  ((ξ + β) * g β ξ) * ((η + γ) * g γ η) / (2 * (β + γ))

theorem mixedPrimitive_step {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (ξ η : ℝ) :
    mixedPrimitive β γ ξ η - mixedPrimitive β γ (ξ + 2) (η + 2) =
      ((γ * ξ + β * η) / (β + γ)) * g β ξ * g γ η := by
  unfold mixedPrimitive
  rw [show ξ + 2 + β = ξ + β + 2 by ring,
    show η + 2 + γ = η + γ + 2 by ring, g_step_two hβ ξ, g_step_two hγ η]
  field_simp
  ring

/-- The lower-order unweighted tail is controlled by the exact leading tail. -/
theorem unweighted_summable_and_bound {β r : ℝ} (hβ : 0 < β) (hr : 1 ≤ r) :
    Summable (fun n : ℕ => g β (r + 2 * n) ^ 2) ∧
      (∑' n : ℕ, g β (r + 2 * n) ^ 2) ≤ energyPrimitive β r / r := by
  have hrp : 0 < r := by linarith
  have hs := (weighted_summable_and_bound hβ hrp.le).1
  have hpt : ∀ n : ℕ, g β (r + 2 * n) ^ 2 ≤
      r⁻¹ * ((r + 2 * n) * g β (r + 2 * n) ^ 2) := by
    intro n
    rw [← div_eq_inv_mul, le_div_iff₀ hrp]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [sq_nonneg (g β (r + 2 * n))]
  have hsum := (hs.mul_left r⁻¹).of_nonneg_of_le (fun n => sq_nonneg _) hpt
  refine ⟨hsum, ?_⟩
  have hle := hsum.tsum_le_tsum hpt (hs.mul_left r⁻¹)
  simpa only [tsum_mul_left, weighted_tsum_eq hβ hr, div_eq_inv_mul] using hle

/-- Reciprocal-symbol tails gain two powers of the starting frequency. -/
theorem reciprocal_summable_and_bound {β r : ℝ} (hβ : 0 < β) (hr : 1 ≤ r) :
    Summable (fun n : ℕ => g β (r + 2 * n) ^ 2 / (r + 2 * n)) ∧
      (∑' n : ℕ, g β (r + 2 * n) ^ 2 / (r + 2 * n)) ≤
        energyPrimitive β r / r ^ 2 := by
  have hrp : 0 < r := by linarith
  obtain ⟨hs, hb⟩ := unweighted_summable_and_bound hβ hr
  have hpt : ∀ n : ℕ, g β (r + 2 * n) ^ 2 / (r + 2 * n) ≤
      r⁻¹ * g β (r + 2 * n) ^ 2 := by
    intro n
    rw [← div_eq_inv_mul]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hrp (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hnonneg : ∀ n : ℕ, 0 ≤ g β (r + 2 * n) ^ 2 / (r + 2 * n) := by
    intro n
    positivity
  have hsum := (hs.mul_left r⁻¹).of_nonneg_of_le hnonneg hpt
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ r⁻¹ * ∑' n : ℕ, g β (r + 2 * n) ^ 2 := by
      simpa only [tsum_mul_left] using hsum.tsum_le_tsum hpt (hs.mul_left r⁻¹)
    _ ≤ r⁻¹ * (energyPrimitive β r / r) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = energyPrimitive β r / r ^ 2 := by ring

lemma weighted_factor_tendsto_zero {β r : ℝ} (hβ : 0 < β) (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => (r + 2 * n + β) * g β (r + 2 * n)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n : ℕ => ((r + 2 * n + β) * g β (r + 2 * n)) ^ 2)
      atTop (𝓝 0) := by
    have h := (energyPrimitive_tendsto_zero hβ hr).mul_const (4 * β)
    simpa only [energyPrimitive, div_mul_cancel₀ _ (by positivity : 4 * β ≠ 0),
      zero_mul] using h
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

lemma mixedPrimitive_tendsto_zero {β γ r t : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hr : 1 ≤ r) (ht : 1 ≤ t) :
    Tendsto (fun n : ℕ => mixedPrimitive β γ (r + 2 * n) (t + 2 * n))
      atTop (𝓝 0) := by
  have h := ((weighted_factor_tendsto_zero hβ hr).mul
    (weighted_factor_tendsto_zero hγ ht)).div_const (2 * (β + γ))
  simpa only [mixedPrimitive, zero_mul, zero_div] using h

lemma weighted_product_summable {β γ r t : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hr : 1 ≤ r) (ht : 1 ≤ t) (a : ℝ) :
    Summable (fun n : ℕ => (a + 2 * n) * g β (r + 2 * n) * g γ (t + 2 * n)) := by
  have hbs := (weighted_summable_and_bound hβ (by linarith : 0 ≤ r)).1
  have hgs := (weighted_summable_and_bound hγ (by linarith : 0 ≤ t)).1
  have hbase := hbs.add hgs
  have hpt : ∀ n : ℕ, |(n + 1) * g β (r + 2 * n) * g γ (t + 2 * n)| ≤
      (r + 2 * n) * g β (r + 2 * n) ^ 2 + (t + 2 * n) * g γ (t + 2 * n) ^ 2 := by
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hy : |g β (r + 2 * n)| * |g γ (t + 2 * n)| ≤
        g β (r + 2 * n) ^ 2 + g γ (t + 2 * n) ^ 2 := by
      nlinarith [sq_nonneg (|g β (r + 2 * n)| - |g γ (t + 2 * n)|),
        sq_abs (g β (r + 2 * n)), sq_abs (g γ (t + 2 * n)),
        sq_nonneg (g β (r + 2 * n)), sq_nonneg (g γ (t + 2 * n))]
    have hmul := mul_le_mul_of_nonneg_left hy (show 0 ≤ (n : ℝ) + 1 by positivity)
    rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity)]
    nlinarith [sq_nonneg (g β (r + 2 * n)), sq_nonneg (g γ (t + 2 * n))]
  have hws : Summable (fun n : ℕ => (n + 1) * g β (r + 2 * n) * g γ (t + 2 * n)) :=
    (hbase.of_nonneg_of_le (fun n => abs_nonneg _) hpt).of_abs
  have hplain : Summable (fun n : ℕ => g β (r + 2 * n) * g γ (t + 2 * n)) := by
    apply (hws.abs.of_nonneg_of_le (fun n => abs_nonneg _) ?_).of_abs
    intro n
    simp only [abs_mul, abs_of_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity)]
    nlinarith [mul_nonneg (abs_nonneg (g β (r + 2 * n)))
      (abs_nonneg (g γ (t + 2 * n))), Nat.cast_nonneg (α := ℝ) n]
  exact ((hws.mul_left 2).add (hplain.mul_left (a - 2))).congr fun n => by ring

theorem mixed_weighted_tsum_eq {β γ r t : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (∑' n : ℕ, ((γ * (r + 2 * n) + β * (t + 2 * n)) / (β + γ)) *
      g β (r + 2 * n) * g γ (t + 2 * n)) = mixedPrimitive β γ r t := by
  have heq : ∀ n : ℕ, (γ * r + β * t) / (β + γ) + 2 * n =
      (γ * (r + 2 * n) + β * (t + 2 * n)) / (β + γ) := by
    intro n
    field_simp
    ring
  have hs := (weighted_product_summable hβ hγ hr ht ((γ * r + β * t) / (β + γ))).congr
    (fun n => by rw [heq n])
  have hfinite : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, ((γ * (r + 2 * n) + β * (t + 2 * n)) / (β + γ)) *
        g β (r + 2 * n) * g γ (t + 2 * n)) =
      mixedPrimitive β γ r t - mixedPrimitive β γ (r + 2 * N) (t + 2 * N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hh := mixedPrimitive_step hβ hγ (r + 2 * N) (t + 2 * N)
      push_cast
      rw [show r + 2 * ((N : ℝ) + 1) = (r + 2 * N) + 2 by ring,
        show t + 2 * ((N : ℝ) + 1) = (t + 2 * N) + 2 by ring]
      linarith
  have hlim := (tendsto_const_nhds (x := mixedPrimitive β γ r t)).sub
    (mixedPrimitive_tendsto_zero hβ hγ hr ht)
  have hlim' : Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range N, ((γ * (r + 2 * n) + β * (t + 2 * n)) / (β + γ)) *
        g β (r + 2 * n) * g γ (t + 2 * n)) atTop (𝓝 (mixedPrimitive β γ r t)) := by
    simpa only [hfinite, sub_zero] using hlim
  exact tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hlim'

end KsIndex.PowerArc
