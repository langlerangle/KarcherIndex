module

public import KsIndexLean.AlphaGroupMultiplierCert
public import KsIndexLean.PowerArcNormalized

@[expose] public section


/-! # Rational formulas and bounds for the four group multipliers

Each multiplier, defined as a sum of normalized coefficient terms, equals a
ratio of integer-coefficient polynomials in `y = x - 2051` for `x ≥ 2051`.
The coefficient bounds from `AlphaGroupMultiplierCert` then give the stated
lower and upper bounds on this same domain.

The coefficient-sum factorizations hold on the larger domains `x ≥ 6` for
parity 0 and `x ≥ 5` for parity 1. Those identities alone do not extend the
certified multiplier bounds to these larger domains. -/
namespace KsIndex.AlphaMultIdentity
open KsIndex.PowerArc KsIndex.AlphaMultiplier

noncomputable def bA : ℝ := 4323618 / 10000000
noncomputable def bB : ℝ := 5676382 / 10000000


noncomputable def M_A0 (x : ℝ) : ℝ :=
    (678297074 / 10^12) * normalizedCoefficient bA (x - 6) 6
  + (10105953973 / 10^12) * normalizedCoefficient bA (x - 6) 5
  + (-15903023220 / 10^12) * normalizedCoefficient bA (x - 6) 4
  + (15903023220 / 10^12) * normalizedCoefficient bA (x - 6) 2
  + (-10105953973 / 10^12) * normalizedCoefficient bA (x - 6) 1
  + (-678297074 / 10^12) * normalizedCoefficient bA (x - 6) 0

set_option maxHeartbeats 4000000 in
-- large cleared rational identity: field_simp + ring over degree-≤6 denominators
theorem M_A0_eq_ratio (x : ℝ) (hx : (2051 : ℝ) ≤ x) :
    M_A0 x = (∑ j, (p_A0 j : ℝ) * (x - 2051) ^ j.val)
           / (∑ j, (d_A0 j : ℝ) * (x - 2051) ^ j.val) := by
  have hxnn : (0 : ℝ) ≤ x - 2051 := by linarith
  simp only [M_A0, normalizedCoefficient, p_A0, d_A0,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.cast_ofNat]
  norm_num
  have da : x - 6 + bA + 2 ≠ 0 := by simp only [bA]; intro h; nlinarith
  have db : x - 6 + 2 + bA + 2 ≠ 0 := by simp only [bA]; intro h; nlinarith
  have dc : x - 6 + 4 + bA + 2 ≠ 0 := by simp only [bA]; intro h; nlinarith
  have dd : x + bA + 2 ≠ 0 := by simp only [bA]; intro h; nlinarith
  have de : x - 6 + 8 + bA + 2 ≠ 0 := by simp only [bA]; intro h; nlinarith
  have df : x - 6 + 10 + bA + 2 ≠ 0 := by simp only [bA]; intro h; nlinarith
  have hden : (14599552809423143151942361801627384142852191097182885223758012500
      + (42679876371641220285736734972914903960224799065518375000000000 * (x - 2051)
      + (51987061461286867563916877113144655259504687500000000000000 * (x - 2051) ^ 2
      + (33772707166089449868374274941531250000000000000000000000 * (x - 2051) ^ 3
      + (12341239061808377243867187500000000000000000000000000 * (x - 2051) ^ 4
      + (2405194173984375000000000000000000000000000000000 * (x - 2051) ^ 5
      + 195312500000000000000000000000000000000000000 * (x - 2051) ^ 6)))))) ≠ 0 := by
    have h2 := pow_nonneg hxnn 2
    have h3 := pow_nonneg hxnn 3
    have h4 := pow_nonneg hxnn 4
    have h5 := pow_nonneg hxnn 5
    have h6 := pow_nonneg hxnn 6
    positivity
  field_simp
  simp only [bA]
  ring

/-- Multiplier `A` parity `0`: the endpoint bound L_A0 ≤ M_A0 x ≤ U_A0
    on x ≥ 2051, combining the identity (M = p/d) with the coefficientwise bound. -/
theorem M_A0_bounds (x : ℝ) (hx : (2051 : ℝ) ≤ x) :
    (L_A0 : ℝ) ≤ M_A0 x ∧ M_A0 x ≤ (U_A0 : ℝ) := by
  rw [M_A0_eq_ratio x hx]
  exact mult_bound_A0 (x - 2051) (by linarith)

noncomputable def M_A1 (x : ℝ) : ℝ :=
    (-3847817393 / 10^12) * normalizedCoefficient bA (x - 5) 5
  + (-12255602695 / 10^12) * normalizedCoefficient bA (x - 5) 4
  + (237044154676 / 10^12) * normalizedCoefficient bA (x - 5) 3
  + (-237044154676 / 10^12) * normalizedCoefficient bA (x - 5) 2
  + (12255602695 / 10^12) * normalizedCoefficient bA (x - 5) 1
  + (3847817393 / 10^12) * normalizedCoefficient bA (x - 5) 0

set_option maxHeartbeats 4000000 in
-- large cleared rational identity: field_simp + ring over degree-≤6 denominators
theorem M_A1_eq_ratio (x : ℝ) (hx : (2051 : ℝ) ≤ x) :
    M_A1 x = (∑ j, (p_A1 j : ℝ) * (x - 2051) ^ j.val)
           / (∑ j, (d_A1 j : ℝ) * (x - 2051) ^ j.val) := by
  have hxnn : (0 : ℝ) ≤ x - 2051 := by linarith
  simp only [M_A1, normalizedCoefficient, p_A1, d_A1,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.cast_ofNat]
  norm_num
  have da : x - 5 + bA + 2 ≠ 0 := by simp only [bA]; intro h; nlinarith
  have db : x - 5 + 2 + bA + 2 ≠ 0 := by simp only [bA]; intro h; nlinarith
  have dc : x - 5 + 4 + bA + 2 ≠ 0 := by simp only [bA]; intro h; nlinarith
  have dd : x - 5 + 6 + bA + 2 ≠ 0 := by simp only [bA]; intro h; nlinarith
  have de : x - 5 + 8 + bA + 2 ≠ 0 := by simp only [bA]; intro h; nlinarith
  have hden : (5690654685913438875914745029625312732196639875402450000
      + (13863222971670820564845697292671908069201250000000000 * (x - 2051)
      + (13509086073361345259849709976612500000000000000000 * (x - 2051) ^ 2
      + (6581994687131134530062500000000000000000000000 * (x - 2051) ^ 3
      + (1603462782656250000000000000000000000000000 * (x - 2051) ^ 4
      + 156250000000000000000000000000000000000 * (x - 2051) ^ 5))))) ≠ 0 := by
    have h2 := pow_nonneg hxnn 2
    have h3 := pow_nonneg hxnn 3
    have h4 := pow_nonneg hxnn 4
    have h5 := pow_nonneg hxnn 5
    positivity
  field_simp
  simp only [bA]
  ring

/-- Multiplier `A` parity `1`: the endpoint bound L_A1 ≤ M_A1 x ≤ U_A1
    on x ≥ 2051, combining the identity (M = p/d) with the coefficientwise bound. -/
theorem M_A1_bounds (x : ℝ) (hx : (2051 : ℝ) ≤ x) :
    (L_A1 : ℝ) ≤ M_A1 x ∧ M_A1 x ≤ (U_A1 : ℝ) := by
  rw [M_A1_eq_ratio x hx]
  exact mult_bound_A1 (x - 2051) (by linarith)

noncomputable def M_B0 (x : ℝ) : ℝ :=
    (-2064148267 / 10^12) * normalizedCoefficient bB (x - 6) 6
  + (-60384017740 / 10^12) * normalizedCoefficient bB (x - 6) 5
  + (-309175124422 / 10^12) * normalizedCoefficient bB (x - 6) 4
  + (347930602765 / 10^12) * normalizedCoefficient bB (x - 6) 3
  + (-309175124422 / 10^12) * normalizedCoefficient bB (x - 6) 2
  + (-60384017740 / 10^12) * normalizedCoefficient bB (x - 6) 1
  + (-2064148267 / 10^12) * normalizedCoefficient bB (x - 6) 0

set_option maxHeartbeats 4000000 in
-- large cleared rational identity: field_simp + ring over degree-≤6 denominators
theorem M_B0_eq_ratio (x : ℝ) (hx : (2051 : ℝ) ≤ x) :
    M_B0 x = (∑ j, (p_B0 j : ℝ) * (x - 2051) ^ j.val)
           / (∑ j, (d_B0 j : ℝ) * (x - 2051) ^ j.val) := by
  have hxnn : (0 : ℝ) ≤ x - 2051 := by linarith
  simp only [M_B0, normalizedCoefficient, p_B0, d_B0,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.cast_ofNat]
  norm_num
  have da : x - 6 + bB + 2 ≠ 0 := by simp only [bB]; intro h; nlinarith
  have db : x - 6 + 2 + bB + 2 ≠ 0 := by simp only [bB]; intro h; nlinarith
  have dc : x - 6 + 4 + bB + 2 ≠ 0 := by simp only [bB]; intro h; nlinarith
  have dd : x + bB + 2 ≠ 0 := by simp only [bB]; intro h; nlinarith
  have de : x - 6 + 8 + bB + 2 ≠ 0 := by simp only [bB]; intro h; nlinarith
  have df : x - 6 + 10 + bB + 2 ≠ 0 := by simp only [bB]; intro h; nlinarith
  have hden : (1168426187270608810267260788542916838371449409033396467900641000000000000
      + (3415515477671777990761463815829725570124694824758530000000000000000000 * (x - 2051)
      + (4160061501369889460105309652904984920760375000000000000000000000000 * (x - 2051) ^ 2
      + (2702350841584786170573995504677500000000000000000000000000000000 * (x - 2051) ^ 3
      + (987429275637326429509375000000000000000000000000000000000000 * (x - 2051) ^ 4
      + (192428216081250000000000000000000000000000000000000000000 * (x - 2051) ^ 5
      + 15625000000000000000000000000000000000000000000000000 * (x - 2051) ^ 6)))))) ≠ 0 := by
    have h2 := pow_nonneg hxnn 2
    have h3 := pow_nonneg hxnn 3
    have h4 := pow_nonneg hxnn 4
    have h5 := pow_nonneg hxnn 5
    have h6 := pow_nonneg hxnn 6
    positivity
  field_simp
  simp only [bB]
  ring

/-- Multiplier `B` parity `0`: the endpoint bound L_B0 ≤ M_B0 x ≤ U_B0
    on x ≥ 2051, combining the identity (M = p/d) with the coefficientwise bound. -/
theorem M_B0_bounds (x : ℝ) (hx : (2051 : ℝ) ≤ x) :
    (L_B0 : ℝ) ≤ M_B0 x ∧ M_B0 x ≤ (U_B0 : ℝ) := by
  rw [M_B0_eq_ratio x hx]
  exact mult_bound_B0 (x - 2051) (by linarith)

noncomputable def M_B1 (x : ℝ) : ℝ :=
    (15584704300 / 10^12) * normalizedCoefficient bB (x - 5) 5
  + (157391608797 / 10^12) * normalizedCoefficient bB (x - 5) 4
  + (546623219487 / 10^12) * normalizedCoefficient bB (x - 5) 3
  + (546623219487 / 10^12) * normalizedCoefficient bB (x - 5) 2
  + (157391608797 / 10^12) * normalizedCoefficient bB (x - 5) 1
  + (15584704300 / 10^12) * normalizedCoefficient bB (x - 5) 0

set_option maxHeartbeats 4000000 in
-- large cleared rational identity: field_simp + ring over degree-≤6 denominators
theorem M_B1_eq_ratio (x : ℝ) (hx : (2051 : ℝ) ≤ x) :
    M_B1 x = (∑ j, (p_B1 j : ℝ) * (x - 2051) ^ j.val)
           / (∑ j, (d_B1 j : ℝ) * (x - 2051) ^ j.val) := by
  have hxnn : (0 : ℝ) ≤ x - 2051 := by linarith
  simp only [M_B1, normalizedCoefficient, p_B1, d_B1,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Nat.cast_ofNat]
  norm_num
  have da : x - 5 + bB + 2 ≠ 0 := by simp only [bB]; intro h; nlinarith
  have db : x - 5 + 2 + bB + 2 ≠ 0 := by simp only [bB]; intro h; nlinarith
  have dc : x - 5 + 4 + bB + 2 ≠ 0 := by simp only [bB]; intro h; nlinarith
  have dd : x - 5 + 6 + bB + 2 ≠ 0 := by simp only [bB]; intro h; nlinarith
  have de : x - 5 + 8 + bB + 2 ≠ 0 := by simp only [bB]; intro h; nlinarith
  have hden : (7115662875047525007841074249635896349218114218246937500000000
      + (17333597817618698373992369465229103836501562500000000000000 * (x - 2051)
      + (16889696768826081925462471904234375000000000000000000000 * (x - 2051) ^ 2
      + (8228577948019386912578125000000000000000000000000000 * (x - 2051) ^ 3
      + (2004460584179687500000000000000000000000000000000 * (x - 2051) ^ 4
      + 195312500000000000000000000000000000000000000 * (x - 2051) ^ 5))))) ≠ 0 := by
    have h2 := pow_nonneg hxnn 2
    have h3 := pow_nonneg hxnn 3
    have h4 := pow_nonneg hxnn 4
    have h5 := pow_nonneg hxnn 5
    positivity
  field_simp
  simp only [bB]
  ring

/-- Multiplier `B` parity `1`: the endpoint bound L_B1 ≤ M_B1 x ≤ U_B1
    on x ≥ 2051, combining the identity (M = p/d) with the coefficientwise bound. -/
theorem M_B1_bounds (x : ℝ) (hx : (2051 : ℝ) ≤ x) :
    (L_B1 : ℝ) ≤ M_B1 x ∧ M_B1 x ≤ (U_B1 : ℝ) := by
  rw [M_B1_eq_ratio x hx]
  exact mult_bound_B1 (x - 2051) (by linarith)

/-! ## Factoring the coefficient sums by a reference coefficient -/

noncomputable def G_A0 (x : ℝ) : ℝ :=
    (678297074 / 10^12) * (g bA (x + 6) / g bA 0)
  + (10105953973 / 10^12) * (g bA (x + 4) / g bA 0)
  + (-15903023220 / 10^12) * (g bA (x + 2) / g bA 0)
  + (15903023220 / 10^12) * (g bA (x - 2) / g bA 0)
  + (-10105953973 / 10^12) * (g bA (x - 4) / g bA 0)
  + (-678297074 / 10^12) * (g bA (x - 6) / g bA 0)

/-- For `x ≥ 6`, the coefficient sum for group A, parity 0, factors as
`g bA (x - 6) / g bA 0` times `M_A0 x`. The separate multiplier
bounds require `x ≥ 2051`. -/
theorem G_A0_eq (x : ℝ) (hx : (6 : ℝ) ≤ x) :
    G_A0 x = (g bA (x - 6) / g bA 0) * M_A0 x := by
  have hb : (0 : ℝ) < bA := by norm_num [bA]
  have hr : (0 : ℝ) ≤ x - 6 := by linarith
  have e6 : g bA (x + 6) = g bA (x - 6) * normalizedCoefficient bA (x - 6) 6 := by
    have h := g_eq_normalizedCoefficient hb hr 6
    have harg : (x - 6) + 2 * ((6 : ℕ) : ℝ) = (x + 6 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e5 : g bA (x + 4) = g bA (x - 6) * normalizedCoefficient bA (x - 6) 5 := by
    have h := g_eq_normalizedCoefficient hb hr 5
    have harg : (x - 6) + 2 * ((5 : ℕ) : ℝ) = (x + 4 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e4 : g bA (x + 2) = g bA (x - 6) * normalizedCoefficient bA (x - 6) 4 := by
    have h := g_eq_normalizedCoefficient hb hr 4
    have harg : (x - 6) + 2 * ((4 : ℕ) : ℝ) = (x + 2 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e2 : g bA (x - 2) = g bA (x - 6) * normalizedCoefficient bA (x - 6) 2 := by
    have h := g_eq_normalizedCoefficient hb hr 2
    have harg : (x - 6) + 2 * ((2 : ℕ) : ℝ) = (x - 2 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e1 : g bA (x - 4) = g bA (x - 6) * normalizedCoefficient bA (x - 6) 1 := by
    have h := g_eq_normalizedCoefficient hb hr 1
    have harg : (x - 6) + 2 * ((1 : ℕ) : ℝ) = (x - 4 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e0 : normalizedCoefficient bA (x - 6) 0 = 1 := rfl
  simp only [G_A0, M_A0, e6, e5, e4, e2, e1, e0]
  ring

noncomputable def G_A1 (x : ℝ) : ℝ :=
    (-3847817393 / 10^12) * (g bA (x + 5) / g bA 0)
  + (-12255602695 / 10^12) * (g bA (x + 3) / g bA 0)
  + (237044154676 / 10^12) * (g bA (x + 1) / g bA 0)
  + (-237044154676 / 10^12) * (g bA (x - 1) / g bA 0)
  + (12255602695 / 10^12) * (g bA (x - 3) / g bA 0)
  + (3847817393 / 10^12) * (g bA (x - 5) / g bA 0)

/-- For `x ≥ 5`, the coefficient sum for group A, parity 1, factors as
`g bA (x - 5) / g bA 0` times `M_A1 x`. The separate multiplier
bounds require `x ≥ 2051`. -/
theorem G_A1_eq (x : ℝ) (hx : (5 : ℝ) ≤ x) :
    G_A1 x = (g bA (x - 5) / g bA 0) * M_A1 x := by
  have hb : (0 : ℝ) < bA := by norm_num [bA]
  have hr : (0 : ℝ) ≤ x - 5 := by linarith
  have e5 : g bA (x + 5) = g bA (x - 5) * normalizedCoefficient bA (x - 5) 5 := by
    have h := g_eq_normalizedCoefficient hb hr 5
    have harg : (x - 5) + 2 * ((5 : ℕ) : ℝ) = (x + 5 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e4 : g bA (x + 3) = g bA (x - 5) * normalizedCoefficient bA (x - 5) 4 := by
    have h := g_eq_normalizedCoefficient hb hr 4
    have harg : (x - 5) + 2 * ((4 : ℕ) : ℝ) = (x + 3 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e3 : g bA (x + 1) = g bA (x - 5) * normalizedCoefficient bA (x - 5) 3 := by
    have h := g_eq_normalizedCoefficient hb hr 3
    have harg : (x - 5) + 2 * ((3 : ℕ) : ℝ) = (x + 1 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e2 : g bA (x - 1) = g bA (x - 5) * normalizedCoefficient bA (x - 5) 2 := by
    have h := g_eq_normalizedCoefficient hb hr 2
    have harg : (x - 5) + 2 * ((2 : ℕ) : ℝ) = (x - 1 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e1 : g bA (x - 3) = g bA (x - 5) * normalizedCoefficient bA (x - 5) 1 := by
    have h := g_eq_normalizedCoefficient hb hr 1
    have harg : (x - 5) + 2 * ((1 : ℕ) : ℝ) = (x - 3 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e0 : normalizedCoefficient bA (x - 5) 0 = 1 := rfl
  simp only [G_A1, M_A1, e5, e4, e3, e2, e1, e0]
  ring

noncomputable def G_B0 (x : ℝ) : ℝ :=
    (-2064148267 / 10^12) * (g bB (x + 6) / g bB 0)
  + (-60384017740 / 10^12) * (g bB (x + 4) / g bB 0)
  + (-309175124422 / 10^12) * (g bB (x + 2) / g bB 0)
  + (347930602765 / 10^12) * (g bB (x) / g bB 0)
  + (-309175124422 / 10^12) * (g bB (x - 2) / g bB 0)
  + (-60384017740 / 10^12) * (g bB (x - 4) / g bB 0)
  + (-2064148267 / 10^12) * (g bB (x - 6) / g bB 0)

/-- For `x ≥ 6`, the coefficient sum for group B, parity 0, factors as
`g bB (x - 6) / g bB 0` times `M_B0 x`. The separate multiplier
bounds require `x ≥ 2051`. -/
theorem G_B0_eq (x : ℝ) (hx : (6 : ℝ) ≤ x) :
    G_B0 x = (g bB (x - 6) / g bB 0) * M_B0 x := by
  have hb : (0 : ℝ) < bB := by norm_num [bB]
  have hr : (0 : ℝ) ≤ x - 6 := by linarith
  have e6 : g bB (x + 6) = g bB (x - 6) * normalizedCoefficient bB (x - 6) 6 := by
    have h := g_eq_normalizedCoefficient hb hr 6
    have harg : (x - 6) + 2 * ((6 : ℕ) : ℝ) = (x + 6 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e5 : g bB (x + 4) = g bB (x - 6) * normalizedCoefficient bB (x - 6) 5 := by
    have h := g_eq_normalizedCoefficient hb hr 5
    have harg : (x - 6) + 2 * ((5 : ℕ) : ℝ) = (x + 4 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e4 : g bB (x + 2) = g bB (x - 6) * normalizedCoefficient bB (x - 6) 4 := by
    have h := g_eq_normalizedCoefficient hb hr 4
    have harg : (x - 6) + 2 * ((4 : ℕ) : ℝ) = (x + 2 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e3 : g bB (x) = g bB (x - 6) * normalizedCoefficient bB (x - 6) 3 := by
    have h := g_eq_normalizedCoefficient hb hr 3
    have harg : (x - 6) + 2 * ((3 : ℕ) : ℝ) = (x : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e2 : g bB (x - 2) = g bB (x - 6) * normalizedCoefficient bB (x - 6) 2 := by
    have h := g_eq_normalizedCoefficient hb hr 2
    have harg : (x - 6) + 2 * ((2 : ℕ) : ℝ) = (x - 2 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e1 : g bB (x - 4) = g bB (x - 6) * normalizedCoefficient bB (x - 6) 1 := by
    have h := g_eq_normalizedCoefficient hb hr 1
    have harg : (x - 6) + 2 * ((1 : ℕ) : ℝ) = (x - 4 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e0 : normalizedCoefficient bB (x - 6) 0 = 1 := rfl
  simp only [G_B0, M_B0, e6, e5, e4, e3, e2, e1, e0]
  ring

noncomputable def G_B1 (x : ℝ) : ℝ :=
    (15584704300 / 10^12) * (g bB (x + 5) / g bB 0)
  + (157391608797 / 10^12) * (g bB (x + 3) / g bB 0)
  + (546623219487 / 10^12) * (g bB (x + 1) / g bB 0)
  + (546623219487 / 10^12) * (g bB (x - 1) / g bB 0)
  + (157391608797 / 10^12) * (g bB (x - 3) / g bB 0)
  + (15584704300 / 10^12) * (g bB (x - 5) / g bB 0)

/-- For `x ≥ 5`, the coefficient sum for group B, parity 1, factors as
`g bB (x - 5) / g bB 0` times `M_B1 x`. The separate multiplier
bounds require `x ≥ 2051`. -/
theorem G_B1_eq (x : ℝ) (hx : (5 : ℝ) ≤ x) :
    G_B1 x = (g bB (x - 5) / g bB 0) * M_B1 x := by
  have hb : (0 : ℝ) < bB := by norm_num [bB]
  have hr : (0 : ℝ) ≤ x - 5 := by linarith
  have e5 : g bB (x + 5) = g bB (x - 5) * normalizedCoefficient bB (x - 5) 5 := by
    have h := g_eq_normalizedCoefficient hb hr 5
    have harg : (x - 5) + 2 * ((5 : ℕ) : ℝ) = (x + 5 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e4 : g bB (x + 3) = g bB (x - 5) * normalizedCoefficient bB (x - 5) 4 := by
    have h := g_eq_normalizedCoefficient hb hr 4
    have harg : (x - 5) + 2 * ((4 : ℕ) : ℝ) = (x + 3 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e3 : g bB (x + 1) = g bB (x - 5) * normalizedCoefficient bB (x - 5) 3 := by
    have h := g_eq_normalizedCoefficient hb hr 3
    have harg : (x - 5) + 2 * ((3 : ℕ) : ℝ) = (x + 1 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e2 : g bB (x - 1) = g bB (x - 5) * normalizedCoefficient bB (x - 5) 2 := by
    have h := g_eq_normalizedCoefficient hb hr 2
    have harg : (x - 5) + 2 * ((2 : ℕ) : ℝ) = (x - 1 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e1 : g bB (x - 3) = g bB (x - 5) * normalizedCoefficient bB (x - 5) 1 := by
    have h := g_eq_normalizedCoefficient hb hr 1
    have harg : (x - 5) + 2 * ((1 : ℕ) : ℝ) = (x - 3 : ℝ) := by push_cast; ring
    rw [harg] at h; exact h
  have e0 : normalizedCoefficient bB (x - 5) 0 = 1 := rfl
  simp only [G_B1, M_B1, e5, e4, e3, e2, e1, e0]
  ring

#print axioms KsIndex.AlphaMultIdentity.M_A0_eq_ratio
#print axioms KsIndex.AlphaMultIdentity.M_A0_bounds
#print axioms KsIndex.AlphaMultIdentity.G_A0_eq

#print axioms KsIndex.AlphaMultIdentity.M_A1_eq_ratio
#print axioms KsIndex.AlphaMultIdentity.M_A1_bounds
#print axioms KsIndex.AlphaMultIdentity.G_A1_eq

#print axioms KsIndex.AlphaMultIdentity.M_B0_eq_ratio
#print axioms KsIndex.AlphaMultIdentity.M_B0_bounds
#print axioms KsIndex.AlphaMultIdentity.G_B0_eq

#print axioms KsIndex.AlphaMultIdentity.M_B1_eq_ratio
#print axioms KsIndex.AlphaMultIdentity.M_B1_bounds
#print axioms KsIndex.AlphaMultIdentity.G_B1_eq

end KsIndex.AlphaMultIdentity
