module

public import KsIndexLean.PowerArcStieltjesSplit
public import KsIndexLean.AlphaTrialRecurrenceConstants

@[expose] public section


/-! The compensated recurrence for the actual power-arc Stieltjes transform.

The reciprocal corrections cancel its first two forcing orders. The transform
is the absolutely convergent series, not an independently supplied recurrence.
-/

namespace KsIndex.PowerArc

theorem powerArcStieltjes_forward (β r z : ℝ)
    (hβ : 0 < β) (hr : β ≤ r) (hz : 0 < z)
    (hd : z + 1 - (r - β) / 2 ≠ 0) :
    powerArcStieltjes β r (z + 1) =
      (z + 1 - (r + β + 2) / 2) / (z + 1 - (r - β) / 2) *
        powerArcStieltjes β r z +
      g β r * ((r + β + 2) / 2 - 1) / (z * (z + 1 - (r - β) / 2)) := by
  have h := g_stieltjes_recurrence hβ hr (z + 1) (by linarith)
  change ((r - β) / 2 - (z + 1)) * powerArcStieltjes β r (z + 1) -
    ((r + β + 2) / 2 - (z + 1)) * powerArcStieltjes β r (z + 1 - 1) =
    -g β r * ((r + β + 2) / 2 - 1) / (z + 1 - 1) at h
  simp only [add_sub_cancel_right] at h
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hd2 : (z + 1) * 2 - (r - β) ≠ 0 := by
    intro hh; apply hd; linarith
  field_simp at h
  field_simp [hd2]
  nlinarith [h]

noncomputable def stieltjesCorrectionC (β r κ : ℝ) : ℝ :=
  κ * (g β r / g β 0) * ((r + β + 2) / 2 - 1) / β

noncomputable def stieltjesCorrectionD (β r κ : ℝ) : ℝ :=
  stieltjesCorrectionC β r κ * ((r - β) / 2) / (1 - β)

noncomputable def compensatedStieltjes (β r κ z : ℝ) : ℝ :=
  -κ * (powerArcStieltjes β r z / g β 0) +
    stieltjesCorrectionC β r κ / z + stieltjesCorrectionD β r κ / z ^ 2

theorem compensatedStieltjes_step (β r κ z : ℝ)
    (hβ : 0 < β) (hβ1 : β < 1) (hr : β ≤ r) (hz : 0 < z)
    (hd : z + 1 - (r - β) / 2 ≠ 0) :
    compensatedStieltjes β r κ (z + 1) =
      (z + 1 - (r + β + 2) / 2) / (z + 1 - (r - β) / 2) *
        compensatedStieltjes β r κ z +
      stieltjesCorrectionD β r κ * (r * z + (r + β) / 2) /
        (z ^ 2 * (z + 1) ^ 2 * (z + 1 - (r - β) / 2)) := by
  let A := (r - β) / 2
  let B := (r + β + 2) / 2
  let C := stieltjesCorrectionC β r κ
  let D := stieltjesCorrectionD β r κ
  let f := fun x => -κ * (powerArcStieltjes β r x / g β 0)
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : z + 1 ≠ 0 := by positivity
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have hβ10 : 1 - β ≠ 0 := by linarith
  have hraw : f (z + 1) = (z + 1 - B) / (z + 1 - A) * f z -
      C * (B - A - 1) / (z * (z + 1 - A)) := by
    dsimp [f, C, A, B, stieltjesCorrectionC]
    rw [powerArcStieltjes_forward β r z hβ hr hz hd]
    have hid : (r + β + 2) / 2 - (r - β) / 2 - 1 = β := by ring
    rw [hid]
    field_simp
    ring
  have hfirst := AlphaResidual.first_compensated_step A B z C (f z) (f (z + 1))
    hz0 hz1 hd hraw
  have hDC : D * (A - B + 2) = C * A := by
    dsimp [D, stieltjesCorrectionD, A, B, C]
    have hid : (r - β) / 2 - (r + β + 2) / 2 + 2 = 1 - β := by ring
    rw [hid]
    field_simp
  rw [← hDC] at hfirst
  have hsecond := AlphaResidual.second_compensated_step A B z D
    (f z + C / z) (f (z + 1) + C / (z + 1)) hz0 hz1 hd hfirst
  have hid : (A + B - 1) * z + B - 1 = r * z + (r + β) / 2 := by
    dsimp [A, B]; ring
  rw [hid] at hsecond
  exact hsecond

/-- The lattice term has the same homogeneous multiplier as the transform. -/
theorem powerArc_homogeneous_step (β r z : ℝ) (n : ℕ)
    (hβ : 0 < β) (hd : z + 1 - (r - β) / 2 ≠ 0) :
    (-1 : ℝ) ^ (n + 1) * g β (2 * (z + 1) - r) / g β 0 =
      (z + 1 - (r + β + 2) / 2) / (z + 1 - (r - β) / 2) *
        ((-1 : ℝ) ^ n * g β (2 * z - r) / g β 0) := by
  have h := g_step_two hβ (2 * z - r)
  have hd2 : 2 * z - r + β + 2 ≠ 0 := by intro hh; apply hd; linarith
  have hg : g β (2 * (z + 1) - r) =
      -((z + 1 - (r + β + 2) / 2) / (z + 1 - (r - β) / 2)) *
        g β (2 * z - r) := by
    rw [show 2 * (z + 1) - r = (2 * z - r) + 2 by ring]
    have hd' : 2 * (z + 1) - (r - β) ≠ 0 := by intro hh; apply hd; linarith
    field_simp [hd']
    nlinarith [h]
  rw [hg, pow_succ]
  ring

noncomputable def compensatedPowerArcGroup (β r κ w : ℝ) (n : ℕ) : ℝ :=
  w * ((-1 : ℝ) ^ n * g β (2 * ((n : ℝ) + 9 / 2) - r) / g β 0) +
    compensatedStieltjes β r κ ((n : ℝ) + 9 / 2)

/-- The actual power-arc/Stieltjes group obeys the compensated recurrence. -/
theorem compensatedPowerArcGroup_step (β r κ w : ℝ) (n : ℕ)
    (hβ : 0 < β) (hβ1 : β < 1) (hr : β ≤ r)
    (hd : (n : ℝ) + 9 / 2 + 1 - (r - β) / 2 ≠ 0) :
    compensatedPowerArcGroup β r κ w (n + 1) =
      ((n : ℝ) + 9 / 2 + 1 - (r + β + 2) / 2) /
        ((n : ℝ) + 9 / 2 + 1 - (r - β) / 2) *
          compensatedPowerArcGroup β r κ w n +
      stieltjesCorrectionD β r κ * (r * ((n : ℝ) + 9 / 2) + (r + β) / 2) /
        (((n : ℝ) + 9 / 2) ^ 2 * ((n : ℝ) + 9 / 2 + 1) ^ 2 *
          ((n : ℝ) + 9 / 2 + 1 - (r - β) / 2)) := by
  have hz : 0 < (n : ℝ) + 9 / 2 := by positivity
  have hs := compensatedStieltjes_step β r κ ((n : ℝ) + 9 / 2) hβ hβ1 hr hz hd
  have hu := powerArc_homogeneous_step β r ((n : ℝ) + 9 / 2) n hβ hd
  simp only [compensatedPowerArcGroup, Nat.cast_add, Nat.cast_one]
  rw [show (n : ℝ) + 1 + 9 / 2 = (n : ℝ) + 9 / 2 + 1 by ring, hs, hu]
  ring

/-- Propagate the initial compensated group bound past any outer cutoff.
The homogeneous product is explicit; no residual recurrence is assumed. -/
theorem compensatedPowerArcGroup_bound (β r κ w : ℝ) (N : ℕ)
    (hβ : β = 4323618 / 10000000 ∨ β = 5676382 / 10000000)
    (hr : r = 14 ∨ r = 15) (hN : 1024 ≤ N) (n : ℕ) :
    |compensatedPowerArcGroup β r κ w (N + n)| ≤
      (|compensatedPowerArcGroup β r κ w N| +
        11 * |stieltjesCorrectionD β r κ| / ((N : ℝ) + 9 / 2) ^ 3) *
      ∏ j ∈ Finset.range n,
        (((N + j : ℕ) : ℝ) + 9 / 2 + 1 - (r + β + 2) / 2) /
          (((N + j : ℕ) : ℝ) + 9 / 2 + 1 - (r - β) / 2) := by
  let z : ℕ → ℝ := fun j => ((N + j : ℕ) : ℝ) + 9 / 2
  let q : ℕ → ℝ := fun j =>
    (z j + 1 - (r + β + 2) / 2) / (z j + 1 - (r - β) / 2)
  let f : ℕ → ℝ := fun j => compensatedPowerArcGroup β r κ w (N + j)
  let e : ℕ → ℝ := fun j => stieltjesCorrectionD β r κ * (r * z j + (r + β) / 2) /
    ((z j) ^ 2 * (z j + 1) ^ 2 * (z j + 1 - (r - β) / 2))
  let p : ℕ → ℝ := fun j => ∏ k ∈ Finset.range j, q k
  let h : ℕ → ℝ := fun j => 1 / (z j) ^ 3
  let K := 11 * |stieltjesCorrectionD β r κ|
  have hb0 : 0 < β := by rcases hβ with rfl | rfl <;> norm_num
  have hb1 : β < 1 := by rcases hβ with rfl | rfl <;> norm_num
  have hbr : β ≤ r := by
    rcases hβ with rfl | rfl <;> rcases hr with rfl | rfl <;> norm_num
  have hz (j : ℕ) : 1028 ≤ z j := by
    have hn : (1024 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [z]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
  have hd (j : ℕ) : 0 < z j + 1 - (r - β) / 2 := by
    have hh := hz j
    rcases hr with rfl | rfl <;> linarith
  have hq (j : ℕ) : 0 ≤ q j := by
    have hh := hz j
    apply div_nonneg _ (hd j).le
    rcases hr with rfl | rfl <;> linarith
  have hzstep (j : ℕ) : z (j + 1) = z j + 1 := by dsimp [z]; push_cast; ring
  have hf (j : ℕ) : f (j + 1) = q j * f j + e j := by
    simpa only [f, q, e, z, Nat.add_assoc] using
      compensatedPowerArcGroup_step β r κ w (N + j) hb0 hb1 hbr (ne_of_gt (hd j))
  have hp (j : ℕ) : p (j + 1) = q j * p j := by
    simp only [p, Finset.prod_range_succ, mul_comm]
  have he (j : ℕ) : |e j| ≤ K * (q j * h j - h (j + 1)) := by
    dsimp only [e, K, q, h]
    rw [hzstep]
    simpa only [div_eq_mul_inv, mul_one, one_mul] using
      AlphaResidual.trial_cubic_forcing_bound β r (z j)
        (stieltjesCorrectionD β r κ) hβ hr (hz j)
  have hzero : |f 0| + K * h 0 ≤ (|f 0| + K * h 0) * p 0 := by
    simp only [p, Finset.range_zero, Finset.prod_empty, mul_one, le_refl]
  have hh := AlphaResidual.recurrence_abs_bound f q e p h (|f 0| + K * h 0) K
    hq (by dsimp [K]; positivity)
    (fun j => by dsimp [h]; positivity) hf hp he hzero n
  simpa only [f, K, h, z, p, q, Nat.add_zero, mul_one_div] using hh

theorem normalizedCoefficient_demodulated_product (β t : ℝ) (n : ℕ) :
    (∏ j ∈ Finset.range n, (t + 2 * j - β) / (t + 2 * j + β + 2)) =
      (-1 : ℝ) ^ n * normalizedCoefficient β t n := by
  induction n with
  | zero => simp [normalizedCoefficient]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, normalizedCoefficient, pow_succ]
    ring

/-- Express the homogeneous multiplier using the same normalized coefficients
as the coefficient and weighted-energy certificates. -/
theorem group_product_eq_normalized (β r : ℝ) (N n : ℕ) :
    (∏ j ∈ Finset.range n,
      (((N + j : ℕ) : ℝ) + 9 / 2 + 1 - (r + β + 2) / 2) /
        (((N + j : ℕ) : ℝ) + 9 / 2 + 1 - (r - β) / 2)) =
      (-1 : ℝ) ^ n * normalizedCoefficient β (2 * N + 9 - r) n := by
  rw [← normalizedCoefficient_demodulated_product]
  apply Finset.prod_congr rfl
  intro j _
  push_cast
  rw [show (N : ℝ) + j + 9 / 2 + 1 - (r + β + 2) / 2 =
    (2 * N + 9 - r + 2 * j - β) / 2 by ring]
  rw [show (N : ℝ) + j + 9 / 2 + 1 - (r - β) / 2 =
    (2 * N + 9 - r + 2 * j + β + 2) / 2 by ring]
  exact div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0) _ _

theorem compensatedPowerArcGroup_normalized_bound (β r κ w : ℝ) (N : ℕ)
    (hβ : β = 4323618 / 10000000 ∨ β = 5676382 / 10000000)
    (hr : r = 14 ∨ r = 15) (hN : 1024 ≤ N) (n : ℕ) :
    |compensatedPowerArcGroup β r κ w (N + n)| ≤
      (|compensatedPowerArcGroup β r κ w N| +
        11 * |stieltjesCorrectionD β r κ| / ((N : ℝ) + 9 / 2) ^ 3) *
        |normalizedCoefficient β (2 * N + 9 - r) n| := by
  have hh := compensatedPowerArcGroup_bound β r κ w N hβ hr hN n
  rw [group_product_eq_normalized] at hh
  have hle : (-1 : ℝ) ^ n * normalizedCoefficient β (2 * N + 9 - r) n ≤
      |normalizedCoefficient β (2 * N + 9 - r) n| := by
    simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
      le_abs_self ((-1 : ℝ) ^ n * normalizedCoefficient β (2 * N + 9 - r) n)
  have hc : 0 ≤ |compensatedPowerArcGroup β r κ w N| +
      11 * |stieltjesCorrectionD β r κ| / ((N : ℝ) + 9 / 2) ^ 3 := by positivity
  exact hh.trans (mul_le_mul_of_nonneg_left hle hc)

end KsIndex.PowerArc

