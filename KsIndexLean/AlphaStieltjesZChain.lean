module

public import KsIndexLean.AlphaStieltjesPeel
public import KsIndexLean.AlphaStieltjesCompensated

@[expose] public section


/-! The forward recurrence in `z` and finite group reduction.

At a fixed base `r`, the recurrence expresses `H(r, z + k)` as a rational
multiple of `H(r, z)` plus accumulated forcing. Combined with upward peeling,
it reduces a finite group to a common base transform. Nonvanishing of each
recurrence denominator is an explicit hypothesis; positivity of `z` alone
is insufficient. The group identity is unnormalized. -/

noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ Real PowerArc

/-- Homogeneous coefficient of the iterated z-forward recurrence. -/
def zChainCoeff (β r z : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => ((z + k + 1 - (r + β + 2) / 2) / (z + k + 1 - (r - β) / 2)) *
      zChainCoeff β r z k

/-- Accumulated forcing of the iterated z-forward recurrence. -/
def zChainForce (β r z : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => ((z + k + 1 - (r + β + 2) / 2) / (z + k + 1 - (r - β) / 2)) *
      zChainForce β r z k
      + g β r * ((r + β + 2) / 2 - 1) / ((z + k) * (z + k + 1 - (r - β) / 2))

/-- The iterated z-forward chain: `H(r, z+k)` as an explicit rational multiple
of `H(r, z)` plus explicit forcing, under the named denominator hypotheses. -/
theorem paS_z_chain {β r z : ℝ} (hβ : 0 < β) (hr : β ≤ r) (hz : 0 < z) (k : ℕ)
    (hd : ∀ u : ℕ, u < k → z + u + 1 - (r - β) / 2 ≠ 0) :
    powerArcStieltjes β r (z + k) =
      zChainCoeff β r z k * powerArcStieltjes β r z + zChainForce β r z k := by
  induction k with
  | zero => simp [zChainCoeff, zChainForce]
  | succ m ih =>
      have hzm : (0 : ℝ) < z + m := by
        have := Nat.cast_nonneg (α := ℝ) m
        linarith
      have hdm : z + m + 1 - (r - β) / 2 ≠ 0 := hd m (Nat.lt_succ_self m)
      have hfwd := powerArcStieltjes_forward β r (z + m) hβ hr hzm hdm
      have ihm := ih (fun u hu => hd u (Nat.lt_succ_of_lt hu))
      rw [show (z + ((m : ℕ) + 1 : ℕ) : ℝ) = (z + m) + 1 by push_cast; ring, hfwd, ihm,
        zChainCoeff, zChainForce]
      push_cast
      ring

/-- A finite combination of transforms at `r i = r_g − 2 k i` reduces to the
base transform with explicit rational multiplier and forcing. Normalization
by `g β 0` is left to callers. -/
theorem group_reduction {ι : Type*} [Fintype ι] (β z r_g : ℝ) (c : ι → ℝ)
    (kk : ι → ℕ) (r : ι → ℝ) (hrel : ∀ i, r i + 2 * kk i = r_g)
    (hβ : 0 < β) (hri : ∀ i, β ≤ r i) (hz : 0 < z)
    (hd : ∀ i, ∀ u : ℕ, u < kk i → z + u + 1 - (r_g - β) / 2 ≠ 0) :
    (∑ i, c i * powerArcStieltjes β (r i) z) =
      (∑ i, c i * (-1 : ℝ) ^ kk i * zChainCoeff β r_g z (kk i)) *
          powerArcStieltjes β r_g z
      + ∑ i, c i * ((∑ u ∈ Finset.range (kk i),
            (-1 : ℝ) ^ u * g β (r i + 2 * u) / (z + u))
          + (-1 : ℝ) ^ kk i * zChainForce β r_g z (kk i)) := by
  rw [Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hterm := paS_iter hβ (hri i) hz (kk i)
  have hbase : r i + 2 * (kk i : ℝ) = r_g := by
    have := hrel i
    exact_mod_cast this
  rw [hbase] at hterm
  have hchain := paS_z_chain hβ (by rw [← hbase]; have := Nat.cast_nonneg (α := ℝ) (kk i); linarith [hri i] : β ≤ r_g) hz (kk i) (hd i)
  rw [hterm, hchain]
  ring

/-! Denominator conditions for the trial.

Four fractional-part lemmas establish nonvanishing for the integer-indexed
`z = n + 9/2` family. The small-`z` helper selects a supplied per-step condition. -/

/-- The uniform n-family discharge: `z = n + 9/2` with integer `n` never hits
the denominators, because `(r_g − β)/2 − 9/2 − 1` has nonzero fractional part. -/
lemma denom_ne_zero_nFamily {β r_g : ℝ} (n : ℤ) (u : ℕ)
    (hfrac : ∀ m : ℤ, (m : ℝ) ≠ (r_g - β) / 2 - 11 / 2) :
    ((n : ℝ) + 9/2) + u + 1 - (r_g - β) / 2 ≠ 0 := by
  intro hc
  apply hfrac (n + u)
  push_cast
  linarith

/-- Fractional-part fact for (β, r_g) = (4323618/10⁷, 15). -/
lemma frac_b15 : ∀ m : ℤ, (m : ℝ) ≠ ((15 : ℝ) - 4323618/10000000) / 2 - 11 / 2 := by
  intro m hc
  have h2 : (20000000 : ℝ) * m = 35676382 := by linarith
  have h3 : (20000000 : ℤ) * m = 35676382 := by exact_mod_cast h2
  omega

/-- Fractional-part fact for (β, r_g) = (4323618/10⁷, 14). -/
lemma frac_b14 : ∀ m : ℤ, (m : ℝ) ≠ ((14 : ℝ) - 4323618/10000000) / 2 - 11 / 2 := by
  intro m hc
  have h2 : (20000000 : ℝ) * m = 25676382 := by linarith
  have h3 : (20000000 : ℤ) * m = 25676382 := by exact_mod_cast h2
  omega

/-- Fractional-part fact for (β, r_g) = (5676382/10⁷, 15). -/
lemma frac_c15 : ∀ m : ℤ, (m : ℝ) ≠ ((15 : ℝ) - 5676382/10000000) / 2 - 11 / 2 := by
  intro m hc
  have h2 : (20000000 : ℝ) * m = 34323618 := by linarith
  have h3 : (20000000 : ℤ) * m = 34323618 := by exact_mod_cast h2
  omega

/-- Fractional-part fact for (β, r_g) = (5676382/10⁷, 14). -/
lemma frac_c14 : ∀ m : ℤ, (m : ℝ) ≠ ((14 : ℝ) - 5676382/10000000) / 2 - 11 / 2 := by
  intro m hc
  have h2 : (20000000 : ℝ) * m = 24323618 := by linarith
  have h3 : (20000000 : ℤ) * m = 24323618 := by exact_mod_cast h2
  omega

/-- Select a denominator condition at `z = 13/3` from supplied nonvanishing
checks for the six steps `u < 6`. -/
lemma denom_ne_zero_smallz {β r_g : ℝ} (u : ℕ) (hu : u < 6)
    (hval : ∀ v : ℕ, v < 6 → (13/3 : ℝ) + v + 1 - (r_g - β) / 2 ≠ 0) :
    (13/3 : ℝ) + u + 1 - (r_g - β) / 2 ≠ 0 :=
  hval u hu

end KsIndex.OppositeHalf
