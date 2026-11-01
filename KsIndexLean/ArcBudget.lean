module

/-
KsIndexLean — Weighted Fourier energy of the junction cutoff.

For `0 < η ≤ 1/4`, the junction field `fJ η` has the coefficient bounds
`‖fc (fJ η) ℓ‖ ≤ 2η√η` and, when `|ℓ+1/2| ≥ 1`,
`‖fc (fJ η) ℓ‖ ≤ Ktail * |ℓ+1/2|^(-3/2)`.
Splitting the squared norm into powers `1/2` and `3/2` and applying these
bounds yields a summable majorant:

`(1+|ℓ|) * ‖fc (fJ η) ℓ‖² ≤
  2^(3/2) * Ktail^(3/2) * η^(3/4) * |ℓ+1/2|^(-5/4)`.

For the exceptional indices `0` and `-1`, the first coefficient bound and
`Ktail ≥ 200` give the same inequality without using the tail estimate.
Summing proves weighted summability and the bound `CB * η^(3/4)`, where
`CB` is independent of `η`. These statements concern the junction field;
combining it with the uncut field and proving arc-support membership are
separate steps.
-/
public import KsIndexLean.JunctionFresnel

@[expose] public section


noncomputable section

open Real Set
open KsIndex.ArcField KsIndex.ArcJunction KsIndex.JunctionFresnel
open KsIndex.PunctureCutoff KsIndex.CutLaplacian

namespace KsIndex.ArcBudget

/-- The coefficient tail constant: `Ktail = (2π)⁻¹·8·CJfr`. -/
def Ktail : ℝ := (2 * π)⁻¹ * (8 * CJfr)

lemma Ktail_ge : 200 ≤ Ktail := by
  have hCJ : 200 ≤ CJfr := by
    unfold CJfr
    nlinarith [Mψ_nonneg, Mψ₂_nonneg]
  have hπ : 2 * π ≤ 6.3 := by nlinarith [Real.pi_lt_d2]
  have hinv : (6.3 : ℝ)⁻¹ ≤ (2 * π)⁻¹ := inv_anti₀ (by positivity) hπ
  calc (200 : ℝ) ≤ (6.3)⁻¹ * (8 * 200) := by norm_num
    _ ≤ (2 * π)⁻¹ * (8 * CJfr) := by
        refine mul_le_mul hinv (by linarith) (by norm_num) (by positivity)
    _ = Ktail := rfl

lemma Ktail_nonneg : 0 ≤ Ktail := le_trans (by norm_num) Ktail_ge

/-! ### The frequency floor and weight comparison -/

lemma xi_pos (ℓ : ℤ) : 0 < |(ℓ : ℝ) + 1/2| := by
  rw [abs_pos]
  intro h
  have h2 : ((2 * ℓ : ℤ) : ℝ) = -1 := by push_cast; linarith
  have : (2 * ℓ : ℤ) = -1 := by exact_mod_cast h2
  omega

lemma xi_ge {ℓ : ℤ} (h0 : ℓ ≠ 0) (h1 : ℓ ≠ -1) : (3 : ℝ)/2 ≤ |(ℓ : ℝ) + 1/2| := by
  rcases le_or_gt 1 ℓ with h | h
  · have h' : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    linarith
  · have hℓ2 : ℓ ≤ -2 := by omega
    have h' : (ℓ : ℝ) ≤ -2 := by exact_mod_cast hℓ2
    rw [abs_of_neg (by linarith)]
    linarith

lemma one_add_abs_le {ℓ : ℤ} (h0 : ℓ ≠ 0) (h1 : ℓ ≠ -1) :
    1 + |(ℓ : ℝ)| ≤ 2 * |(ℓ : ℝ) + 1/2| := by
  rcases le_or_gt 1 ℓ with h | h
  · have h' : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  · have hℓ2 : ℓ ≤ -2 := by omega
    have h' : (ℓ : ℝ) ≤ -2 := by exact_mod_cast hℓ2
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    linarith

/-! ### The envelope series -/

/-- `Σ_ℤ |ℓ + 1/2|^{−5/4}` converges (comparison with `2^{5/4}·|ℓ|^{−5/4}` off `ℓ = 0`). -/
lemma summable_env : Summable (fun ℓ : ℤ => |(ℓ : ℝ) + 1/2| ^ (-(5/4) : ℝ)) := by
  have hbase : Summable (fun ℓ : ℤ => (2 : ℝ) ^ ((5:ℝ)/4) * |(ℓ : ℝ)| ^ (-(5/4) : ℝ)) :=
    (Real.summable_abs_int_rpow (by norm_num)).mul_left _
  have hpatch : Summable (fun ℓ : ℤ =>
      if ℓ = 0 then (0:ℝ) else |(ℓ : ℝ) + 1/2| ^ (-(5/4) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) (fun ℓ => ?_) hbase
    · by_cases h : ℓ = 0
      · simp [h]
      · simp only [h, if_false]
        exact Real.rpow_nonneg (abs_nonneg _) _
    · by_cases h : ℓ = 0
      · simp only [h, if_true]
        positivity
      · simp only [h, if_false]
        have hone : (1 : ℝ) ≤ |(ℓ : ℝ)| := by
          have h1 : (1 : ℤ) ≤ |ℓ| := Int.one_le_abs (by omega)
          calc (1:ℝ) ≤ ((|ℓ| : ℤ) : ℝ) := by exact_mod_cast h1
            _ = |(ℓ : ℝ)| := by push_cast; rfl
        have hlow : |(ℓ : ℝ)| / 2 ≤ |(ℓ : ℝ) + 1/2| := by
          have h1 : |(ℓ : ℝ)| - 1/2 ≤ |(ℓ : ℝ) + 1/2| := by
            have hd := abs_sub_abs_le_abs_sub ((ℓ : ℝ)) (-(1/2))
            rw [sub_neg_eq_add] at hd
            have h3 : |(-(1:ℝ)/2)| = 1/2 := by norm_num
            have h4 : |(ℓ:ℝ)| - |(-(1/2):ℝ)| ≤ |(ℓ:ℝ) + 1/2| := hd
            have h5 : |(-(1/2):ℝ)| = 1/2 := by norm_num
            linarith [h4, h5.le, h5.ge]
          linarith
        have hmono : |(ℓ : ℝ) + 1/2| ^ (-(5/4) : ℝ)
            ≤ (|(ℓ : ℝ)| / 2) ^ (-(5/4) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) hlow (by norm_num)
        refine le_trans hmono (le_of_eq ?_)
        rw [show |(ℓ : ℝ)| / 2 = |(ℓ : ℝ)| * (2 : ℝ)⁻¹ by ring,
          Real.mul_rpow (abs_nonneg _) (by norm_num),
          Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg]
        ring
  have hsingle : Summable (fun ℓ : ℤ =>
      if ℓ = 0 then |((0:ℤ) : ℝ) + 1/2| ^ (-(5/4) : ℝ) else (0:ℝ)) := by
    apply summable_of_ne_finset_zero (s := ({0} : Finset ℤ))
    intro ℓ hℓ
    simp only [Finset.mem_singleton] at hℓ
    simp [hℓ]
  refine (hpatch.add hsingle).congr (fun ℓ => ?_)
  by_cases h : ℓ = 0 <;> simp [h]

/-- The budget constant. -/
def CB : ℝ :=
  2 ^ ((3:ℝ)/2) * Ktail ^ ((3:ℝ)/2) * (∑' ℓ : ℤ, |(ℓ : ℝ) + 1/2| ^ (-(5/4) : ℝ))

/-! ### The pointwise interpolated majorant -/

/-- The tail bound in `rpow` form. -/
lemma tail_rpow (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) (ℓ : ℤ)
    (hℓ : 1 ≤ |(ℓ : ℝ) + 1/2|) :
    ‖Parseval.fc (fJ η) ℓ‖ ≤ Ktail * |(ℓ : ℝ) + 1/2| ^ (-(3/2) : ℝ) := by
  have h := norm_fc_fJ_le_tail η hη0 hη ℓ hℓ
  have hpos := xi_pos ℓ
  have hid : (Real.sqrt |(ℓ : ℝ) + 1/2|)⁻¹ * |(ℓ : ℝ) + 1/2|⁻¹
      = |(ℓ : ℝ) + 1/2| ^ (-(3/2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (abs_nonneg _),
      show |(ℓ : ℝ) + 1/2|⁻¹ = |(ℓ : ℝ) + 1/2| ^ (-(1:ℝ)) by
        rw [Real.rpow_neg (abs_nonneg _), Real.rpow_one],
      ← Real.rpow_add hpos]
    norm_num
  rw [hid] at h
  exact le_trans h (le_of_eq (by rw [Ktail]))

/-- **The interpolated majorant** — for every `ℓ` (the exceptional pair absorbed by
`Ktail ≥ 200`). -/
lemma weighted_le_majorant (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) (ℓ : ℤ) :
    (1 + |(ℓ : ℝ)|) * ‖Parseval.fc (fJ η) ℓ‖ ^ 2
      ≤ 2 ^ ((3:ℝ)/2) * Ktail ^ ((3:ℝ)/2) * η ^ ((3:ℝ)/4)
        * |(ℓ : ℝ) + 1/2| ^ (-(5/4) : ℝ) := by
  have hη1 : η ≤ 1 := by linarith
  have hpos := xi_pos ℓ
  have hhead : ‖Parseval.fc (fJ η) ℓ‖ ≤ 2 * η * Real.sqrt η :=
    norm_fc_fJ_le_head η hη0 hη ℓ
  have hnn : (0:ℝ) ≤ ‖Parseval.fc (fJ η) ℓ‖ := norm_nonneg _
  -- `2η√η = 2·η^{3/2}` and `(2η^{3/2})^{1/2} = 2^{1/2}·η^{3/4}`
  have hhead32 : 2 * η * Real.sqrt η = 2 * η ^ ((3:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,
      show (2:ℝ) * η * η ^ ((1:ℝ)/2) = 2 * (η ^ ((1:ℝ)) * η ^ ((1:ℝ)/2)) by
        rw [Real.rpow_one]; ring,
      ← Real.rpow_add hη0]
    norm_num
  by_cases hexc : ℓ = 0 ∨ ℓ = -1
  · -- exceptional pair: head bound squared against the common majorant
    have habs : |(ℓ : ℝ)| ≤ 1 := by
      rcases hexc with h | h <;> simp [h]
    have hxihalf : |(ℓ : ℝ) + 1/2| = 1/2 := by
      rcases hexc with h | h <;> (rw [h]; norm_num)
    have hW : (1 + |(ℓ : ℝ)|) * ‖Parseval.fc (fJ η) ℓ‖ ^ 2
        ≤ 2 * (2 * η * Real.sqrt η) ^ 2 := by
      have hsq : ‖Parseval.fc (fJ η) ℓ‖ ^ 2 ≤ (2 * η * Real.sqrt η) ^ 2 := by
        exact pow_le_pow_left₀ hnn hhead 2
      nlinarith [sq_nonneg (2 * η * Real.sqrt η), hsq, habs,
        sq_nonneg ‖Parseval.fc (fJ η) ℓ‖]
    have hM : (400:ℝ) * η ^ ((3:ℝ)/4)
        ≤ 2 ^ ((3:ℝ)/2) * Ktail ^ ((3:ℝ)/2) * η ^ ((3:ℝ)/4)
          * |(ℓ : ℝ) + 1/2| ^ (-(5/4) : ℝ) := by
      rw [hxihalf]
      have h1 : (2:ℝ) ≤ 2 ^ ((3:ℝ)/2) := by
        calc (2:ℝ) = 2 ^ ((1:ℝ)) := (Real.rpow_one 2).symm
          _ ≤ 2 ^ ((3:ℝ)/2) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h2 : (200:ℝ) ≤ Ktail ^ ((3:ℝ)/2) := by
        calc (200:ℝ) = 200 ^ ((1:ℝ)) := (Real.rpow_one 200).symm
          _ ≤ 200 ^ ((3:ℝ)/2) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ ≤ Ktail ^ ((3:ℝ)/2) :=
            Real.rpow_le_rpow (by norm_num) Ktail_ge (by norm_num)
      have h3 : (1:ℝ) ≤ ((1:ℝ)/2) ^ (-(5/4) : ℝ) := by
        rw [show ((1:ℝ)/2) = (2:ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num),
          ← Real.rpow_neg (by norm_num), neg_neg]
        calc (1:ℝ) = 2 ^ ((0:ℝ)) := (Real.rpow_zero 2).symm
          _ ≤ 2 ^ ((5:ℝ)/4) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have hηp : (0:ℝ) ≤ η ^ ((3:ℝ)/4) := Real.rpow_nonneg hη0.le _
      have h4 : (400:ℝ) ≤ 2 ^ ((3:ℝ)/2) * Ktail ^ ((3:ℝ)/2) := by
        calc (400:ℝ) = 2 * 200 := by norm_num
          _ ≤ 2 ^ ((3:ℝ)/2) * Ktail ^ ((3:ℝ)/2) :=
            mul_le_mul h1 h2 (by norm_num) (by positivity)
      calc (400:ℝ) * η ^ ((3:ℝ)/4)
          ≤ 2 ^ ((3:ℝ)/2) * Ktail ^ ((3:ℝ)/2) * η ^ ((3:ℝ)/4) :=
            mul_le_mul_of_nonneg_right h4 hηp
        _ ≤ 2 ^ ((3:ℝ)/2) * Ktail ^ ((3:ℝ)/2) * η ^ ((3:ℝ)/4) * ((1:ℝ)/2) ^ (-(5/4) : ℝ) :=
            le_mul_of_one_le_right
              (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
                (Real.rpow_nonneg Ktail_nonneg _)) hηp) h3
    refine le_trans hW (le_trans ?_ hM)
    -- `2·(2η^{3/2})² = 8η³ ≤ 400·η^{3/4}` for `η ≤ 1`
    rw [hhead32]
    have hη3 : η ^ ((3:ℝ)) ≤ η ^ ((3:ℝ)/4) :=
      Real.rpow_le_rpow_of_exponent_ge hη0 hη1 (by norm_num)
    have hηp : (0:ℝ) ≤ η ^ ((3:ℝ)/4) := Real.rpow_nonneg hη0.le _
    have hsq32 : (2 * η ^ ((3:ℝ)/2)) ^ 2 = 4 * η ^ ((3:ℝ)) := by
      rw [mul_pow, ← Real.rpow_natCast (η ^ ((3:ℝ)/2)) 2, ← Real.rpow_mul hη0.le]
      norm_num
    rw [hsq32]
    linarith [hη3, hηp]
  · -- generic `ℓ`: interpolation `‖f̂‖² = ‖f̂‖^{1/2}·‖f̂‖^{3/2}`
    rw [not_or] at hexc
    have htail := tail_rpow η hη0 hη ℓ (le_trans (by norm_num) (xi_ge hexc.1 hexc.2))
    have hweight := one_add_abs_le hexc.1 hexc.2
    have hsplit : ‖Parseval.fc (fJ η) ℓ‖ ^ 2
        = ‖Parseval.fc (fJ η) ℓ‖ ^ ((1:ℝ)/2) * ‖Parseval.fc (fJ η) ℓ‖ ^ ((3:ℝ)/2) := by
      rw [← Real.rpow_natCast ‖Parseval.fc (fJ η) ℓ‖ 2,
        ← Real.rpow_add' hnn (by norm_num : (1:ℝ)/2 + 3/2 ≠ 0)]
      norm_num
    have hf1 : ‖Parseval.fc (fJ η) ℓ‖ ^ ((1:ℝ)/2)
        ≤ (2 * η * Real.sqrt η) ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow hnn hhead (by norm_num)
    have hf2 : ‖Parseval.fc (fJ η) ℓ‖ ^ ((3:ℝ)/2)
        ≤ (Ktail * |(ℓ : ℝ) + 1/2| ^ (-(3/2) : ℝ)) ^ ((3:ℝ)/2) :=
      Real.rpow_le_rpow hnn htail (by norm_num)
    -- rpow algebra for the majorant pieces
    have idA : (2 * η * Real.sqrt η) ^ ((1:ℝ)/2)
        = 2 ^ ((1:ℝ)/2) * η ^ ((3:ℝ)/4) := by
      rw [hhead32, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hη0.le _),
        ← Real.rpow_mul hη0.le]
      norm_num
    have idB : (Ktail * |(ℓ : ℝ) + 1/2| ^ (-(3/2) : ℝ)) ^ ((3:ℝ)/2)
        = Ktail ^ ((3:ℝ)/2) * |(ℓ : ℝ) + 1/2| ^ (-(9/4) : ℝ) := by
      rw [Real.mul_rpow Ktail_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        ← Real.rpow_mul (abs_nonneg _)]
      norm_num
    have idC : |(ℓ : ℝ) + 1/2| * |(ℓ : ℝ) + 1/2| ^ (-(9/4) : ℝ)
        = |(ℓ : ℝ) + 1/2| ^ (-(5/4) : ℝ) := by
      rw [show |(ℓ : ℝ) + 1/2| * |(ℓ : ℝ) + 1/2| ^ (-(9/4) : ℝ)
          = |(ℓ : ℝ) + 1/2| ^ ((1:ℝ)) * |(ℓ : ℝ) + 1/2| ^ (-(9/4) : ℝ) by
          rw [Real.rpow_one],
        ← Real.rpow_add hpos]
      norm_num
    have hprod : ‖Parseval.fc (fJ η) ℓ‖ ^ 2
        ≤ (2 ^ ((1:ℝ)/2) * η ^ ((3:ℝ)/4))
          * (Ktail ^ ((3:ℝ)/2) * |(ℓ : ℝ) + 1/2| ^ (-(9/4) : ℝ)) := by
      rw [hsplit, ← idA, ← idB]
      exact mul_le_mul hf1 hf2 (Real.rpow_nonneg hnn _)
        (Real.rpow_nonneg (by positivity) _)
    calc (1 + |(ℓ : ℝ)|) * ‖Parseval.fc (fJ η) ℓ‖ ^ 2
        ≤ (2 * |(ℓ : ℝ) + 1/2|)
          * ((2 ^ ((1:ℝ)/2) * η ^ ((3:ℝ)/4))
            * (Ktail ^ ((3:ℝ)/2) * |(ℓ : ℝ) + 1/2| ^ (-(9/4) : ℝ))) := by
          refine mul_le_mul hweight hprod (by positivity) (by positivity)
      _ = (2 * 2 ^ ((1:ℝ)/2)) * Ktail ^ ((3:ℝ)/2) * η ^ ((3:ℝ)/4)
          * (|(ℓ : ℝ) + 1/2| * |(ℓ : ℝ) + 1/2| ^ (-(9/4) : ℝ)) := by ring
      _ = 2 ^ ((3:ℝ)/2) * Ktail ^ ((3:ℝ)/2) * η ^ ((3:ℝ)/4)
          * |(ℓ : ℝ) + 1/2| ^ (-(5/4) : ℝ) := by
          rw [idC, show (2:ℝ) * 2 ^ ((1:ℝ)/2) = 2 ^ ((3:ℝ)/2) by
            rw [show (2:ℝ) * 2 ^ ((1:ℝ)/2) = 2 ^ ((1:ℝ)) * 2 ^ ((1:ℝ)/2) by
              rw [Real.rpow_one],
              ← Real.rpow_add (by norm_num)]
            norm_num]

/-! ### The budget -/

/-- The junction Fourier coefficients have summable weighted squared norm for
`0 < η ≤ 1/4`. -/
theorem summable_weighted (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) :
    Summable (fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖Parseval.fc (fJ η) ℓ‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun ℓ => by positivity)
    (fun ℓ => weighted_le_majorant η hη0 hη ℓ) ?_
  exact (summable_env.mul_left _)

/-- **The budget**: `∑' ℓ, (1+|ℓ|)·‖fc (fJ η) ℓ‖² ≤ CB·η^{3/4}` — the junction cut-cost
vanishes as `η → 0`. -/
theorem budget_le (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) :
    (∑' ℓ : ℤ, (1 + |(ℓ : ℝ)|) * ‖Parseval.fc (fJ η) ℓ‖ ^ 2)
      ≤ CB * η ^ ((3:ℝ)/4) := by
  have h := (summable_weighted η hη0 hη).tsum_le_tsum
    (fun ℓ => weighted_le_majorant η hη0 hη ℓ) (summable_env.mul_left _)
  refine le_trans h (le_of_eq ?_)
  rw [tsum_mul_left, CB]
  ring

lemma CB_nonneg : 0 ≤ CB := by
  refine mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg Ktail_nonneg _)) ?_
  exact tsum_nonneg (fun ℓ => Real.rpow_nonneg (abs_nonneg _) _)

end KsIndex.ArcBudget
