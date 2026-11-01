module

public import KsIndexLean.CircleSigmaDomain
public import KsIndexLean.SquareWaveCoefficients

@[expose] public section


/-! # Nonclosedness of the sign-multiplier graph domain

The paper's note accompanying `sgnmul_norm` states that `H^{1/2}_ς(S¹)` is not
closed in `H^{1/2}(S¹)`. This module proves that assertion on the full circle
by an explicit sequence of trigonometric polynomials.

The limit is the constant `1` (`modeHalf 0`). Its product with `ς` is the
square wave, whose weighted coefficient square sum dominates the harmonic
series. Thus `not_memDomSigma_one` excludes the limit from the graph domain.

For `N ≥ 1`, set `L_N = Σ_{n=1}^N 1/n` and
`u_N = 1 − (1/L_N) Σ_{n=1}^N e^{i·12n·θ}/n`. The polynomial vanishes at the
six jumps of `ς`: each exponential equals `1` there. The proof uses the
corresponding coefficient cancellation. At frequencies `6k+3`, writing
`j = 2k+1`, the kernel remainder is
`B_N(j) = −(4/L_N) Σ_{n=1}^N 1/(j(j−4n))`.
The resulting quadratic tail decay gives `memDomSigma_uApprox`.

Finally, `norm_sq_sub_uApprox_le` bounds the squared distance by `13/L_N`
for `N ≥ 1`, and `uApprox_tendsto` proves convergence to the constant.
`memDomSigma_not_closed` combines these results. The norms use the repository's
half-order weights, equivalent to those in the paper; closedness is unchanged
by this norm convention.
-/

noncomputable section
open MeasureTheory
namespace KsIndex.CircleSobolev
open KsIndex.Trace

/-! ## Coefficient linearity (generic `Space s` API) -/

lemma coeff_add (s : ℝ) (u v : Space s) (n : ℤ) :
    coeff s (u + v) n = coeff s u n + coeff s v n := by
  simp only [coeff]
  rw [lp.coeFn_add, Pi.add_apply, mul_add]

lemma coeff_sub (s : ℝ) (u v : Space s) (n : ℤ) :
    coeff s (u - v) n = coeff s u n - coeff s v n := by
  simp only [coeff]
  rw [lp.coeFn_sub, Pi.sub_apply, mul_sub]

lemma coeff_smul (s : ℝ) (c : ℂ) (u : Space s) (n : ℤ) :
    coeff s (c • u) n = c * coeff s u n := by
  simp only [coeff]
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma coeff_finsetSum {ι : Type*} (s : ℝ) (t : Finset ι) (f : ι → Space s) (n : ℤ) :
    coeff s (∑ i ∈ t, f i) n = ∑ i ∈ t, coeff s (f i) n := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [coeff]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, coeff_add, ih]

/-! ## The unit modes of `H^{1/2}` -/

/-- The single Fourier mode `e^{iℓθ}` as an `H^{1/2}` element (stored coordinate
`weight(1/2, ℓ)`, physical coefficient `1`).  `modeHalf 0` is the constant `1`. -/
def modeHalf (ℓ : ℤ) : Space (1 / 2 : ℝ) :=
  lp.single 2 ℓ ((weight (1 / 2) ℓ : ℝ) : ℂ)

lemma coeff_modeHalf (ℓ n : ℤ) :
    coeff (1 / 2) (modeHalf ℓ) n = (Pi.single ℓ 1 : ℤ → ℂ) n := by
  have hw : ((weight (1 / 2) n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (weight_pos (1 / 2) n).ne'
  simp only [coeff, modeHalf, lp.coeFn_single, Pi.single_apply]
  split_ifs with h
  · subst h
    exact inv_mul_cancel₀ hw
  · simp

/-- The realization of `modeHalf ℓ` is the Fourier mode on the circle
(in particular `modeHalf 0` realizes the constant `1`). -/
lemma toL2Half_modeHalf (ℓ : ℤ) : toL2Half (modeHalf ℓ) = fourierTestLp ℓ := by
  apply circleFourierCLE.injective
  apply Subtype.ext
  funext n
  rw [circleFourierCLE_apply, fourierCoeff_toL2, coeff_modeHalf,
    circleFourierCLE_fourierTestLp]
  rw [lp.coeFn_single]

/-! ## The harmonic weights and the approximating sequence -/

/-- The harmonic partial sum `L_N = Σ_{n=1}^N 1/n`. -/
def harmonicLN (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹

lemma one_le_harmonicLN {N : ℕ} (hN : 1 ≤ N) : 1 ≤ harmonicLN N := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩
  calc (1 : ℝ) = ((1 : ℕ) : ℝ)⁻¹ := by norm_num
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ :=
        Finset.single_le_sum (f := fun n : ℕ => ((n : ℝ))⁻¹)
          (fun n _ => by positivity) h1

lemma harmonicLN_pos {N : ℕ} (hN : 1 ≤ N) : 0 < harmonicLN N :=
  lt_of_lt_of_le one_pos (one_le_harmonicLN hN)

/-- The approximating sequence `u_N = 1 − (1/L_N) Σ_{n=1}^N e^{i·12n·θ}/n`: each mode
frequency is a multiple of `12`. For `N ≥ 1`, the polynomial therefore vanishes
at all six jumps of `ς`. -/
def uApprox (N : ℕ) : Space (1 / 2 : ℝ) :=
  modeHalf 0 -
    ((harmonicLN N : ℝ) : ℂ)⁻¹ • ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℂ)⁻¹ • modeHalf (12 * (n : ℤ))

lemma coeff_uApprox (N : ℕ) (d : ℤ) :
    coeff (1 / 2) (uApprox N) d
      = (Pi.single (0 : ℤ) 1 : ℤ → ℂ) d
        - ((harmonicLN N : ℝ) : ℂ)⁻¹
            * ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℂ)⁻¹ * (Pi.single (12 * (n : ℤ)) 1 : ℤ → ℂ) d := by
  rw [uApprox, coeff_sub, coeff_smul, coeff_finsetSum, coeff_modeHalf]
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [coeff_smul, coeff_modeHalf]

/-! ## The coefficients of `ς·u_N` -/

/-- Convolving against a single coefficient spike picks out one shift of the kernel. -/
lemma tsum_sigmaKernel_single (m ℓ : ℤ) :
    ∑' d : ℤ, circleFourierCoeff sigmaField (m - d) * (Pi.single ℓ 1 : ℤ → ℂ) d
      = circleFourierCoeff sigmaField (m - ℓ) := by
  rw [tsum_eq_single ℓ]
  · simp
  · intro b hb
    simp [hb]

/-- The coefficients of `ς·u_N`: the kernel minus the harmonic combination of its
`12n`-shifts (the finite-support specialization of `circleFourierCoeff_sigmaMul`). -/
lemma sigmaMul_uApprox_coeff (N : ℕ) (m : ℤ) :
    circleFourierCoeff (sigmaMul (toL2Half (uApprox N))) m
      = circleFourierCoeff sigmaField m
        - ((harmonicLN N : ℝ) : ℂ)⁻¹
            * ∑ n ∈ Finset.Icc 1 N,
                ((n : ℕ) : ℂ)⁻¹ * circleFourierCoeff sigmaField (m - 12 * n) := by
  rw [circleFourierCoeff_sigmaMul]
  have hcoeff : ∀ d : ℤ,
      circleFourierCoeff sigmaField (m - d) * circleFourierCoeff (toL2Half (uApprox N)) d
        = circleFourierCoeff sigmaField (m - d) * (Pi.single (0 : ℤ) 1 : ℤ → ℂ) d
          - ((harmonicLN N : ℝ) : ℂ)⁻¹
              * ∑ n ∈ Finset.Icc 1 N,
                  ((n : ℕ) : ℂ)⁻¹
                    * (circleFourierCoeff sigmaField (m - d)
                        * (Pi.single (12 * (n : ℤ)) 1 : ℤ → ℂ) d) := by
    intro d
    have hS : ∑ n ∈ Finset.Icc 1 N,
          ((n : ℕ) : ℂ)⁻¹
            * (circleFourierCoeff sigmaField (m - d) * (Pi.single (12 * (n : ℤ)) 1 : ℤ → ℂ) d)
        = circleFourierCoeff sigmaField (m - d)
            * ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℂ)⁻¹ * (Pi.single (12 * (n : ℤ)) 1 : ℤ → ℂ) d := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [fourierCoeff_toL2, coeff_uApprox, hS]
    ring
  rw [tsum_congr hcoeff]
  have hsummable_single : ∀ ℓ : ℤ,
      Summable (fun d : ℤ =>
        circleFourierCoeff sigmaField (m - d) * (Pi.single ℓ 1 : ℤ → ℂ) d) := by
    intro ℓ
    apply summable_of_ne_finset_zero (s := ({ℓ} : Finset ℤ))
    intro b hb
    simp only [Finset.mem_singleton] at hb
    simp [hb]
  have hsummable_comb :
      Summable (fun d : ℤ => ((harmonicLN N : ℝ) : ℂ)⁻¹
        * ∑ n ∈ Finset.Icc 1 N,
            ((n : ℕ) : ℂ)⁻¹
              * (circleFourierCoeff sigmaField (m - d)
                  * (Pi.single (12 * (n : ℤ)) 1 : ℤ → ℂ) d)) := by
    refine Summable.mul_left _ (summable_sum fun n _ => ?_)
    exact (hsummable_single (12 * (n : ℤ))).mul_left _
  rw [(hsummable_single 0).tsum_sub hsummable_comb, tsum_sigmaKernel_single, sub_zero]
  congr 1
  rw [tsum_mul_left]
  congr 1
  rw [Summable.tsum_finsetSum
    (f := fun (n : ℕ) (d : ℤ) => ((n : ℕ) : ℂ)⁻¹
      * (circleFourierCoeff sigmaField (m - d) * (Pi.single (12 * (n : ℤ)) 1 : ℤ → ℂ) d))
    fun n _ => (hsummable_single (12 * (n : ℤ))).mul_left _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [tsum_mul_left, tsum_sigmaKernel_single]

/-! ## The limit: the constant is not in the domain

`ς·1` is the square wave; its `H^{1/2}`-weighted coefficient square sum restricted to the
support `6k+3` dominates the harmonic series. -/

theorem not_memDomSigma_one : ¬ MemDomSigma (modeHalf 0) := by
  intro hmem
  rw [MemDomSigma, mem_range_toL2_iff] at hmem
  rw [show (2 * (1 / 2 : ℝ)) = 1 by norm_num] at hmem
  simp only [Real.rpow_one] at hmem
  have hval : ∀ m : ℤ, circleFourierCoeff (sigmaMul (toL2Half (modeHalf 0))) m
      = circleFourierCoeff sigmaField m := by
    intro m
    rw [toL2Half_modeHalf, circleFourierCoeff_sigmaMul_fourierTestLp, sub_zero]
  simp only [hval] at hmem
  have hinj : Function.Injective (fun k : ℕ => (6 * (k : ℤ) + 3)) := by
    intro a b hab
    simpa using hab
  have hcomp := hmem.comp_injective hinj
  have hle : ∀ k : ℕ, (6 / Real.pi ^ 2) * (1 / ((k : ℝ) + 1))
      ≤ (1 + |((6 * (k : ℤ) + 3 : ℤ) : ℝ)|)
          * ‖circleFourierCoeff sigmaField (6 * (k : ℤ) + 3)‖ ^ 2 := by
    intro k
    rw [circleFourierCoeff_sigmaField_six_add_three, Complex.norm_real, Real.norm_eq_abs]
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hk1 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
    have habs : |2 / Real.pi * (-1 : ℝ) ^ (k : ℤ) / (2 * ((k : ℤ) : ℝ) + 1)|
        = (2 / Real.pi) / (2 * (k : ℝ) + 1) := by
      push_cast
      rw [abs_div, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, mul_one,
        abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi), abs_of_pos hk1]
    rw [habs]
    have habs2 : |((6 * (k : ℤ) + 3 : ℤ) : ℝ)| = 6 * (k : ℝ) + 3 := by
      push_cast
      rw [abs_of_pos (by positivity)]
    rw [habs2, div_pow, div_pow, mul_one_div, div_div, div_div, ← mul_div_assoc]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [mul_nonneg (mul_pos hpi hpi).le
      (by linarith : (0 : ℝ) ≤ 16 * (k : ℝ) + 10)]
  have h6 : Summable (fun k : ℕ => (6 / Real.pi ^ 2) * (1 / ((k : ℝ) + 1))) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hle hcomp
  have h7 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1)) :=
    (summable_mul_left_iff (by positivity : (6 / Real.pi ^ 2 : ℝ) ≠ 0)).mp h6
  have h8 : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    rw [← summable_nat_add_iff 1]
    simpa using h7
  exact Real.not_summable_one_div_natCast h8

/-! ## The approximators lie in the domain (the jump-cancellation estimate) -/

/-- The square-wave kernel vanishes off the class `6k+3`. -/
lemma sigmaField_coeff_eq_zero_of_not_class {m : ℤ} (hm : ¬ ∃ k : ℤ, m = 6 * k + 3) :
    circleFourierCoeff sigmaField m = 0 := by
  by_cases h3 : (3 : ℤ) ∣ m
  · obtain ⟨t, ht⟩ := h3
    rcases Int.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [ht, hk, show (3 : ℤ) * (k + k) = 6 * k by ring]
      exact circleFourierCoeff_sigmaField_six_mul k
    · exact absurd ⟨k, by omega⟩ hm
  · exact circleFourierCoeff_sigmaField_not_dvd m h3

/-- Off the class, every coefficient of `ς·u_N` vanishes (the `12n`-shifts preserve the
class). -/
lemma sigmaMul_uApprox_coeff_eq_zero_of_not_class (N : ℕ) {m : ℤ}
    (hm : ¬ ∃ k : ℤ, m = 6 * k + 3) :
    circleFourierCoeff (sigmaMul (toL2Half (uApprox N))) m = 0 := by
  rw [sigmaMul_uApprox_coeff, sigmaField_coeff_eq_zero_of_not_class hm]
  have hz : ∀ n ∈ Finset.Icc 1 N,
      ((n : ℕ) : ℂ)⁻¹ * circleFourierCoeff sigmaField (m - 12 * n) = 0 := by
    intro n _
    have hcl : ¬ ∃ k : ℤ, m - 12 * n = 6 * k + 3 := by
      rintro ⟨k, hk⟩
      exact hm ⟨k + 2 * n, by omega⟩
    rw [sigmaField_coeff_eq_zero_of_not_class hcl, mul_zero]
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, mul_zero, sub_zero]

/-- The coefficient cancellation for `N ≥ 1`: on the class
`m = 6k+3`, past the head `8N < |2k+1|`, the leading `1/(2k+1)` of the square-wave
kernel cancels against the harmonic combination of its shifts, leaving quadratic decay:
`B_N(j) = −(4/L_N) Σ_n 1/(j(j−4n))` with `j = 2k+1`. -/
lemma sigmaMul_uApprox_coeff_class_bound (N : ℕ) (hN : 1 ≤ N) (k : ℤ)
    (hk : 8 * (N : ℤ) < |2 * k + 1|) :
    ‖circleFourierCoeff (sigmaMul (toL2Half (uApprox N))) (6 * k + 3)‖
      ≤ 8 * (N : ℝ) / (2 * (k : ℝ) + 1) ^ 2 := by
  have hL1 : (1 : ℝ) ≤ harmonicLN N := one_le_harmonicLN hN
  have hL0 : (0 : ℝ) < harmonicLN N := harmonicLN_pos hN
  set j : ℝ := 2 * (k : ℝ) + 1 with hj
  have hjcast : j = ((2 * k + 1 : ℤ) : ℝ) := by push_cast [hj]; ring
  have hjne : j ≠ 0 := by
    rw [hjcast]
    exact_mod_cast (by omega : (2 * k + 1 : ℤ) ≠ 0)
  have habsj : 8 * (N : ℝ) < |j| := by
    rw [hjcast, ← Int.cast_abs]
    exact_mod_cast hk
  have hjn_ne : ∀ n ∈ Finset.Icc 1 N, j - 4 * (n : ℝ) ≠ 0 := by
    intro n _
    have : (2 * k + 1 - 4 * (n : ℤ)) ≠ 0 := by omega
    have hcast : j - 4 * (n : ℝ) = ((2 * k + 1 - 4 * (n : ℤ) : ℤ) : ℝ) := by
      rw [hjcast]; push_cast; ring
    rw [hcast]
    exact_mod_cast this
  have hjn_half : ∀ n ∈ Finset.Icc 1 N, |j| / 2 ≤ |j - 4 * (n : ℝ)| := by
    intro n hn
    have hn' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h4 : |4 * (n : ℝ)| ≤ 4 * (N : ℝ) := by
      rw [abs_of_nonneg (by positivity)]
      linarith
    calc |j| / 2 ≤ |j| - 4 * (N : ℝ) := by linarith
      _ ≤ |j| - |4 * (n : ℝ)| := by linarith
      _ ≤ |j - 4 * (n : ℝ)| := by
          have := abs_sub_abs_le_abs_sub j (4 * (n : ℝ))
          linarith
  -- the real-valued coefficient
  set B : ℝ := 1 / j - (harmonicLN N)⁻¹
      * ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ)⁻¹ * (1 / (j - 4 * (n : ℝ))) with hB
  have hvalue : circleFourierCoeff (sigmaMul (toL2Half (uApprox N))) (6 * k + 3)
      = (((2 / Real.pi) * (-1 : ℝ) ^ k * B : ℝ) : ℂ) := by
    rw [sigmaMul_uApprox_coeff, circleFourierCoeff_sigmaField_six_add_three]
    have hterm : ∀ n ∈ Finset.Icc 1 N,
        ((n : ℕ) : ℂ)⁻¹ * circleFourierCoeff sigmaField (6 * k + 3 - 12 * n)
          = ((((n : ℕ) : ℝ)⁻¹
              * ((2 / Real.pi) * (-1 : ℝ) ^ k * (1 / (j - 4 * (n : ℝ)))) : ℝ) : ℂ) := by
      intro n _
      have hsh : (6 * k + 3 - 12 * (n : ℤ)) = 6 * (k - 2 * n) + 3 := by ring
      rw [hsh, circleFourierCoeff_sigmaField_six_add_three]
      have hsign : (-1 : ℝ) ^ (k - 2 * (n : ℤ)) = (-1 : ℝ) ^ k := by
        rw [zpow_sub₀ (by norm_num : (-1 : ℝ) ≠ 0)]
        rw [show (2 * (n : ℤ)) = (2 : ℤ) * n by ring, zpow_mul]
        norm_num
      have hden : 2 * ((k - 2 * (n : ℤ) : ℤ) : ℝ) + 1 = j - 4 * (n : ℝ) := by
        rw [hj]; push_cast; ring
      rw [hsign, hden]
      push_cast
      ring
    have hreal : (2 / Real.pi * (-1 : ℝ) ^ k / j)
        - (harmonicLN N)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
            ((n : ℕ) : ℝ)⁻¹ * ((2 / Real.pi) * (-1 : ℝ) ^ k * (1 / (j - 4 * (n : ℝ))))
        = (2 / Real.pi) * (-1 : ℝ) ^ k * B := by
      rw [hB]
      rw [show ∑ n ∈ Finset.Icc 1 N,
            ((n : ℕ) : ℝ)⁻¹ * ((2 / Real.pi) * (-1 : ℝ) ^ k * (1 / (j - 4 * (n : ℝ))))
          = ((2 / Real.pi) * (-1 : ℝ) ^ k)
              * ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ)⁻¹ * (1 / (j - 4 * (n : ℝ))) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by ring]
      ring
    rw [Finset.sum_congr rfl hterm, ← hj, ← hreal]
    push_cast
    ring
  -- the cancellation identity
  have hLB : harmonicLN N * B
      = ∑ n ∈ Finset.Icc 1 N, (-4) * (1 / (j * (j - 4 * (n : ℝ)))) := by
    rw [hB, mul_sub, mul_inv_cancel_left₀ (ne_of_gt hL0)]
    rw [harmonicLN, Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : ((n : ℕ) : ℝ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      positivity
    have hjn := hjn_ne n hn
    have hjn2 : j - (n : ℝ) * 4 ≠ 0 := fun h => hjn (by linarith)
    field_simp
    ring
  have hBval : B = (harmonicLN N)⁻¹
      * ∑ n ∈ Finset.Icc 1 N, (-4) * (1 / (j * (j - 4 * (n : ℝ)))) := by
    rw [← hLB, inv_mul_cancel_left₀ (ne_of_gt hL0)]
  -- the termwise bound
  have hjpos : (0 : ℝ) < |j| := abs_pos.mpr hjne
  have hterm_bound : ∀ n ∈ Finset.Icc 1 N,
      |(-4 : ℝ) * (1 / (j * (j - 4 * (n : ℝ))))| ≤ 8 / j ^ 2 := by
    intro n hn
    have hhalf := hjn_half n hn
    have hup : (0 : ℝ) < |j - 4 * (n : ℝ)| := lt_of_lt_of_le (by positivity) hhalf
    have h1 : |(-4 : ℝ) * (1 / (j * (j - 4 * (n : ℝ))))|
        = 4 / (|j| * |j - 4 * (n : ℝ)|) := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), one_div,
        abs_inv, abs_mul, ← one_div, mul_one_div]
    rw [h1]
    calc 4 / (|j| * |j - 4 * (n : ℝ)|) ≤ 4 / (|j| * (|j| / 2)) := by
          gcongr
      _ = 8 / j ^ 2 := by
          rw [← sq_abs j]
          field_simp
          ring
  -- assemble: `|B| ≤ 8N/j²`
  have habsB : |B| ≤ 8 * (N : ℝ) / j ^ 2 := by
    rw [hBval, abs_mul, abs_inv, abs_of_pos hL0]
    have hsum : |∑ n ∈ Finset.Icc 1 N, (-4 : ℝ) * (1 / (j * (j - 4 * (n : ℝ))))|
        ≤ ∑ _n ∈ Finset.Icc 1 N, (8 / j ^ 2) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm_bound)
    rw [Finset.sum_const, Nat.card_Icc] at hsum
    have hcard : (N + 1 - 1 : ℕ) • (8 / j ^ 2 : ℝ) = (N : ℝ) * (8 / j ^ 2) := by
      rw [Nat.add_sub_cancel, nsmul_eq_mul]
    rw [hcard] at hsum
    have hinv : (harmonicLN N)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1
    calc (harmonicLN N)⁻¹ * |∑ n ∈ Finset.Icc 1 N, (-4 : ℝ) * (1 / (j * (j - 4 * (n : ℝ))))|
        ≤ 1 * ((N : ℝ) * (8 / j ^ 2)) := by
          apply mul_le_mul hinv hsum (abs_nonneg _) zero_le_one
      _ = 8 * (N : ℝ) / j ^ 2 := by ring
  -- conclude
  rw [hvalue, Complex.norm_real, Real.norm_eq_abs]
  have hfactor : |(2 / Real.pi) * (-1 : ℝ) ^ k * B| = (2 / Real.pi) * |B| := by
    rw [abs_mul, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, mul_one,
      abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
  rw [hfactor]
  have hpi2 : (2 / Real.pi) ≤ 1 := by
    rw [div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  calc (2 / Real.pi) * |B| ≤ 1 * |B| :=
        mul_le_mul_of_nonneg_right hpi2 (abs_nonneg B)
    _ = |B| := one_mul _
    _ ≤ 8 * (N : ℝ) / j ^ 2 := habsB

/-- The global tail bound: past the head `24N < |m|`, every coefficient of `ς·u_N` is
at most `72N/m²` (zero off the class, the cancellation bound on it). -/
lemma sigmaMul_uApprox_coeff_bound (N : ℕ) (hN : 1 ≤ N) {m : ℤ}
    (hm : 24 * (N : ℤ) < |m|) :
    ‖circleFourierCoeff (sigmaMul (toL2Half (uApprox N))) m‖
      ≤ 72 * (N : ℝ) / (m : ℝ) ^ 2 := by
  have hm0 : (m : ℝ) ≠ 0 := by
    have : m ≠ 0 := by
      intro h0
      rw [h0] at hm
      simp at hm
      omega
    exact_mod_cast this
  by_cases hcl : ∃ k : ℤ, m = 6 * k + 3
  · obtain ⟨k, rfl⟩ := hcl
    have habs : |(6 * k + 3 : ℤ)| = 3 * |2 * k + 1| := by
      rw [show (6 * k + 3 : ℤ) = 3 * (2 * k + 1) by ring, abs_mul]
      norm_num
    have hk : 8 * (N : ℤ) < |2 * k + 1| := by
      rw [habs] at hm
      omega
    have hb := sigmaMul_uApprox_coeff_class_bound N hN k hk
    have heq : 72 * (N : ℝ) / ((6 * k + 3 : ℤ) : ℝ) ^ 2
        = 8 * (N : ℝ) / (2 * (k : ℝ) + 1) ^ 2 := by
      have h9 : ((6 * k + 3 : ℤ) : ℝ) ^ 2 = 9 * (2 * (k : ℝ) + 1) ^ 2 := by
        push_cast
        ring
      rw [h9]
      have hne : (2 * (k : ℝ) + 1) ^ 2 ≠ 0 := by
        have : ((2 * k + 1 : ℤ) : ℝ) ≠ 0 := by
          exact_mod_cast (by omega : (2 * k + 1 : ℤ) ≠ 0)
        push_cast at this ⊢
        intro hc
        exact this (by nlinarith [sq_nonneg (2 * (k : ℝ) + 1)])
      field_simp
      ring
    rw [heq]
    exact hb
  · rw [sigmaMul_uApprox_coeff_eq_zero_of_not_class N hcl, norm_zero]
    positivity

/-- For `N ≥ 1`, the approximators lie in the domain: `ς·u_N ∈ H^{1/2}`. -/
theorem memDomSigma_uApprox (N : ℕ) (hN : 1 ≤ N) : MemDomSigma (uApprox N) := by
  rw [MemDomSigma, mem_range_toL2_iff]
  rw [show (2 * (1 / 2 : ℝ)) = 1 by norm_num]
  simp only [Real.rpow_one]
  set S : Finset ℤ := Finset.Icc (-(24 * (N : ℤ))) (24 * (N : ℤ)) with hS
  rw [← S.summable_compl_iff]
  -- the dominating function `2(72N)²/|m|³`
  have hdom : Summable (fun m : ℤ => 2 * (72 * (N : ℝ)) ^ 2 * (1 / |(m : ℝ)| ^ 3)) := by
    apply Summable.mul_left
    apply Summable.of_nat_of_neg_add_one
    · have h3 := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      apply h3.congr
      intro n
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
    · have h3 := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)
      have h3' : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) := by
        rw [← summable_nat_add_iff 1] at h3
        apply h3.congr
        intro n
        push_cast
        ring_nf
      apply h3'.congr
      intro n
      congr 1
      push_cast
      rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) n] : (-((n : ℝ) + 1) : ℝ) ≤ 0)]
      ring_nf
  refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
    (hdom.comp_injective Subtype.val_injective)
  obtain ⟨m, hmS⟩ := x
  have hm : 24 * (N : ℤ) < |m| := by
    rw [hS, Finset.mem_Icc, not_and_or, not_le, not_le] at hmS
    rcases hmS with h | h
    · rw [abs_of_neg (by omega : m < 0)]
      omega
    · rw [abs_of_pos (by omega : 0 < m)]
      omega
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]
    have : (1 : ℤ) ≤ |m| := by omega
    exact_mod_cast this
  have hb := sigmaMul_uApprox_coeff_bound N hN hm
  have hmcast : 24 * (N : ℝ) < |(m : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hm
  -- (1+|m|)·‖c‖² ≤ (1+|m|)·(72N/m²)² ≤ 2|m|·(72N)²/|m|⁴ = 2(72N)²/|m|³
  have hsq : ‖circleFourierCoeff (sigmaMul (toL2Half (uApprox N))) m‖ ^ 2
      ≤ (72 * (N : ℝ) / (m : ℝ) ^ 2) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have habs4 : ((m : ℝ) ^ 2) ^ 2 = |(m : ℝ)| ^ 4 := by
    calc ((m : ℝ) ^ 2) ^ 2 = (m : ℝ) ^ 4 := by ring
      _ = |(m : ℝ) ^ 4| := (abs_of_nonneg (by positivity)).symm
      _ = |(m : ℝ)| ^ 4 := abs_pow _ _
  calc (1 + |(m : ℝ)|)
        * ‖circleFourierCoeff (sigmaMul (toL2Half (uApprox N))) m‖ ^ 2
      ≤ (1 + |(m : ℝ)|) * (72 * (N : ℝ) / (m : ℝ) ^ 2) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hsq
        positivity
    _ = (1 + |(m : ℝ)|) * ((72 * (N : ℝ)) ^ 2 / |(m : ℝ)| ^ 4) := by
        rw [div_pow, habs4]
    _ ≤ 2 * |(m : ℝ)| * ((72 * (N : ℝ)) ^ 2 / |(m : ℝ)| ^ 4) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 2 * (72 * (N : ℝ)) ^ 2 * (1 / |(m : ℝ)| ^ 3) := by
        have hne : |(m : ℝ)| ≠ 0 := by positivity
        field_simp

/-! ## Convergence of the approximators to the constant -/

lemma coeff_sub_uApprox (N : ℕ) (d : ℤ) :
    coeff (1 / 2) (modeHalf 0 - uApprox N) d
      = ((harmonicLN N : ℝ) : ℂ)⁻¹
          * ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℂ)⁻¹ * (Pi.single (12 * (n : ℤ)) 1 : ℤ → ℂ) d := by
  rw [coeff_sub, coeff_uApprox, coeff_modeHalf]
  ring

lemma harmonicLN_eq_sum_range (N : ℕ) :
    harmonicLN N = ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) := by
  induction N with
  | zero => simp [harmonicLN]
  | succ n ih =>
    rw [harmonicLN, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    rw [show ∑ m ∈ Finset.Icc 1 n, ((m : ℕ) : ℝ)⁻¹ = harmonicLN n from rfl, ih,
      Finset.sum_range_succ]
    push_cast
    ring

/-- The squared `H^{1/2}` distance of the approximator to the constant is at most
`13/L_N` for `N ≥ 1`. -/
theorem norm_sq_sub_uApprox_le (N : ℕ) (hN : 1 ≤ N) :
    ‖modeHalf 0 - uApprox N‖ ^ 2 ≤ 13 / harmonicLN N := by
  classical
  set v := modeHalf 0 - uApprox N with hv
  have hL1 : (1 : ℝ) ≤ harmonicLN N := one_le_harmonicLN hN
  have hL0 : (0 : ℝ) < harmonicLN N := harmonicLN_pos hN
  set T := (Finset.Icc 1 N).image (fun n : ℕ => 12 * (n : ℤ)) with hT
  -- the weighted square function, supported on T
  set f := fun d : ℤ => weight (1 / 2) d ^ 2 * ‖coeff (1 / 2) v d‖ ^ 2 with hf
  have hinj12 : ∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.Icc 1 N,
      12 * (a : ℤ) = 12 * (b : ℤ) → a = b := by
    intro a _ b _ hab
    omega
  have hoffT : ∀ d : ℤ, d ∉ T → f d = 0 := by
    intro d hd
    have hc : coeff (1 / 2) v d = 0 := by
      rw [coeff_sub_uApprox]
      have : ∀ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℂ)⁻¹ * (Pi.single (12 * (n : ℤ)) 1 : ℤ → ℂ) d
          = 0 := by
        intro n hn
        have hdn : d ≠ 12 * (n : ℤ) := by
          intro hdd
          exact hd (Finset.mem_image.mpr ⟨n, hn, hdd.symm⟩)
        simp [hdn]
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero, mul_zero]
    simp [hf, hc]
  have hfin : HasSum f (∑ d ∈ T, f d) := hasSum_sum_of_ne_finset_zero hoffT
  have hnorm : ‖v‖ ^ 2 = ∑ d ∈ T, f d :=
    (hasSum_weighted_sq (1 / 2) v).unique hfin
  -- evaluate the finite sum over the image
  have himg : ∑ d ∈ T, f d = ∑ n ∈ Finset.Icc 1 N, f (12 * (n : ℤ)) := by
    rw [hT, Finset.sum_image hinj12]
  -- the coefficient at `12 n₀`
  have hcoeff12 : ∀ n₀ ∈ Finset.Icc 1 N,
      coeff (1 / 2) v (12 * (n₀ : ℤ))
        = ((harmonicLN N : ℝ) : ℂ)⁻¹ * ((n₀ : ℕ) : ℂ)⁻¹ := by
    intro n₀ hn₀
    rw [coeff_sub_uApprox]
    congr 1
    rw [Finset.sum_eq_single n₀]
    · simp
    · intro b hb hbn
      have : (12 * ((n₀ : ℕ) : ℤ)) ≠ 12 * (b : ℤ) := by
        intro hc
        exact hbn (by omega : b = n₀)
      simp [this]
    · intro hn
      exact absurd hn₀ hn
  -- the term value and bound
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      f (12 * (n : ℤ)) ≤ (13 / harmonicLN N ^ 2) * (n : ℝ)⁻¹ := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn1)
    rw [hf]
    dsimp only
    rw [hcoeff12 n hn]
    have hw : weight (1 / 2) (12 * (n : ℤ)) ^ 2 = 1 + 12 * (n : ℝ) := by
      rw [weight_sq, show (2 * (1 / 2 : ℝ)) = 1 by norm_num, Real.rpow_one]
      push_cast
      rw [abs_of_nonneg (by positivity)]
    have hnn : ‖((harmonicLN N : ℝ) : ℂ)⁻¹ * ((n : ℕ) : ℂ)⁻¹‖ ^ 2
        = ((harmonicLN N)⁻¹ * ((n : ℝ))⁻¹) ^ 2 := by
      rw [norm_mul, norm_inv, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hL0]
      norm_num
    rw [hw, hnn]
    have hbound : (1 + 12 * (n : ℝ)) ≤ 13 * (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith
    calc (1 + 12 * (n : ℝ)) * ((harmonicLN N)⁻¹ * ((n : ℝ))⁻¹) ^ 2
        ≤ 13 * (n : ℝ) * ((harmonicLN N)⁻¹ * ((n : ℝ))⁻¹) ^ 2 := by
          apply mul_le_mul_of_nonneg_right hbound
          positivity
      _ = (13 / harmonicLN N ^ 2) * (n : ℝ)⁻¹ := by
          field_simp
  -- sum the bound
  have hsum : ∑ n ∈ Finset.Icc 1 N, f (12 * (n : ℤ))
      ≤ (13 / harmonicLN N ^ 2) * harmonicLN N := by
    calc ∑ n ∈ Finset.Icc 1 N, f (12 * (n : ℤ))
        ≤ ∑ n ∈ Finset.Icc 1 N, (13 / harmonicLN N ^ 2) * (n : ℝ)⁻¹ :=
          Finset.sum_le_sum hterm
      _ = (13 / harmonicLN N ^ 2) * harmonicLN N := by
          rw [← Finset.mul_sum, harmonicLN]
  have hfinal : (13 / harmonicLN N ^ 2) * harmonicLN N = 13 / harmonicLN N := by
    field_simp
  rw [hnorm, himg]
  rw [hfinal] at hsum
  exact hsum

/-- The approximators converge to the constant in `H^{1/2}`. -/
theorem uApprox_tendsto :
    Filter.Tendsto uApprox Filter.atTop (nhds (modeHalf 0)) := by
  have hLtend : Filter.Tendsto harmonicLN Filter.atTop Filter.atTop := by
    have := Real.tendsto_sum_range_one_div_nat_succ_atTop
    apply this.congr
    intro N
    exact (harmonicLN_eq_sum_range N).symm
  have h13 : Filter.Tendsto (fun N => 13 / harmonicLN N) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hLtend.inv_tendsto_atTop.const_mul (13 : ℝ)
  have hsq : Filter.Tendsto (fun N => ‖modeHalf 0 - uApprox N‖ ^ 2)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun N => by positivity)
      (Filter.eventually_atTop.mpr ⟨1, fun N hN => norm_sq_sub_uApprox_le N hN⟩) h13
  have hnrm : Filter.Tendsto (fun N => ‖modeHalf 0 - uApprox N‖)
      Filter.atTop (nhds 0) := by
    have hcont := (Real.continuous_sqrt.tendsto' 0 0 Real.sqrt_zero).comp hsq
    apply hcont.congr
    intro N
    exact Real.sqrt_sq (norm_nonneg _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply hnrm.congr
  intro N
  exact norm_sub_rev _ _

/-! ## Nonclosedness -/

/-- The first assertion of the paper's `sgnmul_norm` note: `H^{1/2}_ς(S¹)`
is not a closed subspace of `H^{1/2}(S¹)`.  Witness: the approximators `uApprox N`
(for `N ≥ 1`) lie in the domain and converge to the constant `1`,
which does not. -/
theorem memDomSigma_not_closed : ¬ IsClosed {u : Space (1 / 2 : ℝ) | MemDomSigma u} := by
  intro hcl
  have hmem : modeHalf 0 ∈ {u : Space (1 / 2 : ℝ) | MemDomSigma u} := by
    refine hcl.mem_of_tendsto uApprox_tendsto ?_
    exact Filter.eventually_atTop.mpr ⟨1, fun N hN => memDomSigma_uApprox N hN⟩
  exact not_memDomSigma_one hmem

end KsIndex.CircleSobolev
