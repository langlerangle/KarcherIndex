module

public import KsIndexLean.NodeCCoeff
public import KsIndexLean.NodeCSymbol
public import KsIndexLean.NodeCSigmaInf
public import KsIndexLean.NodeCQLowerArith
public import KsIndexLean.NodeCTail

@[expose] public section


/-!
# A Fourier lower bound for the mixed-boundary quadratic form

For `u ∈ dnSpace 1`, coefficient duality gives
`û(0) − û(−1) = Σ conj(Ψ̂(ℓ)) · û(ℓ)`. The trial coefficients at `0` and `-1`
vanish, so only the other modes contribute. The trial function belongs to
`L²`, hence defines an `H^{-1/2}` dual element; the unnormalized circle pairing
has the factor `2π`.

A weighted Cauchy–Schwarz estimate bounds the squared head difference by the
product of the trial's reciprocal-symbol tail and the positive-symbol energy.
Both summability assumptions are explicit in `dn_head_diff_sq_le`.
For the middle classes `a = censusA j k`, with `k ≥ 4`, `2 ≤ j` and `j + 2 ≤ k`,
the tail estimate gives the strict lower bound `nodeC_Q_lower` when the head
coefficients differ. Its energy sum excludes the two indices `0` and `-1`.

-/

noncomputable section
open MeasureTheory Complex Filter Topology
namespace KsIndex.NodeC
open KsIndex.Trace KsIndex.Parseval KsIndex.CircleSobolev KsIndex.WeakH1


/-- `Ψ̂` agrees with the Fourier coefficient of its `L²` realization. -/
lemma trialPsi_coeff_eq_Lp (n : ℤ) :
    circleFourierCoeff trialPsi n = circleFourierCoeff (trialPsiLp : Circle₁ → ℂ) n :=
  (congrFun (circleFourierCoeff_congr_ae trialPsi_memLp.coeFn_toLp) n).symm

/-- `Ψ ∈ L²` gives `ℓ²`-summable Fourier coefficients (Bessel). -/
lemma trialPsi_coeff_sq_summable :
    Summable (fun n : ℤ => ‖circleFourierCoeff trialPsi n‖ ^ 2) := by
  have h := (hasSum_weighted_sq (0 : ℝ) (circleFourierCLE trialPsiLp)).summable
  refine h.congr (fun n => ?_)
  rw [coeff_zero_order, circleFourierCLE_apply, ← trialPsi_coeff_eq_Lp,
    show weight (0 : ℝ) n = 1 from by rw [weight, Real.rpow_zero]]
  ring

/-- The `H^{-1/2}` summability of `Ψ̂` — free from `L²` since `weight(−1/2) ≤ 1`. -/
lemma psiDualFull_summable :
    Summable (fun n : ℤ => weight (-(1 / 2) : ℝ) n ^ 2 * ‖circleFourierCoeff trialPsi n‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    trialPsi_coeff_sq_summable
  have hw : weight (-(1 / 2) : ℝ) n ^ 2 ≤ 1 := by
    have h1 : weight (-(1 / 2) : ℝ) n ≤ 1 := by
      have := weight_mono (show (-(1 / 2) : ℝ) ≤ 0 by norm_num) n
      rwa [show weight (0 : ℝ) n = 1 from by rw [weight, Real.rpow_zero]] at this
    nlinarith [(weight_pos (-(1 / 2) : ℝ) n).le, h1]
  exact mul_le_of_le_one_left (by positivity) hw

/-- The full trial function as an `H^{-1/2}` dual element (coefficients `= Ψ̂`). -/
def psiDualFull : Space (-(1 / 2) : ℝ) :=
  ofCoefficients (-(1 / 2)) (fun n => circleFourierCoeff trialPsi n) psiDualFull_summable

@[simp] lemma psiDualFull_coeff (n : ℤ) :
    coeff (-(1 / 2) : ℝ) psiDualFull n = circleFourierCoeff trialPsi n :=
  coeff_ofCoefficients _ _ _ n

/-- **Plancherel form of the pairing**: `⟨Ψ, u⟩ = 2π·Σ conj(Ψ̂(ℓ))·û(ℓ)`. -/
lemma trialPsi_pairing_tsum (u : Space (1 / 2 : ℝ)) :
    inner ℂ trialPsiLp (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u)
      = (2 * Real.pi : ℂ)
        * ∑' n : ℤ, (starRingEnd ℂ) (circleFourierCoeff trialPsi n) * coeff (1 / 2) u n := by
  have hdual : duality (1 / 2) psiDualFull u = inner ℂ trialPsiLp (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u) := by
    refine duality_eq_inner_of_coefficients (1 / 2) psiDualFull u trialPsiLp (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u)
      (fun n => ?_) (fun n => (fourierCoeff_toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) u n).symm)
    rw [psiDualFull_coeff, trialPsi_coeff_eq_Lp]
  rw [← hdual, duality_eq_tsum]
  congr 1
  exact tsum_congr (fun n => by rw [psiDualFull_coeff])

/-- **The pairing as a Fourier sum** (paper §5): `û(0) − û(−1) = Σ conj(Ψ̂(ℓ))·û(ℓ)`. -/
lemma dn_coeff_diff_eq_tsum (u : Space (1 / 2 : ℝ)) (hu : u ∈ dnSpace 1) :
    coeff (1 / 2) u 0 - coeff (1 / 2) u (-1)
      = ∑' n : ℤ, (starRingEnd ℂ) (circleFourierCoeff trialPsi n) * coeff (1 / 2) u n := by
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact mul_left_cancel₀ h2pi ((trialPsi_pairing u hu).symm.trans (trialPsi_pairing_tsum u))

/-! ### Weighted Cauchy–Schwarz -/

/-- General `ℓ²` Cauchy–Schwarz utility (self-contained; cf. `SIsometry`). -/
private lemma summable_mul_of_sq {p q : ℤ → ℝ} (hp : Summable fun n => p n ^ 2)
    (hq : Summable fun n => q n ^ 2) : Summable fun n => p n * q n := by
  refine ((hp.add hq).mul_left (1 / 2)).of_norm_bounded ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|p n| - |q n|), sq_abs (p n), sq_abs (q n)]

private theorem tsum_mul_sq_le {p q : ℤ → ℝ} (hp : Summable fun n => p n ^ 2)
    (hq : Summable fun n => q n ^ 2) :
    (∑' n : ℤ, p n * q n) ^ 2 ≤ (∑' n : ℤ, p n ^ 2) * ∑' n : ℤ, q n ^ 2 := by
  have hpq := summable_mul_of_sq hp hq
  have hfin : ∀ G : Finset ℤ,
      (∑ n ∈ G, p n * q n) ^ 2 ≤ (∑' n : ℤ, p n ^ 2) * ∑' n : ℤ, q n ^ 2 := by
    intro G
    calc (∑ n ∈ G, p n * q n) ^ 2
        ≤ (∑ n ∈ G, p n ^ 2) * ∑ n ∈ G, q n ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq G p q
      _ ≤ (∑' n : ℤ, p n ^ 2) * ∑' n : ℤ, q n ^ 2 :=
          mul_le_mul (hp.sum_le_tsum G fun _ _ => sq_nonneg _)
            (hq.sum_le_tsum G fun _ _ => sq_nonneg _)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _) (tsum_nonneg fun _ => sq_nonneg _)
  have htend : Tendsto (fun G : Finset ℤ => (∑ n ∈ G, p n * q n) ^ 2) atTop
      (𝓝 ((∑' n : ℤ, p n * q n) ^ 2)) := (hpq.hasSum).pow 2
  exact le_of_tendsto htend (Eventually.of_forall hfin)

/-- `|ℓ + a| > 1` off the two resonant modes (`a ∈ (0,1)`). -/
lemma abs_add_gt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ℓ : ℤ} (h0 : ℓ ≠ 0) (h1 : ℓ ≠ -1) :
    1 < |(ℓ : ℝ) + a| := by
  rcases (by omega : 1 ≤ ℓ ∨ ℓ ≤ -2) with h | h
  · have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]; linarith
  · have : (ℓ : ℝ) ≤ -2 := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]; linarith

/-- The symbol is positive off the two resonant modes. -/
lemma sigma_pos_of_ne {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ℓ : ℤ}
    (h0 : ℓ ≠ 0) (h1 : ℓ ≠ -1) : 0 < sigma k a ℓ := by
  have hg := abs_add_gt_one ha0 ha1 h0 h1
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hinv : (0 : ℝ) < 1 / (k : ℝ) := by positivity
  have hk1 : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hkR]; exact_mod_cast hk
  exact sigma_pos (by linarith) (by linarith) (by linarith)

/-- **Weighted Cauchy–Schwarz.** With reciprocal-symbol tail summability
`hpsum` and positive-`σ` energy summability `hqsum`,
`|û(0) − û(−1)|² ≤ (Σ |Ψ̂|²/σ)·(Σ_{ℓ≠0,−1} σ|û|²)`. -/
lemma dn_head_diff_sq_le {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {u : Space (1 / 2 : ℝ)} (hu : u ∈ dnSpace 1)
    (hpsum : Summable (fun ℓ : ℤ => ‖circleFourierCoeff trialPsi ℓ‖ ^ 2 / sigma k a ℓ))
    (hqsum : Summable (fun ℓ : ℤ =>
      if ℓ = 0 ∨ ℓ = -1 then 0 else sigma k a ℓ * ‖coeff (1 / 2 : ℝ) u ℓ‖ ^ 2)) :
    ‖coeff (1 / 2 : ℝ) u 0 - coeff (1 / 2 : ℝ) u (-1)‖ ^ 2
      ≤ (∑' ℓ : ℤ, ‖circleFourierCoeff trialPsi ℓ‖ ^ 2 / sigma k a ℓ)
        * ∑' ℓ : ℤ,
          (if ℓ = 0 ∨ ℓ = -1 then 0 else sigma k a ℓ * ‖coeff (1 / 2 : ℝ) u ℓ‖ ^ 2) := by
  set p : ℤ → ℝ := fun ℓ =>
    if ℓ = 0 ∨ ℓ = -1 then 0 else ‖circleFourierCoeff trialPsi ℓ‖ / Real.sqrt (sigma k a ℓ) with hp
  set q : ℤ → ℝ := fun ℓ =>
    if ℓ = 0 ∨ ℓ = -1 then 0 else Real.sqrt (sigma k a ℓ) * ‖coeff (1 / 2 : ℝ) u ℓ‖ with hq
  have hσpos : ∀ ℓ : ℤ, ¬ (ℓ = 0 ∨ ℓ = -1) → 0 < sigma k a ℓ := fun ℓ h =>
    sigma_pos_of_ne hk ha0 ha1 (fun e => h (Or.inl e)) (fun e => h (Or.inr e))
  have hpq : ∀ ℓ, p ℓ * q ℓ = ‖circleFourierCoeff trialPsi ℓ‖ * ‖coeff (1 / 2 : ℝ) u ℓ‖ := by
    intro ℓ; simp only [hp, hq]; split_ifs with h
    · rcases h with rfl | rfl
      · rw [trialPsi_coeff_zero]; simp
      · rw [trialPsi_coeff_neg_one]; simp
    · have hsq : Real.sqrt (sigma k a ℓ) ≠ 0 := (Real.sqrt_pos.mpr (hσpos ℓ h)).ne'
      field_simp
  have hp2 : ∀ ℓ, p ℓ ^ 2 = ‖circleFourierCoeff trialPsi ℓ‖ ^ 2 / sigma k a ℓ := by
    intro ℓ; simp only [hp]; split_ifs with h
    · rcases h with rfl | rfl
      · rw [trialPsi_coeff_zero]; simp
      · rw [trialPsi_coeff_neg_one]; simp
    · rw [div_pow, Real.sq_sqrt (hσpos ℓ h).le]
  have hq2 : ∀ ℓ, q ℓ ^ 2 =
      if ℓ = 0 ∨ ℓ = -1 then 0 else sigma k a ℓ * ‖coeff (1 / 2 : ℝ) u ℓ‖ ^ 2 := by
    intro ℓ; simp only [hq]; split_ifs with h
    · simp
    · rw [mul_pow, Real.sq_sqrt (hσpos ℓ h).le]
  have hpsum' : Summable (fun ℓ => p ℓ ^ 2) := hpsum.congr (fun ℓ => (hp2 ℓ).symm)
  have hqsum' : Summable (fun ℓ => q ℓ ^ 2) := hqsum.congr (fun ℓ => (hq2 ℓ).symm)
  have hnorm : Summable (fun ℓ : ℤ =>
      ‖(starRingEnd ℂ) (circleFourierCoeff trialPsi ℓ) * coeff (1 / 2 : ℝ) u ℓ‖) := by
    refine (summable_mul_of_sq hpsum' hqsum').congr fun ℓ => ?_
    rw [hpq, norm_mul, starRingEnd_apply, norm_star]
  have h1 : ‖coeff (1 / 2 : ℝ) u 0 - coeff (1 / 2 : ℝ) u (-1)‖ ≤ ∑' ℓ : ℤ, p ℓ * q ℓ := by
    rw [dn_coeff_diff_eq_tsum u hu]
    refine le_trans (norm_tsum_le_tsum_norm hnorm) (le_of_eq (tsum_congr fun ℓ => ?_))
    rw [hpq, norm_mul, starRingEnd_apply, norm_star]
  calc ‖coeff (1 / 2 : ℝ) u 0 - coeff (1 / 2 : ℝ) u (-1)‖ ^ 2
      ≤ (∑' ℓ : ℤ, p ℓ * q ℓ) ^ 2 := by
        nlinarith [h1, norm_nonneg (coeff (1 / 2 : ℝ) u 0 - coeff (1 / 2 : ℝ) u (-1))]
    _ ≤ (∑' ℓ : ℤ, p ℓ ^ 2) * ∑' ℓ : ℤ, q ℓ ^ 2 := tsum_mul_sq_le hpsum' hqsum'
    _ = _ := by rw [tsum_congr hp2, tsum_congr hq2]

/-! ### The `Q`-lower lemma (paper §5, Lemma `Q-lower`) -/

/-- **`nodeC_Q_lower`.**  For a middle class `a = censusA j k` and DN data `u` with
`û(0) ≠ û(−1)`, the positive-`σ` energy `Q(u)/2π` exceeds
`|û(0)−û(−1)|²·|σ₀||σ₋₁|/(|σ₀|+|σ₋₁|)`.  Combines weighted Cauchy–Schwarz, the
trial-tail bound, `Hs_Rs_sufficient`, `Rs_eq_sigmaInf_recip`, and `σ_∞ < σ_k`. -/
lemma nodeC_Q_lower {k j : ℕ} (hk : 4 ≤ k) (hj2 : 2 ≤ j) (hjk : j + 2 ≤ k)
    {u : Space (1 / 2 : ℝ)} (hu : u ∈ dnSpace 1)
    (hne : coeff (1 / 2 : ℝ) u 0 ≠ coeff (1 / 2 : ℝ) u (-1))
    (hqsum : Summable (fun ℓ : ℤ =>
      if ℓ = 0 ∨ ℓ = -1 then 0
      else sigma k (censusA j k) ℓ * ‖coeff (1 / 2 : ℝ) u ℓ‖ ^ 2)) :
    ‖coeff (1 / 2 : ℝ) u 0 - coeff (1 / 2 : ℝ) u (-1)‖ ^ 2
        * (|sigma k (censusA j k) 0| * |sigma k (censusA j k) (-1)|
            / (|sigma k (censusA j k) 0| + |sigma k (censusA j k) (-1)|))
      < ∑' ℓ : ℤ, if ℓ = 0 ∨ ℓ = -1 then 0
          else sigma k (censusA j k) ℓ * ‖coeff (1 / 2 : ℝ) u ℓ‖ ^ 2 := by
  set a := censusA j k with ha
  have hk1 : 1 ≤ k := by omega
  have ha0 : 0 < a := censusA_pos hk hjk
  have ha1 : a < 1 := censusA_lt_one hk hj2
  have hσ0 : sigma k a 0 < 0 := sigma_census_zero hk hj2 hjk
  have hσ1 : sigma k a (-1) < 0 := sigma_census_negOne hk hj2 hjk
  set X := ‖coeff (1 / 2 : ℝ) u 0 - coeff (1 / 2 : ℝ) u (-1)‖ ^ 2 with hX
  set A := ∑' ℓ : ℤ, ‖circleFourierCoeff trialPsi ℓ‖ ^ 2 / sigma k a ℓ with hAdef
  set B := ∑' ℓ : ℤ, if ℓ = 0 ∨ ℓ = -1 then 0
      else sigma k a ℓ * ‖coeff (1 / 2 : ℝ) u ℓ‖ ^ 2 with hBdef
  have hCS : X ≤ A * B :=
    dn_head_diff_sq_le hk1 ha0 ha1 hu (trialPsi_tail_summable hk1 ha0 ha1) hqsum
  -- the tail `A` is below the reciprocal sum of the two resonant symbols
  have hs0 : 0 < a * (1 - a) := mul_pos ha0 (by linarith)
  have hs4 : a * (1 - a) ≤ 1 / 4 := by nlinarith [sq_nonneg (a - 1 / 2)]
  have hAle : A ≤ 4 * Hs (a * (1 - a)) / 25 + 32 / 75 := trialPsi_tail_bound hk1 ha0 ha1
  have hHR : 4 * Hs (a * (1 - a)) / 25 + 32 / 75 < Rs (a * (1 - a)) := by
    have := Hs_Rs_sufficient hs0 hs4; linarith
  have hRs : Rs (a * (1 - a)) = 1 / |sigmaInf a 0| + 1 / |sigmaInf a (-1)| :=
    Rs_eq_sigmaInf_recip ha0 ha1
  have hden0 : (0 : ℝ) < |((0 : ℤ) : ℝ) + a| := by
    rw [Int.cast_zero, zero_add]; exact abs_pos.mpr ha0.ne'
  have hden1 : (0 : ℝ) < |((-1 : ℤ) : ℝ) + a| := by
    rw [Int.cast_neg, Int.cast_one]
    exact abs_pos.mpr (ne_of_lt (by linarith : (-1 : ℝ) + a < 0))
  have hsi0 : sigmaInf a 0 < sigma k a 0 := sigmaInf_lt_sigma hk1 hden0
  have hsi1 : sigmaInf a (-1) < sigma k a (-1) := sigmaInf_lt_sigma hk1 hden1
  have hσ0pos : 0 < |sigma k a 0| := abs_pos.mpr hσ0.ne
  have hσ1pos : 0 < |sigma k a (-1)| := abs_pos.mpr hσ1.ne
  have habs0 : |sigma k a 0| < |sigmaInf a 0| := by
    rw [abs_of_neg hσ0, abs_of_neg (by linarith : sigmaInf a 0 < 0)]; linarith
  have habs1 : |sigma k a (-1)| < |sigmaInf a (-1)| := by
    rw [abs_of_neg hσ1, abs_of_neg (by linarith : sigmaInf a (-1) < 0)]; linarith
  have hAltrecip : A < 1 / |sigma k a 0| + 1 / |sigma k a (-1)| := by
    have hRlt : 1 / |sigmaInf a 0| + 1 / |sigmaInf a (-1)|
        < 1 / |sigma k a 0| + 1 / |sigma k a (-1)| :=
      add_lt_add (one_div_lt_one_div_of_lt hσ0pos habs0)
        (one_div_lt_one_div_of_lt hσ1pos habs1)
    rw [hRs] at hHR; linarith
  -- positivity of the head difference forces `A, B > 0`
  have hXpos : 0 < X := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) 2
  have hAnn : 0 ≤ A := by
    refine tsum_nonneg (fun ℓ => ?_)
    by_cases h : ℓ = 0 ∨ ℓ = -1
    · rcases h with rfl | rfl
      · rw [trialPsi_coeff_zero]; simp
      · rw [trialPsi_coeff_neg_one]; simp
    · rw [not_or] at h
      exact div_nonneg (sq_nonneg _) (sigma_pos_of_ne hk1 ha0 ha1 h.1 h.2).le
  have hprod : 0 < A * B := lt_of_lt_of_le hXpos hCS
  have hApos : 0 < A := by
    rcases hAnn.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hprod; exact absurd hprod (lt_irrefl 0)
  have hBpos : 0 < B := by
    by_contra hc
    rw [not_lt] at hc
    exact absurd hprod (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hApos.le hc))
  -- conclude
  have hrecip_pos : 0 < 1 / |sigma k a 0| + 1 / |sigma k a (-1)| :=
    add_pos (one_div_pos.mpr hσ0pos) (one_div_pos.mpr hσ1pos)
  have h0ne : |sigma k a 0| ≠ 0 := hσ0pos.ne'
  have h1ne : |sigma k a (-1)| ≠ 0 := hσ1pos.ne'
  have hsne : |sigma k a 0| + |sigma k a (-1)| ≠ 0 := (add_pos hσ0pos hσ1pos).ne'
  have hfac : |sigma k a 0| * |sigma k a (-1)| / (|sigma k a 0| + |sigma k a (-1)|)
      = 1 / (1 / |sigma k a 0| + 1 / |sigma k a (-1)|) := by
    rw [eq_div_iff hrecip_pos.ne']
    field_simp
    ring
  rw [hfac, mul_one_div, div_lt_iff₀ hrecip_pos]
  calc X ≤ A * B := hCS
    _ < (1 / |sigma k a 0| + 1 / |sigma k a (-1)|) * B :=
        mul_lt_mul_of_pos_right hAltrecip hBpos
    _ = B * (1 / |sigma k a 0| + 1 / |sigma k a (-1)|) := by ring

end KsIndex.NodeC
