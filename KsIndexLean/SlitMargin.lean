module

/-
Angular separation between the rescaled arc field and a slit-cut region.

For `η > 0`, a nonzero value `fInf k r η φ` implies `η ≤ cos(kφ)`.
At a point satisfying `1−2δ ≤ ‖w‖²`, `‖w‖ ≤ 1` and `Re(w^k) ≤ 2c`,
with `c ≥ 0` and `1−2δ > 0`, the lemma `cos_k_arg_le` gives
`cos(k arg w) ≤ A := 2c/(1−2δ)^k`.

If `k ≥ 1` and `A < η`, `fInf_margin` combines these inequalities to give

  `cos(arg w − φ) ≤ cos((η−A)/k)`

whenever `fInf k r η φ ≠ 0`. The positive margin `(η−A)/k` depends only on the
parameters, not on the chosen point or angle. The argument uses the Lipschitz
bound for cosine against integer-period translates and then reduces to a
principal angular representative; no inverse cosine is needed.

This is the geometric margin input for a Poisson estimate. It does not itself
bound a Poisson integral or its derivatives. The field condition in the theorem
is pointwise nonvanishing, not membership in the closure of its support.
-/
public import KsIndexLean.ModePoissonBridge
public import KsIndexLean.ArcInfCoeff

@[expose] public section


noncomputable section

open Real Set Complex
open KsIndex.ArcField KsIndex.ArcInfCoeff KsIndex.ModePoissonBridge

namespace KsIndex.SlitMargin

variable {k r : ℕ}

/-- **The circle-separation lemma**: if `cos(kα) ≤ A < B ≤ cos(kφ)`, then `α − φ` keeps
circle-distance `≥ (B−A)/k` from `2πℤ`, so `cos(α − φ) ≤ cos((B−A)/k)`. -/
theorem cos_margin (hk : 1 ≤ k) {A B : ℝ} (hAB : A < B) {α φ : ℝ}
    (hα : Real.cos ((k : ℝ) * α) ≤ A) (hφ : B ≤ Real.cos ((k : ℝ) * φ)) :
    Real.cos (α - φ) ≤ Real.cos ((B - A) / (k : ℝ)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  -- every `2πℤ`-translate of `k(α−φ)` is at distance ≥ B − A (Lipschitz against `cos`)
  have hsep : ∀ j : ℤ, B - A ≤ |(k : ℝ) * (α - φ) - 2 * π * j| := by
    intro j
    have hL := Real.abs_cos_sub_cos_le ((k : ℝ) * α) ((k : ℝ) * φ + 2 * π * j)
    have hcos : Real.cos ((k : ℝ) * φ + 2 * π * j) = Real.cos ((k : ℝ) * φ) := by
      rw [show (k : ℝ) * φ + 2 * π * j = (k : ℝ) * φ + (j : ℤ) * (2 * π) by push_cast; ring,
        Real.cos_add_int_mul_two_pi]
    rw [hcos] at hL
    calc B - A ≤ Real.cos ((k : ℝ) * φ) - Real.cos ((k : ℝ) * α) := by linarith
      _ ≤ |Real.cos ((k : ℝ) * α) - Real.cos ((k : ℝ) * φ)| := by
          rw [abs_sub_comm]; exact le_abs_self _
      _ ≤ |(k : ℝ) * α - ((k : ℝ) * φ + 2 * π * j)| := hL
      _ = |(k : ℝ) * (α - φ) - 2 * π * j| := by congr 1; ring
  -- the separation divides: `α − φ` at distance ≥ (B−A)/k from `2πℤ`
  have hsep' : ∀ j : ℤ, (B - A) / (k : ℝ) ≤ |(α - φ) - 2 * π * j| := by
    intro j
    have h := hsep ((k : ℤ) * j)
    have heq : |(k : ℝ) * (α - φ) - 2 * π * (((k : ℤ) * j : ℤ) : ℝ)|
        = (k : ℝ) * |(α - φ) - 2 * π * j| := by
      rw [show (k : ℝ) * (α - φ) - 2 * π * (((k : ℤ) * j : ℤ) : ℝ)
          = (k : ℝ) * ((α - φ) - 2 * π * j) from by push_cast; ring,
        abs_mul, abs_of_pos hkpos]
    rw [heq] at h
    rw [div_le_iff₀ hkpos]
    linarith
  -- reduce to the principal representative in `(−π, π]`
  have hsub := toIocMod_sub_self Real.two_pi_pos (-π) (α - φ)
  rw [zsmul_eq_mul] at hsub
  set θ' := toIocMod Real.two_pi_pos (-π) (α - φ) with hθ'
  set jd : ℤ := toIocDiv Real.two_pi_pos (-π) (α - φ) with hjd
  have hmem : θ' ∈ Set.Ioc (-π) π := by
    have h := toIocMod_mem_Ioc Real.two_pi_pos (-π) (α - φ)
    rw [show -π + 2 * π = π by ring] at h
    exact h
  have hrep : θ' = (α - φ) - 2 * π * (jd : ℝ) := by
    push_cast at hsub
    linear_combination hsub
  have hcos_eq : Real.cos (α - φ) = Real.cos θ' := by
    rw [hrep, show (α - φ) - 2 * π * (jd : ℝ) = (α - φ) + ((-jd : ℤ) : ℝ) * (2 * π) by
      push_cast; ring, Real.cos_add_int_mul_two_pi]
  have habs : (B - A) / (k : ℝ) ≤ |θ'| := by
    rw [hrep]
    exact hsep' jd
  have habs_le : |θ'| ≤ π := by
    rw [abs_le]
    exact ⟨hmem.1.le, hmem.2⟩
  have hd0 : 0 ≤ (B - A) / (k : ℝ) := div_nonneg (by linarith) hkpos.le
  calc Real.cos (α - φ) = Real.cos θ' := hcos_eq
    _ = Real.cos |θ'| := (Real.cos_abs θ').symm
    _ ≤ Real.cos ((B - A) / (k : ℝ)) :=
        Real.cos_le_cos_of_nonneg_of_le_pi hd0 habs_le habs

/-- On the slit-cut region, `cos(k·arg w) ≤ 2c/(1−2δ)^k` — integer powers only, via
`Re(w^k) = ‖w‖^k·cos(k·arg w)` and `‖w‖^k ≥ (‖w‖²)^k ≥ (1−2δ)^k`. -/
lemma cos_k_arg_le (hk : 1 ≤ k) {c δ : ℝ} (hc : 0 ≤ c) (hδpos : 0 < 1 - 2 * δ)
    {w : ℂ} (hwlow : 1 - 2 * δ ≤ ‖w‖ ^ 2) (hw1 : ‖w‖ ≤ 1) (hwk : (w ^ k).re ≤ 2 * c) :
    Real.cos ((k : ℝ) * Complex.arg w) ≤ 2 * c / (1 - 2 * δ) ^ k := by
  have hw0 : 0 < ‖w‖ := by nlinarith [norm_nonneg w]
  -- `Re(w^k) = ‖w‖^k·cos(k·arg w)`
  have hre : (w ^ k).re = ‖w‖ ^ k * Real.cos ((k : ℝ) * Complex.arg w) := by
    rw [pow_polar w k, show ((k : ℕ) : ℂ) * ↑(Complex.arg w) * Complex.I
        = ↑((k : ℝ) * Complex.arg w) * Complex.I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hpow_pos : (0 : ℝ) < (1 - 2 * δ) ^ k := by positivity
  have hple : (1 - 2 * δ) ^ k ≤ ‖w‖ ^ k := by
    refine pow_le_pow_left₀ hδpos.le ?_ k
    nlinarith [norm_nonneg w]
  rw [le_div_iff₀ hpow_pos]
  rcases le_or_gt (Real.cos ((k : ℝ) * Complex.arg w)) 0 with hneg | hpos
  · calc Real.cos ((k : ℝ) * Complex.arg w) * (1 - 2 * δ) ^ k
        ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hpow_pos.le
      _ ≤ 2 * c := by linarith
  · have h1 : Real.cos ((k : ℝ) * Complex.arg w) * (1 - 2 * δ) ^ k
        ≤ Real.cos ((k : ℝ) * Complex.arg w) * ‖w‖ ^ k :=
      mul_le_mul_of_nonneg_left hple hpos.le
    have h2 : Real.cos ((k : ℝ) * Complex.arg w) * ‖w‖ ^ k ≤ 2 * c := by
      rw [mul_comm, ← hre]
      exact hwk
    linarith

/-- For `η > 0`, a nonzero value of `fInf` forces `η ≤ cos(kφ)`. -/
lemma fInf_supp_cos {η : ℝ} (hη0 : 0 < η) {φ : ℝ}
    (hφ : fInf k r η φ ≠ 0) : η ≤ Real.cos ((k : ℝ) * φ) := by
  by_contra hcon
  rw [not_le] at hcon
  apply hφ
  unfold fInf
  rw [psiF_eq_zero hη0 hcon.le, mul_zero]

/-- For `w` on the slit-cut region and `fInf k r η φ ≠ 0`,
`cos(arg w − φ) ≤ cos d` with the parameter-dependent margin
`d = (η − 2c/(1−2δ)^k)/k > 0` (positivity from `hA`).  Feeds `norm_poissonExt_le`. -/
theorem fInf_margin (hk : 1 ≤ k) {η c δ : ℝ} (hη0 : 0 < η) (hc : 0 ≤ c)
    (hδpos : 0 < 1 - 2 * δ) (hA : 2 * c / (1 - 2 * δ) ^ k < η)
    {w : ℂ} (hwlow : 1 - 2 * δ ≤ ‖w‖ ^ 2) (hw1 : ‖w‖ ≤ 1) (hwk : (w ^ k).re ≤ 2 * c)
    {φ : ℝ} (hφ : fInf k r η φ ≠ 0) :
    Real.cos (Complex.arg w - φ)
      ≤ Real.cos ((η - 2 * c / (1 - 2 * δ) ^ k) / (k : ℝ)) :=
  cos_margin hk hA (cos_k_arg_le hk hc hδpos hwlow hw1 hwk) (fInf_supp_cos hη0 hφ)

end KsIndex.SlitMargin
