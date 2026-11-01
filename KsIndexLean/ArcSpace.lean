module

/-
# Coefficient model of the single-arc half-order Sobolev space

`MemArc u` combines weighted square summability,
`Summable (fun ℓ => (1 + |ℓ|) * ‖u ℓ‖²)`, with the fixed-point condition
`convS₁ u = u`. The kernel `sgnHat` models multiplication by the square wave
`ς₁ = sgn cos θ`: it vanishes on even frequencies and has
`sgnHat (2j+1) = chat j = (2/π)(-1)^j/(2j+1)`.

In physical variables, the corresponding arc condition is vanishing almost
everywhere on `{cos θ < 0}`. Here the domain is defined in coefficients;
weighted summability and the convolution fixed-point equation are separate
requirements. `ArcDom` bundles this domain as a complex submodule, independent
of the sector parameter `k`.

The module proves the parity splitting of `convS₁`, the shifted involution
`convS (convS u) (m-1) = u m` for square-summable sequences, and two consequences
of the fixed-point equation at frequencies `0` and `-1`. It also proves
membership of the Catalan test sequence: the odd coordinates follow from
`ArcSigma.convS_arc`, and the even coordinates from the shifted involution.
-/
public import KsIndexLean.SIsometry
public import KsIndexLean.ArcSigma
public import KsIndexLean.GammaOne

@[expose] public section


noncomputable section

namespace KsIndex.ArcSpace

open KsIndex.CircleQ KsIndex.SIsometry KsIndex.TestField Real

/-! ### The kernel `ς̂₁` -/

/-- `ς̂₁(d)`: the Fourier coefficients of `ς₁ = sgn cos θ`; supported on odd
`d`, with `ς̂₁(2j+1) = chat j = (2/π)(−1)^j/(2j+1)`. -/
def sgnHat (d : ℤ) : ℝ := if Even d then 0 else chat ((d - 1) / 2)

lemma sgnHat_even {d : ℤ} (h : Even d) : sgnHat d = 0 := by
  simp [sgnHat, h]

lemma sgnHat_odd (j : ℤ) : sgnHat (2 * j + 1) = chat j := by
  have h : ¬ Even (2 * j + 1) := Int.not_even_iff_odd.mpr (odd_two_mul_add_one j)
  rw [sgnHat, if_neg h]
  congr 1
  omega

lemma sgnHat_two_mul (j : ℤ) : sgnHat (2 * j) = 0 := sgnHat_even (even_two_mul j)

/-- `ς̂₁` is even (`ς₁` is a real even function). -/
lemma sgnHat_neg (d : ℤ) : sgnHat (-d) = sgnHat d := by
  rcases Int.even_or_odd d with h | h
  · rw [sgnHat_even h, sgnHat_even h.neg]
  · obtain ⟨j, rfl⟩ := h
    rw [show -(2 * j + 1) = 2 * (-(j + 1)) + 1 by ring, sgnHat_odd, sgnHat_odd, chat_refl]
    congr 1
    ring

/-- `ς̂₁(d)² ≤ (4/π²)/d²` (with the Lean convention `1/0 = 0` at `d = 0`). -/
lemma sgnHat_sq_le (d : ℤ) : sgnHat d ^ 2 ≤ 4 / π ^ 2 * (1 / (d : ℝ) ^ 2) := by
  rcases Int.even_or_odd d with h | h
  · rw [sgnHat_even h, zero_pow two_ne_zero]
    positivity
  · obtain ⟨j, rfl⟩ := h
    rw [sgnHat_odd, chat_eq, oddInv]
    have hne : (2 * (j : ℝ) + 1) ≠ 0 := by
      intro h0
      have : (2 * j + 1 : ℤ) = 0 := by exact_mod_cast h0
      omega
    have h1 : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← sq_abs, abs_neg_one_zpow, one_pow]
    push_cast
    rw [mul_pow, mul_pow, h1]
    apply le_of_eq
    field_simp
    norm_num

lemma summable_sgnHat_sq : Summable fun d : ℤ => sgnHat d ^ 2 := by
  have h : Summable fun d : ℤ => 4 / π ^ 2 * (1 / (d : ℝ) ^ 2) :=
    ((Real.summable_one_div_int_pow).mpr (by norm_num : 1 < 2)).mul_left _
  exact h.of_nonneg_of_le (fun d => sq_nonneg _) sgnHat_sq_le

lemma summable_sgnHat_shift_sq (m : ℤ) : Summable fun n : ℤ => sgnHat (m - n) ^ 2 :=
  summable_sgnHat_sq.comp_injective (fun a b h => by omega)

/-! ### The convolution `ς₁·` and its even/odd splitting -/

/-- The kernel of `ς₁·` in `SIsometry.convK` format. -/
def S1ker (m n : ℤ) : ℝ := sgnHat (m - n)

/-- `(ς₁·u)(m) = ∑' n, ς̂₁(m−n) u n`. -/
def convS₁ (u : ℤ → ℂ) (m : ℤ) : ℂ := ∑' n : ℤ, (sgnHat (m - n) : ℂ) * u n

lemma convS₁_eq_convK (u : ℤ → ℂ) (m : ℤ) : convS₁ u m = convK S1ker u m := rfl

lemma summable_convS₁_term {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) (m : ℤ) :
    Summable fun n : ℤ => (sgnHat (m - n) : ℂ) * u n :=
  summable_convK_term (K := S1ker) (fun m => summable_sgnHat_shift_sq m) hu m

lemma convS₁_add {u v : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2)
    (hv : Summable fun n : ℤ => ‖v n‖ ^ 2) (m : ℤ) :
    convS₁ (u + v) m = convS₁ u m + convS₁ v m := by
  have h := (summable_convS₁_term hu m).tsum_add (summable_convS₁_term hv m)
  rw [convS₁, convS₁, convS₁, ← h]
  congr 1
  funext n
  simp only [Pi.add_apply]
  ring

lemma convS₁_smul (t : ℂ) (u : ℤ → ℂ) (m : ℤ) : convS₁ (t • u) m = t * convS₁ u m := by
  rw [convS₁, convS₁, ← tsum_mul_left]
  congr 1
  funext n
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma convS₁_zero (m : ℤ) : convS₁ (0 : ℤ → ℂ) m = 0 := by
  simp [convS₁]

/-- Even/odd split of a summable complex `ℤ`-series. -/
lemma tsum_int_even_add_odd' {F : ℤ → ℂ} (hF : Summable F) :
    ∑' ℓ : ℤ, F ℓ = (∑' n : ℤ, F (2 * n)) + ∑' m : ℤ, F (2 * m + 1) := by
  rw [← hF.tsum_subtype_add_tsum_subtype_compl ({ℓ : ℤ | Even ℓ} : Set ℤ)]
  congr 1
  · exact (KsIndex.GammaOne.evenEquiv.tsum_eq
      (fun x : ↥({ℓ : ℤ | Even ℓ} : Set ℤ) => F x)).symm
  · exact (KsIndex.GammaOne.oddEquiv.tsum_eq
      (fun x : ↥(({ℓ : ℤ | Even ℓ} : Set ℤ)ᶜ) => F x)).symm

/-- Odd output coordinates of `ς₁·u` are `convS` of the even input coordinates. -/
lemma convS₁_odd {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) (m : ℤ) :
    convS₁ u (2 * m + 1) = convS (fun n => u (2 * n)) m := by
  rw [convS₁, tsum_int_even_add_odd' (summable_convS₁_term hu _)]
  have h2 : (∑' n : ℤ, (sgnHat (2 * m + 1 - (2 * n + 1)) : ℂ) * u (2 * n + 1)) = 0 := by
    simp only [show ∀ n : ℤ, 2 * m + 1 - (2 * n + 1) = 2 * (m - n) from fun n => by ring,
      sgnHat_two_mul, Complex.ofReal_zero, zero_mul, tsum_zero]
  have h1 : (∑' n : ℤ, (sgnHat (2 * m + 1 - 2 * n) : ℂ) * u (2 * n))
      = ∑' n : ℤ, (chat (m - n) : ℂ) * u (2 * n) :=
    tsum_congr fun n => by
      rw [show 2 * m + 1 - 2 * n = 2 * (m - n) + 1 by ring, sgnHat_odd]
  rw [h1, h2, add_zero]
  rfl

/-- Even output coordinates of `ς₁·u` are `convS` of the odd input coordinates,
shifted by one. -/
lemma convS₁_even {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) (m : ℤ) :
    convS₁ u (2 * m) = convS (fun n => u (2 * n + 1)) (m - 1) := by
  rw [convS₁, tsum_int_even_add_odd' (summable_convS₁_term hu _)]
  have h1 : (∑' n : ℤ, (sgnHat (2 * m - 2 * n) : ℂ) * u (2 * n)) = 0 := by
    simp only [show ∀ n : ℤ, 2 * m - 2 * n = 2 * (m - n) from fun n => by ring,
      sgnHat_two_mul, Complex.ofReal_zero, zero_mul, tsum_zero]
  have h2 : (∑' n : ℤ, (sgnHat (2 * m - (2 * n + 1)) : ℂ) * u (2 * n + 1))
      = ∑' n : ℤ, (chat (m - 1 - n) : ℂ) * u (2 * n + 1) :=
    tsum_congr fun n => by
      rw [show 2 * m - (2 * n + 1) = 2 * (m - 1 - n) + 1 by ring, sgnHat_odd]
  rw [h1, h2, zero_add]
  rfl

/-! ### `ς₁² = 1` -/

/-- `ς² = 1` in coefficients, on `ℓ²`: `(S(Su))(m−1) = u m`
(`SIsometry.convK_TS_eq` plus the kernel reflection `chat_refl`). -/
theorem convS_convS {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) (m : ℤ) :
    convS (convS u) (m - 1) = u m := by
  have h := convK_TS_eq hu m
  rw [← h]
  unfold convS convK Tker Sker
  congr 1
  funext n
  rw [show m - 1 - n = -(n - m + 1) by ring, chat_refl, show n - m + 1 - 1 = n - m by ring]

/-! ### The domain -/

/-- Membership in (the coefficient model of) `H^{1/2}_{DN;1}(S¹)`: the
`H^{1/2}` weight condition and `ς₁·u = u`. -/
def MemArc (u : ℤ → ℂ) : Prop :=
  Summable (fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖u ℓ‖ ^ 2) ∧ ∀ m : ℤ, convS₁ u m = u m

lemma summable_sq_of_weight {u : ℤ → ℂ}
    (hu : Summable fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖u ℓ‖ ^ 2) :
    Summable fun ℓ : ℤ => ‖u ℓ‖ ^ 2 :=
  hu.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun ℓ => le_mul_of_one_le_left (sq_nonneg _) (by linarith [abs_nonneg (ℓ : ℝ)]))

lemma MemArc.summable_sq {u : ℤ → ℂ} (hu : MemArc u) : Summable fun ℓ : ℤ => ‖u ℓ‖ ^ 2 :=
  summable_sq_of_weight hu.1

lemma memArc_zero : MemArc (0 : ℤ → ℂ) :=
  ⟨summable_zero.congr fun n => by simp, fun m => by rw [convS₁_zero]; rfl⟩

lemma memArc_smul (t : ℂ) {u : ℤ → ℂ} (hu : MemArc u) : MemArc (t • u) := by
  refine ⟨(hu.1.mul_left (‖t‖ ^ 2)).congr fun n => ?_, fun m => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    ring
  · rw [convS₁_smul, hu.2 m]
    rfl

lemma memArc_add {u v : ℤ → ℂ} (hu : MemArc u) (hv : MemArc v) : MemArc (u + v) := by
  refine ⟨((hu.1.add hv.1).mul_left 2).of_nonneg_of_le (fun n => by positivity) fun n => ?_,
    fun m => ?_⟩
  · have h1 : ‖(u + v) n‖ ≤ ‖u n‖ + ‖v n‖ := by
      simp only [Pi.add_apply]
      exact norm_add_le _ _
    have hX : ‖(u + v) n‖ ^ 2 ≤ 2 * ‖u n‖ ^ 2 + 2 * ‖v n‖ ^ 2 := by
      nlinarith [norm_nonneg ((u + v) n), norm_nonneg (u n), norm_nonneg (v n),
        sq_nonneg (‖u n‖ - ‖v n‖)]
    have hw : (0 : ℝ) ≤ 1 + |(n : ℝ)| := by positivity
    calc (1 + |(n : ℝ)|) * ‖(u + v) n‖ ^ 2
        ≤ (1 + |(n : ℝ)|) * (2 * ‖u n‖ ^ 2 + 2 * ‖v n‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hX hw
      _ = 2 * ((1 + |(n : ℝ)|) * ‖u n‖ ^ 2 + (1 + |(n : ℝ)|) * ‖v n‖ ^ 2) := by ring
  · rw [convS₁_add hu.summable_sq hv.summable_sq, hu.2 m, hv.2 m]
    rfl

/-- The coefficient model of `H^{1/2}_{DN;1}(S¹)` as a complex subspace of the
sequence space. -/
def ArcDom : Submodule ℂ (ℤ → ℂ) where
  carrier := {u | MemArc u}
  zero_mem' := memArc_zero
  add_mem' := fun hu hv => memArc_add hu hv
  smul_mem' := fun t _ hu => memArc_smul t hu

@[simp] lemma mem_ArcDom {u : ℤ → ℂ} : u ∈ ArcDom ↔ MemArc u := Iff.rfl

/-! ### The two head identities -/

/-- `∑' n, ς̂₁(n) u n = u 0` for arc-supported `u` (`ς₁u = u` at `m = 0`). -/
theorem tsum_sgnHat_mul {u : ℤ → ℂ} (hu : MemArc u) :
    ∑' n : ℤ, (sgnHat n : ℂ) * u n = u 0 := by
  have h := hu.2 0
  rw [convS₁] at h
  rw [← h]
  exact tsum_congr fun n => by rw [zero_sub, sgnHat_neg]

/-- `∑' n, ς̂₁(n+1) u n = u (−1)` for arc-supported `u` (`ς₁u = u` at `m = −1`). -/
theorem tsum_sgnHat_succ_mul {u : ℤ → ℂ} (hu : MemArc u) :
    ∑' n : ℤ, (sgnHat (n + 1) : ℂ) * u n = u (-1) := by
  have h := hu.2 (-1)
  rw [convS₁] at h
  rw [← h]
  exact tsum_congr fun n => by
    rw [show (-1 : ℤ) - n = -(n + 1) by ring, sgnHat_neg]

/-! ### The Catalan test field is arc-supported -/

/-- The Catalan field as a complex sequence. -/
def cC : ℤ → ℂ := fun ℓ => (c ℓ : ℂ)

lemma cC_apply (ℓ : ℤ) : cC ℓ = (c ℓ : ℂ) := rfl

lemma summable_cC_even_sq : Summable fun n : ℤ => ‖cC (2 * n)‖ ^ 2 := by
  have h := ((summable_abs_mul_sq (show (1 / 3 : ℝ) ∈ Set.Ioo 0 1 by norm_num)).mul_left 3)
    |>.comp_injective KsIndex.GammaOne.two_mul_injective
  refine h.of_nonneg_of_le (fun n => sq_nonneg _) fun n => ?_
  simp only [Function.comp, cC_apply, KsIndex.GammaOne.norm_ofReal_sq]
  have := ArcSigma.habs_ge_third (2 * n)
  push_cast at this ⊢
  nlinarith [sq_nonneg (c (2 * n)), abs_nonneg (2 * (n : ℝ) + 1 / 3)]

/-- `(1+|ℓ|) c(ℓ)²` is summable (`1+|ℓ| ≤ 4|ℓ+1/2|`). -/
lemma summable_cC_weight : Summable fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖cC ℓ‖ ^ 2 := by
  have h := (summable_abs_mul_sq (show (1 / 2 : ℝ) ∈ Set.Ioo 0 1 by norm_num)).mul_left 4
  refine h.of_nonneg_of_le (fun ℓ => by positivity) fun ℓ => ?_
  rw [cC_apply, KsIndex.GammaOne.norm_ofReal_sq]
  have hle : 1 + |(ℓ : ℝ)| ≤ 4 * |(ℓ : ℝ) + 1 / 2| := by
    rcases le_or_gt 0 ℓ with h0 | h0
    · have : (0 : ℝ) ≤ ℓ := by exact_mod_cast h0
      rw [abs_of_nonneg this, abs_of_pos (by linarith)]
      linarith
    · have : (ℓ : ℝ) ≤ -1 := by exact_mod_cast (show ℓ ≤ -1 by omega)
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
      linarith
  nlinarith [sq_nonneg (c ℓ)]

/-- Odd coordinates of `cC` are `convS` of the even ones: (B2). -/
lemma cC_odd_eq_convS : (fun n : ℤ => cC (2 * n + 1)) = convS (fun n : ℤ => cC (2 * n)) := by
  funext m
  rw [cC_apply, ← ArcSigma.convS_arc m]
  rfl

/-- **The Catalan test field is arc-supported**: `c ∈ H^{1/2}_{DN;1}` in
coefficients (the membership claim of the paper's lemma `test-field`).
Odd coordinates of `ς₁c = c` are (B2); even ones follow from `ς₁² = 1`. -/
theorem cC_mem_ArcDom : cC ∈ ArcDom := by
  refine ⟨summable_cC_weight, fun m => ?_⟩
  have hsq : Summable fun ℓ : ℤ => ‖cC ℓ‖ ^ 2 := summable_sq_of_weight summable_cC_weight
  rcases Int.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [← two_mul, convS₁_even hsq, cC_odd_eq_convS, convS_convS summable_cC_even_sq]
  · rw [convS₁_odd hsq, ← cC_odd_eq_convS]

end KsIndex.ArcSpace
