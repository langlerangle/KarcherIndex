module

/-
KsIndexLean — A direct trial-field proof that `γ(1) < 0`.

The witness `arcW n = c (2n)` uses the even Fourier coefficients of the
single-arc test field from `TestField`. On the `(+,2;3)` lattice these have
physical frequencies `6n+1`. The convolution identity proved in `ArcSigma`
gives `convS arcW m = c (2m+1)`, the complementary frequencies `6m+4`.

Weighted summability places this witness in `MemDom`. Rescaling the symbols
and splitting the integer sum into even and odd indices gives
`Qform 1 arcW = 3 * NformArc (1/3) c < 0`. Its nonzero head coefficient
allows normalization, hence `gam 1 < 0`.

This proves the statement of [ksindexi], `threshold_lower_bound`, by a direct
trial-field argument. The paper derives it from the `m=2` index theorem;
that route is formalized separately in `GammaOnePaperRoute`.
-/
public import KsIndexLean.CircleQ
public import KsIndexLean.SingleArc
public import KsIndexLean.ArcSigma

@[expose] public section


noncomputable section

namespace KsIndex.GammaOne

open KsIndex.CircleQ KsIndex.TestField KsIndex.SingleArc Real

/-! ### Convolution of the arc coefficients -/

/-- `ς` applied to the `(+)`-half of the arc field gives its `(−)`-half:
`∑' n, chat (m − n) · c (2n) = c (2m + 1)` — "the class-(2;3) lift of the single-arc test
function is supported where ς = +1".  Proved in `ArcSigma.lean` (square-wave partial
sums + dominated convergence; leaves in `SquareWave.lean`). -/
theorem convS_arc (m : ℤ) :
    convS (fun n : ℤ => (c (2 * n) : ℂ)) m = (c (2 * m + 1) : ℂ) :=
  KsIndex.ArcSigma.convS_arc m

/-! ### The single-arc form at `a = 1/3` is negative on `c` -/

lemma habs_ge_third (ℓ : ℤ) : (1 : ℝ) / 3 ≤ |(ℓ : ℝ) + 1 / 3| := by
  rcases le_or_gt 0 ℓ with h | h
  · have hn : (0 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]; linarith
  · have hle : ℓ ≤ -1 := by omega
    have hn : (ℓ : ℝ) ≤ -1 := by exact_mod_cast hle
    rw [abs_of_neg (by linarith)]; linarith

lemma habs_pos_third (ℓ : ℤ) : 0 < |(ℓ : ℝ) + 1 / 3| :=
  lt_of_lt_of_le (by norm_num) (habs_ge_third ℓ)

lemma summable_c_sq_div_third : Summable (fun ℓ : ℤ => c ℓ ^ 2 / |(ℓ : ℝ) + 1 / 3|) := by
  have hdom : Summable (fun ℓ : ℤ => 9 * (|(ℓ : ℝ) + 1 / 3| * c ℓ ^ 2)) :=
    (summable_abs_mul_sq (show (1 / 3 : ℝ) ∈ Set.Ioo 0 1 by norm_num)).mul_left 9
  refine hdom.of_nonneg_of_le (fun ℓ => by positivity) fun ℓ => ?_
  have hpos := habs_pos_third ℓ
  have h9 : (1 : ℝ) ≤ 9 * |(ℓ : ℝ) + 1 / 3| ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (habs_ge_third ℓ))
      (by linarith [habs_ge_third ℓ] : (0 : ℝ) ≤ |(ℓ : ℝ) + 1 / 3| + 1 / 3)]
  rw [div_le_iff₀ hpos]
  nlinarith [h9, sq_nonneg (c ℓ), hpos]

lemma sigArc_third_mul (ℓ : ℤ) :
    sigArc (1 / 3) ℓ * c ℓ ^ 2
      = |(ℓ : ℝ) + 1 / 3| * c ℓ ^ 2 - 4 / 9 * (c ℓ ^ 2 / |(ℓ : ℝ) + 1 / 3|) := by
  have hpos := habs_pos_third ℓ
  rw [sigArc, ← sq_abs ((ℓ : ℝ) + 1 / 3)]
  field_simp

/-- The summand of `N_{(1/3;3)}(c)` is summable. -/
lemma summable_sigArc_third :
    Summable (fun ℓ : ℤ => sigArc (1 / 3) ℓ * c ℓ ^ 2) := by
  have h1 : Summable (fun ℓ : ℤ => |(ℓ : ℝ) + 1 / 3| * c ℓ ^ 2) :=
    summable_abs_mul_sq (by norm_num)
  refine (h1.sub (summable_c_sq_div_third.mul_left (4 / 9))).congr fun ℓ => ?_
  rw [sigArc_third_mul]

/-- Quantitative negative energy from the four modes `0, -1, 1, -2`:
`∑ c²/|ℓ+1/3| ≥ 387/640`, with all omitted terms nonnegative. -/
theorem NformArc_third_le_sharp : NformArc (1 / 3) c ≤ -(3 / 160 : ℝ) := by
  have ha : (1 / 3 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  have hsum1 : Summable (fun ℓ : ℤ => |(ℓ : ℝ) + 1 / 3| * c ℓ ^ 2) := summable_abs_mul_sq ha
  have hsum2 := summable_c_sq_div_third
  have hsplit : NformArc (1 / 3) c
      = 1 / 4 - 4 / 9 * ∑' ℓ : ℤ, c ℓ ^ 2 / |(ℓ : ℝ) + 1 / 3| := by
    have e : NformArc (1 / 3) c
        = (∑' ℓ : ℤ, |(ℓ : ℝ) + 1 / 3| * c ℓ ^ 2)
          - ∑' ℓ : ℤ, 4 / 9 * (c ℓ ^ 2 / |(ℓ : ℝ) + 1 / 3|) := by
      rw [NformArc, ← hsum1.tsum_sub (hsum2.mul_left (4 / 9))]
      exact tsum_congr fun ℓ => sigArc_third_mul ℓ
    rw [e, test_field ha, tsum_mul_left]
  have hlb : (387 : ℝ) / 640 ≤ ∑' ℓ : ℤ, c ℓ ^ 2 / |(ℓ : ℝ) + 1 / 3| := by
    have hle := hsum2.sum_le_tsum ({0, -1, 1, -2} : Finset ℤ) (fun ℓ _ => by positivity)
    have hcm1 : c (-1) ^ 2 = 1 / 8 := by
      rw [show (-1 : ℤ) = -0 - 1 by ring, c_reflect, c_zero_sq]
    have hcm2 : c (-2) ^ 2 = 1 / 32 := by
      rw [show (-2 : ℤ) = -1 - 1 by ring, c_reflect, c_one_sq]
    have hval : ∑ ℓ ∈ ({0, -1, 1, -2} : Finset ℤ), c ℓ ^ 2 / |(ℓ : ℝ) + 1 / 3| = 387 / 640 := by
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
        c_zero_sq, hcm1, c_one_sq, hcm2,
        show |((0 : ℤ) : ℝ) + 1 / 3| = 1 / 3 by norm_num,
        show |((-1 : ℤ) : ℝ) + 1 / 3| = 2 / 3 by norm_num,
        show |((1 : ℤ) : ℝ) + 1 / 3| = 4 / 3 by norm_num,
        show |((-2 : ℤ) : ℝ) + 1 / 3| = 5 / 3 by norm_num]
      norm_num
    rw [hval] at hle; exact hle
  rw [hsplit]; linarith [hlb]

/-- A coarser margin retained for existing consumers. -/
theorem NformArc_third_le : NformArc (1 / 3) c ≤ -(1 / 96 : ℝ) :=
  le_trans NformArc_third_le_sharp (by norm_num)

/-- The quantitative arc estimate is strictly negative. -/
theorem NformArc_third_neg : NformArc (1 / 3) c < 0 :=
  lt_of_le_of_lt NformArc_third_le (by norm_num)

/-! ### The witness `arcW` and its two halves -/

/-- The `(+)`-half of the arc test field on the `1+6ℤ` lattice: `arcW n = c(2n)`. -/
def arcW : ℤ → ℂ := fun n => (c (2 * n) : ℂ)

@[simp] lemma arcW_apply (n : ℤ) : arcW n = (c (2 * n) : ℂ) := rfl

/-- The convolution identity for the even-index witness. -/
lemma convS_arcW (m : ℤ) : convS arcW m = (c (2 * m + 1) : ℂ) := convS_arc m

lemma norm_ofReal_sq (x : ℝ) : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Injectivity of `n ↦ 2n` and `m ↦ 2m+1` on `ℤ`. -/
lemma two_mul_injective : Function.Injective (fun n : ℤ => 2 * n) := fun a b h => by
  simp only at h; omega

lemma two_mul_add_one_injective : Function.Injective (fun m : ℤ => 2 * m + 1) := fun a b h => by
  simp only at h; omega

/-- `|6n+1| c(2n)²` is summable (even-index subsequence of `3|ℓ+1/3| c(ℓ)²`). -/
lemma summable_even_weight :
    Summable (fun n : ℤ => |6 * (n : ℝ) + 1| * c (2 * n) ^ 2) := by
  have h := ((summable_abs_mul_sq (show (1 / 3 : ℝ) ∈ Set.Ioo 0 1 by norm_num)).mul_left 3)
    |>.comp_injective two_mul_injective
  refine h.congr fun n => ?_
  simp only [Function.comp]
  push_cast
  rw [show (6 * (n : ℝ) + 1) = 3 * (2 * (n : ℝ) + 1 / 3) by ring, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  ring

/-- `|6m+4| c(2m+1)²` is summable (odd-index subsequence of `3|ℓ+1/3| c(ℓ)²`). -/
lemma summable_odd_weight :
    Summable (fun m : ℤ => |6 * (m : ℝ) + 4| * c (2 * m + 1) ^ 2) := by
  have h := ((summable_abs_mul_sq (show (1 / 3 : ℝ) ∈ Set.Ioo 0 1 by norm_num)).mul_left 3)
    |>.comp_injective two_mul_add_one_injective
  refine h.congr fun m => ?_
  simp only [Function.comp]
  push_cast
  rw [show (6 * (m : ℝ) + 4) = 3 * (2 * (m : ℝ) + 1 + 1 / 3) by ring, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  ring

/-- Weighted summability of both coefficient halves places `arcW` in the domain. -/
theorem memDom_arcW : MemDom arcW := by
  refine ⟨summable_even_weight.congr fun n => ?_, summable_odd_weight.congr fun m => ?_⟩
  · rw [arcW_apply, norm_ofReal_sq]
  · rw [convS_arcW m, norm_ofReal_sq]

/-! ### `𝒬₁(arcW) = 3·N_{(1/3;3)}(c)` -/

/-- The sector symbol on the `(+)` lattice is `3×` the single-arc symbol at even index. -/
lemma sigP_eq_three_sigArc (n : ℤ) : sigP n = 3 * sigArc (1 / 3) (2 * n) := by
  have hpos : (0 : ℝ) < |2 * (n : ℝ) + 1 / 3| := by
    have := habs_pos_third (2 * n); push_cast at this; exact this
  rw [sigP, sigArc]
  push_cast
  rw [show (6 * (n : ℝ) + 1) = 3 * (2 * (n : ℝ) + 1 / 3) by ring, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  field_simp
  ring

/-- The sector symbol on the `(−)` lattice is `3×` the single-arc symbol at odd index. -/
lemma sigM_eq_three_sigArc (m : ℤ) : sigM m = 3 * sigArc (1 / 3) (2 * m + 1) := by
  have hpos : (0 : ℝ) < |2 * (m : ℝ) + 1 + 1 / 3| := by
    have := habs_pos_third (2 * m + 1); push_cast at this; exact this
  rw [sigM, sigArc]
  push_cast
  rw [show (6 * (m : ℝ) + 4) = 3 * (2 * (m : ℝ) + 1 + 1 / 3) by ring, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  field_simp
  ring

/-- `ℤ ≃ {even integers}`, `n ↦ 2n`. -/
def evenEquiv : ℤ ≃ ↥({ℓ : ℤ | Even ℓ} : Set ℤ) :=
  Equiv.ofBijective (fun n => ⟨2 * n, even_two_mul n⟩)
    ⟨fun a b h => by
        have := congrArg Subtype.val h
        simp only at this; omega,
     fun ⟨x, hx⟩ => by
        obtain ⟨r, hr⟩ := (hx : Even x)
        exact ⟨r, Subtype.ext (show 2 * r = x by rw [hr, two_mul])⟩⟩

/-- `ℤ ≃ {odd integers}` (the complement), `m ↦ 2m+1`. -/
def oddEquiv : ℤ ≃ ↥(({ℓ : ℤ | Even ℓ} : Set ℤ)ᶜ) :=
  Equiv.ofBijective (fun m => ⟨2 * m + 1, fun h => by
      have ho : Odd (2 * m + 1) := odd_two_mul_add_one m
      exact (Int.not_even_iff_odd.mpr ho) h⟩)
    ⟨fun a b h => by
        have := congrArg Subtype.val h
        simp only at this; omega,
     fun ⟨x, hx⟩ => by
        have ho : Odd x := Int.not_even_iff_odd.mp hx
        obtain ⟨r, hr⟩ := ho
        exact ⟨r, Subtype.ext hr.symm⟩⟩

/-- Even/odd split of a summable `ℤ`-series. -/
lemma tsum_int_even_add_odd {F : ℤ → ℝ} (hF : Summable F) :
    ∑' ℓ : ℤ, F ℓ = (∑' n : ℤ, F (2 * n)) + ∑' m : ℤ, F (2 * m + 1) := by
  rw [← hF.tsum_subtype_add_tsum_subtype_compl ({ℓ : ℤ | Even ℓ} : Set ℤ)]
  congr 1
  · exact (evenEquiv.tsum_eq (fun x : ↥({ℓ : ℤ | Even ℓ} : Set ℤ) => F x)).symm
  · exact (oddEquiv.tsum_eq (fun x : ↥(({ℓ : ℤ | Even ℓ} : Set ℤ)ᶜ) => F x)).symm

/-- The circle energy of `arcW` is three times its single-arc energy. -/
theorem Qform_one_arcW : Qform 1 arcW = 3 * NformArc (1 / 3) c := by
  have hF := summable_sigArc_third
  have hsplit := tsum_int_even_add_odd hF
  have h1 : (∑' n : ℤ, sigP n * ‖arcW n‖ ^ 2)
      = 3 * ∑' n : ℤ, sigArc (1 / 3) (2 * n) * c (2 * n) ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by
      rw [arcW_apply, norm_ofReal_sq, sigP_eq_three_sigArc]; ring
  have h2 : (∑' m : ℤ, sigM m * ‖convS arcW m‖ ^ 2)
      = 3 * ∑' m : ℤ, sigArc (1 / 3) (2 * m + 1) * c (2 * m + 1) ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr fun m => by
      rw [convS_arcW m, norm_ofReal_sq, sigM_eq_three_sigArc]; ring
  rw [Qform, h1, h2, NformArc, hsplit]
  ring

/-! ### Normalization and the conclusion -/

lemma convS_smul' (t : ℂ) (u : ℤ → ℂ) (m : ℤ) : convS (t • u) m = t * convS u m := by
  unfold convS
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma memDom_smul' (t : ℂ) {u : ℤ → ℂ} (hu : MemDom u) : MemDom (t • u) := by
  refine ⟨(hu.1.mul_left (‖t‖ ^ 2)).congr fun n => ?_,
    (hu.2.mul_left (‖t‖ ^ 2)).congr fun m => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]; ring
  · rw [convS_smul', norm_mul, mul_pow]; ring

lemma normSq_smul' (t : ℂ) (u : ℤ → ℂ) : normSq (t • u) = ‖t‖ ^ 2 * normSq u := by
  unfold normSq
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

lemma Qform_smul' (s : ℝ) (t : ℂ) (u : ℤ → ℂ) : Qform s (t • u) = ‖t‖ ^ 2 * Qform s u := by
  unfold Qform
  have h1 : (∑' n : ℤ, sigP n * ‖(t • u) n‖ ^ 2) = ‖t‖ ^ 2 * ∑' n : ℤ, sigP n * ‖u n‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]; ring
  have h2 : (∑' m : ℤ, sigM m * ‖convS (t • u) m‖ ^ 2)
      = ‖t‖ ^ 2 * ∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr fun m => by rw [convS_smul', norm_mul, mul_pow]; ring
  rw [h1, h2]; ring

/-- `γ(s) ≤ 𝒬_s(u)/‖u‖²` for any nonzero domain vector (normalize and use `gam_le`). -/
theorem gam_le_div {s : ℝ} {u : ℤ → ℂ} (hu : MemDom u) (hpos : 0 < normSq u) :
    gam s ≤ Qform s u / normSq u := by
  set t : ℂ := (((Real.sqrt (normSq u))⁻¹ : ℝ) : ℂ) with ht
  have hsq : ‖t‖ ^ 2 = (normSq u)⁻¹ := by
    rw [ht, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hpos.le]
  have hn1 : normSq (t • u) = 1 := by
    rw [normSq_smul', hsq, inv_mul_cancel₀ (ne_of_gt hpos)]
  have h := gam_le (s := s) (memDom_smul' t hu) hn1
  rw [Qform_smul', hsq] at h
  rw [div_eq_inv_mul]
  exact h

/-- `‖arcW‖² > 0` (the head coefficient `c 0 ≠ 0`). -/
lemma normSq_arcW_pos : 0 < normSq arcW := by
  have hsum : Summable (fun n : ℤ => ‖arcW n‖ ^ 2) := summable_normSq memDom_arcW.1
  have h0 : ‖arcW 0‖ ^ 2 = 1 / 8 := by
    rw [show arcW 0 = (c 0 : ℂ) by rfl, norm_ofReal_sq, c_zero_sq]
  have hle : ‖arcW 0‖ ^ 2 ≤ ∑' n : ℤ, ‖arcW n‖ ^ 2 :=
    hsum.le_tsum 0 (fun j _ => sq_nonneg _)
  unfold normSq
  linarith

/-- **`γ(1) < 0`, directly** ([ksindexi] `\ref{threshold_lower_bound}`): the arc
test field is a `𝒬₁`-negative domain vector, using the proved
convolution identity `convS_arc`. -/
theorem gam_one_neg_direct : gam 1 < 0 := by
  have h := gam_le_div (s := 1) memDom_arcW normSq_arcW_pos
  have hneg : Qform 1 arcW < 0 := by
    rw [Qform_one_arcW]; linarith [NformArc_third_neg]
  exact lt_of_le_of_lt h (div_neg_of_neg_of_pos hneg normSq_arcW_pos)

end KsIndex.GammaOne

namespace KsIndex.CircleQ

/-- The lower-threshold statement `γ(1) < 0`, obtained from the negative arc
trial field. `GammaOnePaperRoute.gam_one_neg_paper` supplies the paper's
alternative derivation from the `m=2` index theorem. -/
theorem gam_one_neg : gam 1 < 0 := KsIndex.GammaOne.gam_one_neg_direct

end KsIndex.CircleQ
