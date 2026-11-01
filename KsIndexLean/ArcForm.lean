module

/-
# The single-arc Fourier multiplier form

The paper's `nop-ak` symbol is
`σ(ℓ) = ((ℓ+a)² − b²)/|ℓ+a|`, with `0 < a < 1` and `b = 1 − 1/k`.
Here `sigmaArc a b` keeps both real parameters independent. `ArcMain`
specializes them to `a = 1 − j/k` and `b = 1 − 1/k`.

`NQformArc` is the real quadratic form and `NBformArc` its complex
sesquilinear pairing, conjugate-linear in the first argument. For `0 < a < 1`,
weighted square summability with weight `1 + |ℓ|` gives convergence of both
series. On the coefficient domain `ArcDom`, `indArc` and `nulArc` are the
suprema of the complex dimensions of finite-dimensional negative and radical
subspaces, respectively, with values in `ℕ∞`.

The form splits into its two coordinates at `0` and `−1` and the remaining
tail. When `|b| < 1`, the tail symbol is positive since `|ℓ+a| ≥ 1` away from
those coordinates. Thus a nonzero weighted-square-summable sequence vanishing
at both coordinates has positive form value; arc support is not needed for
this positivity statement.
-/
public import KsIndexLean.ArcSpace
public import KsIndexLean.FormIndex

@[expose] public section


noncomputable section

namespace KsIndex.ArcForm

open KsIndex.ArcSpace KsIndex.FormIndex Real

/-! ### The symbol -/

/-- The symbol with independent real parameters `a` and `b`; the paper
specialization uses `b = 1 − 1/k`. -/
def sigmaArc (a b : ℝ) (ℓ : ℤ) : ℝ := (((ℓ : ℝ) + a) ^ 2 - b ^ 2) / |(ℓ : ℝ) + a|

/-- `|ℓ + a| ≥ min(a, 1−a)` for `a ∈ (0,1)`. -/
lemma abs_add_ge (ha : a ∈ Set.Ioo (0 : ℝ) 1) (ℓ : ℤ) :
    min a (1 - a) ≤ |(ℓ : ℝ) + a| := by
  obtain ⟨ha0, ha1⟩ := ha
  rcases le_or_gt 0 ℓ with h | h
  · have : (0 : ℝ) ≤ ℓ := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    exact le_trans (min_le_left _ _) (by linarith)
  · have : (ℓ : ℝ) ≤ -1 := by exact_mod_cast (show ℓ ≤ -1 by omega)
    rw [abs_of_neg (by linarith)]
    exact le_trans (min_le_right _ _) (by linarith)

lemma abs_add_pos (ha : a ∈ Set.Ioo (0 : ℝ) 1) (ℓ : ℤ) : 0 < |(ℓ : ℝ) + a| :=
  lt_of_lt_of_le (lt_min ha.1 (by linarith [ha.2])) (abs_add_ge ha ℓ)

/-- `|ℓ + a| ≤ 1 + |ℓ|` for `a ∈ (0,1)`. -/
lemma abs_add_le (ha : a ∈ Set.Ioo (0 : ℝ) 1) (ℓ : ℤ) : |(ℓ : ℝ) + a| ≤ 1 + |(ℓ : ℝ)| := by
  calc |(ℓ : ℝ) + a| ≤ |(ℓ : ℝ)| + |a| := _root_.abs_add_le _ _
    _ ≤ 1 + |(ℓ : ℝ)| := by rw [abs_of_pos ha.1]; linarith [ha.2]

/-- `σ = |ℓ+a| − b²/|ℓ+a|`. -/
lemma sigmaArc_eq (ha : a ∈ Set.Ioo (0 : ℝ) 1) (b : ℝ) (ℓ : ℤ) :
    sigmaArc a b ℓ = |(ℓ : ℝ) + a| - b ^ 2 / |(ℓ : ℝ) + a| := by
  have hpos := abs_add_pos ha ℓ
  rw [sigmaArc, ← sq_abs ((ℓ : ℝ) + a)]
  field_simp

/-- The symbol is `O(1+|ℓ|)`: `|σ| ≤ (1 + b²/min(a,1−a))·(1+|ℓ|)`. -/
lemma abs_sigmaArc_le (ha : a ∈ Set.Ioo (0 : ℝ) 1) (b : ℝ) (ℓ : ℤ) :
    |sigmaArc a b ℓ| ≤ (1 + b ^ 2 / min a (1 - a)) * (1 + |(ℓ : ℝ)|) := by
  have hm : 0 < min a (1 - a) := lt_min ha.1 (by linarith [ha.2])
  have hge := abs_add_ge ha ℓ
  have hpos := abs_add_pos ha ℓ
  have hle := abs_add_le ha ℓ
  rw [sigmaArc_eq ha]
  have h1 : b ^ 2 / |(ℓ : ℝ) + a| ≤ b ^ 2 / min a (1 - a) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hm hge
  have h0 : 0 ≤ b ^ 2 / |(ℓ : ℝ) + a| := by positivity
  have h2 : 0 ≤ b ^ 2 / min a (1 - a) := by positivity
  have h3 : 1 ≤ 1 + |(ℓ : ℝ)| := by linarith [abs_nonneg (ℓ : ℝ)]
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- Off the heads `{0, −1}` the symbol is positive when `|b| < 1`. -/
lemma sigmaArc_pos (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1) {ℓ : ℤ}
    (h0 : ℓ ≠ 0) (h1 : ℓ ≠ -1) : 0 < sigmaArc a b ℓ := by
  have hpos := abs_add_pos ha ℓ
  have hge : 1 ≤ |(ℓ : ℝ) + a| := by
    rcases le_or_gt 0 ℓ with h | h
    · have : (1 : ℝ) ≤ ℓ := by exact_mod_cast (show 1 ≤ ℓ by omega)
      rw [abs_of_pos (by linarith [ha.1])]; linarith [ha.1]
    · have : (ℓ : ℝ) ≤ -2 := by exact_mod_cast (show ℓ ≤ -2 by omega)
      rw [abs_of_neg (by linarith [ha.2])]; linarith [ha.2]
  rw [sigmaArc]
  apply div_pos _ hpos
  have : b ^ 2 < 1 := by nlinarith [abs_nonneg b, sq_abs b]
  nlinarith [sq_abs ((ℓ : ℝ) + a)]

/-! ### The forms -/

/-- The quadratic form `N_{(a;k)}(u,u) = ∑ σ|u(ℓ)|²`. -/
def NQformArc (a b : ℝ) (u : ℤ → ℂ) : ℝ := ∑' ℓ : ℤ, sigmaArc a b ℓ * ‖u ℓ‖ ^ 2

/-- The sesquilinear form `N_{(a;k)}(u,v) = ∑ σ conj(u(ℓ)) v(ℓ)`. -/
def NBformArc (a b : ℝ) (u v : ℤ → ℂ) : ℂ :=
  ∑' ℓ : ℤ, (sigmaArc a b ℓ : ℂ) * ((starRingEnd ℂ) (u ℓ) * v ℓ)

/-- `ind_DN(N_{(a;k)})`. -/
def indArc (a b : ℝ) : ℕ∞ := formIndex (NQformArc a b) ArcDom

/-- `nul_DN(N_{(a;k)})`. -/
def nulArc (a b : ℝ) : ℕ∞ := formNullity (NBformArc a b) ArcDom

/-! ### Summability -/

lemma summable_sigmaArc_mul_sq (ha : a ∈ Set.Ioo (0 : ℝ) 1) (b : ℝ) {u : ℤ → ℂ}
    (hu : Summable fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖u ℓ‖ ^ 2) :
    Summable fun ℓ : ℤ => sigmaArc a b ℓ * ‖u ℓ‖ ^ 2 := by
  refine Summable.of_norm ((hu.mul_left (1 + b ^ 2 / min a (1 - a))).of_nonneg_of_le
    (fun ℓ => norm_nonneg _) fun ℓ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖u ℓ‖)]
  have := abs_sigmaArc_le ha b ℓ
  have h0 : 0 ≤ ‖u ℓ‖ ^ 2 := sq_nonneg _
  calc |sigmaArc a b ℓ| * ‖u ℓ‖ ^ 2
      ≤ (1 + b ^ 2 / min a (1 - a)) * (1 + |(ℓ : ℝ)|) * ‖u ℓ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right this h0
    _ = (1 + b ^ 2 / min a (1 - a)) * ((1 + |(ℓ : ℝ)|) * ‖u ℓ‖ ^ 2) := by ring

lemma summable_pair (ha : a ∈ Set.Ioo (0 : ℝ) 1) (b : ℝ) {u v : ℤ → ℂ}
    (hu : Summable fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖u ℓ‖ ^ 2)
    (hv : Summable fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖v ℓ‖ ^ 2) :
    Summable fun ℓ : ℤ => (sigmaArc a b ℓ : ℂ) * ((starRingEnd ℂ) (u ℓ) * v ℓ) := by
  refine Summable.of_norm ?_
  have hs := ((summable_sigmaArc_mul_sq ha b hu).abs.add
    (summable_sigmaArc_mul_sq ha b hv).abs).mul_left (1 / 2)
  refine hs.of_nonneg_of_le (fun ℓ => norm_nonneg _) fun ℓ => ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ‖u ℓ‖), abs_of_nonneg (sq_nonneg ‖v ℓ‖)]
  nlinarith [abs_nonneg (sigmaArc a b ℓ), sq_nonneg (‖u ℓ‖ - ‖v ℓ‖),
    norm_nonneg (u ℓ), norm_nonneg (v ℓ)]

/-! ### The sesquilinear package -/

lemma NQformArc_zero (a b : ℝ) : NQformArc a b 0 = 0 := by
  simp [NQformArc]

lemma NBformArc_self (a b : ℝ) (u : ℤ → ℂ) : NBformArc a b u u = (NQformArc a b u : ℂ) := by
  rw [NBformArc, NQformArc, Complex.ofReal_tsum]
  refine tsum_congr fun ℓ => ?_
  rw [Complex.conj_mul', Complex.ofReal_mul, Complex.ofReal_pow]

lemma NBformArc_conj_symm (a b : ℝ) (u v : ℤ → ℂ) :
    NBformArc a b v u = (starRingEnd ℂ) (NBformArc a b u v) := by
  rw [NBformArc, NBformArc, Complex.conj_tsum]
  refine tsum_congr fun ℓ => ?_
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

lemma NBformArc_add_left (ha : a ∈ Set.Ioo (0 : ℝ) 1) (b : ℝ) {u₁ u₂ v : ℤ → ℂ}
    (h₁ : u₁ ∈ ArcDom) (h₂ : u₂ ∈ ArcDom) (hv : v ∈ ArcDom) :
    NBformArc a b (u₁ + u₂) v = NBformArc a b u₁ v + NBformArc a b u₂ v := by
  rw [NBformArc, NBformArc, NBformArc,
    ← (summable_pair ha b h₁.1 hv.1).tsum_add (summable_pair ha b h₂.1 hv.1)]
  refine tsum_congr fun ℓ => ?_
  simp only [Pi.add_apply, map_add]
  ring

lemma NBformArc_add_right (ha : a ∈ Set.Ioo (0 : ℝ) 1) (b : ℝ) {u v₁ v₂ : ℤ → ℂ}
    (hu : u ∈ ArcDom) (h₁ : v₁ ∈ ArcDom) (h₂ : v₂ ∈ ArcDom) :
    NBformArc a b u (v₁ + v₂) = NBformArc a b u v₁ + NBformArc a b u v₂ := by
  rw [NBformArc, NBformArc, NBformArc,
    ← (summable_pair ha b hu.1 h₁.1).tsum_add (summable_pair ha b hu.1 h₂.1)]
  refine tsum_congr fun ℓ => ?_
  simp only [Pi.add_apply]
  ring

lemma NQformArc_smul (a b : ℝ) (t : ℂ) (u : ℤ → ℂ) :
    NQformArc a b (t • u) = ‖t‖ ^ 2 * NQformArc a b u := by
  rw [NQformArc, NQformArc, ← tsum_mul_left]
  refine tsum_congr fun ℓ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  ring

/-! ### The head split and tail positivity -/

/-- The tail summand: the form's terms off the heads `{0, −1}`. -/
def tailTerm (a b : ℝ) (u : ℤ → ℂ) (ℓ : ℤ) : ℝ :=
  if ℓ = 0 ∨ ℓ = -1 then 0 else sigmaArc a b ℓ * ‖u ℓ‖ ^ 2

lemma summable_tailTerm (ha : a ∈ Set.Ioo (0 : ℝ) 1) (b : ℝ) {u : ℤ → ℂ}
    (hu : Summable fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖u ℓ‖ ^ 2) :
    Summable (tailTerm a b u) := by
  refine Summable.of_norm ((summable_sigmaArc_mul_sq ha b hu).abs.of_nonneg_of_le
    (fun ℓ => norm_nonneg _) fun ℓ => ?_)
  rw [Real.norm_eq_abs, tailTerm]
  split_ifs
  · simp only [abs_zero]; positivity
  · exact le_rfl

/-- `N(u) = σ(0)|u₀|² + σ(−1)|u₋₁|² + ∑ tail`. -/
lemma NQformArc_split (ha : a ∈ Set.Ioo (0 : ℝ) 1) (b : ℝ) {u : ℤ → ℂ}
    (hu : Summable fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖u ℓ‖ ^ 2) :
    NQformArc a b u = sigmaArc a b 0 * ‖u 0‖ ^ 2 + sigmaArc a b (-1) * ‖u (-1)‖ ^ 2
      + ∑' ℓ : ℤ, tailTerm a b u ℓ := by
  have hS := summable_sigmaArc_mul_sq ha b hu
  have hT := summable_tailTerm ha b hu
  have h0 : Summable fun ℓ : ℤ => if ℓ = 0 then sigmaArc a b 0 * ‖u 0‖ ^ 2 else 0 :=
    summable_of_ne_finset_zero (s := {0}) fun ℓ hℓ => by
      simp only [Finset.mem_singleton] at hℓ; simp [hℓ]
  have h1 : Summable fun ℓ : ℤ => if ℓ = -1 then sigmaArc a b (-1) * ‖u (-1)‖ ^ 2 else 0 :=
    summable_of_ne_finset_zero (s := {-1}) fun ℓ hℓ => by
      simp only [Finset.mem_singleton] at hℓ; simp [hℓ]
  have hsum0 : (∑' ℓ : ℤ, if ℓ = 0 then sigmaArc a b 0 * ‖u 0‖ ^ 2 else 0)
      = sigmaArc a b 0 * ‖u 0‖ ^ 2 := tsum_ite_eq 0 _
  have hsum1 : (∑' ℓ : ℤ, if ℓ = -1 then sigmaArc a b (-1) * ‖u (-1)‖ ^ 2 else 0)
      = sigmaArc a b (-1) * ‖u (-1)‖ ^ 2 := tsum_ite_eq (-1) _
  rw [NQformArc, ← hsum0, ← hsum1, ← h0.tsum_add h1, ← (h0.add h1).tsum_add hT]
  refine tsum_congr fun ℓ => ?_
  simp only [tailTerm]
  by_cases hℓ0 : ℓ = 0
  · subst hℓ0; simp
  · by_cases hℓ1 : ℓ = -1
    · subst hℓ1; simp
    · simp [hℓ0, hℓ1]

lemma tailTerm_nonneg (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1) (u : ℤ → ℂ) (ℓ : ℤ) :
    0 ≤ tailTerm a b u ℓ := by
  rw [tailTerm]
  split_ifs with h
  · exact le_rfl
  · push Not at h
    exact mul_nonneg (sigmaArc_pos ha hb h.1 h.2).le (sq_nonneg _)

lemma tsum_tailTerm_nonneg (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1) (u : ℤ → ℂ) :
    0 ≤ ∑' ℓ : ℤ, tailTerm a b u ℓ :=
  tsum_nonneg (tailTerm_nonneg ha hb u)

/-- For `0 < a < 1` and `|b| < 1`, the tail of a weighted-square-summable
sequence is strictly positive if some coordinate outside `{0, −1}` is nonzero. -/
lemma tsum_tailTerm_pos (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1) {u : ℤ → ℂ}
    (hu : Summable fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖u ℓ‖ ^ 2)
    {ℓ₀ : ℤ} (h0 : ℓ₀ ≠ 0) (h1 : ℓ₀ ≠ -1) (hne : u ℓ₀ ≠ 0) :
    0 < ∑' ℓ : ℤ, tailTerm a b u ℓ := by
  have hT := summable_tailTerm ha b hu
  refine lt_of_lt_of_le ?_ (hT.le_tsum ℓ₀ fun ℓ _ => tailTerm_nonneg ha hb u ℓ)
  rw [tailTerm, if_neg (by tauto)]
  exact mul_pos (sigmaArc_pos ha hb h0 h1) (by positivity)

/-- For `0 < a < 1` and `|b| < 1`, a nonzero weighted-square-summable sequence
vanishing at coordinates `0` and `−1` has positive form value. No arc-support
hypothesis is required. -/
theorem NQformArc_pos_of_heads_zero (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1)
    {u : ℤ → ℂ} (hu : Summable fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖u ℓ‖ ^ 2)
    (hu0 : u 0 = 0) (hu1 : u (-1) = 0) (hne : ∃ ℓ, u ℓ ≠ 0) : 0 < NQformArc a b u := by
  obtain ⟨ℓ₀, hℓ₀⟩ := hne
  have h0 : ℓ₀ ≠ 0 := fun h => hℓ₀ (h ▸ hu0)
  have h1 : ℓ₀ ≠ -1 := fun h => hℓ₀ (h ▸ hu1)
  rw [NQformArc_split ha b hu, hu0, hu1]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    add_zero, zero_add]
  exact tsum_tailTerm_pos ha hb hu h0 h1 hℓ₀

end KsIndex.ArcForm
