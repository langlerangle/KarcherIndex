module

/-
KsIndexLean — ZeroMeanBoundaryBlock: the boundary (DtN) block of the
zero-angular-mean decomposition ([ksindexi] tex 2250–2290, the `nop` side of
the j = 0 zero-mean half of Lemma `nop-sphop`).

The boundary space is the mean-zero class-zero `Ḣ^{1/2}`; on it the DtN form
`faithfulDtnB` diagonalizes over the class-zero nonzero Fourier modes
`ℓ ∈ kℤ \ {0}`, whose symbol `σ_k(ℓ) = (ℓ² − (k−1)²)/|ℓ|` is strictly
positive since `|ℓ| ≥ k`.  Hence the block is positive definite — the
boundary counterpart of `neumannCount k 0 = 0` (the paper's radial `ℓ = 0`
mode, the `+1` of `pureNeumann_weak_index`, is excluded by mean-zero).
-/
public import KsIndexLean.ZeroMeanExtension

@[expose] public section


noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.DtNCircle KsIndex.CircleSobolev KsIndex.DtnBridge

/-! ### The symbol on the class-zero modes -/

/-- The DtN symbol is strictly positive on every nonzero mode divisible
by `k`. -/
lemma dtnSymbol_pos_of_dvd {k : ℕ} (hk : 1 ≤ k) (ℓ : NZ)
    (hd : (k : ℤ) ∣ ℓ.val) : 0 < dtnSymbol k ℓ := by
  have habs : (k : ℤ) ≤ |ℓ.val| :=
    Int.le_of_dvd (abs_pos.mpr ℓ.property) ((dvd_abs _ _).mpr hd)
  have habsR : (k : ℝ) ≤ |(ℓ.val : ℝ)| := by exact_mod_cast habs
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [dtnSymbol]
  apply div_pos _ (absval_pos ℓ)
  nlinarith [sq_abs ((ℓ.val : ℝ)), abs_nonneg ((ℓ.val : ℝ))]

/-- Class-zero elements have coefficients supported on multiples of `k`. -/
lemma coeff_eq_zero_of_character_zero {k : ℕ} {f : Space (1 / 2 : ℝ)}
    (hf : f ∈ character (1 / 2 : ℝ) ((0 : ℕ) : ℤ) (k : ℤ))
    {n : ℤ} (hn : ¬ (k : ℤ) ∣ n) : coeff (1 / 2 : ℝ) f n = 0 := by
  apply (mem_character _ _ _ f).mp hf n
  rintro ⟨m, hm⟩
  exact hn ⟨m, by simpa using hm⟩

/-! ### The diagonal series of the self-pairing -/

/-- The symbol-weighted coefficient series converges absolutely on
`Ḣ^{1/2}` data. -/
lemma summable_dtn_coeff_sq (k : ℕ) (f : Space (1 / 2 : ℝ)) :
    Summable (fun ℓ : NZ =>
      dtnSymbol k ℓ * ‖coeff (1 / 2 : ℝ) f ℓ.val‖ ^ 2) := by
  have hw : Summable (fun n : ℤ =>
      (1 + |(n : ℝ)|) * ‖coeff (1 / 2 : ℝ) f n‖ ^ 2) := by
    have h := (hasSum_weighted_sq (1 / 2 : ℝ) f).summable
    simpa only [weight_sq_half] using h
  have hsub : Summable (fun ℓ : NZ =>
      (1 + |(ℓ.val : ℝ)|) * ‖coeff (1 / 2 : ℝ) f ℓ.val‖ ^ 2) :=
    hw.subtype _
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun ℓ => abs_nonneg _) _
    (hsub.mul_left (1 + ((k : ℝ) - 1) ^ 2))
  intro ℓ
  rw [abs_mul, abs_of_nonneg (sq_nonneg ‖coeff (1 / 2 : ℝ) f ℓ.val‖)]
  calc |dtnSymbol k ℓ| * ‖coeff (1 / 2 : ℝ) f ℓ.val‖ ^ 2
      ≤ ((1 + ((k : ℝ) - 1) ^ 2) * (1 + |(ℓ.val : ℝ)|)) *
          ‖coeff (1 / 2 : ℝ) f ℓ.val‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (dtnSymbol_growth k ℓ) (sq_nonneg _)
    _ = (1 + ((k : ℝ) - 1) ^ 2) *
          ((1 + |(ℓ.val : ℝ)|) * ‖coeff (1 / 2 : ℝ) f ℓ.val‖ ^ 2) := by ring

/-- The DtN self-pairing is the real symbol-weighted coefficient series. -/
lemma faithfulDtnB_self_re (k : ℕ) (f : dotted (1 / 2 : ℝ)) :
    faithfulDtnB k f f =
      ((∑' ℓ : NZ, dtnSymbol k ℓ * ‖coeff (1 / 2 : ℝ) f.val ℓ.val‖ ^ 2 : ℝ) : ℂ) := by
  have hmap := Complex.ofRealCLM.map_tsum (summable_dtn_coeff_sq k f.val)
  have hmap' : ((∑' ℓ : NZ, dtnSymbol k ℓ * ‖coeff (1 / 2 : ℝ) f.val ℓ.val‖ ^ 2 : ℝ) : ℂ) =
      ∑' ℓ : NZ, ((dtnSymbol k ℓ * ‖coeff (1 / 2 : ℝ) f.val ℓ.val‖ ^ 2 : ℝ) : ℂ) := hmap
  rw [faithfulDtnB, hmap']
  apply tsum_congr
  intro ℓ
  rw [mul_assoc, mul_comm ((starRingEnd ℂ) _) _, Complex.mul_conj',
    Complex.ofReal_mul, Complex.ofReal_pow]

/-! ### The zero-mean class-zero boundary space and form -/

/-- The paper's mean-zero class-zero boundary data (`Ḣ^{1/2}_{(0;k),⊥}`). -/
def zeroMeanBoundarySpace (k : ℕ) : Submodule ℂ (Space (1 / 2 : ℝ)) :=
  dotted (1 / 2 : ℝ) ⊓ character (1 / 2 : ℝ) ((0 : ℕ) : ℤ) (k : ℤ)

/-- The boundary space embeds in the full mean-zero space. -/
def zeroMeanBoundaryDotted (k : ℕ) :
    zeroMeanBoundarySpace k →ₗ[ℂ] dotted (1 / 2 : ℝ) where
  toFun f := ⟨f.val, f.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The boundary block of the zero-mean decomposition — the `nop` side. -/
def zeroMeanBoundaryForm (k : ℕ) (f g : zeroMeanBoundarySpace k) : ℂ :=
  faithfulDtnB k (zeroMeanBoundaryDotted k f) (zeroMeanBoundaryDotted k g)

lemma zeroMeanBoundaryForm_zero_left (k : ℕ) (f : zeroMeanBoundarySpace k) :
    zeroMeanBoundaryForm k 0 f = 0 := by
  simp [zeroMeanBoundaryForm, faithfulDtnB, zeroMeanBoundaryDotted, coeff]

lemma zeroMeanBoundaryForm_zero_right (k : ℕ) (f : zeroMeanBoundarySpace k) :
    zeroMeanBoundaryForm k f 0 = 0 := by
  simp [zeroMeanBoundaryForm, faithfulDtnB, zeroMeanBoundaryDotted, coeff]

/-! ### Positivity -/

/-- Each diagonal term of the boundary block is nonnegative on class-zero
mean-zero data: on-class symbols are positive, off-class coefficients
vanish. -/
lemma zeroMeanBoundary_term_nonneg {k : ℕ} (hk : 1 ≤ k)
    (f : zeroMeanBoundarySpace k) (ℓ : NZ) :
    0 ≤ dtnSymbol k ℓ * ‖coeff (1 / 2 : ℝ) f.val ℓ.val‖ ^ 2 := by
  by_cases hd : (k : ℤ) ∣ ℓ.val
  · exact mul_nonneg (dtnSymbol_pos_of_dvd hk ℓ hd).le (sq_nonneg _)
  · rw [coeff_eq_zero_of_character_zero f.property.2 hd]
    simp

/-- The boundary block is nonnegative. -/
lemma zeroMeanBoundaryForm_self_nonneg {k : ℕ} (hk : 1 ≤ k)
    (f : zeroMeanBoundarySpace k) :
    0 ≤ (zeroMeanBoundaryForm k f f).re := by
  rw [zeroMeanBoundaryForm, faithfulDtnB_self_re, Complex.ofReal_re]
  exact tsum_nonneg (zeroMeanBoundary_term_nonneg hk f)

/-- The boundary block is positive definite: the class-zero mean-zero modes
all carry a strictly positive symbol. -/
lemma zeroMeanBoundaryForm_self_pos {k : ℕ} (hk : 1 ≤ k)
    (f : zeroMeanBoundarySpace k) (hf : f ≠ 0) :
    0 < (zeroMeanBoundaryForm k f f).re := by
  rw [zeroMeanBoundaryForm, faithfulDtnB_self_re, Complex.ofReal_re]
  have hne : f.val ≠ 0 := fun h => hf (Subtype.ext h)
  have hcoeff : ∃ n : ℤ, coeff (1 / 2 : ℝ) f.val n ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hne
    apply coeff_injective (1 / 2 : ℝ)
    funext n
    rw [hall n]
    simp [coeff]
  obtain ⟨n, hn⟩ := hcoeff
  have hn0 : n ≠ 0 := by
    intro h
    exact hn (h ▸ f.property.1)
  have hdvd : (k : ℤ) ∣ n := by
    by_contra hd
    exact hn (coeff_eq_zero_of_character_zero f.property.2 hd)
  apply (summable_dtn_coeff_sq k f.val).tsum_pos
    (zeroMeanBoundary_term_nonneg hk f) ⟨n, hn0⟩
  exact mul_pos (dtnSymbol_pos_of_dvd hk ⟨n, hn0⟩ hdvd)
    (pow_pos (norm_pos_iff.mpr hn) 2)

end KsIndex.Trace
