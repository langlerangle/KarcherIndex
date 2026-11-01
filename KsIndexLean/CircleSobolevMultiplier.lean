module

public import KsIndexLean.CircleSobolev
public import KsIndexLean.DtNCircle

@[expose] public section


/-! Bounded multipliers on the weighted Fourier family, with physical coefficient laws. -/
noncomputable section
namespace KsIndex.CircleSobolev

lemma norm_multiplier_coordinate_le {s t C : ℝ} (m : ℤ → ℂ)
    (hC : 0 ≤ C) (hm : ∀ n, ‖m n‖ * weight t n ≤ C * weight s n)
    (u : Space s) (n : ℤ) :
    ‖(weight t n : ℂ) * (m n * coeff s u n)‖ ≤ ‖(C : ℂ) • u n‖ := by
  have h := mul_le_mul_of_nonneg_right (hm n) (norm_nonneg (coeff s u n))
  have he : ‖u n‖ = weight s n * ‖coeff s u n‖ := by
    conv_lhs => rw [← weight_mul_coeff s u n]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos s n)]
  rw [norm_mul, norm_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos t n), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hC, he]
  nlinarith

/-- Apply a symbol satisfying the weighted operator estimate. -/
def multiplier {s t C : ℝ} (m : ℤ → ℂ) (hC : 0 ≤ C)
    (hm : ∀ n, ‖m n‖ * weight t n ≤ C * weight s n) (u : Space s) : Space t :=
  ⟨fun n => (weight t n : ℂ) * (m n * coeff s u n),
    (lp.memℓp ((C : ℂ) • u)).mono' (norm_multiplier_coordinate_le m hC hm u)⟩

@[simp] theorem coeff_multiplier {s t C : ℝ} (m : ℤ → ℂ) (hC : 0 ≤ C)
    (hm : ∀ n, ‖m n‖ * weight t n ≤ C * weight s n) (u : Space s) (n : ℤ) :
    coeff t (multiplier m hC hm u) n = m n * coeff s u n := by
  have hw : (weight t n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos t n).ne'
  simp [coeff, multiplier, hw]

theorem norm_multiplier_le {s t C : ℝ} (m : ℤ → ℂ) (hC : 0 ≤ C)
    (hm : ∀ n, ‖m n‖ * weight t n ≤ C * weight s n) (u : Space s) :
    ‖multiplier m hC hm u‖ ≤ C * ‖u‖ := by
  have h := lp.norm_mono (x := multiplier m hC hm u) (y := (C : ℂ) • u)
    (by norm_num : (2 : ENNReal) ≠ 0)
    (norm_multiplier_coordinate_le m hC hm u)
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC] using h

def multiplierCLM {s t C : ℝ} (m : ℤ → ℂ) (hC : 0 ≤ C)
    (hm : ∀ n, ‖m n‖ * weight t n ≤ C * weight s n) : Space s →L[ℂ] Space t :=
  LinearMap.mkContinuous
    { toFun := multiplier m hC hm
      map_add' := fun u v => by
        apply Subtype.ext
        funext n
        change (weight t n : ℂ) * (m n * coeff s (u + v) n) =
          (weight t n : ℂ) * (m n * coeff s u n) +
          (weight t n : ℂ) * (m n * coeff s v n)
        simp [coeff, mul_add]
      map_smul' := fun c u => by
        apply Subtype.ext
        funext n
        simp [multiplier, coeff, mul_left_comm] }
    C (norm_multiplier_le m hC hm)

/-- Every diagonal multiplier preserves the mean-zero constraint. -/
theorem multiplier_mem_dotted {s t C : ℝ} (m : ℤ → ℂ) (hC : 0 ≤ C)
    (hm : ∀ n, ‖m n‖ * weight t n ≤ C * weight s n) {u : Space s}
    (hu : u ∈ dotted s) : multiplier m hC hm u ∈ dotted t := by
  rw [mem_dotted, coeff_multiplier, (mem_dotted s u).mp hu, mul_zero]

/-- Reuse the existing nonzero-mode symbol; zero is only a bookkeeping extension. -/
def dtnMultiplier (k : ℕ) (n : ℤ) : ℂ :=
  if hn : n = 0 then 0 else (KsIndex.DtNCircle.dtnSymbol k ⟨n, hn⟩ : ℂ)

@[simp] theorem dtnMultiplier_nonzero (k : ℕ) (n : KsIndex.DtNCircle.NZ) :
    dtnMultiplier k n = (KsIndex.DtNCircle.dtnSymbol k n : ℂ) := by
  simp [dtnMultiplier, n.property]

lemma dtnSymbol_growth (k : ℕ) (n : KsIndex.DtNCircle.NZ) :
    |KsIndex.DtNCircle.dtnSymbol k n| ≤
      (1 + ((k : ℝ) - 1) ^ 2) * (1 + |(n.val : ℝ)|) := by
  have hn : (1 : ℤ) ≤ |n.val| := by
    have hp := abs_pos.mpr n.property
    omega
  have ha : (1 : ℝ) ≤ |(n.val : ℝ)| := by exact_mod_cast hn
  have hab := KsIndex.DtNCircle.absval_pos n
  rw [KsIndex.DtNCircle.dtnSymbol, abs_div, abs_abs, div_le_iff₀ hab]
  have he : |(n.val : ℝ) ^ 2 - ((k : ℝ) - 1) ^ 2| ≤
      |(n.val : ℝ)| ^ 2 + ((k : ℝ) - 1) ^ 2 := by
    calc
      _ ≤ |(n.val : ℝ) ^ 2| + |((k : ℝ) - 1) ^ 2| := abs_sub _ _
      _ = _ := by simp [sq_abs]
  have hb := sq_nonneg ((k : ℝ) - 1)
  have hx : 0 ≤ ((k : ℝ) - 1) ^ 2 * (|(n.val : ℝ)| - 1) := mul_nonneg hb (by linarith)
  nlinarith [sq_abs (n.val : ℝ)]

lemma dtnMultiplier_bound (k : ℕ) (n : ℤ) :
    ‖dtnMultiplier k n‖ * weight (-(1 / 2 : ℝ)) n ≤
      (1 + ((k : ℝ) - 1) ^ 2) * weight (1 / 2 : ℝ) n := by
  by_cases hn : n = 0
  · subst n
    simpa [dtnMultiplier] using mul_nonneg
      (by positivity : 0 ≤ 1 + ((k : ℝ) - 1) ^ 2) (weight_pos (1 / 2 : ℝ) 0).le
  · have hg := dtnSymbol_growth k ⟨n, hn⟩
    have hw : weight (1 / 2 : ℝ) n ^ 2 = 1 + |(n : ℝ)| := by
      rw [weight_sq]
      norm_num
    rw [weight_neg, ← div_eq_mul_inv, div_le_iff₀ (weight_pos (1 / 2 : ℝ) n)]
    have he : ‖dtnMultiplier k n‖ = |KsIndex.DtNCircle.dtnSymbol k ⟨n, hn⟩| := by
      simp only [dtnMultiplier, dite_eq_right hn, Complex.norm_real, Real.norm_eq_abs]
    rw [he]
    nlinarith

/-- The order-one DtN multiplier from `H^(1/2)` to `H^(-1/2)`. -/
def dtnCLM (k : ℕ) : Space (1 / 2 : ℝ) →L[ℂ] Space (-(1 / 2 : ℝ)) :=
  multiplierCLM (dtnMultiplier k) (by positivity) (dtnMultiplier_bound k)

/-- Identification with the existing symbol, at every physical nonzero mode. -/
theorem coeff_dtnCLM (k : ℕ) (u : Space (1 / 2 : ℝ)) (n : KsIndex.DtNCircle.NZ) :
    coeff (-(1 / 2 : ℝ)) (dtnCLM k u) n =
      (KsIndex.DtNCircle.dtnSymbol k n : ℂ) * coeff (1 / 2 : ℝ) u n := by
  change coeff _ (multiplier (dtnMultiplier k) (by positivity) (dtnMultiplier_bound k) u) n = _
  rw [coeff_multiplier, dtnMultiplier_nonzero]

theorem dtnCLM_mem_dotted (k : ℕ) (u : Space (1 / 2 : ℝ)) :
    dtnCLM k u ∈ dotted (-(1 / 2 : ℝ)) := by
  rw [mem_dotted]
  change coeff _ (multiplier (dtnMultiplier k) (by positivity) (dtnMultiplier_bound k) u) 0 = 0
  rw [coeff_multiplier]
  simp [dtnMultiplier]

/-- The paper's mean-zero DtN map, with the inherited Sobolev norms. -/
def dottedDtnCLM (k : ℕ) : dotted (1 / 2 : ℝ) →L[ℂ] dotted (-(1 / 2 : ℝ)) :=
  (dtnCLM k).restrict (fun u _ => dtnCLM_mem_dotted k u)

theorem coeff_dottedDtnCLM (k : ℕ) (u : dotted (1 / 2 : ℝ))
    (n : KsIndex.DtNCircle.NZ) :
    coeff (-(1 / 2 : ℝ)) (dottedDtnCLM k u) n =
      (KsIndex.DtNCircle.dtnSymbol k n : ℂ) * coeff (1 / 2 : ℝ) u n :=
  coeff_dtnCLM k u n

theorem norm_dottedDtnCLM_apply_le (k : ℕ) (u : dotted (1 / 2 : ℝ)) :
    ‖dottedDtnCLM k u‖ ≤ (1 + ((k : ℝ) - 1) ^ 2) * ‖u‖ :=
  norm_multiplier_le (dtnMultiplier k) (by positivity) (dtnMultiplier_bound k) u

/-- Diagonal multipliers preserve each coefficient-support character class. -/
theorem multiplier_mem_character {s t C : ℝ} (m : ℤ → ℂ) (hC : 0 ≤ C)
    (hm : ∀ n, ‖m n‖ * weight t n ≤ C * weight s n) (j k : ℤ) {u : Space s}
    (hu : u ∈ character s j k) : multiplier m hC hm u ∈ character t j k := by
  rw [mem_character] at hu ⊢
  intro n hn
  rw [coeff_multiplier, hu n hn, mul_zero]

end KsIndex.CircleSobolev
