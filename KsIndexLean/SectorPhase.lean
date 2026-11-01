module

/-
KsIndexLean — SectorPhase: sector indices and nullities in half-angle coordinates.

`SectorSpectralAdditivity` proves the paper's `iop-qop_equiv` (items 4–5) with the two circle
parameters written as `coefT α = sin απ/(1+cos απ)` and
`coefC α = −sin απ/(1−cos απ)`; `Staircase` counts per-phase indices in the
letters `tan(απ/2)` and `tan((1−α)π/2) = cot(απ/2)`.  This file supplies the
half-angle identities and the `s ↦ −s` invariance of `ind`/`nul` (only `s²`
enters `Q_s`), and states the sector index/nullity of `𝓝_{3,α}` for `α ∈ (0,1)`
in the paper's own letters — in particular `ind₂(𝓝_{3,α}) = phaseCount α`.
-/
public import KsIndexLean.SectorSpectralAdditivity
public import KsIndexLean.Staircase

@[expose] public section


noncomputable section

namespace KsIndex.SectorPhase

open KsIndex.CircleQ KsIndex.Sector KsIndex.SectorForm KsIndex.SectorReduce
  KsIndex.SectorIndex KsIndex.FormIndex KsIndex.Statements KsIndex.FormIndexBridge
  KsIndex.Staircase Real

/-! ### `ind`/`nul` see only `s²` -/

lemma Qform_neg (s : ℝ) : Qform (-s) = Qform s := by
  funext u; simp only [Qform, neg_sq]

lemma Bform_neg (s : ℝ) : Bform (-s) = Bform s := by
  funext u v; simp only [Bform, Complex.ofReal_neg, neg_sq]

lemma ind_neg (s : ℝ) : ind (-s) = ind s := by
  rw [ind_eq_formIndex, ind_eq_formIndex, Qform_neg]

lemma nul_neg (s : ℝ) : nul (-s) = nul s := by
  rw [nul_eq_formNullity, nul_eq_formNullity, Bform_neg]

/-! ### Half-angle identities for the embedding coefficients -/

/-- `1 + cos απ ≠ 0` for `α ∈ (0,1)`. -/
lemma one_add_cos_ne_zero {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    (1 : ℝ) + cos (α * π) ≠ 0 := by
  have hπ := pi_pos
  have h : cos π < cos (α * π) :=
    cos_lt_cos_of_nonneg_of_le_pi (by positivity) le_rfl
      (by nlinarith [mul_pos (show (0:ℝ) < 1 - α by linarith) hπ])
  rw [cos_pi] at h
  linarith

/-- `1 − cos απ ≠ 0` for `α ∈ (0,1)`. -/
lemma one_sub_cos_ne_zero {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    (1 : ℝ) - cos (α * π) ≠ 0 := by
  have hπ := pi_pos
  have h : cos (α * π) < cos 0 :=
    cos_lt_cos_of_nonneg_of_le_pi le_rfl
      (by nlinarith [mul_pos (show (0:ℝ) < 1 - α by linarith) hπ]) (by positivity)
  rw [cos_zero] at h
  linarith

/-- `coefT α = tan(απ/2)`: the half-angle identity `sin x/(1+cos x) = tan(x/2)`. -/
lemma coefT_eq_tan {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    coefT α = tan (α * π / 2) := by
  have hπ := pi_pos
  set x := α * π / 2 with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < π / 2 := by
    rw [hx]; nlinarith [mul_pos (show (0:ℝ) < 1 - α by linarith) hπ]
  have hc : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩
  have h2x : α * π = 2 * x := by rw [hx]; ring
  rw [coefT, h2x, sin_two_mul, cos_two_mul, tan_eq_sin_div_cos]
  field_simp
  ring

/-- `coefC α = −tan((1−α)π/2) = −cot(απ/2)`: the half-angle identity
`sin x/(1−cos x) = cot(x/2)`. -/
lemma coefC_eq_neg_tan {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    coefC α = -tan ((1 - α) * π / 2) := by
  have hπ := pi_pos
  set x := α * π / 2 with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < π / 2 := by
    rw [hx]; nlinarith [mul_pos (show (0:ℝ) < 1 - α by linarith) hπ]
  have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi hx0 (by linarith)
  have hc : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩
  have h2x : α * π = 2 * x := by rw [hx]; ring
  have hsub : (1 - α) * π / 2 = π / 2 - x := by rw [hx]; ring
  have hden : 1 - cos (2 * x) = 2 * sin x ^ 2 := by
    rw [cos_two_mul]; linear_combination (-2) * sin_sq_add_cos_sq x
  rw [coefC, h2x, sin_two_mul, hden, hsub, tan_pi_div_two_sub, tan_eq_sin_div_cos, inv_div]
  field_simp

/-! ### `iop-qop_equiv` in the paper's letters -/

/-- **`ind₂(𝓝_{3,α}) = ind(𝒬_{tan(απ/2)}) + ind(𝒬_{cot(απ/2)})`** for `α ∈ (0,1)`
([ksindexi] `iop-qop_equiv` item 4, with `cot(απ/2) = tan((1−α)π/2)`). -/
theorem sector_index_eq (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    formIndex (NQform α) Domς
      = ind (tan (α * π / 2)) + ind (tan ((1 - α) * π / 2)) := by
  rw [formIndex_NQform_Domς_spectral α (one_add_cos_ne_zero h0 h1) (one_sub_cos_ne_zero h0 h1),
    coefT_eq_tan h0 h1, coefC_eq_neg_tan h0 h1, ind_neg]

/-- **`nul₂(𝓝_{3,α}) = nul(𝒬_{tan(απ/2)}) + nul(𝒬_{cot(απ/2)})`** for `α ∈ (0,1)`
([ksindexi] `iop-qop_equiv` item 5). -/
theorem sector_nullity_eq (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    formNullity (NBform α) Domς
      = nul (tan (α * π / 2)) + nul (tan ((1 - α) * π / 2)) := by
  rw [formNullity_NBform_Domς α (one_add_cos_ne_zero h0 h1) (one_sub_cos_ne_zero h0 h1),
    coefT_eq_tan h0 h1, coefC_eq_neg_tan h0 h1, nul_neg]

/-- **The sector index is the staircase per-phase count**: `ind₂(𝓝_{3,α}) =
phaseCount α` (`2` on the middle band `(α*, 1−α*)`, else `1`) for `α ∈ (0,1)`.
This expresses the spectral count in the paper's `ind_null_rel_threshold`
directly in terms of `𝓝_{3,α}`. -/
theorem sector_index_eq_phaseCount (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    formIndex (NQform α) Domς = (phaseCount α : ℕ∞) := by
  rw [sector_index_eq α h0 h1, phaseCount_eq h0 h1]

end KsIndex.SectorPhase
