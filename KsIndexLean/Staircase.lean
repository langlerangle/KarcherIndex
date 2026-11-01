module

/-
KsIndexLean — Staircase: the per-phase index count of [ksindexi] Section 4.

The spectral engine of Prop `\ref{ind_null_rel_threshold}` and the staircase
of Theorem `\ref{k=3}`.  Each quasiperiodic phase `α ∈ (0,1)` contributes, via
`iop`–`qop`, TWO copies of the one-parameter form `Q_s`, at `s = tan(απ/2)` and
`s = cot(απ/2)`.  Because `tan(απ/2)·cot(απ/2) = 1` and the threshold `s* > 1`,
the two arguments straddle `1` with product `1`: at least one is always `< s*`,
and both are `< s*` exactly when `tan(απ/2) ∈ (1/s*, s*)`, i.e.
`α ∈ (α*, 1−α*)`.  Hence the per-phase reduced index is `1` on the edges and `2`
in the middle band. The sum over the nonzero phases `n/m`,
`1 ≤ n < m`, gives the reduced staircase.

This layer is spectral bookkeeping over `circle_main`'s established pattern
`ind s = if s < s* then 1 else 0`; the identification of this model count with
the disk-chain index is supplied by `KsIndex.Spectral.indSurface_three_eq_model`
in `K3IndexComplete`,
with the geometric EW transport in `KarcherGeometricInvariants`.
-/
public import KsIndexLean.Statements

@[expose] public section


noncomputable section

namespace KsIndex.Staircase

open KsIndex.CircleQ KsIndex.Threshold KsIndex.Statements Real Set

/-! ### The threshold `s*` and the index pattern -/

/-- The single-crossing threshold `s* ∈ (1, √3)` of `exists_threshold`. -/
def sstar : ℝ := Classical.choose exists_threshold

lemma sstar_spec :
    sstar ∈ Ioo 1 (Real.sqrt 3) ∧ gam sstar = 0 ∧
      (∀ s : ℝ, 0 < s → s < sstar → gam s < 0) ∧
      (∀ s : ℝ, sstar < s → 0 < gam s) :=
  Classical.choose_spec exists_threshold

lemma one_lt_sstar : 1 < sstar := sstar_spec.1.1

lemma sstar_pos : 0 < sstar := lt_trans one_pos one_lt_sstar

/-- The Morse index of `Q_s` as a function of `s`: `1` below the threshold,
`0` at and above it.  (This is `circle_main`'s index clause, isolated.) -/
lemma ind_eq_ite {s : ℝ} (hs : 0 < s) : ind s = if s < sstar then 1 else 0 := by
  obtain ⟨_, h0, hbelow, habove⟩ := sstar_spec
  by_cases hlt : s < sstar
  · rw [if_pos hlt]
    exact (ind_eq_one_iff hs).mpr (hbelow s hs hlt)
  · rw [if_neg hlt]
    have hnneg : ¬ gam s < 0 := by
      rcases lt_or_eq_of_le (not_lt.mp hlt) with hgt | heq
      · exact asymm (habove s hgt)
      · rw [← heq, h0]; exact lt_irrefl 0
    have hne1 : ind s ≠ 1 := fun h => hnneg ((ind_eq_one_iff hs).mp h)
    exact Order.lt_one_iff.mp (lt_of_le_of_ne (ind_le_one s) hne1)

/-! ### The per-phase reduced index count -/

/-- **Spectral core of `\ref{ind_null_rel_threshold}`.**  For each phase
`α ∈ (0,1)` the reduced per-phase index `ind(Q_{tan(απ/2)}) + ind(Q_{cot(απ/2)})`
is `2` when *both* `tan(απ/2)` and `cot(απ/2)` lie below the threshold, and `1`
otherwise.  It is never `0`: since `cot(απ/2) = tan(απ/2)⁻¹`, the product is `1`,
so with `s* > 1` the two arguments cannot both be `≥ s*`. -/
lemma per_phase_count {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    ind (Real.tan (α * π / 2)) + ind (Real.tan ((1 - α) * π / 2))
      = if Real.tan (α * π / 2) < sstar ∧ Real.tan ((1 - α) * π / 2) < sstar
        then 2 else 1 := by
  have hpi := Real.pi_pos
  have hsp := sstar_pos
  have hx0 : 0 < α * π / 2 := by positivity
  have hx1 : α * π / 2 < π / 2 := by
    nlinarith [mul_pos (show (0:ℝ) < 1 - α by linarith) hpi]
  have ht1pos : 0 < Real.tan (α * π / 2) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith, hx1⟩)
  have ht2eq : Real.tan ((1 - α) * π / 2) = (Real.tan (α * π / 2))⁻¹ := by
    rw [show (1 - α) * π / 2 = π / 2 - α * π / 2 by ring, Real.tan_pi_div_two_sub]
  have ht2pos : 0 < Real.tan ((1 - α) * π / 2) := by rw [ht2eq]; exact inv_pos.mpr ht1pos
  rw [ind_eq_ite ht1pos, ind_eq_ite ht2pos]
  by_cases hb1 : Real.tan (α * π / 2) < sstar <;>
    by_cases hb2 : Real.tan ((1 - α) * π / 2) < sstar
  · rw [if_pos hb1, if_pos hb2, if_pos ⟨hb1, hb2⟩]; rfl
  · rw [if_pos hb1, if_neg hb2, if_neg (fun h => hb2 h.2)]; rfl
  · rw [if_neg hb1, if_pos hb2, if_neg (fun h => hb1 h.1)]; rfl
  · exfalso
    have hprod : Real.tan (α * π / 2) * Real.tan ((1 - α) * π / 2) = 1 := by
      rw [ht2eq, mul_inv_cancel₀ (ne_of_gt ht1pos)]
    have hge1 : sstar ≤ Real.tan (α * π / 2) := not_lt.mp hb1
    have hge2 : sstar ≤ Real.tan ((1 - α) * π / 2) := not_lt.mp hb2
    nlinarith [mul_le_mul hge1 hge2 hsp.le (le_trans hsp.le hge1), hprod,
      one_lt_sstar, mul_pos (show (0:ℝ) < sstar - 1 by linarith [one_lt_sstar]) hsp]

/-! ### The critical phase `α* = (2/π)·arctan(1/s*)` -/

/-- The critical phase `α* := (2/π)·arctan(1/s*)`, lying in `(0, 1/2)`. -/
def alphaStar : ℝ := 2 / π * Real.arctan (1 / sstar)

lemma arctan_inv_sstar_pos : 0 < Real.arctan (1 / sstar) := by
  have h : Real.arctan 0 < Real.arctan (1 / sstar) :=
    Real.arctan_strictMono (one_div_pos.mpr sstar_pos)
  rwa [Real.arctan_zero] at h

lemma arctan_inv_sstar_lt_quarter : Real.arctan (1 / sstar) < π / 4 := by
  have h : Real.arctan (1 / sstar) < Real.arctan 1 :=
    Real.arctan_strictMono ((div_lt_one sstar_pos).mpr one_lt_sstar)
  rwa [Real.arctan_one] at h

lemma alphaStar_pos : 0 < alphaStar := by
  rw [alphaStar]; exact mul_pos (by positivity) arctan_inv_sstar_pos

lemma alphaStar_lt_half : alphaStar < 1 / 2 := by
  have h : 2 / π * Real.arctan (1 / sstar) < 2 / π * (π / 4) :=
    mul_lt_mul_of_pos_left arctan_inv_sstar_lt_quarter (by positivity)
  have e : 2 / π * (π / 4) = 1 / 2 := by field_simp [Real.pi_ne_zero]; ring
  rw [e] at h
  rw [alphaStar]; exact h

/-- `arctan(1/s*) > π/6`, from `s* < √3` (the upper end of `exists_threshold`'s bracket). -/
lemma arctan_inv_sstar_gt_sixth : π / 6 < Real.arctan (1 / sstar) := by
  have hlt : (1 : ℝ) / Real.sqrt 3 < 1 / sstar :=
    one_div_lt_one_div_of_lt sstar_pos sstar_spec.1.2
  have harc : Real.arctan (1 / Real.sqrt 3) < Real.arctan (1 / sstar) :=
    Real.arctan_strictMono hlt
  have hval : Real.arctan (1 / Real.sqrt 3) = π / 6 := by
    have h3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have htan : Real.tan (π / 6) = 1 / Real.sqrt 3 := by
      rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_six, Real.cos_pi_div_six]
      field_simp
    rw [← htan]
    exact Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rwa [hval] at harc

/-- **`α* > 1/3`** (the lower end of the paper's `α* ∈ (1/3, 1/2)` bracket, “Quotients with six ends”, source label `k=3`),
from `s* < √3`. -/
lemma alphaStar_gt_third : 1 / 3 < alphaStar := by
  have h : 2 / π * (π / 6) < 2 / π * Real.arctan (1 / sstar) :=
    mul_lt_mul_of_pos_left arctan_inv_sstar_gt_sixth (by positivity)
  have e : 2 / π * (π / 6) = 1 / 3 := by field_simp [Real.pi_ne_zero]; ring
  rw [e] at h
  rw [alphaStar]; exact h

/-- The paper's threshold bracket `α* ∈ (1/3, 1/2)` (“Quotients with six ends”, source label `k=3`). -/
lemma alphaStar_mem_Ioo : alphaStar ∈ Set.Ioo (1 / 3 : ℝ) (1 / 2) :=
  ⟨alphaStar_gt_third, alphaStar_lt_half⟩

/-- `arctan s* = π/2 − arctan(1/s*)`. -/
lemma arctan_sstar_eq : Real.arctan sstar = π / 2 - Real.arctan (1 / sstar) := by
  rw [one_div, Real.arctan_inv_of_pos sstar_pos]; ring

/-! ### The α*-band reformulation -/

/-- `tan(βπ/2) < s* ↔ β < 1 − α*` for `β ∈ (0,1)`: `tan` is order-isomorphic to
`β` on `(0, π/2)` via `arctan`, and `arctan s* = (1−α*)·π/2`. -/
lemma tan_half_lt_sstar_iff {β : ℝ} (h0 : 0 < β) (h1 : β < 1) :
    Real.tan (β * π / 2) < sstar ↔ β < 1 - alphaStar := by
  have hπ := Real.pi_pos
  have hb0 : 0 < β * π / 2 := by positivity
  have hb1 : β * π / 2 < π / 2 := by
    nlinarith [mul_pos (show (0:ℝ) < 1 - β by linarith) hπ]
  rw [← Real.arctan_strictMono.lt_iff_lt, Real.arctan_tan (by linarith) hb1,
    arctan_sstar_eq, alphaStar]
  have key : (1 : ℝ) - 2 / π * Real.arctan (1 / sstar)
      = (π / 2 - Real.arctan (1 / sstar)) / (π / 2) := by
    field_simp [Real.pi_ne_zero]
  rw [key, lt_div_iff₀ (by positivity : (0:ℝ) < π / 2), mul_div_assoc]

/-- The middle band: both `Q_s` arguments lie below `s*` iff `α ∈ (α*, 1−α*)`. -/
lemma both_lt_sstar_iff {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    (Real.tan (α * π / 2) < sstar ∧ Real.tan ((1 - α) * π / 2) < sstar)
      ↔ α ∈ Ioo alphaStar (1 - alphaStar) := by
  rw [tan_half_lt_sstar_iff h0 h1, tan_half_lt_sstar_iff (by linarith) (by linarith),
    Set.mem_Ioo]
  constructor
  · rintro ⟨ha, hb⟩; exact ⟨by linarith, ha⟩
  · rintro ⟨ha, hb⟩; exact ⟨hb, by linarith⟩

/-- **Paper's `\ref{ind_null_rel_threshold}`, reduced form.**  The per-phase
reduced index is `2` on the open band `(α*, 1−α*)` and `1` outside it,
including both threshold endpoints, for phases in `(0,1)`. -/
lemma per_phase_count_band {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    ind (Real.tan (α * π / 2)) + ind (Real.tan ((1 - α) * π / 2))
      = if α ∈ Ioo alphaStar (1 - alphaStar) then 2 else 1 := by
  rw [per_phase_count h0 h1]
  exact if_congr (both_lt_sstar_iff h0 h1) rfl rfl

/-! ### The staircase sum -/

open Classical in
/-- The per-phase reduced index as a natural number: `2` on the middle band
`(α*, 1−α*)`, else `1`.  Provably equal to the spectral count
`ind(Q_{tan}) + ind(Q_{cot})` — see `phaseCount_eq`. -/
def phaseCount (α : ℝ) : ℕ := if α ∈ Ioo alphaStar (1 - alphaStar) then 2 else 1

/-- `phaseCount` agrees with the spectral count: for `α ∈ (0,1)` it equals
`ind(Q_{tan(απ/2)}) + ind(Q_{tan((1-α)π/2)})`. -/
lemma phaseCount_eq {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    (ind (Real.tan (α * π / 2)) + ind (Real.tan ((1 - α) * π / 2)) : ℕ∞)
      = (phaseCount α : ℕ∞) := by
  rw [per_phase_count_band h0 h1, phaseCount]
  by_cases h : α ∈ Ioo alphaStar (1 - alphaStar) <;> simp [h]

open Classical in
/-- The number of middle-band phases `n/m ∈ (α*, 1−α*)`, `n = 1,…,m−1`. -/
def bandCount (m : ℕ) : ℕ :=
  ∑ n ∈ Finset.Ico 1 m, if (n : ℝ) / m ∈ Ioo alphaStar (1 - alphaStar) then 1 else 0

/-- The reduced spectral staircase.  Summing the per-phase
reduced counts over the phases `n/m` (`n = 1,…,m−1`) gives `(m−1) + #band`.
Every term is a proven `Q_s` fact (`phaseCount_eq`); no geometric input. -/
theorem reduced_staircase (m : ℕ) :
    ∑ n ∈ Finset.Ico 1 m, phaseCount ((n : ℝ) / m) = (m - 1) + bandCount m := by
  classical
  have h : ∀ n : ℕ, phaseCount ((n : ℝ) / m)
      = 1 + (if (n : ℝ) / m ∈ Ioo alphaStar (1 - alphaStar) then 1 else 0) := by
    intro n; rw [phaseCount]
    by_cases hb : (n : ℝ) / m ∈ Ioo alphaStar (1 - alphaStar) <;> simp [hb]
  rw [Finset.sum_congr rfl (fun n _ => h n), Finset.sum_add_distrib, Finset.sum_const,
    Nat.card_Ico, smul_eq_mul, mul_one, bandCount]

/-- The model index of `Ξ_{3,m}` at the circle level. This definition
encodes the `k=3` block structure — the anchor `ind_0 = 3` and the per-phase
`ind_α = 2 + 2·(reduced count)` (from `k=3_bracket` and `j_sym`) — as data.
The disk-chain identification is proved in `K3IndexComplete`; the geometric
EW quotient identification is supplied by `KarcherGeometricInvariants`. -/
def modelIndex (m : ℕ) : ℕ :=
  3 + ∑ n ∈ Finset.Ico 1 m, (2 + 2 * phaseCount ((n : ℝ) / m))

/-- **The staircase formula (model form).**  `modelIndex(m) = 4m − 1 + 2·#band`
for `m ≥ 1` — the closed form of Theorem `\ref{k=3}`, over the model index. -/
theorem modelIndex_eq (m : ℕ) (hm : 1 ≤ m) :
    modelIndex m = 4 * m - 1 + 2 * bandCount m := by
  rw [modelIndex, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul,
    ← Finset.mul_sum, reduced_staircase]
  omega

end KsIndex.Staircase
