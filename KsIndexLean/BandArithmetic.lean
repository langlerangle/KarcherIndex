module

/-
KsIndexLean — exact arithmetic for the open phase band and its resonant endpoints.

This is the counting step in the proof of [ksindexi] Theorem 1.8 (`k=3`), abstracted
from the spectral threshold: only `0 < a < 1/2` and `1 ≤ m` are used. The interval
endpoints stay open even when `m*a` is integral. The primary cardinality identity
has no natural subtraction; the usual floor formula is derived from it.

The endpoint count is arithmetic only. Interpreting endpoint phases as geometric
Jacobi fields requires the separate spectral/kernel correspondence.
-/
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic

@[expose] public section


noncomputable section

namespace KsIndex.BandArithmetic

open Finset

open Classical in
/-- The nonzero phases strictly inside the middle band. -/
def band (a : ℝ) (m : ℕ) : Finset ℕ :=
  (Ico 1 m).filter fun n => a < (n : ℝ) / m ∧ (n : ℝ) / m < 1 - a

open Classical in
/-- The nonzero phases at either endpoint of the middle band. -/
def endpoints (a : ℝ) (m : ℕ) : Finset ℕ :=
  (Ico 1 m).filter fun n => (n : ℝ) / m = a ∨ (n : ℝ) / m = 1 - a

/-- The floor fits strictly below the halfway point; this controls natural subtraction. -/
lemma two_floor_add_one_le {a : ℝ} {m : ℕ}
    (ha : 0 < a) (ha_half : a < 1 / 2) (hm : 1 ≤ m) :
    2 * ⌊(m : ℝ) * a⌋₊ + 1 ≤ m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hfloor := Nat.floor_le (show 0 ≤ (m : ℝ) * a by positivity)
  have hlt : (2 : ℝ) * ⌊(m : ℝ) * a⌋₊ < m := by nlinarith
  have : 2 * ⌊(m : ℝ) * a⌋₊ < m := by exact_mod_cast hlt
  omega

/-- The strict real lower inequality is exactly the floor successor bound. -/
lemma lower_iff {a : ℝ} {m n : ℕ} (ha : 0 < a) (hm : 1 ≤ m) :
    a < (n : ℝ) / m ↔ ⌊(m : ℝ) * a⌋₊ + 1 ≤ n := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [lt_div_iff₀ hmpos, mul_comm a, ← Nat.floor_lt (by positivity)]
  omega

/-- Reflect the strict upper inequality to the same lower inequality at `m-n`. -/
lemma upper_iff {a : ℝ} {m n : ℕ} (ha : 0 < a) (hm : 1 ≤ m) (hn : n ≤ m) :
    (n : ℝ) / m < 1 - a ↔ ⌊(m : ℝ) * a⌋₊ + 1 ≤ m - n := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← lower_iff ha hm, Nat.cast_sub hn, div_lt_iff₀ hmpos, lt_div_iff₀ hmpos]
  constructor <;> intro h <;> nlinarith

/-- An exact interval description, valid uniformly at and away from resonance. -/
theorem band_eq_Icc {a : ℝ} {m : ℕ}
    (ha : 0 < a) (ha_half : a < 1 / 2) (hm : 1 ≤ m) :
    band a m = Icc (⌊(m : ℝ) * a⌋₊ + 1) (m - ⌊(m : ℝ) * a⌋₊ - 1) := by
  classical
  have hq := two_floor_add_one_le ha ha_half hm
  ext n
  simp only [band, mem_filter, mem_Ico, mem_Icc]
  constructor
  · rintro ⟨⟨hn1, hnm⟩, hlo, hhi⟩
    have hl := (lower_iff ha hm).mp hlo
    have hh := (upper_iff ha hm hnm.le).mp hhi
    omega
  · rintro ⟨hlo, hhi⟩
    have hn1 : 1 ≤ n := by omega
    have hnm : n < m := by omega
    exact ⟨⟨hn1, hnm⟩, (lower_iff ha hm).mpr hlo,
      (upper_iff ha hm hnm.le).mpr (by omega)⟩

/-- Primary count identity: all subtraction and its truncation are eliminated. -/
theorem band_card_add {a : ℝ} {m : ℕ}
    (ha : 0 < a) (ha_half : a < 1 / 2) (hm : 1 ≤ m) :
    (band a m).card + 2 * ⌊(m : ℝ) * a⌋₊ + 1 = m := by
  rw [band_eq_Icc ha ha_half hm, Nat.card_Icc]
  have hq := two_floor_add_one_le ha ha_half hm
  omega

/-- The paper's open-band count, in natural-number floor notation. -/
theorem band_card {a : ℝ} {m : ℕ}
    (ha : 0 < a) (ha_half : a < 1 / 2) (hm : 1 ≤ m) :
    (band a m).card = m - 2 * ⌊(m : ℝ) * a⌋₊ - 1 := by
  have := band_card_add ha ha_half hm
  omega

/-- With positive phase and period, integer resonance means equality to the natural floor. -/
lemma resonance_iff_floor {a : ℝ} {m : ℕ} (ha : 0 < a) (hm : 1 ≤ m) :
    (∃ z : ℤ, (m : ℝ) * a = z) ↔ (⌊(m : ℝ) * a⌋₊ : ℝ) = (m : ℝ) * a := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · rintro ⟨z, hz⟩
    have hz0 : 0 ≤ z := by exact_mod_cast (show (0 : ℝ) ≤ z by rw [← hz]; positivity)
    lift z to ℕ using hz0
    simp [hz]
  · intro h
    exact ⟨(⌊(m : ℝ) * a⌋₊ : ℤ), by simpa using h.symm⟩

/-- At resonance, both endpoint indices are interior and distinct. -/
lemma resonant_indices {a : ℝ} {m : ℕ}
    (ha : 0 < a) (ha_half : a < 1 / 2) (hm : 1 ≤ m)
    (hres : ∃ z : ℤ, (m : ℝ) * a = z) :
    let q := ⌊(m : ℝ) * a⌋₊
    q ∈ Ico 1 m ∧ m - q ∈ Ico 1 m ∧ q ≠ m - q := by
  dsimp
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hqreal := (resonance_iff_floor ha hm).mp hres
  have hqpos : 0 < ⌊(m : ℝ) * a⌋₊ := by
    exact_mod_cast (show (0 : ℝ) < ⌊(m : ℝ) * a⌋₊ by rw [hqreal]; positivity)
  have hq := two_floor_add_one_le ha ha_half hm
  simp only [mem_Ico]
  omega

/-- The two actual endpoint indices at resonance. -/
theorem endpoints_eq_pair {a : ℝ} {m : ℕ}
    (ha : 0 < a) (ha_half : a < 1 / 2) (hm : 1 ≤ m)
    (hres : ∃ z : ℤ, (m : ℝ) * a = z) :
    endpoints a m = {⌊(m : ℝ) * a⌋₊, m - ⌊(m : ℝ) * a⌋₊} := by
  classical
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hqreal := (resonance_iff_floor ha hm).mp hres
  obtain ⟨hqmem, hrmem, _⟩ := resonant_indices ha ha_half hm hres
  have hqle : ⌊(m : ℝ) * a⌋₊ ≤ m := (mem_Ico.mp hqmem).2.le
  have hlo (n : ℕ) : (n : ℝ) / m = a ↔ n = ⌊(m : ℝ) * a⌋₊ := by
    rw [div_eq_iff (ne_of_gt hmpos)]
    constructor
    · intro hn
      exact_mod_cast (show (n : ℝ) = ⌊(m : ℝ) * a⌋₊ by nlinarith)
    · intro hn
      rw [hn, hqreal, mul_comm]
  have hhi (n : ℕ) : (n : ℝ) / m = 1 - a ↔ n = m - ⌊(m : ℝ) * a⌋₊ := by
    rw [div_eq_iff (ne_of_gt hmpos)]
    constructor
    · intro hn
      apply Nat.cast_injective (R := ℝ)
      rw [Nat.cast_sub hqle]
      nlinarith
    · intro hn
      rw [hn, Nat.cast_sub hqle, hqreal]
      ring
  ext n
  simp only [endpoints, mem_filter, hlo, hhi, mem_insert, mem_singleton]
  constructor
  · exact fun h => h.2
  · rintro (rfl | rfl)
    · exact ⟨hqmem, Or.inl rfl⟩
    · exact ⟨hrmem, Or.inr rfl⟩

/-- Without integer resonance neither endpoint is a sampled phase. -/
theorem endpoints_eq_empty {a : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hres : ¬ ∃ z : ℤ, (m : ℝ) * a = z) : endpoints a m = ∅ := by
  classical
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  apply eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨_, hn | hn⟩ := mem_filter.mp hn
  · apply hres
    refine ⟨(n : ℤ), ?_⟩
    have := (div_eq_iff (ne_of_gt hmpos)).mp hn
    push_cast
    nlinarith
  · apply hres
    refine ⟨(m : ℤ) - n, ?_⟩
    have := (div_eq_iff (ne_of_gt hmpos)).mp hn
    push_cast
    nlinarith

open Classical in
/-- Exactly two endpoint phases occur at resonance, and none otherwise. -/
theorem endpoints_card {a : ℝ} {m : ℕ}
    (ha : 0 < a) (ha_half : a < 1 / 2) (hm : 1 ≤ m) :
    (endpoints a m).card = if ∃ z : ℤ, (m : ℝ) * a = z then 2 else 0 := by
  classical
  by_cases hres : ∃ z : ℤ, (m : ℝ) * a = z
  · rw [if_pos hres, endpoints_eq_pair ha ha_half hm hres]
    exact card_pair ((resonant_indices ha ha_half hm hres).2.2)
  · rw [if_neg hres, endpoints_eq_empty hm hres, card_empty]

/-- Endpoint phases are excluded from the open band, including at resonance. -/
theorem disjoint_band_endpoints (a : ℝ) (m : ℕ) :
    Disjoint (band a m) (endpoints a m) := by
  classical
  apply disjoint_left.mpr
  intro n hn he
  obtain ⟨_, hlo, hhi⟩ := mem_filter.mp hn
  obtain ⟨_, he | he⟩ := mem_filter.mp he
  · exact (ne_of_gt hlo) he
  · exact (ne_of_lt hhi) he

open Classical in
/-- Arithmetic bookkeeping only: the baseline 3 and multiplicity 2 are supplied
by the caller. This does not identify the count with geometric nullity. -/
theorem baseline_add_two_endpoints {a : ℝ} {m : ℕ}
    (ha : 0 < a) (ha_half : a < 1 / 2) (hm : 1 ≤ m) :
    3 + 2 * (endpoints a m).card =
      if ∃ z : ℤ, (m : ℝ) * a = z then 7 else 3 := by
  classical
  rw [endpoints_card ha ha_half hm]
  split_ifs <;> norm_num

end KsIndex.BandArithmetic
