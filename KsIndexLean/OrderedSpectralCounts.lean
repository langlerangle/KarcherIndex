module

public import KsIndexLean.InfiniteSolutionOrdering

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Filter

/-- First index with value at least a level. For a monotone sequence, this equals
the number of indices with value strictly below the level. -/
def strictSpectralCount (ν : ℕ → ℝ) (hν : Tendsto ν atTop atTop) (L : ℝ) : ℕ :=
  Nat.find ((tendsto_atTop.1 hν L).exists)

/-- First index with value strictly above a level. For a monotone sequence, this equals
the number of indices with value at or below the level. -/
def weakSpectralCount (ν : ℕ → ℝ) (hν : Tendsto ν atTop atTop) (L : ℝ) : ℕ :=
  Nat.find ((hν.eventually (eventually_gt_atTop L)).exists)

lemma strictSpectralCount_spec (ν : ℕ → ℝ) (hν : Tendsto ν atTop atTop) (L : ℝ) :
    L ≤ ν (strictSpectralCount ν hν L) := by
  exact Nat.find_spec ((tendsto_atTop.1 hν L).exists)

lemma weakSpectralCount_spec (ν : ℕ → ℝ) (hν : Tendsto ν atTop atTop) (L : ℝ) :
    L < ν (weakSpectralCount ν hν L) := by
  exact Nat.find_spec ((hν.eventually (eventually_gt_atTop L)).exists)

lemma lt_level_iff_lt_strictSpectralCount (ν : ℕ → ℝ) (hν : Tendsto ν atTop atTop)
    (hmono : Monotone ν) (L : ℝ) (n : ℕ) :
    ν n < L ↔ n < strictSpectralCount ν hν L := by
  constructor
  · intro hn
    by_contra h
    have hle := hmono (Nat.le_of_not_gt h)
    have hs := strictSpectralCount_spec ν hν L
    linarith
  · intro hn
    exact lt_of_not_ge (Nat.find_min _ hn)

lemma le_level_iff_lt_weakSpectralCount (ν : ℕ → ℝ) (hν : Tendsto ν atTop atTop)
    (hmono : Monotone ν) (L : ℝ) (n : ℕ) :
    ν n ≤ L ↔ n < weakSpectralCount ν hν L := by
  constructor
  · intro hn
    by_contra h
    have hle := hmono (Nat.le_of_not_gt h)
    have hs := weakSpectralCount_spec ν hν L
    linarith
  · intro hn
    exact le_of_not_gt (Nat.find_min _ hn)

lemma strictSpectralCount_le_weakSpectralCount (ν : ℕ → ℝ) (hν : Tendsto ν atTop atTop)
    (L : ℝ) : strictSpectralCount ν hν L ≤ weakSpectralCount ν hν L :=
  Nat.find_min' _ (le_of_lt (weakSpectralCount_spec ν hν L))

/-- Strict sublevel indices form exactly a finite initial segment, with multiplicities. -/
lemma strictSpectralCount_set (ν : ℕ → ℝ) (hν : Tendsto ν atTop atTop)
    (hmono : Monotone ν) (L : ℝ) :
    {n | ν n < L} = (Finset.range (strictSpectralCount ν hν L) : Set ℕ) := by
  ext n
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_range]
  exact lt_level_iff_lt_strictSpectralCount ν hν hmono L n

lemma weakSpectralCount_set (ν : ℕ → ℝ) (hν : Tendsto ν atTop atTop)
    (hmono : Monotone ν) (L : ℝ) :
    {n | ν n ≤ L} = (Finset.range (weakSpectralCount ν hν L) : Set ℕ) := by
  ext n
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_range]
  exact le_level_iff_lt_weakSpectralCount ν hν hmono L n

/-- Equality-level indices occupy the interval between the strict and weak counts. -/
lemma eq_level_iff_count_interval (ν : ℕ → ℝ) (hν : Tendsto ν atTop atTop)
    (hmono : Monotone ν) (L : ℝ) (n : ℕ) :
    ν n = L ↔ strictSpectralCount ν hν L ≤ n ∧ n < weakSpectralCount ν hν L := by
  have hs := lt_level_iff_lt_strictSpectralCount ν hν hmono L n
  have hw := le_level_iff_lt_weakSpectralCount ν hν hmono L n
  constructor
  · intro he
    constructor
    · by_contra hn
      have := hs.mpr (Nat.lt_of_not_ge hn)
      linarith
    · exact hw.mp (le_of_eq he)
  · rintro ⟨hsn, hwn⟩
    have hle := hw.mpr hwn
    have hge : L ≤ ν n := by
      by_contra hn
      have := hs.mp (lt_of_not_ge hn)
      omega
    exact le_antisymm hle hge

end KsIndex.Spectral
