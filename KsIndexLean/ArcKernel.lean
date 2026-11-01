module

/-
KsIndexLean — ArcKernel: finite trigonometric kernel identities for the square-wave
series used in the circle sign-multiplication identities.

  chat'_refl       — chat'(−d−1) = chat' d
  kernel_sin       — the sine part over the (d↦−d−1)-symmetric window vanishes
  kernel_cos       — the cosine part is (4/π)∑_{k≤N}(−1)^k cos((2k+1)x)/(2k+1)
  window_reindex   — ∑_{n∈Icc(m−N)(m+N+1)} f n = ∑_{d∈Icc(−N−1)N} f(m−d)
  kernel_total     — ∑_{n∈window} chat'(m−n) cos((2n+½)x) = cos((2m+3/2)x)·T_N(x)

`chat' d = 2/π·(−1)^d/(2d+1)` is definitionally `CircleQ.chat d`.

Statements and proof sketches by Xi (Fable 5); proofs by Aristotle (Harmonic),
project 6911b25f-93a4-443f-b245-8844e01a4660. This module imports only Mathlib.
-/
public import Mathlib

@[expose] public section


noncomputable section

open Real

namespace KsIndex.ArcKernel

/-- The square-wave kernel `chat' d = 2/π · (−1)^d / (2d+1)`. -/
def chat' (d : ℤ) : ℝ := 2 / π * (-1 : ℝ) ^ d / (2 * (d : ℝ) + 1)

/-- Reflection symmetry `chat'(−d−1) = chat' d`: both the numerator sign
and the denominator change sign under the reflection. -/
theorem chat'_refl (d : ℤ) : chat' (-d - 1) = chat' d := by
  have hpow : ((-1 : ℝ)) ^ (-d - 1) = -((-1 : ℝ) ^ d) := by
    rcases Int.even_or_odd d with he | ho
    · rw [he.neg_one_zpow]
      have hodd : Odd (-d - 1) := by rcases he with ⟨k, hk⟩; exact ⟨-k - 1, by omega⟩
      rw [hodd.neg_one_zpow]
    · rw [ho.neg_one_zpow]
      have heven : Even (-d - 1) := by rcases ho with ⟨k, hk⟩; exact ⟨-k - 1, by omega⟩
      rw [heven.neg_one_zpow]; ring
  have hden : (2 * (((-d - 1 : ℤ)) : ℝ) + 1) = -(2 * (d : ℝ) + 1) := by push_cast; ring
  unfold chat'
  rw [hpow, hden]
  field_simp

/-- Auxiliary: the involution `d ↦ -d-1` reindexes the symmetric window `Icc (-N-1) N`. -/
theorem chat'_window_reflect (N : ℕ) (g : ℤ → ℝ) :
    ∑ d ∈ Finset.Icc (-(N : ℤ) - 1) (N : ℤ), g d
      = ∑ d ∈ Finset.Icc (-(N : ℤ) - 1) (N : ℤ), g (-d - 1) := by
  refine Finset.sum_nbij' (i := fun d => -d - 1) (j := fun d => -d - 1) ?_ ?_ ?_ ?_ ?_ <;>
    intro a ha <;> simp only [Finset.mem_Icc] at ha ⊢ <;>
    first | omega | (congr 1; omega)

/-- The sine sum vanishes on `Icc (−N−1) N`: reflection `d ↦ −d−1`
preserves the kernel and negates the sine factor. -/
theorem kernel_sin (N : ℕ) (x : ℝ) :
    ∑ d ∈ Finset.Icc (-(N : ℤ) - 1) (N : ℤ), chat' d * Real.sin ((2 * (d : ℝ) + 1) * x) = 0 := by
  have h : ∑ d ∈ Finset.Icc (-(N : ℤ) - 1) (N : ℤ), chat' d * Real.sin ((2 * (d : ℝ) + 1) * x)
      = -∑ d ∈ Finset.Icc (-(N : ℤ) - 1) (N : ℤ), chat' d * Real.sin ((2 * (d : ℝ) + 1) * x) := by
    conv_lhs => rw [chat'_window_reflect N (fun d => chat' d * Real.sin ((2 * (d : ℝ) + 1) * x))]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _
    show chat' (-a - 1) * Real.sin ((2 * ((-a - 1 : ℤ) : ℝ) + 1) * x)
        = -(chat' a * Real.sin ((2 * (a : ℝ) + 1) * x))
    rw [chat'_refl]
    have harg : (2 * ((-a - 1 : ℤ) : ℝ) + 1) * x = -((2 * (a : ℝ) + 1) * x) := by push_cast; ring
    rw [harg, Real.sin_neg]; ring
  linarith

/-- Auxiliary: the nonnegative half of the window, rewritten as a `range` sum. -/
theorem kernel_cos_nonneg_half (N : ℕ) (x : ℝ) :
    ∑ d ∈ Finset.Icc (0 : ℤ) (N : ℤ), chat' d * Real.cos ((2 * (d : ℝ) + 1) * x)
      = 2 / π * ∑ k ∈ Finset.range (N + 1),
          (-1 : ℝ) ^ k * Real.cos ((2 * (k : ℝ) + 1) * x) / (2 * (k : ℝ) + 1) := by
  rw [Finset.mul_sum]
  refine (Finset.sum_nbij' (i := fun k : ℕ => (k : ℤ)) (j := fun d : ℤ => d.toNat)
    ?_ ?_ ?_ ?_ ?_).symm
  · intro a ha; simp only [Finset.mem_range, Finset.mem_Icc] at *; omega
  · intro a ha; simp only [Finset.mem_range, Finset.mem_Icc] at *; omega
  · intro a _; simp
  · intro a ha; simp only [Finset.mem_Icc] at ha; exact Int.toNat_of_nonneg ha.1
  · intro a _
    simp only [chat', zpow_natCast, Int.cast_natCast]
    ring

/-- The cosine sum on `Icc (−N−1) N` is the square-wave partial sum
`(4/π) ∑_{k=0}^{N} (−1)^k cos((2k+1)x)/(2k+1)`.
Reflection identifies the negative and nonnegative halves of the window. -/
theorem kernel_cos (N : ℕ) (x : ℝ) :
    ∑ d ∈ Finset.Icc (-(N : ℤ) - 1) (N : ℤ), chat' d * Real.cos ((2 * (d : ℝ) + 1) * x)
      = 4 / π * ∑ k ∈ Finset.range (N + 1),
          (-1 : ℝ) ^ k * Real.cos ((2 * (k : ℝ) + 1) * x) / (2 * (k : ℝ) + 1) := by
  have hsplit : Finset.Icc (-(N : ℤ) - 1) (N : ℤ)
      = Finset.Icc (-(N : ℤ) - 1) (-1) ∪ Finset.Icc (0 : ℤ) (N : ℤ) := by
    ext a; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc (-(N : ℤ) - 1) (-1)) (Finset.Icc (0 : ℤ) (N : ℤ)) := by
    rw [Finset.disjoint_left]
    intro a ha hb; simp only [Finset.mem_Icc] at ha hb; omega
  have hneg : ∑ d ∈ Finset.Icc (-(N : ℤ) - 1) (-1), chat' d * Real.cos ((2 * (d : ℝ) + 1) * x)
      = ∑ d ∈ Finset.Icc (0 : ℤ) (N : ℤ), chat' d * Real.cos ((2 * (d : ℝ) + 1) * x) := by
    refine (Finset.sum_nbij' (i := fun d : ℤ => -d - 1) (j := fun d : ℤ => -d - 1)
      ?_ ?_ ?_ ?_ ?_).symm
    · intro a ha; simp only [Finset.mem_Icc] at *; omega
    · intro a ha; simp only [Finset.mem_Icc] at *; omega
    · intro a _; show -(-a - 1) - 1 = a; omega
    · intro a _; show -(-a - 1) - 1 = a; omega
    · intro a _
      show chat' a * Real.cos ((2 * (a : ℝ) + 1) * x)
          = chat' (-a - 1) * Real.cos ((2 * ((-a - 1 : ℤ) : ℝ) + 1) * x)
      rw [chat'_refl]
      congr 1
      have harg : (2 * ((-a - 1 : ℤ) : ℝ) + 1) * x = -((2 * (a : ℝ) + 1) * x) := by
        push_cast; ring
      rw [harg, Real.cos_neg]
  rw [hsplit, Finset.sum_union hdisj, hneg, kernel_cos_nonneg_half]
  ring

/-- Reindex `Icc (m−N) (m+N+1)` as `Icc (−N−1) N` by `d = m−n`. -/
theorem window_reindex (m : ℤ) (N : ℕ) (f : ℤ → ℝ) :
    ∑ n ∈ Finset.Icc (m - (N : ℤ)) (m + (N : ℤ) + 1), f n
      = ∑ d ∈ Finset.Icc (-(N : ℤ) - 1) (N : ℤ), f (m - d) := by
  refine Finset.sum_nbij' (i := fun n => m - n) (j := fun d => m - d) ?_ ?_ ?_ ?_ ?_ <;>
    intro a ha <;> simp only [Finset.mem_Icc] at ha ⊢ <;>
    first | omega | (congr 1; omega)

/-- The shifted kernel sum factors as `cos((2m+3/2)x)` times the square-wave
partial sum. Reindexing and the cosine subtraction formula reduce it to
`kernel_cos` and the vanishing sine sum `kernel_sin`. -/
theorem kernel_total (m : ℤ) (N : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.Icc (m - (N : ℤ)) (m + (N : ℤ) + 1),
        chat' (m - n) * Real.cos ((2 * (n : ℝ) + 1 / 2) * x)
      = Real.cos ((2 * (m : ℝ) + 3 / 2) * x) *
        (4 / π * ∑ k ∈ Finset.range (N + 1),
          (-1 : ℝ) ^ k * Real.cos ((2 * (k : ℝ) + 1) * x) / (2 * (k : ℝ) + 1)) := by
  rw [window_reindex m N (fun n => chat' (m - n) * Real.cos ((2 * (n : ℝ) + 1 / 2) * x))]
  have step : ∀ d : ℤ, chat' (m - (m - d)) * Real.cos ((2 * ((m - d : ℤ) : ℝ) + 1 / 2) * x)
      = Real.cos ((2 * (m : ℝ) + 3 / 2) * x) * (chat' d * Real.cos ((2 * (d : ℝ) + 1) * x))
        + Real.sin ((2 * (m : ℝ) + 3 / 2) * x) * (chat' d * Real.sin ((2 * (d : ℝ) + 1) * x)) := by
    intro d
    have hm : m - (m - d) = d := by omega
    have harg : (2 * ((m - d : ℤ) : ℝ) + 1 / 2) * x
        = (2 * (m : ℝ) + 3 / 2) * x - (2 * (d : ℝ) + 1) * x := by push_cast; ring
    rw [hm, harg, Real.cos_sub]; ring
  simp only [step]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, kernel_sin, kernel_cos]
  ring

end KsIndex.ArcKernel
