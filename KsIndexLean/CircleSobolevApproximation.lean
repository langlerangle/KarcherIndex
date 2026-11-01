module

public import KsIndexLean.CircleSobolevL2
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

@[expose] public section


/-! Finite Fourier approximations in every real Sobolev order. -/
noncomputable section
open Filter
namespace KsIndex.CircleSobolev

/-- Retain a finite set of physical Fourier modes. -/
def truncate (s : ℝ) (F : Finset ℤ) (u : Space s) : Space s :=
  ∑ n ∈ F, lp.single 2 n (u n)

@[simp] theorem truncate_apply (s : ℝ) (F : Finset ℤ) (u : Space s) (n : ℤ) :
    truncate s F u n = if n ∈ F then u n else 0 := by
  simp only [truncate, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single]

@[simp] theorem coeff_truncate (s : ℝ) (F : Finset ℤ) (u : Space s) (n : ℤ) :
    coeff s (truncate s F u) n = if n ∈ F then coeff s u n else 0 := by
  simp only [coeff, truncate_apply]
  split_ifs <;> simp

/-- Finite Fourier sums converge in the full H^s norm, not just coefficientwise. -/
theorem tendsto_truncate (s : ℝ) (u : Space s) :
    Tendsto (fun F : Finset ℤ => truncate s F u) atTop (nhds u) :=
  lp.hasSum_single (by norm_num) u

theorem norm_truncate_le (s : ℝ) (F : Finset ℤ) (u : Space s) :
    ‖truncate s F u‖ ≤ ‖u‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro n
  rw [truncate_apply]
  split_ifs <;> simp

/-- Truncation respects the paper's mean-zero constraint. -/
theorem truncate_mem_dotted (s : ℝ) (F : Finset ℤ) {u : Space s}
    (hu : u ∈ dotted s) : truncate s F u ∈ dotted s := by
  rw [mem_dotted, coeff_truncate]
  split_ifs
  · exact (mem_dotted s u).mp hu
  · rfl

/-- Truncation stays in each Fourier character space. -/
theorem truncate_mem_character (s : ℝ) (j k : ℤ) (F : Finset ℤ) {u : Space s}
    (hu : u ∈ character s j k) : truncate s F u ∈ character s j k := by
  rw [mem_character] at hu ⊢
  intro n hn
  rw [coeff_truncate]
  split_ifs
  · exact hu n hn
  · rfl

/-- The finite approximations converge on the same geometric L2 circle. -/
theorem tendsto_toL2_truncate {s : ℝ} (hs : 0 ≤ s) (u : Space s) :
    Tendsto (fun F : Finset ℤ => toL2 hs (truncate s F u)) atTop (nhds (toL2 hs u)) :=
  (toL2 hs).continuous.continuousAt.tendsto.comp (tendsto_truncate s u)

/-- Finite Fourier truncation as a bounded linear operator. -/
def truncateCLM (s : ℝ) (F : Finset ℤ) : Space s →L[ℂ] Space s :=
  ∑ n ∈ F, (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).comp
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n)

@[simp] theorem truncateCLM_apply (s : ℝ) (F : Finset ℤ) (u : Space s) :
    truncateCLM s F u = truncate s F u := by
  simp only [truncateCLM, sum_apply, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply]
  rfl

/-- Each finite Fourier truncation is compact. -/
theorem isCompactOperator_truncateCLM (s : ℝ) (F : Finset ℤ) :
    IsCompactOperator (truncateCLM s F) := by
  change truncateCLM s F ∈ compactOperator (RingHom.id ℂ) (Space s) (Space s)
  apply Submodule.sum_mem
  intro n hn
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n)).comp_clm
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n)

end KsIndex.CircleSobolev
