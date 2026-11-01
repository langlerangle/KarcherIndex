module

public import KsIndexLean.InvariantCutoff
public import Mathlib.Topology.PartitionOfUnity

@[expose] public section


open Set Filter Topology
open scoped ContDiff BigOperators
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket

/-- Finite algebraic partition weights preserve the support of each input cutoff. -/
def invariantPartitionWeight {ι : Type*} [LinearOrder ι] (t : Finset ι) (χ : ι → ℂ → ℝ)
    (i : ι) (z : ℂ) : ℝ := by
  classical
  exact χ i z * ∏ j ∈ t with j < i, (1 - χ j z)

lemma invariantPartitionWeight_support {ι : Type*} [LinearOrder ι] (t : Finset ι)
    (χ : ι → ℂ → ℝ) (i : ι) :
    tsupport (invariantPartitionWeight t χ i) ⊆ tsupport (χ i) :=
  tsupport_mul_subset_left

lemma invariantPartitionWeight_compact {ι : Type*} [LinearOrder ι] (t : Finset ι)
    {χ : ι → ℂ → ℝ} (i : ι) (hc : HasCompactSupport (χ i)) :
    HasCompactSupport (invariantPartitionWeight t χ i) := hc.mul_right

lemma invariantPartitionWeight_smooth {ι : Type*} [LinearOrder ι] (t : Finset ι)
    {χ : ι → ℂ → ℝ} (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (i : ι) :
    ContDiff ℝ ∞ (invariantPartitionWeight t χ i) := by
  exact (hχ i).mul (contDiff_prod fun j _ => contDiff_const.sub (hχ j))

lemma invariantPartitionWeight_invariant {ι : Type*} [LinearOrder ι] (t : Finset ι)
    {χ : ι → ℂ → ℝ} (hi : ∀ i z, χ i (σ z) = χ i z) (i : ι) (z : ℂ) :
    invariantPartitionWeight t χ i (σ z) = invariantPartitionWeight t χ i z := by
  simp only [invariantPartitionWeight, hi]

lemma invariantPartitionWeight_sum {ι : Type*} [LinearOrder ι] (t : Finset ι)
    (χ : ι → ℂ → ℝ) (z : ℂ) :
    ∑ i ∈ t, invariantPartitionWeight t χ i z = 1 - ∏ i ∈ t, (1 - χ i z) := by
  have hh := Finset.prod_one_sub_ordered t (fun i => χ i z)
  simp only [invariantPartitionWeight] at ⊢
  linarith

lemma invariantPartitionWeight_sum_one_near {ι : Type*} [LinearOrder ι] (t : Finset ι)
    (χ : ι → ℂ → ℝ) {p : ℂ} {i : ι} (hi : i ∈ t) (hχ : χ i =ᶠ[𝓝 p] 1) :
    (fun z => ∑ j ∈ t, invariantPartitionWeight t χ j z) =ᶠ[𝓝 p] 1 := by
  filter_upwards [hχ] with z hz
  rw [invariantPartitionWeight_sum]
  have hp : ∏ j ∈ t, (1 - χ j z) = 0 :=
    Finset.prod_eq_zero hi (by simpa only [Pi.one_apply] using sub_eq_zero.mpr hz.symm)
  simpa only [Pi.one_apply] using (by rw [hp]; ring : (1 : ℝ) - ∏ j ∈ t, (1 - χ j z) = 1)

end KsIndex.Trace
