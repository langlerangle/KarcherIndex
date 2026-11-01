module

public import KsIndexLean.ChainChartRotation
public import KsIndexLean.ChainPhaseFormFactor

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Closed character domain of the actual geometric copywise rotation. -/
def chainChartCharacterDomain (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ) : Submodule ℂ (ChainChartSpace k m) :=
  LinearMap.ker ((chainChartRotationLI k m θ hθ).toContinuousLinearMap -
    d • ContinuousLinearMap.id ℂ (ChainChartSpace k m)).toLinearMap

lemma isClosed_chainChartCharacterDomain (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ) :
    IsClosed (chainChartCharacterDomain k m θ hθ d : Set (ChainChartSpace k m)) :=
  ((chainChartRotationLI k m θ hθ).toContinuousLinearMap -
    d • ContinuousLinearMap.id ℂ (ChainChartSpace k m)).isClosed_ker

lemma mem_chainChartCharacterDomain_iff_coordinates (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ) (q : ChainChartSpace k m) :
    q ∈ chainChartCharacterDomain k m θ hθ d ↔ ∀ n,
      diskRotation θ (chainChartCoordinatesCLM k m q n) =
        d • chainChartCoordinatesCLM k m q n := by
  change chainChartRotationLI k m θ hθ q - d • q = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h n
    have he := congrArg (fun r => chainChartCoordinatesCLM k m r n) h
    simpa only [chainChartRotation_coordinates, map_smul, Pi.smul_apply] using he
  · intro h
    apply chainChartCoordinates_injective k m
    funext n
    simpa only [chainChartRotation_coordinates, map_smul, Pi.smul_apply] using h n

/-- On a translation phase field, the rotation character is determined by its two base copies. -/
lemma chainPhase_character_iff_pair (k m : ℕ) [NeZero m] (c : ℂ) (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (d : ℂ)
    (q : chainChartPhaseDomain k m c) :
    q.val ∈ chainChartCharacterDomain k m θ hθ d ↔
      (chainPhasePairLinearMap k m c q).val ∈ pairCharacterDomain θ d := by
  rw [mem_chainChartCharacterDomain_iff_coordinates]
  change (∀ n, diskRotation θ (chainChartCoordinatesCLM k m q.val n) =
    d • chainChartCoordinatesCLM k m q.val n) ↔
    chainChartCoordinatesCLM k m q.val 1 ∈ weakCharacterDomain θ d ∧
    chainChartCoordinatesCLM k m q.val 0 ∈ weakCharacterDomain θ d
  simp only [mem_weakCharacterDomain]
  constructor
  · intro h
    exact ⟨h 1, h 0⟩
  · rintro ⟨h1, h0⟩ n
    have hq := chainPhase_coordinates_reconstruct k m c q
    have hn := congrFun hq n
    rw [← hn]
    change diskRotation θ (c ^ (n.val / 2) •
      if n.val % 2 = 0 then chainChartCoordinatesCLM k m q.val 0
      else chainChartCoordinatesCLM k m q.val 1) =
        d • (c ^ (n.val / 2) •
          if n.val % 2 = 0 then chainChartCoordinatesCLM k m q.val 0
          else chainChartCoordinatesCLM k m q.val 1)
    rw [map_smul]
    split_ifs
    · rw [h0, smul_comm]
    · rw [h1, smul_comm]

end KsIndex.Trace
