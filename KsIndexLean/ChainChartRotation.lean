module

public import KsIndexLean.ArcTraceRotation
public import KsIndexLean.ChainChartShift

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma weakDiskChain_rotation_mem (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (u : weakDiskChain k m) :
    (fun n => diskRotation θ (u.val n)) ∈ weakDiskChain k m := by
  rw [mem_weakDiskChain]
  intro n
  have hu := (mem_weakDiskChain k m u.val).mp u.property n
  rw [seamBoundary_eq_boundaryArc] at hu ⊢
  have h := arcTrace_rotation_phase _ (measurableSet_boundaryArc _ _) θ
    (circleRotate_boundaryArc_preimage k _ θ hθ) 1 (u.val n) (u.val (n + 1))
    (by simpa using hu)
  simpa using h

lemma diskRotation_family_norm {m : ℕ} [NeZero m] (θ : ℝ)
    (u : ZMod (2 * m) → ComplexH1) : ‖fun n => diskRotation θ (u n)‖ = ‖u‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
    intro n
    rw [(diskRotation θ).norm_map]
    exact norm_le_pi_norm u n
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro n
    simpa only [LinearIsometry.norm_map] using
      norm_le_pi_norm (fun j => diskRotation θ (u j)) n

def weakChainRotationLI (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) : weakDiskChain k m →ₗᵢ[ℂ] weakDiskChain k m where
  toFun u := ⟨fun n => diskRotation θ (u.val n), weakDiskChain_rotation_mem k m θ hθ u⟩
  map_add' u v := by
    apply Subtype.ext
    funext n
    exact (diskRotation θ).map_add (u.val n) (v.val n)
  map_smul' c u := by
    apply Subtype.ext
    funext n
    exact (diskRotation θ).map_smul c (u.val n)
  norm_map' u := diskRotation_family_norm θ u.val

def chainChartRotationLI (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) :
    ChainChartSpace k m →ₗᵢ[ℂ] ChainChartSpace k m :=
  (chainChartLinearIsometryEquiv k m).symm.toLinearIsometry.comp
    ((weakChainRotationLI k m θ hθ).comp (chainChartLinearIsometryEquiv k m).toLinearIsometry)

lemma chainChartRotation_coordinates (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (q : ChainChartSpace k m) :
    chainChartCoordinatesCLM k m (chainChartRotationLI k m θ hθ q) =
      fun n => diskRotation θ (chainChartCoordinatesCLM k m q n) := by
  change ((chainChartLinearIsometryEquiv k m)
    ((chainChartLinearIsometryEquiv k m).symm
      (weakChainRotationLI k m θ hθ (chainChartLinearIsometryEquiv k m q)))).val = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma chainChartRotation_shift_commute (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (q : ChainChartSpace k m) :
    chainChartRotationLI k m θ hθ (chainChartShiftLI k m q) =
      chainChartShiftLI k m (chainChartRotationLI k m θ hθ q) := by
  apply chainChartCoordinates_injective k m
  simp only [chainChartRotation_coordinates, chainChartShift_coordinates]

lemma chainChartRotation_preserves_phase (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (c : ℂ) (q : chainChartPhaseDomain k m c) :
    chainChartRotationLI k m θ hθ q.val ∈ chainChartPhaseDomain k m c := by
  rw [mem_chainChartPhaseDomain, ← chainChartRotation_shift_commute,
    (mem_chainChartPhaseDomain k m c q.val).mp q.property, map_smul]

/-- Actual same-sign planar pullback on each recovered weak copy. -/
lemma chainChartRotation_value_ae (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (q : ChainChartSpace k m)
    (n : ZMod (2 * m)) :
    (valueCLM (chainChartCoordinatesCLM k m (chainChartRotationLI k m θ hθ q) n) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)]
        (valueCLM (chainChartCoordinatesCLM k m q n) : ℂ → ℂ) ∘ planeRotation θ := by
  rw [chainChartRotation_coordinates]
  exact diskRotation_value_ae θ _

/-- The paper's negative-angle rotation satisfies the required arc-invariance hypothesis. -/
lemma paperRotation_root (k : ℕ) (hk : 0 < k) :
    Complex.exp ((-(2 * Real.pi) / k : ℝ) * Complex.I) ^ k = 1 := by
  simpa only [SurfaceSym.rotUnit, Circle.coe_exp] using SurfaceSym.rotUnit_pow hk

def paperChainChartRotationLI (k m : ℕ) [NeZero m] (hk : 0 < k) :
    ChainChartSpace k m →ₗᵢ[ℂ] ChainChartSpace k m :=
  chainChartRotationLI k m (-(2 * Real.pi) / k) (paperRotation_root k hk)

end KsIndex.Trace
