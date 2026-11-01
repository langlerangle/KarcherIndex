module

public import KsIndexLean.PuncturedSlitSmoothApproximation
public import KsIndexLean.ChainChartRotation

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Rotation on the original CcSmooth carrier, with its root condition. -/
def ccSmoothRotation (k m : ℕ) (θ : ℝ) (hθ : Complex.exp (θ * Complex.I) ^ k = 1) :
    Module.End ℂ (KsIndex.Surface.CcSmooth k m) where
  toFun u := ⟨KsIndex.SurfaceSym.rotF (Complex.exp (θ * Complex.I)) u.val,
    KsIndex.SurfaceSym.rotF_mem_CcSmooth (Complex.norm_exp_ofReal_mul_I θ) hθ u.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

lemma ccSmoothCopy_rotation {k m : ℕ} (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (u : KsIndex.Surface.CcSmooth k m)
    (n : ZMod (2 * m)) :
    ccSmoothCopy (ccSmoothRotation k m θ hθ u) n = diskRotation θ (ccSmoothCopy u n) := by
  apply valueCLM_injective
  apply Lp.ext
  have hcomp := (measurePreserving_planeRotation_disk θ).quasiMeasurePreserving.ae_eq_comp
    (ccSmoothCopy_value_ae u n)
  filter_upwards [ccSmoothCopy_value_ae (ccSmoothRotation k m θ hθ u) n,
    diskRotation_value_ae θ (ccSmoothCopy u n), hcomp] with z hz hr hc
  rw [hz, hr, hc]
  rfl

/-- Smooth rotation and weak-chart rotation are the same geometric operation
under the ORIGINAL source encoding. -/
lemma ccSmoothToChainChart_rotation (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (u : KsIndex.Surface.CcSmooth k m) :
    ccSmoothToChainChart k m (ccSmoothRotation k m θ hθ u) =
      chainChartRotationLI k m θ hθ (ccSmoothToChainChart k m u) := by
  apply chainChartCoordinates_injective k m
  rw [chainChartRotation_coordinates, ccSmoothToChainChart_coordinates,
    ccSmoothToChainChart_coordinates]
  funext n
  exact ccSmoothCopy_rotation θ hθ u n

/-- The exact translation phase survives smooth rotation pointwise. -/
lemma ccSmoothRotation_preserves_phase {k m : ℕ} (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (c : ℂ) (u : KsIndex.Surface.CcSmooth k m)
    (hu : ∀ n z, u.val (n + 2) z = c * u.val n z) :
    ∀ n z, (ccSmoothRotation k m θ hθ u).val (n + 2) z =
      c * (ccSmoothRotation k m θ hθ u).val n z := by
  intro n z
  exact hu n (Complex.exp (θ * Complex.I) * z)

/-- Iterating the rotations preserves the intertwining, as required for the
finite character projection. -/
lemma ccSmoothToChainChart_rotation_pow (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (r : ℕ) (u : KsIndex.Surface.CcSmooth k m) :
    ccSmoothToChainChart k m ((ccSmoothRotation k m θ hθ ^ r) u) =
      ((chainChartRotationLI k m θ hθ).toLinearMap ^ r) (ccSmoothToChainChart k m u) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [pow_succ', Module.End.mul_apply, ccSmoothToChainChart_rotation, ih]
    rfl

end KsIndex.Trace
