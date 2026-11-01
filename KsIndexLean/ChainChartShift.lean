module

public import KsIndexLean.ChainChartForms
public import KsIndexLean.SurfaceSym

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma seamBoundary_add_two (k m : ℕ) (n : ZMod (2 * m)) :
    seamBoundary k m (n + 2) = seamBoundary k m n := by
  unfold seamBoundary
  rw [SurfaceSym.seamArc_add_two]

lemma weakDiskChain_shift_mem (k m : ℕ) [NeZero m] (u : weakDiskChain k m) :
    (fun n => u.val (n + 2)) ∈ weakDiskChain k m := by
  rw [mem_weakDiskChain]
  intro n
  have h := (mem_weakDiskChain k m u.val).mp u.property (n + 2)
  rw [seamBoundary_add_two] at h
  simpa only [add_right_comm n 1 2] using h

/-- Reindexing by the paper's full-period translation preserves the graph product norm. -/
lemma copyShift_norm (m : ℕ) [NeZero m] (u : ZMod (2 * m) → ComplexH1) :
    ‖fun n => u (n + 2)‖ = ‖u‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr (fun n => norm_le_pi_norm u (n + 2))
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro n
    simpa using (norm_le_pi_norm (fun j => u (j + 2)) (n - 2))

/-- Shift by two half-period copies; no coordinate rotation or phase is inserted. -/
def weakChainShiftLI (k m : ℕ) [NeZero m] : weakDiskChain k m →ₗᵢ[ℂ] weakDiskChain k m where
  toFun u := ⟨fun n => u.val (n + 2), weakDiskChain_shift_mem k m u⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' u := copyShift_norm m u.val

def chainChartShiftLI (k m : ℕ) [NeZero m] : ChainChartSpace k m →ₗᵢ[ℂ] ChainChartSpace k m :=
  (chainChartLinearIsometryEquiv k m).symm.toLinearIsometry.comp
    ((weakChainShiftLI k m).comp (chainChartLinearIsometryEquiv k m).toLinearIsometry)

lemma chainChartShift_coordinates (k m : ℕ) [NeZero m] (q : ChainChartSpace k m) :
    chainChartCoordinatesCLM k m (chainChartShiftLI k m q) =
      fun n => chainChartCoordinatesCLM k m q (n + 2) := by
  change ((chainChartLinearIsometryEquiv k m)
    ((chainChartLinearIsometryEquiv k m).symm
      (weakChainShiftLI k m (chainChartLinearIsometryEquiv k m q)))).val = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma chainChartDirichlet_shift (k m : ℕ) [NeZero m] (q r : ChainChartSpace k m) :
    chainChartDirichlet k m (chainChartShiftLI k m q) (chainChartShiftLI k m r) =
      chainChartDirichlet k m q r := by
  simp only [chainChartDirichlet, chainChartShift_coordinates]
  exact Fintype.sum_equiv (Equiv.addRight (2 : ZMod (2 * m))) _ _ (fun _ => rfl)

lemma chainChartJacobi_shift (k m : ℕ) [NeZero m] (V : BoundedRealPotential)
    (q r : ChainChartSpace k m) :
    chainChartJacobi k m V (chainChartShiftLI k m q) (chainChartShiftLI k m r) =
      chainChartJacobi k m V q r := by
  simp only [chainChartJacobi, chainChartShift_coordinates]
  exact Fintype.sum_equiv (Equiv.addRight (2 : ZMod (2 * m))) _ _ (fun _ => rfl)

/-- Agreement with the paper's shift on every encoded smooth copy. -/
lemma chainChartShift_smooth_value_ae (k m : ℕ) [NeZero m]
    (u : FaithfulInjection.EnergySmooth k m) (n : ZMod (2 * m)) :
    (valueCLM (chainChartCoordinatesCLM k m
      (chainChartShiftLI k m (energySmoothToChainChart k m u)) n) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] SurfaceSym.shiftF u.val n := by
  rw [chainChartShift_coordinates]
  exact energySmoothToChainChart_value_ae k m u (n + 2)

/-- Closed eigenspace of the shift by two half-period copies.
A decomposition into these eigenspaces requires a separate argument. -/
def chainChartPhaseDomain (k m : ℕ) [NeZero m] (c : ℂ) : Submodule ℂ (ChainChartSpace k m) :=
  LinearMap.ker ((chainChartShiftLI k m).toContinuousLinearMap -
    c • ContinuousLinearMap.id ℂ (ChainChartSpace k m)).toLinearMap

lemma mem_chainChartPhaseDomain (k m : ℕ) [NeZero m] (c : ℂ) (q : ChainChartSpace k m) :
    q ∈ chainChartPhaseDomain k m c ↔ chainChartShiftLI k m q = c • q := by
  change chainChartShiftLI k m q - c • q = 0 ↔ _
  exact sub_eq_zero

lemma isClosed_chainChartPhaseDomain (k m : ℕ) [NeZero m] (c : ℂ) :
    IsClosed (chainChartPhaseDomain k m c : Set (ChainChartSpace k m)) :=
  ((chainChartShiftLI k m).toContinuousLinearMap -
    c • ContinuousLinearMap.id ℂ (ChainChartSpace k m)).isClosed_ker

lemma chainChartCoordinates_injective (k m : ℕ) [NeZero m] :
    Function.Injective (chainChartCoordinatesCLM k m) := by
  intro q r h
  apply (chainChartLinearIsometryEquiv k m).injective
  exact Subtype.ext h

lemma chainChartShift_iterate_coordinates (k m : ℕ) [NeZero m] (j : ℕ)
    (q : ChainChartSpace k m) (n : ZMod (2 * m)) :
    chainChartCoordinatesCLM k m ((chainChartShiftLI k m)^[j] q) n =
      chainChartCoordinatesCLM k m q (n + ((2 * j : ℕ) : ZMod (2 * m))) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', chainChartShift_coordinates]
    dsimp only
    rw [ih]
    push_cast
    ring

/-- One traversal of the m full-period copies is the identity. -/
lemma chainChartShift_period (k m : ℕ) [NeZero m] (q : ChainChartSpace k m) :
    (chainChartShiftLI k m)^[m] q = q := by
  apply chainChartCoordinates_injective k m
  funext n
  simpa only [ZMod.natCast_self, add_zero] using
    chainChartShift_iterate_coordinates k m m q n

lemma mem_chainChartPhaseDomain_iff_coordinates (k m : ℕ) [NeZero m]
    (c : ℂ) (q : ChainChartSpace k m) :
    q ∈ chainChartPhaseDomain k m c ↔ ∀ n,
      chainChartCoordinatesCLM k m q (n + 2) = c • chainChartCoordinatesCLM k m q n := by
  rw [mem_chainChartPhaseDomain]
  constructor
  · intro h n
    have he := congrArg (fun r => chainChartCoordinatesCLM k m r n) h
    simpa only [chainChartShift_coordinates, map_smul, Pi.smul_apply] using he
  · intro h
    apply chainChartCoordinates_injective k m
    funext n
    simpa only [chainChartShift_coordinates, map_smul, Pi.smul_apply] using h n

end KsIndex.Trace
