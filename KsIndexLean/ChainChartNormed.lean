module

public import KsIndexLean.ChainChartQuotient
public import Mathlib.Analysis.Normed.Module.TransferInstance

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

instance chainChartNormedAddCommGroup (k m : ℕ) [NeZero m] :
    NormedAddCommGroup (ChainChartSpace k m) :=
  (weakChainChartEquiv k m).symm.normedAddCommGroup
instance chainChartModule (k m : ℕ) [NeZero m] : Module ℂ (ChainChartSpace k m) :=
  (weakChainChartEquiv k m).symm.addEquiv.module ℂ
instance chainChartNormedSpace (k m : ℕ) [NeZero m] : NormedSpace ℂ (ChainChartSpace k m) :=
  (weakChainChartEquiv k m).symm.addEquiv.normedSpace ℂ

/-- The original cyclic chart quotient with the finite disk product graph norm. -/
def chainChartLinearIsometryEquiv (k m : ℕ) [NeZero m] :
    ChainChartSpace k m ≃ₗᵢ[ℂ] weakDiskChain k m where
  toLinearEquiv := (weakChainChartEquiv k m).symm.addEquiv.linearEquiv ℂ
  norm_map' _ := rfl

instance chainChartCompleteSpace (k m : ℕ) [NeZero m] : CompleteSpace (ChainChartSpace k m) := by
  let : CompleteSpace (weakDiskChain k m) := (isClosed_weakDiskChain k m).completeSpace_coe
  exact (chainChartLinearIsometryEquiv k m).toIsometryEquiv.completeSpace

/-- Continuous recovery in the original ZMod (2*m) copy order. -/
def chainChartCoordinatesCLM (k m : ℕ) [NeZero m] :
    ChainChartSpace k m →L[ℂ] (ZMod (2 * m) → ComplexH1) :=
  (weakDiskChain k m).subtypeL.comp
    (chainChartLinearIsometryEquiv k m).toContinuousLinearEquiv.toContinuousLinearMap

lemma chainChartCoordinates_class (k m : ℕ) [NeZero m] (u : weakDiskChain k m) :
    chainChartCoordinatesCLM k m (weakChainClass k m u) = u.val := by
  change ((weakChainChartEquiv k m).symm (weakChainChartEquiv k m u)).val = u.val
  rw [Equiv.symm_apply_apply]

lemma chainChartCoordinates_seam (k m : ℕ) [NeZero m] (q : ChainChartSpace k m)
    (n : ZMod (2 * m)) :
    arcTrace (seamBoundary k m n) (chainChartCoordinatesCLM k m q n) =
      arcTrace (seamBoundary k m n) (chainChartCoordinatesCLM k m q (n + 1)) :=
  (mem_weakDiskChain k m _).mp ((chainChartLinearIsometryEquiv k m q).property) n

/-- The smooth energy carrier maps linearly into the cyclic chart quotient. -/
def energySmoothToChainChart (k m : ℕ) [NeZero m] :
    FaithfulInjection.EnergySmooth k m →ₗ[ℂ] ChainChartSpace k m :=
  (chainChartLinearIsometryEquiv k m).symm.toLinearEquiv.toLinearMap.comp
    (energySmoothToWeakChain k m)

lemma energySmoothToChainChart_coordinates (k m : ℕ) [NeZero m]
    (u : FaithfulInjection.EnergySmooth k m) :
    chainChartCoordinatesCLM k m (energySmoothToChainChart k m u) = energySmoothCopy u := by
  exact chainChartCoordinates_class k m (energySmoothToWeakChain k m u)

lemma energySmoothToChainChart_value_ae (k m : ℕ) [NeZero m]
    (u : FaithfulInjection.EnergySmooth k m) (n : ZMod (2 * m)) :
    (valueCLM (chainChartCoordinatesCLM k m (energySmoothToChainChart k m u) n) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] u.val n := by
  rw [energySmoothToChainChart_coordinates]
  exact energySmoothCopy_value_ae u n

end KsIndex.Trace
