module

public import KsIndexLean.ChainChartConverse

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

lemma carrier_chartH1_disk (u : ComplexH1) : ChartH1 disk (valueCLM u) :=
  ⟨Lp.memLp _, joinedDiskJet u u 1,
    (joinedDisk_inner_disk_weak u u 1).congr_ae (joinedDiskValue_disk_ae u u 1),
    memLp_joinedDiskJet_disk u u 1⟩

/-- Raw functions in the original cyclic copy and seam-chart convention. -/
def ChainChartFunctions (k m : ℕ) :=
  {f : ZMod (2 * m) → ℂ → ℂ // (∀ n, ChartH1 disk (f n)) ∧
    ∀ n, ChartH1 (extendedSeamDomain (seamBoundary k m n) (isOpen_seamBoundary k m n))
      (Surface.glue f n)}

def chainChartSetoid (k m : ℕ) : Setoid (ChainChartFunctions k m) where
  r f g := ∀ n, f.val n =ᵐ[volume.restrict (disk : Set ℂ)] g.val n
  iseqv := ⟨fun _ _ => Filter.EventuallyEq.rfl, fun h n => (h n).symm,
    fun h₁ h₂ n => (h₁ n).trans (h₂ n)⟩

def ChainChartSpace (k m : ℕ) := Quotient (chainChartSetoid k m)

def weakChainFunction (k m : ℕ) [NeZero m] (u : weakDiskChain k m) :
    ChainChartFunctions k m :=
  ⟨fun n => (valueCLM (u.val n) : ℂ → ℂ), fun n => carrier_chartH1_disk _, by
    intro n
    obtain ⟨J, hJ, hL⟩ := (mem_weakDiskChain_iff_surface_charts k m u.val).mp u.property n
    exact ⟨surface_chart_value_memLp k u.val n, J, hJ, hL⟩⟩

def weakChainClass (k m : ℕ) [NeZero m] (u : weakDiskChain k m) : ChainChartSpace k m :=
  Quotient.mk _ (weakChainFunction k m u)

lemma weakChainClass_injective (k m : ℕ) [NeZero m] :
    Function.Injective (weakChainClass k m) := by
  intro u v h
  have he := Quotient.exact h
  apply Subtype.ext
  funext n
  exact valueCLM_injective (Lp.ext (he n))

lemma weakChainClass_surjective (k m : ℕ) [NeZero m] :
    Function.Surjective (weakChainClass k m) := by
  intro Q
  induction Q using Quotient.inductionOn with
  | h f =>
    obtain ⟨u, hu, _⟩ := chain_chart_reconstruction k m f.val f.property.1 f.property.2
    exact ⟨u, Quotient.sound hu⟩

/-- The genuine cyclic chartwise weak quotient has exactly the weak disk-chain carriers. -/
def weakChainChartEquiv (k m : ℕ) [NeZero m] : weakDiskChain k m ≃ ChainChartSpace k m :=
  Equiv.ofBijective (weakChainClass k m)
    ⟨weakChainClass_injective k m, weakChainClass_surjective k m⟩

end KsIndex.Trace
