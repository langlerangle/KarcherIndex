module

public import KsIndexLean.DiskRotationForms

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma chainChartDirichlet_rotation (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (q r : ChainChartSpace k m) :
    chainChartDirichlet k m (chainChartRotationLI k m θ hθ q)
      (chainChartRotationLI k m θ hθ r) = chainChartDirichlet k m q r := by
  simp only [chainChartDirichlet, chainChartRotation_coordinates, dirichlet_diskRotation]

lemma chainChartJacobi_rotation (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (V : BoundedRealPotential)
    (hV : (fun z => V.V (planeRotation θ z)) =ᵐ[volume.restrict (disk : Set ℂ)] V.V)
    (q r : ChainChartSpace k m) :
    chainChartJacobi k m V (chainChartRotationLI k m θ hθ q)
      (chainChartRotationLI k m θ hθ r) = chainChartJacobi k m V q r := by
  simp only [chainChartJacobi, chainChartRotation_coordinates, weakJacobi_diskRotation θ V hV]

/-- The actual adopted surface potential satisfies the coefficient symmetry. -/
lemma chainChartSurfaceJacobi_rotation (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (q r : ChainChartSpace k m) :
    chainChartJacobi k m (surfacePotential k) (chainChartRotationLI k m θ hθ q)
      (chainChartRotationLI k m θ hθ r) = chainChartJacobi k m (surfacePotential k) q r :=
  chainChartJacobi_rotation k m θ hθ (surfacePotential k)
    (Filter.Eventually.of_forall (surfacePotential_rotation k θ)) q r

/-- Invariance under the precise negative-angle rotation used for the paper's characters. -/
lemma paperChainSurfaceJacobi_rotation (k m : ℕ) [NeZero m] (hk : 0 < k)
    (q r : ChainChartSpace k m) :
    chainChartJacobi k m (surfacePotential k) (paperChainChartRotationLI k m hk q)
      (paperChainChartRotationLI k m hk r) = chainChartJacobi k m (surfacePotential k) q r :=
  chainChartSurfaceJacobi_rotation k m _ (paperRotation_root k hk) q r

end KsIndex.Trace
