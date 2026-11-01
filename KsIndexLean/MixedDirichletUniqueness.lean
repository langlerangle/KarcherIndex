module

public import KsIndexLean.MixedArcWeight

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

/-- A full Dirichlet eigenfunction cannot also satisfy either mixed weak
equation. The free-arc normal condition is derived using a smooth positive
weight times the constructed normal polynomial. -/
theorem sphericalEigen_dirichlet_mixed_eq_zero {k : ℕ} (hk : 0 < k)
    (lam : ℝ) (b : Bool) (u : ComplexH1) (ht : u ∈ zeroTraceDomain Set.univ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (hm : ∀ v ∈ mixedTraceDomain k b (!b), weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) : u = 0 := by
  obtain ⟨G, hG, hGP⟩ := dirichletNormalPolynomial_has_smooth_extension k lam u ht hu
  have hz := sphericalEigen_normal_zero_of_weighted_test k lam u ht hu G hG hGP
    (mixedArcWeight k b) (mixedArcWeight_smooth k b) (fun w => mixedArcWeight_nonneg k b w)
    ((spherical_eigen_equation_iff _ lam u _).mp
      (hm _ (mixedArcWeight_test_mem k b G hG)))
  refine sphericalEigen_dirichlet_normal_openArc_eq_zero k lam u ht hu
    (boundaryArc k (if b then 1 else 0)) (isOpen_boundaryArc _ _) ?_ ?_
  · cases b
    · exact boundaryArc_zero_nonempty hk
    · exact boundaryArc_one_nonempty k
  · filter_upwards [ae_restrict_mem (measurableSet_boundaryArc k (if b then 1 else 0))] with w hw
    exact hz w (mixedArcWeight_pos k b w hw)

end KsIndex.Trace
