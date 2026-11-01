module

public import KsIndexLean.FiniteTestDecomposition

@[expose] public section


open Set MeasureTheory TopologicalSpace
open scoped ContDiff Distributions

noncomputable section
namespace KsIndex.Trace

lemma lineDeriv_finite_test_sum {ι : Type*} [Fintype ι] (U : ι → Opens ℂ)
    (ψ : ∀ i, 𝓓(U i, ℝ)) {Ω : Opens ℂ} (φ : 𝓓(Ω, ℝ))
    (hφ : (φ : ℂ → ℝ) = fun z => ∑ i, ψ i z) (z d : ℂ) :
    lineDeriv ℝ (φ : ℂ → ℝ) z d = ∑ i, lineDeriv ℝ (ψ i : ℂ → ℝ) z d := by
  rw [(φ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv, hφ,
    fderiv_fun_sum (fun i _ => (ψ i).contDiff.differentiable (by simp) z)]
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact ((ψ i).contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv.symm

/-- Finite integral exchange is justified by the local test-product integrability. -/
theorem weak_identity_of_finite_cover {ι : Type*} [Finite ι]
    (U : ι → Opens ℂ) {u g : ℂ → ℂ} (d : ℂ)
    (h : ∀ i, TauCeti.HasWeakLineDerivOn volume (U i) u g d)
    {Ω : Opens ℂ} (φ : 𝓓(Ω, ℝ))
    (hc : tsupport (φ : ℂ → ℝ) ⊆ ⋃ i, (U i : Set ℂ)) :
    (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z d • u z) = -∫ z, (φ : ℂ → ℝ) z • g z := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  obtain ⟨ψ, hψ⟩ := finite_test_decomposition U φ hc
  have hL : ∀ i, Integrable (fun z => lineDeriv ℝ (ψ i : ℂ → ℝ) z d • u z) :=
    fun i => TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
      (h i).locallyIntegrableOn (ψ i) d
  have hR : ∀ i, Integrable (fun z => (ψ i : ℂ → ℝ) z • g z) :=
    fun i => TauCeti.integrable_smul_of_locallyIntegrableOn
      (h i).locallyIntegrableOn_deriv (ψ i)
  calc
    _ = ∫ z, ∑ i, lineDeriv ℝ (ψ i : ℂ → ℝ) z d • u z := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change lineDeriv ℝ (φ : ℂ → ℝ) z d • u z =
          ∑ i, lineDeriv ℝ (ψ i : ℂ → ℝ) z d • u z
        rw [lineDeriv_finite_test_sum U ψ φ hψ z d, Finset.sum_smul]
    _ = ∑ i, ∫ z, lineDeriv ℝ (ψ i : ℂ → ℝ) z d • u z :=
      integral_finsetSum _ (fun i _ => hL i)
    _ = ∑ i, -(∫ z, (ψ i : ℂ → ℝ) z • g z) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (h i).integral_lineDeriv_smul_eq_neg_integral_smul (ψ i)
    _ = -(∫ z, ∑ i, (ψ i : ℂ → ℝ) z • g z) := by
      rw [integral_finsetSum _ (fun i _ => hR i), Finset.sum_neg_distrib]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change (∑ i, (ψ i : ℂ → ℝ) z • g z) = φ z • g z
        rw [← Finset.sum_smul, congrFun hψ z]

end KsIndex.Trace
