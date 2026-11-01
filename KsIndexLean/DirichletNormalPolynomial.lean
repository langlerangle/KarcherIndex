module

public import KsIndexLean.DirichletNormalFourierSupport

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

/-- The normal polynomial is built from the proved finite support of the
actual Dirichlet eigenfunction's canonical normal coefficients. -/
def dirichletNormalPolynomial (k : ℕ) (lam : ℝ) (u : ComplexH1)
    (ht : u ∈ zeroTraceDomain Set.univ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) : C(Circle₁, ℂ) :=
  circleFourierPolynomial
    (sphericalEigen_dirichlet_normal_finite_support k lam u ht hu).toFinset
    (eigenDiskNormalMode k lam u)

lemma dirichletNormalPolynomial_coefficient (k : ℕ) (lam : ℝ) (u : ComplexH1)
    (ht : u ∈ zeroTraceDomain Set.univ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) (n : ℤ) :
    circleCoefficientCLM n (ContinuousMap.toLp 2 circleMeasure ℂ
      (dirichletNormalPolynomial k lam u ht hu)) = eigenDiskNormalMode k lam u n := by
  rw [dirichletNormalPolynomial, circleFourierPolynomial_coefficient]
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  split_ifs with h
  · rfl
  · exact (not_ne_iff.mp h).symm

/-- This L2 representative is uniquely determined by the canonical normal
coefficients. Identification with the full weak boundary residual is separate. -/
lemma dirichletNormalPolynomial_unique (k : ℕ) (lam : ℝ) (u : ComplexH1)
    (ht : u ∈ zeroTraceDomain Set.univ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (f : Lp ℂ 2 circleMeasure) (hf : ∀ n, circleCoefficientCLM n f = eigenDiskNormalMode k lam u n) :
    f = ContinuousMap.toLp 2 circleMeasure ℂ (dirichletNormalPolynomial k lam u ht hu) := by
  apply circleFourierCLE.injective
  apply Subtype.ext
  funext n
  simp only [circleFourierCLE_apply]
  rw [← circleCoefficientCLM_apply, hf, ← circleCoefficientCLM_apply,
    dirichletNormalPolynomial_coefficient]

/-- Open-arc vanishing of the normal polynomial forces the entire Dirichlet
weak eigenfunction to vanish. This does not assume mixed tests already give
that vanishing. -/
theorem sphericalEigen_dirichlet_normal_openArc_eq_zero
    (k : ℕ) (lam : ℝ) (u : ComplexH1) (ht : u ∈ zeroTraceDomain Set.univ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (A : Set Circle₁) (hA : IsOpen A) (hne : A.Nonempty)
    (hz : (dirichletNormalPolynomial k lam u ht hu : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] 0) :
    u = 0 := by
  have hp : ∀ w : Circle₁, dirichletNormalPolynomial k lam u ht hu w = 0 := by
    simp only [dirichletNormalPolynomial, circleFourierPolynomial_apply]
    apply finite_fourier_eq_zero_of_open_ae _ _ A hA hne
    filter_upwards [hz] with w hw
    simpa only [dirichletNormalPolynomial, circleFourierPolynomial_apply, Pi.zero_apply] using hw
  have hp0 : dirichletNormalPolynomial k lam u ht hu = 0 := by
    ext w
    exact hp w
  apply sphericalEigen_eq_zero_of_boundary_cauchy k lam u hu ((mem_fullZeroTrace_iff u).mp ht)
  intro n
  rw [← dirichletNormalPolynomial_coefficient k lam u ht hu n, hp0, map_zero, map_zero]

end KsIndex.Trace
