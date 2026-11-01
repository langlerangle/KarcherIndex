module

public import KsIndexLean.SolutionSpectralSpaces
public import TauCeti.Analysis.InnerProductSpace.Spectrum

@[expose] public section


noncomputable section
namespace KsIndex.Spectral.PositiveCompactSolution
open Module.End

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : KsIndex.Spectral.PositiveCompactSolution H)

/-- A complex Hilbert eigenbasis with positive real eigenvalues.
Its index type carries no ordering assertion and may be finite or empty. -/
lemma exists_positive_hilbertEigenbasis :
    ∃ (s : Set H) (b : HilbertBasis s ℂ H) (μ : s → ℝ),
      (∀ i, 0 < μ i) ∧ ∀ i, S.operator (b i) = (μ i : ℂ) • b i := by
  obtain ⟨s, b, ν, hb, _, hev⟩ :=
    ContinuousLinearMap.exists_hilbertBasis_forall_hasEigenvector_ne_zero
      S.compact S.symmetric (LinearMap.ker_eq_bot.mpr S.injective)
  refine ⟨s, b, fun i => (ν i).re, ?_, ?_⟩
  · intro i
    exact S.eigenvalue_re_pos (hasEigenvalue_of_hasEigenvector (hev i))
  · intro i
    have hr := S.eigenvalue_real (hasEigenvalue_of_hasEigenvector (hev i))
    rw [hr]
    have hbi : b i = (i : H) := congrFun hb i
    rw [hbi]
    exact mem_eigenspace_iff.mp (hev i).1

/-- Choice of a basis is explicit and carries no ordering assertion. -/
def eigenbasisIndex : Set H := S.exists_positive_hilbertEigenbasis.choose

def eigenbasis : HilbertBasis S.eigenbasisIndex ℂ H :=
  S.exists_positive_hilbertEigenbasis.choose_spec.choose

def basisEigenvalue : S.eigenbasisIndex → ℝ :=
  S.exists_positive_hilbertEigenbasis.choose_spec.choose_spec.choose

lemma basisEigenvalue_pos (i : S.eigenbasisIndex) : 0 < S.basisEigenvalue i :=
  S.exists_positive_hilbertEigenbasis.choose_spec.choose_spec.choose_spec.1 i

lemma eigenbasis_equation (i : S.eigenbasisIndex) :
    S.operator (S.eigenbasis i) = (S.basisEigenvalue i : ℂ) • S.eigenbasis i :=
  S.exists_positive_hilbertEigenbasis.choose_spec.choose_spec.choose_spec.2 i

lemma eigenbasis_expansion (f : H) :
    HasSum (fun i => (S.basisEigenvalue i : ℂ) • S.eigenbasis.repr f i • S.eigenbasis i)
      (S.operator f) :=
  ContinuousLinearMap.hasSum_smul_repr_of_apply_eq_smul S.operator S.eigenbasis
    (fun i => (S.basisEigenvalue i : ℂ)) S.eigenbasis_equation f

end KsIndex.Spectral.PositiveCompactSolution
