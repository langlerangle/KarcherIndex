module

public import KsIndexLean.SolutionSpectralSpaces

@[expose] public section


noncomputable section
open Module.End
namespace KsIndex.Spectral.PositiveCompactSolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H] (S : KsIndex.Spectral.PositiveCompactSolution H)

/-- Finite sectors have a finite list indexed by complex dimension, including dimension zero. -/
def finiteEigenvalues : Fin (Module.finrank ℂ H) → ℝ := S.symmetric.eigenvalues rfl

def finiteEigenbasis : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
  S.symmetric.eigenvectorBasis rfl

lemma finiteEigenvalues_antitone : Antitone S.finiteEigenvalues :=
  S.symmetric.eigenvalues_antitone rfl

lemma finiteEigenvalues_pos (i : Fin (Module.finrank ℂ H)) : 0 < S.finiteEigenvalues i :=
  S.eigenvalue_pos (S.symmetric.hasEigenvalue_eigenvalues rfl i)

lemma finiteEigenbasis_equation (i : Fin (Module.finrank ℂ H)) :
    S.operator (S.finiteEigenbasis i) = (S.finiteEigenvalues i : ℂ) • S.finiteEigenbasis i :=
  S.symmetric.apply_eigenvectorBasis rfl i

/-- Multiplicities are dimensions over C, not dimensions of a realification. -/
lemma finiteEigenvalues_multiplicity (μ : ℂ) :
    Finset.card {i : Fin (Module.finrank ℂ H) | (S.finiteEigenvalues i : ℂ) = μ} =
      Module.finrank ℂ (eigenspace S.operator.toLinearMap μ) := by
  classical
  exact S.symmetric.card_filter_eigenvalues_eq rfl μ

/-- Reciprocal shift of the ordered solution spectrum. The weak-Jacobi
identification and min-max characterization are separate obligations. -/
def finiteReciprocalShift (c : ℝ) (i : Fin (Module.finrank ℂ H)) : ℝ :=
  (S.finiteEigenvalues i)⁻¹ - c

lemma finiteReciprocalShift_monotone (c : ℝ) : Monotone (S.finiteReciprocalShift c) := by
  intro i j hij
  apply sub_le_sub_right
  exact (inv_le_inv₀ (S.finiteEigenvalues_pos i) (S.finiteEigenvalues_pos j)).mpr
    (S.finiteEigenvalues_antitone hij)

end KsIndex.Spectral.PositiveCompactSolution
