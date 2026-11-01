module

public import KsIndexLean.SpectralEnergyLowerBound
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section


noncomputable section
namespace KsIndex.Spectral

variable {E H ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- More complex trial dimensions than coefficient constraints leave a nonzero
vector annihilating all constraints. No independence of the constraints is needed. -/
lemma exists_nonzero_orthogonal_in_trial [Fintype ι]
    (J : E →L[ℂ] H) (b : ι → H) (W : Submodule ℂ E)
    [FiniteDimensional ℂ W] (hdim : Fintype.card ι < Module.finrank ℂ W) :
    ∃ u : W, u ≠ 0 ∧ ∀ i, inner ℂ (b i) (J u) = 0 := by
  let L : W →ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun u i => inner ℂ (b i) (J u)
      map_add' := fun u v => by ext i; simp
      map_smul' := fun a u => by ext i; simp }
  have hker : L.ker ≠ ⊥ := by
    intro he
    have hd := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp he)
    have heq : Module.finrank ℂ (ι → ℂ) = Fintype.card ι := by simp
    rw [heq] at hd
    omega
  obtain ⟨u, hu, hne⟩ := L.ker.ne_bot_iff.mp hker
  refine ⟨u, hne, fun i => ?_⟩
  exact congrFun (LinearMap.mem_ker.mp hu) i

/-- The usual `n+1` versus `n` dimension step, with all dimensions over C. -/
lemma exists_nonzero_orthogonal_before (J : E →L[ℂ] H) (b : ℕ → H)
    (W : Submodule ℂ E) [FiniteDimensional ℂ W] (n : ℕ)
    (hdim : n < Module.finrank ℂ W) :
    ∃ u : W, u ≠ 0 ∧ ∀ i < n, inner ℂ (b i) (J u) = 0 := by
  obtain ⟨u, hu, hcoeff⟩ := exists_nonzero_orthogonal_in_trial J
    (fun i : Fin n => b i.val) W (by simpa using hdim)
  exact ⟨u, hu, fun i hi => hcoeff ⟨i, hi⟩⟩

section Energy
variable [CompleteSpace E] [CompleteSpace H]

/-- Every complex trial space of dimension greater than `n` contains a vector
with shifted Rayleigh quotient at least the `n`th reciprocal eigenvalue. -/
lemma trial_bound_ge_reciprocal (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hJ : Function.Injective J) (hherm : ∀ u w, star (B w u) = B u w)
    (b : HilbertBasis ℕ ℂ H) (μ : ℕ → ℝ) (hμ : ∀ i, 0 < μ i) (hanti : Antitone μ)
    (hev : ∀ i, compactFormSolution B hB J (b i) = (μ i : ℂ) • b i)
    (W : Submodule ℂ E) [FiniteDimensional ℂ W] (n : ℕ) (hdim : n < Module.finrank ℂ W)
    (L : ℝ) (hL : ∀ u : W, (B u u).re ≤ L * ‖J u‖ ^ 2) : (μ n)⁻¹ ≤ L := by
  obtain ⟨u, hu, horth⟩ := exists_nonzero_orthogonal_before J b W n hdim
  have hlo := spectral_tail_energy_lower_bound B hB J hherm b μ hμ hanti hev n u horth
  have hbulk : J u ≠ 0 := by
    intro he
    have hz : (u : E) = 0 := hJ (he.trans J.map_zero.symm)
    exact hu (Subtype.ext hz)
  have hp : 0 < ‖J u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hbulk)
  nlinarith [hL u]

end Energy
end KsIndex.Spectral
