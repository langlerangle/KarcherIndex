module

public import KsIndexLean.NegativeSpectralSpace

@[expose] public section


noncomputable section
namespace KsIndex.InvariantHermitian
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

lemma involution_eigenspaces_sup (R : Module.End ℂ E) (hR : Function.Involutive R) :
    Module.End.eigenspace R 1 ⊔ Module.End.eigenspace R (-1) = ⊤ := by
  apply top_unique
  intro u hu
  apply Submodule.mem_sup.mpr
  refine ⟨(2 : ℂ)⁻¹ • (u + R u), ?_, (2 : ℂ)⁻¹ • (u - R u), ?_, ?_⟩
  · apply Module.End.mem_eigenspace_iff.mpr
    simp only [map_smul, map_add, hR u, one_smul]
    rw [add_comm]
  · apply Module.End.mem_eigenspace_iff.mpr
    simp only [map_smul, map_sub, hR u, neg_one_smul]
    rw [← smul_neg, neg_sub]
  · rw [← smul_add]
    have he : u + R u + (u - R u) = (2 : ℂ) • u := by
      rw [two_smul]; abel
    rw [he, smul_smul]
    norm_num

lemma involution_eigenspaces_inf (R : Module.End ℂ E) :
    Module.End.eigenspace R 1 ⊓ Module.End.eigenspace R (-1) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro u hu
  have hp := Module.End.mem_eigenspace_iff.mp hu.1
  have hm := Module.End.mem_eigenspace_iff.mp hu.2
  simp only [one_smul] at hp
  simp only [neg_one_smul] at hm
  have hh : (2 : ℂ) • u = 0 := by
    rw [two_smul]
    exact (congrArg (fun x => x + u) (hp.symm.trans hm)).trans (neg_add_cancel u)
  exact (smul_eq_zero.mp hh).resolve_left (by norm_num)

lemma involution_finrank_split [FiniteDimensional ℂ E]
    (R : Module.End ℂ E) (hR : Function.Involutive R) :
    Module.finrank ℂ E = Module.finrank ℂ (Module.End.eigenspace R 1) +
      Module.finrank ℂ (Module.End.eigenspace R (-1)) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (Module.End.eigenspace R 1) (Module.End.eigenspace R (-1))
  rw [involution_eigenspaces_sup R hR, involution_eigenspaces_inf R] at h
  simpa using h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- The restriction exists because commutation preserves all negative eigenspaces. -/
def negativeSpectralInvolution (T R : Module.End ℂ H) (hcomm : Function.Commute T R) :
    Module.End ℂ (negativeSpectralSpace T) :=
  R.restrict (negativeSpectralSpace_stable T R hcomm)

omit [FiniteDimensional ℂ H] in
lemma negativeSpectralInvolution_involutive (T R : Module.End ℂ H)
    (hcomm : Function.Commute T R) (hR : Function.Involutive R) :
    Function.Involutive (negativeSpectralInvolution T R hcomm) := by
  intro u
  exact Subtype.ext (hR u.val)

/-- The paper's finite negative spectral space splits into its two symmetry blocks. -/
lemma negative_trial_le_involution_blocks (T R : Module.End ℂ H)
    (hT : T.IsSymmetric) (hcomm : Function.Commute T R) (hR : Function.Involutive R)
    (X : Submodule ℂ H)
    (hX : ∀ u : X, u ≠ 0 → (inner ℂ u.val (T u.val)).re < 0) :
    Module.finrank ℂ X ≤
      Module.finrank ℂ (Module.End.eigenspace (negativeSpectralInvolution T R hcomm) 1) +
      Module.finrank ℂ (Module.End.eigenspace (negativeSpectralInvolution T R hcomm) (-1)) := by
  have h := negative_trial_finrank_le_negativeSpectralSpace T hT X hX
  rw [involution_finrank_split _ (negativeSpectralInvolution_involutive T R hcomm hR)] at h
  exact h

end KsIndex.InvariantHermitian
