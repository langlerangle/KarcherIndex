module

public import KsIndexLean.SurfaceSym

@[expose] public section


/-! Rotation-character decomposition inside a fixed translation phase. -/
noncomputable section
namespace KsIndex.SurfaceSym
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.FormIndex

/-- Rotation preserves the smooth test domain in any fixed translation phase. -/
lemma rot_mem_shiftBlock {k m : ℕ} (hk : 0 < k) {μ : ℂ}
    {U : ZMod (2 * m) × ℂ → ℂ}
    (hU : U ∈ Dom k m ⊓ Module.End.eigenspace (shiftE m) μ) :
    rotE m (rotUnit k : ℂ) U ∈ Dom k m ⊓ Module.End.eigenspace (shiftE m) μ := by
  obtain ⟨hD, hE⟩ := Submodule.mem_inf.mp hU
  rw [Module.End.mem_eigenspace_iff] at hE
  refine Submodule.mem_inf.mpr ⟨rot_mem_Dom hk hD, ?_⟩
  rw [Module.End.mem_eigenspace_iff, ← Module.End.mul_apply,
    ← rotE_mul_shiftE, Module.End.mul_apply, hE, map_smul]

/-- The index in a fixed translation phase is the sum of its rotation-character
indices. This is a restricted-domain statement, not only a global phase sum. -/
theorem phase_index_eq_sum_rotation {k m : ℕ} [NeZero m] (hk : 2 ≤ k) (μ : ℂ) :
    formIndex (Qs k m) (Dom k m ⊓ Module.End.eigenspace (shiftE m) μ) =
      ∑ r : Fin k, formIndex (Qs k m)
        ((Dom k m ⊓ Module.End.eigenspace (rotE m (rotUnit k : ℂ)) (zeta k ^ (r : ℕ)))
          ⊓ Module.End.eigenspace (shiftE m) μ) := by
  have hS := (sesq_surface (m := m) hk).mono
    (show Dom k m ⊓ Module.End.eigenspace (shiftE m) μ ≤ Dom k m from inf_le_left)
  have h := formIndex_eq_sum_eigen (rotE m (rotUnit k : ℂ)) hS
    (show 0 < k by omega) (fun U _ => rot_pow_id (by omega) U)
    (fun U hU => rot_mem_shiftBlock (by omega) hU)
    (fun U hU V hV => rot_inv hU.1 hV.1)
  refine h.trans (Finset.sum_congr rfl fun r _ => ?_)
  apply congrArg (formIndex (Qs k m))
  ac_rfl

end KsIndex.SurfaceSym
