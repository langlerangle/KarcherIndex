module

public import KsIndexLean.FiberEmbed

@[expose] public section


/-! Rotation decomposition of bounded Jacobi fields within one translation phase. -/
noncomputable section
namespace KsIndex.NullityDecomp
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.FormIndex

/-- Bounded Jacobi fields with one translation character and unrestricted rotation. -/
def boundedJacobiPhase (k m n : ℕ) :=
  BoundedJacobiE k m ⊓ Module.End.eigenspace (shiftE m) (zeta m ^ n)

/-- This is a rank decomposition of bounded fields, not a compact-test radical. -/
theorem boundedJacobiPhase_rank_eq_sum (k m n : ℕ) (hk : 0 < k) :
    Cardinal.toENat (Module.rank ℂ (boundedJacobiPhase k m n)) =
      ∑ r : Fin k, Cardinal.toENat (Module.rank ℂ (isotypicFiber k m r n)) := by
  rw [← formNullity_zero_eq_rank]
  rw [formNullity_eq_sum_eigen (g := rotE m (rotUnit k : ℂ)) (sesq_zero _) hk
    (fun u _ => rot_pow_id hk u)
    (fun u hu => by
      refine ⟨rotE_mem_boundedJacobiE hk hu.1, ?_⟩
      have he := Module.End.mem_eigenspace_iff.mp hu.2
      apply Module.End.mem_eigenspace_iff.mpr
      rw [← Module.End.mul_apply,
        ← rotE_mul_shiftE, Module.End.mul_apply, he, map_smul])
    (fun _ _ _ _ => rfl)]
  apply Finset.sum_congr rfl
  intro r _
  rw [formNullity_zero_eq_rank]
  have hd : boundedJacobiPhase k m n ⊓
      Module.End.eigenspace (rotE m (rotUnit k : ℂ)) (zeta k ^ (r : ℕ)) =
      isotypicFiber k m r n := by
    unfold boundedJacobiPhase isotypicFiber
    ac_rfl
  rw [hd]

end KsIndex.NullityDecomp
