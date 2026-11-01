module

public import KsIndexLean.NullityDecompClauses

@[expose] public section


/-!
# Symmetry-sector decomposition of bounded Jacobi nullity

For `k > 0`, `nulSurface k 2` is the sum of the ranks of the joint rotation and
reflection sectors, with ranks converted to `ℕ∞` by `Cardinal.toENat`. The result
uses four copies (`m = 2`) and does not assume finite-dimensionality.

`BoundedJacobiE` transports the bounded Jacobi fields to functions on pairs of a
copy index and a complex coordinate. Their rank is expressed as the nullity of the
zero form. Three applications of `formNullity_eq_sum_eigen` decompose this space
under `rotE 2 (rotUnit k)`, `reflE 2 1`, and `reflE 2 (-1)`. The symmetry-preservation
lemmas and commutation identities supply the required invariant subspaces.

The sector `(r, s₁, s₀)` has eigenvalues `zeta k ^ r`, `zeta 2 ^ s₁`, and
`zeta 2 ^ s₀`, respectively. The sum ranges over `Fin k`, `Fin 2`, and `Fin 2`;
zero sectors are allowed. This is an algebraic decomposition of bounded Jacobi
fields. Identification with disk spaces and their boundary trace conditions is
provided by additional results.
-/

noncomputable section
namespace KsIndex.NullityDecomp
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.FormIndex Complex

/-! ### The uncurried carrier -/

/-- `BoundedJacobi`, uncurried to the `(ι → ℂ)` shape the decomposition engine consumes. -/
def BoundedJacobiE (k m : ℕ) : Submodule ℂ (ZMod (2 * m) × ℂ → ℂ) :=
  (BoundedJacobi k m).map (uncurryE m).toLinearMap

lemma mem_boundedJacobiE {k m : ℕ} {U : ZMod (2 * m) × ℂ → ℂ} :
    U ∈ BoundedJacobiE k m ↔ (uncurryE m).symm U ∈ BoundedJacobi k m := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro h
    exact ⟨(uncurryE m).symm U, h, by simp⟩

/-- `nulSurface` through the zero form on the uncurried carrier. -/
lemma nulSurface_eq_formNullity_zero (k m : ℕ) :
    nulSurface k m = formNullity (fun _ _ => (0 : ℂ)) (BoundedJacobiE k m) := by
  rw [formNullity_zero_eq_rank]
  unfold nulSurface BoundedJacobiE
  congr 1
  exact LinearEquiv.rank_eq ((uncurryE m).submoduleMap (BoundedJacobi k m))

/-! ### Stability of the carrier under the symmetries -/

lemma uncurry_symm_reflE {m : ℕ} (c : ZMod (2 * m)) (U : ZMod (2 * m) × ℂ → ℂ) :
    (uncurryE m).symm (reflE m c U) = reflF c ((uncurryE m).symm U) := rfl

lemma rotE_mem_boundedJacobiE {k m : ℕ} (hk : 0 < k) {U : ZMod (2 * m) × ℂ → ℂ}
    (hU : U ∈ BoundedJacobiE k m) :
    rotE m ((rotUnit k : Circle) : ℂ) U ∈ BoundedJacobiE k m := by
  rw [mem_boundedJacobiE] at hU ⊢
  rw [uncurry_symm_rotE]
  exact rotF_mem_boundedJacobi (Circle.norm_coe _) (rotUnit_pow hk) hU

lemma reflE_mem_boundedJacobiE {k m : ℕ} {c : ZMod (2 * m)} (hc : parity m c = 1)
    {U : ZMod (2 * m) × ℂ → ℂ} (hU : U ∈ BoundedJacobiE k m) :
    reflE m c U ∈ BoundedJacobiE k m := by
  rw [mem_boundedJacobiE] at hU ⊢
  rw [uncurry_symm_reflE]
  exact reflF_mem_boundedJacobi hc hU

/-- A commuting endomorphism preserves eigenspaces. -/
lemma comm_apply_eigenspace {M : Type*} [AddCommGroup M] [Module ℂ M]
    {g g' : Module.End ℂ M} (hcomm : ∀ v, g (g' v) = g' (g v)) {μ : ℂ} {v : M}
    (hv : v ∈ Module.End.eigenspace g μ) : g' v ∈ Module.End.eigenspace g μ := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  rw [hcomm, hv, map_smul]

/-! ### The sectors and the decomposition -/

/-- The joint symmetry sector of `BoundedJacobi k 2`: rotation class `r`, reflection
parities `(s₁, s₀)` for `reflE 2 1` and `reflE 2 (-1)`, respectively. -/
def boundedJacobiSector (k : ℕ) (r s₁ s₀ : ℕ) : Submodule ℂ (ZMod (2 * 2) × ℂ → ℂ) :=
  ((BoundedJacobiE k 2 ⊓
      Module.End.eigenspace (rotE 2 ((rotUnit k : Circle) : ℂ)) (zeta k ^ r)) ⊓
    Module.End.eigenspace (reflE 2 1) (zeta 2 ^ s₁)) ⊓
    Module.End.eigenspace (reflE 2 (-1)) (zeta 2 ^ s₀)

/-- Bounded Jacobi nullity for four copies is the sum of the joint-sector ranks,
converted to extended natural numbers. -/
theorem nulSurface_eq_sum_sectors (k : ℕ) (hk : 0 < k) :
    nulSurface k 2 = ∑ r : Fin k, ∑ s₁ : Fin 2, ∑ s₀ : Fin 2,
      Cardinal.toENat (Module.rank ℂ
        (boundedJacobiSector k (r : ℕ) (s₁ : ℕ) (s₀ : ℕ))) := by
  have hc1 : parity 2 (1 : ZMod (2 * 2)) = 1 := by decide
  have hcm1 : parity 2 (-1 : ZMod (2 * 2)) = 1 := by decide
  have hcomm4 : (2 : ZMod (2 * 2)) * ((1 : ZMod (2 * 2)) - (-1 : ZMod (2 * 2))) = 0 := by
    decide
  rw [nulSurface_eq_formNullity_zero]
  -- first split: the rotation
  rw [formNullity_eq_sum_eigen (g := rotE 2 ((rotUnit k : Circle) : ℂ))
    (sesq_zero _) hk (fun u _ => rot_pow_id hk u)
    (fun u hu => rotE_mem_boundedJacobiE hk hu) (fun _ _ _ _ => rfl)]
  refine Finset.sum_congr rfl fun r _ => ?_
  -- second split: the z=π reflection
  rw [formNullity_eq_sum_eigen (g := reflE 2 1) (sesq_zero _) two_pos
    (fun u _ => reflE_sq 2 1 u)
    (fun u hu => Submodule.mem_inf.mpr
      ⟨reflE_mem_boundedJacobiE hc1 (Submodule.mem_inf.mp hu).1,
        comm_apply_eigenspace (fun v => (reflE_rotE_comm 2 1 _ v).symm)
          (Submodule.mem_inf.mp hu).2⟩)
    (fun _ _ _ _ => rfl)]
  refine Finset.sum_congr rfl fun s₁ _ => ?_
  -- third split: the z=0 reflection
  rw [formNullity_eq_sum_eigen (g := reflE 2 (-1)) (sesq_zero _) two_pos
    (fun u _ => reflE_sq 2 (-1) u)
    (fun u hu => by
      obtain ⟨hu12, hu3⟩ := Submodule.mem_inf.mp hu
      obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu12
      exact Submodule.mem_inf.mpr
        ⟨Submodule.mem_inf.mpr
          ⟨reflE_mem_boundedJacobiE hcm1 hu1,
            comm_apply_eigenspace (fun v => (reflE_rotE_comm 2 (-1) _ v).symm) hu2⟩,
          comm_apply_eigenspace (fun v => reflE_comm 2 1 (-1) hcomm4 v) hu3⟩)
    (fun _ _ _ _ => rfl)]
  refine Finset.sum_congr rfl fun s₀ _ => ?_
  -- back to ranks
  rw [formNullity_zero_eq_rank]
  rfl

end KsIndex.NullityDecomp
