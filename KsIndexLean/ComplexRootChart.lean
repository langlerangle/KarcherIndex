module

public import Mathlib.Analysis.Complex.CoveringMap

@[expose] public section


/-! Local topology of continuous complex roots. Away from zero, a continuous
root of a local homeomorphism is itself a local homeomorphism. -/
namespace KsIndex

/-- A continuous root inherits local invertibility from its power, provided
it never meets the branch point on the region in question. -/
theorem isLocalHomeomorphOn_complex_root {X : Type*} [TopologicalSpace X]
    {f : X → ℂ} {s : Set X} {m : ℕ} (hm : 0 < m)
    (hc : ∀ x ∈ s, ContinuousAt f x) (hn : ∀ x ∈ s, f x ≠ 0)
    (hp : IsLocalHomeomorphOn (fun x => f x ^ m) s) :
    IsLocalHomeomorphOn f s := by
  apply hp.of_comp_left (g := fun z : ℂ => z ^ m) _ hc
  apply (isCoveringMapOn_npow m (by exact_mod_cast (Nat.ne_of_gt hm) : (m : ℂ) ≠ 0)).isLocalHomeomorphOn.mono
  rintro z ⟨x, hx, rfl⟩
  exact pow_ne_zero m (hn x hx)

/-- The global version used after restricting an end chart to its punctured
source. -/
theorem isLocalHomeomorph_complex_root {X : Type*} [TopologicalSpace X]
    {f : X → ℂ} {m : ℕ} (hm : 0 < m) (hc : Continuous f)
    (hn : ∀ x, f x ≠ 0) (hp : IsLocalHomeomorph (fun x => f x ^ m)) :
    IsLocalHomeomorph f := by
  apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
  exact isLocalHomeomorphOn_complex_root hm (fun _ _ => hc.continuousAt)
    (fun x _ => hn x) hp.isLocalHomeomorphOn

/-- An injective continuous root as above is an open embedding, so its
inverse on its image is continuous. -/
theorem isOpenEmbedding_complex_root {X : Type*} [TopologicalSpace X]
    {f : X → ℂ} {m : ℕ} (hm : 0 < m) (hc : Continuous f)
    (hn : ∀ x, f x ≠ 0) (hp : IsLocalHomeomorph (fun x => f x ^ m))
    (hi : Function.Injective f) : Topology.IsOpenEmbedding f :=
  (isLocalHomeomorph_complex_root hm hc hn hp).isOpenEmbedding_of_injective hi

end KsIndex
