module

public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section


/-! Compactness from finitely many reductions to a proper restricted map. -/
open Set

/-- A closed set has compact inverse images when finitely many continuous
reconstructions reduce it to a set with compact inverse images. -/
theorem isCompact_restrict_of_finite_reductions
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [Finite ι]
    {f : X → Y} (hf : Continuous f) {S T : Set X} (hS : IsClosed S)
    (hT : ∀ K : Set Y, IsCompact K → IsCompact (T ∩ f ⁻¹' K))
    (g r : ι → X → X) (A : ι → Y → Y)
    (hr : ∀ i, Continuous (r i)) (hA : ∀ i, Continuous (A i))
    (hinv : ∀ i x, r i (g i x) = x)
    (heq : ∀ i x, f (g i x) = A i (f x))
    (hcover : ∀ x ∈ S, ∃ i, g i x ∈ T)
    {K : Set Y} (hK : IsCompact K) : IsCompact (S ∩ f ⁻¹' K) := by
  have hc : IsCompact (⋃ i, r i '' (T ∩ f ⁻¹' (A i '' K))) :=
    isCompact_iUnion fun i => (hT _ (hK.image (hA i))).image (hr i)
  apply hc.of_isClosed_subset (hS.inter (hK.isClosed.preimage hf))
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx.1
  exact mem_iUnion.mpr ⟨i, g i x, ⟨hi, ⟨f x, hx.2, (heq i x).symm⟩⟩, hinv i x⟩

/-- A two-piece version, with the identity as the first reduction. -/
theorem isCompact_restrict_of_two_reductions
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {S T : Set X} (hS : IsClosed S)
    (hT : ∀ K : Set Y, IsCompact K → IsCompact (T ∩ f ⁻¹' K))
    (g r : X → X) (A : Y → Y) (hr : Continuous r) (hA : Continuous A)
    (hinv : ∀ x, r (g x) = x) (heq : ∀ x, f (g x) = A (f x))
    (hcover : ∀ x ∈ S, x ∈ T ∨ g x ∈ T)
    {K : Set Y} (hK : IsCompact K) : IsCompact (S ∩ f ⁻¹' K) := by
  have hc := (hT K hK).union ((hT _ (hK.image hA)).image hr)
  apply hc.of_isClosed_subset (hS.inter (hK.isClosed.preimage hf))
  intro x hx
  rcases hcover x hx.1 with hi | hi
  · exact Or.inl ⟨hi, hx.2⟩
  · exact Or.inr ⟨g x, ⟨hi, ⟨f x, hx.2, (heq x).symm⟩⟩, hinv x⟩
