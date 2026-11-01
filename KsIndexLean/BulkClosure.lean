module

public import KsIndexLean.FiniteDiskBulkCompact

@[expose] public section


noncomputable section
open Set
namespace KsIndex.Spectral

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Ambient sector space: closure of the actual bulk image, not all of ambient L2. -/
def bulkClosure (J : V →L[ℂ] H) : Submodule ℂ H :=
  J.toLinearMap.range.topologicalClosure

lemma mem_bulkClosure (J : V →L[ℂ] H) (v : V) : J v ∈ bulkClosure J :=
  subset_closure ⟨v, rfl⟩

/-- Bulk inclusion with codomain restricted to its ambient sector closure. -/
def closureEmbedding (J : V →L[ℂ] H) : V →L[ℂ] bulkClosure J :=
  J.codRestrict (bulkClosure J) (mem_bulkClosure J)

lemma closureEmbedding_injective {J : V →L[ℂ] H} (hJ : Function.Injective J) :
    Function.Injective (closureEmbedding J) := by
  intro u v h
  exact hJ (congrArg Subtype.val h)

lemma closureEmbedding_denseRange (J : V →L[ℂ] H) : DenseRange (closureEmbedding J) := by
  change Dense (Set.range (closureEmbedding J))
  rw [Subtype.dense_iff]
  change (bulkClosure J : Set H) ⊆ closure ((fun x : bulkClosure J => (x : H)) '' Set.range (closureEmbedding J))
  have he : (fun x : bulkClosure J => (x : H)) '' Set.range (closureEmbedding J) = Set.range J := by
    ext x
    constructor
    · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨closureEmbedding J v, ⟨v, rfl⟩, rfl⟩
  rw [he]
  exact subset_rfl

lemma closureEmbedding_compact {J : V →L[ℂ] H} (hJ : IsCompactOperator J) :
    IsCompactOperator (closureEmbedding J) :=
  hJ.codRestrict (mem_bulkClosure J) J.toLinearMap.range.isClosed_topologicalClosure

instance bulkClosure_completeSpace [CompleteSpace H] (J : V →L[ℂ] H) :
    CompleteSpace (bulkClosure J) := by
  unfold bulkClosure
  infer_instance

end KsIndex.Spectral
