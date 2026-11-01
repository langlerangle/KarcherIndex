module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section


/-! Compactness transfers through a norm bound into a complete target. -/
noncomputable section
open Set
namespace KsIndex

/-- A linear map dominated by a compact linear map is compact. -/
theorem compact_of_norm_le_compact
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (T : E →L[ℂ] F) (S : E →L[ℂ] G) (C : NNReal)
    (hT : IsCompactOperator T) (h : ∀ x, ‖S x‖ ≤ C * ‖T x‖) :
    IsCompactOperator S := by
  let R := Set.range T
  let pick : R → E := fun y => y.property.choose
  have hp : ∀ y : R, T (pick y) = y.val := fun y => y.property.choose_spec
  let f : R → G := fun y => S (pick y)
  have hf : LipschitzWith C f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh := h (pick x - pick y)
    simpa only [map_sub, hp, dist_eq_norm, Subtype.dist_eq, f] using hh
  have ht : TotallyBounded (T '' Metric.closedBall 0 1) :=
    (hT.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  have hr := totallyBounded_preimage
    (isUniformEmbedding_subtype_val.isUniformInducing : IsUniformInducing (Subtype.val : R → F)) ht
  have hb := hr.image hf.uniformContinuous
  have he : S '' Metric.closedBall 0 1 ⊆
      f '' (Subtype.val ⁻¹' (T '' Metric.closedBall 0 1)) := by
    rintro _ ⟨x,hx,rfl⟩
    let y : R := ⟨T x, ⟨x,rfl⟩⟩
    refine ⟨y, ⟨x,hx,rfl⟩, ?_⟩
    have hh := h (pick y - x)
    have hz : T (pick y - x) = 0 := by rw [map_sub, hp]; exact sub_self _
    rw [hz, norm_zero, mul_zero] at hh
    have hs : S (pick y - x) = 0 := norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
    exact sub_eq_zero.mp (by simpa only [map_sub] using hs)
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall S.toLinearMap
    (by norm_num : (0 : ℝ) < 1)).mpr ((hb.subset he).closure.isCompact_of_isClosed isClosed_closure)
end KsIndex
