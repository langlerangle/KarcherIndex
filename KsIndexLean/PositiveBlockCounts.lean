module

public import KsIndexLean.DtnBridge
public import KsIndexLean.IndexCoordinateTransport

@[expose] public section


noncomputable section
namespace KsIndex.DtnBridge
open KsIndex.NegativeDensity
variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]

lemma negativeIndex_le_of_pointwise_le (Q R : E → ℝ) (h : ∀ x, Q x ≤ R x) :
    negativeIndex R ≤ negativeIndex Q := by
  unfold negativeIndex
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfin => ?_
  exact le_iSup_of_le V (le_iSup_of_le (fun x hx hn => (h x).trans_lt (hV x hx hn))
    (le_iSup_of_le hfin le_rfl))

/-- A nonnegative product block contributes no negative directions, even at infinite index. -/
lemma negativeIndex_nonnegative_product (Q : E → ℝ) (R : F → ℝ)
    (hQ : Q 0 = 0) (hR : R 0 = 0) (hpos : ∀ y, 0 ≤ R y) :
    negativeIndex (fun p : E × F => Q p.1 + R p.2) = negativeIndex Q := by
  apply le_antisymm
  · exact (negativeIndex_le_of_pointwise_le (fun p : E × F => Q p.1)
      (fun p => Q p.1 + R p.2) (fun p => le_add_of_nonneg_right (hpos p.2))).trans
      (negativeIndex_pullback_le Q hQ (LinearMap.fst ℂ E F))
  · have h := negativeIndex_pullback_le (fun p : E × F => Q p.1 + R p.2)
      (by simp [hQ, hR]) (LinearMap.inl ℂ E F)
    simpa only [LinearMap.inl_apply, hR, add_zero] using h

/-- A linear map injective on the radical transports its finite-dimensional subspaces. -/
lemma sesqNullity_le_of_radical_map (B : E → E → ℂ) (C : F → F → ℂ)
    (T : E →ₗ[ℂ] F)
    (hmap : ∀ u, (∀ w, B u w = 0) → ∀ z, C (T u) z = 0)
    (hker : ∀ u, (∀ w, B u w = 0) → T u = 0 → u = 0) :
    sesqNullity B ≤ sesqNullity C := by
  unfold sesqNullity
  refine iSup_le fun W => iSup_le fun hW => iSup_le fun hfin => ?_
  let := hfin
  let L : W →ₗ[ℂ] F := T.comp W.subtype
  have hi : Function.Injective L := by
    intro u v huv
    apply sub_eq_zero.mp
    apply Subtype.ext
    apply hker (u - v).val (hW _ (u - v).property)
    change L (u - v) = 0
    rw [map_sub, huv, sub_self]
  have hr : ∀ u ∈ LinearMap.range L, ∀ z, C u z = 0 := by
    rintro _ ⟨w, rfl⟩ z
    exact hmap w.val (hW _ w.property) z
  rw [← LinearMap.finrank_range_of_inj hi]
  exact le_iSup_of_le (LinearMap.range L) (le_iSup_of_le hr
    (le_iSup_of_le (inferInstance : FiniteDimensional ℂ (LinearMap.range L)) le_rfl))

/-- A positive-definite block contributes no radical. No density or spectral hypothesis. -/
lemma sesqNullity_positive_product (B : E → E → ℂ) (C : F → F → ℂ)
    (hB : ∀ x, B x 0 = 0) (hC : ∀ y, C 0 y = 0)
    (hpos : ∀ y, y ≠ 0 → 0 < (C y y).re) :
    sesqNullity (fun p q : E × F => B p.1 q.1 + C p.2 q.2) = sesqNullity B := by
  have hz (p : E × F) (hp : ∀ q : E × F, B p.1 q.1 + C p.2 q.2 = 0) : p.2 = 0 := by
    by_contra hn
    have he := hp (0, p.2)
    rw [hB, zero_add] at he
    have h := hpos p.2 hn
    rw [he] at h
    exact (lt_irrefl 0 h)
  apply le_antisymm
  · apply sesqNullity_le_of_radical_map _ B (LinearMap.fst ℂ E F)
    · intro p hp x
      have he := hp (x, 0)
      change B p.1 x = 0
      simpa only [hz p hp, hC, add_zero] using he
    · intro p hp he
      exact Prod.ext he (hz p hp)
  · apply sesqNullity_le_of_radical_map B _ (LinearMap.inl ℂ E F)
    · intro x hx p
      change B x p.1 + C 0 p.2 = 0
      rw [hx, hC, add_zero]
    · intro x hx he
      exact congrArg Prod.fst he

lemma sesqNullity_nonzero_mul (B : E → E → ℂ) (c : ℂ) (hc : c ≠ 0) :
    sesqNullity (fun u v => c * B u v) = sesqNullity B := by
  simp only [sesqNullity, mul_eq_zero, hc, false_or]

lemma sesqNullity_eq_finrank_radical (B : E → E → ℂ) (K : Submodule ℂ E)
    [FiniteDimensional ℂ K] (hK : ∀ u, u ∈ K ↔ ∀ w, B u w = 0) :
    sesqNullity B = (Module.finrank ℂ K : ℕ∞) := by
  apply le_antisymm
  · unfold sesqNullity
    refine iSup_le fun W => iSup_le fun hW => iSup_le fun hfin => ?_
    have hle : W ≤ K := fun u hu => (hK u).mpr (hW u hu)
    exact_mod_cast Submodule.finrank_mono hle
  · exact le_iSup_of_le K (le_iSup_of_le (fun u hu => (hK u).mp hu)
      (le_iSup_of_le (inferInstance : FiniteDimensional ℂ K) le_rfl))

end KsIndex.DtnBridge
