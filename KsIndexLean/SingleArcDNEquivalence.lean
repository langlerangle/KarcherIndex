module

public import KsIndexLean.CirclePowerFourier
public import KsIndexLean.DNHalfTraceSpace

@[expose] public section


noncomputable section
open MeasureTheory
namespace KsIndex.SingleArcReindex
open KsIndex.Trace KsIndex.CircleSobolev

lemma insert_mem_dnSpace_iff {k j : ℕ} (hk : 3 ≤ k) (hj : j ≤ k)
    (f : Space (1 / 2)) : insert hk j f ∈ dnSpace k ↔ f ∈ dnSpace 1 := by
  change insert hk j f ∈ arcZero _ _ ↔ f ∈ arcZero _ _
  rw [mem_arcZero_iff, mem_arcZero_iff, toL2_insert_eq_phasedPower hk hj]
  exact phasedPowerL2_arc_zero_iff (by omega : 0 < k) (k-j) 0 _

lemma extract_mem_dnSpace_iff {k j : ℕ} (hk : 3 ≤ k) (hj : j ≤ k)
    (f : Space (1 / 2)) (hf : f ∈ character (1 / 2) j k) :
    extract hk j f ∈ dnSpace 1 ↔ f ∈ dnSpace k := by
  rw [← insert_mem_dnSpace_iff hk hj, insert_extract hk hj f hf]

/-- The single-arc correspondence between dnCharacterSpace k j and dnSpace 1. -/
def dnEquiv {k j : ℕ} (hk : 3 ≤ k) (hj : j ≤ k) :
    dnCharacterSpace k j ≃ₗ[ℂ] dnSpace 1 where
  toFun f := ⟨extract hk j f.val,
    (extract_mem_dnSpace_iff hk hj f.val f.property.2).mpr f.property.1⟩
  invFun g := ⟨insert hk j g.val,
    ⟨(insert_mem_dnSpace_iff hk hj g.val).mpr g.property, insert_mem_character hk hj g.val⟩⟩
  left_inv f := Subtype.ext (insert_extract hk hj f.val f.property.2)
  right_inv g := Subtype.ext (extract_insert hk j g.val)
  map_add' f g := Subtype.ext ((extractLinear hk j).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((extractLinear hk j).map_smul c f.val)

/-- Both directions are continuous in the half-order Sobolev norms. -/
def dnContinuousEquiv {k j : ℕ} (hk : 3 ≤ k) (hj : j ≤ k) :
    dnCharacterSpace k j ≃L[ℂ] dnSpace 1 :=
  (dnEquiv hk hj).toContinuousLinearEquivOfBounds
    (Real.sqrt 2) (Real.sqrt ((k : ℝ)+1))
    (fun f => by
      change ‖extract hk j f.val‖ ≤ Real.sqrt 2 * ‖f.val‖
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      simpa only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        using extract_norm_sq_le hk j f.val)
    (fun g => by
      change ‖insert hk j g.val‖ ≤ Real.sqrt ((k : ℝ)+1) * ‖g.val‖
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      simpa only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ)+1 by positivity)]
        using insert_norm_sq_le hk j g.val)

end KsIndex.SingleArcReindex
