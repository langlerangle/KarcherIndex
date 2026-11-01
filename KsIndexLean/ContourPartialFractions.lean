module

public import KsIndexLean.ContourChainOperations

@[expose] public section


/-! Image-wise congruence and actual integration of finite partial fractions. -/
open Set MeasureTheory
open scoped BigOperators
noncomputable section
namespace KsIndex.Piecewise

namespace Piece
lemma integrable_congr_image (p : Piece) {f g : ℂ → ℂ} (h : EqOn f g p.image) :
    p.Integrable f ↔ p.Integrable g := by
  apply intervalIntegrable_congr
  intro t ht
  rw [uIoc_of_le p.lt.le] at ht
  change p.velocity t * f (p.curve t) = p.velocity t * g (p.curve t)
  rw [h (mem_image_of_mem _ ⟨ht.1.le, ht.2⟩)]
lemma contour_congr_image (p : Piece) {f g : ℂ → ℂ} (h : EqOn f g p.image) :
    p.contour f = p.contour g := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le p.lt.le] at ht
  change p.velocity t * f (p.curve t) = p.velocity t * g (p.curve t)
  rw [h (mem_image_of_mem _ ht)]
end Piece

namespace Chain
lemma integrable_congr_image (C : Chain) {f g : ℂ → ℂ} (h : EqOn f g C.image) :
    C.Integrable f ↔ C.Integrable g := by
  apply forall_congr'
  intro i
  apply (C.piece i).integrable_congr_image
  intro w hw
  exact h (mem_iUnion.mpr ⟨i, hw⟩)
lemma contour_congr_image (C : Chain) {f g : ℂ → ℂ} (h : EqOn f g C.image) :
    C.contour f = C.contour g := by
  apply Finset.sum_congr rfl
  intro i _
  apply (C.piece i).contour_congr_image
  intro w hw
  exact h (mem_iUnion.mpr ⟨i, hw⟩)

/-- Every winding summand carries its own membership and avoidance certificate. -/
def residueWindingSum (C : Chain) (hc : C.IsClosed) (S : Finset ℂ) (R : ℂ → ℂ)
    (hA : ∀ z ∈ S, C.Avoids z) : ℂ :=
  ∑ z : S, (C.winding hc z.val (hA z.val z.property) : ℂ) * R z.val

lemma integrable_of_partial_fractions (C : Chain) (S : Finset ℂ) (R : ℂ → ℂ)
    (hA : ∀ z ∈ S, C.Avoids z) {f : ℂ → ℂ}
    (hf : ∀ w ∈ C.image, f w = ∑ z ∈ S, R z / (w - z)) : C.Integrable f := by
  have hI : C.Integrable (fun w => ∑ z ∈ S, R z * (w - z)⁻¹) :=
    C.integrable_sum S (fun z hz =>
      C.integrable_const_mul (R z) (C.integrable_reciprocal (hA z hz)))
  apply (C.integrable_congr_image (g := fun w => ∑ z ∈ S, R z * (w - z)⁻¹) ?_).mpr hI
  intro w hw
  simpa only [div_eq_mul_inv] using hf w hw

lemma contour_of_partial_fractions (C : Chain) (hc : C.IsClosed) (S : Finset ℂ)
    (R : ℂ → ℂ) (hA : ∀ z ∈ S, C.Avoids z) {f : ℂ → ℂ}
    (hf : ∀ w ∈ C.image, f w = ∑ z ∈ S, R z / (w - z)) :
    C.contour f = (2 * Real.pi * Complex.I) * C.residueWindingSum hc S R hA := by
  classical
  have hg : EqOn f (fun w => ∑ z : S, R z.val * (w - z.val)⁻¹) C.image := by
    intro w hw
    change f w = ∑ z : S, R z.val * (w - z.val)⁻¹
    rw [Finset.sum_coe_sort S (fun z => R z * (w - z)⁻¹)]
    simpa only [div_eq_mul_inv] using hf w hw
  have hI : ∀ z : S, C.Integrable (fun w => R z.val * (w - z.val)⁻¹) :=
    fun z => C.integrable_const_mul (R z.val) (C.integrable_reciprocal (hA z.val z.property))
  rw [C.contour_congr_image hg, C.contour_sum Finset.univ (fun z _ => hI z)]
  unfold residueWindingSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [C.contour_const_mul (R z.val) (C.integrable_reciprocal (hA z.val z.property))]
  change R z.val * C.logIntegral z.val = _
  rw [C.logIntegral_eq_winding hc z.val (hA z.val z.property)]
  ring

lemma residueWindingSum_eq_single (C : Chain) (hc : C.IsClosed) (S : Finset ℂ)
    (R : ℂ → ℂ) (hA : ∀ z ∈ S, C.Avoids z) (z : ℂ) (hz : z ∈ S)
    (hcenter : C.winding hc z (hA z hz) = 1)
    (hother : ∀ w, ∀ hw : w ∈ S, w ≠ z → C.winding hc w (hA w hw) = 0) :
    C.residueWindingSum hc S R hA = R z := by
  classical
  unfold residueWindingSum
  rw [Finset.sum_eq_single (⟨z, hz⟩ : S)]
  · simp only [hcenter, Int.cast_one, one_mul]
  · intro w _ hw
    have hne : w.val ≠ z := fun he => hw (Subtype.ext he)
    rw [hother w.val w.property hne]
    simp
  · simp

end Chain
end KsIndex.Piecewise
