module

public import KsIndexLean.LoopExponentialTransport
public import Mathlib.Data.Fin.Rev
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section


/-! Certified C¹ pieces with interval-only regularity and actual contour integrals. -/
open Set MeasureTheory
open scoped Topology BigOperators

noncomputable section

namespace KsIndex.Piecewise

structure Piece where
  a : ℝ
  b : ℝ
  lt : a < b
  curve : ℝ → ℂ
  velocity : ℝ → ℂ
  continuous_curve : ContinuousOn curve (Icc a b)
  continuous_velocity : ContinuousOn velocity (Icc a b)
  derivative : ∀ t ∈ Icc a b, HasDerivWithinAt curve (velocity t) (Icc a b) t

namespace Piece

def start (p : Piece) : ℂ := p.curve p.a
def finish (p : Piece) : ℂ := p.curve p.b
def image (p : Piece) : Set ℂ := p.curve '' Icc p.a p.b
def Avoids (p : Piece) (z : ℂ) : Prop := ∀ t ∈ Icc p.a p.b, p.curve t ≠ z
def Integrable (p : Piece) (f : ℂ → ℂ) : Prop :=
  IntervalIntegrable (fun t => p.velocity t * f (p.curve t)) volume p.a p.b
def contour (p : Piece) (f : ℂ → ℂ) : ℂ :=
  ∫ t in p.a..p.b, p.velocity t * f (p.curve t)

lemma integrable_of_continuousOn (p : Piece) {f : ℂ → ℂ}
    (hf : ContinuousOn f p.image) : p.Integrable f := by
  have h := p.continuous_velocity.mul
    (hf.comp p.continuous_curve (fun t ht => mem_image_of_mem _ ht))
  rw [← uIcc_of_le p.lt.le] at h
  exact h.intervalIntegrable

lemma start_ne (p : Piece) {z : ℂ} (h : p.Avoids z) : p.start ≠ z :=
  h p.a ⟨le_rfl, p.lt.le⟩
lemma finish_ne (p : Piece) {z : ℂ} (h : p.Avoids z) : p.finish ≠ z :=
  h p.b ⟨p.lt.le, le_rfl⟩

lemma integrable_reciprocal (p : Piece) {z : ℂ} (h : p.Avoids z) :
    p.Integrable (fun w => (w - z)⁻¹) := by
  apply p.integrable_of_continuousOn
  apply (continuousOn_id.sub continuousOn_const).inv₀
  rintro w ⟨t, ht, rfl⟩
  exact sub_ne_zero.mpr (h t ht)

lemma exp_contour_reciprocal (p : Piece) {z : ℂ} (h : p.Avoids z) :
    Complex.exp (p.contour (fun w => (w - z)⁻¹)) = (p.finish - z) / (p.start - z) := by
  have hd : ∀ t ∈ Icc p.a p.b,
      HasDerivWithinAt (fun t => p.curve t - z) (p.velocity t) (Icc p.a p.b) t := by
    intro t ht
    exact (p.derivative t ht).sub_const z
  simpa only [contour, start, finish, div_eq_mul_inv] using
    LoopTransport.exp_integral_logarithmicDerivative (γ := fun t => p.curve t - z) p.lt
      (p.continuous_curve.sub continuousOn_const) p.continuous_velocity hd
      (fun t ht => sub_ne_zero.mpr (h t ht))

lemma integrable_add (p : Piece) {f g : ℂ → ℂ}
    (hf : p.Integrable f) (hg : p.Integrable g) : p.Integrable (fun w => f w + g w) := by
  simpa only [Integrable, mul_add] using hf.add hg
lemma contour_add (p : Piece) {f g : ℂ → ℂ}
    (hf : p.Integrable f) (hg : p.Integrable g) :
    p.contour (fun w => f w + g w) = p.contour f + p.contour g := by
  simp only [contour, mul_add]
  exact intervalIntegral.integral_add hf hg
lemma integrable_const_mul (p : Piece) (c : ℂ) {f : ℂ → ℂ}
    (hf : p.Integrable f) : p.Integrable (fun w => c * f w) := by
  simpa only [Integrable, mul_left_comm] using hf.const_mul c
lemma contour_const_mul (p : Piece) (c : ℂ) {f : ℂ → ℂ}
    (_hf : p.Integrable f) : p.contour (fun w => c * f w) = c * p.contour f := by
  simp only [contour, mul_left_comm, intervalIntegral.integral_const_mul]

lemma integrable_sum (p : Piece) {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, p.Integrable (f i)) : p.Integrable (fun w => ∑ i ∈ s, f i w) := by
  have hi := IntervalIntegrable.sum s hf
  unfold Integrable
  convert hi using 1 <;> first | rfl | (ext t; simp only [Finset.sum_apply, Finset.mul_sum])
lemma contour_sum (p : Piece) {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, p.Integrable (f i)) :
    p.contour (fun w => ∑ i ∈ s, f i w) = ∑ i ∈ s, p.contour (f i) := by
  simp only [contour, Finset.mul_sum]
  exact intervalIntegral.integral_finsetSum hf

lemma reflection_mem (p : Piece) {t : ℝ} (ht : t ∈ Icc p.a p.b) :
    p.a + p.b - t ∈ Icc p.a p.b := by
  constructor <;> linarith [ht.1, ht.2]

def reverse (p : Piece) : Piece where
  a := p.a
  b := p.b
  lt := p.lt
  curve := fun t => p.curve (p.a + p.b - t)
  velocity := fun t => -p.velocity (p.a + p.b - t)
  continuous_curve := p.continuous_curve.comp
    (continuous_const.sub continuous_id).continuousOn (fun _ ht => p.reflection_mem ht)
  continuous_velocity := (p.continuous_velocity.comp
    (continuous_const.sub continuous_id).continuousOn (fun _ ht => p.reflection_mem ht)).neg
  derivative := by
    intro t ht
    have hr : HasDerivWithinAt (fun s : ℝ => p.a + p.b - s) (-1) (Icc p.a p.b) t :=
      ((hasDerivAt_id t).const_sub (p.a + p.b)).hasDerivWithinAt
    convert (p.derivative _ (p.reflection_mem ht)).scomp t hr
      (fun _ hs => p.reflection_mem hs) using 1 <;> first | rfl | simp

@[simp] lemma reverse_start (p : Piece) : p.reverse.start = p.finish := by
  simp [reverse, start, finish]
@[simp] lemma reverse_finish (p : Piece) : p.reverse.finish = p.start := by
  simp [reverse, start, finish]
lemma reverse_avoids (p : Piece) {z : ℂ} (h : p.Avoids z) : p.reverse.Avoids z :=
  fun _ ht => h _ (p.reflection_mem ht)
lemma reverse_integrable (p : Piece) {f : ℂ → ℂ} (h : p.Integrable f) :
    p.reverse.Integrable f := by
  have hr := (h.comp_sub_left (p.a + p.b)).symm.neg
  change IntervalIntegrable (fun x => -(p.velocity (p.a + p.b - x) *
    f (p.curve (p.a + p.b - x)))) _ _ _ at hr
  simpa only [Integrable, reverse, add_sub_cancel_left, add_sub_cancel_right, neg_mul] using hr
lemma reverse_contour (p : Piece) {f : ℂ → ℂ} (_h : p.Integrable f) :
    p.reverse.contour f = -p.contour f := by
  simp only [contour, reverse, neg_mul, intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_comp_sub_left
    (fun t => p.velocity t * f (p.curve t))]
  simp

def constant (z : ℂ) : Piece where
  a := 0
  b := 1
  lt := zero_lt_one
  curve := fun _ => z
  velocity := fun _ => 0
  continuous_curve := continuousOn_const
  continuous_velocity := continuousOn_const
  derivative := fun _ _ => hasDerivWithinAt_const _ _ _
@[simp] lemma constant_start (z : ℂ) : (constant z).start = z := rfl
@[simp] lemma constant_finish (z : ℂ) : (constant z).finish = z := rfl
lemma constant_integrable (z : ℂ) (f : ℂ → ℂ) : (constant z).Integrable f := by
  simp only [Integrable, constant, zero_mul]
  exact intervalIntegrable_const
@[simp] lemma constant_contour (z : ℂ) (f : ℂ → ℂ) : (constant z).contour f = 0 := by
  simp [contour, constant]

end Piece
end KsIndex.Piecewise
