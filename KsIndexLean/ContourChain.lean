module

public import KsIndexLean.ContourPiece
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section


/-! Finite composable chains of certified pieces, with actual contour integrals. -/
open Set
open scoped BigOperators
noncomputable section

namespace KsIndex.Piecewise

structure Chain where
  n : ℕ
  piece : Fin (n + 1) → Piece
  matching : ∀ i : Fin n, (piece i.castSucc).finish = (piece i.succ).start

namespace Chain

def start (C : Chain) : ℂ := (C.piece 0).start
def finish (C : Chain) : ℂ := (C.piece (Fin.last C.n)).finish
def image (C : Chain) : Set ℂ := ⋃ i, (C.piece i).image
def Avoids (C : Chain) (z : ℂ) : Prop := ∀ i, (C.piece i).Avoids z
def Integrable (C : Chain) (f : ℂ → ℂ) : Prop := ∀ i, (C.piece i).Integrable f
def contour (C : Chain) (f : ℂ → ℂ) : ℂ := ∑ i, (C.piece i).contour f
def logIntegral (C : Chain) (z : ℂ) : ℂ := C.contour (fun w => (w - z)⁻¹)
def IsClosed (C : Chain) : Prop := C.finish = C.start

lemma integrable_of_continuousOn (C : Chain) {f : ℂ → ℂ}
    (hf : ContinuousOn f C.image) : C.Integrable f := by
  intro i
  apply (C.piece i).integrable_of_continuousOn
  exact hf.mono (by intro w hw; exact Set.mem_iUnion.mpr ⟨i, hw⟩)
lemma integrable_reciprocal (C : Chain) {z : ℂ} (h : C.Avoids z) :
    C.Integrable (fun w => (w - z)⁻¹) := fun i => (C.piece i).integrable_reciprocal (h i)
lemma start_ne (C : Chain) {z : ℂ} (h : C.Avoids z) : C.start ≠ z :=
  (C.piece 0).start_ne (h 0)
lemma finish_ne (C : Chain) {z : ℂ} (h : C.Avoids z) : C.finish ≠ z :=
  (C.piece (Fin.last C.n)).finish_ne (h _)

lemma integrable_add (C : Chain) {f g : ℂ → ℂ}
    (hf : C.Integrable f) (hg : C.Integrable g) : C.Integrable (fun w => f w + g w) :=
  fun i => (C.piece i).integrable_add (hf i) (hg i)
lemma contour_add (C : Chain) {f g : ℂ → ℂ}
    (hf : C.Integrable f) (hg : C.Integrable g) :
    C.contour (fun w => f w + g w) = C.contour f + C.contour g := by
  simp only [contour, fun i => (C.piece i).contour_add (hf i) (hg i), Finset.sum_add_distrib]
lemma integrable_const_mul (C : Chain) (c : ℂ) {f : ℂ → ℂ}
    (hf : C.Integrable f) : C.Integrable (fun w => c * f w) :=
  fun i => (C.piece i).integrable_const_mul c (hf i)
lemma contour_const_mul (C : Chain) (c : ℂ) {f : ℂ → ℂ}
    (hf : C.Integrable f) : C.contour (fun w => c * f w) = c * C.contour f := by
  simp only [contour, fun i => (C.piece i).contour_const_mul c (hf i), Finset.mul_sum]

lemma integrable_sum (C : Chain) {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, C.Integrable (f i)) : C.Integrable (fun w => ∑ i ∈ s, f i w) :=
  fun j => (C.piece j).integrable_sum s (fun i hi => hf i hi j)
lemma contour_sum (C : Chain) {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ s, C.Integrable (f i)) :
    C.contour (fun w => ∑ i ∈ s, f i w) = ∑ i ∈ s, C.contour (f i) := by
  simp only [contour,
    fun j => (C.piece j).contour_sum s (fun i hi => hf i hi j)]
  exact Finset.sum_comm

lemma exp_sum_transport {n : ℕ} (p : Fin (n + 1) → Piece) (z : ℂ)
    (hm : ∀ i : Fin n, (p i.castSucc).finish = (p i.succ).start)
    (ha : ∀ i, (p i).Avoids z) :
    Complex.exp (∑ i, (p i).contour (fun w => (w - z)⁻¹)) =
      ((p (Fin.last n)).finish - z) / ((p 0).start - z) := by
  induction n with
  | zero => simpa using (p 0).exp_contour_reciprocal (ha 0)
  | succ n ih =>
    rw [Fin.sum_univ_succ, Complex.exp_add, (p 0).exp_contour_reciprocal (ha 0)]
    rw [ih (fun i => p i.succ) (fun i => hm i.succ) (fun i => ha i.succ)]
    have hj := hm (0 : Fin (n + 1))
    simp only [Fin.castSucc_zero] at hj
    rw [hj]
    have hn := sub_ne_zero.mpr ((p (Fin.succ 0)).start_ne (ha _))
    have hl : (Fin.last n).succ = Fin.last (n + 1) := rfl
    rw [hl]
    field_simp

lemma exp_logIntegral (C : Chain) {z : ℂ} (h : C.Avoids z) :
    Complex.exp (C.logIntegral z) = (C.finish - z) / (C.start - z) :=
  exp_sum_transport C.piece z C.matching h

lemma unique_integer (C : Chain) (hc : C.IsClosed) {z : ℂ} (h : C.Avoids z) :
    ∃! n : ℤ, C.logIntegral z = (n : ℂ) * (2 * Real.pi * Complex.I) := by
  have he := C.exp_logIntegral h
  rw [show C.finish = C.start from hc, div_self (sub_ne_zero.mpr (C.start_ne h))] at he
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  refine ⟨n, hn, ?_⟩
  intro m hm
  exact_mod_cast (mul_right_cancel₀ Complex.two_pi_I_ne_zero (hm.symm.trans hn))

def winding (C : Chain) (hc : C.IsClosed) (z : ℂ) (h : C.Avoids z) : ℤ :=
  (C.unique_integer hc h).exists.choose
lemma logIntegral_eq_winding (C : Chain) (hc : C.IsClosed) (z : ℂ) (h : C.Avoids z) :
    C.logIntegral z = (C.winding hc z h : ℂ) * (2 * Real.pi * Complex.I) :=
  (C.unique_integer hc h).exists.choose_spec
lemma winding_eq_of_integral (C : Chain) (hc : C.IsClosed) (z : ℂ) (h : C.Avoids z)
    (n : ℤ) (hn : C.logIntegral z = (n : ℂ) * (2 * Real.pi * Complex.I)) :
    C.winding hc z h = n :=
  (C.unique_integer hc h).unique (C.logIntegral_eq_winding hc z h) hn

lemma winding_proof_independent (C : Chain) (hc hc' : C.IsClosed) (z : ℂ)
    (h h' : C.Avoids z) : C.winding hc z h = C.winding hc' z h' := rfl

def singleton (p : Piece) : Chain where
  n := 0
  piece := fun _ => p
  matching := Fin.elim0
@[simp] lemma singleton_start (p : Piece) : (singleton p).start = p.start := rfl
@[simp] lemma singleton_finish (p : Piece) : (singleton p).finish = p.finish := rfl
@[simp] lemma singleton_contour (p : Piece) (f : ℂ → ℂ) :
    (singleton p).contour f = p.contour f := by
  change (∑ _ : Fin 1, p.contour f) = p.contour f
  rw [Fin.sum_univ_one]
lemma singleton_integrable (p : Piece) {f : ℂ → ℂ} (h : p.Integrable f) :
    (singleton p).Integrable f := fun _ => h
lemma singleton_avoids (p : Piece) {z : ℂ} (h : p.Avoids z) :
    (singleton p).Avoids z := fun _ => h

def reverse (C : Chain) : Chain where
  n := C.n
  piece := fun i => (C.piece i.rev).reverse
  matching := by
    intro i
    simpa only [Fin.rev_castSucc, Fin.rev_succ, Piece.reverse_start,
      Piece.reverse_finish] using (C.matching i.rev).symm
@[simp] lemma reverse_start (C : Chain) : C.reverse.start = C.finish := by
  change (C.piece ((0 : Fin (C.n + 1)).rev)).reverse.start = C.finish
  rw [Piece.reverse_start, Fin.rev_zero]
  rfl
@[simp] lemma reverse_finish (C : Chain) : C.reverse.finish = C.start := by
  change (C.piece (Fin.last C.n).rev).reverse.finish = C.start
  rw [Piece.reverse_finish, Fin.rev_last]
  rfl
lemma reverse_closed (C : Chain) (h : C.IsClosed) : C.reverse.IsClosed := by
  simpa [IsClosed] using h.symm
lemma reverse_avoids (C : Chain) {z : ℂ} (h : C.Avoids z) : C.reverse.Avoids z :=
  fun i => (C.piece i.rev).reverse_avoids (h _)
lemma reverse_integrable (C : Chain) {f : ℂ → ℂ} (h : C.Integrable f) :
    C.reverse.Integrable f := fun i => (C.piece i.rev).reverse_integrable (h _)
lemma reverse_contour (C : Chain) {f : ℂ → ℂ} (h : C.Integrable f) :
    C.reverse.contour f = -C.contour f := by
  simp only [contour, reverse,
    fun (i : Fin (C.n + 1)) => (C.piece i.rev).reverse_contour (h _), Finset.sum_neg_distrib]
  congr 1
  exact Equiv.sum_comp (Fin.revPerm) (fun i => (C.piece i).contour f)
lemma reverse_winding (C : Chain) (hc : C.IsClosed) (z : ℂ) (h : C.Avoids z) :
    C.reverse.winding (C.reverse_closed hc) z (C.reverse_avoids h) = -C.winding hc z h := by
  apply C.reverse.winding_eq_of_integral
  rw [logIntegral, C.reverse_contour (C.integrable_reciprocal h)]
  rw [← logIntegral, C.logIntegral_eq_winding hc z h]
  simp

end Chain
end KsIndex.Piecewise
