module

public import KsIndexLean.ContourChainOperations

@[expose] public section


/-! Natural repetition uses actual certified concatenation at a closed chain's start. -/
noncomputable section
namespace KsIndex.Piecewise.Chain

def repeatBased (C : Chain) (hc : C.IsClosed) :
    ℕ → {D : Chain // D.IsClosed ∧ D.start = C.start}
  | 0 => ⟨identity C.start, identity_closed _, identity_start _⟩
  | n + 1 =>
    let D := repeatBased C hc n
    ⟨D.val.append C (D.property.1.trans D.property.2),
      D.val.append_closed C D.property.1 hc D.property.2,
      (append_start _ _ _).trans D.property.2⟩

def natRepeat (C : Chain) (hc : C.IsClosed) (n : ℕ) : Chain := (repeatBased C hc n).val

lemma repeat_closed (C : Chain) (hc : C.IsClosed) (n : ℕ) :
    (C.natRepeat hc n).IsClosed := (repeatBased C hc n).property.1

@[simp] lemma repeat_start (C : Chain) (hc : C.IsClosed) (n : ℕ) :
    (C.natRepeat hc n).start = C.start := (repeatBased C hc n).property.2

@[simp] lemma repeat_zero (C : Chain) (hc : C.IsClosed) :
    C.natRepeat hc 0 = identity C.start := rfl

lemma repeat_succ (C : Chain) (hc : C.IsClosed) (n : ℕ) :
    C.natRepeat hc (n + 1) = (C.natRepeat hc n).append C
      ((C.repeat_closed hc n).trans (C.repeat_start hc n)) := rfl

lemma repeat_avoids (C : Chain) (hc : C.IsClosed) {z : ℂ} (ha : C.Avoids z)
    (n : ℕ) : (C.natRepeat hc n).Avoids z := by
  induction n with
  | zero => exact identity_avoids (C.start_ne ha)
  | succ n ih => rw [repeat_succ]; exact append_avoids _ _ _ ih ha

lemma repeat_integrable (C : Chain) (hc : C.IsClosed) {f : ℂ → ℂ}
    (hf : C.Integrable f) (n : ℕ) : (C.natRepeat hc n).Integrable f := by
  induction n with
  | zero => exact identity_integrable _ _
  | succ n ih => rw [repeat_succ]; exact append_integrable _ _ _ ih hf

lemma repeat_contour (C : Chain) (hc : C.IsClosed) {f : ℂ → ℂ}
    (hf : C.Integrable f) (n : ℕ) :
    (C.natRepeat hc n).contour f = (n : ℂ) * C.contour f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [repeat_succ, append_contour _ _ _ (C.repeat_integrable hc hf n) hf, ih]
    push_cast
    ring

end KsIndex.Piecewise.Chain
