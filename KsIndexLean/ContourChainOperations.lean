module

public import KsIndexLean.ContourChain

@[expose] public section


/-! Concatenation of certified finite chains and its integral and winding laws. -/
open scoped BigOperators
noncomputable section
namespace KsIndex.Piecewise.Chain

def append (C D : Chain) (h : C.finish = D.start) : Chain where
  n := C.n + 1 + D.n
  piece := Fin.append (m := C.n + 1) (n := D.n + 1) C.piece D.piece
  matching := by
    intro i
    refine Fin.addCases (m := C.n + 1) (n := D.n) ?_ ?_ i
    · intro j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · change (Fin.append C.piece D.piece
          ((Fin.last C.n).castAdd (D.n + 1))).finish = _
        rw [Fin.append_left]
        have he : ((Fin.last C.n).castAdd D.n).succ =
            Fin.natAdd (C.n + 1) (0 : Fin (D.n + 1)) := by ext; simp
        rw [he, Fin.append_right]
        exact h
      · change (Fin.append C.piece D.piece (k.castSucc.castAdd (D.n + 1))).finish =
          (Fin.append C.piece D.piece (k.succ.castAdd (D.n + 1))).start
        simpa only [Fin.append_left] using C.matching k
    · intro j
      change (Fin.append C.piece D.piece (j.castSucc.natAdd (C.n + 1))).finish =
        (Fin.append C.piece D.piece (j.succ.natAdd (C.n + 1))).start
      simpa only [Fin.append_right] using D.matching j

@[simp] lemma append_start (C D : Chain) (h : C.finish = D.start) :
    (C.append D h).start = C.start := by
  change (Fin.append C.piece D.piece ((0 : Fin (C.n + 1)).castAdd (D.n + 1))).start = _
  simp [start]
@[simp] lemma append_finish (C D : Chain) (h : C.finish = D.start) :
    (C.append D h).finish = D.finish := by
  change (Fin.append C.piece D.piece ((Fin.last D.n).natAdd (C.n + 1))).finish = _
  rw [Fin.append_right]
  rfl

lemma append_avoids (C D : Chain) (h : C.finish = D.start) {z : ℂ}
    (hC : C.Avoids z) (hD : D.Avoids z) : (C.append D h).Avoids z := by
  intro i
  refine Fin.addCases (m := C.n + 1) (n := D.n + 1) ?_ ?_ i
  · intro j; simpa only [append, Fin.append_left] using hC j
  · intro j; simpa only [append, Fin.append_right] using hD j
lemma append_integrable (C D : Chain) (h : C.finish = D.start) {f : ℂ → ℂ}
    (hC : C.Integrable f) (hD : D.Integrable f) : (C.append D h).Integrable f := by
  intro i
  refine Fin.addCases (m := C.n + 1) (n := D.n + 1) ?_ ?_ i
  · intro j; simpa only [append, Fin.append_left] using hC j
  · intro j; simpa only [append, Fin.append_right] using hD j
lemma append_contour (C D : Chain) (h : C.finish = D.start) {f : ℂ → ℂ}
    (_hC : C.Integrable f) (_hD : D.Integrable f) :
    (C.append D h).contour f = C.contour f + D.contour f := by
  change (∑ i : Fin ((C.n + 1) + (D.n + 1)),
    (Fin.append C.piece D.piece i).contour f) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, contour]
lemma append_closed (C D : Chain) (hC : C.IsClosed) (hD : D.IsClosed)
    (hb : C.start = D.start) : (C.append D (hC.trans hb)).IsClosed := by
  simp only [IsClosed, append_start, append_finish]
  exact hD.trans hb.symm
lemma append_winding (C D : Chain) (hC : C.IsClosed) (hD : D.IsClosed)
    (hb : C.start = D.start) (z : ℂ) (haC : C.Avoids z) (haD : D.Avoids z) :
    (C.append D (hC.trans hb)).winding (C.append_closed D hC hD hb) z
      (C.append_avoids D _ haC haD) = C.winding hC z haC + D.winding hD z haD := by
  apply winding_eq_of_integral
  rw [logIntegral, append_contour _ _ _ (C.integrable_reciprocal haC)
    (D.integrable_reciprocal haD)]
  rw [← logIntegral, ← logIntegral, C.logIntegral_eq_winding hC z haC,
    D.logIntegral_eq_winding hD z haD]
  push_cast
  ring

/-- The identity is a certified constant piece, not a degenerate parameter interval. -/
def identity (z : ℂ) : Chain := singleton (Piece.constant z)
@[simp] lemma identity_start (z : ℂ) : (identity z).start = z := rfl
@[simp] lemma identity_finish (z : ℂ) : (identity z).finish = z := rfl
lemma identity_closed (z : ℂ) : (identity z).IsClosed := rfl
lemma identity_avoids {w z : ℂ} (h : w ≠ z) : (identity w).Avoids z :=
  fun _ _ _ => h
lemma identity_integrable (w : ℂ) (f : ℂ → ℂ) : (identity w).Integrable f :=
  singleton_integrable _ (Piece.constant_integrable w f)
@[simp] lemma identity_contour (w : ℂ) (f : ℂ → ℂ) : (identity w).contour f = 0 := by
  simp [identity]
lemma identity_winding {w z : ℂ} (h : w ≠ z) :
    (identity w).winding (identity_closed w) z (identity_avoids h) = 0 := by
  apply winding_eq_of_integral
  simp [logIntegral]

end KsIndex.Piecewise.Chain
