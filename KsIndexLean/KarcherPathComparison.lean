module

public import KsIndexLean.KarcherPeriodSet

@[expose] public section


/-! Common-endpoint path integrals agree modulo the certified vertical period lattice.
This is consistency only: no connecting-path existence, quotient map, or surface cover.
The finite punctured chart is not identified here with the disk/seam model. -/
noncomputable section
namespace KsIndex.KarcherData
open Piecewise

/-- Traverse C forward, then D backward. Only the common finish is needed to join. -/
def comparisonLoop (C D : Chain) (ht : C.finish = D.finish) : Chain :=
  C.append D.reverse (ht.trans (Chain.reverse_start D).symm)

lemma comparisonLoop_closed (C D : Chain) (hs : C.start = D.start)
    (ht : C.finish = D.finish) : (comparisonLoop C D ht).IsClosed := by
  simpa only [comparisonLoop, Chain.IsClosed, Chain.append_finish,
    Chain.append_start, Chain.reverse_finish] using hs.symm

lemma comparisonLoop_avoids (C D : Chain) (ht : C.finish = D.finish) {z : ℂ}
    (hC : C.Avoids z) (hD : D.Avoids z) : (comparisonLoop C D ht).Avoids z :=
  C.append_avoids D.reverse _ hC (D.reverse_avoids hD)

lemma periodVector_comparisonLoop {k : ℕ} (hk : 2 ≤ k) (C D : Chain)
    (ht : C.finish = D.finish)
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z)
    (hD : ∀ z ∈ Surface.punctures k, D.Avoids z) :
    periodVector k (comparisonLoop C D ht) = periodVector k C - periodVector k D := by
  rw [comparisonLoop, periodVector_append hk C D.reverse _ hC
    (fun z hz => D.reverse_avoids (hD z hz)), periodVector_reverse hk D hD]
  rfl

/-- Explicit index of the actual closed comparison chain; neither input must be closed. -/
theorem path_difference_eq_index {k : ℕ} (hk : 2 ≤ k) (C D : Chain)
    (hs : C.start = D.start) (ht : C.finish = D.finish)
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z)
    (hD : ∀ z ∈ Surface.punctures k, D.Avoids z) :
    periodVector k C - periodVector k D =
      (0, 0, (2 * Real.pi) * (periodIndex hk (comparisonLoop C D ht)
        (comparisonLoop_closed C D hs ht)
        (fun z hz => comparisonLoop_avoids C D ht (hC z hz) (hD z hz)) : ℝ)) := by
  rw [← periodVector_comparisonLoop hk C D ht hC hD]
  exact periodVector_eq_index hk _ _ _

/-- Same endpoints and avoidance suffice for agreement modulo the vertical lattice. -/
theorem path_difference_mem_lattice {k : ℕ} (hk : 2 ≤ k) (C D : Chain)
    (hs : C.start = D.start) (ht : C.finish = D.finish)
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z)
    (hD : ∀ z ∈ Surface.punctures k, D.Avoids z) :
    ∃ n : ℤ, periodVector k C - periodVector k D =
      (0, 0, (2 * Real.pi) * (n : ℝ)) :=
  ⟨_, path_difference_eq_index hk C D hs ht hC hD⟩

theorem path_horizontal_eq {k : ℕ} (hk : 2 ≤ k) (C D : Chain)
    (hs : C.start = D.start) (ht : C.finish = D.finish)
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z)
    (hD : ∀ z ∈ Surface.punctures k, D.Avoids z) :
    (C.contour (coeff1 k)).re = (D.contour (coeff1 k)).re ∧
    (C.contour (coeff2 k)).re = (D.contour (coeff2 k)).re := by
  obtain ⟨n, hn⟩ := path_difference_mem_lattice hk C D hs ht hC hD
  have h1 := congrArg Prod.fst hn
  have h2 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) hn
  change (C.contour (coeff1 k)).re - (D.contour (coeff1 k)).re = 0 at h1
  change (C.contour (coeff2 k)).re - (D.contour (coeff2 k)).re = 0 at h2
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

theorem path_vertical_difference {k : ℕ} (hk : 2 ≤ k) (C D : Chain)
    (hs : C.start = D.start) (ht : C.finish = D.finish)
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z)
    (hD : ∀ z ∈ Surface.punctures k, D.Avoids z) :
    ∃ n : ℤ, (C.contour (coeff3 k)).re - (D.contour (coeff3 k)).re =
      (2 * Real.pi) * (n : ℝ) := by
  obtain ⟨n, hn⟩ := path_difference_mem_lattice hk C D hs ht hC hD
  exact ⟨n, congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) hn⟩

end KsIndex.KarcherData
