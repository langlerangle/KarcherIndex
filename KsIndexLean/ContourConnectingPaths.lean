module

public import KsIndexLean.ContourChainOperations
public import KsIndexLean.FiniteObstacleWaypoint

@[expose] public section


/-! Two actual certified straight pieces connect points outside a finite obstacle set. -/
noncomputable section
namespace KsIndex.Piecewise
open Set

def linePiece (a b : ℂ) : Piece where
  a := 0
  b := 1
  lt := by norm_num
  curve := fun t => a + (t : ℂ) * (b - a)
  velocity := fun _ => b - a
  continuous_curve :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
  continuous_velocity := continuousOn_const
  derivative := by
    intro t _
    have hd : HasDerivAt (fun t : ℝ => a + (t : ℂ) * (b - a)) (b - a) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const (b - a)).const_add a
    exact hd.hasDerivWithinAt

@[simp] lemma linePiece_start (a b : ℂ) : (linePiece a b).start = a := by
  simp [Piece.start, linePiece]
@[simp] lemma linePiece_finish (a b : ℂ) : (linePiece a b).finish = b := by
  simp [Piece.finish, linePiece]

lemma linePiece_avoids {a b z : ℂ}
    (h : ∀ s : ℝ, z ≠ a + (s : ℂ) * (b - a)) : (linePiece a b).Avoids z := by
  intro t _ he
  exact h t he.symm

/-- Construct the second segment in reverse, using the waypoint condition based at y. -/
theorem exists_chain_avoiding_finset (S : Finset ℂ) (x y : ℂ)
    (hx : x ∉ S) (hy : y ∉ S) :
    ∃ C : Chain, C.start = x ∧ C.finish = y ∧ (∀ z ∈ S, C.Avoids z) := by
  obtain ⟨c, hxc, hyc⟩ := exists_finite_obstacle_waypoint S x y hx hy
  let C := Chain.singleton (linePiece x c)
  let D := (Chain.singleton (linePiece y c)).reverse
  have hj : C.finish = D.start := by simp [C, D]
  refine ⟨C.append D hj, ?_, ?_, ?_⟩
  · simp [C]
  · simp [D]
  · intro z hz
    apply Chain.append_avoids
    · exact Chain.singleton_avoids _ (linePiece_avoids (hxc z hz))
    · exact Chain.reverse_avoids _ (Chain.singleton_avoids _ (linePiece_avoids (hyc z hz)))

end KsIndex.Piecewise
