module

public import Mathlib.Topology.UnitInterval
public import KsIndexLean.CellDiskCoordinates

@[expose] public section


/-! Standard one-cell coordinates on a nondegenerate real interval. -/
noncomputable section
open Set Metric Topology
namespace KsIndex

lemma norm_fin_one (x : Fin 1 → ℝ) : ‖x‖ = |x 0| := by
  have he : x = fun _ => x 0 := by funext i; congr 1; exact Subsingleton.elim _ _
  rw [he]
  simp

/-- Evaluation identifies the closed one-cell with the interval [-1,1]. -/
def cellUnitIntervalHomeomorph : closedBall (0 : Fin 1 → ℝ) 1 ≃ₜ Icc (-1 : ℝ) 1 where
  toFun x := ⟨x.val 0, by
    have hx := x.property
    rw [mem_closedBall, dist_zero_right, norm_fin_one, abs_le] at hx
    exact hx⟩
  invFun t := ⟨fun _ => t.val, by
    rw [mem_closedBall, dist_zero_right, norm_fin_one, abs_le]
    exact t.property⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg x.val (Subsingleton.elim _ _)
  right_inv t := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_apply 0).comp continuous_subtype_val
  continuous_invFun := by fun_prop

/-- Coordinates on any nondegenerate interval, compatible with its endpoints. -/
def cellIntervalCoordinates (a b : ℝ) (hab : a < b) :
    closedBall (0 : Fin 1 → ℝ) 1 ≃ₜ Icc a b :=
  cellUnitIntervalHomeomorph.trans ((iccHomeoI (-1) 1 (by norm_num)).trans (iccHomeoI a b hab).symm)

lemma cellIntervalCoordinates_val (a b : ℝ) (hab : a < b)
    (x : closedBall (0 : Fin 1 → ℝ) 1) :
    (cellIntervalCoordinates a b hab x).val = (b - a) * ((x.val 0 + 1) / 2) + a := by
  change (b - a) * ((x.val 0 - (-1)) / (1 - (-1))) + a = _
  ring

lemma cellIntervalCoordinates_interior (a b : ℝ) (hab : a < b)
    (x : closedBall (0 : Fin 1 → ℝ) 1) :
    (cellIntervalCoordinates a b hab x).val ∈ Ioo a b ↔ ‖x.val‖ < 1 := by
  rw [cellIntervalCoordinates_val, norm_fin_one, abs_lt]
  constructor
  · intro hx
    constructor <;> nlinarith [hx.1, hx.2]
  · intro hx
    constructor <;> nlinarith [hx.1, hx.2]

lemma cellIntervalCoordinates_boundary (a b : ℝ) (hab : a < b)
    (x : closedBall (0 : Fin 1 → ℝ) 1) (hx : ‖x.val‖ = 1) :
    (cellIntervalCoordinates a b hab x).val = a ∨
      (cellIntervalCoordinates a b hab x).val = b := by
  rw [norm_fin_one, abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at hx
  rw [cellIntervalCoordinates_val]
  rcases hx with hx | hx
  · right; rw [hx]; ring
  · left; rw [hx]; ring

end KsIndex
