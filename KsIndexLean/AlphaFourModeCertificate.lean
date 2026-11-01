module

public import KsIndexLean.AlphaStarPositiveBound

@[expose] public section


/-! Exact finite algebra for a four-mode positive certificate at s=11/8.
This module proves positivity of the finite rational matrix. Its relation to
the infinite Fourier operator is established in the Gram and pairing modules;
`AlphaFourModePositivity` assembles positivity of gamma(11/8). -/
noncomputable section
namespace KsIndex.AlphaFourMode

/-- Conservative rational matrix form for the four retained modes. -/
def certificateForm (x : Fin 4 → ℝ) : ℝ :=
    (18208422751 / 214742088000 : ℝ) * x 0 * x 0 +
    (-14067 / 6162250 : ℝ) * x 0 * x 1 +
    (112247 / 12324500 : ℝ) * x 0 * x 2 +
    (-76169 / 12324500 : ℝ) * x 0 * x 3 +
    (250319501 / 71580696000 : ℝ) * x 1 * x 1 +
    (-98179 / 6162250 : ℝ) * x 1 * x 2 +
    (25047 / 3081125 : ℝ) * x 1 * x 3 +
    (4140583679 / 214742088000 : ℝ) * x 2 * x 2 +
    (-1004 / 3081125 : ℝ) * x 2 * x 3 +
    (13565293669 / 71580696000 : ℝ) * x 3 * x 3

/-- Positive diagonal coefficients of the rational square decomposition. -/
def pivots : Fin 4 → ℝ := ![(18208422751 / 214742088000 : ℝ),
    (4537898070156295763 / 1303371573578814696000 : ℝ),
    (1061841291072197908757626477 / 974477706716533438492173144000 : ℝ),
    (8218998507821034530116584670913304769 / 76007338656486512558615398531687992000 : ℝ)]
/-- Triangular change of coordinates in the rational square decomposition. -/
def transformed (x : Fin 4 → ℝ) : Fin 4 → ℝ := ![x 0 + (-245103408 / 18208422751 : ℝ) * x 1 + (977895864 / 18208422751 : ℝ) * x 2 + (-663584328 / 18208422751 : ℝ) * x 3,
    x 1 + (-10302977751088150128 / 4537898070156295763 : ℝ) * x 2 + (5243451298278757344 / 4537898070156295763 : ℝ) * x 3,
    x 2 + (8903751176120504784217068096 / 1061841291072197908757626477 : ℝ) * x 3,
    x 3]

private lemma pivots_pos (i : Fin 4) : 0 < pivots i := by
  fin_cases i <;> norm_num [pivots]

private lemma transformed_injective : Function.Injective transformed := by
  intro x z h
  have e3 : x 3 = z 3 := by simpa [transformed] using congrFun h 3
  have e2 : x 2 = z 2 := by simpa [transformed, e3] using congrFun h 2
  have e1 : x 1 = z 1 := by simpa [transformed, e3, e2] using congrFun h 1
  have e0 : x 0 = z 0 := by simpa [transformed, e3, e2, e1] using congrFun h 0
  funext i
  fin_cases i <;> assumption

/-- Exact LDL square decomposition; all coefficients are rational. -/
lemma certificateForm_eq_squares (x : Fin 4 → ℝ) :
    certificateForm x = ∑ i : Fin 4, pivots i * (transformed x i)^2 := by
  simp [certificateForm, pivots, transformed, Fin.sum_univ_succ]
  ring

/-- Strict positivity of the finite matrix from its exact rational square decomposition. -/
theorem certificateForm_pos {x : Fin 4 → ℝ} (hx : x ≠ 0) : 0 < certificateForm x := by
  have hy : transformed x ≠ 0 := by
    intro h
    have hzero : transformed (0 : Fin 4 → ℝ) = 0 := by ext i; fin_cases i <;> simp [transformed]
    exact hx (transformed_injective (h.trans hzero.symm))
  obtain ⟨i, hi⟩ : ∃ i, transformed x i ≠ 0 := by
    by_contra! h
    exact hy (funext h)
  rw [certificateForm_eq_squares]
  exact Finset.sum_pos' (fun j _ => mul_nonneg (pivots_pos j).le (sq_nonneg _))
    ⟨i, Finset.mem_univ i, mul_pos (pivots_pos i) (sq_pos_of_ne_zero hi)⟩

end KsIndex.AlphaFourMode
