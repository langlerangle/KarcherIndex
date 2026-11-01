module

public import KsIndexLean.KarcherPlanePreimage

@[expose] public section


/-! Angular sector lemmas for the checkerboard containment. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex Set

lemma cos_nonpos_sector {x : ℝ} (hx : Real.cos x ≤ 0) :
    ∃ j : ℤ, (1 / 2 + 2 * (j : ℝ)) * Real.pi ≤ x ∧
      x ≤ (3 / 2 + 2 * (j : ℝ)) * Real.pi := by
  let j : ℤ := ⌊(x - Real.pi / 2) / (2 * Real.pi)⌋
  have hp : 0 < 2 * Real.pi := by positivity
  have hlo := (le_div_iff₀ hp).mp (Int.floor_le ((x - Real.pi / 2) / (2 * Real.pi)))
  have hhi := (div_lt_iff₀ hp).mp (Int.lt_floor_add_one ((x - Real.pi / 2) / (2 * Real.pi)))
  change (j : ℝ) * (2 * Real.pi) ≤ x - Real.pi / 2 at hlo
  change x - Real.pi / 2 < ((j : ℝ) + 1) * (2 * Real.pi) at hhi
  refine ⟨j, by nlinarith, ?_⟩
  by_contra hn
  have hpos : 0 < Real.cos (x - ((j : ℝ) + 1) * (2 * Real.pi)) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith⟩
  have he : Real.cos (x - ((j : ℝ) + 1) * (2 * Real.pi)) = Real.cos x := by
    have hh := Real.cos_add_int_mul_two_pi (x - ((j : ℝ) + 1) * (2 * Real.pi)) (j + 1)
    push_cast at hh
    convert hh.symm using 1
    congr 1
    ring
  rw [he] at hpos
  linarith

lemma polar_rotated_im (z : ℂ) (t : ℝ) :
    (Complex.exp ((t : ℂ) * I) * z).im = ‖z‖ * Real.sin (t + z.arg) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [show Complex.exp ((t : ℂ) * I) * ((‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * I)) =
      (‖z‖ : ℂ) * Complex.exp (((t + z.arg : ℝ) : ℂ) * I) by
    rw [mul_left_comm, ← Complex.exp_add]; congr 2; push_cast; ring]
  rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

lemma rotated_mul (s t : ℝ) (z : ℂ) :
    Complex.exp ((s : ℂ) * I) * (Complex.exp ((t : ℂ) * I) * z) =
      Complex.exp (((s + t : ℝ) : ℂ) * I) * z := by
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Two oriented half-plane inequalities give a polar angle in `[l, u]` when
`l < u`. The origin is allowed. -/
theorem polar_of_sector_sides {z : ℂ} {l u : ℝ}
    (hlu : l < u)
    (hl : 0 ≤ (Complex.exp (((-l : ℝ) : ℂ) * I) * z).im)
    (hu : (Complex.exp (((-u : ℝ) : ℂ) * I) * z).im ≤ 0) :
    ∃ θ ∈ Icc l u, z = (‖z‖ : ℂ) * Complex.exp ((θ : ℂ) * I) := by
  by_cases hz : z = 0
  · exact ⟨l, ⟨le_rfl, hlu.le⟩, by simp [hz]⟩
  let v := Complex.exp (((-l : ℝ) : ℂ) * I) * z
  have hv0 : v ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hz
  have hvnorm : ‖v‖ = ‖z‖ := by
    dsimp only [v]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have ha0 : 0 ≤ v.arg := Complex.arg_nonneg_iff.mpr hl
  have hau : v.arg ≤ u - l := by
    by_contra hn
    have hp : 0 < Real.sin (v.arg - (u - l)) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Complex.arg_le_pi v])
    have he : (Complex.exp (((-(u - l) : ℝ) : ℂ) * I) * v).im =
        (Complex.exp (((-u : ℝ) : ℂ) * I) * z).im := by
      dsimp [v]
      rw [rotated_mul, show -(u - l) + -l = -u by ring]
    have hh := polar_rotated_im v (-(u - l))
    rw [he] at hh
    have hs : 0 < ‖v‖ * Real.sin (v.arg - (u - l)) := mul_pos (norm_pos_iff.mpr hv0) hp
    have ht : -(u - l) + v.arg = v.arg - (u - l) := by ring
    rw [ht] at hh
    linarith
  refine ⟨v.arg + l, ⟨by linarith, by linarith⟩, ?_⟩
  have hvpolar := Complex.norm_mul_exp_arg_mul_I v
  have he : Complex.exp ((l : ℂ) * I) * v = z := by
    dsimp [v]
    rw [rotated_mul]
    simp
  calc
    z = Complex.exp ((l : ℂ) * I) * v := he.symm
    _ = Complex.exp ((l : ℂ) * I) * ((‖v‖ : ℂ) * Complex.exp ((v.arg : ℂ) * I)) :=
      congrArg (fun x : ℂ => Complex.exp ((l : ℂ) * I) * x) hvpolar.symm
    _ = _ := by
      rw [hvnorm, mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      ring

end KsIndex.KarcherData
