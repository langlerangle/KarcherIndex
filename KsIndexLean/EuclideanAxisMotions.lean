module

public import KsIndexLean.CheckerboardPeriods
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

@[expose] public section


/-! Euclidean rigid motions in complex-horizontal and real-vertical coordinates.
Orthogonality uses the Euclidean scalar product, not the product norm. -/
noncomputable section
namespace KsIndex
open Complex

def spaceDot (p q : SpacePoint) : ℝ := p.1.re * q.1.re + p.1.im * q.1.im + p.2 * q.2

/-- An arbitrary affine Euclidean rigid motion of real three-space. -/
structure EuclideanMotion where
  affine : SpacePoint ≃ᵃ[ℝ] SpacePoint
  orthogonal : ∀ v w, spaceDot (affine.linear v) (affine.linear w) = spaceDot v w

namespace EuclideanMotion
variable (F : EuclideanMotion)

lemma apply_eq_linear_add (p : SpacePoint) :
    F.affine p = F.affine.linear p + F.affine 0 := by
  simpa using F.affine.map_vadd (0 : SpacePoint) p

lemma linear_vertical (hv : (F.affine.linear (0, 1)).1 = 0) (t : ℝ) :
    F.affine.linear (0, t) = (0, t * (F.affine.linear (0, 1)).2) := by
  have he : ((0 : ℂ), t) = t • ((0 : ℂ), (1 : ℝ)) := by simp
  rw [he, map_smul]
  ext <;> simp [hv]

lemma vertical_sign (hv : (F.affine.linear (0, 1)).1 = 0) :
    (F.affine.linear (0, 1)).2 = 1 ∨ (F.affine.linear (0, 1)).2 = -1 := by
  have hh := F.orthogonal (0, 1) (0, 1)
  simp [spaceDot, hv] at hh
  exact sq_eq_one_iff.mp (by nlinarith : (F.affine.linear (0, 1)).2 ^ 2 = 1)

lemma linear_horizontal (hv : (F.affine.linear (0, 1)).1 = 0) (z : ℂ) :
    (F.affine.linear (z, 0)).2 = 0 := by
  have hh := F.orthogonal (z, 0) (0, 1)
  simp [spaceDot, hv] at hh
  rcases F.vertical_sign hv with hs | hs <;> simpa [hs] using hh

/-- Once the vertical direction is preserved, a Euclidean rigid motion has
one of the two usual complex forms in the horizontal plane. -/
theorem axis_direction_normal_form (hv : (F.affine.linear (0, 1)).1 = 0) :
    ∃ (c : ℂ) (ε : ℝ), ‖c‖ = 1 ∧ (ε = 1 ∨ ε = -1) ∧
      ((∀ p, F.affine p = (c * p.1 + (F.affine 0).1, ε * p.2 + (F.affine 0).2)) ∨
       (∀ p, F.affine p = (c * starRingEnd ℂ p.1 + (F.affine 0).1,
          ε * p.2 + (F.affine 0).2))) := by
  let c := (F.affine.linear (1, 0)).1
  let d := (F.affine.linear (I, 0)).1
  have hcz := F.linear_horizontal hv 1
  have hdz := F.linear_horizontal hv I
  have hc2 : c.re * c.re + c.im * c.im = 1 := by
    have hh := F.orthogonal (1, 0) (1, 0)
    simpa [spaceDot, hcz, c] using hh
  have hd2 : d.re * d.re + d.im * d.im = 1 := by
    have hh := F.orthogonal (I, 0) (I, 0)
    simpa [spaceDot, hdz, d] using hh
  have hcd : c.re * d.re + c.im * d.im = 0 := by
    have hh := F.orthogonal (1, 0) (I, 0)
    simpa [spaceDot, hcz, hdz, c, d] using hh
  have hc : ‖c‖ = 1 := by
    have hh := Complex.normSq_eq_norm_sq c
    simp only [Complex.normSq_apply] at hh
    nlinarith [norm_nonneg c]
  let u := starRingEnd ℂ c * d
  have hu : u.re = 0 := by simpa [u, Complex.mul_re] using hcd
  have hui : u.im = 1 ∨ u.im = -1 := by
    have hs : u.im ^ 2 = 1 := by
      dsimp [u]
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      nlinarith [sq_nonneg (c.re * d.re + c.im * d.im),
        mul_nonneg (sq_nonneg c.re) (sq_nonneg d.re)]
    rcases sq_eq_one_iff.mp hs with hh | hh <;> simp_all
  have hcu : c * u = d := by
    dsimp [u]
    rw [← mul_assoc, Complex.mul_conj', hc]
    norm_num
  have hformula (z : ℂ) : (F.affine.linear (z, 0)).1 = z.re • c + z.im • d := by
    have he : (z, (0 : ℝ)) = z.re • ((1 : ℂ), (0 : ℝ)) + z.im • (I, (0 : ℝ)) := by
      ext <;> simp
    rw [he, map_add, map_smul, map_smul]
    rfl
  have hfull (p : SpacePoint) : F.affine p =
      (p.1.re • c + p.1.im • d + (F.affine 0).1,
        (F.affine.linear (0, 1)).2 * p.2 + (F.affine 0).2) := by
    rw [F.apply_eq_linear_add]
    have he : p = (p.1, 0) + (0, p.2) := by ext <;> simp
    conv_lhs => rw [he, map_add]
    rw [F.linear_vertical hv]
    ext <;> simp [hformula, F.linear_horizontal hv, mul_comm]
  refine ⟨c, (F.affine.linear (0, 1)).2, hc, F.vertical_sign hv, ?_⟩
  rcases hui with hi | hi
  · have hue : u = I := Complex.ext (by simpa using hu) (by simpa using hi)
    have hd : d = c * I := by rw [← hcu, hue]
    left
    intro p
    rw [hfull, hd]
    apply Prod.ext
    · apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
    · rfl
  · have hue : u = -I := Complex.ext (by simpa using hu) (by simpa using hi)
    have hd : d = c * -I := by rw [← hcu, hue]
    right
    intro p
    rw [hfull, hd]
    apply Prod.ext
    · apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
    · rfl

end EuclideanMotion
end KsIndex
