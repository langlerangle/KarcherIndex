module

public import KsIndexLean.KarcherConformalOrientation
public import KsIndexLean.KarcherWeingarten

@[expose] public section


/-! Regularity and orthogonality of the actual cross-product normal. -/
noncomputable section
open scoped ContDiff Topology
namespace KsIndex.KarcherData

lemma chartUnitNormal_differentiableAt {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : ContDiffAt ℝ 2 X w)
    (hp : 0 < euclideanSq (euclideanCross (fderiv ℝ X w 1)
      (fderiv ℝ X w Complex.I))) :
    DifferentiableAt ℝ (chartUnitNormal X) w := by
  have hD := (hX.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by simp)
  have ha := hD.clm_apply (differentiableAt_const (1 : ℂ))
  have hb := hD.clm_apply (differentiableAt_const Complex.I)
  let C := fun z => euclideanCross (fderiv ℝ X z 1) (fderiv ℝ X z Complex.I)
  have hC : DifferentiableAt ℝ C w := by
    exact ((ha.snd.fst.mul hb.snd.snd).sub (ha.snd.snd.mul hb.snd.fst)).prodMk
      (((ha.snd.snd.mul hb.fst).sub (ha.fst.mul hb.snd.snd)).prodMk
        ((ha.fst.mul hb.snd.fst).sub (ha.snd.fst.mul hb.fst)))
  have hs : DifferentiableAt ℝ (fun z => euclideanSq (C z)) w := by
    exact ((hC.fst.pow 2).add (hC.snd.fst.pow 2)).add (hC.snd.snd.pow 2)
  exact ((hs.sqrt hp.ne').inv (Real.sqrt_ne_zero'.mpr hp)).smul hC

lemma chartUnitNormal_orthogonal (X : ℂ → AmbientTriple) (w v : ℂ) :
    euclideanDot (chartUnitNormal X w) (fderiv ℝ X w v) = 0 := by
  rw [chartUnitNormal, euclideanDot_smul_left]
  suffices h : euclideanDot
      (euclideanCross (fderiv ℝ X w 1) (fderiv ℝ X w Complex.I))
      (fderiv ℝ X w v) = 0 by rw [h, mul_zero]
  rw [real_linear_complex_components (fderiv ℝ X w) v]
  simp only [euclideanDot, euclideanCross, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

end KsIndex.KarcherData
