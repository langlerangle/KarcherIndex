module

public import KsIndexLean.SphericalAtlasBridge
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section


open scoped RealInnerProductSpace
noncomputable section
namespace KsIndex.Spherical

def stereoDifferential (z v : ℂ) : Ambient := WithLp.toLp 2
  ![(2 * v.re * (1 + ‖z‖ ^ 2) - 4 * z.re * inner ℝ z v) / (1 + ‖z‖ ^ 2) ^ 2,
    (2 * v.im * (1 + ‖z‖ ^ 2) - 4 * z.im * inner ℝ z v) / (1 + ‖z‖ ^ 2) ^ 2,
    4 * inner ℝ z v / (1 + ‖z‖ ^ 2) ^ 2]

lemma stereoPoint_line_deriv (z v : ℂ) :
    HasDerivAt (fun t : ℝ => stereoPoint (z + t • v)) (stereoDifferential z v) 0 := by
  have hf : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hn : HasDerivAt (fun t : ℝ => 1 + ‖z + t • v‖ ^ 2) (2 * inner ℝ z v) 0 := by
    simpa using hf.norm_sq.const_add 1
  have hr := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hf).const_mul 2
  have hi := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hf).const_mul 2
  have ht := hf.norm_sq.sub_const 1
  have hd : (1 : ℝ) + ‖z + (0 : ℝ) • v‖ ^ 2 ≠ 0 := by positivity
  have hp : HasDerivAt
      (fun t : ℝ => ![2 * (z + t • v).re / (1 + ‖z + t • v‖ ^ 2),
        2 * (z + t • v).im / (1 + ‖z + t • v‖ ^ 2),
        (‖z + t • v‖ ^ 2 - 1) / (1 + ‖z + t • v‖ ^ 2)])
      (WithLp.ofLp (stereoDifferential z v)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! hr.div hn hd using 1
      simp [stereoDifferential]
      ring
    · convert! hi.div hn hd using 1
      simp [stereoDifferential]
      ring
    · convert! ht.div hn hd using 1
      simp [stereoDifferential]
      ring
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt
    |>.comp_hasDerivAt 0 hp

lemma fderiv_stereoPoint_apply (z v : ℂ) :
    fderiv ℝ stereoPoint z v = stereoDifferential z v := by
  have hf : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hh := (contDiff_stereoPoint.differentiable (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt 0 hf
  have he := hh.unique (stereoPoint_line_deriv z v)
  simpa using he

end KsIndex.Spherical
