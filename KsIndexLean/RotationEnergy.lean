module

public import KsIndexLean.RotationLp
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section


/-! Exact preservation of the two-real-direction energy. This is the coordinate
energy used by the adopted complex H¹ graph norm, not an operator-norm surrogate.
The annular integral theorem concerns data; no quotient carrier is constructed. -/

open Set MeasureTheory

namespace KsIndex.Trace

lemma linearMap_complex_coordinates (L : ℂ →L[ℝ] ℂ) (z : ℂ) :
    L z = z.re • L 1 + z.im • L Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by simp
  conv_lhs => rw [hz]
  simp only [map_add, map_smul]

/-- Orthogonal change of real input coordinates preserves the squared column norms. -/
lemma linearMap_unit_rotation_energy (L : ℂ →L[ℝ] ℂ) {c : ℂ} (hc : ‖c‖ = 1) :
    ‖L c‖ ^ 2 + ‖L (c * Complex.I)‖ ^ 2 = ‖L 1‖ ^ 2 + ‖L Complex.I‖ ^ 2 := by
  have hcs : c.re ^ 2 + c.im ^ 2 = 1 := by
    have h := congrArg (fun t : ℝ => t ^ 2) hc
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    nlinarith
  calc
    ‖L c‖ ^ 2 + ‖L (c * Complex.I)‖ ^ 2 =
        (c.re ^ 2 + c.im ^ 2) * (‖L 1‖ ^ 2 + ‖L Complex.I‖ ^ 2) := by
      rw [linearMap_complex_coordinates L c, linearMap_complex_coordinates L (c * Complex.I)]
      simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      ring
    _ = ‖L 1‖ ^ 2 + ‖L Complex.I‖ ^ 2 := by rw [hcs, one_mul]

lemma planeRotation_derivative_energy (θ : ℝ) (L : ℂ →L[ℝ] ℂ) :
    ‖L (planeRotation θ 1)‖ ^ 2 + ‖L (planeRotation θ Complex.I)‖ ^ 2 =
      ‖L 1‖ ^ 2 + ‖L Complex.I‖ ^ 2 := by
  simpa only [planeRotation_apply, mul_one] using
    linearMap_unit_rotation_energy L (Complex.norm_exp_ofReal_mul_I θ)

/-- The total derivative energy is invariant on the open annulus. -/
theorem integral_planeRotation_derivative_energy (θ a b : ℝ) (U : ℂ → ℂ →L[ℝ] ℂ) :
    (∫ z, (‖U (planeRotation θ z) (planeRotation θ 1)‖ ^ 2 +
      ‖U (planeRotation θ z) (planeRotation θ Complex.I)‖ ^ 2)
      ∂volume.restrict (rotationAnnulus a b : Set ℂ)) =
    ∫ z, (‖U z 1‖ ^ 2 + ‖U z Complex.I‖ ^ 2)
      ∂volume.restrict (rotationAnnulus a b : Set ℂ) := by
  simp_rw [planeRotation_derivative_energy]
  exact (measurePreserving_planeRotation_annulus θ a b).integral_comp
    (planeRotation θ).toHomeomorph.measurableEmbedding
    (fun z => ‖U z 1‖ ^ 2 + ‖U z Complex.I‖ ^ 2)

/-- With L² derivative data, the sums of the finite coordinate energies agree. -/
theorem integral_planeRotation_derivative_energy_split (θ a b : ℝ)
    {U : ℂ → ℂ →L[ℝ] ℂ}
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (rotationAnnulus a b : Set ℂ)))
    (hI : MemLp (fun z => U z Complex.I) 2
      (volume.restrict (rotationAnnulus a b : Set ℂ))) :
    (∫ z, ‖U (planeRotation θ z) (planeRotation θ 1)‖ ^ 2
      ∂volume.restrict (rotationAnnulus a b : Set ℂ)) +
    (∫ z, ‖U (planeRotation θ z) (planeRotation θ Complex.I)‖ ^ 2
      ∂volume.restrict (rotationAnnulus a b : Set ℂ)) =
    (∫ z, ‖U z 1‖ ^ 2 ∂volume.restrict (rotationAnnulus a b : Set ℂ)) +
    ∫ z, ‖U z Complex.I‖ ^ 2 ∂volume.restrict (rotationAnnulus a b : Set ℂ) := by
  have hint {f : ℂ → ℂ} (hf : MemLp f 2
      (volume.restrict (rotationAnnulus a b : Set ℂ))) :
      Integrable (fun z => ‖f z‖ ^ 2) (volume.restrict (rotationAnnulus a b : Set ℂ)) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  rw [← integral_add (hint (memLp_rotated_derivative θ a b h1 hI 1))
    (hint (memLp_rotated_derivative θ a b h1 hI Complex.I)),
    ← integral_add (hint h1) (hint hI)]
  exact integral_planeRotation_derivative_energy θ a b U

end KsIndex.Trace
