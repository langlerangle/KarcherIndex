module

public import KsIndexLean.SphericalReflection
public import KsIndexLean.PlaneRotation

@[expose] public section


open Set Metric

noncomputable section
namespace KsIndex.Spherical

/-- Rotation about the vertical axis, with the plane rotation's angle convention. -/
def rotateAmbient (θ : ℝ) (p : Ambient) : Ambient :=
  let z := KsIndex.Trace.planeRotation θ (Complex.mk (p 0) (p 1))
  WithLp.toLp 2 ![z.re, z.im, p 2]

lemma rotateAmbient_norm_sq (θ : ℝ) (p : Ambient) :
    ‖rotateAmbient θ p‖ ^ 2 = ‖p‖ ^ 2 := by
  have h := congrArg (fun r : ℝ => r ^ 2)
    ((KsIndex.Trace.planeRotation θ).norm_map (Complex.mk (p 0) (p 1)))
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp only [rotateAmbient, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  change _ + _ + p 2 ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2
  nlinarith [h]

def rotateSphere (θ : ℝ) (p : Sphere) : Sphere :=
  ⟨rotateAmbient θ p.val, mem_sphere_zero_iff_norm.mpr (by
    have h := rotateAmbient_norm_sq θ p.val
    rw [mem_sphere_zero_iff_norm.mp p.property] at h
    nlinarith [norm_nonneg (rotateAmbient θ p.val)])⟩

lemma rotateSphere_height (θ : ℝ) (p : Sphere) :
    (rotateSphere θ p).val 2 = p.val 2 := rfl

lemma rotateSphere_reflect (θ : ℝ) (p : Sphere) :
    rotateSphere θ (reflectSphere p) = reflectSphere (rotateSphere θ p) := by
  apply Subtype.ext
  ext i
  fin_cases i <;> rfl

lemma rotateAmbient_stereoPoint (θ : ℝ) (z : ℂ) :
    rotateAmbient θ (stereoPoint z) = stereoPoint (KsIndex.Trace.planeRotation θ z) := by
  have hn := (KsIndex.Trace.planeRotation θ).norm_map z
  have hs (r : ℝ) (w : ℂ) : (r • w).re = r * w.re ∧ (r • w).im = r * w.im := by
    exact ⟨Complex.smul_re r w, Complex.smul_im r w⟩
  have hz : Complex.mk (stereoPoint z 0) (stereoPoint z 1) =
      (2 / (1 + ‖z‖ ^ 2) : ℝ) • z := by
    apply Complex.ext
    · rw [(hs _ _).1]
      change 2 * z.re / (1 + ‖z‖ ^ 2) = _
      ring
    · rw [(hs _ _).2]
      change 2 * z.im / (1 + ‖z‖ ^ 2) = _
      ring
  unfold rotateAmbient
  rw [hz, map_smul]
  ext i
  fin_cases i
  · change (((2 / (1 + ‖z‖ ^ 2) : ℝ) • KsIndex.Trace.planeRotation θ z).re) = _
    rw [(hs _ _).1]
    change _ = 2 * (KsIndex.Trace.planeRotation θ z).re /
      (1 + ‖KsIndex.Trace.planeRotation θ z‖ ^ 2)
    rw [hn]
    ring
  · change (((2 / (1 + ‖z‖ ^ 2) : ℝ) • KsIndex.Trace.planeRotation θ z).im) = _
    rw [(hs _ _).2]
    change _ = 2 * (KsIndex.Trace.planeRotation θ z).im /
      (1 + ‖KsIndex.Trace.planeRotation θ z‖ ^ 2)
    rw [hn]
    ring
  · change (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2) =
      (‖KsIndex.Trace.planeRotation θ z‖ ^ 2 - 1) / (1 + ‖KsIndex.Trace.planeRotation θ z‖ ^ 2)
    rw [hn]

lemma rotateSphere_sphereChart (θ : ℝ) (z : ℂ) :
    rotateSphere θ (sphereChart z) = sphereChart (KsIndex.Trace.planeRotation θ z) := by
  exact Subtype.ext (rotateAmbient_stereoPoint θ z)

lemma rotateSphere_southChart (θ : ℝ) (z : ℂ) :
    rotateSphere θ (southChart z) = southChart (KsIndex.Trace.planeRotation θ z) := by
  rw [southChart, rotateSphere_reflect, rotateSphere_sphereChart, southChart]

lemma continuous_rotateSphere (θ : ℝ) : Continuous (rotateSphere θ) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : Sphere =>
      (KsIndex.Trace.planeRotation θ (Complex.mk (p.val 0) (p.val 1))).re)
    simp only [KsIndex.Trace.planeRotation_apply, Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun p : Sphere =>
      (KsIndex.Trace.planeRotation θ (Complex.mk (p.val 0) (p.val 1))).im)
    simp only [KsIndex.Trace.planeRotation_apply, Complex.mk_eq_add_mul_I]
    fun_prop
  · change Continuous (fun p : Sphere => p.val 2)
    fun_prop

end KsIndex.Spherical
