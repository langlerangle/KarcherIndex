module

public import KsIndexLean.KarcherGlobalEquivariance
public import KsIndexLean.SphericalSlitDomain

@[expose] public section


/-! The two actual global parameter reflections, including both regular poles. -/
noncomputable section
open Set Metric
namespace KsIndex.KarcherData

/-- Conjugation in the finite coordinate is reflection of the sphere's second coordinate. -/
def conjugateAmbient (p : Spherical.Ambient) : Spherical.Ambient :=
  WithLp.toLp 2 ![p 0, -p 1, p 2]

lemma conjugateAmbient_norm_sq (p : Spherical.Ambient) :
    ‖conjugateAmbient p‖ ^ 2 = ‖p‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, conjugateAmbient]

def conjugateSphere (p : Spherical.Sphere) : Spherical.Sphere :=
  ⟨conjugateAmbient p.val, mem_sphere_zero_iff_norm.mpr (by
    have h := conjugateAmbient_norm_sq p.val
    have hn := mem_sphere_zero_iff_norm.mp p.property
    rw [hn] at h
    nlinarith [norm_nonneg (conjugateAmbient p.val)])⟩

lemma conjugateSphere_involutive : Function.Involutive conjugateSphere := by
  intro p
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [conjugateSphere, conjugateAmbient]

lemma continuous_conjugateSphere : Continuous conjugateSphere := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : Spherical.Sphere => p.val 0)
    fun_prop
  · change Continuous (fun p : Spherical.Sphere => -p.val 1)
    fun_prop
  · change Continuous (fun p : Spherical.Sphere => p.val 2)
    fun_prop

lemma conjugateSphere_finite (z : ℂ) :
    conjugateSphere (Spherical.sphereChart z) = Spherical.sphereChart (starRingEnd ℂ z) := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [conjugateSphere, conjugateAmbient, Spherical.sphereChart,
    Spherical.stereoPoint, neg_div]

lemma conjugate_not_puncture {k : ℕ} {z : ℂ} (hz : z ∉ Surface.punctures k) :
    starRingEnd ℂ z ∉ Surface.punctures k := by
  intro h
  apply hz
  have he := congrArg (starRingEnd ℂ) h
  simpa [Surface.punctures] using he

/-- Global conjugation on the punctured parameter sphere. -/
def parameterConjugation {k : ℕ} (p : ParameterSphere k) : ParameterSphere k :=
  ⟨conjugateSphere p.val, by
    rintro ⟨z, hz, he⟩
    have hc : starRingEnd ℂ z ∈ Surface.punctures k := by
      simpa [Surface.punctures] using congrArg (starRingEnd ℂ) hz
    have hp : Spherical.sphereChart (starRingEnd ℂ z) = p.val := by
      rw [← conjugateSphere_finite, he, conjugateSphere_involutive]
    exact p.property ⟨_, hc, hp⟩⟩

lemma continuous_parameterConjugation (k : ℕ) :
    Continuous (parameterConjugation (k := k)) :=
  (continuous_conjugateSphere.comp continuous_subtype_val).subtype_mk _

lemma parameterConjugation_finite {k : ℕ} (w : PuncturedPlane k) :
    parameterConjugation (finiteParameter w) =
      finiteParameter ⟨starRingEnd ℂ w.val, conjugate_not_puncture w.property⟩ :=
  Subtype.ext (conjugateSphere_finite w.val)

lemma parameterConjugation_involutive (k : ℕ) :
    Function.Involutive (parameterConjugation (k := k)) :=
  fun p => Subtype.ext (conjugateSphere_involutive p.val)

lemma parameterConjugation_infinity (k : ℕ) :
    parameterConjugation (infinityParameter k) = infinityParameter k := by
  apply Subtype.ext
  apply north_unique
  exact infinitySphereChart_zero_height

/-- Reflection across the equator preserves each removed puncture individually. -/
lemma reflectSphere_fixes_puncture {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ Surface.punctures k) :
    Spherical.reflectSphere (Spherical.sphereChart z) = Spherical.sphereChart z := by
  apply Spherical.reflectSphere_eq_of_equator
  exact (Spherical.stereoPoint_equator_iff z).mpr (puncture_norm hk hz)

/-- The seam reflection on the whole parameter sphere. It interchanges 0 and infinity. -/
def parameterSeamReflection {k : ℕ} (hk : 2 ≤ k) (p : ParameterSphere k) : ParameterSphere k :=
  ⟨Spherical.reflectSphere p.val, by
    rintro ⟨z, hz, he⟩
    have hp : Spherical.sphereChart z = p.val := by
      rw [← reflectSphere_fixes_puncture hk hz, he, Spherical.reflectSphere_involutive]
    exact p.property ⟨z, hz, hp⟩⟩

lemma continuous_parameterSeamReflection {k : ℕ} (hk : 2 ≤ k) :
    Continuous (parameterSeamReflection hk) :=
  (Spherical.continuous_reflectSphere.comp continuous_subtype_val).subtype_mk _

lemma parameterSeamReflection_involutive {k : ℕ} (hk : 2 ≤ k) :
    Function.Involutive (parameterSeamReflection hk) :=
  fun p => Subtype.ext (Spherical.reflectSphere_involutive p.val)

lemma parameterSeamReflection_finite {k : ℕ} (hk : 2 ≤ k) (w : PuncturedPlane k)
    (hw0 : w.val ≠ 0) (hw : (starRingEnd ℂ w.val)⁻¹ ∉ Surface.punctures k) :
    parameterSeamReflection hk (finiteParameter w) =
      finiteParameter ⟨(starRingEnd ℂ w.val)⁻¹, hw⟩ := by
  apply Subtype.ext
  exact Spherical.southChart_inverse_conj hw0

lemma zero_not_puncture {k : ℕ} (hk : 2 ≤ k) : (0 : ℂ) ∉ Surface.punctures k := by
  simp [Surface.punctures, show 2 * k ≠ 0 by omega]

lemma parameterSeamReflection_zero {k : ℕ} (hk : 2 ≤ k) :
    parameterSeamReflection hk (finiteParameter ⟨0, zero_not_puncture hk⟩) =
      infinityParameter k := by
  apply Subtype.ext
  change Spherical.southChart 0 = Spherical.southChart (starRingEnd ℂ 0)
  simp

lemma parameterSeamReflection_infinity {k : ℕ} (hk : 2 ≤ k) :
    parameterSeamReflection hk (infinityParameter k) =
      finiteParameter ⟨0, zero_not_puncture hk⟩ := by
  rw [← parameterSeamReflection_zero hk, parameterSeamReflection_involutive]

end KsIndex.KarcherData
