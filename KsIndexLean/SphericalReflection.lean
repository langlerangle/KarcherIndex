module

public import KsIndexLean.SphericalChartHomeomorph

@[expose] public section


open Set Metric

noncomputable section
namespace KsIndex.Spherical

/-- Reflection in the equatorial plane of the actual Euclidean sphere. -/
def reflectAmbient (p : Ambient) : Ambient := WithLp.toLp 2 ![p 0, p 1, -p 2]

lemma reflectAmbient_norm_sq (p : Ambient) : ‖reflectAmbient p‖ ^ 2 = ‖p‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, reflectAmbient]

def reflectSphere (p : Sphere) : Sphere :=
  ⟨reflectAmbient p.val, mem_sphere_zero_iff_norm.mpr (by
    have h := reflectAmbient_norm_sq p.val
    have hn := mem_sphere_zero_iff_norm.mp p.property
    rw [hn] at h
    nlinarith [norm_nonneg (reflectAmbient p.val)])⟩

lemma reflectSphere_involutive : Function.Involutive reflectSphere := by
  intro p
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [reflectSphere, reflectAmbient]

lemma continuous_reflectSphere : Continuous reflectSphere := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : Sphere => p.val 0)
    fun_prop
  · change Continuous (fun p : Sphere => p.val 1)
    fun_prop
  · change Continuous (fun p : Sphere => -p.val 2)
    fun_prop

def reflectSphereHomeomorph : Sphere ≃ₜ Sphere where
  toFun := reflectSphere
  invFun := reflectSphere
  left_inv := reflectSphere_involutive
  right_inv := reflectSphere_involutive
  continuous_toFun := continuous_reflectSphere
  continuous_invFun := continuous_reflectSphere

/-- The complementary coordinate chart obtained by equatorial reflection. -/
def southChart (z : ℂ) : Sphere := reflectSphere (sphereChart z)

lemma range_southChart : Set.range southChart = {p : Sphere | p.val 2 ≠ -1} := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    change -(stereoPoint z 2) ≠ -1
    intro h
    apply stereoPoint_third_ne_one z
    linarith
  · intro hp
    have hr : (reflectSphere p).val 2 ≠ 1 := by
      change -p.val 2 ≠ 1
      intro h
      apply hp
      linarith
    obtain ⟨z, hz⟩ := (Set.ext_iff.mp range_sphereChart (reflectSphere p)).mpr hr
    refine ⟨z, ?_⟩
    rw [southChart, hz, reflectSphere_involutive]

lemma sphere_chart_cover : Set.range sphereChart ∪ Set.range southChart = Set.univ := by
  rw [range_sphereChart, range_southChart]
  ext p
  simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
  by_cases h : p.val 2 = 1
  · right
    rw [h]
    norm_num
  · exact Or.inl h

end KsIndex.Spherical
