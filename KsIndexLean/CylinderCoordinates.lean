module

public import KsIndexLean.KarcherParameterSphere
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section


/-! Global logarithmic coordinates on the punctured complex plane. The circle
coordinate is multiplicative; AddCircle's standard homeomorphism identifies
it with angles modulo 2π. -/
noncomputable section
open Set Topology
namespace KsIndex.Cylindrical

abbrev Cylinder := ℝ × Circle
abbrev NonzeroPlane := ({0}ᶜ : Set ℂ)

/-- Global logarithmic polar coordinates, with no choice of an argument branch. -/
def logarithmicHomeomorph : NonzeroPlane ≃ₜ Cylinder where
  toFun z := (Real.log ‖z.val‖,
    ⟨‖z.val‖⁻¹ • z.val, by
      change dist (‖z.val‖⁻¹ • z.val) 0 = 1
      rw [dist_zero_right]
      simp [norm_ne_zero_iff.mpr z.property]⟩)
  invFun p := ⟨(Real.exp p.1 : ℂ) * (p.2 : ℂ),
    mul_ne_zero (by exact_mod_cast Real.exp_ne_zero p.1) p.2.coe_ne_zero⟩
  left_inv z := by
    apply Subtype.ext
    simp [Real.exp_log (norm_pos_iff.mpr z.property), Complex.real_smul,
      norm_ne_zero_iff.mpr z.property]
  right_inv p := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp [Complex.real_smul]
  continuous_toFun := by
    apply Continuous.prodMk
    · exact Real.continuousOn_log.comp_continuous continuous_subtype_val.norm
        (fun z => norm_ne_zero_iff.mpr z.property)
    · apply Continuous.subtype_mk
      exact (continuous_subtype_val.norm.inv₀
        (fun z => norm_ne_zero_iff.mpr z.property)).smul continuous_subtype_val
  continuous_invFun := by fun_prop

lemma logarithmicHomeomorph_time (z : NonzeroPlane) :
    (logarithmicHomeomorph z).1 = Real.log ‖z.val‖ := rfl

lemma logarithmicHomeomorph_angle (z : NonzeroPlane) :
    ((logarithmicHomeomorph z).2 : ℂ) = (‖z.val‖⁻¹ : ℂ) * z.val := by
  change ‖z.val‖⁻¹ • z.val = _
  simp only [Complex.real_smul, Complex.ofReal_inv]

lemma logarithmicHomeomorph_symm (p : Cylinder) :
    (logarithmicHomeomorph.symm p).val = (Real.exp p.1 : ℂ) * (p.2 : ℂ) := rfl

/-- The logarithmic half cylinder corresponds exactly to the punctured unit disk. -/
lemma logarithmicHomeomorph_nonpos_iff (z : NonzeroPlane) :
    (logarithmicHomeomorph z).1 ≤ 0 ↔ ‖z.val‖ ≤ 1 := by
  rw [logarithmicHomeomorph_time]
  exact Real.log_nonpos_iff (norm_nonneg z.val)

/-- The equatorial cylinder is the unit circle. -/
lemma logarithmicHomeomorph_zero_iff (z : NonzeroPlane) :
    (logarithmicHomeomorph z).1 = 0 ↔ ‖z.val‖ = 1 := by
  rw [logarithmicHomeomorph_time]
  constructor
  · exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr z.property)
  · intro h; rw [h, Real.log_one]

/-- The circle coordinate may equivalently be written as an angle modulo 2π. -/
def additiveCylinderHomeomorph : Cylinder ≃ₜ ℝ × AddCircle (2 * Real.pi) :=
  (Homeomorph.refl ℝ).prodCongr AddCircle.homeomorphCircle'.symm

/-- Complex conjugation reverses the angular coordinate and preserves time. -/
lemma logarithmicHomeomorph_conj (z : NonzeroPlane) :
    logarithmicHomeomorph ⟨(starRingEnd ℂ) z.val,
      (map_ne_zero (starRingEnd ℂ)).mpr z.property⟩ =
      ((logarithmicHomeomorph z).1, (logarithmicHomeomorph z).2⁻¹) := by
  apply Prod.ext
  · simp [logarithmicHomeomorph_time]
  · apply Subtype.ext
    simp only [logarithmicHomeomorph_angle, Circle.coe_inv, Complex.norm_conj, mul_inv_rev,
      inv_inv]
    have hn : (‖z.val‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr z.property
    have hzz : z.val * (starRingEnd ℂ) z.val = (‖z.val‖ : ℂ)^2 := by
      rw [Complex.mul_conj, ← Complex.sq_norm, Complex.ofReal_pow]
    have hz : z.val ≠ 0 := z.property
    field_simp [hn, hz]
    linear_combination hzz

/-- Inverse conjugation reverses time and preserves the angular coordinate. -/
lemma logarithmicHomeomorph_sigma (z : NonzeroPlane) :
    logarithmicHomeomorph ⟨((starRingEnd ℂ) z.val)⁻¹,
      inv_ne_zero (by exact (map_ne_zero (starRingEnd ℂ)).mpr z.property)⟩ =
      (-(logarithmicHomeomorph z).1, (logarithmicHomeomorph z).2) := by
  apply logarithmicHomeomorph.symm.injective
  apply Subtype.ext
  simp only [Homeomorph.symm_apply_apply, logarithmicHomeomorph_symm,
    logarithmicHomeomorph_time, logarithmicHomeomorph_angle, Real.exp_neg,
    Real.exp_log (norm_pos_iff.mpr z.property)]
  have hn : (‖z.val‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr z.property
  have hzz : z.val * (starRingEnd ℂ) z.val = (‖z.val‖ : ℂ)^2 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, Complex.ofReal_pow]
  push_cast
  field_simp [hn, (map_ne_zero (starRingEnd ℂ)).mpr z.property]
  linear_combination -hzz

/-- Multiplication by a unit complex number acts only on the circle coordinate. -/
lemma logarithmicHomeomorph_rotate (z : NonzeroPlane) (a : Circle) :
    logarithmicHomeomorph ⟨(a : ℂ) * z.val, mul_ne_zero a.coe_ne_zero z.property⟩ =
      ((logarithmicHomeomorph z).1, a * (logarithmicHomeomorph z).2) := by
  apply Prod.ext
  · simp [logarithmicHomeomorph_time]
  · apply Subtype.ext
    simp only [logarithmicHomeomorph_angle, Circle.coe_mul, norm_mul, Circle.norm_coe,
      one_mul]
    ring

/-- The removed cylinder points lie at time zero and the EW puncture angles. -/
def cylinderPunctures (k : ℕ) : Set Cylinder :=
  {p | p.1 = 0 ∧ (p.2 : ℂ) ^ (2 * k) = -1}

lemma logarithmicHomeomorph_punctures {k : ℕ} (hk : 2 ≤ k) (z : NonzeroPlane) :
    z.val ∈ Surface.punctures k ↔ logarithmicHomeomorph z ∈ cylinderPunctures k := by
  constructor
  · intro hz
    have hn := KarcherData.puncture_norm hk hz
    refine ⟨(logarithmicHomeomorph_zero_iff z).mpr hn, ?_⟩
    simpa [logarithmicHomeomorph_angle, hn, Surface.punctures] using hz
  · rintro ⟨ht, ha⟩
    have hn := (logarithmicHomeomorph_zero_iff z).mp ht
    simpa [logarithmicHomeomorph_angle, hn, Surface.punctures] using ha

/-- Logarithmic coordinates with the EW punctures removed. -/
def puncturedLogarithmicHomeomorph {k : ℕ} (hk : 2 ≤ k) :
    {z : NonzeroPlane // z.val ∉ Surface.punctures k} ≃ₜ
      {p : Cylinder // p ∉ cylinderPunctures k} :=
  logarithmicHomeomorph.subtype (fun z => not_congr (logarithmicHomeomorph_punctures hk z))

/-- The punctured closed disk corresponds to the punctured closed half cylinder. -/
def halfLogarithmicHomeomorph {k : ℕ} (hk : 2 ≤ k) :
    {z : NonzeroPlane // z.val ∉ Surface.punctures k ∧ ‖z.val‖ ≤ 1} ≃ₜ
      {p : Cylinder // p ∉ cylinderPunctures k ∧ p.1 ≤ 0} :=
  logarithmicHomeomorph.subtype (fun z =>
    and_congr (not_congr (logarithmicHomeomorph_punctures hk z))
      (logarithmicHomeomorph_nonpos_iff z).symm)

end KsIndex.Cylindrical
