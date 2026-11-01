module

public import KsIndexLean.SphericalBulkMap
public import KsIndexLean.CompactPolarJacobi

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Spherical
open KsIndex.WeakH1

/-- The actual spherical chart area density as a bounded flat-disk potential. -/
def sphericalMassPotential : BoundedRealPotential where
  V := stereoAreaDensity
  C := 4
  nonneg := by norm_num
  measurable := continuous_stereoAreaDensity.measurable.aestronglyMeasurable
  bound := Filter.Eventually.of_forall fun z => by
    rw [abs_of_pos (stereoAreaDensity_pos z)]
    exact stereoAreaDensity_le_four z

lemma weightedDisk_mass_eq_potential (u v : ComplexH1) :
    inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v) =
      potential sphericalMassPotential u v := by
  rw [L2.inner_def, potential_integral]
  have he : (∫ z, inner ℂ (weightedDiskValueCLM u z) (weightedDiskValueCLM v z)
      ∂stereoAreaMeasure.restrict (disk : Set ℂ)) =
      ∫ z, inner ℂ (valueCLM u z) (valueCLM v z)
        ∂stereoAreaMeasure.restrict (disk : Set ℂ) := by
    apply integral_congr_ae
    filter_upwards [sphericalBulkMap_ae (valueCLM u), sphericalBulkMap_ae (valueCLM v)] with z hu hv
    change inner ℂ (sphericalBulkMap (valueCLM u) z) (sphericalBulkMap (valueCLM v) z) = _
    rw [hu, hv]
  rw [he, stereoAreaMeasure, restrict_withDensity disk.isOpen.measurableSet,
    integral_withDensity_eq_integral_toReal_smul
      continuous_stereoAreaDensity.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (stereoAreaDensity_pos z).le]
  simp only [RCLike.inner_apply, Complex.real_smul, sphericalMassPotential]
  ring

/-- Absorb an arbitrary real eigenvalue into the flat-disk coefficient, using
precisely the mass density from the spherical metric. -/
def sphericalEigenPotential (V : BoundedRealPotential) (lam : ℝ) : BoundedRealPotential where
  V := fun z => V.V z + lam * stereoAreaDensity z
  C := V.C + |lam| * 4
  nonneg := add_nonneg V.nonneg (by positivity)
  measurable := V.measurable.add
    (aestronglyMeasurable_const.mul continuous_stereoAreaDensity.measurable.aestronglyMeasurable)
  bound := by
    filter_upwards [V.bound] with z hz
    calc
      |V.V z + lam * stereoAreaDensity z| ≤ |V.V z| + |lam * stereoAreaDensity z| := abs_add_le _ _
      _ ≤ V.C + |lam| * 4 := by
        rw [abs_mul, abs_of_pos (stereoAreaDensity_pos z)]
        exact add_le_add hz (mul_le_mul_of_nonneg_left (stereoAreaDensity_le_four z) (abs_nonneg lam))

lemma sphericalEigenPotential_pairing (V : BoundedRealPotential) (lam : ℝ) (u v : ComplexH1) :
    potential (sphericalEigenPotential V lam) u v =
      potential V u v + (lam : ℂ) * potential sphericalMassPotential u v := by
  rw [potential_integral, potential_integral, potential_integral, ← integral_const_mul,
    ← integral_add (potential_integrable V u v)
      ((potential_integrable sphericalMassPotential u v).const_mul (lam : ℂ))]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [sphericalEigenPotential, sphericalMassPotential, Complex.ofReal_add, Complex.ofReal_mul]
  ring

lemma weakJacobi_sphericalEigenPotential (V : BoundedRealPotential) (lam : ℝ) (u v : ComplexH1) :
    weakJacobi (sphericalEigenPotential V lam) u v = weakJacobi V u v -
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v) := by
  rw [weightedDisk_mass_eq_potential, weakJacobi, weakJacobi, sphericalEigenPotential_pairing]
  ring

lemma spherical_eigen_equation_iff (V : BoundedRealPotential) (lam : ℝ) (u v : ComplexH1) :
    weakJacobi V u v = (lam : ℂ) *
      inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v) ↔
    weakJacobi (sphericalEigenPotential V lam) u v = 0 := by
  rw [weakJacobi_sphericalEigenPotential, sub_eq_zero]

end KsIndex.Spherical
