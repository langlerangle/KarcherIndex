module

public import KsIndexLean.MixedHalfPeriodLinear
public import KsIndexLean.MixedSectorRadicalEquiv
public import KsIndexLean.HemisphereMixedWeakRadical

@[expose] public section


/-!
# Mixed half-period fields and single-hemisphere weak nullity

For `k ≥ 2` and a supplied `PaperHalfPeriodRealization k`, the bounded geometric
mixed half-period fields with flags `true, false`, restricted to rotation character
`j`, are complex-linearly equivalent to `hemisphereMixedWeakRadical k j true false`.
The equivalence composes the character-restricted disk-coordinate identification,
the disk mixed-sector radical equivalence, and `hemisphereMixedRadicalEquiv`.
It gives equality of complex dimensions and finite-dimensionality of the geometric
character space.

The character space is defined through its `ComplexH1` image. Membership is also
characterized by the pointwise rotation identity on the open coordinate disk.
A member satisfies that identity on the punctured closed disk, including its seam
points. Puncture endpoints are excluded from this last statement.
-/
noncomputable section
open Set MeasureTheory Filter Topology
open KsIndex.Trace KsIndex.WeakH1 KsIndex.FormIndex KsIndex.Spherical KsIndex.Spectral
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The character-restricted actual geometric mixed half-period field space (paper character j). -/
def classicalMixedHalfPeriodCharacter (R : PaperHalfPeriodRealization k) (j : ℕ) :
    Submodule ℂ (R.classicalMixedHalfPeriodSpace true false) :=
  (weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j)).comap
    (R.classicalMixedHalfPeriodToH1 true false)

/-- The disk-coordinate equivalence restricts to the rotation character because the
`toH1` maps commute with it. -/
def classicalMixedHalfPeriodCharacterSectorEquiv (R : PaperHalfPeriodRealization k) (j : ℕ) :
    R.classicalMixedHalfPeriodCharacter j ≃ₗ[ℂ] classicalMixedSector h.out j :=
  LinearEquiv.ofLinearMap
    ({ toFun := fun u => ⟨R.classicalMixedHalfPeriodDiskEquiv true false u.val, by
          change classicalMixedDiskToH1 h.out true false
            (R.classicalMixedHalfPeriodDiskEquiv true false u.val)
              ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j)
          rw [← R.classicalMixedHalfPeriodToH1_eq_disk]
          exact u.property⟩
       map_add' := fun u v => Subtype.ext (map_add _ _ _)
       map_smul' := fun a u => Subtype.ext (map_smul _ _ _) } :
      R.classicalMixedHalfPeriodCharacter j →ₗ[ℂ] classicalMixedSector h.out j)
    ({ toFun := fun g => ⟨(R.classicalMixedHalfPeriodDiskEquiv true false).symm g.val, by
          change R.classicalMixedHalfPeriodToH1 true false
            ((R.classicalMixedHalfPeriodDiskEquiv true false).symm g.val)
              ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j)
          rw [R.classicalMixedHalfPeriodToH1_eq_disk, LinearEquiv.apply_symm_apply]
          exact g.property⟩
       map_add' := fun u v => Subtype.ext (map_add _ _ _)
       map_smul' := fun a u => Subtype.ext (map_smul _ _ _) } :
      classicalMixedSector h.out j →ₗ[ℂ] R.classicalMixedHalfPeriodCharacter j)
    (by refine LinearMap.ext fun g => ?_; exact Subtype.ext (LinearEquiv.apply_symm_apply _ _))
    (by refine LinearMap.ext fun u => ?_; exact Subtype.ext (LinearEquiv.symm_apply_apply _ _))

/-- The character-restricted geometric field space is equivalent to the disk weak form radical. -/
def classicalMixedHalfPeriodRadicalEquiv (R : PaperHalfPeriodRealization k) (j : ℕ) :
    R.classicalMixedHalfPeriodCharacter j ≃ₗ[ℂ]
      @Spectral.formRadical (mixedCharacterDomain k j true false) inferInstance
        (diskDomain_innerProductSpace _)
        (domainJacobiForm (mixedCharacterDomain k j true false) (surfacePotential k)) :=
  (R.classicalMixedHalfPeriodCharacterSectorEquiv j).trans
    (classicalMixedSectorRadicalEquiv h.out j)

/-- Actual bounded geometric mixed half-period fields and the full-test
literal single-lower-hemisphere Jacobi kernel correspond in each paper rotation character. -/
def classicalMixedHalfPeriodHemisphereEquiv (R : PaperHalfPeriodRealization k) (j : ℕ) :
    R.classicalMixedHalfPeriodCharacter j ≃ₗ[ℂ] hemisphereMixedWeakRadical k j true false :=
  (R.classicalMixedHalfPeriodRadicalEquiv j).trans (hemisphereMixedRadicalEquiv k j true false)

/-- **Mixed single-hemisphere nullity.** -/
theorem classical_mixedHalfPeriod_hemisphere_nullity (R : PaperHalfPeriodRealization k) (j : ℕ) :
    Module.finrank ℂ (R.classicalMixedHalfPeriodCharacter j) =
      Module.finrank ℂ (hemisphereMixedWeakRadical k j true false) :=
  (R.classicalMixedHalfPeriodHemisphereEquiv j).finrank_eq

lemma classicalMixedHalfPeriodCharacter_finiteDimensional (R : PaperHalfPeriodRealization k)
    (j : ℕ) : FiniteDimensional ℂ (R.classicalMixedHalfPeriodCharacter j) := by
  let := hemisphereMixedWeakRadical_finiteDimensional k j true false
  exact (R.classicalMixedHalfPeriodHemisphereEquiv j).symm.finiteDimensional

/-! ### Pointwise characterization of the rotation character -/

/-- an actual geometric mixed field with the interior pointwise rotation
character lies in the character space. -/
theorem mem_classicalMixedHalfPeriodCharacter_of_pointwise (R : PaperHalfPeriodRealization k)
    (j : ℕ) (u : R.classicalMixedHalfPeriodSpace true false)
    (hc : ∀ z ∈ Surface.disk,
      R.halfPeriodCoordinate u.val (planeRotation (-(2 * Real.pi) / k) z)
        = zeta k ^ j * R.halfPeriodCoordinate u.val z) :
    u ∈ R.classicalMixedHalfPeriodCharacter j := by
  have hc' : ∀ w ∈ Surface.disk,
      (R.classicalMixedHalfPeriodData u).toDisk.value (planeRotation (-(2 * Real.pi) / k) w)
        = zeta k ^ j * (R.classicalMixedHalfPeriodData u).toDisk.value w := by
    intro w hw
    change R.halfPeriodCoordinate (R.classicalMixedHalfPeriodData u).value
        (planeRotation (-(2 * Real.pi) / k) w)
      = zeta k ^ j * R.halfPeriodCoordinate (R.classicalMixedHalfPeriodData u).value w
    rw [classicalMixedHalfPeriodData_value]
    exact hc w hw
  exact (R.classicalMixedHalfPeriodData u).toDisk.toH1_character h.out _ _ hc'

/-- Value of the sector image on the physical disk is the geometric field's coordinate. -/
private lemma sector_value_eq (R : PaperHalfPeriodRealization k) (j : ℕ)
    (u : R.classicalMixedHalfPeriodCharacter j) {w : ℂ}
    (hw : w ∈ Metric.closedBall (0 : ℂ) 1 \ Surface.punctures k) :
    (classicalMixedDiskData (R.classicalMixedHalfPeriodCharacterSectorEquiv j u).val).value w
      = R.halfPeriodCoordinate u.val.val w :=
  classicalMixedDiskData_value (R.classicalMixedHalfPeriodCharacterSectorEquiv j u).val ⟨w, hw⟩

/-- a character-space field has the pointwise rotation character on
the open disk. -/
theorem classicalMixedHalfPeriodCharacter_pointwise_interior (R : PaperHalfPeriodRealization k)
    (j : ℕ) (u : R.classicalMixedHalfPeriodCharacter j) :
    ∀ z ∈ Surface.disk,
      R.halfPeriodCoordinate u.val.val (planeRotation (-(2 * Real.pi) / k) z)
        = zeta k ^ j * R.halfPeriodCoordinate u.val.val z := by
  intro z hz
  have hzd : z ∈ Metric.closedBall (0 : ℂ) 1 \ Surface.punctures k :=
    ⟨Metric.ball_subset_closedBall hz, Surface.punctures_notMem_disk (by have := h.out; omega) hz⟩
  have hrdisk : planeRotation (-(2 * Real.pi) / k) z ∈ Surface.disk := by
    rw [SurfaceForm.mem_disk_iff] at hz ⊢
    rw [(planeRotation _).norm_map]; exact hz
  have hrz : planeRotation (-(2 * Real.pi) / k) z ∈
      Metric.closedBall (0 : ℂ) 1 \ Surface.punctures k :=
    ⟨Metric.ball_subset_closedBall hrdisk,
      Surface.punctures_notMem_disk (by have := h.out; omega) hrdisk⟩
  have hf := classicalMixedSector_pointwise h.out j
    (R.classicalMixedHalfPeriodCharacterSectorEquiv j u) z hzd
  rw [R.sector_value_eq j u hrz, R.sector_value_eq j u hzd] at hf
  exact hf

/-- the character space is exactly the interior pointwise rotation
character of the actual geometric field (not merely the weak-character comap name). -/
theorem mem_classicalMixedHalfPeriodCharacter_iff (R : PaperHalfPeriodRealization k) (j : ℕ)
    (u : R.classicalMixedHalfPeriodSpace true false) :
    u ∈ R.classicalMixedHalfPeriodCharacter j ↔
      ∀ z ∈ Surface.disk,
        R.halfPeriodCoordinate u.val (planeRotation (-(2 * Real.pi) / k) z)
          = zeta k ^ j * R.halfPeriodCoordinate u.val z := by
  constructor
  · exact fun hu => R.classicalMixedHalfPeriodCharacter_pointwise_interior j ⟨u, hu⟩
  · exact R.mem_classicalMixedHalfPeriodCharacter_of_pointwise j u

/-- The character rotation permutes the punctures (its factor is a `(2k)`-th root of unity). -/
lemma planeRotation_notMem_punctures {z : ℂ} (hz : z ∉ Surface.punctures k) :
    planeRotation (-(2 * Real.pi) / k) z ∉ Surface.punctures k := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := h.out; omega)
  simp only [Surface.punctures, Set.mem_ofPred_eq] at hz ⊢
  rw [planeRotation_apply, mul_pow]
  have hroot : (Complex.exp (↑(-(2 * Real.pi) / k) * Complex.I)) ^ (2 * k) = 1 := by
    rw [← Complex.exp_nat_mul,
      show (↑(2 * k) : ℂ) * (↑(-(2 * Real.pi) / k) * Complex.I)
        = ((-2 : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) from by push_cast; field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I (-2)
  rw [hroot, one_mul]
  exact hz

/-- a character-space field has the
pointwise rotation character on the entire physical punctured closed disk. -/
theorem classicalMixedHalfPeriodCharacter_pointwise (R : PaperHalfPeriodRealization k) (j : ℕ)
    (u : R.classicalMixedHalfPeriodCharacter j) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1 \ Surface.punctures k,
      R.halfPeriodCoordinate u.val.val (planeRotation (-(2 * Real.pi) / k) z)
        = zeta k ^ j * R.halfPeriodCoordinate u.val.val z := by
  intro z hz
  have hrz : planeRotation (-(2 * Real.pi) / k) z
      ∈ Metric.closedBall (0 : ℂ) 1 \ Surface.punctures k := by
    refine ⟨?_, planeRotation_notMem_punctures hz.2⟩
    simp only [Metric.mem_closedBall, dist_zero_right, (planeRotation _).norm_map]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
  have hf := classicalMixedSector_pointwise h.out j
    (R.classicalMixedHalfPeriodCharacterSectorEquiv j u) z hz
  rw [R.sector_value_eq j u hrz, R.sector_value_eq j u hz] at hf
  exact hf

end KsIndex.KarcherData.PaperHalfPeriodRealization
