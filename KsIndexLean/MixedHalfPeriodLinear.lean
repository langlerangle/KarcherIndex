module

public import KsIndexLean.KarcherMixedHalfPeriodClassical
public import KsIndexLean.KarcherHalfPeriodLinear
public import KsIndexLean.MixedPhysicalSpace
public import KsIndexLean.MixedClassicalUniqueness
public import KsIndexLean.MixedPhysicalRadical

@[expose] public section


/-!
# Classical mixed half-period fields and their disk coordinates

For `k ≥ 2` and a `PaperHalfPeriodRealization k`, this module constructs the
complex vector space of geometric classical fields with the boundary choices
`b1`, `b0`, its injective map to `ComplexH1`, and its linear equivalence with the
corresponding physical disk field space. The forward and backward coordinate
maps are inverse on physical functions, and their weak H1 representatives agree.
Proof-bearing extensions outside the physical disk contribute no additional
functions or dimensions to these spaces.

-/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Trace KsIndex.WeakH1
variable {k : ℕ} [h : Fact (2 ≤ k)]

namespace ClassicalMixedHalfPeriodJacobi
variable {R : PaperHalfPeriodRealization k} {b1 b0 : Bool}

/-- Equality of the associated weak fields determines the actual geometric mixed half-period
functions. The comparison uses equality on the punctured closed disk, transported
through the realization's disk homeomorphism. -/
theorem value_eq_of_toH1_eq (u v : R.ClassicalMixedHalfPeriodJacobi b1 b0)
    (he : u.toDisk.toH1 h.out = v.toDisk.toH1 h.out) : u.value = v.value := by
  have hd := ClassicalMixedHalfDiskJacobi.eqOn_of_toH1_eq h.out u.toDisk v.toDisk he
  funext q
  let w := R.diskHomeomorph q
  have hw := hd (show w.val.val ∈ Metric.closedBall (0 : ℂ) 1 \ Surface.punctures k from
    ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using w.property, w.val.property⟩)
  change R.halfPeriodCoordinate u.value w.val.val = R.halfPeriodCoordinate v.value w.val.val at hw
  simpa only [halfPeriodCoordinate_apply, w, Homeomorph.symm_apply_apply] using hw

end ClassicalMixedHalfPeriodJacobi

/-- Actual mixed half-period functions satisfying the classical geometric conditions. -/
def classicalMixedHalfPeriodSpace (R : PaperHalfPeriodRealization k) (b1 b0 : Bool) :
    Submodule ℂ (PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) where
  carrier := {f | ∃ u : R.ClassicalMixedHalfPeriodJacobi b1 b0, u.value = f}
  zero_mem' := by
    refine ⟨ClassicalMixedHalfPeriodJacobi.ofDisk R
      (ClassicalMixedHalfDiskJacobi.zeroData k b1 b0), ?_⟩
    rfl
  add_mem' := by
    rintro f g ⟨u, rfl⟩ ⟨v, rfl⟩
    refine ⟨ClassicalMixedHalfPeriodJacobi.ofDisk R (u.toDisk.addData v.toDisk), ?_⟩
    funext q
    change R.halfPeriodCoordinate u.value (R.diskHomeomorph q).val.val +
      R.halfPeriodCoordinate v.value (R.diskHomeomorph q).val.val = u.value q + v.value q
    simp only [halfPeriodCoordinate_apply, Homeomorph.symm_apply_apply]
  smul_mem' := by
    rintro a f ⟨u, rfl⟩
    refine ⟨ClassicalMixedHalfPeriodJacobi.ofDisk R (u.toDisk.smulData a), ?_⟩
    funext q
    change a * R.halfPeriodCoordinate u.value (R.diskHomeomorph q).val.val = a * u.value q
    simp only [halfPeriodCoordinate_apply, Homeomorph.symm_apply_apply]

/-- A proof-bearing representative; the underlying function is fixed. -/
def classicalMixedHalfPeriodData (R : PaperHalfPeriodRealization k) {b1 b0 : Bool}
    (u : R.classicalMixedHalfPeriodSpace b1 b0) : R.ClassicalMixedHalfPeriodJacobi b1 b0 :=
  u.property.choose

@[simp] lemma classicalMixedHalfPeriodData_value (R : PaperHalfPeriodRealization k) {b1 b0 : Bool}
    (u : R.classicalMixedHalfPeriodSpace b1 b0) :
    (R.classicalMixedHalfPeriodData u).value = u.val :=
  u.property.choose_spec

/-- The classical mixed field's actual weak representative (finite energy derived, not assumed). -/
def classicalMixedHalfPeriodToH1 (R : PaperHalfPeriodRealization k) (b1 b0 : Bool) :
    R.classicalMixedHalfPeriodSpace b1 b0 →ₗ[ℂ] ComplexH1 where
  toFun u := (R.classicalMixedHalfPeriodData u).toDisk.toH1 h.out
  map_add' u v := by
    apply valueCLM_injective
    rw [map_add]
    apply Lp.ext
    filter_upwards [(R.classicalMixedHalfPeriodData (u + v)).toDisk.toH1_value_ae h.out,
      (R.classicalMixedHalfPeriodData u).toDisk.toH1_value_ae h.out,
      (R.classicalMixedHalfPeriodData v).toDisk.toH1_value_ae h.out,
      Lp.coeFn_add (valueCLM ((R.classicalMixedHalfPeriodData u).toDisk.toH1 h.out))
        (valueCLM ((R.classicalMixedHalfPeriodData v).toDisk.toH1 h.out))] with z huv hu hv ha
    rw [huv, ha]
    simp only [Pi.add_apply]
    rw [hu, hv]
    change R.halfPeriodCoordinate (R.classicalMixedHalfPeriodData (u + v)).value z =
      R.halfPeriodCoordinate (R.classicalMixedHalfPeriodData u).value z +
      R.halfPeriodCoordinate (R.classicalMixedHalfPeriodData v).value z
    simp only [classicalMixedHalfPeriodData_value, Submodule.coe_add, halfPeriodCoordinate_add]
  map_smul' a u := by
    apply valueCLM_injective
    rw [map_smul]
    apply Lp.ext
    filter_upwards [(R.classicalMixedHalfPeriodData (a • u)).toDisk.toH1_value_ae h.out,
      (R.classicalMixedHalfPeriodData u).toDisk.toH1_value_ae h.out,
      Lp.coeFn_smul a (valueCLM ((R.classicalMixedHalfPeriodData u).toDisk.toH1 h.out))]
      with z hau hu ha
    simp only [RingHom.id_apply]
    rw [hau, ha]
    simp only [Pi.smul_apply]
    rw [hu]
    change R.halfPeriodCoordinate (R.classicalMixedHalfPeriodData (a • u)).value z =
      a • R.halfPeriodCoordinate (R.classicalMixedHalfPeriodData u).value z
    simp only [classicalMixedHalfPeriodData_value, Submodule.coe_smul, halfPeriodCoordinate_smul]

/-- The weak representative loses no actual mixed half-period field. -/
theorem classicalMixedHalfPeriodToH1_injective (R : PaperHalfPeriodRealization k) (b1 b0 : Bool) :
    Function.Injective (R.classicalMixedHalfPeriodToH1 b1 b0) := by
  intro u v he
  have hh := ClassicalMixedHalfPeriodJacobi.value_eq_of_toH1_eq
    (R.classicalMixedHalfPeriodData u) (R.classicalMixedHalfPeriodData v) he
  apply Subtype.ext
  simpa only [classicalMixedHalfPeriodData_value] using hh

namespace ClassicalMixedHalfPeriodJacobi
variable {R : PaperHalfPeriodRealization k} {b1 b0 : Bool}

/-- Forget proof data, retaining the actual function in its linear space. -/
def toSpace (u : R.ClassicalMixedHalfPeriodJacobi b1 b0) : R.classicalMixedHalfPeriodSpace b1 b0 :=
  ⟨u.value, ⟨u, rfl⟩⟩

end ClassicalMixedHalfPeriodJacobi

/-! ### The physical-space coordinate equivalence -/

/-- The physical half-disk point under the actual disk homeomorphism. -/
def diskPoint (R : PaperHalfPeriodRealization k)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) : Trace.PhysicalHalfDisk k :=
  ⟨(R.diskHomeomorph q).val.val,
    ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using (R.diskHomeomorph q).property,
     (R.diskHomeomorph q).val.property⟩⟩

/-- Backward coordinate map value identity: reconstruction evaluates the disk field at the
homeomorph image. -/
@[simp] lemma ofDisk_data_value (R : PaperHalfPeriodRealization k) {b1 b0 : Bool}
    (g : classicalMixedDiskSpace k b1 b0)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    (ClassicalMixedHalfPeriodJacobi.ofDisk R (classicalMixedDiskData g)).value q =
      g.val (R.diskPoint q) :=
  classicalMixedDiskData_value g (R.diskPoint q)

/-- The physical-disk point `z` as a punctured-closed-disk point. -/
def diskPointOfPhysical (z : Trace.PhysicalHalfDisk k) : PuncturedClosedDisk k :=
  ⟨⟨z.val, z.property.2⟩, by simpa [Metric.mem_closedBall, dist_zero_right] using z.property.1⟩

/-- Forward coordinate map: an actual geometric mixed field ↦ its physical-disk values. -/
def mixedHalfPeriodToDiskSpace (R : PaperHalfPeriodRealization k) (b1 b0 : Bool) :
    R.classicalMixedHalfPeriodSpace b1 b0 →ₗ[ℂ] classicalMixedDiskSpace k b1 b0 where
  toFun u := ⟨fun z => R.halfPeriodCoordinate u.val z.val,
    ⟨(R.classicalMixedHalfPeriodData u).toDisk, fun z => by
      change R.halfPeriodCoordinate (R.classicalMixedHalfPeriodData u).value z.val
        = R.halfPeriodCoordinate u.val z.val
      rw [classicalMixedHalfPeriodData_value]⟩⟩
  map_add' u v := by
    apply Subtype.ext; funext z
    simp only [Submodule.coe_add, Pi.add_apply, halfPeriodCoordinate_add]
  map_smul' a u := by
    apply Subtype.ext; funext z
    simp only [Submodule.coe_smul, Pi.smul_apply, halfPeriodCoordinate_smul, RingHom.id_apply,
      smul_eq_mul]

/-- Backward coordinate map: a physical disk field ↦ the reconstructed geometric field. -/
def diskSpaceToMixedHalfPeriod (R : PaperHalfPeriodRealization k) (b1 b0 : Bool) :
    classicalMixedDiskSpace k b1 b0 →ₗ[ℂ] R.classicalMixedHalfPeriodSpace b1 b0 where
  toFun g := ⟨(ClassicalMixedHalfPeriodJacobi.ofDisk R (classicalMixedDiskData g)).value,
    ⟨ClassicalMixedHalfPeriodJacobi.ofDisk R (classicalMixedDiskData g), rfl⟩⟩
  map_add' g h := by
    apply Subtype.ext; funext q
    change (ClassicalMixedHalfPeriodJacobi.ofDisk R (classicalMixedDiskData (g + h))).value q
      = (ClassicalMixedHalfPeriodJacobi.ofDisk R (classicalMixedDiskData g)).value q
      + (ClassicalMixedHalfPeriodJacobi.ofDisk R (classicalMixedDiskData h)).value q
    rw [R.ofDisk_data_value, R.ofDisk_data_value, R.ofDisk_data_value, Submodule.coe_add,
      Pi.add_apply]
  map_smul' a g := by
    apply Subtype.ext; funext q
    change (ClassicalMixedHalfPeriodJacobi.ofDisk R (classicalMixedDiskData (a • g))).value q
      = a • (ClassicalMixedHalfPeriodJacobi.ofDisk R (classicalMixedDiskData g)).value q
    rw [R.ofDisk_data_value, R.ofDisk_data_value, Submodule.coe_smul, Pi.smul_apply]

/-- The geometric mixed half-period field space is linearly equivalent to the
physical disk field space through the `toDisk` and `ofDisk` coordinate maps. -/
def classicalMixedHalfPeriodDiskEquiv (R : PaperHalfPeriodRealization k) (b1 b0 : Bool) :
    R.classicalMixedHalfPeriodSpace b1 b0 ≃ₗ[ℂ] classicalMixedDiskSpace k b1 b0 :=
  LinearEquiv.ofLinearMap (R.mixedHalfPeriodToDiskSpace b1 b0) (R.diskSpaceToMixedHalfPeriod b1 b0)
    (by
      refine LinearMap.ext fun g => ?_
      apply Subtype.ext; funext z
      change R.halfPeriodCoordinate
        (ClassicalMixedHalfPeriodJacobi.ofDisk R (classicalMixedDiskData g)).value
          (diskPointOfPhysical z).val.val = g.val z
      rw [R.halfPeriodCoordinate_apply, R.ofDisk_data_value]
      have hz : R.diskPoint (R.diskHomeomorph.symm (diskPointOfPhysical z)) = z := by
        apply Subtype.ext
        exact congrArg (fun w : PuncturedClosedDisk k => w.val.val)
          (R.diskHomeomorph.apply_symm_apply (diskPointOfPhysical z))
      rw [hz])
    (by
      refine LinearMap.ext fun u => ?_
      apply Subtype.ext; funext q
      change (ClassicalMixedHalfPeriodJacobi.ofDisk R
        (classicalMixedDiskData (R.mixedHalfPeriodToDiskSpace b1 b0 u))).value q = u.val q
      rw [R.ofDisk_data_value]
      change R.halfPeriodCoordinate u.val (R.diskHomeomorph q).val.val = u.val q
      rw [R.halfPeriodCoordinate_apply u.val (R.diskHomeomorph q), Homeomorph.symm_apply_apply])

/-- Value agreement: the coordinate equivalence sends a geometric field to its disk coordinates. -/
@[simp] lemma classicalMixedHalfPeriodDiskEquiv_apply (R : PaperHalfPeriodRealization k)
    {b1 b0 : Bool} (u : R.classicalMixedHalfPeriodSpace b1 b0) (z : Trace.PhysicalHalfDisk k) :
    (R.classicalMixedHalfPeriodDiskEquiv b1 b0 u).val z = R.halfPeriodCoordinate u.val z.val :=
  rfl

/-- **Commuting weak representatives:** the geometric and disk Sobolev maps agree through the
coordinate equivalence. This is what lets the nullity endpoint be a composition of identified
fields rather than a standalone dimension identity. -/
theorem classicalMixedHalfPeriodToH1_eq_disk (R : PaperHalfPeriodRealization k) {b1 b0 : Bool}
    (u : R.classicalMixedHalfPeriodSpace b1 b0) :
    R.classicalMixedHalfPeriodToH1 b1 b0 u
      = classicalMixedDiskToH1 h.out b1 b0 (R.classicalMixedHalfPeriodDiskEquiv b1 b0 u) := by
  refine mixed_toH1_eq_of_eqOn h.out
    (R.classicalMixedHalfPeriodData u).toDisk
    (classicalMixedDiskData (R.classicalMixedHalfPeriodDiskEquiv b1 b0 u)) ?_
  intro w hw
  have key : (classicalMixedDiskData (R.classicalMixedHalfPeriodDiskEquiv b1 b0 u)).value w
      = R.halfPeriodCoordinate u.val w :=
    classicalMixedDiskData_value (R.classicalMixedHalfPeriodDiskEquiv b1 b0 u) ⟨w, hw⟩
  change (R.classicalMixedHalfPeriodData u).toDisk.value w = _
  rw [key]
  change R.halfPeriodCoordinate (R.classicalMixedHalfPeriodData u).value w
    = R.halfPeriodCoordinate u.val w
  rw [classicalMixedHalfPeriodData_value]

end KsIndex.KarcherData.PaperHalfPeriodRealization
