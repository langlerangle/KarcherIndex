module

public import KsIndexLean.KarcherHalfPeriodClassicalInverse
public import KsIndexLean.HalfDiskLinear

@[expose] public section


/-! The complex vector space of actual bounded classical half-period fields,
and its faithful linear map to the disk Sobolev space. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Trace KsIndex.WeakH1
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Actual half-period functions satisfying the classical geometric conditions. -/
def classicalHalfPeriodSpace (R : PaperHalfPeriodRealization k) (b : Bool) :
    Submodule ℂ (PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) where
  carrier := {f | ∃ u : R.ClassicalHalfPeriodJacobi b, u.value = f}
  zero_mem' := by
    refine ⟨ClassicalHalfPeriodJacobi.ofDisk R (ClassicalHalfDiskJacobi.zeroData k b),?_⟩
    rfl
  add_mem' := by
    rintro f g ⟨u,rfl⟩ ⟨v,rfl⟩
    refine ⟨ClassicalHalfPeriodJacobi.ofDisk R (u.toDisk.addData v.toDisk),?_⟩
    funext q
    change R.halfPeriodCoordinate u.value (R.diskHomeomorph q).val.val +
      R.halfPeriodCoordinate v.value (R.diskHomeomorph q).val.val = u.value q + v.value q
    simp only [halfPeriodCoordinate_apply,Homeomorph.symm_apply_apply]
  smul_mem' := by
    rintro a f ⟨u,rfl⟩
    refine ⟨ClassicalHalfPeriodJacobi.ofDisk R (u.toDisk.smulData a),?_⟩
    funext q
    change a * R.halfPeriodCoordinate u.value (R.diskHomeomorph q).val.val = a * u.value q
    simp only [halfPeriodCoordinate_apply,Homeomorph.symm_apply_apply]

/-- A proof-bearing representative of an actual field. The underlying function
is fixed; this choice affects only proof data. -/
def classicalHalfPeriodData (R : PaperHalfPeriodRealization k) {b : Bool}
    (u : R.classicalHalfPeriodSpace b) : R.ClassicalHalfPeriodJacobi b := u.property.choose

@[simp] lemma classicalHalfPeriodData_value (R : PaperHalfPeriodRealization k) {b : Bool}
    (u : R.classicalHalfPeriodSpace b) : (R.classicalHalfPeriodData u).value = u.val :=
  u.property.choose_spec

lemma halfPeriodCoordinate_add (R : PaperHalfPeriodRealization k)
    (f g : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) (z : ℂ) :
    R.halfPeriodCoordinate (f+g) z = R.halfPeriodCoordinate f z + R.halfPeriodCoordinate g z := by
  unfold halfPeriodCoordinate
  split_ifs <;> simp only [Pi.add_apply,add_zero]

lemma halfPeriodCoordinate_smul (R : PaperHalfPeriodRealization k) (a : ℂ)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) (z : ℂ) :
    R.halfPeriodCoordinate (a • f) z = a • R.halfPeriodCoordinate f z := by
  unfold halfPeriodCoordinate
  split_ifs <;> simp only [Pi.smul_apply,smul_zero]

/-- The classical field's actual weak representative; finite energy is derived
by the preceding cutoff proof, not required in the source space. -/
def classicalHalfPeriodToH1 (R : PaperHalfPeriodRealization k) (b : Bool) :
    R.classicalHalfPeriodSpace b →ₗ[ℂ] ComplexH1 where
  toFun u := (R.classicalHalfPeriodData u).toDisk.toH1 h.out
  map_add' u v := by
    apply valueCLM_injective
    rw [map_add]
    apply Lp.ext
    filter_upwards [(R.classicalHalfPeriodData (u+v)).toDisk.toH1_value_ae h.out,
      (R.classicalHalfPeriodData u).toDisk.toH1_value_ae h.out,
      (R.classicalHalfPeriodData v).toDisk.toH1_value_ae h.out,
      Lp.coeFn_add (valueCLM ((R.classicalHalfPeriodData u).toDisk.toH1 h.out))
        (valueCLM ((R.classicalHalfPeriodData v).toDisk.toH1 h.out))] with z huv hu hv ha
    rw [huv,ha]
    simp only [Pi.add_apply]
    rw [hu,hv]
    change R.halfPeriodCoordinate (R.classicalHalfPeriodData (u+v)).value z =
      R.halfPeriodCoordinate (R.classicalHalfPeriodData u).value z +
      R.halfPeriodCoordinate (R.classicalHalfPeriodData v).value z
    simp only [classicalHalfPeriodData_value,Submodule.coe_add,halfPeriodCoordinate_add]
  map_smul' a u := by
    apply valueCLM_injective
    rw [map_smul]
    apply Lp.ext
    filter_upwards [(R.classicalHalfPeriodData (a • u)).toDisk.toH1_value_ae h.out,
      (R.classicalHalfPeriodData u).toDisk.toH1_value_ae h.out,
      Lp.coeFn_smul a (valueCLM ((R.classicalHalfPeriodData u).toDisk.toH1 h.out))]
      with z hau hu ha
    simp only [RingHom.id_apply]
    rw [hau,ha]
    simp only [Pi.smul_apply]
    rw [hu]
    change R.halfPeriodCoordinate (R.classicalHalfPeriodData (a • u)).value z =
      a • R.halfPeriodCoordinate (R.classicalHalfPeriodData u).value z
    simp only [classicalHalfPeriodData_value,Submodule.coe_smul,halfPeriodCoordinate_smul]

/-- The weak representative loses no actual half-period field. -/
theorem classicalHalfPeriodToH1_injective (R : PaperHalfPeriodRealization k) (b : Bool) :
    Function.Injective (R.classicalHalfPeriodToH1 b) := by
  intro u v he
  have hh := ClassicalHalfPeriodJacobi.value_eq_of_toH1_eq
    (R.classicalHalfPeriodData u) (R.classicalHalfPeriodData v) he
  apply Subtype.ext
  simpa only [classicalHalfPeriodData_value] using hh

/-- Pointwise a.e. description of the linear weak representative. -/
lemma classicalHalfPeriodToH1_value_ae (R : PaperHalfPeriodRealization k) {b : Bool}
    (u : R.classicalHalfPeriodSpace b) :
    valueCLM (R.classicalHalfPeriodToH1 b u) =ᵐ[volume.restrict (Surface.disk : Set ℂ)]
      R.halfPeriodCoordinate u.val := by
  filter_upwards [(R.classicalHalfPeriodData u).toDisk.toH1_value_ae h.out] with z hz
  exact hz.trans (congrArg (fun f => R.halfPeriodCoordinate f z)
    (R.classicalHalfPeriodData_value u))

namespace ClassicalHalfPeriodJacobi
variable {R : PaperHalfPeriodRealization k} {b : Bool}

/-- Forget proof data, retaining the actual function in its linear space. -/
def toSpace (u : R.ClassicalHalfPeriodJacobi b) : R.classicalHalfPeriodSpace b :=
  ⟨u.value,⟨u,rfl⟩⟩

@[simp] theorem toSpace_toH1 (u : R.ClassicalHalfPeriodJacobi b) :
    R.classicalHalfPeriodToH1 b u.toSpace = u.toDisk.toH1 h.out := by
  apply ((R.classicalHalfPeriodData u.toSpace).toDisk.toH1_eq_iff_closed u.toDisk h.out).mpr
  intro z hz
  change R.halfPeriodCoordinate (R.classicalHalfPeriodData u.toSpace).value z =
    R.halfPeriodCoordinate u.value z
  rw [classicalHalfPeriodData_value]
  rfl

end ClassicalHalfPeriodJacobi
end KsIndex.KarcherData.PaperHalfPeriodRealization
