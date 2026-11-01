module

public import KsIndexLean.MixedHalfDiskLinear

@[expose] public section


/-! The vector space of actual mixed classical fields on the punctured closed
disk. Arbitrary exterior extensions do not contribute additional dimensions. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.WeakH1

abbrev PhysicalHalfDisk (k : ℕ) := {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) 1 \ punctures k}

def classicalMixedDiskSpace (k : ℕ) (b1 b0 : Bool) :
    Submodule ℂ (PhysicalHalfDisk k → ℂ) where
  carrier := {f | ∃ U : ClassicalMixedHalfDiskJacobi k b1 b0, ∀ z, U.value z.val = f z}
  zero_mem' := ⟨ClassicalMixedHalfDiskJacobi.zeroData k b1 b0, fun _ => rfl⟩
  add_mem' := by
    rintro f g ⟨U, hU⟩ ⟨V, hV⟩
    exact ⟨U.addData V, fun z => by change U.value z.val + V.value z.val = _; rw [hU, hV]; rfl⟩
  smul_mem' := by
    rintro a f ⟨U, hU⟩
    exact ⟨U.smulData a, fun z => by change a * U.value z.val = _; rw [hU]; rfl⟩

def classicalMixedDiskData {k : ℕ} {b1 b0 : Bool} (u : classicalMixedDiskSpace k b1 b0) :
    ClassicalMixedHalfDiskJacobi k b1 b0 := u.property.choose

lemma classicalMixedDiskData_value {k : ℕ} {b1 b0 : Bool}
    (u : classicalMixedDiskSpace k b1 b0) (z : PhysicalHalfDisk k) :
    (classicalMixedDiskData u).value z.val = u.val z := u.property.choose_spec z

/-- The weak representative of a physical classical field, independent of its
chosen extension off the physical domain. -/
def classicalMixedDiskToH1 {k : ℕ} (hk : 2 ≤ k) (b1 b0 : Bool) :
    classicalMixedDiskSpace k b1 b0 →ₗ[ℂ] ComplexH1 where
  toFun u := (classicalMixedDiskData u).toH1 hk
  map_add' u v := by
    apply valueCLM_injective
    rw [map_add]
    apply Lp.ext
    filter_upwards [(classicalMixedDiskData (u+v)).toH1_value_ae hk,
      (classicalMixedDiskData u).toH1_value_ae hk,
      (classicalMixedDiskData v).toH1_value_ae hk,
      Lp.coeFn_add (valueCLM ((classicalMixedDiskData u).toH1 hk))
        (valueCLM ((classicalMixedDiskData v).toH1 hk)),
      ae_restrict_mem measurableSet_disk] with z huv hu hv ha hz
    rw [huv, ha]
    simp only [Pi.add_apply]
    rw [hu, hv]
    let q : PhysicalHalfDisk k := ⟨z, Metric.ball_subset_closedBall hz,
      punctures_notMem_disk (by omega) hz⟩
    change (classicalMixedDiskData (u+v)).value q.val =
      (classicalMixedDiskData u).value q.val + (classicalMixedDiskData v).value q.val
    rw [classicalMixedDiskData_value, classicalMixedDiskData_value, classicalMixedDiskData_value]
    rfl
  map_smul' a u := by
    apply valueCLM_injective
    rw [map_smul]
    apply Lp.ext
    filter_upwards [(classicalMixedDiskData (a • u)).toH1_value_ae hk,
      (classicalMixedDiskData u).toH1_value_ae hk,
      Lp.coeFn_smul a (valueCLM ((classicalMixedDiskData u).toH1 hk)),
      ae_restrict_mem measurableSet_disk] with z hau hu ha hz
    simp only [RingHom.id_apply]
    rw [hau, ha]
    simp only [Pi.smul_apply]
    rw [hu]
    let q : PhysicalHalfDisk k := ⟨z, Metric.ball_subset_closedBall hz,
      punctures_notMem_disk (by omega) hz⟩
    change (classicalMixedDiskData (a • u)).value q.val =
      a • (classicalMixedDiskData u).value q.val
    rw [classicalMixedDiskData_value, classicalMixedDiskData_value]
    rfl

/-- No physical classical field is lost under passage to the Sobolev representative. -/
theorem classicalMixedDiskToH1_injective {k : ℕ} (hk : 2 ≤ k) (b1 b0 : Bool) :
    Function.Injective (classicalMixedDiskToH1 hk b1 b0) := by
  intro u v he
  have hh := ClassicalMixedHalfDiskJacobi.eqOn_of_toH1_eq hk
    (classicalMixedDiskData u) (classicalMixedDiskData v) he
  apply Subtype.ext
  funext z
  simpa only [classicalMixedDiskData_value] using hh z.property

end KsIndex.Trace

#print axioms KsIndex.Trace.classicalMixedDiskSpace
#print axioms KsIndex.Trace.classicalMixedDiskToH1
