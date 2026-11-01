module

public import KsIndexLean.KarcherHalfPeriodLinear
public import KsIndexLean.KarcherDiskRotation
public import KsIndexLean.HalfDiskReflection
public import KsIndexLean.PureSectorRadicalEquivalence

@[expose] public section


/-! Rotation characters of actual classical EW half-period fields and their
maps into the full-test weak Jacobi radicals. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Trace KsIndex.WeakH1 KsIndex.FormIndex KsIndex.Spectral
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma halfPeriodCoordinate_rotation (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ)
    (w : PuncturedClosedDisk k) :
    R.halfPeriodCoordinate f (planeRotation (-(2 * Real.pi) / k) w.val.val) =
      f (R.halfPeriodRotation (R.diskHomeomorph.symm w)) := by
  have hr : (R.diskRotation w).val.val = planeRotation (-(2 * Real.pi) / k) w.val.val := by
    simpa only [planeRotation_apply,neg_mul] using R.diskRotation_coordinate w
  rw [← hr,halfPeriodCoordinate_apply]
  exact congrArg f (R.diskHomeomorph.symm_apply_apply
    (R.halfPeriodRotation (R.diskHomeomorph.symm w)))

/-- The character condition is imposed using the actual geometric rotation. -/
def classicalHalfPeriodCharacter (R : PaperHalfPeriodRealization k) (b : Bool) (j : ℕ) :
    Submodule ℂ (R.classicalHalfPeriodSpace b) where
  carrier := {u | ∀ q, u.val (R.halfPeriodRotation q) = zeta k ^ j * u.val q}
  zero_mem' := by intro q; simp
  add_mem' := by
    intro u v hu hv q
    change u.val (R.halfPeriodRotation q) + v.val (R.halfPeriodRotation q) =
      zeta k ^ j * (u.val q + v.val q)
    rw [hu,hv,mul_add]
  smul_mem' := by
    intro a u hu q
    change a * u.val (R.halfPeriodRotation q) = zeta k ^ j * (a * u.val q)
    rw [hu]
    ring

lemma classical_character_coordinate (R : PaperHalfPeriodRealization k) {b : Bool} {j : ℕ}
    (u : R.classicalHalfPeriodCharacter b j) {z : ℂ} (hz : z ∈ Surface.disk) :
    (R.classicalHalfPeriodData u.val).toDisk.value (planeRotation (-(2 * Real.pi) / k) z) =
      zeta k ^ j * (R.classicalHalfPeriodData u.val).toDisk.value z := by
  let w : PuncturedClosedDisk k := ⟨⟨z,Surface.punctures_notMem_disk (k := k)
    (by have := h.out; omega) hz⟩,(SurfaceForm.mem_disk_iff.mp hz).le⟩
  change R.halfPeriodCoordinate (R.classicalHalfPeriodData u.val).value
    (planeRotation (-(2 * Real.pi) / k) w.val.val) =
    zeta k ^ j * R.halfPeriodCoordinate (R.classicalHalfPeriodData u.val).value w.val.val
  rw [classicalHalfPeriodData_value,halfPeriodCoordinate_rotation,halfPeriodCoordinate_apply]
  exact u.property _

/-- The weak representative lies in precisely the pure-boundary character domain. -/
lemma classical_character_mem_domain (R : PaperHalfPeriodRealization k) {b : Bool} {j : ℕ}
    (u : R.classicalHalfPeriodCharacter b j) :
    R.classicalHalfPeriodToH1 b u.val ∈ mixedCharacterDomain k j b b := by
  have hc := (R.classicalHalfPeriodData u.val).toDisk.toH1_character h.out _ _
    (fun z hz => R.classical_character_coordinate u hz)
  cases b
  · rw [mixedDD_eq_fullDirichletCharacter (by have := h.out; omega)]
    exact ⟨(R.classicalHalfPeriodData u.val).toDisk.dirichlet_mem_zeroTrace h.out,hc⟩
  · exact ⟨(mixedTraceDomain_NN k).symm ▸ Submodule.mem_top,hc⟩

abbrev halfPeriodWeakRadical (k j : ℕ) (b : Bool) :=
  @formRadical (mixedCharacterDomain k j b b) inferInstance (diskDomain_innerProductSpace _)
    (domainJacobiForm (mixedCharacterDomain k j b b) (surfacePotential k))

/-- Actual geometric character fields pair to zero against every admissible
weak test, not only against classical compact tests. -/
def classicalHalfPeriodToRadical (R : PaperHalfPeriodRealization k) (b : Bool) (j : ℕ) :
    R.classicalHalfPeriodCharacter b j →ₗ[ℂ] halfPeriodWeakRadical k j b := by
  let L := (R.classicalHalfPeriodToH1 b).comp (R.classicalHalfPeriodCharacter b j).subtype
  let M : R.classicalHalfPeriodCharacter b j →ₗ[ℂ] mixedCharacterDomain k j b b :=
    L.codRestrict _ (fun u => R.classical_character_mem_domain u)
  exact M.codRestrict _ (fun u => (mem_formRadical _ _).mpr (fun v =>
    (R.classicalHalfPeriodData u.val).toDisk.character_tests_zero h.out j v))

@[simp] lemma classicalHalfPeriodToRadical_value (R : PaperHalfPeriodRealization k)
    (b : Bool) (j : ℕ) (u : R.classicalHalfPeriodCharacter b j) :
    (R.classicalHalfPeriodToRadical b j u).val.val = R.classicalHalfPeriodToH1 b u.val := rfl

theorem classicalHalfPeriodToRadical_injective (R : PaperHalfPeriodRealization k)
    (b : Bool) (j : ℕ) : Function.Injective (R.classicalHalfPeriodToRadical b j) := by
  intro u v he
  apply Subtype.ext
  apply R.classicalHalfPeriodToH1_injective b
  exact congrArg (fun x : halfPeriodWeakRadical k j b => x.val.val) he

/-- A classical coordinate character defines the actual geometric character. -/
def classicalCharacterOfDisk (R : PaperHalfPeriodRealization k) {b : Bool} (j : ℕ)
    (u : ClassicalHalfDiskJacobi k b)
    (hc : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      u.value (planeRotation (-(2 * Real.pi) / k) z) = zeta k ^ j * u.value z) :
    R.classicalHalfPeriodCharacter b j := by
  refine ⟨(ClassicalHalfPeriodJacobi.ofDisk R u).toSpace,?_⟩
  intro q
  change u.value (R.diskHomeomorph (R.halfPeriodRotation q)).val.val =
    zeta k ^ j * u.value (R.diskHomeomorph q).val.val
  have hr : (R.diskHomeomorph (R.halfPeriodRotation q)).val.val =
      planeRotation (-(2 * Real.pi) / k) (R.diskHomeomorph q).val.val := by
    have hh := R.diskRotation_coordinate (R.diskHomeomorph q)
    simpa only [diskRotation,Homeomorph.symm_apply_apply,planeRotation_apply,neg_mul] using hh
  rw [hr]
  exact hc _ (by simpa [Metric.mem_closedBall,dist_zero_right] using (R.diskHomeomorph q).property)

@[simp] theorem classicalCharacterOfDisk_toH1 (R : PaperHalfPeriodRealization k)
    {b : Bool} (j : ℕ) (u : ClassicalHalfDiskJacobi k b)
    (hc : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      u.value (planeRotation (-(2 * Real.pi) / k) z) = zeta k ^ j * u.value z) :
    R.classicalHalfPeriodToH1 b (R.classicalCharacterOfDisk j u hc).val = u.toH1 h.out := by
  exact (ClassicalHalfPeriodJacobi.toSpace_toH1 _).trans
    (ClassicalHalfPeriodJacobi.toDisk_ofDisk_toH1 R u)

end KsIndex.KarcherData.PaperHalfPeriodRealization
