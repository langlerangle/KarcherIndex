module

public import KsIndexLean.KarcherHalfPeriodClassical
public import KsIndexLean.JacobiFamily

@[expose] public section


/-! Pullback of classical disk fields to the actual EW half-period.
The inverse identities concern physical values, without retaining arbitrary
values at deleted points or outside the disk. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Pull a coordinate function back to the actual closed half-period. -/
def halfPeriodOfCoordinate (R : PaperHalfPeriodRealization k) (f : ℂ → ℂ)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) : ℂ :=
  f (R.diskHomeomorph q).val.val

lemma halfPeriodCoordinate_ofCoordinate (R : PaperHalfPeriodRealization k) (f : ℂ → ℂ)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (hp : z ∉ Surface.punctures k) :
    R.halfPeriodCoordinate (R.halfPeriodOfCoordinate f) z = f z := by
  have hh := R.halfPeriodCoordinate_apply (R.halfPeriodOfCoordinate f)
    (⟨⟨z,hp⟩,hz⟩ : PuncturedClosedDisk k)
  exact hh.trans (congrArg (fun w : PuncturedClosedDisk k => f w.val.val)
    (R.diskHomeomorph.apply_symm_apply (⟨⟨z,hp⟩,hz⟩ : PuncturedClosedDisk k)))

lemma halfPeriodCoordinate_ofCoordinate_germ (R : PaperHalfPeriodRealization k)
    (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ Surface.disk) :
    R.halfPeriodCoordinate (R.halfPeriodOfCoordinate f) =ᶠ[nhds z] f := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  exact R.halfPeriodCoordinate_ofCoordinate f (SurfaceForm.mem_disk_iff.mp hw).le
    (Surface.punctures_notMem_disk (k := k) (by have := h.out; omega) hw)

namespace ClassicalHalfPeriodJacobi
variable {R : PaperHalfPeriodRealization k} {b : Bool}

/-- A coordinate classical field defines a classical field on the actual
half-period, with the actual immersion equation and unit-conormal condition. -/
def ofDisk (R : PaperHalfPeriodRealization k) (u : Trace.ClassicalHalfDiskJacobi k b) :
    R.ClassicalHalfPeriodJacobi b where
  value := R.halfPeriodOfCoordinate u.value
  smooth := u.smooth.congr (fun z hz => R.halfPeriodCoordinate_ofCoordinate u.value
    (SurfaceForm.mem_disk_iff.mp hz).le
    (Surface.punctures_notMem_disk (k := k) (by have := h.out; omega) hz))
  bounded := by
    obtain ⟨C,hC⟩ := u.bounded
    exact ⟨C,fun q => hC _ (R.diskHomeomorph q).property (R.diskHomeomorph q).val.property⟩
  equation := by
    intro w hw
    have hd : w.val.val ∈ Surface.disk := SurfaceForm.mem_disk_iff.mpr hw
    have hg := R.halfPeriodCoordinate_ofCoordinate_germ u.value hd
    apply (R.halfPeriodJacobiAt_eq _ w).trans
    apply (diskJacobi_eq_zero_iff_flat h.out w.val.property _).mpr
    rw [JacobiFamily.laplacian_congr hg, hg.self_of_nhds]
    exact u.equation _ hd
  boundary := by
    intro w hw
    obtain ⟨F,hF,hs,hB⟩ := u.boundary w.val.val hw w.val.property
    refine ⟨F,hF,?_,?_⟩
    · have ho : IsOpen {z : ℂ | z ∉ Surface.punctures k} :=
        isOpen_ne_fun (continuous_id.pow (2 * k)) continuous_const
      filter_upwards [hs, ho.mem_nhds w.val.property] with z hz hp
      intro hnorm
      exact (R.halfPeriodCoordinate_ofCoordinate u.value hnorm hp).trans (hz hnorm)
    · cases b
      · exact hB
      · exact (unit_conormal_derivative_zero_iff
          (Surface.rho_pos (by have := h.out; omega) w.val.property) F w.val.val).mpr hB

/-- Reconstructing a geometric field from its coordinates recovers all actual
half-period values. -/
@[simp] theorem ofDisk_toDisk_value (u : R.ClassicalHalfPeriodJacobi b) :
    (ofDisk R u.toDisk).value = u.value := by
  funext q
  change R.halfPeriodCoordinate u.value (R.diskHomeomorph q).val.val = u.value q
  simp only [halfPeriodCoordinate_apply, Homeomorph.symm_apply_apply]

/-- Reconstructing disk data recovers exactly its physical values. -/
theorem toDisk_ofDisk_closed (R : PaperHalfPeriodRealization k)
    (u : Trace.ClassicalHalfDiskJacobi k b) :
    EqOn (ofDisk R u).toDisk.value u.value
      (Metric.closedBall (0 : ℂ) 1 \ Surface.punctures k) := by
  intro z hz
  exact R.halfPeriodCoordinate_ofCoordinate u.value
    (by simpa [Metric.mem_closedBall,dist_zero_right] using hz.1) hz.2

/-- The inverse construction also preserves the actual Sobolev representative. -/
@[simp] theorem toDisk_ofDisk_toH1 (R : PaperHalfPeriodRealization k)
    (u : Trace.ClassicalHalfDiskJacobi k b) :
    (ofDisk R u).toDisk.toH1 h.out = u.toH1 h.out :=
  ((ofDisk R u).toDisk.toH1_eq_iff_closed u h.out).mpr (toDisk_ofDisk_closed R u)

end ClassicalHalfPeriodJacobi
end KsIndex.KarcherData.PaperHalfPeriodRealization
