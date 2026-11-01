module

public import KsIndexLean.KarcherBoundaryConormal
public import KsIndexLean.KarcherGeometricJacobi
public import KsIndexLean.KarcherDiskJacobiOperator
public import KsIndexLean.KarcherHalfPeriodHomeomorph
public import KsIndexLean.HalfDiskExtensional

@[expose] public section


/-! Classical bounded fields on the actual closed EW half-period.
Smoothness is expressed in its finite parameter coordinate, with one-sided
smooth germs at the boundary. The equation uses the actual immersion metric
and curvature. Neither global reflection nor finite energy is assumed. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]
attribute [local instance] Classical.propDecidable

/-- Coordinate representative of an actual half-period function, extended by
zero only outside its physical domain. -/
def halfPeriodCoordinate (R : PaperHalfPeriodRealization k)
    (u : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) (z : ℂ) : ℂ :=
  if hz : ‖z‖ ≤ 1 ∧ z ∉ Surface.punctures k then
    u (R.diskHomeomorph.symm ⟨⟨z,hz.2⟩,hz.1⟩) else 0

@[simp] lemma halfPeriodCoordinate_apply (R : PaperHalfPeriodRealization k)
    (u : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ)
    (w : PuncturedClosedDisk k) :
    R.halfPeriodCoordinate u w.val.val = u (R.diskHomeomorph.symm w) := by
  rcases w with ⟨⟨z,hp⟩,hz⟩
  simp [halfPeriodCoordinate,hz,hp]

/-- The actual Jacobi operator in the finite immersion chart at a half-period
point. The arbitrary exterior extension is irrelevant at interior points. -/
def halfPeriodJacobiAt (R : PaperHalfPeriodRealization k)
    (u : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ)
    (w : PuncturedClosedDisk k) : ℂ :=
  let X := R.centeredChart (R.diskHomeomorph.symm w).val
  conformalLaplaceBeltrami (fun z => chartAreaDensity X z)
    (R.halfPeriodCoordinate u) w.val.val +
    (conformalSecondFundamentalNorm X w.val.val (chartAreaDensity X w.val.val) : ℂ)^2 *
      u (R.diskHomeomorph.symm w)

lemma halfPeriodJacobiAt_eq (R : PaperHalfPeriodRealization k)
    (u : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ)
    (w : PuncturedClosedDisk k) :
    R.halfPeriodJacobiAt u w = diskJacobi k (R.halfPeriodCoordinate u) w.val.val := by
  have hp := R.diskHomeomorph_symm_projection w
  dsimp only [halfPeriodJacobiAt]
  rw [R.centeredChart_finite_laplaceBeltrami _ _ hp,
    R.centeredChart_areaDensity _ _ hp, (R.centeredChart_finite_curvature _ _ hp).2]
  simp only [diskJacobi, halfPeriodCoordinate_apply]

/-- A bounded classical field on the actual half-period. Boundary smoothness
means a local extension, not a prescribed reflected extension. The normal
vector is normalized using the actual conformal immersion metric. -/
structure ClassicalHalfPeriodJacobi (R : PaperHalfPeriodRealization k) (neumann : Bool) where
  value : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) (R.halfPeriodCoordinate value) Surface.disk
  bounded : ∃ C : ℝ, ∀ q, ‖value q‖ ≤ C
  equation : ∀ w : PuncturedClosedDisk k, ‖w.val.val‖ < 1 → R.halfPeriodJacobiAt value w = 0
  boundary : ∀ w : PuncturedClosedDisk k, ‖w.val.val‖ = 1 →
    ∃ F : ℂ → ℂ, ContDiffAt ℝ (⊤ : ℕ∞) F w.val.val ∧
      (∀ᶠ z in nhds w.val.val, ‖z‖ ≤ 1 → R.halfPeriodCoordinate value z = F z) ∧
      if neumann then fderiv ℝ F w.val.val ((Surface.rho k w.val.val)⁻¹ • w.val.val) = 0
      else F w.val.val = 0

namespace ClassicalHalfPeriodJacobi
variable {R : PaperHalfPeriodRealization k} {b : Bool}

/-- Passing to the disk derives the flat equation and unnormalized radial
boundary condition from their actual geometric counterparts. -/
def toDisk (u : R.ClassicalHalfPeriodJacobi b) : Trace.ClassicalHalfDiskJacobi k b where
  value := R.halfPeriodCoordinate u.value
  smooth := u.smooth
  bounded := by
    obtain ⟨C,hC⟩ := u.bounded
    refine ⟨C,fun z hz hp => ?_⟩
    exact (R.halfPeriodCoordinate_apply u.value ⟨⟨z,hp⟩,hz⟩) ▸ hC _
  equation := by
    intro z hz
    have hp := Surface.punctures_notMem_disk (k := k) (by have := h.out; omega) hz
    have hn : ‖z‖ < 1 := SurfaceForm.mem_disk_iff.mp hz
    have he := u.equation ⟨⟨z,hp⟩,hn.le⟩ hn
    have hf := (R.halfPeriodJacobiAt_eq u.value (⟨⟨z,hp⟩,hn.le⟩ : PuncturedClosedDisk k)).symm.trans he
    exact (diskJacobi_eq_zero_iff_flat h.out hp _).mp hf
  boundary := by
    intro z hz hp
    obtain ⟨F,hF,hs,hB⟩ := u.boundary ⟨⟨z,hp⟩,hz.le⟩ hz
    refine ⟨F,hF,hs,?_⟩
    cases b
    · exact hB
    · exact (unit_conormal_derivative_zero_iff
        (Surface.rho_pos (by have := h.out; omega) hp) F z).mp hB

/-- Equality of the associated weak fields determines the actual geometric
half-period functions, with no artificial exterior degrees of freedom. -/
theorem value_eq_of_toH1_eq (u v : R.ClassicalHalfPeriodJacobi b)
    (he : u.toDisk.toH1 h.out = v.toDisk.toH1 h.out) : u.value = v.value := by
  have hd := (u.toDisk.toH1_eq_iff_closed v.toDisk h.out).mp he
  funext q
  let w := R.diskHomeomorph q
  have hw := hd (show w.val.val ∈ Metric.closedBall (0 : ℂ) 1 \ Surface.punctures k from
    ⟨by simpa [Metric.mem_closedBall,dist_zero_right] using w.property,w.val.property⟩)
  change R.halfPeriodCoordinate u.value w.val.val = R.halfPeriodCoordinate v.value w.val.val at hw
  simpa only [halfPeriodCoordinate_apply, w, Homeomorph.symm_apply_apply] using hw

end ClassicalHalfPeriodJacobi
end KsIndex.KarcherData.PaperHalfPeriodRealization
