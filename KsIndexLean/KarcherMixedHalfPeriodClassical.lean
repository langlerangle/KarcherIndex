module

public import KsIndexLean.KarcherHalfPeriodClassicalInverse
public import KsIndexLean.KarcherHalfPeriodBoundary
public import KsIndexLean.MixedHalfDiskHemisphere

@[expose] public section


/-! Classical mixed boundary fields on the actual EW half-period. Boundary
conditions are imposed at the physical heights 0 and π; their disk arc labels
are derived from the height identification. No finite energy or reflected
continuation is assumed. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The first flag concerns physical height π, the second physical height 0.
A true flag imposes zero unit-conormal derivative; false imposes zero value. -/
structure ClassicalMixedHalfPeriodJacobi (R : PaperHalfPeriodRealization k)
    (b1 b0 : Bool) where
  value : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) (R.halfPeriodCoordinate value) Surface.disk
  bounded : ∃ C : ℝ, ∀ q, ‖value q‖ ≤ C
  equation : ∀ w : PuncturedClosedDisk k, ‖w.val.val‖ < 1 → R.halfPeriodJacobiAt value w = 0
  boundary : ∀ w : PuncturedClosedDisk k, ‖w.val.val‖ = 1 →
    ∃ F : ℂ → ℂ, ContDiffAt ℝ (⊤ : ℕ∞) F w.val.val ∧
      (∀ᶠ z in nhds w.val.val, ‖z‖ ≤ 1 → R.halfPeriodCoordinate value z = F z) ∧
      (HeightLift.height (R.diskHomeomorph.symm w).val + Real.pi = Real.pi →
        if b1 then fderiv ℝ F w.val.val ((Surface.rho k w.val.val)⁻¹ • w.val.val) = 0
        else F w.val.val = 0) ∧
      (HeightLift.height (R.diskHomeomorph.symm w).val + Real.pi = 0 →
        if b0 then fderiv ℝ F w.val.val ((Surface.rho k w.val.val)⁻¹ • w.val.val) = 0
        else F w.val.val = 0)

lemma coordinate_height_zero_iff_arc (R : PaperHalfPeriodRealization k)
    (w : PuncturedClosedDisk k) :
    HeightLift.height (R.diskHomeomorph.symm w).val + Real.pi = 0 ↔
      w.val.val ∈ Surface.arc k 0 :=
  halfPeriod_height_zero_iff_arc h.out (reflectionBasepoint k) w.val rfl R.C
    (R.diskHomeomorph.symm w) (R.diskHomeomorph_symm_projection w)

lemma coordinate_height_pi_iff_arc (R : PaperHalfPeriodRealization k)
    (w : PuncturedClosedDisk k) :
    HeightLift.height (R.diskHomeomorph.symm w).val + Real.pi = Real.pi ↔
      w.val.val ∈ Surface.arc k 1 :=
  halfPeriod_height_pi_iff_arc h.out (reflectionBasepoint k) w.val rfl R.C
    (R.diskHomeomorph.symm w) (R.diskHomeomorph_symm_projection w)

namespace ClassicalMixedHalfPeriodJacobi
variable {R : PaperHalfPeriodRealization k} {b1 b0 : Bool}

/-- The geometric PDE and physical boundary conditions give the mixed disk
PDE and its separate arc conditions. -/
def toDisk (u : R.ClassicalMixedHalfPeriodJacobi b1 b0) :
    Trace.ClassicalMixedHalfDiskJacobi k b1 b0 where
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
    let w : PuncturedClosedDisk k := ⟨⟨z,hp⟩,hz.le⟩
    obtain ⟨F,hF,hs,h1,h0⟩ := u.boundary w hz
    refine ⟨F,hF,hs,?_,?_⟩
    · intro ha
      have hb := h1 ((R.coordinate_height_pi_iff_arc w).mpr ha)
      cases b1
      · exact hb
      · exact (unit_conormal_derivative_zero_iff
          (Surface.rho_pos (by have := h.out; omega) hp) F z).mp hb
    · intro ha
      have hb := h0 ((R.coordinate_height_zero_iff_arc w).mpr ha)
      cases b0
      · exact hb
      · exact (unit_conormal_derivative_zero_iff
          (Surface.rho_pos (by have := h.out; omega) hp) F z).mp hb

/-- Pulling a mixed disk field back yields the actual immersion equation and
unit-conormal conditions at the correct physical boundary heights. -/
def ofDisk (R : PaperHalfPeriodRealization k)
    (u : Trace.ClassicalMixedHalfDiskJacobi k b1 b0) :
    R.ClassicalMixedHalfPeriodJacobi b1 b0 where
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
    obtain ⟨F,hF,hs,h1,h0⟩ := u.boundary w.val.val hw w.val.property
    refine ⟨F,hF,?_,?_,?_⟩
    · have ho : IsOpen {z : ℂ | z ∉ Surface.punctures k} :=
        isOpen_ne_fun (continuous_id.pow (2 * k)) continuous_const
      filter_upwards [hs, ho.mem_nhds w.val.property] with z hz hp
      intro hnorm
      exact (R.halfPeriodCoordinate_ofCoordinate u.value hnorm hp).trans (hz hnorm)
    · intro hh
      have hb := h1 ((R.coordinate_height_pi_iff_arc w).mp hh)
      cases b1
      · exact hb
      · exact (unit_conormal_derivative_zero_iff
          (Surface.rho_pos (by have := h.out; omega) w.val.property) F w.val.val).mpr hb
    · intro hh
      have hb := h0 ((R.coordinate_height_zero_iff_arc w).mp hh)
      cases b0
      · exact hb
      · exact (unit_conormal_derivative_zero_iff
          (Surface.rho_pos (by have := h.out; omega) w.val.property) F w.val.val).mpr hb

/-- Reconstruction recovers every actual half-period value. -/
@[simp] theorem ofDisk_toDisk_value (u : R.ClassicalMixedHalfPeriodJacobi b1 b0) :
    (ofDisk R u.toDisk).value = u.value := by
  funext q
  change R.halfPeriodCoordinate u.value (R.diskHomeomorph q).val.val = u.value q
  simp only [halfPeriodCoordinate_apply, Homeomorph.symm_apply_apply]

/-- Disk reconstruction recovers all physical disk values. Exterior and
puncture values are deliberately not part of this identity. -/
theorem toDisk_ofDisk_closed (R : PaperHalfPeriodRealization k)
    (u : Trace.ClassicalMixedHalfDiskJacobi k b1 b0) :
    EqOn (ofDisk R u).toDisk.value u.value
      (Metric.closedBall (0 : ℂ) 1 \ Surface.punctures k) := by
  intro z hz
  exact R.halfPeriodCoordinate_ofCoordinate u.value
    (by simpa [Metric.mem_closedBall,dist_zero_right] using hz.1) hz.2

/-- The geometric bounded field supplies a weak field on the actual round
hemisphere; finite energy has been proved rather than assumed. -/
def toHemisphere (u : R.ClassicalMixedHalfPeriodJacobi b1 b0) :
    Spherical.HemisphereChartSpace := u.toDisk.toHemisphere h.out

/-- An interior rotation character places the geometric field in the
corresponding mixed spherical Sobolev domain. -/
theorem toHemisphere_mem_character (u : R.ClassicalMixedHalfPeriodJacobi b1 b0) (j : ℕ)
    (hc : ∀ w ∈ Surface.disk,
      R.halfPeriodCoordinate u.value (Trace.planeRotation (-(2 * Real.pi) / k) w) =
        FormIndex.zeta k ^ j * R.halfPeriodCoordinate u.value w) :
    u.toHemisphere ∈ Spherical.hemisphereMixedCharacterDomain k j b1 b0 :=
  u.toDisk.toHemisphere_mem_character h.out j hc

/-- The geometric Jacobi equation yields the canonical-area weak equation
against every mixed character test on the hemisphere. -/
theorem toHemisphere_tests_zero (u : R.ClassicalMixedHalfPeriodJacobi b1 b0) (j : ℕ)
    (v : Spherical.hemisphereMixedCharacterDomain k j b1 b0) :
    Spherical.hemisphereJacobi (WeakH1.surfacePotential k) u.toHemisphere v.val = 0 :=
  u.toDisk.toHemisphere_tests_zero h.out j v

end ClassicalMixedHalfPeriodJacobi
end KsIndex.KarcherData.PaperHalfPeriodRealization
