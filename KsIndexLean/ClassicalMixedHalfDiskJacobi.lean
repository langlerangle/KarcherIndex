module

public import KsIndexLean.ClassicalHalfDiskJacobi
public import KsIndexLean.NullityGreen

@[expose] public section


/-! Bounded classical Jacobi fields with separate boundary conditions on the
two arc families. Finite energy and reflected continuation are conclusions to
be proved, not fields of this structure. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SingleDisk

/-- Classical data on the closed disk minus the boundary punctures. The flags
refer to arc 1 and arc 0 respectively; true means zero normal derivative. -/
structure ClassicalMixedHalfDiskJacobi (k : ℕ) (b1 b0 : Bool) where
  value : ℂ → ℂ
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) value (disk : Set ℂ)
  bounded : ∃ C : ℝ, ∀ w : ℂ, ‖w‖ ≤ 1 → w ∉ punctures k → ‖value w‖ ≤ C
  equation : ∀ w ∈ (disk : Set ℂ), laplacian value w + (potV k w : ℂ) * value w = 0
  boundary : ∀ w : ℂ, ‖w‖ = 1 → w ∉ punctures k →
    ∃ F : ℂ → ℂ, ContDiffAt ℝ (⊤ : ℕ∞) F w ∧
      (∀ᶠ z in nhds w, ‖z‖ ≤ 1 → value z = F z) ∧
      (w ∈ arc k 1 → if b1 then fderiv ℝ F w w = 0 else F w = 0) ∧
      (w ∈ arc k 0 → if b0 then fderiv ℝ F w w = 0 else F w = 0)

namespace ClassicalMixedHalfDiskJacobi
variable {k : ℕ} {b1 b0 : Bool} (u : ClassicalMixedHalfDiskJacobi k b1 b0)

/-- The punctured closed disk has ordinary interior and one-sided boundary
germs before any continuation across its boundary. -/
lemma disk_germ {w : ℂ} (hw : ‖w‖ ≤ 1) (hp : w ∉ punctures k) :
    ∃ F : ℂ → ℂ, ContDiffAt ℝ (⊤ : ℕ∞) F w ∧ u.value =ᶠ[nhdsWithin w disk] F := by
  rcases lt_or_eq_of_le hw with hi | he
  · exact ⟨u.value, u.smooth.contDiffAt
      (Metric.isOpen_ball.mem_nhds (mem_disk_iff.mpr hi)), EventuallyEq.rfl⟩
  · obtain ⟨F, hF, hs, _⟩ := u.boundary w he hp
    refine ⟨F, hF, ?_⟩
    filter_upwards [hs.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hd
    exact hz (mem_disk_iff.mp hd).le

/-- Each arc's own boundary condition cancels the diagonal Green flux.
No uniform boundary flag around the circle is needed. -/
lemma diagonal_boundary_flux_zero {w : ℂ} (hw : ‖w‖ = 1) (hp : w ∉ punctures k) :
    (starRingEnd ℂ) (fderivWithin ℝ u.value (Metric.closedBall (0 : ℂ) 1) w w) *
      u.value w = 0 := by
  obtain ⟨F, hF, hs, h1, h0⟩ := u.boundary w hw hp
  have hv : u.value w = F w := hs.self_of_nhds hw.le
  rw [NullityDecomp.fderivWithin_closedBall_of_extension hw hF hs, hv]
  rcases mem_arc_of_not_puncture hw hp with ha | ha
  · have hb := h0 ha
    cases b0
    · change F w = 0 at hb
      rw [hb, mul_zero]
    · change fderiv ℝ F w w = 0 at hb
      rw [hb, map_zero, zero_mul]
  · have hb := h1 ha
    cases b1
    · change F w = 0 at hb
      rw [hb, mul_zero]
    · change fderiv ℝ F w w = 0 at hb
      rw [hb, map_zero, zero_mul]

/-- Local smooth germs make every puncture-cutoff energy integral finite. -/
theorem cutoff_energy_integrable (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    IntegrableOn (fun w => (PunctureCutoff.cutP k ε w) ^ 2 *
      gradSq u.value w) disk :=
  FaithfulInjection.integrableOn_cutPSq_gradSq_of_disk_germs hk
    (fun _ hw hp => u.disk_germ hw hp) h0 h1

/-- The cutoff cancels the flux also at the deleted boundary points. -/
theorem cutoff_boundary_flux_zero (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    {w : ℂ} (hw : ‖w‖ = 1) :
    (starRingEnd ℂ) (fderivWithin ℝ u.value (Metric.closedBall (0 : ℂ) 1) w w) *
      (((PunctureCutoff.cutP k ε w) ^ 2 : ℂ) * u.value w) = 0 := by
  by_cases hp : w ∈ punctures k
  · have hc : PunctureCutoff.cutP k ε w = 0 :=
      PunctureCutoff.cutP_eq_zero hk h0 h1
        ⟨w, hp, by simpa only [sub_self, norm_zero] using sq_nonneg ε⟩
    simp [hc]
  · calc
      _ = ((PunctureCutoff.cutP k ε w) ^ 2 : ℂ) *
          ((starRingEnd ℂ) (fderivWithin ℝ u.value (Metric.closedBall (0 : ℂ) 1) w w) *
            u.value w) := by ring
      _ = 0 := by rw [u.diagonal_boundary_flux_zero hw hp, mul_zero]

/-- Boundedness alone gives the value-L2 bound; derivative energy is not an
input to this argument. -/
theorem value_sq_integrable (hk : 1 ≤ k) :
    IntegrableOn (fun w => ‖u.value w‖ ^ 2) disk := by
  obtain ⟨C, hC⟩ := u.bounded
  have hc : IntegrableOn (fun _ : ℂ => C ^ 2) disk :=
    integrableOn_const measure_ball_lt_top.ne
  refine hc.mono' ((u.smooth.continuousOn.norm.pow 2).aestronglyMeasurable
    measurableSet_disk) ?_
  apply ae_restrict_of_forall_mem measurableSet_disk
  intro w hw
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (hC w (mem_disk_iff.mp hw).le (punctures_notMem_disk hk hw)) 2

/-- Pure boundary data are special cases of the mixed carrier. -/
def ofPure {b : Bool} (v : ClassicalHalfDiskJacobi k b) :
    ClassicalMixedHalfDiskJacobi k b b where
  value := v.value
  smooth := v.smooth
  bounded := v.bounded
  equation := v.equation
  boundary w hw hp := by
    obtain ⟨F, hF, hs, hb⟩ := v.boundary w hw hp
    exact ⟨F, hF, hs, fun _ => hb, fun _ => hb⟩

/-- Equal flags recover the original pure boundary carrier with the same
function and equation; there are no extra degrees of boundary freedom. -/
def toPure {b : Bool} (v : ClassicalMixedHalfDiskJacobi k b b) :
    ClassicalHalfDiskJacobi k b where
  value := v.value
  smooth := v.smooth
  bounded := v.bounded
  equation := v.equation
  boundary w hw hp := by
    obtain ⟨F, hF, hs, h1, h0⟩ := v.boundary w hw hp
    refine ⟨F, hF, hs, ?_⟩
    rcases mem_arc_of_not_puncture hw hp with ha | ha
    · exact h0 ha
    · exact h1 ha

end ClassicalMixedHalfDiskJacobi
end KsIndex.Trace
