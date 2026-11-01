module

public import KsIndexLean.MixedHalfDiskTrace
public import KsIndexLean.VerticalWeakGreen
public import KsIndexLean.WeakCharacterReconstruction
public import KsIndexLean.GeneralDirichletPositivity

@[expose] public section


/-! Classical half-disk Jacobi fields tested against regular functions
supported away from the deleted boundary points. -/
noncomputable section
open Set MeasureTheory Filter Topology Complex
namespace KsIndex.Trace.ClassicalMixedHalfDiskJacobi
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.FaithfulInjection KsIndex.WeakH1
open KsIndex.NullityDecomp
variable {k : ℕ} {b1 b0 : Bool} (u : ClassicalMixedHalfDiskJacobi k b1 b0)

/-- A regular test supported away from punctures makes the Green flux
continuous even if the classical field is not regular at those punctures. -/
lemma test_flux_continuous {G : ℂ → ℂ} (hG : ContDiff ℝ 1 G) {ε : ℝ} (hε : 0 < ε)
    (hGP : ∀ w, ‖w‖ ≤ 1 → (∃ p ∈ punctures k, ‖w-p‖ < ε) → G w = 0) (a : ℂ) :
    ContinuousOn (fun w => (starRingEnd ℂ)
      (fderivWithin ℝ u.value (Metric.closedBall (0 : ℂ) 1) w a) * G w)
      (Metric.closedBall (0 : ℂ) 1) := by
  intro w hw
  have hwn : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
  rcases lt_or_eq_of_le hwn with hi | he
  · have hd : w ∈ Surface.disk := mem_disk_iff.mpr hi
    have heq : (fun z => (starRingEnd ℂ)
        (fderivWithin ℝ u.value (Metric.closedBall (0 : ℂ) 1) z a) * G z) =ᶠ[nhds w]
        (fun z => (starRingEnd ℂ) (fderiv ℝ u.value z a) * G z) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hd] with z hz
      rw [fderivWithin_closedBall_interior (mem_disk_iff.mp hz)]
    have hc := (continuousOn_fderivDir_of_disk u.smooth a).continuousAt
      (Metric.isOpen_ball.mem_nhds hd)
    exact (((Complex.continuous_conj.continuousAt.comp hc).mul hG.continuous.continuousAt).congr
      heq.symm).continuousWithinAt
  · by_cases hp : w ∈ punctures k
    · apply continuousWithinAt_const.congr_of_eventuallyEq
      · filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds w hε),
          self_mem_nhdsWithin] with z hz hzB
        have hz1 : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hzB
        rw [hGP z hz1 ⟨w,hp, by simpa [Metric.mem_ball, dist_eq_norm] using hz⟩, mul_zero]
      · rw [hGP w hwn ⟨w,hp, by simpa using hε⟩, mul_zero]
    · obtain ⟨F,hF,hs,_⟩ := u.boundary w he hp
      exact flux_continuousWithinAt_of_extension he hF hs hG a

/-- The classical equation annihilates a regular Sobolev test supported away
from punctures, with the matching mixed boundary conditions. -/
theorem regular_test_zero (hk : 2 ≤ k) (v : ComplexH1) {G : ℂ → ℂ}
    (hG : ContDiff ℝ 1 G)
    (hv : (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] G)
    (hx : (dxCLM v : ℂ → ℂ) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun w => fderiv ℝ G w 1))
    (hy : (dyCLM v : ℂ → ℂ) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun w => fderiv ℝ G w I))
    {ε : ℝ} (hε : 0 < ε)
    (hGP : ∀ w, ‖w‖ ≤ 1 → (∃ p ∈ punctures k, ‖w-p‖ < ε) → G w = 0)
    (hD1 : b1 = false → ∀ w ∈ arc k 1, G w = 0)
    (hD0 : b0 = false → ∀ w ∈ arc k 0, G w = 0) :
    weakJacobi (surfacePotential k) (u.toH1 hk) v = 0 := by
  have hpot : Integrable (fun w => ((surfacePotential k).V w : ℂ) *
      (starRingEnd ℂ) (u.value w) * G w) (volume.restrict (WeakH1.disk : Set ℂ)) := by
    apply (potential_integrable (surfacePotential k) (u.toH1 hk) v).congr
    filter_upwards [u.toH1_value_ae hk,hv] with w h1 h2
    rw [h1,h2]
  have hgrad : Integrable (KsIndex.GradOrtho.gradInner u.value G)
      (volume.restrict (WeakH1.disk : Set ℂ)) := by
    apply (dirichlet_integrable (u.toH1 hk) v).congr
    filter_upwards [u.toH1_dx_ae hk,u.toH1_dy_ae hk,hx,hy] with w h1 h2 h3 h4
    simp only [KsIndex.GradOrtho.gradInner,h1,h2,h3,h4]
  have hl (w : ℂ) (hw : w ∈ Surface.disk) :
      laplacian u.value w = -((potV k w : ℂ) * u.value w) :=
    eq_neg_of_add_eq_zero_left (u.equation w hw)
  have hpt : ∀ w ∈ Surface.disk,
      KsIndex.GradOrtho.gradInner u.value G w + (starRingEnd ℂ) (laplacian u.value w) * G w =
      KsIndex.GradOrtho.gradInner u.value G w -
        ((surfacePotential k).V w : ℂ) * (starRingEnd ℂ) (u.value w) * G w := by
    intro w hw
    change _ = _ - (potV k w : ℂ) * _ * _
    rw [hl w hw,map_neg,map_mul,Complex.conj_ofReal]
    ring
  have hint : IntegrableOn (fun w => KsIndex.GradOrtho.gradInner u.value G w +
      (starRingEnd ℂ) (laplacian u.value w) * G w) Surface.disk :=
    by
      apply (hgrad.sub hpot).congr
      filter_upwards [ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with w hw
      exact (hpt w hw).symm
  have hgreen := KsIndex.FirstGreen.first_green_disk
    (fun w hw => differentiableAt_fderiv_dir (u.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds hw)) 1)
    (fun w hw => differentiableAt_fderiv_dir (u.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds hw)) I)
    (fun w _ => hG.differentiable (by norm_num) w)
    (u.test_flux_continuous hG hε hGP 1) (u.test_flux_continuous hG hε hGP I) hint
  have hzero : ∀ w : ℂ, ‖w‖ = 1 → (starRingEnd ℂ)
      (fderivWithin ℝ u.value (Metric.closedBall (0 : ℂ) 1) w w) * G w = 0 := by
    intro w hw
    by_cases hp : w ∈ punctures k
    · rw [hGP w hw.le ⟨w,hp,by simpa using hε⟩,mul_zero]
    · obtain ⟨F,hF,hs,h1,h0⟩ := u.boundary w hw hp
      rcases mem_arc_of_not_puncture hw hp with ha | ha
      · cases b0 with
        | false => rw [hD0 rfl w ha, mul_zero]
        | true =>
          have hN : fderiv ℝ F w w = 0 := h0 ha
          rw [fderivWithin_closedBall_of_extension hw hF hs,hN,map_zero,zero_mul]
      · cases b1 with
        | false => rw [hD1 rfl w ha, mul_zero]
        | true =>
          have hN : fderiv ℝ F w w = 0 := h1 ha
          rw [fderivWithin_closedBall_of_extension hw hF hs,hN,map_zero,zero_mul]
  have hcircle : (fun θ : ℝ => (starRingEnd ℂ)
      (fderivWithin ℝ u.value (Metric.closedBall (0 : ℂ) 1)
        (exp ((θ : ℂ)*I)) (exp ((θ : ℂ)*I))) * G (exp ((θ : ℂ)*I))) = fun _ => 0 := by
    funext θ
    exact hzero _ (by simp)
  rw [hcircle,intervalIntegral.integral_zero] at hgreen
  rw [weakJacobi_integral_representatives (surfacePotential k) _ _
    (u.toH1_value_ae hk) hv (u.toH1_dx_ae hk) (u.toH1_dy_ae hk) hx hy]
  calc
    _ = ∫ w in (WeakH1.disk : Set ℂ), KsIndex.GradOrtho.gradInner u.value G w -
        ((surfacePotential k).V w : ℂ) * (starRingEnd ℂ) (u.value w) * G w :=
      (integral_sub hgrad hpot).symm
    _ = ∫ w in Surface.disk, KsIndex.GradOrtho.gradInner u.value G w +
        (starRingEnd ℂ) (laplacian u.value w) * G w :=
      (setIntegral_congr_fun Metric.isOpen_ball.measurableSet hpt).symm
    _ = 0 := hgreen

/-- Every natural-core test with matching mixed boundary conditions is annihilated. -/
theorem natural_core_zero (hk : 2 ≤ k) (ff : KsIndex.SingleDisk.NatCc k b1 b0) :
    weakJacobi (surfacePotential k) (u.toH1 hk) (naturalCoreH1 (by omega) ff) = 0 := by
  obtain ⟨G,hG,he,hv,hx,hy,ht⟩ := sector_core_rep (by omega : 1 ≤ k) ff
  obtain ⟨ε,hε,hP⟩ := ff.property.2.2.2.2
  apply u.regular_test_zero hk (naturalCoreH1 (by omega) ff) hG hv hx hy (half_pos hε)
    (fun w hw hp => C1rep_vanishes_near hε hG.continuous he hP hw hp)
  · intro hb w hw
    have hh := ff.property.2.1
    simp only [hb, KsIndex.SingleDisk.ArcCond] at hh
    obtain ⟨δ,hδ,hh⟩ := hh
    exact C1rep_vanishes_near hδ hG.continuous he hh hw.1.le
      ⟨w, KsIndex.SingleDisk.arc_one_subset_slitC hw, by simpa using half_pos hδ⟩
  · intro hb w hw
    have hh := ff.property.2.2.1
    simp only [hb, KsIndex.SingleDisk.ArcCond] at hh
    obtain ⟨δ,hδ,hh⟩ := hh
    exact C1rep_vanishes_near hδ hG.continuous he hh hw.1.le
      ⟨w, KsIndex.Bracket.arc_zero_subset_slit hw, by simpa using half_pos hδ⟩

/-- Density extends the equation to every test in each mixed-boundary rotation
character, without any character hypothesis on the classical solution. -/
theorem character_tests_zero (hk : 2 ≤ k) (r : ℕ)
    (v : mixedCharacterDomain k r b1 b0) :
    weakJacobi (surfacePotential k) (u.toH1 hk) v = 0 := by
  have hc : Continuous (fun v : mixedCharacterDomain k r b1 b0 =>
      weakJacobi (surfacePotential k) (u.toH1 hk) v) :=
    (continuous_weakJacobi_fixed_left (surfacePotential k) (u.toH1 hk)).comp continuous_subtype_val
  have he := (naturalCharacterToMixed_denseRange (by omega : 1 ≤ k) r b1 b0).equalizer hc
    (continuous_const : Continuous (fun _ : mixedCharacterDomain k r b1 b0 => (0 : ℂ))) (by
      funext f
      exact u.natural_core_zero hk ⟨f.val,f.property.1⟩)
  exact congrFun he v

end KsIndex.Trace.ClassicalMixedHalfDiskJacobi
