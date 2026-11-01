module

public import KsIndexLean.ClassicalMixedHalfDiskJacobi

@[expose] public section


/-! The truncated Green identity for bounded classical half-period fields.
Only one-sided boundary germs are used; finite energy is not an input. -/
noncomputable section
open Set MeasureTheory Filter Topology Complex
namespace KsIndex.Trace.ClassicalMixedHalfDiskJacobi
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.PunctureCutoff KsIndex.FaithfulInjection
variable {k : ℕ} {b1 b0 : Bool} (u : ClassicalMixedHalfDiskJacobi k b1 b0)

/-- The cross term is integrable for each positive puncture cutoff. -/
lemma cutoff_cross_integrable (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    IntegrableOn (crossDens k ε u.value) disk := by
  obtain ⟨C, hC⟩ := u.bounded
  exact integrableOn_crossDens_of_disk_germs hk u.smooth (fun _ hw hp => u.disk_germ hw hp)
    h0 h1 (fun w hw => hC w (mem_disk_iff.mp hw).le (punctures_notMem_disk (by omega) hw))

/-- The potential term is integrable independently of the derivative energy. -/
lemma cutoff_potential_integrable (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    IntegrableOn (fun w => potV k w * (cutP k ε w)^(2 : ℕ) * ‖u.value w‖^(2 : ℕ)) disk := by
  obtain ⟨C, hC⟩ := u.bounded
  exact integrableOn_potTestReal_of_disk k u.smooth h0 h1
    (fun w hw => hC w (mem_disk_iff.mp hw).le (punctures_notMem_disk (by omega) hw))

/-- Green's formula tested against the squared puncture cutoff times the field.
Each arc’s Dirichlet or Neumann condition cancels the circle flux. -/
theorem cutoff_green_identity (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ((∫ w in disk, (cutP k ε w)^(2 : ℕ) * gradSq u.value w : ℝ) : ℂ) =
      -(∫ w in disk, crossDens k ε u.value w) +
      ((∫ w in disk, potV k w * (cutP k ε w)^(2 : ℕ) * ‖u.value w‖^(2 : ℕ) : ℝ) : ℂ) := by
  have he := (u.cutoff_energy_integrable hk h0 h1).ofReal (𝕜 := ℂ)
  have hc := u.cutoff_cross_integrable hk h0 h1
  have hp := (u.cutoff_potential_integrable hk h0 h1).ofReal (𝕜 := ℂ)
  let G := fun w => KsIndex.GradOrtho.gradInner u.value
    (fun z => ((cutP k ε z)^(2 : ℕ) : ℂ) * u.value z) w +
    (starRingEnd ℂ) (laplacian u.value w) * (((cutP k ε w)^(2 : ℕ) : ℂ) * u.value w)
  have hpt : ∀ w ∈ disk, G w = (((cutP k ε w)^(2 : ℕ) * gradSq u.value w : ℝ) : ℂ) +
      crossDens k ε u.value w - ((potV k w * (cutP k ε w)^(2 : ℕ) * ‖u.value w‖^(2 : ℕ) : ℝ) : ℂ) := by
    intro w hw
    have hd := (u.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt (by simp)
    have hl : laplacian u.value w = -(potV k w : ℂ) * u.value w := by
      have := u.equation w hw
      linear_combination this
    have hn : (starRingEnd ℂ) (u.value w) * u.value w = (‖u.value w‖ : ℂ)^(2 : ℕ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    dsimp only [G]
    rw [gradInner_testV_expand (m := 1) (u := fun _ => u.value) h0 h1 0 hd, hl]
    simp only [crossDens, map_mul, map_neg, Complex.conj_ofReal]
    push_cast
    linear_combination -((potV k w : ℂ) * ((cutP k ε w)^(2 : ℕ) : ℂ)) * hn
  have hint : IntegrableOn G disk := ((he.add hc).sub hp).congr_fun
    (fun w hw => (hpt w hw).symm) measurableSet_disk
  have hf (e : ℂ) := continuousOn_flux_of_disk_germs (by omega : 1 ≤ k) u.smooth
    (fun w hw hp => by obtain ⟨F,hF,hs,_⟩ := u.boundary w hw hp; exact ⟨F,hF,hs⟩) e h0 h1
  have hgreen := KsIndex.FirstGreen.first_green_disk
    (fun w hw => differentiableAt_fderiv_dir (u.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds hw)) 1)
    (fun w hw => differentiableAt_fderiv_dir (u.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds hw)) I)
    (fun w hw => (differentiableAt_cutPSqC k h0 h1 w).mul
      ((u.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt (by simp)))
    (hf 1) (hf I) hint
  have hz : (∫ θ in (-Real.pi : ℝ)..Real.pi,
      (starRingEnd ℂ) (fderivWithin ℝ u.value (Metric.closedBall 0 1)
        (exp ((θ : ℂ)*I)) (exp ((θ : ℂ)*I))) *
      (((cutP k ε (exp ((θ : ℂ)*I)))^(2 : ℕ) : ℂ) * u.value (exp ((θ : ℂ)*I)))) = 0 := by
    have hzero : ∀ θ : ℝ, (starRingEnd ℂ) (fderivWithin ℝ u.value (Metric.closedBall 0 1)
        (exp ((θ : ℂ)*I)) (exp ((θ : ℂ)*I))) *
      (((cutP k ε (exp ((θ : ℂ)*I)))^(2 : ℕ) : ℂ) * u.value (exp ((θ : ℂ)*I))) = 0 := by
      intro θ
      apply u.cutoff_boundary_flux_zero (by omega) h0 h1
      simp
    simp_rw [hzero]
    simp
  simp only [Pi.mul_apply] at hgreen
  rw [hz] at hgreen
  change (∫ w in disk, G w) = 0 at hgreen
  have hsum : IntegrableOn (fun w => (((cutP k ε w)^(2 : ℕ) * gradSq u.value w : ℝ) : ℂ) +
      crossDens k ε u.value w) disk := he.add hc
  have hdecomp : (∫ w in disk, G w) =
      ((∫ w in disk, (cutP k ε w)^(2 : ℕ) * gradSq u.value w : ℝ) : ℂ) +
      (∫ w in disk, crossDens k ε u.value w) -
      ((∫ w in disk, potV k w * (cutP k ε w)^(2 : ℕ) * ‖u.value w‖^(2 : ℕ) : ℝ) : ℂ) := by
    calc
      _ = ∫ w in disk, (((cutP k ε w)^(2 : ℕ) * gradSq u.value w : ℝ) : ℂ) +
          crossDens k ε u.value w - ((potV k w * (cutP k ε w)^(2 : ℕ) * ‖u.value w‖^(2 : ℕ) : ℝ) : ℂ) :=
        setIntegral_congr_fun measurableSet_disk hpt
      _ = (∫ w in disk, (((cutP k ε w)^(2 : ℕ) * gradSq u.value w : ℝ) : ℂ) +
          crossDens k ε u.value w) -
          ∫ w in disk, ((potV k w * (cutP k ε w)^(2 : ℕ) * ‖u.value w‖^(2 : ℕ) : ℝ) : ℂ) :=
        integral_sub hsum hp
      _ = _ := by
        apply congrArg₂ (fun (x y : ℂ) => x - y)
        · calc
            _ = (∫ w in disk, (((cutP k ε w)^(2 : ℕ) * gradSq u.value w : ℝ) : ℂ)) +
                ∫ w in disk, crossDens k ε u.value w := integral_add he hc
            _ = _ := congrArg (· + ∫ w in disk, crossDens k ε u.value w) integral_ofReal
        · exact integral_ofReal
  rw [hdecomp] at hgreen
  linear_combination hgreen

end KsIndex.Trace.ClassicalMixedHalfDiskJacobi
