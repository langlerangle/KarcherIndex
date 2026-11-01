module

public import KsIndexLean.GroundStateWeakFlux
public import KsIndexLean.GroundStateRigidity

@[expose] public section


/-! Interior rigidity from vanishing ground-state flux. No quotient regularity
at the boundary is needed. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.GroundState
open KsIndex.WeakH1

lemma groundFlux_zero_rigid (g f : ℂ → ℂ) (hg : ContDiff ℝ 1 g)
    (hf : ContDiffOn ℝ 1 f (disk : Set ℂ))
    (hne : ∀ z ∈ (disk : Set ℂ), g z ≠ 0)
    (hflux : ∀ z ∈ (disk : Set ℂ),
      groundFlux g f 1 z = 0 ∧ groundFlux g f Complex.I z = 0) :
    ∃ c : ℂ, ∀ z ∈ (disk : Set ℂ), f z = c * g z := by
  let v := fun z => f z / g z
  have hv : ∀ z ∈ (disk : Set ℂ), ContDiffAt ℝ 1 v z := by
    intro z hz
    simpa only [v, div_eq_mul_inv] using
      (hf.contDiffAt (disk.isOpen.mem_nhds hz)).mul
        (hg.contDiffAt.fun_inv (hne z hz))
  have hprod : ∀ z ∈ (disk : Set ℂ), (fun w => g w * v w) =ᶠ[𝓝 z] f := by
    intro z hz
    filter_upwards [disk.isOpen.mem_nhds hz] with w hw
    exact mul_div_cancel₀ (f w) (hne w hw)
  have hd : ∀ z ∈ (disk : Set ℂ), fderiv ℝ v z = 0 := by
    intro z hz
    have hdir (d : ℂ) (hzero : groundFlux g f d z = 0) : fderiv ℝ v z d = 0 := by
      have hp := groundFlux_product (hg.differentiable (by norm_num) z)
        ((hv z hz).differentiableAt (by norm_num)) d
      have heq : groundFlux g (fun w => g w * v w) d z = groundFlux g f d z := by
        unfold groundFlux
        rw [(hprod z hz).fderiv_eq]
        change g z * fderiv ℝ f z d - (g z * v z) * fderiv ℝ g z d = _
        rw [(hprod z hz).eq_of_nhds]
      rw [heq, hzero] at hp
      exact (mul_eq_zero.mp hp.symm).resolve_left (pow_ne_zero 2 (hne z hz))
    apply fderiv_eq_zero_of_gradSq_eq_zero
    simp only [KsIndex.Surface.gradSq, hdir 1 (hflux z hz).1,
      hdir Complex.I (hflux z hz).2, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  obtain ⟨c, hc⟩ := disk.isOpen.exists_is_const_of_fderiv_eq_zero
    (convex_ball (0 : ℂ) 1).isPreconnected
    (fun z hz => ((hv z hz).differentiableAt (by norm_num)).differentiableWithinAt) hd
  refine ⟨c, fun z hz => ?_⟩
  have he : f z / g z = c := hc z hz
  exact (div_eq_iff (hne z hz)).mp he

/-- A smooth interior representative of a zero-energy Dirichlet field is
pointwise a multiple of the positive vertical mode. -/
theorem radial_ground_smooth_kernel {k : ℕ} (hk : 2 ≤ k) (F : SmoothH1Data)
    (hb : smoothToH1 F ∈ KsIndex.Trace.zeroTraceDomain Set.univ)
    (he : (weakJacobi (surfacePotential k) (smoothToH1 F) (smoothToH1 F)).re = 0) :
    ∃ c : ℂ, ∀ z ∈ (disk : Set ℂ), F.F z = c * KsIndex.JacobiMode.modeU k 0 z := by
  obtain ⟨G, Dx, Dy, hG, hDx, hDy, hzero⟩ := radial_ground_weak_flux hk
  have hz := hzero (smoothToH1 F) hb he
  let g := KsIndex.JacobiMode.modeU k 0
  have hg : ContDiff ℝ 1 g :=
    (KsIndex.ModeDiag.modeU_contDiff (by omega : 1 ≤ k) 0).of_le (by simp)
  have hflux (D : BoundedRealPotential) (T : ComplexH1 →L[ℂ] L2C) (d : ℂ)
      (hD : ∀ z, (D.V z : ℂ) = fderiv ℝ g z d)
      (hT : T (smoothToH1 F) =ᵐ[volume.restrict (disk : Set ℂ)]
        fun z => fderiv ℝ F.F z d)
      (h0 : weakFlux G D T (smoothToH1 F) = 0) :
      ∀ z ∈ (disk : Set ℂ), groundFlux g F.F d z = 0 := by
    have ha := weakFlux_smooth_ae G D T F g d hG hD hT
    rw [h0] at ha
    have hae : groundFlux g F.F d =ᵐ[volume.restrict (disk : Set ℂ)] (fun _ => 0) := by
      filter_upwards [ha, Lp.coeFn_zero ℂ 2 (volume.restrict (disk : Set ℂ))] with z he hz
      exact he.symm.trans hz
    have hfd := F.smooth.continuousOn_fderiv_of_isOpen disk.isOpen (by simp)
    have hgd : ContinuousOn (fderiv ℝ g) (disk : Set ℂ) :=
      (hg.continuous_fderiv (by norm_num)).continuousOn
    have hc : ContinuousOn (groundFlux g F.F d) (disk : Set ℂ) :=
      (hg.continuous.continuousOn.mul (hfd.clm_apply continuousOn_const)).sub
        (F.smooth.continuousOn.mul (hgd.clm_apply continuousOn_const))
    exact fun z hz => Measure.eqOn_open_of_ae_eq hae disk.isOpen hc continuousOn_const hz
  apply groundFlux_zero_rigid g F.F hg (F.smooth.of_le (by simp))
  · intro z hz heq
    have hp := radial_ground_positive hk hz
    change 0 < (g z).re at hp
    rw [heq] at hp
    exact (lt_irrefl 0) hp
  · intro z hzd
    exact ⟨hflux Dx dxCLM 1 hDx (smoothToH1_dx_ae F) hz.1 z hzd,
      hflux Dy dyCLM Complex.I hDy (smoothToH1_dy_ae F) hz.2 z hzd⟩

end KsIndex.GroundState
