module

public import KsIndexLean.GroundStateFlux
public import KsIndexLean.GroundStateDirichlet

@[expose] public section


/-! Continuous Sobolev realization of the flux `g ∂u - (∂g) u`. Bounded
coefficients define maps from complex `H¹` to `L²`; density extends the core
energy bound to the full zero-trace domain. For the positive radial Jacobi
field, zero energy implies that both weak flux components vanish. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.GroundState
open KsIndex.WeakH1 KsIndex.Trace KsIndex.SingleDisk

/-- A continuous real function supplies a bounded multiplier on the disk. -/
lemma exists_bounded_coefficient (a : ℂ → ℝ) (ha : Continuous a) :
    ∃ A : BoundedRealPotential, A.V = a := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    ha.continuousOn
  refine ⟨⟨a, max C 0, le_max_right _ _, ha.aestronglyMeasurable, ?_⟩, rfl⟩
  apply ae_restrict_of_forall_mem disk.isOpen.measurableSet
  intro z hz
  have hb : |a z| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC z (Metric.ball_subset_closedBall hz)
  exact hb.trans (le_max_left _ _)

lemma ofReal_re_of_real {z : ℂ} (hz : (starRingEnd ℂ) z = z) : (z.re : ℂ) = z := by
  have hi := congrArg Complex.im hz
  simp only [Complex.conj_im] at hi
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

/-- The real ground state and both of its derivatives have bounded
multipliers on the closed disk; no inverse ground state is used. -/
lemma exists_ground_coefficients (g : ℂ → ℂ) (hg : ContDiff ℝ 1 g)
    (hr : ∀ z, (starRingEnd ℂ) (g z) = g z) :
    ∃ G Dx Dy : BoundedRealPotential,
      (∀ z, (G.V z : ℂ) = g z) ∧
      (∀ z, (Dx.V z : ℂ) = fderiv ℝ g z 1) ∧
      (∀ z, (Dy.V z : ℂ) = fderiv ℝ g z Complex.I) := by
  obtain ⟨G, hG⟩ := exists_bounded_coefficient (fun z => (g z).re)
    (Complex.continuous_re.comp hg.continuous)
  have hd (d : ℂ) : Continuous (fun z => (fderiv ℝ g z d).re) :=
    Complex.continuous_re.comp
      ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  obtain ⟨Dx, hDx⟩ := exists_bounded_coefficient _ (hd 1)
  obtain ⟨Dy, hDy⟩ := exists_bounded_coefficient _ (hd Complex.I)
  refine ⟨G, Dx, Dy, ?_, ?_, ?_⟩
  · intro z
    rw [hG]
    exact ofReal_re_of_real (hr z)
  · intro z
    rw [hDx]
    exact ofReal_re_of_real (derivative_real (hg.differentiable (by norm_num) z) hr 1)
  · intro z
    rw [hDy]
    exact ofReal_re_of_real
      (derivative_real (hg.differentiable (by norm_num) z) hr Complex.I)

/-- Bounded coefficients make the flux continuous even where the ground
state vanishes on the boundary. -/
def weakFlux (G D : BoundedRealPotential) (T : ComplexH1 →L[ℂ] L2C) :
    ComplexH1 →L[ℂ] L2C :=
  (weightedCLM G).comp T - (weightedCLM D).comp valueCLM

lemma weakFlux_smooth_ae (G D : BoundedRealPotential)
    (T : ComplexH1 →L[ℂ] L2C) (F : SmoothH1Data) (g : ℂ → ℂ) (d : ℂ)
    (hG : ∀ z, (G.V z : ℂ) = g z)
    (hD : ∀ z, (D.V z : ℂ) = fderiv ℝ g z d)
    (hT : T (smoothToH1 F) =ᵐ[volume.restrict (disk : Set ℂ)]
      fun z => fderiv ℝ F.F z d) :
    weakFlux G D T (smoothToH1 F) =ᵐ[volume.restrict (disk : Set ℂ)]
      groundFlux g F.F d := by
  change (weightedLp G (T (smoothToH1 F)) -
    weightedLp D (valueCLM (smoothToH1 F)) : L2C) =ᵐ[_] _
  filter_upwards [Lp.coeFn_sub (weightedLp G (T (smoothToH1 F)))
      (weightedLp D (valueCLM (smoothToH1 F))),
    weightedLp_ae G (T (smoothToH1 F)),
    weightedLp_ae D (valueCLM (smoothToH1 F)),
    smoothToH1_value_ae F, hT] with z hs hg hd hf ht
  simp only [hs, Pi.sub_apply, hg, hd, hf, ht, hG, hD, groundFlux]
  ring

lemma weakFlux_smooth_norm_sq (G D : BoundedRealPotential)
    (T : ComplexH1 →L[ℂ] L2C) (F : SmoothH1Data) (g : ℂ → ℂ) (d : ℂ)
    (hG : ∀ z, (G.V z : ℂ) = g z)
    (hD : ∀ z, (D.V z : ℂ) = fderiv ℝ g z d)
    (hT : T (smoothToH1 F) =ᵐ[volume.restrict (disk : Set ℂ)]
      fun z => fderiv ℝ F.F z d) :
    ‖weakFlux G D T (smoothToH1 F)‖ ^ 2 =
      ∫ z in (disk : Set ℂ), ‖groundFlux g F.F d z‖ ^ 2 := by
  rw [lp_norm_sq]
  apply integral_congr_ae
  filter_upwards [weakFlux_smooth_ae G D T F g d hG hD hT] with z hz
  rw [hz]

/-- Any continuous quadratic flux bound on the smooth Dirichlet core
extends to the entire zero-trace domain. -/
theorem fullDirichlet_flux_bound_of_core (A B : ComplexH1 →L[ℂ] L2C)
    (V : BoundedRealPotential) (M : ℝ)
    (hcore : ∀ f : NatCc 1 false false,
      ‖A (naturalCoreH1 (by decide : 1 ≤ 1) f)‖ ^ 2 +
      ‖B (naturalCoreH1 (by decide : 1 ≤ 1) f)‖ ^ 2 ≤
      M * (weakJacobi V (naturalCoreH1 (by decide : 1 ≤ 1) f)
        (naturalCoreH1 (by decide : 1 ≤ 1) f)).re)
    (u : ComplexH1) (hu : u ∈ zeroTraceDomain Set.univ) :
    ‖A u‖ ^ 2 + ‖B u‖ ^ 2 ≤ M * (weakJacobi V u u).re := by
  let E : Submodule ℂ ComplexH1 := mixedCharacterDomain 1 0 false false
  have hleft : Continuous (fun v : E => ‖A v.val‖ ^ 2 + ‖B v.val‖ ^ 2) :=
    ((A.continuous.comp continuous_subtype_val).norm.pow 2).add
      ((B.continuous.comp continuous_subtype_val).norm.pow 2)
  have hright : Continuous (fun v : E => M * (weakJacobi V v.val v.val).re) :=
    continuous_const.mul (continuous_energy_on V E)
  have hd := naturalCharacterToMixed_denseRange (by decide : 1 ≤ 1) 0 false false
  refine hd.induction_on
    (p := fun v : E => ‖A v.val‖ ^ 2 + ‖B v.val‖ ^ 2 ≤
      M * (weakJacobi V v.val v.val).re)
    (⟨u, zeroTrace_mem_trivial_DD u hu⟩ : E) (isClosed_le hleft hright) ?_
  intro f
  exact hcore ⟨f.val, f.property.1⟩

/-- Extend the ground-state flux estimate to the geometric zero-trace weak
domain by compact-core density. The real `C²` field solves the Jacobi equation,
vanishes on the circle, is nonzero in the open disk, and satisfies `‖g‖² ≤ M`
there. No smooth quotient at the boundary is assumed. -/
theorem fullDirichlet_groundFlux_bound {k : ℕ} (hk : 2 ≤ k)
    (g : ℂ → ℂ) (G Dx Dy : BoundedRealPotential) (M : ℝ)
    (hg : ContDiff ℝ 2 g)
    (hr : ∀ z, (starRingEnd ℂ) (g z) = g z)
    (hb : ∀ z : Circle₁, g z = 0)
    (he : ∀ z ∈ (disk : Set ℂ),
      KsIndex.Surface.laplacian g z + KsIndex.Surface.potV k z * g z = 0)
    (hne : ∀ z ∈ (disk : Set ℂ), g z ≠ 0)
    (hM : ∀ z ∈ (disk : Set ℂ), ‖g z‖ ^ 2 ≤ M)
    (hG : ∀ z, (G.V z : ℂ) = g z)
    (hDx : ∀ z, (Dx.V z : ℂ) = fderiv ℝ g z 1)
    (hDy : ∀ z, (Dy.V z : ℂ) = fderiv ℝ g z Complex.I)
    (u : ComplexH1) (hu : u ∈ zeroTraceDomain Set.univ) :
    ‖weakFlux G Dx dxCLM u‖ ^ 2 + ‖weakFlux G Dy dyCLM u‖ ^ 2 ≤
      M * (weakJacobi (surfacePotential k) u u).re := by
  apply fullDirichlet_flux_bound_of_core _ _ _ M _ u hu
  intro f
  let F := naturalCoreData (by decide : 1 ≤ 1) f
  change ‖weakFlux G Dx dxCLM (smoothToH1 F)‖ ^ 2 +
    ‖weakFlux G Dy dyCLM (smoothToH1 F)‖ ^ 2 ≤
      M * (weakJacobi (surfacePotential k) (smoothToH1 F) (smoothToH1 F)).re
  rw [weakFlux_smooth_norm_sq G Dx dxCLM F g 1 hG hDx (smoothToH1_dx_ae F),
    weakFlux_smooth_norm_sq G Dy dyCLM F g Complex.I hG hDy (smoothToH1_dy_ae F),
    smooth_weakJacobi_self_eq_Qd hk, Complex.ofReal_re]
  have hf : ContDiff ℝ 1 F.F := (dd_contDiff f.property).of_le (by simp)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hi (a : ℂ → ℝ) (ha : Continuous a) : IntegrableOn a (disk : Set ℂ) :=
    (ha.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set
      Metric.ball_subset_closedBall
  rw [← integral_add
    (hi (fun z => ‖groundFlux g F.F 1 z‖ ^ 2)
      ((continuous_groundFlux hg1 hf 1).norm.pow 2))
    (hi (fun z => ‖groundFlux g F.F Complex.I z‖ ^ 2)
      ((continuous_groundFlux hg1 hf Complex.I).norm.pow 2))]
  have h := groundFlux_test_bound g F.F (KsIndex.Surface.potV k) M hg hf hr hb he hM
    (fun z hz => hne z (dd_tsupport_subset_disk f.property hz))
  rw [integral_sub (hi _ (KsIndex.PiAssembly.continuous_gradSq hf))
    (hi _ (KsIndex.PiAssembly.continuous_potVsq hf.continuous))] at h
  change _ ≤ M * (KsIndex.Surface.dirichletG k F.F - KsIndex.Surface.potentialG k F.F)
  rw [KsIndex.Surface.dirichletG_sub_potentialG hk F.F]
  exact h

lemma flux_zero_of_energy_zero (A B : ComplexH1 →L[ℂ] L2C)
    (V : BoundedRealPotential) (M : ℝ) (u : ComplexH1)
    (hbound : ‖A u‖ ^ 2 + ‖B u‖ ^ 2 ≤ M * (weakJacobi V u u).re)
    (hu : (weakJacobi V u u).re = 0) : A u = 0 ∧ B u = 0 := by
  rw [hu, mul_zero] at hbound
  constructor <;> apply norm_eq_zero.mp <;>
    nlinarith [sq_nonneg ‖A u‖, sq_nonneg ‖B u‖, norm_nonneg (A u), norm_nonneg (B u)]

/-- The actual positive vertical Jacobi field controls the flux of every
zero-trace Sobolev field. In particular its zero-energy space has zero flux. -/
theorem radial_ground_weak_flux {k : ℕ} (hk : 2 ≤ k) :
    ∃ G Dx Dy : BoundedRealPotential,
      (∀ z, (G.V z : ℂ) = KsIndex.JacobiMode.modeU k 0 z) ∧
      (∀ z, (Dx.V z : ℂ) = fderiv ℝ (KsIndex.JacobiMode.modeU k 0) z 1) ∧
      (∀ z, (Dy.V z : ℂ) = fderiv ℝ (KsIndex.JacobiMode.modeU k 0) z Complex.I) ∧
      ∀ u : ComplexH1, u ∈ zeroTraceDomain Set.univ →
        (weakJacobi (surfacePotential k) u u).re = 0 →
        weakFlux G Dx dxCLM u = 0 ∧ weakFlux G Dy dyCLM u = 0 := by
  let g := KsIndex.JacobiMode.modeU k 0
  have hg : ContDiff ℝ 2 g :=
    (KsIndex.ModeDiag.modeU_contDiff (by omega : 1 ≤ k) 0).of_le (by simp)
  have hr : ∀ z, (starRingEnd ℂ) (g z) = g z := by
    intro z
    simp only [g, KsIndex.JacobiMode.modeU, pow_zero, mul_one, Complex.conj_ofReal]
  obtain ⟨G, Dx, Dy, hG, hDx, hDy⟩ := exists_ground_coefficients g
    (hg.of_le (by norm_num)) hr
  refine ⟨G, Dx, Dy, hG, hDx, hDy, ?_⟩
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (hg.continuous.norm.pow 2).continuousOn
  intro u hu he0
  apply flux_zero_of_energy_zero _ _ _ M u _ he0
  apply fullDirichlet_groundFlux_bound hk g G Dx Dy M hg hr _ _ _ _ hG hDx hDy u hu
  · intro z
    change KsIndex.JacobiMode.modeU k 0 z = 0
    rw [KsIndex.JacobiMode.modeU, show ‖(z : ℂ)‖ = 1 by simp,
      KsIndex.Radial.gRad_zero_one hk]
    simp
  · intro z _
    exact modeU_jacobi hk 0 z
  · intro z hz heq
    have hp := radial_ground_positive hk hz
    change 0 < (g z).re at hp
    rw [heq] at hp
    exact (lt_irrefl 0) hp
  · intro z hz
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, abs_norm] using
      hM z (Metric.ball_subset_closedBall hz)

end KsIndex.GroundState
