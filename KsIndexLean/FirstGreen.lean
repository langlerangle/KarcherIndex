module

/-
The disk divergence theorem and first-Green identity.

For a Cartesian flux `(Fx, Fy) : ℂ → ℂ` continuous up to the closed unit disk and differentiable
on its interior, with integrable polar pullback of the divergence as specified
by `disk_divergence`, the disk identity reads
    `∫_disk (∂_x Fx + ∂_y Fy)  =  ∫_{-π}^{π} (cos θ · Fx + sin θ · Fy)(e^{iθ}) dθ`
(the right side is the outward normal flux across the unit circle, `ds = dθ`).  The proof is the
`P,Q` polar flux transformation: with `z = r e^{iθ}`,
    `P(r,θ) = r (cos θ · Fx z + sin θ · Fy z)`,   `Q(r,θ) = −sin θ · Fx z + cos θ · Fy z`,
one has `∂_r P + ∂_θ Q = r · (∂_x Fx + ∂_y Fy)(z)` EXACTLY — no `1/r`, no singular polar Laplacian.
Feeding this to Mathlib's rectangle divergence theorem on `[0,1] × [−π,π]`
(`integral2_divergence_prod_of_hasFDerivAt`) and converting the area side with the polar
change of variables (`integral_comp_polarCoord_symm`) gives the disk identity: the `r = 1` edge is
the flux, the `r = 0` edge dies by the `r`-factor (`P(0,θ) = 0`), and the `θ = ±π` edges cancel by
periodicity.  Substituting `Fx = conj(∂_x u)·v`, `Fy = conj(∂_y u)·v` yields the jacobiB-matched
first-Green identity `∫_D gradInner u v + ∫_D conj(Δu)·v = ∫ conj(∂_ν u)·v` used for the finite-energy and weak-equation arguments.

-/
public import KsIndexLean.PolarGrad
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section


noncomputable section

open Complex Real MeasureTheory Topology

namespace KsIndex.FirstGreen

/-! ### The trig collapse identities

The algebraic heart of `∂_r P + ∂_θ Q = r · div F`: after the product/chain rule the two
directional-derivative coefficients collapse to `1` and `I` respectively, via
`e^{iθ} · conj(e^{iθ}) = |e^{iθ}|² = 1`. -/

/-- `cos θ · e^{iθ} − sin θ · (I · e^{iθ}) = 1`.  (The `∂_x`-coefficient in the divergence
collapse: `e^{iθ}(cos θ − I sin θ) = e^{iθ} e^{−iθ} = 1`.) -/
lemma cos_expθ_sub_sin_I_expθ (θ : ℝ) :
    (Real.cos θ : ℂ) * Complex.exp (↑θ * Complex.I)
      - (Real.sin θ : ℂ) * (Complex.I * Complex.exp (↑θ * Complex.I)) = 1 := by
  have he : Complex.exp (↑θ * Complex.I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hp : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.cos_sq_add_sin_sq,
      Complex.ofReal_one]
  rw [he]
  linear_combination hp - (Real.sin θ : ℂ) ^ 2 * Complex.I_sq

/-- `sin θ · e^{iθ} + cos θ · (I · e^{iθ}) = I`.  (The `∂_y`-coefficient in the divergence
collapse: `e^{iθ}(sin θ + I cos θ) = I e^{iθ} e^{−iθ} = I`.) -/
lemma sin_expθ_add_cos_I_expθ (θ : ℝ) :
    (Real.sin θ : ℂ) * Complex.exp (↑θ * Complex.I)
      + (Real.cos θ : ℂ) * (Complex.I * Complex.exp (↑θ * Complex.I)) = Complex.I := by
  have he : Complex.exp (↑θ * Complex.I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hp : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.cos_sq_add_sin_sq,
      Complex.ofReal_one]
  rw [he]
  linear_combination (Real.sin θ : ℂ) * (Real.cos θ : ℂ) * Complex.I_sq + Complex.I * hp

/-! ### The polar map and its derivative -/

/-- The polar map `(r,θ) ↦ r e^{iθ}` as a map `ℝ² → ℂ`. -/
def polarZ (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)

/-- The `HasFDerivAt` witness for the polar map (via the product/`cexp` chain rule). -/
lemma hasFDerivAt_polarZ (r θ : ℝ) :
    HasFDerivAt polarZ (fderiv ℝ polarZ (r, θ)) (r, θ) := by
  have hf : HasFDerivAt (fun p : ℝ × ℝ => (p.1 : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) (r, θ) :=
    (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)).hasFDerivAt
  have hs : HasFDerivAt (fun p : ℝ × ℝ => (p.2 : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) (r, θ) :=
    (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)).hasFDerivAt
  have hg : HasFDerivAt (fun p : ℝ × ℝ => Complex.exp ((p.2 : ℂ) * Complex.I)) _ (r, θ) :=
    (hs.mul_const Complex.I).cexp
  exact (hf.mul hg : HasFDerivAt polarZ _ (r, θ)).differentiableAt.hasFDerivAt

/-- The derivative of the polar map, evaluated on a direction: `∂_r (r e^{iθ}) = e^{iθ}` (direction
`(1,0)`) and `∂_θ (r e^{iθ}) = i r e^{iθ}` (direction `(0,1)`). -/
lemma fderiv_polarZ_apply (r θ : ℝ) (v : ℝ × ℝ) :
    fderiv ℝ polarZ (r, θ) v
      = (v.1 : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
        + (v.2 : ℂ) * ((r : ℂ) * (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) := by
  have hf : HasFDerivAt (fun p : ℝ × ℝ => (p.1 : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) (r, θ) :=
    (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)).hasFDerivAt
  have hs : HasFDerivAt (fun p : ℝ × ℝ => (p.2 : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) (r, θ) :=
    (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)).hasFDerivAt
  have hg : HasFDerivAt (fun p : ℝ × ℝ => Complex.exp ((p.2 : ℂ) * Complex.I)) _ (r, θ) :=
    (hs.mul_const Complex.I).cexp
  have hfd : fderiv ℝ polarZ (r, θ) = _ := (hf.mul hg).fderiv
  rw [hfd]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Complex.ofRealCLM_apply,
    smul_eq_mul]
  ring

/-- `polarZ` is smooth everywhere; `fun_prop`-visible for flux differentiability. -/
@[fun_prop]
lemma differentiable_polarZ : Differentiable ℝ polarZ := by
  unfold polarZ; fun_prop

/-! ### The P,Q flux transformation

For a Cartesian flux `(Fx, Fy)`, `fluxP` and `fluxQ` are the radial-weighted and angular flux
components in polar coordinates: `∂_r (fluxP) + ∂_θ (fluxQ) = r · (∂_x Fx + ∂_y Fy)` at `r e^{iθ}`,
the divergence collapse with no `1/r`. -/

/-- The radial-weighted flux `P(r,θ) = r (cos θ · Fx + sin θ · Fy)` at `z = r e^{iθ}`. -/
def fluxP (Fx Fy : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) * ((Real.cos p.2 : ℂ) * Fx (polarZ p) + (Real.sin p.2 : ℂ) * Fy (polarZ p))

/-- The angular flux `Q(r,θ) = −sin θ · Fx + cos θ · Fy` at `z = r e^{iθ}`. -/
def fluxQ (Fx Fy : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  -(Real.sin p.2 : ℂ) * Fx (polarZ p) + (Real.cos p.2 : ℂ) * Fy (polarZ p)

lemma differentiableAt_fluxP {Fx Fy : ℂ → ℂ} {r θ : ℝ}
    (hFx : DifferentiableAt ℝ Fx (polarZ (r, θ))) (hFy : DifferentiableAt ℝ Fy (polarZ (r, θ))) :
    DifferentiableAt ℝ (fluxP Fx Fy) (r, θ) := by
  unfold fluxP
  fun_prop (disch := assumption)

lemma differentiableAt_fluxQ {Fx Fy : ℂ → ℂ} {r θ : ℝ}
    (hFx : DifferentiableAt ℝ Fx (polarZ (r, θ))) (hFy : DifferentiableAt ℝ Fy (polarZ (r, θ))) :
    DifferentiableAt ℝ (fluxQ Fx Fy) (r, θ) := by
  unfold fluxQ
  fun_prop (disch := assumption)

/-- **The polar flux divergence identity** (Astra's P,Q transform, no `1/r`):
`∂_r (fluxP) + ∂_θ (fluxQ) = r · (∂_x Fx + ∂_y Fy)` at `z = r e^{iθ}`.  The zeroth-order terms
cancel and the directional-derivative coefficients collapse to `1` and `I` via the trig identities
and the `ℝ`-linearity of `fderiv Fx z` / `fderiv Fy z`. -/
lemma fluxPQ_divergence {Fx Fy : ℂ → ℂ} {r θ : ℝ}
    (hFx : DifferentiableAt ℝ Fx (polarZ (r, θ))) (hFy : DifferentiableAt ℝ Fy (polarZ (r, θ))) :
    fderiv ℝ (fluxP Fx Fy) (r, θ) (1, 0) + fderiv ℝ (fluxQ Fx Fy) (r, θ) (0, 1)
      = (r : ℂ) * (fderiv ℝ Fx (polarZ (r, θ)) 1 + fderiv ℝ Fy (polarZ (r, θ)) Complex.I) := by
  set eiθ := Complex.exp ((θ : ℂ) * Complex.I) with heiθ
  -- polar-map slice derivatives
  have hwr : HasDerivAt (fun s : ℝ => polarZ (s, θ)) eiθ r := by
    simpa [polarZ, one_mul] using (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const eiθ
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) (eiθ * Complex.I) θ := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I
    simpa [heiθ] using h1.cexp
  have hwθ : HasDerivAt (fun t : ℝ => polarZ (r, t)) ((r : ℂ) * (eiθ * Complex.I)) θ := by
    simpa [polarZ] using hexp.const_mul (r : ℂ)
  -- composition slice derivatives of Fx, Fy
  have hFxr := hFx.hasFDerivAt.comp_hasDerivAt r hwr
  have hFyr := hFy.hasFDerivAt.comp_hasDerivAt r hwr
  have hFxθ := hFx.hasFDerivAt.comp_hasDerivAt θ hwθ
  have hFyθ := hFy.hasFDerivAt.comp_hasDerivAt θ hwθ
  have hcosθ : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) (-(Real.sin θ : ℂ)) θ := by
    simpa using (Real.hasDerivAt_cos θ).ofReal_comp
  have hsinθ : HasDerivAt (fun t : ℝ => (Real.sin t : ℂ)) (Real.cos θ : ℂ) θ := by
    simpa using (Real.hasDerivAt_sin θ).ofReal_comp
  -- the slice derivatives, with the function pinned to the `fluxP`/`fluxQ` restriction (defeq to
  -- the combinator's function) so uniqueness against the 2D restriction applies
  have hslP : HasDerivAt (fun s : ℝ => fluxP Fx Fy (s, θ))
      (1 * ((Real.cos θ : ℂ) * Fx (polarZ (r, θ)) + (Real.sin θ : ℂ) * Fy (polarZ (r, θ)))
        + (r : ℂ) * ((Real.cos θ : ℂ) * fderiv ℝ Fx (polarZ (r, θ)) eiθ
            + (Real.sin θ : ℂ) * fderiv ℝ Fy (polarZ (r, θ)) eiθ)) r :=
    (Complex.ofRealCLM.hasDerivAt (x := r)).mul
      ((hFxr.const_mul (Real.cos θ : ℂ)).add (hFyr.const_mul (Real.sin θ : ℂ)))
  have hslQ : HasDerivAt (fun t : ℝ => fluxQ Fx Fy (r, t))
      ((-(Real.cos θ : ℂ) * Fx (polarZ (r, θ))
          + -(Real.sin θ : ℂ) * fderiv ℝ Fx (polarZ (r, θ)) ((r : ℂ) * (eiθ * Complex.I)))
        + (-(Real.sin θ : ℂ) * Fy (polarZ (r, θ))
            + (Real.cos θ : ℂ) * fderiv ℝ Fy (polarZ (r, θ)) ((r : ℂ) * (eiθ * Complex.I)))) θ :=
    (hsinθ.neg.mul hFxθ).add (hcosθ.mul hFyθ)
  -- connect the slice derivatives to the 2D directional derivatives via uniqueness
  have hinj_r : HasDerivAt (fun s : ℝ => (s, θ)) ((1 : ℝ), (0 : ℝ)) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r θ)
  have hinj_θ : HasDerivAt (fun t : ℝ => (r, t)) ((0 : ℝ), (1 : ℝ)) θ :=
    (hasDerivAt_const θ r).prodMk (hasDerivAt_id θ)
  have hcP := ((differentiableAt_fluxP hFx hFy).hasFDerivAt).comp_hasDerivAt r hinj_r
  have hcQ := ((differentiableAt_fluxQ hFx hFy).hasFDerivAt).comp_hasDerivAt θ hinj_θ
  simp only [Function.comp_def] at hcP hcQ
  have hP := hcP.unique hslP
  have hQ := hcQ.unique hslQ
  rw [hP, hQ]
  -- pull the real `r` out of the ℝ-linear derivatives, and collapse the trig coefficients
  have hx : fderiv ℝ Fx (polarZ (r, θ)) ((r : ℂ) * (eiθ * Complex.I))
      = (r : ℂ) * fderiv ℝ Fx (polarZ (r, θ)) (eiθ * Complex.I) := by
    rw [← Complex.real_smul, map_smul, Complex.real_smul]
  have hy : fderiv ℝ Fy (polarZ (r, θ)) ((r : ℂ) * (eiθ * Complex.I))
      = (r : ℂ) * fderiv ℝ Fy (polarZ (r, θ)) (eiθ * Complex.I) := by
    rw [← Complex.real_smul, map_smul, Complex.real_smul]
  have hcx : (Real.cos θ : ℂ) * fderiv ℝ Fx (polarZ (r, θ)) eiθ
      - (Real.sin θ : ℂ) * fderiv ℝ Fx (polarZ (r, θ)) (eiθ * Complex.I)
      = fderiv ℝ Fx (polarZ (r, θ)) 1 := by
    rw [← Complex.real_smul, ← Complex.real_smul, ← map_smul, ← map_smul, ← map_sub]
    congr 1
    rw [Complex.real_smul, Complex.real_smul, mul_comm eiθ Complex.I, heiθ]
    exact cos_expθ_sub_sin_I_expθ θ
  have hcy : (Real.sin θ : ℂ) * fderiv ℝ Fy (polarZ (r, θ)) eiθ
      + (Real.cos θ : ℂ) * fderiv ℝ Fy (polarZ (r, θ)) (eiθ * Complex.I)
      = fderiv ℝ Fy (polarZ (r, θ)) Complex.I := by
    rw [← Complex.real_smul, ← Complex.real_smul, ← map_smul, ← map_smul, ← map_add]
    congr 1
    rw [Complex.real_smul, Complex.real_smul, mul_comm eiθ Complex.I, heiθ]
    exact sin_expθ_add_cos_I_expθ θ
  rw [hx, hy, ← hcx, ← hcy]
  ring

/-! ### The disk polar reduction

The area side of the divergence theorem: `∫_{|w|<1} G = ∫₀¹∫_{-π}^{π} r · G(r e^{iθ})`, the ℂ-valued
analogue of `KsIndex.BallPolar.setIntegral_ball_polar` kept on `(-π,π)` (no `2π` periodicity shift),
so it lands directly on the rectangle the divergence theorem uses.  Proof: the polar change of
variables on the ball indicator, restrict the target to `r < 1`, Fubini. -/

/-- The polar map `polarZ` agrees with Mathlib's `Complex.polarCoord.symm`. -/
lemma polarZ_eq_polarCoordSymm (p : ℝ × ℝ) : polarZ p = Complex.polarCoord.symm p := by
  rw [Complex.polarCoord_symm_apply, polarZ, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

/-- **Polar reduction over the unit disk** (ℂ-valued, angle range `(-π,π)`).  For `G : ℂ → ℂ`
whose polar pullback `r • G(r e^{iθ})` is integrable on `(0,1) × (-π,π)`,
`∫_{|w|<1} G = ∫₀¹∫_{-π}^{π} r · G(r e^{iθ}) dθ dr`. -/
theorem disk_polar_reduction {G : ℂ → ℂ}
    (hPI : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℝ) • G (polarZ p))
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π)) :
    ∫ w in Metric.ball (0 : ℂ) 1, G w
      = ∫ r in (0 : ℝ)..1, ∫ θ in (-π : ℝ)..π, (r : ℂ) * G (polarZ (r, θ)) := by
  set g : ℝ × ℝ → ℂ := fun p => (p.1 : ℝ) • G (polarZ p) with hg
  -- Polar change of variables applied to the indicator of the unit ball.
  have h1 : ∫ w in Metric.ball (0 : ℂ) 1, G w
      = ∫ p in polarCoord.target,
          p.1 • (Metric.ball (0 : ℂ) 1).indicator G (Complex.polarCoord.symm p) := by
    rw [Complex.integral_comp_polarCoord_symm, MeasureTheory.integral_indicator measurableSet_ball]
  have hsub : Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π ⊆ polarCoord.target := by
    rw [polarCoord_target]
    exact Set.prod_mono (fun x hx => hx.1) (fun x hx => hx)
  have hmt : MeasurableSet polarCoord.target := by
    rw [polarCoord_target]; exact measurableSet_Ioi.prod measurableSet_Ioo
  have hnorm : ∀ p : ℝ × ℝ, 0 < p.1 → ‖Complex.polarCoord.symm p‖ = p.1 := by
    intro p hp; rw [Complex.norm_polarCoord_symm]; exact abs_of_pos hp
  -- The indicator restricts the target down to `Ioo 0 1 ×ˢ Ioo (-π) π`.
  have h2 : ∫ p in polarCoord.target,
          p.1 • (Metric.ball (0 : ℂ) 1).indicator G (Complex.polarCoord.symm p)
      = ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π, g p := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmt hsub ?_]
    · apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      intro p hp
      have hp1 : 0 < p.1 := hp.1.1
      have hmem : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) 1 := by
        simp only [Metric.mem_ball, dist_zero_right, hnorm p hp1]; exact hp.1.2
      change p.1 • (Metric.ball (0 : ℂ) 1).indicator G (Complex.polarCoord.symm p) = g p
      rw [Set.indicator_of_mem hmem, ← polarZ_eq_polarCoordSymm]
    · intro p hp
      obtain ⟨hpt, hps⟩ := hp
      rw [polarCoord_target] at hpt
      have hp1 : 0 < p.1 := hpt.1
      have hnb : Complex.polarCoord.symm p ∉ Metric.ball (0 : ℂ) 1 := by
        simp only [Metric.mem_ball, dist_zero_right, hnorm p hp1, not_lt]
        by_contra h
        exact hps ⟨⟨hp1, not_le.mp h⟩, hpt.2⟩
      rw [Set.indicator_of_notMem hnb]; simp
  -- Fubini on the product set, then interval-integral / smul bookkeeping.
  have h3 : ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π, g p
      = ∫ r in Set.Ioo (0 : ℝ) 1, ∫ θ in Set.Ioo (-π) π, g (r, θ) :=
    setIntegral_prod g hPI
  rw [h1, h2, h3, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo (fun r _ => ?_)
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  simp only [hg, Complex.real_smul]

/-! ### The disk divergence identity (the engine)

`∫_{|w|<1} (∂_x Fx + ∂_y Fy) = ∫_{-π}^{π} (cos θ · Fx + sin θ · Fy)(e^{iθ}) dθ`.  Assembles
`disk_polar_reduction` (area side), `fluxPQ_divergence` (pointwise), and Mathlib's rectangle
divergence theorem `integral2_divergence_prod_of_hasFDerivAt`.  Boundary evaluation: the `r = 0`
edge dies by the `r`-factor, the `θ = ±π` edges cancel by periodicity, and the `r = 1` edge is the
flux. The hypotheses require `Fx,Fy` continuous up to the closed disk,
differentiable on its interior, divergence integrable (here in the polar pullback form `hPI`, which
the consumer produces from disk integrability). -/
theorem disk_divergence {Fx Fy : ℂ → ℂ}
    (hFxc : ContinuousOn Fx (Metric.closedBall 0 1))
    (hFyc : ContinuousOn Fy (Metric.closedBall 0 1))
    (hFxd : ∀ w ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℝ Fx w)
    (hFyd : ∀ w ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℝ Fy w)
    (hPI : IntegrableOn (fun p : ℝ × ℝ =>
        (p.1 : ℝ) • (fderiv ℝ Fx (polarZ p) 1 + fderiv ℝ Fy (polarZ p) Complex.I))
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π)) :
    ∫ w in Metric.ball (0 : ℂ) 1, (fderiv ℝ Fx w 1 + fderiv ℝ Fy w Complex.I)
      = ∫ θ in (-π : ℝ)..π,
          ((Real.cos θ : ℂ) * Fx (Complex.exp ((θ : ℂ) * Complex.I))
            + (Real.sin θ : ℂ) * Fy (Complex.exp ((θ : ℂ) * Complex.I))) := by
  have hpi_le : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  -- a null set of radii to discard (`r = 1`, where the divergence identity may fail on the circle)
  have hne1 : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ 1 := by
    rw [ae_iff]
    have hset : {a : ℝ | ¬ a ≠ 1} = {1} := by ext r; simp
    rw [hset]; exact measure_singleton 1
  -- `polarZ` maps the closed rectangle into the closed disk
  have hpolarZc : Continuous polarZ := differentiable_polarZ.continuous
  have hmapsC : Set.MapsTo polarZ (Set.uIcc (0 : ℝ) 1 ×ˢ Set.uIcc (-π) π)
      (Metric.closedBall 0 1) := by
    intro p hp
    rw [Metric.mem_closedBall, dist_zero_right, polarZ_eq_polarCoordSymm,
      Complex.norm_polarCoord_symm]
    have hp1 : p.1 ∈ Set.Icc (0 : ℝ) 1 := by rw [← Set.uIcc_of_le zero_le_one]; exact hp.1
    rw [abs_of_nonneg hp1.1]; exact hp1.2
  have hFxpc : ContinuousOn (fun p : ℝ × ℝ => Fx (polarZ p))
      (Set.uIcc (0 : ℝ) 1 ×ˢ Set.uIcc (-π) π) := hFxc.comp hpolarZc.continuousOn hmapsC
  have hFypc : ContinuousOn (fun p : ℝ × ℝ => Fy (polarZ p))
      (Set.uIcc (0 : ℝ) 1 ×ˢ Set.uIcc (-π) π) := hFyc.comp hpolarZc.continuousOn hmapsC
  have Hcf : ContinuousOn (fluxP Fx Fy) (Set.uIcc (0 : ℝ) 1 ×ˢ Set.uIcc (-π) π) := by
    unfold fluxP
    refine (Complex.continuous_ofReal.comp continuous_fst).continuousOn.mul (ContinuousOn.add ?_ ?_)
    · exact ((Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp continuous_snd)).continuousOn).mul hFxpc
    · exact ((Complex.continuous_ofReal.comp
        (Real.continuous_sin.comp continuous_snd)).continuousOn).mul hFypc
  have Hcg : ContinuousOn (fluxQ Fx Fy) (Set.uIcc (0 : ℝ) 1 ×ˢ Set.uIcc (-π) π) := by
    unfold fluxQ
    refine ContinuousOn.add ?_ ?_
    · exact (((Complex.continuous_ofReal.comp
        (Real.continuous_sin.comp continuous_snd)).neg).continuousOn).mul hFxpc
    · exact ((Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp continuous_snd)).continuousOn).mul hFypc
  -- interior differentiability of the fluxes
  have Hdf : ∀ p ∈ Set.Ioo (min (0 : ℝ) 1) (max 0 1) ×ˢ Set.Ioo (min (-π) π) (max (-π) π),
      HasFDerivAt (fluxP Fx Fy) (fderiv ℝ (fluxP Fx Fy) p) p := by
    intro p hp
    simp only [show min (0 : ℝ) 1 = 0 from min_eq_left zero_le_one,
      show max (0 : ℝ) 1 = 1 from max_eq_right zero_le_one,
      show min (-π : ℝ) π = -π from min_eq_left hpi_le,
      show max (-π : ℝ) π = π from max_eq_right hpi_le] at hp
    have hmem : polarZ p ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, polarZ_eq_polarCoordSymm,
        Complex.norm_polarCoord_symm, abs_of_pos hp.1.1]
      exact hp.1.2
    exact (differentiableAt_fluxP (hFxd _ hmem) (hFyd _ hmem)).hasFDerivAt
  have Hdg : ∀ p ∈ Set.Ioo (min (0 : ℝ) 1) (max 0 1) ×ˢ Set.Ioo (min (-π) π) (max (-π) π),
      HasFDerivAt (fluxQ Fx Fy) (fderiv ℝ (fluxQ Fx Fy) p) p := by
    intro p hp
    simp only [show min (0 : ℝ) 1 = 0 from min_eq_left zero_le_one,
      show max (0 : ℝ) 1 = 1 from max_eq_right zero_le_one,
      show min (-π : ℝ) π = -π from min_eq_left hpi_le,
      show max (-π : ℝ) π = π from max_eq_right hpi_le] at hp
    have hmem : polarZ p ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, polarZ_eq_polarCoordSymm,
        Complex.norm_polarCoord_symm, abs_of_pos hp.1.1]
      exact hp.1.2
    exact (differentiableAt_fluxQ (hFxd _ hmem) (hFyd _ hmem)).hasFDerivAt
  -- the pointwise divergence identity on the open rectangle
  have hdiveq : ∀ p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π,
      fderiv ℝ (fluxP Fx Fy) p (1, 0) + fderiv ℝ (fluxQ Fx Fy) p (0, 1)
        = (p.1 : ℝ) • (fderiv ℝ Fx (polarZ p) 1 + fderiv ℝ Fy (polarZ p) Complex.I) := by
    intro p hp
    obtain ⟨r, θ⟩ := p
    have hmem : polarZ (r, θ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, polarZ_eq_polarCoordSymm,
        Complex.norm_polarCoord_symm, abs_of_pos hp.1.1]
      exact hp.1.2
    rw [fluxPQ_divergence (hFxd _ hmem) (hFyd _ hmem), Complex.real_smul]
  -- integrability of the divergence integrand on the closed rectangle (from `hPI`)
  have hmeas_ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hdiv_int_ioo : IntegrableOn
      (fun x => fderiv ℝ (fluxP Fx Fy) x (1, 0) + fderiv ℝ (fluxQ Fx Fy) x (0, 1))
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π) :=
    hPI.congr_fun (fun p hp => (hdiveq p hp).symm) hmeas_ioo
  have hprod_ae : (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π)
      =ᵐ[volume] (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-π) π) :=
    Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  have Hi : IntegrableOn
      (fun x => fderiv ℝ (fluxP Fx Fy) x (1, 0) + fderiv ℝ (fluxQ Fx Fy) x (0, 1))
      (Set.uIcc (0 : ℝ) 1 ×ˢ Set.uIcc (-π) π) := by
    rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le hpi_le]
    exact hdiv_int_ioo.congr_set_ae hprod_ae.symm
  -- boundary evaluations
  have hpolarZ1 : ∀ y : ℝ, polarZ ((1 : ℝ), y) = Complex.exp ((y : ℂ) * Complex.I) := by
    intro y
    change ((1 : ℝ) : ℂ) * Complex.exp ((y : ℂ) * Complex.I) = Complex.exp ((y : ℂ) * Complex.I)
    rw [Complex.ofReal_one, one_mul]
  have hfluxP1 : ∀ y : ℝ, fluxP Fx Fy (1, y)
      = (Real.cos y : ℂ) * Fx (Complex.exp ((y : ℂ) * Complex.I))
        + (Real.sin y : ℂ) * Fy (Complex.exp ((y : ℂ) * Complex.I)) := by
    intro y
    change ((1 : ℝ) : ℂ) * ((Real.cos y : ℂ) * Fx (polarZ ((1 : ℝ), y))
        + (Real.sin y : ℂ) * Fy (polarZ ((1 : ℝ), y))) = _
    rw [Complex.ofReal_one, one_mul, hpolarZ1 y]
  have e2 : Complex.exp (((-π : ℝ) : ℂ) * Complex.I) = -1 := by
    rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  have hpz : ∀ x : ℝ, polarZ (x, π) = polarZ (x, -π) := by
    intro x
    change (x : ℂ) * Complex.exp ((π : ℂ) * Complex.I)
      = (x : ℂ) * Complex.exp (((-π : ℝ) : ℂ) * Complex.I)
    rw [Complex.exp_pi_mul_I, e2]
  have hfluxQ_eq : ∀ x : ℝ, fluxQ Fx Fy (x, π) = fluxQ Fx Fy (x, -π) := by
    intro x
    change -(Real.sin π : ℂ) * Fx (polarZ (x, π)) + (Real.cos π : ℂ) * Fy (polarZ (x, π))
      = -(Real.sin (-π) : ℂ) * Fx (polarZ (x, -π)) + (Real.cos (-π) : ℂ) * Fy (polarZ (x, -π))
    rw [hpz x]
    simp only [Real.sin_pi, Real.cos_pi, Real.sin_neg, Real.cos_neg, neg_zero]
  have e0 : (∫ y in (-π : ℝ)..π, fluxP Fx Fy (0, y)) = 0 := by
    have h0 : (fun y : ℝ => fluxP Fx Fy (0, y)) = fun _ => (0 : ℂ) := by
      funext y; simp [fluxP]
    rw [h0]; simp
  have eP : (∫ y in (-π : ℝ)..π, fluxP Fx Fy (1, y))
      = ∫ θ in (-π : ℝ)..π,
          ((Real.cos θ : ℂ) * Fx (Complex.exp ((θ : ℂ) * Complex.I))
            + (Real.sin θ : ℂ) * Fy (Complex.exp ((θ : ℂ) * Complex.I))) := by
    apply intervalIntegral.integral_congr; intro y _; exact hfluxP1 y
  have eQ : (∫ x in (0 : ℝ)..1, fluxQ Fx Fy (x, π)) = ∫ x in (0 : ℝ)..1, fluxQ Fx Fy (x, -π) := by
    apply intervalIntegral.integral_congr; intro x _; exact hfluxQ_eq x
  calc ∫ w in Metric.ball (0 : ℂ) 1, (fderiv ℝ Fx w 1 + fderiv ℝ Fy w Complex.I)
      = ∫ r in (0 : ℝ)..1, ∫ θ in (-π : ℝ)..π,
          (r : ℂ) * (fderiv ℝ Fx (polarZ (r, θ)) 1 + fderiv ℝ Fy (polarZ (r, θ)) Complex.I) :=
        disk_polar_reduction (G := fun w => fderiv ℝ Fx w 1 + fderiv ℝ Fy w Complex.I) hPI
    _ = ∫ r in (0 : ℝ)..1, ∫ θ in (-π : ℝ)..π,
          (fderiv ℝ (fluxP Fx Fy) (r, θ) (1, 0) + fderiv ℝ (fluxQ Fx Fy) (r, θ) (0, 1)) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hne1] with r hr1
        intro hr_mem
        rw [Set.uIoc_of_le zero_le_one] at hr_mem
        have hrpos : 0 < r := hr_mem.1
        have hrlt : r < 1 := lt_of_le_of_ne hr_mem.2 hr1
        apply intervalIntegral.integral_congr
        intro θ _
        have hmem : polarZ (r, θ) ∈ Metric.ball (0 : ℂ) 1 := by
          rw [Metric.mem_ball, dist_zero_right, polarZ_eq_polarCoordSymm,
            Complex.norm_polarCoord_symm, abs_of_pos hrpos]
          exact hrlt
        exact (fluxPQ_divergence (hFxd _ hmem) (hFyd _ hmem)).symm
    _ = (((∫ x in (0 : ℝ)..1, fluxQ Fx Fy (x, π)) - ∫ x in (0 : ℝ)..1, fluxQ Fx Fy (x, -π))
          + ∫ y in (-π : ℝ)..π, fluxP Fx Fy (1, y)) - ∫ y in (-π : ℝ)..π, fluxP Fx Fy (0, y) :=
        integral2_divergence_prod_of_hasFDerivAt (fluxP Fx Fy) (fluxQ Fx Fy)
          (fderiv ℝ (fluxP Fx Fy)) (fderiv ℝ (fluxQ Fx Fy)) 0 (-π) 1 π Hcf Hcg Hdf Hdg Hi
    _ = ∫ θ in (-π : ℝ)..π,
          ((Real.cos θ : ℂ) * Fx (Complex.exp ((θ : ℂ) * Complex.I))
            + (Real.sin θ : ℂ) * Fy (Complex.exp ((θ : ℂ) * Complex.I))) := by
        rw [eQ, eP, e0]; ring

/-! ### The consumer converter (disk integrability → polar-pullback `hPI`)

The engine's integrability hypothesis `hPI` is in polar-pullback form, but every integrability fact
the consumers actually hold (`integrableOn_gradInner`, the Cauchy–Schwarz lemmas, O1 step (0)'s
`integrableOn_cutPSq_gradSq`) is stated on the disk `Metric.ball 0 1` in `w`-coordinates.  This
converter bridges the two, via the Jacobian change of variables on the *real* polar coordinate
(`integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`, det `= r`) and the volume-preserving
`ℂ ≃ ℝ²` identification (`Complex.volume_preserving_equiv_real_prod`).  One direction suffices:
disk integrability ⟹ `hPI`. -/

/-- **Disk integrability ⟹ polar-pullback integrability.**  If `G` is integrable on the open unit
disk, then `r • G(r e^{iθ})` is integrable on `(0,1) × (-π,π)` — the hypothesis the engine wants. -/
theorem polar_integrable_of_disk {G : ℂ → ℂ} (hG : IntegrableOn G (Metric.ball (0 : ℂ) 1)) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℝ) • G (polarZ p))
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π) := by
  have hmS : MeasurableSet (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π ⊆ polarCoord.target := by
    rw [polarCoord_target]
    exact Set.prod_mono (fun x hx => hx.1) (fun x hx => hx)
  -- `polarZ = (ℝ²→ℂ identification) ∘ (real polarCoord.symm)`
  have hbridge : ∀ p : ℝ × ℝ,
      polarZ p = Complex.measurableEquivRealProd.symm (polarCoord.symm p) := by
    intro p
    rw [polarZ_eq_polarCoordSymm p, ← Complex.measurableEquivRealProd_symm_polarCoord_symm_apply p]
  -- Stage 1: pull the ℂ-integrability of `G` back to `ℝ²` via the volume-preserving equivalence.
  have hmp : MeasurePreserving (⇑Complex.measurableEquivRealProd.symm)
      (volume : Measure (ℝ × ℝ)) volume :=
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  have himg : (⇑Complex.measurableEquivRealProd.symm) '' (polarCoord.symm '' (Set.Ioo (0 : ℝ) 1 ×ˢ
      Set.Ioo (-π) π)) ⊆ Metric.ball (0 : ℂ) 1 := by
    rintro _ ⟨q, ⟨p, hp, rfl⟩, rfl⟩
    rw [Metric.mem_ball, dist_zero_right, ← hbridge p, polarZ_eq_polarCoordSymm,
      Complex.norm_polarCoord_symm, abs_of_pos hp.1.1]
    exact hp.1.2
  have hg1 : IntegrableOn (G ∘ (⇑Complex.measurableEquivRealProd.symm))
      (polarCoord.symm '' (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π)) := by
    rw [← MeasurePreserving.integrableOn_image hmp
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
    exact hG.mono_set himg
  -- Stage 2: Jacobian change of variables on the real polar coordinate (det `= r`).
  have hf' : ∀ x ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π,
      HasFDerivWithinAt polarCoord.symm (fderivPolarCoordSymm x)
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π) x :=
    fun x _ => (hasFDerivAt_polarCoord_symm x).hasFDerivWithinAt
  have hinj : Set.InjOn polarCoord.symm (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π) :=
    polarCoord.symm.injOn.mono hsub
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hmS hf' hinj
    (G ∘ (⇑Complex.measurableEquivRealProd.symm))] at hg1
  refine hg1.congr_fun (fun x hx => ?_) hmS
  simp only [det_fderivPolarCoordSymm, abs_of_pos hx.1.1, Function.comp_apply, ← hbridge x]

/-! ### First Green identity — the interior divergence decomposition

Substituting the Jacobi product flux `Fx = conj(∂_x u)·v`, `Fy = conj(∂_y u)·v` into the disk
divergence theorem, the interior divergence `∂_x Fx + ∂_y Fy` decomposes (product rule plus the
`ℝ`-linearity of conjugation) as `gradInner u v + conj(Δu)·v`.  This is the pointwise core. -/

/-- The Fréchet derivative of a conjugated function: `fderiv (conj ∘ g) = conj ∘L fderiv g`
(conjugation is `ℝ`-linear).  Repackages `Complex.conjCLE`, matching `SigmaDeriv`'s pattern. -/
lemma hasFDerivAt_conj {g : ℂ → ℂ} {w : ℂ} (hg : DifferentiableAt ℝ g w) :
    HasFDerivAt (fun z => (starRingEnd ℂ) (g z))
      ((Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g w)) w := by
  have hconj : HasFDerivAt (fun z : ℂ => (starRingEnd ℂ) z)
      (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ) (g w) := by
    have hfun : (fun z : ℂ => (starRingEnd ℂ) z) = ⇑Complex.conjCLE := by
      funext z; rw [Complex.conjCLE_apply]
    rw [hfun]; exact Complex.conjCLE.hasFDerivAt
  exact hconj.comp w hg.hasFDerivAt

/-- **First Green pointwise identity.**  For `u` twice-differentiable and `v` differentiable at `w`,
the divergence of the Jacobi product flux decomposes as the gradient cross density plus the
conjugated Laplacian term:
`∂_x(conj(∂_x u)·v) + ∂_y(conj(∂_y u)·v) = gradInner u v + conj(Δu)·v`. -/
lemma first_green_pointwise {u v : ℂ → ℂ} {w : ℂ}
    (hux : DifferentiableAt ℝ (fun z => fderiv ℝ u z 1) w)
    (huy : DifferentiableAt ℝ (fun z => fderiv ℝ u z Complex.I) w)
    (hv : DifferentiableAt ℝ v w) :
    fderiv ℝ (fun z => (starRingEnd ℂ) (fderiv ℝ u z 1) * v z) w 1
      + fderiv ℝ (fun z => (starRingEnd ℂ) (fderiv ℝ u z Complex.I) * v z) w Complex.I
      = KsIndex.GradOrtho.gradInner u v w
        + (starRingEnd ℂ) (KsIndex.Surface.laplacian u w) * v w := by
  have hFx : HasFDerivAt (fun z => (starRingEnd ℂ) (fderiv ℝ u z 1) * v z)
      _ w := (hasFDerivAt_conj hux).mul hv.hasFDerivAt
  have hFy : HasFDerivAt (fun z => (starRingEnd ℂ) (fderiv ℝ u z Complex.I) * v z)
      _ w := (hasFDerivAt_conj huy).mul hv.hasFDerivAt
  rw [hFx.fderiv, hFy.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, smul_eq_mul, KsIndex.GradOrtho.gradInner, KsIndex.Surface.laplacian,
    map_add]
  ring

/-- The `fderivWithin`-based Jacobi flux (using the interior trace derivative
`fderivWithin ℝ u (closedBall 0 1)`, the lemma-3 currency) has the same interior divergence
decomposition, since on the open disk `fderivWithin (closedBall) = fderiv`. -/
lemma first_green_pointwise_within {u v : ℂ → ℂ} {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1)
    (hux : DifferentiableAt ℝ (fun z => fderiv ℝ u z 1) w)
    (huy : DifferentiableAt ℝ (fun z => fderiv ℝ u z Complex.I) w)
    (hv : DifferentiableAt ℝ v w) :
    fderiv ℝ (fun z => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) z 1) * v z) w 1
      + fderiv ℝ
          (fun z => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) z Complex.I) * v z)
          w Complex.I
      = KsIndex.GradOrtho.gradInner u v w
        + (starRingEnd ℂ) (KsIndex.Surface.laplacian u w) * v w := by
  have hwithin : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      fderivWithin ℝ u (Metric.closedBall 0 1) z = fderiv ℝ u z := fun z hz =>
    fderivWithin_of_mem_nhds
      (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall)
  have hex : (fun z => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) z 1) * v z)
      =ᶠ[𝓝 w] (fun z => (starRingEnd ℂ) (fderiv ℝ u z 1) * v z) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz
    rw [hwithin z hz]
  have hey : (fun z => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) z Complex.I) * v z)
      =ᶠ[𝓝 w] (fun z => (starRingEnd ℂ) (fderiv ℝ u z Complex.I) * v z) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz
    rw [hwithin z hz]
  rw [hex.fderiv_eq, hey.fderiv_eq]
  exact first_green_pointwise hux huy hv

/-- **Boundary radial collapse.**  The disk-divergence boundary integrand
`cos θ · (conj(L 1)·V) + sin θ · (conj(L I)·V)` collapses to `conj(L(e^{iθ}))·V`, the radial
(normal) trace: `L` is `ℝ`-linear and `cos θ · 1 + sin θ · I = e^{iθ}`.  With `L` the interior trace
derivative and `V = v(e^{iθ})`, this is the lemma-3 trace currency `conj(∂_ν u)·v`. -/
lemma boundary_radial_collapse (θ : ℝ) (L : ℂ →L[ℝ] ℂ) (V : ℂ) :
    (Real.cos θ : ℂ) * ((starRingEnd ℂ) (L 1) * V)
      + (Real.sin θ : ℂ) * ((starRingEnd ℂ) (L Complex.I) * V)
      = (starRingEnd ℂ) (L (Complex.exp ((θ : ℂ) * Complex.I))) * V := by
  have he : Complex.exp ((θ : ℂ) * Complex.I)
      = (Real.cos θ : ℝ) • (1 : ℂ) + (Real.sin θ : ℝ) • Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.real_smul,
      Complex.real_smul, mul_one]
  rw [he, map_add, map_smul, map_smul]
  simp only [Complex.real_smul, map_add, map_mul, Complex.conj_ofReal]
  ring

/-! ### The first Green identity on the disk (the O1/O2 consumable) -/

/-- **First Green identity on the unit disk.**  For `u` twice-differentiable on the open disk and
continuously-`fderivWithin`-differentiable up to its closure, and `v` differentiable up to the
closure, with the divergence integrable,
`∫_{|w|<1} (gradInner u v + conj(Δu)·v) = ∫_{-π}^{π} conj(∂_ν u)·v` where `∂_ν u` is the outward
radial (normal) trace `fderivWithin ℝ u (closedBall 0 1) (e^{iθ}) (e^{iθ})` (the lemma-3 currency).
Assembles `disk_divergence` with the Jacobi product flux, using `first_green_pointwise_within`
(interior), `polar_integrable_of_disk` (the integrability hypothesis) and `boundary_radial_collapse`
(the trace). -/
theorem first_green_disk {u v : ℂ → ℂ}
    (hu2x : ∀ w ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℝ (fun z => fderiv ℝ u z 1) w)
    (hu2y : ∀ w ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℝ (fun z => fderiv ℝ u z Complex.I) w)
    (hv : ∀ w ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℝ v w)
    (hFxc : ContinuousOn
      (fun w => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) w 1) * v w)
      (Metric.closedBall 0 1))
    (hFyc : ContinuousOn
      (fun w => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) w Complex.I) * v w)
      (Metric.closedBall 0 1))
    (hInt : IntegrableOn (fun w => KsIndex.GradOrtho.gradInner u v w
      + (starRingEnd ℂ) (KsIndex.Surface.laplacian u w) * v w) (Metric.ball 0 1)) :
    ∫ w in Metric.ball (0 : ℂ) 1, (KsIndex.GradOrtho.gradInner u v w
        + (starRingEnd ℂ) (KsIndex.Surface.laplacian u w) * v w)
      = ∫ θ in (-π : ℝ)..π, (starRingEnd ℂ)
          (fderivWithin ℝ u (Metric.closedBall 0 1) (Complex.exp ((θ : ℂ) * Complex.I))
            (Complex.exp ((θ : ℂ) * Complex.I))) * v (Complex.exp ((θ : ℂ) * Complex.I)) := by
  -- pointwise interior divergence identity
  have hdiv_eq : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      fderiv ℝ (fun z => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) z 1) * v z) w 1
        + fderiv ℝ
            (fun z => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) z Complex.I) * v z)
            w Complex.I
        = KsIndex.GradOrtho.gradInner u v w
          + (starRingEnd ℂ) (KsIndex.Surface.laplacian u w) * v w :=
    fun w hw => first_green_pointwise_within hw (hu2x w hw) (hu2y w hw) (hv w hw)
  -- the within-flux agrees with the raw flux near every interior point (differentiability transfer)
  have hgerm : ∀ d : ℂ, ∀ w ∈ Metric.ball (0 : ℂ) 1,
      (fun z => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) z d) * v z)
        =ᶠ[𝓝 w] (fun z => (starRingEnd ℂ) (fderiv ℝ u z d) * v z) := by
    intro d w hw
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz
    rw [fderivWithin_of_mem_nhds
      (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall)]
  have hFxd : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      DifferentiableAt ℝ
        (fun z => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) z 1) * v z) w := by
    intro w hw
    have hraw := ((hasFDerivAt_conj (hu2x w hw)).mul (hv w hw).hasFDerivAt).differentiableAt
    exact hraw.congr_of_eventuallyEq (hgerm 1 w hw)
  have hFyd : ∀ w ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℝ
      (fun z => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) z Complex.I) * v z)
      w := by
    intro w hw
    have hraw := ((hasFDerivAt_conj (hu2y w hw)).mul (hv w hw).hasFDerivAt).differentiableAt
    exact hraw.congr_of_eventuallyEq (hgerm Complex.I w hw)
  -- disk integrability of the divergence (from `hInt` via the pointwise identity)
  have hG : IntegrableOn (fun w =>
      fderiv ℝ (fun z => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) z 1) * v z) w 1
        + fderiv ℝ
            (fun z => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) z Complex.I) * v z)
            w Complex.I) (Metric.ball 0 1) :=
    hInt.congr_fun (fun w hw => (hdiv_eq w hw).symm) measurableSet_ball
  have hdd := disk_divergence hFxc hFyc hFxd hFyd (polar_integrable_of_disk hG)
  calc ∫ w in Metric.ball (0 : ℂ) 1, (KsIndex.GradOrtho.gradInner u v w
          + (starRingEnd ℂ) (KsIndex.Surface.laplacian u w) * v w)
      = ∫ w in Metric.ball (0 : ℂ) 1,
          (fderiv ℝ (fun z => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) z 1) * v z)
              w 1
            + fderiv ℝ
                (fun z => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) z Complex.I)
                  * v z) w Complex.I) :=
        setIntegral_congr_fun measurableSet_ball (fun w hw => (hdiv_eq w hw).symm)
    _ = ∫ θ in (-π : ℝ)..π,
          ((Real.cos θ : ℂ) * ((starRingEnd ℂ)
                (fderivWithin ℝ u (Metric.closedBall 0 1) (Complex.exp ((θ : ℂ) * Complex.I)) 1)
              * v (Complex.exp ((θ : ℂ) * Complex.I)))
            + (Real.sin θ : ℂ) * ((starRingEnd ℂ)
                (fderivWithin ℝ u (Metric.closedBall 0 1) (Complex.exp ((θ : ℂ) * Complex.I))
                  Complex.I) * v (Complex.exp ((θ : ℂ) * Complex.I)))) := hdd
    _ = ∫ θ in (-π : ℝ)..π, (starRingEnd ℂ)
          (fderivWithin ℝ u (Metric.closedBall 0 1) (Complex.exp ((θ : ℂ) * Complex.I))
            (Complex.exp ((θ : ℂ) * Complex.I))) * v (Complex.exp ((θ : ℂ) * Complex.I)) := by
        refine intervalIntegral.integral_congr (fun θ _ => ?_)
        exact boundary_radial_collapse θ
          (fderivWithin ℝ u (Metric.closedBall 0 1) (Complex.exp ((θ : ℂ) * Complex.I)))
          (v (Complex.exp ((θ : ℂ) * Complex.I)))

end KsIndex.FirstGreen
