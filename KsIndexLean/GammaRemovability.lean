module

public import KsIndexLean.PunctureRemoval
public import KsIndexLean.JacobiMode

@[expose] public section


/-!
# Removability of a puncture for smooth fields with square-integrable jets

A `C²` field on a punctured open chart has the weak derivative supplied by
TauCeti's classical-to-weak bridge. Full-chart `L²` bounds on its value and
encoded gradient then give a `W1p` representative across the puncture via
`exists_w1p_of_punctured_jet`.

The encoding `gradEnc f = ∂ₓf + i·∂_yf` matches `W1p.gradient`.
`innerSL_gradEnc` identifies it with the totalized Fréchet derivative at
every point, since both sides are built from `fderiv ℝ f x`.

For a pointwise solution of `Δf + V f = 0`, integration by parts gives the
punctured test identity. If `V` is measurable and bounded on compact subsets,
`isWeakSolOn_of_punctured_tests` extends the weak equation to the full chart.
The final theorem packages this extension and almost-everywhere agreement
of both value and gradient.
-/

noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
namespace KsIndex.PunctureRemoval
open KsIndex.JacobiMode

/-! ### The gradient encoding -/

/-- Complex encoding of the real gradient:
`gradEnc f x = ∂ₓf(x) + i·∂_yf(x)`. -/
def gradEnc (f : ℂ → ℝ) (x : ℂ) : ℂ := ⟨fderiv ℝ f x 1, fderiv ℝ f x Complex.I⟩

@[simp] lemma gradEnc_re (f : ℂ → ℝ) (x : ℂ) :
    (gradEnc f x).re = fderiv ℝ f x 1 := rfl

@[simp] lemma gradEnc_im (f : ℂ → ℝ) (x : ℂ) :
    (gradEnc f x).im = fderiv ℝ f x Complex.I := rfl

/-- The encoded inner-product family equals the totalized Fréchet derivative everywhere. -/
lemma innerSL_gradEnc (f : ℂ → ℝ) (x : ℂ) :
    (innerSL ℝ (gradEnc f x) : ℂ →L[ℝ] ℝ) = fderiv ℝ f x := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  rw [map_add, map_add, map_smul, map_smul, map_smul, map_smul,
    innerSL_one, innerSL_I, gradEnc_re, gradEnc_im]

/-! ### The punctured weak jet -/

/-- **The punctured jet.** A field twice differentiable at every point of the
punctured chart carries the weak jet on the punctured opens, in the
`innerSL` encoding used by `exists_w1p_of_punctured_jet`. -/
lemma hasWeakFDerivOn_punctured_of_contDiffAt {Ω : Opens ℂ} {z₀ : ℂ} {f : ℂ → ℝ}
    (hsm : ∀ x ∈ Ω.carrier \ {z₀}, ContDiffAt ℝ 2 f x) :
    TauCeti.HasWeakFDerivOn (volume : Measure ℂ) (puncturedOpens Ω z₀) f
      (fun x => innerSL ℝ (gradEnc f x)) := by
  have hopen : IsOpen ((puncturedOpens Ω z₀ : Opens ℂ) : Set ℂ) :=
    (puncturedOpens Ω z₀).isOpen
  have hcf : ContinuousOn f ((puncturedOpens Ω z₀ : Opens ℂ) : Set ℂ) :=
    fun x hx => ((hsm x hx).continuousAt).continuousWithinAt
  have hcg : ContinuousOn (fderiv ℝ f) ((puncturedOpens Ω z₀ : Opens ℂ) : Set ℂ) :=
    fun x hx => (((hsm x hx).fderiv_right (m := 1)
      (by norm_num)).continuousAt).continuousWithinAt
  have hdiff : ∀ x ∈ ((puncturedOpens Ω z₀ : Opens ℂ) : Set ℂ),
      DifferentiableAt ℝ f x :=
    fun x hx => (hsm x hx).differentiableAt (by norm_num)
  have hli_f : LocallyIntegrableOn f
      ((puncturedOpens Ω z₀ : Opens ℂ) : Set ℂ) (volume : Measure ℂ) :=
    hcf.locallyIntegrableOn hopen.measurableSet
  have hli_g : LocallyIntegrableOn (fderiv ℝ f)
      ((puncturedOpens Ω z₀ : Opens ℂ) : Set ℂ) (volume : Measure ℂ) :=
    hcg.locallyIntegrableOn hopen.measurableSet
  have h := TauCeti.hasWeakFDerivOn_of_differentiableOn hli_f hli_g hdiff
  have hfe : (fun x => (innerSL ℝ (gradEnc f x) : ℂ →L[ℝ] ℝ)) = fderiv ℝ f := by
    funext x
    exact innerSL_gradEnc f x
  rw [hfe]
  exact h

/-- A `C²` field on the punctured chart with full-chart `L²` value and gradient
data has a `W1p` representative on the full chart with the same jet almost
everywhere. This statement does not require a differential equation. -/
theorem exists_w1p_of_contDiffAt_punctured {Ω : Opens ℂ} {z₀ : ℂ} {f : ℂ → ℝ}
    (hsm : ∀ x ∈ Ω.carrier \ {z₀}, ContDiffAt ℝ 2 f x)
    (hu2 : MemLp f 2 ((volume : Measure ℂ).restrict Ω.carrier))
    (hg2 : MemLp (gradEnc f) 2 ((volume : Measure ℂ).restrict Ω.carrier)) :
    ∃ û : TauCeti.W1p (volume : Measure ℂ) Ω 2,
      (TauCeti.W1p.value û : ℂ → ℝ)
          =ᵐ[(volume : Measure ℂ).restrict Ω.carrier] f
        ∧ (TauCeti.W1p.gradient û : ℂ → ℂ)
            =ᵐ[(volume : Measure ℂ).restrict Ω.carrier] gradEnc f :=
  exists_w1p_of_punctured_jet hu2 hg2 (hasWeakFDerivOn_punctured_of_contDiffAt hsm)


/-! ### The smooth test identity and weak-solution extension -/

/-- The real flat Laplacian (the `ℝ`-valued mirror of `Surface.laplacian`). -/
def lapReal (f : ℂ → ℝ) (x : ℂ) : ℝ :=
  fderiv ℝ (fun z => fderiv ℝ f z 1) x 1
    + fderiv ℝ (fun z => fderiv ℝ f z Complex.I) x Complex.I

/-- A product of a `U`-continuous factor with a globally continuous factor
whose closed support lies inside the open `U` is globally continuous. -/
lemma continuous_mul_of_tsupport_subset {U : Set ℂ} (hU : IsOpen U)
    {a b : ℂ → ℝ} (ha : ContinuousOn a U) (hb : Continuous b)
    (hbs : tsupport b ⊆ U) : Continuous (fun x => a x * b x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact ((ha x hx).continuousAt (hU.mem_nhds hx)).mul hb.continuousAt
  · have hxb : x ∉ tsupport b := fun h => hx (hbs h)
    have hz : (fun x => a x * b x) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hxb] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    exact ContinuousAt.congr continuousAt_const hz.symm


/-- Off the closed support, the derivative vanishes (the test is locally
zero there). -/
lemma fderiv_notMem_tsupport_zero {φ : ℂ → ℝ} {x : ℂ} (h : x ∉ tsupport φ) :
    fderiv ℝ φ x = 0 := by
  have hev : φ =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds h] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [hev.fderiv_eq]
  simp

/-- Integrability of a directional gradient pairing: the `U`-continuous
partial of `f` against the compactly supported partial of the test. -/
lemma integrable_gradPairing {U : Opens ℂ} {f : ℂ → ℝ}
    (hsm : ContDiffOn ℝ 2 f (U : Set ℂ))
    {φ : ℂ → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ (U : Set ℂ)) (e : ℂ) :
    MeasureTheory.Integrable (fun x => fderiv ℝ f x e * fderiv ℝ φ x e)
      (volume : Measure ℂ) := by
  have hUopen : IsOpen (U : Set ℂ) := U.isOpen
  have hfd1 : ContDiffOn ℝ 1 (fderiv ℝ f) (U : Set ℂ) :=
    hsm.fderiv_of_isOpen hUopen (by norm_num)
  have hbcont : Continuous (fun x => fderiv ℝ φ x e) :=
    (hφs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hbsupp : HasCompactSupport (fun x => fderiv ℝ φ x e) :=
    (hφc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L e) (by simp)
  have hbts : tsupport (fun x => fderiv ℝ φ x e) ⊆ (U : Set ℂ) := by
    refine subset_trans (closure_minimal ?_ (isClosed_tsupport φ)) hφU
    intro x hx
    by_contra hxφ
    rw [Function.mem_support] at hx
    exact hx (by rw [fderiv_notMem_tsupport_zero hxφ]; simp)
  have hcont : Continuous (fun x => fderiv ℝ f x e * fderiv ℝ φ x e) :=
    continuous_mul_of_tsupport_subset hUopen
      ((ContinuousLinearMap.apply ℝ ℝ e).contDiff.comp_contDiffOn
        hfd1).continuousOn hbcont hbts
  exact hcont.integrable_of_hasCompactSupport hbsupp.mul_left

/-- **The smooth test identity**: a `C²` pointwise solution of
`Δf + V·f = 0` on an open set pairs, against every test compactly supported
there, as gradient-pairing = potential-pairing. -/
lemma smooth_test_identity {U : Opens ℂ} {V : ℂ → ℝ} {f : ℂ → ℝ}
    (hsm : ContDiffOn ℝ 2 f (U : Set ℂ))
    (heq : ∀ x ∈ (U : Set ℂ), lapReal f x + V x * f x = 0)
    {φ : ℂ → ℝ} (hφs : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ (U : Set ℂ)) :
    (∫ x, (fderiv ℝ f x 1 * fderiv ℝ φ x 1
        + fderiv ℝ f x Complex.I * fderiv ℝ φ x Complex.I)
      ∂(volume : Measure ℂ))
      = ∫ x, V x * f x * φ x ∂(volume : Measure ℂ) := by
  have hUopen : IsOpen (U : Set ℂ) := U.isOpen
  have hfd1 : ContDiffOn ℝ 1 (fderiv ℝ f) (U : Set ℂ) :=
    hsm.fderiv_of_isOpen hUopen (by norm_num)
  let φT : 𝓓(U, ℝ) := ⟨φ, hφs, hφc, hφU⟩
  have hcoe : (φT : ℂ → ℝ) = φ := rfl
  -- per-direction integration by parts, from the classical-to-weak bridge
  have hIBP : ∀ e : ℂ,
      (∫ x, fderiv ℝ f x e * fderiv ℝ φ x e ∂(volume : Measure ℂ))
        = -∫ x, fderiv ℝ (fun y => fderiv ℝ f y e) x e * φ x
            ∂(volume : Measure ℂ) := by
    intro e
    have hfe1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y e) (U : Set ℂ) :=
      (ContinuousLinearMap.apply ℝ ℝ e).contDiff.comp_contDiffOn hfd1
    have hdiff : ∀ x ∈ (U : Set ℂ),
        DifferentiableAt ℝ (fun y => fderiv ℝ f y e) x := fun x hx =>
      (hfe1.contDiffAt (hUopen.mem_nhds hx)).differentiableAt (by norm_num)
    have hcfe : LocallyIntegrableOn (fun y => fderiv ℝ f y e)
        (U : Set ℂ) (volume : Measure ℂ) :=
      hfe1.continuousOn.locallyIntegrableOn hUopen.measurableSet
    have hcdfe : LocallyIntegrableOn (fderiv ℝ (fun y => fderiv ℝ f y e))
        (U : Set ℂ) (volume : Measure ℂ) :=
      (hfe1.continuousOn_fderiv_of_isOpen hUopen le_rfl).locallyIntegrableOn
        hUopen.measurableSet
    have hjet := TauCeti.hasWeakFDerivOn_of_differentiableOn hcfe hcdfe hdiff
    have hident := (TauCeti.hasWeakLineDerivOn_iff_testFunction.mp (hjet.hasWeakLineDerivOn e)).2.2.2
    have h := hident φT
    have hL : (∫ x, lineDeriv ℝ (φT : ℂ → ℝ) x e • (fun y => fderiv ℝ f y e) x
        ∂(volume : Measure ℂ))
        = ∫ x, fderiv ℝ f x e * fderiv ℝ φ x e ∂(volume : Measure ℂ) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      have hld : lineDeriv ℝ φ x e = fderiv ℝ φ x e :=
        (hφs.differentiable (by norm_num) x).lineDeriv_eq_fderiv
      simp [hcoe, hld, smul_eq_mul, mul_comm]
    have hR : (∫ x, (φT : ℂ → ℝ) x •
          (fun y => fderiv ℝ (fun z => fderiv ℝ f z e) y e) x
        ∂(volume : Measure ℂ))
        = ∫ x, fderiv ℝ (fun y => fderiv ℝ f y e) x e * φ x
            ∂(volume : Measure ℂ) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      exact mul_comm _ _
    rw [← hL, ← hR]
    exact h
  -- integrability of the per-direction products
  have hterm : ∀ e : ℂ, MeasureTheory.Integrable
      (fun x => fderiv ℝ f x e * fderiv ℝ φ x e) (volume : Measure ℂ) :=
    fun e => integrable_gradPairing hsm hφs hφc hφU e
  have hterm2 : ∀ e : ℂ, MeasureTheory.Integrable
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y e) x e * φ x)
      (volume : Measure ℂ) := by
    intro e
    have hfe1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y e) (U : Set ℂ) :=
      (ContinuousLinearMap.apply ℝ ℝ e).contDiff.comp_contDiffOn hfd1
    have hacont : ContinuousOn (fun x => fderiv ℝ (fun y => fderiv ℝ f y e) x e)
        (U : Set ℂ) := by
      have h := hfe1.continuousOn_fderiv_of_isOpen hUopen le_rfl
      exact (ContinuousLinearMap.apply ℝ ℝ e).continuous.comp_continuousOn h
    have hcont : Continuous
        (fun x => fderiv ℝ (fun y => fderiv ℝ f y e) x e * φ x) :=
      continuous_mul_of_tsupport_subset hUopen hacont hφs.continuous hφU
    exact hcont.integrable_of_hasCompactSupport hφc.mul_left
  -- assemble
  calc (∫ x, (fderiv ℝ f x 1 * fderiv ℝ φ x 1
        + fderiv ℝ f x Complex.I * fderiv ℝ φ x Complex.I)
      ∂(volume : Measure ℂ))
      = (∫ x, fderiv ℝ f x 1 * fderiv ℝ φ x 1 ∂(volume : Measure ℂ))
        + ∫ x, fderiv ℝ f x Complex.I * fderiv ℝ φ x Complex.I
            ∂(volume : Measure ℂ) :=
        integral_add (hterm 1) (hterm Complex.I)
    _ = -(∫ x, fderiv ℝ (fun y => fderiv ℝ f y 1) x 1 * φ x
            ∂(volume : Measure ℂ))
        + -∫ x, fderiv ℝ (fun y => fderiv ℝ f y Complex.I) x Complex.I * φ x
            ∂(volume : Measure ℂ) := by
        rw [hIBP 1, hIBP Complex.I]
    _ = -∫ x, (fderiv ℝ (fun y => fderiv ℝ f y 1) x 1 * φ x
          + fderiv ℝ (fun y => fderiv ℝ f y Complex.I) x Complex.I * φ x)
            ∂(volume : Measure ℂ) := by
        rw [integral_add (hterm2 1) (hterm2 Complex.I)]
        ring
    _ = ∫ x, V x * f x * φ x ∂(volume : Measure ℂ) := by
        rw [← integral_neg]
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        by_cases hx : x ∈ tsupport φ
        · have hxU : x ∈ (U : Set ℂ) := hφU hx
          have h := heq x hxU
          unfold lapReal at h
          have : fderiv ℝ (fun y => fderiv ℝ f y 1) x 1
              + fderiv ℝ (fun y => fderiv ℝ f y Complex.I) x Complex.I
              = -(V x * f x) := by linarith
          calc -(fderiv ℝ (fun y => fderiv ℝ f y 1) x 1 * φ x
                + fderiv ℝ (fun y => fderiv ℝ f y Complex.I) x Complex.I * φ x)
              = -((fderiv ℝ (fun y => fderiv ℝ f y 1) x 1
                + fderiv ℝ (fun y => fderiv ℝ f y Complex.I) x Complex.I) * φ x) := by
                ring
            _ = V x * f x * φ x := by rw [this]; ring
        · have hφ0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
          simp [hφ0]


/-- A `C²` solution of `Δf + V f = 0` off one point, with full-chart `L²`
value and gradient data, extends to a full-chart weak solution with the same
jet almost everywhere. The potential is measurable and bounded on compact
subsets of the chart. -/
theorem exists_w1p_isWeakSolOn_of_smooth_punctured {Ω : Opens ℂ} {z₀ : ℂ}
    {V : ℂ → ℝ} {f : ℂ → ℝ}
    (hV : ∀ K, K ⊆ Ω.carrier → IsCompact K → ∃ Cv, ∀ x ∈ K, |V x| ≤ Cv)
    (hVm : Measurable V)
    (hsm : ∀ x ∈ Ω.carrier \ {z₀}, ContDiffAt ℝ 2 f x)
    (heq : ∀ x ∈ Ω.carrier \ {z₀}, lapReal f x + V x * f x = 0)
    (hu2 : MeasureTheory.MemLp f 2 ((volume : Measure ℂ).restrict Ω.carrier))
    (hg2 : MeasureTheory.MemLp (gradEnc f) 2
      ((volume : Measure ℂ).restrict Ω.carrier)) :
    ∃ û : TauCeti.W1p (volume : Measure ℂ) Ω 2,
      IsWeakSolOn V Ω û
        ∧ (TauCeti.W1p.value û : ℂ → ℝ)
            =ᵐ[(volume : Measure ℂ).restrict Ω.carrier] f
        ∧ (TauCeti.W1p.gradient û : ℂ → ℂ)
            =ᵐ[(volume : Measure ℂ).restrict Ω.carrier] gradEnc f := by
  obtain ⟨û, hval, hgrad⟩ := exists_w1p_of_contDiffAt_punctured hsm hu2 hg2
  refine ⟨û, ?_, hval, hgrad⟩
  apply isWeakSolOn_of_punctured_tests hV hVm
  intro φ hφs hφc hφS
  have hφΩ : tsupport φ ⊆ Ω.carrier := hφS.trans Set.sdiff_subset
  -- the punctured opens as the identity's open set
  have hsmOn : ContDiffOn ℝ 2 f ((puncturedOpens Ω z₀ : Opens ℂ) : Set ℂ) :=
    fun x hx => (hsm x hx).contDiffWithinAt
  -- congr the û-integrand to the f-side
  have hae : (fun x =>
      (TauCeti.W1p.gradient û x).re * fderiv ℝ φ x 1
        + (TauCeti.W1p.gradient û x).im * fderiv ℝ φ x Complex.I
        - V x * TauCeti.W1p.value û x * φ x)
      =ᵐ[(volume : Measure ℂ).restrict Ω.carrier]
      (fun x => (fderiv ℝ f x 1 * fderiv ℝ φ x 1
        + fderiv ℝ f x Complex.I * fderiv ℝ φ x Complex.I)
        - V x * f x * φ x) := by
    filter_upwards [hval, hgrad] with x h1 h2
    rw [h1, h2, gradEnc_re, gradEnc_im]
  rw [integral_congr_ae hae]
  -- integrability: the gradient part globally, the potential part by difference
  have hA : MeasureTheory.Integrable (fun x =>
      fderiv ℝ f x 1 * fderiv ℝ φ x 1
        + fderiv ℝ f x Complex.I * fderiv ℝ φ x Complex.I)
      (volume : Measure ℂ) :=
    (integrable_gradPairing hsmOn hφs hφc hφS 1).add
      (integrable_gradPairing hsmOn hφs hφc hφS Complex.I)
  obtain ⟨Cv, hCv⟩ := hV (tsupport φ) hφΩ hφc
  have hintû := integrable_testIntegrand û hVm hφs hφc
    (le_max_right Cv 0) (fun x hx => (hCv x hx).trans (le_max_left _ _))
  have hintf : MeasureTheory.Integrable (fun x =>
      (fderiv ℝ f x 1 * fderiv ℝ φ x 1
        + fderiv ℝ f x Complex.I * fderiv ℝ φ x Complex.I)
        - V x * f x * φ x)
      ((volume : Measure ℂ).restrict Ω.carrier) := hintû.congr hae
  have hB : MeasureTheory.Integrable (fun x => V x * f x * φ x)
      ((volume : Measure ℂ).restrict Ω.carrier) := by
    have h := (hA.restrict (s := Ω.carrier)).sub hintf
    apply h.congr
    apply Filter.Eventually.of_forall
    intro x
    simp only [Pi.sub_apply]
    ring
  -- split and localize to global integrals
  rw [integral_sub (hA.restrict (s := Ω.carrier)) hB]
  have hAvan : ∀ x ∉ Ω.carrier,
      (fderiv ℝ f x 1 * fderiv ℝ φ x 1
        + fderiv ℝ f x Complex.I * fderiv ℝ φ x Complex.I) = 0 := by
    intro x hx
    have hxφ : x ∉ tsupport φ := fun h => hx (hφΩ h)
    rw [fderiv_notMem_tsupport_zero hxφ]
    simp
  have hBvan : ∀ x ∉ Ω.carrier, V x * f x * φ x = 0 := by
    intro x hx
    have hxφ : x ∉ tsupport φ := fun h => hx (hφΩ h)
    rw [image_eq_zero_of_notMem_tsupport hxφ, mul_zero]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hAvan,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hBvan]
  -- the smooth test identity closes it
  rw [sub_eq_zero]
  exact smooth_test_identity hsmOn heq hφs hφc hφS

end KsIndex.PunctureRemoval
