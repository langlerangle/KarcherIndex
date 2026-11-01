module

/-
KsIndexLean — Compact-support divergence and Green identities on the plane.

The file proves `∫ u*Δφ = ∫ Δu*φ` on `ℂ`, using `Surface.laplacian`,
for `u` smooth on an open set `U` and a globally smooth test function `φ`
whose compact support lies in `U`.

The divergence corollary first places a compactly supported differentiable
field inside a rectangle. Continuity of its divergence supplies integrability,
and all four boundary integrals vanish. The measure-preserving identification
of `ℂ` with `ℝ × ℝ` transports this result to complex coordinates.

For Green's identity, the field components are `u*∂ᵥφ - φ*∂ᵥu`, for
`v = 1,I`. Their first-order cross terms cancel within each component,
so the proof does not require symmetry of mixed partials. Outside
`tsupport φ`, the field and both integrands vanish locally. Since every
point lies in `U` or in the open complement of `tsupport φ`, local
smoothness and this vanishing establish global differentiability of the
field and continuity and integrability of the terms used in the identity.
-/
public import KsIndexLean.Surface

@[expose] public section


noncomputable section

open Complex MeasureTheory Metric
open scoped ContDiff

namespace KsIndex.Green

open KsIndex.Surface

/-! ### Small helpers: vanishing off a closed set kills the derivative -/

/-- A function vanishing on a neighbourhood has zero `fderiv`. -/
lemma fderiv_zero_of_eventually_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {h : E → F} {x : E}
    (hev : h =ᶠ[nhds x] fun _ => (0 : F)) : fderiv ℝ h x = 0 := by
  rw [hev.fderiv_eq]
  exact fderiv_const_apply 0

/-- Off `tsupport φ`, `φ` vanishes. -/
lemma zero_of_notMem_tsupport {φ : ℂ → ℂ} {w : ℂ} (hw : w ∉ tsupport φ) : φ w = 0 := by
  by_contra h0
  exact hw (subset_closure (Function.mem_support.mpr h0))

/-- Off `tsupport φ`, `φ` vanishes on a whole neighbourhood. -/
lemma eventually_zero_of_notMem_tsupport {φ : ℂ → ℂ} {w : ℂ} (hw : w ∉ tsupport φ) :
    φ =ᶠ[nhds w] fun _ => (0 : ℂ) :=
  Filter.eventuallyEq_of_mem ((isClosed_tsupport φ).isOpen_compl.mem_nhds hw)
    fun z hz => zero_of_notMem_tsupport hz

/-- Off `tsupport φ`, the (full) derivative of `φ` vanishes. -/
lemma fderiv_zero_of_notMem_tsupport {φ : ℂ → ℂ} {w : ℂ} (hw : w ∉ tsupport φ) :
    fderiv ℝ φ w = 0 :=
  fderiv_zero_of_eventually_zero (eventually_zero_of_notMem_tsupport hw)

/-- Off `tsupport φ`, the flat Laplacian of `φ` vanishes. -/
lemma laplacian_zero_of_notMem_tsupport {φ : ℂ → ℂ} {w : ℂ} (hw : w ∉ tsupport φ) :
    laplacian φ w = 0 := by
  have hev : ∀ v : ℂ, (fun z => fderiv ℝ φ z v) =ᶠ[nhds w] fun _ => (0 : ℂ) := by
    intro v
    refine Filter.eventuallyEq_of_mem ((isClosed_tsupport φ).isOpen_compl.mem_nhds hw)
      fun z hz => ?_
    rw [fderiv_zero_of_notMem_tsupport hz]
    simp
  simp only [laplacian]
  rw [(hev 1).fderiv_eq, (hev I).fderiv_eq]
  simp

/-! ### (i) The compact-support divergence corollary on the plane -/

/-- **Divergence corollary on `ℝ × ℝ`**: a differentiable field `(f, g)` with continuous
divergence, vanishing outside a compact set, has `∫ (∂₁f + ∂₂g) = 0`.  Rectangle large enough to contain the support strictly;
all four boundary integrals vanish. -/
theorem integral_div_prod_eq_zero (f g : ℝ × ℝ → ℂ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hdc : Continuous fun x => fderiv ℝ f x (1, 0) + fderiv ℝ g x (0, 1))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hfK : ∀ x ∉ K, f x = 0) (hgK : ∀ x ∉ K, g x = 0) :
    ∫ x, (fderiv ℝ f x (1, 0) + fderiv ℝ g x (0, 1)) = 0 := by
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).mp hK.isBounded
  set S : ℝ := max R 0 with hSdef
  have hS0 : 0 ≤ S := le_max_right R 0
  have hKball : K ⊆ closedBall (0 : ℝ × ℝ) S :=
    hR.trans (closedBall_subset_closedBall (le_max_left R 0))
  -- membership in the ball bounds both coordinates
  have hcoord : ∀ p ∈ K, |p.1| ≤ S ∧ |p.2| ≤ S := by
    intro p hp
    have hn : ‖p‖ ≤ S := by simpa [dist_zero_right] using mem_closedBall.mp (hKball hp)
    constructor
    · calc |p.1| = ‖p.1‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖p‖ := norm_fst_le p
        _ ≤ S := hn
    · calc |p.2| = ‖p.2‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖p‖ := norm_snd_le p
        _ ≤ S := hn
  set aa : ℝ := -(S + 1) with haa
  set bb : ℝ := S + 1 with hbb
  have hle : ((aa, aa) : ℝ × ℝ) ≤ (bb, bb) := by
    constructor <;> · simp only [haa, hbb]; linarith
  have hKIcc : K ⊆ Set.Icc ((aa, aa) : ℝ × ℝ) (bb, bb) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hcoord p hp
    rw [abs_le] at h1 h2
    exact ⟨⟨by simp only [haa]; linarith [h1.1], by simp only [haa]; linarith [h2.1]⟩,
      ⟨by simp only [hbb]; linarith [h1.2], by simp only [hbb]; linarith [h2.2]⟩⟩
  -- a point with an extreme coordinate is outside K
  have hout : ∀ p : ℝ × ℝ, |p.1| = S + 1 ∨ |p.2| = S + 1 → p ∉ K := by
    rintro p (h | h) hp
    · have := (hcoord p hp).1; rw [h] at this; linarith
    · have := (hcoord p hp).2; rw [h] at this; linarith
  -- derivatives vanish off K (K is closed, so f ≡ 0 on a neighbourhood there)
  have hev : ∀ (h : ℝ × ℝ → ℂ), (∀ x ∉ K, h x = 0) → ∀ x ∉ K,
      h =ᶠ[nhds x] fun _ => (0 : ℂ) := fun h hh x hx =>
    Filter.eventuallyEq_of_mem (hK.isClosed.isOpen_compl.mem_nhds hx) fun y hy => hh y hy
  have hdiv0 : ∀ x ∉ K, fderiv ℝ f x (1, 0) + fderiv ℝ g x (0, 1) = 0 := by
    intro x hx
    rw [fderiv_zero_of_eventually_zero (hev f hfK x hx),
      fderiv_zero_of_eventually_zero (hev g hgK x hx)]
    simp
  -- the divergence theorem on the rectangle
  have key := integral_divergence_prod_Icc_of_hasFDerivAt_of_le f g
    (fderiv ℝ f) (fderiv ℝ g) (aa, aa) (bb, bb) hle
    hf.continuous.continuousOn hg.continuous.continuousOn
    (fun x _ => (hf x).hasFDerivAt) (fun x _ => (hg x).hasFDerivAt)
    (hdc.continuousOn.integrableOn_compact isCompact_Icc)
  -- boundary integrands all vanish
  have hgtop : ∀ x : ℝ, g (x, bb) = 0 := fun x =>
    hgK _ (hout _ (Or.inr (by simp [hbb, abs_of_nonneg, hS0]; linarith)))
  have hgbot : ∀ x : ℝ, g (x, aa) = 0 := fun x =>
    hgK _ (hout _ (Or.inr (by simp only [haa]; rw [abs_neg, abs_of_nonneg (by linarith)])))
  have hfright : ∀ y : ℝ, f (bb, y) = 0 := fun y =>
    hfK _ (hout _ (Or.inl (by simp only [hbb]; rw [abs_of_nonneg (by linarith)])))
  have hfleft : ∀ y : ℝ, f (aa, y) = 0 := fun y =>
    hfK _ (hout _ (Or.inl (by simp only [haa]; rw [abs_neg, abs_of_nonneg (by linarith)])))
  calc ∫ x, (fderiv ℝ f x (1, 0) + fderiv ℝ g x (0, 1))
      = ∫ x in Set.Icc ((aa, aa) : ℝ × ℝ) (bb, bb),
          (fderiv ℝ f x (1, 0) + fderiv ℝ g x (0, 1)) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero
          fun x hx => hdiv0 x fun hxK => hx (hKIcc hxK)).symm
    _ = _ := key
    _ = 0 := by simp [hgtop, hgbot, hfright, hfleft]

/-! ### (ii) Transport to `ℂ` -/

/-- **Divergence corollary on `ℂ`**: a differentiable field `(f, g)` with continuous
divergence, vanishing outside a compact set, has `∫ (∂f·1 + ∂g·I) = 0`, the directions `1, I` being the plane coordinates. -/
theorem integral_div_complex_eq_zero (f g : ℂ → ℂ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hdc : Continuous fun w => fderiv ℝ f w 1 + fderiv ℝ g w I)
    {K : Set ℂ} (hK : IsCompact K)
    (hfK : ∀ w ∉ K, f w = 0) (hgK : ∀ w ∉ K, g w = 0) :
    ∫ w, (fderiv ℝ f w 1 + fderiv ℝ g w I) = 0 := by
  set e := Complex.equivRealProdCLM with he
  -- directional derivative transport for a composition with the linear chart
  have hcompd : ∀ (h : ℂ → ℂ), Differentiable ℝ h → ∀ (p : ℝ × ℝ) (v : ℝ × ℝ),
      fderiv ℝ (h ∘ ⇑e.symm) p v = fderiv ℝ h (e.symm p) (e.symm v) := by
    intro h hh p v
    rw [fderiv_comp p (hh _) e.symm.differentiableAt, e.symm.fderiv]
    rfl
  have hsymm10 : e.symm (1, 0) = 1 := by
    rw [Complex.equivRealProdCLM_symm_apply]; simp
  have hsymm01 : e.symm (0, 1) = I := by
    rw [Complex.equivRealProdCLM_symm_apply]; simp
  -- the transported field and its data
  have hfP : Differentiable ℝ (f ∘ ⇑e.symm) := hf.comp e.symm.differentiable
  have hgP : Differentiable ℝ (g ∘ ⇑e.symm) := hg.comp e.symm.differentiable
  have hdivP : ∀ p : ℝ × ℝ,
      fderiv ℝ (f ∘ ⇑e.symm) p (1, 0) + fderiv ℝ (g ∘ ⇑e.symm) p (0, 1)
        = fderiv ℝ f (e.symm p) 1 + fderiv ℝ g (e.symm p) I := by
    intro p
    rw [hcompd f hf p (1, 0), hcompd g hg p (0, 1), hsymm10, hsymm01]
  have hdcP : Continuous fun p =>
      fderiv ℝ (f ∘ ⇑e.symm) p (1, 0) + fderiv ℝ (g ∘ ⇑e.symm) p (0, 1) := by
    have : (fun p => fderiv ℝ (f ∘ ⇑e.symm) p (1, 0) + fderiv ℝ (g ∘ ⇑e.symm) p (0, 1))
        = (fun w => fderiv ℝ f w 1 + fderiv ℝ g w I) ∘ ⇑e.symm := funext fun p => hdivP p
    rw [this]
    exact hdc.comp e.symm.continuous
  have hKP : IsCompact (⇑e '' K) := hK.image e.continuous
  have hnotP : ∀ p : ℝ × ℝ, p ∉ ⇑e '' K → e.symm p ∉ K := by
    intro p hp hmem
    exact hp ⟨e.symm p, hmem, e.apply_symm_apply p⟩
  have hzero := integral_div_prod_eq_zero (f ∘ ⇑e.symm) (g ∘ ⇑e.symm) hfP hgP hdcP hKP
    (fun p hp => by simp only [Function.comp_apply]; exact hfK _ (hnotP p hp))
    (fun p hp => by simp only [Function.comp_apply]; exact hgK _ (hnotP p hp))
  -- pull the integral back along the measure-preserving chart
  have htrans := Complex.volume_preserving_equiv_real_prod.integral_comp'
    (fun p => fderiv ℝ (f ∘ ⇑e.symm) p (1, 0) + fderiv ℝ (g ∘ ⇑e.symm) p (0, 1))
  rw [hzero] at htrans
  rw [← htrans]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  show fderiv ℝ f w 1 + fderiv ℝ g w I
      = fderiv ℝ (f ∘ ⇑e.symm) (Complex.measurableEquivRealProd w) (1, 0)
        + fderiv ℝ (g ∘ ⇑e.symm) (Complex.measurableEquivRealProd w) (0, 1)
  rw [hdivP]
  have : e.symm (Complex.measurableEquivRealProd w) = w := by
    rw [Complex.measurableEquivRealProd_apply, Complex.equivRealProdCLM_symm_apply]
    simp [Complex.re_add_im]
  rw [this]

/-! ### (iii) The cross-cancellation product rule -/

/-- The per-component cancellation `∂ᵥ(u ∂ᵥφ − φ ∂ᵥu) = u ∂ᵥ²φ − φ ∂ᵥ²u` at a joint smooth
point: the first-order cross terms cancel within the single component, so no symmetry of mixed
partials is needed anywhere in the Green identity. -/
lemma fderiv_cross_cancel {u φ : ℂ → ℂ} {w : ℂ} (hu : ContDiffAt ℝ ∞ u w)
    (hφ : ContDiffAt ℝ ∞ φ w) (v : ℂ) :
    fderiv ℝ (fun z => u z * fderiv ℝ φ z v - φ z * fderiv ℝ u z v) w v
      = u w * fderiv ℝ (fun z => fderiv ℝ φ z v) w v
        - φ w * fderiv ℝ (fun z => fderiv ℝ u z v) w v := by
  have hdu : DifferentiableAt ℝ u w := (hu.of_le two_le_infty).differentiableAt (by norm_num)
  have hdφ : DifferentiableAt ℝ φ w := (hφ.of_le two_le_infty).differentiableAt (by norm_num)
  have hdu' : DifferentiableAt ℝ (fun z => fderiv ℝ u z v) w :=
    ((hu.fderiv_right (m := 1)
      (by simpa using (WithTop.coe_le_coe.mpr (le_top : (1 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
        contDiffAt_const).differentiableAt one_ne_zero
  have hdφ' : DifferentiableAt ℝ (fun z => fderiv ℝ φ z v) w :=
    ((hφ.fderiv_right (m := 1)
      (by simpa using (WithTop.coe_le_coe.mpr (le_top : (1 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
        contDiffAt_const).differentiableAt one_ne_zero
  have hA : DifferentiableAt ℝ (fun z => u z * fderiv ℝ φ z v) w := hdu.mul hdφ'
  have hB : DifferentiableAt ℝ (fun z => φ z * fderiv ℝ u z v) w := hdφ.mul hdu'
  rw [fderiv_fun_sub hA hB, fderiv_fun_mul hdu hdφ', fderiv_fun_mul hdφ hdu']
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Continuity of the flat Laplacian at a point of `C^∞`-smoothness. -/
lemma laplacian_continuousAt {f : ℂ → ℂ} {w : ℂ} (hf : ContDiffAt ℝ ∞ f w) :
    ContinuousAt (fun z => laplacian f z) w := by
  have hin : ∀ v : ℂ, ContinuousAt (fun z => fderiv ℝ (fun y => fderiv ℝ f y v) z v) w := by
    intro v
    have h2 : ContDiffAt ℝ 2 (fun z => fderiv ℝ f z v) w :=
      (hf.fderiv_right (m := 2)
        (by simpa using (WithTop.coe_le_coe.mpr (le_top : (2 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
          contDiffAt_const
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ fun z => fderiv ℝ f z v) w :=
      h2.fderiv_right (m := 1) le_rfl
    exact (h1.clm_apply contDiffAt_const).continuousAt
  have hsum : ContinuousAt (fun z => fderiv ℝ (fun y => fderiv ℝ f y 1) z 1
      + fderiv ℝ (fun y => fderiv ℝ f y I) z I) w := (hin 1).add (hin I)
  simpa only [laplacian] using hsum

/-! ### (iv) The Green identity -/

/-- **The Green identity** on `ℂ`: for `u` smooth on an open set `U` and `φ` a smooth test
function compactly supported inside `U`, `∫ u·Δφ = ∫ Δu·φ` (full-plane integrals; both
integrands vanish off `tsupport φ`). -/
theorem green_identity {U : Set ℂ} (hU : IsOpen U) {u φ : ℂ → ℂ}
    (hu : ContDiffOn ℝ ∞ u U) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    ∫ w, u w * laplacian φ w = ∫ w, laplacian u w * φ w := by
  have huAt : ∀ w ∈ U, ContDiffAt ℝ ∞ u w := fun w hw => hu.contDiffAt (hU.mem_nhds hw)
  have hcov : ∀ w : ℂ, w ∈ U ∨ w ∉ tsupport φ := fun w =>
    or_iff_not_imp_left.mpr fun hw hts => hw (hφU hts)
  have hopenC : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
  -- the Green field components, zero off `tsupport φ`
  set F : ℂ → ℂ → ℂ := fun v z => u z * fderiv ℝ φ z v - φ z * fderiv ℝ u z v with hFdef
  have hFzero : ∀ (v : ℂ) {z : ℂ}, z ∉ tsupport φ → F v z = 0 := by
    intro v z hz
    simp only [hFdef, zero_of_notMem_tsupport hz, fderiv_zero_of_notMem_tsupport hz]
    simp
  have hFev : ∀ (v : ℂ) {z : ℂ}, z ∉ tsupport φ → F v =ᶠ[nhds z] fun _ => (0 : ℂ) :=
    fun v {z} hz => Filter.eventuallyEq_of_mem (hopenC.mem_nhds hz) fun y hy => hFzero v hy
  -- global differentiability by the two-case split
  have hFdiff : ∀ v : ℂ, Differentiable ℝ (F v) := by
    intro v w
    rcases hcov w with hw | hw
    · have hφAt : ContDiffAt ℝ ∞ φ w := hφ.contDiffAt
      have huw := huAt w hw
      have hdu : DifferentiableAt ℝ u w := (huw.of_le two_le_infty).differentiableAt (by norm_num)
      have hdφ : DifferentiableAt ℝ φ w :=
        (hφAt.of_le two_le_infty).differentiableAt (by norm_num)
      have hdu' : DifferentiableAt ℝ (fun z => fderiv ℝ u z v) w :=
        ((huw.fderiv_right (m := 1)
          (by simpa using (WithTop.coe_le_coe.mpr (le_top : (1 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
            contDiffAt_const).differentiableAt one_ne_zero
      have hdφ' : DifferentiableAt ℝ (fun z => fderiv ℝ φ z v) w :=
        ((hφAt.fderiv_right (m := 1)
          (by simpa using (WithTop.coe_le_coe.mpr (le_top : (1 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
            contDiffAt_const).differentiableAt one_ne_zero
      exact (hdu.mul hdφ').sub (hdφ.mul hdu')
    · exact (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq (hFev v hw)
  -- the pointwise divergence identity, everywhere
  have hdivF : ∀ w : ℂ, fderiv ℝ (F 1) w 1 + fderiv ℝ (F I) w I
      = u w * laplacian φ w - φ w * laplacian u w := by
    intro w
    rcases hcov w with hw | hw
    · rw [hFdef]
      rw [fderiv_cross_cancel (huAt w hw) hφ.contDiffAt 1,
        fderiv_cross_cancel (huAt w hw) hφ.contDiffAt I]
      simp only [laplacian]
      ring
    · rw [fderiv_zero_of_eventually_zero (hFev 1 hw),
        fderiv_zero_of_eventually_zero (hFev I hw),
        zero_of_notMem_tsupport hw, laplacian_zero_of_notMem_tsupport hw]
      simp
  -- continuity of the two integrands (two-case split again)
  have hP1 : Continuous fun w => u w * laplacian φ w := by
    rw [continuous_iff_continuousAt]
    intro w
    rcases hcov w with hw | hw
    · exact ((huAt w hw).continuousAt).mul (laplacian_continuousAt hφ.contDiffAt)
    · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
      refine (Filter.eventuallyEq_of_mem (hopenC.mem_nhds hw) fun z hz => ?_).symm
      rw [laplacian_zero_of_notMem_tsupport hz, mul_zero]
  have hP2 : Continuous fun w => φ w * laplacian u w := by
    rw [continuous_iff_continuousAt]
    intro w
    rcases hcov w with hw | hw
    · exact hφ.continuous.continuousAt.mul (laplacian_continuousAt (huAt w hw))
    · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
      refine (Filter.eventuallyEq_of_mem (hopenC.mem_nhds hw) fun z hz => ?_).symm
      rw [zero_of_notMem_tsupport hz, zero_mul]
  -- compact supports and integrability
  have hcs : ∀ h : ℂ → ℂ, (∀ w ∉ tsupport φ, h w = 0) → HasCompactSupport h := by
    intro h hh
    refine IsCompact.of_isClosed_subset hφc isClosed_closure
      (closure_minimal ?_ (isClosed_tsupport φ))
    intro w hw
    by_contra hts
    exact hw (hh w hts)
  have hcs1 : HasCompactSupport fun w => u w * laplacian φ w :=
    hcs _ fun w hw => by rw [laplacian_zero_of_notMem_tsupport hw, mul_zero]
  have hcs2 : HasCompactSupport fun w => φ w * laplacian u w :=
    hcs _ fun w hw => by rw [zero_of_notMem_tsupport hw, zero_mul]
  have hi1 : Integrable fun w => u w * laplacian φ w :=
    hP1.integrable_of_hasCompactSupport hcs1
  have hi2 : Integrable fun w => φ w * laplacian u w :=
    hP2.integrable_of_hasCompactSupport hcs2
  -- assemble: ∫ (u·Δφ − φ·Δu) = ∫ div F = 0
  have hdc : Continuous fun w => fderiv ℝ (F 1) w 1 + fderiv ℝ (F I) w I := by
    have : (fun w => fderiv ℝ (F 1) w 1 + fderiv ℝ (F I) w I)
        = fun w => u w * laplacian φ w - φ w * laplacian u w := funext hdivF
    rw [this]
    exact hP1.sub hP2
  have hzero := integral_div_complex_eq_zero (F 1) (F I) (hFdiff 1) (hFdiff I) hdc hφc
    (fun w hw => hFzero 1 hw) (fun w hw => hFzero I hw)
  have hsub : ∫ w, (u w * laplacian φ w - φ w * laplacian u w) = 0 := by
    rw [← hzero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => (hdivF w).symm)
  rw [integral_sub hi1 hi2] at hsub
  have hflip : (fun w => φ w * laplacian u w) = fun w => laplacian u w * φ w := by
    funext w; ring
  rw [sub_eq_zero.mp hsub, hflip]

end KsIndex.Green
