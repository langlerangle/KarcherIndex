module

public import KsIndexLean.SeamStraddleTest
public import KsIndexLean.SeamInversionTransport
public import KsIndexLean.PaperSlitTestTransport

@[expose] public section


/-!
# Across-seam weak Jacobi identities

For a pair-radical vector in the paper slit character domain, a smooth test
supported in the seam annulus gives a pair `(ψ, phase⁻¹ · (ψ ∘ σ))`.
The radical identity yields the sum of the two weak Jacobi pairings, with
`phase⁻¹` multiplying the second term. The test must satisfy the stated
sector-vanishing and rotation-character conditions.

The test uses the inverse phase while the glued field uses the phase itself:
the first slot of the form is conjugate-linear, and conjugation inverts the
unit-modulus phase. Inversion transports the second pairing to the outer
half-annulus. This requires differentiability and the stated almost-everywhere
jet identifications on the open inner half-annulus, not smoothness up to the seam.

The final identities use an explicit three-term character-weighted sum of
rotated tests. This sum is not divided by three. It preserves the required
support and sector-vanishing conditions and has the specified character.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.WeakH1 KsIndex.PaperSlitAdapter

/-! ### σ commutes with rotations -/

/-- The seam reflection commutes with every unit-modulus scaling (so with
every rotation): `σ(a·z) = a·σ(z)` for `‖a‖ = 1` — including the assigned
value at `z = 0`, where both sides are `0`. -/
lemma sigma_rotation_comm {a : ℂ} (ha : ‖a‖ = 1) (z : ℂ) :
    Bracket.σ (a * z) = a * Bracket.σ z := by
  have hσa : ((starRingEnd ℂ) a)⁻¹ = a := by
    have h := Bracket.σ_self ha
    rwa [Bracket.σ, one_div] at h
  simp only [Bracket.σ, one_div, map_mul, mul_inv, hσa]

/-! ### Character membership of the straddling pair -/

/-- A straddling pair built on a `(θ, c)`-equivariant test lies in the pair
character domain: the direct slot by the equivariance itself, the σ-pulled
slot because `σ` commutes with rotations. -/
lemma straddlePair_mem_pairCharacter (phase : ℂ) {ψ : ℂ → ℂ}
    (hs : ContDiff ℝ ∞ ψ)
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (θ : ℝ) (c : ℂ)
    (h_char : ∀ z, ψ (planeRotation θ z) = c * ψ z) :
    straddlePair phase hs h_in h_out ∈ pairCharacterDomain θ c := by
  rw [KsIndex.Spectral.mem_pairCharacterDomain_iff]
  constructor
  · exact weakCharacter_of_value_eq _ θ c (globalSmoothH1_value ψ hs) h_char
  · apply Submodule.smul_mem
    apply weakCharacter_of_value_eq _ θ c
      (globalSmoothH1_value _ (straddle_pull_smooth hs h_in h_out))
    intro z
    have hcomm : Bracket.σ (planeRotation θ z) =
        Complex.exp ((θ : ℂ) * Complex.I) * Bracket.σ z := by
      rw [planeRotation_apply]
      exact sigma_rotation_comm (by rw [Complex.norm_exp_ofReal_mul_I]) z
    have hc := h_char (Bracket.σ z)
    rw [planeRotation_apply] at hc
    calc ψ (Bracket.σ (planeRotation θ z))
        = ψ (Complex.exp ((θ : ℂ) * Complex.I) * Bracket.σ z) := by rw [hcomm]
      _ = c * ψ (Bracket.σ z) := hc

/-- The paper-domain specialization: a class-`j` equivariant straddling test
produces a pair in `paperSlitCharacterDomain α j`. -/
theorem straddlePair_mem_paperSlitCharacter (α : ℝ) (j : ℕ) {ψ : ℂ → ℂ}
    (hs : ContDiff ℝ ∞ ψ)
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (h_sector : ∀ w : ℂ, ‖w‖ = 1 → 0 ≤ (w ^ 3).re → ψ w = 0)
    (h_char : ∀ z, ψ (planeRotation (-(2 * Real.pi) / 3) z) =
      (KsIndex.FormIndex.zeta 3 ^ j) * ψ z) :
    straddlePair (Complex.exp ((2 * Real.pi * α) * Complex.I)) hs h_in h_out ∈
      paperSlitCharacterDomain α j :=
  Submodule.mem_inf.mpr
    ⟨straddlePair_mem_paperSlit α hs h_in h_out h_sector,
     straddlePair_mem_pairCharacter _ hs h_in h_out _ _ h_char⟩

/-! ### The combined identity -/

/-- **The form-level across-seam identity.** A pair-radical vector pairs to
zero against every straddling test: the combined identity whose second term
carries the glue prefactor `phase⁻¹` — the conjugation-duality face of the
seam. The straddling counterpart of `pair_radical_D1_snd/fst`. -/
theorem pair_radical_straddle {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (h_sector : ∀ w : ℂ, ‖w‖ = 1 → 0 ≤ (w ^ 3).re → ψ w = 0)
    (h_char : ∀ z, ψ (planeRotation (-(2 * Real.pi) / 3) z) =
      (KsIndex.FormIndex.zeta 3 ^ j) * ψ z) :
    weakJacobi (surfacePotential 3) u.val.1 (globalSmoothH1 ψ hs) +
      (Complex.exp ((2 * Real.pi * α) * Complex.I))⁻¹ *
        weakJacobi (surfacePotential 3) u.val.2
          (globalSmoothH1 (fun z => ψ (Bracket.σ z))
            (straddle_pull_smooth hs h_in h_out)) = 0 := by
  have h := hrad ⟨straddlePair (Complex.exp ((2 * Real.pi * α) * Complex.I))
      hs h_in h_out,
    straddlePair_mem_paperSlitCharacter α j hs h_in h_out h_sector h_char⟩
  have h2 : weakJacobi (surfacePotential 3) u.val.1 (globalSmoothH1 ψ hs) +
      weakJacobi (surfacePotential 3) u.val.2
        ((Complex.exp ((2 * Real.pi * α) * Complex.I))⁻¹ •
          globalSmoothH1 (fun z => ψ (Bracket.σ z))
            (straddle_pull_smooth hs h_in h_out)) = 0 := h
  rwa [weakJacobi_smul_right] at h2

/-! ### Conversion to outer half-annulus integrals

The representative hypotheses concern the open inner half-annulus.
The conclusions are sums of inner and outer half-annulus integrals;
no boundary smoothness of the representatives is assumed. -/

open KsIndex.GradOrtho KsIndex.Surface

/-- The σ-pull of a straddling test vanishes on the small ball.
The assigned value at zero is covered by the inner vanishing condition. -/
lemma straddle_pull_small {ψ : ℂ → ℂ}
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    {z : ℂ} (hz : ‖z‖ < 1 / 2) : ψ (Bracket.σ z) = 0 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · have hσ0 : Bracket.σ (0 : ℂ) = 0 := by simp [Bracket.σ]
    rw [hσ0]
    exact h_in 0 (by norm_num)
  · apply h_out
    rw [Bracket.norm_σ, show (2 : ℝ) = (2⁻¹)⁻¹ by norm_num]
    exact (inv_le_inv₀ (by positivity) (norm_pos_iff.mpr hz0)).mpr (by linarith)

/-- σ carries the outer half-annulus into the inner one. -/
lemma sigma_mem_inner {w : ℂ} (hw : w ∈ outerHalfAnnulus) :
    Bracket.σ w ∈ innerHalfAnnulus := by
  rw [← sigma_image_innerHalf] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  rwa [Bracket.σ_σ]

/-- A disk integral of an integrand vanishing on the open small ball
localizes to the inner half-annulus (the circle `‖z‖ = 1/2` is null). -/
lemma disk_integral_localize (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, ‖z‖ < 1 / 2 → F z = 0) :
    (∫ z in (WeakH1.disk : Set ℂ), F z) = ∫ z in innerHalfAnnulus, F z := by
  have hnull : volume (Metric.sphere (0 : ℂ) (1 / 2)) = 0 :=
    Measure.addHaar_sphere volume 0 (1 / 2)
  have hsub : innerHalfAnnulus ⊆ (WeakH1.disk : Set ℂ) := fun z hz => by
    change z ∈ Metric.ball (0 : ℂ) 1
    simp only [Metric.mem_ball, dist_zero_right]
    exact hz.2
  have hae : ∀ᵐ z ∂(volume.restrict (WeakH1.disk : Set ℂ)),
      F z = innerHalfAnnulus.indicator F z := by
    have h0 : ∀ᵐ z : ℂ ∂volume, z ∉ Metric.sphere (0 : ℂ) (1 / 2) :=
      compl_mem_ae_iff.mpr hnull
    have h0' := h0.filter_mono (ae_mono (Measure.restrict_le_self
      (s := (WeakH1.disk : Set ℂ))))
    filter_upwards [h0', ae_restrict_mem WeakH1.disk.isOpen.measurableSet]
      with z hzs hzd
    by_cases hzi : z ∈ innerHalfAnnulus
    · rw [Set.indicator_of_mem hzi]
    · rw [Set.indicator_of_notMem hzi]
      apply hF
      have hd : ‖z‖ < 1 := by
        simpa [WeakH1.disk, Metric.mem_ball, dist_zero_right] using hzd
      have hns : ‖z‖ ≠ 1 / 2 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hzs
      rcases lt_trichotomy (1 / 2 : ℝ) ‖z‖ with h | h | h
      · exact absurd ⟨h, hd⟩ hzi
      · exact absurd h.symm hns
      · exact h
  calc (∫ z in (WeakH1.disk : Set ℂ), F z)
      = ∫ z in (WeakH1.disk : Set ℂ), innerHalfAnnulus.indicator F z :=
        integral_congr_ae hae
    _ = ∫ z in innerHalfAnnulus, F z := by
        rw [integral_indicator measurableSet_innerHalfAnnulus,
          Measure.restrict_restrict measurableSet_innerHalfAnnulus,
          Set.inter_eq_left.mpr hsub]

/-- **The localized representative form of the weak pairing.** For a smooth
global test vanishing on the small ball, the weak Jacobi pairing against an
H¹ element with a smooth LOCAL representative on the open inner half-annulus
is the pair of inner half-annulus integrals in that representative. -/
lemma weakJacobi_inner_localized_general (k : ℕ) (u : ComplexH1) {τ f : ℂ → ℂ}
    (hτ : ContDiff ℝ ∞ τ)
    (hτ0 : ∀ z : ℂ, ‖z‖ < 1 / 2 → τ z = 0)
    (hval : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus] f)
    (hdx : (dxCLM u : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f z 1))
    (hdy : (dyCLM u : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f z Complex.I)) :
    weakJacobi (surfacePotential k) u (globalSmoothH1 τ hτ) =
      (∫ z in innerHalfAnnulus, gradInner f τ z) -
        ∫ z in innerHalfAnnulus, (potV k z : ℂ) * starRingEnd ℂ (f z) * τ z := by
  have hfd0 : ∀ z : ℂ, ‖z‖ < 1 / 2 → fderiv ℝ τ z = 0 := by
    intro z hz
    have hev : τ =ᶠ[nhds z] (fun _ => (0 : ℂ)) := by
      apply Filter.eventuallyEq_of_mem
        (Metric.isOpen_ball.mem_nhds
          (show z ∈ Metric.ball (0 : ℂ) (1 / 2) by
            simp only [Metric.mem_ball, dist_zero_right]; exact hz))
      intro x hx
      exact hτ0 x (by simpa [Metric.mem_ball, dist_zero_right] using hx)
    rw [hev.fderiv_eq]
    simp
  rw [weakJacobi_integral_representatives (surfacePotential k) u (globalSmoothH1 τ hτ)
    (f := (valueCLM u : ℂ → ℂ)) (g := τ)
    (a := (dxCLM u : ℂ → ℂ)) (b := (dyCLM u : ℂ → ℂ))
    (c := fun x => fderiv ℝ τ x 1) (d := fun x => fderiv ℝ τ x Complex.I)
    Filter.EventuallyEq.rfl (globalSmoothH1_value τ hτ)
    Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl
    (globalSmoothH1_dx τ hτ) (globalSmoothH1_dy τ hτ)]
  congr 1
  · rw [disk_integral_localize _ (fun z hz => by rw [hfd0 z hz]; simp)]
    apply integral_congr_ae
    have hdx' := hdx
    have hdy' := hdy
    filter_upwards [hdx', hdy'] with z h1 h2
    rw [h1, h2]
    rfl
  · rw [disk_integral_localize _ (fun z hz => by rw [hτ0 z hz]; ring)]
    apply integral_congr_ae
    filter_upwards [hval] with z h1
    rw [h1]
    rfl


lemma weakJacobi_inner_localized (u : ComplexH1) {τ f : ℂ → ℂ}
    (hτ : ContDiff ℝ ∞ τ)
    (hτ0 : ∀ z : ℂ, ‖z‖ < 1 / 2 → τ z = 0)
    (hval : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus] f)
    (hdx : (dxCLM u : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f z 1))
    (hdy : (dyCLM u : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f z Complex.I)) :
    weakJacobi (surfacePotential 3) u (globalSmoothH1 τ hτ) =
      (∫ z in innerHalfAnnulus, gradInner f τ z) -
        ∫ z in innerHalfAnnulus, (potV 3 z : ℂ) * starRingEnd ℂ (f z) * τ z :=
  weakJacobi_inner_localized_general 3 u hτ hτ0 hval hdx hdy

/-- The weak pairing of `u₂` against the σ-pulled straddling
test, in a smooth local representative on the OPEN inner half-annulus,
equals the OUTER half-annulus pairing of the σ-pulled representative against
`ψ` itself — the copy-2 term rewritten as an outer-side glued-field pairing,
by inversion transport of the gradient and potential integrals. -/
theorem weakJacobi_straddle_outer_rep_general (k : ℕ) (hk : 2 ≤ k) (u₂ : ComplexH1) {ψ f : ℂ → ℂ}
    (hs : ContDiff ℝ ∞ ψ)
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (hf : ∀ z ∈ innerHalfAnnulus, DifferentiableAt ℝ f z)
    (hval : (valueCLM u₂ : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus] f)
    (hdx : (dxCLM u₂ : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f z 1))
    (hdy : (dyCLM u₂ : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f z Complex.I)) :
    weakJacobi (surfacePotential k) u₂
        (globalSmoothH1 (fun z => ψ (Bracket.σ z))
          (straddle_pull_smooth hs h_in h_out)) =
      (∫ w in outerHalfAnnulus, gradInner (f ∘ Bracket.σ) ψ w) -
        ∫ w in outerHalfAnnulus, (potV k w : ℂ) *
          starRingEnd ℂ ((f ∘ Bracket.σ) w) * ψ w := by
  rw [weakJacobi_inner_localized_general k u₂ (straddle_pull_smooth hs h_in h_out)
    (fun z hz => straddle_pull_small h_in h_out hz) hval hdx hdy]
  have hff : (f ∘ Bracket.σ) ∘ Bracket.σ = f := by
    funext z
    simp [Function.comp, Bracket.σ_σ]
  have hdiff : ∀ w ∈ outerHalfAnnulus, DifferentiableAt ℝ (f ∘ Bracket.σ) w := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h
      have := hw.1
      rw [h, norm_zero] at this
      norm_num at this
    exact (hf _ (sigma_mem_inner hw)).comp w
      (SigmaDeriv.hasFDerivAt_sigmaR hw0).differentiableAt
  have hψdiff : ∀ w ∈ outerHalfAnnulus, DifferentiableAt ℝ ψ w :=
    fun w _ => (hs.differentiable (by simp)).differentiableAt
  rw [gradInner_seam_transport hdiff hψdiff, potential_seam_transport_general k hk (f ∘ Bracket.σ) ψ,
    show (f ∘ Bracket.σ) ∘ Bracket.σ = f from hff]
  congr 1
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    simp only [Function.comp_apply, Bracket.σ_σ]


theorem weakJacobi_straddle_outer_rep (u₂ : ComplexH1) {ψ f : ℂ → ℂ}
    (hs : ContDiff ℝ ∞ ψ)
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (hf : ∀ z ∈ innerHalfAnnulus, DifferentiableAt ℝ f z)
    (hval : (valueCLM u₂ : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus] f)
    (hdx : (dxCLM u₂ : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f z 1))
    (hdy : (dyCLM u₂ : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f z Complex.I)) :
    weakJacobi (surfacePotential 3) u₂
        (globalSmoothH1 (fun z => ψ (Bracket.σ z))
          (straddle_pull_smooth hs h_in h_out)) =
      (∫ w in outerHalfAnnulus, gradInner (f ∘ Bracket.σ) ψ w) -
        ∫ w in outerHalfAnnulus, (potV 3 w : ℂ) *
          starRingEnd ℂ ((f ∘ Bracket.σ) w) * ψ w :=
  weakJacobi_straddle_outer_rep_general 3 (by decide) u₂ hs h_in h_out hf hval hdx hdy

/-- The across-seam annulus identity.
A pair-radical vector with smooth local representatives `f₁, f₂` on the open
inner half-annulus satisfies, against every class-`j` straddling test, the
combined identity: the inner pairing of `f₁` plus `phase⁻¹` times the outer
pairing of the σ-pulled `f₂` vanishes — the glued representative's weak
Jacobi equation across the seam, as a sum of half-annulus integrals. -/
theorem pair_radical_annulus_identity {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    {ψ f₁ f₂ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (h_sector : ∀ w : ℂ, ‖w‖ = 1 → 0 ≤ (w ^ 3).re → ψ w = 0)
    (h_char : ∀ z, ψ (planeRotation (-(2 * Real.pi) / 3) z) =
      (KsIndex.FormIndex.zeta 3 ^ j) * ψ z)
    (hval₁ : (valueCLM u.val.1 : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus] f₁)
    (hdx₁ : (dxCLM u.val.1 : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f₁ z 1))
    (hdy₁ : (dyCLM u.val.1 : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f₁ z Complex.I))
    (hf₂ : ∀ z ∈ innerHalfAnnulus, DifferentiableAt ℝ f₂ z)
    (hval₂ : (valueCLM u.val.2 : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus] f₂)
    (hdx₂ : (dxCLM u.val.2 : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f₂ z 1))
    (hdy₂ : (dyCLM u.val.2 : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f₂ z Complex.I)) :
    ((∫ z in innerHalfAnnulus, gradInner f₁ ψ z) -
        ∫ z in innerHalfAnnulus, (potV 3 z : ℂ) * starRingEnd ℂ (f₁ z) * ψ z) +
      (Complex.exp ((2 * Real.pi * α) * Complex.I))⁻¹ *
        ((∫ w in outerHalfAnnulus, gradInner (f₂ ∘ Bracket.σ) ψ w) -
          ∫ w in outerHalfAnnulus, (potV 3 w : ℂ) *
            starRingEnd ℂ ((f₂ ∘ Bracket.σ) w) * ψ w) = 0 := by
  have h3a := pair_radical_straddle u hrad hs h_in h_out h_sector h_char
  rw [weakJacobi_inner_localized u.val.1 hs (fun z hz => h_in z hz.le)
    hval₁ hdx₁ hdy₁] at h3a
  rw [weakJacobi_straddle_outer_rep u.val.2 hs h_in h_out hf₂
    hval₂ hdx₂ hdy₂] at h3a
  exact h3a

/-! ### Character-weighted sums of tests

Inversion commutes with rotations and the gluing phase is rotation-independent.
The explicit three-term sum below produces a class-`j` test using
`xi 3 = conj (zeta 3)`. The construction acts on smooth test functions. -/

/-- The cube of the rotation unit is `1` (the `k = 3` rotation has order 3). -/
lemma rotUnit_third_cubed :
    Complex.exp (((-(2 * Real.pi) / 3 : ℝ) : ℂ) * Complex.I) ^ 3 = 1 := by
  rw [← Complex.exp_nat_mul]
  rw [show ((3 : ℕ) : ℂ) * ((((-(2 * Real.pi) / 3 : ℝ)) : ℂ) * Complex.I) =
    -(2 * Real.pi * Complex.I) from by push_cast; ring]
  rw [Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

/-- `ξ₃^{2j} = ζ₃^j` (the weight arithmetic behind the average's character). -/
lemma xi_two_mul_eq_zeta (j : ℕ) :
    KsIndex.FormIndex.xi 3 ^ (2 * j) = KsIndex.FormIndex.zeta 3 ^ j := by
  have h1 := KsIndex.FormIndex.zeta_pow_mul_xi_pow (by norm_num : 0 < 3) (2 * j)
  have h3 : KsIndex.FormIndex.zeta 3 ^ (3 * j) = 1 := by
    rw [pow_mul, KsIndex.FormIndex.zeta_pow_N (by norm_num), one_pow]
  calc KsIndex.FormIndex.xi 3 ^ (2 * j)
      = KsIndex.FormIndex.zeta 3 ^ (3 * j) * KsIndex.FormIndex.xi 3 ^ (2 * j) := by
        rw [h3, one_mul]
    _ = KsIndex.FormIndex.zeta 3 ^ j *
        (KsIndex.FormIndex.zeta 3 ^ (2 * j) * KsIndex.FormIndex.xi 3 ^ (2 * j)) := by
        rw [show 3 * j = j + 2 * j from by ring, pow_add, mul_assoc]
    _ = KsIndex.FormIndex.zeta 3 ^ j := by rw [h1, mul_one]

/-- The class-`j` average of a test: the explicit three-term `ξ`-weighted sum
of rotates (`k = 3`, so no `Finset` machinery is needed). -/
def straddleAverage (j : ℕ) (ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ψ z + KsIndex.FormIndex.xi 3 ^ j * ψ (planeRotation (-(2 * Real.pi) / 3) z) +
    KsIndex.FormIndex.xi 3 ^ (2 * j) *
      ψ (planeRotation (-(2 * Real.pi) / 3) (planeRotation (-(2 * Real.pi) / 3) z))

lemma straddleAverage_smooth (j : ℕ) {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (straddleAverage j ψ) := by
  have hrot : ContDiff ℝ ∞ (fun z : ℂ =>
      Complex.exp (((-(2 * Real.pi) / 3 : ℝ) : ℂ) * Complex.I) * z) :=
    contDiff_const.mul contDiff_id
  exact (hs.add (contDiff_const.mul (hs.comp hrot))).add
    (contDiff_const.mul (hs.comp (hrot.comp hrot)))

lemma straddleAverage_in (j : ℕ) {ψ : ℂ → ℂ}
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) : straddleAverage j ψ w = 0 := by
  have hn : ∀ z : ℂ, ‖planeRotation (-(2 * Real.pi) / 3) z‖ = ‖z‖ :=
    (planeRotation (-(2 * Real.pi) / 3)).norm_map
  simp only [straddleAverage, h_in w hw, h_in _ ((hn w).trans_le hw),
    h_in _ (((hn _).trans (hn w)).trans_le hw), mul_zero, add_zero]

lemma straddleAverage_out (j : ℕ) {ψ : ℂ → ℂ}
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (w : ℂ) (hw : 2 ≤ ‖w‖) : straddleAverage j ψ w = 0 := by
  have hn : ∀ z : ℂ, ‖planeRotation (-(2 * Real.pi) / 3) z‖ = ‖z‖ :=
    (planeRotation (-(2 * Real.pi) / 3)).norm_map
  simp only [straddleAverage, h_out w hw, h_out _ (hw.trans_eq (hn w).symm),
    h_out _ (hw.trans_eq ((hn _).trans (hn w)).symm), mul_zero, add_zero]

/-- The rotation preserves the cube, so the bad-sector vanishing is inherited
term by term. -/
lemma straddleAverage_sector (j : ℕ) {ψ : ℂ → ℂ}
    (h_sector : ∀ w : ℂ, ‖w‖ = 1 → 0 ≤ (w ^ 3).re → ψ w = 0)
    (w : ℂ) (hw : ‖w‖ = 1) (hre : 0 ≤ (w ^ 3).re) : straddleAverage j ψ w = 0 := by
  have hn : ∀ z : ℂ, ‖planeRotation (-(2 * Real.pi) / 3) z‖ = ‖z‖ :=
    (planeRotation (-(2 * Real.pi) / 3)).norm_map
  have hcube : ∀ z : ℂ, ((planeRotation (-(2 * Real.pi) / 3) z) ^ 3).re = (z ^ 3).re := by
    intro z
    rw [planeRotation_apply, mul_pow, rotUnit_third_cubed, one_mul]
  simp only [straddleAverage, h_sector w hw hre,
    h_sector _ ((hn w).trans hw) (by rw [hcube]; exact hre),
    h_sector _ (((hn _).trans (hn w)).trans hw) (by rw [hcube, hcube]; exact hre),
    mul_zero, add_zero]

/-- **The average carries the class-`j` character** — the convention-sensitive
computation, derived: `R³ = id` reindexes the sum and `ζ^j·ξ^j = 1`,
`ξ^{2j} = ζ^j` close the weights. -/
lemma straddleAverage_char (j : ℕ) (ψ : ℂ → ℂ) (z : ℂ) :
    straddleAverage j ψ (planeRotation (-(2 * Real.pi) / 3) z) =
      KsIndex.FormIndex.zeta 3 ^ j * straddleAverage j ψ z := by
  have hR3 : planeRotation (-(2 * Real.pi) / 3)
      (planeRotation (-(2 * Real.pi) / 3) (planeRotation (-(2 * Real.pi) / 3) z)) = z := by
    simp only [planeRotation_apply]
    calc Complex.exp (((-(2 * Real.pi) / 3 : ℝ) : ℂ) * Complex.I) *
          (Complex.exp (((-(2 * Real.pi) / 3 : ℝ) : ℂ) * Complex.I) *
            (Complex.exp (((-(2 * Real.pi) / 3 : ℝ) : ℂ) * Complex.I) * z))
        = Complex.exp (((-(2 * Real.pi) / 3 : ℝ) : ℂ) * Complex.I) ^ 3 * z := by ring
      _ = z := by rw [rotUnit_third_cubed, one_mul]
  have h1 := KsIndex.FormIndex.zeta_pow_mul_xi_pow (by norm_num : 0 < 3) j
  unfold straddleAverage
  rw [hR3]
  have h2 : KsIndex.FormIndex.zeta 3 ^ j * KsIndex.FormIndex.xi 3 ^ (2 * j) =
      KsIndex.FormIndex.xi 3 ^ j := by
    rw [show 2 * j = j + j from by ring, pow_add, ← mul_assoc, h1, one_mul]
  calc ψ (planeRotation (-(2 * Real.pi) / 3) z) +
        KsIndex.FormIndex.xi 3 ^ j *
          ψ (planeRotation (-(2 * Real.pi) / 3) (planeRotation (-(2 * Real.pi) / 3) z)) +
        KsIndex.FormIndex.xi 3 ^ (2 * j) * ψ z
      = (KsIndex.FormIndex.zeta 3 ^ j * KsIndex.FormIndex.xi 3 ^ j) *
          ψ (planeRotation (-(2 * Real.pi) / 3) z) +
        (KsIndex.FormIndex.zeta 3 ^ j * KsIndex.FormIndex.xi 3 ^ (2 * j)) *
          ψ (planeRotation (-(2 * Real.pi) / 3) (planeRotation (-(2 * Real.pi) / 3) z)) +
        (KsIndex.FormIndex.xi 3 ^ (2 * j)) * ψ z := by rw [h1, h2]; ring
    _ = KsIndex.FormIndex.zeta 3 ^ j *
        (ψ z + KsIndex.FormIndex.xi 3 ^ j * ψ (planeRotation (-(2 * Real.pi) / 3) z) +
          KsIndex.FormIndex.xi 3 ^ (2 * j) *
            ψ (planeRotation (-(2 * Real.pi) / 3) (planeRotation (-(2 * Real.pi) / 3) z))) := by
        rw [xi_two_mul_eq_zeta]
        ring

/-- Every straddling test satisfying the support and sector conditions,
with its rotations summed into class `j`,
produces a pair in `paperSlitCharacterDomain α j` — the full character-domain
test supply from the function-level average. -/
theorem straddleAverage_pair_mem (α : ℝ) (j : ℕ) {ψ : ℂ → ℂ}
    (hs : ContDiff ℝ ∞ ψ)
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (h_sector : ∀ w : ℂ, ‖w‖ = 1 → 0 ≤ (w ^ 3).re → ψ w = 0) :
    straddlePair (Complex.exp ((2 * Real.pi * α) * Complex.I))
        (straddleAverage_smooth j hs) (straddleAverage_in j h_in)
        (straddleAverage_out j h_out) ∈
      paperSlitCharacterDomain α j :=
  straddlePair_mem_paperSlitCharacter α j (straddleAverage_smooth j hs)
    (straddleAverage_in j h_in) (straddleAverage_out j h_out)
    (straddleAverage_sector j h_sector) (straddleAverage_char j ψ)

/-- The across-seam annulus identity at the character-weighted test sum.
The original test satisfies the stated support and sector-vanishing conditions. -/
theorem pair_radical_annulus_identity_average {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    {ψ f₁ f₂ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (h_in : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (h_out : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (h_sector : ∀ w : ℂ, ‖w‖ = 1 → 0 ≤ (w ^ 3).re → ψ w = 0)
    (hval₁ : (valueCLM u.val.1 : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus] f₁)
    (hdx₁ : (dxCLM u.val.1 : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f₁ z 1))
    (hdy₁ : (dyCLM u.val.1 : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f₁ z Complex.I))
    (hf₂ : ∀ z ∈ innerHalfAnnulus, DifferentiableAt ℝ f₂ z)
    (hval₂ : (valueCLM u.val.2 : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus] f₂)
    (hdx₂ : (dxCLM u.val.2 : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f₂ z 1))
    (hdy₂ : (dyCLM u.val.2 : ℂ → ℂ) =ᵐ[volume.restrict innerHalfAnnulus]
      (fun z => fderiv ℝ f₂ z Complex.I)) :
    ((∫ z in innerHalfAnnulus, gradInner f₁ (straddleAverage j ψ) z) -
        ∫ z in innerHalfAnnulus, (potV 3 z : ℂ) * starRingEnd ℂ (f₁ z) *
          straddleAverage j ψ z) +
      (Complex.exp ((2 * Real.pi * α) * Complex.I))⁻¹ *
        ((∫ w in outerHalfAnnulus, gradInner (f₂ ∘ Bracket.σ) (straddleAverage j ψ) w) -
          ∫ w in outerHalfAnnulus, (potV 3 w : ℂ) *
            starRingEnd ℂ ((f₂ ∘ Bracket.σ) w) * straddleAverage j ψ w) = 0 :=
  pair_radical_annulus_identity u hrad (straddleAverage_smooth j hs)
    (straddleAverage_in j h_in) (straddleAverage_out j h_out)
    (straddleAverage_sector j h_sector) (straddleAverage_char j ψ)
    hval₁ hdx₁ hdy₁ hf₂ hval₂ hdx₂ hdy₂

end KsIndex.PaperSlitTransport
