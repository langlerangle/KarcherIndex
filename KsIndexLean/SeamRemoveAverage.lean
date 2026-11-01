module

public import KsIndexLean.GlobalSmoothH1Linear
public import KsIndexLean.PaperSlitInteriorSmooth
public import KsIndexLean.SeamStraddleIdentity
public import KsIndexLean.PaperCharacterTestExtension

@[expose] public section


/-! Removing the character test average at the weak-form level. The field is
already in the character subspace, so averaging any test multiplies its pairing
by three. The seam inversion commutes with the same rotation. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.WeakH1 KsIndex.PaperSlitAdapter KsIndex.FormIndex

lemma globalSmoothH1_straddleAverage (j : ℕ) {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ) :
    globalSmoothH1 (straddleAverage j ψ) (straddleAverage_smooth j hs) =
      globalSmoothH1 ψ hs + xi 3 ^ j • diskRotation (-(2 * Real.pi) / 3) (globalSmoothH1 ψ hs) +
      xi 3 ^ (2 * j) • diskRotation (-(2 * Real.pi) / 3)
        (diskRotation (-(2 * Real.pi) / 3) (globalSmoothH1 ψ hs)) := by
  let R := planeRotation (-(2 * Real.pi) / 3)
  have h1 := hs.comp R.contDiff
  have h2 := h1.comp R.contDiff
  have hc1 : ContDiff ℝ ∞ (xi 3 ^ j • (fun z => ψ (R z))) := contDiff_const.smul h1
  have hc2 : ContDiff ℝ ∞ (xi 3 ^ (2 * j) • (fun z => ψ (R (R z)))) :=
    contDiff_const.smul h2
  have hR := globalSmoothH1_rotation (-(2 * Real.pi) / 3) hs
  have hRR := (globalSmoothH1_rotation (-(2 * Real.pi) / 3) h1).trans
    (congrArg (diskRotation (-(2 * Real.pi) / 3)) hR)
  have hA := (globalSmoothH1_smul (xi 3 ^ j) h1).trans
    (congrArg (fun v : ComplexH1 => xi 3 ^ j • v) hR)
  have hB := (globalSmoothH1_smul (xi 3 ^ (2 * j)) h2).trans
    (congrArg (fun v : ComplexH1 => xi 3 ^ (2 * j) • v) hRR)
  have hAB := (globalSmoothH1_add hs hc1).trans
    (congrArg (fun v : ComplexH1 => globalSmoothH1 ψ hs + v) hA)
  exact (globalSmoothH1_add (hs.add hc1) hc2).trans
    (congrArg₂ (fun v w : ComplexH1 => v + w) hAB hB)

lemma weakJacobi_straddleAverage (j : ℕ) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (zeta 3 ^ j))
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ) :
    weakJacobi (surfacePotential 3) u
      (globalSmoothH1 (straddleAverage j ψ) (straddleAverage_smooth j hs)) =
      3 * weakJacobi (surfacePotential 3) u (globalSmoothH1 ψ hs) := by
  have hrot := surfaceJacobi_character_test_rotation 3 (-(2 * Real.pi) / 3)
    (zeta 3 ^ j) (paperCharacter_norm j) u ((mem_weakCharacterDomain _ _ u).mp hu)
  rw [globalSmoothH1_straddleAverage j hs]
  simp only [weakJacobi_add_right, weakJacobi_smul_right, hrot]
  have h1 : xi 3 ^ j * zeta 3 ^ j = 1 := by
    rw [mul_comm]; exact zeta_pow_mul_xi_pow (by norm_num) j
  have h2 : xi 3 ^ (2 * j) * (zeta 3 ^ j * zeta 3 ^ j) = 1 := by
    rw [xi_two_mul_eq_zeta]
    calc
      zeta 3 ^ j * (zeta 3 ^ j * zeta 3 ^ j) = (zeta 3 ^ j) ^ 3 := by ring
      _ = 1 := paperCharacter_cube j
  linear_combination
    h1 * weakJacobi (surfacePotential 3) u (globalSmoothH1 ψ hs) +
    h2 * weakJacobi (surfacePotential 3) u (globalSmoothH1 ψ hs)

lemma straddleAverage_sigma (j : ℕ) (ψ : ℂ → ℂ) :
    (fun z => straddleAverage j ψ (Bracket.σ z)) =
      straddleAverage j (fun z => ψ (Bracket.σ z)) := by
  have hc (z : ℂ) : Bracket.σ (planeRotation (-(2 * Real.pi) / 3) z) =
      planeRotation (-(2 * Real.pi) / 3) (Bracket.σ z) := by
    simp only [planeRotation_apply]
    exact sigma_rotation_comm (Complex.norm_exp_ofReal_mul_I _) z
  funext z
  simp only [straddleAverage, hc]

/-- Every smooth straddling test is allowed, without a rotation-character
hypothesis on the test. The inverse phase is unchanged. -/
theorem pair_radical_straddle_all_tests {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (hsector : ∀ w : ℂ, ‖w‖ = 1 → 0 ≤ (w ^ 3).re → ψ w = 0) :
    weakJacobi (surfacePotential 3) u.val.1 (globalSmoothH1 ψ hs) +
      (Complex.exp ((2 * Real.pi * α) * Complex.I))⁻¹ *
        weakJacobi (surfacePotential 3) u.val.2
          (globalSmoothH1 (fun z => ψ (Bracket.σ z)) (straddle_pull_smooth hs hi ho)) = 0 := by
  have h := pair_radical_straddle u hrad (straddleAverage_smooth j hs)
    (straddleAverage_in j hi) (straddleAverage_out j ho)
    (straddleAverage_sector j hsector) (straddleAverage_char j ψ)
  have hemb : globalSmoothH1 (fun z => straddleAverage j ψ (Bracket.σ z))
      (straddle_pull_smooth (straddleAverage_smooth j hs)
        (straddleAverage_in j hi) (straddleAverage_out j ho)) =
      globalSmoothH1 (straddleAverage j (fun z => ψ (Bracket.σ z)))
        (straddleAverage_smooth j (straddle_pull_smooth hs hi ho)) := by
    congr 1
    exact straddleAverage_sigma j ψ
  rw [hemb, weakJacobi_straddleAverage j u.val.1 u.property.2.1 hs,
    weakJacobi_straddleAverage j u.val.2 u.property.2.2 (straddle_pull_smooth hs hi ho)] at h
  linear_combination (1 / 3 : ℂ) * h

/-- The unaveraged annulus identity for actual smooth disk representatives.
Only the geometric support restrictions remain on the test. -/
theorem pair_radical_annulus_identity_all_tests {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    {f g ψ : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (disk : Set ℂ))
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (disk : Set ℂ))
    (ha : valueCLM u.val.1 =ᵐ[volume.restrict (disk : Set ℂ)] f)
    (hb : valueCLM u.val.2 =ᵐ[volume.restrict (disk : Set ℂ)] g)
    (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (hsector : ∀ w : ℂ, ‖w‖ = 1 → 0 ≤ (w ^ 3).re → ψ w = 0) :
    ((∫ z in innerHalfAnnulus, KsIndex.GradOrtho.gradInner f ψ z) -
        ∫ z in innerHalfAnnulus, (KsIndex.Surface.potV 3 z : ℂ) * starRingEnd ℂ (f z) * ψ z) +
      (Complex.exp ((2 * Real.pi * α) * Complex.I))⁻¹ *
        ((∫ w in outerHalfAnnulus, KsIndex.GradOrtho.gradInner (g ∘ Bracket.σ) ψ w) -
          ∫ w in outerHalfAnnulus, (KsIndex.Surface.potV 3 w : ℂ) *
            starRingEnd ℂ ((g ∘ Bracket.σ) w) * ψ w) = 0 := by
  obtain ⟨hfx, hfy⟩ := Weq.disk_smooth_representative_derivatives u.val.1 hf ha
  obtain ⟨hgx, hgy⟩ := Weq.disk_smooth_representative_derivatives u.val.2 hg hb
  have hsub : innerHalfAnnulus ⊆ (disk : Set ℂ) := by
    intro z hz
    exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hz.2)
  have hm := ae_mono (Measure.restrict_mono (μ := (volume : Measure ℂ)) hsub le_rfl)
  have h := pair_radical_straddle_all_tests u hrad hs hi ho hsector
  rw [weakJacobi_inner_localized u.val.1 hs (fun z hz => hi z hz.le)
    (ha.filter_mono hm) (hfx.filter_mono hm) (hfy.filter_mono hm)] at h
  rw [weakJacobi_straddle_outer_rep u.val.2 hs hi ho
    (fun z hz => (hg.contDiffAt (disk.isOpen.mem_nhds (hsub hz))).differentiableAt (by simp))
    (hb.filter_mono hm) (hgx.filter_mono hm) (hgy.filter_mono hm)] at h
  exact h

end KsIndex.PaperSlitTransport
