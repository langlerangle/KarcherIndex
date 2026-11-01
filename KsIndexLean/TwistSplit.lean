module

/-
# Twisted copy-swap and the boundary-continuous character split

For `k ≥ 1` and `ζ² = 1`, `swapTwE_mem_DomTw_c` proves that the twisted
copy-swap preserves `DomTw_c k ζ = DomTw k ζ ∩ BdyCont`. Boundary continuity
supplies the raw circle-value identities used in this proof: the two copies
agree on `arc k 1`, and `v₁ = ζ v₀` on `arc k 0`.

Writing `σ w = 1 / conj w`, these identities give, near the respective seam arcs,
`glue (swapTwF ζ v) 0 = ζ · (glue v 0) ∘ σ` and
`glueTw ζ (swapTwF ζ v) = (glueTw ζ v) ∘ σ`. The latter uses `ζ² = 1`.
The reflection is smooth near the unit circle and fixes it pointwise, so
these local identities preserve the required seam smoothness. The argument
uses `BdyCont`; it does not establish stability of the unrestricted `DomTw`.

For `k ≥ 2`, `formIndex_swapTw_split_c` splits the form index of a rotation
block in `DomTw_c` into the indices of its `+1` and `-1` copy-swap eigenspaces.
Its explicit twist assumptions are `ζ² = 1`, `‖ζ‖ = 1` and `ζ ≠ 0`; the
rotation parameters `a` and `μ` are arbitrary in this statement. The proof
combines domain stability with `formIndex_swapTw_split`.
-/
public import KsIndexLean.TwistRetract

@[expose] public section


noncomputable section

open Complex MeasureTheory Metric Filter Topology
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.Bracket KsIndex.Twisted
  KsIndex.FormIndex
open scoped ContDiff

namespace KsIndex.TwistSwap

variable {k : ℕ}

/-! ### The circle reflection `σ w = 1/w̄` -/

lemma sigmaR_fix {w₀ : ℂ} (hw₀ : ‖w₀‖ = 1) : 1 / (starRingEnd ℂ) w₀ = w₀ := by
  have hw0 : w₀ ≠ 0 := by rintro rfl; simp at hw₀
  rw [one_div]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [Complex.conj_mul', hw₀]; norm_num

lemma sigmaR_contDiffAt {w₀ : ℂ} (hw₀ : ‖w₀‖ = 1) :
    ContDiffAt ℝ ∞ (fun w => 1 / (starRingEnd ℂ) w) w₀ := by
  have hw0 : w₀ ≠ 0 := by rintro rfl; simp at hw₀
  have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => (starRingEnd ℂ) w) w₀ := by
    have := (Complex.conjCLE.contDiff (n := ∞)).contDiffAt (x := w₀)
    exact this.congr_of_eventuallyEq (Eventually.of_forall fun w => by simp)
  have h2 : ContDiffAt ℝ ∞ (Inv.inv : ℂ → ℂ) ((starRingEnd ℂ) w₀) :=
    contDiffAt_inv ℝ (by simpa using hw0)
  simp only [one_div]
  exact h2.comp w₀ h1

lemma norm_sigmaR {w : ℂ} (_hw : w ≠ 0) : ‖(1 / (starRingEnd ℂ) w : ℂ)‖ = ‖w‖⁻¹ := by
  rw [norm_div, norm_one, Complex.norm_conj, one_div]

lemma sigmaR_involutive {w : ℂ} (_hw : w ≠ 0) :
    1 / (starRingEnd ℂ) (1 / (starRingEnd ℂ) w) = w := by
  rw [map_div₀, map_one, Complex.conj_conj, one_div_one_div]

lemma exterior_neBot {w : ℂ} (hw : ‖w‖ = 1) : (𝓝[{z : ℂ | 1 < ‖z‖}] w).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  refine ⟨((1 + ε / 2 : ℝ) : ℂ) * w, ?_, ?_⟩
  · change 1 < ‖((1 + ε / 2 : ℝ) : ℂ) * w‖
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hw, mul_one]
    linarith
  · rw [dist_eq_norm]
    have : w - ((1 + ε / 2 : ℝ) : ℂ) * w = ((-(ε / 2) : ℝ) : ℂ) * w := by push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonpos (by linarith), hw, mul_one]
    linarith

/-! ### Boundary seam matching -/

/-- On the closed disk, if `G` reads copy `A` inside and `c · (B ∘ σ)` outside and is continuous at
a circle point `w`, then the raw circle values satisfy the seam matching `A w = c · B w`.  This is
where continuity of `B` up to the circle identifies the exterior limit with `B w`. -/
lemma glue_circle_match {A B G : ℂ → ℂ} {c : ℂ} {w : ℂ} (hw : ‖w‖ = 1)
    (hBc : ContinuousWithinAt B (Metric.closedBall 0 1) w) (hG : ContinuousAt G w)
    (hin : ∀ z, ‖z‖ ≤ 1 → G z = A z)
    (hout : ∀ z, 1 < ‖z‖ → G z = c * B (1 / (starRingEnd ℂ) z)) :
    A w = c * B w := by
  have hGw : G w = A w := hin w (le_of_eq hw)
  have hσfix : (1 / (starRingEnd ℂ) w) = w := sigmaR_fix hw
  have hext : Tendsto (fun z => 1 / (starRingEnd ℂ) z) (𝓝[{z : ℂ | 1 < ‖z‖}] w)
      (𝓝[Metric.closedBall 0 1] w) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h := (sigmaR_contDiffAt hw).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (s := {z : ℂ | 1 < ‖z‖}))
      rwa [hσfix] at h
    · filter_upwards [self_mem_nhdsWithin] with z hz
      rw [Metric.mem_closedBall, dist_zero_right, norm_div, norm_one, Complex.norm_conj, one_div,
        inv_le_one_iff₀]
      right; exact le_of_lt hz
  have hBt : Tendsto B (𝓝[Metric.closedBall 0 1] w) (𝓝 (B w)) := hBc
  have hBout : Tendsto (fun z => c * B (1 / (starRingEnd ℂ) z)) (𝓝[{z : ℂ | 1 < ‖z‖}] w)
      (𝓝 (c * B w)) := by
    have h1 : Tendsto (fun z => B (1 / (starRingEnd ℂ) z)) (𝓝[{z : ℂ | 1 < ‖z‖}] w) (𝓝 (B w)) := by
      simpa only [Function.comp_def] using hBt.comp hext
    exact h1.const_mul c
  have hGout : Tendsto G (𝓝[{z : ℂ | 1 < ‖z‖}] w) (𝓝 (G w)) :=
    hG.tendsto.mono_left nhdsWithin_le_nhds
  have hGeqOut : G =ᶠ[𝓝[{z : ℂ | 1 < ‖z‖}] w] fun z => c * B (1 / (starRingEnd ℂ) z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hout z hz
  have := exterior_neBot hw
  have huniq := tendsto_nhds_unique (hGout.congr' hGeqOut) hBout
  rw [hGw] at huniq
  exact huniq

/-- Arc-1 seam matching: `v 0 w = v 1 w` at a circle point where `glue v 0` is continuous. -/
lemma seam_match_glue {v : ZMod (2 * 1) → ℂ → ℂ}
    (hbc : ∀ n, ContinuousOn (v n) (Metric.closedBall 0 1)) {w : ℂ} (hw : ‖w‖ = 1)
    (hG : ContinuousAt (glue v 0) w) : v 0 w = v 1 w := by
  have h := glue_circle_match (A := v 0) (B := v 1) (c := 1) (G := glue v 0) hw
    ((hbc 1).continuousWithinAt (mem_closedBall_zero_iff.mpr (le_of_eq hw))) hG
    (fun z hz => by simp only [glue, if_pos hz])
    (fun z hz => by simp only [glue, if_neg (not_le.mpr hz)]; rw [zero_add, one_mul])
  rwa [one_mul] at h

/-- Arc-0 seam matching: `v 1 w = ζ · v 0 w` at a circle point where `glueTw ζ v` is continuous. -/
lemma seam_match_glueTw {ζ : ℂ} {v : ZMod (2 * 1) → ℂ → ℂ}
    (hbc : ∀ n, ContinuousOn (v n) (Metric.closedBall 0 1)) {w : ℂ} (hw : ‖w‖ = 1)
    (hG : ContinuousAt (glueTw ζ v) w) : v 1 w = ζ * v 0 w :=
  glue_circle_match (A := v 1) (B := v 0) (c := ζ) (G := glueTw ζ v) hw
    ((hbc 0).continuousWithinAt (mem_closedBall_zero_iff.mpr (le_of_eq hw))) hG
    (fun z hz => by simp only [glueTw, if_pos hz])
    (fun z hz => by simp only [glueTw, if_neg (not_le.mpr hz)])

/-! ### The reflection identities on the seam neighbourhoods -/

/-- `glue (swapTwF ζ v) 0 = ζ · (glue v 0) ∘ σ` on a neighbourhood of each `arc k 1` point. -/
lemma glue0_swapTwF_eventuallyEq (hk : 1 ≤ k) {ζ : ℂ} {v : ZMod (2 * 1) → ℂ → ℂ}
    (hbc : ∀ n, ContinuousOn (v n) (Metric.closedBall 0 1))
    (hc2 : ∀ w ∈ seamArc k 1 0, ContDiffAt ℝ ∞ (glue v 0) w) {w₀ : ℂ} (hw₀ : w₀ ∈ arc k 1) :
    glue (swapTwF ζ v) 0 =ᶠ[𝓝 w₀] fun z => ζ * glue v 0 (1 / (starRingEnd ℂ) z) := by
  have hOopen : IsOpen {w : ℂ | 0 < (w ^ k).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_pow k))
  have hw₀O : w₀ ∈ {w : ℂ | 0 < (w ^ k).re} := by
    have h2 := hw₀.2; rw [pow_one, neg_one_mul] at h2
    change 0 < (w₀ ^ k).re; linarith
  refine eventuallyEq_of_mem (hOopen.mem_nhds hw₀O) fun w hwO => ?_
  have hwO' : 0 < (w ^ k).re := hwO
  have hwne : w ≠ 0 := by
    rintro rfl; rw [zero_pow (by omega : k ≠ 0), Complex.zero_re] at hwO'
    exact absurd hwO' (lt_irrefl 0)
  have e1 : (0 + 1 : ZMod (2 * 1)) = 1 := by decide
  have e3 : (1 + 1 : ZMod (2 * 1)) = 0 := by decide
  have hσn : ‖(1 / (starRingEnd ℂ) w : ℂ)‖ = ‖w‖⁻¹ := norm_sigmaR hwne
  have hσσ : (1 / (starRingEnd ℂ) (1 / (starRingEnd ℂ) w)) = w := sigmaR_involutive hwne
  have h0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hwne
  simp only [glue, swapTwF, e1, e3]
  rcases lt_trichotomy ‖w‖ 1 with hlt | heq | hgt
  · have hσgt : ¬ ‖(1 / (starRingEnd ℂ) w : ℂ)‖ ≤ 1 := by
      rw [hσn, not_le]; exact (one_lt_inv₀ h0).mpr hlt
    rw [if_pos (le_of_lt hlt), if_neg hσgt, hσσ]
  · have hσle : ‖(1 / (starRingEnd ℂ) w : ℂ)‖ ≤ 1 := by rw [hσn, heq]; norm_num
    have hwarc : w ∈ arc k 1 := ⟨heq, by rw [pow_one, neg_one_mul]; linarith⟩
    have hmatch : v 0 w = v 1 w :=
      seam_match_glue hbc heq ((hc2 w (by rw [seamArc_one_zero]; exact hwarc)).continuousAt)
    rw [if_pos (le_of_eq heq), if_pos hσle, sigmaR_fix heq, hmatch]
  · have hσlt : ‖(1 / (starRingEnd ℂ) w : ℂ)‖ ≤ 1 := by
      rw [hσn, inv_le_one_iff₀]; right; exact le_of_lt hgt
    rw [if_neg (not_le.mpr hgt), if_pos hσlt]

/-- `glueTw ζ (swapTwF ζ v) = (glueTw ζ v) ∘ σ` on a neighbourhood of each `arc k 0` point
under the hypothesis `ζ² = 1`. -/
lemma glueTw_swapTwF_eventuallyEq (hk : 1 ≤ k) {ζ : ℂ} (hζ2 : ζ ^ 2 = 1)
    {v : ZMod (2 * 1) → ℂ → ℂ} (hbc : ∀ n, ContinuousOn (v n) (Metric.closedBall 0 1))
    (hc3 : ∀ w ∈ seamArc k 1 1, ContDiffAt ℝ ∞ (glueTw ζ v) w) {w₀ : ℂ} (hw₀ : w₀ ∈ arc k 0) :
    glueTw ζ (swapTwF ζ v) =ᶠ[𝓝 w₀] fun z => glueTw ζ v (1 / (starRingEnd ℂ) z) := by
  have hOopen : IsOpen {w : ℂ | (w ^ k).re < 0} :=
    isOpen_lt (Complex.continuous_re.comp (continuous_pow k)) continuous_const
  have hw₀O : w₀ ∈ {w : ℂ | (w ^ k).re < 0} := by
    have h2 := hw₀.2; rw [pow_zero, one_mul] at h2
    change (w₀ ^ k).re < 0; exact h2
  refine eventuallyEq_of_mem (hOopen.mem_nhds hw₀O) fun w hwO => ?_
  have hwO' : (w ^ k).re < 0 := hwO
  have hwne : w ≠ 0 := by
    rintro rfl; rw [zero_pow (by omega : k ≠ 0), Complex.zero_re] at hwO'
    exact absurd hwO' (lt_irrefl 0)
  have e1 : (0 + 1 : ZMod (2 * 1)) = 1 := by decide
  have e3 : (1 + 1 : ZMod (2 * 1)) = 0 := by decide
  have hσn : ‖(1 / (starRingEnd ℂ) w : ℂ)‖ = ‖w‖⁻¹ := norm_sigmaR hwne
  have hσσ : (1 / (starRingEnd ℂ) (1 / (starRingEnd ℂ) w)) = w := sigmaR_involutive hwne
  have h0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hwne
  simp only [glueTw, swapTwF, e1, e3]
  rcases lt_trichotomy ‖w‖ 1 with hlt | heq | hgt
  · have hσgt : ¬ ‖(1 / (starRingEnd ℂ) w : ℂ)‖ ≤ 1 := by
      rw [hσn, not_le]; exact (one_lt_inv₀ h0).mpr hlt
    rw [if_pos (le_of_lt hlt), if_neg hσgt, hσσ]
  · have hσle : ‖(1 / (starRingEnd ℂ) w : ℂ)‖ ≤ 1 := by rw [hσn, heq]; norm_num
    have hwarc : w ∈ arc k 0 := ⟨heq, by rw [pow_zero, one_mul]; exact hwO'⟩
    have hmatch : v 1 w = ζ * v 0 w :=
      seam_match_glueTw hbc heq ((hc3 w (by rw [seamArc_one_one]; exact hwarc)).continuousAt)
    rw [if_pos (le_of_eq heq), if_pos hσle, sigmaR_fix heq, hmatch]
  · have hσlt : ‖(1 / (starRingEnd ℂ) w : ℂ)‖ ≤ 1 := by
      rw [hσn, inv_le_one_iff₀]; right; exact le_of_lt hgt
    rw [if_neg (not_le.mpr hgt), if_pos hσlt, ← mul_assoc, ← pow_two, hζ2, one_mul]

/-! ### The twisted swap preserves `DomTw_c` -/

theorem swapTwE_mem_DomTw_c (hk : 1 ≤ k) {ζ : ℂ} (hζ2 : ζ ^ 2 = 1) {U : ZMod (2 * 1) × ℂ → ℂ}
    (hU : U ∈ DomTw_c k ζ) : swapTwE ζ U ∈ DomTw_c k ζ := by
  obtain ⟨hUD, hUB⟩ := Submodule.mem_inf.mp hU
  obtain ⟨⟨hc1, hc2, hc3, hc4⟩, hsupp⟩ := mem_DomTw.mp hUD
  have hbc : ∀ n, ContinuousOn ((uncurryE 1).symm U n) (Metric.closedBall 0 1) := mem_BdyCont.mp hUB
  set v := (uncurryE 1).symm U with hv
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_DomTw, uncurry_symm_swapTwE, ← hv]
    refine ⟨⟨fun n => ?_, fun w hw => ?_, fun w hw => ?_, fun n w hw => ?_⟩, ?_⟩
    · change ContDiffOn ℝ ∞ (fun w => ζ • v (n + 1) w) disk
      exact (hc1 (n + 1)).const_smul ζ
    · have hwarc : w ∈ arc k 1 := by rw [← seamArc_one_zero]; exact hw
      have hrhs : ContDiffAt ℝ ∞ (fun z => ζ * glue v 0 (1 / (starRingEnd ℂ) z)) w := by
        have hg : ContDiffAt ℝ ∞ (glue v 0) (1 / (starRingEnd ℂ) w) := by
          rw [sigmaR_fix hwarc.1]; exact hc2 w hw
        have hcomp : ContDiffAt ℝ ∞ (fun z => glue v 0 (1 / (starRingEnd ℂ) z)) w := by
          have h := hg.comp w (sigmaR_contDiffAt hwarc.1)
          simpa only [Function.comp_def] using h
        exact contDiffAt_const.mul hcomp
      exact hrhs.congr_of_eventuallyEq (glue0_swapTwF_eventuallyEq hk hbc hc2 hwarc)
    · have hwarc : w ∈ arc k 0 := by rw [← seamArc_one_one]; exact hw
      have hrhs : ContDiffAt ℝ ∞ (fun z => glueTw ζ v (1 / (starRingEnd ℂ) z)) w := by
        have hg : ContDiffAt ℝ ∞ (glueTw ζ v) (1 / (starRingEnd ℂ) w) := by
          rw [sigmaR_fix hwarc.1]; exact hc3 w hw
        have h := hg.comp w (sigmaR_contDiffAt hwarc.1)
        simpa only [Function.comp_def] using h
      exact hrhs.congr_of_eventuallyEq (glueTw_swapTwF_eventuallyEq hk hζ2 hbc hc3 hwarc)
    · change ζ * v (n + 1) w = 0
      rw [hc4 (n + 1) w hw, mul_zero]
    · obtain ⟨ε, hε, hz⟩ := hsupp
      exact ⟨ε, hε, fun n w hw => by change ζ * v (n + 1) w = 0; rw [hz (n + 1) w hw, mul_zero]⟩
  · rw [mem_BdyCont]
    intro n
    change ContinuousOn (fun w => ζ • v (n + 1) w) (Metric.closedBall 0 1)
    exact (hbc (n + 1)).const_smul ζ

/-! ### The character split on the boundary-continuous domain -/

theorem formIndex_swapTw_split_c (hk : 2 ≤ k) {ζ a μ : ℂ} (hζ2 : ζ ^ 2 = 1) (hζ1 : ‖ζ‖ = 1)
    (hζ0 : ζ ≠ 0) :
    formIndex (Qs k 1) (DomTw_c k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ)
      = formIndex (Qs k 1)
          ((DomTw_c k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ) ⊓
            Module.End.eigenspace (swapTwE ζ) 1)
        + formIndex (Qs k 1)
          ((DomTw_c k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ) ⊓
            Module.End.eigenspace (swapTwE ζ) (-1)) := by
  have hEq : DomTw_c k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ
      = DomTw k ζ ⊓ (BdyCont ⊓ Module.End.eigenspace (rotE 1 a) μ) := by
    rw [DomTw_c, inf_assoc]
  have hD : ∀ U ∈ DomTw k ζ ⊓ (BdyCont ⊓ Module.End.eigenspace (rotE 1 a) μ),
      swapTwE ζ U ∈ DomTw k ζ ⊓ (BdyCont ⊓ Module.End.eigenspace (rotE 1 a) μ) := by
    intro U hU
    obtain ⟨hUD, hUBE⟩ := Submodule.mem_inf.mp hU
    obtain ⟨hUB, hUE⟩ := Submodule.mem_inf.mp hUBE
    have hc : swapTwE ζ U ∈ DomTw_c k ζ :=
      swapTwE_mem_DomTw_c (by omega) hζ2 (Submodule.mem_inf.mpr ⟨hUD, hUB⟩)
    obtain ⟨hcD, hcB⟩ := Submodule.mem_inf.mp hc
    exact Submodule.mem_inf.mpr ⟨hcD, Submodule.mem_inf.mpr ⟨hcB, swapTwE_mem_rot hUE⟩⟩
  rw [hEq, formIndex_swapTw_split hk hζ2 hζ1 hζ0 (BdyCont ⊓ Module.End.eigenspace (rotE 1 a) μ) hD]

end KsIndex.TwistSwap
