module

public import KsIndexLean.NullityTrace
public import KsIndexLean.NaturalCoreGreenData
public import KsIndexLean.SmoothDiskGreen

@[expose] public section


/-!
# Green pairing of sector fields with natural-core tests

The copy-`0` field of a bounded Jacobi symmetry sector has a smooth local
extension across each open boundary arc: `glue u 0` at arc `1`, and
`(glue u 3) ∘ σ` at arc `0`, where `σ(z) = 1 / conj z`. Even reflection parity
gives `F ∘ σ = F` locally. Differentiating at a unit-circle point, where the radial
direction is sent to its negative, proves vanishing of the radial derivative.

For `k ≥ 2`, `sector_core_green` expresses the weak Jacobi pairing with a
natural-core test as a boundary flux integral. The test's vanishing near
punctures makes the flux product continuous there; no smooth extension of the
sector field through a puncture is asserted.

For reflection indices `s₁, s₀ < 2`, `sector_pairing_zero` uses the matching
flags `decide (s₁ = 0)` and `decide (s₀ = 0)`. On even-parity arcs the radial
flux vanishes; on odd-parity arcs the test vanishes; at punctures the test also
vanishes. Thus the pairing is zero against these natural-core tests. Extension
to all mixed-domain tests by density is established separately.
-/

noncomputable section
namespace KsIndex.NullityDecomp
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.SurfaceForm KsIndex.WeakH1 KsIndex.Trace
open KsIndex.FaithfulInjection Complex MeasureTheory Filter Topology
open KsIndex.FormIndex
open scoped ContDiff

variable {k r s₁ s₀ : ℕ}

/-! ### Weak derivative representatives -/

lemma energySmoothToH1_dx {k m : ℕ} (u : ↥(EnergySmooth k m)) (n : ZMod (2 * m)) :
    (dxCLM (energySmoothToH1 u n) : ℂ → ℂ)
      =ᵐ[volume.restrict (KsIndex.WeakH1.disk : Set ℂ)]
      (fun w => fderiv ℝ (u.val n) w 1) := by
  have h := (smoothToH1_coordinates (energySmoothData u n)).2.1
  rw [show dxLp (smoothToH1 (energySmoothData u n)) =
      dxCLM (energySmoothToH1 u n) from rfl] at h
  rw [h]
  exact MemLp.coeFn_toLp _

lemma energySmoothToH1_dy {k m : ℕ} (u : ↥(EnergySmooth k m)) (n : ZMod (2 * m)) :
    (dyCLM (energySmoothToH1 u n) : ℂ → ℂ)
      =ᵐ[volume.restrict (KsIndex.WeakH1.disk : Set ℂ)]
      (fun w => fderiv ℝ (u.val n) w Complex.I) := by
  have h := (smoothToH1_coordinates (energySmoothData u n)).2.2
  rw [show dyLp (smoothToH1 (energySmoothData u n)) =
      dyCLM (energySmoothToH1 u n) from rfl] at h
  rw [h]
  exact MemLp.coeFn_toLp _


/-! ### `ζ₂`-parity helpers -/

lemma zeta_two_pow_even {s : ℕ} (h : s % 2 = 0) : zeta 2 ^ s = 1 := by
  obtain ⟨t, rfl⟩ := (Nat.even_iff.mpr h)
  rw [← two_mul, pow_mul, KsIndex.Bracket.zeta_two, neg_one_sq, one_pow]

lemma zeta_two_pow_odd {s : ℕ} (h : s % 2 = 1) : zeta 2 ^ s = -1 := by
  obtain ⟨t, rfl⟩ := (Nat.odd_iff.mpr h)
  rw [pow_succ, pow_mul, KsIndex.Bracket.zeta_two, neg_one_sq, one_pow, one_mul]

/-! ### Collar `C¹` (indeed `C^∞`) extensions at open-arc points -/

/-- At an `arc k 1` point, `glue u 0` is a full-neighbourhood smooth extension of the
copy-`0` field from the closed-disk side. -/
lemma sector_extension_arc1 {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) {w : ℂ} (hw : w ∈ arc k 1) :
    ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w ∧
      (∀ᶠ z in 𝓝 w, ‖z‖ ≤ 1 → (uncurryE 2).symm W 0 z = F z) ∧
      (∀ᶠ z in 𝓝 w, F (1 / (starRingEnd ℂ) z) = zeta 2 ^ s₁ * F z) := by
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, -, -, -, hsv⟩ := sector_field_mem hW
  have hws : w ∈ seamArc k 2 (0 : ZMod (2 * 2)) := by
    obtain ⟨hz1, hz2⟩ := hw
    refine ⟨hz1, ?_⟩
    rw [show (parity 2 ((0 : ZMod (2 * 2)) + 1)).val = 1 from by decide]
    simpa using hz2
  have hw1 : ‖w‖ = 1 := hw.1
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw1
    exact zero_ne_one hw1
  refine ⟨glue ((uncurryE 2).symm W) 0, hsm2 0 w hws, ?_, ?_⟩
  · filter_upwards with z hz
    simp [glue, hz]
  · -- the σ-parity of the glue near the arc, by the three-sided case analysis
    have hZ : {z : ℂ | z ≠ 0} ∈ 𝓝 w := (isOpen_ne (x := (0 : ℂ))).mem_nhds hw0
    have hT : {z : ℂ | (-1 : ℝ) ^ 1 * ((z ^ k).re) < 0} ∈ 𝓝 w :=
      (isOpen_signSet k 1).mem_nhds hw.2
    filter_upwards [hZ, hT] with z hz0 hzT
    set u0 := (uncurryE 2).symm W with hu0
    have hcopy1 : ∀ y, u0 1 y = zeta 2 ^ s₁ * u0 0 y := fun y => sector_copy_one hW y
    rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
    · -- inside: LHS else-branch through `σσ = z`; RHS if-branch
      have hσn : 1 < ‖1 / (starRingEnd ℂ) z‖ := by
        rw [norm_sigma]
        exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hz0, h1⟩
      simp only [glue]
      rw [ite_eq_right (not_le.mpr hσn), sigma_sigma, ite_eq_left (le_of_lt h1),
        show (0 : ZMod (2 * 2)) + 1 = 1 from by decide]
      exact hcopy1 z
    · -- on the circle: `σ z = z`, `z` is an arc-1 point; both parities close
      have hσz := sigma_circle h1
      have hzarc : z ∈ arc k 1 := ⟨h1, hzT⟩
      simp only [glue, hσz]
      rw [ite_eq_left (le_of_eq h1)]
      rcases (by omega : s₁ % 2 = 0 ∨ s₁ % 2 = 1) with hpar | hpar
      · rw [zeta_two_pow_even hpar, one_mul]
      · rw [zeta_two_pow_odd hpar]
        have hv' : u0 0 z = 0 := sector_vanishes_arc1 hW (zeta_two_pow_odd hpar) hzarc
        rw [hv']
        ring
    · -- outside: LHS if-branch at `σ z`; RHS else-branch, closed by `ζ² = 1`
      have hσn : ‖1 / (starRingEnd ℂ) z‖ < 1 := by
        rw [norm_sigma]
        exact inv_lt_one_of_one_lt₀ h1
      simp only [glue]
      rw [ite_eq_left (le_of_lt hσn), ite_eq_right (not_le.mpr h1),
        show (0 : ZMod (2 * 2)) + 1 = 1 from by decide]
      have hz2 : zeta 2 ^ s₁ * zeta 2 ^ s₁ = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, KsIndex.Bracket.zeta_two, neg_one_sq, one_pow]
      rw [hcopy1 (1 / (starRingEnd ℂ) z), ← mul_assoc, hz2, one_mul]

/-- At an `arc k 0` point, `(glue u 3) ∘ σ` is a full-neighbourhood smooth extension of the
copy-`0` field from the closed-disk side. -/
lemma sector_extension_arc0 {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) {w : ℂ} (hw : w ∈ arc k 0) :
    ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w ∧
      (∀ᶠ z in 𝓝 w, ‖z‖ ≤ 1 → (uncurryE 2).symm W 0 z = F z) ∧
      (∀ᶠ z in 𝓝 w, F (1 / (starRingEnd ℂ) z) = zeta 2 ^ s₀ * F z) := by
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, -, -, -, hsv⟩ := sector_field_mem hW
  have hws : w ∈ seamArc k 2 (3 : ZMod (2 * 2)) := by
    obtain ⟨hz1, hz2⟩ := hw
    refine ⟨hz1, ?_⟩
    rw [show (parity 2 ((3 : ZMod (2 * 2)) + 1)).val = 0 from by decide]
    simpa using hz2
  have hw1 : ‖w‖ = 1 := hw.1
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw1
    exact zero_ne_one hw1
  -- the composite extension `glue u 3 ∘ σ`
  have hσw : (1 / (starRingEnd ℂ) w) = w := sigma_circle hw1
  have hσ : ContDiffAt ℝ ∞ (fun z : ℂ => 1 / (starRingEnd ℂ) z) w := by
    simp only [one_div]
    have hconj : ContDiffAt ℝ ∞ (fun z : ℂ => (starRingEnd ℂ) z) w :=
      Complex.conjCLE.contDiff.contDiffAt
    have hne : (starRingEnd ℂ) w ≠ 0 := by simpa using hw0
    exact (contDiffAt_inv ℝ hne).comp w hconj
  have hglue3 : ContDiffAt ℝ ∞ (glue ((uncurryE 2).symm W) 3) (1 / (starRingEnd ℂ) w) := by
    rw [hσw]
    exact hsm2 3 w hws
  have hF : ContDiffAt ℝ ∞
      (fun z => glue ((uncurryE 2).symm W) 3 (1 / (starRingEnd ℂ) z)) w := by
    have h := hglue3.comp w hσ
    rw [Function.comp_def] at h
    exact h
  refine ⟨fun z => glue ((uncurryE 2).symm W) 3 (1 / (starRingEnd ℂ) z), hF, ?_, ?_⟩
  · -- closed-side agreement through inversion and matching seam values
    have hZ : {z : ℂ | z ≠ 0} ∈ 𝓝 w := (isOpen_ne (x := (0 : ℂ))).mem_nhds hw0
    have hT : {z : ℂ | (-1 : ℝ) ^ 0 * ((z ^ k).re) < 0} ∈ 𝓝 w :=
      (isOpen_signSet k 0).mem_nhds hw.2
    filter_upwards [hZ, hT] with z hz0 hzT hz1
    rcases eq_or_lt_of_le hz1 with hz1' | hz1'
    · have hσz : (1 / (starRingEnd ℂ) z) = z := sigma_circle hz1'
      rw [hσz]
      simp only [glue]
      rw [ite_eq_left (le_of_eq hz1')]
      have hzs : z ∈ seamArc k 2 (3 : ZMod (2 * 2)) := by
        refine ⟨hz1', ?_⟩
        rw [show (parity 2 ((3 : ZMod (2 * 2)) + 1)).val = 0 from by decide]
        simpa using hzT
      have hs := hsv (3 : ZMod (2 * 2)) z hzs
      rw [show (3 : ZMod (2 * 2)) + 1 = 0 from by decide] at hs
      exact hs
    · have hσn : 1 < ‖1 / (starRingEnd ℂ) z‖ := by
        rw [norm_sigma]
        exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hz0, hz1'⟩
      simp only [glue]
      rw [ite_eq_right (not_le.mpr hσn), sigma_sigma,
        show (3 : ZMod (2 * 2)) + 1 = 0 from by decide]
  · -- the σ-parity of the composite: `F ∘ σ = glue u 3` and
    -- `glue u 3 = ζ₂^{s₀} · glue u 3 ∘ σ` by the copy relation
    have hZ : {z : ℂ | z ≠ 0} ∈ 𝓝 w := (isOpen_ne (x := (0 : ℂ))).mem_nhds hw0
    have hT : {z : ℂ | (-1 : ℝ) ^ 0 * ((z ^ k).re) < 0} ∈ 𝓝 w :=
      (isOpen_signSet k 0).mem_nhds hw.2
    filter_upwards [hZ, hT] with z hz0 hzT
    rw [sigma_sigma]
    have hcopy3 : ∀ y, (uncurryE 2).symm W 3 y = zeta 2 ^ s₀ * (uncurryE 2).symm W 0 y :=
      fun y => sector_copy_three hW y
    rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
    · -- inside: LHS if-branch = `u 3 z`; RHS `ζ^{s₀}·u 0 (σσz)` via else-branch
      have hσn : 1 < ‖1 / (starRingEnd ℂ) z‖ := by
        rw [norm_sigma]
        exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hz0, h1⟩
      simp only [glue]
      rw [ite_eq_left (le_of_lt h1), ite_eq_right (not_le.mpr hσn), sigma_sigma,
        show (3 : ZMod (2 * 2)) + 1 = 0 from by decide]
      exact hcopy3 z
    · -- circle: both sides `u 3 z`; even trivial, odd via the arc-0 vanishing
      have hσz : (1 / (starRingEnd ℂ) z) = z := sigma_circle h1
      have hzarc : z ∈ arc k 0 := ⟨h1, hzT⟩
      simp only [glue, hσz]
      rw [ite_eq_left (le_of_eq h1)]
      rcases (by omega : s₀ % 2 = 0 ∨ s₀ % 2 = 1) with hpar | hpar
      · rw [zeta_two_pow_even hpar, one_mul]
      · rw [zeta_two_pow_odd hpar]
        have hv := sector_vanishes_arc0 hW (zeta_two_pow_odd hpar) hzarc
        have h3 := hcopy3 z
        rw [zeta_two_pow_odd hpar, hv] at h3
        rw [h3]
        ring
    · -- outside: LHS else-branch = `u 0 (σz)`; RHS `ζ^{s₀}·u 3 (σz)`, closed by `ζ² = 1`
      have hσn : ‖1 / (starRingEnd ℂ) z‖ < 1 := by
        rw [norm_sigma]
        exact inv_lt_one_of_one_lt₀ h1
      simp only [glue]
      rw [ite_eq_right (not_le.mpr h1), ite_eq_left (le_of_lt hσn),
        show (3 : ZMod (2 * 2)) + 1 = 0 from by decide]
      have hz2 : zeta 2 ^ s₀ * zeta 2 ^ s₀ = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, KsIndex.Bracket.zeta_two, neg_one_sq, one_pow]
      rw [hcopy3 (1 / (starRingEnd ℂ) z), ← mul_assoc, hz2, one_mul]

/-! ### The even-parity flux vanishing and the within-derivative bridge -/

/-- The derivative of the circle inversion `σ` at a unit-circle point sends the radial
direction `w` to `−w`. -/
lemma sigma_hasFDerivAt {w : ℂ} (hw0 : w ≠ 0) :
    HasFDerivAt (fun z : ℂ => 1 / (starRingEnd ℂ) z)
      (ContinuousLinearMap.comp
        ((ContinuousLinearMap.toSpanSingleton ℂ
          (-(((starRingEnd ℂ) w) ^ 2)⁻¹)).restrictScalars ℝ)
        (Complex.conjCLE.toContinuousLinearMap)) w := by
  have hconj : HasFDerivAt (fun z : ℂ => (starRingEnd ℂ) z)
      Complex.conjCLE.toContinuousLinearMap w :=
    Complex.conjCLE.hasFDerivAt
  have hne : (starRingEnd ℂ) w ≠ 0 := by simpa using hw0
  have hinv : HasFDerivAt (fun x : ℂ => x⁻¹)
      (ContinuousLinearMap.toSpanSingleton ℂ (-(((starRingEnd ℂ) w) ^ 2)⁻¹))
      ((starRingEnd ℂ) w) :=
    hasFDerivAt_inv hne
  have h := (hinv.restrictScalars ℝ).comp w hconj
  simpa [one_div, Function.comp_def] using h

/-- **The classical inversion argument**: an eventually σ-even function at a unit-circle
point has vanishing radial derivative there. -/
lemma flux_zero_of_sigma_even {F : ℂ → ℂ} {w : ℂ} (hw1 : ‖w‖ = 1)
    (hF : ContDiffAt ℝ ∞ F w)
    (hpar : ∀ᶠ z in 𝓝 w, F (1 / (starRingEnd ℂ) z) = F z) :
    fderiv ℝ F w w = 0 := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw1
    exact zero_ne_one hw1
  have hσw : (1 / (starRingEnd ℂ) w) = w := sigma_circle hw1
  have hFd : HasFDerivAt F (fderiv ℝ F w) w :=
    (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hFσw : HasFDerivAt F (fderiv ℝ F w) (1 / (starRingEnd ℂ) w) := by
    rw [hσw]
    exact hFd
  have hcomp := hFσw.comp w (sigma_hasFDerivAt hw0)
  have hlam : HasFDerivAt (fun z => F (1 / (starRingEnd ℂ) z))
      ((fderiv ℝ F w).comp (ContinuousLinearMap.comp
        ((ContinuousLinearMap.toSpanSingleton ℂ
          (-(((starRingEnd ℂ) w) ^ 2)⁻¹)).restrictScalars ℝ)
        (Complex.conjCLE.toContinuousLinearMap))) w := hcomp
  have heq : fderiv ℝ (fun z => F (1 / (starRingEnd ℂ) z)) w = fderiv ℝ F w :=
    Filter.EventuallyEq.fderiv_eq hpar
  rw [hlam.fderiv] at heq
  have happ := congrArg (fun L : ℂ →L[ℝ] ℂ => L w) heq
  -- the σ-derivative sends `w` to `−w` on the unit circle
  have hne : (starRingEnd ℂ) w ≠ 0 := by simpa using hw0
  have hcw : (starRingEnd ℂ) w * w = 1 := by
    rw [mul_comm, Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, hw1]
    norm_num
  have hinvw : ((starRingEnd ℂ) w)⁻¹ = w := inv_eq_of_mul_eq_one_right hcw
  have hval : (starRingEnd ℂ) w * -(((starRingEnd ℂ) w) ^ 2)⁻¹ = -w := by
    rw [pow_two, mul_inv, mul_neg, ← mul_assoc, mul_inv_cancel₀ hne, one_mul, hinvw]
  have happ' : (fderiv ℝ F w) ((starRingEnd ℂ) w • (-(((starRingEnd ℂ) w) ^ 2)⁻¹)) =
      (fderiv ℝ F w) w := happ
  rw [smul_eq_mul, hval, map_neg] at happ'
  linear_combination (-(1 : ℂ) / 2) * happ'

/-- At a unit-circle point where the field agrees with a smooth extension on the
closed-disk side, the within-closed-ball derivative IS the extension's derivative. -/
lemma fderivWithin_closedBall_of_extension {f F : ℂ → ℂ} {w : ℂ} (hw1 : ‖w‖ = 1)
    (hF : ContDiffAt ℝ ∞ F w)
    (hagree : ∀ᶠ z in 𝓝 w, ‖z‖ ≤ 1 → f z = F z) :
    fderivWithin ℝ f (Metric.closedBall (0 : ℂ) 1) w = fderiv ℝ F w := by
  have hwmem : w ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, hw1]
  have hud : UniqueDiffOn ℝ (Metric.closedBall (0 : ℂ) 1) :=
    uniqueDiffOn_convex (convex_closedBall 0 1)
      (by rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
          exact ⟨0, Metric.mem_ball_self (by norm_num)⟩)
  have hev : f =ᶠ[𝓝[Metric.closedBall (0 : ℂ) 1] w] F := by
    filter_upwards [hagree.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with z hz hzmem
    exact hz (by simpa [Metric.mem_closedBall, dist_zero_right] using hzmem)
  have hfw : f w = F w := hagree.self_of_nhds (le_of_eq hw1)
  rw [Filter.EventuallyEq.fderivWithin_eq hev hfw]
  exact (hF.differentiableAt (by norm_num)).fderivWithin (hud w hwmem)

/-! ### Vanishing transfer to the `C¹` representative -/

/-- A continuous function agreeing on the open disk with one that vanishes ε-near a set
vanishes (ε/2)-near it on the closed disk: interior points directly, circle points by the
radial limit. -/
lemma C1rep_vanishes_near {f G : ℂ → ℂ} {S : Set ℂ} {ε : ℝ} (hε : 0 < ε)
    (hG : Continuous G) (hfG : ∀ w ∈ Surface.disk, f w = G w)
    (hf0 : ∀ w, (∃ p ∈ S, ‖w - p‖ < ε) → f w = 0)
    {x : ℂ} (hx : ‖x‖ ≤ 1) (hxS : ∃ p ∈ S, ‖x - p‖ < ε / 2) : G x = 0 := by
  obtain ⟨p, hpS, hxp⟩ := hxS
  rcases lt_or_eq_of_le hx with h1 | h1
  · rw [← hfG x (mem_disk_iff.mpr h1)]
    exact hf0 x ⟨p, hpS, lt_of_lt_of_le hxp (by linarith)⟩
  · -- circle point: radial limit of interior zeros
    have hzero : ∀ᶠ t in 𝓝[<] (1 : ℝ), G ((t : ℝ) • x) = 0 := by
      have hmem : Set.Ioo (max (1/2) (1 - ε / (2 * (1 + ‖x‖)))) 1 ∈ 𝓝[<] (1 : ℝ) := by
        apply Ioo_mem_nhdsLT
        apply max_lt (by norm_num)
        have hpos : 0 < ε / (2 * (1 + ‖x‖)) := by positivity
        linarith
      filter_upwards [hmem] with t ht
      have ht1 : t < 1 := ht.2
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) (le_of_lt (max_lt_iff.mp ht.1).1)
      have htn : ‖(t : ℝ) • x‖ < 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, h1, mul_one]
        exact ht1
      rw [← hfG _ (mem_disk_iff.mpr htn)]
      apply hf0
      refine ⟨p, hpS, ?_⟩
      have hd : ‖(t : ℝ) • x - x‖ = (1 - t) * ‖x‖ := by
        rw [show (t : ℝ) • x - x = -((1 - t) • x) by rw [sub_smul, one_smul]; ring,
          norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
      calc ‖(t : ℝ) • x - p‖ ≤ ‖(t : ℝ) • x - x‖ + ‖x - p‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ = (1 - t) * ‖x‖ + ‖x - p‖ := by rw [hd]
        _ < ε / 2 + ε / 2 := by
            apply add_lt_add ?_ hxp
            have hxb : ‖x‖ ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
            have ht' : 1 - t < ε / (2 * (1 + ‖x‖)) := by
              have := (max_lt_iff.mp ht.1).2
              linarith
            calc (1 - t) * ‖x‖ ≤ (1 - t) * (1 + ‖x‖) := by
                  apply mul_le_mul_of_nonneg_left hxb (by linarith)
              _ < (ε / (2 * (1 + ‖x‖))) * (1 + ‖x‖) := by
                  apply mul_lt_mul_of_pos_right ht' (by positivity)
              _ = ε / 2 := by field_simp
        _ = ε := by ring
    have hlim : Filter.Tendsto (fun t : ℝ => G ((t : ℝ) • x)) (𝓝[<] (1 : ℝ)) (𝓝 (G x)) := by
      have hc : Filter.Tendsto (fun t : ℝ => (t : ℝ) • x) (𝓝[<] (1 : ℝ)) (𝓝 x) := by
        have h1s : Filter.Tendsto (fun t : ℝ => t • x) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) • x)) :=
          tendsto_id.smul_const x
        rw [one_smul] at h1s
        exact h1s.mono_left nhdsWithin_le_nhds
      exact (hG.tendsto x).comp hc
    have h0 : Filter.Tendsto (fun t : ℝ => G ((t : ℝ) • x)) (𝓝[<] (1 : ℝ)) (𝓝 0) :=
      tendsto_const_nhds.congr' (hzero.mono fun t ht => ht.symm)
    have hne : (𝓝[<] (1 : ℝ)).NeBot := by
      apply mem_closure_iff_nhdsWithin_neBot.mp
      rw [closure_Iio]
      exact Set.mem_Iic.mpr le_rfl
    exact tendsto_nhds_unique hlim h0

/-- The interior form of the within-derivative. -/
lemma fderivWithin_closedBall_interior {f : ℂ → ℂ} {z : ℂ} (hz : ‖z‖ < 1) :
    fderivWithin ℝ f (Metric.closedBall (0 : ℂ) 1) z = fderiv ℝ f z := by
  apply fderivWithin_of_mem_nhds
  exact Filter.mem_of_superset
    ((Metric.isOpen_ball).mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hz))
    Metric.ball_subset_closedBall


/-- At a circle point with a collar extension, the flux integrand is continuous within the
closed disk: the within-derivative agrees with the extension's derivative on a fixed
neighbourhood, and the latter varies continuously. -/
lemma flux_continuousWithinAt_of_extension {f F G : ℂ → ℂ} {w : ℂ} (hw1 : ‖w‖ = 1)
    (hF : ContDiffAt ℝ ∞ F w)
    (hagree : ∀ᶠ z in 𝓝 w, ‖z‖ ≤ 1 → f z = F z)
    (hG : ContDiff ℝ 1 G) (a : ℂ) :
    ContinuousWithinAt (fun z => (starRingEnd ℂ)
      (fderivWithin ℝ f (Metric.closedBall (0 : ℂ) 1) z a) * G z)
      (Metric.closedBall (0 : ℂ) 1) w := by
  have hud : UniqueDiffOn ℝ (Metric.closedBall (0 : ℂ) 1) :=
    uniqueDiffOn_convex (convex_closedBall 0 1)
      (by rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
          exact ⟨0, Metric.mem_ball_self (by norm_num)⟩)
  obtain ⟨U, hUo, hUmem, hFU⟩ :=
    (hF.of_le (le_trans (by norm_num) two_le_infty)).contDiffOn' (m := 1) le_rfl (by norm_num)
  rw [Set.insert_eq_self.mpr (Set.mem_univ w), Set.univ_inter] at hFU
  obtain ⟨V, hVagree, hVo, hVmem⟩ := eventually_nhds_iff.mp hagree
  have hkey : ∀ z, z ∈ (U ∩ V) ∩ Metric.closedBall (0 : ℂ) 1 →
      fderivWithin ℝ f (Metric.closedBall (0 : ℂ) 1) z = fderiv ℝ F z := by
    rintro z ⟨⟨hzU, hzV⟩, hzB⟩
    have hzB' : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hzB
    have hev : f =ᶠ[𝓝[Metric.closedBall (0 : ℂ) 1] z] F := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hzV),
        self_mem_nhdsWithin] with y hyV hyB
      exact hVagree y hyV (by simpa [Metric.mem_closedBall, dist_zero_right] using hyB)
    have hfz : f z = F z := hVagree z hzV hzB'
    rw [Filter.EventuallyEq.fderivWithin_eq hev hfz]
    have hdz : DifferentiableAt ℝ F z :=
      (hFU.contDiffAt (hUo.mem_nhds hzU)).differentiableAt (by norm_num)
    exact hdz.fderivWithin (hud z hzB)
  have hcaF : ContinuousAt (fun z => fderiv ℝ F z a) w := by
    have hcf : ContinuousOn (fun z => fderiv ℝ F z) U :=
      hFU.continuousOn_fderiv_of_isOpen hUo le_rfl
    exact (hcf.continuousAt (hUo.mem_nhds hUmem)).clm_apply continuousAt_const
  have hcont : ContinuousWithinAt (fun z => (starRingEnd ℂ) (fderiv ℝ F z a) * G z)
      (Metric.closedBall (0 : ℂ) 1) w :=
    ((Complex.continuous_conj.continuousAt.comp hcaF).mul
      hG.continuous.continuousAt).continuousWithinAt
  apply hcont.congr_of_eventuallyEq
  · filter_upwards [mem_nhdsWithin_of_mem_nhds ((hUo.inter hVo).mem_nhds ⟨hUmem, hVmem⟩),
      self_mem_nhdsWithin] with z hzN hzB
    rw [hkey z ⟨hzN, hzB⟩]
  · rw [hkey w ⟨⟨hUmem, hVmem⟩,
      by simpa [Metric.mem_closedBall, dist_zero_right] using le_of_eq hw1⟩]

/-- Flux continuity: for a sector field against a `C¹` test vanishing near the
punctures, the boundary-flux integrand is continuous on the closed disk — interior points by
smoothness, open-arc points through the collar extensions, punctures by the test's vanishing. -/
lemma sector_flux_continuousOn {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀)
    {G : ℂ → ℂ} (hG : ContDiff ℝ 1 G) {εP : ℝ} (hεP : 0 < εP)
    (hGP : ∀ x, ‖x‖ ≤ 1 → (∃ p ∈ punctures k, ‖x - p‖ < εP) → G x = 0)
    (a : ℂ) :
    ContinuousOn (fun w => (starRingEnd ℂ)
      (fderivWithin ℝ ((uncurryE 2).symm W 0) (Metric.closedBall (0 : ℂ) 1) w a) * G w)
      (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, -, -, -, hsv⟩ := sector_field_mem hW
  set f := (uncurryE 2).symm W 0 with hf
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  rcases lt_or_eq_of_le hx with h1 | h1
  · -- interior: the within-derivative is the ordinary derivative of a smooth function
    have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 x :=
      (Metric.isOpen_ball).mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using h1)
    have hcont : ContinuousAt (fun w => (starRingEnd ℂ) (fderiv ℝ f w a) * G w) x := by
      have hdf : ContinuousAt (fun w => fderiv ℝ f w a) x := by
        have h2 : ContDiffAt ℝ 1 f x :=
          ((hsm1 0).contDiffAt ((Metric.isOpen_ball).mem_nhds
            (mem_disk_iff.mpr h1))).of_le (le_trans (by norm_num) two_le_infty)
        exact ((h2.fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply
          continuousAt_const)
      exact (Complex.continuous_conj.continuousAt.comp hdf).mul hG.continuous.continuousAt
    apply hcont.continuousWithinAt.congr_of_eventuallyEq
    · filter_upwards [Filter.inter_mem (self_mem_nhdsWithin)
        (mem_nhdsWithin_of_mem_nhds hball)] with z hz
      rw [fderivWithin_closedBall_interior
        (by simpa [Metric.mem_ball, dist_zero_right] using hz.2)]
    · rw [fderivWithin_closedBall_interior h1]
  · -- boundary: arcs through the collar extensions, punctures by the test vanishing
    rcases lt_trichotomy ((x ^ k).re) 0 with hre | hre | hre
    · -- `x ∈ arc k 0`
      obtain ⟨F, hF, hagree, -⟩ := sector_extension_arc0 hW ⟨h1, by simpa using hre⟩
      exact flux_continuousWithinAt_of_extension h1 hF hagree hG a
    · -- puncture: the test vanishes nearby
      have hxp : x ∈ punctures k := by
        change x ^ (2 * k) = -1
        have hnorm : ‖x ^ k‖ = 1 := by rw [norm_pow, h1, one_pow]
        have him : (x ^ k).im ^ 2 = 1 := by
          have h2 : (x ^ k).re ^ 2 + (x ^ k).im ^ 2 = 1 := by
            have := Complex.normSq_eq_norm_sq (x ^ k)
            rw [hnorm] at this
            rw [Complex.normSq_apply] at this
            nlinarith [this]
          rw [hre] at h2
          nlinarith [h2]
        have h2k : x ^ (2 * k) = (x ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
        rw [h2k, pow_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im, hre]
        constructor
        · simp only [Complex.neg_re, Complex.one_re]
          nlinarith [him]
        · simp
      have hev : ∀ᶠ z in 𝓝[Metric.closedBall (0 : ℂ) 1] x,
          (starRingEnd ℂ) (fderivWithin ℝ f (Metric.closedBall (0 : ℂ) 1) z a) * G z = 0 := by
        have hball : Metric.ball x εP ∈ 𝓝 x := Metric.ball_mem_nhds x hεP
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hball] with z hz1 hz2
        have hz1' : ‖z‖ ≤ 1 := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hz1
        rw [hGP z hz1' ⟨x, hxp, by simpa [dist_eq_norm] using hz2⟩, mul_zero]
      have hx0 : (starRingEnd ℂ)
          (fderivWithin ℝ f (Metric.closedBall (0 : ℂ) 1) x a) * G x = 0 := by
        rw [hGP x hx ⟨x, hxp, by simpa using hεP⟩, mul_zero]
      apply continuousWithinAt_const.congr_of_eventuallyEq
      · filter_upwards [hev] with z hz
        rw [hz]
      · rw [hx0]
    · -- `x ∈ arc k 1`
      obtain ⟨F, hF, hagree, -⟩ := sector_extension_arc1 hW ⟨h1, by simpa using hre⟩
      exact flux_continuousWithinAt_of_extension h1 hF hagree hG a

/-! ### The Green identity for a sector field against a natural-core test -/

/-- The natural-core `C¹` representative, with the pointwise open-disk agreement exposed
(the ingredient `naturalCoreH1_C1_representative` hides). -/
lemma sector_core_rep {k : ℕ} (hk1 : 1 ≤ k) {b1 b0 : Bool} (ff : KsIndex.SingleDisk.NatCc k b1 b0) :
    ∃ G : ℂ → ℂ, ContDiff ℝ 1 G ∧ (∀ w ∈ Surface.disk, ff.val w = G w) ∧
      (valueCLM (naturalCoreH1 hk1 ff) =ᵐ[volume.restrict (KsIndex.WeakH1.disk : Set ℂ)] G) ∧
      (dxCLM (naturalCoreH1 hk1 ff) =ᵐ[volume.restrict (KsIndex.WeakH1.disk : Set ℂ)]
        (fun w => fderiv ℝ G w 1)) ∧
      (dyCLM (naturalCoreH1 hk1 ff) =ᵐ[volume.restrict (KsIndex.WeakH1.disk : Set ℂ)]
        (fun w => fderiv ℝ G w Complex.I)) ∧
      ((diskTraceCLM (naturalCoreH1 hk1 ff) : Circle₁ → ℂ) =ᵐ[circleMeasure]
        (fun w => G (w : ℂ))) := by
  obtain ⟨G, hG, he⟩ := KsIndex.SeamUpper.natCc_extension hk1 ff.property
  have hd : ∀ w ∈ (KsIndex.WeakH1.disk : Set ℂ), fderiv ℝ ff.val w = fderiv ℝ G w := by
    intro w hw
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [KsIndex.WeakH1.disk.isOpen.mem_nhds hw] with z hz
    exact he z hz
  have hv : valueCLM (naturalCoreH1 hk1 ff)
      =ᵐ[volume.restrict (KsIndex.WeakH1.disk : Set ℂ)] G := by
    filter_upwards [naturalCoreH1_value_ae hk1 ff,
      ae_restrict_mem KsIndex.WeakH1.disk.isOpen.measurableSet] with w hw hmem
    exact hw.trans (he w hmem)
  refine ⟨G, hG, he, hv, ?_, ?_, diskTrace_coe_ae hG.continuous.continuousOn hv⟩
  · filter_upwards [naturalCoreH1_dx_ae hk1 ff,
      ae_restrict_mem KsIndex.WeakH1.disk.isOpen.measurableSet] with w hw hmem
    exact hw.trans (congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) (hd w hmem))
  · filter_upwards [naturalCoreH1_dy_ae hk1 ff,
      ae_restrict_mem KsIndex.WeakH1.disk.isOpen.measurableSet] with w hw hmem
    exact hw.trans (congrArg (fun L : ℂ →L[ℝ] ℂ => L Complex.I) (hd w hmem))

/-- The sector field's derivative representatives, specialized. -/
lemma sectorRestrictFun_dx (hk : 2 ≤ k) (W : ↥(boundedJacobiSector k r s₁ s₀)) :
    (dxCLM (sectorRestrictFun hk W) : ℂ → ℂ)
      =ᵐ[volume.restrict (KsIndex.WeakH1.disk : Set ℂ)]
      (fun w => fderiv ℝ ((uncurryE 2).symm W.val 0) w 1) :=
  energySmoothToH1_dx _ 0

lemma sectorRestrictFun_dy (hk : 2 ≤ k) (W : ↥(boundedJacobiSector k r s₁ s₀)) :
    (dyCLM (sectorRestrictFun hk W) : ℂ → ℂ)
      =ᵐ[volume.restrict (KsIndex.WeakH1.disk : Set ℂ)]
      (fun w => fderiv ℝ ((uncurryE 2).symm W.val 0) w Complex.I) :=
  energySmoothToH1_dy _ 0

/-- The Green identity: the weak Jacobi pairing of a sector field against a
natural-core test equals the boundary flux integral, `first_green_disk` discharged through the
piecewise flux continuity and the Caccioppoli representatives. -/
lemma sector_core_green (hk : 2 ≤ k) (hk1 : 1 ≤ k)
    (W : ↥(boundedJacobiSector k r s₁ s₀)) {b1 b0 : Bool}
    (ff : KsIndex.SingleDisk.NatCc k b1 b0) :
    weakJacobi (surfacePotential k) (sectorRestrictFun hk W) (naturalCoreH1 hk1 ff) =
      ∫ w : Circle₁, (starRingEnd ℂ)
        (fderivWithin ℝ ((uncurryE 2).symm W.val 0) (Metric.closedBall (0 : ℂ) 1)
          (w : ℂ) (w : ℂ))
        * (diskTraceCLM (naturalCoreH1 hk1 ff) : Circle₁ → ℂ) w ∂circleMeasure := by
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, hbd, hjac, hpz, hsv⟩ := sector_field_mem W.property
  obtain ⟨G, hG, heq, hval, hdxG, hdyG, ht⟩ := sector_core_rep hk1 ff
  obtain ⟨εP, hεP, hP⟩ := (KsIndex.SingleDisk.mem_NatCc.mp ff.property).2.2.2.2
  set f0 := (uncurryE 2).symm W.val 0 with hf0
  have hGP : ∀ x, ‖x‖ ≤ 1 → (∃ p ∈ punctures k, ‖x - p‖ < εP / 2) → G x = 0 :=
    fun x hx hxp => C1rep_vanishes_near hεP hG.continuous heq hP hx hxp
  -- the `first_green_disk` hypotheses
  have hu2 : ∀ a : ℂ, ∀ w ∈ Metric.ball (0 : ℂ) 1,
      DifferentiableAt ℝ (fun z => fderiv ℝ f0 z a) w := by
    intro a w hw
    have h2 : ContDiffAt ℝ 2 f0 w :=
      ((hsm1 0).contDiffAt ((Metric.isOpen_ball).mem_nhds hw)).of_le two_le_infty
    exact ((h2.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have hvd : ∀ w ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℝ G w :=
    fun w _ => hG.differentiable (by norm_num) w
  have hFc : ∀ a : ℂ, ContinuousOn
      (fun w => (starRingEnd ℂ)
        (fderivWithin ℝ f0 (Metric.closedBall (0 : ℂ) 1) w a) * G w)
      (Metric.closedBall (0 : ℂ) 1) :=
    fun a => sector_flux_continuousOn W.property hG (half_pos hεP) hGP a
  -- the Jacobi equation and the integrabilities
  have hlap : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      laplacian f0 w = -((potV k w : ℂ) * f0 w) :=
    fun w hw => laplacian_eq_of_isJacobiField hk hjac 0 hw
  have hp : Integrable (fun x => ((surfacePotential k).V x : ℂ) *
      (starRingEnd ℂ) (f0 x) * G x)
      (volume.restrict (KsIndex.WeakH1.disk : Set ℂ)) := by
    apply (potential_integrable (surfacePotential k) (sectorRestrictFun hk W)
      (naturalCoreH1 hk1 ff)).congr
    filter_upwards [sectorRestrictFun_value hk W, hval] with x h1 h2
    rw [h1, h2]
  have hg : Integrable (KsIndex.GradOrtho.gradInner f0 G)
      (volume.restrict (KsIndex.WeakH1.disk : Set ℂ)) := by
    apply (dirichlet_integrable (sectorRestrictFun hk W) (naturalCoreH1 hk1 ff)).congr
    filter_upwards [sectorRestrictFun_dx hk W, sectorRestrictFun_dy hk W,
      hdxG, hdyG] with x h1 h2 h3 h4
    simp only [KsIndex.GradOrtho.gradInner, hf0]
    rw [h1, h2, h3, h4]
  have hInt : MeasureTheory.IntegrableOn
      (fun w => KsIndex.GradOrtho.gradInner f0 G w
        + (starRingEnd ℂ) (laplacian f0 w) * G w) (Metric.ball (0 : ℂ) 1) := by
    have hsub : Integrable (fun x => KsIndex.GradOrtho.gradInner f0 G x -
        ((surfacePotential k).V x : ℂ) * (starRingEnd ℂ) (f0 x) * G x)
        (volume.restrict (KsIndex.WeakH1.disk : Set ℂ)) := hg.sub hp
    apply hsub.congr
    filter_upwards [ae_restrict_mem KsIndex.WeakH1.disk.isOpen.measurableSet] with w hw
    have hV : ((surfacePotential k).V w : ℂ) = ((potV k w : ℝ) : ℂ) := rfl
    rw [hV, hlap w hw, map_neg, map_mul, Complex.conj_ofReal]
    ring
  have hgreen := KsIndex.FirstGreen.first_green_disk
    (hu2 1) (hu2 Complex.I) hvd (hFc 1) (hFc Complex.I) hInt
  -- the boundary integrand is continuous on the circle: `ℝ`-linear direction decomposition
  have hdecomp : ∀ (L : ℂ →L[ℝ] ℂ) (z : ℂ), L z = z.re • L 1 + z.im • L Complex.I := by
    intro L z
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul]
  have hcirc : Continuous (fun w : Circle₁ => (starRingEnd ℂ)
      (fderivWithin ℝ f0 (Metric.closedBall (0 : ℂ) 1) (w : ℂ) (w : ℂ)) * G (w : ℂ)) := by
    have hmem : ∀ w : Circle₁, (w : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 :=
      fun w => Metric.sphere_subset_closedBall w.property
    have h1 : Continuous (fun w : Circle₁ => (starRingEnd ℂ)
        (fderivWithin ℝ f0 (Metric.closedBall (0 : ℂ) 1) (w : ℂ) 1) * G (w : ℂ)) :=
      (hFc 1).comp_continuous continuous_subtype_val hmem
    have hI : Continuous (fun w : Circle₁ => (starRingEnd ℂ)
        (fderivWithin ℝ f0 (Metric.closedBall (0 : ℂ) 1) (w : ℂ) Complex.I) * G (w : ℂ)) :=
      (hFc Complex.I).comp_continuous continuous_subtype_val hmem
    have hre : Continuous (fun w : Circle₁ => (((w : ℂ).re : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (Complex.continuous_re.comp continuous_subtype_val)
    have him : Continuous (fun w : Circle₁ => (((w : ℂ).im : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (Complex.continuous_im.comp continuous_subtype_val)
    apply ((hre.mul h1).add (him.mul hI)).congr
    intro w
    rw [hdecomp (fderivWithin ℝ f0 (Metric.closedBall (0 : ℂ) 1) (w : ℂ)) (w : ℂ),
      Complex.real_smul, Complex.real_smul, map_add, map_mul, map_mul,
      Complex.conj_ofReal, Complex.conj_ofReal]
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  -- trace → representative on the circle
  have htr : (∫ w : Circle₁, (starRingEnd ℂ)
      (fderivWithin ℝ f0 (Metric.closedBall (0 : ℂ) 1) (w : ℂ) (w : ℂ))
      * (diskTraceCLM (naturalCoreH1 hk1 ff) : Circle₁ → ℂ) w ∂circleMeasure) =
      ∫ w : Circle₁, (starRingEnd ℂ)
      (fderivWithin ℝ f0 (Metric.closedBall (0 : ℂ) 1) (w : ℂ) (w : ℂ))
      * G (w : ℂ) ∂circleMeasure := by
    apply integral_congr_ae
    filter_upwards [ht] with w hw
    rw [hw]
  rw [htr, integral_circleMeasure_window (-Real.pi) hcirc.aestronglyMeasurable,
    show -Real.pi + 2 * Real.pi = Real.pi by ring, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    weakJacobi_integral_representatives (surfacePotential k) _ _
      (sectorRestrictFun_value hk W) hval (sectorRestrictFun_dx hk W)
      (sectorRestrictFun_dy hk W) hdxG hdyG]
  change (∫ x in (KsIndex.WeakH1.disk : Set ℂ), KsIndex.GradOrtho.gradInner f0 G x) -
    (∫ x in (KsIndex.WeakH1.disk : Set ℂ),
      ((surfacePotential k).V x : ℂ) * (starRingEnd ℂ) (f0 x) * G x) = _
  rw [← integral_sub hg hp]
  calc (∫ x in (KsIndex.WeakH1.disk : Set ℂ), (KsIndex.GradOrtho.gradInner f0 G x -
        ((surfacePotential k).V x : ℂ) * (starRingEnd ℂ) (f0 x) * G x))
      = ∫ w in Metric.ball (0 : ℂ) 1, (KsIndex.GradOrtho.gradInner f0 G w
          + (starRingEnd ℂ) (laplacian f0 w) * G w) := by
        apply setIntegral_congr_fun KsIndex.WeakH1.disk.isOpen.measurableSet
        intro w hw
        have hV : ((surfacePotential k).V w : ℂ) = ((potV k w : ℝ) : ℂ) := rfl
        dsimp only
        rw [hV, hlap w hw, map_neg, map_mul, Complex.conj_ofReal]
        ring
    _ = ∫ θ in (-Real.pi : ℝ)..Real.pi, (starRingEnd ℂ)
          (fderivWithin ℝ f0 (Metric.closedBall (0 : ℂ) 1)
            (Complex.exp ((θ : ℂ) * Complex.I)) (Complex.exp ((θ : ℂ) * Complex.I)))
          * G (Complex.exp ((θ : ℂ) * Complex.I)) := hgreen
    _ = _ := by
        apply intervalIntegral.integral_congr
        intro θ _
        simp only [circleParam_coe]

/-! ### The boundary term vanishes at matched parities -/

/-- Even `s₁`: the sector field's radial `fderivWithin` vanishes on `arc k 1` — the collar
extension is `σ`-even there, so the inversion argument kills its radial derivative. -/
lemma sector_flux_vanishes_arc1 {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) (hs : s₁ % 2 = 0)
    {w : ℂ} (hw : w ∈ arc k 1) :
    fderivWithin ℝ ((uncurryE 2).symm W 0) (Metric.closedBall (0 : ℂ) 1) w w = 0 := by
  obtain ⟨F, hF, hagree, hpar⟩ := sector_extension_arc1 hW hw
  rw [fderivWithin_closedBall_of_extension hw.1 hF hagree]
  apply flux_zero_of_sigma_even hw.1 hF
  filter_upwards [hpar] with z hz
  rw [hz, zeta_two_pow_even hs, one_mul]

/-- Even `s₀`: the sector field's radial `fderivWithin` vanishes on `arc k 0`. -/
lemma sector_flux_vanishes_arc0 {W : ZMod (2 * 2) × ℂ → ℂ}
    (hW : W ∈ boundedJacobiSector k r s₁ s₀) (hs : s₀ % 2 = 0)
    {w : ℂ} (hw : w ∈ arc k 0) :
    fderivWithin ℝ ((uncurryE 2).symm W 0) (Metric.closedBall (0 : ℂ) 1) w w = 0 := by
  obtain ⟨F, hF, hagree, hpar⟩ := sector_extension_arc0 hW hw
  rw [fderivWithin_closedBall_of_extension hw.1 hF hagree]
  apply flux_zero_of_sigma_even hw.1 hF
  filter_upwards [hpar] with z hz
  rw [hz, zeta_two_pow_even hs, one_mul]

/-- A unit-circle point with `Re(w^k) = 0` is a puncture. -/
lemma puncture_of_re_pow_zero {x : ℂ} (hx : ‖x‖ = 1) (hre : (x ^ k).re = 0) :
    x ∈ punctures k := by
  change x ^ (2 * k) = -1
  have hnorm : ‖x ^ k‖ = 1 := by rw [norm_pow, hx, one_pow]
  have him : (x ^ k).im ^ 2 = 1 := by
    have h2 : (x ^ k).re ^ 2 + (x ^ k).im ^ 2 = 1 := by
      have := Complex.normSq_eq_norm_sq (x ^ k)
      rw [hnorm] at this
      rw [Complex.normSq_apply] at this
      nlinarith [this]
    rw [hre] at h2
    nlinarith [h2]
  have h2k : x ^ (2 * k) = (x ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [h2k, pow_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im, hre]
  constructor
  · simp only [Complex.neg_re, Complex.one_re]
    nlinarith [him]
  · simp

/-- Vanishing of the pairing: against a natural-core test
with the parity-matched flags, the sector Green pairing is zero.  Pointwise on the circle:
even-parity arcs kill the flux factor (`flux_zero_of_sigma_even` through the collar
extensions), odd-parity arcs kill the test factor (`SuppAwaySet` near the closed slit,
transferred to the `C¹` representative), punctures kill the test factor (`SuppAwayP1`). -/
lemma sector_pairing_zero (hk : 2 ≤ k) (hk1 : 1 ≤ k) (hs₁ : s₁ < 2) (hs₀ : s₀ < 2)
    (W : ↥(boundedJacobiSector k r s₁ s₀))
    (ff : KsIndex.SingleDisk.NatCc k (decide (s₁ = 0)) (decide (s₀ = 0))) :
    weakJacobi (surfacePotential k) (sectorRestrictFun hk W) (naturalCoreH1 hk1 ff) = 0 := by
  obtain ⟨G, hG, heq, hval, hdxG, hdyG, ht⟩ := sector_core_rep hk1 ff
  rw [sector_core_green hk hk1 W ff]
  have hzero : ∀ w : Circle₁, (starRingEnd ℂ)
      (fderivWithin ℝ ((uncurryE 2).symm W.val 0) (Metric.closedBall (0 : ℂ) 1)
        (w : ℂ) (w : ℂ)) * G (w : ℂ) = 0 := by
    intro w
    have hw1 : ‖(w : ℂ)‖ = 1 := by
      have := w.property
      simp only [Metric.mem_sphere, dist_zero_right] at this
      exact this
    rcases lt_trichotomy ((((w : ℂ)) ^ k).re) 0 with hre | hre | hre
    · -- `arc k 0`
      have harc : (w : ℂ) ∈ arc k 0 := ⟨hw1, by simpa using hre⟩
      rcases (by omega : s₀ = 0 ∨ s₀ = 1) with h0 | h1
      · rw [sector_flux_vanishes_arc0 W.property (by omega) harc, map_zero, zero_mul]
      · subst h1
        obtain ⟨ε, hε, hcl⟩ : KsIndex.SingleDisk.SuppAwaySet (KsIndex.Bracket.slit k) ff.val :=
          (KsIndex.SingleDisk.mem_NatCc.mp ff.property).2.2.1
        rw [C1rep_vanishes_near hε hG.continuous heq hcl (le_of_eq hw1)
          ⟨(w : ℂ), KsIndex.Bracket.arc_zero_subset_slit harc, by simpa using half_pos hε⟩,
          mul_zero]
    · -- puncture
      have hxp : (w : ℂ) ∈ punctures k := puncture_of_re_pow_zero hw1 hre
      obtain ⟨εP, hεP, hP⟩ := (KsIndex.SingleDisk.mem_NatCc.mp ff.property).2.2.2.2
      rw [C1rep_vanishes_near hεP hG.continuous heq hP (le_of_eq hw1)
        ⟨(w : ℂ), hxp, by simpa using half_pos hεP⟩, mul_zero]
    · -- `arc k 1`
      have harc : (w : ℂ) ∈ arc k 1 := ⟨hw1, by simpa using hre⟩
      rcases (by omega : s₁ = 0 ∨ s₁ = 1) with h0 | h1
      · rw [sector_flux_vanishes_arc1 W.property (by omega) harc, map_zero, zero_mul]
      · subst h1
        obtain ⟨ε, hε, hcl⟩ :
            KsIndex.SingleDisk.SuppAwaySet (KsIndex.SingleDisk.slitC k) ff.val :=
          (KsIndex.SingleDisk.mem_NatCc.mp ff.property).2.1
        rw [C1rep_vanishes_near hε hG.continuous heq hcl (le_of_eq hw1)
          ⟨(w : ℂ), KsIndex.SingleDisk.arc_one_subset_slitC harc, by simpa using half_pos hε⟩,
          mul_zero]
  calc (∫ w : Circle₁, (starRingEnd ℂ)
      (fderivWithin ℝ ((uncurryE 2).symm W.val 0) (Metric.closedBall (0 : ℂ) 1)
        (w : ℂ) (w : ℂ))
      * (diskTraceCLM (naturalCoreH1 hk1 ff) : Circle₁ → ℂ) w ∂circleMeasure)
      = ∫ (_ : Circle₁), (0 : ℂ) ∂circleMeasure := by
        apply integral_congr_ae
        filter_upwards [ht] with w hw
        rw [hw]
        exact hzero w
    _ = 0 := by simp

end KsIndex.NullityDecomp
