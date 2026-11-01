module

public import KsIndexLean.EnergySmooth
public import KsIndexLean.Bracket

@[expose] public section


/-!
# Compact-part bounds for EnergySmooth representatives

An `EnergySmooth` chain family is uniformly bounded away from the punctures.
On the closed disk minus ε-neighbourhoods of the punctures, each copy is
continuous: open-disk smoothness handles interior points, and the glue germs
handle the giving and receiving seams. On the receiving seam, `SeamVal`
identifies the representative with the reflected germ of the previous copy.
Compactness and the finite number of copies give a uniform bound; outside
the closed disk the representative vanishes.

The proof uses no Jacobi equation or energy estimate. Bounds near the
punctures are separate from this compact-part estimate.
-/

noncomputable section
open Set Complex
open scoped ContDiff
namespace KsIndex.FaithfulInjection
open KsIndex.Surface KsIndex.SurfaceForm

/-! ### The arc dichotomy on the circle -/

/-- A unit-circle point that is not a puncture has `Re (w^k) ≠ 0`. -/
lemma circle_not_puncture_re_ne {k : ℕ} {w : ℂ} (hw : ‖w‖ = 1)
    (hp : w ∉ punctures k) : ((w ^ k).re) ≠ 0 := by
  intro h0
  apply hp
  have hnk : ‖w ^ k‖ = 1 := by rw [norm_pow, hw, one_pow]
  have hsq1 : (w ^ k).re * (w ^ k).re + (w ^ k).im * (w ^ k).im = 1 := by
    have h := Complex.sq_norm (w ^ k)
    rw [hnk, one_pow, Complex.normSq_apply] at h
    linarith [h]
  have him : (w ^ k).im * (w ^ k).im = 1 := by
    rw [h0] at hsq1
    linarith
  have hsq : (w ^ k) ^ 2 = -1 := by
    apply Complex.ext
    · simp only [pow_two, Complex.mul_re, Complex.neg_re, Complex.one_re, h0]
      linarith
    · simp only [pow_two, Complex.mul_im, Complex.neg_im, Complex.one_im, h0]
      ring
  show w ^ (2 * k) = -1
  rw [show 2 * k = k * 2 from by ring, pow_mul]
  exact hsq

/-! ### Continuity of a representative on the closed disk, away from punctures -/

/-- Per-point continuity of a smooth seam-normalized chain family on the
closed disk away from the punctures. Interior points: open-disk smoothness.
Circle points: the glue germ, directly on the giving seam, composed with the
reflection `z ↦ 1/z̄` on the receiving seam (where `SeamVal` pins the honest
value). -/
lemma isSmooth_continuousWithinAt {k m : ℕ}
    {u : ZMod (2 * m) → ℂ → ℂ} (hs : IsSmooth k m u) (hsv : SeamVal k u)
    (n : ZMod (2 * m)) {w : ℂ} (hw : ‖w‖ ≤ 1) (hp : w ∉ punctures k) :
    ContinuousWithinAt (u n) {z : ℂ | ‖z‖ ≤ 1} w := by
  obtain ⟨hs1, hs2, _⟩ := hs
  rcases lt_or_eq_of_le hw with hlt | heq
  · exact (((hs1 n).contDiffAt
      (Metric.isOpen_ball.mem_nhds (mem_disk_iff.mpr hlt))).continuousAt).continuousWithinAt
  · have hw1 : ‖w‖ = 1 := heq
    have hw0 : w ≠ 0 := fun h => by
      rw [h, norm_zero] at hw1
      exact zero_ne_one hw1
    have hre := circle_not_puncture_re_ne hw1 hp
    have hseam' : seamArc k m (n - 1) = arc k (parity m n).val := by
      unfold seamArc
      rw [sub_add_cancel]
    by_cases hgive : w ∈ seamArc k m n
    · -- the giving seam: `u n` agrees with the smooth germ `glue u n` inside
      have hglue : ContinuousAt (glue u n) w := (hs2 n w hgive).continuousAt
      apply hglue.continuousWithinAt.congr
      · intro z hz
        have hz' : ‖z‖ ≤ 1 := hz
        simp [glue, hz']
      · have hw' : ‖w‖ ≤ 1 := hw
        simp [glue, hw']
    · -- the receiving seam: `w` lies in the OTHER arc family
      have harc : w ∈ arc k (parity m n).val := by
        have hseam : seamArc k m n = arc k (parity m (n + 1)).val := rfl
        have hadd : parity m (n + 1) = parity m n + 1 := by
          rw [map_add, map_one]
        have hpar2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
        rw [hseam, hadd] at hgive
        rcases hpar2 (parity m n) with h | h <;> rw [h] at hgive ⊢
        · rw [show ((0 : ZMod 2) + 1).val = 1 from by decide] at hgive
          rw [show ((0 : ZMod 2)).val = 0 from by decide]
          refine ⟨hw1, ?_⟩
          simp only [pow_zero, one_mul]
          rcases lt_or_gt_of_ne hre with hneg | hpos
          · exact hneg
          · exact absurd ⟨hw1, by simpa using hpos⟩ hgive
        · rw [show ((1 : ZMod 2) + 1).val = 0 from by decide] at hgive
          rw [show ((1 : ZMod 2)).val = 1 from by decide]
          refine ⟨hw1, ?_⟩
          rcases lt_or_gt_of_ne hre with hneg | hpos
          · exact absurd ⟨hw1, by simpa using hneg⟩ hgive
          · simpa using hpos
      have hrecv : w ∈ seamArc k m (n - 1) := by
        rw [hseam']
        exact harc
      -- the comparison germ: the previous copy's glue, reflected
      have hglue : ContinuousAt (glue u (n - 1)) w := (hs2 (n - 1) w hrecv).continuousAt
      have hσw : (1 / (starRingEnd ℂ) w) = w := by
        have h := Bracket.σ_self hw1
        rwa [Bracket.σ_apply] at h
      have hσ : ContinuousAt (fun z : ℂ => 1 / (starRingEnd ℂ) z) w := by
        have h2 : (starRingEnd ℂ) w ≠ 0 := by simpa using hw0
        exact continuousAt_const.div Complex.continuous_conj.continuousAt h2
      have hglue' : ContinuousAt (glue u (n - 1)) (1 / (starRingEnd ℂ) w) := by
        rwa [hσw]
      have hcomp : ContinuousAt (fun z => glue u (n - 1) (1 / (starRingEnd ℂ) z)) w :=
        ContinuousAt.comp (g := glue u (n - 1))
          (f := fun z : ℂ => 1 / (starRingEnd ℂ) z) hglue' hσ
      -- the open neighbourhood on which the congruence holds
      set T : Set ℂ := {z : ℂ | z ≠ 0 ∧
        ((-1 : ℝ) ^ (parity m n).val * ((z ^ k).re) < 0 ∨ ‖z‖ < 1)} with hT
      have hcontf : Continuous fun z : ℂ =>
          (-1 : ℝ) ^ (parity m n).val * ((z ^ k).re) := by
        fun_prop
      have hTopen : IsOpen T := by
        apply IsOpen.inter isOpen_ne
        exact IsOpen.union (isOpen_lt hcontf continuous_const)
          (isOpen_lt continuous_norm continuous_const)
      have hwT : w ∈ T := ⟨hw0, Or.inl harc.2⟩
      -- the pointwise congruence on `T ∩ {‖z‖ ≤ 1}`
      have hEq : ∀ z, z ∈ T ∩ {z : ℂ | ‖z‖ ≤ 1} →
          u n z = glue u (n - 1) (1 / (starRingEnd ℂ) z) := by
        rintro z ⟨⟨hz0, hzcase⟩, hz1⟩
        have hz1' : ‖z‖ ≤ 1 := hz1
        rcases lt_or_eq_of_le hz1' with hzlt | hzeq
        · -- interior: the reflected point is strictly outside, so the glue
          -- takes its outside branch, which is `u n ∘ (reflection²) = u n`
          have hz0' : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
          have houter : ¬ (‖1 / (starRingEnd ℂ) z‖ ≤ 1) := by
            rw [norm_div, norm_one, Complex.norm_conj]
            exact not_le.mpr ((one_lt_div hz0').mpr hzlt)
          simp only [glue, houter, ite_false]
          rw [sub_add_cancel]
          have hσσ := Bracket.σ_σ z
          rw [Bracket.σ_apply, Bracket.σ_apply] at hσσ
          rw [hσσ]
        · -- circle: the reflection fixes `z`, the glue takes its inside
          -- branch, and `SeamVal` pins the value
          have hz1' : ‖z‖ = 1 := hzeq
          have hσz : (1 / (starRingEnd ℂ) z) = z := by
            have h := Bracket.σ_self hz1'
            rwa [Bracket.σ_apply] at h
          rw [hσz]
          have hle : ‖z‖ ≤ 1 := hz1'.le
          simp only [glue, hle, ite_true]
          have hz_arc : z ∈ seamArc k m (n - 1) := by
            rw [hseam']
            refine ⟨hz1', ?_⟩
            rcases hzcase with h | h
            · exact h
            · rw [hz1'] at h
              exact absurd h (lt_irrefl 1)
          have hval := hsv (n - 1) z hz_arc
          rw [sub_add_cancel] at hval
          exact hval
      apply hcomp.continuousWithinAt.congr_of_eventuallyEq
      · apply Filter.eventuallyEq_of_mem
          (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (hTopen.mem_nhds hwT))
            self_mem_nhdsWithin)
        exact hEq
      · exact hEq w ⟨hwT, hw⟩

/-! ### The compact-part bound -/

/-- An `EnergySmooth` chain family is uniformly bounded away from
the punctures: for every `ε > 0` there is one constant bounding every copy
at every point at distance `≥ ε` from all punctures. No Jacobi equation, no
energy — continuity up to the seams plus compactness. -/
theorem energySmooth_bounded_away {k m : ℕ} [NeZero m]
    {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ EnergySmooth k m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n, ∀ w : ℂ, (∀ p ∈ punctures k, ε ≤ ‖w - p‖) → ‖u n w‖ ≤ C := by
  obtain ⟨hsm, -, -, -, hsv⟩ := hu
  -- the compact core
  set K : Set ℂ := {z : ℂ | ‖z‖ ≤ 1} ∩ ⋂ p ∈ punctures k, {z : ℂ | ε ≤ ‖z - p‖}
    with hKdef
  have hball : {z : ℂ | ‖z‖ ≤ 1} = Metric.closedBall (0 : ℂ) 1 := by
    ext z
    simp [Metric.mem_closedBall, dist_zero_right]
  have hKcompact : IsCompact K := by
    rw [hKdef, hball]
    apply (isCompact_closedBall (0 : ℂ) 1).inter_right
    exact isClosed_biInter fun p _ =>
      isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)
  -- per-copy continuity on the core
  have hcont : ∀ n : ZMod (2 * m), ContinuousOn (u n) K := by
    intro n z hz
    have hz1 : ‖z‖ ≤ 1 := hz.1
    have hzp : z ∉ punctures k := by
      intro hmem
      have h' : ε ≤ ‖z - z‖ := Set.mem_iInter₂.mp hz.2 z hmem
      rw [sub_self, norm_zero] at h'
      exact absurd h' (not_le.mpr hε)
    exact (isSmooth_continuousWithinAt hsm hsv n hz1 hzp).mono
      Set.inter_subset_left
  -- per-copy bounds, then the finite max
  choose C hC using fun n : ZMod (2 * m) =>
    hKcompact.exists_bound_of_continuousOn (hcont n)
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have hne : (Finset.univ : Finset (ZMod (2 * m))).Nonempty := Finset.univ_nonempty
  refine ⟨max ((Finset.univ : Finset (ZMod (2 * m))).sup' hne C) 0, ?_⟩
  intro n w hdist
  by_cases hw1 : ‖w‖ ≤ 1
  · have hwK : w ∈ K := ⟨hw1, Set.mem_iInter₂.mpr fun p hp => hdist p hp⟩
    calc ‖u n w‖ ≤ C n := hC n w hwK
      _ ≤ (Finset.univ : Finset (ZMod (2 * m))).sup' hne C :=
          Finset.le_sup' C (Finset.mem_univ n)
      _ ≤ _ := le_max_left _ _
  · rw [hsm.2.2 n w (not_le.mp hw1), norm_zero]
    exact le_max_right _ _

end KsIndex.FaithfulInjection
