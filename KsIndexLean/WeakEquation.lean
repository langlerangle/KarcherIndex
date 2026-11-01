module

/-
Bounded smooth Jacobi fields satisfy the weak Jacobi equation.

For `k ≥ 2` and nonzero `m`, `bddJacobi_le_weakKer` proves
`BoundedJacobi k m ≤ WeakKer k m`. Finite energy comes from
`bddJacobi_le_energySmooth`. The remaining statement is
`∀ φ ∈ CcSmooth, jacobiB k m u φ = 0` for a bounded smooth Jacobi field `u`.
First-Green identities leave seam fluxes which cancel over the `2m` copies
by `sum_bTest_eq_zero` and `seam_flux_pointwise_cancel_conj`. The test's
`SuppAwayP` condition already removes the punctures; this step requires no
new cutoff limit or Fatou argument.

A `CcSmooth` test need not satisfy `SeamVal`: its raw receiving-arc boundary
values can differ from its interior trace. The Green identity therefore uses
`testTrace φ n`, a closed-disk-continuous representative equal to `φ n` on
the open disk and taking the giving side's trace on each seam. Since `jacobiB`
uses open-disk data, this replacement preserves the form and makes the
boundary trace matching in the flux cancellation definitional.
-/
public import KsIndexLean.Caccioppoli

@[expose] public section


open Complex Real MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace KsIndex.FaithfulInjection

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.GradOrtho KsIndex.JacobiFields
  KsIndex.PunctureCutoff KsIndex.PunctureGreen KsIndex.SeamNormal

variable {k m : ℕ} {u φ : ZMod (2 * m) → ℂ → ℂ}

/-! ### The trace-continuous test representative -/

open Classical in
/-- **The trace-continuous test representative.**  Equal to `φ n` on the open disk; on the boundary
circle it takes the honest interior TRACE — on the giving arc `seamArc k m n` the raw value `φ n w`
(already the germ value, `glue`'s inside branch), on the receiving arc `seamArc k m (n−1)` the
giving side's value `φ (n−1) w` (the trace, per `seam_test_trace_match`); `0` at punctures/outside.
`jacobiB` only sees open-disk data, so `jacobiB u φ = jacobiB u (testTrace φ)`
(`testTrace_eqOn_disk`), while the boundary flux reads the trace — which both incident copies share,
making the seam cancellation definitional. -/
def testTrace (k m : ℕ) (φ : ZMod (2 * m) → ℂ → ℂ) (n : ZMod (2 * m)) (w : ℂ) : ℂ :=
  if ‖w‖ < 1 then φ n w
  else if w ∈ seamArc k m n then φ n w
  else if w ∈ seamArc k m (n - 1) then φ (n - 1) w
  else 0

/-- On the open disk the trace representative is the test itself — hence `jacobiB` cannot tell them
apart (its integrals are over the open disk, the circle being null). -/
lemma testTrace_eqOn_disk (φ : ZMod (2 * m) → ℂ → ℂ) (n : ZMod (2 * m)) {w : ℂ} (hw : w ∈ disk) :
    testTrace k m φ n w = φ n w := by
  rw [testTrace, if_pos (mem_disk_iff.mp hw)]

/-- On the giving arc the trace value is `φ n w` (raw = interior trace here). -/
lemma testTrace_giving (φ : ZMod (2 * m) → ℂ → ℂ) {n : ZMod (2 * m)} {w : ℂ}
    (hw : w ∈ seamArc k m n) : testTrace k m φ n w = φ n w := by
  have h1 : ‖w‖ = 1 := norm_eq_one_of_mem_seamArc hw
  rw [testTrace, if_neg (by rw [h1]; norm_num), if_pos hw]

/-- On the receiving arc the trace value is the giving side's value `φ (n−1) w` (the interior trace,
by `seam_test_trace_match`), NOT the possibly-spiked raw `φ n w`. -/
lemma testTrace_receiving (φ : ZMod (2 * m) → ℂ → ℂ) {n : ZMod (2 * m)} {w : ℂ}
    (hw : w ∈ seamArc k m (n - 1)) : testTrace k m φ n w = φ (n - 1) w := by
  have h1 : ‖w‖ = 1 := norm_eq_one_of_mem_seamArc hw
  have hidx : (n - 1 + 1 : ZMod (2 * m)) = n := by ring
  have hnotn : w ∉ seamArc k m n := by
    intro hn
    exact notMem_seamArc_succ hw (by rw [hidx]; exact hn)
  rw [testTrace, if_neg (by rw [h1]; norm_num), if_neg hnotn, if_pos hw]

/-! ### The closed-disk germ for the trace representative -/

/-- **Closed-disk germ for the trace representative.**  The `exists_germ_closedBall` analog for
`testTrace φ n`, and — crucially — WITHOUT `SeamVal`: off the punctures, `testTrace φ n` agrees on
the whole closed disk near `w₀` with a `C^∞`-at-`w₀` germ (`glue φ n` on the giving arc, the
reflected `glue φ (n−1) ∘ σ` on the receiving arc).  The receiving circle-side match is
`testTrace`'s definitional trace value (`testTrace_receiving`), not `SeamVal` — which is exactly why
a seam-spiked test still carries a continuous boundary flux. -/
lemma exists_germ_closedBall_test (hsm : IsSmooth k m φ) (n : ZMod (2 * m)) {w₀ : ℂ}
    (hw₀ : ‖w₀‖ = 1) (hp : w₀ ∉ punctures k) :
    ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w₀ ∧ ∃ W : Set ℂ, IsOpen W ∧ w₀ ∈ W ∧
      ∀ z ∈ W, ‖z‖ ≤ 1 → testTrace k m φ n z = F z := by
  have harc := mem_arc_of_not_puncture hw₀ hp
  have hpv := parity_succ_val m n
  have hlt2 := ZMod.val_lt (parity m n)
  have hcases : w₀ ∈ seamArc k m n ∨ w₀ ∈ seamArc k m (n - 1) := by
    rw [seamArc_pred]; unfold seamArc; rw [hpv]
    rcases (by omega : (parity m n).val = 0 ∨ (parity m n).val = 1) with h | h <;>
      rcases harc with h0 | h1 <;> rw [h]
    · exact Or.inr h0
    · exact Or.inl h1
    · exact Or.inl h0
    · exact Or.inr h1
  rcases hcases with hA | hB
  · -- giving arc: `glue φ n` on a circle-arc neighborhood
    obtain ⟨ε, hε, harcnear⟩ := seamArc_openness hA
    refine ⟨glue φ n, (eventuallyEq_glue_giving hsm hA).1,
      Metric.ball w₀ ε, Metric.isOpen_ball, Metric.mem_ball_self hε, fun z hzB hz1 => ?_⟩
    have hval : testTrace k m φ n z = φ n z := by
      rcases lt_or_eq_of_le hz1 with hlt | heq1
      · exact testTrace_eqOn_disk φ n (mem_disk_iff.mpr hlt)
      · refine testTrace_giving φ (harcnear z heq1 ?_)
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hzB
    rw [hval]; simp only [glue, if_pos hz1]
  · -- receiving arc: reflected germ, circle-side match via `testTrace_receiving` (no `SeamVal`)
    obtain ⟨hFc, hee⟩ := eventuallyEq_glue_recv (n := n - 1) hsm hB
    have hidx : (n - 1 + 1 : ZMod (2 * m)) = n := by ring
    rw [hidx] at hee
    obtain ⟨V₀, hV₀eq, hV₀open, hV₀mem⟩ := eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hee)
    obtain ⟨ε, hε, harcnear⟩ := seamArc_openness hB
    refine ⟨(glue φ (n - 1)) ∘ fun z : ℂ => 1 / (starRingEnd ℂ) z, hFc,
      V₀ ∩ Metric.ball w₀ ε, hV₀open.inter Metric.isOpen_ball,
      ⟨hV₀mem, Metric.mem_ball_self hε⟩, ?_⟩
    rintro z ⟨hzV₀, hzB⟩ hz1
    rcases lt_or_eq_of_le hz1 with hlt | heq1
    · rw [testTrace_eqOn_disk φ n (mem_disk_iff.mpr hlt)]
      exact hV₀eq z hzV₀ (mem_disk_iff.mpr hlt)
    · have hz_norm : ‖z‖ = 1 := heq1
      have hz_arc : z ∈ seamArc k m (n - 1) :=
        harcnear z hz_norm (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hzB)
      have hσz : (1 : ℂ) / (starRingEnd ℂ) z = z := sigma_fix_circle hz_norm
      have hFz : ((glue φ (n - 1)) ∘ fun z : ℂ => 1 / (starRingEnd ℂ) z) z = φ (n - 1) z := by
        simp only [Function.comp_apply, hσz, glue, if_pos (le_of_eq hz_norm)]
      rw [testTrace_receiving φ hz_arc, hFz]

/-! ### Continuity of the boundary flux up to the closed disk -/

/-- **The boundary flux `conj(∂ u)·(testTrace φ)` is continuous up to the closed disk** — the
`hFxc`/`hFyc` hypothesis of `first_green_disk`.  Interior points use `fderivWithin = fderiv` and
`testTrace = φ`; punctures use `SuppAwayP` (`testTrace = 0` on a neighborhood — so the flux is
locally `0` regardless of any derivative behavior of `u`, the exact O1 `cutP`-pattern); other
boundary points use the two smooth closed-disk germs (`exists_germ_closedBall` for `u`,
`exists_germ_closedBall_test` for `testTrace φ`). -/
lemma continuousOn_flux_test (hu : IsSmooth k m u) (hsv : SeamVal k u)
    (hsm : IsSmooth k m φ) (hsupp : SuppAwayP k m φ) (n : ZMod (2 * m)) (e : ℂ) :
    ContinuousOn (fun w => (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1) w e)
        * testTrace k m φ n w) (Metric.closedBall 0 1) := by
  intro w₀ hw₀
  have hn0 : ‖w₀‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hw₀
  rcases lt_or_eq_of_le hn0 with hlt | heq
  · -- interior point: `fderivWithin = fderiv`, `testTrace = φ`, everything smooth
    have hwdisk : w₀ ∈ disk := mem_disk_iff.mpr hlt
    have hcdu : ContDiffAt ℝ ∞ (u n) w₀ := (hu.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hwdisk)
    have hcdφ : ContDiffAt ℝ ∞ (φ n) w₀ := (hsm.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hwdisk)
    have hEq : (fun w => (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1) w e)
          * testTrace k m φ n w)
        =ᶠ[𝓝 w₀] (fun w => (starRingEnd ℂ) (fderiv ℝ (u n) w e) * φ n w) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hwdisk] with z hz
      rw [fderivWithin_of_mem_nhds
        (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall),
        testTrace_eqOn_disk φ n hz]
    have hfd : ContinuousAt (fun w => fderiv ℝ (u n) w e) w₀ :=
      ((hcdu.fderiv_right (m := 0) (by exact_mod_cast le_top)).continuousAt).clm_apply
        continuousAt_const
    have hcont : ContinuousAt (fun w => (starRingEnd ℂ) (fderiv ℝ (u n) w e) * φ n w) w₀ :=
      ((Complex.continuous_conj.continuousAt).comp hfd).mul hcdφ.continuousAt
    exact ((hcont.congr hEq.symm).continuousWithinAt)
  · -- boundary point
    by_cases hpunc : w₀ ∈ punctures k
    · -- puncture: `testTrace = 0` nearby (SuppAwayP), so the flux vanishes on a neighborhood
      obtain ⟨εs, hεs, hz0⟩ := hsupp
      have hF0 : (fun w => (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1) w e)
            * testTrace k m φ n w) =ᶠ[𝓝 w₀] (fun _ => (0 : ℂ)) := by
        filter_upwards [Metric.ball_mem_nhds w₀ hεs] with z hz
        have hzball : ‖z - w₀‖ < εs := by rwa [Metric.mem_ball, dist_eq_norm] at hz
        have htt0 : testTrace k m φ n z = 0 := by
          unfold testTrace
          split_ifs
          · exact hz0 n z ⟨w₀, hpunc, hzball⟩
          · exact hz0 n z ⟨w₀, hpunc, hzball⟩
          · exact hz0 (n - 1) z ⟨w₀, hpunc, hzball⟩
          · rfl
        rw [htt0, mul_zero]
      exact (continuousAt_const.congr hF0.symm).continuousWithinAt
    · -- other boundary point: the two smooth closed-disk germs
      obtain ⟨Fu, hFuc, Wu, hWuopen, hwWu, hWueq⟩ := exists_germ_closedBall hu hsv n heq hpunc
      obtain ⟨Fφ, hFφc, Wφ, hWφopen, hwWφ, hWφeq⟩ := exists_germ_closedBall_test hsm n heq hpunc
      have hev : ∀ᶠ z in 𝓝 w₀, DifferentiableAt ℝ Fu z := by
        filter_upwards [(hFuc.of_le two_le_infty).eventually (by simp)] with z hz
          using hz.differentiableAt (by norm_num)
      obtain ⟨V, hVsub, hVopen, hVmem⟩ := eventually_nhds_iff.mp hev
      have hfdF : ContinuousAt (fun w => fderiv ℝ Fu w e) w₀ :=
        ((hFuc.fderiv_right (m := 0) (by exact_mod_cast le_top)).continuousAt).clm_apply
          continuousAt_const
      have hRHS : ContinuousAt (fun w => (starRingEnd ℂ) (fderiv ℝ Fu w e) * Fφ w) w₀ :=
        ((Complex.continuous_conj.continuousAt).comp hfdF).mul hFφc.continuousAt
      refine (hRHS.continuousWithinAt).congr_of_eventuallyEq
        (eventually_nhdsWithin_iff.mpr ?_) ?_
      · filter_upwards [(hWuopen.inter (hVopen.inter hWφopen)).mem_nhds
          ⟨hwWu, hVmem, hwWφ⟩] with z hz hzcb
        obtain ⟨hzWu, hzV, hzWφ⟩ := hz
        have hz1 : ‖z‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hzcb
        have hfdw : fderivWithin ℝ (u n) (Metric.closedBall 0 1) z e = fderiv ℝ Fu z e := by
          have hcongr : u n =ᶠ[𝓝[Metric.closedBall (0 : ℂ) 1] z] Fu := by
            refine eventually_nhdsWithin_iff.mpr ?_
            filter_upwards [hWuopen.mem_nhds hzWu] with y hy hycb
            exact hWueq y hy (by rwa [Metric.mem_closedBall, dist_zero_right] at hycb)
          rw [hcongr.fderivWithin_eq (hWueq z hzWu hz1),
            (hVsub z hzV).hasFDerivAt.hasFDerivWithinAt.fderivWithin
              (uniqueDiffWithinAt_closedBall hzcb)]
        rw [hfdw, hWφeq z hzWφ hz1]
      · have hfdw₀ : fderivWithin ℝ (u n) (Metric.closedBall 0 1) w₀ e = fderiv ℝ Fu w₀ e := by
          have hcongr : u n =ᶠ[𝓝[Metric.closedBall (0 : ℂ) 1] w₀] Fu := by
            refine eventually_nhdsWithin_iff.mpr ?_
            filter_upwards [hWuopen.mem_nhds hwWu] with y hy hycb
            exact hWueq y hy (by rwa [Metric.mem_closedBall, dist_zero_right] at hycb)
          rw [hcongr.fderivWithin_eq (hWueq w₀ hwWu hn0),
            (hVsub w₀ hVmem).hasFDerivAt.hasFDerivWithinAt.fderivWithin
              (uniqueDiffWithinAt_closedBall hw₀)]
        rw [hfdw₀, hWφeq w₀ hwWφ hn0]

/-- **The radial boundary flux `conj(∂_ν u)·(testTrace φ)` is continuous up to the closed disk** —
the diagonal variant of `continuousOn_flux_test` with direction equal to the point itself (the
normal trace `∂_ν`), needed for the boundary θ-integral's integrability in the summation. -/
lemma continuousOn_flux_test_diag (hu : IsSmooth k m u) (hsv : SeamVal k u)
    (hsm : IsSmooth k m φ) (hsupp : SuppAwayP k m φ) (n : ZMod (2 * m)) :
    ContinuousOn (fun w => (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1) w w)
        * testTrace k m φ n w) (Metric.closedBall 0 1) := by
  intro w₀ hw₀
  have hn0 : ‖w₀‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hw₀
  rcases lt_or_eq_of_le hn0 with hlt | heq
  · -- interior point
    have hwdisk : w₀ ∈ disk := mem_disk_iff.mpr hlt
    have hcdu : ContDiffAt ℝ ∞ (u n) w₀ := (hu.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hwdisk)
    have hcdφ : ContDiffAt ℝ ∞ (φ n) w₀ := (hsm.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hwdisk)
    have hEq : (fun w => (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1) w w)
          * testTrace k m φ n w)
        =ᶠ[𝓝 w₀] (fun w => (starRingEnd ℂ) (fderiv ℝ (u n) w w) * φ n w) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hwdisk] with z hz
      rw [fderivWithin_of_mem_nhds
        (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall),
        testTrace_eqOn_disk φ n hz]
    have hfd : ContinuousAt (fun w => fderiv ℝ (u n) w w) w₀ :=
      ((hcdu.fderiv_right (m := 0) (by exact_mod_cast le_top)).continuousAt).clm_apply
        continuousAt_id
    have hcont : ContinuousAt (fun w => (starRingEnd ℂ) (fderiv ℝ (u n) w w) * φ n w) w₀ :=
      ((Complex.continuous_conj.continuousAt).comp hfd).mul hcdφ.continuousAt
    exact ((hcont.congr hEq.symm).continuousWithinAt)
  · -- boundary point
    by_cases hpunc : w₀ ∈ punctures k
    · obtain ⟨εs, hεs, hz0⟩ := hsupp
      have hF0 : (fun w => (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1) w w)
            * testTrace k m φ n w) =ᶠ[𝓝 w₀] (fun _ => (0 : ℂ)) := by
        filter_upwards [Metric.ball_mem_nhds w₀ hεs] with z hz
        have hzball : ‖z - w₀‖ < εs := by rwa [Metric.mem_ball, dist_eq_norm] at hz
        have htt0 : testTrace k m φ n z = 0 := by
          unfold testTrace
          split_ifs
          · exact hz0 n z ⟨w₀, hpunc, hzball⟩
          · exact hz0 n z ⟨w₀, hpunc, hzball⟩
          · exact hz0 (n - 1) z ⟨w₀, hpunc, hzball⟩
          · rfl
        rw [htt0, mul_zero]
      exact (continuousAt_const.congr hF0.symm).continuousWithinAt
    · obtain ⟨Fu, hFuc, Wu, hWuopen, hwWu, hWueq⟩ := exists_germ_closedBall hu hsv n heq hpunc
      obtain ⟨Fφ, hFφc, Wφ, hWφopen, hwWφ, hWφeq⟩ := exists_germ_closedBall_test hsm n heq hpunc
      have hev : ∀ᶠ z in 𝓝 w₀, DifferentiableAt ℝ Fu z := by
        filter_upwards [(hFuc.of_le two_le_infty).eventually (by simp)] with z hz
          using hz.differentiableAt (by norm_num)
      obtain ⟨V, hVsub, hVopen, hVmem⟩ := eventually_nhds_iff.mp hev
      have hfdF : ContinuousAt (fun w => fderiv ℝ Fu w w) w₀ :=
        ((hFuc.fderiv_right (m := 0) (by exact_mod_cast le_top)).continuousAt).clm_apply
          continuousAt_id
      have hRHS : ContinuousAt (fun w => (starRingEnd ℂ) (fderiv ℝ Fu w w) * Fφ w) w₀ :=
        ((Complex.continuous_conj.continuousAt).comp hfdF).mul hFφc.continuousAt
      refine (hRHS.continuousWithinAt).congr_of_eventuallyEq
        (eventually_nhdsWithin_iff.mpr ?_) ?_
      · filter_upwards [(hWuopen.inter (hVopen.inter hWφopen)).mem_nhds
          ⟨hwWu, hVmem, hwWφ⟩] with z hz hzcb
        obtain ⟨hzWu, hzV, hzWφ⟩ := hz
        have hz1 : ‖z‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hzcb
        have hfdw : fderivWithin ℝ (u n) (Metric.closedBall 0 1) z z = fderiv ℝ Fu z z := by
          have hcongr : u n =ᶠ[𝓝[Metric.closedBall (0 : ℂ) 1] z] Fu := by
            refine eventually_nhdsWithin_iff.mpr ?_
            filter_upwards [hWuopen.mem_nhds hzWu] with y hy hycb
            exact hWueq y hy (by rwa [Metric.mem_closedBall, dist_zero_right] at hycb)
          rw [hcongr.fderivWithin_eq (hWueq z hzWu hz1),
            (hVsub z hzV).hasFDerivAt.hasFDerivWithinAt.fderivWithin
              (uniqueDiffWithinAt_closedBall hzcb)]
        rw [hfdw, hWφeq z hzWφ hz1]
      · have hfdw₀ : fderivWithin ℝ (u n) (Metric.closedBall 0 1) w₀ w₀ = fderiv ℝ Fu w₀ w₀ := by
          have hcongr : u n =ᶠ[𝓝[Metric.closedBall (0 : ℂ) 1] w₀] Fu := by
            refine eventually_nhdsWithin_iff.mpr ?_
            filter_upwards [hWuopen.mem_nhds hwWu] with y hy hycb
            exact hWueq y hy (by rwa [Metric.mem_closedBall, dist_zero_right] at hycb)
          rw [hcongr.fderivWithin_eq (hWueq w₀ hwWu hn0),
            (hVsub w₀ hVmem).hasFDerivAt.hasFDerivWithinAt.fderivWithin
              (uniqueDiffWithinAt_closedBall hw₀)]
        rw [hfdw₀, hWφeq w₀ hwWφ hn0]

/-! ### The summed boundary flux vanishes -/

/-- At a puncture the trace representative is `0`: punctures satisfy `(w^k)² = −1`, so
`(w^k).re = 0`, which excludes them from BOTH arc families — the `else` branch of `testTrace`.
(No `SuppAwayP` needed here; the arc geometry alone kills it.) -/
lemma testTrace_puncture (φ : ZMod (2 * m) → ℂ → ℂ) (n : ZMod (2 * m)) {w : ℂ} (hnorm : ‖w‖ = 1)
    (hp : w ∈ punctures k) : testTrace k m φ n w = 0 := by
  have hzk : (w ^ k) ^ 2 = -1 := by
    have hpp : w ^ (2 * k) = -1 := hp
    rw [← hpp, ← pow_mul, mul_comm k 2]
  have hre : (w ^ k).re = 0 := by
    set z := w ^ k with hz
    have h2 : z * z = -1 := by rw [← sq]; exact hzk
    have himeq : z.re * z.im + z.im * z.re = 0 := by
      have := congrArg Complex.im h2; simpa [Complex.mul_im] using this
    have hreeq : z.re * z.re - z.im * z.im = -1 := by
      have := congrArg Complex.re h2; simpa [Complex.mul_re] using this
    by_contra hne
    have him0 : z.im = 0 := by
      rcases mul_eq_zero.mp (show z.re * z.im = 0 by linear_combination himeq / 2) with h | h
      · exact absurd h hne
      · exact h
    rw [him0] at hreeq; nlinarith [hreeq]
  have hnotarc : ∀ j : ZMod (2 * m), w ∉ seamArc k m j := by
    intro j hj
    simp only [seamArc, arc, Set.mem_ofPred_eq] at hj
    rw [hre, mul_zero] at hj; exact lt_irrefl 0 hj.2
  rw [testTrace, if_neg (by rw [hnorm]; norm_num), if_neg (hnotarc n), if_neg (hnotarc (n - 1))]

/-- **The summed boundary flux vanishes pointwise per angle.**  At a fixed boundary point
`w = e^{iθ}`, the `2m`-copy sum of `conj(∂_ν uₙ)·(testTrace φ n)` is `0`.  Off the punctures, the
seam involution `τ a = if w ∈ seamArc a then a+1 else a−1` pairs each copy with a neighbour, and the
paired flux cancels by `seam_flux_pointwise_cancel_conj` — with the shared trace `t := φ a w` read
off DEFINITIONALLY from `testTrace_giving`/`testTrace_receiving` (no `SeamVal` on `φ`).  At a
puncture every term is `0` (`testTrace_puncture`). -/
lemma sum_bTest_eq_zero (hu : IsSmooth k m u) (hsv : SeamVal k u)
    [NeZero m] (θ : ℝ) :
    ∑ n : ZMod (2 * m), (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1)
        (Complex.exp ((θ : ℂ) * Complex.I)) (Complex.exp ((θ : ℂ) * Complex.I)))
        * testTrace k m φ n (Complex.exp ((θ : ℂ) * Complex.I)) = 0 := by
  classical
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have : Fact (1 < 2 * m) := ⟨by have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m); omega⟩
  set w := Complex.exp ((θ : ℂ) * Complex.I) with hw_def
  have hnorm : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  by_cases hpunc : w ∈ punctures k
  · simp only [testTrace_puncture _ _ hnorm hpunc, mul_zero, Finset.sum_const_zero]
  · refine Finset.sum_involution
      (fun a _ => if w ∈ seamArc k m a then a + 1 else a - 1) ?_ ?_
      (fun _ _ => Finset.mem_univ _) ?_
    · -- pairwise cancellation
      intro a _
      by_cases ha : w ∈ seamArc k m a
      · simp only [if_pos ha]
        have hidx : (a + 1 - 1 : ZMod (2 * m)) = a := by ring
        have ha1 : w ∈ seamArc k m (a + 1 - 1) := by rw [hidx]; exact ha
        rw [testTrace_giving φ ha, testTrace_receiving φ ha1, hidx]
        exact seam_flux_pointwise_cancel_conj hu hsv ha (φ a w)
      · simp only [if_neg ha]
        have hmem : w ∈ seamArc k m (a - 1) := (mem_seamArc_or_pred hnorm hpunc a).resolve_left ha
        have hidx : (a - 1 + 1 : ZMod (2 * m)) = a := by ring
        have hlem := seam_flux_pointwise_cancel_conj hu hsv hmem (φ (a - 1) w)
        rw [hidx] at hlem
        rw [testTrace_receiving φ hmem, testTrace_giving φ hmem]
        linear_combination hlem
    · -- `τ a ≠ a`
      intro a _ _
      have h10 : (1 : ZMod (2 * m)) ≠ 0 := one_ne_zero
      by_cases ha : w ∈ seamArc k m a
      · simp only [if_pos ha]
        exact fun h => h10 (add_left_cancel (show a + 1 = a + 0 from by rw [add_zero]; exact h))
      · simp only [if_neg ha]; exact fun h => h10 (by rwa [sub_eq_self] at h)
    · -- involution
      intro a _
      by_cases ha : w ∈ seamArc k m a
      · rw [if_pos ha, if_neg (fun h => notMem_seamArc_succ ha h)]; ring
      · rw [if_neg ha, if_pos ((mem_seamArc_or_pred hnorm hpunc a).resolve_left ha)]; ring

/-- **The summed boundary θ-integral vanishes.**  Swapping the finite sum with the boundary
θ-integral (each summand continuous, hence interval-integrable, via `continuousOn_flux_test_diag`)
and applying the pointwise cancellation `sum_bTest_eq_zero`. -/
lemma sum_bTestFlux_eq_zero (hu : IsSmooth k m u) (hsv : SeamVal k u) (hsm : IsSmooth k m φ)
    (hsupp : SuppAwayP k m φ) [NeZero m] :
    ∑ n : ZMod (2 * m), (∫ θ in (-π : ℝ)..π,
        (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1)
          (Complex.exp ((θ : ℂ) * Complex.I)) (Complex.exp ((θ : ℂ) * Complex.I)))
          * testTrace k m φ n (Complex.exp ((θ : ℂ) * Complex.I))) = 0 := by
  have hexp : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hmaps : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro θ; rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I θ)
  have hII : ∀ n : ZMod (2 * m), IntervalIntegrable
      (fun θ => (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1)
          (Complex.exp ((θ : ℂ) * Complex.I)) (Complex.exp ((θ : ℂ) * Complex.I)))
          * testTrace k m φ n (Complex.exp ((θ : ℂ) * Complex.I))) volume (-π) π := fun n =>
    ((continuousOn_flux_test_diag hu hsv hsm hsupp n).comp_continuous hexp hmaps).intervalIntegrable
      _ _
  rw [← intervalIntegral.integral_finsetSum (fun n _ => hII n)]
  simp only [sum_bTest_eq_zero hu hsv, intervalIntegral.integral_zero]

/-! ### The per-copy weak-equation identity and the assembly -/

/-- **Per-copy weak identity.**  Testing the Jacobi equation `Δu = −potV·u` against `testTrace φ n`
through `first_green_disk`: the `n`-th `jacobiB` summand equals the seam boundary flux.  The
engine's interior term `conj(Δuₙ)·(testTrace φ n)` becomes the potential term via
`laplacian_eq_of_isJacobiField`; `testTrace = φ` on the open disk turns the gradient/potential
integrals into the honest `jacobiB` summand (the integrability from the O1 trunk facts). -/
lemma green_percopy_test (hk : 2 ≤ k) (hu : IsSmooth k m u) (hsv : SeamVal k u)
    (hjac : IsJacobiField k m u) (hφ : φ ∈ CcSmooth k m) (n : ZMod (2 * m))
    (hui : IntegrableOn (gradSq (u n)) disk) (hul : IntegrableOn (fun w => ‖u n w‖ ^ 2) disk) :
    ((∫ w in disk, gradInner (u n) (φ n) w)
        - ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * φ n w)
      = ∫ θ in (-π : ℝ)..π, (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1)
          (Complex.exp ((θ : ℂ) * Complex.I)) (Complex.exp ((θ : ℂ) * Complex.I)))
          * testTrace k m φ n (Complex.exp ((θ : ℂ) * Complex.I)) := by
  have hsm : IsSmooth k m φ := hφ.1
  have hsupp : SuppAwayP k m φ := hφ.2
  have hφreg : Regular φ := regular_of_mem hφ
  have hu2x : ∀ w ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℝ (fun z => fderiv ℝ (u n) z 1) w :=
    fun w hw => differentiableAt_fderiv_dir
      ((hu.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hw)) 1
  have hu2y : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      DifferentiableAt ℝ (fun z => fderiv ℝ (u n) z Complex.I) w :=
    fun w hw => differentiableAt_fderiv_dir
      ((hu.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hw)) Complex.I
  have hv : ∀ w ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℝ (testTrace k m φ n) w := by
    intro w hw
    have hφd : DifferentiableAt ℝ (φ n) w :=
      ((hsm.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt (by simp)
    refine hφd.congr_of_eventuallyEq ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz using testTrace_eqOn_disk φ n hz
  have hgradI : IntegrableOn (gradInner (u n) (φ n)) disk :=
    integrableOn_gradInner_left n hui hφreg
  have hpotI : IntegrableOn (fun w => (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * φ n w) disk :=
    integrableOn_potDens_left n hul (hu.1 n).continuousOn hφreg
  have hpt : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      gradInner (u n) (testTrace k m φ n) w
        + (starRingEnd ℂ) (laplacian (u n) w) * testTrace k m φ n w
      = gradInner (u n) (φ n) w - (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * φ n w := by
    intro w hw
    have hfd : fderiv ℝ (testTrace k m φ n) w = fderiv ℝ (φ n) w := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz using testTrace_eqOn_disk φ n hz
    have hgi : gradInner (u n) (testTrace k m φ n) w = gradInner (u n) (φ n) w := by
      unfold gradInner; rw [hfd]
    have htt : testTrace k m φ n w = φ n w := testTrace_eqOn_disk φ n hw
    have hlap : laplacian (u n) w = -((potV k w : ℂ) * u n w) :=
      laplacian_eq_of_isJacobiField hk hjac n hw
    rw [hgi, htt, hlap, map_neg, map_mul, Complex.conj_ofReal]
    ring
  have hInt : IntegrableOn (fun w => gradInner (u n) (testTrace k m φ n) w
      + (starRingEnd ℂ) (laplacian (u n) w) * testTrace k m φ n w) (Metric.ball 0 1) :=
    (hgradI.sub hpotI).congr_fun (fun w hw => (hpt w hw).symm) measurableSet_ball
  have hgreen := KsIndex.FirstGreen.first_green_disk hu2x hu2y hv
    (continuousOn_flux_test hu hsv hsm hsupp n 1)
    (continuousOn_flux_test hu hsv hsm hsupp n Complex.I) hInt
  have hLHS : (∫ w in Metric.ball (0 : ℂ) 1, gradInner (u n) (testTrace k m φ n) w
        + (starRingEnd ℂ) (laplacian (u n) w) * testTrace k m φ n w)
      = (∫ w in disk, gradInner (u n) (φ n) w)
        - ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * φ n w := by
    rw [← integral_sub hgradI hpotI]
    exact setIntegral_congr_fun measurableSet_ball hpt
  rw [hLHS] at hgreen
  exact hgreen

/-- **O2 — the weak equation.**  Every bounded smooth Jacobi field annihilates `jacobiB` against
every `C_c^∞` test.  Per copy, `green_percopy_test` turns the `jacobiB` summand into a seam boundary
flux; summed over the `2m` copies the flux cancels (`sum_bTestFlux_eq_zero`).  The energy/`L²`
integrability the per-copy step needs comes from O1 (`bddJacobi_le_energySmooth`). -/
theorem weakEq_of_boundedJacobi (hk : 2 ≤ k) [NeZero m] {u : ZMod (2 * m) → ℂ → ℂ}
    (hu : u ∈ BoundedJacobi k m) {φ : ZMod (2 * m) → ℂ → ℂ} (hφ : φ ∈ CcSmooth k m) :
    jacobiB k m u φ = 0 := by
  have huE : u ∈ EnergySmooth k m := bddJacobi_le_energySmooth hk hu
  have h2m : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  unfold jacobiB
  rw [Finset.sum_congr rfl (fun n _ => green_percopy_test hk hu.1 hu.2.2.2.2 hu.2.2.1 hφ n
    (huE.2.1 n) (huE.2.2.1 n))]
  exact sum_bTestFlux_eq_zero hu.1 hu.2.2.2.2 hφ.1 hφ.2

/-- **The faithful injection §5 milestone**: `BoundedJacobi k m ≤ WeakKer k m` — every bounded
smooth Jacobi field lies in the weak Jacobi kernel on the smooth energy carrier (O1's finite energy
plus O2's weak equation). -/
theorem bddJacobi_le_weakKer (hk : 2 ≤ k) [NeZero m] : BoundedJacobi k m ≤ WeakKer k m := by
  intro u hu
  exact ⟨bddJacobi_le_energySmooth hk hu, fun φ hφ => weakEq_of_boundedJacobi hk hu hφ⟩

end KsIndex.FaithfulInjection
