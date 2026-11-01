module

/-
KsIndexLean — SeamPureD: the pure-Dirichlet seam count on the natural spaces is ZERO, every class.

A `NatCc k false false` function vanishes near BOTH closed slits (`SuppAwaySet` on `slitC k` and
`slit k`), whose union is the whole unit circle, and vanishes outside the closed disk; with
smoothness on the open disk it is therefore globally `C^∞` — its own closed-disk extension — and
every boundary trace `Fm f ℓ 1` vanishes.  By the mode-sum identity `Qd_eq_tsum` every angular
mode is then nonnegative (`modeTerm_nonneg` with the full trace kill; the head σ-signs are
irrelevant at zero trace), so `Qd ≥ 0` on the whole space and `formIndex_le_of_domMap` with the
EMPTY head gives

  `formIndex (Qd k) (NatCc k false false ⊓ Erot1 k r) = 0`   (`k ≥ 3`, every class `r`).

This is the `pureD` value (`dCount = 0`) of `SingleDiskBridge.SeamBridge` on the natural spaces —
the paper's row `ind_{D,j}(Ξ_k^{(0,π)}) = 0` of Proposition `D_and_N_half_period`.
-/
public import KsIndexLean.SeamUpper

@[expose] public section


noncomputable section

open Complex MeasureTheory Set Filter Topology
open KsIndex.Parseval KsIndex.FourierMode KsIndex.Radial KsIndex.Surface KsIndex.SurfaceForm
  KsIndex.SingleDiskBridge KsIndex.FormIndex KsIndex.PiAssembly KsIndex.Bracket
open scoped ContDiff

namespace KsIndex.SingleDisk

variable {k : ℕ}

/-- A pure-Dirichlet natural test function vanishes on a uniform neighbourhood of every point of
the unit circle (the two closed slits cover the circle). -/
lemma dd_vanish_near_circle {f : ℂ → ℂ} (hf : f ∈ NatCc k false false) :
    ∃ ε > 0, ∀ w₀ : ℂ, ‖w₀‖ = 1 → ∀ w ∈ Metric.ball w₀ ε, f w = 0 := by
  obtain ⟨_, h1, h0, _, _⟩ := mem_NatCc.mp hf
  obtain ⟨ε₁, hε₁, h₁⟩ := h1
  obtain ⟨ε₂, hε₂, h₂⟩ := h0
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun w₀ hw₀ w hw => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hw
  rcases le_total 0 ((w₀ ^ k).re) with hre | hre
  · exact h₁ w ⟨w₀, ⟨hw₀, hre⟩, hw.trans_le (min_le_left _ _)⟩
  · exact h₂ w ⟨w₀, ⟨hw₀, hre⟩, hw.trans_le (min_le_right _ _)⟩

/-- A pure-Dirichlet natural test function is globally smooth: it is its own extension. -/
lemma dd_contDiff {f : ℂ → ℂ} (hf : f ∈ NatCc k false false) : ContDiff ℝ ∞ f := by
  obtain ⟨hsm, _, _, hout, _⟩ := mem_NatCc.mp hf
  obtain ⟨ε, hε, hvan⟩ := dd_vanish_near_circle hf
  rw [contDiff_iff_contDiffAt]
  intro w₀
  rcases lt_trichotomy ‖w₀‖ 1 with hlt | heq | hgt
  · exact hsm.contDiffAt (Metric.isOpen_ball.mem_nhds (mem_disk_iff.mpr hlt))
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds w₀ hε] with w hw
    exact hvan w₀ heq w hw
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    have hopen : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hgt] with w hw
    exact hout w hw

/-- Every boundary trace of a pure-Dirichlet natural test function vanishes. -/
lemma dd_trace_zero {f : ℂ → ℂ} (hf : f ∈ NatCc k false false) (ℓ : ℤ) : Fm f ℓ 1 = 0 := by
  obtain ⟨ε, hε, hvan⟩ := dd_vanish_near_circle hf
  have hs : slice f 1 = fun _ => (0 : ℂ) := by
    funext θ
    simp only [slice]
    have hn : ‖((1 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)‖ = 1 := by
      rw [norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]; norm_num
    exact hvan _ hn _ (Metric.mem_ball_self hε)
  unfold Fm
  rw [hs]
  unfold fc
  simp

/-- **The pure-Dirichlet seam count vanishes on the natural spaces** (`k ≥ 3`, every class `r`):
`ind(Qd k) = 0` on `NatCc k false false ⊓ Erot1 k r`.  This is `SeamBridge.pureD` with
`dCount = 0` on `NatCc` — the paper's `ind_{D,j}(Ξ_k^{(0,π)}) = 0`. -/
theorem seamNat_pureD (hk : 3 ≤ k) (r : ℕ) :
    formIndex (Qd k) (NatCc k false false ⊓ Erot1 k r) = 0 := by
  refine le_antisymm ?_ zero_le
  have h1i : (1 : WithTop ℕ∞) ≤ ∞ := le_trans (by norm_num) KsIndex.Surface.two_le_infty
  have key : ∀ u : ↥(NatCc k false false ⊓ Erot1 k r), 0 ≤ Qd k (u : ℂ → ℂ) := by
    intro u
    have hf : (u : ℂ → ℂ) ∈ NatCc k false false := (Submodule.mem_inf.mp u.2).1
    have hfE : (u : ℂ → ℂ) ∈ Erot1 k r := (Submodule.mem_inf.mp u.2).2
    have hG : ContDiff ℝ 1 (u : ℂ → ℂ) := (dd_contDiff hf).of_le h1i
    have hGeq : ∀ w ∈ disk, (u : ℂ → ℂ) w = (u : ℂ → ℂ) w := fun _ _ => rfl
    have htrace : ∀ ℓ : ℤ, ℓ ∈ KsIndex.SeamUpper.headSet k r → Fm (u : ℂ → ℂ) ℓ 1 = 0 :=
      fun ℓ _ => dd_trace_zero hf ℓ
    have hQ : Qd k (u : ℂ → ℂ) = 2 * Real.pi * ∑' ℓ : ℤ,
        ∫ s in (0 : ℝ)..1, lhsC k ℓ.natAbs (Fm (u : ℂ → ℂ) ℓ) (FmD (u : ℂ → ℂ) ℓ) s :=
      Qd_eq_tsum hG (by omega)
    rw [hQ]
    refine mul_nonneg (by positivity) (tsum_nonneg fun ℓ => ?_)
    exact KsIndex.SeamUpper.modeTerm_nonneg hk hG hGeq hfE htrace ℓ
  have h := formIndex_le_of_domMap
      (T := (0 : ↥(NatCc k false false ⊓ Erot1 k r) →ₗ[ℂ] (Fin 0 → ℂ)))
      (fun u _ => key u)
  simpa using h

end KsIndex.SingleDisk
