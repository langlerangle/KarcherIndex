module

/-
# Boundedness of Jacobi fields in the `k = 3` energy space

For nonzero `m`, a Jacobi field in `EnergySmooth 3 m` is bounded. This carrier
includes value L², finite Dirichlet energy, smoothness and seam compatibility.
The result here is specialized to that carrier and the chain encoding.

At each puncture, `endField_memLp_bundle` supplies the chart field's L² value
and the gradients of its real and imaginary parts. The chart field satisfies
the pulled-back Jacobi equation away from the origin. Puncture removability
therefore bounds it near the origin, and shrinking chart coverage transfers
that bound to every physical copy near the given puncture.

`end_bounds_of_jacobi` supplies a radius and bound for each puncture, uniform
in the copy index. `isBounded_of_end_bounds` then gives global boundedness.
The theorem does not identify the chain encoding with an ambient surface;
that identification belongs to the geometric transport results.
-/
public import KsIndexLean.GammaInteriorBounded
public import KsIndexLean.GammaAssembly
public import KsIndexLean.B2Foundation
public import KsIndexLean.EndChartPotential
public import KsIndexLean.EndFieldWitness
public import KsIndexLean.EndFieldEnergyProof

@[expose] public section


noncomputable section
open Set MeasureTheory Complex TopologicalSpace
open KsIndex.Surface KsIndex.EndChart KsIndex.B2
  KsIndex.FaithfulInjection KsIndex.PunctureRemoval KsIndex.EndField

namespace KsIndex.GammaProducer

variable {m : ℕ}

/-! ### Chart-field boundedness near the puncture preimage

`chartField_bounded_endIdx` applies puncture removability to the coverage
index `endIdx m c p`, using the chart field's regularity, equation and L² inputs. -/

/-! ### From chart-field bounds to bounds on every copy

A chart-field bound and shrinking value coverage give a bound near a fixed
puncture, uniform in the copy index. The radius and constant may depend on
that puncture. -/
/-- **The near-puncture bound from removability and coverage.**
Given the chart field `endFieldWith p u idx` bounded near `ζ = 0` (the removability output `hbd`)
and the shrinking value-coverage `hcov`, the surface field `u` is bounded near `p`:
closed-disk points `w≠p` are covered (value `≤ M`); `w = p` by `PunctureZero`; `‖w‖>1` by the
exterior normalization; `C = max M 0`.  This is the assembly; the witness `idx`, `hbd`, `hcov`
are supplied below by the explicit end-field construction and energy proof. -/
theorem near_puncture_bound {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (hu : u ∈ EnergySmooth 3 m) {p : ℂ} (hp : p ∈ punctures 3) (idx : ℂ → ZMod (2 * m))
    (hbd : ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ ζ : ℂ, dist ζ 0 < δ → ζ ≠ 0 →
      ‖endFieldWith p u idx ζ‖ ≤ M)
    (hcov : ∀ r : ℝ, 0 < r → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ZMod (2 * m)) (w : ℂ),
      ‖w - p‖ < δ → ‖w‖ ≤ 1 → w ≠ p →
        ∃ ζ : ℂ, 0 < ‖ζ‖ ∧ ‖ζ‖ < r ∧ endFieldWith p u idx ζ = u n w) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (n : ZMod (2 * m)) (w : ℂ), ‖w - p‖ < δ → ‖u n w‖ ≤ C := by
  obtain ⟨δ', hδ', M, hM⟩ := hbd
  obtain ⟨δ, hδ, hcovδ⟩ := hcov δ' hδ'
  refine ⟨δ, hδ, max M 0, fun n w hw => ?_⟩
  by_cases hwp : w = p
  · rw [hwp, hu.2.2.2.1 n p hp, norm_zero]; exact le_max_right _ _
  · by_cases hw1 : 1 < ‖w‖
    · rw [hu.1.2.2 n w hw1, norm_zero]; exact le_max_right _ _
    · obtain ⟨ζ, hζ0, hζr, heq⟩ := hcovδ n w hw (not_lt.mp hw1) hwp
      rw [← heq]
      exact le_trans (hM ζ (by rw [dist_zero_right]; exact hζr) (norm_pos_iff.mp hζ0))
        (le_max_left _ _)

/-- **The chart field is bounded near zero.** Given the three `MemLp` facts on `ball 0 r₀` with `r₀ ≤ 1`, and the `c`-parity bit, the removability call produces the
chart-field bound `hbd`: the `C²` (`hsm`) and PDE (`hre`/`him`) obligations are the proved
`endField_contDiffAt_punctured` / `endField_hre` / `endField_him` (whose `‖ζ‖^m < 1` domain comes
from `‖ζ‖ < r₀ ≤ 1`). -/
lemma chartField_bounded_endIdx [NeZero m] {u : ZMod (2 * m) → ℂ → ℂ}
    (hu : u ∈ EnergySmooth 3 m) (hjac : IsJacobiField 3 m u) {p : ℂ} (hp : p ∈ punctures 3)
    (c : ZMod (2 * m)) (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ 3).im) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1)
    (hu2 : MemLp (endFieldWith p u (endIdx m c p)) 2 (volume.restrict (Metric.ball 0 r₀)))
    (hgr : MemLp (gradEnc (fun z => (endFieldWith p u (endIdx m c p) z).re)) 2
      (volume.restrict (Metric.ball 0 r₀)))
    (hgi : MemLp (gradEnc (fun z => (endFieldWith p u (endIdx m c p) z).im)) 2
      (volume.restrict (Metric.ball 0 r₀))) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ ζ : ℂ, dist ζ 0 < δ → ζ ≠ 0 →
      ‖endFieldWith p u (endIdx m c p) ζ‖ ≤ M := by
  have hp1 : ‖p‖ = 1 := EndChart.norm_eq_one_of_mem_punctures hp
  have hz₀ : (0 : ℂ) ∈ (⟨Metric.ball 0 r₀, Metric.isOpen_ball⟩ : Opens ℂ).carrier :=
    Metric.mem_ball_self hr₀
  have hdom : ∀ z ∈ (⟨Metric.ball 0 r₀, Metric.isOpen_ball⟩ : Opens ℂ).carrier \ {0},
      z ≠ 0 ∧ ‖z‖ ^ m < 1 := by
    intro z hz
    have hzne : z ≠ 0 := by simpa using hz.2
    have hznorm : ‖z‖ < r₀ := by
      have := hz.1; rw [Metric.mem_ball, dist_zero_right] at this; exact this
    exact ⟨hzne, pow_lt_one₀ (norm_nonneg z) (lt_of_lt_of_le hznorm hr₀1) (NeZero.ne m)⟩
  refine bounded_near_complex_of_smooth_punctured (Ω := ⟨Metric.ball 0 r₀, Metric.isOpen_ball⟩)
    (z₀ := 0) hz₀ (V := endPotential p m) (F := endFieldWith p u (endIdx m c p))
    ?_ ?_ ?_ ?_ ?_ hu2 hgr hgi
  · intro K _ hK
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (contDiff_endPotential p m).continuous.continuousOn
    exact ⟨C, fun z hz => by simpa [Real.norm_eq_abs] using hC z hz⟩
  · exact (contDiff_endPotential p m).continuous.measurable
  · intro z hz
    exact endField_contDiffAt_punctured p hp1 hp hu.1 hu.2.2.2.2 c hbit z (hdom z hz).1 (hdom z hz).2
  · intro z hz
    exact endField_hre p hp1 hp hu.1 hjac hu.2.2.2.2 c hbit z (hdom z hz).1 (hdom z hz).2
  · intro z hz
    exact endField_him p hp1 hp hu.1 hjac hu.2.2.2.2 c hbit z (hdom z hz).1 (hdom z hz).2

/-- For each puncture, the chart-field bound and coverage supply a neighborhood bound
uniform over all copies, via `near_puncture_bound`. -/
theorem end_bounds_of_jacobi [NeZero m] {u : ZMod (2 * m) → ℂ → ℂ}
    (hu : u ∈ EnergySmooth 3 m) (hjac : IsJacobiField 3 m u) :
    ∀ p ∈ punctures 3, ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ n (w : ℂ),
      ‖w - p‖ < δ → ‖u n w‖ ≤ C := by
  intro p hp
  -- choose the parity bit for `c`; `idx = endIdx m c p`
  obtain ⟨c, hbit⟩ := exists_parity_pin (m := m) hp
  -- The actual end field has full-chart L² value and both gradients, derived
  -- from EnergySmooth by finite-sheet/reflection energy transport and the annular anchor.
  obtain ⟨r₀, hr₀, hr₀1, hu2, hgr, hgi⟩ :
      ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧
        MemLp (endFieldWith p u (endIdx m c p)) 2 (volume.restrict (Metric.ball 0 r₀)) ∧
        MemLp (gradEnc (fun z => (endFieldWith p u (endIdx m c p) z).re)) 2
          (volume.restrict (Metric.ball 0 r₀)) ∧
        MemLp (gradEnc (fun z => (endFieldWith p u (endIdx m c p) z).im)) 2
          (volume.restrict (Metric.ball 0 r₀)) := by
    exact ⟨1/4, by norm_num, by norm_num,
      endField_memLp_bundle (Nat.pos_of_ne_zero (NeZero.ne m)) ⟨u, hu⟩ p hp c hbit⟩
  exact near_puncture_bound hu hp (endIdx m c p)
    (chartField_bounded_endIdx hu hjac hp c hbit hr₀ hr₀1 hu2 hgr hgi)
    (endField_coverage (Nat.pos_of_ne_zero (NeZero.ne m)) p (EndChart.norm_eq_one_of_mem_punctures hp) hu c)

/-! ### Global boundedness for `k = 3` -/

/-- A Jacobi field in `EnergySmooth 3 m` is bounded. This is the finite-energy
to boundedness direction for this carrier, whose hypotheses include value L²,
smoothness, and seam compatibility. The paper’s `jacobi_finiteness` lemma is
stated for every k ≥ 3 and assumes only finite Dirichlet energy. -/
theorem bounded_of_jacobi_energySmooth [NeZero m] {u : ZMod (2 * m) → ℂ → ℂ}
    (hu : u ∈ EnergySmooth 3 m) (hjac : IsJacobiField 3 m u) : IsBounded u :=
  isBounded_of_end_bounds (by norm_num) hu (end_bounds_of_jacobi hu hjac)

end KsIndex.GammaProducer
