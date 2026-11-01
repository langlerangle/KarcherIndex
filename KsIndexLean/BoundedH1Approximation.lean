module

public import KsIndexLean.RadialH1Carrier
public import KsIndexLean.WeakPunctureApproximation

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Radial truncations converge in the original adopted H1 norm for every H1 function. -/
theorem diskRadial_tendsto {t : ℕ → ℝ} (ht : ∀ n, 0 ≤ t n)
    (ht0 : Tendsto t atTop (𝓝 0)) (u : ComplexH1) :
    Tendsto (fun n => diskRadial (t n) (ht n) u) atTop (𝓝 u) := by
  have hv := radial_value_toLp_tendsto ht ht0 (Lp.memLp (valueCLM u))
  have hx := radial_jet_toLp_tendsto ht ht0 (Lp.memLp (valueCLM u)) (Lp.memLp (dxLp u))
  have hy := radial_jet_toLp_tendsto ht ht0 (Lp.memLp (valueCLM u)) (Lp.memLp (dyLp u))
  rw [Lp.toLp_coeFn] at hv hx hy
  have ev : (fun n => valueCLM (diskRadial (t n) (ht n) u)) =
      (fun n => radialValueLp (t n) (ht n) u) :=
    funext fun n => (diskRadial_coordinates (t n) (ht n) u).1
  have ex : (fun n => dxLp (diskRadial (t n) (ht n) u)) =
      (fun n => radialDxLp (t n) (ht n) u) :=
    funext fun n => (diskRadial_coordinates (t n) (ht n) u).2.1
  have ey : (fun n => dyLp (diskRadial (t n) (ht n) u)) =
      (fun n => radialDyLp (t n) (ht n) u) :=
    funext fun n => (diskRadial_coordinates (t n) (ht n) u).2.2
  have hv' : Tendsto (fun n => valueCLM (diskRadial (t n) (ht n) u)) atTop (𝓝 (valueCLM u)) := by
    rw [ev]
    exact hv
  have hx' : Tendsto (fun n => dxLp (diskRadial (t n) (ht n) u)) atTop (𝓝 (dxLp u)) := by
    rw [ex]
    exact hx
  have hy' : Tendsto (fun n => dyLp (diskRadial (t n) (ht n) u)) atTop (𝓝 (dyLp u)) := by
    rw [ey]
    exact hy
  have hv2 := (tendsto_iff_norm_sub_tendsto_zero.mp hv').pow 2
  have hx2 := (tendsto_iff_norm_sub_tendsto_zero.mp hx').pow 2
  have hy2 := (tendsto_iff_norm_sub_tendsto_zero.mp hy').pow 2
  have hid n : ‖diskRadial (t n) (ht n) u - u‖ ^ 2 =
      ‖valueCLM (diskRadial (t n) (ht n) u) - valueCLM u‖ ^ 2 +
      ‖dxLp (diskRadial (t n) (ht n) u) - dxLp u‖ ^ 2 +
      ‖dyLp (diskRadial (t n) (ht n) u) - dyLp u‖ ^ 2 := by
    rw [coordinate_graph_norm_sq]
    change ‖valueCLM (diskRadial (t n) (ht n) u - u)‖ ^ 2 +
      ‖dxCLM (diskRadial (t n) (ht n) u - u)‖ ^ 2 +
      ‖dyCLM (diskRadial (t n) (ht n) u - u)‖ ^ 2 = _
    simp only [map_sub]
    rfl
  have hsq : Tendsto (fun n => ‖diskRadial (t n) (ht n) u - u‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hid]
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_add] using (hv2.add hx2).add hy2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

/-- Bounded values are dense in the actual disk H1 carrier. -/
theorem exists_bounded_h1_approx (u : ComplexH1) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ComplexH1, ∃ M : ℝ, 0 < M ∧ ‖v - u‖ < ε ∧
      ∀ᵐ z ∂volume.restrict disk, ‖valueCLM v z‖ ≤ M := by
  have ht (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hc := diskRadial_tendsto (fun n => (ht n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat u
  obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.mp hc ε hε).exists
  refine ⟨diskRadial _ (ht n).le u, (Real.sqrt (1 / ((n : ℝ) + 1)))⁻¹,
    inv_pos.mpr (Real.sqrt_pos.mpr (ht n)), ?_, diskRadial_bounded (ht n) u⟩
  simpa only [dist_eq_norm] using hn

/-- Every disk H1 value admits close bounded approximants avoiding all punctures.
Boundary/phase-domain preservation is a separate obligation. -/
theorem exists_h1_puncture_approx {k : ℕ} (hk : 1 ≤ k) (u : ComplexH1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ComplexH1, ∃ M ρ : ℝ, 0 < M ∧ 0 < ρ ∧ ‖v - u‖ < ε ∧
      (∀ᵐ z ∂volume.restrict disk, ‖valueCLM v z‖ ≤ M) ∧
      (∀ᵐ z ∂volume.restrict disk,
        (∃ p ∈ Surface.punctures k, ‖z - p‖ ≤ ρ) → valueCLM v z = 0) := by
  obtain ⟨w, M, hM, hw, hb⟩ := exists_bounded_h1_approx u (half_pos hε)
  obtain ⟨v, ρ, hρ, hv, hvb, hvz⟩ := exists_bounded_puncture_approx hk w hb (half_pos hε)
  refine ⟨v, M, ρ, hM, hρ, ?_, hvb, hvz⟩
  calc
    ‖v - u‖ = ‖(v - w) + (w - u)‖ := by congr 1; abel
    _ ≤ ‖v - w‖ + ‖w - u‖ := norm_add_le _ _
    _ < ε := by linarith

end KsIndex.Trace
