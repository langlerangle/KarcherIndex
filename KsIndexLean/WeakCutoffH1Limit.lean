module

public import KsIndexLean.WeakCutoffDerivativeLimit

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.PunctureCutoff KsIndex.FaithfulInjection

lemma diskCutoff_dx_tendsto {k : ℕ} (hk : 1 ≤ k) (u : ComplexH1) {M : ℝ}
    (hu : ∀ᵐ z ∂volume.restrict disk, ‖valueCLM u z‖ ≤ M) :
    Tendsto (fun j => dxLp (diskCutoff k j u)) atTop (𝓝 (dxLp u)) := by
  apply cutoff_coordinate_tendsto hk (dxLp u) _ (valueCLM u) 1
    (hfg := fun j => diskCutoff_dx_ae k j u) (hu := hu)
    (hm := (Lp.memLp (valueCLM u)).aestronglyMeasurable)
  intro j z
  have hd := ((cutP_contDiff k (cutoffEps_pos j)
    (cutoffEps_lt_one j)).differentiable (by simp)) z
  rw [show cutPC k (cutoffEps j) = (fun z => (cutP k (cutoffEps j) z : ℂ)) from rfl,
    gradSq_ofReal hd]
  exact le_add_of_nonneg_right (sq_nonneg _)

lemma diskCutoff_dy_tendsto {k : ℕ} (hk : 1 ≤ k) (u : ComplexH1) {M : ℝ}
    (hu : ∀ᵐ z ∂volume.restrict disk, ‖valueCLM u z‖ ≤ M) :
    Tendsto (fun j => dyLp (diskCutoff k j u)) atTop (𝓝 (dyLp u)) := by
  apply cutoff_coordinate_tendsto hk (dyLp u) _ (valueCLM u) Complex.I
    (hfg := fun j => diskCutoff_dy_ae k j u) (hu := hu)
    (hm := (Lp.memLp (valueCLM u)).aestronglyMeasurable)
  intro j z
  have hd := ((cutP_contDiff k (cutoffEps_pos j)
    (cutoffEps_lt_one j)).differentiable (by simp)) z
  rw [show cutPC k (cutoffEps j) = (fun z => (cutP k (cutoffEps j) z : ℂ)) from rfl,
    gradSq_ofReal hd]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- H1 convergence of puncture cutoffs for an almost-everywhere bounded weak H1 function.
The value bound is an explicit hypothesis; arbitrary unbounded H1 functions
require a separate approximation argument. -/
theorem diskCutoff_tendsto_of_bounded {k : ℕ} (hk : 1 ≤ k) (u : ComplexH1) {M : ℝ}
    (hu : ∀ᵐ z ∂volume.restrict disk, ‖valueCLM u z‖ ≤ M) :
    Tendsto (fun j => diskCutoff k j u) atTop (𝓝 u) := by
  have hv := (tendsto_iff_norm_sub_tendsto_zero.mp (diskCutoff_value_tendsto hk u)).pow 2
  have hx := (tendsto_iff_norm_sub_tendsto_zero.mp (diskCutoff_dx_tendsto hk u hu)).pow 2
  have hy := (tendsto_iff_norm_sub_tendsto_zero.mp (diskCutoff_dy_tendsto hk u hu)).pow 2
  have hid (j : ℕ) : ‖diskCutoff k j u - u‖ ^ 2 =
      ‖valueCLM (diskCutoff k j u) - valueCLM u‖ ^ 2 +
      ‖dxLp (diskCutoff k j u) - dxLp u‖ ^ 2 +
      ‖dyLp (diskCutoff k j u) - dyLp u‖ ^ 2 := by
    rw [coordinate_graph_norm_sq]
    change ‖valueCLM (diskCutoff k j u - u)‖ ^ 2 +
      ‖dxCLM (diskCutoff k j u - u)‖ ^ 2 +
      ‖dyCLM (diskCutoff k j u - u)‖ ^ 2 = _
    simp only [map_sub]
    rfl
  have hsq : Tendsto (fun j => ‖diskCutoff k j u - u‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hid]
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_add] using (hv.add hx).add hy
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

end KsIndex.Trace
