module

public import KsIndexLean.RadialTruncationLimit

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace

lemma radial_value_memLp {μ : Measure ℂ} {t : ℝ} (ht : 0 ≤ t)
    {u : ℂ → ℂ} (hu : MemLp u 2 μ) : MemLp (radialTruncate t ∘ u) 2 μ :=
  (radialTruncate_lipschitz ht).comp_memLp (radialTruncate_zero t) hu

lemma radial_jet_memLp {μ : Measure ℂ} {t : ℝ} (ht : 0 ≤ t)
    {u v : ℂ → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    MemLp (fun z => radialJet t (u z) (v z)) 2 μ :=
  bounded_operator_memLp ((radialJet_continuous ht).comp_aestronglyMeasurable
    hu.aestronglyMeasurable) hv (Eventually.of_forall fun z => radialJet_norm_le ht (u z))

/-- Radial truncation converges in L2 for every L2 input, without a bounded-value hypothesis. -/
theorem radial_value_toLp_tendsto {μ : Measure ℂ} {t : ℕ → ℝ}
    (ht : ∀ n, 0 ≤ t n) (ht0 : Tendsto t atTop (𝓝 0))
    {u : ℂ → ℂ} (hu : MemLp u 2 μ) :
    Tendsto (fun n => (radial_value_memLp (ht n) hu).toLp (radialTruncate (t n) ∘ u))
      atTop (𝓝 (hu.toLp u)) := by
  let hf := fun n => radial_value_memLp (ht n) hu
  have hb : Integrable (fun z => (2 * ‖u z‖) ^ 2) μ := by
    have hi := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
    have he : (fun z => (2 * ‖u z‖) ^ 2) = (fun z => 4 * ‖u z‖ ^ 2) := by
      funext z
      ring
    rw [he]
    exact hi.const_mul 4
  have hbound n : ∀ᵐ z ∂μ, ‖((radialTruncate (t n) ∘ u) - u) z‖ ≤ 2 * ‖u z‖ := by
    apply Eventually.of_forall
    intro z
    change ‖radialTruncate (t n) (u z) - u z‖ ≤ _
    have h := norm_sub_le (radialTruncate (t n) (u z)) (u z)
    linarith [radialTruncate_norm_le (ht n) (u z)]
  have hpoint : ∀ᵐ z ∂μ, Tendsto
      (fun n => ((radialTruncate (t n) ∘ u) - u) z) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro z
    have h := ((radialTruncate_tendsto (u z)).comp ht0).sub_const (u z)
    simp only [sub_self] at h
    exact h
  have h := toLp_tendsto_zero_of_dominated (fun n => (hf n).sub hu) hb hbound hpoint
  exact tendsto_sub_nhds_zero_iff.mp h

/-- The radial weak-jet coefficient converges strongly on every L2 derivative field. -/
theorem radial_jet_toLp_tendsto {μ : Measure ℂ} {t : ℕ → ℝ}
    (ht : ∀ n, 0 ≤ t n) (ht0 : Tendsto t atTop (𝓝 0))
    {u v : ℂ → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Tendsto (fun n => (radial_jet_memLp (ht n) hu hv).toLp
      (fun z => radialJet (t n) (u z) (v z))) atTop (𝓝 (hv.toLp v)) := by
  have hA n : AEStronglyMeasurable (fun z => radialJet (t n) (u z)) μ :=
    (radialJet_continuous (ht n)).comp_aestronglyMeasurable hu.aestronglyMeasurable
  have hB : AEStronglyMeasurable (fun _ : ℂ => ContinuousLinearMap.id ℝ ℂ) μ :=
    aestronglyMeasurable_const
  have ha n : ∀ᵐ z ∂μ, ‖radialJet (t n) (u z)‖ ≤ 2 :=
    Eventually.of_forall fun z => radialJet_norm_le (ht n) (u z)
  have hb : ∀ᵐ z ∂μ, ‖(fun _ : ℂ => ContinuousLinearMap.id ℝ ℂ) z‖ ≤ (2 : ℝ) :=
    Eventually.of_forall fun _ => by norm_num
  have hAt : ∀ᵐ z ∂μ, Tendsto (fun n => radialJet (t n) (u z)) atTop
      (𝓝 (ContinuousLinearMap.id ℝ ℂ)) :=
    Eventually.of_forall fun z => (radialJet_tendsto (u z)).comp ht0
  have h := bounded_operator_tendsto hA hB (fun _ => hv) hv ha hb hAt tendsto_const_nhds
  exact h

end KsIndex.Trace
