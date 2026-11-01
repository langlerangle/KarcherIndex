module

public import KsIndexLean.LocalContinuousExtension
public import Mathlib.Topology.Compactness.Lindelof

@[expose] public section


open Set MeasureTheory

namespace KsIndex.Trace
open KsIndex.WeakH1

lemma radial_ball_collar (x : Circle₁) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 1 / 2 ≤ c ∧ c < 1 ∧ ∃ A : Set Circle₁, IsOpen A ∧ x ∈ A ∧
      radialWedge c A ⊆ Metric.ball (x : ℂ) ε ∧
      ∀ w ∈ A, (w : ℂ) ∈ Metric.ball (x : ℂ) ε := by
  let δ := min (ε / 4) (1 / 4 : ℝ)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 4 := min_le_right _ _
  refine ⟨1 - δ, by linarith, by linarith, Metric.ball x δ, Metric.isOpen_ball,
    Metric.mem_ball_self hδ, ?_, ?_⟩
  · rintro z ⟨t, ht, w, hw, rfl⟩
    have hdist : dist (t • (w : ℂ)) (w : ℂ) = 1 - t := by
      have he : t • (w : ℂ) - (w : ℂ) = (t - 1) • (w : ℂ) := by
        rw [sub_smul, one_smul]
      rw [dist_eq_norm, he, norm_smul, mem_sphere_zero_iff_norm.mp w.property,
        mul_one, Real.norm_eq_abs, abs_of_neg (by linarith [ht.2])]
      ring
    have hw' : dist (w : ℂ) (x : ℂ) < δ := Metric.mem_ball.mp hw
    have hd := dist_triangle (t • (w : ℂ)) (w : ℂ) (x : ℂ)
    rw [hdist] at hd
    apply Metric.mem_ball.mpr
    linarith [ht.1]
  · intro w hw
    apply Metric.mem_ball.mpr
    have hw' : dist (w : ℂ) (x : ℂ) < δ := Metric.mem_ball.mp hw
    linarith

/-- Agreement on some boundary neighbourhood from a genuinely local continuous extension. -/
theorem exists_boundary_neighbourhood_agreement (u : ComplexH1) {O : Set ℂ} (hO : IsOpen O)
    {f : ℂ → ℂ} (hf : ContinuousOn f O) {x : Circle₁} (hx : (x : ℂ) ∈ O)
    (he : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), z ∈ O → valueCLM u z = f z) :
    ∃ A : Set Circle₁, IsOpen A ∧ x ∈ A ∧
      (diskTraceCLM u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] (fun w => f (w : ℂ)) := by
  obtain ⟨ε, hε, g, hg, hgf⟩ := exists_global_continuous_local hO hf hx
  obtain ⟨η, hη, hηO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hx)
  obtain ⟨c, hc, hc1, A, hA, hxA, hWA, hAA⟩ := radial_ball_collar x (lt_min hε hη)
  have hWε : radialWedge c A ⊆ Metric.ball (x : ℂ) ε :=
    hWA.trans (Metric.ball_subset_ball (min_le_left _ _))
  have hWO : radialWedge c A ⊆ O :=
    (hWA.trans (Metric.ball_subset_ball (min_le_right _ _))).trans hηO
  have hsub : annulusSet c 1 ⊆ (disk : Set ℂ) := by
    intro z hz
    simpa [disk, Metric.mem_ball, dist_zero_right] using hz.2
  have he' := he.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hw : ∀ᵐ z ∂volume.restrict (annulusSet c 1),
      z ∈ radialWedge c A → valueCLM u z = g z := by
    filter_upwards [he'] with z hz hzW
    exact (hz (hWO hzW)).trans (hgf (hWε hzW)).symm
  have ht := arcTrace_eq_of_wedge A hA.measurableSet u hc hc1 hg.continuousOn hw
  have ht' : boundaryRestrict A (diskTraceCLM u) =
      boundaryRestrict A (closedAnnulusProfile hg.continuousOn 1) := ht
  have hv := (closedAnnulusProfile_coe_ae hg.continuousOn (t := 1) (by norm_num)).filter_mono
    (ae_mono (Measure.restrict_le_self (s := A)))
  refine ⟨A, hA, hxA, ?_⟩
  filter_upwards [boundaryRestrict_coe_ae A (diskTraceCLM u),
    boundaryRestrict_coe_ae A (closedAnnulusProfile hg.continuousOn 1), hv,
    ae_restrict_mem hA.measurableSet] with w h1 h2 hvw hwA
  have heq := congrArg (fun v : Lp ℂ 2 (circleMeasure.restrict A) => v w) ht'
  rw [h1, h2, hvw] at heq
  simp only [one_smul] at heq
  exact heq.trans
    (hgf ((Metric.ball_subset_ball (min_le_left _ _)) (hAA w hwA)))

end KsIndex.Trace
