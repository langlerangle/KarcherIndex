module

public import KsIndexLean.BoundedOperatorL2Limit

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace

lemma bounded_operator_toLp_norm_le {μ : Measure ℂ} {A : ℂ → ℂ →L[ℝ] ℂ} {g : ℂ → ℂ}
    (hA : AEStronglyMeasurable A μ) (hg : MemLp g 2 μ) {C : ℝ}
    (hb : ∀ᵐ z ∂μ, ‖A z‖ ≤ C) :
    ‖(bounded_operator_memLp hA hg hb).toLp (fun z => A z (g z))‖ ≤ C * ‖hg.toLp g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(bounded_operator_memLp hA hg hb).coeFn_toLp, hg.coeFn_toLp, hb] with z hz hw hb
  rw [hz, hw]
  exact (A z).le_opNorm (g z) |>.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

lemma bounded_operator_tendsto_zero {μ : Measure ℂ}
    {A : ℕ → ℂ → ℂ →L[ℝ] ℂ} {g : ℕ → ℂ → ℂ}
    (hA : ∀ n, AEStronglyMeasurable (A n) μ) (hg : ∀ n, MemLp (g n) 2 μ) {C : ℝ}
    (hb : ∀ n, ∀ᵐ z ∂μ, ‖A n z‖ ≤ C)
    (ht : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 0)) :
    Tendsto (fun n => (bounded_operator_memLp (hA n) (hg n) (hb n)).toLp
      (fun z => A n z (g n z))) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have hnorm : Tendsto (fun n => ‖(hg n).toLp (g n)‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using ht.norm
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => bounded_operator_toLp_norm_le
    (hA n) (hg n) (hb n))
  simpa using hnorm.const_mul C

/-- Simultaneous strong L2 convergence of the input and bounded AE convergence of its
operator coefficient imply strong L2 convergence of the applied fields. -/
theorem bounded_operator_tendsto {μ : Measure ℂ}
    {A : ℕ → ℂ → ℂ →L[ℝ] ℂ} {B : ℂ → ℂ →L[ℝ] ℂ}
    {g : ℕ → ℂ → ℂ} {v : ℂ → ℂ}
    (hA : ∀ n, AEStronglyMeasurable (A n) μ) (hB : AEStronglyMeasurable B μ)
    (hg : ∀ n, MemLp (g n) 2 μ) (hv : MemLp v 2 μ) {C : ℝ}
    (ha : ∀ n, ∀ᵐ z ∂μ, ‖A n z‖ ≤ C) (hb : ∀ᵐ z ∂μ, ‖B z‖ ≤ C)
    (hAt : ∀ᵐ z ∂μ, Tendsto (fun n => A n z) atTop (𝓝 (B z)))
    (hgt : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 (hv.toLp v))) :
    Tendsto (fun n => (bounded_operator_memLp (hA n) (hg n) (ha n)).toLp
      (fun z => A n z (g n z))) atTop
      (𝓝 ((bounded_operator_memLp hB hv hb).toLp (fun z => B z (v z)))) := by
  have hdiff : Tendsto (fun n => ((hg n).sub hv).toLp (g n - v)) atTop (𝓝 0) := by
    have h := hgt.sub_const (hv.toLp v)
    simp only [sub_self] at h
    exact h
  have hfirst := bounded_operator_tendsto_zero hA (fun n => (hg n).sub hv) ha hdiff
  obtain ⟨he, hsecond⟩ := operator_error_tendsto_zero hA hB hv ha hb hAt
  have hsum := hfirst.add hsecond
  have hid n :
      (bounded_operator_memLp (hA n) ((hg n).sub hv) (ha n)).toLp
        (fun z => A n z ((g n - v) z)) +
        (he n).toLp (fun z => (A n z - B z) (v z)) =
      (bounded_operator_memLp (hA n) (hg n) (ha n)).toLp (fun z => A n z (g n z)) -
        (bounded_operator_memLp hB hv hb).toLp (fun z => B z (v z)) := by
    let x := (bounded_operator_memLp (hA n) ((hg n).sub hv) (ha n)).toLp
      (fun z => A n z ((g n - v) z))
    let y := (he n).toLp (fun z => (A n z - B z) (v z))
    let w := (bounded_operator_memLp (hA n) (hg n) (ha n)).toLp (fun z => A n z (g n z))
    let t := (bounded_operator_memLp hB hv hb).toLp (fun z => B z (v z))
    change x + y = w - t
    apply Lp.ext
    filter_upwards [Lp.coeFn_add x y, Lp.coeFn_sub w t,
      (bounded_operator_memLp (hA n) ((hg n).sub hv) (ha n)).coeFn_toLp,
      (he n).coeFn_toLp, (bounded_operator_memLp (hA n) (hg n) (ha n)).coeFn_toLp,
      (bounded_operator_memLp hB hv hb).coeFn_toLp] with z hadd hsub h1 h2 h3 h4
    rw [hadd, hsub]
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [h1, h2, h3, h4]
    simp only [Pi.sub_apply, map_sub, sub_apply]
    abel
  simp only [hid, zero_add] at hsum
  exact (tendsto_sub_nhds_zero_iff).mp hsum

end KsIndex.Trace
