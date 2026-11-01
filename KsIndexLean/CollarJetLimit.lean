module

public import KsIndexLean.CollarInversionDerivative
public import KsIndexLean.BoundedScalarL2

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket

lemma sigmaJetPullback_memLp {X Y : ℂ → ℂ}
    (hX : MemLp X 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hY : MemLp Y 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2))) (d : ℂ) :
    MemLp (sigmaJetPullback X Y d) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) :=
  (bounded_real_smul_memLp (measurable_fderiv_apply_const ℝ σ d).re.aestronglyMeasurable
    (memLp_sigma_collar hX) (sigma_collar_derivative_re_bound d)).add
  (bounded_real_smul_memLp (measurable_fderiv_apply_const ℝ σ d).im.aestronglyMeasurable
    (memLp_sigma_collar hY) (sigma_collar_derivative_im_bound d))

lemma sigmaJetPullback_sub (X Y U V : ℂ → ℂ) (d : ℂ) :
    sigmaJetPullback (X - U) (Y - V) d =
      sigmaJetPullback X Y d - sigmaJetPullback U V d := by
  funext z
  simp only [sigmaJetPullback, Pi.sub_apply, smul_sub]
  abel

lemma sigmaJetPullback_tendsto_zero {X Y : ℕ → ℂ → ℂ}
    (hX : ∀ n, MemLp (X n) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hY : ∀ n, MemLp (Y n) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (htX : Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 0))
    (htY : Tendsto (fun n => (hY n).toLp (Y n)) atTop (𝓝 0)) (d : ℂ) :
    Tendsto (fun n => (sigmaJetPullback_memLp (hX n) (hY n) d).toLp
      (sigmaJetPullback (X n) (Y n) d)) atTop (𝓝 0) := by
  have hx := bounded_real_smul_tendsto_zero
    (measurable_fderiv_apply_const ℝ σ d).re.aestronglyMeasurable
    (fun n => memLp_sigma_collar (hX n)) (sigma_collar_derivative_re_bound d)
    (toLp_sigma_collar_tendsto_zero hX htX)
  have hy := bounded_real_smul_tendsto_zero
    (measurable_fderiv_apply_const ℝ σ d).im.aestronglyMeasurable
    (fun n => memLp_sigma_collar (hY n)) (sigma_collar_derivative_im_bound d)
    (toLp_sigma_collar_tendsto_zero hY htY)
  have hh := hx.add hy
  simp only [zero_add] at hh
  exact hh

/-- Strong coordinate-jet convergence survives the actual inversion derivative pullback. -/
theorem sigmaJetPullback_tendsto {X Y : ℕ → ℂ → ℂ} {U V : ℂ → ℂ}
    (hX : ∀ n, MemLp (X n) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hY : ∀ n, MemLp (Y n) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hU : MemLp U 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hV : MemLp V 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (htX : Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (hU.toLp U)))
    (htY : Tendsto (fun n => (hY n).toLp (Y n)) atTop (𝓝 (hV.toLp V))) (d : ℂ) :
    Tendsto (fun n => (sigmaJetPullback_memLp (hX n) (hY n) d).toLp
      (sigmaJetPullback (X n) (Y n) d)) atTop
      (𝓝 ((sigmaJetPullback_memLp hU hV d).toLp (sigmaJetPullback U V d))) := by
  have hx : Tendsto (fun n => ((hX n).sub hU).toLp (X n - U)) atTop (𝓝 0) := by
    have hh := htX.sub_const (hU.toLp U)
    simp only [sub_self] at hh
    exact hh
  have hy : Tendsto (fun n => ((hY n).sub hV).toLp (Y n - V)) atTop (𝓝 0) := by
    have hh := htY.sub_const (hV.toLp V)
    simp only [sub_self] at hh
    exact hh
  have hh := sigmaJetPullback_tendsto_zero (fun n => (hX n).sub hU)
    (fun n => (hY n).sub hV) hx hy d
  simp only [sigmaJetPullback_sub] at hh
  exact tendsto_sub_nhds_zero_iff.mp hh

end KsIndex.Trace
