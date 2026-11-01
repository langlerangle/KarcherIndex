module

public import KsIndexLean.ReflectionAverageJet

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.WeakH1

lemma phaseAverage_fixed_ae {μ : Measure ℂ} (s : ℂ) {u v : ℂ → ℂ}
    (h : ∀ᵐ z ∂μ, s * v z = u z) : phaseAverage s u v =ᵐ[μ] u := by
  filter_upwards [h] with z hz
  rw [phaseAverage_apply, hz]
  ring

/-- Reflection averaging converges to the original value when its actual AE parity holds. -/
theorem reflectionAverage_tendsto_fixed (s : ℂ) {u : ℕ → ℂ → ℂ} {v : ℂ → ℂ}
    (hu : ∀ n, MemLp (u n) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hv : MemLp v 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (ht : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hv.toLp v)))
    (hp : ∀ᵐ z ∂volume.restrict (annulusSet (1 / 2 : ℝ) 2), s * v (σ z) = v z) :
    Tendsto (fun n => (reflectionAverage_memLp s (hu n)).toLp (reflectionAverage s (u n)))
      atTop (𝓝 (hv.toLp v)) := by
  have he : (reflectionAverage_memLp s hv).toLp (reflectionAverage s v) = hv.toLp v := by
    apply Lp.ext
    have hh : reflectionAverage s v =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 2)] v := by
      rw [reflectionAverage_eq_phaseAverage]
      exact phaseAverage_fixed_ae s hp
    exact (reflectionAverage_memLp s hv).coeFn_toLp.trans (hh.trans hv.coeFn_toLp.symm)
  rw [← he]
  exact reflectionAverage_tendsto s hu hv ht

/-- Actual parity of the limiting weak jet identifies the averaged directional derivative limit. -/
theorem reflectionAverageJet_tendsto_fixed (s : ℂ) {X Y : ℕ → ℂ → ℂ} {U V : ℂ → ℂ}
    (hX : ∀ n, MemLp (X n) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hY : ∀ n, MemLp (Y n) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hU : MemLp U 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hV : MemLp V 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (htX : Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (hU.toLp U)))
    (htY : Tendsto (fun n => (hY n).toLp (Y n)) atTop (𝓝 (hV.toLp V))) (d : ℂ)
    (hp : ∀ᵐ z ∂volume.restrict (annulusSet (1 / 2 : ℝ) 2),
      s * sigmaJetPullback U V d z = Dxy U V z d) :
    Tendsto (fun n => (reflectionAverageJet_memLp s (hX n) (hY n) d).toLp
      (reflectionAverageJet s (X n) (Y n) d)) atTop
      (𝓝 ((Dxy_direction_memLp hU hV d).toLp (fun z => Dxy U V z d))) := by
  have he : (reflectionAverageJet_memLp s hU hV d).toLp (reflectionAverageJet s U V d) =
      (Dxy_direction_memLp hU hV d).toLp (fun z => Dxy U V z d) := by
    apply Lp.ext
    exact (reflectionAverageJet_memLp s hU hV d).coeFn_toLp.trans
      ((phaseAverage_fixed_ae s hp).trans (Dxy_direction_memLp hU hV d).coeFn_toLp.symm)
  rw [← he]
  exact reflectionAverageJet_tendsto s hX hY hU hV htX htY d

end KsIndex.Trace
