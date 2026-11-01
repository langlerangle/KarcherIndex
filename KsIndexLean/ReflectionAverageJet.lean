module

public import KsIndexLean.ReflectionAverageL2

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.WeakH1

lemma Dxy_direction_memLp {μ : Measure ℂ} {X Y : ℂ → ℂ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (d : ℂ) :
    MemLp (fun z => Dxy X Y z d) 2 μ :=
  (hX.const_smul d.re).add (hY.const_smul d.im)

lemma Dxy_direction_tendsto {μ : Measure ℂ} {X Y : ℕ → ℂ → ℂ} {U V : ℂ → ℂ}
    (hX : ∀ n, MemLp (X n) 2 μ) (hY : ∀ n, MemLp (Y n) 2 μ)
    (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (htX : Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (hU.toLp U)))
    (htY : Tendsto (fun n => (hY n).toLp (Y n)) atTop (𝓝 (hV.toLp V))) (d : ℂ) :
    Tendsto (fun n => (Dxy_direction_memLp (hX n) (hY n) d).toLp
      (fun z => Dxy (X n) (Y n) z d)) atTop
      (𝓝 ((Dxy_direction_memLp hU hV d).toLp (fun z => Dxy U V z d))) := by
  exact (htX.const_smul d.re).add (htY.const_smul d.im)

/-- The directional derivative average associated with reflectionAverage. -/
def reflectionAverageJet (s : ℂ) (X Y : ℂ → ℂ) (d : ℂ) : ℂ → ℂ :=
  phaseAverage s (fun z => Dxy X Y z d) (sigmaJetPullback X Y d)

lemma reflectionAverageJet_memLp (s : ℂ) {X Y : ℂ → ℂ}
    (hX : MemLp X 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hY : MemLp Y 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2))) (d : ℂ) :
    MemLp (reflectionAverageJet s X Y d) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) :=
  phaseAverage_memLp s (Dxy_direction_memLp hX hY d) (sigmaJetPullback_memLp hX hY d)

lemma reflectionAverageJet_tendsto (s : ℂ) {X Y : ℕ → ℂ → ℂ} {U V : ℂ → ℂ}
    (hX : ∀ n, MemLp (X n) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hY : ∀ n, MemLp (Y n) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hU : MemLp U 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hV : MemLp V 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (htX : Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (hU.toLp U)))
    (htY : Tendsto (fun n => (hY n).toLp (Y n)) atTop (𝓝 (hV.toLp V))) (d : ℂ) :
    Tendsto (fun n => (reflectionAverageJet_memLp s (hX n) (hY n) d).toLp
      (reflectionAverageJet s (X n) (Y n) d)) atTop
      (𝓝 ((reflectionAverageJet_memLp s hU hV d).toLp (reflectionAverageJet s U V d))) :=
  phaseAverage_tendsto s (fun n => Dxy_direction_memLp (hX n) (hY n) d)
    (fun n => sigmaJetPullback_memLp (hX n) (hY n) d)
    (Dxy_direction_memLp hU hV d) (sigmaJetPullback_memLp hU hV d)
    (Dxy_direction_tendsto hX hY hU hV htX htY d)
    (sigmaJetPullback_tendsto hX hY hU hV htX htY d)

/-- The averaged jet is the actual classical derivative of the averaged smooth function. -/
lemma fderiv_reflectionAverage (s : ℂ) {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hf : DifferentiableAt ℝ f z) (hi : DifferentiableAt ℝ f (σ z)) (d : ℂ) :
    fderiv ℝ (reflectionAverage s f) z d =
      reflectionAverageJet s (fun w => fderiv ℝ f w 1)
        (fun w => fderiv ℝ f w Complex.I) d z := by
  have hσ : DifferentiableAt ℝ σ z :=
    (KsIndex.SigmaDeriv.hasFDerivAt_sigmaR hz).differentiableAt
  have hd := (hf.hasFDerivAt.add
    ((hi.hasFDerivAt.comp z hσ.hasFDerivAt).const_smul s)).const_smul ((2 : ℂ)⁻¹)
  rw [reflectionAverage_eq_phaseAverage]
  change fderiv ℝ ((2 : ℂ)⁻¹ • (f + s • (f ∘ σ))) z d = _
  rw [hd.fderiv]
  simp only [reflectionAverageJet, phaseAverage_apply, smul_apply, add_apply, Dxy_apply]
  rw [← realLinear_coordinates, sigmaJetPullback_eq]
  simp only [ContinuousLinearMap.comp_apply, smul_eq_mul, div_eq_mul_inv]
  ring

end KsIndex.Trace
