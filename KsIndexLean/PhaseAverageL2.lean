module

public import KsIndexLean.CollarJetLimit

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace

/-- The two-term phase average used for values and directional derivatives. -/
def phaseAverage (s : ℂ) (u v : ℂ → ℂ) : ℂ → ℂ :=
  (2 : ℂ)⁻¹ • (u + s • v)

lemma phaseAverage_apply (s : ℂ) (u v : ℂ → ℂ) (z : ℂ) :
    phaseAverage s u v z = (u z + s * v z) / 2 := by
  simp only [phaseAverage, Pi.smul_apply, Pi.add_apply, smul_eq_mul, div_eq_mul_inv]
  ring

lemma phaseAverage_memLp {μ : Measure ℂ} (s : ℂ) {u v : ℂ → ℂ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) : MemLp (phaseAverage s u v) 2 μ :=
  (hu.add (hv.const_smul s)).const_smul _

lemma phaseAverage_toLp {μ : Measure ℂ} (s : ℂ) {u v : ℂ → ℂ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    (phaseAverage_memLp s hu hv).toLp (phaseAverage s u v) =
      (2 : ℂ)⁻¹ • (hu.toLp u + s • hv.toLp v) := by
  rfl

lemma phaseAverage_tendsto {μ : Measure ℂ} (s : ℂ) {u v : ℕ → ℂ → ℂ} {a b : ℂ → ℂ}
    (hu : ∀ n, MemLp (u n) 2 μ) (hv : ∀ n, MemLp (v n) 2 μ)
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (htu : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (ha.toLp a)))
    (htv : Tendsto (fun n => (hv n).toLp (v n)) atTop (𝓝 (hb.toLp b))) :
    Tendsto (fun n => (phaseAverage_memLp s (hu n) (hv n)).toLp (phaseAverage s (u n) (v n)))
      atTop (𝓝 ((phaseAverage_memLp s ha hb).toLp (phaseAverage s a b))) := by
  exact (htu.add (htv.const_smul s)).const_smul ((2 : ℂ)⁻¹)

end KsIndex.Trace
