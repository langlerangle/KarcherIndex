module

public import KsIndexLean.KarcherScrewPullback
public import KsIndexLean.PaperSlitScrewDomain

@[expose] public section


/-! Canonical geometric screw encoding and its weak disk-value representation. -/
noncomputable section
open MeasureTheory
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma encode_screw_pullback (R : PaperHalfPeriodRealization k)
    {m : ℕ} [NeZero m]
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    encodeDiskFunction (R.diskFunctionPullback (f ∘ R.periodScrew m)) =
      fun n z => encodeDiskFunction (R.diskFunctionPullback f) (n + 1)
        (KsIndex.Trace.planeRotation (-Real.pi/k) z) := by
  have hp : Complex.exp ((-Real.pi/k : ℝ) * Complex.I) ^ (2*k) = 1 :=
    root_double_of_neg_one (paper_screw_root h.out)
  have hn : ‖Complex.exp ((-Real.pi/k : ℝ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  funext n z
  have hv : (KsIndex.Trace.planeRotation (-Real.pi/k) z ∉ Surface.punctures k ∧
      ‖KsIndex.Trace.planeRotation (-Real.pi/k) z‖ ≤ 1) ↔
      (z ∉ Surface.punctures k ∧ ‖z‖ ≤ 1) := by
    simp only [KsIndex.Trace.planeRotation_apply, Surface.punctures, Set.mem_ofPred_eq,
      mul_pow, hp, one_mul, norm_mul, hn]
  by_cases hz : z ∉ Surface.punctures k ∧ ‖z‖ ≤ 1
  · let w : PuncturedClosedDisk k := ⟨⟨z,hz.1⟩,hz.2⟩
    change encodeDiskFunction _ n w.val.val =
      encodeDiskFunction _ (n + 1) (KsIndex.Trace.planeRotation (-Real.pi/k) w.val.val)
    rw [KsIndex.Trace.planeRotation_apply, ← R.diskScrew_coordinate w,
      encodeDiskFunction_on_disk, encodeDiskFunction_on_disk]
    exact R.diskFunctionPullback_screw f n w
  · have hz' := mt hv.mp hz
    simp only [encodeDiskFunction, dite_eq_right hz, dite_eq_right hz']

/-- An H1 representative of one geometric disk copy rotates to an H1 representative
of the preceding copy of the screw pullback. Equality is almost everywhere. -/
lemma screw_copy_value_ae (R : PaperHalfPeriodRealization k)
    {m : ℕ} [NeZero m]
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (n : ZMod (2 * m)) (u : KsIndex.WeakH1.ComplexH1)
    (hu : KsIndex.WeakH1.valueCLM u =ᵐ[volume.restrict (KsIndex.WeakH1.disk : Set ℂ)]
      encodeDiskFunction (R.diskFunctionPullback f) (n + 1)) :
    KsIndex.WeakH1.valueCLM (KsIndex.Trace.diskRotation (-Real.pi/k) u) =ᵐ[
      volume.restrict (KsIndex.WeakH1.disk : Set ℂ)]
      encodeDiskFunction (R.diskFunctionPullback (f ∘ R.periodScrew m)) n := by
  have hm := KsIndex.Trace.measurePreserving_planeRotation_disk (-Real.pi/k)
  have hc := hm.quasiMeasurePreserving.ae_eq_comp hu
  have hr := KsIndex.Trace.diskRotation_value_ae (-Real.pi/k) u
  rw [R.encode_screw_pullback]
  exact hr.trans hc

end KsIndex.KarcherData.PaperHalfPeriodRealization
