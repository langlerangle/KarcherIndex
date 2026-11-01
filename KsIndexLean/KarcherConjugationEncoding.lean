module

public import KsIndexLean.KarcherDiskConjugation

@[expose] public section


/-! Pullback by the actual reflection in y=0 conjugates disk coordinates,
not function values. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma encode_conjugation_pullback (R : PaperHalfPeriodRealization k)
    {m : ℕ} [NeZero m]
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    encodeDiskFunction (R.diskFunctionPullback (f ∘ R.periodConjugation m)) =
      fun n z => encodeDiskFunction (R.diskFunctionPullback f) n (starRingEnd ℂ z) := by
  funext n z
  have hv : (starRingEnd ℂ z ∉ Surface.punctures k ∧ ‖starRingEnd ℂ z‖ ≤ 1) ↔
      (z ∉ Surface.punctures k ∧ ‖z‖ ≤ 1) := by
    constructor
    · rintro ⟨hp, hn⟩
      refine ⟨?_, by simpa using hn⟩
      have hc := conjugate_not_puncture hp
      simpa using hc
    · rintro ⟨hp, hn⟩
      exact ⟨conjugate_not_puncture hp, by simpa using hn⟩
  by_cases hz : z ∉ Surface.punctures k ∧ ‖z‖ ≤ 1
  · let w : PuncturedClosedDisk k := ⟨⟨z,hz.1⟩,hz.2⟩
    change encodeDiskFunction _ n w.val.val =
      encodeDiskFunction _ n (starRingEnd ℂ w.val.val)
    rw [← R.diskConjugation_coordinate w, encodeDiskFunction_on_disk,
      encodeDiskFunction_on_disk]
    change f (R.periodConjugation m (R.orderedDiskPoint n w)) =
      f (R.orderedDiskPoint n (R.diskConjugation w))
    rw [R.periodConjugation_orderedDiskPoint]
  · have hz' := mt hv.mp hz
    simp only [encodeDiskFunction, dite_eq_right hz, dite_eq_right hz']

lemma periodConjugation_involutive (R : PaperHalfPeriodRealization k) (m : ℕ) :
    Function.Involutive (R.periodConjugation m) := by
  intro q
  induction q using Quotient.inductionOn with
  | h q => exact congrArg (HeightLift.periodQuotientMap m) (R.conjugationLift_involutive q)

end KsIndex.KarcherData.PaperHalfPeriodRealization
