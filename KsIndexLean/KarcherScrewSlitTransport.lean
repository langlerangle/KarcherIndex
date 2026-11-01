module

public import KsIndexLean.KarcherScrewEncoding

@[expose] public section


/-! The geometric screw and the analytic slit action agree on weak representatives
of the two base copies. The carrier is the actual finite period quotient. -/
noncomputable section
open MeasureTheory KsIndex.Trace KsIndex.WeakH1
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma encode_translation_character (R : PaperHalfPeriodRealization k)
    {m : ℕ} [NeZero m] (c : ℂ)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hf : ∀ q, f (HeightLift.periodDeck m 1 q) = c * f q)
    (n : ZMod (2 * m)) (z : ℂ) :
    encodeDiskFunction (R.diskFunctionPullback f) (n+2) z =
      c * encodeDiskFunction (R.diskFunctionPullback f) n z := by
  by_cases hz : z ∉ Surface.punctures k ∧ ‖z‖ ≤ 1
  · let w : PuncturedClosedDisk k := ⟨⟨z,hz.1⟩,hz.2⟩
    change encodeDiskFunction _ (n+2) w.val.val = c * encodeDiskFunction _ n w.val.val
    rw [encodeDiskFunction_on_disk, encodeDiskFunction_on_disk]
    have he := hf (R.orderedDiskPoint n w)
    rw [R.periodDeck_orderedDiskPoint] at he
    exact he
  · simp only [encodeDiskFunction, dite_eq_right hz, mul_zero]

/-- Weak representatives of the upper (copy1) and lower (copy0) geometric values. -/
def RepresentsSlitPair (R : PaperHalfPeriodRealization k) {m : ℕ} [NeZero m]
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (u : DiskPairH1) : Prop :=
    (valueCLM u.1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
      encodeDiskFunction (R.diskFunctionPullback f) 1) ∧
    (valueCLM u.2 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
      encodeDiskFunction (R.diskFunctionPullback f) 0)

lemma representsSlitPair_screw [h3 : Fact (2 ≤ 3)] (R : PaperHalfPeriodRealization 3)
    {m : ℕ} [NeZero m] (α : ℝ)
    (f : HeightLift.PeriodQuotient (extendedEWMap h3.out (reflectionBasepoint 3) R.C) m → ℂ)
    (hf : ∀ q, f (HeightLift.periodDeck m 1 q) =
      Complex.exp ((2 * Real.pi * α) * Complex.I) * f q)
    (u : DiskPairH1) (hu : R.RepresentsSlitPair f u) :
    R.RepresentsSlitPair (f ∘ R.periodScrew m) (paperSlitScrewPair α u) := by
  let c : ℂ := Complex.exp ((2 * Real.pi * α) * Complex.I)
  have h2 : valueCLM (c • u.2) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
      encodeDiskFunction (R.diskFunctionPullback f) (1+1) := by
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul c (valueCLM u.2), hu.2] with z hz h0
    simp only [Pi.smul_apply, smul_eq_mul] at hz
    rw [hz, h0]
    convert (R.encode_translation_character c f hf 0 z).symm using 1
    norm_num
  have hupper := R.screw_copy_value_ae f 1 (c • u.2) h2
  have hlower := R.screw_copy_value_ae f 0 u.1 (by simpa using hu.1)
  constructor
  · simpa only [paperSlitScrewPair, Prod.fst, c, map_smul, Nat.cast_ofNat] using hupper
  · exact hlower

lemma RepresentsSlitPair.unique (R : PaperHalfPeriodRealization k)
    {m : ℕ} [NeZero m]
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (u v : DiskPairH1) (hu : R.RepresentsSlitPair f u) (hv : R.RepresentsSlitPair f v) :
    u = v := by
  apply Prod.ext
  · exact valueCLM_injective (Lp.ext (hu.1.trans hv.1.symm))
  · exact valueCLM_injective (Lp.ext (hu.2.trans hv.2.symm))

/-- The actual geometric screw has the stated trace action on every represented
slit character vector. The finite-quotient carrier and representation hypothesis
are explicit; this does not assert an all-real infinite-tower existence theorem. -/
theorem geometric_screw_slit_trace [h3 : Fact (2 ≤ 3)] (R : PaperHalfPeriodRealization 3)
    {m : ℕ} [NeZero m] {α : ℝ} {j : ℕ} (hj : j % 3 = 2)
    (f : HeightLift.PeriodQuotient (extendedEWMap h3.out (reflectionBasepoint 3) R.C) m → ℂ)
    (hf : ∀ q, f (HeightLift.periodDeck m 1 q) =
      Complex.exp ((2 * Real.pi * α) * Complex.I) * f q)
    (u : paperSlitCharacterDomain α j) (hu : R.RepresentsSlitPair f u.val) :
    ∃ v : paperSlitCharacterDomain α j,
      R.RepresentsSlitPair (f ∘ R.periodScrew m) v.val ∧
      (fun i : KsIndex.Sector.Idx => circleFourierCoeff (diskTraceCLM v.val.2)
        (KsIndex.PaperSlitAdapter.idxToNZ i).val) =
        Complex.exp (Complex.I * (Real.pi * (α + 2/3))) •
          KsIndex.Sector.rop α (fun i : KsIndex.Sector.Idx =>
            circleFourierCoeff (diskTraceCLM u.val.2) (KsIndex.PaperSlitAdapter.idxToNZ i).val) :=
  ⟨paperSlitScrew α j u, R.representsSlitPair_screw α f hf u.val hu,
    paperSlitScrew_lower_trace hj u⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
