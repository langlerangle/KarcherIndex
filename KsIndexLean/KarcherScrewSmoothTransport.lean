module

public import KsIndexLean.KarcherScrewSlitTransport
public import KsIndexLean.KarcherSlitIndex

@[expose] public section


/-! The slit representation of compact smooth geometric joint-sector tests. -/
noncomputable section
open MeasureTheory
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spectral
variable [Fact (2 ≤ 3)] (R : PaperHalfPeriodRealization 3)
variable {m : ℕ} [NeZero m] {n j : ℕ}

lemma smoothCopy_represents_descent (v : Surface.CcSmooth 3 m) (a : ZMod (2 * m)) :
    valueCLM (ccSmoothCopy v a) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
      encodeDiskFunction (R.diskFunctionPullback (R.modelTestFunction v.val)) a := by
  rw [R.modelTestFunction_encoding]
  filter_upwards [ccSmoothCopy_value_ae v a,
    ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with z hz hd
  rw [hz]
  exact (FaithfulInjection.testTrace_eqOn_disk v.val a hd).symm

lemma smoothJointSector_representsSlitPair (u : paperSmoothJointSector m n j) :
    R.RepresentsSlitPair (R.geometricTestDescent u.val)
      (paperChainSlitEquiv m n j (paperSmoothToChainSector m n j u)).val := by
  rw [paperChainSlitEquiv_coordinates]
  let v := domCcSmoothEquiv 3 m (paperSmoothUnderlying m n j u)
  change R.RepresentsSlitPair (R.modelTestFunction v.val)
    (chainChartCoordinatesCLM 3 m (ccSmoothToChainChart 3 m v) 1,
     chainChartCoordinatesCLM 3 m (ccSmoothToChainChart 3 m v) 0)
  rw [ccSmoothToChainChart_coordinates]
  exact ⟨R.smoothCopy_represents_descent v 1, R.smoothCopy_represents_descent v 0⟩

/-- Every actual compact smooth joint-sector test has its established weak slit
representative; no surjectivity from smooth tests onto the weak domain is claimed. -/
lemma geometricSmoothJointSector_has_slit_representative
    (f : R.geometricSmoothJointSector (m := m) n j) :
    ∃ u : paperSlitCharacterDomain ((n : ℝ) / m) j,
      R.RepresentsSlitPair f.val u.val := by
  obtain ⟨u, hu, he⟩ := f.property
  refine ⟨paperChainSlitEquiv m n j (paperSmoothToChainSector m n j ⟨u, hu⟩), ?_⟩
  rw [← he]
  exact R.smoothJointSector_representsSlitPair ⟨u, hu⟩

/-- The geometric screw trace formula on actual compact smooth joint sectors. -/
theorem geometricSmoothJointSector_screw_trace (hj : j % 3 = 2)
    (f : R.geometricSmoothJointSector (m := m) n j) :
    ∃ u v : paperSlitCharacterDomain ((n : ℝ) / m) j,
      R.RepresentsSlitPair f.val u.val ∧
      R.RepresentsSlitPair (f.val ∘ R.periodScrew m) v.val ∧
      (fun i : KsIndex.Sector.Idx => circleFourierCoeff (diskTraceCLM v.val.2)
        (KsIndex.PaperSlitAdapter.idxToNZ i).val) =
        Complex.exp (Complex.I * (Real.pi * (((n : ℝ) / m : ℝ) + 2/3))) •
          KsIndex.Sector.rop ((n : ℝ) / m) (fun i : KsIndex.Sector.Idx =>
            circleFourierCoeff (diskTraceCLM u.val.2)
              (KsIndex.PaperSlitAdapter.idxToNZ i).val) := by
  obtain ⟨u, hu⟩ := R.geometricSmoothJointSector_has_slit_representative f
  have ht : ∀ q, f.val (HeightLift.periodDeck m 1 q) =
      Complex.exp ((2*Real.pi*(((n : ℝ)/m : ℝ)))*Complex.I) * f.val q := by
    intro q
    have he := ((R.mem_geometricSmoothJointSector n j f.val).mp f.property).2.1 q
    rw [← paperRationalPhase_eq_zeta m n] at he
    exact he
  obtain ⟨v, hv, he⟩ := R.geometric_screw_slit_trace hj f.val ht u hu
  exact ⟨u, v, hu, hv, he⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
