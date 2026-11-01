module

public import KsIndexLean.KarcherScrewSlitTransport
public import KsIndexLean.KarcherSlitNullity

@[expose] public section


/-! Weak slit representatives of actual bounded geometric Jacobi fields. -/
noncomputable section
open MeasureTheory
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.NullityDecomp KsIndex.Trace KsIndex.WeakH1 KsIndex.Spectral KsIndex.PaperSlitTransport
variable [Fact (2 ≤ 3)] (R : PaperHalfPeriodRealization 3)
variable {m : ℕ} [NeZero m] {n j : ℕ}

lemma geometricJointFiber_representsSlitPair
    (G : R.geometricJointFiber (m := m) n j) :
    R.RepresentsSlitPair G.val.val
      (paperChainSlitEquiv m n j
        (fiberToSectorLin (R.geometricJointFiberToModel n j G))).val := by
  rw [paperChainSlitEquiv_coordinates]
  change R.RepresentsSlitPair G.val.val
    (chainChartCoordinatesCLM 3 m (fiberToChain (R.geometricJointFiberToModel n j G)) 1,
     chainChartCoordinatesCLM 3 m (fiberToChain (R.geometricJointFiberToModel n j G)) 0)
  rw [fiberToChain_coord]
  constructor
  · exact energySmoothCopy_value_ae (fiberES (R.geometricJointFiberToModel n j G)) 1
  · exact energySmoothCopy_value_ae (fiberES (R.geometricJointFiberToModel n j G)) 0

/-- On an actual geometric Jacobi joint fiber, the screw trace identity needs
no additional representation hypothesis. -/
theorem geometricJointFiber_screw_trace (hj : j % 3 = 2)
    (G : R.geometricJointFiber (m := m) n j) :
    ∃ v : paperSlitCharacterDomain ((n : ℝ) / m) j,
      R.RepresentsSlitPair (G.val.val ∘ R.periodScrew m) v.val ∧
      (fun i : KsIndex.Sector.Idx => circleFourierCoeff (diskTraceCLM v.val.2)
        (KsIndex.PaperSlitAdapter.idxToNZ i).val) =
        Complex.exp (Complex.I * ((Real.pi * (((n : ℝ) / m : ℝ) + 2/3)))) •
          KsIndex.Sector.rop ((n : ℝ) / m) (fun i : KsIndex.Sector.Idx =>
            circleFourierCoeff (diskTraceCLM
              (paperChainSlitEquiv m n j
                (fiberToSectorLin (R.geometricJointFiberToModel n j G))).val.2)
              (KsIndex.PaperSlitAdapter.idxToNZ i).val) := by
  apply R.geometric_screw_slit_trace hj G.val.val _ _
    (R.geometricJointFiber_representsSlitPair G)
  intro q
  have ht := ((R.mem_geometricJointFiber n j G.val).mp G.property).1 q
  rw [← paperRationalPhase_eq_zeta m n] at ht
  exact ht

end KsIndex.KarcherData.PaperHalfPeriodRealization
