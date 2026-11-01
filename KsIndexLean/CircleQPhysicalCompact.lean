module

public import KsIndexLean.CircleSigmaDomain
public import KsIndexLean.CircleSobolevCompact

@[expose] public section


/-! Compact physical L² inclusion of the positive sign-compatible graph domain. -/
noncomputable section
namespace KsIndex.CircleQ
open CircleSobolev MeasureTheory Trace

/-- Physical L² realization of a sign-compatible graph element. -/
def graphToL2CLM : ↥sigmaGraph →L[ℂ] Lp ℂ 2 circleMeasure :=
  toL2Half.comp (graphFstCLM.comp sigmaGraph.subtypeL)

/-- The positive Fourier character inside the graph-domain Hilbert space. -/
def positivePhysicalGraph : Submodule ℂ ↥sigmaGraph :=
  (character (1 / 2 : ℝ) (-1) 6).comap
    (graphFstCLM.comp sigmaGraph.subtypeL).toLinearMap

@[simp] theorem mem_positivePhysicalGraph (q : ↥sigmaGraph) :
    q ∈ positivePhysicalGraph ↔
      (q : SigmaGraphAmbient).fst ∈ character (1 / 2 : ℝ) (-1) 6 := Iff.rfl

/-- Compactness survives passage from half-order norm to the stronger graph norm. -/
theorem isCompactOperator_graphToL2 : IsCompactOperator graphToL2CLM :=
  isCompactOperator_toL2_half.comp_clm (graphFstCLM.comp sigmaGraph.subtypeL)

/-- Compact inclusion for the exact positive physical graph-domain carrier. -/
theorem isCompactOperator_positiveGraphToL2 :
    IsCompactOperator (graphToL2CLM.comp positivePhysicalGraph.subtypeL) :=
  isCompactOperator_graphToL2.comp_clm positivePhysicalGraph.subtypeL

end KsIndex.CircleQ
