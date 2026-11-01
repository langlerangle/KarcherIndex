module

public import KsIndexLean.BulkClosure
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1

/-- Sum-of-squares L2 target for a finite disk family. -/
abbrev FiniteBulkL2 (ι : Type*) := PiLp 2 (fun _ : ι => L2C)

/-- Hilbert bulk map retaining the actual finite-family form-domain carrier. -/
def finiteHilbertValueCLM (ι : Type*) [Fintype ι] :
    (ι → ComplexH1) →L[ℂ] FiniteBulkL2 ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => L2C)).symm.toContinuousLinearMap.comp
    (finiteDiskValueCLM ι)

lemma finiteHilbertValueCLM_compact (ι : Type*) [Fintype ι] :
    IsCompactOperator (finiteHilbertValueCLM ι) :=
  (finiteDiskValueCLM_compact ι).clm_comp
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => L2C)).symm.toContinuousLinearMap

lemma finiteHilbertValueCLM_injective (ι : Type*) [Fintype ι] :
    Function.Injective (finiteHilbertValueCLM ι) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => L2C)).symm.injective.comp
    (finiteDiskValueCLM_injective ι)

abbrev PairBulkL2 := WithLp 2 (L2C × L2C)

def pairHilbertValueCLM : KsIndex.Trace.DiskPairH1 →L[ℂ] PairBulkL2 :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ L2C L2C).symm.toContinuousLinearMap.comp
    pairDiskValueCLM

lemma pairHilbertValueCLM_compact : IsCompactOperator pairHilbertValueCLM :=
  pairDiskValueCLM_compact.clm_comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ L2C L2C).symm.toContinuousLinearMap

lemma pairHilbertValueCLM_injective : Function.Injective pairHilbertValueCLM :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ L2C L2C).symm.injective.comp
    pairDiskValueCLM_injective

/-- The ambient L2 sector associated with any actual single-disk form domain. -/
abbrev DiskAmbient (D : Submodule ℂ ComplexH1) := bulkClosure (V := D) (H := L2C) (domainValueCLM D)

abbrev diskAmbientEmbedding (D : Submodule ℂ ComplexH1) :=
  closureEmbedding (V := D) (H := L2C) (domainValueCLM D)

lemma diskAmbientEmbedding_spec (D : Submodule ℂ ComplexH1) :
    Function.Injective (diskAmbientEmbedding D) ∧ DenseRange (diskAmbientEmbedding D) ∧
      IsCompactOperator (diskAmbientEmbedding D) :=
  ⟨closureEmbedding_injective (V := D) (domainValueCLM_injective D),
    closureEmbedding_denseRange (V := D) _, closureEmbedding_compact (V := D) (domainValueCLM_compact D)⟩

/-- The ambient L2 sector for a coupled pair, with the Hilbert product norm. -/
abbrev PairAmbient (D : Submodule ℂ KsIndex.Trace.DiskPairH1) :=
  bulkClosure (V := D) (H := PairBulkL2) (pairHilbertValueCLM.comp D.subtypeL)

abbrev pairAmbientEmbedding (D : Submodule ℂ KsIndex.Trace.DiskPairH1) :=
  closureEmbedding (V := D) (H := PairBulkL2) (pairHilbertValueCLM.comp D.subtypeL)

lemma pairAmbientEmbedding_spec (D : Submodule ℂ KsIndex.Trace.DiskPairH1) :
    Function.Injective (pairAmbientEmbedding D) ∧ DenseRange (pairAmbientEmbedding D) ∧
      IsCompactOperator (pairAmbientEmbedding D) :=
  ⟨closureEmbedding_injective (V := D) (pairHilbertValueCLM_injective.comp Subtype.val_injective),
    closureEmbedding_denseRange (V := D) _,
    closureEmbedding_compact (V := D) (pairHilbertValueCLM_compact.comp_clm D.subtypeL)⟩

/-- The ambient L2 sector for a finite chain or any of its linear sectors. -/
abbrev FiniteAmbient {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) :=
  bulkClosure (V := D) (H := FiniteBulkL2 ι) ((finiteHilbertValueCLM ι).comp D.subtypeL)

abbrev finiteAmbientEmbedding {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) :=
  closureEmbedding (V := D) (H := FiniteBulkL2 ι) ((finiteHilbertValueCLM ι).comp D.subtypeL)

lemma finiteAmbientEmbedding_spec {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) :
    Function.Injective (finiteAmbientEmbedding D) ∧ DenseRange (finiteAmbientEmbedding D) ∧
      IsCompactOperator (finiteAmbientEmbedding D) :=
  ⟨closureEmbedding_injective (V := D) ((finiteHilbertValueCLM_injective ι).comp Subtype.val_injective),
    closureEmbedding_denseRange (V := D) _,
    closureEmbedding_compact (V := D) ((finiteHilbertValueCLM_compact ι).comp_clm D.subtypeL)⟩

end KsIndex.Spectral
