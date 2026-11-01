module

public import KsIndexLean.DiskBulkCompact
public import KsIndexLean.WeakTransmissionDomains
public import KsIndexLean.WeakDiskChain

@[expose] public section


noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Topology
namespace KsIndex.WeakH1

/-- Bulk inclusion on any linear disk domain, with its inherited H1 topology. -/
def domainValueCLM (D : Submodule ℂ ComplexH1) : D →L[ℂ] L2C :=
  valueCLM.comp D.subtypeL

lemma domainValueCLM_compact (D : Submodule ℂ ComplexH1) :
    IsCompactOperator (domainValueCLM D) :=
  valueCLM_isCompactOperator.comp_clm D.subtypeL

/-- Componentwise bulk values on the actual finite family carrier. -/
def finiteDiskValueCLM (ι : Type*) [Fintype ι] :
    (ι → ComplexH1) →L[ℂ] (ι → L2C) :=
  ContinuousLinearMap.pi (fun i => valueCLM.comp (ContinuousLinearMap.proj i))

lemma finiteDiskValueCLM_compact (ι : Type*) [Fintype ι] :
    IsCompactOperator (finiteDiskValueCLM ι) := by
  obtain ⟨K, hK, hinc⟩ := IsCompactOperator.image_closedBall_subset_compact
    (f := valueCLM.toLinearMap) valueCLM_isCompactOperator 1
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ (by norm_num),
    Set.pi Set.univ (fun _ : ι => K), (by simpa [Set.pi] using isCompact_pi_infinite (fun _ : ι => hK)), ?_⟩
  rintro f ⟨u, hu, rfl⟩ i _
  apply hinc
  refine ⟨u i, ?_, rfl⟩
  simp only [Metric.mem_closedBall, dist_zero_right] at hu ⊢
  exact (norm_le_pi_norm u i).trans hu

/-- Every finite-copy domain inherits bulk compactness, including phase constraints. -/
def finiteDomainValueCLM {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) : D →L[ℂ] (ι → L2C) :=
  (finiteDiskValueCLM ι).comp D.subtypeL

lemma finiteDomainValueCLM_compact {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) : IsCompactOperator (finiteDomainValueCLM D) :=
  (finiteDiskValueCLM_compact ι).comp_clm D.subtypeL

/-- Bulk values on the paper's ordered upper/lower disk pair. -/
def pairDiskValueCLM : KsIndex.Trace.DiskPairH1 →L[ℂ] (L2C × L2C) :=
  valueCLM.prodMap valueCLM

lemma pairDiskValueCLM_compact : IsCompactOperator pairDiskValueCLM := by
  obtain ⟨K, hK, hinc⟩ := IsCompactOperator.image_closedBall_subset_compact
    (f := valueCLM.toLinearMap) valueCLM_isCompactOperator 1
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ (by norm_num),
    K ×ˢ K, hK.prod hK, ?_⟩
  rintro f ⟨u, hu, rfl⟩
  have hu' : ‖u‖ ≤ 1 := by simpa using hu
  constructor
  · exact hinc ⟨u.1, by simpa using (norm_fst_le u).trans hu', rfl⟩
  · exact hinc ⟨u.2, by simpa using (norm_snd_le u).trans hu', rfl⟩

def pairDomainValueCLM (D : Submodule ℂ KsIndex.Trace.DiskPairH1) :
    D →L[ℂ] (L2C × L2C) := pairDiskValueCLM.comp D.subtypeL

lemma pairDomainValueCLM_compact (D : Submodule ℂ KsIndex.Trace.DiskPairH1) :
    IsCompactOperator (pairDomainValueCLM D) :=
  pairDiskValueCLM_compact.comp_clm D.subtypeL

lemma domainValueCLM_injective (D : Submodule ℂ ComplexH1) :
    Function.Injective (domainValueCLM D) := by
  intro u v h
  apply Subtype.ext
  exact valueCLM_injective h

lemma finiteDiskValueCLM_injective (ι : Type*) [Fintype ι] :
    Function.Injective (finiteDiskValueCLM ι) := by
  intro u v h
  funext i
  exact valueCLM_injective (congrFun h i)

lemma finiteDomainValueCLM_injective {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) : Function.Injective (finiteDomainValueCLM D) := by
  intro u v h
  apply Subtype.ext
  exact finiteDiskValueCLM_injective ι h

lemma pairDiskValueCLM_injective : Function.Injective pairDiskValueCLM := by
  intro u v h
  exact Prod.ext (valueCLM_injective (congrArg Prod.fst h))
    (valueCLM_injective (congrArg Prod.snd h))

lemma pairDomainValueCLM_injective (D : Submodule ℂ KsIndex.Trace.DiskPairH1) :
    Function.Injective (pairDomainValueCLM D) := by
  intro u v h
  apply Subtype.ext
  exact pairDiskValueCLM_injective h

end KsIndex.WeakH1

namespace KsIndex.Trace
open KsIndex.WeakH1

lemma mixedTraceDomain_bulk_compact (k : ℕ) (b1 b0 : Bool) :
    IsCompactOperator (domainValueCLM (mixedTraceDomain k b1 b0)) :=
  domainValueCLM_compact _

lemma mixedCharacterDomain_bulk_compact (k r : ℕ) (b1 b0 : Bool) :
    IsCompactOperator (domainValueCLM (mixedCharacterDomain k r b1 b0)) :=
  domainValueCLM_compact _

lemma slitTraceDomain_bulk_compact (k : ℕ) (phase : ℂ) :
    IsCompactOperator (pairDomainValueCLM (slitTraceDomain k phase)) :=
  pairDomainValueCLM_compact _

lemma paperSlitCharacterDomain_bulk_compact (α : ℝ) (j : ℕ) :
    IsCompactOperator (pairDomainValueCLM (paperSlitCharacterDomain α j)) :=
  pairDomainValueCLM_compact _

lemma weakDiskChain_bulk_compact (k m : ℕ) [NeZero m] :
    IsCompactOperator (finiteDomainValueCLM (weakDiskChain k m)) :=
  finiteDomainValueCLM_compact _

end KsIndex.Trace
