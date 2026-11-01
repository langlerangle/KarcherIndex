module

public import KsIndexLean.WeakDirichletKernelClassification
public import KsIndexLean.SlitReflectionNullity

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

local instance fullDirichletInner : InnerProductSpace ℂ (zeroTraceDomain Set.univ) :=
  diskDomain_innerProductSpace (zeroTraceDomain Set.univ)

def verticalDirichletVector : zeroTraceDomain Set.univ :=
  ⟨verticalThreeH1, verticalThreeH1_zeroTrace _⟩

lemma verticalDirichletVector_ne_zero : verticalDirichletVector ≠ 0 := by
  intro h
  exact verticalThreeH1_ne_zero (congrArg Subtype.val h)

lemma fullDirichlet_radical_eq_span :
    formRadical (domainJacobiForm (zeroTraceDomain Set.univ) (surfacePotential 3)) =
      Submodule.span ℂ {verticalDirichletVector} := by
  ext u
  rw [mem_formRadical, Submodule.mem_span_singleton]
  simp only [domainJacobiForm_apply]
  rw [fullDirichlet_kernel_iff_smul_vertical]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- Complex multiplicity of the actual full Dirichlet zero eigenspace. -/
lemma fullDirichlet_weakNullity_eq_one :
    diskWeakNullity (zeroTraceDomain Set.univ) (surfacePotential 3) = 1 := by
  unfold diskWeakNullity
  rw [fullDirichlet_radical_eq_span]
  exact finrank_span_singleton verticalDirichletVector_ne_zero

end KsIndex.Spectral
