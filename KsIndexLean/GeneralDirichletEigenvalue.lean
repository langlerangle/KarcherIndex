module

public import KsIndexLean.GeneralDirichletValues
public import KsIndexLean.DiskWeakMultiplicity

@[expose] public section


/-!
# The zero Dirichlet eigenspace with spherical bulk mass

The full weak eigenspace at zero is the one-dimensional span of the
vertical field. Every element is invariant under all disk rotations.
This identifies the eigenspace, independently of a least-eigenvalue claim.
-/
noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.FormIndex

local instance fullDirichletEigenInner : InnerProductSpace ℂ (zeroTraceDomain Set.univ) :=
  diskDomain_innerProductSpace _

local instance fullDirichletEigenComplete : CompleteSpace (zeroTraceDomain Set.univ) :=
  (isClosed_zeroTraceDomain Set.univ).completeSpace_coe

def fullVerticalVector {k : ℕ} (hk : 2 ≤ k) : zeroTraceDomain Set.univ :=
  ⟨radialDirichletH1 hk, (mem_fullZeroTrace_iff _).mpr (radialDirichletH1_trace hk)⟩

lemma fullDirichlet_zero_eigenspace_iff {k : ℕ} (hk : 2 ≤ k)
    (u : zeroTraceDomain Set.univ) :
    u ∈ diskWeakEigenspace (zeroTraceDomain Set.univ) (surfacePotential k) 0 ↔
      ∃ c : ℂ, (u : ComplexH1) = c • radialDirichletH1 hk := by
  rw [mem_diskWeakEigenspace_all]
  simp only [Complex.ofReal_zero, zero_mul]
  constructor
  · intro h
    exact generalDirichlet_kernel_span hk u u.property (fun v hv => h ⟨v, hv⟩)
  · rintro ⟨c, hc⟩ v
    rw [hc, weakJacobi_smul_left, radialDirichletH1_weak hk v v.property, mul_zero]

lemma fullDirichlet_zero_eigenspace_span {k : ℕ} (hk : 2 ≤ k) :
    diskWeakEigenspace (zeroTraceDomain Set.univ) (surfacePotential k) 0 =
      Submodule.span ℂ {fullVerticalVector hk} := by
  ext u
  rw [fullDirichlet_zero_eigenspace_iff hk, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩

lemma fullDirichlet_zero_eigenspace_finrank {k : ℕ} (hk : 2 ≤ k) :
    Module.finrank ℂ (diskWeakEigenspace (zeroTraceDomain Set.univ)
      (surfacePotential k) 0) = 1 := by
  rw [fullDirichlet_zero_eigenspace_span hk]
  apply finrank_span_singleton
  intro h
  exact radialDirichletH1_ne_zero hk (congrArg Subtype.val h)

lemma fullDirichlet_zero_eigenfunction_rotation {k : ℕ} (hk : 2 ≤ k)
    (u : zeroTraceDomain Set.univ)
    (hu : u ∈ diskWeakEigenspace (zeroTraceDomain Set.univ) (surfacePotential k) 0)
    (θ : ℝ) : diskRotation θ (u : ComplexH1) = u := by
  obtain ⟨c, hc⟩ := (fullDirichlet_zero_eigenspace_iff hk u).mp hu
  rw [hc, map_smul, radialDirichletH1_rotation]

end KsIndex.Spectral
