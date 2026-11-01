module

public import KsIndexLean.FullHalfOrderTraceLift
public import KsIndexLean.CircleSigmaDomain
public import KsIndexLean.PaperSlitIndexTransport

@[expose] public section


/-! At nonintegral phase (`sin (α * π) ≠ 0`), the unrestricted sign-multiplier
graph domain is the lower trace image of weak disk pairs satisfying the phased
seam conditions. The forward trace-realization implication holds at every phase. -/
noncomputable section
open MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.CircleSobolev KsIndex.PaperSlitAdapter

/-- For nonintegral phase, the phased seam multiplier and sign multiplier
impose the same half-order regularity condition. -/
theorem memDomSigma_iff_arcMul_range (α : ℝ)
    (hsin : Real.sin (α * Real.pi) ≠ 0) (f : Space (1 / 2 : ℝ)) :
    MemDomSigma f ↔ arcMul α (toL2Half f) ∈ Set.range toL2Half := by
  let D := LinearMap.range toL2Half.toLinearMap
  have hf : toL2Half f ∈ D := ⟨f, rfl⟩
  have hc : (Real.cos (α * Real.pi) : ℂ) • toL2Half f ∈ D := D.smul_mem _ hf
  have hi : Complex.I * (Real.sin (α * Real.pi) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hsin)
  have he := Complex.exp_ne_zero (Complex.I * (α * Real.pi))
  change sigmaMul (toL2Half f) ∈ D ↔ arcMul α (toL2Half f) ∈ D
  unfold arcMul
  rw [D.smul_mem_iff he]
  constructor
  · intro h
    exact D.sub_mem hc (D.smul_mem _ h)
  · intro h
    apply (D.smul_mem_iff hi).mp
    have hh := D.sub_mem hc h
    simpa only [sub_sub_cancel] using hh

/-- Every graph-domain trace is the lower trace of an unrestricted seam pair. -/
theorem exists_paperSlitPair_of_memDomSigma (α : ℝ)
    (f : Space (1 / 2 : ℝ)) (hf : MemDomSigma f) :
    ∃ u : DiskPairH1, u ∈ paperSlitDomain α ∧ halfDiskTraceCLM u.2 = f := by
  let g : Space (1 / 2 : ℝ) := Complex.exp (Complex.I * (α * Real.pi)) •
    ((Real.cos (α * Real.pi) : ℂ) • f -
      (Complex.I * (Real.sin (α * Real.pi) : ℂ)) • sigmaLift f hf)
  obtain ⟨u1, hu1⟩ := halfDiskTraceCLM_surjective g
  obtain ⟨u2, hu2⟩ := halfDiskTraceCLM_surjective f
  have ht1 : diskTraceCLM u1 = toL2Half g := by
    rw [← toL2_halfDiskTrace, ← halfDiskTraceCLM_apply, hu1]
  have ht2 : diskTraceCLM u2 = toL2Half f := by
    rw [← toL2_halfDiskTrace, ← halfDiskTraceCLM_apply, hu2]
  have hg : toL2Half g = arcMul α (toL2Half f) := by
    simp only [g, map_smul, map_sub, toL2Half_sigmaLift, arcMul]
  refine ⟨(u1,u2), ?_, hu2⟩
  change (u1,u2) ∈ slitTraceDomain 3 (Complex.exp ((2 * Real.pi * α) * Complex.I))
  rw [mem_slitTraceDomain]
  apply arcs_of_full_relation
  rw [ht1, hg, ht2]
  exact arcMul_coe α (toL2Half f)

/-- At nonintegral phase, every unrestricted seam pair has graph-domain lower trace. -/
theorem memDomSigma_lowerTrace_of_paperSlitPair (α : ℝ)
    (hsin : Real.sin (α * Real.pi) ≠ 0) (u : DiskPairH1)
    (hu : u ∈ paperSlitDomain α) : MemDomSigma (halfDiskTraceCLM u.2) := by
  apply (memDomSigma_iff_arcMul_range α hsin _).mpr
  obtain ⟨h1,h0⟩ := (mem_slitTraceDomain 3 _ u).mp hu
  have he : diskTraceCLM u.1 = arcMul α (diskTraceCLM u.2) := by
    apply Lp.ext
    exact (seam_full_relation α u.1 u.2 h1 h0).trans (arcMul_coe α _).symm
  refine ⟨halfDiskTraceCLM u.1, ?_⟩
  simpa only [halfDiskTraceCLM_apply, toL2Half, toL2_halfDiskTrace] using he

/-- At nonintegral phase, the full sign-multiplier graph domain equals the lower
trace image of the phased weak disk-pair seam domain; no rotation-character
assumption is needed. -/
theorem memDomSigma_iff_exists_paperSlitPair (α : ℝ)
    (hsin : Real.sin (α * Real.pi) ≠ 0) (f : Space (1 / 2 : ℝ)) :
    MemDomSigma f ↔
      ∃ u : DiskPairH1, u ∈ paperSlitDomain α ∧ halfDiskTraceCLM u.2 = f := by
  constructor
  · exact exists_paperSlitPair_of_memDomSigma α f
  · rintro ⟨u,hu,rfl⟩
    exact memDomSigma_lowerTrace_of_paperSlitPair α hsin u hu

end KsIndex.Trace
