module

public import KsIndexLean.GeneralDirichletRegularityBase
public import KsIndexLean.DiskSmoothRepresentative
public import KsIndexLean.GroundStateInteriorRigidity

@[expose] public section


/-! # Ground-state classification of the weak Dirichlet kernel

For `k ≥ 2`, every zero-trace weak Jacobi kernel field on the disk is a
complex multiple of the vertical radial mode `globalSmoothH1 (modeU k 0)`.

Interior regularity supplies a smooth representative. Identification of its
classical derivatives with the weak derivatives gives a smooth H¹ carrier
representing the original field. The zero-trace condition and zero energy
then give pointwise ground-state rigidity in the open disk. Injectivity of
the value map transfers this identity back to the Sobolev carrier.

The argument requires no regularity of the quotient at the boundary.
`GeneralDirichletKernel.generalDirichlet_kernel_span` uses this theorem to
express the classification in terms of `radialDirichletH1`.
-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.GroundState
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Weq KsIndex.JacobiMode KsIndex.ModeDiag

/-- **Ground-state full weak Dirichlet kernel classification**, `k ≥ 2`. -/
theorem fullDirichlet_kernel_span_ground_state {k : ℕ} (hk : 2 ≤ k) (u : ComplexH1)
    (hu : u ∈ zeroTraceDomain Set.univ)
    (hQ : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v = 0) :
    ∃ c : ℂ, u = c • globalSmoothH1 (modeU k 0) (modeU_contDiff (by omega) 0) := by
  -- (1) smooth interior representative `f` of `u`, with the actual Jacobi PDE on the disk
  obtain ⟨f, hf, hval, _hpde⟩ := fullDirichlet_tests_classical hk u hQ
  -- (2) `f`'s classical coordinate derivatives equal `u`'s weak derivatives a.e. ⇒ L² jets
  obtain ⟨hdx, hdy⟩ := disk_smooth_representative_derivatives u hf hval
  have hfmem : MemLp f 2 (volume.restrict (disk : Set ℂ)) :=
    (Lp.memLp (valueCLM u)).ae_eq hval
  have hdxmem : MemLp (fun z => fderiv ℝ f z 1) 2 (volume.restrict (disk : Set ℂ)) :=
    (Lp.memLp (dxCLM u)).ae_eq hdx
  have hdymem : MemLp (fun z => fderiv ℝ f z Complex.I) 2 (volume.restrict (disk : Set ℂ)) :=
    (Lp.memLp (dyCLM u)).ae_eq hdy
  -- assemble the smooth H¹ carrier with `F.F = f`
  let F : SmoothH1Data := ⟨f, hf, hfmem, hdxmem, hdymem⟩
  -- (3) `smoothToH1 F = u` by injectivity of the value carrier (both values = f a.e.)
  have hFu : smoothToH1 F = u :=
    valueCLM_injective (Lp.ext ((smoothToH1_value_ae F).trans hval.symm))
  -- (4) transport zero-trace and zero-energy to `F`
  have hFtrace : smoothToH1 F ∈ zeroTraceDomain Set.univ := hFu ▸ hu
  have hFenergy : (weakJacobi (surfacePotential k) (smoothToH1 F) (smoothToH1 F)).re = 0 := by
    rw [hFu, hQ u hu, Complex.zero_re]
  -- (5) the geometric interior-rigidity kernel theorem: `f = c · modeU k 0` on the disk
  obtain ⟨c, hc⟩ := radial_ground_smooth_kernel hk F hFtrace hFenergy
  -- (6) transfer the pointwise value identity back to H¹ via value injectivity
  refine ⟨c, valueCLM_injective (Lp.ext ?_)⟩
  rw [map_smul]
  have hgv := globalSmoothH1_value (modeU k 0) (modeU_contDiff (by omega) 0)
  filter_upwards [hval, hgv, ae_restrict_mem disk.isOpen.measurableSet,
    Lp.coeFn_smul c (valueCLM (globalSmoothH1 (modeU k 0) (modeU_contDiff (by omega) 0)))]
    with z hz_uf hz_Wmode hz_mem hz_smul
  -- goal: ↑(valueCLM u) z = ↑(c • valueCLM W) z
  rw [hz_smul, Pi.smul_apply, hz_Wmode, smul_eq_mul, hz_uf]
  exact hc z hz_mem

end KsIndex.GroundState
