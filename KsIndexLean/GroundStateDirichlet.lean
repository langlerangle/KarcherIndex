module

public import KsIndexLean.GroundStateTransform
public import KsIndexLean.PureDirichletCompactCore
public import KsIndexLean.NaturalCoreForm
public import KsIndexLean.VerticalWeakGreen

@[expose] public section


/-! Transfer of the positive-ground-state argument to the full zero-trace
Sobolev domain, using compactly supported smooth density. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.GroundState
open KsIndex.Trace KsIndex.WeakH1 KsIndex.SingleDisk KsIndex.Surface

lemma ground_state_Qd_nonnegative {k : ℕ} (hk : 2 ≤ k)
    (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f)
    (hs : tsupport f ⊆ (WeakH1.disk : Set ℂ)) :
    0 ≤ KsIndex.SingleDiskBridge.Qd k f := by
  have h := radial_ground_test_nonnegative hk f hf hs
  have hi (a : ℂ → ℝ) (ha : Continuous a) :
      IntegrableOn a (WeakH1.disk : Set ℂ) :=
    (ha.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set
      Metric.ball_subset_closedBall
  rw [integral_sub (hi _ (KsIndex.PiAssembly.continuous_gradSq hf))
    (hi _ (KsIndex.PiAssembly.continuous_potVsq hf.continuous))] at h
  change 0 ≤ dirichletG k f - potentialG k f
  rw [dirichletG_sub_potentialG hk f]
  exact h

/-- The auxiliary one-fold rotation imposes no character restriction. Its
Dirichlet sector therefore contains every zero-trace Sobolev function. -/
lemma zeroTrace_mem_trivial_DD (u : ComplexH1)
    (hu : u ∈ zeroTraceDomain Set.univ) : u ∈ mixedCharacterDomain 1 0 false false := by
  refine ⟨?_, (mem_trivial_NN_sector u).2⟩
  constructor
  · exact zeroTraceDomain_antitone (Set.subset_univ _) hu
  · exact zeroTraceDomain_antitone (Set.subset_univ _) hu

lemma continuous_energy_on (V : BoundedRealPotential) (D : Submodule ℂ ComplexH1) :
    Continuous (fun v : D => (weakJacobi V v.val v.val).re) := by
  have hp : Continuous (fun v : D => ((v : ComplexH1), (v : ComplexH1))) :=
    continuous_subtype_val.prodMk continuous_subtype_val
  have hw := (continuous_weakJacobi V).comp hp
  simpa only [Function.comp_def] using Complex.continuous_re.comp hw

/-- Nonnegativity on the full Dirichlet domain from the positive vertical
Jacobi field, compact-core density, and continuity of the actual weak form. -/
theorem fullDirichlet_nonnegative_ground_state {k : ℕ} (hk : 2 ≤ k)
    (u : ComplexH1) (hu : u ∈ zeroTraceDomain Set.univ) :
    0 ≤ (weakJacobi (surfacePotential k) u u).re := by
  let E : Submodule ℂ ComplexH1 := mixedCharacterDomain 1 0 false false
  have hc := continuous_energy_on (surfacePotential k) E
  have hd := naturalCharacterToMixed_denseRange (by decide : 1 ≤ 1) 0 false false
  refine hd.induction_on
    (p := fun v : E => 0 ≤ (weakJacobi (surfacePotential k) v.val v.val).re)
    (⟨u, zeroTrace_mem_trivial_DD u hu⟩ : E) (isClosed_le continuous_const hc) ?_
  intro f
  change 0 ≤ (weakJacobi (surfacePotential k)
    (naturalCoreH1 (by decide : 1 ≤ 1) ⟨f.val, f.property.1⟩)
    (naturalCoreH1 (by decide : 1 ≤ 1) ⟨f.val, f.property.1⟩)).re
  rw [show naturalCoreH1 (by decide : 1 ≤ 1) (⟨f.val, f.property.1⟩ : NatCc 1 false false) =
      smoothToH1 (naturalCoreData (by decide : 1 ≤ 1) ⟨f.val, f.property.1⟩) from rfl,
    smooth_weakJacobi_self_eq_Qd hk, Complex.ofReal_re]
  exact ground_state_Qd_nonnegative hk f.val
    ((dd_contDiff f.property.1).of_le (by simp)) (dd_tsupport_subset_disk f.property.1)

end KsIndex.GroundState
