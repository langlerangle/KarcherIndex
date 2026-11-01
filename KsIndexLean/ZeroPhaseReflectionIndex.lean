module

public import KsIndexLean.WeakHemisphereIndex
public import KsIndexLean.FullBoundaryMatching
public import KsIndexLean.PaperSmoothSectorIndexEquality

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.NegativeDensity

def fullEquatorReflectionEquiv :
    transmissionDomain Set.univ 1 ≃ₗ[ℂ] ComplexH1 × zeroTraceDomain Set.univ where
  toFun u := ((2 : ℂ)⁻¹ • (u.val.1 + u.val.2),
    ⟨(2 : ℂ)⁻¹ • (u.val.1 - u.val.2), by
      have hu := (mem_transmissionDomain Set.univ 1 u.val).mp u.property
      rw [one_smul] at hu
      change arcTrace Set.univ ((2 : ℂ)⁻¹ • (u.val.1 - u.val.2)) = 0
      rw [map_smul, map_sub, hu, sub_self, smul_zero]⟩)
  invFun v := ⟨(v.1 + v.2.val, v.1 - v.2.val), by
    apply (mem_transmissionDomain Set.univ 1 _).mpr
    have hv : arcTrace Set.univ v.2.val = 0 := v.2.property
    simp only [map_add, map_sub, hv, add_zero, sub_zero, one_smul]⟩
  left_inv u := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> module
  right_inv v := by
    apply Prod.ext
    · dsimp
      module
    · apply Subtype.ext
      dsimp
      module
  map_add' u v := by
    apply Prod.ext
    · dsimp
      module
    · apply Subtype.ext
      dsimp
      module
  map_smul' c u := by
    apply Prod.ext
    · dsimp
      module
    · apply Subtype.ext
      dsimp
      module


def fullEquatorSubspaceReflectionEquiv (C : Submodule ℂ ComplexH1) :
    ↥(transmissionDomain Set.univ 1 ⊓
      (C.comap (ContinuousLinearMap.fst ℂ ComplexH1 ComplexH1).toLinearMap ⊓
       C.comap (ContinuousLinearMap.snd ℂ ComplexH1 ComplexH1).toLinearMap)) ≃ₗ[ℂ]
      C × ↥(zeroTraceDomain Set.univ ⊓ C) := by
  let e := fullEquatorReflectionEquiv
  have hc (u : transmissionDomain Set.univ 1) (hu : u.val.1 ∈ C ∧ u.val.2 ∈ C) :
      (e u).1 ∈ C ∧ (e u).2.val ∈ C := by
    constructor
    · exact C.smul_mem _ (C.add_mem hu.1 hu.2)
    · exact C.smul_mem _ (C.sub_mem hu.1 hu.2)
  refine
    { toFun := fun u => (⟨(e ⟨u.val, u.property.1⟩).1, (hc ⟨u.val, u.property.1⟩ u.property.2).1⟩,
        ⟨(e ⟨u.val, u.property.1⟩).2.val,
          ⟨(e ⟨u.val, u.property.1⟩).2.property, (hc ⟨u.val, u.property.1⟩ u.property.2).2⟩⟩)
      invFun := fun v => ⟨(e.symm (v.1.val, ⟨v.2.val, v.2.property.1⟩)).val,
        ⟨(e.symm _).property, (even_odd_mem_iff C _ _).mpr
          ⟨v.1.property, v.2.property.2⟩⟩⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro u v
    have h := e.map_add ⟨u.val, u.property.1⟩ ⟨v.val, v.property.1⟩
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · apply Subtype.ext
      exact congrArg (fun w => w.2.val) h
  · intro c u
    have h := e.map_smul c ⟨u.val, u.property.1⟩
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · apply Subtype.ext
      exact congrArg (fun w => w.2.val) h
  · intro u
    apply Subtype.ext
    exact congrArg (fun w : transmissionDomain Set.univ 1 => w.val) (e.symm_apply_apply ⟨u.val, u.property.1⟩)
  · intro v
    have h := e.apply_symm_apply (v.1.val, ⟨v.2.val, v.2.property.1⟩)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · apply Subtype.ext
      exact congrArg (fun w => w.2.val) h


lemma full_zeroTrace_eq {k : ℕ} (hk : 1 ≤ k) :
    zeroTraceDomain Set.univ = mixedTraceDomain k false false := by
  ext u
  change arcTrace Set.univ u = 0 ↔
    arcTrace (boundaryArc k 1) u = 0 ∧ arcTrace (boundaryArc k 0) u = 0
  simpa only [map_zero] using full_trace_eq_iff_arcs hk u 0

lemma paperSlit_zeroPhase_domain (j : ℕ) :
    paperSlitCharacterDomain 0 j = transmissionDomain Set.univ 1 ⊓
      pairCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j) := by
  unfold paperSlitCharacterDomain paperSlitDomain
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero]
  rw [slitTraceDomain_one_eq (by decide : 1 ≤ 3)]

def paperZeroPhaseReflectionEquiv (j : ℕ) :
    paperSlitCharacterDomain 0 j ≃ₗ[ℂ]
      ↥(mixedCharacterDomain 3 j true true) × ↥(mixedCharacterDomain 3 j false false) := by
  have hN : mixedCharacterDomain 3 j true true =
      weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j) := by
    simp [mixedCharacterDomain, mixedTraceDomain, naturalArcDomain]
  have hD : mixedCharacterDomain 3 j false false = zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j) := by
    rw [full_zeroTrace_eq (by decide : 1 ≤ 3)]
    rfl
  exact (LinearEquiv.ofEq _ _ (paperSlit_zeroPhase_domain j)).trans
    ((fullEquatorSubspaceReflectionEquiv _).trans
      (LinearEquiv.prodCongr (LinearEquiv.ofEq _ _ hN.symm) (LinearEquiv.ofEq _ _ hD.symm)))

lemma paperZeroPhaseReflection_jacobi (j : ℕ) (V : BoundedRealPotential)
    (u v : ↥(mixedCharacterDomain 3 j true true) × ↥(mixedCharacterDomain 3 j false false)) :
    weakJacobi V ((paperZeroPhaseReflectionEquiv j).symm u).val.1
        ((paperZeroPhaseReflectionEquiv j).symm v).val.1 +
      weakJacobi V ((paperZeroPhaseReflectionEquiv j).symm u).val.2
        ((paperZeroPhaseReflectionEquiv j).symm v).val.2 =
      2 * (weakJacobi V u.1.val v.1.val + weakJacobi V u.2.val v.2.val) :=
  weakJacobi_even_odd V _ _ _ _

lemma paperZeroPhase_pair_index {j : ℕ} (hj : j < 3) :
    pairWeakIndex (paperSlitCharacterDomain 0 j) (surfacePotential 3) = 1 := by
  rw [pair_reflection_index _ _ _ _ (paperZeroPhaseReflectionEquiv j)
    (paperZeroPhaseReflection_jacobi j (surfacePotential 3)),
    three_pureNeumann_weak_index hj, pureDirichlet_weak_index_zero (by decide), add_zero]

lemma pairWeakIndex_eq_pair_negativeIndex (D : Submodule ℂ DiskPairH1)
    (V : BoundedRealPotential) :
    pairWeakIndex D V = negativeIndex (fun u : D =>
      (weakJacobi V u.val.1 u.val.1 + weakJacobi V u.val.2 u.val.2).re) := by
  have hz : weakJacobi V 0 0 = 0 := by
    have h := weakJacobi_add_left V 0 0 0
    simp only [add_zero] at h
    linear_combination -h
  have h := negativeIndex_linearEquiv (pairHilbertCoordinates D)
    (fun u : D => (weakJacobi V u.val.1 u.val.1 + weakJacobi V u.val.2 u.val.2).re)
    (by change (weakJacobi V 0 0 + weakJacobi V 0 0).re = 0; simp only [hz, add_zero, Complex.zero_re])
  simpa only [pairWeakIndex, pairFiniteJacobi_eq] using h

/-- Each rotation character in the zero translation phase contributes one
negative direction to the smooth sector, for every positive m. -/
theorem paperSmooth_zeroPhase_sector_index (m : ℕ) [NeZero m] {j : ℕ} (hj : j < 3) :
    KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m) (paperSmoothJointSector m 0 j) = 1 := by
  rw [paperSmoothSector_index_eq_slit]
  rw [show ((0 : ℕ) : ℝ) / (m : ℝ) = 0 by simp]
  exact (pairWeakIndex_eq_pair_negativeIndex (paperSlitCharacterDomain 0 j)
    (surfacePotential 3)).symm.trans (paperZeroPhase_pair_index hj)

/-- The sum of the three rotation-sector indices at zero translation phase
is three. The conclusion concerns index; it does not assert a nullity count. -/
theorem paperSmooth_zeroPhase_total_index (m : ℕ) [NeZero m] :
    (∑ j : Fin 3, KsIndex.FormIndex.formIndex (SurfaceForm.Qs 3 m)
      (paperSmoothJointSector m 0 j.val)) = 3 := by
  simp only [paperSmooth_zeroPhase_sector_index m (Fin.is_lt _)]
  norm_num

end KsIndex.Spectral
