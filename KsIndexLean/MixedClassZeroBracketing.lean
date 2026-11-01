module

public import KsIndexLean.CountIndexIdentifications
public import KsIndexLean.GeneralDirichletValues
public import KsIndexLean.GroundStateDirichletIndexZero
public import KsIndexLean.WeakHemisphereIndex
public import KsIndexLean.SlitReflectionNullity
public import KsIndexLean.SectorInfinite

@[expose] public section


/-! # Class-zero Zaremba index/nullity via the Dirichlet strict bracketing

Paper-faithful alternative to the Gram (`GramDip`) class-zero route: the class-zero
(`r = 0`) mixed index `1` and nullity `0` from the pure-Dirichlet lower comparison
(`sector_weakIndex_add_nullity_le_mixed`, `ind_DD=0`, `nul_DD=1`) and the pure-Neumann
upper comparison (`sector_weakIndex_add_nullity_le_neumann`, `ind_NN=1`), never through
`mixed_weak_index_one` / `seamNat_TF_eq_one` / `GramDip`. -/

noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.Trace KsIndex.GroundState KsIndex.SingleDiskBridge

variable {k : ℕ}

lemma diskWeakIndex_def' (D : Submodule ℂ ComplexH1) (V : BoundedRealPotential) :
    diskWeakIndex D V =
      KsIndex.NegativeDensity.negativeIndex (fun u : D => (weakJacobi V u u).re) := rfl

lemma diskWeakNullity_def' (D : Submodule ℂ ComplexH1) (V : BoundedRealPotential) :
    diskWeakNullity D V = Module.finrank ℂ (@formRadical D inferInstance
      (diskDomain_innerProductSpace D) (domainJacobiForm D V)) := rfl

/-- **Class-zero paper route (conditional on sector infinitude)**: `ind_{DN,0}=1`,
`nul_{DN,0}=0`, either mixed orientation `b1 ≠ b0`, via Dirichlet lower + Neumann upper. -/
theorem mixed_class_zero_pair_bracketing (hk : 3 ≤ k) {b1 b0 : Bool} (hb : b1 ≠ b0)
    [Infinite (diskSpectralData (mixedCharacterDomain k 0 false false)
      (surfacePotential k)).eigenbasisIndex]
    [Infinite (diskSpectralData (mixedCharacterDomain k 0 b1 b0)
      (surfacePotential k)).eigenbasisIndex]
    [Infinite (diskSpectralData (mixedCharacterDomain k 0 true true)
      (surfacePotential k)).eigenbasisIndex] :
    diskWeakIndex (mixedCharacterDomain k 0 b1 b0) (surfacePotential k) = 1 ∧
    diskWeakNullity (mixedCharacterDomain k 0 b1 b0) (surfacePotential k) = 0 := by
  have hb' : b1 = false ∨ b0 = false := by cases b1 <;> cases b0 <;> simp_all
  have hnb : (!b1) = b0 := by cases b1 <;> cases b0 <;> simp_all
  have : Infinite (diskSpectralData (mixedCharacterDomain k 0 b1 (!b1))
      (surfacePotential k)).eigenbasisIndex := by rw [hnb]; infer_instance
  have hlow := sector_weakIndex_add_nullity_le_mixed (k := k) (by omega : 0 < k) 0 b1
  rw [hnb,
    ← diskWeakIndex_def' (mixedCharacterDomain k 0 false false) (surfacePotential k),
    ← diskWeakNullity_def' (mixedCharacterDomain k 0 false false) (surfacePotential k),
    ← diskWeakIndex_def' (mixedCharacterDomain k 0 b1 b0) (surfacePotential k),
    pureDirichlet_weak_index_zero_ground_state hk 0,
    pureSector_dirichlet_nullity_gen (by omega : 2 ≤ k) (by omega : (0:ℕ) < k)] at hlow
  simp only [ite_true, Nat.cast_one, zero_add] at hlow
  have hup := sector_weakIndex_add_nullity_le_neumann (k := k) (by omega : 0 < k) 0 b1 b0 hb'
  rw [← diskWeakIndex_def' (mixedCharacterDomain k 0 b1 b0) (surfacePotential k),
    ← diskWeakNullity_def' (mixedCharacterDomain k 0 b1 b0) (surfacePotential k),
    ← diskWeakIndex_def' (mixedCharacterDomain k 0 true true) (surfacePotential k),
    pureNeumann_weak_index hk (by omega : (0:ℕ) < k)] at hup
  simp only [Nat.cast_zero, neumannCount_zero hk, ite_true, zero_add] at hup
  have hidx : diskWeakIndex (mixedCharacterDomain k 0 b1 b0) (surfacePotential k) = 1 :=
    le_antisymm (le_trans le_self_add hup) hlow
  refine ⟨hidx, ?_⟩
  rw [hidx] at hup
  have hnat : 1 + diskWeakNullity (mixedCharacterDomain k 0 b1 b0) (surfacePotential k) ≤ 1 := by
    exact_mod_cast hup
  omega

/-- **Class-zero paper route (unconditional)**: sector infinitude discharged by
`sector_eigenbasisIndex_infinite`; only `k ≥ 3` and distinct boundary flags remain. -/
theorem mixed_class_zero_pair_bracketing_uncond (hk : 3 ≤ k) {b1 b0 : Bool} (hb : b1 ≠ b0) :
    diskWeakIndex (mixedCharacterDomain k 0 b1 b0) (surfacePotential k) = 1 ∧
    diskWeakNullity (mixedCharacterDomain k 0 b1 b0) (surfacePotential k) = 0 := by
  have := sector_eigenbasisIndex_infinite k (by omega) 0 false false
  have := sector_eigenbasisIndex_infinite k (by omega) 0 b1 b0
  have := sector_eigenbasisIndex_infinite k (by omega) 0 true true
  exact mixed_class_zero_pair_bracketing hk hb

end KsIndex.Spectral
