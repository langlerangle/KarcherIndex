module

public import KsIndexLean.D5CarrierBridge
public import KsIndexLean.GeneralCharacterTestExtension
public import KsIndexLean.ArcTraceRotation
public import KsIndexLean.ChainChartRotation
public import KsIndexLean.WeakTransmissionDomains

@[expose] public section


noncomputable section
namespace KsIndex.FormIndex
open Finset

/-- Finite Fourier averaging projects any complex module carrying a cyclic
operator onto the prescribed character. -/
lemma cyclic_average_mem_eigenspace {E : Type*} [AddCommGroup E] [Module ℂ E]
    (g : Module.End ℂ E) (r : ℕ) {N : ℕ} (hN : 0 < N)
    (hgN : ∀ u, (g ^ N) u = u) (v : E) :
    (N : ℂ)⁻¹ • (∑ i ∈ Finset.range N, xi N ^ (r * i) • (g ^ i) v)
      ∈ Module.End.eigenspace g (zeta N ^ r) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [Module.End.mem_eigenspace_iff]
  set S : ℕ → E := fun j => xi (m + 1) ^ (r * j) • (g ^ j) v
    with hSdef
  have hterm : ∀ k, g (S k) = zeta (m + 1) ^ r • S (k + 1) := by
    intro k
    simp only [hSdef]
    rw [map_smul, ← Module.End.mul_apply, ← pow_succ', smul_smul]
    congr 1
    -- ξ^{rk} = ζ^r · ξ^{r(k+1)}
    rw [mul_add, mul_one, pow_add, ← mul_assoc, mul_comm (zeta (m + 1) ^ r),
      mul_assoc, zeta_pow_mul_xi_pow hN r, mul_one]
  have hwrap : S (m + 1) = S 0 := by
    simp only [hSdef]
    rw [hgN v, mul_zero, pow_zero, pow_zero, Module.End.one_apply, one_smul,
      mul_comm r, pow_mul, xi_pow_N hN, one_pow, one_smul]
  calc g ((↑(m + 1) : ℂ)⁻¹ • ∑ k ∈ range (m + 1), S k)
      = (↑(m + 1) : ℂ)⁻¹ • ∑ k ∈ range (m + 1), g (S k) := by
        rw [map_smul, map_sum]
    _ = (↑(m + 1) : ℂ)⁻¹ • ∑ k ∈ range (m + 1),
          zeta (m + 1) ^ r • S (k + 1) := by
        congr 1
        exact Finset.sum_congr rfl fun k _ => hterm k
    _ = zeta (m + 1) ^ r • ((↑(m + 1) : ℂ)⁻¹ •
          ∑ k ∈ range (m + 1), S (k + 1)) := by
        rw [← Finset.smul_sum, smul_comm]
    _ = zeta (m + 1) ^ r • ((↑(m + 1) : ℂ)⁻¹ •
          ∑ k ∈ range (m + 1), S k) := by
        congr 2
        -- Σ_{k<m+1} S (k+1) = Σ_{k<m+1} S k, since S (m+1) = S 0
        have h1 : ∑ i ∈ range (m + 1 + 1), S i =
            (∑ i ∈ range (m + 1), S (i + 1)) + S 0 :=
          Finset.sum_range_succ' S (m + 1)
        have h2 : ∑ i ∈ range (m + 1 + 1), S i =
            (∑ i ∈ range (m + 1), S i) + S (m + 1) :=
          Finset.sum_range_succ S (m + 1)
        have h3 := h1.symm.trans h2
        rw [hwrap] at h3
        exact add_right_cancel h3

end KsIndex.FormIndex

namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.FormIndex

/-- The continuous H1 character average lands in the weak
rotation eigenspace. -/
lemma carrierCharProj_mem_character {k : ℕ} (hk : 0 < k) (r : ℕ) (u : ComplexH1) :
    carrierCharProj k r u ∈ weakCharacterDomain (rotAngle k) (zeta k ^ r) := by
  apply (mem_weakCharacterDomain _ _ _).mpr
  have h := cyclic_average_mem_eigenspace (diskRotation (rotAngle k)).toLinearMap r hk
    (cyclicDiskRotation_period hk) u
  rw [Module.End.mem_eigenspace_iff] at h
  simpa only [carrierCharProj_apply, diskRotation_power, LinearIsometry.coe_toLinearMap] using h

/-- The same rotation average on both disks preserves either slit phase
relation, without requiring the phase to have finite order. -/
lemma carrierCharProj_arc_phase {k : ℕ} (hk : 0 < k) (r a : ℕ) (c : ℂ)
    (u v : ComplexH1) (h : arcTrace (boundaryArc k a) u = c • arcTrace (boundaryArc k a) v) :
    arcTrace (boundaryArc k a) (carrierCharProj k r u) =
      c • arcTrace (boundaryArc k a) (carrierCharProj k r v) := by
  have hp i : arcTrace (boundaryArc k a) (((diskRotation (rotAngle k)).toLinearMap ^ i) u) =
      c • arcTrace (boundaryArc k a) (((diskRotation (rotAngle k)).toLinearMap ^ i) v) := by
    induction i with
    | zero => exact h
    | succ i hi =>
      simp only [pow_succ', Module.End.mul_apply]
      exact arcTrace_rotation_phase _ (isOpen_boundaryArc k a).measurableSet _
        (circleRotate_boundaryArc_preimage k a _ (paperRotation_root k hk)) c _ _ hi
  simp only [diskRotation_power] at hp
  simp only [carrierCharProj_apply, map_smul, map_sum, hp, smul_comm _ c,
    ← Finset.smul_sum]

/-- Independent of the slit phase, the pair average satisfies both the slit
trace conditions and the chosen rotation character. -/
lemma carrierCharProj_pair_mem {k : ℕ} (hk : 0 < k) (r : ℕ) (c : ℂ)
    (u : DiskPairH1) (hu : u ∈ slitTraceDomain k c) :
    (carrierCharProj k r u.1, carrierCharProj k r u.2) ∈
      slitTraceDomain k c ⊓ pairCharacterDomain (rotAngle k) (zeta k ^ r) := by
  obtain ⟨h1, h0⟩ := (mem_slitTraceDomain k c u).mp hu
  constructor
  · apply (mem_slitTraceDomain k c _).mpr
    constructor
    · simpa only [one_smul] using
        carrierCharProj_arc_phase hk r 1 1 u.1 u.2 (by simpa only [one_smul] using h1)
    · exact carrierCharProj_arc_phase hk r 0 c u.1 u.2 h0
  · exact ⟨carrierCharProj_mem_character hk r u.1, carrierCharProj_mem_character hk r u.2⟩

/-- Pair projection preserves convergence to data already in the character. -/
lemma carrierCharProj_pair_tendsto {k : ℕ} (hk : 0 < k) (r : ℕ)
    {U : ℕ → DiskPairH1} {u : DiskPairH1}
    (hU : Filter.Tendsto U Filter.atTop (nhds u))
    (hu : u ∈ pairCharacterDomain (rotAngle k) (zeta k ^ r)) :
    Filter.Tendsto (fun n => (carrierCharProj k r (U n).1, carrierCharProj k r (U n).2))
      Filter.atTop (nhds u) := by
  have h1 := carrierCharProj_tendsto k r ((continuous_fst.tendsto u).comp hU)
  have h2 := carrierCharProj_tendsto k r ((continuous_snd.tendsto u).comp hU)
  rw [carrierCharProj_eq_self (u := u.1) hk hu.1] at h1
  rw [carrierCharProj_eq_self (u := u.2) hk hu.2] at h2
  exact h1.prodMk_nhds h2

end KsIndex.Trace
