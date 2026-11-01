module

public import KsIndexLean.WeakCharacterProjection

@[expose] public section


/-!
# Reconstruction by the finite rotation characters

The continuous H1 character averages sum to the original weak function.
Each average preserves the full zero-trace condition.
-/
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.FormIndex

lemma carrierCharProj_sum {k : ℕ} (hk : 0 < k) (u : ComplexH1) :
    (∑ r : Fin k, carrierCharProj k r u) = u := by
  simp only [carrierCharProj_apply]
  rw [← Finset.smul_sum,
    Fin.sum_univ_eq_sum_range
      (fun r : ℕ => ∑ i ∈ Finset.range k, xi k ^ (r * i) •
        diskRotation ((i : ℝ) * rotAngle k) u) k,
    Finset.sum_comm]
  have hinner : ∀ i ∈ Finset.range k,
      (∑ r ∈ Finset.range k, xi k ^ (r * i) •
        diskRotation ((i : ℝ) * rotAngle k) u) =
        if i = 0 then (k : ℂ) • u else 0 := by
    intro i hi
    rw [← Finset.sum_smul]
    have hre : (∑ r ∈ Finset.range k, xi k ^ (r * i)) =
        ∑ r ∈ Finset.range k, (xi k ^ i) ^ r :=
      Finset.sum_congr rfl fun r _ => by rw [← pow_mul, mul_comm]
    rw [hre]
    split_ifs with hi0
    · subst i
      simp [diskRotation_zero]
    · have hne := xi_pow_ne_one hk hi0 (Finset.mem_range.mp hi)
      have hpow : (xi k ^ i) ^ k = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, xi_pow_N hk, one_pow]
      rw [geom_sum_eq_zero_of_pow_eq_one hpow hne, zero_smul]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' (Finset.range k) 0,
    if_pos (Finset.mem_range.mpr hk), smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hk.ne' : (k : ℂ) ≠ 0), one_smul]

lemma carrierCharProj_mem_fullDirichlet (k r : ℕ) (u : ComplexH1)
    (hu : u ∈ zeroTraceDomain Set.univ) :
    carrierCharProj k r u ∈ zeroTraceDomain Set.univ := by
  rw [carrierCharProj_apply]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (diskRotation_mem_fullZeroTrace _ u hu)

lemma fullDirichlet_character_reconstruction {k : ℕ} (hk : 0 < k)
    (u : ComplexH1) (hu : u ∈ zeroTraceDomain Set.univ) :
    (∑ r : Fin k, carrierCharProj k r u) = u ∧
      ∀ r : Fin k, carrierCharProj k r u ∈
        zeroTraceDomain Set.univ ⊓ weakCharacterDomain (rotAngle k) (zeta k ^ (r : ℕ)) :=
  ⟨carrierCharProj_sum hk u, fun r =>
    ⟨carrierCharProj_mem_fullDirichlet k r u hu, carrierCharProj_mem_character hk r u⟩⟩

/-- Distinct rotation characters are orthogonal for the actual Jacobi form. -/
lemma surfaceJacobi_distinct_characters {k : ℕ} (hk : 0 < k) (r s : Fin k)
    (hrs : r ≠ s) (u v : ComplexH1)
    (hu : u ∈ weakCharacterDomain (rotAngle k) (zeta k ^ (r : ℕ)))
    (hv : v ∈ weakCharacterDomain (rotAngle k) (zeta k ^ (s : ℕ))) :
    weakJacobi (surfacePotential k) u v = 0 := by
  have h := surfaceJacobi_diskRotation k (rotAngle k) u v
  rw [(mem_weakCharacterDomain _ _ _).mp hu,
    (mem_weakCharacterDomain _ _ _).mp hv,
    weakJacobi_smul_left, weakJacobi_smul_right, conj_zeta_pow] at h
  have hn := xi_pow_mul_zeta_pow_ne_one hk r.isLt s.isLt
    (fun e => hrs (Fin.ext e))
  have hz : (xi k ^ (r : ℕ) * zeta k ^ (s : ℕ) - 1) *
      weakJacobi (surfacePotential k) u v = 0 := by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hn)

end KsIndex.Trace
