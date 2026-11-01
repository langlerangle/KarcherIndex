module

public import KsIndexLean.CyclicCharacterTests
public import KsIndexLean.PaperCharacterTestExtension

@[expose] public section


noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.FormIndex

lemma diskRotation_power (θ : ℝ) (n : ℕ) (u : ComplexH1) :
    ((diskRotation θ).toLinearMap ^ n) u = diskRotation ((n : ℝ) * θ) u := by
  induction n with
  | zero => simp [diskRotation_zero]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change diskRotation θ (diskRotation ((n : ℝ) * θ) u) = _
    rw [← diskRotation_add]
    congr 1
    push_cast
    ring

lemma cyclicDiskRotation_period {k : ℕ} (hk : 0 < k) (u : ComplexH1) :
    ((diskRotation (-(2 * Real.pi) / k)).toLinearMap ^ k) u = u := by
  rw [diskRotation_power]
  have he : (k : ℝ) * (-(2 * Real.pi) / k) = -(2 * Real.pi) := by
    field_simp
  rw [he, diskRotation_neg_two_pi]

lemma cyclicCharacter_power {k : ℕ} (hk : 0 < k) (j : ℕ) :
    (zeta k ^ j) ^ k = 1 := by
  rw [← pow_mul, Nat.mul_comm j k, pow_mul, zeta_pow_N hk, one_pow]

lemma cyclicCharacter_norm {k : ℕ} (hk : 0 < k) (j : ℕ) :
    ‖zeta k ^ j‖ = 1 := by
  have h := congrArg norm (cyclicCharacter_power hk j)
  rw [norm_pow, norm_one] at h
  exact (pow_left_inj₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    (Nat.ne_of_gt hk)).mp (by simpa using h)

/-- Full-domain weak testing follows from character testing on any domain
preserved by the paper's k-fold rotation. -/
lemma surfaceJacobi_cyclic_tests_suffice {k : ℕ} (hk : 0 < k) (j : ℕ)
    (D : Submodule ℂ ComplexH1)
    (hD : ∀ v ∈ D, diskRotation (-(2 * Real.pi) / k) v ∈ D)
    (u : ComplexH1) (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1,
      v ∈ D ⊓ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∀ v ∈ D, weakJacobi (surfacePotential k) u v = 0 := by
  let L : ComplexH1 →ₗ[ℂ] ℂ :=
    { toFun := weakJacobi (surfacePotential k) u
      map_add' := weakJacobi_add_right (surfacePotential k) u
      map_smul' := fun a v => weakJacobi_smul_right (surfacePotential k) a u v }
  apply cyclicCharacter_tests_suffice (diskRotation _).toLinearMap (zeta k ^ j)
    k hk (cyclicCharacter_power hk j) (cyclicDiskRotation_period hk) D hD L
    (surfaceJacobi_character_test_rotation k _ _ (cyclicCharacter_norm hk j) u
      ((mem_weakCharacterDomain _ _ u).mp hu))
  intro v hv he
  exact hQ v ⟨hv, (mem_weakCharacterDomain _ _ v).mpr he⟩

lemma generalDirichlet_character_tests_extend {k : ℕ} (hk : 0 < k) (j : ℕ)
    (u : ComplexH1) (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v = 0 :=
  surfaceJacobi_cyclic_tests_suffice hk j _ (diskRotation_mem_fullZeroTrace _) u hu hQ

end KsIndex.Trace
