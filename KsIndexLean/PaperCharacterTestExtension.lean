module

public import KsIndexLean.CubicCharacterTests
public import KsIndexLean.FullDirichletNullity
public import KsIndexLean.DiskTraceCovariance

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.FormIndex

lemma diskRotation_neg_two_pi (u : ComplexH1) : diskRotation (-(2 * Real.pi)) u = u := by
  apply valueCLM_injective
  apply Lp.ext
  filter_upwards [diskRotation_value_ae (-(2 * Real.pi)) u] with z hz
  rw [hz]
  simp only [Function.comp_apply]
  apply congrArg (fun w => valueCLM u w)
  rw [planeRotation_apply]
  have he : (((-(2 * Real.pi) : ℝ) : ℂ) * Complex.I) = -(2 * Real.pi * Complex.I) := by push_cast; ring
  rw [he, Complex.exp_neg, Complex.exp_two_pi_mul_I]
  simp

lemma paperDiskRotation_cube (u : ComplexH1) :
    diskRotation (-(2 * Real.pi) / 3)
      (diskRotation (-(2 * Real.pi) / 3) (diskRotation (-(2 * Real.pi) / 3) u)) = u := by
  rw [← diskRotation_add, ← diskRotation_add]
  have he : (-(2 * Real.pi) / 3 + -(2 * Real.pi) / 3) + -(2 * Real.pi) / 3 = -(2 * Real.pi) := by ring
  rw [he, diskRotation_neg_two_pi]

lemma diskRotation_mem_fullZeroTrace (θ : ℝ) (u : ComplexH1)
    (hu : u ∈ zeroTraceDomain Set.univ) : diskRotation θ u ∈ zeroTraceDomain Set.univ := by
  rw [mem_fullZeroTrace_iff, diskTrace_rotation, (mem_fullZeroTrace_iff u).mp hu, map_zero]

lemma paperCharacter_cube (j : ℕ) : (zeta 3 ^ j) ^ 3 = 1 := by
  rw [← pow_mul, Nat.mul_comm j 3, pow_mul, zeta_pow_N (by decide : 0 < 3), one_pow]

lemma paperCharacter_norm (j : ℕ) : ‖zeta 3 ^ j‖ = 1 := by
  have h := congrArg norm (paperCharacter_cube j)
  rw [norm_pow, norm_one] at h
  exact (pow_left_inj₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1) (by decide : (3 : ℕ) ≠ 0)).mp (by simpa using h)

/-- Character-restricted Dirichlet testing implies the full Dirichlet weak equation. -/
lemma paperDirichlet_character_tests_extend (j : ℕ) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (zeta 3 ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / 3) (zeta 3 ^ j) →
      weakJacobi (surfacePotential 3) u v = 0) :
    ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential 3) u v = 0 := by
  apply surfaceJacobi_cubic_tests_suffice 3 _ _ (paperCharacter_cube j)
    (paperCharacter_norm j) paperDiskRotation_cube (zeroTraceDomain Set.univ)
    (diskRotation_mem_fullZeroTrace _) u ((mem_weakCharacterDomain _ _ u).mp hu)
  intro v hv hc
  exact hQ v ⟨hv, (mem_weakCharacterDomain _ _ v).mpr hc⟩

/-- The analogous extension for a full Neumann character sector. -/
lemma paperNeumann_character_tests_extend (j : ℕ) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (zeta 3 ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (zeta 3 ^ j) →
      weakJacobi (surfacePotential 3) u v = 0) :
    ∀ v : ComplexH1, weakJacobi (surfacePotential 3) u v = 0 := by
  have h := surfaceJacobi_cubic_tests_suffice 3 _ _ (paperCharacter_cube j)
    (paperCharacter_norm j) paperDiskRotation_cube (⊤ : Submodule ℂ ComplexH1)
    (fun _ _ => trivial) u ((mem_weakCharacterDomain _ _ u).mp hu)
    (fun v _ hv => hQ v ((mem_weakCharacterDomain _ _ v).mpr hv))
  exact fun v => h v trivial

/-- Every full Dirichlet character-kernel vector is a multiple of the vertical field. -/
lemma paperDirichlet_character_kernel_spanned (j : ℕ) (u : ComplexH1)
    (hu : u ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / 3) (zeta 3 ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / 3) (zeta 3 ^ j) →
      weakJacobi (surfacePotential 3) u v = 0) :
    ∃ c : ℂ, u = c • verticalThreeH1 := by
  exact fullDirichlet_kernel_eq_smul_vertical ⟨u, hu.1⟩
    (fun v => paperDirichlet_character_tests_extend j u hu.2 hQ v v.property)

end KsIndex.Trace
