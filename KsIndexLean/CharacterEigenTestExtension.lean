module

public import KsIndexLean.GeneralCharacterTestExtension
public import KsIndexLean.NeumannOpenArcUniqueness

@[expose] public section


noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.FormIndex KsIndex.Spherical

lemma sphericalEigenJacobi_diskRotation (k : ℕ) (lam θ : ℝ) (u v : ComplexH1) :
    weakJacobi (sphericalEigenPotential (surfacePotential k) lam)
      (diskRotation θ u) (diskRotation θ v) =
    weakJacobi (sphericalEigenPotential (surfacePotential k) lam) u v := by
  rw [weakJacobi_sphericalEigenPotential, weakJacobi_sphericalEigenPotential,
    surfaceJacobi_diskRotation, weightedDisk_mass_diskRotation]

lemma sphericalEigenJacobi_character_test_rotation (k : ℕ) (lam θ : ℝ) (c : ℂ)
    (hc : ‖c‖ = 1) (u : ComplexH1) (hu : diskRotation θ u = c • u)
    (v : ComplexH1) :
    weakJacobi (sphericalEigenPotential (surfacePotential k) lam) u (diskRotation θ v) =
      c * weakJacobi (sphericalEigenPotential (surfacePotential k) lam) u v := by
  have h := sphericalEigenJacobi_diskRotation k lam θ u v
  rw [hu, weakJacobi_smul_left] at h
  have hc' : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  calc
    _ = (c * (starRingEnd ℂ) c) * weakJacobi (sphericalEigenPotential (surfacePotential k) lam) u (diskRotation θ v) := by rw [hc', one_mul]
    _ = c * weakJacobi (sphericalEigenPotential (surfacePotential k) lam) u v := by rw [mul_assoc, h]

/-- Character-restricted eigen-equations extend to all tests in an invariant
boundary domain, for every real spectral parameter. -/
lemma sphericalEigen_cyclic_tests_suffice {k : ℕ} (hk : 0 < k) (j : ℕ) (lam : ℝ)
    (D : Submodule ℂ ComplexH1)
    (hD : ∀ v ∈ D, diskRotation (-(2 * Real.pi) / k) v ∈ D)
    (u : ComplexH1) (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1,
      v ∈ D ⊓ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v =
        (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    ∀ v ∈ D, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v) := by
  let V := sphericalEigenPotential (surfacePotential k) lam
  let L : ComplexH1 →ₗ[ℂ] ℂ :=
    { toFun := weakJacobi V u
      map_add' := weakJacobi_add_right V u
      map_smul' := fun a v => weakJacobi_smul_right V a u v }
  have hz : ∀ v ∈ D, L v = 0 := by
    apply cyclicCharacter_tests_suffice (diskRotation _).toLinearMap (zeta k ^ j)
      k hk (cyclicCharacter_power hk j) (cyclicDiskRotation_period hk) D hD L
      (sphericalEigenJacobi_character_test_rotation k lam _ _ (cyclicCharacter_norm hk j) u
        ((mem_weakCharacterDomain _ _ u).mp hu))
    intro v hv he
    exact (spherical_eigen_equation_iff _ lam u v).mp
      (hQ v ⟨hv, (mem_weakCharacterDomain _ _ v).mpr he⟩)
  intro v hv
  exact (spherical_eigen_equation_iff _ lam u v).mpr (hz v hv)

lemma sphericalEigen_neumann_character_tests_extend {k : ℕ} (hk : 0 < k) (j : ℕ) (lam : ℝ)
    (u : ComplexH1) (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j),
      weakJacobi (surfacePotential k) u v =
        (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    ∀ v : ComplexH1, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v) := by
  intro v
  exact sphericalEigen_cyclic_tests_suffice hk j lam ⊤ (fun _ _ => Submodule.mem_top)
    u hu (fun w hw => hQ w hw.2) v Submodule.mem_top

/-- Open-arc uniqueness on the paper's actual cyclic character sector. -/
theorem sphericalEigen_neumann_character_openArc_eq_zero {k : ℕ}
    (hk : 0 < k) (j : ℕ) (lam : ℝ) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j),
      weakJacobi (surfacePotential k) u v =
        (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (A : Set Circle₁) (hA : IsOpen A) (hne : A.Nonempty) (hz : u ∈ zeroTraceDomain A) : u = 0 :=
  sphericalEigen_neumann_mem_zeroTrace_eq_zero k lam u
    (sphericalEigen_neumann_character_tests_extend hk j lam u hu hQ) A hA hne hz

end KsIndex.Trace
