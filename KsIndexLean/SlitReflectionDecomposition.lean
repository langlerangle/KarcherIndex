module

public import KsIndexLean.SlitCharacterBracketing

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Split an actual Neumann slit pair into its even and odd hemisphere data.
The odd data vanish on the glued arc; neither component is discarded. -/
def slitNeumannReflectionEquiv (k : ℕ) :
    slitNeumannDomain k ≃ₗ[ℂ] ComplexH1 × zeroTraceDomain (boundaryArc k 1) where
  toFun u := ((2 : ℂ)⁻¹ • (u.val.1 + u.val.2),
    ⟨(2 : ℂ)⁻¹ • (u.val.1 - u.val.2), by
      have hu := (mem_transmissionDomain (boundaryArc k 1) 1 u.val).mp u.property
      rw [one_smul] at hu
      change arcTrace (boundaryArc k 1) ((2 : ℂ)⁻¹ • (u.val.1 - u.val.2)) = 0
      rw [map_smul, map_sub, hu, sub_self, smul_zero]⟩)
  invFun v := ⟨(v.1 + v.2.val, v.1 - v.2.val), by
    apply (mem_transmissionDomain (boundaryArc k 1) 1 _).mpr
    have hv : arcTrace (boundaryArc k 1) v.2.val = 0 := v.2.property
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


/-- Dirichlet slit data split into an even component vanishing on the slit
and an odd component vanishing on both boundary arcs. -/
def slitDirichletReflectionEquiv (k : ℕ) :
    slitDirichletDomain k ≃ₗ[ℂ]
      zeroTraceDomain (boundaryArc k 0) ×
        ↥(zeroTraceDomain (boundaryArc k 0) ⊓ zeroTraceDomain (boundaryArc k 1)) where
  toFun u := (⟨(2 : ℂ)⁻¹ • (u.val.1 + u.val.2),
      (zeroTraceDomain _).smul_mem _ ((zeroTraceDomain _).add_mem u.property.1.2 u.property.2)⟩,
    ⟨(2 : ℂ)⁻¹ • (u.val.1 - u.val.2),
      ⟨(zeroTraceDomain _).smul_mem _ ((zeroTraceDomain _).sub_mem u.property.1.2 u.property.2), by
        have hu := (mem_transmissionDomain (boundaryArc k 1) 1 u.val).mp u.property.1.1
        rw [one_smul] at hu
        change arcTrace (boundaryArc k 1) ((2 : ℂ)⁻¹ • (u.val.1 - u.val.2)) = 0
        rw [map_smul, map_sub, hu, sub_self, smul_zero]⟩⟩)
  invFun v := ⟨(v.1.val + v.2.val, v.1.val - v.2.val), by
    refine ⟨⟨?_, (zeroTraceDomain _).add_mem v.1.property v.2.property.1⟩,
      (zeroTraceDomain _).sub_mem v.1.property v.2.property.1⟩
    apply (mem_transmissionDomain (boundaryArc k 1) 1 _).mpr
    have hv : arcTrace (boundaryArc k 1) v.2.val = 0 := v.2.property.2
    simp only [map_add, map_sub, hv, add_zero, sub_zero, one_smul]⟩
  left_inv u := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> module
  right_inv v := by
    apply Prod.ext <;> apply Subtype.ext <;> dsimp <;> module
  map_add' u v := by
    apply Prod.ext <;> apply Subtype.ext <;> dsimp <;> module
  map_smul' c u := by
    apply Prod.ext <;> apply Subtype.ext <;> dsimp <;> module


/-- The even/odd reconstruction diagonalizes the Jacobi pairing with factor two. -/
lemma weakJacobi_even_odd (V : BoundedRealPotential) (a b c d : ComplexH1) :
    weakJacobi V (a + b) (c + d) + weakJacobi V (a - b) (c - d) =
      2 * (weakJacobi V a c + weakJacobi V b d) := by
  simp only [sub_eq_add_neg, ← neg_one_smul ℂ b, ← neg_one_smul ℂ d,
    weakJacobi_add_left, weakJacobi_add_right, weakJacobi_smul_left, weakJacobi_smul_right,
    map_neg, map_one]
  ring


lemma slitNeumannReflection_jacobi (k : ℕ) (V : BoundedRealPotential)
    (u v : ComplexH1 × zeroTraceDomain (boundaryArc k 1)) :
    weakJacobi V ((slitNeumannReflectionEquiv k).symm u).val.1
      ((slitNeumannReflectionEquiv k).symm v).val.1 +
    weakJacobi V ((slitNeumannReflectionEquiv k).symm u).val.2
      ((slitNeumannReflectionEquiv k).symm v).val.2 =
      2 * (weakJacobi V u.1 v.1 + weakJacobi V u.2.val v.2.val) :=
  weakJacobi_even_odd V _ _ _ _

lemma slitDirichletReflection_jacobi (k : ℕ) (V : BoundedRealPotential)
    (u v : zeroTraceDomain (boundaryArc k 0) ×
      ↥(zeroTraceDomain (boundaryArc k 0) ⊓ zeroTraceDomain (boundaryArc k 1))) :
    weakJacobi V ((slitDirichletReflectionEquiv k).symm u).val.1
      ((slitDirichletReflectionEquiv k).symm v).val.1 +
    weakJacobi V ((slitDirichletReflectionEquiv k).symm u).val.2
      ((slitDirichletReflectionEquiv k).symm v).val.2 =
      2 * (weakJacobi V u.1.val v.1.val + weakJacobi V u.2.val v.2.val) :=
  weakJacobi_even_odd V _ _ _ _


/-- Membership in any complex subspace is equivalent before and after the
invertible even/odd change of coordinates. -/
lemma even_odd_mem_iff (D : Submodule ℂ ComplexH1) (a b : ComplexH1) :
    a + b ∈ D ∧ a - b ∈ D ↔ a ∈ D ∧ b ∈ D := by
  constructor
  · rintro ⟨hp, hm⟩
    have ha := D.smul_mem (2 : ℂ)⁻¹ (D.add_mem hp hm)
    have hb := D.smul_mem (2 : ℂ)⁻¹ (D.sub_mem hp hm)
    have hea : (2 : ℂ)⁻¹ • ((a + b) + (a - b)) = a := by module
    have heb : (2 : ℂ)⁻¹ • ((a + b) - (a - b)) = b := by module
    exact ⟨hea ▸ ha, heb ▸ hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨D.add_mem ha hb, D.sub_mem ha hb⟩

lemma mem_pairCharacterDomain_iff (θ : ℝ) (c : ℂ) (u : DiskPairH1) :
    u ∈ pairCharacterDomain θ c ↔
      u.1 ∈ weakCharacterDomain θ c ∧ u.2 ∈ weakCharacterDomain θ c := Iff.rfl

lemma slitNeumannReflection_character (k : ℕ) (θ : ℝ) (c : ℂ)
    (v : ComplexH1 × zeroTraceDomain (boundaryArc k 1)) :
    ((slitNeumannReflectionEquiv k).symm v).val ∈ pairCharacterDomain θ c ↔
      v.1 ∈ weakCharacterDomain θ c ∧ v.2.val ∈ weakCharacterDomain θ c := by
  rw [mem_pairCharacterDomain_iff]
  exact even_odd_mem_iff (weakCharacterDomain θ c) v.1 v.2.val

lemma slitDirichletReflection_character (k : ℕ) (θ : ℝ) (c : ℂ)
    (v : zeroTraceDomain (boundaryArc k 0) ×
      ↥(zeroTraceDomain (boundaryArc k 0) ⊓ zeroTraceDomain (boundaryArc k 1))) :
    ((slitDirichletReflectionEquiv k).symm v).val ∈ pairCharacterDomain θ c ↔
      v.1.val ∈ weakCharacterDomain θ c ∧ v.2.val ∈ weakCharacterDomain θ c := by
  rw [mem_pairCharacterDomain_iff]
  exact even_odd_mem_iff (weakCharacterDomain θ c) v.1.val v.2.val

/-- Weighted mass has exactly the same factor two as the Jacobi pairing. -/
lemma weightedMass_even_odd (a b c d : ComplexH1) :
    inner ℂ (weightedDiskValueCLM (a + b)) (weightedDiskValueCLM (c + d)) +
    inner ℂ (weightedDiskValueCLM (a - b)) (weightedDiskValueCLM (c - d)) =
      2 * (inner ℂ (weightedDiskValueCLM a) (weightedDiskValueCLM c) +
        inner ℂ (weightedDiskValueCLM b) (weightedDiskValueCLM d)) := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  ring

end KsIndex.Spectral
