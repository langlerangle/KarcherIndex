module

public import KsIndexLean.MixedDirichletUniqueness
public import KsIndexLean.GeneralDirichletPositivity
public import KsIndexLean.ArcTraceRotation

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.FormIndex

lemma cyclicAngle_exp_power {k : ℕ} (hk : 0 < k) :
    Complex.exp (((-(2 * Real.pi) / k : ℝ) : ℂ) * Complex.I) ^ k = 1 := by
  rw [← Complex.exp_nat_mul]
  have he : (k : ℂ) * (((-(2 * Real.pi) / k : ℝ) : ℂ) * Complex.I) =
      -(2 * Real.pi * Complex.I) := by
    push_cast
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp
  rw [he, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

lemma mixedTraceDomain_cyclic_rotation {k : ℕ} (hk : 0 < k) (b1 b0 : Bool)
    (u : ComplexH1) (hu : u ∈ mixedTraceDomain k b1 b0) :
    diskRotation (-(2 * Real.pi) / k) u ∈ mixedTraceDomain k b1 b0 := by
  have hz (n : ℕ) (h : u ∈ zeroTraceDomain (boundaryArc k n)) :
      diskRotation (-(2 * Real.pi) / k) u ∈ zeroTraceDomain (boundaryArc k n) := by
    change arcTrace (boundaryArc k n) u = 0 at h
    change arcTrace _ _ = 0
    rw [arcTrace_rotation _ (measurableSet_boundaryArc k n) _
      (circleRotate_boundaryArc_preimage k n _ (cyclicAngle_exp_power hk)) u, h, map_zero]
  cases b1 <;> cases b0 <;>
    simp only [mixedTraceDomain, naturalArcDomain, Bool.false_eq_true, ite_false, ite_true,
      inf_top_eq, top_inf_eq] at hu ⊢
  · exact ⟨hz 1 hu.1, hz 0 hu.2⟩
  · exact hz 1 hu
  · exact hz 0 hu
  · exact Submodule.mem_top

lemma fullZeroTrace_le_mixed (k : ℕ) (b1 b0 : Bool) :
    zeroTraceDomain Set.univ ≤ mixedTraceDomain k b1 b0 := by
  have h (n : ℕ) : zeroTraceDomain Set.univ ≤ zeroTraceDomain (boundaryArc k n) :=
    zeroTraceDomain_antitone (subset_univ _)
  cases b1 <;> cases b0 <;>
    simp only [mixedTraceDomain, naturalArcDomain, Bool.false_eq_true, ite_false, ite_true,
      inf_top_eq, top_inf_eq]
  · exact le_inf (h 1) (h 0)
  · exact h 1
  · exact h 0
  · exact le_top

/-- Character-restricted mixed tests already exclude a nonzero DD eigenfunction. -/
theorem sphericalEigen_dirichlet_mixed_character_eq_zero {k : ℕ} (hk : 0 < k)
    (j : ℕ) (lam : ℝ) (b : Bool) (u : ComplexH1)
    (ht : u ∈ mixedCharacterDomain k j false false)
    (hm : ∀ v ∈ mixedCharacterDomain k j b (!b), weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) : u = 0 := by
  have hfull := (mixedDD_eq_fullDirichletCharacter hk j ▸ ht)
  have he := sphericalEigen_cyclic_tests_suffice hk j lam (mixedTraceDomain k b (!b))
    (mixedTraceDomain_cyclic_rotation hk b (!b)) u hfull.2 hm
  exact sphericalEigen_dirichlet_mixed_eq_zero hk lam b u hfull.1
    (fun v hv => he v (fullZeroTrace_le_mixed k b (!b) hv)) he

end KsIndex.Trace
