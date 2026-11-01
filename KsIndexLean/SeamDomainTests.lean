module

public import KsIndexLean.PaperJoinedSeamPairing
public import KsIndexLean.SeamDomainWeakGluing
public import KsIndexLean.WeakOpenEquation

@[expose] public section


/-! Compactly supported tests on the actual seam domain discharge the annular
and excluded-sector support conditions in the joined-field identities. -/
noncomputable section
open Set MeasureTheory
open scoped Distributions
namespace KsIndex.Trace

lemma seam_test_zero_of_not_mem {A : Set Circle₁} (hA : IsOpen A)
    (ψ : 𝓓(seamDomain A hA, ℂ)) {z : ℂ} (hz : z ∉ seamDomain A hA) : ψ z = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hz (ψ.tsupport_subset h))

lemma seam_test_inner_zero {A : Set Circle₁} (hA : IsOpen A)
    (ψ : 𝓓(seamDomain A hA, ℂ)) (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) : ψ z = 0 :=
  seam_test_zero_of_not_mem hA ψ (fun h => (not_lt_of_ge hz) h.1.1)

lemma seam_test_outer_zero {A : Set Circle₁} (hA : IsOpen A)
    (ψ : 𝓓(seamDomain A hA, ℂ)) (z : ℂ) (hz : 2 ≤ ‖z‖) : ψ z = 0 :=
  seam_test_zero_of_not_mem hA ψ (fun h => (not_lt_of_ge hz) h.1.2)

lemma seam_test_unmatched_zero {A : Set Circle₁} (hA : IsOpen A)
    (ψ : 𝓓(seamDomain A hA, ℂ)) (w : Circle₁) (hw : w ∉ A) : ψ w = 0 :=
  seam_test_zero_of_not_mem hA ψ (fun h => h.2 ⟨w, hw, rfl⟩)

lemma seam_test_arc0_sector_zero
    (ψ : 𝓓(seamDomain (boundaryArc 3 0) (isOpen_boundaryArc 3 0), ℂ))
    (z : ℂ) (hz : ‖z‖ = 1) (hr : 0 ≤ (z ^ 3).re) : ψ z = 0 := by
  let w : Circle₁ := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
  apply seam_test_unmatched_zero (isOpen_boundaryArc 3 0) ψ w
  intro hw
  have hh := (mem_boundaryArc 3 0 w).mp hw
  have hlt : (z ^ 3).re < 0 := by simpa [w] using hh
  exact (not_lt_of_ge hr) hlt

lemma seam_test_arc1_sector_zero
    (ψ : 𝓓(seamDomain (boundaryArc 3 1) (isOpen_boundaryArc 3 1), ℂ))
    (z : ℂ) (hz : ‖z‖ = 1) (hr : (z ^ 3).re ≤ 0) : ψ z = 0 := by
  let w : Circle₁ := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
  apply seam_test_unmatched_zero (isOpen_boundaryArc 3 1) ψ w
  intro hw
  have hh := (mem_boundaryArc 3 1 w).mp hw
  have hlt : -(z ^ 3).re < 0 := by simpa [w] using hh
  linarith

end KsIndex.Trace
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.PaperSlitAdapter

theorem pair_radical_joined_halves_test {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    (ψ : 𝓓(seamDomain (boundaryArc 3 0) (isOpen_boundaryArc 3 0), ℂ)) :
    joinedHalfResidual u.val.1 u.val.2 (Complex.exp ((2 * Real.pi * α) * Complex.I)) ψ
      innerHalfAnnulus +
    joinedHalfResidual u.val.1 u.val.2 (Complex.exp ((2 * Real.pi * α) * Complex.I)) ψ
      outerHalfAnnulus = 0 :=
  pair_radical_joined_halves u hrad ψ.contDiff
    (seam_test_inner_zero _ ψ) (seam_test_outer_zero _ ψ) (seam_test_arc0_sector_zero ψ)

theorem pair_radical_joined_halves_one_test {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    (ψ : 𝓓(seamDomain (boundaryArc 3 1) (isOpen_boundaryArc 3 1), ℂ)) :
    joinedHalfResidual u.val.1 u.val.2 1 ψ innerHalfAnnulus +
    joinedHalfResidual u.val.1 u.val.2 1 ψ outerHalfAnnulus = 0 :=
  pair_radical_joined_halves_one u hrad ψ.contDiff
    (seam_test_inner_zero _ ψ) (seam_test_outer_zero _ ψ) (seam_test_arc1_sector_zero ψ)

end KsIndex.PaperSlitTransport
