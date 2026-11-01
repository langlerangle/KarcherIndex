module

public import KsIndexLean.JacobiExtensionSplitting
public import KsIndexLean.PositiveBlockCounts
public import KsIndexLean.SlitReflectionIndex

@[expose] public section


noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.CircleSobolev KsIndex.DtnBridge KsIndex.NegativeDensity
open KsIndex.Spectral

def dnBoundaryForm {k j : ℕ} (hj0 : 0 < j) (hjk : j < k)
    (f g : dnCharacterSpace k (j : ℤ)) : ℂ :=
  faithfulDtnB k (dnCharacterDotted hj0 hjk f) (dnCharacterDotted hj0 hjk g)

lemma dnBoundaryForm_zero_left {k j : ℕ} (hj0 : 0 < j) (hjk : j < k)
    (f : dnCharacterSpace k (j : ℤ)) : dnBoundaryForm hj0 hjk 0 f = 0 := by
  simp [dnBoundaryForm, faithfulDtnB, dnCharacterDotted, coeff]

lemma dnBoundaryForm_zero_right {k j : ℕ} (hj0 : 0 < j) (hjk : j < k)
    (f : dnCharacterSpace k (j : ℤ)) : dnBoundaryForm hj0 hjk f 0 = 0 := by
  simp [dnBoundaryForm, faithfulDtnB, dnCharacterDotted, coeff]

private lemma weakJacobi_zero_left' (V : BoundedRealPotential) (v : ComplexH1) :
    weakJacobi V 0 v = 0 := by
  simpa only [zero_smul, map_zero, zero_mul] using weakJacobi_smul_left V (0 : ℂ) 0 v

/-- Model z-reduction: the actual DN disk index equals the half-order boundary index. -/
lemma dnJacobi_index_eq_boundary {k j : ℕ} (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    diskWeakIndex (mixedCharacterDomain k j true false) (surfacePotential k) =
      negativeIndex (fun f : dnCharacterSpace k (j : ℤ) => (dnBoundaryForm hj0 hjk f f).re) := by
  let B := dnBoundaryForm hj0 hjk
  let R := fun w : mixedCharacterDomain k j false false => (weakJacobi (surfacePotential k) w w).re
  have hR0 : R 0 = 0 := by simp [R, weakJacobi_zero_left']
  have hRp (w : mixedCharacterDomain k j false false) : 0 ≤ R w := by
    by_cases hw : w = 0
    · rw [hw, hR0]
    · exact (generalDirichlet_character_positive_of_range hk hj0 hjk w hw).le
  have he := negativeIndex_congr (dnJacobiSplit (by omega : 2 ≤ k) hj0 hjk).symm
    (fun p => 2 * Real.pi * (B p.1 p.1).re + R p.2)
    (fun u : mixedCharacterDomain k j true false => (weakJacobi (surfacePotential k) u u).re)
    (by
      intro p
      rw [dnJacobiSplit_symm_form]
      simp [B, R, dnBoundaryForm, Complex.mul_re])
  change negativeIndex (fun u : mixedCharacterDomain k j true false =>
    (weakJacobi (surfacePotential k) u u).re) = _
  rw [he]
  exact (negativeIndex_nonnegative_product
    (fun f : dnCharacterSpace k (j : ℤ) => 2 * Real.pi * (B f f).re) R
    (by simp [B, dnBoundaryForm_zero_left]) hR0 hRp).trans
    (negativeIndex_pos_mul _ _ Real.two_pi_pos)

/-- Model z-reduction for the radical, obtained through the honest splitting. -/
lemma dnJacobi_sesqNullity_eq_boundary {k j : ℕ} (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    sesqNullity (fun u v : mixedCharacterDomain k j true false =>
      weakJacobi (surfacePotential k) u v) = sesqNullity (dnBoundaryForm hj0 hjk) := by
  have he := sesqNullity_congr (dnJacobiSplit (by omega : 2 ≤ k) hj0 hjk).symm
    (fun p q => (2 * Real.pi : ℂ) * dnBoundaryForm hj0 hjk p.1 q.1 +
      weakJacobi (surfacePotential k) p.2.val q.2.val)
    (fun u v : mixedCharacterDomain k j true false => weakJacobi (surfacePotential k) u v)
    (fun p q => dnJacobiSplit_symm_form (by omega) hj0 hjk p q)
  rw [he]
  have hp := sesqNullity_positive_product
    (fun f g : dnCharacterSpace k (j : ℤ) => (2 * Real.pi : ℂ) * dnBoundaryForm hj0 hjk f g)
    (fun u v : mixedCharacterDomain k j false false => weakJacobi (surfacePotential k) u v)
    (fun x => by rw [dnBoundaryForm_zero_right, mul_zero])
    (fun y => weakJacobi_zero_left' _ _)
    (fun y hy => generalDirichlet_character_positive_of_range hk hj0 hjk y hy)
  exact hp.trans (sesqNullity_nonzero_mul _ _ (by exact_mod_cast Real.two_pi_pos.ne'))

/-- The radical supremum agrees with the existing finite-dimensional disk nullity. -/
lemma disk_sesqNullity_eq_weakNullity (D : Submodule ℂ ComplexH1) [CompleteSpace D]
    (V : BoundedRealPotential) :
    sesqNullity (fun u v : D => weakJacobi V u v) = (diskWeakNullity D V : ℕ∞) := by
  let K := @formRadical D inferInstance (diskDomain_innerProductSpace D)
    (domainJacobiForm D V)
  let : FiniteDimensional ℂ K := diskRadical_finiteDimensional D V
  exact sesqNullity_eq_finrank_radical _ K (fun u => by
    exact (mem_formRadical _ u))

lemma dnJacobi_nullity_eq_boundary {k j : ℕ} (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) :
    (diskWeakNullity (mixedCharacterDomain k j true false) (surfacePotential k) : ℕ∞) =
      sesqNullity (dnBoundaryForm hj0 hjk) := by
  let : CompleteSpace (mixedCharacterDomain k j true false) :=
    (isClosed_mixedCharacterDomain k j true false).completeSpace_coe
  rw [← disk_sesqNullity_eq_weakNullity]
  exact dnJacobi_sesqNullity_eq_boundary hk hj0 hjk

end KsIndex.Trace
