module

public import KsIndexLean.NodeCSymbol
public import KsIndexLean.SingleArcDNEquivalence
public import KsIndexLean.JacobiExtensionCounts

@[expose] public section


noncomputable section
namespace KsIndex.SingleArcReindex
open KsIndex.Trace KsIndex.CircleSobolev KsIndex.ModeWitness KsIndex.DtNCircle

/-- The nonzero lattice, for the nontrivial characters in the paper. -/
def latticeNZ {k j : ℕ} (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) (n : ℤ) : NZ :=
  ⟨lz k j n, lz_ne_zero hk hj0 (by omega) n⟩

lemma lattice_symbol {k j : ℕ} (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k) (n : ℤ) :
    dtnSymbol k (latticeNZ hk hj0 hjk n) =
      (k : ℝ) * NodeC.sigma k (1-(j : ℝ)/k) n := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have he : (lz k j n : ℝ) = (k : ℝ) * ((n : ℝ)+(1-(j : ℝ)/k)) := by
    simp only [lz, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_sub,
      Nat.cast_sub (le_of_lt hjk)]
    field_simp
  change (((lz k j n : ℤ) : ℝ)^2 - ((k : ℝ)-1)^2) / |(lz k j n : ℝ)| = _
  rw [he, abs_mul, abs_of_pos hkp, NodeC.sigma]
  have ha : |(n : ℝ)+(1-(j : ℝ)/k)| ≠ 0 := by
    intro h
    have hz : (lz k j n : ℝ) = 0 := by rw [he, abs_eq_zero.mp h, mul_zero]
    exact (latticeNZ hk hj0 hjk n).property (by exact_mod_cast hz)
  field_simp

/-- Paper-coordinate boundary form, with the same unscaled convention as Node A. -/
def singleArcForm (k j : ℕ) (f g : dnSpace 1) : ℂ :=
  ∑' n : ℤ, (NodeC.sigma k (1-(j : ℝ)/k) n : ℂ) *
    starRingEnd ℂ (coeff (1/2) f.val n) * coeff (1/2) g.val n

/-- Exact reindexing of the unscaled boundary pairing. -/
theorem dnBoundaryForm_eq_singleArc {k j : ℕ} (hk : 3 ≤ k)
    (hj0 : 0 < j) (hjk : j < k) (f g : dnCharacterSpace k j) :
    dnBoundaryForm hj0 hjk f g = (k : ℂ) *
      singleArcForm k j (dnEquiv hk (le_of_lt hjk) f) (dnEquiv hk (le_of_lt hjk) g) := by
  let F : NZ → ℂ := fun m => (dtnSymbol k m : ℂ) *
    starRingEnd ℂ (coeff (1/2) f.val m.val) * coeff (1/2) g.val m.val
  have hi : Function.Injective (latticeNZ hk hj0 hjk) := by
    intro n m h
    exact lz_injective hk (congrArg Subtype.val h)
  have hs : Function.support F ⊆ Set.range (latticeNZ hk hj0 hjk) := by
    intro m hm
    by_contra hn
    have hoff : ¬ ∃ q, m.val = -(j : ℤ) + (k : ℤ)*q := by
      intro h
      obtain ⟨q, hq⟩ := (lattice_range (le_of_lt hjk) m.val).mpr h
      exact hn ⟨q, Subtype.ext hq.symm⟩
    have hz := (mem_character _ _ _ _).mp f.property.2 m.val hoff
    exact hm (by simp [F, hz])
  change (∑' m : NZ, F m) = _
  rw [← hi.tsum_eq hs, singleArcForm, ← tsum_mul_left]
  apply tsum_congr
  intro n
  change (dtnSymbol k (latticeNZ hk hj0 hjk n) : ℂ) *
      starRingEnd ℂ (coeff (1/2) f.val (lz k j n)) * coeff (1/2) g.val (lz k j n) =
    (k : ℂ) * ((NodeC.sigma k (1-(j : ℝ)/k) n : ℂ) *
      starRingEnd ℂ (coeff (1/2) (extract hk j f.val) n) *
      coeff (1/2) (extract hk j g.val) n)
  rw [lattice_symbol hk hj0 hjk, Complex.ofReal_mul, coeff_extract, coeff_extract]
  push_cast
  ring

/-- The paper-coordinate pairing is a convergent series on its actual DN domain. -/
lemma singleArcForm_summable {k j : ℕ} (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k)
    (f g : dnSpace 1) :
    Summable (fun n : ℤ => (NodeC.sigma k (1-(j : ℝ)/k) n : ℂ) *
      starRingEnd ℂ (coeff (1/2) f.val n) * coeff (1/2) g.val n) := by
  have hs := (summable_coefficientDuality (1/2)
    (dtnCLM k (insert hk j f.val)) (insert hk j g.val)).comp_injective
    (lz_injective (r := j) hk)
  have hkn : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have h := hs.mul_left (k : ℂ)⁻¹
  apply h.congr
  intro n
  simp only [Function.comp_apply]
  have hd := coeff_dtnCLM k (insert hk j f.val) (latticeNZ hk hj0 hjk n)
  change coeff (-(1/2)) (dtnCLM k (insert hk j f.val)) (lz k j n) =
    (dtnSymbol k (latticeNZ hk hj0 hjk n) : ℂ) *
      coeff (1/2) (insert hk j f.val) (lz k j n) at hd
  rw [hd, coeff_insert, coeff_insert, insertCoeff_lattice hk, insertCoeff_lattice hk,
    lattice_symbol hk hj0 hjk, Complex.ofReal_mul, map_mul, map_mul,
    Complex.conj_ofReal, Complex.conj_ofReal]
  push_cast
  field_simp

end KsIndex.SingleArcReindex
