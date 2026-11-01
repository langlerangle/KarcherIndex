module

public import KsIndexLean.KarcherResidues
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section


/-! The actual normalized Karcher denominator and its simple finite root set. -/
open Polynomial
open scoped BigOperators
noncomputable section
namespace KsIndex.KarcherData

def denominatorPoly (k : ℕ) : ℂ[X] := X ^ (2 * k) + 1
def punctureFinset (k : ℕ) : Finset ℂ := (denominatorPoly k).roots.toFinset

lemma denominatorPoly_monic {k : ℕ} (hk : 2 ≤ k) : (denominatorPoly k).Monic := by
  simpa only [denominatorPoly, map_one] using
    (monic_X_pow_add_C (1 : ℂ) (by omega : 2 * k ≠ 0))
lemma denominatorPoly_natDegree (k : ℕ) : (denominatorPoly k).natDegree = 2 * k := by
  simpa only [denominatorPoly, map_one] using
    (natDegree_X_pow_add_C (R := ℂ) (n := 2 * k) (r := 1))
lemma denominatorPoly_eval (k : ℕ) (w : ℂ) :
    (denominatorPoly k).eval w = denominator k w := by
  simp [denominatorPoly, denominator, add_comm]
lemma denominatorPoly_separable {k : ℕ} (hk : 2 ≤ k) :
    (denominatorPoly k).Separable := by
  simpa only [map_neg, map_one, sub_neg_eq_add, denominatorPoly] using
    (separable_X_pow_sub_C (-1 : ℂ)
      (by exact_mod_cast (show 2 * k ≠ 0 by omega)) (by norm_num : (-1 : ℂ) ≠ 0))
lemma denominatorPoly_roots_nodup {k : ℕ} (hk : 2 ≤ k) :
    (denominatorPoly k).roots.Nodup := Polynomial.nodup_roots (denominatorPoly_separable hk)
lemma denominatorPoly_splits (k : ℕ) : (denominatorPoly k).Splits := IsAlgClosed.splits _
lemma mem_punctureFinset {k : ℕ} (hk : 2 ≤ k) {z : ℂ} :
    z ∈ punctureFinset k ↔ z ∈ Surface.punctures k := by
  rw [punctureFinset, Multiset.mem_toFinset,
    mem_roots (denominatorPoly_monic hk).ne_zero]
  change (denominatorPoly k).eval z = 0 ↔ z ^ (2 * k) = -1
  simp [denominatorPoly, eq_neg_iff_add_eq_zero]
lemma punctureFinset_card {k : ℕ} (hk : 2 ≤ k) : (punctureFinset k).card = 2 * k := by
  rw [punctureFinset, Multiset.toFinset_card_of_nodup (denominatorPoly_roots_nodup hk),
    ← (denominatorPoly_splits k).natDegree_eq_card_roots, denominatorPoly_natDegree]
lemma denominatorPoly_factorization {k : ℕ} (hk : 2 ≤ k) :
    denominatorPoly k = ∏ z ∈ punctureFinset k, (X - C z) := by
  classical
  rw [(denominatorPoly_splits k).eq_prod_roots_of_monic (denominatorPoly_monic hk)]
  rw [punctureFinset, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr (denominatorPoly_roots_nodup hk)]
lemma denominatorPoly_eq_nodal {k : ℕ} (hk : 2 ≤ k) :
    denominatorPoly k = Lagrange.nodal (punctureFinset k) id := by
  simpa only [Lagrange.nodal_eq, id_eq] using denominatorPoly_factorization hk
lemma denominatorPoly_derivative_eval (k : ℕ) (z : ℂ) :
    (denominatorPoly k).derivative.eval z = denominatorDeriv k z := by
  simp [denominatorPoly, denominatorDeriv, derivative_pow, mul_comm]
lemma denominatorPoly_rootMultiplicity {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ punctureFinset k) : (denominatorPoly k).rootMultiplicity z = 1 := by
  have hmem : z ∈ (denominatorPoly k).roots := Multiset.mem_toFinset.mp hz
  rw [← count_roots]
  exact Multiset.count_eq_one_of_mem (denominatorPoly_roots_nodup hk) hmem
lemma erased_product_eval_eq_derivative {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ punctureFinset k) :
    (∏ w ∈ (punctureFinset k).erase z, (X - C w)).eval z = denominatorDeriv k z := by
  have he := Lagrange.eval_nodal_derivative_eval_node_eq (v := id) hz
  rw [← denominatorPoly_eq_nodal hk, denominatorPoly_derivative_eval] at he
  simpa only [id_eq, Lagrange.nodal_eq] using he.symm

lemma nodalWeight_eq_inv_denominatorDeriv {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∈ punctureFinset k) :
    Lagrange.nodalWeight (punctureFinset k) id z = (denominatorDeriv k z)⁻¹ := by
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hz,
    ← denominatorPoly_eq_nodal hk, denominatorPoly_derivative_eval]
  rfl

end KsIndex.KarcherData
