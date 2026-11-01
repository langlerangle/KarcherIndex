module

public import KsIndexLean.OrderedSpectralCounts

@[expose] public section


/-!
# Spectral threshold comparisons from strict eigenvalue inequalities

A strict pointwise inequality between ordered spectra turns the nonpositive
count of the higher spectrum into a lower bound on the negative count of the
lower spectrum. This module supplies infinite/infinite, finite/finite, and
finite/infinite versions.

For infinite sequences, `strictSpectralCount` and `weakSpectralCount` are
first-crossing indices. The infinite/infinite comparison needs no monotonicity
because it compares those indices directly. Interpreting them as cardinalities
of the full sublevel sets uses the monotonicity lemmas in `OrderedSpectralCounts`.
The finite/finite version compares filtered finite sets with an index inclusion.
The finite/infinite version assumes monotonicity of the infinite sequence to
identify its sublevel set with an initial segment.
-/

noncomputable section
namespace KsIndex.Spectral
open Filter

/-- If `ν n < μ n` for every index, the first index where `μ > L` is at most
the first index where `ν ≥ L`: at the latter index, `μ > ν ≥ L`.
No monotonicity is needed for this first-crossing comparison. When both
sequences are monotone, it also compares the cardinalities of `{μ ≤ L}`
and `{ν < L}`; at level zero these are the nonpositive and negative counts. -/
lemma weakSpectralCount_le_strictSpectralCount_of_lt {ν μ : ℕ → ℝ}
    (hν : Tendsto ν atTop atTop) (hμ : Tendsto μ atTop atTop)
    (h : ∀ n, ν n < μ n) (L : ℝ) :
    weakSpectralCount μ hμ L ≤ strictSpectralCount ν hν L :=
  Nat.find_min' _ (lt_of_le_of_lt (strictSpectralCount_spec ν hν L) (h _))

/-- **Cross transfer (finite/finite).** Higher spectrum `μ` over `Fin a`, lower `ν`
over `Fin b` with the finrank inclusion `a ≤ b`, and a strict per-index gap on `Fin a`.
Then the nonpositive-style count of `μ` is bounded by the strict count of `ν`. Proof:
the index inclusion `Fin a ↪ Fin b` carries `{μ ≤ L}` into `{ν < L}` (via `ν i < μ i ≤ L`)
injectively. No monotonicity needed. -/
lemma finite_weakCount_le_strictCount_of_lt {a b : ℕ}
    (μ : Fin a → ℝ) (ν : Fin b → ℝ) (hab : a ≤ b)
    (hgap : ∀ i : Fin a, ν ⟨i.val, i.isLt.trans_le hab⟩ < μ i) (L : ℝ) :
    (Finset.univ.filter fun j => μ j ≤ L).card ≤
      (Finset.univ.filter fun j => ν j < L).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun i : Fin a => (⟨i.val, i.isLt.trans_le hab⟩ : Fin b)) ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact lt_of_lt_of_le (hgap i) hi
  · intro i _ j _ hij
    simp only [Fin.mk.injEq] at hij
    exact Fin.ext hij

/-- **Cross transfer (finite/infinite).** Higher spectrum `μ` over `Fin a`, lower `ν`
infinite. The strict per-index gap carries `{μ ≤ L}` into `range (strictSpectralCount ν)`
via `i ↦ i.val` (each `ν i < μ i ≤ L`, so `i < strictSpectralCount ν` by
`lt_level_iff_lt_strictSpectralCount`). -/
lemma finite_weakCount_le_infStrictCount_of_lt {a : ℕ}
    (μ : Fin a → ℝ) (ν : ℕ → ℝ) (hν : Tendsto ν atTop atTop) (hνmono : Monotone ν)
    (hgap : ∀ i : Fin a, ν i.val < μ i) (L : ℝ) :
    (Finset.univ.filter fun j => μ j ≤ L).card ≤ strictSpectralCount ν hν L := by
  classical
  have hsub : (Finset.univ.filter fun j : Fin a => μ j ≤ L).card ≤
      (Finset.range (strictSpectralCount ν hν L)).card := by
    refine Finset.card_le_card_of_injOn (fun i : Fin a => i.val) ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range] at hi ⊢
      exact (lt_level_iff_lt_strictSpectralCount ν hν hνmono L i.val).mp
        (lt_of_lt_of_le (hgap i) hi)
    · intro i _ j _ hij
      exact Fin.ext hij
  simpa using hsub

end KsIndex.Spectral
