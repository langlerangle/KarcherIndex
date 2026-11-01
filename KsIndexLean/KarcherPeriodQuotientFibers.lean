module

public import KsIndexLean.KarcherPeriodQuotientCharts
public import Mathlib.Data.ZMod.Basic

@[expose] public section


/-! Finite fibers of the intrinsic period quotient over its parameter surface. -/
noncomputable section
namespace KsIndex.KarcherData.HeightLift
variable {P : Type*} {F : P → PeriodTarget}

lemma deck_injective_at (q : HeightLift F) :
    Function.Injective (fun n : ℤ => deck n q) := by
  intro n l he
  have hh := congrArg height he
  simp only [height_deck] at hh
  have hn : (n : ℝ) = (l : ℝ) := by nlinarith [Real.pi_pos]
  exact_mod_cast hn

/-- Two integer deck translates have the same m-period class exactly when
 their integer labels are congruent modulo m. -/
lemma periodQuotientMap_deck_eq_iff (m : ℕ) (q : HeightLift F) (n l : ℤ) :
    periodQuotientMap m (deck n q) = periodQuotientMap m (deck l q) ↔
      (n : ZMod m) = (l : ZMod m) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  constructor
  · intro he
    obtain ⟨t, ht⟩ := Quotient.exact he
    have hi : t * (m : ℤ) + n = l :=
      deck_injective_at q (by simpa only [deck_add] using ht)
    exact ⟨t, by nlinarith [hi]⟩
  · rintro ⟨t, ht⟩
    apply Quotient.sound
    refine ⟨t, ?_⟩
    rw [← deck_add]
    have hi : t * (m : ℤ) + n = l := by nlinarith [ht]
    rw [hi]

variable {m : ℕ} [NeZero m]

/-- Choosing one real-height lift labels its quotient fiber by ZMod m. -/
def quotientFiberPoint (q : HeightLift F) (z : ZMod m) :
    {x : PeriodQuotient F m // quotientProjection m x = projection q} :=
  ⟨periodQuotientMap m (deck (z.val : ℤ) q), rfl⟩

lemma quotientFiberPoint_bijective (q : HeightLift F) :
    Function.Bijective (quotientFiberPoint (m := m) q) := by
  constructor
  · intro z w he
    have hx := congrArg Subtype.val he
    change periodQuotientMap m (deck (z.val : ℤ) q) =
      periodQuotientMap m (deck (w.val : ℤ) q) at hx
    have hz := (periodQuotientMap_deck_eq_iff m q _ _).mp hx
    simpa using hz
  · intro x
    obtain ⟨r, hr⟩ := Quotient.exists_rep x.val
    have hp : projection r = projection q := by
      exact (congrArg (quotientProjection (F := F) m) hr).trans x.property
    obtain ⟨n, hn⟩ := (same_projection_iff q r).mp hp.symm
    refine ⟨(n : ZMod m), ?_⟩
    apply Subtype.ext
    change periodQuotientMap m (deck (((n : ZMod m).val : ℕ) : ℤ) q) = x.val
    rw [← hr, ← hn]
    apply (periodQuotientMap_deck_eq_iff m q _ _).mpr
    simp

/-- An equivalence with the actual projection fiber, not merely its labels. -/
def quotientFiberEquiv (q : HeightLift F) :
    ZMod m ≃ {x : PeriodQuotient F m // quotientProjection m x = projection q} :=
  Equiv.ofBijective _ (quotientFiberPoint_bijective q)

lemma card_quotientProjection_fiber (p : P) :
    Nat.card {x : PeriodQuotient F m // quotientProjection m x = p} = m := by
  obtain ⟨q, rfl⟩ := projection_surjective (F := F) p
  rw [← Nat.card_congr (quotientFiberEquiv (m := m) q)]
  simp

end KsIndex.KarcherData.HeightLift
