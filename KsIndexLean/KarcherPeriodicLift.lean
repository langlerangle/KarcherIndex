module

public import KsIndexLean.KarcherSymmetryRelations

@[expose] public section


/-! The intrinsic real-height lift of a map to the periodic ambient target.
The parameter point is retained; this is not an ambient-image identification. -/
noncomputable section
namespace KsIndex.KarcherData

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Pull back the real height coordinate along the actual quotient-valued map. -/
abbrev HeightLift {P : Type*} (F : P → PeriodTarget) :=
  {q : P × ℝ // (q.2 : AddCircle (2 * Real.pi)) = (F q.1).2.2}

namespace HeightLift
variable {P : Type*} {F : P → PeriodTarget}

def projection (q : HeightLift F) : P := q.val.1

def height (q : HeightLift F) : ℝ := q.val.2

/-- The actual real-valued ambient parametrization of the lifted carrier. -/
def ambient (q : HeightLift F) : AmbientTriple :=
  ((F (projection q)).1, (F (projection q)).2.1, height q)

lemma project_ambient (q : HeightLift F) : projectPeriod (ambient q) = F (projection q) := by
  exact Prod.ext rfl (Prod.ext rfl q.property)

lemma projection_surjective : Function.Surjective (projection (F := F)) := by
  intro p
  obtain ⟨z, _, hz⟩ := AddCircle.eq_coe_Ico (F p).2.2
  exact ⟨⟨(p, z), hz⟩, rfl⟩

lemma coe_integer_period (n : ℤ) :
    (((n : ℝ) * (2 * Real.pi) : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
  apply (AddCircle.coe_eq_zero_iff _).mpr
  exact ⟨n, by rw [zsmul_eq_mul]⟩

/-- Integral vertical translation on the intrinsic lift. -/
def deck (n : ℤ) (q : HeightLift F) : HeightLift F :=
  ⟨(projection q, height q + (n : ℝ) * (2 * Real.pi)), by
    rw [AddCircle.coe_add, coe_integer_period, add_zero]
    exact q.property⟩

@[simp] lemma projection_deck (n : ℤ) (q : HeightLift F) : projection (deck n q) = projection q := rfl
@[simp] lemma height_deck (n : ℤ) (q : HeightLift F) :
    height (deck n q) = height q + (n : ℝ) * (2 * Real.pi) := rfl

@[simp] lemma deck_zero (q : HeightLift F) : deck 0 q = q := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · simp [deck, height]

lemma deck_add (n m : ℤ) (q : HeightLift F) : deck (n + m) q = deck n (deck m q) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change height q + ((n + m : ℤ) : ℝ) * (2 * Real.pi) =
      (height q + (m : ℝ) * (2 * Real.pi)) + (n : ℝ) * (2 * Real.pi)
    push_cast
    ring

lemma ambient_deck (n : ℤ) (q : HeightLift F) :
    ambient (deck n q) = ambient q + (0, 0, (n : ℝ) * (2 * Real.pi)) := by
  ext <;> simp [ambient, height_deck]

/-- No nontrivial integral deck translation fixes a parameter point. -/
lemma deck_free {n : ℤ} {q : HeightLift F} (he : deck n q = q) : n = 0 := by
  have hh := congrArg height he
  rw [height_deck] at hh
  have hn : (n : ℝ) * (2 * Real.pi) = 0 := by linarith
  have hn' : (n : ℝ) = 0 := (mul_eq_zero.mp hn).resolve_right (by positivity)
  exact_mod_cast hn'

/-- All lifts of the same parameter point differ by an integral period. -/
theorem same_projection_iff (q r : HeightLift F) :
    projection q = projection r ↔ ∃ n : ℤ, deck n q = r := by
  constructor
  · intro hp
    have he : (height r : AddCircle (2 * Real.pi)) = (height q : AddCircle (2 * Real.pi)) := by
      change (r.val.2 : AddCircle (2 * Real.pi)) = q.val.2
      rw [r.property, q.property]
      exact congrArg (fun p => (F p).2.2) hp.symm
    have hz : (((height r - height q : ℝ)) : AddCircle (2 * Real.pi)) = 0 := by
      rw [AddCircle.coe_sub, he, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).mp hz
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hp
    · change height q + (n : ℝ) * (2 * Real.pi) = height r
      rw [zsmul_eq_mul] at hn
      linarith
  · rintro ⟨n, rfl⟩
    rfl

/-- Equivalence by translation through multiples of m full periods. -/
def periodSetoid (m : ℕ) : Setoid (HeightLift F) where
  r q r := ∃ n : ℤ, deck (n * (m : ℤ)) q = r
  iseqv := {
    refl := fun q => ⟨0, by simp⟩
    symm := by
      rintro q r ⟨n, rfl⟩
      refine ⟨-n, ?_⟩
      rw [← deck_add, neg_mul, neg_add_cancel, deck_zero]
    trans := by
      rintro q r s ⟨n, rfl⟩ ⟨l, rfl⟩
      exact ⟨l + n, by rw [add_mul, deck_add]⟩ }

/-- The intrinsic m-period quotient. Positive m is used for the paper's surfaces. -/
def PeriodQuotient (F : P → PeriodTarget) (m : ℕ) := Quotient (periodSetoid (F := F) m)

def quotientProjection (m : ℕ) : PeriodQuotient F m → P :=
  Quotient.lift projection (by
    rintro q r ⟨n, rfl⟩
    rfl)

lemma quotientProjection_surjective (m : ℕ) :
    Function.Surjective (quotientProjection (F := F) m) := by
  intro p
  obtain ⟨q, hq⟩ := projection_surjective (F := F) p
  exact ⟨Quotient.mk _ q, hq⟩

/-- The full-period quotient has exactly the original parameter points as its fibers.
This is a set equivalence; the covering topology is a separate construction. -/
def onePeriodEquiv : PeriodQuotient F 1 ≃ P :=
  Equiv.ofBijective (quotientProjection 1) ⟨by
    intro q r
    induction q using Quotient.inductionOn with | h q =>
      induction r using Quotient.inductionOn with | h r =>
        intro he
        obtain ⟨n, hn⟩ := (same_projection_iff q r).mp he
        apply Quotient.sound
        exact ⟨n, by simpa only [Nat.cast_one, mul_one] using hn⟩,
    quotientProjection_surjective 1⟩

section Topology
variable [TopologicalSpace P]

lemma continuous_projection : Continuous (projection (F := F)) :=
  continuous_fst.comp continuous_subtype_val

lemma continuous_height : Continuous (height (F := F)) :=
  continuous_snd.comp continuous_subtype_val

lemma continuous_ambient (hF : Continuous F) : Continuous (ambient (F := F)) :=
  (hF.fst.comp continuous_projection).prodMk
    ((hF.snd.fst.comp continuous_projection).prodMk continuous_height)

lemma continuous_deck (n : ℤ) : Continuous (deck (F := F) n) :=
  (continuous_projection.prodMk (continuous_height.add continuous_const)).subtype_mk _

/-- Deck translation is a homeomorphism, with negative translation as its inverse. -/
def deckHomeomorph (n : ℤ) : HeightLift F ≃ₜ HeightLift F where
  toFun := deck n
  invFun := deck (-n)
  left_inv q := by rw [← deck_add, neg_add_cancel, deck_zero]
  right_inv q := by rw [← deck_add, add_neg_cancel, deck_zero]
  continuous_toFun := continuous_deck n
  continuous_invFun := continuous_deck (-n)

end Topology
end HeightLift
/-- The intrinsic singly periodic carrier associated to the actual EW integral. -/
abbrev PeriodicEWCarrier {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) (C : PeriodTarget) :=
  HeightLift (extendedEWMap hk b C)

/-- The already-constructed EW extension yields a continuous real ambient map
on its intrinsic height lift. Smooth covering charts remain a separate step. -/
theorem exists_continuous_periodicEWMap {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    ∃ C : PeriodTarget,
      Continuous (HeightLift.ambient (F := extendedEWMap hk b C)) := by
  obtain ⟨C, hC, _⟩ := exists_continuous_extendedEWMap hk b
  exact ⟨C, HeightLift.continuous_ambient hC⟩

end KsIndex.KarcherData
