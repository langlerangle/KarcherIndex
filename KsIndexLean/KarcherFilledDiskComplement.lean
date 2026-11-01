module

public import KsIndexLean.KarcherFilledDiskChain

@[expose] public section


/-! Removing the filled vertices recovers the original punctured disk chain. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [Fact (2 ≤ k)] [NeZero m]

/-- The planar coordinate survives every gluing, including at the vertices. -/
def coordinate : FilledChain k m → ClosedDisk :=
  Quotient.lift Prod.snd (fun _ _ hh => hh.1)

lemma continuous_coordinate : Continuous (coordinate (k := k) (m := m)) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact continuous_snd

/-- The complement of the added endpoint vertices. -/
def regularSet : Set (FilledChain k m) := {q | (coordinate q).val ∉ Surface.punctures k}

lemma regularSet_isOpen : IsOpen (regularSet (k := k) (m := m)) := by
  have hc : IsClosed {q : FilledChain k m | (coordinate q).val ^ (2 * k) = -1} :=
    isClosed_eq ((continuous_subtype_val.comp continuous_coordinate).pow _) continuous_const
  exact hc.isOpen_compl

/-- The original punctured copies are the preimage of the vertex complement. -/
def regularSourceHomeomorph : (ZMod (2 * m) × PuncturedClosedDisk k) ≃ₜ
    ((Quotient.mk (filledSetoid k m)) ⁻¹' regularSet) where
  toFun p := ⟨(p.1, ⟨p.2.val.val, p.2.property⟩), p.2.val.property⟩
  invFun p := (p.val.1, ⟨⟨p.val.2.val, p.property⟩, p.val.2.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The punctured gluing mapped into the filled gluing, away from its vertices. -/
def toRegular : GluedDiskChain k m → regularSet (k := k) (m := m) :=
  Quotient.lift (fun p => ⟨Quotient.mk (filledSetoid k m)
      (p.1, ⟨p.2.val.val, p.2.property⟩), p.2.val.property⟩)
    (by
      intro p q hh
      apply Subtype.ext
      apply Quotient.sound
      rcases p with ⟨i, w⟩
      rcases q with ⟨j, v⟩
      have he := hh.1
      dsimp only at he
      subst v
      exact (filledRel_same _ w.val.property).mpr hh)

lemma toRegular_isQuotientMap : IsQuotientMap (toRegular (k := k) (m := m)) := by
  apply isQuotientMap_quotient_mk'.of_comp_isQuotientMap
  exact (isQuotientMap_quotient_mk'.restrictPreimage_isOpen regularSet_isOpen).comp
    regularSourceHomeomorph.isQuotientMap

lemma toRegular_bijective : Function.Bijective (toRegular (k := k) (m := m)) := by
  constructor
  · intro x y hh
    induction x using Quotient.inductionOn with
    | h p =>
      induction y using Quotient.inductionOn with
      | h q =>
        have he := Quotient.exact (congrArg Subtype.val hh)
        rcases p with ⟨i, w⟩
        rcases q with ⟨j, v⟩
        have hw : w = v := by
          have hv : w.val.val = v.val.val :=
            congrArg (fun z : ClosedDisk => z.val) he.1
          exact Subtype.ext (Subtype.ext hv)
        subst v
        exact Quotient.sound ((filledRel_same _ w.val.property).mp he)
  · rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | h p =>
      exact ⟨Quotient.mk (diskGluingSetoid k m)
        (p.1, ⟨⟨p.2.val, hq⟩, p.2.property⟩), rfl⟩

/-- The compact filling has precisely the original punctured chain as its
open vertex complement, with the original quotient topology. -/
def regularHomeomorph : GluedDiskChain k m ≃ₜ regularSet (k := k) (m := m) where
  toEquiv := Equiv.ofBijective toRegular toRegular_bijective
  continuous_toFun := toRegular_isQuotientMap.continuous
  continuous_invFun := by
    apply toRegular_isQuotientMap.continuous_iff.mpr
    have he : (Equiv.ofBijective toRegular (toRegular_bijective (k := k) (m := m))).symm
        ∘ toRegular = id := by
      funext q
      exact (Equiv.ofBijective toRegular toRegular_bijective).symm_apply_apply q
    change Continuous ((Equiv.ofBijective toRegular
      (toRegular_bijective (k := k) (m := m))).symm ∘ toRegular)
    rw [he]
    exact continuous_id

end KsIndex.KarcherData.DiskCompactification
