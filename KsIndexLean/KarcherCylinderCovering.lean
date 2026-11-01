module

public import KsIndexLean.CylinderCoordinates
public import KsIndexLean.KarcherConformalCovering
public import KsIndexLean.KarcherHalfPeriodHomeomorph

@[expose] public section


/-! Logarithmic cylindrical coordinates on the actual EW covering, with the
finite zero and regular infinity removed from its parameter surface. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData
open Cylindrical

abbrev CylindricalPlane (k : ℕ) := {z : NonzeroPlane // z.val ∉ Surface.punctures k}

def cylindricalParameter (k : ℕ) (z : CylindricalPlane k) : ParameterSphere k :=
  finiteParameter ⟨z.val.val, z.property⟩

lemma cylindricalParameter_isEmbedding (k : ℕ) : IsEmbedding (cylindricalParameter k) := by
  have hh : IsEmbedding (fun z : CylindricalPlane k =>
      Spherical.sphereChart z.val.val) :=
    isOpenEmbedding_sphereChart.isEmbedding.comp
      (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
  exact IsEmbedding.subtypeVal.of_comp_iff.mp hh

/-- The finite nonzero part of the parameter surface, with its actual subspace topology. -/
def cylindricalParameterHomeomorph {k : ℕ} (hk : 2 ≤ k) :
    Set.range (cylindricalParameter k) ≃ₜ {p : Cylinder // p ∉ cylinderPunctures k} :=
  (cylindricalParameter_isEmbedding k).toHomeomorph.symm.trans
    (puncturedLogarithmicHomeomorph hk)

/-- The restriction removes exactly the two regular poles. -/
lemma mem_cylindricalParameter_range {k : ℕ} (hk : 2 ≤ k) (p : ParameterSphere k) :
    p ∈ Set.range (cylindricalParameter k) ↔
      p ≠ finiteParameter ⟨0, zero_not_puncture hk⟩ ∧ p ≠ infinityParameter k := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨?_, finiteParameter_ne_infinity _⟩
    intro he
    have hz := (isOpenEmbedding_finiteParameter k).injective he
    exact z.val.property (congrArg Subtype.val hz)
  · rintro ⟨hz, hi⟩
    rcases parameterSphere_cases p with he | ⟨w, rfl⟩
    · exact (hi he).elim
    · have hw : w.val ≠ 0 := by
        intro he
        apply hz
        congr 1
        exact Subtype.ext he
      exact ⟨⟨⟨w.val, hw⟩, w.property⟩, rfl⟩

namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

/-- The actual EW lift with the two pole fibers removed. -/
abbrev CylindricalCarrier :=
  (HeightLift.projection (F := extendedEWMap h.out (reflectionBasepoint k) R.C)) ⁻¹'
    Set.range (cylindricalParameter k)

/-- The logarithmic map on the actual intrinsic EW lift. -/
def cylindricalCover (q : R.CylindricalCarrier) :
    {p : Cylinder // p ∉ cylinderPunctures k} :=
  cylindricalParameterHomeomorph h.out ⟨HeightLift.projection q.val, q.property⟩

/-- The logarithmic coordinate map is a genuine covering of the punctured cylinder. -/
theorem cylindricalCover_isCoveringMap : IsCoveringMap R.cylindricalCover := by
  exact (R.covering.restrictPreimage (Set.range (cylindricalParameter k))).homeomorph_comp
    (cylindricalParameterHomeomorph h.out)

/-- Cylindrical coordinates are unchanged by any integral period translation. -/
lemma cylindricalCover_deck (n : ℤ) (q : R.CylindricalCarrier) :
    R.cylindricalCover ⟨HeightLift.deck n q.val, q.property⟩ = R.cylindricalCover q := rfl

/-- The covering uses the same logarithmic coordinate as the finite EW parameter. -/
lemma cylindricalCover_finite (q : R.CylindricalCarrier) (w : CylindricalPlane k)
    (hq : HeightLift.projection q.val = cylindricalParameter k w) :
    (R.cylindricalCover q).val = logarithmicHomeomorph w.val := by
  have he : (⟨HeightLift.projection q.val, q.property⟩ :
      Set.range (cylindricalParameter k)) =
      (cylindricalParameter_isEmbedding k).toHomeomorph w := Subtype.ext hq
  simp only [cylindricalCover, cylindricalParameterHomeomorph, Homeomorph.trans_apply, he,
    Homeomorph.symm_apply_apply]
  rfl

/-- Removing the half-period center gives a closed half cylinder with exactly
the boundary punctures removed. The underlying disk map is the existing EW map. -/
def halfCylindricalHomeomorph :
    {q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C // (R.diskMap q).val.val ≠ 0} ≃ₜ
      {p : Cylinder // p ∉ cylinderPunctures k ∧ p.1 ≤ 0} := by
  let e := R.diskHomeomorph.subtype (p := fun q => (R.diskMap q).val.val ≠ 0)
    (q := fun w => w.val.val ≠ 0) (fun q => Iff.rfl)
  let d : {w : PuncturedClosedDisk k // w.val.val ≠ 0} ≃ₜ
      {z : NonzeroPlane // z.val ∉ Surface.punctures k ∧ ‖z.val‖ ≤ 1} := {
    toFun := fun w => ⟨⟨w.val.val.val, w.property⟩, w.val.val.property, w.val.property⟩
    invFun := fun z => ⟨⟨⟨z.val.val, z.property.1⟩, z.property.2⟩, z.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact e.trans (d.trans (halfLogarithmicHomeomorph h.out))

end PaperHalfPeriodRealization
end KsIndex.KarcherData
