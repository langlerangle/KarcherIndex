module

public import KsIndexLean.KarcherSeamAreaCoverage

@[expose] public section


/-! Local inversion of the area-coordinate law on one open disk copy. -/
noncomputable section
open Set MeasureTheory Topology
namespace KsIndex.KarcherData
open scoped QuotientArea
namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

lemma map_copy_inverse_area (n : ZMod (2*m))
    (C : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hC : Measurable C) (hCi : Set.InjOn C (R.quotientCopyInterior n))
    {D U : Set ℂ} (hU : MeasurableSet U) (hUD : U ⊆ D)
    (hmap : Measure.map C ((R.quotientArea).restrict (R.quotientCopyInterior n)) =
      (ewAreaMeasure k).restrict D)
    (g : ℂ → HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m)
    (hg : AEMeasurable g ((ewAreaMeasure k).restrict U))
    (hs : ∀ z ∈ U, g z ∈ R.quotientCopyInterior n)
    (hc : ∀ z ∈ U, C (g z) = z) :
    Measure.map g ((ewAreaMeasure k).restrict U) = (R.quotientArea).restrict (g '' U) := by
  let ν := (R.quotientArea).restrict (R.quotientCopyInterior n)
  have hm : Measure.map C (ν.restrict (C ⁻¹' U)) = (ewAreaMeasure k).restrict U := by
    rw [← Measure.restrict_map hC hU, hmap, Measure.restrict_restrict hU,
      Set.inter_eq_left.mpr hUD]
  have hg' : AEMeasurable g (Measure.map C (ν.restrict (C ⁻¹' U))) := by rw [hm]; exact hg
  have hp : ∀ᵐ x ∂ν, x ∈ R.quotientCopyInterior n :=
    ae_restrict_mem (R.isOpen_quotientCopyInterior n).measurableSet
  have hi : ∀ x ∈ R.quotientCopyInterior n, C x ∈ U → g (C x) = x := by
    intro x hx hxu
    exact hCi (hs _ hxu) hx (hc _ hxu)
  rw [← hm, AEMeasurable.map_map_of_aemeasurable hg' hC.aemeasurable]
  have hid : Measure.map (g ∘ C) (ν.restrict (C ⁻¹' U)) = ν.restrict (C ⁻¹' U) := by
    calc
      _ = Measure.map id (ν.restrict (C ⁻¹' U)) := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_of_ae hp, ae_restrict_mem (hC hU)] with x hx hxu
        exact hi x hx hxu
      _ = _ := Measure.map_id
  rw [hid, Measure.restrict_restrict (hC hU)]
  congr 1
  ext x
  constructor
  · rintro ⟨hxu, hx⟩
    exact ⟨C x, hxu, hi x hx hxu⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨by change C (g z) ∈ U; rw [hc z hz]; exact hz, hs z hz⟩

lemma diskCoordinate_val_injOn_copy (n : ZMod (2*m)) :
    Set.InjOn (fun x => (R.diskCoordinate x).val.val) (R.quotientCopyInterior n) := by
  intro x hx y hy he
  have hh : R.copyInteriorHomeomorph n ⟨x,hx⟩ = R.copyInteriorHomeomorph n ⟨y,hy⟩ :=
    Subtype.ext he
  exact congrArg Subtype.val ((R.copyInteriorHomeomorph n).injective hh)

end PaperHalfPeriodRealization
end KsIndex.KarcherData
