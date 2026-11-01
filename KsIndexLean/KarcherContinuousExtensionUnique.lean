module

public import KsIndexLean.KarcherGlobalNormal

@[expose] public section


/-! Uniqueness of the continuous extension of the fixed based EW integral.
This is not uniqueness of the normalized covering map among other coverings. -/
noncomputable section
namespace KsIndex.KarcherData

lemma continuous_extendedEWMap_unique {k : ℕ} [h : Fact (2 ≤ k)]
    (b : PuncturedPlane k) {C D : PeriodTarget}
    (hC : Continuous (extendedEWMap h.out b C))
    (hD : Continuous (extendedEWMap h.out b D)) :
    extendedEWMap h.out b C = extendedEWMap h.out b D := by
  apply (denseRange_finiteParameter (k := k)).equalizer hC hD
  funext w
  simp only [Function.comp_apply, extendedEWMap_finite]

lemma continuous_infinity_value_unique {k : ℕ} [h : Fact (2 ≤ k)]
    (b : PuncturedPlane k) {C D : PeriodTarget}
    (hC : Continuous (extendedEWMap h.out b C))
    (hD : Continuous (extendedEWMap h.out b D)) : C = D := by
  have he := congrFun (continuous_extendedEWMap_unique b hC hD) (infinityParameter k)
  simpa only [extendedEWMap_infinity] using he

end KsIndex.KarcherData
