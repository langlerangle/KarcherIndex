module

public import KsIndexLean.InteriorModeRegularity

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma interiorDiskClassicalDerivative_nested {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) (k : ℕ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v = 0) :
    EqOn (interiorDiskClassicalDerivative hab k u n)
      (interiorDiskClassicalDerivative hcd k u n) (Icc c d) := by
  have hc := ha.trans_le hac
  have hd := hdb.trans hb
  have he := interiorDiskMode_nested ha hab hb hac hcd hdb u n
  have hi : EqOn (interiorDiskClassicalDerivative hab k u n)
      (interiorDiskClassicalDerivative hcd k u n) (Ioo c d) := by
    intro r hr
    have hro : r ∈ Ioo a b := ⟨hac.trans_lt hr.1, hr.2.trans_le hdb⟩
    have ho := interiorDiskMode_hasDerivAt ha hab hb k u n hu hro
    have hn := interiorDiskMode_hasDerivAt hc hcd hd k u n hu hr
    have heq : interiorDiskMode hcd u n =ᶠ[nhds r] interiorDiskMode hab u n := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
      exact (he (Ioo_subset_Icc_self ht)).symm
    exact (ho.congr_of_eventuallyEq heq).unique hn
  apply eqOn_Icc_of_ae_eq hcd
    ((interiorDiskClassicalDerivative_continuousOn ha hab hb k u n).mono
      (Icc_subset_Icc hac hdb))
    (interiorDiskClassicalDerivative_continuousOn hc hcd hd k u n)
  exact ae_restrict_of_forall_mem measurableSet_Ioo hi

lemma interiorDiskMode_overlap {a b c d r : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hc : 0 < c) (hcd : c < d) (hd : d ≤ 1) (u : ComplexH1) (n : ℤ)
    (hr : r ∈ Icc a b) (hr' : r ∈ Icc c d) :
    interiorDiskMode hab u n r = interiorDiskMode hcd u n r := by
  have hmin : 0 < min a c := lt_min ha hc
  have hspan : min a c < max b d := (min_le_left a c).trans_lt (hab.trans_le (le_max_left b d))
  have hmax : max b d ≤ 1 := max_le hb hd
  exact (interiorDiskMode_nested hmin hspan hmax (min_le_left a c) hab
    (le_max_left b d) u n hr).symm.trans
    (interiorDiskMode_nested hmin hspan hmax (min_le_right a c) hcd
      (le_max_right b d) u n hr')

lemma interiorDiskClassicalDerivative_overlap {a b c d r : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hc : 0 < c) (hcd : c < d) (hd : d ≤ 1) (k : ℕ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v = 0)
    (hr : r ∈ Icc a b) (hr' : r ∈ Icc c d) :
    interiorDiskClassicalDerivative hab k u n r = interiorDiskClassicalDerivative hcd k u n r := by
  have hmin : 0 < min a c := lt_min ha hc
  have hspan : min a c < max b d := (min_le_left a c).trans_lt (hab.trans_le (le_max_left b d))
  have hmax : max b d ≤ 1 := max_le hb hd
  exact (interiorDiskClassicalDerivative_nested hmin hspan hmax (min_le_left a c) hab
    (le_max_left b d) k u n hu hr).symm.trans
    (interiorDiskClassicalDerivative_nested hmin hspan hmax (min_le_right a c) hcd
      (le_max_right b d) k u n hu hr')

end KsIndex.Trace
