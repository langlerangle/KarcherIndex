module

public import KsIndexLean.OuterRadialCauchyUniqueness
public import KsIndexLean.InteriorModeCompatibility
public import KsIndexLean.PuncturedModeLinearity

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

lemma eigenDiskClassicalDerivative_nested {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    EqOn (eigenDiskClassicalDerivative hab k lam u n)
      (eigenDiskClassicalDerivative hcd k lam u n) (Icc c d) := by
  have hc := ha.trans_le hac
  have hd := hdb.trans hb
  have he := interiorDiskMode_nested ha hab hb hac hcd hdb u n
  have hi : EqOn (eigenDiskClassicalDerivative hab k lam u n)
      (eigenDiskClassicalDerivative hcd k lam u n) (Ioo c d) := by
    intro r hr
    have hro : r ∈ Ioo a b := ⟨hac.trans_lt hr.1, hr.2.trans_le hdb⟩
    have ho := eigenDiskMode_hasDerivAt ha hab hb k lam u n hu hro
    have hn := eigenDiskMode_hasDerivAt hc hcd hd k lam u n hu hr
    have heq : interiorDiskMode hcd u n =ᶠ[nhds r] interiorDiskMode hab u n := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
      exact (he (Ioo_subset_Icc_self ht)).symm
    exact (ho.congr_of_eventuallyEq heq).unique hn
  apply eqOn_Icc_of_ae_eq hcd
    ((eigenDiskClassicalDerivative_continuousOn ha hab hb k lam u n).mono
      (Icc_subset_Icc hac hdb))
    (eigenDiskClassicalDerivative_continuousOn hc hcd hd k lam u n)
  exact ae_restrict_of_forall_mem measurableSet_Ioo hi

lemma eigenDiskClassicalDerivative_overlap {a b c d r : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (hc : 0 < c) (hcd : c < d) (hd : d ≤ 1) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (hr : r ∈ Icc a b) (hr' : r ∈ Icc c d) :
    eigenDiskClassicalDerivative hab k lam u n r = eigenDiskClassicalDerivative hcd k lam u n r := by
  have hmin : 0 < min a c := lt_min ha hc
  have hspan : min a c < max b d := (min_le_left a c).trans_lt (hab.trans_le (le_max_left b d))
  have hmax : max b d ≤ 1 := max_le hb hd
  exact (eigenDiskClassicalDerivative_nested hmin hspan hmax (min_le_left a c) hab
    (le_max_left b d) k lam u n hu hr).symm.trans
    (eigenDiskClassicalDerivative_nested hmin hspan hmax (min_le_right a c) hcd
      (le_max_right b d) k lam u n hu hr')


/-- Canonical outer-boundary flux coefficient, defined using the fixed collar. -/
def eigenDiskNormalMode (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ) : ℂ :=
  eigenDiskFluxRepresentative (by norm_num : (1 / 2 : ℝ) < 1) k lam u n 1

lemma eigenDiskFluxRepresentative_one {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    eigenDiskFluxRepresentative ha1 k lam u n 1 = eigenDiskNormalMode k lam u n := by
  have h := eigenDiskClassicalDerivative_overlap ha ha1 le_rfl
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) le_rfl
    k lam u n hu (show (1 : ℝ) ∈ Icc a 1 from ⟨ha1.le, le_rfl⟩)
    (by norm_num : (1 : ℝ) ∈ Icc (1 / 2) 1)
  simpa [eigenDiskClassicalDerivative, eigenDiskNormalMode] using h

/-- Full-circle zero Cauchy data force a weak spherical eigenfunction to vanish.
This does not assert that mixed boundary conditions supply these data. -/
theorem sphericalEigen_eq_zero_of_boundary_cauchy (k : ℕ) (lam : ℝ) (u : ComplexH1)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (ht : diskTraceCLM u = 0) (hn : ∀ n : ℤ, eigenDiskNormalMode k lam u n = 0) :
    u = 0 := by
  apply complexH1_eq_of_punctured_modes
  intro n r hr
  have ha : 0 < r / 2 := half_pos hr.1
  have hab : r / 2 < 1 := by linarith [hr.2]
  have hend : (1 : ℝ) ∈ Icc (r / 2) 1 := ⟨hab.le, le_rfl⟩
  have hf : interiorDiskMode hab u n 1 = 0 := by
    rw [← puncturedDiskMode_eq_interior ha hab le_rfl u n hend, puncturedDiskMode_one, ht]
    rw [← circleFourierEquiv_apply]
    simp
  have hg : eigenDiskFluxRepresentative hab k lam u n 1 = 0 :=
    (eigenDiskFluxRepresentative_one ha hab k lam u n hu).trans (hn n)
  have hz := sphericalEigen_mode_zero_of_outer_cauchy ha hab le_rfl k lam u n hu hf hg
    r (show r ∈ Icc (r / 2) 1 from ⟨by linarith [hr.1], hr.2⟩)
  rw [puncturedDiskMode_zero n hr,
    puncturedDiskMode_eq_interior ha hab le_rfl u n ⟨by linarith [hr.1], hr.2⟩]
  exact hz.1

end KsIndex.Trace
