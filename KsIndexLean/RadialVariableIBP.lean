module

public import KsIndexLean.VariableFunctionalIBP
public import KsIndexLean.EndpointRepresentative

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The actual endpoint representative is absolutely continuous on the closed interval. -/
theorem representative_absolutelyContinuous {a b : ℝ} (hab : a < b) (f : ℝ → E)
    {g : ℝ → E} (hg : IntervalIntegrable g volume a b) :
    AbsolutelyContinuousOnInterval (representative hab f g) a b := by
  apply absolutelyContinuous_of_dist_le
    (banach_primitive_absolutelyContinuous hg (left_mem_uIcc : a ∈ uIcc a b))
  intro x hx y hy
  simp [representative, primitiveFun]

/-- The prescribed weak radial jet differentiates the actual representative a.e. -/
theorem representative_ae_hasDerivAt {a b : ℝ} (hab : a < b) (f : ℝ → E)
    {g : ℝ → E} (hg : IntervalIntegrable g volume a b) :
    ∀ᵐ t, t ∈ uIcc a b → HasDerivAt (representative hab f g) (g t) t := by
  filter_upwards [hg.ae_hasDerivAt_integral] with t ht htI
  exact (ht htI a left_mem_uIcc).const_add (bumpMean hab (f - primitiveFun a g))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Radial integration by parts with a varying functional, using the genuine endpoint trace. -/
theorem weak_radial_variable_ibp {a b : ℝ} (hab : a < b) {f g : ℝ → E}
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b) {L M : ℝ → E →L[ℝ] F}
    (hL : AbsolutelyContinuousOnInterval L a b) (hM : ContinuousOn M (uIcc a b))
    (hd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt L (M t) t) :
    (∫ t in a..b, L t (g t) + M t (f t)) =
      L b (representative hab f g b) - L a (representative hab f g a) := by
  have hrep := representative_absolutelyContinuous hab f hg
  have hi := (intervalIntegrable_clm_apply hL.continuousOn hg).add
    (intervalIntegrable_clm_apply hM hrep.continuousOn.intervalIntegrable)
  rw [← integral_clm_product_rule hL hrep hd (representative_ae_hasDerivAt hab f hg) hi]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp (representative_ae_eq hab hw hg),
    volume.ae_ne b] with t ht htb htI
  rw [uIoc_of_le hab.le] at htI
  rw [ht ⟨htI.1, lt_of_le_of_ne htI.2 htb⟩]

/-- Vanishing endpoint tests remove the boundary contribution in the radial weak identity. -/
theorem weak_radial_variable_ibp_zero {a b : ℝ} (hab : a < b) {f g : ℝ → E}
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b) {L M : ℝ → E →L[ℝ] F}
    (hL : AbsolutelyContinuousOnInterval L a b) (hM : ContinuousOn M (uIcc a b))
    (hd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt L (M t) t) (ha : L a = 0) (hb : L b = 0) :
    (∫ t in a..b, L t (g t) + M t (f t)) = 0 := by
  rw [weak_radial_variable_ibp hab hw hg hL hM hd, ha, hb]
  simp

end KsIndex.Trace
