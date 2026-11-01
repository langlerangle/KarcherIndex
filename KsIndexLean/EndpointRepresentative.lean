module

public import KsIndexLean.CircleMeasure
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

@[expose] public section


/-! # Continuous representatives on closed intervals

A function with an interval-integrable weak line derivative has a unique
continuous representative on the closed interval. It is constructed as `c + F`,
where `F` is the primitive of the derivative and `c` is the normalized-bump mean
of `f − F`. A du Bois-Reymond argument identifies this representative with the
original function almost everywhere on the open interval. Endpoint values are
then defined by continuity; disk traces are constructed in separate modules. -/

open MeasureTheory Set TopologicalSpace intervalIntegral
open scoped Distributions Topology ContDiff

noncomputable section

namespace KsIndex.Trace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The open parameter interval as an `Opens ℝ`. -/
def intervalOpens (a b : ℝ) : Opens ℝ := ⟨Ioo a b, isOpen_Ioo⟩

lemma mem_intervalOpens {a b t : ℝ} : t ∈ intervalOpens a b ↔ a < t ∧ t < b := Iff.rfl

section Bump

variable {a b : ℝ}

/-- A fixed bump adapted to the interval. -/
def intervalBump (hab : a < b) : ContDiffBump ((a + b) / 2) where
  rIn := (b - a) / 6
  rOut := (b - a) / 3
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

lemma tsupport_intervalBump (hab : a < b) :
    tsupport (intervalBump hab) ⊆ Ioo a b := by
  rw [(intervalBump hab).tsupport_eq]
  intro t ht
  rw [Metric.mem_closedBall, Real.dist_eq] at ht
  have hro : (intervalBump hab).rOut = (b - a) / 3 := rfl
  rw [hro] at ht
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  constructor <;> linarith

lemma intervalBump_integral_pos (hab : a < b) :
    0 < ∫ t, intervalBump hab t := (intervalBump hab).integral_pos

end Bump

section Primitive

/-- The primitive of a smooth compactly supported real function with zero mean is
itself smooth and compactly supported inside the interval.  The separation step. -/
lemma exists_test_primitive {a b : ℝ} (_hab : a < b) {h : ℝ → ℝ}
    (hsm : ContDiff ℝ ∞ h) (hcs : HasCompactSupport h)
    (hsupp : tsupport h ⊆ Ioo a b) (hzero : (∫ t, h t) = 0) :
    ∃ H : ℝ → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ Ioo a b ∧
      deriv H = h := by
  classical
  by_cases hK : tsupport h = ∅
  · have hh0 : ∀ t, h t = 0 := fun t =>
      image_eq_zero_of_notMem_tsupport (by rw [hK]; exact Set.notMem_empty t)
    refine ⟨0, contDiff_const,
      HasCompactSupport.intro (K := Icc a b) isCompact_Icc (fun t _ => rfl), ?_, ?_⟩
    · have : tsupport (0 : ℝ → ℝ) = ∅ := by
        simp [tsupport, Function.support]
      rw [this]
      exact empty_subset _
    · funext t
      rw [hh0 t]
      simp
  · have hKc : IsCompact (tsupport h) := hcs
    have hKne : (tsupport h).Nonempty := Set.nonempty_iff_ne_empty.mpr hK
    set c := sInf (tsupport h) with hc
    set d := sSup (tsupport h) with hd
    have hcK : c ∈ tsupport h := hKc.sInf_mem hKne
    have hdK : d ∈ tsupport h := hKc.sSup_mem hKne
    have hac : a < c := (hsupp hcK).1
    have hdb : d < b := (hsupp hdK).2
    have hcd : c ≤ d := le_csSup hKc.bddAbove hcK
    have hvan_lt : ∀ t, t < c ∨ d < t → h t = 0 := by
      intro t ht
      apply image_eq_zero_of_notMem_tsupport
      intro htK
      rcases ht with h1 | h1
      · exact absurd (csInf_le hKc.bddBelow htK) (not_le.mpr h1)
      · exact absurd (le_csSup hKc.bddAbove htK) (not_le.mpr h1)
    -- continuity extends the vanishing to the closed half-lines
    have hclosed : IsClosed {t : ℝ | h t = 0} := isClosed_eq hsm.continuous continuous_const
    have hc0 : h c = 0 := by
      have h2 : closure (Iio c) ⊆ {t : ℝ | h t = 0} :=
        hclosed.closure_subset_iff.mpr (fun τ hτ => hvan_lt τ (Or.inl hτ))
      exact h2 (by rw [closure_Iio]; exact mem_Iic.mpr le_rfl)
    have hd0 : h d = 0 := by
      have h2 : closure (Ioi d) ⊆ {t : ℝ | h t = 0} :=
        hclosed.closure_subset_iff.mpr (fun τ hτ => hvan_lt τ (Or.inr hτ))
      exact h2 (by rw [closure_Ioi]; exact mem_Ici.mpr le_rfl)
    have hvan_le : ∀ t ≤ c, h t = 0 := by
      intro t ht
      rcases eq_or_lt_of_le ht with rfl | hlt
      · exact hc0
      · exact hvan_lt t (Or.inl hlt)
    have hvan_ge : ∀ t, d ≤ t → h t = 0 := by
      intro t ht
      rcases eq_or_lt_of_le ht with rfl | hlt
      · exact hd0
      · exact hvan_lt t (Or.inr hlt)
    set H : ℝ → ℝ := fun t => ∫ τ in a..t, h τ with hH
    have hderiv : ∀ t, HasDerivAt H (h t) t := fun t =>
      intervalIntegral.integral_hasDerivAt_right
        (hsm.continuous.intervalIntegrable a t)
        (hsm.continuous.stronglyMeasurableAtFilter volume (𝓝 t))
        hsm.continuous.continuousAt
    have hderiv' : deriv H = h := funext fun t => (hderiv t).deriv
    have hHsm : ContDiff ℝ ∞ H := by
      rw [contDiff_infty_iff_deriv]
      exact ⟨fun t => (hderiv t).differentiableAt, by rw [hderiv']; exact hsm⟩
    have hleft : ∀ t ≤ c, H t = 0 := by
      intro t ht
      change (∫ τ in a..t, h τ) = 0
      have hEq : EqOn h 0 (uIcc a t) := by
        intro τ hτ
        apply hvan_le
        calc τ ≤ max a t := hτ.2
        _ ≤ c := max_le hac.le ht
      rw [intervalIntegral.integral_congr hEq]
      simp
    have hright : ∀ t, d ≤ t → H t = 0 := by
      intro t ht
      change (∫ τ in a..t, h τ) = 0
      rw [intervalIntegral.integral_of_le (by linarith : a ≤ t),
        MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero, hzero]
      intro τ hτ
      rw [Set.mem_Ioc, not_and_or] at hτ
      rcases hτ with h1 | h1
      · exact hvan_le τ (by push Not at h1; linarith)
      · exact hvan_ge τ (by push Not at h1; linarith)
    have hHsupp : Function.support H ⊆ Icc c d := by
      intro t ht
      by_contra hmem
      rw [Set.mem_Icc, not_and_or] at hmem
      apply ht
      rcases hmem with h1 | h1
      · exact hleft t (by push Not at h1; exact h1.le)
      · exact hright t (by push Not at h1; exact h1.le)
    have hHts : tsupport H ⊆ Icc c d :=
      closure_minimal hHsupp isClosed_Icc
    refine ⟨H, hHsm, HasCompactSupport.intro (K := Icc c d) isCompact_Icc
      (fun t ht => ?_), ?_, hderiv'⟩
    · by_contra hne
      exact ht (hHsupp hne)
    · exact hHts.trans (fun τ hτ => ⟨lt_of_lt_of_le hac hτ.1, lt_of_le_of_lt hτ.2 hdb⟩)

end Primitive

section ZeroCore

variable {a b : ℝ}

/-- In dimension one, the line derivative along `1` is the ordinary derivative. -/
lemma lineDeriv_one_eq_deriv (φ : ℝ → ℝ) (x : ℝ) :
    lineDeriv ℝ φ x 1 = deriv φ x := by
  unfold lineDeriv
  simp only [smul_eq_mul, mul_one]
  rw [deriv_comp_const_add]
  simp

/-- The actual Bochner constant: the normalized bump mean. -/
def bumpMean (hab : a < b) (f : ℝ → E) : E :=
  (∫ t, intervalBump hab t)⁻¹ • ∫ t, intervalBump hab t • f t

/-- **du Bois-Reymond**: zero weak line derivative on the interval forces the function
to agree a.e. with its OWN bump mean — an actual constant, not a chosen one. -/
theorem zero_weak_deriv_ae_const (hab : a < b) {f : ℝ → E}
    (hweak : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f 0 1) :
    f =ᵐ[volume.restrict (Ioo a b)] fun _ => bumpMean hab f := by
  classical
  have hLoc : MeasureTheory.LocallyIntegrableOn f (Ioo a b) volume :=
    hweak.locallyIntegrableOn
  -- the bump as a bundled test function
  set χraw : ℝ → ℝ := fun t => intervalBump hab t with hχraw
  have hχsm : ContDiff ℝ ∞ χraw := (intervalBump hab).contDiff
  have hχcs : HasCompactSupport χraw := (intervalBump hab).hasCompactSupport
  have hχsupp : tsupport χraw ⊆ Ioo a b := tsupport_intervalBump hab
  have hχpos : (0 : ℝ) < ∫ t, χraw t := intervalBump_integral_pos hab
  -- integrability of smul pairings against f, for any compactly-supported-in-Ioo weight
  have hpair : ∀ (g : ℝ → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b → MeasureTheory.Integrable (fun t => g t • f t) volume := by
    intro g hg hgc hgs
    exact TauCeti.integrable_smul_of_locallyIntegrableOn hLoc
      (⟨g, hg, hgc, hgs⟩ : 𝓓(intervalOpens a b, ℝ))
  -- the weak-derivative test identity, in deriv form, for any bundled test
  have htest : ∀ (H : ℝ → ℝ) (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H)
      (hHs : tsupport H ⊆ Ioo a b),
      (∫ t, deriv H t • f t) = 0 := by
    intro H hH hHc hHs
    have h1 := hweak.integral_lineDeriv_smul_eq_neg_integral_smul
      (⟨H, hH, hHc, hHs⟩ : 𝓓(intervalOpens a b, ℝ))
    simp only [Pi.zero_apply, smul_zero, MeasureTheory.integral_zero, neg_zero] at h1
    rw [← h1]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    congr 1
    exact (lineDeriv_one_eq_deriv H t).symm
  -- every raw test integrates f - bumpMean to zero
  have hkey : ∀ (g : ℝ → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b →
      (∫ t, g t • (f t - bumpMean hab f)) = 0 := by
    intro g hg hgc hgs
    set lam : ℝ := (∫ t, g t) / (∫ t, χraw t) with hlam
    set h : ℝ → ℝ := fun t => g t - lam * χraw t with hh
    have hhsm : ContDiff ℝ ∞ h := hg.sub (contDiff_const.mul hχsm)
    have hhcs : HasCompactSupport h := hgc.sub (hχcs.mul_left)
    have hhsupp : tsupport h ⊆ Ioo a b := by
      have h1 : Function.support h ⊆ tsupport g ∪ tsupport χraw := by
        intro t ht
        by_contra hn
        rw [Set.mem_union, not_or] at hn
        apply ht
        change g t - lam * χraw t = 0
        rw [image_eq_zero_of_notMem_tsupport hn.1,
          image_eq_zero_of_notMem_tsupport hn.2]
        ring
      refine (closure_minimal h1 (IsClosed.union isClosed_closure isClosed_closure)).trans ?_
      exact Set.union_subset hgs hχsupp
    have hhzero : (∫ t, h t) = 0 := by
      rw [hh]
      rw [MeasureTheory.integral_sub (hg.continuous.integrable_of_hasCompactSupport hgc)
        ((hχsm.continuous.integrable_of_hasCompactSupport hχcs).const_mul lam)]
      rw [MeasureTheory.integral_const_mul, hlam,
        div_mul_cancel₀ _ hχpos.ne', sub_self]
    obtain ⟨H, hHsm, hHcs, hHsupp, hHderiv⟩ :=
      exists_test_primitive hab hhsm hhcs hhsupp hhzero
    have h0 := htest H hHsm hHcs hHsupp
    rw [hHderiv] at h0
    -- ∫ h • f = 0, so ∫ g • f = lam • ∫ χ • f
    have hsplit : (∫ t, h t • f t) =
        (∫ t, g t • f t) - lam • ∫ t, χraw t • f t := by
      have hgint := hpair g hg hgc hgs
      have hχint := hpair χraw hχsm hχcs hχsupp
      rw [hh]
      have : (fun t => (g t - lam * χraw t) • f t) =
          fun t => g t • f t - lam • (χraw t • f t) := by
        funext t
        rw [sub_smul, smul_smul]
      have hχint' : MeasureTheory.Integrable (fun t => lam • (χraw t • f t)) volume :=
        hχint.smul lam
      rw [this, MeasureTheory.integral_sub hgint hχint', MeasureTheory.integral_smul]
    rw [h0] at hsplit
    -- and ∫ g • const(bumpMean) is the same quantity
    have hgconst : (∫ t, g t • bumpMean hab f) = lam • ∫ t, χraw t • f t := by
      rw [_root_.integral_smul_const, bumpMean, smul_smul, hlam]
      rfl
    have hgint := hpair g hg hgc hgs
    have hgcint : MeasureTheory.Integrable (fun t => g t • bumpMean hab f) volume := by
      apply MeasureTheory.Integrable.smul_const
      exact hg.continuous.integrable_of_hasCompactSupport hgc
    rw [show (fun t => g t • (f t - bumpMean hab f)) =
        fun t => g t • f t - g t • bumpMean hab f from
      funext fun t => smul_sub _ _ _]
    rw [MeasureTheory.integral_sub hgint hgcint, hgconst]
    exact hsplit.symm
  -- the anchor closes it on the open interval
  have hLoc' : MeasureTheory.LocallyIntegrableOn
      (fun t => f t - bumpMean hab f) (Ioo a b) volume :=
    hLoc.sub ((continuous_const : Continuous fun _ : ℝ =>
      bumpMean hab f).locallyIntegrable.locallyIntegrableOn _)
  have hzero := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hLoc' hkey
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hzero] with t ht htI
  exact sub_eq_zero.mp (ht htI)

end ZeroCore

section PrimitiveBridge

variable {a b : ℝ}

/-- The explicit primitive of `g` based at the left endpoint `a`. -/
def primitiveFun (a : ℝ) (g : ℝ → E) : ℝ → E := fun t => ∫ τ in a..t, g τ

omit [CompleteSpace E] in
/-- The primitive of an interval-integrable function is continuous on the closed
interval — the Bochner-measurability obligation for `F`, discharged not assumed. -/
lemma primitiveFun_continuousOn (hab : a ≤ b) {g : ℝ → E}
    (hg : IntervalIntegrable g volume a b) :
    ContinuousOn (primitiveFun a g) (Icc a b) := by
  have h := intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
  rwa [uIcc_of_le hab] at h

/-- FTC against a test on a half-line: `∫_{[τ,∞)} deriv φ = −φ τ` for a smooth
compactly supported `φ` living inside `Ioo a b`.  The classical half of the
test/Fubini route. -/
lemma integral_Ici_deriv {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b) (τ : ℝ) :
    ∫ t in Ici τ, deriv φ t = -φ τ := by
  obtain ⟨hφdiff, hφdsm⟩ := contDiff_infty_iff_deriv.mp hφ
  have hcont : Continuous (deriv φ) := hφdsm.continuous
  have hint : MeasureTheory.Integrable (deriv φ) volume :=
    hcont.integrable_of_hasCompactSupport hφc.deriv
  have hzero : ∀ t, b ≤ t → deriv φ t = 0 := by
    intro t ht
    by_contra h
    exact absurd (hφs (support_deriv_subset (Function.mem_support.mpr h))).2
      (not_lt.mpr ht)
  have hφzero : ∀ t, b ≤ t → φ t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport (fun hmem => absurd (hφs hmem).2 (not_lt.mpr ht))
  set R : ℝ := max τ b with hR
  have hdisj : Disjoint (Ioc τ R) (Ioi R) := by
    rw [Set.disjoint_left]
    rintro x ⟨_, hxR⟩ hx
    exact absurd hx (not_lt.mpr hxR)
  have hsplit : Ioi τ = Ioc τ R ∪ Ioi R := (Ioc_union_Ioi_eq_Ioi (le_max_left τ b)).symm
  have h2 : ∫ t in Ioi R, deriv φ t = 0 := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t (ht : t ∈ Ioi R) => hzero t ((le_max_right τ b).trans (le_of_lt ht)))]
    simp
  have h3 : ∫ t in Ioc τ R, deriv φ t = φ R - φ τ := by
    rw [← intervalIntegral.integral_of_le (le_max_left τ b)]
    exact intervalIntegral.integral_deriv_eq_sub (fun x _ => hφdiff x)
      (hcont.intervalIntegrable τ R)
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi, hsplit,
    MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hint.integrableOn
      hint.integrableOn,
    h2, h3, hφzero R (le_max_right τ b), add_zero, zero_sub]

/-- **The primitive bridge**: `F t = ∫ a..t g` has weak line derivative `g` on the
open interval for MERELY interval-integrable `g` — the direct test/Fubini route
(the classical FTC does not apply to integrable-only `g`).  With weak subtraction
this reduces the general representative to the du Bois-Reymond zero core. -/
theorem primitive_weak_deriv (hab : a < b) {g : ℝ → E}
    (hg : IntervalIntegrable g volume a b) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) (primitiveFun a g) g 1 := by
  classical
  have hgIoc : MeasureTheory.IntegrableOn g (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hg
  set g' : ℝ → E := (Ioc a b).indicator g with hg'def
  have hg'int : MeasureTheory.Integrable g' volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Ioc).mpr hgIoc
  have hFloc : MeasureTheory.LocallyIntegrableOn (primitiveFun a g) (Ioo a b) volume :=
    ((primitiveFun_continuousOn hab.le hg).mono Ioo_subset_Icc_self).locallyIntegrableOn
      measurableSet_Ioo
  have hgloc : MeasureTheory.LocallyIntegrableOn g (Ioo a b) volume :=
    (hgIoc.mono_set Ioo_subset_Ioc_self).locallyIntegrableOn
  rw [TauCeti.hasWeakLineDerivOn_iff hFloc hgloc]
  intro φ hφ hφc hφs
  have hφs' : tsupport φ ⊆ Ioo a b := hφs
  obtain ⟨hφdiff, hφdsm⟩ := contDiff_infty_iff_deriv.mp hφ
  have hφdint : MeasureTheory.Integrable (deriv φ) volume :=
    hφdsm.continuous.integrable_of_hasCompactSupport hφc.deriv
  -- the sliced kernel of the triangle {a < τ ≤ t}
  set k : ℝ → ℝ → E := fun t τ => (Ioc a t).indicator (fun σ => deriv φ t • g' σ) τ
    with hkdef
  have hkint : MeasureTheory.Integrable (Function.uncurry k)
      (volume.prod volume) := by
    have hbase : MeasureTheory.Integrable (fun p : ℝ × ℝ => deriv φ p.1 • g' p.2)
        (volume.prod volume) := hφdint.smul_prod hg'int
    have hS : MeasurableSet {p : ℝ × ℝ | a < p.2 ∧ p.2 ≤ p.1} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst)
    have huncurry : Function.uncurry k =
        Set.indicator {p : ℝ × ℝ | a < p.2 ∧ p.2 ≤ p.1}
          (fun p : ℝ × ℝ => deriv φ p.1 • g' p.2) := by
      funext p
      by_cases hp : p.2 ∈ Ioc a p.1
      · simp only [Function.uncurry, hkdef]
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem (by exact hp)]
      · simp only [Function.uncurry, hkdef]
        rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (by exact hp)]
    rw [huncurry]
    exact hbase.indicator hS
  -- inner slice: the τ-integral of the kernel is the sliced primitive
  have hinner : ∀ t : ℝ, (∫ τ, k t τ) = deriv φ t • ∫ τ in Ioc a t, g' τ := by
    intro t
    simp only [hkdef]
    rw [MeasureTheory.integral_indicator measurableSet_Ioc, MeasureTheory.integral_smul]
  -- LHS reduction to the double integral
  have hleft : (∫ x, deriv φ x • primitiveFun a g x) = ∫ t, ∫ τ, k t τ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [hinner t]
    by_cases hd : deriv φ t = 0
    · rw [hd, zero_smul, zero_smul]
    · have htI : t ∈ Ioo a b := hφs' (support_deriv_subset (Function.mem_support.mpr hd))
      congr 1
      rw [primitiveFun, intervalIntegral.integral_of_le htI.1.le]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun τ hτ => ?_)
      obtain ⟨hτ1, hτ2⟩ := Set.mem_Ioc.mp hτ
      exact (Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hτ1, hτ2.trans htI.2.le⟩) g).symm
  -- outer slice: the t-integral of the kernel is the tested derivative
  have houter : ∀ τ : ℝ, (∫ t, k t τ) = -(φ τ • g' τ) := by
    intro τ
    by_cases hτa : a < τ
    · have hkτ : (fun t => k t τ) = (Ici τ).indicator (fun t => deriv φ t • g' τ) := by
        funext t
        by_cases ht : τ ≤ t
        · simp only [hkdef]
          rw [Set.indicator_of_mem (mem_Ici.mpr ht),
            Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hτa, ht⟩)]
        · simp only [hkdef]
          rw [Set.indicator_of_notMem (fun h => ht (mem_Ici.mp h)),
            Set.indicator_of_notMem (fun hmem => ht (Set.mem_Ioc.mp hmem).2)]
      rw [hkτ, MeasureTheory.integral_indicator measurableSet_Ici,
        _root_.integral_smul_const, integral_Ici_deriv hφ hφc hφs' τ, neg_smul]
    · have h1 : (fun t => k t τ) = fun _ => (0 : E) := by
        funext t
        simp only [hkdef]
        exact Set.indicator_of_notMem (fun hmem => hτa (Set.mem_Ioc.mp hmem).1) _
      have h2 : g' τ = 0 :=
        Set.indicator_of_notMem (fun hmem => hτa (Set.mem_Ioc.mp hmem).1) g
      rw [h1, MeasureTheory.integral_zero, h2, smul_zero, neg_zero]
  -- RHS congruence: φ kills everything outside the interval
  have hright : (∫ x, φ x • g x) = ∫ x, φ x • g' x := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ioc a b
    · rw [hg'def, Set.indicator_of_mem hx]
    · rw [image_eq_zero_of_notMem_tsupport
        (fun hmem => hx (Ioo_subset_Ioc_self (hφs' hmem))), zero_smul, zero_smul]
  -- assemble: lineDeriv → deriv, slice, swap, collapse
  have hLD : (∫ x, lineDeriv ℝ φ x 1 • primitiveFun a g x) =
      ∫ x, deriv φ x • primitiveFun a g x := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [lineDeriv_one_eq_deriv]
  calc (∫ x, lineDeriv ℝ φ x 1 • primitiveFun a g x)
      = ∫ x, deriv φ x • primitiveFun a g x := hLD
    _ = ∫ t, ∫ τ, k t τ := hleft
    _ = ∫ τ, ∫ t, k t τ := MeasureTheory.integral_integral_swap hkint
    _ = ∫ τ, -(φ τ • g' τ) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall houter)
    _ = -∫ τ, φ τ • g' τ := MeasureTheory.integral_neg _
    _ = -∫ x, φ x • g x := by rw [hright]

end PrimitiveBridge

section Representative

variable {a b : ℝ}

/-- **The endpoint representative**: the explicit primitive plus the actual Bochner
constant — the normalized-bump mean of `f − F` (NOT of `f` alone, which is correct
only in the zero-derivative core), never a pointwise choice. -/
def representative (hab : a < b) (f g : ℝ → E) : ℝ → E :=
  fun t => bumpMean hab (f - primitiveFun a g) + primitiveFun a g t

omit [CompleteSpace E] in
/-- The representative is continuous up to the closed endpoints. -/
theorem representative_continuousOn (hab : a < b) (f : ℝ → E) {g : ℝ → E}
    (hg : IntervalIntegrable g volume a b) :
    ContinuousOn (representative hab f g) (Icc a b) :=
  continuousOn_const.add (primitiveFun_continuousOn hab.le hg)

/-- **Existence**: the representative agrees with `f` a.e. on the open interval.
Weak subtraction of the primitive bridge reduces to the du Bois-Reymond core. -/
theorem representative_ae_eq (hab : a < b) {f g : ℝ → E}
    (hweak : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b) :
    f =ᵐ[volume.restrict (Ioo a b)] representative hab f g := by
  have hsub : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (f - primitiveFun a g) 0 1 := by
    have h := hweak.sub (primitive_weak_deriv hab hg)
    rwa [sub_self] at h
  have hcore := zero_weak_deriv_ae_const hab hsub
  filter_upwards [hcore] with t ht
  rw [Pi.sub_apply] at ht
  exact eq_add_of_sub_eq ht

omit [CompleteSpace E] in
/-- The FTC identity on the closed interval: differences of the representative are
interval integrals of `g`.  This is where `IntervalIntegrable g` up to the closed
endpoints is genuinely consumed. -/
theorem representative_sub_eq_integral (hab : a < b) (f : ℝ → E) {g : ℝ → E}
    (hg : IntervalIntegrable g volume a b) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    representative hab f g t - representative hab f g s = ∫ τ in s..t, g τ := by
  have hgs : IntervalIntegrable g volume a s :=
    hg.mono_set (uIcc_subset_uIcc left_mem_uIcc (((uIcc_of_le hab.le).symm ▸ hs)))
  have hgt : IntervalIntegrable g volume a t :=
    hg.mono_set (uIcc_subset_uIcc left_mem_uIcc (((uIcc_of_le hab.le).symm ▸ ht)))
  simp only [representative, primitiveFun]
  rw [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left hgt hgs

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- **The uniqueness workhorse**: two functions continuous on the closed interval
that agree a.e. on the open interval agree everywhere on the closed interval —
continuity extends the a.e. equality to the endpoints. -/
theorem eqOn_Icc_of_ae_eq (hab : a < b) {U V : ℝ → E}
    (hU : ContinuousOn U (Icc a b)) (hV : ContinuousOn V (Icc a b))
    (hae : U =ᵐ[volume.restrict (Ioo a b)] V) :
    EqOn U V (Icc a b) := by
  have hnull : volume ({τ : ℝ | ¬U τ = V τ} ∩ Ioo a b) = 0 := by
    have h := MeasureTheory.ae_iff.mp hae
    rwa [MeasureTheory.Measure.restrict_apply' measurableSet_Ioo] at h
  intro t htI
  by_contra hne
  have hcw : ContinuousWithinAt (fun τ => U τ - V τ) (Icc a b) t := (hU.sub hV) t htI
  have hmem : {x : E | x ≠ 0} ∈ 𝓝 (U t - V t) :=
    isOpen_ne.mem_nhds (sub_ne_zero.mpr hne)
  have hev : (fun τ => U τ - V τ) ⁻¹' {x : E | x ≠ 0} ∈ 𝓝[Icc a b] t := hcw hmem
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  set lo : ℝ := max (t - ε) a with hlo
  set hi : ℝ := min (t + ε) b with hhi
  have hlohi : lo < hi := by
    obtain ⟨hta, htb⟩ := htI
    rw [hlo, hhi]
    apply max_lt
    · apply lt_min <;> linarith
    · apply lt_min <;> linarith
  have hsub : Ioo lo hi ⊆ {τ : ℝ | ¬U τ = V τ} ∩ Ioo a b := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := hτ
    have hτIoo : τ ∈ Ioo a b :=
      ⟨lt_of_le_of_lt (le_max_right _ _) h1, lt_of_lt_of_le h2 (min_le_right _ _)⟩
    have hτball : τ ∈ Metric.ball t ε := by
      rw [Real.ball_eq_Ioo]
      exact ⟨lt_of_le_of_lt (le_max_left _ _) h1, lt_of_lt_of_le h2 (min_le_left _ _)⟩
    have hne0 : U τ - V τ ≠ 0 := hball ⟨hτball, Ioo_subset_Icc_self hτIoo⟩
    exact ⟨fun heq => hne0 (sub_eq_zero.mpr heq), hτIoo⟩
  have hpos : (0 : ENNReal) < volume (Ioo lo hi) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hle : volume (Ioo lo hi) = 0 :=
    le_zero_iff.mp (hnull ▸ MeasureTheory.measure_mono hsub)
  exact absurd hle hpos.ne'

/-- **Uniqueness**: any continuous-on-`Icc` function agreeing with `f` a.e. on the
open interval IS the representative, everywhere on the closed interval — in
particular the endpoint values `U a`, `U b` are well-defined functions of the data. -/
theorem representative_unique (hab : a < b) {f g U : ℝ → E}
    (hweak : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b)
    (hU : ContinuousOn U (Icc a b))
    (hUf : U =ᵐ[volume.restrict (Ioo a b)] f) :
    EqOn U (representative hab f g) (Icc a b) :=
  eqOn_Icc_of_ae_eq hab hU (representative_continuousOn hab f hg)
    (hUf.trans (representative_ae_eq hab hweak hg))

/-- Existence of a continuous representative with the integral difference identity.
The interface includes `IntervalIntegrable f`; the proof uses only the local
integrability of `f` supplied by `hweak`. Interval integrability of the derivative
is used to obtain continuity up to both endpoints. -/
theorem exists_continuous_representative (hab : a < b) {f g : ℝ → E}
    (hweak : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (_hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) :
    ∃ U : ℝ → E, ContinuousOn U (Icc a b) ∧
      f =ᵐ[volume.restrict (Ioo a b)] U ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, U t - U s = ∫ τ in s..t, g τ :=
  ⟨representative hab f g, representative_continuousOn hab f hg,
    representative_ae_eq hab hweak hg,
    fun _s hs _t ht => representative_sub_eq_integral hab f hg hs ht⟩

/-- **A.e.-invariance**: the representative (hence each endpoint value) depends only
on the a.e.-classes of the data on the open interval. The derivative-equality
hypothesis `_hgae` is redundant for this proof: continuity and agreement of both
representatives with the same a.e.-class of functions already give equality. -/
theorem representative_congr_ae (hab : a < b) {f f' g g' : ℝ → E}
    (hweak : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b)
    (hweak' : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f' g' 1)
    (hg' : IntervalIntegrable g' volume a b)
    (hf : f =ᵐ[volume.restrict (Ioo a b)] f')
    (_hgae : g =ᵐ[volume.restrict (Ioo a b)] g') :
    EqOn (representative hab f g) (representative hab f' g') (Icc a b) :=
  eqOn_Icc_of_ae_eq hab (representative_continuousOn hab f hg)
    (representative_continuousOn hab f' hg')
    (((representative_ae_eq hab hweak hg).symm.trans hf).trans
      (representative_ae_eq hab hweak' hg'))

/-- Additivity on the closed interval (values outside are unconstrained). -/
theorem representative_add (hab : a < b) {f₁ f₂ g₁ g₂ : ℝ → E}
    (hweak₁ : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f₁ g₁ 1)
    (hg₁ : IntervalIntegrable g₁ volume a b)
    (hweak₂ : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f₂ g₂ 1)
    (hg₂ : IntervalIntegrable g₂ volume a b) :
    EqOn (representative hab (f₁ + f₂) (g₁ + g₂))
      (representative hab f₁ g₁ + representative hab f₂ g₂) (Icc a b) := by
  have h1 := representative_ae_eq hab hweak₁ hg₁
  have h2 := representative_ae_eq hab hweak₂ hg₂
  have hsum := representative_ae_eq hab (hweak₁.add hweak₂) (hg₁.add hg₂)
  refine eqOn_Icc_of_ae_eq hab
    (representative_continuousOn hab (f₁ + f₂) (hg₁.add hg₂))
    ((representative_continuousOn hab f₁ hg₁).add
      (representative_continuousOn hab f₂ hg₂)) ?_
  filter_upwards [h1, h2, hsum] with t ht1 ht2 htsum
  rw [← htsum, Pi.add_apply, Pi.add_apply, ht1, ht2]

/-- Real homogeneity on the closed interval. -/
theorem representative_smul (hab : a < b) (c : ℝ) {f g : ℝ → E}
    (hweak : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b) :
    EqOn (representative hab (c • f) (c • g))
      (c • representative hab f g) (Icc a b) := by
  have h := representative_ae_eq hab hweak hg
  have hsmul := representative_ae_eq hab (hweak.const_smul c) (hg.smul c)
  refine eqOn_Icc_of_ae_eq hab
    (representative_continuousOn hab (c • f) (hg.smul c))
    ((representative_continuousOn hab f hg).const_smul c) ?_
  filter_upwards [h, hsmul] with t ht htsmul
  rw [← htsmul, Pi.smul_apply, Pi.smul_apply, ht]

section ComplexScalars

variable [NormedSpace ℂ E] [SMulCommClass ℝ ℂ E]

/-- Complex scalars pass through the weak-derivative hypothesis (the compatible
scalar structures are the explicit instance hypotheses of this section). -/
theorem weak_deriv_const_smul_complex (z : ℂ) {f g : ℝ → E}
    (hweak : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) (z • f) (z • g) 1 := by
  rw [TauCeti.hasWeakLineDerivOn_iff (hweak.locallyIntegrableOn.smul z)
    (hweak.locallyIntegrableOn_deriv.smul z)]
  intro φ hφ hφc hφs
  have h := (TauCeti.hasWeakLineDerivOn_iff hweak.locallyIntegrableOn
    hweak.locallyIntegrableOn_deriv).mp hweak φ hφ hφc hφs
  calc (∫ x, lineDeriv ℝ φ x 1 • (z • f) x)
      = ∫ x, z • (lineDeriv ℝ φ x 1 • f x) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [Pi.smul_apply, smul_comm]
    _ = z • ∫ x, lineDeriv ℝ φ x 1 • f x := MeasureTheory.integral_smul z _
    _ = z • (-∫ x, φ x • g x) := by rw [h]
    _ = -(z • ∫ x, φ x • g x) := smul_neg z _
    _ = -∫ x, z • (φ x • g x) := by rw [MeasureTheory.integral_smul]
    _ = -∫ x, φ x • (z • g) x := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [Pi.smul_apply, smul_comm]

/-- Complex homogeneity on the closed interval, under the explicit compatible
scalar-structure hypotheses. -/
theorem representative_smul_complex (hab : a < b) (z : ℂ) {f g : ℝ → E}
    (hweak : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b) :
    EqOn (representative hab (z • f) (z • g))
      (z • representative hab f g) (Icc a b) := by
  have h := representative_ae_eq hab hweak hg
  have hsmul := representative_ae_eq hab (weak_deriv_const_smul_complex z hweak)
    (hg.smul z)
  refine eqOn_Icc_of_ae_eq hab
    (representative_continuousOn hab (z • f) (hg.smul z))
    ((representative_continuousOn hab f hg).const_smul z) ?_
  filter_upwards [h, hsmul] with t ht htsmul
  rw [← htsmul, Pi.smul_apply, Pi.smul_apply, ht]

end ComplexScalars

omit [CompleteSpace E] in
/-- Bound a representative value by another value and the integral of the derivative
norm. This does not bound endpoint values solely in terms of annular L² data. -/
theorem representative_norm_le (hab : a < b) (f : ℝ → E) {g : ℝ → E}
    (hg : IntervalIntegrable g volume a b) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖representative hab f g t‖ ≤
      ‖representative hab f g s‖ + |∫ τ in s..t, ‖g τ‖| := by
  have hftc := representative_sub_eq_integral hab f hg hs ht
  have hsplit : representative hab f g t =
      representative hab f g s + (representative hab f g t - representative hab f g s) := by
    abel
  calc ‖representative hab f g t‖
      = ‖representative hab f g s +
          (representative hab f g t - representative hab f g s)‖ := by rw [← hsplit]
    _ ≤ ‖representative hab f g s‖ +
          ‖representative hab f g t - representative hab f g s‖ := norm_add_le _ _
    _ = ‖representative hab f g s‖ + ‖∫ τ in s..t, g τ‖ := by rw [hftc]
    _ ≤ ‖representative hab f g s‖ + |∫ τ in s..t, ‖g τ‖| :=
        add_le_add le_rfl intervalIntegral.norm_integral_le_abs_integral_norm

end Representative

end KsIndex.Trace
