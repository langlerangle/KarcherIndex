module

public import KsIndexLean.ReflectionCoreTrace
public import KsIndexLean.TwistTransport
public import KsIndexLean.SlitSeamGauges

@[expose] public section


/-!
# Reflection-germ tests in weak mixed-character domains

Reflection germs on both boundary arcs supply one-sided smooth extensions,
giving `ReflCc k s₁ s₀ ⊆ NatCc k true true`. The associated Sobolev element is
constructed through `naturalCoreH1`. For `k ≥ 1`, its traces agree almost
everywhere with the boundary values on the two arcs.

A smooth odd-reflection germ at a circle point forces its value to vanish:
the inside and outside radial limits through `σ` have opposite signs.
Consequently the sign choices `sgn b₁` and `sgn b₀` give membership in the
corresponding mixed trace domain. Rotation characters are preserved, and
for `k ≥ 2` the weak Jacobi self-pairing equals the original disk form.
-/

open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk

/-- Reflection germs on both arcs give the all-Neumann natural package. -/
lemma reflCc_le_natural_neumann (k : ℕ) (s₁ s₀ : ℂ) :
    KsIndex.TwistSwap.ReflCc k s₁ s₀ ≤ NatCc k true true := by
  intro f hf
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := hf
  refine ⟨h1, ?_, ?_, h4, h5⟩
  · intro w hw
    refine ⟨KsIndex.SingleDisk.refl s₁ f, h2 w hw,
      Filter.Eventually.of_forall fun z hz => ?_⟩
    have hn : ‖z‖ ≤ 1 := (KsIndex.SurfaceForm.mem_disk_iff.mp hz).le
    simp only [KsIndex.SingleDisk.refl, ite_eq_left hn]
  · intro w hw
    refine ⟨KsIndex.SingleDisk.refl s₀ f, h3 w hw,
      Filter.Eventually.of_forall fun z hz => ?_⟩
    have hn : ‖z‖ ≤ 1 := (KsIndex.SurfaceForm.mem_disk_iff.mp hz).le
    simp only [KsIndex.SingleDisk.refl, ite_eq_left hn]

def twistedAsNatural {k : ℕ} {s₁ s₀ : ℂ}
    (f : KsIndex.TwistSwap.ReflCc k s₁ s₀) : NatCc k true true :=
  ⟨f.val, reflCc_le_natural_neumann k s₁ s₀ f.property⟩

def twistedCoreH1 {k : ℕ} (hk : 1 ≤ k) {s₁ s₀ : ℂ}
    (f : KsIndex.TwistSwap.ReflCc k s₁ s₀) : ComplexH1 :=
  naturalCoreH1 hk (twistedAsNatural f)

lemma twistedCoreH1_value_ae {k : ℕ} (hk : 1 ≤ k) {s₁ s₀ : ℂ}
    (f : KsIndex.TwistSwap.ReflCc k s₁ s₀) :
    (valueCLM (twistedCoreH1 hk f) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] f.val :=
  naturalCoreH1_value_ae hk (twistedAsNatural f)

/-- **Odd-germ pointwise vanishing**: a smooth `refl (−1)` germ at a circle
point forces the function to vanish there — the inside and outside radial
limits through σ differ by the sign. -/
lemma odd_germ_vanish {f : ℂ → ℂ} {w : ℂ} (hw : ‖w‖ = 1)
    (hgerm : ContDiffAt ℝ ∞ (KsIndex.SingleDisk.refl (-1) f) w) : f w = 0 := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    norm_num at hw
  have hcont := hgerm.continuousAt
  -- outside approach: F((1+1/(n+1))·w) = −f((1+1/(n+1))⁻¹·w)
  set c : ℕ → ℝ := fun n => 1 + 1 / (n + 1 : ℝ) with hcdef
  have hc1 : ∀ n, 1 < c n := fun n => by
    simp only [hcdef]
    have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith
  have hctend : Tendsto c atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := (tendsto_const_nhds (x := (1 : ℝ))).add h0
    simpa [hcdef] using this
  have hcast : Tendsto (fun n => ((c n : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    have := Complex.continuous_ofReal.continuousAt.tendsto.comp hctend
    simpa [Function.comp_def] using this
  have houtside : Tendsto (fun n => ((c n : ℝ) : ℂ) * w) atTop (𝓝 w) := by
    have := hcast.mul_const w
    simpa using this
  have hF1 : Tendsto (fun n => KsIndex.SingleDisk.refl (-1) f (((c n : ℝ) : ℂ) * w))
      atTop (𝓝 (KsIndex.SingleDisk.refl (-1) f w)) :=
    hcont.tendsto.comp houtside
  have hwconj : w * (starRingEnd ℂ) w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
    norm_num
  have hwinv : ((starRingEnd ℂ) w)⁻¹ = w := by
    rw [← inv_eq_of_mul_eq_one_right hwconj, inv_inv]
  -- each outside term equals −f((cₙ)⁻¹·w), an inside point
  have hval : ∀ n, KsIndex.SingleDisk.refl (-1) f (((c n : ℝ) : ℂ) * w) =
      -f ((((c n : ℝ)⁻¹ : ℝ) : ℂ) * w) := by
    intro n
    have hgt : ¬(‖((c n : ℝ) : ℂ) * w‖ ≤ 1) := by
      rw [norm_mul, hw, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (lt_trans one_pos (hc1 n))]
      exact not_le.mpr (hc1 n)
    have hσ : KsIndex.Bracket.σ (((c n : ℝ) : ℂ) * w) =
        (((c n : ℝ)⁻¹ : ℝ) : ℂ) * w := by
      rw [KsIndex.Bracket.σ_apply, map_mul, Complex.conj_ofReal, one_div,
        mul_inv, hwinv, Complex.ofReal_inv]
    simp only [KsIndex.SingleDisk.refl, hgt, ite_false, hσ, neg_one_mul]
  -- the inside points tend to w from inside; f agrees with F there
  have hcinv : Tendsto (fun n => (c n)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    have := hctend.inv₀ one_ne_zero
    simpa using this
  have hcastinv : Tendsto (fun n => (((c n)⁻¹ : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    have := Complex.continuous_ofReal.continuousAt.tendsto.comp hcinv
    simpa [Function.comp_def] using this
  have hinside : Tendsto (fun n => (((c n)⁻¹ : ℝ) : ℂ) * w) atTop (𝓝 w) := by
    have := hcastinv.mul_const w
    simpa using this
  have hF2 : Tendsto (fun n => KsIndex.SingleDisk.refl (-1) f
      ((((c n)⁻¹ : ℝ) : ℂ) * w)) atTop
      (𝓝 (KsIndex.SingleDisk.refl (-1) f w)) :=
    hcont.tendsto.comp hinside
  have hval2 : ∀ n, KsIndex.SingleDisk.refl (-1) f ((((c n)⁻¹ : ℝ) : ℂ) * w) =
      f ((((c n)⁻¹ : ℝ) : ℂ) * w) := by
    intro n
    have hle : ‖(((c n)⁻¹ : ℝ) : ℂ) * w‖ ≤ 1 := by
      rw [norm_mul, hw, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (lt_trans one_pos (hc1 n)))]
      exact inv_le_one_of_one_le₀ (hc1 n).le
    simp only [KsIndex.SingleDisk.refl, ite_eq_left hle]
  -- combine: F w = −(F w) at the circle value
  have hFw : KsIndex.SingleDisk.refl (-1) f w = f w := by
    simp only [KsIndex.SingleDisk.refl, ite_eq_left hw.le]
  have hlim1 : Tendsto (fun n => -f ((((c n)⁻¹ : ℝ) : ℂ) * w)) atTop
      (𝓝 (f w)) := by
    have h := hF1
    simp only [hval] at h
    rwa [hFw] at h
  have hlim2 : Tendsto (fun n => f ((((c n)⁻¹ : ℝ) : ℂ) * w)) atTop
      (𝓝 (f w)) := by
    have h := hF2
    simp only [hval2] at h
    rwa [hFw] at h
  have h2 : f w = -f w := tendsto_nhds_unique hlim1 hlim2.neg
  have hre : (f w).re = 0 := by
    have h3 := congrArg Complex.re h2
    simp only [Complex.neg_re] at h3
    linarith
  have him : (f w).im = 0 := by
    have h3 := congrArg Complex.im h2
    simp only [Complex.neg_im] at h3
    linarith
  exact Complex.ext (by simpa using hre) (by simpa using him)

/-- The trace on arc 1 is the boundary value (via the `s₁` germ family). -/
lemma twistedCoreH1_arc1_trace {k : ℕ} (hk : 1 ≤ k) {s₁ s₀ : ℂ}
    (f : KsIndex.TwistSwap.ReflCc k s₁ s₀) :
    (diskTraceCLM (twistedCoreH1 hk f) : Circle₁ → ℂ)
      =ᵐ[circleMeasure.restrict (boundaryArc k 1)] (fun w => f.val (w : ℂ)) := by
  have he : (valueCLM (twistedCoreH1 hk f) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] KsIndex.SingleDisk.refl s₁ f.val := by
    filter_upwards [twistedCoreH1_value_ae hk f,
      ae_restrict_mem disk.isOpen.measurableSet] with z hz hzD
    rw [hz, KsIndex.SingleDisk.refl,
      ite_eq_left (KsIndex.SurfaceForm.mem_disk_iff.mp hzD).le]
  have ht := diskTrace_smooth_germs (twistedCoreH1 hk f)
    (A := boundaryArc k 1) (fun w hw => f.property.2.1 w hw) he
  filter_upwards [ht] with w hw
  simpa only [KsIndex.SingleDisk.refl, mem_sphere_zero_iff_norm.mp w.property,
    le_refl, ite_true] using hw

/-- The trace on arc 0 is the boundary value (via the `s₀` germ family). -/
lemma twistedCoreH1_arc0_trace {k : ℕ} (hk : 1 ≤ k) {s₁ s₀ : ℂ}
    (f : KsIndex.TwistSwap.ReflCc k s₁ s₀) :
    (diskTraceCLM (twistedCoreH1 hk f) : Circle₁ → ℂ)
      =ᵐ[circleMeasure.restrict (boundaryArc k 0)] (fun w => f.val (w : ℂ)) := by
  have he : (valueCLM (twistedCoreH1 hk f) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] KsIndex.SingleDisk.refl s₀ f.val := by
    filter_upwards [twistedCoreH1_value_ae hk f,
      ae_restrict_mem disk.isOpen.measurableSet] with z hz hzD
    rw [hz, KsIndex.SingleDisk.refl,
      ite_eq_left (KsIndex.SurfaceForm.mem_disk_iff.mp hzD).le]
  have ht := diskTrace_smooth_germs (twistedCoreH1 hk f)
    (A := boundaryArc k 0) (fun w hw => f.property.2.2.1 w hw) he
  filter_upwards [ht] with w hw
  simpa only [KsIndex.SingleDisk.refl, mem_sphere_zero_iff_norm.mp w.property,
    le_refl, ite_true] using hw

/-- **Sign-flag membership**: at the `sgn` signs, the twisted carrier lands
in the b-flag mixed domain — the `b = false` trace conditions come from the
odd-germ pointwise vanishing. -/
lemma twistedCoreH1_mem_mixed {k : ℕ} (hk : 1 ≤ k) {b₁ b₀ : Bool}
    (f : KsIndex.TwistSwap.ReflCc k (sgn b₁) (sgn b₀)) :
    twistedCoreH1 hk f ∈ mixedTraceDomain k b₁ b₀ := by
  constructor
  · apply (mem_naturalArcDomain k 1 b₁ _).mpr
    intro hb
    filter_upwards [twistedCoreH1_arc1_trace hk f,
      ae_restrict_mem (isOpen_boundaryArc k 1).measurableSet] with w hw hwA
    rw [hw]
    exact odd_germ_vanish (mem_sphere_zero_iff_norm.mp w.property)
      (by simpa only [hb, sgn, Bool.false_eq_true, ite_false]
        using f.property.2.1 (w : ℂ) hwA)
  · apply (mem_naturalArcDomain k 0 b₀ _).mpr
    intro hb
    filter_upwards [twistedCoreH1_arc0_trace hk f,
      ae_restrict_mem (isOpen_boundaryArc k 0).measurableSet] with w hw hwA
    rw [hw]
    exact odd_germ_vanish (mem_sphere_zero_iff_norm.mp w.property)
      (by simpa only [hb, sgn, Bool.false_eq_true, ite_false]
        using f.property.2.2.1 (w : ℂ) hwA)

lemma twistedCoreH1_mem_character {k : ℕ} (hk : 1 ≤ k) {b₁ b₀ : Bool}
    (f : KsIndex.TwistSwap.ReflCc k (sgn b₁) (sgn b₀)) (r : ℕ)
    (hf : f.val ∈ Erot1 k r) :
    twistedCoreH1 hk f ∈ mixedCharacterDomain k r b₁ b₀ :=
  ⟨twistedCoreH1_mem_mixed hk f,
    (naturalCoreH1_mem_character hk (twistedAsNatural f) r hf).2⟩

/-- Complex-linear map from reflection-germ character tests into the
corresponding weak mixed-character domain. -/
def twistedCharacterToMixed {k : ℕ} (hk : 1 ≤ k) (r : ℕ) (b₁ b₀ : Bool) :
    ↥(KsIndex.TwistSwap.ReflCc k (sgn b₁) (sgn b₀) ⊓ Erot1 k r) →ₗ[ℂ]
      mixedCharacterDomain k r b₁ b₀ where
  toFun f := ⟨twistedCoreH1 hk ⟨f.val, f.property.1⟩,
    twistedCoreH1_mem_character hk ⟨f.val, f.property.1⟩ r f.property.2⟩
  map_add' f g := Subtype.ext (naturalCoreH1_add hk
    (twistedAsNatural ⟨f.val, f.property.1⟩)
    (twistedAsNatural ⟨g.val, g.property.1⟩))
  map_smul' c f := Subtype.ext (naturalCoreH1_smul hk c
    (twistedAsNatural ⟨f.val, f.property.1⟩))

/-- The weak Jacobi self-pairing of the reflection-germ carrier equals
the disk Jacobi form of the original test. -/
lemma twistedCoreH1_form {k : ℕ} (hk : 2 ≤ k) {b₁ b₀ : Bool}
    (f : KsIndex.TwistSwap.ReflCc k (sgn b₁) (sgn b₀)) :
    weakJacobi (surfacePotential k) (twistedCoreH1 (by omega) f)
      (twistedCoreH1 (by omega) f) =
      (KsIndex.SingleDiskBridge.Qd k f.val : ℂ) :=
  smooth_weakJacobi_self_eq_Qd hk (naturalCoreData (by omega) (twistedAsNatural f))

end KsIndex.Trace
