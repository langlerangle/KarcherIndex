module

public import KsIndexLean.SphericalSignedForms
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma boundaryArc_cover_ae {k : ℕ} (hk : 1 ≤ k) :
    ∀ᵐ w ∂circleMeasure, w ∈ boundaryArc k 0 ∪ boundaryArc k 1 := by
  let S : Set ℂ := ↑(Polynomial.nthRootsFinset (2 * k) (-1 : ℂ))
  have hs : S.Countable := (Finset.finite_toSet _).countable
  have hn := (hs.preimage_circleMap (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)).ae_notMem volume
  change ∀ᵐ w ∂Measure.map circleParam (volume.restrict (Ico 0 (2 * Real.pi))),
    w ∈ boundaryArc k 0 ∪ boundaryArc k 1
  apply (ae_map_iff measurable_circleParam.aemeasurable
    ((measurableSet_boundaryArc k 0).union (measurableSet_boundaryArc k 1))).mpr
  filter_upwards [hn.filter_mono (ae_mono Measure.restrict_le_self)] with t ht
  change circleParam t ∈ boundaryArc k 0 ∪ boundaryArc k 1
  apply (boundaryArc_union k (circleParam t)).mpr
  intro h
  apply ht
  change (circleParam t : ℂ) ∈ Polynomial.nthRootsFinset (2 * k) (-1 : ℂ)
  rw [Polynomial.mem_nthRootsFinset (by omega)]
  have hn : Complex.normSq ((circleParam t : ℂ) ^ k) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow, mem_sphere_zero_iff_norm.mp (circleParam t).property]
    simp
  have he : ((circleParam t : ℂ) ^ k) ^ 2 = -1 := by
    apply Complex.ext <;> simp only [pow_two, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, h]
    · simp only [Complex.normSq_apply, h] at hn
      nlinarith
    · ring
  simpa only [← pow_mul, Nat.mul_comm k 2] using he

lemma arcTrace_eq_iff_ae (A : Set Circle₁) (u v : ComplexH1) :
    arcTrace A u = arcTrace A v ↔
      (diskTraceCLM u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] diskTraceCLM v := by
  constructor
  · intro h
    exact (boundaryRestrict_coe_ae A (diskTraceCLM u)).symm.trans
      ((Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℂ 2 (circleMeasure.restrict A) =>
        (f : Circle₁ → ℂ)) h)).trans (boundaryRestrict_coe_ae A (diskTraceCLM v)))
  · intro h
    apply Lp.ext
    exact (boundaryRestrict_coe_ae A (diskTraceCLM u)).trans
      (h.trans (boundaryRestrict_coe_ae A (diskTraceCLM v)).symm)

lemma full_trace_eq_iff_arcs {k : ℕ} (hk : 1 ≤ k) (u v : ComplexH1) :
    arcTrace Set.univ u = arcTrace Set.univ v ↔
      arcTrace (boundaryArc k 1) u = arcTrace (boundaryArc k 1) v ∧
      arcTrace (boundaryArc k 0) u = arcTrace (boundaryArc k 0) v := by
  simp only [arcTrace_eq_iff_ae, Measure.restrict_univ]
  constructor
  · intro h
    exact ⟨h.filter_mono (ae_mono Measure.restrict_le_self),
      h.filter_mono (ae_mono Measure.restrict_le_self)⟩
  · rintro ⟨h1, h0⟩
    have h1' := (ae_restrict_iff' (measurableSet_boundaryArc k 1)).mp h1
    have h0' := (ae_restrict_iff' (measurableSet_boundaryArc k 0)).mp h0
    filter_upwards [h1', h0', boundaryArc_cover_ae hk] with w hw1 hw0 hw
    exact hw.elim hw0 hw1

lemma slitTraceDomain_one_eq {k : ℕ} (hk : 1 ≤ k) :
    slitTraceDomain k 1 = transmissionDomain Set.univ 1 := by
  ext p
  simp only [mem_slitTraceDomain, mem_transmissionDomain, one_smul]
  exact (full_trace_eq_iff_arcs hk p.1 p.2).symm

end KsIndex.Trace
