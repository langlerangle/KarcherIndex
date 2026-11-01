module

public import KsIndexLean.KarcherBasedPeriods
public import Mathlib.Analysis.Convex.PathConnected

@[expose] public section


/-! Continuous partial integrals of certified contour pieces. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Piecewise.Piece

/-- A nondegenerate initial segment, with regularity inherited on its interval. -/
def initialSegment (p : Piece) (t : ℝ) (ha : p.a < t) (hb : t ≤ p.b) : Piece where
  a := p.a
  b := t
  lt := ha
  curve := p.curve
  velocity := p.velocity
  continuous_curve := p.continuous_curve.mono (Icc_subset_Icc le_rfl hb)
  continuous_velocity := p.continuous_velocity.mono (Icc_subset_Icc le_rfl hb)
  derivative s hs := (p.derivative s ⟨hs.1, hs.2.trans hb⟩).mono (Icc_subset_Icc le_rfl hb)

lemma initialSegment_avoids (p : Piece) {z : ℂ} (hz : p.Avoids z)
    (t : ℝ) (ha : p.a < t) (hb : t ≤ p.b) : (p.initialSegment t ha hb).Avoids z :=
  fun s hs => hz s ⟨hs.1, hs.2.trans hb⟩

/-- The actual partial contour integral, including the zero-length initial value. -/
def partialContour (p : Piece) (f : ℂ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in p.a..t, p.velocity s * f (p.curve s)

lemma continuousOn_partialContour (p : Piece) {f : ℂ → ℂ} (hf : p.Integrable f) :
    ContinuousOn (p.partialContour f) (Icc p.a p.b) := by
  change ContinuousOn (fun t => ∫ s in p.a..t, p.velocity s * f (p.curve s)) _
  simpa only [uIcc_of_le p.lt.le] using
    intervalIntegral.continuousOn_primitive_interval' hf Set.left_mem_uIcc

@[simp] lemma partialContour_start (p : Piece) (f : ℂ → ℂ) : p.partialContour f p.a = 0 := by
  simp [partialContour]
lemma partialContour_finish (p : Piece) (f : ℂ → ℂ) : p.partialContour f p.b = p.contour f := rfl

end KsIndex.Piecewise.Piece
namespace KsIndex.KarcherData
open Piecewise

/-- The real partial EW integral of a certified piece. -/
def pieceIntegral (k : ℕ) (p : Piece) (t : ℝ) : AmbientTriple :=
  ((p.partialContour (coeff1 k) t).re,
    (p.partialContour (coeff2 k) t).re, (p.partialContour (coeff3 k) t).re)

lemma continuousOn_pieceIntegral {k : ℕ} (_hk : 2 ≤ k) (p : Piece)
    (hA : ∀ z ∈ Surface.punctures k, p.Avoids z) :
    ContinuousOn (pieceIntegral k p) (Icc p.a p.b) := by
  have hnp : ∀ z ∈ p.image, z ∉ Surface.punctures k := by
    rintro z ⟨t, ht, rfl⟩ hz
    exact hA _ hz t ht rfl
  have h1 := p.integrable_of_continuousOn (fun z hz =>
    (differentiableAt_coeff1 (hnp z hz)).continuousAt.continuousWithinAt)
  have h2 := p.integrable_of_continuousOn (fun z hz =>
    (differentiableAt_coeff2 (hnp z hz)).continuousAt.continuousWithinAt)
  have h3 := p.integrable_of_continuousOn (fun z hz =>
    (differentiableAt_coeff3 (hnp z hz)).continuousAt.continuousWithinAt)
  exact (Complex.continuous_re.comp_continuousOn (p.continuousOn_partialContour h1)).prodMk
    ((Complex.continuous_re.comp_continuousOn (p.continuousOn_partialContour h2)).prodMk
      (Complex.continuous_re.comp_continuousOn (p.continuousOn_partialContour h3)))

/-- Partial integrals agree with the descended EW map all along a piece. -/
theorem descendedIntegral_piece {k : ℕ} (hk : 2 ≤ k) (base : PuncturedPlane k)
    (p : Piece) (hA : ∀ z ∈ Surface.punctures k, p.Avoids z)
    (t : ℝ) (ht : t ∈ Icc p.a p.b) :
    descendedIntegral hk base ⟨p.curve t, fun hz => hA _ hz t ht rfl⟩ =
      descendedIntegral hk base ⟨p.start, fun hz => p.start_ne (hA _ hz) rfl⟩ +
        projectPeriod (pieceIntegral k p t) := by
  rcases ht.1.eq_or_lt with he | he
  · subst t
    simp [pieceIntegral, projectPeriod, Piece.start]
  · let D := Chain.singleton (p.initialSegment t he ht.2)
    have hD : ∀ z ∈ Surface.punctures k, D.Avoids z :=
      fun z hz => Chain.singleton_avoids _ (p.initialSegment_avoids (hA z hz) t he ht.2)
    have hh := descendedIntegral_increment hk base
      (⟨p.start, fun hz => p.start_ne (hA _ hz) rfl⟩ : PuncturedPlane k)
      (⟨p.curve t, fun hz => hA _ hz t ht rfl⟩ : PuncturedPlane k) D rfl rfl hD
    simpa only [quotientIntegral, periodVector, D, Chain.singleton_contour,
      Piece.contour, Piece.initialSegment, pieceIntegral, Piece.partialContour] using hh

/-- Lift an entire certified piece by its actual partial vertical integral,
 starting at a prescribed compatible real height. -/
def pieceLift {k : ℕ} (hk : 2 ≤ k) (base : PuncturedPlane k) (C : PeriodTarget)
    (p : Piece) (hA : ∀ z ∈ Surface.punctures k, p.Avoids z)
    (z : ℝ) (hz : (z : AddCircle (2 * Real.pi)) =
      (descendedIntegral hk base ⟨p.start, fun hz => p.start_ne (hA _ hz) rfl⟩).2.2)
    (t : Icc p.a p.b) : PeriodicEWCarrier hk base C :=
  ⟨(finiteParameter ⟨p.curve t.val, fun hw => hA _ hw t.val t.property rfl⟩,
    z + (pieceIntegral k p t.val).2.2), by
    dsimp only [Prod.fst, Prod.snd]
    erw [extendedEWMap_finite, descendedIntegral_piece hk base p hA t.val t.property]
    change ((z + (pieceIntegral k p t.val).2.2 : ℝ) : AddCircle (2 * Real.pi)) = _
    rw [AddCircle.coe_add, hz]
    rfl⟩

/-- The integrated piece is continuous in the intrinsic lift's existing topology. -/
theorem continuous_pieceLift {k : ℕ} (hk : 2 ≤ k) (base : PuncturedPlane k) (C : PeriodTarget)
    (p : Piece) (hA : ∀ z ∈ Surface.punctures k, p.Avoids z)
    (z : ℝ) (hz : (z : AddCircle (2 * Real.pi)) =
      (descendedIntegral hk base ⟨p.start, fun hz => p.start_ne (hA _ hz) rfl⟩).2.2) :
    Continuous (pieceLift hk base C p hA z hz) := by
  have hc : Continuous (fun t : Icc p.a p.b => p.curve t.val) :=
    p.continuous_curve.comp_continuous continuous_subtype_val (fun t => t.property)
  have hp : Continuous (fun t : Icc p.a p.b =>
      (⟨p.curve t.val, fun hw => hA _ hw t.val t.property rfl⟩ : PuncturedPlane k)) :=
    hc.subtype_mk _
  have hi : Continuous (fun t : Icc p.a p.b => pieceIntegral k p t.val) :=
    (continuousOn_pieceIntegral hk p hA).comp_continuous continuous_subtype_val (fun t => t.property)
  exact (((isOpenEmbedding_finiteParameter k).continuous.comp hp).prodMk
    (continuous_const.add hi.snd.snd)).subtype_mk _

/-- The endpoint height increment is the actual contour integral, not merely
 its residue modulo the period. -/
lemma pieceLift_finish_height {k : ℕ} (hk : 2 ≤ k) (base : PuncturedPlane k) (C : PeriodTarget)
    (p : Piece) (hA : ∀ z ∈ Surface.punctures k, p.Avoids z)
    (z : ℝ) (hz : (z : AddCircle (2 * Real.pi)) =
      (descendedIntegral hk base ⟨p.start, fun hz => p.start_ne (hA _ hz) rfl⟩).2.2) :
    HeightLift.height (pieceLift hk base C p hA z hz ⟨p.b, p.lt.le, le_rfl⟩) =
      z + (p.contour (coeff3 k)).re := rfl

/-- The lifted endpoints of a certified piece are joined by a continuous path. -/
theorem joined_pieceLift_endpoints {k : ℕ} (hk : 2 ≤ k) (base : PuncturedPlane k) (C : PeriodTarget)
    (p : Piece) (hA : ∀ z ∈ Surface.punctures k, p.Avoids z)
    (z : ℝ) (hz : (z : AddCircle (2 * Real.pi)) =
      (descendedIntegral hk base ⟨p.start, fun hz => p.start_ne (hA _ hz) rfl⟩).2.2) :
    Joined (pieceLift hk base C p hA z hz ⟨p.a, le_rfl, p.lt.le⟩)
      (pieceLift hk base C p hA z hz ⟨p.b, p.lt.le, le_rfl⟩) := by
  have hp := (convex_Icc p.a p.b).isPathConnected ⟨p.a, le_rfl, p.lt.le⟩
  exact (hp.joinedIn p.a ⟨le_rfl, p.lt.le⟩ p.b ⟨p.lt.le, le_rfl⟩).joined_subtype.map
    (continuous_pieceLift hk base C p hA z hz)

end KsIndex.KarcherData
