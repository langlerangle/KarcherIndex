module

public import Mathlib

@[expose] public section

/-!
# Intrinsic index and bounded-field nullity of the EW quotients

The definitions specify the based Weierstrass map on the punctured parameter
sphere, its periodic quotients, the Jacobi form on all compactly supported smooth
complex functions, and the space of uniformly bounded smooth complex Jacobi
fields. The coordinate conditions include the regular point at infinity.

For the six-ended family, one realization and one spectrally characterized
threshold serve all positive integer periods, including the resonance case.
-/


noncomputable section
open Set Metric MeasureTheory Topology
open scoped Real
namespace KSPalomar.Intrinsic.Full

/-! ### Carrier -/
/-- The finite punctures: roots of z^(2k) = -1. -/
def punctures (k : ℕ) : Set ℂ := {w | w ^ (2 * k) = -1}
/-- The complex plane with the finite punctures removed. -/
abbrev PuncturedPlane (k : ℕ) := {w : ℂ // w ∉ punctures k}

/-- Euclidean three-space with its standard real inner product. -/
abbrev Ambient := EuclideanSpace ℝ (Fin 3)
/-- The unit sphere in Euclidean three-space. -/
abbrev Sphere := Metric.sphere (0 : Ambient) 1

/-- Inverse stereographic projection from the complex plane to the unit sphere, with 0 at the south pole. -/
def stereoPoint (z : ℂ) : Ambient :=
  WithLp.toLp 2 ![2 * z.re / (1 + ‖z‖ ^ 2), 2 * z.im / (1 + ‖z‖ ^ 2),
    (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2)]

lemma stereoPoint_norm_sq (z : ℂ) : ‖stereoPoint z‖ ^ 2 = 1 := by
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hz : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_three]
  change (2 * z.re / (1 + ‖z‖ ^ 2)) ^ 2 + (2 * z.im / (1 + ‖z‖ ^ 2)) ^ 2 +
    ((‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2)) ^ 2 = 1
  field_simp
  nlinarith [sq_nonneg (‖z‖ ^ 2)]

/-- Inverse stereographic projection, valued in the unit-sphere subtype. -/
def sphereChart (z : ℂ) : Sphere :=
  ⟨stereoPoint z, mem_sphere_zero_iff_norm.mpr (by
    have h := stereoPoint_norm_sq z
    nlinarith [norm_nonneg (stereoPoint z)])⟩

/-- Stereographic coordinate (x + iy)/(1 - z), inverse to sphereChart away from the north pole. -/
def stereoCoord (p : Ambient) : ℂ := Complex.mk (p 0) (p 1) / ((1 - p 2 : ℝ) : ℂ)

lemma stereoCoord_stereoPoint (z : ℂ) : stereoCoord (stereoPoint z) = z := by
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  change Complex.mk (2 * z.re / (1 + ‖z‖ ^ 2)) (2 * z.im / (1 + ‖z‖ ^ 2)) /
    ((1 - (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) = z
  have he : 1 - (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2) = 2 / (1 + ‖z‖ ^ 2) := by field_simp; ring
  have hn : Complex.mk (2 * z.re / (1 + ‖z‖ ^ 2)) (2 * z.im / (1 + ‖z‖ ^ 2)) =
      ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, add_zero] <;> ring
  have hc : ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast div_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hd
  rw [he, hn]; exact mul_div_cancel_left₀ z hc

lemma sphereChart_injective : Function.Injective sphereChart := by
  intro z w h
  have he := congrArg (fun p : Sphere => stereoCoord p.val) h
  simpa only [sphereChart, stereoCoord_stereoPoint] using he

/-- The unit sphere with the finite punctures removed; the north pole remains a regular parameter. -/
def ParameterSphere (k : ℕ) := {p : Sphere // p ∉ sphereChart '' punctures k}

instance (k : ℕ) : TopologicalSpace (ParameterSphere k) :=
  @instTopologicalSpaceSubtype Sphere (fun p => p ∉ sphereChart '' punctures k) inferInstance

/-- Embed a finite nonpunctured complex parameter into the parameter sphere. -/
def finiteParameter {k : ℕ} (w : PuncturedPlane k) : ParameterSphere k :=
  ⟨sphereChart w.val, by
    rintro ⟨z, hz, he⟩
    exact w.property (sphereChart_injective he ▸ hz)⟩

/-! ### Seam reflection -/
/-- Reflection of Euclidean three-space across the horizontal coordinate plane. -/
def reflectAmbient (p : Ambient) : Ambient := WithLp.toLp 2 ![p 0, p 1, -p 2]

lemma reflectAmbient_norm_sq (p : Ambient) : ‖reflectAmbient p‖ ^ 2 = ‖p‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, reflectAmbient]

/-- Equatorial reflection restricted to the unit sphere. -/
def reflectSphere (p : Sphere) : Sphere :=
  ⟨reflectAmbient p.val, mem_sphere_zero_iff_norm.mpr (by
    have h := reflectAmbient_norm_sq p.val
    have hn := mem_sphere_zero_iff_norm.mp p.property
    rw [hn] at h
    nlinarith [norm_nonneg (reflectAmbient p.val)])⟩

lemma reflectSphere_involutive : Function.Involutive reflectSphere := by
  intro p; apply Subtype.ext; ext i; fin_cases i <;> simp [reflectSphere, reflectAmbient]

lemma reflectSphere_eq_of_equator (p : Sphere) (hp : p.val 2 = 0) : reflectSphere p = p := by
  apply Subtype.ext; ext i; fin_cases i <;> simp [reflectSphere, reflectAmbient, hp]

lemma stereoPoint_equator_iff (z : ℂ) : stereoPoint z 2 = 0 ↔ ‖z‖ = 1 := by
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  change (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2) = 0 ↔ ‖z‖ = 1
  rw [div_eq_zero_iff]; simp only [hd, or_false]
  constructor <;> intro h <;> nlinarith [norm_nonneg z]

lemma puncture_norm {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ∈ punctures k) : ‖z‖ = 1 := by
  have hz' : z ^ (2 * k) = -1 := hz
  have h := congrArg norm hz'
  simp only [norm_pow, norm_neg, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hk)))).1 h

lemma reflectSphere_fixes_puncture {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ∈ punctures k) :
    reflectSphere (sphereChart z) = sphereChart z := by
  apply reflectSphere_eq_of_equator
  exact (stereoPoint_equator_iff z).mpr (puncture_norm hk hz)

/-- Equatorial reflection on the punctured parameter sphere; the punctures are fixed. -/
def parameterSeamReflection {k : ℕ} (hk : 2 ≤ k) (p : ParameterSphere k) : ParameterSphere k :=
  ⟨reflectSphere p.val, by
    rintro ⟨z, hz, he⟩
    have hp : sphereChart z = p.val := by
      rw [← reflectSphere_fixes_puncture hk hz, he, reflectSphere_involutive]
    exact p.property ⟨z, hz, hp⟩⟩

/-! ### Period target and the intrinsic height lift -/
/-- The ambient quotient with two real horizontal coordinates and vertical coordinate modulo 2π. -/
abbrev PeriodTarget := ℝ × ℝ × AddCircle (2 * Real.pi)

/-- Negate the vertical circle coordinate while retaining both horizontal coordinates. -/
def reflZ (p : PeriodTarget) : PeriodTarget := (p.1, p.2.1, -p.2.2)

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Pairs of a parameter and a real height lifting the vertical circle coordinate of F. -/
abbrev HeightLift {P : Type*} (F : P → PeriodTarget) :=
  {q : P × ℝ // (q.2 : AddCircle (2 * Real.pi)) = (F q.1).2.2}

namespace HeightLift
variable {P : Type*} {F : P → PeriodTarget}
/-- The parameter retained by a point of the height lift. -/
def projection (q : HeightLift F) : P := q.val.1
/-- The real vertical coordinate of a point of the height lift. -/
def height (q : HeightLift F) : ℝ := q.val.2

lemma coe_integer_period (n : ℤ) :
    (((n : ℝ) * (2 * Real.pi) : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
  apply (AddCircle.coe_eq_zero_iff _).mpr
  exact ⟨n, by rw [zsmul_eq_mul]⟩

/-- The deck transformation adding 2πn to the lifted height and retaining the parameter. -/
def deck (n : ℤ) (q : HeightLift F) : HeightLift F :=
  ⟨(projection q, height q + (n : ℝ) * (2 * Real.pi)), by
    rw [AddCircle.coe_add, coe_integer_period, add_zero]; exact q.property⟩

@[simp] lemma projection_deck (n : ℤ) (q : HeightLift F) : projection (deck n q) = projection q := rfl
@[simp] lemma height_deck (n : ℤ) (q : HeightLift F) :
    height (deck n q) = height q + (n : ℝ) * (2 * Real.pi) := rfl

@[simp] lemma deck_zero (q : HeightLift F) : deck 0 q = q := by
  apply Subtype.ext; apply Prod.ext
  · rfl
  · simp [deck, height]

lemma deck_add (n m : ℤ) (q : HeightLift F) : deck (n + m) q = deck n (deck m q) := by
  apply Subtype.ext; apply Prod.ext
  · rfl
  · change height q + ((n + m : ℤ) : ℝ) * (2 * Real.pi) =
      (height q + (m : ℝ) * (2 * Real.pi)) + (n : ℝ) * (2 * Real.pi)
    push_cast; ring

/-- Identify height lifts differing by an integer multiple of m deck periods. -/
def periodSetoid (m : ℕ) : Setoid (HeightLift F) where
  r q r := ∃ n : ℤ, deck (n * (m : ℤ)) q = r
  iseqv := {
    refl := fun q => ⟨0, by simp⟩
    symm := by
      rintro q r ⟨n, rfl⟩
      refine ⟨-n, ?_⟩
      rw [← deck_add, neg_mul, neg_add_cancel, deck_zero]
    trans := by
      rintro q r s ⟨n, rfl⟩ ⟨l, rfl⟩
      exact ⟨l + n, by rw [add_mul, deck_add]⟩ }

/-- The quotient of the height lift by deck translations through integer multiples of 2πm. -/
def PeriodQuotient (F : P → PeriodTarget) (m : ℕ) := Quotient (periodSetoid (F := F) m)

instance periodQuotientTopology [TopologicalSpace P] (m : ℕ) :
    TopologicalSpace (PeriodQuotient F m) :=
  @instTopologicalSpaceQuotient (HeightLift F) (periodSetoid (F := F) m) inferInstance

end HeightLift

open HeightLift

/-- The Borel measurable space of the period quotient. -/
instance periodQuotientMeasurableSpace {P : Type*} [TopologicalSpace P] {F : P → PeriodTarget}
    (m : ℕ) : MeasurableSpace (HeightLift.PeriodQuotient F m) := borel _

/-! ### Punctured closed disk + EW disk measure -/
/-- The closed unit disk with the finite punctures removed. -/
def PuncturedClosedDisk (k : ℕ) := {w : PuncturedPlane k // ‖w.val‖ ≤ 1}

instance (k : ℕ) : TopologicalSpace (PuncturedClosedDisk k) :=
  @instTopologicalSpaceSubtype (PuncturedPlane k) (fun w => ‖w.val‖ ≤ 1) inferInstance

instance (k : ℕ) : MeasurableSpace (PuncturedClosedDisk k) :=
  @Subtype.instMeasurableSpace (PuncturedPlane k) (fun w => ‖w.val‖ ≤ 1) inferInstance

/-- The EW conformal length factor k (|w|^(2k-2) + 1) / |w^(2k) + 1|. -/
def rho (k : ℕ) (w : ℂ) : ℝ := k * (‖w‖ ^ (2 * k - 2) + 1) / ‖w ^ (2 * k) + 1‖

/-- Planar area weighted by the square of the EW conformal factor. -/
def ewAreaMeasure (k : ℕ) : Measure ℂ :=
  volume.withDensity (fun w => ENNReal.ofReal (rho k w ^ 2))

/-- Pull back the EW area measure to the punctured closed disk by its inclusion. -/
def ewDiskMeasure (k : ℕ) : Measure (PuncturedClosedDisk k) :=
  (ewAreaMeasure k).comap (fun w => w.val.val)

/-! ### A disk section in the height lift -/
/-- A map to the ambient period quotient and an embedded lift of the punctured
closed disk, with prescribed parameter projection, heights in [-π, 0], and
compatibility with reflection across the seam. -/
structure ExposedDiskSection (k : ℕ) (hk : 2 ≤ k) where
  F : ParameterSphere k → PeriodTarget
  baseSection : PuncturedClosedDisk k → HeightLift F
  proj_eq : ∀ w, HeightLift.projection (baseSection w) = finiteParameter w.val
  height_norm : ∀ w, 0 ≤ HeightLift.height (baseSection w) + Real.pi ∧
    HeightLift.height (baseSection w) + Real.pi ≤ Real.pi
  closed_emb : IsClosedEmbedding baseSection
  seam_id : ∀ p, F (parameterSeamReflection hk p) = reflZ (F p)

namespace ExposedDiskSection
variable {k : ℕ} {hk : 2 ≤ k} (S : ExposedDiskSection k hk)

/-- The upper-seam reflected lift: reflect the parameter, negate the height. Well-typed via the seam
identity (`F∘parameterSeamReflection = reflZ∘F`). -/
def upperSeamLift (q : HeightLift S.F) : HeightLift S.F :=
  ⟨(parameterSeamReflection hk (HeightLift.projection q), -(HeightLift.height q)), by
    have h1 : ((HeightLift.height q : ℝ) : AddCircle (2 * Real.pi)) =
        (S.F (HeightLift.projection q)).2.2 := q.property
    rw [S.seam_id (HeightLift.projection q)]
    change ((-(HeightLift.height q) : ℝ) : AddCircle (2 * Real.pi)) =
      -(S.F (HeightLift.projection q)).2.2
    rw [← h1, ← AddCircle.coe_neg]⟩

/-- Even disk copy (`j`-th period translate of the base section). -/
def evenDiskPoint (j : ℤ) (w : PuncturedClosedDisk k) : HeightLift S.F :=
  HeightLift.deck j (S.baseSection w)

/-- Odd disk copy (`j`-th period translate of the seam-reflected base section). -/
def oddDiskPoint (j : ℤ) (w : PuncturedClosedDisk k) : HeightLift S.F :=
  HeightLift.deck j (S.upperSeamLift (S.baseSection w))

/-- The ordered `ZMod (2m)` disk copy, valued directly in the period quotient. -/
def orderedDiskPoint (m : ℕ) (n : ZMod (2 * m)) (w : PuncturedClosedDisk k) :
    HeightLift.PeriodQuotient S.F m :=
  if n.val % 2 = 0 then Quotient.mk _ (S.evenDiskPoint ((n.val / 2 : ℕ) : ℤ) w)
  else Quotient.mk _ (S.oddDiskPoint ((n.val / 2 : ℕ) : ℤ) w)

/-- The quotient area measure: the sum of the 2m ordered-copy pushforwards of the
Enneper-Weierstrass disk area, without division by the number of copies. -/
def quotientArea (m : ℕ) [NeZero m] : Measure (HeightLift.PeriodQuotient S.F m) :=
  haveI : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩
  ∑ n : ZMod (2 * m), Measure.map (fun w => S.orderedDiskPoint m n w) (ewDiskMeasure k)

/-- Every quotient point is represented in at least one of the ordered disk copies. -/
def Covers (m : ℕ) : Prop :=
  Function.Surjective (fun p : ZMod (2 * m) × PuncturedClosedDisk k => S.orderedDiskPoint m p.1 p.2)

/-- A disk coordinate of a quotient point, chosen from an ordered-copy representative
provided by `Covers`. The choice is used in the copywise expressions below. -/
def diskCoordinate (m : ℕ) (hCov : S.Covers m) (q : HeightLift.PeriodQuotient S.F m) :
    PuncturedClosedDisk k :=
  (hCov q).choose.2

end ExposedDiskSection
end KSPalomar.Intrinsic.Full
end


noncomputable section
open MeasureTheory Complex Classical
namespace KSPalomar.Intrinsic.Full

/-- Flat gradient-squared `‖∂_x f‖²+‖∂_y f‖²`. -/
def gradSq (f : ℂ → ℂ) (w : ℂ) : ℝ := ‖fderiv ℝ f w 1‖ ^ 2 + ‖fderiv ℝ f w I‖ ^ 2

/-- Second fundamental form norm `|A_k|`. -/
def absA (k : ℕ) (w : ℂ) : ℝ :=
  2 * Real.sqrt 2 * ((k : ℝ) - 1) / rho k w * (‖w‖ ^ (k - 2) / (‖w‖ ^ (2 * k - 2) + 1))

namespace ExposedDiskSection
variable {k : ℕ} {hk : 2 ≤ k} (S : ExposedDiskSection k hk)

/-- A quotient function pulled back to copy `n`'s disk coordinate (guarded to the punctured closed disk),
i.e. `G ∘ orderedDiskPoint n`, extended by zero outside the punctured closed disk. -/
def pulledBack (m : ℕ) (G : HeightLift.PeriodQuotient S.F m → ℂ) (n : ZMod (2 * m)) (z : ℂ) : ℂ :=
  if hw : z ∉ punctures k ∧ ‖z‖ ≤ 1 then G (S.orderedDiskPoint m n ⟨⟨z, hw.1⟩, hw.2⟩) else 0

/-- The open interior of ordered disk copy `n` (image of `norm < 1`). -/
def quotientCopyInterior (m : ℕ) (n : ZMod (2 * m)) : Set (HeightLift.PeriodQuotient S.F m) :=
  {q | ∃ w : PuncturedClosedDisk k, ‖w.val.val‖ < 1 ∧ S.orderedDiskPoint m n w = q}

/-- Assemble copywise real densities over the open copies, evaluating at the disk coordinate; zero on seams. -/
def assembleCopyDensity (m : ℕ) [NeZero m] (hCov : S.Covers m) (d : ZMod (2 * m) → ℂ → ℝ)
    (q : HeightLift.PeriodQuotient S.F m) : ℝ :=
  haveI : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩
  ∑ n : ZMod (2 * m), (S.quotientCopyInterior m n).indicator
    (fun x => d n (S.diskCoordinate m hCov x).val.val) q

/-- Inverse-metric gradient density `ρ⁻²·|∇(G∘chart)|²`, assembled over the copies. -/
def quotientGradSq (m : ℕ) [NeZero m] (hCov : S.Covers m)
    (G : HeightLift.PeriodQuotient S.F m → ℂ) (q : HeightLift.PeriodQuotient S.F m) : ℝ :=
  S.assembleCopyDensity m hCov (fun n z => (rho k z ^ 2)⁻¹ * gradSq (S.pulledBack m G n) z) q

/-- Second fundamental norm in the common disk coordinate. -/
def quotientAbsA (m : ℕ) [NeZero m] (hCov : S.Covers m) (q : HeightLift.PeriodQuotient S.F m) : ℝ :=
  absA k (S.diskCoordinate m hCov q).val.val

/-- The signed geometric Jacobi form integrated against the quotient area:
`∫ (|∇G|²_g − |A|²|G|²) dA_g`. -/
def quotientJacobiQ (m : ℕ) [NeZero m] (hCov : S.Covers m)
    (G : HeightLift.PeriodQuotient S.F m → ℂ) : ℝ :=
  ∫ q, (S.quotientGradSq m hCov G q - (S.quotientAbsA m hCov q) ^ 2 * ‖G q‖ ^ 2) ∂(S.quotientArea m)

end ExposedDiskSection
end KSPalomar.Intrinsic.Full
end


noncomputable section
open Complex MeasureTheory
open scoped ContDiff Manifold
namespace KSPalomar.Intrinsic.Full

/-! ### Variational form index (general, over `ι → ℂ`) -/
variable {ι : Type*}

/-- `Q`-negative-definite subspaces of `D`. -/
def NegOn (Q : (ι → ℂ) → ℝ) (D V : Submodule ℂ (ι → ℂ)) : Prop :=
  V ≤ D ∧ ∀ u ∈ V, u ≠ 0 → Q u < 0

/-- The Morse index of `Q` on `D`: sup of `finrank` over finite-dim `Q`-negative subspaces. -/
def formIndex (Q : (ι → ℂ) → ℝ) (D : Submodule ℂ (ι → ℂ)) : ℕ∞ :=
  ⨆ (V : Submodule ℂ (ι → ℂ)) (_ : NegOn Q D V) (_ : FiniteDimensional ℂ V),
    (Module.finrank ℂ V : ℕ∞)

/-! ### Flat Laplacian and its conformal rescaling (Surface) -/
/-- The flat real two-dimensional Laplacian of a complex-valued function, in directions 1 and I. -/
def laplacian (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  fderiv ℝ (fun z => fderiv ℝ f z 1) w 1 + fderiv ℝ (fun z => fderiv ℝ f z I) w I

/-- The flat Laplacian divided by the square of the EW conformal factor. -/
def laplacianG (k : ℕ) (f : ℂ → ℂ) (w : ℂ) : ℂ := ((rho k w ^ 2)⁻¹ : ℝ) * laplacian f w

lemma two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  simpa using (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

lemma laplacian_add {f g : ℂ → ℂ} {w : ℂ} (hf : ContDiffAt ℝ ∞ f w) (hg : ContDiffAt ℝ ∞ g w) :
    laplacian (f + g) w = laplacian f w + laplacian g w := by
  have hf2 : ContDiffAt ℝ 2 f w := hf.of_le two_le_infty
  have hg2 : ContDiffAt ℝ 2 g w := hg.of_le two_le_infty
  have h1 : ∀ v : ℂ, (fun z => fderiv ℝ (f + g) z v)
      =ᶠ[nhds w] (fun z => fderiv ℝ f z v) + (fun z => fderiv ℝ g z v) := by
    intro v
    filter_upwards [hf2.eventually (by simp), hg2.eventually (by simp)] with z hfz hgz
    rw [fderiv_add (hfz.differentiableAt (by norm_num)) (hgz.differentiableAt (by norm_num))]
    rfl
  have hdf : ∀ v : ℂ, DifferentiableAt ℝ (fun z => fderiv ℝ f z v) w := fun v =>
    ((hf.fderiv_right (m := 1)
      (by simpa using (WithTop.coe_le_coe.mpr (le_top : (1 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
        contDiffAt_const).differentiableAt one_ne_zero
  have hdg : ∀ v : ℂ, DifferentiableAt ℝ (fun z => fderiv ℝ g z v) w := fun v =>
    ((hg.fderiv_right (m := 1)
      (by simpa using (WithTop.coe_le_coe.mpr (le_top : (1 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
        contDiffAt_const).differentiableAt one_ne_zero
  simp only [laplacian]
  rw [(h1 1).fderiv_eq, (h1 I).fderiv_eq, fderiv_add (hdf 1) (hdg 1), fderiv_add (hdf I) (hdg I)]
  simp only [add_apply]
  ring

lemma laplacian_smul (c : ℂ) {f : ℂ → ℂ} {w : ℂ} (hf : ContDiffAt ℝ ∞ f w) :
    laplacian (c • f) w = c * laplacian f w := by
  have hf2 : ContDiffAt ℝ 2 f w := hf.of_le two_le_infty
  have h1 : ∀ v : ℂ, (fun z => fderiv ℝ (c • f) z v)
      =ᶠ[nhds w] fun z => c * fderiv ℝ f z v := by
    intro v
    filter_upwards [hf2.eventually (by simp)] with z hfz
    rw [fderiv_const_smul (hfz.differentiableAt (by norm_num))]
    rfl
  have hdf : ∀ v : ℂ, DifferentiableAt ℝ (fun z => fderiv ℝ f z v) w := fun v =>
    ((hf.fderiv_right (m := 1)
      (by simpa using (WithTop.coe_le_coe.mpr (le_top : (1 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
        contDiffAt_const).differentiableAt one_ne_zero
  simp only [laplacian]
  rw [(h1 1).fderiv_eq, (h1 I).fderiv_eq, fderiv_const_mul (hdf 1),
    fderiv_const_mul (hdf I)]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

namespace ExposedDiskSection
variable {k : ℕ} {hk : 2 ≤ k} (S : ExposedDiskSection k hk)

/-- Compactly supported smooth complex test functions on the quotient (full domain). -/
def compactSmoothDomain (m : ℕ) [ChartedSpace ℂ (HeightLift.PeriodQuotient S.F m)] :
    Submodule ℂ (HeightLift.PeriodQuotient S.F m → ℂ) where
  carrier := {f | ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f}
  zero_mem' := ⟨contMDiff_const, by simp [HasCompactSupport]⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    have hc : ContDiff ℝ ∞ (fun z : ℂ => c * z) := contDiff_const.mul contDiff_id
    exact ⟨hc.contMDiff.comp hf.1, (show HasCompactSupport f from hf.2).smul_left⟩

/-- The intrinsic variational index: `FormIndex` of the signed Jacobi form over the test domain. -/
def geometricIndex (m : ℕ) [NeZero m] [ChartedSpace ℂ (HeightLift.PeriodQuotient S.F m)]
    (hCov : S.Covers m) : ℕ∞ :=
  formIndex (S.quotientJacobiQ m hCov) (S.compactSmoothDomain m)

/-- The geometric Jacobi operator in the quotient chart centered at the image x of
the lift q. Both the chart expression of u and the metric/curvature coefficients
are evaluated at the coordinate `(chartAt ℂ x) x`. -/
def jacobiAt (m : ℕ) [ChartedSpace ℂ (HeightLift.PeriodQuotient S.F m)]
    (u : HeightLift.PeriodQuotient S.F m → ℂ) (q : HeightLift S.F) : ℂ :=
  let x : HeightLift.PeriodQuotient S.F m := Quotient.mk (HeightLift.periodSetoid (F := S.F) m) q
  laplacianG k (fun w => u ((chartAt ℂ x).symm w)) ((chartAt ℂ x) x) +
    (absA k ((chartAt ℂ x) x) : ℂ) ^ 2 * u x

/-- The geometric Jacobi equation, imposed at EVERY lift (no selected representative, no a.e.). -/
def IsGeometricJacobi (m : ℕ) [ChartedSpace ℂ (HeightLift.PeriodQuotient S.F m)]
    (u : HeightLift.PeriodQuotient S.F m → ℂ) : Prop :=
  ∀ q : HeightLift S.F, S.jacobiAt m u q = 0

/-- Bounded smooth solutions of the geometric Jacobi equation. -/
def IsBoundedGeometricJacobi (m : ℕ) [ChartedSpace ℂ (HeightLift.PeriodQuotient S.F m)]
    (u : HeightLift.PeriodQuotient S.F m → ℂ) : Prop :=
  ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u ∧ (∃ C : ℝ, ∀ x, ‖u x‖ ≤ C) ∧ S.IsGeometricJacobi m u

section Linear
variable (m : ℕ) [ChartedSpace ℂ (HeightLift.PeriodQuotient S.F m)]
  [IsManifold 𝓘(ℝ, ℂ) ∞ (HeightLift.PeriodQuotient S.F m)]

/-- A smooth quotient function pulls back along a chart inverse to a `C^∞` plane function at the center. -/
lemma chartPullback_contDiffAt (x : HeightLift.PeriodQuotient S.F m)
    {u : HeightLift.PeriodQuotient S.F m → ℂ} (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u) :
    ContDiffAt ℝ ∞ (fun w => u ((chartAt ℂ x).symm w)) ((chartAt ℂ x) x) := by
  have hs := (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := x)).contMDiffAt
    ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))
  exact ((hu _).comp _ hs).contDiffAt

lemma jacobiAt_add {u v : HeightLift.PeriodQuotient S.F m → ℂ}
    (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u) (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ v)
    (q : HeightLift S.F) :
    S.jacobiAt m (u + v) q = S.jacobiAt m u q + S.jacobiAt m v q := by
  simp only [jacobiAt, laplacianG]
  change _ * laplacian ((fun w => u ((chartAt ℂ _).symm w)) + (fun w => v ((chartAt ℂ _).symm w))) _ + _ = _
  rw [laplacian_add
      (S.chartPullback_contDiffAt m (Quotient.mk (HeightLift.periodSetoid (F := S.F) m) q) hu)
      (S.chartPullback_contDiffAt m (Quotient.mk (HeightLift.periodSetoid (F := S.F) m) q) hv)]
  rw [show (u + v) (Quotient.mk (HeightLift.periodSetoid (F := S.F) m) q)
        = u (Quotient.mk (HeightLift.periodSetoid (F := S.F) m) q)
          + v (Quotient.mk (HeightLift.periodSetoid (F := S.F) m) q) from rfl]
  ring

lemma jacobiAt_smul (c : ℂ) {u : HeightLift.PeriodQuotient S.F m → ℂ}
    (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u) (q : HeightLift S.F) :
    S.jacobiAt m (c • u) q = c * S.jacobiAt m u q := by
  simp only [jacobiAt, laplacianG]
  change _ * laplacian (c • (fun w => u ((chartAt ℂ _).symm w))) _ + _ = _
  erw [laplacian_smul c
      (S.chartPullback_contDiffAt m (Quotient.mk (HeightLift.periodSetoid (F := S.F) m) q) hu)]
  rw [show (c • u) (Quotient.mk (HeightLift.periodSetoid (F := S.F) m) q)
        = c * u (Quotient.mk (HeightLift.periodSetoid (F := S.F) m) q) from rfl]
  ring

lemma isBoundedGeometricJacobi_zero :
    S.IsBoundedGeometricJacobi m (0 : HeightLift.PeriodQuotient S.F m → ℂ) := by
  refine ⟨contMDiff_const, ⟨0, fun x => by simp⟩, ?_⟩
  intro q
  have h := S.jacobiAt_smul m (0 : ℂ) (u := (0 : HeightLift.PeriodQuotient S.F m → ℂ))
    contMDiff_const q
  simpa using h

lemma isBoundedGeometricJacobi_add {u v : HeightLift.PeriodQuotient S.F m → ℂ}
    (hu : S.IsBoundedGeometricJacobi m u) (hv : S.IsBoundedGeometricJacobi m v) :
    S.IsBoundedGeometricJacobi m (u + v) := by
  obtain ⟨hsu, ⟨C, hC⟩, hju⟩ := hu
  obtain ⟨hsv, ⟨D, hD⟩, hjv⟩ := hv
  refine ⟨hsu.add hsv, ⟨C + D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩, ?_⟩
  intro q
  rw [S.jacobiAt_add m hsu hsv q, hju q, hjv q, zero_add]

lemma isBoundedGeometricJacobi_smul (c : ℂ) {u : HeightLift.PeriodQuotient S.F m → ℂ}
    (hu : S.IsBoundedGeometricJacobi m u) : S.IsBoundedGeometricJacobi m (c • u) := by
  obtain ⟨hsu, ⟨C, hC⟩, hju⟩ := hu
  have hc : ContDiff ℝ ∞ (fun z : ℂ => c * z) := contDiff_const.mul contDiff_id
  refine ⟨hc.contMDiff.comp hsu, ⟨‖c‖ * C, fun x => ?_⟩, ?_⟩
  · simpa only [Pi.smul_apply, norm_smul] using mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)
  · intro q
    rw [S.jacobiAt_smul m c hsu q, hju q, mul_zero]

/-- The complex vector space of bounded smooth geometric Jacobi fields. -/
def boundedGeometricJacobi : Submodule ℂ (HeightLift.PeriodQuotient S.F m → ℂ) where
  carrier := {u | S.IsBoundedGeometricJacobi m u}
  zero_mem' := S.isBoundedGeometricJacobi_zero m
  add_mem' := fun hu hv => S.isBoundedGeometricJacobi_add m hu hv
  smul_mem' := fun c _ hu => S.isBoundedGeometricJacobi_smul m c hu

/-- The intrinsic geometric nullity: complex dimension of bounded smooth Jacobi fields. -/
def geometricNullity : ℕ∞ := Cardinal.toENat (Module.rank ℂ (S.boundedGeometricJacobi m))

end Linear
end ExposedDiskSection
end KSPalomar.Intrinsic.Full
end


noncomputable section
open Complex
open scoped ContDiff Manifold Topology
namespace KSPalomar.Intrinsic.Full

/-! ### Weierstrass map vocabulary -/
/-- Project a real three-vector to the ambient quotient by reducing its height modulo 2π. -/
def projectPeriod (p : ℝ × ℝ × ℝ) : PeriodTarget := (p.1, p.2.1, (p.2.2 : AddCircle (2 * Real.pi)))
/-- The meromorphic Gauss-map coordinate g(w) = w^(k-1). -/
def gauss (k : ℕ) (w : ℂ) : ℂ := w ^ (k - 1)
/-- The coefficient k/(1 + w^(2k)) of the Weierstrass differential. -/
def etaTarget (k : ℕ) (w : ℂ) : ℂ := (k : ℂ) / (1 + w ^ (2 * k))
/-- The first Weierstrass coefficient (1 - g²)h. -/
def phi1 (g h : ℂ) : ℂ := (1 - g ^ 2) * h
/-- The second Weierstrass coefficient i(1 + g²)h. -/
def phi2 (g h : ℂ) : ℂ := Complex.I * (1 + g ^ 2) * h
/-- The third Weierstrass coefficient 2gh. -/
def phi3 (g h : ℂ) : ℂ := 2 * g * h
/-- The first Weierstrass coefficient evaluated on the specified Gauss map and differential. -/
def coeff1 (k : ℕ) (w : ℂ) : ℂ := phi1 (gauss k w) (etaTarget k w)
/-- The second Weierstrass coefficient evaluated on the specified Gauss map and differential. -/
def coeff2 (k : ℕ) (w : ℂ) : ℂ := phi2 (gauss k w) (etaTarget k w)
/-- The third Weierstrass coefficient evaluated on the specified Gauss map and differential. -/
def coeff3 (k : ℕ) (w : ℂ) : ℂ := phi3 (gauss k w) (etaTarget k w)

/-- A parametrized C¹ curve on a nondegenerate closed real interval, with its continuous velocity. -/
structure EWPiece where
  a : ℝ
  b : ℝ
  lt : a < b
  curve : ℝ → ℂ
  velocity : ℝ → ℂ
  continuous_curve : ContinuousOn curve (Set.Icc a b)
  continuous_velocity : ContinuousOn velocity (Set.Icc a b)
  derivative : ∀ t ∈ Set.Icc a b, HasDerivWithinAt curve (velocity t) (Set.Icc a b) t

namespace EWPiece
/-- The initial endpoint of a curve piece. -/
def start (p : EWPiece) : ℂ := p.curve p.a
/-- The final endpoint of a curve piece. -/
def finish (p : EWPiece) : ℂ := p.curve p.b
/-- The complex contour integral over a piece, using its velocity and orientation. -/
def contour (p : EWPiece) (f : ℂ → ℂ) : ℂ := ∫ t in p.a..p.b, p.velocity t * f (p.curve t)
/-- The entire closed curve piece avoids the specified complex point. -/
def Avoids (p : EWPiece) (z : ℂ) : Prop := ∀ t ∈ Set.Icc p.a p.b, p.curve t ≠ z
end EWPiece

/-- A nonempty finite sequence of C¹ pieces whose consecutive endpoints agree. -/
structure EWChain where
  n : ℕ
  piece : Fin (n + 1) → EWPiece
  matching : ∀ i : Fin n, (piece i.castSucc).finish = (piece i.succ).start

namespace EWChain
/-- The initial endpoint of the first piece of a chain. -/
def start (C : EWChain) : ℂ := (C.piece 0).start
/-- The final endpoint of the last piece of a chain. -/
def finish (C : EWChain) : ℂ := (C.piece (Fin.last C.n)).finish
/-- The sum of the contour integrals over all pieces of a chain. -/
def contour (C : EWChain) (f : ℂ → ℂ) : ℂ := ∑ i, (C.piece i).contour f
/-- Every piece of the chain avoids the specified complex point. -/
def Avoids (C : EWChain) (z : ℂ) : Prop := ∀ i, (C.piece i).Avoids z
end EWChain

/-- The real parts of the three Weierstrass contour integrals along a chain. -/
def periodVector (k : ℕ) (C : EWChain) : ℝ × ℝ × ℝ :=
  ((C.contour (coeff1 k)).re, (C.contour (coeff2 k)).re, (C.contour (coeff3 k)).re)
/-- The Weierstrass integral along a chain, with vertical coordinate reduced modulo 2π. -/
def quotientIntegral (k : ℕ) (C : EWChain) : PeriodTarget := projectPeriod (periodVector k C)

/-- The full-sphere based EW map characterization: `F` at every finite parameter equals the quotient
integral of every puncture-avoiding chain from `b`, with continuity through regular infinity. -/
def IsBasedEWMapSphere {k : ℕ} (b : PuncturedPlane k) (F : ParameterSphere k → PeriodTarget) : Prop :=
  Continuous F ∧ ∀ (w : PuncturedPlane k) (c : EWChain),
    c.start = b.val → c.finish = w.val → (∀ z ∈ punctures k, c.Avoids z) →
    F (finiteParameter w) = quotientIntegral k c

namespace HeightLift
variable {P : Type*} {F : P → PeriodTarget}
/-- The parameter projection induced on the periodic quotient of the height lift. -/
def quotientProjection (m : ℕ) : PeriodQuotient F m → P :=
  Quotient.lift projection (by rintro q r ⟨n, rfl⟩; rfl)
end HeightLift

/-! ### Exposed atlas-compatibility (intended parameter-sphere atlas) -/
section Atlas
variable {k : ℕ} [ChartedSpace ℂ (ParameterSphere k)] {F : ParameterSphere k → PeriodTarget} (m : ℕ)
  [ChartedSpace ℂ (HeightLift.PeriodQuotient F m)]

/-- The quotient atlas agrees with the parameter charts pulled back along the projection. -/
structure CompatibleProjectionAtlas : Prop where
  chart_apply : ∀ q r : HeightLift.PeriodQuotient F m,
    chartAt ℂ q r = chartAt ℂ (HeightLift.quotientProjection m q) (HeightLift.quotientProjection m r)
  symm_projection : ∀ (q : HeightLift.PeriodQuotient F m) {z : ℂ}, z ∈ (chartAt ℂ q).target →
    HeightLift.quotientProjection m ((chartAt ℂ q).symm z)
      = (chartAt ℂ (HeightLift.quotientProjection m q)).symm z

end Atlas

/-! ### The six-ended spectral threshold

This is the sequence form of the reduced circle problem in Section 4,
"Quotients with six ends", of the cited paper, especially "Reduction to the
circle", "Frequency parity" and "Threshold". Section 2's half-period
Dirichlet-to-Neumann symbol is `(j^2 - (k-1)^2) / |j|`; at `k = 3` it restricts
to the rotation/parity sectors `j = 6n+1` and `j = 6m+4` below.

The alternating-arc sign function `varsigma` has Fourier coefficients supported
on `6ℤ+3`. Reindexing gives `chat d = varsigma_hat (6d+3)`, so multiplication by
`varsigma` between these sectors is `convS`, since
`(6m+4) - (6n+1) = 6(m-n)+3`. The two weighted summability conditions in
`MemDom` express the form domain for the sequence and its sign transform.
`Qform s` is the reduced quadratic form; `gam s` is its variational infimum
on normalized domain sequences. Its spectral interpretation belongs to the
paper's "Threshold" analysis.

For `s > 0`, `criticalPhase s = (2/π) arctan(1/s)` inverts
`s = cot(πα/2)`. Thus `1 < s < sqrt 3` corresponds to `1/3 < α < 1/2`.
`IsThreshold` specifies the zero and signs of `gam`; `unique_threshold` proves
existence and uniqueness. The resulting phase is the same threshold used by
the geometric staircase and the certified numerical bounds.
-/
/-- The k = 3 half-period Dirichlet-to-Neumann symbol on the rotation/parity sector j = 6n + 1. -/
def sigP (n : ℤ) : ℝ := ((6 * (n : ℝ) + 1) ^ 2 - 4) / |6 * (n : ℝ) + 1|
/-- The same half-period Dirichlet-to-Neumann symbol on the sector j = 6m + 4. -/
def sigM (m : ℤ) : ℝ := ((6 * (m : ℝ) + 4) ^ 2 - 4) / |6 * (m : ℝ) + 4|
/-- The coefficient of the alternating-arc sign function at frequency 6d + 3:
`2(-1)^d/(π(2d + 1))`. Its other Fourier frequencies vanish outside 6ℤ + 3. -/
def chat (d : ℤ) : ℝ := 2 / Real.pi * (-1) ^ d / (2 * (d : ℝ) + 1)
/-- Fourier representation of multiplication by the alternating-arc sign function,
from frequencies 6n + 1 to frequencies 6m + 4, expressed as convolution with `chat`. -/
def convS (u : ℤ → ℂ) (m : ℤ) : ℂ := ∑' n : ℤ, (chat (m - n) : ℂ) * u n
/-- The reduced form domain: weighted square summability of the sequence and its
sign transform, with weights |6n + 1| and |6m + 4| respectively. -/
def MemDom (u : ℤ → ℂ) : Prop :=
  Summable (fun n : ℤ => |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2)
    ∧ Summable (fun m : ℤ => |6 * (m : ℝ) + 4| * ‖convS u m‖ ^ 2)
/-- The squared ℓ² norm, expressed as the bilateral sum of squared absolute values. -/
def normSq (u : ℤ → ℂ) : ℝ := ∑' n : ℤ, ‖u n‖ ^ 2
/-- The reduced circle quadratic form: energy in the 6n + 1 sector plus s² times
the energy of the sign-transformed sequence in the 6m + 4 sector. -/
def Qform (s : ℝ) (u : ℤ → ℂ) : ℝ :=
  (∑' n : ℤ, sigP n * ‖u n‖ ^ 2) + s ^ 2 * ∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2
/-- The infimum of Qform on unit-norm sequences in its form domain. -/
def gam (s : ℝ) : ℝ := sInf {r : ℝ | ∃ u : ℤ → ℂ, MemDom u ∧ normSq u = 1 ∧ Qform s u = r}
/-- For positive s, the phase α = 2 arctan(1/s)/π, inverse to s = cot(πα/2). -/
def criticalPhase (s : ℝ) : ℝ := 2 / Real.pi * Real.arctan (1 / s)
/-- A zero of gam in (1, √3), with gam negative below it on positive parameters and positive above it. -/
def IsThreshold (s : ℝ) : Prop :=
  s ∈ Set.Ioo 1 (Real.sqrt 3) ∧ gam s = 0 ∧
    (∀ t : ℝ, 0 < t → t < s → gam t < 0) ∧ (∀ t : ℝ, s < t → 0 < gam t)

/-! ### The reflection basepoint, the infinity chart, and the covered smooth section bundle -/
/-- The finite parameter w = 1, used to normalize the based Weierstrass integral. -/
def reflectionBasepoint (k : ℕ) : PuncturedPlane k := ⟨1, by norm_num [punctures, Set.mem_setOf_eq]⟩

/-- The infinity-side stereographic chart (= `southChart (conj v)`): regular at `0` (the north point),
agreeing with `sphereChart (v⁻¹)` for `v ≠ 0`. -/
def infinitySphereChart (v : ℂ) : Sphere := reflectSphere (sphereChart (starRingEnd ℂ v))

/-- The north point is outside the image of the finite punctures. -/
theorem infinitySphereChart_zero_not_mem_punctures (k : ℕ) :
    infinitySphereChart 0 ∉ sphereChart '' punctures k := by
  rintro ⟨z, _hz, he⟩
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h2 := congrArg (fun p : Sphere => p.val 2) he
  have hz2 : stereoPoint z 2 = (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2) := rfl
  have hinf : (infinitySphereChart 0).val 2 = 1 := by
    simp [infinitySphereChart, reflectSphere, reflectAmbient, sphereChart, stereoPoint]
  rw [show ((sphereChart z).val 2) = stereoPoint z 2 from rfl, hz2, hinf] at h2
  rw [div_eq_one_iff_eq hd] at h2
  nlinarith [sq_nonneg ‖z‖]

/-- The regular point at infinity of the parameter sphere (the north point), not a finite puncture. -/
def infinityParameter (k : ℕ) : ParameterSphere k :=
  ⟨infinitySphereChart 0, infinitySphereChart_zero_not_mem_punctures k⟩

/-- Data for a smooth periodic quotient of the based Enneper-Weierstrass realization.

The underlying section is required to satisfy the based integral specification at
w = 1. Its disk lift has prescribed projection and height in [-π, 0], a window
shorter than the 2π deck period. Parameter charts are prescribed locally by their
coordinate values and inverse-chart germs at finite points and at infinity.
The quotient atlas is smooth and compatible with parameter projection, and the
ordered disk copies cover the quotient. Germ conditions specify local coordinates;
they do not assert equality of global chart domains or a surface-uniqueness theorem.

The metric factor `rho` and curvature magnitude `absA` are explicit expressions
for the data g = w^(k-1), η = k dw/(1+w^(2k)); the vertical differential is 2gη.
They are not defined by differentiating the bundled map F. For nonzero,
nonpunctured w, inversion σ(w) = 1/conj(w) gives
`rho (σ w) = ‖w‖^2 * rho w`, so the metric transforms with the coordinate
Jacobian; `absA` is a scalar invariant under this transition. The deck action
uses vertical period 2π, and the quotient identifies heights modulo 2πm.

The identification with the paper's named Karcher surface uses the
characterization recalled in its Theorem 1.1, attributed to Scherk, Karcher and
Pérez-Traizet. The formalization constructs the explicit realization and does
not prove a surface-uniqueness theorem. -/
structure CoveredSmoothSection (k : ℕ) (hk : 2 ≤ k) (m : ℕ) where
  toSection   : ExposedDiskSection k hk
  basedMap    : IsBasedEWMapSphere (reflectionBasepoint k) toSection.F
  pos         : 0 < m
  paramChart  : ChartedSpace ℂ (ParameterSphere k)
  -- the intended parameter atlas, pinned by its finite/infinity coordinate germs:
  chart_finite_center : ∀ w : PuncturedPlane k,
    @chartAt ℂ _ (ParameterSphere k) _ paramChart (finiteParameter w) (finiteParameter w) = w.val
  chart_finite_germ : ∀ w : PuncturedPlane k,
    (fun z => (@chartAt ℂ _ (ParameterSphere k) _ paramChart (finiteParameter w)).symm z |>.val)
      =ᶠ[𝓝 w.val] sphereChart
  chart_infinity_center :
    @chartAt ℂ _ (ParameterSphere k) _ paramChart (infinityParameter k) (infinityParameter k) = 0
  chart_infinity_germ :
    (fun z => (@chartAt ℂ _ (ParameterSphere k) _ paramChart (infinityParameter k)).symm z |>.val)
      =ᶠ[𝓝 (0 : ℂ)] infinitySphereChart
  chart       : ChartedSpace ℂ (HeightLift.PeriodQuotient toSection.F m)
  isManifold  : @IsManifold ℝ _ ℂ _ _ ℂ _ 𝓘(ℝ, ℂ) ∞ _ _ chart
  atlasCompat : @CompatibleProjectionAtlas k paramChart toSection.F m chart
  covers      : toSection.Covers m

/-- The intrinsic Morse index of the bundled surface. -/
def CoveredSmoothSection.index {k : ℕ} {hk : 2 ≤ k} {m : ℕ} (B : CoveredSmoothSection k hk m) : ℕ∞ :=
  letI : NeZero m := ⟨Nat.ne_of_gt B.pos⟩
  letI := B.chart
  B.toSection.geometricIndex m B.covers

/-- The intrinsic nullity of the bundled surface. -/
def CoveredSmoothSection.nullity {k : ℕ} {hk : 2 ≤ k} {m : ℕ} (B : CoveredSmoothSection k hk m) : ℕ∞ :=
  letI := B.chart
  letI := B.isManifold
  B.toSection.geometricNullity m


end KSPalomar.Intrinsic.Full

end


noncomputable section
open scoped Classical
namespace KSPalomar.Intrinsic.Full
/-- **Intrinsic index/nullity, m = 2, k ≥ 3.** -/
theorem exists_intrinsic_index_nullity_m2 {k : ℕ} (hk : 2 ≤ k) (hk3 : 3 ≤ k) :
    ∃ B : CoveredSmoothSection k hk 2, B.index = ((4 * k - 3 : ℕ) : ℕ∞) ∧ B.nullity = 3 := by
  sorry

open Classical in
/-- **Intrinsic staircase index + resonance nullity dichotomy, k = 3, all m > 0** (one fixed section and
one fixed threshold `s` before the universal period quantifier). -/
theorem exists_intrinsic_staircase_k3 :
    ∃ (B0 : ExposedDiskSection 3 (by norm_num))
      (_ : IsBasedEWMapSphere (reflectionBasepoint 3) B0.F) (s : ℝ) (_ : IsThreshold s),
      ∀ m : ℕ, 0 < m →
        ∃ B : CoveredSmoothSection 3 (by norm_num) m, B.toSection = B0 ∧
          B.index = ((6 * m - 4 * ⌊(m : ℝ) * criticalPhase s⌋₊ - 3 : ℕ) : ℕ∞) ∧
          B.nullity = (if ∃ z : ℤ, (m : ℝ) * criticalPhase s = (z : ℝ) then 7 else 3) := by
  sorry


end KSPalomar.Intrinsic.Full
end

noncomputable section
namespace KSPalomar.Intrinsic.Full

/-! ### Certified bounds for the same critical phase used by the geometric theorem

The threshold is the one characterized by `IsThreshold` above. The strict
decimal enclosure also gives the stated floor and nonresonance consequences
through period 2298; no irrationality claim is made.
-/

/-- There exists exactly one sign-changing threshold with the stated characterization. -/
theorem unique_threshold : ∃! s : ℝ, IsThreshold s := by
  sorry

/-- Both strict decimal bounds concern the uniquely characterized critical phase. -/
theorem decimal_bounds (s : ℝ) (hs : IsThreshold s) :
    (4323617 : ℝ) / 10000000 < criticalPhase s ∧
    criticalPhase s < (4323619 : ℝ) / 10000000 := by
  sorry

/-- Exact natural floor and nonresonance for each positive integer period at most 2298. -/
theorem period_arithmetic (s : ℝ) (hs : IsThreshold s) (m : ℕ)
    (hm : 0 < m) (hmax : m ≤ 2298) :
    ⌊(m : ℝ) * criticalPhase s⌋₊ = 4323617 * m / 10000000 ∧
    ∀ z : ℤ, (m : ℝ) * criticalPhase s ≠ (z : ℝ) := by
  sorry

end KSPalomar.Intrinsic.Full
end
