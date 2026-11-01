module

public import KsIndexLean.KarcherSymmetry
public import KsIndexLean.KarcherPeriodIndex

@[expose] public section


/-!
# Contour transformations and integrated symmetry identities

Complex scaling, conjugation and reciprocal maps act on certified contour chains.
Their change-of-variables formulas transfer the Weierstrass coefficient identities
from `KarcherSymmetry` to period vectors and `descendedIntegral`. The latter
transforms both its base point and endpoint, so these are identities for integral
differences in `PeriodTarget`, not assertions about an absolute translation constant.
Reciprocal and seam-reflection constructions require chains avoiding zero.
-/
noncomputable section
namespace KsIndex.KarcherData
open Piecewise

/-- Complex scaling of a certified piece by `a : ℂ`, using `w ↦ a·w`. -/
def Piece.smul (a : ℂ) (p : Piece) : Piece where
  a := p.a
  b := p.b
  lt := p.lt
  curve := fun t => a * p.curve t
  velocity := fun t => a * p.velocity t
  continuous_curve := continuousOn_const.mul p.continuous_curve
  continuous_velocity := continuousOn_const.mul p.continuous_velocity
  derivative := fun t ht => (p.derivative t ht).const_mul a

@[simp] lemma Piece.smul_start (a : ℂ) (p : Piece) : (Piece.smul a p).start = a * p.start := rfl
@[simp] lemma Piece.smul_finish (a : ℂ) (p : Piece) : (Piece.smul a p).finish = a * p.finish := rfl

/-- Change of variables on a piece: `contour(a·p, f) = a·contour(p, f∘(a·))`. -/
lemma Piece.smul_contour (a : ℂ) (p : Piece) (f : ℂ → ℂ) :
    (Piece.smul a p).contour f = a * p.contour (fun v => f (a * v)) := by
  simp only [Piece.contour, Piece.smul]
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr (fun t _ => by ring)

/-- `a·p` avoids `z` when `p` avoids `a⁻¹·z` (`a ≠ 0`). -/
lemma Piece.smul_avoids {a : ℂ} (ha : a ≠ 0) {p : Piece} {z : ℂ} (h : p.Avoids (a⁻¹ * z)) :
    (Piece.smul a p).Avoids z := by
  intro t ht he
  apply h t ht
  simp only [Piece.smul] at he
  rw [← he, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

/-- Complex scaling of a chain by `a`. -/
def Chain.smul (a : ℂ) (C : Chain) : Chain where
  n := C.n
  piece := fun i => Piece.smul a (C.piece i)
  matching := fun i => by
    show (Piece.smul a (C.piece i.castSucc)).finish = (Piece.smul a (C.piece i.succ)).start
    rw [Piece.smul_finish, Piece.smul_start, C.matching i]

@[simp] lemma Chain.smul_start (a : ℂ) (C : Chain) : (Chain.smul a C).start = a * C.start := rfl

@[simp] lemma Chain.smul_finish (a : ℂ) (C : Chain) : (Chain.smul a C).finish = a * C.finish := rfl

/-- Change of variables on a chain: `contour(a·C, f) = a·contour(C, f∘(a·))`. -/
lemma Chain.smul_contour (a : ℂ) (C : Chain) (f : ℂ → ℂ) :
    (Chain.smul a C).contour f = a * C.contour (fun v => f (a * v)) := by
  simp only [Chain.contour, Chain.smul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Piece.smul_contour a (C.piece i) f)

/-- `a·C` avoids `z` when `C` avoids `a⁻¹·z` and `a ≠ 0`. -/
lemma Chain.smul_avoids {a : ℂ} (ha : a ≠ 0) {C : Chain} {z : ℂ} (h : C.Avoids (a⁻¹ * z)) :
    (Chain.smul a C).Avoids z :=
  fun i => Piece.smul_avoids ha (h i)

/-- `a·C` is closed when `C` is. -/
lemma Chain.smul_isClosed {a : ℂ} (C : Chain) (hc : C.IsClosed) : (Chain.smul a C).IsClosed := by
  unfold Chain.IsClosed
  rw [Chain.smul_finish, Chain.smul_start, hc]

/-! ### Integrability of the EW coefficients on puncture-avoiding chains. -/

/-- A point on a puncture-avoiding chain's image is not that avoided point. -/
lemma Chain.ne_of_mem_image {C : Chain} {w z : ℂ} (hw : w ∈ C.image) (h : C.Avoids z) : w ≠ z := by
  rw [Chain.image, Set.mem_iUnion] at hw
  obtain ⟨i, hi⟩ := hw
  rw [Piece.image, Set.mem_image] at hi
  obtain ⟨t, ht, hwt⟩ := hi
  rw [← hwt]
  exact h i t ht

/-- Any function differentiable off the punctures is contour-integrable on a puncture-avoiding chain. -/
lemma Chain.integrable_of_differentiable_off_punctures {k : ℕ} {C : Chain} {f : ℂ → ℂ}
    (hf : ∀ w, w ∉ Surface.punctures k → DifferentiableAt ℂ f w)
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) : C.Integrable f :=
  C.integrable_of_continuousOn fun w hw =>
    (hf w fun hp => Chain.ne_of_mem_image hw (hC w hp) rfl).continuousAt.continuousWithinAt

lemma coeff1_integrableOn {k : ℕ} {C : Chain} (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    C.Integrable (coeff1 k) :=
  Chain.integrable_of_differentiable_off_punctures (fun _ hw => differentiableAt_coeff1 hw) hC

lemma coeff2_integrableOn {k : ℕ} {C : Chain} (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    C.Integrable (coeff2 k) :=
  Chain.integrable_of_differentiable_off_punctures (fun _ hw => differentiableAt_coeff2 hw) hC

lemma coeff3_integrableOn {k : ℕ} {C : Chain} (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    C.Integrable (coeff3 k) :=
  Chain.integrable_of_differentiable_off_punctures (fun _ hw => differentiableAt_coeff3 hw) hC

/-- The rotated chain avoids the punctures when `C` does (`a^(2k)=1` ⟹ `a⁻¹·puncture` is a puncture). -/
lemma Chain.smul_avoids_punctures {k : ℕ} (hk : 1 ≤ k) {a : ℂ} (ha2k : a ^ (2 * k) = 1) {C : Chain}
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    ∀ z ∈ Surface.punctures k, (Chain.smul a C).Avoids z := by
  have hane : a ≠ 0 := by
    rintro rfl; rw [zero_pow (by omega : 2 * k ≠ 0)] at ha2k; exact zero_ne_one ha2k
  intro z hz
  apply Chain.smul_avoids hane
  apply hC
  simp only [Surface.punctures, Set.mem_ofPred_eq] at hz ⊢
  rw [mul_pow, inv_pow, ha2k, inv_one, one_mul, hz]

/-! ### The contour-combo rotation identities (heart of the `periodVector` rotation). -/

/-- Package `contour` ℂ-linearity for the `f + i·g` combination. -/
lemma Chain.contour_add_Imul (C : Chain) {f g : ℂ → ℂ} (hf : C.Integrable f) (hg : C.Integrable g) :
    C.contour (fun v => f v + Complex.I * g v) = C.contour f + Complex.I * C.contour g := by
  rw [C.contour_add (f := f) (g := fun v => Complex.I * g v) hf
      (C.integrable_const_mul Complex.I hg), C.contour_const_mul Complex.I hg]

/-- `A`-combo under rotation at the contour level: scales by `a⁻¹` (`a^(2k)=1`). -/
lemma contour_combo_A_smul {k : ℕ} (hk : 1 ≤ k) {a : ℂ} (ha2k : a ^ (2 * k) = 1) {C : Chain}
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    (Chain.smul a C).contour (coeff1 k) + Complex.I * (Chain.smul a C).contour (coeff2 k)
      = a⁻¹ * (C.contour (coeff1 k) + Complex.I * C.contour (coeff2 k)) := by
  have hane : a ≠ 0 := by
    rintro rfl; rw [zero_pow (by omega : 2 * k ≠ 0)] at ha2k; exact zero_ne_one ha2k
  have ha1 : a * (a ^ (k - 1)) ^ 2 = a⁻¹ := by
    have key : a * (a * (a ^ (k - 1)) ^ 2) = 1 := by
      rw [show a * (a * (a ^ (k - 1)) ^ 2) = (a * a ^ (k - 1)) ^ 2 from by ring, mul_pow_pred hk,
        ← pow_mul, mul_comm k 2, ha2k]
    rw [inv_eq_one_div, eq_div_iff hane]; linear_combination key
  have hCsa := Chain.smul_avoids_punctures hk ha2k hC
  have hi1 := coeff1_integrableOn hCsa
  have hi2 := coeff2_integrableOn hCsa
  have hc1 := coeff1_integrableOn hC
  have hc2 := coeff2_integrableOn hC
  rw [← Chain.contour_add_Imul _ hi1 hi2, Chain.smul_contour]
  rw [show (fun v => coeff1 k (a * v) + Complex.I * coeff2 k (a * v))
        = (fun v => (a ^ (k - 1)) ^ 2 * (coeff1 k v + Complex.I * coeff2 k v)) from
      funext fun v => coeff_combo_A_rot ha2k v]
  rw [C.contour_const_mul ((a ^ (k - 1)) ^ 2) (C.integrable_add hc1 (C.integrable_const_mul _ hc2)),
    ← mul_assoc, ha1, Chain.contour_add_Imul _ hc1 hc2]

/-- Package `contour` ℂ-linearity for the `f - i·g` combination. -/
lemma Chain.contour_sub_Imul (C : Chain) {f g : ℂ → ℂ} (hf : C.Integrable f) (hg : C.Integrable g) :
    C.contour (fun v => f v - Complex.I * g v) = C.contour f - Complex.I * C.contour g := by
  rw [show (fun v => f v - Complex.I * g v) = (fun v => f v + (-Complex.I) * g v) from by
      funext v; ring,
    C.contour_add (f := f) (g := fun v => (-Complex.I) * g v) hf
      (C.integrable_const_mul (-Complex.I) hg), C.contour_const_mul (-Complex.I) hg]
  ring

/-- `B`-combo under rotation at the contour level: scales by `a` (`a^(2k)=1`; `B∘(a·)=B`). -/
lemma contour_combo_B_smul {k : ℕ} (hk : 1 ≤ k) {a : ℂ} (ha2k : a ^ (2 * k) = 1) {C : Chain}
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    (Chain.smul a C).contour (coeff1 k) - Complex.I * (Chain.smul a C).contour (coeff2 k)
      = a * (C.contour (coeff1 k) - Complex.I * C.contour (coeff2 k)) := by
  have hCsa := Chain.smul_avoids_punctures hk ha2k hC
  have hi1 := coeff1_integrableOn hCsa
  have hi2 := coeff2_integrableOn hCsa
  have hc1 := coeff1_integrableOn hC
  have hc2 := coeff2_integrableOn hC
  rw [← Chain.contour_sub_Imul _ hi1 hi2, Chain.smul_contour]
  rw [show (fun v => coeff1 k (a * v) - Complex.I * coeff2 k (a * v))
        = (fun v => coeff1 k v - Complex.I * coeff2 k v) from
      funext fun v => coeff_combo_B_rot ha2k v]
  rw [Chain.contour_sub_Imul _ hc1 hc2]

/-- Vertical (`coeff3`) under rotation: scales by `a^k` (`a^(2k)=1`; `coeff3∘(a·)=a^(k-1)·coeff3`). -/
lemma contour_coeff3_smul {k : ℕ} (hk : 1 ≤ k) {a : ℂ} (ha2k : a ^ (2 * k) = 1) {C : Chain}
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    (Chain.smul a C).contour (coeff3 k) = a ^ k * C.contour (coeff3 k) := by
  rw [Chain.smul_contour,
    show (fun v => coeff3 k (a * v)) = (fun v => a ^ (k - 1) * coeff3 k v) from
      funext fun v => coeff3_rot ha2k v,
    C.contour_const_mul (a ^ (k - 1)) (coeff3_integrableOn hC), ← mul_assoc, mul_pow_pred hk]

/-- `Re`-decomposition of a horizontal pair: `2(Re w₁ + i Re w₂) = (w₁+iw₂) + conj(w₁−iw₂)`. -/
lemma two_re_horiz (w₁ w₂ : ℂ) :
    2 * ((w₁.re : ℂ) + (w₂.re : ℂ) * Complex.I)
      = (w₁ + Complex.I * w₂) + starRingEnd ℂ (w₁ - Complex.I * w₂) := by
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.conj_re, Complex.conj_im] <;> ring

/-- Horizontal rotation of `periodVector`: `Re p₁ + i Re p₂ ↦ a⁻¹·(Re z₁ + i Re z₂)`. -/
lemma periodVector_horiz_smul {k : ℕ} (hk : 1 ≤ k) {a : ℂ} (ha2k : a ^ (2 * k) = 1) {C : Chain}
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    (((Chain.smul a C).contour (coeff1 k)).re : ℂ)
        + (((Chain.smul a C).contour (coeff2 k)).re : ℂ) * Complex.I
      = a⁻¹ * (((C.contour (coeff1 k)).re : ℂ) + ((C.contour (coeff2 k)).re : ℂ) * Complex.I) := by
  have hnorm : ‖a‖ = 1 := by
    have hn : ‖a‖ ^ (2 * k) = 1 := by rw [← norm_pow, ha2k, norm_one]
    rcases lt_trichotomy ‖a‖ 1 with h | h | h
    · exact absurd hn (ne_of_lt (pow_lt_one₀ (norm_nonneg a) h (by omega)))
    · exact h
    · exact absurd hn (ne_of_gt (one_lt_pow₀ h (by omega)))
  have hconja : starRingEnd ℂ a = a⁻¹ := (Complex.inv_eq_conj hnorm).symm
  have hA := contour_combo_A_smul hk ha2k hC
  have hB := contour_combo_B_smul hk ha2k hC
  refine mul_left_cancel₀ (two_ne_zero) ?_
  rw [two_re_horiz, hA, hB,
    show (2 : ℂ) * (a⁻¹ * (((C.contour (coeff1 k)).re : ℂ) + ((C.contour (coeff2 k)).re : ℂ) * Complex.I))
      = a⁻¹ * (2 * (((C.contour (coeff1 k)).re : ℂ) + ((C.contour (coeff2 k)).re : ℂ) * Complex.I))
      from by ring, two_re_horiz, map_mul, hconja]
  ring

/-! ### The `PeriodTarget` rotation action and the `descendedIntegral` rotation equivariance. -/

/-- Rotation action on `PeriodTarget`: horizontal rotate by `a⁻¹`, vertical fixed. -/
def PeriodTarget.rotate (a : ℂ) (p : PeriodTarget) : PeriodTarget :=
  ((a⁻¹ * ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I)).re,
    (a⁻¹ * ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I)).im, p.2.2)

/-- `projectPeriod ∘ periodVector` of the rotated chain = the `PeriodTarget` rotation of the original. -/
lemma projectPeriod_periodVector_smul {k : ℕ} (hk : 1 ≤ k) {a : ℂ} (hak : a ^ k = 1) {C : Chain}
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    projectPeriod (periodVector k (Chain.smul a C))
      = PeriodTarget.rotate a (projectPeriod (periodVector k C)) := by
  have ha2k : a ^ (2 * k) = 1 := by rw [two_mul, pow_add, hak, one_mul]
  have hh := periodVector_horiz_smul hk ha2k hC
  have hv := contour_coeff3_smul hk ha2k hC
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · have := congrArg Complex.re hh
    simpa [projectPeriod, periodVector, PeriodTarget.rotate, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] using this
  · have := congrArg Complex.im hh
    simpa [projectPeriod, periodVector, PeriodTarget.rotate, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] using this
  · simp only [projectPeriod, periodVector, PeriodTarget.rotate, hv, hak, one_mul]

/-- **Rotation equivariance of the actual `descendedIntegral`** (`a^k=1`): at rotated points it is the
`PeriodTarget` rotation (horizontal by `a⁻¹`, vertical fixed) of the original value. -/
theorem descendedIntegral_smul {k : ℕ} (hk : 2 ≤ k) {a : ℂ} (hak : a ^ k = 1) (b w : PuncturedPlane k)
    (hb : a * b.val ∉ Surface.punctures k) (hw : a * w.val ∉ Surface.punctures k) :
    descendedIntegral hk ⟨a * b.val, hb⟩ ⟨a * w.val, hw⟩
      = PeriodTarget.rotate a (descendedIntegral hk b w) := by
  have ha2k : a ^ (2 * k) = 1 := by rw [two_mul, pow_add, hak, one_mul]
  obtain ⟨C, hCs, hCf, hCA⟩ := exists_connecting_chain hk b.property w.property
  have hsmulA := Chain.smul_avoids_punctures (by omega) ha2k hCA
  rw [descendedIntegral_eq hk ⟨a * b.val, hb⟩ ⟨a * w.val, hw⟩ (Chain.smul a C)
      (by rw [Chain.smul_start, hCs]) (by rw [Chain.smul_finish, hCf]) hsmulA,
    descendedIntegral_eq hk b w C hCs hCf hCA]
  exact projectPeriod_periodVector_smul (by omega) hak hCA

/-! ### The `refl_{y=0}` conjugation chain map and its `descendedIntegral` equivariance.

The anti-holomorphic deck `w ↦ conj w` is realized on the contour `Chain` level by the genuine
real-C¹ map `conjMap`, with conjugated velocity rather than a complex-linear
derivative. Its contour satisfies
`contour(conjMap C, f) = conj(contour(C, v ↦ conj(f(conj v))))` via `intervalIntegral_conj`
(unconditional — no integrability hypothesis is needed at the chain-map level, unlike the rotation
combos). Specialized to the Weierstrass coefficients (`coeff1/2/3_conj`, the `diag(1,-1,1)` data) this
yields the `refl_{y=0}` reflection on `periodVector`, hence on `descendedIntegral`. -/

/-- Conjugation of a certified piece (anti-holomorphic deck `w ↦ conj w`): a genuine real-C¹ map,
with real-parameter derivative `conj(velocity)` via `HasDerivWithinAt.star`. -/
def Piece.conjMap (p : Piece) : Piece where
  a := p.a
  b := p.b
  lt := p.lt
  curve := fun t => starRingEnd ℂ (p.curve t)
  velocity := fun t => starRingEnd ℂ (p.velocity t)
  continuous_curve := Complex.continuous_conj.comp_continuousOn p.continuous_curve
  continuous_velocity := Complex.continuous_conj.comp_continuousOn p.continuous_velocity
  derivative := fun t ht => (p.derivative t ht).star

@[simp] lemma Piece.conjMap_start (p : Piece) :
    (Piece.conjMap p).start = starRingEnd ℂ p.start := rfl

@[simp] lemma Piece.conjMap_finish (p : Piece) :
    (Piece.conjMap p).finish = starRingEnd ℂ p.finish := rfl

/-- Change of variables for the conjugation map:
`contour(conjMap p, f) = conj(contour(p, v ↦ conj(f(conj v))))`, via `intervalIntegral_conj`. -/
lemma Piece.conjMap_contour (p : Piece) (f : ℂ → ℂ) :
    (Piece.conjMap p).contour f
      = starRingEnd ℂ (p.contour (fun v => starRingEnd ℂ (f (starRingEnd ℂ v)))) := by
  simp only [Piece.contour, Piece.conjMap]
  rw [← intervalIntegral.intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [map_mul, Complex.conj_conj]

/-- Conjugation of a chain. -/
def Chain.conjMap (C : Chain) : Chain where
  n := C.n
  piece := fun i => Piece.conjMap (C.piece i)
  matching := fun i => by
    show (Piece.conjMap (C.piece i.castSucc)).finish = (Piece.conjMap (C.piece i.succ)).start
    rw [Piece.conjMap_finish, Piece.conjMap_start, C.matching i]

@[simp] lemma Chain.conjMap_start (C : Chain) :
    (Chain.conjMap C).start = starRingEnd ℂ C.start := rfl

@[simp] lemma Chain.conjMap_finish (C : Chain) :
    (Chain.conjMap C).finish = starRingEnd ℂ C.finish := rfl

lemma Chain.conjMap_contour (C : Chain) (f : ℂ → ℂ) :
    (Chain.conjMap C).contour f
      = starRingEnd ℂ (C.contour (fun v => starRingEnd ℂ (f (starRingEnd ℂ v)))) := by
  simp only [Chain.contour, Chain.conjMap, map_sum]
  exact Finset.sum_congr rfl (fun i _ => Piece.conjMap_contour (C.piece i) f)

/-- `conjMap p` avoids `z` when `p` avoids `conj z`. -/
lemma Piece.conjMap_avoids {p : Piece} {z : ℂ} (h : p.Avoids (starRingEnd ℂ z)) :
    (Piece.conjMap p).Avoids z := by
  intro t ht he
  apply h t ht
  simp only [Piece.conjMap] at he
  have := congrArg (starRingEnd ℂ) he
  simpa using this

/-- `conjMap C` avoids `z` when `C` avoids `conj z`. -/
lemma Chain.conjMap_avoids {C : Chain} {z : ℂ} (h : C.Avoids (starRingEnd ℂ z)) :
    (Chain.conjMap C).Avoids z :=
  fun i => Piece.conjMap_avoids (h i)

/-- The puncture set `{w^{2k}=-1}` is invariant under conjugation. -/
lemma conj_mem_punctures {k : ℕ} {z : ℂ} (hz : z ∈ Surface.punctures k) :
    starRingEnd ℂ z ∈ Surface.punctures k := by
  have hz' : z ^ (2 * k) = -1 := hz
  show (starRingEnd ℂ z) ^ (2 * k) = -1
  rw [← map_pow, hz', map_neg, map_one]

/-- `conjMap C` avoids all punctures when `C` does (puncture set is conj-invariant). -/
lemma Chain.conjMap_avoids_punctures {k : ℕ} {C : Chain}
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    ∀ z ∈ Surface.punctures k, (Chain.conjMap C).Avoids z :=
  fun z hz => Chain.conjMap_avoids (hC _ (conj_mem_punctures hz))

/-- `coeff1` contour under conjugation: `conj` of the original (refl_y keeps `x`). -/
lemma contour_coeff1_conjMap {k : ℕ} (C : Chain) :
    (Chain.conjMap C).contour (coeff1 k) = starRingEnd ℂ (C.contour (coeff1 k)) := by
  rw [Chain.conjMap_contour]
  have hfun : (fun v => starRingEnd ℂ (coeff1 k (starRingEnd ℂ v))) = coeff1 k := by
    funext v; rw [coeff1_conj, Complex.conj_conj]
  rw [hfun]

/-- `coeff3` contour under conjugation: `conj` of the original (refl_y keeps `z`). -/
lemma contour_coeff3_conjMap {k : ℕ} (C : Chain) :
    (Chain.conjMap C).contour (coeff3 k) = starRingEnd ℂ (C.contour (coeff3 k)) := by
  rw [Chain.conjMap_contour]
  have hfun : (fun v => starRingEnd ℂ (coeff3 k (starRingEnd ℂ v))) = coeff3 k := by
    funext v; rw [coeff3_conj, Complex.conj_conj]
  rw [hfun]

/-- `coeff2` contour under conjugation: `-conj` of the original (the `i` in `phi2` flips `y`). -/
lemma contour_coeff2_conjMap {k : ℕ} {C : Chain}
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    (Chain.conjMap C).contour (coeff2 k) = -starRingEnd ℂ (C.contour (coeff2 k)) := by
  rw [Chain.conjMap_contour]
  have hfun : (fun v => starRingEnd ℂ (coeff2 k (starRingEnd ℂ v)))
      = (fun v => (-1 : ℂ) * coeff2 k v) := by
    funext v; rw [coeff2_conj, map_neg, Complex.conj_conj]; ring
  rw [hfun, C.contour_const_mul (-1) (coeff2_integrableOn hC), map_mul, map_neg, map_one,
    neg_one_mul]

/-- **`refl_{y=0}` on the real period vector**: `(x, y, z) ↦ (x, -y, z)` under conjugation. -/
lemma periodVector_conjMap {k : ℕ} {C : Chain}
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    periodVector k (Chain.conjMap C)
      = ((periodVector k C).1, -(periodVector k C).2.1, (periodVector k C).2.2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show ((Chain.conjMap C).contour (coeff1 k)).re = (C.contour (coeff1 k)).re
    rw [contour_coeff1_conjMap, Complex.conj_re]
  · show ((Chain.conjMap C).contour (coeff2 k)).re = -(C.contour (coeff2 k)).re
    rw [contour_coeff2_conjMap hC, Complex.neg_re, Complex.conj_re]
  · show ((Chain.conjMap C).contour (coeff3 k)).re = (C.contour (coeff3 k)).re
    rw [contour_coeff3_conjMap, Complex.conj_re]

/-- Reflection action on `PeriodTarget` for `refl_{y=0}`: negate the second (horizontal) coordinate,
leaving the first horizontal coordinate and the vertical `AddCircle` component fixed. -/
def PeriodTarget.reflY (p : PeriodTarget) : PeriodTarget := (p.1, -p.2.1, p.2.2)

/-- `projectPeriod ∘ periodVector` of the conjugated chain = the `refl_y` action on the original. -/
lemma projectPeriod_periodVector_conjMap {k : ℕ} {C : Chain}
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    projectPeriod (periodVector k (Chain.conjMap C))
      = PeriodTarget.reflY (projectPeriod (periodVector k C)) := by
  rw [periodVector_conjMap hC]
  rfl

/-- **`refl_{y=0}` equivariance of the actual `descendedIntegral`**: at the conjugated points it is the
`PeriodTarget` reflection `(x,y,z) ↦ (x,-y,z)` of the original value. -/
theorem descendedIntegral_conjMap {k : ℕ} (hk : 2 ≤ k) (b w : PuncturedPlane k)
    (hb : starRingEnd ℂ b.val ∉ Surface.punctures k)
    (hw : starRingEnd ℂ w.val ∉ Surface.punctures k) :
    descendedIntegral hk ⟨starRingEnd ℂ b.val, hb⟩ ⟨starRingEnd ℂ w.val, hw⟩
      = PeriodTarget.reflY (descendedIntegral hk b w) := by
  obtain ⟨C, hCs, hCf, hCA⟩ := exists_connecting_chain hk b.property w.property
  rw [descendedIntegral_eq hk ⟨starRingEnd ℂ b.val, hb⟩ ⟨starRingEnd ℂ w.val, hw⟩ (Chain.conjMap C)
      (by rw [Chain.conjMap_start, hCs]) (by rw [Chain.conjMap_finish, hCf])
      (Chain.conjMap_avoids_punctures hCA),
    descendedIntegral_eq hk b w C hCs hCf hCA]
  exact projectPeriod_periodVector_conjMap hCA

/-! ### The holomorphic inversion chain map `w ↦ w⁻¹` (reciprocal; nonzero-domain restriction). -/

/-- Holomorphic reciprocal of a certified piece, on a piece avoiding `0` (real derivative
`-velocity/curve²` via `HasDerivWithinAt.inv`). -/
def Piece.invMap (p : Piece) (h0 : p.Avoids 0) : Piece where
  a := p.a
  b := p.b
  lt := p.lt
  curve := fun t => (p.curve t)⁻¹
  velocity := fun t => -(p.velocity t) / (p.curve t) ^ 2
  continuous_curve := p.continuous_curve.inv₀ (fun t ht => h0 t ht)
  continuous_velocity :=
    (p.continuous_velocity.neg).div (p.continuous_curve.pow 2)
      (fun t ht => pow_ne_zero 2 (h0 t ht))
  derivative := fun t ht => (p.derivative t ht).inv (h0 t ht)

@[simp] lemma Piece.invMap_start (p : Piece) (h0 : p.Avoids 0) :
    (Piece.invMap p h0).start = (p.start)⁻¹ := rfl

@[simp] lemma Piece.invMap_finish (p : Piece) (h0 : p.Avoids 0) :
    (Piece.invMap p h0).finish = (p.finish)⁻¹ := rfl

/-- Change of variables for the inversion map: `contour(invMap p, f) = contour(p, w ↦ -(w²)⁻¹·f(w⁻¹))`
(the factor `-(w²)⁻¹` is the complex derivative of the reciprocal map). -/
lemma Piece.invMap_contour (p : Piece) (h0 : p.Avoids 0) (f : ℂ → ℂ) :
    (Piece.invMap p h0).contour f = p.contour (fun w => -((w ^ 2)⁻¹) * f (w⁻¹)) := by
  simp only [Piece.contour, Piece.invMap]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

/-- Inversion of a chain, on a chain avoiding `0`. -/
def Chain.invMap (C : Chain) (h0 : C.Avoids 0) : Chain where
  n := C.n
  piece := fun i => Piece.invMap (C.piece i) (h0 i)
  matching := fun i => by
    show (Piece.invMap (C.piece i.castSucc) (h0 i.castSucc)).finish
        = (Piece.invMap (C.piece i.succ) (h0 i.succ)).start
    rw [Piece.invMap_finish, Piece.invMap_start, C.matching i]

@[simp] lemma Chain.invMap_start (C : Chain) (h0 : C.Avoids 0) :
    (Chain.invMap C h0).start = (C.start)⁻¹ := rfl

@[simp] lemma Chain.invMap_finish (C : Chain) (h0 : C.Avoids 0) :
    (Chain.invMap C h0).finish = (C.finish)⁻¹ := rfl

lemma Chain.invMap_contour (C : Chain) (h0 : C.Avoids 0) (f : ℂ → ℂ) :
    (Chain.invMap C h0).contour f = C.contour (fun w => -((w ^ 2)⁻¹) * f (w⁻¹)) := by
  simp only [Chain.contour, Chain.invMap]
  exact Finset.sum_congr rfl (fun i _ => Piece.invMap_contour (C.piece i) (h0 i) f)

/-- `invMap p` avoids `z` when `p` avoids `z⁻¹`. -/
lemma Piece.invMap_avoids {p : Piece} (h0 : p.Avoids 0) {z : ℂ} (h : p.Avoids z⁻¹) :
    (Piece.invMap p h0).Avoids z := by
  intro t ht he
  apply h t ht
  simp only [Piece.invMap] at he
  rw [← he, inv_inv]

/-- `invMap C` avoids `z` when `C` avoids `z⁻¹`. -/
lemma Chain.invMap_avoids {C : Chain} (h0 : C.Avoids 0) {z : ℂ} (h : C.Avoids z⁻¹) :
    (Chain.invMap C h0).Avoids z :=
  fun i => Piece.invMap_avoids (h0 i) (h i)

/-! ### Contour congruence on an avoided set, and the seam reflection `σ(w) = 1/conj w`. -/

/-- If `f` and `g` agree off `z` and `p` avoids `z`, their contours agree (the integrand only sees
curve points, all `≠ z`). -/
lemma Piece.contour_congr_of_avoids (p : Piece) {z : ℂ} (hz : p.Avoids z) {f g : ℂ → ℂ}
    (h : ∀ w, w ≠ z → f w = g w) : p.contour f = p.contour g := by
  simp only [Piece.contour]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le p.lt.le] at ht
  rw [h (p.curve t) (hz t ht)]

lemma Chain.contour_congr_of_avoids (C : Chain) {z : ℂ} (hz : C.Avoids z) {f g : ℂ → ℂ}
    (h : ∀ w, w ≠ z → f w = g w) : C.contour f = C.contour g := by
  simp only [Chain.contour]
  exact Finset.sum_congr rfl (fun i _ => Piece.contour_congr_of_avoids (C.piece i) (hz i) h)

/-- The puncture set is invariant under inversion. -/
lemma inv_mem_punctures {k : ℕ} {z : ℂ} (hz : z ∈ Surface.punctures k) :
    z⁻¹ ∈ Surface.punctures k := by
  have hz' : z ^ (2 * k) = -1 := hz
  show (z⁻¹) ^ (2 * k) = -1
  rw [inv_pow, hz']; simp

/-- `conjMap C` avoids `0` when `C` does (`conj 0 = 0`). -/
lemma Chain.conjMap_avoids_zero {C : Chain} (h0 : C.Avoids 0) : (Chain.conjMap C).Avoids 0 :=
  Chain.conjMap_avoids (by simpa using h0)

/-- The seam-reflection chain map `w ↦ (conj w)⁻¹`, realized as inversion ∘ conjugation. -/
def Chain.reflZMap (C : Chain) (h0 : C.Avoids 0) : Chain :=
  Chain.invMap (Chain.conjMap C) (Chain.conjMap_avoids_zero h0)

@[simp] lemma Chain.reflZMap_start (C : Chain) (h0 : C.Avoids 0) :
    (Chain.reflZMap C h0).start = (starRingEnd ℂ C.start)⁻¹ := rfl

@[simp] lemma Chain.reflZMap_finish (C : Chain) (h0 : C.Avoids 0) :
    (Chain.reflZMap C h0).finish = (starRingEnd ℂ C.finish)⁻¹ := rfl

/-- `reflZMap C` avoids all punctures when `C` does (punctures are σ-invariant: conj- and
inversion-invariant). -/
lemma Chain.reflZMap_avoids_punctures {k : ℕ} {C : Chain} (h0 : C.Avoids 0)
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    ∀ z ∈ Surface.punctures k, (Chain.reflZMap C h0).Avoids z := by
  intro z hz
  refine Chain.invMap_avoids (Chain.conjMap_avoids_zero h0) (Chain.conjMap_avoids ?_)
  exact hC _ (conj_mem_punctures (inv_mem_punctures hz))

/-- `coeff1` contour under the seam reflection: `conj` of the original (refl_z keeps `x`). -/
lemma contour_coeff1_reflZMap {k : ℕ} (hk : 2 ≤ k) {C : Chain} (h0 : C.Avoids 0) :
    (Chain.reflZMap C h0).contour (coeff1 k) = starRingEnd ℂ (C.contour (coeff1 k)) := by
  show (Chain.invMap (Chain.conjMap C) (Chain.conjMap_avoids_zero h0)).contour (coeff1 k) = _
  rw [Chain.invMap_contour, Chain.conjMap_contour]
  congr 1
  refine Chain.contour_congr_of_avoids C h0 (fun w hw => ?_)
  have key : -(((starRingEnd ℂ w) ^ 2)⁻¹) * coeff1 k ((starRingEnd ℂ w)⁻¹)
      = starRingEnd ℂ (coeff1 k w) := by
    rw [← inv_pow, ← coeff1_refl_z_pullback hk hw]; ring
  show starRingEnd ℂ (-(((starRingEnd ℂ w) ^ 2)⁻¹) * coeff1 k ((starRingEnd ℂ w)⁻¹)) = coeff1 k w
  rw [key, Complex.conj_conj]

/-- `coeff2` contour under the seam reflection: `conj` of the original (refl_z keeps `y`; the two `-1`s
cancel). -/
lemma contour_coeff2_reflZMap {k : ℕ} (hk : 2 ≤ k) {C : Chain} (h0 : C.Avoids 0) :
    (Chain.reflZMap C h0).contour (coeff2 k) = starRingEnd ℂ (C.contour (coeff2 k)) := by
  show (Chain.invMap (Chain.conjMap C) (Chain.conjMap_avoids_zero h0)).contour (coeff2 k) = _
  rw [Chain.invMap_contour, Chain.conjMap_contour]
  congr 1
  refine Chain.contour_congr_of_avoids C h0 (fun w hw => ?_)
  have key : -(((starRingEnd ℂ w) ^ 2)⁻¹) * coeff2 k ((starRingEnd ℂ w)⁻¹)
      = starRingEnd ℂ (coeff2 k w) := by
    rw [← inv_pow, ← coeff2_refl_z_pullback hk hw]; ring
  show starRingEnd ℂ (-(((starRingEnd ℂ w) ^ 2)⁻¹) * coeff2 k ((starRingEnd ℂ w)⁻¹)) = coeff2 k w
  rw [key, Complex.conj_conj]

/-- `coeff3` contour under the seam reflection: `-conj` of the original (the `diag(1,1,-1)` height
flip). -/
lemma contour_coeff3_reflZMap {k : ℕ} (hk : 2 ≤ k) {C : Chain} (h0 : C.Avoids 0)
    (hCA : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    (Chain.reflZMap C h0).contour (coeff3 k) = -starRingEnd ℂ (C.contour (coeff3 k)) := by
  show (Chain.invMap (Chain.conjMap C) (Chain.conjMap_avoids_zero h0)).contour (coeff3 k) = _
  rw [Chain.invMap_contour, Chain.conjMap_contour]
  have hcongr : C.contour (fun v => starRingEnd ℂ
        (-(((starRingEnd ℂ v) ^ 2)⁻¹) * coeff3 k ((starRingEnd ℂ v)⁻¹)))
      = C.contour (fun v => (-1 : ℂ) * coeff3 k v) := by
    refine Chain.contour_congr_of_avoids C h0 (fun w hw => ?_)
    have key : -(((starRingEnd ℂ w) ^ 2)⁻¹) * coeff3 k ((starRingEnd ℂ w)⁻¹)
        = -starRingEnd ℂ (coeff3 k w) := by
      rw [← inv_pow, ← coeff3_refl_z_pullback hk hw]; ring
    show starRingEnd ℂ (-(((starRingEnd ℂ w) ^ 2)⁻¹) * coeff3 k ((starRingEnd ℂ w)⁻¹))
        = (-1 : ℂ) * coeff3 k w
    rw [key, map_neg, Complex.conj_conj]; ring
  rw [hcongr, C.contour_const_mul (-1) (coeff3_integrableOn hCA), map_mul, map_neg, map_one,
    neg_one_mul]

/-- **`refl_{z=0}` on the real period vector**: `(x, y, z) ↦ (x, y, -z)` under the seam reflection. -/
lemma periodVector_reflZMap {k : ℕ} (hk : 2 ≤ k) {C : Chain} (h0 : C.Avoids 0)
    (hCA : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    periodVector k (Chain.reflZMap C h0)
      = ((periodVector k C).1, (periodVector k C).2.1, -(periodVector k C).2.2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show ((Chain.reflZMap C h0).contour (coeff1 k)).re = (C.contour (coeff1 k)).re
    rw [contour_coeff1_reflZMap hk, Complex.conj_re]
  · show ((Chain.reflZMap C h0).contour (coeff2 k)).re = (C.contour (coeff2 k)).re
    rw [contour_coeff2_reflZMap hk, Complex.conj_re]
  · show ((Chain.reflZMap C h0).contour (coeff3 k)).re = -(C.contour (coeff3 k)).re
    rw [contour_coeff3_reflZMap hk h0 hCA, Complex.neg_re, Complex.conj_re]

/-- Reflection action on `PeriodTarget` for `refl_{z=0}`: negate the vertical `AddCircle` coordinate. -/
def PeriodTarget.reflZ (p : PeriodTarget) : PeriodTarget := (p.1, p.2.1, -p.2.2)

/-- `projectPeriod ∘ periodVector` of the seam-reflected chain = the `refl_z` action on the original. -/
lemma projectPeriod_periodVector_reflZMap {k : ℕ} (hk : 2 ≤ k) {C : Chain} (h0 : C.Avoids 0)
    (hCA : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    projectPeriod (periodVector k (Chain.reflZMap C h0))
      = PeriodTarget.reflZ (projectPeriod (periodVector k C)) := by
  rw [periodVector_reflZMap hk h0 hCA]
  simp only [projectPeriod, PeriodTarget.reflZ, QuotientAddGroup.mk_neg]

/-- A connecting chain avoiding punctures AND `0`, for nonzero endpoints. -/
theorem exists_connecting_chain_ne_zero {k : ℕ} (hk : 2 ≤ k) {x y : ℂ}
    (hx : x ∉ Surface.punctures k) (hy : y ∉ Surface.punctures k) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ∃ C : Chain, C.start = x ∧ C.finish = y ∧
      (∀ z ∈ Surface.punctures k, C.Avoids z) ∧ C.Avoids 0 := by
  obtain ⟨C, hs, ht, hA⟩ := exists_chain_avoiding_finset (insert 0 (punctureFinset k)) x y
    (by simp only [Finset.mem_insert, not_or]
        exact ⟨hx0, fun h => hx ((mem_punctureFinset hk).mp h)⟩)
    (by simp only [Finset.mem_insert, not_or]
        exact ⟨hy0, fun h => hy ((mem_punctureFinset hk).mp h)⟩)
  exact ⟨C, hs, ht,
    fun z hz => hA z (Finset.mem_insert_of_mem ((mem_punctureFinset hk).mpr hz)),
    hA 0 (Finset.mem_insert_self 0 _)⟩

/-- **`refl_{z=0}` equivariance of the actual `descendedIntegral`** (seam reflection `σ(w)=1/conj w`):
at the seam-reflected (nonzero) points it is the `PeriodTarget.reflZ` action `(x,y,z)↦(x,y,-z)` of the
original value. -/
theorem descendedIntegral_reflZMap {k : ℕ} (hk : 2 ≤ k) (b w : PuncturedPlane k)
    (hb0 : b.val ≠ 0) (hw0 : w.val ≠ 0)
    (hb : (starRingEnd ℂ b.val)⁻¹ ∉ Surface.punctures k)
    (hw : (starRingEnd ℂ w.val)⁻¹ ∉ Surface.punctures k) :
    descendedIntegral hk ⟨(starRingEnd ℂ b.val)⁻¹, hb⟩ ⟨(starRingEnd ℂ w.val)⁻¹, hw⟩
      = PeriodTarget.reflZ (descendedIntegral hk b w) := by
  obtain ⟨C, hCs, hCf, hCA, hC0⟩ := exists_connecting_chain_ne_zero hk b.property w.property hb0 hw0
  rw [descendedIntegral_eq hk ⟨(starRingEnd ℂ b.val)⁻¹, hb⟩ ⟨(starRingEnd ℂ w.val)⁻¹, hw⟩
      (Chain.reflZMap C hC0)
      (by rw [Chain.reflZMap_start, hCs]) (by rw [Chain.reflZMap_finish, hCf])
      (Chain.reflZMap_avoids_punctures hC0 hCA),
    descendedIntegral_eq hk b w C hCs hCf hCA]
  exact projectPeriod_periodVector_reflZMap hk hC0 hCA

/-! ### The screw deck `w ↦ a·(conj w)⁻¹` (`a^k = -1`), realized as rotation ∘ seam reflection.

On the chain level the map is `smul a (reflZMap C)`. The condition `a^k = -1`
implies `a^(2k) = 1`, and its vertical sign cancels the seam reflection's sign.
The resulting action on integral differences is `PeriodTarget.rotate a`, with
horizontal factor `a⁻¹` and unchanged vertical component. This statement does
not choose a particular root `a` or determine an absolute vertical translation. -/

/-- `projectPeriod ∘ periodVector` of the screwed chain = the rotation `PeriodTarget.rotate a` on the
original (horizontal by `a⁻¹`, vertical kept — the `a^k=-1` vertical flip cancels refl_z's). -/
lemma projectPeriod_periodVector_screwMap {k : ℕ} (hk : 2 ≤ k) {a : ℂ} (hak : a ^ k = -1)
    {C : Chain} (h0 : C.Avoids 0) (hCA : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    projectPeriod (periodVector k (Chain.smul a (Chain.reflZMap C h0)))
      = PeriodTarget.rotate a (projectPeriod (periodVector k C)) := by
  have ha2k : a ^ (2 * k) = 1 := by rw [mul_comm, pow_mul, hak]; norm_num
  have hCD := Chain.reflZMap_avoids_punctures h0 hCA
  have hh := periodVector_horiz_smul (by omega) ha2k hCD
  rw [contour_coeff1_reflZMap hk, contour_coeff2_reflZMap hk] at hh
  rw [Complex.conj_re, Complex.conj_re] at hh
  have hv : (Chain.smul a (Chain.reflZMap C h0)).contour (coeff3 k)
      = starRingEnd ℂ (C.contour (coeff3 k)) := by
    rw [contour_coeff3_smul (by omega) ha2k hCD, contour_coeff3_reflZMap hk h0 hCA, hak]; ring
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · have := congrArg Complex.re hh
    simpa [projectPeriod, periodVector, PeriodTarget.rotate, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] using this
  · have := congrArg Complex.im hh
    simpa [projectPeriod, periodVector, PeriodTarget.rotate, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] using this
  · simp only [projectPeriod, periodVector, PeriodTarget.rotate, hv, Complex.conj_re]

/-- Screw equivariance of `descendedIntegral` for `w ↦ a·(conj w)⁻¹`, `a^k = -1`.
Transforming both nonzero endpoints gives the action `PeriodTarget.rotate a` on
integral differences. Any absolute translation cancels in this difference;
its value is not determined by this theorem. -/
theorem descendedIntegral_screwMap {k : ℕ} (hk : 2 ≤ k) {a : ℂ} (hak : a ^ k = -1)
    (b w : PuncturedPlane k) (hb0 : b.val ≠ 0) (hw0 : w.val ≠ 0)
    (hb : a * (starRingEnd ℂ b.val)⁻¹ ∉ Surface.punctures k)
    (hw : a * (starRingEnd ℂ w.val)⁻¹ ∉ Surface.punctures k) :
    descendedIntegral hk ⟨a * (starRingEnd ℂ b.val)⁻¹, hb⟩ ⟨a * (starRingEnd ℂ w.val)⁻¹, hw⟩
      = PeriodTarget.rotate a (descendedIntegral hk b w) := by
  obtain ⟨C, hCs, hCf, hCA, hC0⟩ := exists_connecting_chain_ne_zero hk b.property w.property hb0 hw0
  have ha2k : a ^ (2 * k) = 1 := by rw [mul_comm, pow_mul, hak]; norm_num
  have hsmulA : ∀ z ∈ Surface.punctures k, (Chain.smul a (Chain.reflZMap C hC0)).Avoids z :=
    Chain.smul_avoids_punctures (by omega) ha2k (Chain.reflZMap_avoids_punctures hC0 hCA)
  rw [descendedIntegral_eq hk ⟨a * (starRingEnd ℂ b.val)⁻¹, hb⟩ ⟨a * (starRingEnd ℂ w.val)⁻¹, hw⟩
      (Chain.smul a (Chain.reflZMap C hC0))
      (by rw [Chain.smul_start, Chain.reflZMap_start, hCs])
      (by rw [Chain.smul_finish, Chain.reflZMap_finish, hCf]) hsmulA,
    descendedIntegral_eq hk b w C hCs hCf hCA]
  exact projectPeriod_periodVector_screwMap hk hak hC0 hCA

end KsIndex.KarcherData
