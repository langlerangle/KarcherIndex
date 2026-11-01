module

/-
Natural single-disk test spaces and mixed-boundary index transport.

`NatCc k b₁ b₀` imposes natural boundary conditions on both arc families.
The chart screw `w ↦ e^{iπ/k} w` exchanges the flags, preserves the form `Qd k`,
and commutes with the rotation characters. Consequently `seamNat_mixed`
identifies the two mixed indices on these natural spaces.

The separately defined `SingleCc` uses a different reflection encoding on
arc 1. In particular, its `b₁ = false` condition includes whole-circle boundary
vanishing, so it must not be treated as the natural mixed domain merely by
swapping flags. `ArcEncodingDensity` names an explicit index-equality
hypothesis between these domains; this file does not prove it, and its mixed
case has the obstruction described below.

The established m=2 index route uses the distinct `ReflEncodingDensity`
hypothesis, discharged in `D5Discharge`, rather than `ArcEncodingDensity`.
-/
public import KsIndexLean.SingleDisk

@[expose] public section


noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped ContDiff

namespace KsIndex.SingleDisk

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.FormIndex KsIndex.Twisted
  KsIndex.Bracket KsIndex.SingleDiskBridge KsIndex.GradOrtho

variable {k : ℕ}

/-! ### The closed `arc_1` family and the generic arc condition -/

/-- The closed complement of the open slit: `{|w| = 1, Re(w^k) ≥ 0}` (`arc_1` with its endpoints,
the punctures). -/
def slitC (k : ℕ) : Set ℂ := {w | ‖w‖ = 1 ∧ 0 ≤ (w ^ k).re}

lemma arc_one_subset_slitC : arc k 1 ⊆ slitC k := fun w hw => by
  obtain ⟨h1, h2⟩ := hw
  refine ⟨h1, ?_⟩
  simp only [pow_one, neg_one_mul, neg_lt_zero] at h2
  exact h2.le

lemma punctures_subset_slitC (hk : 1 ≤ k) : punctures k ⊆ slitC k := by
  intro p hp
  have hp' : p ^ (2 * k) = -1 := hp
  have hnorm : ‖p‖ = 1 := by
    have h1 : ‖p‖ ^ (2 * k) = 1 := by rw [← norm_pow, hp', norm_neg, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg p) (by omega)).mp h1
  refine ⟨hnorm, ?_⟩
  have hsq : (p ^ k) * (p ^ k) = -1 := by rw [← pow_add, ← two_mul, hp']
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.one_re, Complex.neg_im,
    Complex.one_im, neg_zero] at hre him
  nlinarith [sq_nonneg ((p ^ k).re), sq_nonneg ((p ^ k).im)]

/-- Vanishing near a set (one copy). -/
def SuppAwaySet (S : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∃ ε > 0, ∀ w, (∃ p ∈ S, ‖w - p‖ < ε) → f w = 0

/-- The natural condition on an arc family `A` with closure `S`: Neumann (`true`) = one-sided
smooth extension at every point of `A`; Dirichlet (`false`) = vanishing near `S`. -/
def ArcCond (A S : Set ℂ) : Bool → (ℂ → ℂ) → Prop
  | true, f => ∀ w ∈ A, OneSided f w
  | false, f => SuppAwaySet S f

lemma arcCond_zero (A S : Set ℂ) (b : Bool) : ArcCond A S b 0 := by
  cases b
  · exact ⟨1, one_pos, fun _ _ => rfl⟩
  · exact fun w _ => oneSided_zero w

lemma arcCond_add {A S : Set ℂ} {b : Bool} {f g : ℂ → ℂ} (hf : ArcCond A S b f)
    (hg : ArcCond A S b g) : ArcCond A S b (f + g) := by
  cases b
  · obtain ⟨ε₁, h₁, hf⟩ := hf
    obtain ⟨ε₂, h₂, hg⟩ := hg
    refine ⟨min ε₁ ε₂, lt_min h₁ h₂, fun w ⟨p, hp, hwp⟩ => ?_⟩
    simp only [Pi.add_apply, hf w ⟨p, hp, lt_of_lt_of_le hwp (min_le_left _ _)⟩,
      hg w ⟨p, hp, lt_of_lt_of_le hwp (min_le_right _ _)⟩, add_zero]
  · exact fun w hw => oneSided_add (hf w hw) (hg w hw)

lemma arcCond_smul {A S : Set ℂ} {b : Bool} (c : ℂ) {f : ℂ → ℂ} (hf : ArcCond A S b f) :
    ArcCond A S b (c • f) := by
  cases b
  · obtain ⟨ε, hε, hf⟩ := hf
    exact ⟨ε, hε, fun w hw => by simp only [Pi.smul_apply, hf w hw, smul_zero]⟩
  · exact fun w hw => oneSided_smul c (hf w hw)

/-- `Arc0Cond` is the generic condition on `(arc_0, slit)`. -/
lemma arc0Cond_eq (k : ℕ) (b : Bool) (f : ℂ → ℂ) :
    Arc0Cond k b f ↔ ArcCond (arc k 0) (slit k) b f := by
  cases b <;> exact Iff.rfl

/-! ### The natural single-disk spaces -/

/-- The arc-uniform single-disk package: natural condition `b₁` on `arc_1`, `b₀` on `arc_0`. -/
def IsSmoothNat (k : ℕ) (b₁ b₀ : Bool) (f : ℂ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ f disk
    ∧ ArcCond (arc k 1) (slitC k) b₁ f
    ∧ ArcCond (arc k 0) (slit k) b₀ f
    ∧ (∀ w, 1 < ‖w‖ → f w = 0)
    ∧ SuppAwayP1 k f

/-- **The natural single-disk test space** `NatCc k b₁ b₀`. -/
def NatCc (k : ℕ) (b₁ b₀ : Bool) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | IsSmoothNat k b₁ b₀ f}
  zero_mem' := ⟨contDiffOn_const, arcCond_zero _ _ _, arcCond_zero _ _ _, fun _ _ => rfl,
    ⟨1, one_pos, fun _ _ => rfl⟩⟩
  add_mem' := by
    rintro f g ⟨f1, f2, f3, f4, ⟨ε₁, h₁, f5⟩⟩ ⟨g1, g2, g3, g4, ⟨ε₂, h₂, g5⟩⟩
    refine ⟨f1.add g1, arcCond_add f2 g2, arcCond_add f3 g3, fun w hw => ?_,
      ⟨min ε₁ ε₂, lt_min h₁ h₂, fun w ⟨p, hp, hwp⟩ => ?_⟩⟩
    · simp only [Pi.add_apply, f4 w hw, g4 w hw, add_zero]
    · simp only [Pi.add_apply, f5 w ⟨p, hp, lt_of_lt_of_le hwp (min_le_left _ _)⟩,
        g5 w ⟨p, hp, lt_of_lt_of_le hwp (min_le_right _ _)⟩, add_zero]
  smul_mem' := by
    rintro c f ⟨f1, f2, f3, f4, ⟨ε, hε, f5⟩⟩
    refine ⟨f1.const_smul c, arcCond_smul c f2, arcCond_smul c f3, fun w hw => ?_,
      ⟨ε, hε, fun w hw => ?_⟩⟩
    · simp only [Pi.smul_apply, f4 w hw, smul_zero]
    · simp only [Pi.smul_apply, f5 w hw, smul_zero]

lemma mem_NatCc {b₁ b₀ : Bool} {f : ℂ → ℂ} : f ∈ NatCc k b₁ b₀ ↔ IsSmoothNat k b₁ b₀ f :=
  Iff.rfl

/-! ### The screw -/

/-- The screw unit `e^{iπ/k}`: `screwUnit k ^ k = −1`. -/
def screwUnit (k : ℕ) : ℂ := exp (((π / k : ℝ)) * I)

lemma norm_screwUnit (k : ℕ) : ‖screwUnit k‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma screwUnit_pow (hk : 1 ≤ k) : screwUnit k ^ k = -1 := by
  unfold screwUnit
  rw [← Complex.exp_nat_mul]
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have : (k : ℂ) * (((π / k : ℝ)) * I) = π * I := by
    push_cast
    field_simp
  rw [this, Complex.exp_pi_mul_I]

/-- Rotation by a unimodular `a` with `a^k = −1` exchanges the two arc families. -/
lemma mul_mem_arc_zero {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = -1) {w : ℂ} (hw : w ∈ arc k 1) :
    a * w ∈ arc k 0 := by
  obtain ⟨h1, h2⟩ := hw
  refine ⟨by rw [norm_mul, ha, h1, one_mul], ?_⟩
  simp only [pow_one, neg_one_mul, neg_lt_zero] at h2
  simp only [mul_pow, hak, neg_one_mul, Complex.neg_re, pow_zero, one_mul]
  linarith

lemma mul_mem_arc_one {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = -1) {w : ℂ} (hw : w ∈ arc k 0) :
    a * w ∈ arc k 1 := by
  obtain ⟨h1, h2⟩ := hw
  refine ⟨by rw [norm_mul, ha, h1, one_mul], ?_⟩
  simp only [pow_zero, one_mul] at h2
  simp only [mul_pow, hak, neg_one_mul, Complex.neg_re, pow_one]
  linarith

lemma mul_mem_slit {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = -1) {p : ℂ} (hp : p ∈ slitC k) :
    a * p ∈ slit k := by
  obtain ⟨h1, h2⟩ := hp
  refine ⟨by rw [norm_mul, ha, h1, one_mul], ?_⟩
  simp only [mul_pow, hak, neg_one_mul, Complex.neg_re]
  linarith

lemma mul_mem_slitC {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = -1) {p : ℂ} (hp : p ∈ slit k) :
    a * p ∈ slitC k := by
  obtain ⟨h1, h2⟩ := hp
  refine ⟨by rw [norm_mul, ha, h1, one_mul], ?_⟩
  simp only [mul_pow, hak, neg_one_mul, Complex.neg_re]
  linarith

lemma mul_mem_punctures {a : ℂ} (hak : a ^ k = -1) {p : ℂ} (hp : p ∈ punctures k) :
    a * p ∈ punctures k := by
  have hp' : p ^ (2 * k) = -1 := hp
  change (a * p) ^ (2 * k) = -1
  rw [mul_pow, mul_comm 2 k, pow_mul, hak, neg_one_sq, one_mul, mul_comm k 2, hp']

/-- One-sided smoothness transports along `w ↦ a w`. -/
lemma oneSided_rot {a : ℂ} (ha : ‖a‖ = 1) {f : ℂ → ℂ} {w : ℂ} (hf : OneSided f (a * w)) :
    OneSided (fun z => f (a * z)) w := by
  obtain ⟨F, hF, hFe⟩ := hf
  have hmul : ContDiffAt ℝ ∞ (fun z : ℂ => a * z) w := contDiffAt_const.mul contDiffAt_id
  refine ⟨fun z => F (a * z), hF.comp w hmul, ?_⟩
  have ht : Tendsto (fun z : ℂ => a * z) (𝓝 w) (𝓝 (a * w)) := hmul.continuousAt
  filter_upwards [ht.eventually hFe] with z hz hzd
  exact hz (by rw [mem_disk_iff, norm_mul, ha, one_mul]; exact mem_disk_iff.mp hzd)

lemma suppAwaySet_rot {S T : Set ℂ} {a : ℂ} (ha : ‖a‖ = 1) (hST : ∀ p ∈ T, a * p ∈ S)
    {f : ℂ → ℂ} (hf : SuppAwaySet S f) : SuppAwaySet T (fun z => f (a * z)) := by
  obtain ⟨ε, hε, hf⟩ := hf
  refine ⟨ε, hε, fun w ⟨p, hp, hwp⟩ => hf (a * w) ⟨a * p, hST p hp, ?_⟩⟩
  rw [← mul_sub, norm_mul, ha, one_mul]; exact hwp

lemma arcCond_rot {A A' S S' : Set ℂ} {b : Bool} {a : ℂ} (ha : ‖a‖ = 1)
    (hA : ∀ w ∈ A', a * w ∈ A) (hS : ∀ p ∈ S', a * p ∈ S) {f : ℂ → ℂ}
    (hf : ArcCond A S b f) : ArcCond A' S' b (fun z => f (a * z)) := by
  cases b
  · exact suppAwaySet_rot ha hS hf
  · exact fun w hw => oneSided_rot ha (hf (a * w) (hA w hw))

/-- **The screw exchanges the natural spaces**: for unimodular `a` with `a^k = −1`,
`rot1 a` maps `NatCc k b₁ b₀` into `NatCc k b₀ b₁`. -/
lemma rot1_mem_NatCc {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = -1) {b₁ b₀ : Bool} {f : ℂ → ℂ}
    (hf : f ∈ NatCc k b₁ b₀) : rot1 a f ∈ NatCc k b₀ b₁ := by
  obtain ⟨f1, f2, f3, f4, ⟨ε, hε, f5⟩⟩ := mem_NatCc.mp hf
  have hmaps : Set.MapsTo (fun z : ℂ => a * z) disk disk := fun z hz => by
    rw [mem_disk_iff, norm_mul, ha, one_mul]; exact mem_disk_iff.mp hz
  refine ⟨?_, ?_, ?_, fun w hw => ?_, ⟨ε, hε, fun w ⟨p, hp, hwp⟩ => ?_⟩⟩
  · exact f1.comp (contDiffOn_const.mul contDiffOn_id) hmaps
  · exact arcCond_rot ha (fun w hw => mul_mem_arc_zero ha hak hw)
      (fun p hp => mul_mem_slit ha hak hp) f3
  · exact arcCond_rot ha (fun w hw => mul_mem_arc_one ha hak hw)
      (fun p hp => mul_mem_slitC ha hak hp) f2
  · exact f4 _ (by rw [norm_mul, ha, one_mul]; exact hw)
  · exact f5 (a * w) ⟨a * p, mul_mem_punctures hak hp, by
      rw [← mul_sub, norm_mul, ha, one_mul]; exact hwp⟩

/-- Single-disk rotations commute, so `rot1 a` preserves every `rot1 c`-eigenspace. -/
lemma rot1_mem_eigen (a : ℂ) {c μ : ℂ} {f : ℂ → ℂ}
    (hf : f ∈ Module.End.eigenspace (rot1 c) μ) :
    rot1 a f ∈ Module.End.eigenspace (rot1 c) μ := by
  rw [Module.End.mem_eigenspace_iff] at hf ⊢
  have hcomm : rot1 c (rot1 a f) = rot1 a (rot1 c f) := by
    funext w; simp only [rot1_apply, mul_left_comm]
  rw [hcomm, hf, map_smul]

lemma rot1_rot1_inv {a : ℂ} (ha : a ≠ 0) (f : ℂ → ℂ) : rot1 a (rot1 a⁻¹ f) = f := by
  funext w; simp only [rot1_apply]; rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]

/-! ### Rotation invariance of the one-disk form -/

/-- The disk integral of a real function is invariant under rotation by a circle element. -/
lemma setIntegral_disk_comp_mul_real (a : Circle) (F : ℂ → ℝ) :
    ∫ w in disk, F ((a : ℂ) * w) = ∫ w in disk, F w := by
  have hmp : MeasurePreserving (rotation a) volume volume := (rotation a).measurePreserving
  have hemb : MeasurableEmbedding (rotation a) := (rotation a).toHomeomorph.measurableEmbedding
  have hpre : (rotation a) ⁻¹' disk = disk := by
    ext w
    simp only [Set.mem_preimage, rotation_apply, disk, Metric.mem_ball, dist_zero_right,
      norm_mul, Circle.norm_coe, one_mul]
  have h := hmp.setIntegral_preimage_emb hemb F disk
  rw [hpre] at h
  simpa only [rotation_apply] using h

lemma gradSq_comp_mul {f : ℂ → ℂ} {a : ℂ} (ha : ‖a‖ = 1) {w : ℂ}
    (hf : DifferentiableAt ℝ f (a * w)) :
    gradSq (fun z => f (a * z)) w = gradSq f (a * w) := by
  have h := gradInner_comp_mul ha hf hf
  rw [gradInner_self, gradInner_self] at h
  exact_mod_cast h

/-- **Rotation invariance of the one-disk form** under any unimodular rotation. -/
lemma Qd_rot1 (hk : 2 ≤ k) {a : ℂ} (ha : ‖a‖ = 1) {f : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f disk) :
    Qd k (rot1 a f) = Qd k f := by
  let ac : Circle := ⟨a, mem_sphere_zero_iff_norm.mpr ha⟩
  have hac : (ac : ℂ) = a := rfl
  unfold Qd
  rw [dirichletG_collapse (by omega), dirichletG_collapse (by omega),
    potentialG_collapse hk, potentialG_collapse hk]
  have h1 : ∫ w in disk, gradSq (rot1 a f) w = ∫ w in disk, gradSq f w := by
    rw [← setIntegral_disk_comp_mul_real ac (gradSq f), hac]
    refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
    have haw : a * w ∈ disk := by
      rw [mem_disk_iff, norm_mul, ha, one_mul]; exact mem_disk_iff.mp hw
    exact gradSq_comp_mul ha
      ((hf.contDiffAt (Metric.isOpen_ball.mem_nhds haw)).differentiableAt
        (by simp))
  have h2 : ∫ w in disk, potV k w * ‖rot1 a f w‖ ^ 2 = ∫ w in disk, potV k w * ‖f w‖ ^ 2 := by
    rw [← setIntegral_disk_comp_mul_real ac (fun w => potV k w * ‖f w‖ ^ 2), hac]
    refine setIntegral_congr_fun measurableSet_disk fun w _ => ?_
    simp only [rot1_apply, KsIndex.ThetaOrtho.potV_rotation k ha]
  rw [h1, h2]

/-! ### The screw transport and the mixed congruence -/

/-- **Screw transport.**  On the natural spaces the chart screw is a plain index transport:
`ind(Qd k)` on `NatCc k b₁ b₀ ⊓ E_rot1(c, μ)` equals that on `NatCc k b₀ b₁ ⊓ E_rot1(c, μ)`. -/
theorem screw_transport (hk : 2 ≤ k) (b₁ b₀ : Bool) {c μ : ℂ} :
    formIndex (Qd k) (NatCc k b₁ b₀ ⊓ Module.End.eigenspace (rot1 c) μ)
      = formIndex (Qd k) (NatCc k b₀ b₁ ⊓ Module.End.eigenspace (rot1 c) μ) := by
  have ha := norm_screwUnit k
  have hak := screwUnit_pow (k := k) (by omega)
  have ha0 : screwUnit k ≠ 0 := by
    intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  have hai : ‖(screwUnit k)⁻¹‖ = 1 := by rw [norm_inv, ha, inv_one]
  have haik : (screwUnit k)⁻¹ ^ k = -1 := by rw [inv_pow, hak, inv_neg, inv_one]
  refine formIndex_transport_surj (rot1 (screwUnit k)) (fun f hf => ?_) (fun g hg => ?_)
    (fun f hf => ?_) (Qd_zero k)
  · exact Submodule.mem_inf.mpr ⟨rot1_mem_NatCc ha hak hf.1, rot1_mem_eigen _ hf.2⟩
  · refine ⟨rot1 (screwUnit k)⁻¹ g, ?_, rot1_rot1_inv ha0 g⟩
    exact Submodule.mem_inf.mpr ⟨rot1_mem_NatCc hai haik hg.1, rot1_mem_eigen _ hg.2⟩
  · exact (Qd_rot1 hk ha hf.1.1).symm

/-- The natural seam quantities of class `r`. -/
def seamNat (k : ℕ) (b₁ b₀ : Bool) (r : ℕ) : ℕ∞ :=
  formIndex (Qd k) (NatCc k b₁ b₀ ⊓ Erot1 k r)

/-- **The mixed congruence on the natural spaces**: `ind_{DN,j} = ind_{ND,j}`, by the screw. -/
theorem seamNat_mixed (hk : 2 ≤ k) (r : ℕ) : seamNat k false true r = seamNat k true false r :=
  screw_transport hk false true

/-- Equality of reflection-encoded (`SingleCc`) and natural (`NatCc`)
single-disk indices in every flag and rotation class, kept as an explicit hypothesis.

This hypothesis is believed to be unsatisfiable in the `(false, true)` case:
`IsSmoothS` requires whole-circle boundary vanishing when `b₁ = false`, rather
than only the intended Dirichlet arc condition. This is a warning about the
encoding; no formal impossibility theorem is asserted here. In particular,
`mixed_congruence` below must not be cited as an unconditional mixed-domain result.
The unconditional natural-space congruence is `seamNat_mixed`.

The m=2 index theorem does not require this hypothesis: `indSurface_two_val_refl`
uses only `ReflEncodingDensity`, and `KsIndex.Trace.indSurface_two_val_final` in `D5Discharge`
discharges that distinct hypothesis. -/
def ArcEncodingDensity (k : ℕ) : Prop :=
  ∀ (b₁ b₀ : Bool) (r : ℕ), seam k b₁ b₀ r = seamNat k b₁ b₀ r

/-- Conditional equality of the two mixed reflection-encoded seam indices.
The hypothesis `ArcEncodingDensity` is explicit and has the encoding caveat
above. For the unconditional comparison on natural test spaces, use
`seamNat_mixed`. This conditional theorem is not used to discharge the m=2
index formula. -/
theorem mixed_congruence (hk : 2 ≤ k) (hd : ArcEncodingDensity k) (r : ℕ) :
    seam k false true r = seam k true false r := by
  rw [hd false true r, hd true false r]
  exact seamNat_mixed hk r

end KsIndex.SingleDisk
