module

public import KsIndexLean.SingleDiskNat
public import KsIndexLean.SingleDiskBridge
public import KsIndexLean.TwistTransport

@[expose] public section


/-!
# Rotation invariance of the compact cores

For a unit complex number `a` satisfying `a^k = 1`, precomposition by
multiplication by `a` preserves `SingleCc`, `NatCc`, and `ReflCc` with their
boundary flags or reflection parameters unchanged. The proofs transport the
arc, slit, puncture-neighborhood, and regularity conditions defining each core.
Circle reflection commutes with this unimodular rotation. Eigenspace
membership under rotation is handled separately by `rot1_mem_eigen`.
-/

open Complex Real MeasureTheory Filter Topology Metric
open scoped ContDiff
noncomputable section
namespace KsIndex.SingleDisk
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.FormIndex
open KsIndex.Bracket KsIndex.SingleDiskBridge

variable {k : ℕ}

/-! ### Same-arc transports (`a^k = 1` preserves every re-sign condition) -/

/-- Rotation with `a^k = 1` preserves each arc family (both `n`). -/
lemma mul_mem_arc_same {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = 1) {n : ℕ}
    {w : ℂ} (hw : w ∈ arc k n) : a * w ∈ arc k n := by
  obtain ⟨h1, h2⟩ := hw
  refine ⟨by rw [norm_mul, ha, h1, one_mul], ?_⟩
  rwa [mul_pow, hak, one_mul]

/-- Rotation with `a^k = 1` preserves the closed slit. -/
lemma mul_mem_slit_same {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = 1) {p : ℂ}
    (hp : p ∈ Bracket.slit k) : a * p ∈ Bracket.slit k := by
  obtain ⟨h1, h2⟩ := hp
  refine ⟨by rw [norm_mul, ha, h1, one_mul], ?_⟩
  rwa [mul_pow, hak, one_mul]

/-- Rotation with `a^k = 1` preserves the closed co-slit. -/
lemma mul_mem_slitC_same {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = 1) {p : ℂ}
    (hp : p ∈ slitC k) : a * p ∈ slitC k := by
  obtain ⟨h1, h2⟩ := hp
  refine ⟨by rw [norm_mul, ha, h1, one_mul], ?_⟩
  rwa [mul_pow, hak, one_mul]

/-- Rotation with `a^k = 1` permutes the punctures. -/
lemma mul_mem_punctures_same {a : ℂ} (hak : a ^ k = 1) {p : ℂ}
    (hp : p ∈ punctures k) : a * p ∈ punctures k := by
  have hp' : p ^ (2 * k) = -1 := hp
  change (a * p) ^ (2 * k) = -1
  rw [mul_pow, mul_comm 2 k, pow_mul, hak, one_pow, one_mul, mul_comm k 2, hp']

/-! ### σ and `refl` commute with unimodular rotations -/

/-- The circle reflection commutes with unimodular rotation:
`σ(a·z) = a·σ(z)` (since `1/ā = a` on the unit circle). -/
lemma σ_unimodular_mul {a : ℂ} (ha : ‖a‖ = 1) (z : ℂ) :
    Bracket.σ (a * z) = a * Bracket.σ z := by
  have hconj : a * (starRingEnd ℂ) a = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have hca : ((starRingEnd ℂ) a)⁻¹ = a := by
    rw [← inv_eq_of_mul_eq_one_right hconj, inv_inv]
  rw [Bracket.σ_apply, Bracket.σ_apply, map_mul, one_div, one_div, mul_inv, hca]

/-- `refl s` commutes with unimodular rotation. -/
lemma refl_rot1 {a : ℂ} (ha : ‖a‖ = 1) (s : ℂ) (f : ℂ → ℂ) :
    refl s (rot1 a f) = rot1 a (refl s f) := by
  funext z
  simp only [refl, rot1_apply, norm_mul, ha, one_mul, σ_unimodular_mul ha]

/-! ### Rotation preserves each core -/

/-- Flag-preserving rotation equivariance of the natural
core: for unimodular `a` with `a^k = 1`, `rot1 a` maps `NatCc k b₁ b₀` into
itself. -/
theorem rot1_mem_natCc_same {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = 1)
    {b₁ b₀ : Bool} {f : ℂ → ℂ} (hf : f ∈ NatCc k b₁ b₀) :
    rot1 a f ∈ NatCc k b₁ b₀ := by
  obtain ⟨f1, f2, f3, f4, ⟨ε, hε, f5⟩⟩ := mem_NatCc.mp hf
  have hmaps : Set.MapsTo (fun z : ℂ => a * z) disk disk := fun z hz => by
    rw [mem_disk_iff, norm_mul, ha, one_mul]
    exact mem_disk_iff.mp hz
  refine ⟨f1.comp (contDiffOn_const.mul contDiffOn_id) hmaps, ?_, ?_,
    fun w hw => ?_, ⟨ε, hε, fun w ⟨p, hp, hwp⟩ => ?_⟩⟩
  · exact arcCond_rot ha (fun w hw => mul_mem_arc_same ha hak hw)
      (fun p hp => mul_mem_slitC_same ha hak hp) f2
  · exact arcCond_rot ha (fun w hw => mul_mem_arc_same ha hak hw)
      (fun p hp => mul_mem_slit_same ha hak hp) f3
  · exact f4 (a * w) (by rw [norm_mul, ha, one_mul]; exact hw)
  · exact f5 (a * w) ⟨a * p, mul_mem_punctures_same hak hp, by
      rw [← mul_sub, norm_mul, ha, one_mul]; exact hwp⟩

/-- Flag-preserving rotation equivariance of the
mixed-flag core. -/
theorem rot1_mem_singleCc_same {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = 1)
    {b₁ b₀ : Bool} {f : ℂ → ℂ} (hf : f ∈ SingleCc k b₁ b₀) :
    rot1 a f ∈ SingleCc k b₁ b₀ := by
  obtain ⟨f1, f2, f3, f4, f5, ⟨ε, hε, f6⟩⟩ := mem_SingleCc.mp hf
  have hmaps : Set.MapsTo (fun z : ℂ => a * z) disk disk := fun z hz => by
    rw [mem_disk_iff, norm_mul, ha, one_mul]
    exact mem_disk_iff.mp hz
  refine ⟨f1.comp (contDiffOn_const.mul contDiffOn_id) hmaps, ?_, ?_,
    fun w hw => ?_, fun hb w hw => ?_, ⟨ε, hε, fun w ⟨p, hp, hwp⟩ => ?_⟩⟩
  · -- arc-1 reflection germ, via refl∘rot commutation + same-arc transport
    intro w hw
    rw [refl_rot1 ha]
    exact (f2 (a * w) (mul_mem_arc_same ha hak hw)).comp w
      ((contDiff_const.mul contDiff_id).contDiffAt)
  · -- Arc0Cond via the generic transport with same-arc/slit lemmas
    rw [arc0Cond_eq] at f3 ⊢
    exact arcCond_rot ha (fun w hw => mul_mem_arc_same ha hak hw)
      (fun p hp => mul_mem_slit_same ha hak hp) f3
  · exact f4 (a * w) (by rw [norm_mul, ha, one_mul]; exact hw)
  · exact f5 hb (a * w) (by rw [norm_mul, ha, one_mul]; exact hw)
  · exact f6 (a * w) ⟨a * p, mul_mem_punctures_same hak hp, by
      rw [← mul_sub, norm_mul, ha, one_mul]; exact hwp⟩

/-- Rotation equivariance of the reflection-encoded core, preserving its
arbitrary complex reflection parameters. -/
theorem rot1_mem_reflCc_same {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = 1)
    (s₁ s₀ : ℂ) {f : ℂ → ℂ} (hf : f ∈ KsIndex.TwistSwap.ReflCc k s₁ s₀) :
    rot1 a f ∈ KsIndex.TwistSwap.ReflCc k s₁ s₀ := by
  obtain ⟨f1, f2, f3, f4, ⟨ε, hε, f5⟩, f6⟩ := hf
  have hmaps : Set.MapsTo (fun z : ℂ => a * z) disk disk := fun z hz => by
    rw [mem_disk_iff, norm_mul, ha, one_mul]
    exact mem_disk_iff.mp hz
  have hmapsB : Set.MapsTo (fun z : ℂ => a * z)
      (Metric.closedBall 0 1) (Metric.closedBall 0 1) := fun z hz => by
    simp only [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    rw [norm_mul, ha, one_mul]
    exact hz
  refine ⟨f1.comp (contDiffOn_const.mul contDiffOn_id) hmaps, ?_, ?_,
    fun w hw => ?_, ⟨ε, hε, fun w ⟨p, hp, hwp⟩ => ?_⟩, ?_⟩
  · intro w hw
    rw [refl_rot1 ha]
    exact (f2 (a * w) (mul_mem_arc_same ha hak hw)).comp w
      ((contDiff_const.mul contDiff_id).contDiffAt)
  · intro w hw
    rw [refl_rot1 ha]
    exact (f3 (a * w) (mul_mem_arc_same ha hak hw)).comp w
      ((contDiff_const.mul contDiff_id).contDiffAt)
  · exact f4 (a * w) (by rw [norm_mul, ha, one_mul]; exact hw)
  · exact f5 (a * w) ⟨a * p, mul_mem_punctures_same hak hp, by
      rw [← mul_sub, norm_mul, ha, one_mul]; exact hwp⟩
  · exact f6.comp ((continuous_const.mul continuous_id).continuousOn) hmapsB

end KsIndex.SingleDisk
