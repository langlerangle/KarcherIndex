module

public import KsIndexLean.ArcTraceRotation
public import KsIndexLean.DiskRotationForms
public import KsIndexLean.JacobiExtensionCounts
public import KsIndexLean.SingleArcConditionalAssembly

@[expose] public section


noncomputable section
open MeasureTheory Set
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.CircleSobolev KsIndex.DtnBridge KsIndex.Spectral

lemma halfSectorAngle_power {k : ℕ} (hk : 0 < k) :
    Complex.exp (((Real.pi / k : ℝ) : ℂ) * Complex.I) ^ k = -1 := by
  rw [← Complex.exp_nat_mul]
  have he : (k : ℂ) * (((Real.pi / k : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
    push_cast
    have hn : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp
  rw [he, Complex.exp_pi_mul_I]

lemma circleRotate_arc_swap_zero {k : ℕ} {θ : ℝ}
    (hθ : Complex.exp ((θ : ℂ) * Complex.I) ^ k = -1) :
    circleRotate θ ⁻¹' boundaryArc k 0 = boundaryArc k 1 := by
  ext w
  simp only [Set.mem_preimage, mem_boundaryArc]
  change (-1 : ℝ) ^ 0 * ((Complex.exp ((θ : ℂ) * Complex.I) * (w : ℂ)) ^ k).re < 0 ↔ _
  rw [mul_pow, hθ]
  simp

lemma circleRotate_arc_swap_one {k : ℕ} {θ : ℝ}
    (hθ : Complex.exp ((θ : ℂ) * Complex.I) ^ k = -1) :
    circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 0 := by
  ext w
  simp only [Set.mem_preimage, mem_boundaryArc]
  change (-1 : ℝ) ^ 1 * ((Complex.exp ((θ : ℂ) * Complex.I) * (w : ℂ)) ^ k).re < 0 ↔ _
  rw [mul_pow, hθ]
  simp

lemma zeroTrace_rotation_preimage (A : Set Circle₁) (hA : MeasurableSet A)
    (θ : ℝ) (u : ComplexH1) (hu : u ∈ zeroTraceDomain A) :
    diskRotation θ u ∈ zeroTraceDomain (circleRotate θ ⁻¹' A) := by
  rw [mem_zeroTraceDomain] at hu ⊢
  have hm := (measurePreserving_circleRotate θ).restrict_preimage hA
  have h := hm.quasiMeasurePreserving.ae_eq_comp hu
  have hr := ae_restrict_of_ae (s := circleRotate θ ⁻¹' A)
    (boundaryRotation_coe_ae θ (diskTraceCLM u))
  rw [diskTrace_rotation]
  filter_upwards [h, hr] with w hw hr
  exact hr.trans hw

lemma diskRotation_preserves_character (θ φ : ℝ) (c : ℂ) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain φ c) : diskRotation θ u ∈ weakCharacterDomain φ c := by
  rw [mem_weakCharacterDomain] at hu ⊢
  rw [← diskRotation_add, add_comm φ θ, diskRotation_add, hu, map_smul]

lemma diskRotation_swaps_mixed {k j : ℕ} {θ : ℝ}
    (hθ : Complex.exp ((θ : ℂ) * Complex.I) ^ k = -1) (b1 b0 : Bool)
    (u : ComplexH1) (hu : u ∈ mixedCharacterDomain k j b1 b0) :
    diskRotation θ u ∈ mixedCharacterDomain k j b0 b1 := by
  refine ⟨?_, diskRotation_preserves_character θ _ _ u hu.2⟩
  have hz0 (h : u ∈ zeroTraceDomain (boundaryArc k 0)) :
      diskRotation θ u ∈ zeroTraceDomain (boundaryArc k 1) := by
    simpa only [circleRotate_arc_swap_zero hθ] using
      zeroTrace_rotation_preimage _ (measurableSet_boundaryArc k 0) θ u h
  have hz1 (h : u ∈ zeroTraceDomain (boundaryArc k 1)) :
      diskRotation θ u ∈ zeroTraceDomain (boundaryArc k 0) := by
    simpa only [circleRotate_arc_swap_one hθ] using
      zeroTrace_rotation_preimage _ (measurableSet_boundaryArc k 1) θ u h
  have hm := hu.1
  cases b1 <;> cases b0 <;>
    simp only [mixedTraceDomain, naturalArcDomain, Bool.false_eq_true, ite_false, ite_true,
      inf_top_eq, top_inf_eq] at hm ⊢
  · exact ⟨hz0 hm.2, hz1 hm.1⟩
  · exact hz1 hm
  · exact hz0 hm
  · exact Submodule.mem_top

lemma neg_halfSectorAngle_power {k : ℕ} (hk : 0 < k) :
    Complex.exp (((-(Real.pi / k) : ℝ) : ℂ) * Complex.I) ^ k = -1 := by
  rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, inv_pow, halfSectorAngle_power hk]
  norm_num

/-- Pure rotation swaps mixed flags and preserves the character j. -/
def mixedOrientationEquiv {k : ℕ} (hk : 0 < k) (j : ℕ) (b1 b0 : Bool) :
    mixedCharacterDomain k j b1 b0 ≃ₗ[ℂ] mixedCharacterDomain k j b0 b1 where
  toFun u := ⟨diskRotation (Real.pi / k) u.val,
    diskRotation_swaps_mixed (halfSectorAngle_power hk) b1 b0 u.val u.property⟩
  invFun v := ⟨diskRotation (-(Real.pi / k)) v.val,
    diskRotation_swaps_mixed (neg_halfSectorAngle_power hk) b0 b1 v.val v.property⟩
  left_inv u := Subtype.ext (diskRotation_neg _ u.val)
  right_inv v := by
    apply Subtype.ext
    change diskRotation (Real.pi / k) (diskRotation (-(Real.pi / k)) v.val) = v.val
    rw [← diskRotation_add, add_neg_cancel, diskRotation_zero]
  map_add' u v := Subtype.ext ((diskRotation (Real.pi / k)).map_add u.val v.val)
  map_smul' c u := Subtype.ext ((diskRotation (Real.pi / k)).map_smul c u.val)

lemma mixedOrientationEquiv_form {k : ℕ} (hk : 0 < k) (j : ℕ) (b1 b0 : Bool)
    (u v : mixedCharacterDomain k j b1 b0) :
    weakJacobi (surfacePotential k) (mixedOrientationEquiv hk j b1 b0 u).val
      (mixedOrientationEquiv hk j b1 b0 v).val = weakJacobi (surfacePotential k) u.val v.val :=
  surfaceJacobi_diskRotation k (Real.pi / k) u.val v.val

/-- The form-preserving rotation transports the radical and preserves nullity. -/
theorem mixedOrientation_nullity {k : ℕ} (hk : 0 < k) (j : ℕ) (b1 b0 : Bool) :
    diskWeakNullity (mixedCharacterDomain k j b1 b0) (surfacePotential k) =
      diskWeakNullity (mixedCharacterDomain k j b0 b1) (surfacePotential k) := by
  let : CompleteSpace (mixedCharacterDomain k j b1 b0) :=
    (isClosed_mixedCharacterDomain k j b1 b0).completeSpace_coe
  let : CompleteSpace (mixedCharacterDomain k j b0 b1) :=
    (isClosed_mixedCharacterDomain k j b0 b1).completeSpace_coe
  have h := sesqNullity_congr (mixedOrientationEquiv hk j b1 b0)
    (fun u v => weakJacobi (surfacePotential k) u.val v.val)
    (fun u v => weakJacobi (surfacePotential k) u.val v.val)
    (mixedOrientationEquiv_form hk j b1 b0)
  rw [disk_sesqNullity_eq_weakNullity, disk_sesqNullity_eq_weakNullity] at h
  exact_mod_cast h.symm

/-- Mixed nullity vanishes in every rotation character and either orientation,
assuming the stated middle-character single-arc upper bounds. -/
theorem both_mixed_nullities_zero_of_middle_bounds {k : ℕ} (hk : 3 ≤ k)
    (hC : ∀ j : ℕ, 2 ≤ j → j + 2 ≤ k → SingleArcReindex.SingleArcUpperBound k j)
    (j : ℕ) (hj : j < k) (b1 b0 : Bool) (hb : b1 ≠ b0) :
    diskWeakNullity (mixedCharacterDomain k j b1 b0) (surfacePotential k) = 0 := by
  have h := SingleArcReindex.all_mixed_nullity_zero_of_middle_bounds hk hC j hj
  cases b1 <;> cases b0
  · exact (hb rfl).elim
  · rw [mixedOrientation_nullity (by omega : 0 < k) j false true]
    exact h
  · exact h
  · exact (hb rfl).elim

end KsIndex.Trace
