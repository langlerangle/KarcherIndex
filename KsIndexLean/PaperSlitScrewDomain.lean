module

public import KsIndexLean.MixedOrientationRotation
public import KsIndexLean.PaperSlitScrewTrace

@[expose] public section


/-! The screw's two-half action preserves the analytic slit character domain. -/
noncomputable section
open MeasureTheory Set
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- A rotated transmission relation holds on the preimage of its boundary arc. -/
lemma arcTrace_rotation_preimage_phase (A : Set Circle₁) (hA : MeasurableSet A)
    (θ : ℝ) (c : ℂ) (u v : ComplexH1) (hu : arcTrace A u = c • arcTrace A v) :
    arcTrace (circleRotate θ ⁻¹' A) (diskRotation θ u) =
      c • arcTrace (circleRotate θ ⁻¹' A) (diskRotation θ v) := by
  have hz : u - c • v ∈ zeroTraceDomain A := by
    change arcTrace A (u - c • v) = 0
    rw [map_sub, map_smul, hu, sub_self]
  have hr := zeroTrace_rotation_preimage A hA θ (u - c • v) hz
  change arcTrace (circleRotate θ ⁻¹' A) (diskRotation θ (u - c • v)) = 0 at hr
  rw [map_sub, map_smul, map_sub, map_smul, sub_eq_zero] at hr
  exact hr

/-- Ordered (upper, lower) screw action: the upper output crosses one full period. -/
def paperSlitScrewPair (α : ℝ) (u : DiskPairH1) : DiskPairH1 :=
  (Complex.exp ((2 * Real.pi * α) * Complex.I) • diskRotation (-Real.pi/3) u.2,
    diskRotation (-Real.pi/3) u.1)

lemma paperSlitScrewPair_mem (α : ℝ) (u : DiskPairH1) (hu : u ∈ paperSlitDomain α) :
    paperSlitScrewPair α u ∈ paperSlitDomain α := by
  have hθ : Complex.exp (((-Real.pi/3 : ℝ) : ℂ) * Complex.I) ^ 3 = -1 := by
    rw [← Complex.exp_nat_mul]
    have he : (3 : ℂ) * (((-Real.pi/3 : ℝ) : ℂ) * Complex.I) =
        -(Real.pi : ℂ) * Complex.I := by push_cast; ring
    norm_num only [Nat.cast_ofNat]
    rw [he, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  obtain ⟨h1,h0⟩ := (mem_slitTraceDomain _ _ u).mp hu
  have hr0 := arcTrace_rotation_preimage_phase (boundaryArc 3 0)
    (measurableSet_boundaryArc _ _) (-Real.pi/3) _ u.1 u.2 h0
  have hr1 := arcTrace_rotation_preimage_phase (boundaryArc 3 1)
    (measurableSet_boundaryArc _ _) (-Real.pi/3) 1 u.1 u.2 (by simpa using h1)
  rw [circleRotate_arc_swap_zero hθ] at hr0
  rw [circleRotate_arc_swap_one hθ, one_smul] at hr1
  apply (mem_slitTraceDomain _ _ _).mpr
  dsimp only [paperSlitScrewPair, Prod.fst, Prod.snd]
  constructor
  · rw [map_smul, hr0]
  · rw [map_smul, hr1]

lemma pairCharacter_rotated_swap (θ φ : ℝ) (c d : ℂ) (u : DiskPairH1)
    (hu : u ∈ pairCharacterDomain φ d) :
    (c • diskRotation θ u.2, diskRotation θ u.1) ∈ pairCharacterDomain φ d := by
  rw [pairCharacterDomain, Submodule.mem_inf, Submodule.mem_comap, Submodule.mem_comap] at hu ⊢
  have ha : diskRotation θ u.2 ∈ weakCharacterDomain φ d :=
    diskRotation_preserves_character θ φ d u.2 hu.2
  have hb : diskRotation θ u.1 ∈ weakCharacterDomain φ d :=
    diskRotation_preserves_character θ φ d u.1 hu.1
  exact ⟨(weakCharacterDomain φ d).smul_mem c ha, hb⟩

lemma paperSlitScrewPair_mem_character (α : ℝ) (j : ℕ) (u : DiskPairH1)
    (hu : u ∈ paperSlitCharacterDomain α j) :
    paperSlitScrewPair α u ∈ paperSlitCharacterDomain α j :=
  ⟨paperSlitScrewPair_mem α u hu.1,
    pairCharacter_rotated_swap (-Real.pi/3) (-(2*Real.pi)/3)
      (Complex.exp ((2*Real.pi*α)*Complex.I)) (KsIndex.FormIndex.zeta 3 ^ j) u hu.2⟩

/-- Forward screw action on the admissible analytic slit character domain. -/
def paperSlitScrew (α : ℝ) (j : ℕ) (u : paperSlitCharacterDomain α j) :
    paperSlitCharacterDomain α j :=
  ⟨paperSlitScrewPair α u.val, paperSlitScrewPair_mem_character α j u.val u.property⟩

/-- The lower trace of the domain-preserving action has the exact j=2 phase. -/
theorem paperSlitScrew_lower_trace {α : ℝ} {j : ℕ} (hj : j % 3 = 2)
    (u : paperSlitCharacterDomain α j) :
    (fun i : KsIndex.Sector.Idx => circleFourierCoeff
      (diskTraceCLM (paperSlitScrew α j u).val.2) (KsIndex.PaperSlitAdapter.idxToNZ i).val) =
      Complex.exp (Complex.I * (Real.pi * (α + 2/3))) •
        KsIndex.Sector.rop α (fun i : KsIndex.Sector.Idx =>
          circleFourierCoeff (diskTraceCLM u.val.2) (KsIndex.PaperSlitAdapter.idxToNZ i).val) :=
  KsIndex.PaperSlitAdapter.rotated_upper_trace_eq_phase_rop hj u

end KsIndex.Trace
