module

public import KsIndexLean.KarcherCompactDoubleDisk
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


/-! The hemisphere parametrizations used to identify the doubled disk with the sphere. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.DiskCompactification

/-- The nonnegative height of the unit hemisphere over a point of the closed disk. -/
def hemisphereHeight (z : ClosedDisk) : ℝ := Real.sqrt (1 - ‖z.val‖ ^ 2)

lemma hemisphereHeight_sq (z : ClosedDisk) : hemisphereHeight z ^ 2 = 1 - ‖z.val‖ ^ 2 := by
  apply Real.sq_sqrt
  have := z.property
  have := norm_nonneg z.val
  nlinarith

lemma hemisphereHeight_eq_zero_iff (z : ClosedDisk) :
    hemisphereHeight z = 0 ↔ ‖z.val‖ = 1 := by
  have hs := hemisphereHeight_sq z
  have hn := norm_nonneg z.val
  constructor
  · intro h
    rw [h] at hs
    nlinarith
  · intro h
    simp [hemisphereHeight, h]

lemma continuous_hemisphereHeight : Continuous hemisphereHeight := by
  unfold hemisphereHeight
  fun_prop

/-- Upper and lower hemispheres, with sheet zero chosen as the upper one. -/
def hemisphereVector (p : Copies 1) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![p.2.val.re, p.2.val.im,
    if p.1 = 0 then hemisphereHeight p.2 else -hemisphereHeight p.2]

lemma hemisphereVector_norm (p : Copies 1) : ‖hemisphereVector p‖ = 1 := by
  have hs := hemisphereHeight_sq p.2
  have hz := Complex.sq_norm p.2.val
  rw [Complex.normSq_apply] at hz
  have he := EuclideanSpace.real_norm_sq_eq (hemisphereVector p)
  have he' : ‖hemisphereVector p‖ ^ 2 = p.2.val.re ^ 2 +
      (p.2.val.im ^ 2 + hemisphereHeight p.2 ^ 2) := by
    rw [he]
    simp [hemisphereVector, Fin.sum_univ_succ]
  nlinarith [norm_nonneg (hemisphereVector p)]

lemma continuous_hemisphereVector : Continuous hemisphereVector := by
  unfold hemisphereVector
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : Copies 1 => p.2.val.re)
    fun_prop
  · change Continuous (fun p : Copies 1 => p.2.val.im)
    fun_prop
  · change Continuous (fun p : Copies 1 =>
      if p.1 = 0 then hemisphereHeight p.2 else -hemisphereHeight p.2)
    apply Continuous.if _ (continuous_hemisphereHeight.comp continuous_snd)
      (continuous_hemisphereHeight.comp continuous_snd).neg
    have hc : IsClopen {p : Copies 1 | p.1 = 0} :=
      (isClopen_discrete ({0} : Set (ZMod (2 * 1)))).preimage continuous_fst
    simp [hc.frontier_eq]

lemma hemisphereVector_eq_iff (p q : Copies 1) :
    hemisphereVector p = hemisphereVector q ↔
      p.2 = q.2 ∧ (p.1 = q.1 ∨ ‖p.2.val‖ = 1) := by
  constructor
  · intro he
    have hre := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) he
    have him := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) he
    have hheight := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) he
    change p.2.val.re = q.2.val.re at hre
    change p.2.val.im = q.2.val.im at him
    have hz : p.2 = q.2 := Subtype.ext (Complex.ext hre him)
    refine ⟨hz, ?_⟩
    by_cases hi : p.1 = q.1
    · exact Or.inl hi
    · right
      apply (hemisphereHeight_eq_zero_iff p.2).mp
      rcases p with ⟨i,z⟩
      rcases q with ⟨j,v⟩
      dsimp only at *
      subst v
      have hi' : i = 0 ∨ i = 1 := by
        fin_cases i <;> first | exact Or.inl rfl | exact Or.inr rfl
      have hj' : j = 0 ∨ j = 1 := by
        fin_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl
      rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
      · exact (hi rfl).elim
      · simp [hemisphereVector] at hheight
        linarith
      · simp [hemisphereVector] at hheight
        linarith
      · exact (hi rfl).elim
  · rintro ⟨hz, hi | hb⟩
    · have hpq : p = q := Prod.ext hi hz
      rw [hpq]
    · have hh := (hemisphereHeight_eq_zero_iff p.2).mpr hb
      have hhq : hemisphereHeight q.2 = 0 := hz ▸ hh
      simp [hemisphereVector, hhq, hz]

lemma hemisphereVector_surjective :
    ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → ∃ p : Copies 1, hemisphereVector p = x := by
  intro x hx
  have hs := EuclideanSpace.real_norm_sq_eq x
  rw [hx] at hs
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, one_pow] at hs
  change 1 = (x 0) ^ 2 + ((x 1) ^ 2 + (x 2) ^ 2) at hs
  let z : ℂ := ⟨x 0, x 1⟩
  have hzsq : ‖z‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    change x 0 * x 0 + x 1 * x 1 = _
    ring
  have hz : ‖z‖ ≤ 1 := by nlinarith [norm_nonneg z, sq_nonneg (x 2)]
  let w : ClosedDisk := ⟨z, hz⟩
  have hh : hemisphereHeight w ^ 2 = (x 2) ^ 2 := by
    have h := hemisphereHeight_sq w
    change hemisphereHeight w ^ 2 = 1 - ‖z‖ ^ 2 at h
    nlinarith
  have hnonneg : 0 ≤ hemisphereHeight w := Real.sqrt_nonneg _
  by_cases hx2 : 0 ≤ x 2
  · refine ⟨(0,w), ?_⟩
    have he : hemisphereHeight w = x 2 := by nlinarith
    ext i
    fin_cases i <;> simp [hemisphereVector, w, z, he]
  · refine ⟨(1,w), ?_⟩
    have he : -hemisphereHeight w = x 2 := by nlinarith
    ext i
    fin_cases i <;> simp [hemisphereVector, w, z, he]

variable {k : ℕ} [Fact (2 ≤ k)]

/-- The map from the one-period compactification to the ordinary unit two-sphere. -/
def onePeriodSphereMap : FilledChain k 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  Quotient.lift (fun p => ⟨hemisphereVector p, by
    simpa only [Metric.mem_sphere, dist_zero_right] using hemisphereVector_norm p⟩)
    (fun p q hpq => Subtype.ext ((hemisphereVector_eq_iff p q).mpr
      ((filledRel_one_period p q).mp hpq)))

lemma continuous_onePeriodSphereMap : Continuous (onePeriodSphereMap (k := k)) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact continuous_hemisphereVector.subtype_mk _

lemma onePeriodSphereMap_bijective : Function.Bijective (onePeriodSphereMap (k := k)) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with | h p =>
      induction b using Quotient.inductionOn with | h q =>
        intro he
        apply Quotient.sound
        apply (filledRel_one_period p q).mpr
        apply (hemisphereVector_eq_iff p q).mp
        exact congrArg Subtype.val he
  · intro x
    obtain ⟨p, hp⟩ := hemisphereVector_surjective x.val (by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property)
    exact ⟨Quotient.mk _ p, Subtype.ext hp⟩

/-- The one-period compactified surface is homeomorphic to the two-sphere. -/
def onePeriodSphereHomeomorph :
    FilledChain k 1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  IsHomeomorph.homeomorph _ (isHomeomorph_iff_continuous_bijective.mpr
    ⟨continuous_onePeriodSphereMap, onePeriodSphereMap_bijective⟩)

end KsIndex.KarcherData.DiskCompactification
