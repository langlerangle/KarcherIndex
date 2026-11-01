module

public import KsIndexLean.KarcherCompactSurfaceFaces
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section


/-! Embedded circular arcs in the closed faces of the compactified surface. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- The angle of the `t`-th puncture, with integer indexing to include the wraparound. -/
def vertexAngle (k : ℕ) (t : ℤ) : ℝ := (2 * (t : ℝ) + 1) * Real.pi / (2 * k)

lemma vertexAngle_gap (t : ℤ) :
    vertexAngle k (t + 1) - vertexAngle k t = Real.pi / k := by
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (by have := h.out; omega : k ≠ 0)
  simp only [vertexAngle, Int.cast_add, Int.cast_one]
  field_simp
  ring

lemma vertexAngle_lt (t : ℤ) : vertexAngle k t < vertexAngle k (t + 1) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast (by have := h.out; omega : 0 < k)
  have := div_pos Real.pi_pos hk
  rw [← vertexAngle_gap (k := k) t] at this
  linarith

/-- The closed angular interval between consecutive punctures. -/
abbrev EdgeInterval (k : ℕ) (t : ℤ) := Icc (vertexAngle k t) (vertexAngle k (t + 1))

/-- The unit-circle arc, regarded as a map into the closed disk. -/
def edgeParameter (t : ℤ) (s : EdgeInterval k t) : ClosedDisk :=
  ⟨(Circle.exp s.val : ℂ), by simp⟩

omit h in
lemma continuous_edgeParameter (t : ℤ) : Continuous (edgeParameter (k := k) t) := by
  unfold edgeParameter
  fun_prop

lemma edgeParameter_injective (t : ℤ) : Function.Injective (edgeParameter (k := k) t) := by
  intro a b hab
  apply Subtype.ext
  apply Circle.exp_injOn_Icc (a := vertexAngle k t) (b := vertexAngle k (t + 1))
  · rw [vertexAngle_gap]
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast (by have := h.out; omega : 1 ≤ k)
    have hk0 : (0 : ℝ) < k := by linarith
    apply (div_lt_iff₀ hk0).mpr
    nlinarith [Real.pi_pos]
  · exact a.property
  · exact b.property
  · apply Subtype.ext
    exact congrArg (fun z : ClosedDisk => z.val) hab

lemma edgeParameter_isClosedEmbedding (t : ℤ) :
    IsClosedEmbedding (edgeParameter (k := k) t) :=
  (continuous_edgeParameter t).isClosedEmbedding (edgeParameter_injective t)

/-- A boundary arc in one specified face of the compact surface. -/
def faceEdgeMap (i : ZMod (2 * m)) (t : ℤ) : EdgeInterval k t → FilledChain k m :=
  faceMap i ∘ edgeParameter t

lemma faceEdgeMap_isClosedEmbedding (i : ZMod (2 * m)) (t : ℤ) :
    IsClosedEmbedding (faceEdgeMap (k := k) i t) :=
  (faceMap_isClosedEmbedding i).comp (edgeParameter_isClosedEmbedding t)

/-- Each parametrized closed boundary arc is homeomorphic to its actual image. -/
def faceEdgeHomeomorph (i : ZMod (2 * m)) (t : ℤ) :
    EdgeInterval k t ≃ₜ range (faceEdgeMap (k := k) i t) :=
  (faceEdgeMap_isClosedEmbedding i t).isEmbedding.toHomeomorph

lemma faceEdgeMap_coordinate_norm (i : ZMod (2 * m)) (t : ℤ) (s : EdgeInterval k t) :
    ‖(coordinate (faceEdgeMap (k := k) i t s)).val‖ = 1 := by
  change ‖(Circle.exp s.val : ℂ)‖ = 1
  simp

/-- Every endpoint of the angular subdivision is an actual deleted EW puncture. -/
lemma vertexAngle_mem_punctures (t : ℤ) :
    (Circle.exp (vertexAngle k t) : ℂ) ∈ Surface.punctures k := by
  change (Circle.exp (vertexAngle k t) : ℂ) ^ (2 * k) = -1
  rw [Circle.coe_exp, ← Complex.exp_nat_mul]
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := h.out; omega)
  have he : ((2 * k : ℕ) : ℂ) * ((vertexAngle k t : ℂ) * Complex.I) =
      (t : ℂ) * (2 * Real.pi * Complex.I) + Real.pi * Complex.I := by
    simp only [vertexAngle]
    push_cast
    field_simp
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I,
    one_mul]

/-- The angular puncture equation has no additional solutions between vertices. -/
lemma exp_mem_punctures_iff (s : ℝ) :
    (Circle.exp s : ℂ) ∈ Surface.punctures k ↔ ∃ t : ℤ, s = vertexAngle k t := by
  constructor
  · intro hp
    change (Circle.exp s : ℂ) ^ (2 * k) = -1 at hp
    rw [Circle.coe_exp, ← Complex.exp_nat_mul, ← Complex.exp_pi_mul_I] at hp
    obtain ⟨t, ht⟩ := Complex.exp_eq_exp_iff_exists_int.mp hp
    have hi := congrArg Complex.im ht
    simp at hi
    have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (by have := h.out; omega : k ≠ 0)
    refine ⟨t, ?_⟩
    unfold vertexAngle
    apply (eq_div_iff (mul_ne_zero (by norm_num) hk)).mpr
    nlinarith
  · rintro ⟨t, rfl⟩
    exact vertexAngle_mem_punctures t

lemma edgeParameter_interior_not_puncture (t : ℤ) (s : EdgeInterval k t)
    (hs : s.val ∈ Ioo (vertexAngle k t) (vertexAngle k (t + 1))) :
    (edgeParameter (k := k) t s).val ∉ Surface.punctures k := by
  intro hp
  obtain ⟨n, hn⟩ := (exp_mem_punctures_iff s.val).mp hp
  have hk : (0 : ℝ) < 2 * k := by have := h.out; positivity
  rw [hn] at hs
  have hlow := (div_lt_div_iff_of_pos_right hk).mp hs.1
  have hupp := (div_lt_div_iff_of_pos_right hk).mp hs.2
  have hnlow : (t : ℝ) < n := by nlinarith [Real.pi_pos]
  have hnupp : (n : ℝ) < (t + 1 : ℤ) := by nlinarith [Real.pi_pos]
  have hl : t < n := by exact_mod_cast hnlow
  have hu : n < t + 1 := by exact_mod_cast hnupp
  omega

lemma edgeParameter_left_mem_punctures (t : ℤ) :
    (edgeParameter (k := k) t ⟨vertexAngle k t,
      ⟨le_rfl, (vertexAngle_lt t).le⟩⟩).val ∈ Surface.punctures k :=
  vertexAngle_mem_punctures t

lemma edgeParameter_right_mem_punctures (t : ℤ) :
    (edgeParameter (k := k) t ⟨vertexAngle k (t + 1),
      ⟨(vertexAngle_lt t).le, le_rfl⟩⟩).val ∈ Surface.punctures k :=
  vertexAngle_mem_punctures (t + 1)

/-- The angular intervals cover the entire real line, including their endpoints. -/
lemma exists_edgeInterval (s : ℝ) : ∃ t : ℤ, s ∈ EdgeInterval k t := by
  let x : ℝ := (2 * k * s / Real.pi - 1) / 2
  let t : ℤ := ⌊x⌋
  have hlo : (t : ℝ) ≤ x := Int.floor_le x
  have hhi : x < (t : ℝ) + 1 := Int.lt_floor_add_one x
  have hx : 2 * x * Real.pi = 2 * k * s - Real.pi := by
    dsimp [x]
    field_simp
  have hk : (0 : ℝ) < 2 * k := by have := h.out; positivity
  refine ⟨t, ?_, ?_⟩
  · change (2 * (t : ℝ) + 1) * Real.pi / (2 * k) ≤ s
    apply (div_le_iff₀ hk).mpr
    nlinarith [Real.pi_pos]
  · change s ≤ (2 * ((t + 1 : ℤ) : ℝ) + 1) * Real.pi / (2 * k)
    apply (le_div_iff₀ hk).mpr
    push_cast
    nlinarith [Real.pi_pos]

/-- Every point of the circle occurs on one of the individual closed arcs. -/
lemma exists_edgeParameter (w : ClosedDisk) (hw : ‖w.val‖ = 1) :
    ∃ (t : ℤ) (s : EdgeInterval k t), edgeParameter t s = w := by
  let c : Circle := ⟨w.val, by
    simpa [Submonoid.unitSphere, Metric.mem_sphere, dist_zero_right] using hw⟩
  obtain ⟨t, ht⟩ := exists_edgeInterval (k := k) (Complex.arg w.val)
  refine ⟨t, ⟨Complex.arg w.val, ht⟩, ?_⟩
  apply Subtype.ext
  exact congrArg (fun z : Circle => (z : ℂ)) (Circle.exp_arg c)

/-- The individual closed arcs cover exactly the boundary of the face decomposition. -/
lemma faceEdges_cover_boundary :
    (⋃ (i : ZMod (2 * m)) (t : ℤ), range (faceEdgeMap (k := k) i t)) =
      {q : FilledChain k m | ‖(coordinate q).val‖ = 1} := by
  ext q
  constructor
  · intro hq
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hq
    obtain ⟨t,s,rfl⟩ := Set.mem_iUnion.mp hi
    exact faceEdgeMap_coordinate_norm i t s
  · intro hq
    obtain ⟨p,rfl⟩ := Quotient.mk_surjective q
    obtain ⟨t,s,hs⟩ := exists_edgeParameter (k := k) p.2 hq
    exact Set.mem_iUnion.mpr ⟨p.1, Set.mem_iUnion.mpr ⟨t, s, by
      change faceMap p.1 (edgeParameter t s) = faceMap p.1 p.2
      rw [hs]⟩⟩

/-- In the interior of an arc, different faces meet exactly along their assigned seams. -/
lemma faceEdgeMap_eq_iff_interior {i j : ZMod (2 * m)} (hij : i ≠ j)
    (t : ℤ) (s : EdgeInterval k t)
    (hs : s.val ∈ Ioo (vertexAngle k t) (vertexAngle k (t + 1))) :
    faceEdgeMap (k := k) i t s = faceEdgeMap j t s ↔
      (j = i + 1 ∧ (edgeParameter t s).val ∈ Surface.seamArc k m i) ∨
      (i = j + 1 ∧ (edgeParameter t s).val ∈ Surface.seamArc k m j) := by
  change faceMap i (edgeParameter t s) = faceMap j (edgeParameter t s) ↔ _
  rw [faceMap_eq_iff_boundary hij]
  simp only [true_and, eq_self, edgeParameter_interior_not_puncture t s hs, false_or]

lemma vertexAngle_add_period (t n : ℤ) :
    vertexAngle k (t + (2 * k : ℤ) * n) = vertexAngle k t + n * (2 * Real.pi) := by
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (by have := h.out; omega : k ≠ 0)
  simp only [vertexAngle]
  push_cast
  field_simp
  ring

/-- Repeated angular labels describe the same circular edge after one full turn. -/
lemma range_edgeParameter_add_period (t n : ℤ) :
    range (edgeParameter (k := k) (t + (2 * k : ℤ) * n)) =
      range (edgeParameter (k := k) t) := by
  have hend : vertexAngle k (t + (2 * k : ℤ) * n + 1) =
      vertexAngle k (t + 1) + n * (2 * Real.pi) := by
    rw [show t + (2 * k : ℤ) * n + 1 = (t + 1) + (2 * k : ℤ) * n by ring,
      vertexAngle_add_period]
  ext w
  constructor
  · rintro ⟨s, rfl⟩
    have hlo := s.property.1
    have hhi := s.property.2
    rw [vertexAngle_add_period] at hlo
    rw [hend] at hhi
    refine ⟨⟨s.val - n * (2 * Real.pi), by constructor <;> linarith⟩, ?_⟩
    apply Subtype.ext
    change (Circle.exp (s.val - n * (2 * Real.pi)) : ℂ) = (Circle.exp s.val : ℂ)
    apply congrArg (fun c : Circle => (c : ℂ))
    apply Circle.exp_eq_exp.mpr
    exact ⟨-n, by push_cast; ring⟩
  · rintro ⟨s, rfl⟩
    refine ⟨⟨s.val + n * (2 * Real.pi), ?_⟩, ?_⟩
    · constructor
      · rw [vertexAngle_add_period]
        linarith [s.property.1]
      · rw [hend]
        linarith [s.property.2]
    · apply Subtype.ext
      change (Circle.exp (s.val + n * (2 * Real.pi)) : ℂ) = (Circle.exp s.val : ℂ)
      exact congrArg (fun c : Circle => (c : ℂ)) (Circle.exp_eq_exp.mpr ⟨n, rfl⟩)

/-- The whole boundary circle is covered by a finite family of `2*k` arcs. -/
lemma exists_finite_edgeParameter (w : ClosedDisk) (hw : ‖w.val‖ = 1) :
    ∃ (t : Fin (2 * k)) (s : EdgeInterval k (t.val : ℤ)), edgeParameter (t.val : ℤ) s = w := by
  obtain ⟨t,s,hs⟩ := exists_edgeParameter (k := k) w hw
  have hk : (0 : ℤ) < 2 * k := by have := h.out; positivity
  let r : ℤ := t % (2 * k)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hk)
  have hrlt : r < 2 * k := Int.emod_lt_of_pos _ hk
  have he : t = r + (2 * k) * (t / (2 * k)) := by
    exact (Int.emod_add_mul_ediv t (2 * k)).symm
  have hm : w ∈ range (edgeParameter (k := k) t) := ⟨s, hs⟩
  rw [he, range_edgeParameter_add_period] at hm
  obtain ⟨u,hu⟩ := hm
  have hrnat : r.toNat < 2 * k := by omega
  refine ⟨⟨r.toNat, hrnat⟩, ?_⟩
  have hc : (r.toNat : ℤ) = r := by omega
  change ∃ s : EdgeInterval k (r.toNat : ℤ), edgeParameter (r.toNat : ℤ) s = w
  rw [hc]
  exact ⟨u,hu⟩

lemma vertexAngle_strictMono : StrictMono (vertexAngle k) := by
  intro a b hab
  have hk : (0 : ℝ) < 2 * k := by have := h.out; positivity
  apply (div_lt_div_iff_of_pos_right hk).mpr
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  nlinarith [Real.pi_pos]

/-- Interior points in distinct arcs of the finite subdivision cannot coincide. -/
lemma edgeParameter_interior_index_unique (a b : Fin (2 * k))
    (s : EdgeInterval k (a.val : ℤ)) (u : EdgeInterval k (b.val : ℤ))
    (hs : s.val ∈ Ioo (vertexAngle k (a.val : ℤ)) (vertexAngle k (a.val + 1 : ℤ)))
    (hu : u.val ∈ Ioo (vertexAngle k (b.val : ℤ)) (vertexAngle k (b.val + 1 : ℤ)))
    (he : edgeParameter (a.val : ℤ) s = edgeParameter (b.val : ℤ) u) : a = b := by
  have htop : vertexAngle k (2 * k : ℤ) - vertexAngle k 0 ≤ 2 * Real.pi := by
    have hp := vertexAngle_add_period (k := k) 0 1
    simp only [mul_one, zero_add, Int.cast_one, one_mul] at hp
    linarith
  have hsmem : s.val ∈ Ico (vertexAngle k 0) (vertexAngle k (2 * k : ℤ)) := by
    constructor
    · exact le_trans (vertexAngle_strictMono.monotone (by omega)) hs.1.le
    · exact lt_of_lt_of_le hs.2 (vertexAngle_strictMono.monotone (by omega))
  have humem : u.val ∈ Ico (vertexAngle k 0) (vertexAngle k (2 * k : ℤ)) := by
    constructor
    · exact le_trans (vertexAngle_strictMono.monotone (by omega)) hu.1.le
    · exact lt_of_lt_of_le hu.2 (vertexAngle_strictMono.monotone (by omega))
  have hsu : s.val = u.val := Circle.exp_injOn_Ico htop hsmem humem
    (Circle.ext (congrArg (fun w : ClosedDisk => w.val) he))
  apply Fin.ext
  by_contra hab
  rcases lt_or_gt_of_ne hab with hab | hba
  · have hh : vertexAngle k (a.val + 1 : ℤ) ≤ vertexAngle k (b.val : ℤ) :=
      vertexAngle_strictMono.monotone (by omega)
    linarith [hs.2, hu.1]
  · have hh : vertexAngle k (b.val + 1 : ℤ) ≤ vertexAngle k (a.val : ℤ) :=
      vertexAngle_strictMono.monotone (by omega)
    linarith [hu.2, hs.1]

lemma finite_faceEdges_cover_boundary :
    (⋃ (i : ZMod (2 * m)) (t : Fin (2 * k)),
      range (faceEdgeMap (k := k) i (t.val : ℤ))) =
      {q : FilledChain k m | ‖(coordinate q).val‖ = 1} := by
  ext q
  constructor
  · intro hq
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hq
    obtain ⟨t,s,rfl⟩ := Set.mem_iUnion.mp hi
    exact faceEdgeMap_coordinate_norm i (t.val : ℤ) s
  · intro hq
    obtain ⟨p,rfl⟩ := Quotient.mk_surjective q
    obtain ⟨t,s,hs⟩ := exists_finite_edgeParameter (k := k) p.2 hq
    exact Set.mem_iUnion.mpr ⟨p.1, Set.mem_iUnion.mpr ⟨t,s, by
      change faceMap p.1 (edgeParameter (t.val : ℤ) s) = faceMap p.1 p.2
      rw [hs]⟩⟩

end KsIndex.KarcherData.DiskCompactification
