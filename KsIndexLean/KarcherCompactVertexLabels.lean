module

public import KsIndexLean.KarcherCompactCellOrientation

@[expose] public section


/-! Cyclic angular labels for the actual filled vertices. -/
noncomputable section
open Set
namespace KsIndex.KarcherData.DiskCompactification
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The cyclic label `t` denotes the puncture at angle `(2*t+1)*pi/(2*k)`. -/
def angularVertex (t : Fin (2 * k)) : VertexIndex k :=
  ⟨(Circle.exp (vertexAngle k (t.val : ℤ)) : ℂ),
    (mem_punctureFinset h.out).mpr (vertexAngle_mem_punctures _)⟩

lemma angularVertex_injective : Function.Injective (angularVertex (k := k)) := by
  intro a b he
  have htop : vertexAngle k (2 * k : ℤ) - vertexAngle k 0 ≤ 2 * Real.pi := by
    have hp := vertexAngle_add_period (k := k) 0 1
    simp only [mul_one, zero_add, Int.cast_one, one_mul] at hp
    linarith
  have ham : vertexAngle k (a.val : ℤ) ∈ Ico (vertexAngle k 0) (vertexAngle k (2 * k : ℤ)) :=
    ⟨vertexAngle_strictMono.monotone (by omega), vertexAngle_strictMono (by omega)⟩
  have hbm : vertexAngle k (b.val : ℤ) ∈ Ico (vertexAngle k 0) (vertexAngle k (2 * k : ℤ)) :=
    ⟨vertexAngle_strictMono.monotone (by omega), vertexAngle_strictMono (by omega)⟩
  have hec : Circle.exp (vertexAngle k (a.val : ℤ)) = Circle.exp (vertexAngle k (b.val : ℤ)) :=
    Circle.ext (congrArg (fun v : VertexIndex k => v.val) he)
  have hab := vertexAngle_strictMono.injective (Circle.exp_injOn_Ico htop ham hbm hec)
  apply Fin.ext
  exact_mod_cast hab

lemma angularVertex_bijective : Function.Bijective (angularVertex (k := k)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨angularVertex_injective, ?_⟩
  rw [Fintype.card_fin, Fintype.card_coe, punctureFinset_card h.out]

/-- A cyclic enumeration of all actual puncture vertices, not just a cardinality identity. -/
def angularVertexEquiv : Fin (2 * k) ≃ VertexIndex k :=
  Equiv.ofBijective angularVertex angularVertex_bijective

/-- The final angular endpoint closes up to the initial vertex. -/
lemma vertexAngle_full_turn :
    Circle.exp (vertexAngle k (2 * k : ℤ)) = Circle.exp (vertexAngle k 0) := by
  have hp := vertexAngle_add_period (k := k) 0 1
  simp only [mul_one, zero_add, Int.cast_one, one_mul] at hp
  rw [hp]
  exact Circle.exp_eq_exp.mpr ⟨1, by simp⟩

def angularSuccessor (t : Fin (2 * k)) : Fin (2 * k) :=
  ⟨(t.val + 1) % (2 * k), Nat.mod_lt _ (by have := h.out; omega)⟩

lemma angularVertex_successor (t : Fin (2 * k)) :
    (angularVertex (angularSuccessor t)).val =
      (Circle.exp (vertexAngle k (t.val + 1 : ℤ)) : ℂ) := by
  by_cases ht : t.val + 1 < 2 * k
  · simp only [angularVertex, angularSuccessor, Nat.mod_eq_of_lt ht, Nat.cast_add, Nat.cast_one]
  · have ht' : t.val + 1 = 2 * k := by omega
    have hz : (t.val : ℤ) + 1 = (2 * k : ℤ) := by exact_mod_cast ht'
    simp only [angularVertex, angularSuccessor, ht', Nat.mod_self, Nat.cast_zero, hz]
    exact congrArg (fun c : Circle => (c : ℂ)) vertexAngle_full_turn.symm

/-- The start of every face arc is the vertex with the same cyclic label. -/
lemma faceEdgeMap_start {m : ℕ} [NeZero m] (i : ZMod (2 * m)) (t : Fin (2 * k)) :
    faceEdgeMap (k := k) i (t.val : ℤ)
      ⟨vertexAngle k (t.val : ℤ), le_rfl, (vertexAngle_lt _).le⟩ =
      vertex (angularVertex t).val ((mem_punctureFinset h.out).mp (angularVertex t).property) := by
  apply (coordinate_eq_vertex_iff _ _ _).mp
  rfl

/-- The end of every face arc is the next cyclic vertex, including wraparound. -/
lemma faceEdgeMap_finish {m : ℕ} [NeZero m] (i : ZMod (2 * m)) (t : Fin (2 * k)) :
    faceEdgeMap (k := k) i (t.val : ℤ)
      ⟨vertexAngle k (t.val + 1 : ℤ), (vertexAngle_lt _).le, le_rfl⟩ =
      vertex (angularVertex (angularSuccessor t)).val
        ((mem_punctureFinset h.out).mp (angularVertex (angularSuccessor t)).property) := by
  apply (coordinate_eq_vertex_iff _ _ _).mp
  exact (angularVertex_successor t).symm

end KsIndex.KarcherData.DiskCompactification
