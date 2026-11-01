module

public import KsIndexLean.EndpointRepresentative

@[expose] public section


open Set MeasureTheory intervalIntegral

noncomputable section
namespace KsIndex.Trace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Join two representatives at a cut; its isolated value at the cut is immaterial a.e. -/
def joinAt (c : ℝ) (f g : ℝ → E) (t : ℝ) : E := if t ≤ c then f t else g t

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma joinAt_integrable_left {a c : ℝ} (hac : a ≤ c) {f g : ℝ → E}
    (hf : IntervalIntegrable f volume a c) : IntervalIntegrable (joinAt c f g) volume a c := by
  apply hf.congr_uIoo
  rw [uIoo_of_le hac]
  intro t ht
  simp only [joinAt, ite_eq_left ht.2.le]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma joinAt_integrable_right {c b : ℝ} (hcb : c ≤ b) {f g : ℝ → E}
    (hg : IntervalIntegrable g volume c b) : IntervalIntegrable (joinAt c f g) volume c b := by
  apply hg.congr_uIoo
  rw [uIoo_of_le hcb]
  intro t ht
  simp only [joinAt, ite_eq_right (not_le.mpr ht.1)]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma joinAt_integrable {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) {f g : ℝ → E}
    (hf : IntervalIntegrable f volume a c) (hg : IntervalIntegrable g volume c b) :
    IntervalIntegrable (joinAt c f g) volume a b :=
  (joinAt_integrable_left hac hf).trans (joinAt_integrable_right hcb hg)

omit [CompleteSpace E] in
lemma integral_joinAt_left {a c t : ℝ} (hat : a ≤ t) (htc : t ≤ c) (f g : ℝ → E) :
    ∫ s in a..t, joinAt c f g s = ∫ s in a..t, f s := by
  apply integral_congr_Ioo_of_le hat
  intro s hs
  simp only [joinAt, ite_eq_left (hs.2.le.trans htc)]

omit [CompleteSpace E] in
lemma integral_joinAt_right {c t : ℝ} (hct : c ≤ t) (f g : ℝ → E) :
    ∫ s in c..t, joinAt c f g s = ∫ s in c..t, g s := by
  apply integral_congr_Ioo_of_le hct
  intro s hs
  simp only [joinAt, ite_eq_right (not_le.mpr hs.1)]

/-- The candidate across the seam is a single Bochner primitive plus one constant. -/
def joinedPrimitive (a c : ℝ) (u : E) (g h : ℝ → E) : ℝ → E :=
  fun t => u + primitiveFun a (joinAt c g h) t

omit [CompleteSpace E] in
lemma joinedPrimitive_continuousOn {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (u : E) {g h : ℝ → E} (hg : IntervalIntegrable g volume a c)
    (hh : IntervalIntegrable h volume c b) :
    ContinuousOn (joinedPrimitive a c u g h) (Icc a b) :=
  continuousOn_const.add (primitiveFun_continuousOn (hac.trans hcb)
    (joinAt_integrable hac hcb hg hh))

lemma joinedPrimitive_weak {a c b : ℝ} (hac : a < c) (hcb : c < b) (u : E)
    {g h : ℝ → E} (hg : IntervalIntegrable g volume a c)
    (hh : IntervalIntegrable h volume c b) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (joinedPrimitive a c u g h) (joinAt c g h) 1 := by
  have hc := TauCeti.hasWeakLineDerivOn_const (μ := volume) (Ω := intervalOpens a b) (v := 1) u
  have hp := primitive_weak_deriv (hac.trans hcb) (joinAt_integrable hac.le hcb.le hg hh)
  change TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
    (fun _ => u) (0 : ℝ → E) 1 at hc
  have hs := hc.add hp
  simp only [zero_add] at hs
  apply hs.congr_ae
  filter_upwards [] with t
  rfl

omit [CompleteSpace E] in
/-- On the left, the global primitive agrees with the original endpoint representative. -/
lemma joinedPrimitive_left {a c : ℝ} (hac : a < c) (f : ℝ → E) {g h : ℝ → E}
    (hg : IntervalIntegrable g volume a c) {t : ℝ} (ht : t ∈ Icc a c) :
    joinedPrimitive a c (representative hac f g a) g h t = representative hac f g t := by
  have he := representative_sub_eq_integral hac f hg (left_mem_Icc.mpr hac.le) ht
  simp only [joinedPrimitive, primitiveFun, integral_joinAt_left ht.1 ht.2]
  rw [← he]
  abel

omit [CompleteSpace E] in
/-- Matching at the seam makes the same primitive agree on the right as well. -/
lemma joinedPrimitive_right {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (f p : ℝ → E) {g h : ℝ → E} (hg : IntervalIntegrable g volume a c)
    (hh : IntervalIntegrable h volume c b)
    (hmatch : representative hac f g c = representative hcb p h c)
    {t : ℝ} (ht : t ∈ Icc c b) :
    joinedPrimitive a c (representative hac f g a) g h t = representative hcb p h t := by
  have hl := representative_sub_eq_integral hac f hg
    (left_mem_Icc.mpr hac.le) (right_mem_Icc.mpr hac.le)
  have hr := representative_sub_eq_integral hcb p hh (left_mem_Icc.mpr hcb.le) ht
  have hj := joinAt_integrable_right hcb.le (f := g) hh
  have hjt : IntervalIntegrable (joinAt c g h) volume c t :=
    hj.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le hcb.le]; exact Icc_subset_Icc le_rfl ht.2)
  have hi := integral_add_adjacent_intervals (joinAt_integrable_left hac.le (g := h) hg) hjt
  rw [integral_joinAt_left hac.le le_rfl, integral_joinAt_right ht.1] at hi
  simp only [joinedPrimitive, primitiveFun]
  rw [← hi, ← hl, ← hr, ← hmatch]
  abel

end KsIndex.Trace
