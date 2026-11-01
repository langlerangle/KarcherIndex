module

/-
# Arc selection and end-chart coverage for general `k`

At a puncture `p`, the equation `p^(2k) = −1` gives `Re(p^k) = 0` and
`Im(p^k) = ±1`. Thus `Re((p·q)^k) = −Im(p^k)·Im(q^k)`. Combined with a
parity choice and a unit-circle hypothesis, this identity identifies the seam
arc containing an end-chart image.

The polynomial `Sk k q` satisfies `Im(q^k) = Im(q)·Re(Sk k q)` without
assuming `|q| = 1` or dividing by `Im(q)`. For `k > 0`, continuity and
`Sk k 1 = k` give a neighborhood where its real part is positive. The sign of
`Im(q)` and the unit-circle condition for arc membership remain separate inputs.

`endField_coverage_general` supplies arbitrarily small nonzero chart preimages
for every copy's values near a unit-circle point, including points on the
circle. It assumes `m > 0`, seam value agreement and puncture vanishing.
These are algebraic and coverage results; analytic regularity and boundedness
of end fields are established by their consumers.
-/
public import KsIndexLean.EndFieldWitness

@[expose] public section


noncomputable section
open Complex
namespace KsIndex.EndField
open KsIndex.Surface KsIndex.EndChart

/-! ### The puncture sign fact for general `k`

`p ∈ punctures k ⟺ p^{2k} = −1`, so `(p^k)² = −1`: the `k`-th power is a square root of `−1`,
hence `Re(p^k) = 0` and `Im(p^k) = ±1`.  (Verbatim generalization of `cube_re_im`.) -/

/-- At a puncture of `Ξ_k`, the `k`-th power squares to `−1`. -/
lemma pk_sq_of_puncture {p : ℂ} {k : ℕ} (hp : p ∈ punctures k) : (p ^ k) ^ 2 = -1 := by
  have h : p ^ (2 * k) = -1 := hp
  calc (p ^ k) ^ 2 = p ^ (2 * k) := by rw [← pow_mul, Nat.mul_comm k 2]
    _ = -1 := h

/-- Hence `Re(p^k) = 0` and `Im(p^k)² = 1` — the `k`-th power is `±i`. -/
lemma pk_re_im {p : ℂ} {k : ℕ} (hp : p ∈ punctures k) :
    (p ^ k).re = 0 ∧ (p ^ k).im ^ 2 = 1 := by
  have h2 : (p ^ k) ^ 2 = -1 := pk_sq_of_puncture hp
  set z : ℂ := p ^ k with hz
  have hr : z.re * z.re - z.im * z.im = -1 := by
    have := congrArg Complex.re h2
    rwa [sq, Complex.mul_re, show ((-1 : ℂ)).re = -1 from by simp] at this
  have hi : z.re * z.im + z.im * z.re = 0 := by
    have := congrArg Complex.im h2
    rwa [sq, Complex.mul_im, show ((-1 : ℂ)).im = 0 from by simp] at this
  have hmul : z.re * z.im = 0 := by linear_combination hi / 2
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exfalso; nlinarith [hr, h, sq_nonneg z.re]
  refine ⟨hre0, ?_⟩
  nlinarith [hr, hre0]

/-- The imaginary part of `p^k` is nonzero (`±1`) — the transversality making the zero of
`Re(w^k)` at `p` a genuine sign crossing. -/
lemma pk_im_ne {p : ℂ} {k : ℕ} (hp : p ∈ punctures k) : (p ^ k).im ≠ 0 := by
  intro h
  have := (pk_re_im hp).2
  rw [h] at this
  norm_num at this

/-! ### General-`k` puncture / circle norms

`p ∈ punctures k ⟹ ‖p‖ = 1` (generalizes `norm_eq_one_of_mem_punctures`), and circle points
through `p` stay on the unit circle (generalizes `norm_circlePt`).  Route-independent; these are
the geometric inputs the arc block consumes via its `‖p‖ = 1` hypotheses. -/

/-- A puncture of `Ξ_k` lies on the unit circle: `‖p‖ = 1` (for `k ≠ 0`; `punctures 0 = ∅`). -/
lemma norm_eq_one_of_mem_punctures_k {p : ℂ} {k : ℕ} (hk : k ≠ 0) (hp : p ∈ punctures k) :
    ‖p‖ = 1 := by
  have h2k : 2 * k ≠ 0 := Nat.mul_ne_zero two_ne_zero hk
  have hpow : ‖p‖ ^ (2 * k) = 1 := by
    have := congrArg norm hp
    simpa [norm_pow] using this
  rcases lt_trichotomy ‖p‖ 1 with h | h | h
  · exfalso; have hlt := pow_lt_one₀ (norm_nonneg p) h h2k; linarith [hpow, hlt]
  · exact h
  · exfalso; have hgt := one_lt_pow₀ h h2k; linarith [hpow, hgt]

/-- Circle points through a puncture stay on the unit circle: `‖p·e^{iθ}‖ = 1`. -/
lemma norm_circlePt_k {p : ℂ} {k : ℕ} (hk : k ≠ 0) (hp : p ∈ punctures k) (θ : ℝ) :
    ‖p * Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
  rw [norm_mul, norm_eq_one_of_mem_punctures_k hk hp, one_mul, Complex.norm_exp_ofReal_mul_I]

/-! ### The general-`k` sign identity

`Re((p·q)^k) = −Im(p^k)·Im(q^k)` when `Re(p^k) = 0`.  Generalizes `re_cube_mul` via `mul_pow`. -/

/-- **The sign bridge**: `Re((p·q)^k) = −Im(p^k)·Im(q^k)` when `Re(p^k) = 0`. -/
lemma re_kpow_mul {p q : ℂ} {k : ℕ} (hp : (p ^ k).re = 0) :
    ((p * q) ^ k).re = -(p ^ k).im * (q ^ k).im := by
  rw [mul_pow, Complex.mul_re, hp]; ring

/-! ### The identity on the end chart

`endChart = p·q` with `q = conj(p)·endChart` (uses `p·conj p = ‖p‖² = 1`; both helpers
`endChart_eq_p_mul_conj`, `conj_mul_endChart` are already general in `k` and `m`). -/

/-- `Re((endChart)^k) = −Im(p^k)·Im(q^k)`, the `re_kpow_mul` bridge applied to `endChart = p·q`. -/
lemma reKpow_endChart_eq {p : ℂ} {k : ℕ} (hpunc : p ∈ punctures k) (hp : ‖p‖ = 1) (m : ℕ) (ζ : ℂ) :
    ((endChart p m ζ) ^ k).re
      = -(p ^ k).im * (((starRingEnd ℂ) p * endChart p m ζ) ^ k).im := by
  have key := re_kpow_mul (q := (starRingEnd ℂ) p * endChart p m ζ) (pk_re_im hpunc).1
  rwa [endChart_eq_p_mul_conj hp m ζ] at key

/-! ### Arc membership from the sign of `Im(q^k)`

The following lemmas take the imaginary-part sign, unit-circle membership and
parity condition as hypotheses. Positive and negative imaginary parts select
the reflected and direct families respectively. -/

/-- **General-`k` `a₂` arc membership.**  With `Im(q^k) > 0` and the parity pin
`0 < (−1)^(parity(c+2N))·Im(p^k)`, the chart image lands in `seamArc k m (c+2N−1)`:
`Re((endChart)^k) = −Im(p^k)·Im(q^k)` gives arc sign `< 0`. -/
lemma arc_mem_of_imKpow_pos {p : ℂ} {k : ℕ} (hpunc : p ∈ punctures k) (hp : ‖p‖ = 1)
    {m : ℕ} {ζ : ℂ} {N : ℤ} {c : ZMod (2 * m)}
    (hseam : ‖endChart p m ζ‖ = 1)
    (hQ : 0 < (((starRingEnd ℂ) p * endChart p m ζ) ^ k).im)
    (hpar : 0 < (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)))).val * (p ^ k).im) :
    endChart p m ζ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1) := by
  have hre := reKpow_endChart_eq hpunc hp m ζ
  have hc : c + 2 * (N : ZMod (2 * m)) - 1 + 1 = c + 2 * (N : ZMod (2 * m)) := by ring
  simp only [seamArc, arc, Set.mem_ofPred_eq]
  rw [hc]
  refine ⟨hseam, ?_⟩
  rw [hre]
  nlinarith [hpar, hQ]

/-- **General-`k` `a₁` arc membership.**  With `Im(q^k) < 0` and the parity pin
`(−1)^(parity(n+1))·Im(p^k) < 0`, the chart image lands in `seamArc k m n`. -/
lemma arc_mem_of_imKpow_neg {p : ℂ} {k : ℕ} (hpunc : p ∈ punctures k) (hp : ‖p‖ = 1)
    {m : ℕ} {ζ : ℂ} {n : ZMod (2 * m)}
    (hseam : ‖endChart p m ζ‖ = 1)
    (hQ : (((starRingEnd ℂ) p * endChart p m ζ) ^ k).im < 0)
    (hpar : (-1 : ℝ) ^ (parity m (n + 1)).val * (p ^ k).im < 0) :
    endChart p m ζ ∈ seamArc k m n := by
  have hre := reKpow_endChart_eq hpunc hp m ζ
  simp only [seamArc, arc, Set.mem_ofPred_eq]
  refine ⟨hseam, ?_⟩
  rw [hre]
  nlinarith [hpar, hQ]

/-! ### The circle sign identity

Along the unit circle through a puncture, `Re((p·exp(iθ))^k)` is
`−Im(p^k)·sin(kθ)`, with `Im(p^k) = ±1`. -/

/-- **`Re((p·e^{iθ})^k) = −Im(p^k)·sin(kθ)`** along the unit circle through a puncture. -/
lemma reKpow_circle {p : ℂ} {k : ℕ} (hp : p ∈ punctures k) (θ : ℝ) :
    ((p * Complex.exp ((θ : ℂ) * Complex.I)) ^ k).re
      = -(p ^ k).im * Real.sin ((k : ℝ) * θ) := by
  have hre : (p ^ k).re = 0 := (pk_re_im hp).1
  have hexp : (p * Complex.exp ((θ : ℂ) * Complex.I)) ^ k
      = p ^ k * Complex.exp ((((k : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
    have hc : ((k : ℕ) : ℂ) * ((θ : ℂ) * Complex.I) = (((k : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [mul_pow, ← Complex.exp_nat_mul, hc]
  rw [hexp, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, hre]
  ring

/-! ### The sign of `Im(q^k)` near `q = 1`

The sign estimate uses the division-free polynomial `S_k(q) = Σ_{i<k} qⁱ·conj(q)^{k-1-i}`.
The finite geometric-sum factorization `q^k − conj(q)^k = (q − conj q)·S_k(q)` gives, on imaginary
parts (using `conj(q)^k = conj(q^k)` and `(q − conj q).re = 0`), the identity

    Im(q^k) = Im(q) · Re(S_k(q)),

with NO `|q|=1` assumption and NO division by `Im(q)`.  Since `S_k(1) = k > 0`, continuity gives a
neighborhood of `q = 1` on which `Re(S_k(q)) > 0`; there the sign of `Im(q^k)` is exactly that of
`Im(q)`.  The sign of `Im(q)` and the seam/membership are supplied separately (the circle/angle
lemmas and `arc_mem_of_imKpow_*`), not automatically from closeness. -/

/-- The division-free factor `S_k(q) = Σ_{i<k} qⁱ·conj(q)^{k-1-i}` (conj-symmetric, hence real;
`geom_sum₂`-shaped so Mathlib's `Commute.mul_geom_sum₂` applies directly). -/
def Sk (k : ℕ) (q : ℂ) : ℂ := ∑ i ∈ Finset.range k, q ^ i * ((starRingEnd ℂ) q) ^ (k - 1 - i)

/-- **The core identity** `Im(q^k) = Im(q)·Re(S_k(q))` — division-free, no `|q|=1`. -/
lemma imKpow_eq (k : ℕ) (q : ℂ) : (q ^ k).im = q.im * (Sk k q).re := by
  have hfact : (q - (starRingEnd ℂ) q) * Sk k q = q ^ k - ((starRingEnd ℂ) q) ^ k :=
    (Commute.all q ((starRingEnd ℂ) q)).mul_geom_sum₂ k
  have him := congrArg Complex.im hfact
  simp only [Complex.mul_im, Complex.sub_im, Complex.sub_re, Complex.conj_re, Complex.conj_im,
    ← map_pow] at him
  linear_combination -him / 2

/-- `S_k(1) = k`. -/
lemma Sk_one (k : ℕ) : Sk k 1 = (k : ℂ) := by
  simp [Sk]

/-- `S_k` is continuous (a finite sum of monomials in `q` and `conj q`). -/
lemma continuous_Sk (k : ℕ) : Continuous (Sk k) := by
  unfold Sk
  refine continuous_finsetSum _ (fun i _ => ?_)
  exact (continuous_pow i).mul (Complex.continuous_conj.pow (k - 1 - i))

/-- **The sign neighborhood**: a positive radius about `q = 1` on which `Re(S_k(q)) > 0`
(`S_k(1) = k > 0` + continuity).  The explicit value is unneeded — local existence suffices, to be
intersected downstream with the other domain conditions. -/
lemma Sk_re_pos_near_one (k : ℕ) (hk : 0 < k) :
    ∃ r > 0, ∀ q : ℂ, ‖q - 1‖ < r → 0 < (Sk k q).re := by
  have hopen : IsOpen {q : ℂ | 0 < (Sk k q).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_Sk k))
  have hmem : (1 : ℂ) ∈ {q : ℂ | 0 < (Sk k q).re} := by
    show 0 < (Sk k (1 : ℂ)).re
    rw [Sk_one, Complex.natCast_re]
    exact_mod_cast hk
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  refine ⟨r, hr, fun q hq => hsub ?_⟩
  rwa [Metric.mem_ball, dist_eq_norm]

/-- **`Im(q^k) > 0`** from `Im(q) > 0` and the sign neighborhood (`Re(S_k(q)) > 0`). -/
lemma imKpow_pos_of_imPos {k : ℕ} {q : ℂ} (hq : 0 < q.im) (hS : 0 < (Sk k q).re) :
    0 < (q ^ k).im := by
  rw [imKpow_eq]; exact mul_pos hq hS

/-- **`Im(q^k) < 0`** from `Im(q) < 0` and the sign neighborhood (`Re(S_k(q)) > 0`). -/
lemma imKpow_neg_of_imNeg {k : ℕ} {q : ℂ} (hq : q.im < 0) (hS : 0 < (Sk k q).re) :
    (q ^ k).im < 0 := by
  rw [imKpow_eq]; exact mul_neg_of_neg_of_pos hq hS

/-! ### the end-chart `Im(q^k)` sign near the seam

`q = conj(p)·endChart` has `Im(q) = ‖ζ‖^m·sin(angT)` (k-independent geometry, from
`conj_mul_endChart`/`conj_mul_pow_im`), so once the `S_k`-positivity `0 < Re(S_k(q))` is supplied
(from `Sk_re_pos_near_one`, i.e. `ζ` small so `q` is near 1), the sign of `Im(q^k)` is that of
`sin(angT)`.  These feed `arc_mem_of_imKpow_*` exactly as `q_imCube_pos`/`_neg` fed `arc_mem_a2`/
`a1` in the k=3 witness — but via the division-free `S_k` route, so they need NEITHER `cos(angT)`
NOR `‖endChart‖=1` (the k=3 cubic `4q.re²−1` factor is replaced by `Re(S_k(q))`). -/

/-- `Im((conj p · endChart)^k) > 0` from `sin(angT) > 0` and `Re(S_k(q)) > 0` (reflected `a₂`). -/
lemma q_imKpow_pos {p : ℂ} {k m : ℕ} {ζ : ℂ} (hp : ‖p‖ = 1) (hζ : ζ ≠ 0)
    (hsin : 0 < Real.sin (angT p m ζ))
    (hS : 0 < (Sk k ((starRingEnd ℂ) p * endChart p m ζ)).re) :
    0 < (((starRingEnd ℂ) p * endChart p m ζ) ^ k).im := by
  have hρ : 0 < ‖ζ‖ ^ m := pow_pos (norm_pos_iff.mpr hζ) m
  have hqim : ((starRingEnd ℂ) p * endChart p m ζ).im = ‖ζ‖ ^ m * Real.sin (angT p m ζ) := by
    rw [conj_mul_endChart hp m ζ, Complex.add_im, Complex.one_im, conj_mul_pow_im hp]; ring
  exact imKpow_pos_of_imPos (by rw [hqim]; exact mul_pos hρ hsin) hS

/-- `Im((conj p · endChart)^k) < 0` from `sin(angT) < 0` and `Re(S_k(q)) > 0` (direct `a₁`). -/
lemma q_imKpow_neg {p : ℂ} {k m : ℕ} {ζ : ℂ} (hp : ‖p‖ = 1) (hζ : ζ ≠ 0)
    (hsin : Real.sin (angT p m ζ) < 0)
    (hS : 0 < (Sk k ((starRingEnd ℂ) p * endChart p m ζ)).re) :
    (((starRingEnd ℂ) p * endChart p m ζ) ^ k).im < 0 := by
  have hρ : 0 < ‖ζ‖ ^ m := pow_pos (norm_pos_iff.mpr hζ) m
  have hqim : ((starRingEnd ℂ) p * endChart p m ζ).im = ‖ζ‖ ^ m * Real.sin (angT p m ζ) := by
    rw [conj_mul_endChart hp m ζ, Complex.add_im, Complex.one_im, conj_mul_pow_im hp]; ring
  exact imKpow_neg_of_imNeg (by rw [hqim]; exact mul_neg_of_pos_of_neg hρ hsin) hS

/-! ### The parity choice for general `k`

The first producer of the general-k boundedness chain: at a puncture `(p^k).im = ±1 ≠ 0`
(`pk_im_ne`), so a parity bit `c ∈ {0,1}` can be chosen making `(−1)^(parity m c)·Im(p^k) > 0` —
the pin `arc_mem_of_imKpow_pos`/`_neg` consume.  Generalizes `EndFieldWitness.exists_parity_pin`. -/

/-- **The parity pin, general `k`**: choose `c` with `(−1)^(parity m c)·Im(p^k) > 0`. -/
lemma exists_parity_pin_general {k m : ℕ} {p : ℂ} (hpunc : p ∈ punctures k) :
    ∃ c : ZMod (2 * m), 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ k).im := by
  rcases lt_or_gt_of_ne (pk_im_ne hpunc) with hlt | hgt
  · refine ⟨1, ?_⟩
    rw [show (parity m (1 : ZMod (2 * m))).val = 1 from by rw [map_one]; rfl, pow_one]
    linarith [hlt]
  · refine ⟨0, ?_⟩
    rw [show (parity m (0 : ZMod (2 * m))).val = 0 from by rw [map_zero]; rfl, pow_zero]
    linarith [hgt]

/-! ### Shrinking chart coverage for all copies

The coverage theorem uses only seam value agreement and puncture vanishing,
so it applies independently of an analytic field-space choice. On the unit
circle, `Re(w^k) = 0` identifies the punctures; other circle points use seam
agreement to match the two copy parities. -/

open KsIndex.B2

/-- On the unit circle, `Re(wᵏ) = 0` forces `w` to be a puncture (`w^{2k} = −1`).
Generalizes `mem_punctures_of_reCube_zero`. -/
lemma mem_punctures_of_reKpow_zero {w : ℂ} {k : ℕ} (hw : ‖w‖ = 1) (hre0 : (w ^ k).re = 0) :
    w ∈ punctures k := by
  have hz : Complex.normSq (w ^ k) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow, hw, one_pow]; norm_num
  have him : (w ^ k).im * (w ^ k).im = 1 := by
    rw [Complex.normSq_apply, hre0] at hz; linarith
  have hsq2 : (w ^ k) ^ 2 = -1 := by
    rw [sq]; apply Complex.ext
    · simp only [Complex.mul_re, Complex.neg_re, Complex.one_re, hre0]; linarith
    · simp only [Complex.mul_im, Complex.neg_im, Complex.one_im, hre0]; ring
  show w ^ (2 * k) = -1
  rw [mul_comm 2 k, pow_mul, hsq2]

/-- **Shrinking chart coverage for all copies.** For `m > 0`, every copy
`n` and point `w ≠ p` in the closed unit disk sufficiently near the unit-circle point `p`, there is a small `ζ` with
`endFieldWith p u (endIdx m c p) ζ = u n w`: direct preimage for one parity, reflected for the other
(interior), and on the circle `SeamVal` (non-puncture) or `PunctureZero` (puncture) closes the
opposite parity. The hypotheses are `SeamVal` and `PunctureZero`; no smoothness
or energy assumption is needed. -/
lemma endField_coverage_general {k m : ℕ} (hm : 0 < m) {u : ZMod (2 * m) → ℂ → ℂ}
    (p : ℂ) (hp : ‖p‖ = 1) (hsv : SeamVal k u) (hpz : PunctureZero k u) (c : ZMod (2 * m)) :
    ∀ r : ℝ, 0 < r → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ZMod (2 * m)) (w : ℂ),
      ‖w - p‖ < δ → ‖w‖ ≤ 1 → w ≠ p →
        ∃ ζ : ℂ, 0 < ‖ζ‖ ∧ ‖ζ‖ < r ∧ endFieldWith p u (endIdx m c p) ζ = u n w := by
  intro r hr
  have hrm : 0 < r ^ m := pow_pos hr m
  refine ⟨min (r ^ m / 2) (1 / 2), lt_min (by positivity) (by norm_num), ?_⟩
  intro n w hwδ hw1 hwp
  have hδ1 : min (r ^ m / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hδr : min (r ^ m / 2) (1 / 2) ≤ r ^ m / 2 := min_le_left _ _
  have hwhalf : 1 / 2 < ‖w‖ := by
    have h1 := norm_sub_norm_le p w; rw [norm_sub_rev] at h1; nlinarith [h1, hwδ, hδ1, hp]
  have hw0 : w ≠ 0 := by rw [← norm_pos_iff]; linarith [hwhalf]
  have hwpz : w - p ≠ 0 := sub_ne_zero.mpr hwp
  -- the chart-radius bound ‖ζ‖ < r from ‖ζ‖^m = ‖w-p‖
  have hζrad : ∀ ζ : ℂ, ‖ζ‖ ^ m = ‖w - p‖ → ‖ζ‖ < r := fun ζ hζ => by
    apply lt_of_pow_lt_pow_left₀ m hr.le; rw [hζ]; nlinarith [hwδ, hδr, hrm]
  have hζpos : ∀ ζ : ℂ, ζ ^ m = w - p → 0 < ‖ζ‖ := fun ζ hζ => by
    rw [norm_pos_iff]; intro h; rw [h, zero_pow hm.ne'] at hζ; exact hwpz hζ.symm
  obtain ⟨J, hJ | hJ⟩ := exists_two_mul_or (n - c)
  · -- direct leg: n = c + 2J
    have hnc : n = c + 2 * (J : ZMod (2 * m)) := by linear_combination hJ
    obtain ⟨ζ, hζm, hζnorm, hζidx⟩ := exists_root_endIdx hm c p hwpz J
    have hew : endChart p m ζ = w := by rw [endChart, hζm]; ring
    exact ⟨ζ, hζpos ζ hζm, hζrad ζ hζnorm, by rw [endField_direct_eval p u c hew hw1, hζidx, ← hnc]⟩
  · -- parity c+1: n = c + 2J + 1
    have hnc : n = c + 2 * (J : ZMod (2 * m)) + 1 := by linear_combination hJ
    rcases lt_or_eq_of_le hw1 with hwlt | hweq
    · -- interior reflected
      have hσpz : Bracket.σ w - p ≠ 0 := by
        intro hh
        exact hwp (by rw [← Bracket.σ_σ w, sub_eq_zero.mp hh, Bracket.σ_self hp])
      obtain ⟨ζ, hζm, hζnorm, hζidx⟩ := exists_root_endIdx hm c p hσpz J
      have hew : endChart p m ζ = Bracket.σ w := by rw [endChart, hζm]; ring
      have hζn' : ‖ζ‖ ^ m = ‖w - p‖ / ‖w‖ := by rw [hζnorm, norm_sigma_sub hp hw0]
      have hwpos : (0 : ℝ) < ‖w‖ := by linarith [hwhalf]
      refine ⟨ζ, ?_, ?_, ?_⟩
      · rw [norm_pos_iff]; rintro rfl; rw [zero_pow hm.ne'] at hζm; exact hσpz hζm.symm
      · apply lt_of_pow_lt_pow_left₀ m hr.le
        rw [hζn', div_lt_iff₀ hwpos]; nlinarith [hwδ, hδr, hwhalf, hrm]
      · rw [endField_reflected_eval p u c hew hw0 hwlt, hζidx,
          show c + 2 * (J : ZMod (2 * m)) + 1 = n from hnc.symm]
    · -- circle boundary
      have hwnorm : ‖w‖ = 1 := hweq
      by_cases hre0 : (w ^ k).re = 0
      · -- w is a puncture: PunctureZero
        have hwpunc : w ∈ punctures k := mem_punctures_of_reKpow_zero hwnorm hre0
        obtain ⟨ζ, hζm, hζnorm, _⟩ := exists_mpow_root hm hwpz
        have hew : endChart p m ζ = w := by rw [endChart, hζm]; ring
        exact ⟨ζ, hζpos ζ hζm, hζrad ζ hζnorm,
          by rw [endField_direct_eval p u c hew hw1, hpz _ w hwpunc, hpz n w hwpunc]⟩
      · -- non-puncture: SeamVal on the incident arc
        have hsign : (-1 : ℝ) ^ (parity m n).val * (w ^ k).re ≠ 0 :=
          mul_ne_zero (pow_ne_zero _ (by norm_num)) hre0
        rcases lt_or_gt_of_ne hsign with hlt | hgt
        · -- w ∈ seamArc (n-1); root endIdx = n-1
          have hmem : w ∈ seamArc k m (n - 1) := by
            simp only [seamArc, arc, Set.mem_ofPred_eq]
            exact ⟨hwnorm, by rw [show (n - 1) + 1 = n from by ring]; exact hlt⟩
          obtain ⟨ζ, hζm, hζnorm, hζidx⟩ := exists_root_endIdx hm c p hwpz J
          have hew : endChart p m ζ = w := by rw [endChart, hζm]; ring
          refine ⟨ζ, hζpos ζ hζm, hζrad ζ hζnorm, ?_⟩
          rw [endField_direct_eval p u c hew hw1, hζidx,
            show c + 2 * (J : ZMod (2 * m)) = n - 1 from by rw [hnc]; ring]
          have hsvn := hsv (n - 1) w hmem
          rw [show (n - 1) + 1 = n from by ring] at hsvn
          exact hsvn.symm
        · -- w ∈ seamArc n; root endIdx = n+1
          have hmem : w ∈ seamArc k m n := by
            simp only [seamArc, arc, Set.mem_ofPred_eq]
            refine ⟨hwnorm, ?_⟩
            rw [show parity m (n + 1) = parity m n + 1 from by rw [map_add, map_one],
              neg_one_pow_parity_add_one]
            nlinarith [hgt]
          obtain ⟨ζ, hζm, hζnorm, hζidx⟩ := exists_root_endIdx hm c p hwpz (J + 1)
          have hew : endChart p m ζ = w := by rw [endChart, hζm]; ring
          refine ⟨ζ, hζpos ζ hζm, hζrad ζ hζnorm, ?_⟩
          rw [endField_direct_eval p u c hew hw1, hζidx,
            show c + 2 * ((J + 1 : ℤ) : ZMod (2 * m)) = n + 1 from by rw [hnc]; push_cast; ring]
          exact hsv n w hmem

end KsIndex.EndField
