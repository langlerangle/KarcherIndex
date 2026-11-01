module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Tactic

@[expose] public section


noncomputable section
namespace KsIndex.Weierstrass

/-- Convention: X = Re ∫ Φ, with Φ = h(1-g², i(1+g²), 2g). -/
def phi1 (g h : ℂ) : ℂ := (1 - g ^ 2) * h
def phi2 (g h : ℂ) : ℂ := Complex.I * (1 + g ^ 2) * h
def phi3 (g h : ℂ) : ℂ := 2 * g * h

lemma weierstrass_null (g h : ℂ) :
    phi1 g h ^ 2 + phi2 g h ^ 2 + phi3 g h ^ 2 = 0 := by
  unfold phi1 phi2 phi3
  calc
    _ = (1 + Complex.I ^ 2) * (1 + g ^ 2) ^ 2 * h ^ 2 := by ring
    _ = 0 := by simp

def realSq (a b c : ℂ) : ℝ := a.re ^ 2 + b.re ^ 2 + c.re ^ 2
def imagSq (a b c : ℂ) : ℝ := a.im ^ 2 + b.im ^ 2 + c.im ^ 2
def realImagDot (a b c : ℂ) : ℝ := a.re * a.im + b.re * b.im + c.re * c.im

lemma null_equal_lengths {a b c : ℂ} (h : a ^ 2 + b ^ 2 + c ^ 2 = 0) :
    realSq a b c = imagSq a b c := by
  have hr := congrArg Complex.re h
  simp [pow_two, Complex.mul_re] at hr
  unfold realSq imagSq
  nlinarith

lemma null_orthogonal {a b c : ℂ} (h : a ^ 2 + b ^ 2 + c ^ 2 = 0) :
    realImagDot a b c = 0 := by
  have hi := congrArg Complex.im h
  simp [pow_two, Complex.mul_im] at hi
  unfold realImagDot
  nlinarith

lemma weierstrass_equal_lengths (g h : ℂ) :
    realSq (phi1 g h) (phi2 g h) (phi3 g h) =
      imagSq (phi1 g h) (phi2 g h) (phi3 g h) :=
  null_equal_lengths (weierstrass_null g h)

lemma weierstrass_orthogonal (g h : ℂ) :
    realImagDot (phi1 g h) (phi2 g h) (phi3 g h) = 0 :=
  null_orthogonal (weierstrass_null g h)

lemma weierstrass_real_metric (g h : ℂ) :
    realSq (phi1 g h) (phi2 g h) (phi3 g h) =
      ‖h‖ ^ 2 * (1 + ‖g‖ ^ 2) ^ 2 := by
  rw [Complex.sq_norm h, Complex.sq_norm g]
  simp [realSq, phi1, phi2, phi3, Complex.normSq_apply, pow_two]
  ring

lemma weierstrass_imag_metric (g h : ℂ) :
    imagSq (phi1 g h) (phi2 g h) (phi3 g h) =
      ‖h‖ ^ 2 * (1 + ‖g‖ ^ 2) ^ 2 := by
  rw [← weierstrass_equal_lengths]
  exact weierstrass_real_metric g h

lemma weierstrass_metric_pos (g h : ℂ) (hh : h ≠ 0) :
    0 < realSq (phi1 g h) (phi2 g h) (phi3 g h) := by
  rw [weierstrass_real_metric]
  exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hh)) (sq_pos_of_pos (by positivity))

end KsIndex.Weierstrass
