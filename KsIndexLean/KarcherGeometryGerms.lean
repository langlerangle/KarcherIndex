module

public import KsIndexLean.KarcherCurvature

@[expose] public section


/-! First and second geometric data depend only on the local immersion germ
and are unchanged by ambient translations. -/
noncomputable section
open Topology
namespace KsIndex.KarcherData

lemma firstFundamentalForm_germ {X Y : ℂ → AmbientTriple} {w : ℂ}
    (h : X =ᶠ[𝓝 w] Y) (u v : ℂ) :
    firstFundamentalForm X w u v = firstFundamentalForm Y w u v := by
  simp only [firstFundamentalForm, h.fderiv_eq]

lemma chartUnitNormal_germ {X Y : ℂ → AmbientTriple} {w : ℂ}
    (h : X =ᶠ[𝓝 w] Y) : chartUnitNormal X w = chartUnitNormal Y w := by
  simp only [chartUnitNormal, h.fderiv_eq]

lemma scalarHessian_germ {f g : ℂ → ℝ} {w : ℂ}
    (h : f =ᶠ[𝓝 w] g) :
    bilinearIteratedFDerivTwo ℝ f w = bilinearIteratedFDerivTwo ℝ g w := by
  simp only [bilinearIteratedFDerivTwo, (h.fderiv (𝕜 := ℝ)).fderiv_eq]

lemma secondFundamentalForm_germ {X Y : ℂ → AmbientTriple} {w : ℂ}
    (h : X =ᶠ[𝓝 w] Y) : secondFundamentalForm X w = secondFundamentalForm Y w := by
  have h1 : (fun z => (X z).1) =ᶠ[𝓝 w] (fun z => (Y z).1) :=
    h.mono (fun z hz => congrArg (fun p : AmbientTriple => p.1) hz)
  have h2 : (fun z => (X z).2.1) =ᶠ[𝓝 w] (fun z => (Y z).2.1) :=
    h.mono (fun z hz => congrArg (fun p : AmbientTriple => p.2.1) hz)
  have h3 : (fun z => (X z).2.2) =ᶠ[𝓝 w] (fun z => (Y z).2.2) :=
    h.mono (fun z hz => congrArg (fun p : AmbientTriple => p.2.2) hz)
  simp only [secondFundamentalForm, chartUnitNormal_germ h,
    scalarHessian_germ h1, scalarHessian_germ h2, scalarHessian_germ h3]

lemma chartMeanCurvature_germ {X Y : ℂ → AmbientTriple} {w : ℂ}
    (h : X =ᶠ[𝓝 w] Y) : chartMeanCurvature X w = chartMeanCurvature Y w := by
  simp only [chartMeanCurvature, firstFundamentalForm_germ h, secondFundamentalForm_germ h]

lemma firstFundamentalForm_translate (X : ℂ → AmbientTriple) (t : AmbientTriple) (w u v : ℂ) :
    firstFundamentalForm (fun z => t + X z) w u v = firstFundamentalForm X w u v := by
  simp only [firstFundamentalForm, fderiv_const_add]

lemma chartUnitNormal_translate (X : ℂ → AmbientTriple) (t : AmbientTriple) (w : ℂ) :
    chartUnitNormal (fun z => t + X z) w = chartUnitNormal X w := by
  simp only [chartUnitNormal, fderiv_const_add]

lemma secondFundamentalForm_translate (X : ℂ → AmbientTriple) (t : AmbientTriple) (w : ℂ) :
    secondFundamentalForm (fun z => t + X z) w = secondFundamentalForm X w := by
  have hh (f : ℂ → ℝ) (c : ℝ) :
      bilinearIteratedFDerivTwo ℝ (fun z => c + f z) w =
        bilinearIteratedFDerivTwo ℝ f w := by
    have hd : fderiv ℝ (fun z => c + f z) = fderiv ℝ f := by
      funext z
      exact fderiv_const_add c
    simp only [bilinearIteratedFDerivTwo, hd]
  simp only [secondFundamentalForm, chartUnitNormal_translate, Prod.fst_add, Prod.snd_add,
    hh]

lemma chartMeanCurvature_translate (X : ℂ → AmbientTriple) (t : AmbientTriple) (w : ℂ) :
    chartMeanCurvature (fun z => t + X z) w = chartMeanCurvature X w := by
  simp only [chartMeanCurvature, firstFundamentalForm_translate, secondFundamentalForm_translate]

lemma conformalSecondFundamentalNorm_germ {X Y : ℂ → AmbientTriple} {w : ℂ}
    (h : X =ᶠ[𝓝 w] Y) (q : ℝ) :
    conformalSecondFundamentalNorm X w q = conformalSecondFundamentalNorm Y w q := by
  simp only [conformalSecondFundamentalNorm, conformalSecondFundamentalNormSq,
    secondFundamentalForm_germ h]

lemma conformalSecondFundamentalNorm_translate
    (X : ℂ → AmbientTriple) (t : AmbientTriple) (w : ℂ) (q : ℝ) :
    conformalSecondFundamentalNorm (fun z => t + X z) w q =
      conformalSecondFundamentalNorm X w q := by
  simp only [conformalSecondFundamentalNorm, conformalSecondFundamentalNormSq,
    secondFundamentalForm_translate]

end KsIndex.KarcherData
