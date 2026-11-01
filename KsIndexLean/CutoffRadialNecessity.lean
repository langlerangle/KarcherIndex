module

public import KsIndexLean.DiskCutoffGluing

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- A weak joined cutoff profile cannot conceal a jump in the genuine disk traces. -/
theorem cutoff_trace_eq_of_radial_weak (η : C(Circle₁, ℝ)) (u v : ComplexH1) (c : ℂ)
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens (1 / 2) 2)
      (joinAt 1 (fun r => circleMul η (diskProfile u r))
        (fun r => circleMul η (c • diskProfile v r⁻¹)))
      (joinAt 1 (fun r => circleMul η (diskRadialProfile u r))
        (fun r => circleMul η (c • invertedRadialDeriv (diskRadialProfile v) r))) 1) :
    circleMul η (diskTraceCLM u) = circleMul η (c • diskTraceCLM v) := by
  have hv := invertedProfile_weak (disk_weak_polar v).2.2 (disk_weak_polar v).2.1
  have hg := invertedRadialDeriv_integrable (disk_weak_polar v).2.1
  have hp := weak_deriv_const_smul_complex c hv
  have hq := hg.smul c
  have he := match_of_weak_joinAt (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 2)
    (circleMul_weakInterval η (disk_weak_polar u).2.2) (circleMul_weakInterval η hp)
    ⟨(circleMulCLM η).integrable_comp (disk_weak_polar u).2.1.1,
      (circleMulCLM η).integrable_comp (disk_weak_polar u).2.1.2⟩
    ⟨(circleMulCLM η).integrable_comp hq.1, (circleMulCLM η).integrable_comp hq.2⟩ hw
  rw [representative_circleMul (by norm_num) η (disk_weak_polar u).2.2
      (disk_weak_polar u).2.1 (by norm_num),
    representative_circleMul (by norm_num) η hp hq (by norm_num),
    representative_smul_complex (by norm_num) c hv hg (by norm_num), Pi.smul_apply,
    invertedProfile_endpoint (disk_weak_polar v).2.2 (disk_weak_polar v).2.1] at he
  exact he

end KsIndex.Trace
