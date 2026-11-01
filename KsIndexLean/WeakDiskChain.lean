module

public import KsIndexLean.EnergySmoothSeamTrace

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.FaithfulInjection

/-- The actual incident-seam trace difference on a finite chain of weak disk classes. -/
def chainSeamOperator (k m : ℕ) [NeZero m] (n : ZMod (2 * m)) :
    (ZMod (2 * m) → ComplexH1) →L[ℂ]
      Lp ℂ 2 (circleMeasure.restrict (seamBoundary k m n)) :=
  (arcTrace (seamBoundary k m n)).comp (ContinuousLinearMap.proj n) -
    (arcTrace (seamBoundary k m n)).comp (ContinuousLinearMap.proj (n + 1))

def weakDiskChain (k m : ℕ) [NeZero m] : Submodule ℂ (ZMod (2 * m) → ComplexH1) :=
  ⨅ n, LinearMap.ker (chainSeamOperator k m n).toLinearMap

lemma mem_weakDiskChain (k m : ℕ) [NeZero m] (u : ZMod (2 * m) → ComplexH1) :
    u ∈ weakDiskChain k m ↔ ∀ n,
      arcTrace (seamBoundary k m n) (u n) = arcTrace (seamBoundary k m n) (u (n + 1)) := by
  simp only [weakDiskChain, Submodule.mem_iInf, LinearMap.mem_ker]
  change (∀ n, arcTrace (seamBoundary k m n) (u n) -
    arcTrace (seamBoundary k m n) (u (n + 1)) = 0) ↔ _
  simp only [sub_eq_zero]

lemma isClosed_weakDiskChain (k m : ℕ) [NeZero m] :
    IsClosed (weakDiskChain k m : Set (ZMod (2 * m) → ComplexH1)) := by
  simp only [weakDiskChain, Submodule.coe_iInf]
  exact isClosed_iInter (fun n => (chainSeamOperator k m n).isClosed_ker)

lemma energySmoothCopy_add {k m : ℕ} (u v : EnergySmooth k m) (n : ZMod (2 * m)) :
    energySmoothCopy (u + v) n = energySmoothCopy u n + energySmoothCopy v n := by
  apply valueCLM_injective
  rw [map_add]
  apply Lp.ext
  filter_upwards [energySmoothCopy_value_ae (u + v) n, energySmoothCopy_value_ae u n,
    energySmoothCopy_value_ae v n,
    Lp.coeFn_add (valueCLM (energySmoothCopy u n)) (valueCLM (energySmoothCopy v n))]
    with z hs hu hv ha
  rw [ha, Pi.add_apply, hs, hu, hv]
  rfl

lemma energySmoothCopy_smul {k m : ℕ} (c : ℂ) (u : EnergySmooth k m) (n : ZMod (2 * m)) :
    energySmoothCopy (c • u) n = c • energySmoothCopy u n := by
  apply valueCLM_injective
  rw [map_smul]
  apply Lp.ext
  filter_upwards [energySmoothCopy_value_ae (c • u) n, energySmoothCopy_value_ae u n,
    Lp.coeFn_smul c (valueCLM (energySmoothCopy u n))] with z hs hu hc
  rw [hc, Pi.smul_apply, hs, hu]
  rfl

/-- The proved smooth-to-weak map preserves every incident Sobolev trace match. -/
def energySmoothToWeakChain (k m : ℕ) [NeZero m] :
    EnergySmooth k m →ₗ[ℂ] weakDiskChain k m where
  toFun u := ⟨energySmoothCopy u, (mem_weakDiskChain k m _).mpr (energySmooth_seam_trace_eq u)⟩
  map_add' u v := Subtype.ext (funext (energySmoothCopy_add u v))
  map_smul' c u := Subtype.ext (funext (energySmoothCopy_smul c u))

lemma energySmoothToWeakChain_value_ae (k m : ℕ) [NeZero m]
    (u : EnergySmooth k m) (n : ZMod (2 * m)) :
    (valueCLM ((energySmoothToWeakChain k m u).val n) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] u.val n := energySmoothCopy_value_ae u n

end KsIndex.Trace
