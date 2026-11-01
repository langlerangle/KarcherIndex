module

/-
Run with `lake env lean scripts/check_task_b_route.lean`.
Inspect declaration types and proof bodies, not module imports: the alternative
ArcEstimate file is imported for shared definitions and algebra, but its numerical
proof and the evaluated Basel sum must not occur in the faithful route.
-/
import all KsIndexLean.ArcEstimate
import all KsIndexLean.ArcEstimateFaithful
import all KsIndexLean.ArcForm
import all KsIndexLean.ArcKernel
import all KsIndexLean.ArcPsi
import all KsIndexLean.ArcRationalFaithful
import all KsIndexLean.ArcSigma
import all KsIndexLean.ArcSpace
import all KsIndexLean.ArcTailIntegral
import all KsIndexLean.ArcUpper
import all KsIndexLean.ArcUpperEdge
import all KsIndexLean.CircleQ
import all KsIndexLean.FormIndex
import all KsIndexLean.FormIndexExt
import all KsIndexLean.GammaOne
import all KsIndexLean.SIsometry
import all KsIndexLean.SingleArc
import all KsIndexLean.SquareWave
import all KsIndexLean.TestField
import Lean.Util.FoldConsts




open Lean Elab Command

set_option maxRecDepth 10000 in
run_cmd withoutExporting do
  let env ← getEnv
  let roots := #[
    ``KsIndex.ArcEstimateFaithful.Sconst_lt_paper,
    ``KsIndex.ArcEstimateFaithful.Q_lower_coeff,
    ``KsIndex.ArcUpper.NQformArc_pos_on_slice,
    ``KsIndex.ArcUpper.indArc_add_nulArc_le_one_interior]
  let forbidden := #[
    ``KsIndex.ArcEstimate.Sconst_lt,
    ``KsIndex.ArcEstimate.Sconst_le,
    ``KsIndex.ArcEstimate.Sconst_term_le,
    ``KsIndex.ArcEstimate.tsum_domTerm,
    ``KsIndex.ArcEstimate.H_lt_R,
    ``KsIndex.ArcEstimate.cubic_ineq,
    ``KsIndex.ArcPsi.tsum_pairW,
    ``KsIndex.ArcPsi.hasSum_pairW]
  let required := #[
    ``KsIndex.ArcTailIntegral.first_interval_gap,
    ``KsIndex.ArcTailIntegral.cube_sum_lt_integral,
    ``KsIndex.ArcRationalFaithful.R_sub_H_ge,
    ``KsIndex.ArcRationalFaithful.R_ge_four_thirds]
  for root in roots do
    let mut pending := #[root]
    let mut visited : NameSet := {}
    while !pending.isEmpty do
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then
        throwError "Forbidden alternate-proof dependency {name} in {root}"
      let some info := env.find? name
        | throwError "Missing declaration {name} while inspecting {root}"
      -- External modules precede this project in the import graph and cannot
      -- depend on any of the project declarations checked by this audit.
      let some idx := env.getModuleIdxFor? name
        | throwError "Missing defining module for {name}"
      unless (`KsIndexLean).isPrefixOf env.header.moduleNames[idx]! do continue
      for dependency in info.getUsedConstantsAsSet.toList do
        if !visited.contains dependency then pending := pending.push dependency
    for name in required do
      unless visited.contains name do
        throwError "Expected paper-route dependency {name} absent from {root}"
    logInfo m!"PASS {root}: required paper intermediates present; alternate numerical route absent."
