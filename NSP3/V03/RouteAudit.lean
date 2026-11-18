import NSP3.V03.Main
import NSP3.P3Main
import NSP3.P4Final
import Lean.Util.FoldConsts

/-! This metaprogram checks the proof-constant graph; it supplies no mathematical axiom. -/
open Lean Elab Command

private def isProjectName (n : Name) : Bool :=
  n.toString.startsWith "NSP3." || n.toString.startsWith "_private.NSP3."

private partial def projectClosure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n::tail =>
    if seen.contains n || !isProjectName n then projectClosure env tail seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => projectClosure env tail seen
      | some ci =>
        let used := ci.type.getUsedConstants.toList ++
          match ci.value? (allowOpaque := true) with
          | none => []
          | some value => value.getUsedConstants.toList
        projectClosure env (used ++ tail) seen

run_cmd do
  let closure := projectClosure (← getEnv) [`NSP3.V03.P3_MAIN]
  let required := [
    `NSP3.V03.noFull_unified,
    `NSP3.V03.eight_profiles_sharp,
    `NSP3.V03.eight_profiles_finite,
    `NSP3.V03.endpointBF_eq_actual,
    `NSP3.V03.numerical_semigroup_rho_upper]
  for n in required do
    unless closure.contains n do
      throwError "V03 proof route is missing required dependency {n}"
  let excluded := [
    `NSP3.P3_MAIN,
    `NSP3.all_m_rho_values_isGreatest,
    `NSP3.all_m_sharp_attainment,
    `NSP3.intrinsic_rho_sharp,
    `NSP3.cyclicStaircase_boundary_card_sharp,
    `NSP3.fullSupport_ordered_symbolic_sharp,
    `NSP3.noFull_sharp_bound_ordered,
    `NSP3.noFull_balanced_sharp,
    `NSP3.noFull_unbalanced_sharp,
    `NSP3.fullSupport_t4_q444_symbolic_sharp,
    `NSP3.fullSupport_q544_BF_sharp_lower,
    `NSP3.fullSupport_smallwidth_six_BW_lower]
  for n in excluded do
    if closure.contains n then
      throwError "V03 proof route still depends on replaced conclusion {n}"
  logInfo "V03_P3_ROUTE_PASS: new capacity inputs present; replaced conclusions absent"

run_cmd do
  let closure := projectClosure (← getEnv) [`NSP3.V03.P4_e3]
  unless closure.contains `NSP3.V03.sqrt_lt_binomial do
    throwError "V03 P4 route does not use the short binomial comparison"
  if closure.contains `NSP3.c3_binomial_gap_identity then
    throwError "V03 P4 route still uses the old quartic expansion"
  logInfo "V03_P4_ROUTE_PASS: short binomial comparison present; old quartic absent"

#print axioms NSP3.V03.P3_MAIN
#print axioms NSP3.V03.P4_e3

run_cmd do
  let env ← getEnv
  let p3 := projectClosure env [`NSP3.P3_MAIN]
  unless p3.contains `NSP3.V03.P3_MAIN do
    throwError "Public P3 endpoint does not forward to the V03 proof"
  let p4 := projectClosure env [`NSP3.P4_e3]
  unless p4.contains `NSP3.V03.P4_e3 do
    throwError "Public P4 endpoint does not forward to the V03 proof"
  if p4.contains `NSP3.c3_binomial_gap_identity then
    throwError "Public P4 endpoint still uses the replaced quartic expansion"
  logInfo "PUBLIC_V03_ROUTE_PASS: original P3/P4 names forward to V03 proofs"

