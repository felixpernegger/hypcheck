import Lean
import Std
open Lean Elab Command Meta

/-- Adds `HypCheckDrop.<T>.h<i> : T'` with T's own proof term, binder `i` dropped (normal compile:
the kernel checks it like any declaration). `neg` drops the binder even if used, replacing it by a
wrong term (must fail). -/
elab "#drop_check " id:ident i:num neg:(&" neg")? : command => liftTermElabM do
  let n := id.getId; let i := i.getNat
  let ci ← getConstInfo n
  let some v := ci.value? (allowOpaque := true) | throwError "no value"
  let (ty, pf) ← forallTelescope ci.type fun xs body => lambdaBoundedTelescope v xs.size fun ys b => do
    let rest := ys.eraseIdxIfInBounds i
    let some x := ys[i]? | throwError "idx"
    if b.containsFVar x.fvarId! && neg.isNone then throwError "used"
    let b := if neg.isSome then b.replaceFVar x (mkConst ``True.intro) else b
    return (← mkForallFVars rest (body.replaceFVars xs ys), ← mkLambdaFVars rest b)
  let d := (`HypCheckDrop ++ privateToUserName n).str s!"h{i}"
  addDecl (.thmDecl { name := d, levelParams := ci.levelParams, type := ty, value := pf })
  logInfo m!"OK {d}"

#drop_check Std.Iter.toListRev_eq_toListRev_toIterM 3
#drop_check Std.DHashMap.Raw.insertMany_list_singleton 8
#drop_check Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition 14
#drop_check Std.HashSet.forM_eq_forM 6
#drop_check List.forM_map 4
#drop_check Std.IterM.length_eq_fold 6
#drop_check Std.Rio.mem_succ_iff 7
#drop_check Std.IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition 10
#drop_check Std.Rco.toArray_iter_eq_toArray 4
#drop_check Std.TreeSet.forM_eq_forM 5
#drop_check Array.foldrM_wfParam 4
#drop_check Std.DHashMap.Const.equiv_iff_toList_perm 7
#drop_check Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition 14
#drop_check Std.Rii.size_eq_match_rci 6
#drop_check Std.Rci.isSome_succMany?_of_lt_length_toList 6
#drop_check Std.DHashMap.Raw.forIn_eq_forIn 6
#drop_check Std.DTreeMap.Raw.get?_insertMany_list_of_mem 7
#drop_check Std.IterM.toList_filterMapM_filterMapWithPostcondition 12
#drop_check Std.HashSet.Raw.equiv_iff_toList_perm 5
#drop_check Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMapM 7
#drop_check Std.IterM.DefaultConsumers.forIn'_eq_match_step 6
#drop_check Std.Rii.getElem?_toList_eq 5
#drop_check Std.Internal.List.getKey_eq_getKeyD 3
#drop_check Std.Rcc.size_eq_ite_roc 7
#drop_check Std.toList_roc_eq_toList_rcc_of_isSome_succ? 5
#drop_check Std.IterM.all_mapM 16
#drop_check Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition 10
#drop_check Std.Ric.succ_mem_succ_iff 7
#drop_check Lean.Grind.Order.le_of_offset_eq_2_k 6
#drop_check Std.Iter.allM_eq_forIn 8
-- negative controls (hypothesis used): each must fail
#drop_check Std.DHashMap.Internal.Raw₀.getKey?_inter_of_contains_eq_false_right 6 neg
#drop_check Std.TreeMap.Raw.isEmpty_inter_left 8 neg
#drop_check Std.DTreeMap.Equiv.constGetD_eq 8 neg
#drop_check Std.DTreeMap.Internal.Impl.contains_findCell 8 neg
#drop_check Std.TreeSet.Raw.Equiv.minD_eq 7 neg
