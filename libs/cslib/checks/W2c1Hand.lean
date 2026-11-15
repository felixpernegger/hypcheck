import Lean.Elab.Command
import Cslib
-- CSLib toolkit header (copy of hypcheck runs/hand22/Header.lean with `import Cslib`; ~150 MB, 1.5 s to import)


set_option linter.unusedVariables false

open Lean Meta Elab Term

/-- `_private.M.«0».x` ↦ `_private.M.0.x`: all-digit string components become numeric. -/
def hcFixName : Name → Name
  | .str p s => if !s.isEmpty && s.all Char.isDigit then .num (hcFixName p) s.toNat! else .str (hcFixName p) s
  | .num p k => .num (hcFixName p) k
  | .anonymous => .anonymous

/-- The constant named by `T`: a public name (resolved as usual) or a private one written in full
as `_private.Mod.«0».x` (private names are not reachable by their short name from another module). -/
def hcConst (T : Ident) : TermElabM Name := do
  let n := hcFixName T.getId
  if isPrivateName n then
    unless (← getEnv).contains n do throwError "unknown private constant {n}"
    return n
  realizeGlobalConstNoOverloadWithInfo T

/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- `priv% c`: the constant `c` (public, or private written as `_private.Mod.«0».x`), with fresh
universe levels; use it to mention private definitions and lemmas inside statements and proofs. -/
elab "priv% " c:ident : term => do
  mkConstWithFreshMVarLevels (← hcConst c)

section

namespace W2c1
open Cslib Cslib.SKI Relation

theorem chInj {n m : ℕ} {a : SKI} (h1 : IsChurch n a) (h2 : IsChurch m a) : n = m :=
  isChurch_injective _ _ _ _ h1 h2 ⟨_, .refl, .refl⟩
theorem blInj {u v : Bool} {a : SKI} (h1 : IsBool u a) (h2 : IsBool v a) : u = v :=
  isBool_injective _ _ _ _ h1 h2 ⟨_, .refl, .refl⟩
theorem stuck {x y : SKI} (hx : x.RedexFree) (h : ReflTransGen Red x y) : x = y :=
  (redexFree_iff_mred_eq.mp hx y).mp h
theorem rfSS : RedexFree (SKI.S ⬝ SKI.S) := by simp [RedexFree]
theorem rfKS : RedexFree (SKI.K ⬝ SKI.S) := by simp [RedexFree]
theorem rfSK : RedexFree (SKI.S ⬝ SKI.K) := by simp [RedexFree]
theorem nSSKS : ¬ ReflTransGen Red (SKI.S ⬝ SKI.S) (SKI.K ⬝ SKI.S) := fun h => by
  have := stuck rfSS h; simp at this
theorem nSSSK : ¬ ReflTransGen Red (SKI.S ⬝ SKI.S) (SKI.S ⬝ SKI.K) := fun h => by
  have := stuck rfSS h; simp at this
-- K ⬝ c computes the constant function
theorem cK {k : ℕ} {c : SKI} (hc : IsChurch k c) : Computes (SKI.K ⬝ c) (fun _ => Part.some k) :=
  fun n cn _ m hm => by
    rw [Part.mem_some_iff.mp hm]; exact isChurch_trans _ (MRed.K _ _) hc
theorem cI : Computes SKI.I (fun n => Part.some n) :=
  fun n cn h m hm => by rw [Part.mem_some_iff.mp hm]; exact isChurch_trans _ (MRed.I _) h

end W2c1

open Cslib Cslib.SKI Relation W2c1

-- `Cslib.SKI.computes_of_total` idx 3: necessary (t = I, g = id, f = const 1)
theorem w2c1_cot3 : ¬ drop0% Cslib.SKI.computes_of_total 3 := fun h => by
  have := h (t := SKI.I) (f := fun _ => Part.some 1) id
    (fun n cn hc => isChurch_trans _ (MRed.I _) hc) 0 _ zero_correct 1 (Part.mem_some _)
  exact absurd (chInj this (isChurch_trans _ (MRed.I _) zero_correct)) (by decide)

-- `Cslib.SKI.computes_of_total` idx 4: necessary (t = K ⬝ One, f = g = const 0)
theorem w2c1_cot4 : ¬ drop0% Cslib.SKI.computes_of_total 4 := fun h => by
  have := h (t := SKI.K ⬝ SKI.One) (f := fun _ => Part.some 0) (fun _ => 0) (fun _ => rfl)
    0 _ zero_correct 0 (Part.mem_some _)
  exact absurd (chInj this (isChurch_trans _ (MRed.K _ _) one_correct)) (by decide)

-- `Cslib.SKI.comp_computes` idx 4: necessary (tf = K ⬝ One claimed to compute const 0, tg = I)
theorem w2c1_cc4 : ¬ drop0% Cslib.SKI.comp_computes 4 := fun h => by
  have h1 := h (f := fun _ => Part.some 0) (tf := SKI.K ⬝ SKI.One) cI 0 _ zero_correct 0 (by simp [PFun.comp])
  have h2 := comp_computes (cK one_correct) cI 0 _ zero_correct 1 (by simp [PFun.comp])
  exact absurd (chInj h1 h2) (by decide)

-- `Cslib.SKI.comp_computes` idx 5: necessary (tg = K ⬝ One claimed to compute const 0, tf = I)
theorem w2c1_cc5 : ¬ drop0% Cslib.SKI.comp_computes 5 := fun h => by
  have h1 := h (g := fun _ => Part.some 0) (tg := SKI.K ⬝ SKI.One) cI 0 _ zero_correct 0 (by simp [PFun.comp])
  have h2 := comp_computes cI (cK one_correct) 0 _ zero_correct 1 (by simp [PFun.comp])
  exact absurd (chInj h1 h2) (by decide)

-- `Cslib.SKI.pair_computes` idx 4: necessary (tf = K ⬝ One claimed to compute const 0, tg = I)
theorem w2c1_pc4 : ¬ drop0% Cslib.SKI.pair_computes 4 := fun h => by
  have h1 := h (f := fun _ => Part.some 0) (tf := SKI.K ⬝ SKI.One) cI 0 _ zero_correct (Nat.pair 0 0)
    (by simp [Seq.seq])
  have h2 := pair_computes (cK one_correct) cI 0 _ zero_correct (Nat.pair 1 0) (by simp [Seq.seq])
  exact absurd (chInj h1 h2) (by decide)

-- `Cslib.SKI.pair_computes` idx 5: necessary (tg = K ⬝ One claimed to compute const 0, tf = I)
theorem w2c1_pc5 : ¬ drop0% Cslib.SKI.pair_computes 5 := fun h => by
  have h1 := h (g := fun _ => Part.some 0) (tg := SKI.K ⬝ SKI.One) cI 0 _ zero_correct (Nat.pair 0 0)
    (by simp [Seq.seq])
  have h2 := pair_computes cI (cK one_correct) 0 _ zero_correct (Nat.pair 0 1) (by simp [Seq.seq])
  exact absurd (chInj h1 h2) (by decide)

-- `Cslib.SKI.MRed.head` idx 3: necessary (a = S, a' = K, b = S; S ⬝ S is redex-free)
theorem w2c1_mh3 : ¬ drop0% Cslib.SKI.MRed.head 3 := fun h => nSSKS (h (a := SKI.S) (a' := SKI.K) SKI.S)

-- `Cslib.SKI.MRed.tail` idx 3: necessary (a = S, b = S, b' = K)
theorem w2c1_mt3 : ¬ drop0% Cslib.SKI.MRed.tail 3 := fun h => nSSSK (h SKI.S (b := SKI.S) (b' := SKI.K))

-- `Cslib.SKI.parallel_mRed` idx 4: necessary (a = S, a' = K, b = b' = S)
theorem w2c1_pm4 : ¬ drop0% Cslib.SKI.parallel_mRed 4 := fun h =>
  nSSKS (h (a := SKI.S) (a' := SKI.K) (b := SKI.S) (b' := SKI.S) .refl)

-- `Cslib.SKI.parallel_mRed` idx 5: necessary (a = a' = S, b = S, b' = K)
theorem w2c1_pm5 : ¬ drop0% Cslib.SKI.parallel_mRed 5 := fun h =>
  nSSSK (h (a := SKI.S) (a' := SKI.S) (b := SKI.S) (b' := SKI.K) .refl)

-- `Cslib.SKI.parallel_red` idx 4: necessary (a = S, a' = K, b = I ⬝ S, b' = S; unique normal forms)
theorem w2c1_pr4 : ¬ drop0% Cslib.SKI.parallel_red 4 := fun h => by
  have h1 := h (a := SKI.S) (a' := SKI.K) (b := SKI.I ⬝ SKI.S) (b' := SKI.S) (.red_I _)
  have h2 : ReflTransGen Red (SKI.S ⬝ (SKI.I ⬝ SKI.S)) (SKI.S ⬝ SKI.S) := MRed.tail _ (MRed.I _)
  have := unique_normal_form h1 h2 rfKS rfSS; simp at this

-- `Cslib.SKI.parallel_red` idx 5: necessary (a = I ⬝ S, a' = S, b = S, b' = K)
theorem w2c1_pr5 : ¬ drop0% Cslib.SKI.parallel_red 5 := fun h => by
  have h1 := h (a := SKI.I ⬝ SKI.S) (a' := SKI.S) (b := SKI.S) (b' := SKI.K) (.red_I _)
  have h2 : ReflTransGen Red ((SKI.I ⬝ SKI.S) ⬝ SKI.S) (SKI.S ⬝ SKI.S) := MRed.head _ (MRed.I _)
  have := unique_normal_form h1 h2 rfSK rfSS; simp at this

-- `Cslib.SKI.join_mRed_head` idx 3: necessary (x = S, x' = K, y = S)
theorem w2c1_jh3 : ¬ drop0% Cslib.SKI.join_mRed_head 3 := fun h => by
  have := eq_of_join_mRed_redexFree (h (x := SKI.S) (x' := SKI.K) SKI.S) rfSS rfKS; simp at this

-- `Cslib.SKI.mJoin_red_head` idx 3: necessary (x = S, x' = K, y = S)
theorem w2c1_mjh3 : ¬ drop0% Cslib.SKI.mJoin_red_head 3 := fun h => by
  have := eq_of_join_mRed_redexFree (h (x := SKI.S) (x' := SKI.K) SKI.S) rfSS rfKS; simp at this

-- `Cslib.SKI.join_mRed_tail` idx 3: necessary (x = S, y = S, y' = K)
theorem w2c1_jt3 : ¬ drop0% Cslib.SKI.join_mRed_tail 3 := fun h => by
  have := eq_of_join_mRed_redexFree (h SKI.S (y := SKI.S) (y' := SKI.K)) rfSS rfSK; simp at this

-- `Cslib.SKI.mJoin_red_tail` idx 3: necessary (x = S, y = S, y' = K)
theorem w2c1_mjt3 : ¬ drop0% Cslib.SKI.mJoin_red_tail 3 := fun h => by
  have := eq_of_join_mRed_redexFree (h SKI.S (y := SKI.S) (y' := SKI.K)) rfSS rfSK; simp at this

-- `Cslib.SKI.RedexFree.normal_red` idx 1: necessary (x = I ⬝ S steps)
theorem w2c1_nr1 : ¬ drop0% Cslib.SKI.RedexFree.normal_red 1 := fun h =>
  h (x := SKI.I ⬝ SKI.S) ⟨_, .red_I _⟩

-- `Cslib.SKI.eq_of_join_mRed_redexFree` idx 3: necessary (x = I ⬝ S, y = S)
theorem w2c1_ej3 : ¬ drop0% Cslib.SKI.eq_of_join_mRed_redexFree 3 := fun h => by
  have := h (x := SKI.I ⬝ SKI.S) (y := SKI.S) ⟨_, MRed.I _, .refl⟩ (by simp [RedexFree]); simp at this

-- `Cslib.SKI.eq_of_mJoin_red_redexFree` idx 3: necessary (x = I ⬝ S, y = S)
theorem w2c1_emj3 : ¬ drop0% Cslib.SKI.eq_of_mJoin_red_redexFree 3 := fun h => by
  have := h (x := SKI.I ⬝ SKI.S) (y := SKI.S) ⟨_, MRed.I _, .refl⟩ (by simp [RedexFree]); simp at this

-- `Cslib.SKI.isBool_injective` idx 4: necessary (x = y = TT, u = false, v = true)
theorem w2c1_bi4 : ¬ drop0% Cslib.SKI.isBool_injective 4 := fun h =>
  absurd (h TT TT false true TT_correct ⟨_, .refl, .refl⟩) (by decide)

-- `Cslib.SKI.isBool_injective` idx 5: necessary (x = y = TT, u = true, v = false)
theorem w2c1_bi5 : ¬ drop0% Cslib.SKI.isBool_injective 5 := fun h =>
  absurd (h TT TT true false TT_correct ⟨_, .refl, .refl⟩) (by decide)

-- `Cslib.SKI.isBool_injective` idx 6: necessary (x = TT, y = FF)
theorem w2c1_bi6 : ¬ drop0% Cslib.SKI.isBool_injective 6 := fun h =>
  absurd (h TT FF true false TT_correct FF_correct) (by decide)

-- `Cslib.SKI.isChurch_injective` idx 4: necessary (x = y = One, n = 0, m = 1)
theorem w2c1_ci4 : ¬ drop0% Cslib.SKI.isChurch_injective 4 := fun h =>
  absurd (h SKI.One SKI.One 0 1 one_correct ⟨_, .refl, .refl⟩) (by decide)

-- `Cslib.SKI.isChurch_injective` idx 5: necessary (x = y = Zero, n = 0, m = 1)
theorem w2c1_ci5 : ¬ drop0% Cslib.SKI.isChurch_injective 5 := fun h =>
  absurd (h SKI.Zero SKI.Zero 0 1 zero_correct ⟨_, .refl, .refl⟩) (by decide)

-- `Cslib.SKI.isChurch_injective` idx 6: necessary (x = Zero, y = One)
theorem w2c1_ci6 : ¬ drop0% Cslib.SKI.isChurch_injective 6 := fun h =>
  absurd (h SKI.Zero SKI.One 0 1 zero_correct one_correct) (by decide)

-- `Cslib.SKI.rice` idx 2: necessary (P = K ⬝ FF)
theorem w2c1_rice2 : ¬ drop0% Cslib.SKI.rice 2 := fun h =>
  h (P := SKI.K ⬝ FF) (fun _ => .inr (MRed.K _ _)) ⟨SKI.S, MRed.K _ _⟩

-- `Cslib.SKI.rice` idx 3: necessary (P = K ⬝ TT)
theorem w2c1_rice3 : ¬ drop0% Cslib.SKI.rice 3 := fun h =>
  h (P := SKI.K ⬝ TT) (fun _ => .inl (MRed.K _ _)) ⟨SKI.S, MRed.K _ _⟩

-- `Cslib.SKI.rice'` idx 1: necessary (P = I: I ⬝ S has normal form S)
theorem w2c1_ricep1 : ¬ drop0% Cslib.SKI.rice' 1 := fun h => by
  rcases h (P := SKI.I) with h | h
  · have := unique_normal_form (h SKI.S) (MRed.I _) (by simp [TT, RedexFree]) (by simp [RedexFree])
    simp [TT] at this
  · have := unique_normal_form (h SKI.S) (MRed.I _) (by simp [FF, RedexFree]) (by simp [RedexFree])
    simp [FF] at this

end

section

namespace W2c1
open Cslib Cslib.SKI Relation
theorem lHd {ns ms : List ℕ} {c : SKI} (h1 : IsChurchList ns c) (h2 : IsChurchList ms c) :
    ns.headD 0 = ms.headD 0 :=
  chInj (SKI.List.head_correct ns c h1) (SKI.List.head_correct ms c h2)
theorem lTl {ns ms : List ℕ} {c : SKI} (h1 : IsChurchList ns c) (h2 : IsChurchList ms c) :
    ns.tail.headD 0 = ms.tail.headD 0 :=
  lHd (SKI.List.tail_correct ns c h1) (SKI.List.tail_correct ms c h2)
theorem lpair {ns ms : List ℕ} {a b : SKI} (ha : IsChurchList ns a) (hb : IsChurchList ms b) :
    IsChurchListPair ns ms (MkPair ⬝ a ⬝ b) :=
  ⟨isChurchList_trans (fst_correct a b) ha, isChurchList_trans (snd_correct a b) hb⟩
end W2c1

open Cslib Cslib.SKI Relation W2c1

-- `Cslib.SKI.isChurchList_trans` idx 3: necessary (cns' = Nil, cns = toChurch [1])
theorem w2c1_clt3 : ¬ drop0% Cslib.SKI.isChurchList_trans 3 := fun h => by
  have := lHd (h (ns := []) (cns := SKI.List.toChurch [1]) SKI.List.nil_correct) (SKI.List.toChurch_correct [1])
  simp at this

-- `Cslib.SKI.isChurchList_trans` idx 4: necessary (cns = cns' = S, ns = [] and [1])
theorem w2c1_clt4 : ¬ drop0% Cslib.SKI.isChurchList_trans 4 := fun h => by
  have := lHd (h (ns := []) (cns := SKI.S) (cns' := SKI.S) .refl) (h (ns := [1]) (cns' := SKI.S) .refl)
  simp at this

-- `Cslib.SKI.IsChurchListPair.fst` idx 3: necessary (prev = [] and [1], same p)
theorem w2c1_clpf3 : ¬ drop0% Cslib.SKI.IsChurchListPair.fst 3 := fun h => by
  have := lHd (h (prev := []) (curr := []) (p := SKI.S)) (h (prev := [1]) (curr := []) (p := SKI.S))
  simp at this

-- `Cslib.SKI.IsChurchListPair.snd` idx 3: necessary (curr = [] and [1], same p)
theorem w2c1_clps3 : ¬ drop0% Cslib.SKI.IsChurchListPair.snd 3 := fun h => by
  have := lHd (h (prev := []) (curr := []) (p := SKI.S)) (h (prev := []) (curr := [1]) (p := SKI.S))
  simp at this

-- `Cslib.SKI.isChurchListPair_trans` idx 4: necessary (p' = MkPair Nil Nil, p = MkPair [1] Nil)
theorem w2c1_clpt4 : ¬ drop0% Cslib.SKI.isChurchListPair_trans 4 := fun h => by
  have h1 := h (p := MkPair ⬝ SKI.List.toChurch [1] ⬝ SKI.List.Nil)
    (lpair SKI.List.nil_correct SKI.List.nil_correct)
  have := lHd h1.1 (lpair (SKI.List.toChurch_correct [1]) SKI.List.nil_correct).1
  simp at this

-- `Cslib.SKI.isChurchListPair_trans` idx 5: necessary (p = p' = S, prev = [] and [1])
theorem w2c1_clpt5 : ¬ drop0% Cslib.SKI.isChurchListPair_trans 5 := fun h => by
  have := lHd (h (prev := []) (curr := []) (p := SKI.S) (p' := SKI.S) .refl).1
    (h (prev := [1]) (curr := []) (p := SKI.S) (p' := SKI.S) .refl).1
  simp at this

-- `Cslib.SKI.List.cons_correct` idx 4: necessary (x = 0 and 1, same cx = S)
theorem w2c1_cons4 : ¬ drop0% Cslib.SKI.List.cons_correct 4 := fun h => by
  have := lHd (h (x := 0) (cx := SKI.S) SKI.List.nil_correct) (h (x := 1) (cx := SKI.S) SKI.List.nil_correct)
  simp at this

-- `Cslib.SKI.List.cons_correct` idx 5: necessary (xs = [] and [1], same cxs = S)
theorem w2c1_cons5 : ¬ drop0% Cslib.SKI.List.cons_correct 5 := fun h => by
  have := lTl (h (xs := []) (cxs := SKI.S) zero_correct) (h (xs := [1]) (cxs := SKI.S) zero_correct)
  simp at this

-- `Cslib.SKI.List.singleton_correct` idx 2: necessary (x = 0 and 1, same cx)
theorem w2c1_sing2 : ¬ drop0% Cslib.SKI.List.singleton_correct 2 := fun h => by
  have := lHd (h (x := 0) (cx := SKI.S)) (h (x := 1) (cx := SKI.S))
  simp at this

-- `Cslib.SKI.List.headD_correct` idx 2: necessary (d = 0 and 1, same cd, ns = [])
theorem w2c1_hd2 : ¬ drop0% Cslib.SKI.List.headD_correct 2 := fun h => by
  have := chInj (h (d := 0) (cd := SKI.S) SKI.List.nil_correct) (h (d := 1) (cd := SKI.S) SKI.List.nil_correct)
  simp at this

-- `Cslib.SKI.List.headD_correct` idx 5: necessary (ns = [] and [1], same cns)
theorem w2c1_hd5 : ¬ drop0% Cslib.SKI.List.headD_correct 5 := fun h => by
  have := chInj (h zero_correct (ns := []) (cns := SKI.S)) (h zero_correct (ns := [1]) (cns := SKI.S))
  simp at this

-- `Cslib.SKI.List.head_correct` idx 2: necessary (ns = [] and [1], same cns)
theorem w2c1_head2 : ¬ drop0% Cslib.SKI.List.head_correct 2 := fun h => by
  have := chInj (h [] SKI.S) (h [1] SKI.S)
  simp at this

-- `Cslib.SKI.List.tailStep_correct` idx 4: necessary (x = 0 and 1, same cx, xs = [])
theorem w2c1_ts4 : ¬ drop0% Cslib.SKI.List.tailStep_correct 4 := fun h => by
  have hp := lpair SKI.List.nil_correct SKI.List.nil_correct
  have := lHd (h (x := 0) (xs := []) (cx := SKI.S) hp).2 (h (x := 1) (xs := []) (cx := SKI.S) hp).2
  simp at this

-- `Cslib.SKI.List.tailStep_correct` idx 5: necessary (xs = [] and [1], same p)
theorem w2c1_ts5 : ¬ drop0% Cslib.SKI.List.tailStep_correct 5 := fun h => by
  have := lHd (h (xs := []) (p := SKI.S) zero_correct).1 (h (xs := [1]) (p := SKI.S) zero_correct).1
  simp at this

-- `Cslib.SKI.List.tailFold_correct` idx 2: necessary (ns = [] and [1]; both pairs are reducts of one term)
theorem w2c1_tf2 : ¬ drop0% Cslib.SKI.List.tailFold_correct 2 := fun h => by
  obtain ⟨p1, r1, h1⟩ := h [] SKI.S
  obtain ⟨p2, r2, h2⟩ := h [1] SKI.S
  have := lHd (isChurchListPair_trans r1 h1).2 (isChurchListPair_trans r2 h2).2
  simp at this

-- `Cslib.SKI.List.tail_correct` idx 2: necessary (ns = [0] and [0, 1], same cns)
theorem w2c1_tail2 : ¬ drop0% Cslib.SKI.List.tail_correct 2 := fun h => by
  have := lHd (h [0] SKI.S) (h [0, 1] SKI.S)
  simp at this

-- `Cslib.SKI.List.prependZero_correct` idx 2: necessary (ns = [] and [1], same cns)
theorem w2c1_pz2 : ¬ drop0% Cslib.SKI.List.prependZero_correct 2 := fun h => by
  have := lTl (h (ns := []) (cns := SKI.S)) (h (ns := [1]) (cns := SKI.S))
  simp at this

-- `Cslib.SKI.List.succHead_correct` idx 2: necessary (ns = [] and [1], same cns)
theorem w2c1_sh2 : ¬ drop0% Cslib.SKI.List.succHead_correct 2 := fun h => by
  have := lHd (h [] SKI.S) (h [1] SKI.S)
  simp at this

-- `Cslib.SKI.church_red` idx 5: necessary (n = 1, f = S, f' = K, x = x' = S)
theorem w2c1_chr5 : ¬ drop0% Cslib.SKI.church_red 5 := fun h =>
  nSSKS (h 1 SKI.S SKI.K SKI.S SKI.S .refl)

-- `Cslib.SKI.church_red` idx 6: necessary (n = 0, x = S, x' = K)
theorem w2c1_chr6 : ¬ drop0% Cslib.SKI.church_red 6 := fun h => by
  have := stuck (by simp [RedexFree]) (h 0 SKI.S SKI.S SKI.S SKI.K .refl); simp at this

-- `Cslib.SKI.isChurch_trans` idx 3: necessary (a' = Zero, a = One)
theorem w2c1_ict3 : ¬ drop0% Cslib.SKI.isChurch_trans 3 := fun h =>
  absurd (chInj (h 0 (a := SKI.One) zero_correct) one_correct) (by decide)

-- `Cslib.SKI.isChurch_trans` idx 4: necessary (a = a' = S, n = 0 and 1)
theorem w2c1_ict4 : ¬ drop0% Cslib.SKI.isChurch_trans 4 := fun h =>
  absurd (chInj (h 0 (a := SKI.S) (a' := SKI.S) .refl) (h 1 (a := SKI.S) (a' := SKI.S) .refl)) (by decide)

-- `Cslib.SKI.succ_correct` idx 2: necessary (n = 0 and 1, same a)
theorem w2c1_succ2 : ¬ drop0% Cslib.SKI.succ_correct 2 := fun h =>
  absurd (chInj (h 0 SKI.S) (h 1 SKI.S)) (by decide)

-- `Cslib.SKI.isChurchPair_trans` idx 3: necessary (a' = MkPair Zero Zero, a = MkPair One Zero)
theorem w2c1_icp3 : ¬ drop0% Cslib.SKI.isChurchPair_trans 3 := fun h => by
  have h1 := h (0, 0) (MkPair ⬝ SKI.One ⬝ SKI.Zero) (MkPair ⬝ SKI.Zero ⬝ SKI.Zero)
    ⟨isChurch_trans _ (fst_correct _ _) zero_correct, isChurch_trans _ (snd_correct _ _) zero_correct⟩
  exact absurd (chInj h1.1 (isChurch_trans _ (fst_correct _ _) one_correct)) (by decide)

-- `Cslib.SKI.isChurchPair_trans` idx 4: necessary (a = a' = S, ns = (0, 0) and (1, 0))
theorem w2c1_icp4 : ¬ drop0% Cslib.SKI.isChurchPair_trans 4 := fun h =>
  absurd (chInj (h (0, 0) SKI.S SKI.S .refl).1 (h (1, 0) SKI.S SKI.S .refl).1) (by decide)

-- `Cslib.SKI.predAux_correct` idx 2: necessary (ns = (0, 0) and (0, 1), same p)
theorem w2c1_pa2 : ¬ drop0% Cslib.SKI.predAux_correct 2 := fun h =>
  absurd (chInj (h SKI.S (0, 0)).1 (h SKI.S (0, 1)).1) (by decide)

-- `Cslib.SKI.pred_correct` idx 2: necessary (n = 1 and 2, same a)
theorem w2c1_pred2 : ¬ drop0% Cslib.SKI.pred_correct 2 := fun h =>
  absurd (chInj (h 1 SKI.S) (h 2 SKI.S)) (by decide)

-- `Cslib.SKI.isZero_correct` idx 2: necessary (n = 0 and 1, same a)
theorem w2c1_iz2 : ¬ drop0% Cslib.SKI.isZero_correct 2 := fun h =>
  absurd (blInj (h 0 SKI.S) (h 1 SKI.S)) (by decide)

-- `Cslib.SKI.rec_zero` idx 3: necessary (a = One, x = Zero, g = K ⬝ (K ⬝ One))
theorem w2c1_rz3 : ¬ drop0% Cslib.SKI.rec_zero 3 := fun h => by
  have h0 := isChurch_trans 0 (h SKI.Zero (SKI.K ⬝ (SKI.K ⬝ SKI.One)) SKI.One) zero_correct
  have h1 := isChurch_trans 1 ((rec_succ 0 SKI.Zero (SKI.K ⬝ (SKI.K ⬝ SKI.One)) SKI.One one_correct).trans
    ((MRed.head _ (MRed.K _ _)).trans (MRed.K _ _))) one_correct
  exact absurd (chInj h0 h1) (by decide)

-- `Cslib.SKI.rec_succ` idx 4: necessary (a = Zero, x = Zero, g = K ⬝ (K ⬝ One))
theorem w2c1_rs4 : ¬ drop0% Cslib.SKI.rec_succ 4 := fun h => by
  have h0 := isChurch_trans 0 (rec_zero SKI.Zero (SKI.K ⬝ (SKI.K ⬝ SKI.One)) SKI.Zero zero_correct) zero_correct
  have h1 := isChurch_trans 1 ((h 0 SKI.Zero (SKI.K ⬝ (SKI.K ⬝ SKI.One)) SKI.Zero).trans
    ((MRed.head _ (MRed.K _ _)).trans (MRed.K _ _))) one_correct
  exact absurd (chInj h0 h1) (by decide)

-- `Cslib.SKI.rec_correct'` idx 3: necessary (base = Zero, r = const 1, step = K ⬝ (K ⬝ One))
theorem w2c1_rc3 : ¬ drop0% Cslib.SKI.rec_correct' 3 := fun h => by
  have h1 := h SKI.Zero (SKI.K ⬝ (SKI.K ⬝ SKI.One)) (fun _ => 1)
    (fun _ _ _ _ _ => isChurch_trans 1 ((MRed.head _ (MRed.K _ _)).trans (MRed.K _ _)) one_correct)
    0 SKI.Zero zero_correct
  have h0 := isChurch_trans 0 (rec_zero SKI.Zero (SKI.K ⬝ (SKI.K ⬝ SKI.One)) SKI.Zero zero_correct) zero_correct
  exact absurd (chInj h1 h0) (by decide)

-- `Cslib.SKI.rec_correct'` idx 4: necessary (base = Zero, r = id, step = K ⬝ (K ⬝ Zero), n = 1)
theorem w2c1_rc4 : ¬ drop0% Cslib.SKI.rec_correct' 4 := fun h => by
  have h1 := h SKI.Zero (SKI.K ⬝ (SKI.K ⬝ SKI.Zero)) id zero_correct 1 SKI.One one_correct
  have h0 := isChurch_trans 0 ((rec_succ 0 SKI.Zero (SKI.K ⬝ (SKI.K ⬝ SKI.Zero)) SKI.One one_correct).trans
    ((MRed.head _ (MRed.K _ _)).trans (MRed.K _ _))) zero_correct
  exact absurd (chInj h1 h0) (by decide)

-- `Cslib.SKI.rec_correct'` idx 7: necessary (r = id, step = K ⬝ Succ; n = 0 and 1 with the same cn)
theorem w2c1_rc7 : ¬ drop0% Cslib.SKI.rec_correct' 7 := fun h => by
  have hs : ∀ (k : ℕ) (cb cp : SKI), IsChurch (k + 1) cb → IsChurch (id k) cp →
      IsChurch (id (k + 1)) (SKI.K ⬝ SKI.Succ ⬝ cb ⬝ cp) :=
    fun k cb cp _ hp => isChurch_trans _ (MRed.head _ (MRed.K _ _)) (succ_correct k cp hp)
  exact absurd (chInj (h SKI.Zero _ id zero_correct hs 0 SKI.S) (h SKI.Zero _ id zero_correct hs 1 SKI.S))
    (by decide)

-- `Cslib.SKI.rfindAboveAux_base` idx 3: necessary (f = K ⬝ One, a = Zero, R₀ = K ⬝ (K ⬝ One))
theorem w2c1_rab3 : ¬ drop0% Cslib.SKI.rfindAboveAux_base 3 := fun h => by
  have h0 := isChurch_trans 0 (h (SKI.K ⬝ (SKI.K ⬝ SKI.One)) (SKI.K ⬝ SKI.One) SKI.Zero) zero_correct
  have h1 := isChurch_trans 1 ((rfindAboveAux_step (SKI.K ⬝ (SKI.K ⬝ SKI.One)) (SKI.K ⬝ SKI.One) SKI.Zero
    (m := 0) (isChurch_trans _ (MRed.K _ _) one_correct)).trans
    ((MRed.head _ (MRed.K _ _)).trans (MRed.K _ _))) one_correct
  exact absurd (chInj h0 h1) (by decide)

-- `Cslib.SKI.rfindAboveAux_step` idx 4: necessary (f = K ⬝ Zero, a = Zero, R₀ = K ⬝ (K ⬝ One))
theorem w2c1_ras4 : ¬ drop0% Cslib.SKI.rfindAboveAux_step 4 := fun h => by
  have h0 := isChurch_trans 0 (rfindAboveAux_base (SKI.K ⬝ (SKI.K ⬝ SKI.One)) (SKI.K ⬝ SKI.Zero) SKI.Zero
    (isChurch_trans _ (MRed.K _ _) zero_correct)) zero_correct
  have h1 := isChurch_trans 1 ((h (SKI.K ⬝ (SKI.K ⬝ SKI.One)) (SKI.K ⬝ SKI.Zero) SKI.Zero (m := 0)).trans
    ((MRed.head _ (MRed.K _ _)).trans (MRed.K _ _))) one_correct
  exact absurd (chInj h0 h1) (by decide)

end

section

namespace W2c1
open Cslib Cslib.SKI Relation
theorem kz (y : SKI) : IsChurch 0 (SKI.K ⬝ SKI.Zero ⬝ y) := isChurch_trans _ (MRed.K _ _) zero_correct
theorem ko (y : SKI) : IsChurch 1 (SKI.K ⬝ SKI.One ⬝ y) := isChurch_trans _ (MRed.K _ _) one_correct
theorem vac {P : ℕ → Prop} : ∀ i < 0, P i := fun i hi => absurd hi (Nat.not_lt_zero _)
end W2c1

open Cslib Cslib.SKI Relation W2c1

-- `Cslib.SKI.RFindAbove_correct'` idx 4: necessary (x = Zero claimed to be m = 1; f = K ⬝ Zero, n = 0)
theorem w2c1_rfa'4 : ¬ drop0% Cslib.SKI.RFindAbove_correct' 4 := fun h =>
  absurd (chInj (h (SKI.K ⬝ SKI.Zero) SKI.Zero 0 1 (fun y _ => kz y) vac)
    (RFindAbove_correct' (SKI.K ⬝ SKI.Zero) SKI.Zero 0 0 zero_correct (fun y _ => kz y) vac)) (by decide)

-- `Cslib.SKI.RFindAbove_correct'` idx 5: necessary (f = K ⬝ One, n = 0 and 1)
theorem w2c1_rfa'5 : ¬ drop0% Cslib.SKI.RFindAbove_correct' 5 := fun h =>
  absurd (chInj (h (SKI.K ⬝ SKI.One) SKI.Zero 0 0 zero_correct vac)
    (h (SKI.K ⬝ SKI.One) SKI.Zero 1 0 zero_correct (fun _ _ y _ => ⟨0, ko y⟩))) (by decide)

-- `Cslib.SKI.RFindAbove_correct'` idx 6: necessary (f = K ⬝ Zero, n = 0 and 1)
theorem w2c1_rfa'6 : ¬ drop0% Cslib.SKI.RFindAbove_correct' 6 := fun h =>
  absurd (chInj (h (SKI.K ⬝ SKI.Zero) SKI.Zero 0 0 zero_correct (fun y _ => kz y))
    (h (SKI.K ⬝ SKI.Zero) SKI.Zero 1 0 zero_correct (fun y _ => kz y))) (by decide)

-- `Cslib.SKI.RFindAbove_correct` idx 3: necessary (fNat i = 1 - i but f = K ⬝ Zero)
theorem w2c1_rfa3 : ¬ drop0% Cslib.SKI.RFindAbove_correct 3 := fun h =>
  absurd (chInj (h (fun i => 1 - i) (SKI.K ⬝ SKI.Zero) SKI.Zero 1 0 zero_correct rfl
      (fun i hi => by simp; omega))
    (RFindAbove_correct (fun _ => 0) (SKI.K ⬝ SKI.Zero) SKI.Zero (fun _ y _ => kz y) 0 0 zero_correct rfl vac))
    (by decide)

-- `Cslib.SKI.RFindAbove_correct` idx 6: necessary (x = Zero claimed to be m = 1)
theorem w2c1_rfa6 : ¬ drop0% Cslib.SKI.RFindAbove_correct 6 := fun h =>
  absurd (chInj (h (fun _ => 0) (SKI.K ⬝ SKI.Zero) SKI.Zero (fun _ y _ => kz y) 0 1 rfl vac)
    (RFindAbove_correct (fun _ => 0) (SKI.K ⬝ SKI.Zero) SKI.Zero (fun _ y _ => kz y) 0 0 zero_correct rfl vac))
    (by decide)

-- `Cslib.SKI.RFindAbove_correct` idx 7: necessary (fNat = 1, f = K ⬝ One, n = 0 and 1)
theorem w2c1_rfa7 : ¬ drop0% Cslib.SKI.RFindAbove_correct 7 := fun h =>
  absurd (chInj (h (fun _ => 1) (SKI.K ⬝ SKI.One) SKI.Zero (fun _ y _ => ko y) 0 0 zero_correct vac)
    (h (fun _ => 1) (SKI.K ⬝ SKI.One) SKI.Zero (fun _ y _ => ko y) 1 0 zero_correct (fun _ _ => one_ne_zero)))
    (by decide)

-- `Cslib.SKI.RFindAbove_correct` idx 8: necessary (fNat = 0, f = K ⬝ Zero, n = 0 and 1)
theorem w2c1_rfa8 : ¬ drop0% Cslib.SKI.RFindAbove_correct 8 := fun h =>
  absurd (chInj (h (fun _ => 0) (SKI.K ⬝ SKI.Zero) SKI.Zero (fun _ y _ => kz y) 0 0 zero_correct rfl)
    (h (fun _ => 0) (SKI.K ⬝ SKI.Zero) SKI.Zero (fun _ y _ => kz y) 1 0 zero_correct rfl)) (by decide)

-- `Cslib.SKI.RFind_correct` idx 2: necessary (fNat i = 1 - i but f = K ⬝ Zero)
theorem w2c1_rf2 : ¬ drop0% Cslib.SKI.RFind_correct 2 := fun h =>
  absurd (chInj (h (fun i => 1 - i) (SKI.K ⬝ SKI.Zero) 1 rfl (fun i hi => by simp; omega))
    (RFind_correct (fun _ => 0) (SKI.K ⬝ SKI.Zero) (fun _ y _ => kz y) 0 rfl vac)) (by decide)

-- `Cslib.SKI.RFind_correct` idx 4: necessary (fNat = 1, f = K ⬝ One, n = 0 and 1)
theorem w2c1_rf4 : ¬ drop0% Cslib.SKI.RFind_correct 4 := fun h =>
  absurd (chInj (h (fun _ => 1) (SKI.K ⬝ SKI.One) (fun _ y _ => ko y) 0 vac)
    (h (fun _ => 1) (SKI.K ⬝ SKI.One) (fun _ y _ => ko y) 1 (fun _ _ => one_ne_zero))) (by decide)

-- `Cslib.SKI.add_correct` idx 5: necessary (m = 0 and 1, same b)
theorem w2c1_add5 : ¬ drop0% Cslib.SKI.add_correct 5 := fun h =>
  absurd (chInj (h 0 0 SKI.Zero SKI.S zero_correct) (h 0 1 SKI.Zero SKI.S zero_correct)) (by decide)

-- `Cslib.SKI.mul_correct` idx 4: necessary (n = 0 and 1, same a; m = 1)
theorem w2c1_mul4 : ¬ drop0% Cslib.SKI.mul_correct 4 := fun h =>
  absurd (chInj (h (n := 0) (a := SKI.S) one_correct) (h (n := 1) (a := SKI.S) one_correct)) (by decide)

-- `Cslib.SKI.mul_correct` idx 5: necessary (m = 0 and 1, same b; n = 1)
theorem w2c1_mul5 : ¬ drop0% Cslib.SKI.mul_correct 5 := fun h =>
  absurd (chInj (h (m := 0) (b := SKI.S) one_correct) (h (m := 1) (b := SKI.S) one_correct)) (by decide)

-- `Cslib.SKI.sub_correct` idx 4: necessary (n = 0 and 1, same a; m = 0)
theorem w2c1_sub4 : ¬ drop0% Cslib.SKI.sub_correct 4 := fun h =>
  absurd (chInj (h 0 0 SKI.S SKI.Zero zero_correct) (h 1 0 SKI.S SKI.Zero zero_correct)) (by decide)

-- `Cslib.SKI.sub_correct` idx 5: necessary (m = 0 and 1, same b; n = 1)
theorem w2c1_sub5 : ¬ drop0% Cslib.SKI.sub_correct 5 := fun h =>
  absurd (chInj (h 1 0 SKI.One SKI.S one_correct) (h 1 1 SKI.One SKI.S one_correct)) (by decide)

-- `Cslib.SKI.le_correct` idx 4: necessary (n = 0 and 1, same a; m = 0)
theorem w2c1_le4 : ¬ drop0% Cslib.SKI.le_correct 4 := fun h =>
  absurd (blInj (h 0 0 SKI.S SKI.Zero zero_correct) (h 1 0 SKI.S SKI.Zero zero_correct)) (by decide)

-- `Cslib.SKI.le_correct` idx 5: necessary (m = 0 and 1, same b; n = 1)
theorem w2c1_le5 : ¬ drop0% Cslib.SKI.le_correct 5 := fun h =>
  absurd (blInj (h 1 0 SKI.One SKI.S one_correct) (h 1 1 SKI.One SKI.S one_correct)) (by decide)

-- `Cslib.SKI.sqrt_correct` idx 2: necessary (n = 0 and 1, same cn)
theorem w2c1_sqrt2 : ¬ drop0% Cslib.SKI.sqrt_correct 2 := fun h =>
  absurd (chInj (h 0 SKI.S) (h 1 SKI.S)) (by simp)

-- `Cslib.SKI.natPair_correct` idx 4: necessary (a = 0 and 1, same ca)
theorem w2c1_np4 : ¬ drop0% Cslib.SKI.natPair_correct 4 := fun h =>
  absurd (chInj (h 0 0 SKI.S SKI.Zero zero_correct) (h 1 0 SKI.S SKI.Zero zero_correct)) (by simp [Nat.pair])

-- `Cslib.SKI.natPair_correct` idx 5: necessary (b = 0 and 1, same cb)
theorem w2c1_np5 : ¬ drop0% Cslib.SKI.natPair_correct 5 := fun h =>
  absurd (chInj (h 0 0 SKI.Zero SKI.S zero_correct) (h 0 1 SKI.Zero SKI.S zero_correct)) (by simp [Nat.pair])

-- `_private.Cslib.Languages.CombinatoryLogic.Recursion.0.Cslib.SKI.natUnpair_church` idx 2: necessary (n = 0 and 1)
theorem w2c1_nuc2 : ¬ drop0% _private.Cslib.Languages.CombinatoryLogic.Recursion.«0».Cslib.SKI.natUnpair_church 2 :=
  fun h => absurd (chInj (h 0 SKI.S).1 (h 1 SKI.S).1) (by simp)

-- `Cslib.SKI.natUnpairLeft_correct` idx 2: necessary (n = pair 0 0 and pair 1 0)
theorem w2c1_nul2 : ¬ drop0% Cslib.SKI.natUnpairLeft_correct 2 := fun h =>
  absurd (chInj (h (Nat.pair 0 0) SKI.S) (h (Nat.pair 1 0) SKI.S)) (by simp [Nat.unpair_pair])

-- `Cslib.SKI.natUnpairRight_correct` idx 2: necessary (n = pair 0 0 and pair 0 1)
theorem w2c1_nur2 : ¬ drop0% Cslib.SKI.natUnpairRight_correct 2 := fun h =>
  absurd (chInj (h (Nat.pair 0 0) SKI.S) (h (Nat.pair 0 1) SKI.S)) (by simp [Nat.unpair_pair])

end

section

open Cslib Cslib.SKI Relation W2c1 Nat.Partrec

namespace W2c1
theorem t00 : IsChurch (Nat.pair 0 0) SKI.Zero := by
  have : Nat.pair 0 0 = 0 := rfl
  rw [this]; exact zero_correct
theorem t01 : IsChurch (Nat.pair 0 1) SKI.One := by
  have : Nat.pair 0 1 = 1 := rfl
  rw [this]; exact one_correct

theorem ez (n : ℕ) : Code.eval .zero n = Part.some 0 := rfl
theorem es (n : ℕ) : Code.eval .succ n = Part.some (n + 1) := rfl
theorem pz (n : ℕ) : (pure 0 : ℕ →. ℕ) n = Part.some 0 := rfl
theorem ecz (n : ℕ) : Code.eval (Code.comp .succ .zero) n = Part.some 1 := by
  exact Part.eq_some_iff.mpr (Part.mem_bind (f := Code.eval .zero n) (g := Code.eval .succ)
    (by rw [ez]; exact Part.mem_some 0) (by rw [es]; exact Part.mem_some 1))

theorem m00 : (0 : ℕ) ∈ Code.eval (Code.prec .zero .zero) (Nat.pair 0 (Nat.succ 0)) := by
  rw [Code.eval_prec_succ]; simp [ez]
theorem m11 : (1 : ℕ) ∈ Code.eval (Code.prec .zero .succ) (Nat.pair 0 (Nat.succ 0)) := by
  rw [Code.eval_prec_succ, Code.eval_prec_zero]; simp [ez, es, show Nat.pair 0 (Nat.pair 0 0) = 0 from rfl]
theorem mS (a : ℕ) : (a + 1 : ℕ) ∈ Code.eval (Code.prec .succ .zero) (Nat.pair a 0) := by
  rw [Code.eval_prec_zero]; simp [es]
theorem mC : (1 : ℕ) ∈ Code.eval (Code.prec (Code.comp .succ .zero) .zero) (Nat.pair 0 0) := by
  rw [Code.eval_prec_zero]; simp [ecz]
theorem mR0 : (0 : ℕ) ∈ Code.eval (Code.rfind' .zero) (Nat.pair 0 0) := by
  simp only [Code.eval, Nat.unpaired, Nat.unpair_pair, Part.mem_map_iff]
  refine ⟨0, Nat.mem_rfind.mpr ⟨?_, fun hm => absurd hm (Nat.not_lt_zero _)⟩, rfl⟩
  simp [pz]
theorem mR1 : (1 : ℕ) ∈ Code.eval (Code.rfind' (Code.prec (Code.comp .succ .zero) .zero)) (Nat.pair 0 0) := by
  simp only [Code.eval.eq_8, Nat.unpaired, Nat.unpair_pair, Part.mem_map_iff]
  refine ⟨1, Nat.mem_rfind.mpr ⟨?_, ?_⟩, rfl⟩
  · simp only [Nat.add_zero]
    rw [show (1 : ℕ) = Nat.succ 0 from rfl, Code.eval_prec_succ]; simp [ecz, ez]
  · intro m hm
    obtain rfl : m = 0 := by omega
    rw [Nat.add_zero, Code.eval_prec_zero]; simp [ecz]

def enc : SKI → ℕ
  | .S => 0
  | .K => 1
  | .I => 2
  | .app a b => Nat.pair (enc a) (enc b) + 3
theorem encInj (a : SKI) : ∀ b, enc a = enc b → a = b := by
  induction a with
  | app a1 a2 ih1 ih2 =>
    intro b h
    cases b with
    | app b1 b2 =>
      have h' := Nat.add_right_cancel (show Nat.pair (enc a1) (enc a2) + 3 = Nat.pair (enc b1) (enc b2) + 3 from h)
      obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp h'
      rw [ih1 _ h1, ih2 _ h2]
    | _ => simp [enc] at h
  | _ => intro b h; cases b <;> simp [enc] at h ⊢

end W2c1

-- `Cslib.SKI.natPartrec_skiComputable` idx 1: necessary (Cantor: the indicator functions of all sets of ℕ would be computed by distinct SKI terms)
theorem w2c1_npsc1 : ¬ drop0% Cslib.SKI.natPartrec_skiComputable 1 := fun h => by
  classical
  let F : Set ℕ → (ℕ →. ℕ) := fun s n => Part.some (if n ∈ s then 1 else 0)
  choose t ht using fun s => (h (F s) : ∃ t, Computes t (F s))
  apply Function.cantor_injective (fun s => enc (t s))
  intro s s' hss
  have he : t s = t s' := encInj _ _ hss
  ext n
  have h1 := ht s n (toChurch n) (toChurch_correct n) _ (Part.mem_some _)
  have h2 := ht s' n (toChurch n) (toChurch_correct n) _ (Part.mem_some _)
  rw [he] at h1
  have := chInj h1 h2
  by_cases a : n ∈ s <;> by_cases b : n ∈ s' <;> simp_all

-- `_private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.0.Cslib.SKI.prec_rec_correct` idx 11: necessary (m = 0 and 1)
theorem w2c1_prc11 : ¬ drop0% _private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.«0».Cslib.SKI.prec_rec_correct 11 :=
  fun h => absurd (chInj
    (h .zero .zero _ _ (Code.toSKI_correct _) (Code.toSKI_correct _) 0 SKI.Zero zero_correct 0 0 SKI.Zero zero_correct)
    (h .zero .zero _ _ (Code.toSKI_correct _) (Code.toSKI_correct _) 0 SKI.Zero zero_correct 0 1 SKI.Zero zero_correct))
    (by decide)

-- `_private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.0.Cslib.SKI.prec_rec_correct` idx 13: necessary (f = zero, g = succ; b₀ = 0 and 1 with cb = Zero)
theorem w2c1_prc13 : ¬ drop0% _private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.«0».Cslib.SKI.prec_rec_correct 13 :=
  fun h => absurd (chInj
    (h .zero .succ _ _ (Code.toSKI_correct _) (Code.toSKI_correct _) 0 SKI.Zero zero_correct 0 0
      (by rw [Code.eval_prec_zero, ez]; exact Part.mem_some _) SKI.Zero)
    (h .zero .succ _ _ (Code.toSKI_correct _) (Code.toSKI_correct _) 0 SKI.Zero zero_correct (Nat.succ 0) 1 m11 SKI.Zero))
    (by decide)

-- `_private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.0.Cslib.SKI.prec_rec_correct` idx 8: necessary (f = succ, g = zero; a₀ = 0 and 1 with ca = Zero)
theorem w2c1_prc8 : ¬ drop0% _private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.«0».Cslib.SKI.prec_rec_correct 8 :=
  fun h => absurd (chInj
    (h .succ .zero _ _ (Code.toSKI_correct _) (Code.toSKI_correct _) 0 SKI.Zero 0 1 (mS 0) SKI.Zero zero_correct)
    (h .succ .zero _ _ (Code.toSKI_correct _) (Code.toSKI_correct _) 1 SKI.Zero 0 2 (mS 1) SKI.Zero zero_correct))
    (by decide)

-- `_private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.0.Cslib.SKI.prec_rec_correct` idx 5: necessary (tg = toSKI succ claimed to compute zero; b₀ = 1)
theorem w2c1_prc5 : ¬ drop0% _private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.«0».Cslib.SKI.prec_rec_correct 5 :=
  fun h => absurd (chInj
    (h .zero .zero Code.zero.toSKI Code.succ.toSKI (Code.toSKI_correct _) 0 SKI.Zero zero_correct (Nat.succ 0) 0 m00
      SKI.One one_correct)
    ((priv% _private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.«0».Cslib.SKI.prec_rec_correct) .zero .succ
      Code.zero.toSKI Code.succ.toSKI (Code.toSKI_correct _) (Code.toSKI_correct _) 0 SKI.Zero zero_correct
      (Nat.succ 0) 1 m11 SKI.One one_correct))
    (by decide)

-- `_private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.0.Cslib.SKI.rfind_eval_aux` idx 5: necessary (f = zero, b = false)
theorem w2c1_rea5 : ¬ drop0% _private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.«0».Cslib.SKI.rfind_eval_aux 5 :=
  fun h => by
  obtain ⟨v, hv, hm⟩ := h (f := .zero) (a₀ := 0) (m₀ := 0) (j := 0) (b := false)
  rw [ez] at hm; rw [Part.mem_some_iff.mp hm] at hv; simp at hv

-- `_private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.0.Cslib.SKI.rfind_eval_root` idx 4: necessary (f = succ)
theorem w2c1_rer4 : ¬ drop0% _private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.«0».Cslib.SKI.rfind_eval_root 4 :=
  fun h => by
  have := h (f := .succ) (a₀ := 0) (m₀ := 0) (k := 0)
  rw [es] at this; simp at this

-- `_private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.0.Cslib.SKI.rfind_eval_pos_below` idx 4: necessary (f = zero, k = 1, i = 0)
theorem w2c1_repb4 : ¬ drop0% _private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.«0».Cslib.SKI.rfind_eval_pos_below 4 :=
  fun h => by
  obtain ⟨vi, hne, hm⟩ := h (f := .zero) (a₀ := 0) (m₀ := 0) (k := 1) 0 (by decide)
  rw [ez] at hm; exact hne (Part.mem_some_iff.mp hm)

-- `_private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.0.Cslib.SKI.rfind_eval_pos_below` idx 6: necessary (f = zero, k = 0, i = 0)
theorem w2c1_repb6 : ¬ drop0% _private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.«0».Cslib.SKI.rfind_eval_pos_below 6 :=
  fun h => by
  obtain ⟨vi, hne, hm⟩ := h (f := .zero) (a₀ := 0) (m₀ := 0) (k := 0)
    (Nat.mem_rfind.mpr ⟨by rw [ez]; simp, fun hm => absurd hm (Nat.not_lt_zero _)⟩) 0
  rw [ez] at hm; exact hne (Part.mem_some_iff.mp hm)

-- `_private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.0.Cslib.SKI.prec_computes` idx 4: necessary (tf = toSKI (comp succ zero) claimed to compute zero)
theorem w2c1_pcs4 : ¬ drop0% _private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.«0».Cslib.SKI.prec_computes 4 :=
  fun h => absurd (chInj
    (h (f := .zero) (g := .zero) (tf := (Code.comp .succ .zero).toSKI) (Code.toSKI_correct .zero)
      (Nat.pair 0 0) SKI.Zero t00 0 (by rw [Code.eval_prec_zero, ez]; exact Part.mem_some _))
    (Code.toSKI_correct (Code.prec (Code.comp .succ .zero) .zero) (Nat.pair 0 0) SKI.Zero t00 1 mC))
    (by decide)

-- `_private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.0.Cslib.SKI.prec_computes` idx 5: necessary (tg = toSKI succ claimed to compute zero)
theorem w2c1_pcs5 : ¬ drop0% _private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.«0».Cslib.SKI.prec_computes 5 :=
  fun h => absurd (chInj
    (h (f := .zero) (g := .zero) (tg := Code.succ.toSKI) (Code.toSKI_correct .zero)
      (Nat.pair 0 (Nat.succ 0)) SKI.One t01 0 m00)
    (Code.toSKI_correct (Code.prec .zero .succ) (Nat.pair 0 (Nat.succ 0)) SKI.One t01 1 m11))
    (by decide)

-- `_private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.0.Cslib.SKI.rfind_computes` idx 2: necessary (tf = toSKI (prec (comp succ zero) zero) claimed to compute zero)
theorem w2c1_rfc2 : ¬ drop0% _private.Cslib.Languages.CombinatoryLogic.PartrecToSKI.«0».Cslib.SKI.rfind_computes 2 :=
  fun h => absurd (chInj
    (h (f := .zero) (tf := (Code.prec (Code.comp .succ .zero) .zero).toSKI) (Nat.pair 0 0) SKI.Zero t00 0 mR0)
    (Code.toSKI_correct (Code.rfind' (Code.prec (Code.comp .succ .zero) .zero)) (Nat.pair 0 0) SKI.Zero t00 1 mR1))
    (by decide)

end

section

namespace W2c1
open Cslib LambdaCalculus.LocallyNameless.Fsub

theorem fNoLook {Γ : Env ℕ} {X : ℕ} (h : ∀ σ, Binding.sub σ ∉ Γ.dlookup X) : ¬ Ty.Wf Γ (.fvar X) := by
  intro w; cases w with | var hm => exact h _ hm
theorem fNotWf0 {X : ℕ} : ¬ Ty.Wf ([] : Env ℕ) (.fvar X) := fNoLook (by simp)
theorem fwSub (a : ℕ) : Env.Wf ([⟨a, .sub .top⟩] : Env ℕ) := .sub .empty .top (by simp)
theorem fwVar (a : ℕ) : Ty.Wf ([⟨a, .sub .top⟩] : Env ℕ) (.fvar a) :=
  .var (show Binding.sub .top ∈ _ from by simp)
theorem fSubTop : Sub ([] : Env ℕ) .top .top := .top .empty .top
theorem fId (σ : Ty ℕ) (h : Ty.Wf [] σ) : Typing ([] : Env ℕ) (.abs σ (.bvar 0)) (.arrow σ σ) :=
  .abs ∅ (fun x _ => .var (.ty .empty h (by simp)) (by simp))
theorem fLcId : Term.LC (.abs .top (.bvar 0) : Term ℕ) := .abs ∅ .top (fun x _ => .var)
-- ill-formed contexts: a binding to an unbound type variable
theorem badTy : ¬ Env.Wf ([⟨0, .ty (.fvar 7)⟩] : Env ℕ) := fun h => by
  cases h with | ty _ hw _ => exact fNotWf0 hw
theorem badSub : ¬ Env.Wf ([⟨0, .sub (.fvar 7)⟩] : Env ℕ) := fun h => by
  cases h with | sub _ hw _ => exact fNotWf0 hw
end W2c1

open Cslib LambdaCalculus.LocallyNameless.Fsub W2c1

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.open_subst_var` idx 8: necessary (δ = bvar 0, σ = fvar 0, X = 0, Y = 1)
theorem w2c1_osv8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Ty.open_subst_var 8 := fun h => by
  have e := h (Var := ℕ) (δ := .bvar 0) (Y := 1) (X := 0) (σ := .fvar 0) (by decide)
  change Ty.bvar 0 = Ty.fvar 1 at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTy_neq_eq` idx 6: necessary (X = Y = 0, t = tapp (fvar 0) (bvar 0))
theorem w2c1_orne6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTy_neq_eq 6 := fun h => by
  have e := h (Var := ℕ) (t := .tapp (.fvar 0) (.bvar 0)) (X := 0) (Y := 0) (σ := .top) (τ := .top) rfl
  change Term.tapp (.fvar 0) (.bvar 0) = Term.tapp (.fvar 0) .top at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTy_neq_eq` idx 7: necessary (X = 0, Y = 1, t = tapp (fvar 0) (bvar 0))
theorem w2c1_orne7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTy_neq_eq 7 := fun h => by
  have e := h (Var := ℕ) (t := .tapp (.fvar 0) (.bvar 0)) (X := 0) (Y := 1) (σ := .top) (τ := .top) (by decide)
  change Term.tapp (.fvar 0) (.bvar 0) = Term.tapp (.fvar 0) .top at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm_ty_eq` idx 6: necessary (t = tapp (fvar 0) (bvar 0))
theorem w2c1_ortye6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTm_ty_eq 6 := fun h => by
  have e := h (Var := ℕ) (t := .tapp (.fvar 0) (.bvar 0)) (δ := .top) (x := 0) (s := .fvar 0) (y := 0)
  change Term.tapp (.fvar 0) (.bvar 0) = Term.tapp (.fvar 0) .top at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTy_lc` idx 6: necessary (t = tapp (fvar 0) (bvar 0))
theorem w2c1_orlc6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTy_lc 6 := fun h => by
  have e := h (Var := ℕ) (X := 0) (σ := .top) (t := .tapp (.fvar 0) (.bvar 0))
  change Term.tapp (.fvar 0) (.bvar 0) = Term.tapp (.fvar 0) .top at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.substTy_fresh` idx 4: necessary (t = tapp (fvar 0) (fvar 0), X = 0)
theorem w2c1_stf4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.substTy_fresh 4 := fun h => by
  have e := h (Var := ℕ) (t := .tapp (.fvar 0) (.fvar 0)) (X := 0) (δ := .top)
  change Term.tapp (.fvar 0) (.fvar 0) = Term.tapp (.fvar 0) .top at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTy_substTy` idx 7: necessary (δ = bvar 0)
theorem w2c1_orst7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTy_substTy 7 := fun h => by
  have e := h (Var := ℕ) (δ := .bvar 0) (Y := 0) (t := .tapp (.fvar 0) (.fvar 0)) (σ := .top) (X := 0)
  change Term.tapp (.fvar 0) (.bvar 0) = Term.tapp (.fvar 0) .top at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTy_substTy` idx 6: necessary (δ = bvar 0)
theorem w2c1_otst6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTy_substTy 6 := fun h => by
  have e := h (Var := ℕ) (δ := .bvar 0) (t := .tapp (.fvar 0) (.fvar 0)) (σ := .top) (X := 0)
  change Term.tapp (.fvar 0) (.bvar 0) = Term.tapp (.fvar 0) .top at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTy_substTy_var` idx 7: necessary (Y = X = 0)
theorem w2c1_otstv7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTy_substTy_var 7 := fun h => by
  have e := h (Var := ℕ) (δ := .top) (Y := 0) (X := 0) (t := .tapp (.fvar 0) (.bvar 0)) .top
  change Term.tapp (.fvar 0) .top = Term.tapp (.fvar 0) (.fvar 0) at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTy_substTy_var` idx 8: necessary (δ = bvar 0)
theorem w2c1_otstv8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTy_substTy_var 8 := fun h => by
  have e := h (Var := ℕ) (δ := .bvar 0) (Y := 1) (X := 0) (t := .tapp (.fvar 0) (.fvar 0)) (by decide)
  change Term.tapp (.fvar 0) (.bvar 0) = Term.tapp (.fvar 0) (.fvar 1) at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTy_substTy_intro` idx 6: necessary (X = 0 free in t)
theorem w2c1_orsti6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTy_substTy_intro 6 := fun h => by
  have e := h (Var := ℕ) (δ := .top) (X := 0) (Y := 0) (t := .tapp (.fvar 0) (.fvar 0))
  change Term.tapp (.fvar 0) (.fvar 0) = Term.tapp (.fvar 0) .top at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTy_substTy_intro` idx 5: necessary (X = 0 free in t)
theorem w2c1_otsti5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTy_substTy_intro 5 := fun h => by
  have e := h (Var := ℕ) (X := 0) (t := .tapp (.fvar 0) (.fvar 0)) (δ := .top)
  change Term.tapp (.fvar 0) (.fvar 0) = Term.tapp (.fvar 0) .top at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTy_substTm` idx 7: necessary (s = tapp (fvar 5) (bvar 0), t = fvar 0)
theorem w2c1_orstm7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openRecTy_substTm 7 := fun h => by
  have e := h (Var := ℕ) (s := .tapp (.fvar 5) (.bvar 0)) (Y := 0) (t := .fvar 0) (δ := .top) (x := 0)
  change Term.tapp (.fvar 5) (.bvar 0) = Term.tapp (.fvar 5) .top at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTy_substTm` idx 6: necessary (s = tapp (fvar 5) (bvar 0), t = fvar 0)
theorem w2c1_otstm6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTy_substTm 6 := fun h => by
  have e := h (Var := ℕ) (s := .tapp (.fvar 5) (.bvar 0)) (t := .fvar 0) (δ := .top) (x := 0)
  change Term.tapp (.fvar 5) (.bvar 0) = Term.tapp (.fvar 5) .top at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTy_substTm_var` idx 5: necessary (s = tapp (fvar 5) (bvar 0), t = fvar 0)
theorem w2c1_otstmv5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.openTy_substTm_var 5 := fun h => by
  have e := h (Var := ℕ) (s := .tapp (.fvar 5) (.bvar 0)) (t := .fvar 0) (x := 0) (Y := 3)
  change Term.tapp (.fvar 5) (.bvar 0) = Term.tapp (.fvar 5) (.fvar 3) at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.substTy_lc` idx 6: necessary (δ = bvar 0 substituted into tapp (fvar 0) (fvar 0))
theorem w2c1_stlc6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.substTy_lc 6 := fun h => by
  have e := h (Var := ℕ) (t := .tapp (.fvar 0) (.fvar 0)) (δ := .bvar 0) (.tapp .var .var) (X := 0)
  change Term.LC (Term.tapp (.fvar 0) (.bvar 0)) at e
  cases e with | tapp _ h2 => nomatch h2

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding.subst_fresh` idx 4: necessary (γ = sub (fvar 0), X = 0)
theorem w2c1_bsf4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Binding.subst_fresh 4 := fun h => by
  have e := h (Var := ℕ) (X := 0) (γ := .sub (.fvar 0)) (δ := .top)
  change Binding.sub (Ty.fvar 0) = Binding.sub .top at e; cases e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.open_tm_body` idx 5: necessary (t₁ = bvar 1)
theorem w2c1_otb5 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.open_tm_body 5 := fun h => by
  have e := h (Var := ℕ) (t₁ := .bvar 1) (t₂ := .fvar 0) .var
  change Term.LC (Term.bvar 1) at e; nomatch e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.open_tm_body` idx 6: necessary (t₁ = t₂ = bvar 0)
theorem w2c1_otb6 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Term.open_tm_body 6 := fun h => by
  have e := h (Var := ℕ) (t₁ := .bvar 0) (t₂ := .bvar 0) ⟨∅, fun x _ => .var⟩
  change Term.LC (Term.bvar 0) at e; nomatch e

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.preservation` idx 7: necessary (ill-formed context [0 : fvar 7])
theorem w2c1_pres7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.preservation 7 := fun h =>
  badTy (h (Var := ℕ) (Γ := [⟨0, .ty (.fvar 7)⟩]) (τ := .top)
    (Term.Red.abs fLcId (Term.Value.abs fLcId))).wf.1

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.preservation` idx 8: necessary (t' = bvar 0 is not locally closed)
theorem w2c1_pres8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.preservation 8 := fun h => by
  have := (h (Var := ℕ) (t' := .bvar 0) (fId .top .top)).wf.2.1
  nomatch this

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.refl` idx 4: necessary (ill-formed context, σ = ⊤)
theorem w2c1_srefl4 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.refl 4 := fun h =>
  badTy (Sub.wf _ _ _ (h (Var := ℕ) (Γ := [⟨0, .ty (.fvar 7)⟩]) (σ := .top) .top)).1

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.weaken` idx 8: necessary (Δ ill-formed)
theorem w2c1_sweak8 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.weaken 8 := fun h =>
  badTy (Sub.wf _ _ _ (h (Var := ℕ) (Γ := []) (Δ := [⟨0, .ty (.fvar 7)⟩]) (Θ := []) fSubTop)).1

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.weaken_head` idx 7: necessary (Γ ill-formed)
theorem w2c1_sweakh7 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.weaken_head 7 := fun h =>
  badTy (Sub.wf _ _ _ (h (Var := ℕ) (Γ := [⟨0, .ty (.fvar 7)⟩]) (Δ := []) fSubTop)).1

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow_aux` idx 11: necessary (δ = ⊤ narrowed to the ill-formed δ' = fvar 7)
theorem w2c1_snarrowa11 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow_aux 11 := fun h =>
  badSub (Sub.wf _ _ _ (h (Var := ℕ) (Γ := []) (Δ := []) (σ := .top) (τ := .top) (δ := .top) (X := 0)
    (δ' := .fvar 7) (fun _ _ _ => Sub.trans) (.top (fwSub 0) .top))).1

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow` idx 9: necessary (δ' = ⊤ narrowed to the ill-formed δ = fvar 7)
theorem w2c1_snarrow9 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.narrow 9 := fun h =>
  badSub (Sub.wf _ _ _ (h (Var := ℕ) (Γ := []) (Δ := []) (σ := .top) (τ := .top) (δ := .fvar 7) (δ' := .top)
    (X := 0) (.top (fwSub 0) .top))).1

-- `Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.map_subst` idx 11: necessary (σ = fvar 0 substituted by the unbound fvar 7)
theorem w2c1_smap11 : ¬ drop0% Cslib.LambdaCalculus.LocallyNameless.Fsub.Sub.map_subst 11 := fun h => by
  have := (Sub.wf _ _ _ (h (Var := ℕ) (Γ := []) (Δ := []) (σ := .fvar 0) (τ := .top) (δ := .fvar 7) (X := 0)
    (δ' := .top) (.top (fwSub 0) (fwVar 0)))).2.1
  change Ty.Wf [] (Ty.fvar 7) at this
  exact fNotWf0 this

end
