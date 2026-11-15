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

namespace T2c1
open Turing

inductive St | R | L | E1 | E2 | W

def stF : St → Fin 5 | .R => 0 | .L => 1 | .E1 => 2 | .E2 => 3 | .W => 4

instance : Finite St := Finite.of_injective stF (by
  intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide))

-- zigzag machine: R/L walk right/left over the marks (one more per round, input head counts rounds),
-- then E1/E2 erase the marks and W rewinds the input head
noncomputable def M : MultiTapeTM 1 Bool St :=
  MultiTapeTM.ofTr .R (fun q inp work => match q, work 0 with
    | .R, some _ => ⟨.zero, fun _ => (none, .pos), some true, some .R⟩
    | .R, none => ⟨.zero, fun _ => (some (some true), .neg), some true, some .L⟩
    | .L, some _ => ⟨.zero, fun _ => (none, .neg), some true, some .L⟩
    | .L, none => match inp with
      | some _ => ⟨.pos, fun _ => (none, .pos), none, some .R⟩
      | none => ⟨.zero, fun _ => (none, .pos), none, some .E1⟩
    | .E1, some _ => ⟨.zero, fun _ => (none, .pos), none, some .E1⟩
    | .E1, none => ⟨.zero, fun _ => (none, .neg), none, some .E2⟩
    | .E2, some _ => ⟨.zero, fun _ => (some none, .neg), none, some .E2⟩
    | .E2, none => ⟨.neg, fun _ => (none, .pos), none, some .W⟩
    | .W, _ => match inp with
      | some _ => ⟨.neg, fun _ => (none, .zero), none, some .W⟩
      | none => ⟨.pos, fun _ => (none, .zero), none, none⟩)

def marks (r : ℕ) : ℤ → Option Bool := fun j => if 0 ≤ j ∧ j < r then some true else none

def mk {w : List Bool} (q : Option St) (ip : Fin (w.length + 2)) (r : ℕ) (p : ℤ)
    (out : List Bool) : Cfg 1 Bool St w := ⟨q, ip, fun _ => marks r, fun _ => p, out⟩

theorem sR1 {w : List Bool} (ip : Fin (w.length + 2)) (r : ℕ) (p : ℤ) (out : List Bool)
    (h0 : 0 ≤ p) (h1 : p < r) :
    M.step (mk (some .R) ip r p out) = mk (some .R) ip r (p + 1) (out ++ [true]) := by
  rw [MultiTapeTM.step_of_state (q := .R) rfl]
  have : (mk (w := w) (some .R) ip r p out).workTapeSymbols 0 = some true := by
    simp [Cfg.workTapeSymbols, mk, marks, h0, h1]
  simp only [M, MultiTapeTM.tr_ofTr, this]
  ext <;> simp [mk, Action.apply, SignType.cast]

theorem sR2 {w : List Bool} (ip : Fin (w.length + 2)) (r : ℕ) (out : List Bool) :
    M.step (mk (some .R) ip r r out) = mk (some .L) ip (r + 1) (r - 1) (out ++ [true]) := by
  rw [MultiTapeTM.step_of_state (q := .R) rfl]
  have : (mk (w := w) (some .R) ip r r out).workTapeSymbols 0 = none := by
    simp [Cfg.workTapeSymbols, mk, marks]
  simp only [M, MultiTapeTM.tr_ofTr, this]
  ext
  · simp [mk, Action.apply]
  · simp [mk, Action.apply]
  · rename_i i j
    simp only [mk, Action.apply, marks, Function.update_apply]
    split_ifs <;> first | rfl | omega
  · simp [mk, Action.apply, SignType.cast]; ring
  · simp [mk, Action.apply]

theorem sL1 {w : List Bool} (ip : Fin (w.length + 2)) (r : ℕ) (p : ℤ) (out : List Bool)
    (h0 : 0 ≤ p) (h1 : p < r) :
    M.step (mk (some .L) ip r p out) = mk (some .L) ip r (p - 1) (out ++ [true]) := by
  rw [MultiTapeTM.step_of_state (q := .L) rfl]
  have : (mk (w := w) (some .L) ip r p out).workTapeSymbols 0 = some true := by
    simp [Cfg.workTapeSymbols, mk, marks, h0, h1]
  simp only [M, MultiTapeTM.tr_ofTr, this]
  ext <;> simp [mk, Action.apply, SignType.cast]; ring

theorem sL2 {w : List Bool} (ip : Fin (w.length + 2)) (r : ℕ) (out : List Bool) (b : Bool)
    (hb : (mk (w := w) (some .L) ip r (-1) out).inputSymbol = some b) :
    M.step (mk (some .L) ip r (-1) out) = mk (some .R) (moveInputPos ip .pos) r 0 out := by
  rw [MultiTapeTM.step_of_state (q := .L) rfl]
  have : (mk (w := w) (some .L) ip r (-1) out).workTapeSymbols 0 = none := by
    simp [Cfg.workTapeSymbols, mk, marks]
  simp only [M, MultiTapeTM.tr_ofTr, this, hb]
  ext <;> simp [mk, Action.apply, SignType.cast]

theorem sL3 {w : List Bool} (ip : Fin (w.length + 2)) (r : ℕ) (out : List Bool)
    (hb : (mk (w := w) (some .L) ip r (-1) out).inputSymbol = none) :
    M.step (mk (some .L) ip r (-1) out) = mk (some .E1) ip r 0 out := by
  rw [MultiTapeTM.step_of_state (q := .L) rfl]
  have : (mk (w := w) (some .L) ip r (-1) out).workTapeSymbols 0 = none := by
    simp [Cfg.workTapeSymbols, mk, marks]
  simp only [M, MultiTapeTM.tr_ofTr, this, hb]
  ext <;> simp [mk, Action.apply, SignType.cast]

theorem rfS {w : List Bool} (c : Cfg 1 Bool St w) (d : ℕ) :
    M.runFrom c (d + 1) = M.runFrom (M.step c) d := by
  simp only [MultiTapeTM.runFrom, Function.iterate_succ_apply]

theorem rf1 {w : List Bool} (c : Cfg 1 Bool St w) : M.runFrom c 1 = M.step c := rfl

theorem rfA {w : List Bool} (c : Cfg 1 Bool St w) (a b : ℕ) :
    M.runFrom c (a + b) = M.runFrom (M.runFrom c a) b := by
  simp only [MultiTapeTM.runFrom]; rw [add_comm, Function.iterate_add_apply]

theorem walkR {w : List Bool} (ip : Fin (w.length + 2)) (r : ℕ) : ∀ (d : ℕ) (p : ℤ)
    (out : List Bool), 0 ≤ p → p + d = r →
    M.runFrom (mk (some .R) ip r p out) d = mk (some .R) ip r r (out ++ List.replicate d true)
  | 0, p, out, _, h => by simp [MultiTapeTM.runFrom]; congr; omega
  | d + 1, p, out, h0, h => by
    rw [rfS, sR1 ip r p out h0 (by omega), walkR ip r d (p + 1) _ (by omega) (by omega)]
    simp [List.replicate_succ]

theorem walkL {w : List Bool} (ip : Fin (w.length + 2)) (r : ℕ) : ∀ (d : ℕ) (p : ℤ)
    (out : List Bool), p + 1 = d → d ≤ r →
    M.runFrom (mk (some .L) ip r p out) d =
      mk (some .L) ip r (-1) (out ++ List.replicate d true)
  | 0, p, out, h, _ => by simp [MultiTapeTM.runFrom]; congr; omega
  | d + 1, p, out, h, hr => by
    rw [rfS, sL1 ip r p out (by omega) (by omega), walkL ip r d (p - 1) _ (by omega) (by omega)]
    simp [List.replicate_succ]

-- round r on input 1^n
def cR (n r : ℕ) (hr : r ≤ n) : Cfg 1 Bool St (List.replicate n true) :=
  mk (some .R) ⟨r + 1, by simp; omega⟩ r 0 (List.replicate (r * r) true)

theorem round (n r : ℕ) (hr : r ≤ n) :
    M.runFrom (cR n r hr) (r + 1 + r + 1) =
      if h : r < n then cR n (r + 1) h
      else mk (some .E1) ⟨r + 1, by simp; omega⟩ (r + 1) 0 (List.replicate ((r + 1) * (r + 1)) true) := by
  rw [rfA, rfA, rfA, cR, walkR _ r r 0 _ le_rfl (by simp), rf1 (mk (some .R) _ _ _ _),
    sR2, walkL _ (r + 1) r ((r : ℤ) - 1) _ (by omega) (by omega), rf1]
  have eo : List.replicate (r * r) true ++ List.replicate r true ++ [true] ++ List.replicate r true
      = List.replicate ((r + 1) * (r + 1)) true := by
    simp only [← List.replicate_succ', ← List.replicate_add]; congr 1; ring
  split_ifs with h
  · rw [sL2 (b := true)]
    · simp only [cR, eo]; congr
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · exact inputSymbolInner r (by simp [mk]; omega) (by simp; omega) |>.trans (by simp)
  · rw [sL3, eo]
    exact inputSymbol_eq_none_of_boundary (Or.inr (by simp [mk]; omega))

theorem sE1a {w : List Bool} (ip : Fin (w.length + 2)) (r : ℕ) (p : ℤ) (out : List Bool)
    (h0 : 0 ≤ p) (h1 : p < r) :
    M.step (mk (some .E1) ip r p out) = mk (some .E1) ip r (p + 1) out := by
  rw [MultiTapeTM.step_of_state (q := .E1) rfl]
  have : (mk (w := w) (some .E1) ip r p out).workTapeSymbols 0 = some true := by
    simp [Cfg.workTapeSymbols, mk, marks, h0, h1]
  simp only [M, MultiTapeTM.tr_ofTr, this]
  ext <;> simp [mk, Action.apply, SignType.cast]

theorem sE1b {w : List Bool} (ip : Fin (w.length + 2)) (r : ℕ) (out : List Bool) :
    M.step (mk (some .E1) ip r r out) = mk (some .E2) ip r (r - 1) out := by
  rw [MultiTapeTM.step_of_state (q := .E1) rfl]
  have : (mk (w := w) (some .E1) ip r r out).workTapeSymbols 0 = none := by
    simp [Cfg.workTapeSymbols, mk, marks]
  simp only [M, MultiTapeTM.tr_ofTr, this]
  ext <;> simp [mk, Action.apply, SignType.cast]; ring

theorem sE2a {w : List Bool} (ip : Fin (w.length + 2)) (r : ℕ) (p : ℤ) (out : List Bool)
    (hp : p = r) :
    M.step (mk (some .E2) ip (r + 1) p out) = mk (some .E2) ip r (p - 1) out := by
  subst hp
  rw [MultiTapeTM.step_of_state (q := .E2) rfl]
  have : (mk (w := w) (some .E2) ip (r + 1) r out).workTapeSymbols 0 = some true := by
    simp [Cfg.workTapeSymbols, mk, marks]
  simp only [M, MultiTapeTM.tr_ofTr, this]
  ext
  · simp [mk, Action.apply]
  · simp [mk, Action.apply]
  · rename_i i j
    simp only [mk, Action.apply, marks, Function.update_apply]
    split_ifs <;> first | rfl | omega
  · simp [mk, Action.apply, SignType.cast]; ring
  · simp [mk, Action.apply]

theorem sE2b {w : List Bool} (ip : Fin (w.length + 2)) (out : List Bool) :
    M.step (mk (some .E2) ip 0 (-1) out) = mk (some .W) (moveInputPos ip .neg) 0 0 out := by
  rw [MultiTapeTM.step_of_state (q := .E2) rfl]
  have : (mk (w := w) (some .E2) ip 0 (-1) out).workTapeSymbols 0 = none := by
    simp [Cfg.workTapeSymbols, mk, marks]
  simp only [M, MultiTapeTM.tr_ofTr, this]
  ext <;> simp [mk, Action.apply, SignType.cast]

theorem sWa {w : List Bool} (ip : Fin (w.length + 2)) (out : List Bool) (b : Bool)
    (hb : (mk (w := w) (some .W) ip 0 0 out).inputSymbol = some b) :
    M.step (mk (some .W) ip 0 0 out) = mk (some .W) (moveInputPos ip .neg) 0 0 out := by
  rw [MultiTapeTM.step_of_state (q := .W) rfl]
  simp only [M, MultiTapeTM.tr_ofTr, hb]
  ext <;> simp [mk, Action.apply, SignType.cast]

theorem sWb {w : List Bool} (ip : Fin (w.length + 2)) (out : List Bool)
    (hb : (mk (w := w) (some .W) ip 0 0 out).inputSymbol = none) :
    M.step (mk (some .W) ip 0 0 out) = mk none (moveInputPos ip .pos) 0 0 out := by
  rw [MultiTapeTM.step_of_state (q := .W) rfl]
  simp only [M, MultiTapeTM.tr_ofTr, hb]
  ext <;> simp [mk, Action.apply, SignType.cast]

theorem walkE1 {w : List Bool} (ip : Fin (w.length + 2)) (r : ℕ) (out : List Bool) :
    ∀ (d : ℕ) (p : ℤ), 0 ≤ p → p + d = r →
    M.runFrom (mk (some .E1) ip r p out) d = mk (some .E1) ip r r out
  | 0, p, _, h => by rw [show p = r by simpa using h]; rfl
  | d + 1, p, h0, h => by
    rw [rfS, sE1a ip r p out h0 (by omega), walkE1 ip r out d (p + 1) (by omega) (by omega)]

theorem walkE2 {w : List Bool} (ip : Fin (w.length + 2)) (out : List Bool) :
    ∀ (r : ℕ) (p : ℤ), p = r - 1 →
    M.runFrom (mk (some .E2) ip r p out) r = mk (some .E2) ip 0 (-1) out
  | 0, p, h => by rw [show p = -1 by simpa using h]; rfl
  | r + 1, p, h => by
    rw [rfS, sE2a ip r p out (by omega), walkE2 ip out r (p - 1) (by omega)]

theorem walkW (n : ℕ) (out : List Bool) : ∀ (j : ℕ) (hj : j ≤ n),
    M.runFrom (mk (w := List.replicate n true) (some .W) ⟨j, by simp; omega⟩ 0 0 out) j =
      mk (some .W) ⟨0, by simp⟩ 0 0 out
  | 0, _ => rfl
  | j + 1, hj => by
    rw [rfS, sWa (b := true)]
    · rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
      exact walkW n out j (by omega)
    · exact inputSymbolInner j (by simp [mk]; omega) (by simp; omega) |>.trans (by simp)

theorem cleanup (n : ℕ) (out : List Bool) :
    M.runFrom (mk (w := List.replicate n true) (some .E1) ⟨n + 1, by simp⟩ (n + 1) 0 out)
      ((n + 1) + (1 + ((n + 1) + (1 + (n + 1))))) = mk none ⟨1, by simp⟩ 0 0 out := by
  rw [rfA _ (n + 1), walkE1 _ _ _ (n + 1) 0 le_rfl (by simp), rfA _ 1, rf1, sE1b,
    rfA _ (n + 1), walkE2 _ _ (n + 1) _ rfl, rfA _ 1, rf1, sE2b,
    moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
  simp only [add_tsub_cancel_right]
  rw [rfA _ n, walkW n out n le_rfl, rf1, sWb]
  · congr 1
  · exact inputSymbol_eq_none_of_boundary (Or.inl (by simp [mk]))

theorem initR (n : ℕ) : M.initCfg (List.replicate n true) = cR n 0 (Nat.zero_le _) := by
  ext <;> simp [cR, mk, marks, Cfg.init, MultiTapeNTM.initCfg, M]

theorem runR (n : ℕ) : ∀ r (hr : r ≤ n),
    M.runFrom (M.initCfg (List.replicate n true)) (r * (r + 1)) = cR n r hr
  | 0, _ => by rw [initR]; rfl
  | r + 1, hr => by
    have := round n r (by omega)
    rw [dite_eq_left_of_eq_true (eq_true (by omega))] at this
    rw [show (r + 1) * (r + 1 + 1) = r * (r + 1) + (r + 1 + r + 1) by ring, rfA, runR n r (by omega),
      this]

def tT (n : ℕ) : ℕ := n * (n + 1) + (n + 1 + n + 1) + ((n + 1) + (1 + ((n + 1) + (1 + (n + 1)))))

theorem haltR (n : ℕ) : M.runFrom (M.initCfg (List.replicate n true)) (tT n) =
    mk none ⟨1, by simp⟩ 0 0 (List.replicate ((n + 1) * (n + 1)) true) := by
  rw [tT, rfA _ (n * (n + 1) + (n + 1 + n + 1)), rfA _ (n * (n + 1)), runR n n le_rfl, round n n le_rfl,
    dite_eq_right_of_eq_false (eq_false (lt_irrefl n)), cleanup]

theorem posB {w : List Bool} : ∀ i : ℕ, |(M.runFrom (M.initCfg w) i).workTapePos 0| ≤ i
  | 0 => by simp [MultiTapeTM.runFrom, Cfg.init]
  | i + 1 => by
    have ih := posB (w := w) i
    rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom]
    rcases hq : (M.runFrom (M.initCfg w) i).state with _ | q
    · rw [MultiTapeTM.step_of_halt hq]; push_cast; linarith
    · rw [MultiTapeTM.step_of_state hq]
      have := Turing.workTapePos_apply_le (M.tr q (M.runFrom (M.initCfg w) i).inputSymbol
        (M.runFrom (M.initCfg w) i).workTapeSymbols) (M.runFrom (M.initCfg w) i) 0
      rw [abs_le] at this ih ⊢; push_cast; constructor <;> linarith

theorem spB {w : List Bool} {T : ℕ} (hT : (M.runFrom (M.initCfg w) T).state = none) :
    M.RunsInSpace w (2 * T + 1) := fun p => by
  have h := MultiTapeNTM.RunPath.spaceUsedByTape_le_card p.toRunPath (i := 0) (S := window T) (by
    rintro c ⟨i, rfl⟩
    rw [MultiTapeTM.runPath_apply_eq_runFrom, p.head_eq, mem_window]
    rcases le_total (i : ℕ) T with hi | hi
    · have := posB (w := w) i; rw [abs_le] at this; omega
    · rw [MultiTapeTM.runFrom_eq_of_halt _ _ hi hT]; have := posB (w := w) T; rw [abs_le] at this; omega)
  rw [card_window] at h
  change ∑ j, MultiTapeNTM.RunPath.spaceUsedByTape p.toRunPath j ≤ _
  simpa using h

theorem inSym {Q : Type} {w : List Bool} (c c' : Cfg 0 Bool Q w) (h : c.inputPos = c'.inputPos) :
    c.inputSymbol = c'.inputSymbol := by
  simp only [Cfg.inputSymbol, h]

-- a halting machine with no work tapes outputs at most |Q|·(|w|+2) symbols
theorem tapeless {Q : Type} [Finite Q] (tm : MultiTapeTM 0 Bool Q) (w : List Bool) (T : ℕ)
    (hT : (tm.runFrom (tm.initCfg w) T).state = none) :
    (tm.runFrom (tm.initCfg w) T).output.length ≤ Nat.card Q * (w.length + 2) := by
  classical
  have := Fintype.ofFinite Q
  set c : ℕ → Cfg 0 Bool Q w := fun i => tm.runFrom (tm.initCfg w) i with hc
  have hstep : ∀ i, c (i + 1) = tm.step (c i) := fun i => by
    simp only [hc, MultiTapeTM.runFrom, Function.iterate_succ_apply']
  have hout : ∀ i, (c i).output.length ≤ i := by
    intro i; induction i with
    | zero => simp [hc, MultiTapeTM.runFrom, Cfg.init]
    | succ i ih =>
      rw [hstep]
      rcases hq : (c i).state with _ | q
      · rw [MultiTapeTM.step_of_halt hq]; omega
      · rw [MultiTapeTM.step_of_state hq]
        simp only [Action.apply_output, List.length_append]
        have : ∀ o : Option Bool, o.toList.length ≤ 1 := fun o => by cases o <;> simp
        have := this (tm.tr q (c i).inputSymbol (c i).workTapeSymbols).output
        omega
  let key : ℕ → Option Q × Fin (w.length + 2) := fun i => ((c i).state, (c i).inputPos)
  have hdet : ∀ i j, key i = key j → key (i + 1) = key (j + 1) := by
    intro i j hij
    simp only [key, Prod.mk.injEq] at hij
    obtain ⟨hs, hp⟩ := hij
    show ((c (i+1)).state, (c (i+1)).inputPos) = ((c (j+1)).state, (c (j+1)).inputPos)
    rw [hstep, hstep]
    rcases hq : (c i).state with _ | q
    · rw [MultiTapeTM.step_of_halt hq, MultiTapeTM.step_of_halt (hs ▸ hq)]
      simp [hs, hp]
    · rw [MultiTapeTM.step_of_state hq, MultiTapeTM.step_of_state (hs ▸ hq), inSym _ _ hp,
        show (c i).workTapeSymbols = (c j).workTapeSymbols from funext fun x => x.elim0]
      simp [Action.apply, hp]
  have hiter : ∀ d i j, key i = key j → key (i + d) = key (j + d) := by
    intro d; induction d with
    | zero => exact fun i j h => h
    | succ d ih => exact fun i j h => hdet _ _ (ih i j h)
  set B := Nat.card Q * (w.length + 2)
  by_cases hA : ∃ i ≤ B, (c i).state = none
  · obtain ⟨i, hiB, hi⟩ := hA
    have e : c T = c i := by
      rcases le_total i T with h | h
      · exact MultiTapeTM.runFrom_eq_of_halt _ _ h hi
      · exact (MultiTapeTM.runFrom_eq_of_halt _ _ h hT).symm
    change (c T).output.length ≤ B
    rw [e]; exact (hout i).trans hiB
  · simp only [not_exists, not_and] at hA
    exfalso
    let g : Fin (B + 1) → Q × Fin (w.length + 2) := fun i => ((c i).state.getD tm.q₀, (c i).inputPos)
    obtain ⟨a, b, hab, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt g (by
      simp [B, Nat.card_eq_fintype_card])
    have hk : ∀ a b : Fin (B + 1), g a = g b → key a = key b := by
      intro a b h
      simp only [g, Prod.mk.injEq] at h
      obtain ⟨qa, hqa⟩ := Option.ne_none_iff_exists'.mp (hA a (by omega))
      obtain ⟨qb, hqb⟩ := Option.ne_none_iff_exists'.mp (hA b (by omega))
      simp only [key, hqa, hqb, Option.getD_some] at h ⊢
      rw [h.1, h.2]
    -- wlog a < b
    obtain ⟨a, b, hlt, hkab⟩ : ∃ a b : ℕ, a < b ∧ b ≤ B ∧ key a = key b := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
      · exact ⟨a, b, h, by omega, hk a b hg⟩
      · exact ⟨b, a, h, by omega, (hk a b hg).symm⟩
    have hall : ∀ x, (c x).state ≠ none := by
      intro x
      induction x using Nat.strong_induction_on with
      | _ x ih =>
        by_cases hx : x ≤ B
        · exact hA x hx
        · have e := hiter (x - b) a b hkab.2
          rw [show b + (x - b) = x by omega] at e
          have := ih (a + (x - b)) (by omega)
          intro hxn; apply this
          have := congrArg Prod.fst e
          simp only [key] at this
          rw [this]; exact hxn
    exact hall T hT

def encU : ℕ ↪ List Bool := ⟨fun n => List.replicate n true, fun a b h => by
  simpa using congrArg List.length h⟩

theorem encU_apply (n : ℕ) : encU n = List.replicate n true := rfl

def fSq (n : ℕ) : List Bool := List.replicate ((n + 1) * (n + 1)) true

theorem compM : MultiTapeTM.ComputableInTimeAndSpace fSq encU (Function.Embedding.refl _) tT
    (fun n => 2 * tT n + 1) := by
  refine ⟨1, St, inferInstance, M, fun n => ?_⟩
  have hh : (M.runFrom (M.initCfg (encU n)) (tT n)).state = none := by
    rw [encU_apply, haltR]; rfl
  refine ⟨⟨tT n, hh, ?_⟩, MultiTapeTM.runsInTime_of_halted hh, spB hh⟩
  rw [encU_apply, haltR]; rfl

-- space 0 forces no work tapes
theorem k0 {k : ℕ} {Q : Type} {tm : MultiTapeTM (k + 1) Bool Q} {w : List Bool}
    (h : tm.RunsInSpace w 0) : False := by
  have h1 := h (MultiTapeNTM.ComputationPath.ofDeterministic tm w 0)
  have h2 : 0 < MultiTapeNTM.RunPath.spaceUsedByTape
      (MultiTapeNTM.ComputationPath.ofDeterministic tm w 0).toRunPath 0 :=
    Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  have h3 := Finset.single_le_sum (f := fun j => MultiTapeNTM.RunPath.spaceUsedByTape
      (MultiTapeNTM.ComputationPath.ofDeterministic tm w 0).toRunPath j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
  change ∑ j, MultiTapeNTM.RunPath.spaceUsedByTape _ j ≤ 0 at h1
  omega

-- fSq is not computable without work tapes: its output length is quadratic
theorem noTapeless {k : ℕ} {Q : Type} [Finite Q] (tm : MultiTapeTM k Bool Q) {t : ℕ → ℕ}
    (H : tm.ComputesFunInTimeAndSpace encU (Function.Embedding.refl _) fSq t (fun _ => 0)) :
    False := by
  cases k with
  | succ k => exact k0 (H 0).2.2
  | zero =>
    obtain ⟨u, hu, ho⟩ := (H (Nat.card Q + 1)).1
    have := tapeless tm _ u hu
    rw [ho, encU_apply] at this
    simp only [Function.Embedding.refl_apply, fSq, List.length_replicate] at this
    nlinarith

theorem compT : MultiTapeTM.ComputableTidilyInTimeAndSpace fSq encU (Function.Embedding.refl _) tT
    (fun n => 2 * tT n + 1) := by
  refine ⟨1, St, inferInstance, M, fun n => MultiTapeTM.computesTidily_iff.mpr
    ⟨MultiTapeNTM.RunPath.ofDeterministic M (M.initCfg (encU n)) (tT n), ?_, ?_, le_rfl, ?_⟩⟩
  · change M.initCfg (encU n) = _
    ext <;> simp [wordsCfg, Cfg.init, MultiTapeNTM.initCfg]
  · change M.runFrom (M.initCfg (encU n)) (tT n) = _
    rw [encU_apply, haltR]
    ext <;> simp [mk, marks, wordsCfg, fSq]
  · have hh : (M.runFrom (M.initCfg (encU n)) (tT n)).state = none := by
      rw [encU_apply, haltR]; rfl
    exact spB hh (MultiTapeNTM.ComputationPath.ofDeterministic M _ (tT n))

theorem k0p {k : ℕ} {Q : Type} {tm : MultiTapeTM (k + 1) Bool Q} {w : List Bool}
    (p : tm.RunPath w) (h : p.space ≤ 0) : False := by
  have h2 : 0 < MultiTapeNTM.RunPath.spaceUsedByTape p 0 :=
    Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
  have h3 := Finset.single_le_sum (f := fun j => MultiTapeNTM.RunPath.spaceUsedByTape p j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
  change ∑ j, MultiTapeNTM.RunPath.spaceUsedByTape _ j ≤ 0 at h
  omega

theorem noTapelessT {k : ℕ} {Q : Type} [Finite Q] (tm : MultiTapeTM k Bool Q) {t : ℕ → ℕ}
    (H : MultiTapeTM.ComputesFunTidilyInTimeAndSpace tm encU (Function.Embedding.refl _) fSq t
      (fun _ => 0)) : False := by
  obtain ⟨p, hh, hl, -, hs⟩ := MultiTapeTM.computesTidily_iff.mp (H (Nat.card Q + 1))
  cases k with
  | succ k => exact k0p p hs
  | zero =>
    have e1 : p.last = tm.runFrom p.head p.length :=
      MultiTapeTM.runPath_apply_eq_runFrom p (Fin.last _)
    have e2 : p.head = tm.initCfg (encU (Nat.card Q + 1)) := by
      rw [hh]; exact Cfg.ext_zero_tapes rfl rfl rfl
    have e : p.last = tm.runFrom (tm.initCfg (encU (Nat.card Q + 1))) p.length := by
      rw [e1, e2]
    have hT : (tm.runFrom (tm.initCfg (encU (Nat.card Q + 1))) p.length).state = none := by
      rw [← e, hl]; rfl
    have := tapeless tm _ _ hT
    rw [← e, hl] at this
    simp only [wordsCfg, encU_apply, Function.Embedding.refl_apply, fSq,
      List.length_replicate] at this
    nlinarith

end T2c1

-- `Turing.MultiTapeTM.ComputableInTimeAndSpace.mono` 11: necessary (f n = 1^((n+1)²) on unary input: a zigzag machine with one work tape computes it in time n²+6n+7; space 0 forces no work tapes, and a halting tapeless machine outputs ≤ |Q|(n+2) symbols)
theorem cim11 : ¬ drop0% Turing.MultiTapeTM.ComputableInTimeAndSpace.mono 11 := fun h => by
  obtain ⟨k, Q, hQ, tm, H⟩ := @h ℕ (List Bool) T2c1.fSq T2c1.encU (Function.Embedding.refl _)
    T2c1.tT (fun n => 2 * T2c1.tT n + 1) T2c1.tT (fun _ => 0) T2c1.compM (fun _ => le_rfl)
  exact T2c1.noTapeless tm H

-- `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.mono` 11: necessary (same zigzag machine, which erases its marks and rewinds its input head; space 0 forces no work tapes, and a halting tapeless machine outputs ≤ |Q|(n+2) symbols)
theorem ctm11 : ¬ drop0% Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.mono 11 := fun h => by
  obtain ⟨k, Q, hQ, tm, H⟩ := @h ℕ (List Bool) T2c1.fSq T2c1.encU (Function.Embedding.refl _)
    T2c1.tT (fun n => 2 * T2c1.tT n + 1) T2c1.tT (fun _ => 0) T2c1.compT (fun _ => le_rfl)
  exact T2c1.noTapelessT tm H


open Cslib Cslib.Circuits

namespace T2c1

def mS : Signature.{0} := ⟨Option (Fin 5), fun o => o.elim 6 (fun _ => 0)⟩
instance : Finite mS.Op := inferInstanceAs (Finite (Option (Fin 5)))
def mI : Interpretation mS (Fin 5) := fun op => match op with
  | none => fun v : Fin 6 → Fin 5 => v (v 0).succ
  | some u => fun _ => u

def lf (n j : ℕ) (φ : (Fin j → Fin 5) → Fin 5) : (Fin n → Fin 5) → Fin 5 :=
  fun x => φ (fun i => if h : i.val < n then x ⟨i, h⟩ else 0)

def margs (n j : ℕ) (hj : j < n) (φ : (Fin (j+1) → Fin 5) → Fin 5) :
    Fin 6 → (Fin n → Fin 5) → Fin 5 :=
  Fin.cons (fun x => x ⟨j, hj⟩) (fun u => lf n j (fun y => φ (Fin.snoc y u)))

theorem margs_eq {n j : ℕ} (hj : j < n) (φ : (Fin (j+1) → Fin 5) → Fin 5) :
    (fun x => mI none (fun i => margs n j hj φ i x)) = lf n (j+1) φ := by
  funext x
  show margs n j hj φ ((margs n j hj φ 0 x).succ) x = _
  simp only [margs, Fin.cons_zero, Fin.cons_succ, lf]
  congr 1; funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [hj]
  · simp

abbrev L (n j : ℕ) : Set ((Fin n → Fin 5) → Fin 5) := Set.range (lf n j)

theorem inp {n j : ℕ} (hj : j < n) : (fun x : Fin n → Fin 5 => x ⟨j, hj⟩) ∈ inputs n :=
  ⟨⟨j, hj⟩, rfl⟩

theorem lvl {n j : ℕ} (hj : j < n) :
    Synthesis mI (inputs n ∪ L n j) (L n (j+1)) (5 ^ (5 ^ (j+1))) := by
  have := Synthesis.family (I := mI) (s := inputs n ∪ L n j) (lf n (j+1)) (fun _ => 1)
    (fun φ => by
      rw [← margs_eq hj]
      exact Synthesis.gate (I := mI) none (margs n j hj φ) (fun (i : Fin 6) => by
        refine Fin.cases ?_ (fun u => ?_) i
        · exact Or.inl (inp hj)
        · exact Or.inr ⟨fun y => φ (Fin.snoc y u), rfl⟩))
  simpa [Fintype.card_fun] using this

def z0 (n : ℕ) : Fin 0 → (Fin n → Fin 5) → Fin 5 := Fin.elim0

theorem lvl0 (n : ℕ) : Synthesis mI (inputs n) (L n 0) 5 := by
  have := Synthesis.family (I := mI) (s := inputs n) (lf n 0) (fun _ => 1)
    (fun φ => by
      have e : lf n 0 φ = fun x => mI (some (φ Fin.elim0)) (fun i => z0 n i x) := by
        funext x; simp only [lf, mI]; congr 1; funext i; exact i.elim0
      rw [e]
      exact Synthesis.gate (I := mI) (some (φ Fin.elim0)) (z0 n)
        (fun (i : Fin 0) => i.elim0))
  simpa [Fintype.card_fun] using this

def ca : ℕ → ℕ
  | 0 => 5
  | j + 1 => ca j + 5 ^ (5 ^ (j+1))

def ct : ℕ → ℕ
  | 0 => 0
  | t + 1 => 5 * ct t + 1

theorem lvlA (n : ℕ) : ∀ j, j ≤ n → Synthesis mI (inputs n) (L n j) (ca j)
  | 0, _ => lvl0 n
  | j + 1, hj => (lvlA n j (by omega)).trans (lvl (by omega))

theorem tree (n m : ℕ) : ∀ t, m + t ≤ n → ∀ φ : (Fin (m+t) → Fin 5) → Fin 5,
    Synthesis mI (inputs n ∪ L n m) {lf n (m+t) φ} (ct t)
  | 0, _, φ => Synthesis.of_mem (Or.inr ⟨φ, rfl⟩)
  | t + 1, ht, φ => by
    have hj : m + t < n := by omega
    have := Synthesis.gate_of_syntheses (I := mI) (s := inputs n ∪ L n m) none
      (margs n (m+t) hj φ) (Fin.cons (0 : ℕ) (fun _ : Fin 5 => ct t)) (fun (i : Fin 6) => by
        refine Fin.cases ?_ (fun u => ?_) i
        · exact Synthesis.of_mem (Or.inl (inp hj))
        · show Synthesis _ _ {lf n (m+t) (fun y => φ (Fin.snoc y u))} (ct t)
          exact tree n m t (by omega) _)
    rw [margs_eq hj] at this
    refine this.mono subset_rfl subset_rfl ?_
    show (∑ i : Fin 6, (Fin.cons (0:ℕ) (fun _ : Fin 5 => ct t) : Fin 6 → ℕ) i) + 1 ≤ ct (t+1)
    simp [Fin.sum_univ_succ, ct]

theorem lfn (n : ℕ) (f : (Fin n → Fin 5) → Fin 5) : lf n n f = f := by
  funext x; simp [lf]

theorem main (m t : ℕ) (f : (Fin (m+t) → Fin 5) → Fin 5) :
    ∃ c : Circuit mS (m+t) 1, c.Computes mI (single f) ∧ c.size ≤ ca m + ct t := by
  have h := (lvlA (m+t) m (by omega)).trans (tree (m+t) m t le_rfl f)
  rw [lfn] at h
  exact h.exists_circuit

theorem ct_eq : ∀ t, 4 * ct t + 1 = 5 ^ t
  | 0 => rfl
  | t + 1 => by have := ct_eq t; simp only [ct, pow_succ]; omega

theorem ca_le : ∀ m, ca m ≤ (m + 1) * 5 ^ (5 ^ m)
  | 0 => by simp [ca]
  | m + 1 => by
    have h1 := ca_le m
    have h2 : 5 ^ (5 ^ m) ≤ 5 ^ (5 ^ (m+1)) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp only [ca]; nlinarith

theorem sq_le : ∀ Q, 4 * Q ^ 2 ≤ 5 ^ Q
  | 0 => by norm_num
  | 1 => by norm_num
  | Q + 2 => by
    have := sq_le (Q + 1)
    have h2 : 4 * (Q + 2) ^ 2 ≤ 5 * (4 * (Q + 1) ^ 2) := by ring_nf; nlinarith [Nat.zero_le (Q * Q)]
    rw [pow_succ 5 (Q+1)]; linarith

theorem bound (m : ℕ) :
    (m + (2 * 5 ^ m - m)) * (ca m + ct (2 * 5 ^ m - m)) ≤ 5 ^ (m + (2 * 5 ^ m - m)) := by
  have hm : m < 5 ^ m := Nat.lt_pow_self (by norm_num)
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 5 ^ m := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = 2 * 5 ^ m - m := ⟨_, rfl⟩
  rw [← ht]
  have e : m + t = 2 * Q := by omega
  have e1 : 5 ^ (m + t) = Q * 5 ^ t := by rw [pow_add, hQ]
  have e2 : 5 ^ (m + t) = 5 ^ Q * 5 ^ Q := by rw [e, two_mul, pow_add]
  have ha : ca m ≤ Q * 5 ^ Q := by
    have := ca_le m; rw [← hQ] at this
    exact this.trans (Nat.mul_le_mul_right _ (by omega))
  have hc := ct_eq t
  have hs := sq_le Q
  rw [e] at e1 e2 ⊢
  have h1 : 4 * (2 * Q * ca m) ≤ 2 * 5 ^ (2 * Q) := by
    calc 4 * (2 * Q * ca m) ≤ 4 * (2 * Q * (Q * 5 ^ Q)) := by gcongr
      _ = 2 * (4 * Q ^ 2) * 5 ^ Q := by ring
      _ ≤ 2 * 5 ^ Q * 5 ^ Q := by gcongr
      _ = 2 * 5 ^ (2 * Q) := by rw [e2]; ring
  have h2 : 4 * (2 * Q * ct t) ≤ 2 * 5 ^ (2 * Q) := by
    calc 4 * (2 * Q * ct t) = 2 * Q * (4 * ct t) := by ring
      _ ≤ 2 * Q * 5 ^ t := by gcongr; omega
      _ = 2 * 5 ^ (2 * Q) := by rw [e1]; ring
  nlinarith

end T2c1

-- `Cslib.Circuits.Shannon.exists_hard_function` 6: necessary (U = Fin 5, ops: constants and a 6-ary multiplexer x ↦ x (x 0).succ; all functions of the first m inputs, then a 5-ary multiplexer tree: every function on 2·5^m inputs has ≤ 5^n/n gates)
theorem ehf6 : ¬ drop0% Cslib.Circuits.Shannon.exists_hard_function 6 := fun h => by
  obtain ⟨N, hN⟩ := @h T2c1.mS (Fin 5) _ _ _ T2c1.mI
  have hN5 : N < 5 ^ N := Nat.lt_pow_self (by norm_num)
  obtain ⟨f, hf⟩ := hN (N + (2 * 5 ^ N - N)) (by omega)
  obtain ⟨c, hc, hs⟩ := T2c1.main N (2 * 5 ^ N - N) f
  have h1 := hf c hc
  have h2 := T2c1.bound N
  have hn0 : 0 < N + (2 * 5 ^ N - N) := by omega
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  rw [div_lt_iff₀ (by exact_mod_cast hn0)] at h1
  have h3 : c.size * (N + (2 * 5 ^ N - N)) ≤ 5 ^ (N + (2 * 5 ^ N - N)) :=
    (Nat.mul_le_mul_right _ hs).trans (by rw [mul_comm]; exact h2)
  have h4 : (c.size : ℝ) * ((N + (2 * 5 ^ N - N) : ℕ) : ℝ) ≤ (5 : ℝ) ^ (N + (2 * 5 ^ N - N)) := by
    exact_mod_cast h3
  push_cast at h4 h1
  linarith

-- `_private.Cslib.Computability.Circuit.Shannon.0.Cslib.Circuits.Shannon.eventually_card_lt` 6: necessary (same 6-ary multiplexer basis on Fin 5: every function on n = 2·5^m inputs is computable with ≤ 5^n/n gates)
theorem ecl6 : ¬ drop0% _private.Cslib.Computability.Circuit.Shannon.«0».Cslib.Circuits.Shannon.eventually_card_lt 6 := fun h => by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (@h T2c1.mS (Fin 5) _ _ _ T2c1.mI)
  have hN5 : N < 5 ^ N := Nat.lt_pow_self (by norm_num)
  have h1 := hN (N + (2 * 5 ^ N - N)) (by omega)
  have h2 := T2c1.bound N
  have hn0 : 0 < N + (2 * 5 ^ N - N) := by omega
  have huniv : computableFunctions T2c1.mI (N + (2 * 5 ^ N - N))
      (Fintype.card (Fin 5) ^ (N + (2 * 5 ^ N - N)) / (N + (2 * 5 ^ N - N))) = Finset.univ := by
    apply Finset.eq_univ_of_forall; intro f
    obtain ⟨c, hc, hs⟩ := T2c1.main N (2 * 5 ^ N - N) f
    refine mem_computableFunctions.mpr ⟨c, hc, ?_⟩
    rw [Fintype.card_fin, Nat.le_div_iff_mul_le hn0]
    exact (Nat.mul_le_mul_right _ hs).trans (by rw [mul_comm]; exact h2)
  rw [huniv] at h1
  simp at h1
