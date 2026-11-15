import Lean.Elab.Command
-- add the library modules your rows need here (e.g. `import Init`, `import Std.Sat.AIG.CNF`); avoid `import Lean`/`import Std` (1.5 GB)
import Init

/-!
Hand pass StrLem (hand22, 2026-11-08): 99 hypotheses of private theorems in
Init.Data.String.Lemmas.{Decode, Lossy, Pattern.Basic, Pattern.Find.String, Pattern.Memcmp,
Pattern.Split.Basic, Pattern.String.ForwardSearcher} (UTF-8 helper, lossy decoding, the KMP model
`ForwardSliceSearcher`: `PartialMatch`, `prefixFunction`, `IsTable`, `Invariants`).
For hypothesis `hᵢ` of theorem `T` this file proves `¬T'` (`drop0% T i`), for a dependent one
`¬∀ indep, Hᵢ` (`indep0% T i`), or, for the removable ones, `T'` (`drop% T i`) or `∀ indep, Hᵢ`
(`indep% T i`). 83 necessary, 14 removable, 2 independent (support lemmas at the end; rows in
`runs/hand22/StrLem_independent.jsonl`).

Reusable models and helpers (all built here unless noted):
- Lossy: byte arrays `b0 = ⟨#[0]⟩` (decodes to `'\x00'`), `b80 = ⟨#[0x80]⟩` (a lone continuation
  byte), `ByteArray.empty`; the private loops `skipContinuationBytes`/`fromUTF8Lossy.go` are
  well-founded, so they are evaluated through the library's own private step lemmas
  (`skip_lt`, `skip_cont`, `skip_ncont`, `go_lt`, `go_some`, `go_none`, `go_b0`, `skip_b80`).
- Decode `helper`: concrete `BitVec` splits of the first UTF-8 byte (`'a'` = 0x61, `'é'` = 0xC3 …),
  everything by `decide`; `helper_key` is the Nat argument for the removable `hl₂`.
- KMP model: notations `PM`/`PMMk`, `Inv`/`InvMk`, `IsTable`/`TabMk`, `pf`, `pfr` for the private
  structures and functions (constructors are private, so `⟨…⟩` does not work); `PartialMatch` is
  decidable (library instance), so all partial-match facts on `"a"`, `"aa"`, `"ab"`, `"é"`, … are
  `decide`; `pf_eq` computes `prefixFunction` from `prefixFunction_eq_iff` with a decidable bounded
  check; `eqn% c` (term elaborator, defined here) gives the unfolding equation of a private
  well-founded definition (`prefixFunctionRecurrence`, `buildTable.go`, `buildTable.computeDistance`)
  for `rw`; `pfr_congr` rewrites the guess argument under its dependent bound proof;
  `vsf_unique`: a valid search list determines its start position (refutes `hp`/`heq` of
  `isValidSearchFrom_toList` without evaluating the KMP iterator); `pm_valid_start`: the start of a
  full partial match of a non-empty pattern is a valid position (via `Invariants.isValidForSlice`).
- Patterns: `PA.a` (only `"a"` matches, strict), `PT.t` (everything matches, not strict), `PF.f`
  (nothing matches, strict) with `lm_a_end`, `lrm_a_start`, `not_matchesAt_f`; slices `sA`, `sB`,
  `sE`; `fss_lma_empty` copied from `checks/StrPatternHand.lean`; `sfs_nil/sfs_rej/sfs_mat` (the
  private `splitFromSteps` equations, by `rfl`).
- Independence support: `YSe` (copied from `checks/OpEHand.lean`), a forward searcher that rejects
  forever (not `Finite`).

Run with the lean4 repo's stage1 binary: runs/hand22/lean.sh checks/StrLemHand.lean.
-/

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


/-! # Decode and Lossy -/

namespace StrLemHand

/-! ## Decode -/

-- `Char.utf8Size_le_of_le`
theorem utf8Size_le_of_le_h2 : ¬ drop0% _private.Init.Data.String.Lemmas.Decode.«0».Char.utf8Size_le_of_le 2 :=
  fun h => absurd (h (c := 'é') (d := 'a')) (by decide)

-- `String.helper`
theorem helper_h4 : ¬ indep0% _private.Init.Data.String.Lemmas.Decode.«0».String.helper 4 := fun h =>
  absurd (h (c := 'a') (d := 'é') (w := 9) (w' := 1) (b := 0) (a := 0) (b' := 1) (a' := 0x43#7)
    (by decide) (by decide) 1 (by decide) (by decide) (by decide)) (by decide)

-- `String.helper`
theorem helper_h5 : ¬ indep0% _private.Init.Data.String.Lemmas.Decode.«0».String.helper 5 := fun h =>
  absurd (h (c := 'a') (d := 'a') (w := 1) (w' := 9) (b := 0) (a := 0x61#7) (b' := 256#9) (a' := 0)
    (by decide) (by decide) 1 (by decide) (by decide) (by decide)) (by decide)

-- `String.helper`
theorem helper_h10 : ¬ drop0% _private.Init.Data.String.Lemmas.Decode.«0».String.helper 10 := fun h =>
  absurd (h (c := 'a') (d := 'a') (w := 8) (w' := 8) (b := 0) (a := 0) (b' := 0x61#8) (a' := 0)
    (by decide) (by decide) (by decide) 8 (by decide) (by decide) (by decide)) (by decide)

-- `String.helper`
theorem helper_h11 : ¬ drop0% _private.Init.Data.String.Lemmas.Decode.«0».String.helper 11 := fun h =>
  absurd (h (c := 'a') (d := 'a') (w := 8) (w' := 8) (b := 0x61#8) (a := 0) (b' := 0xFF#8) (a' := 0)
    (by decide) (by decide) (by decide) 8 (by decide) (by decide) (by decide)) (by decide)

-- `String.helper`
theorem helper_h13 : ¬ drop0% _private.Init.Data.String.Lemmas.Decode.«0».String.helper 13 := fun h =>
  absurd (h (c := 'a') (d := 'a') (w := 0) (w' := 8) (b := 0) (a := 0x61#8) (b' := 0x61#8) (a' := 0)
    (by decide) (by decide) (by decide) (by decide) 2 (by decide) (by decide)) (by decide)

-- `String.helper`
theorem helper_h15 : ¬ drop0% _private.Init.Data.String.Lemmas.Decode.«0».String.helper 15 := fun h =>
  absurd (h (c := 'a') (d := 'a') (w := 8) (w' := 8) (b := 0x61#8) (a := 0) (b' := 0x61#8) (a' := 0)
    (by decide) (by decide) (by decide) (by decide) 8 (by decide) (by decide)) (by decide)

/-! ## Lossy -/

set_option quotPrecheck false in
set_option hygiene false in
local notation "skipCB" => priv% _private.Init.Data.String.Lossy.«0».String.skipContinuationBytes
set_option quotPrecheck false in
set_option hygiene false in
local notation "lossyGo" => priv% _private.Init.Data.String.Lossy.«0».String.fromUTF8Lossy.go

theorem skip_lt (b : ByteArray) (i : Nat) (h : ¬ i < b.size) : skipCB b i = i :=
  (priv% _private.Init.Data.String.Lemmas.Lossy.«0».String.skipContinuationBytes_of_not_lt) h
theorem skip_cont (b : ByteArray) (i : Nat) (h : i < b.size) (hc : b[i].isUTF8ContinuationByte = true) :
    skipCB b i = skipCB b (i + 1) :=
  (priv% _private.Init.Data.String.Lemmas.Lossy.«0».String.skipContinuationBytes_of_isUTF8ContinuationByte) h hc
theorem skip_ncont (b : ByteArray) (i : Nat) (h : i < b.size) (hc : ¬ b[i].isUTF8ContinuationByte = true) :
    skipCB b i = i :=
  (priv% _private.Init.Data.String.Lemmas.Lossy.«0».String.skipContinuationBytes_of_not_isUTF8ContinuationByte) h hc
theorem go_lt (b : ByteArray) (i : Nat) (acc : String) (h : ¬ i < b.size) : lossyGo b i acc = acc :=
  (priv% _private.Init.Data.String.Lemmas.Lossy.«0».String.fromUTF8Lossy.go_of_not_lt) h
theorem go_some (b : ByteArray) (i : Nat) (acc : String) (c : Char) (h : i < b.size)
    (hc : b.utf8DecodeChar? i = some c) : lossyGo b i acc = lossyGo b (i + c.utf8Size) (acc.push c) :=
  (priv% _private.Init.Data.String.Lemmas.Lossy.«0».String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_some) h hc
theorem go_none (b : ByteArray) (i : Nat) (acc : String) (h : i < b.size)
    (hc : b.utf8DecodeChar? i = none) : lossyGo b i acc = lossyGo b (skipCB b (i + 1)) (acc.push '�') :=
  (priv% _private.Init.Data.String.Lemmas.Lossy.«0».String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_none) h hc

abbrev b0 : ByteArray := ⟨#[0]⟩
abbrev b80 : ByteArray := ⟨#[0x80]⟩

theorem go_b0 (acc : String) : lossyGo b0 0 acc = acc.push '\x00' := by
  rw [go_some b0 0 acc '\x00' (by decide) (by decide), go_lt _ _ _ (by decide)]
theorem skip_b80 : skipCB b80 0 = 1 := by
  rw [skip_cont _ _ (by decide) (by decide), skip_lt _ _ (by decide)]

-- `String.fromUTF8Lossy.go_of_not_lt`
theorem go_of_not_lt_h3 : ¬ drop0% _private.Init.Data.String.Lemmas.Lossy.«0».String.fromUTF8Lossy.go_of_not_lt 3 :=
  fun h => absurd ((go_b0 "").symm.trans (h (b := b0) (i := 0) (acc := ""))) (by decide)

-- `String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_none`
theorem go_none_h3 : ¬ drop0% _private.Init.Data.String.Lemmas.Lossy.«0».String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_none 3 :=
  fun h => by
    have := h (b := ByteArray.empty) (i := 0) (acc := "") (by decide)
    rw [go_lt _ _ _ (by decide), skip_lt _ _ (by decide), go_lt _ _ _ (by decide)] at this
    exact absurd this (by decide)

-- `String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_none`
theorem go_none_h4 : ¬ drop0% _private.Init.Data.String.Lemmas.Lossy.«0».String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_none 4 :=
  fun h => by
    have := h (b := b0) (i := 0) (acc := "") (by decide)
    rw [go_b0, skip_lt _ _ (by decide), go_lt _ _ _ (by decide)] at this
    exact absurd this (by decide)

-- `String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_some`: `i < b.size` follows from `hc`
theorem go_some_h4 : drop% _private.Init.Data.String.Lemmas.Lossy.«0».String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_some 4 :=
  fun hc => (priv% _private.Init.Data.String.Lemmas.Lossy.«0».String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_some)
    (ByteArray.lt_size_of_isSome_utf8DecodeChar? (by simp [hc])) hc

-- `String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_some`
theorem go_some_h5 : ¬ drop0% _private.Init.Data.String.Lemmas.Lossy.«0».String.fromUTF8Lossy.go_of_utf8DecodeChar?_eq_some 5 :=
  fun h => by
    have := h (b := b0) (i := 0) (acc := "") (c := 'a') (by decide)
    rw [go_b0, go_lt _ _ _ (by decide)] at this
    exact absurd this (by decide)

-- `String.fromUTF8Lossy_of_utf8DecodeChar?_eq_none`
theorem lossy_none_h1 : ¬ drop0% _private.Init.Data.String.Lemmas.Lossy.«0».String.fromUTF8Lossy_of_utf8DecodeChar?_eq_none 1 :=
  fun h => by
    have := congrArg String.length (h (b := ByteArray.empty) (by decide))
    simp only [String.length_append, String.fromUTF8Lossy_empty, String.length_empty] at this
    rw [show (String.singleton '\ufffd').length = 1 from by decide] at this
    omega

-- `String.skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte`
theorem skip_forall_h3 : ¬ drop0% _private.Init.Data.String.Lemmas.Lossy.«0».String.skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte 3 :=
  fun h => absurd ((skip_lt ByteArray.empty 1 (by decide)).symm.trans (h (b := ByteArray.empty) (i := 1) (j := 0) (by decide)
    (fun k hk => absurd hk (by simp)) (fun hj => absurd hj (by decide)))) (by decide)

-- `String.skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte`
theorem skip_forall_h4 : ¬ drop0% _private.Init.Data.String.Lemmas.Lossy.«0».String.skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte 4 :=
  fun h => absurd ((skip_lt ByteArray.empty 0 (by decide)).symm.trans (h (b := ByteArray.empty) (i := 0) (j := 1) (by decide)
    (fun k hk => absurd hk (by simp)) (fun hj => absurd hj (by decide)))) (by decide)

-- `String.skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte`
theorem skip_forall_h5 : ¬ drop0% _private.Init.Data.String.Lemmas.Lossy.«0».String.skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte 5 :=
  fun h => absurd ((skip_ncont b0 0 (by decide) (by decide)).symm.trans (h (b := b0) (i := 0) (j := 1) (by decide)
    (by decide) (fun hj => absurd hj (by decide)))) (by decide)

-- `String.skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte`
theorem skip_forall_h6 : ¬ drop0% _private.Init.Data.String.Lemmas.Lossy.«0».String.skipContinuationBytes_eq_of_forall_isUTF8ContinuationByte 6 :=
  fun h => absurd (skip_b80.symm.trans (h (b := b80) (i := 0) (j := 0) (by decide) (by decide)
    (fun k hk h1 h2 => absurd h2 (by omega)))) (by decide)

-- `String.skipContinuationBytes_le_size`
theorem skip_le_size_h2 : ¬ drop0% _private.Init.Data.String.Lemmas.Lossy.«0».String.skipContinuationBytes_le_size 2 :=
  fun h => absurd (h (b := ByteArray.empty) (i := 1)) (by rw [skip_lt _ _ (by decide)]; decide)

-- `String.skipContinuationBytes_of_isUTF8ContinuationByte`
theorem skip_cont_h3 : ¬ drop0% _private.Init.Data.String.Lemmas.Lossy.«0».String.skipContinuationBytes_of_isUTF8ContinuationByte 3 :=
  fun h => absurd (h (b := b0) (i := 0) (by decide))
    (by rw [skip_ncont _ _ (by decide) (by decide), skip_lt _ _ (by decide)]; decide)

-- `String.skipContinuationBytes_of_not_isUTF8ContinuationByte`
theorem skip_ncont_h3 : ¬ drop0% _private.Init.Data.String.Lemmas.Lossy.«0».String.skipContinuationBytes_of_not_isUTF8ContinuationByte 3 :=
  fun h => absurd (h (b := b80) (i := 0) (by decide)) (by rw [skip_b80]; decide)

-- `String.skipContinuationBytes_of_not_lt`
theorem skip_not_lt_h2 : ¬ drop0% _private.Init.Data.String.Lemmas.Lossy.«0».String.skipContinuationBytes_of_not_lt 2 :=
  fun h => absurd (h (b := b80) (i := 0)) (by rw [skip_b80]; decide)

end StrLemHand

namespace StrLemHand
open String String.Slice.Pattern String.Slice.Pattern.Model

/-- Nat core of the `hl₂` argument: with `w' < len ≤ w`, comparing the top `len` bits of `x` with
`y` (zero-extended) already decides the comparison of the top `w'` bits. -/
theorem helper_key (w w' len x y : Nat) (h1 : len ≤ w) (h2 : w' < len) (hx : x < 2 ^ w)
    (hy : y < 2 ^ w') (h : (x >>> (w - len)) % 2 ^ len < (y >>> (w' - len)) % 2 ^ len) :
    (x >>> (w - w')) % 2 ^ w' < (y >>> (w' - w')) % 2 ^ w' := by
  have hyl : y < 2 ^ len := Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega))
  rw [show w' - len = 0 by omega, Nat.shiftRight_zero, Nat.mod_eq_of_lt hyl] at h
  rw [Nat.sub_self, Nat.shiftRight_zero, Nat.mod_eq_of_lt hy]
  rw [Nat.shiftRight_eq_div_pow] at h ⊢
  have hxl : x / 2 ^ (w - len) < 2 ^ len := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show len + (w - len) = w by omega]
    exact hx
  rw [Nat.mod_eq_of_lt hxl] at h
  calc x / 2 ^ (w - w') % 2 ^ w' ≤ x / 2 ^ (w - w') := Nat.mod_le _ _
    _ ≤ x / 2 ^ (w - len) := Nat.div_le_div_left (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.two_pow_pos _)
    _ < y := h

-- `String.helper`: removable; if `len > w'` the comparison `hlt` of the top `len` bits (the right
-- side is `b'` zero-extended) implies the comparison of the top `w'` bits, so the library lemma
-- applies with `len := w'`
theorem helper_h14 : drop% _private.Init.Data.String.Lemmas.Decode.«0».String.helper 14 := by
  intro c d w w' hw hw' b a b' a' h₁ h₂ len hl₁ hlt
  by_cases hl₂ : len ≤ w'
  · exact (priv% _private.Init.Data.String.Lemmas.Decode.«0».String.helper) hw hw' h₁ h₂ len hl₁ hl₂ hlt
  · refine (priv% _private.Init.Data.String.Lemmas.Decode.«0».String.helper) hw hw' h₁ h₂ w' (by omega)
      (Nat.le_refl _) ?_
    simp only [autoParam, BitVec.lt_def, BitVec.extractLsb'_toNat] at hlt ⊢
    exact helper_key w w' len b.toNat b'.toNat hl₁ (by omega) b.isLt b'.isLt hlt

end StrLemHand

/-! # Pattern lemmas: Basic, Find.String, Memcmp, Split.Basic -/

set_option linter.deprecated false

namespace StrLemHand
open String String.Slice.Pattern String.Slice.Pattern.Model
open String (Slice)

/-! ## Pattern models -/

/-- `PA.a`: only `"a"` matches (strict); `PT.t`: every string matches (not strict); `PF.f`: nothing
matches (strict). -/
inductive PA | a
inductive PT | t
inductive PF | f
instance : PatternModel PA.a := ⟨fun t => t = "a"⟩
instance : StrictPatternModel PA.a := ⟨fun (h : ("" : String) = "a") => absurd h (by decide)⟩
instance : PatternModel PT.t := ⟨fun _ => True⟩
instance : PatternModel PF.f := ⟨fun _ => False⟩
instance : StrictPatternModel PF.f := ⟨id⟩

abbrev sA : Slice := "a".toSlice
abbrev sB : Slice := "b".toSlice
abbrev sE : Slice := "".toSlice

theorem not_matchesAt_f {s : Slice} {p : s.Pos} : ¬ MatchesAt PF.f p :=
  fun ⟨⟨_, h⟩⟩ => h.isLongestMatch_sliceFrom.isMatch.matches_copy

theorem lm_a_end : IsLongestMatch PA.a sA.endPos :=
  ⟨⟨show (sA.sliceTo sA.endPos).copy = "a" by decide⟩,
    fun p hp => absurd (Slice.Pos.le_endPos p) (Std.not_le.2 hp)⟩
theorem not_lm_b_end : ¬ IsLongestMatch PA.a sB.endPos :=
  fun h => absurd h.isMatch.matches_copy (show ¬ (sB.sliceTo sB.endPos).copy = "a" by decide)
theorem not_lm_a_start : ¬ IsLongestMatch PA.a sA.startPos :=
  fun h => absurd h.isMatch.matches_copy (show ¬ (sA.sliceTo sA.startPos).copy = "a" by decide)

theorem lrm_a_start : IsLongestRevMatch PA.a sA.startPos :=
  ⟨⟨show (sA.sliceFrom sA.startPos).copy = "a" by decide⟩,
    fun p hp => absurd (Slice.Pos.startPos_le p) (Std.not_le.2 hp)⟩
theorem not_lrm_b_start : ¬ IsLongestRevMatch PA.a sB.startPos :=
  fun h => absurd h.isRevMatch.matches_copy (show ¬ (sB.sliceFrom sB.startPos).copy = "a" by decide)
theorem not_lrm_a_end : ¬ IsLongestRevMatch PA.a sA.endPos :=
  fun h => absurd h.isRevMatch.matches_copy (show ¬ (sA.sliceFrom sA.endPos).copy = "a" by decide)

/-! ## `Init.Data.String.Lemmas.Pattern.Basic` -/

-- `String.Slice.Pattern.Model.isLongestMatch_of_eq`
theorem lm_of_eq_h7 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.Basic.«0».String.Slice.Pattern.Model.isLongestMatch_of_eq 7 :=
  fun h => not_lm_b_end (h (pat := PA.a) (s := sA) (t := sB) (pos := sA.endPos) (pos' := sB.endPos) (by decide) lm_a_end)

-- `String.Slice.Pattern.Model.isLongestMatch_of_eq`
theorem lm_of_eq_h8 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.Basic.«0».String.Slice.Pattern.Model.isLongestMatch_of_eq 8 :=
  fun h => not_lm_a_start (h (pat := PA.a) (s := sA) (t := sA) (pos := sA.endPos) (pos' := sA.startPos) rfl lm_a_end)

-- `String.Slice.Pattern.Model.isLongestMatch_of_eq`
theorem lm_of_eq_h9 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.Basic.«0».String.Slice.Pattern.Model.isLongestMatch_of_eq 9 :=
  fun h => not_lm_a_start (h (pat := PA.a) (s := sA) (t := sA) (pos := sA.startPos) (pos' := sA.startPos) rfl rfl)

-- `String.Slice.Pattern.Model.isLongestRevMatch_of_eq`
theorem lrm_of_eq_h7 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.Basic.«0».String.Slice.Pattern.Model.isLongestRevMatch_of_eq 7 :=
  fun h => not_lrm_b_start (h (pat := PA.a) (s := sA) (t := sB) (pos := sA.startPos) (pos' := sB.startPos) (by decide) lrm_a_start)

-- `String.Slice.Pattern.Model.isLongestRevMatch_of_eq`
theorem lrm_of_eq_h8 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.Basic.«0».String.Slice.Pattern.Model.isLongestRevMatch_of_eq 8 :=
  fun h => not_lrm_a_end (h (pat := PA.a) (s := sA) (t := sA) (pos := sA.startPos) (pos' := sA.endPos) rfl lrm_a_start)

-- `String.Slice.Pattern.Model.isLongestRevMatch_of_eq`
theorem lrm_of_eq_h9 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.Basic.«0».String.Slice.Pattern.Model.isLongestRevMatch_of_eq 9 :=
  fun h => not_lrm_a_end (h (pat := PA.a) (s := sA) (t := sA) (pos := sA.endPos) (pos' := sA.endPos) rfl rfl)

/-! ## `Init.Data.String.Lemmas.Pattern.Find.String`, `…Pattern.Memcmp` -/

-- `String.Slice.contains_eq_true_of_isEmpty`
theorem contains_isEmpty_h1 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.Find.String.«0».String.Slice.contains_eq_true_of_isEmpty 1 :=
  fun h => by
    have := String.Slice.contains_slice_iff.1 (h (pat := sA) sB)
    revert this; decide

-- `String.Slice.contains_string_eq_true_of_empty`
theorem contains_empty_h1 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.Find.String.«0».String.Slice.contains_string_eq_true_of_empty 1 :=
  fun h => by
    have := String.Slice.contains_string_iff.1 (h (pat := "a") sB)
    revert this; decide

-- `String.Slice.Pattern.Internal.extract_offsetBy_eq_extract_copy`
theorem extract_offsetBy_h3 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.Memcmp.«0».String.Slice.Pattern.Internal.extract_offsetBy_eq_extract_copy 3 :=
  fun h => absurd (h (s := "ab".toSlice.sliceTo ("ab".toSlice.pos ⟨1⟩ (by decide))) (p := ⟨0⟩) (len := 2)) (by decide)

/-! ## `Init.Data.String.Lemmas.Pattern.Split.Basic` -/

set_option quotPrecheck false in
set_option hygiene false in
notation "sfs" => priv% _private.Init.Data.String.Lemmas.Pattern.Split.Basic.«0».String.Slice.Pattern.Model.splitFromSteps

theorem sfs_nil {s : Slice} (pos : s.Pos) : sfs pos [] = [s.subsliceFrom pos] := rfl
theorem sfs_rej {s : Slice} (pos a b : s.Pos) (l : List (SearchStep s)) :
    sfs pos (.rejected a b :: l) = sfs pos l := rfl
theorem sfs_mat {s : Slice} (pos a b : s.Pos) (l : List (SearchStep s)) :
    sfs pos (.matched a b :: l) = s.subslice! pos a :: sfs b l := rfl

-- `String.Slice.Pattern.Model.IsValidSearchFrom.splitFromSteps_eq_extend_split`
theorem sfs_split_h4 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.Split.Basic.«0».String.Slice.Pattern.Model.IsValidSearchFrom.splitFromSteps_eq_extend_split 4 :=
  fun h => (h (s := sE) PT.t [] sE.startPos sE.startPos (Std.le_refl _)
    (fun p h₁ h₂ => absurd (Std.lt_of_lt_of_le h₂ h₁) Std.lt_irrefl)
    (IsValidSearchFrom.endPos_of_eq (by decide) rfl)).not_matches_empty trivial

-- `String.Slice.Pattern.Model.IsValidSearchFrom.splitFromSteps_eq_extend_split`
theorem sfs_split_h8 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.Split.Basic.«0».String.Slice.Pattern.Model.IsValidSearchFrom.splitFromSteps_eq_extend_split 8 :=
  fun h => absurd (h (s := sA) PF.f [.rejected sA.startPos sA.endPos] sA.endPos sA.startPos
    (fun p h₁ h₂ => absurd (Slice.Pos.startPos_le p) (Std.not_le.2 h₂))
    (.mismatched (by decide) (fun _ _ _ => not_matchesAt_f) .endPos)) (by decide)

-- `String.Slice.Pattern.Model.IsValidSearchFrom.splitFromSteps_eq_extend_split`: removable; `h'` only
-- feeds the induction hypothesis, and `Model.split` from `pos'` does not look at `[pos, pos')`
-- (the library proof without `h'`)
theorem sfs_split_h9 : drop% _private.Init.Data.String.Lemmas.Pattern.Split.Basic.«0».String.Slice.Pattern.Model.IsValidSearchFrom.splitFromSteps_eq_extend_split 9 := by
  intro s ρ pat _ _ l pos pos' h₀ h
  induction h generalizing pos with
  | endPos => rw [sfs_nil]; simp
  | matched hm valid ih =>
    rw [sfs_mat, Slice.subslice!_eq_subslice h₀, split_eq_of_isLongestMatchAt hm, ih _ (Std.le_refl _)]
  | mismatched hlt rej valid ih =>
    rw [sfs_rej, split_eq_of_not_matchesAt _ (Std.le_of_lt hlt) rej, ih]

-- `String.Slice.Pattern.Model.IsValidSearchFrom.splitFromSteps_eq_extend_split`
theorem sfs_split_h10 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.Split.Basic.«0».String.Slice.Pattern.Model.IsValidSearchFrom.splitFromSteps_eq_extend_split 10 :=
  fun h => by
    have := congrArg List.length (h (s := sA) PF.f [.matched sA.startPos sA.endPos] sA.startPos sA.startPos
      (Std.le_refl _) (fun p h₁ h₂ => absurd (Std.lt_of_lt_of_le h₂ h₁) Std.lt_irrefl))
    rw [split_eq_of_not_matchesAt sA.endPos (by decide) (fun _ _ _ => not_matchesAt_f), split_endPos] at this
    exact absurd this (by decide)

end StrLemHand

/-! # KMP model (Pattern.String.ForwardSearcher) -/

open Lean Meta in
/-- `eqn% c`: the unfolding equation `c.eq_def` of a (possibly private) definition `c`. -/
elab "eqn% " c:ident : term => do
  let n ← hcConst c
  let some eq ← getUnfoldEqnFor? n (nonRec := true) | throwError "no unfold equation for {n}"
  mkConstWithFreshMVarLevels eq

set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option quotPrecheck false
set_option hygiene false
notation "PM" => priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch
notation "PMMk" => priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.mk
notation "Inv" => priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants
notation "InvMk" => priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.mk
notation "IsTable" => priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable
notation "TabMk" => priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.mk
notation "pf" => priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction
notation "pfr" => priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence
set_option hygiene true
set_option quotPrecheck true

namespace StrLemHand
open String String.Slice.Pattern String.Slice.Pattern.Model
open String (Slice)

/-! ## KMP model: evaluation helpers -/

theorem pf_eq {pat : ByteArray} {i : Nat} {hi : i < pat.size} {k : Nat} (h1 : k ≤ i)
    (h2 : PM pat pat k (i + 1)) (h3 : ∀ j, j < i - k → ¬ PM pat pat (k + 1 + j) (i + 1)) :
    pf pat i hi = k :=
  (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_eq_iff).2 ⟨h1, h2, fun k' hk hk' => by
    have := h3 (k' - k - 1) (by omega)
    rwa [show k + 1 + (k' - k - 1) = k' by omega] at this⟩

theorem pfr_congr {pat : ByteArray} {st : Nat} {hst : st < pat.size} {g g' : Nat} (e : g = g')
    {hg : g < st} (hg' : g' < st) : pfr pat st hst g hg = pfr pat st hst g' hg' := by
  subst e; rfl

theorem pf_zero {pat : ByteArray} {hi : 0 < pat.size} : pf pat 0 hi = 0 :=
  (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_zero) (b := pat) (hi := hi)

theorem pm_zero {pat s : ByteArray} {stackPos : Nat} (h : stackPos ≤ s.size) : PM pat s 0 stackPos :=
  (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.partialMatch_zero) h

theorem inv_pm {pat s : Slice} {n t : Pos.Raw} (h : Inv pat s n t) :
    PM pat.copy.toByteArray s.copy.toByteArray n.byteIdx t.byteIdx :=
  (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.partialMatch) h

theorem table_le {b : ByteArray} {v : Array Nat} (h : IsTable b v) : v.size ≤ b.size :=
  (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.size_le) h

theorem table_get_le {b : ByteArray} {v : Array Nat} (h : IsTable b v) (i : Nat) (hi : i < v.size) :
    v[i] ≤ i := by
  rw [(priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.eq_prefixFunction) h i hi]
  exact (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le) (pat := b)

theorem table_get {b : ByteArray} {v : Array Nat} (h : IsTable b v) (i : Nat) (hi : i < v.size) :
    v[i] = pf b i (Nat.lt_of_lt_of_le hi (table_le h)) :=
  (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.eq_prefixFunction) h i hi

theorem matchesAt_of_pm {pat s : Slice} (hpat : pat.isEmpty = false) {pos : s.Pos}
    (h : PM pat.copy.toByteArray s.copy.toByteArray pat.copy.toByteArray.size
      (pos.offset.byteIdx + pat.copy.toByteArray.size)) : MatchesAt pat pos :=
  ((priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.matchesAt_iff_partialMatch) hpat).2 h

/-- Positions in a valid search list are determined by the list. -/
theorem vsf_unique {ρ : Type} {pat : ρ} [PatternModel pat] {s : Slice} {p q : s.Pos}
    {l : List (SearchStep s)} (h₁ : IsValidSearchFrom pat p l) (h₂ : IsValidSearchFrom pat q l) :
    p = q := by
  cases h₁ <;> cases h₂ <;> rfl

/-! ## KMP model (`Init.Data.String.Lemmas.Pattern.String.ForwardSearcher`) -/

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.base_start`
theorem base_start_h2 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.base_start 2 :=
  fun h => absurd (h (pat := "".toSlice) (s := "".toSlice)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.inc`
theorem inc_h4 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.inc 4 := fun h =>
  absurd (inv_pm (h (pat := "aa".toSlice) (s := "a".toSlice) (needlePos := ⟨1⟩) (stackPos := ⟨0⟩)
    (by decide) (by decide) (by decide))) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.inc`
theorem inc_h5 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.inc 5 := fun h =>
  absurd (h (pat := "a".toSlice) (s := "aa".toSlice) (stackPos := ⟨1⟩) (needlePos := ⟨1⟩) (InvMk (by decide) (by decide) (fun e => absurd e (by decide)))
    (by decide)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.inc`
theorem inc_h6 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.inc 6 := fun h =>
  absurd (h (pat := "aa".toSlice) (s := "a".toSlice) (stackPos := ⟨1⟩) (needlePos := ⟨1⟩) (InvMk (by decide) (by decide) (fun e => absurd e (by decide)))
    (by decide)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.inc`
theorem inc_h7 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.inc 7 := fun h =>
  absurd (inv_pm (h (pat := "a".toSlice) (s := "b".toSlice) (needlePos := ⟨0⟩) (stackPos := ⟨0⟩)
    (InvMk (by decide) (by decide) (fun _ => by decide)) (by decide) (by decide))) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isEmpty_eq_false`
theorem isEmpty_eq_false_h4 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isEmpty_eq_false 4 := fun h =>
  absurd (h (pat := "".toSlice) (s := "".toSlice) (needlePos := ⟨0⟩) (stackPos := ⟨0⟩)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isLongestMatchAt`
theorem isLongestMatchAt_h4 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isLongestMatchAt 4 := fun h =>
  absurd ((priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isEmpty_eq_false) (h (pat := "".toSlice) (s := "".toSlice) (stackPos := ⟨0⟩) (needlePos := ⟨0⟩) (by decide))) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isLongestMatchAt`
theorem isLongestMatchAt_h5 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isLongestMatchAt 5 := fun h =>
  absurd (h (pat := "a".toSlice) (s := "a".toSlice) (stackPos := ⟨0⟩) (needlePos := ⟨0⟩) (InvMk (by decide) (by decide) (fun _ => by decide))) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidForSlice`
theorem isValidForSlice_h4 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidForSlice 4 := fun h =>
  absurd (h (pat := "a".toSlice) (s := "é".toSlice) (needlePos := ⟨0⟩) (stackPos := ⟨1⟩)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidForSlice'`
theorem isValidForSlice'_h4 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidForSlice' 4 := fun h =>
  absurd (h (pat := "a".toSlice) (s := "".toSlice) (needlePos := ⟨0⟩) (stackPos := ⟨1⟩) rfl) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidForSlice'`
theorem isValidForSlice'_h5 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidForSlice' 5 := fun h =>
  absurd (h (pat := "é".toSlice) (s := "é".toSlice) (needlePos := ⟨1⟩) (stackPos := ⟨1⟩)
    (InvMk (by decide) (by decide) (fun e => absurd e (by decide)))) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.offset`
theorem offset_h3 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.offset 3 := fun h =>
  absurd ((priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isEmpty_eq_false) (h (pat := "".toSlice) (s := "".toSlice) (pos := "".toSlice.startPos)))
    (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.partialMatch`
theorem partialMatch_h4 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.partialMatch 4 := fun h =>
  absurd (h (pat := "a".toSlice) (s := "".toSlice) (needlePos := ⟨1⟩) (stackPos := ⟨0⟩)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.start`
theorem start_h2 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.start 2 := fun h =>
  absurd ((priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isEmpty_eq_false) (h "".toSlice "".toSlice)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.zero_of_eq`
theorem zero_of_eq_h4 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.zero_of_eq 4 := fun h =>
  absurd ((priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isEmpty_eq_false) (h (pat := "".toSlice) (s := "".toSlice) (needlePos := ⟨0⟩)
    (stackPos := ⟨0⟩) (by decide))) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.zero_of_eq`
theorem zero_of_eq_h5 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.zero_of_eq 5 := fun h =>
  absurd ((priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidForSlice') (h (pat := "é".toSlice) (s := "é".toSlice) (needlePos := ⟨1⟩)
    (stackPos := ⟨1⟩) (InvMk (by decide) (by decide) (fun e => absurd e (by decide)))) rfl) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.of_prefixFunction_eq`
theorem of_pf_h4 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.of_prefixFunction_eq 4 := fun h =>
  absurd (inv_pm (h (pat := "aa".toSlice) (s := "".toSlice) (needlePos := ⟨2⟩) (stackPos := ⟨0⟩) (by decide)
    (k := 1) (hki := by decide) (pf_eq (by decide) (by decide) (by decide)) (by decide))) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.of_prefixFunction_eq`: `hki` follows from
-- the partial match (needle position at most the pattern size) and `needlePos ≠ 0`
theorem of_pf_h7 : indep% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.of_prefixFunction_eq 7 := by
  intro pat s stackPos needlePos h h' k hk₀
  have := (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.needlePos_le_size) (inv_pm h)
  simp only [ne_eq, Pos.Raw.ext_iff, Pos.Raw.byteIdx_zero] at h'
  omega

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.of_prefixFunction_eq`
theorem of_pf_h8 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.of_prefixFunction_eq 8 := fun h =>
  absurd (inv_pm (h (pat := "a".toSlice) (s := "a".toSlice) (needlePos := ⟨1⟩) (stackPos := ⟨1⟩)
    (InvMk (by decide) (by decide) (fun e => absurd e (by decide))) (by decide)
    (k := 5) (hki := by decide) (by decide))) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.of_prefixFunction_eq`
theorem of_pf_h9 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.of_prefixFunction_eq 9 := fun h =>
  absurd ((priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidForSlice') (h (pat := "é".toSlice) (s := "é".toSlice) (needlePos := ⟨1⟩)
    (stackPos := ⟨1⟩) (InvMk (by decide) (by decide) (fun e => absurd e (by decide))) (by decide)
    (k := 0) (hki := by decide) pf_zero) rfl) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq`
theorem not_matchesAt_h4 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq 4 := fun h =>
  h (pat := "abc".toSlice) (s := "xabc".toSlice) (stackPos := ⟨2⟩) (needlePos := ⟨2⟩) (k := 0) (hki := by decide)
    (pf_eq (by decide) (by decide) (by decide)) ("xabc".toSlice.pos ⟨1⟩ (by decide)) (by decide) (by decide)
    (h₁ := by decide) (h₂ := by decide) (by decide) (matchesAt_of_pm (by decide) (by decide))

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq`: `hki`
-- follows from `h₂ : needlePos < pat.rawEndPos`
theorem not_matchesAt_h6 : indep% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq 6 := by
  intro pat s stackPos needlePos h k p hp₁ hp₂ h₁ h₂ hmism
  simp only [Pos.Raw.lt_iff, Slice.byteIdx_rawEndPos] at h₂
  simp only [size_toByteArray, Slice.utf8ByteSize_copy]
  omega

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq`
theorem not_matchesAt_h7 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq 7 := fun h =>
  h (pat := "aab".toSlice) (s := "aaab".toSlice) (stackPos := ⟨2⟩) (needlePos := ⟨2⟩)
    (InvMk (by decide) (by decide) (fun e => absurd e (by decide))) (k := 0) (hki := by decide)
    ("aaab".toSlice.pos ⟨1⟩ (by decide)) (by decide) (by decide)
    (h₁ := by decide) (h₂ := by decide) (by decide) (matchesAt_of_pm (by decide) (by decide))

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq`
theorem not_matchesAt_h9 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq 9 := fun h =>
  h (pat := "a".toSlice) (s := "ab".toSlice) (stackPos := ⟨1⟩) (needlePos := ⟨0⟩)
    (InvMk (by decide) (by decide) (fun _ => by decide)) (k := 0) (hki := by decide) pf_zero
    "ab".toSlice.startPos (by decide)
    (h₁ := by decide) (h₂ := by decide) (by decide) (matchesAt_of_pm (by decide) (by decide))

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq`
theorem not_matchesAt_h10 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq 10 := fun h =>
  h (pat := "a".toSlice) (s := "ba".toSlice) (stackPos := ⟨0⟩) (needlePos := ⟨0⟩)
    (InvMk (by decide) (by decide) (fun _ => by decide)) (k := 0) (hki := by decide) pf_zero
    ("ba".toSlice.pos ⟨1⟩ (by decide)) (by decide)
    (h₁ := by decide) (h₂ := by decide) (by decide) (matchesAt_of_pm (by decide) (by decide))

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq`
theorem not_matchesAt_h11 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq 11 := fun h =>
  absurd (h (pat := "ab".toSlice) (s := "a".toSlice) (stackPos := ⟨1⟩) (needlePos := ⟨1⟩) (InvMk (by decide) (by decide) (fun e => absurd e (by decide)))
    (k := 0) (hki := by decide) pf_zero "a".toSlice.startPos (by decide) (by decide) (h₂ := by decide)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq`
theorem not_matchesAt_h12 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq 12 := fun h =>
  absurd (h (pat := "a".toSlice) (s := "ab".toSlice) (stackPos := ⟨1⟩) (needlePos := ⟨1⟩) (InvMk (by decide) (by decide) (fun e => absurd e (by decide)))
    (k := 0) (hki := by decide) pf_zero "ab".toSlice.startPos (by decide) (by decide) (h₁ := by decide)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq`
theorem not_matchesAt_h13 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.not_matchesAt_of_prefixFunction_eq 13 := fun h =>
  h (pat := "aa".toSlice) (s := "aa".toSlice) (stackPos := ⟨1⟩) (needlePos := ⟨1⟩)
    (InvMk (by decide) (by decide) (fun e => absurd e (by decide))) (k := 0) (hki := by decide) pf_zero
    "aa".toSlice.startPos (by decide) (by decide)
    (h₁ := by decide) (h₂ := by decide) (matchesAt_of_pm (by decide) (by decide))

/-! ### Prefix tables -/

theorem table_empty : IsTable ByteArray.empty #[] := (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.isTable_empty)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.eq_prefixFunction`
theorem eq_pf_h2 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.eq_prefixFunction 2 := fun h =>
  absurd (table_le (h (b := ByteArray.empty) (v := #[0]) 0 (by decide))) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.eq_prefixFunction`
theorem eq_pf_h4 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.eq_prefixFunction 4 := fun h =>
  absurd (h (b := ByteArray.empty) (v := #[]) table_empty 0) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.push`
theorem push_h2 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.push 2 := fun h => by
  have := table_get (h (b := ⟨#[0, 0]⟩) (v := #[5]) (d := pf ⟨#[0, 0]⟩ 1 (by decide)) (by decide) rfl) 0 (by decide)
  rw [pf_zero] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.push`
theorem push_h4 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.push 4 := fun h =>
  absurd (h (b := ByteArray.empty) (v := #[]) table_empty (d := 0)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.push`
theorem push_h5 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.push 5 := fun h => by
  have := table_get (h (b := ⟨#[0]⟩) (v := #[]) (TabMk (by decide) (fun i hi => absurd hi (by simp)))
    (d := 5) (by decide)) 0 (by decide)
  rw [pf_zero] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.isTable_singleton`
theorem isTable_singleton_h1 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.isTable_singleton 1 := fun h =>
  absurd (table_le (h (b := ByteArray.empty))) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.getElem_buildTable`
theorem getElem_buildTable_h2 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.getElem_buildTable 2 := fun h =>
  absurd (h (pat := "".toSlice) (i := 0)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.le_prefixFunction`
theorem le_pf_h5 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.le_prefixFunction 5 := fun h => by
  have := h (pat := ⟨#[0]⟩) (stackPos := 1) (needlePos := 1) (by decide) (by decide)
  rw [pf_zero] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.partialMatch_of_le`: if
-- `stackPos - newStackPos > needlePos` the new needle position truncates to `0`, and the empty
-- partial match holds whenever `newStackPos ≤ s.size`
theorem partialMatch_of_le_h7 : drop% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.partialMatch_of_le 7 := by
  intro pat s stackPos needlePos h newStackPos h'
  by_cases h'' : stackPos - newStackPos ≤ needlePos
  · exact (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.partialMatch_of_le) h newStackPos h' h''
  · rw [show needlePos - (stackPos - newStackPos) = 0 by omega]
    exact pm_zero (Nat.le_trans h' ((priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.stackPos_le_size) h))

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence_eq_prefixFunction`
theorem pfr_eq_h5 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence_eq_prefixFunction 5 := fun h => by
  have := h (pat := ⟨#[0, 0, 0]⟩) (stackPos := 2) (hst := by decide) (guess := 0) (hg := by decide) (by decide)
  rw [eqn% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence, if_pos (by decide),
    pf_eq (k := 2) (by decide) (by decide) (by decide)] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence_eq_prefixFunction`
theorem pfr_eq_h6 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence_eq_prefixFunction 6 := fun h => by
  have e : pf ⟨#[0, 1, 1]⟩ 2 (by decide) = 0 := pf_eq (by decide) (by decide) (by decide)
  have := h (pat := ⟨#[0, 1, 1]⟩) (stackPos := 2) (hst := by decide) (guess := 1) (hg := by decide)
    (by rw [e]; decide)
  rw [eqn% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence, if_pos (by decide), e] at this
  exact absurd this (by decide)

/-! ### `buildTable` -/

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.isTable_buildTableGo`
theorem buildTableGo_h2 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.isTable_buildTableGo 2 := fun h =>
  absurd (h (pat := "".toSlice) (table := #[]) (ht := by decide) (h := by decide)
    (TabMk (by decide) (fun i hi => absurd hi (by simp)))) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.isTable_buildTableGo`: `ht` follows from `ht'`
-- (`IsTable.size_le`)
theorem buildTableGo_h3 : indep% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.isTable_buildTableGo 3 := by
  intro pat table ht₀ h ht'
  simpa using table_le ht'

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.isTable_buildTableGo`: `h` follows from `ht'`
-- (table entries are prefix-function values, `prefixFunction_le`)
theorem buildTableGo_h4 : indep% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.isTable_buildTableGo 4 := by
  intro pat table ht₀ ht ht'
  exact table_get_le ht'

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.isTable_buildTableGo`
theorem buildTableGo_h5 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.isTable_buildTableGo 5 := fun h => by
  have H := h (pat := "aa".toSlice) (table := #[0, 0]) (ht₀ := by decide) (ht := by decide) (h := by decide)
  rw [eqn% _private.Init.Data.String.Pattern.String.«0».String.Slice.Pattern.ForwardSliceSearcher.buildTable.go, dif_neg (by decide)] at H
  have := table_get H 1 (by decide)
  rw [pf_eq (k := 1) (by decide) (by decide) (by decide)] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.computeDistance_eq_prefixFunctionRecurrence`
theorem cd_h2 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.computeDistance_eq_prefixFunctionRecurrence 2 := fun h =>
  absurd (h (s := "a".toSlice) 5 (patByte := 0) #[0] (ht := by decide)
    ((priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.isTable_singleton) (by decide)) (h := by decide) (guess := 0) (hg := by decide)
    (hg' := by decide)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.computeDistance_eq_prefixFunctionRecurrence`
theorem cd_h4 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.computeDistance_eq_prefixFunctionRecurrence 4 := fun h => by
  have := h (s := "ab".toSlice) 1 (by decide) (patByte := 0x61) #[0] (ht := by decide)
    ((priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.isTable_singleton) (by decide)) (h := by decide) (guess := 0) (hg := by decide)
    (hg' := by decide)
  rw [eqn% _private.Init.Data.String.Pattern.String.«0».String.Slice.Pattern.ForwardSliceSearcher.buildTable.computeDistance, if_pos (by decide), eqn% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence, if_neg (by decide),
    dif_pos rfl] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.computeDistance_eq_prefixFunctionRecurrence`: `ht`
-- follows from `ht'` (`IsTable.size_le`)
theorem cd_h6 : indep% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.computeDistance_eq_prefixFunctionRecurrence 6 := by
  intro s i hi patByte hpat table ht' h guess hg hg'
  simpa using table_le ht'

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.computeDistance_eq_prefixFunctionRecurrence`
theorem cd_h7 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.computeDistance_eq_prefixFunctionRecurrence 7 := fun h => by
  have := h (s := "abcb".toSlice) 3 (by decide) (patByte := 0x62) (by decide) #[0, 1, 0] (ht := by decide)
    (h := by decide) (guess := 2) (hg := by decide) (hg' := by decide)
  have e : pf "abcb".toSlice.copy.toByteArray 1 (by decide) = 0 := pf_eq (by decide) (by decide) (by decide)
  rw [eqn% _private.Init.Data.String.Pattern.String.«0».String.Slice.Pattern.ForwardSliceSearcher.buildTable.computeDistance, if_neg (by decide), dif_neg (by decide), eqn% _private.Init.Data.String.Pattern.String.«0».String.Slice.Pattern.ForwardSliceSearcher.buildTable.computeDistance,
    if_pos (by decide), eqn% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence, if_neg (by decide), dif_neg (by decide)] at this
  rw [pfr_congr e (by decide)] at this
  rw [eqn% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence, if_neg (by decide), dif_pos rfl] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.computeDistance_eq_prefixFunctionRecurrence`: `h`
-- follows from `ht'` (table entries are prefix-function values)
theorem cd_h8 : indep% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.computeDistance_eq_prefixFunctionRecurrence 8 := by
  intro s i hi patByte hpat table ht ht' guess hg hg'
  exact table_get_le ht'

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.computeDistance_eq_prefixFunctionRecurrence`
theorem cd_h10 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.computeDistance_eq_prefixFunctionRecurrence 10 := fun h =>
  absurd (h (s := "aa".toSlice) 0 (by decide) (patByte := 0x61) (by decide) #[0, 1] (ht := by decide)
    (TabMk (by decide) (fun i hi => by
      match i, hi with
      | 0, _ => exact pf_zero.symm
      | 1, _ => exact (pf_eq (k := 1) (by decide) (by decide) (by decide)).symm))
    (h := by decide) (guess := 1) (hg' := by decide)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.computeDistance_eq_prefixFunctionRecurrence`
theorem cd_h11 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.computeDistance_eq_prefixFunctionRecurrence 11 := fun h =>
  absurd (h (s := "aa".toSlice) 1 (by decide) (patByte := 0x61) (by decide) #[] (ht := by decide)
    (TabMk (by decide) (fun i hi => absurd hi (by simp))) (h := fun i hi => absurd hi (by simp))
    (guess := 0) (hg := by decide)) (by decide)

/-! ### Partial matches and valid positions -/

/-- The start of a full partial match of a non-empty pattern is a valid position (as in
`Invariants.isValidForSlice`: the first byte of the pattern is a UTF-8 first byte). -/
theorem pm_valid_start {pat s : Slice} (hpat : pat.isEmpty = false) {pos : Pos.Raw}
    (h : PM pat.copy.toByteArray s.copy.toByteArray pat.utf8ByteSize pos.byteIdx) :
    (pos.unoffsetBy pat.rawEndPos).IsValidForSlice s := by
  have hne : pat.utf8ByteSize ≠ 0 := by simpa [Slice.isEmpty_eq] using hpat
  exact (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidForSlice) (InvMk hpat h (fun e => absurd e (by
    simpa [Pos.Raw.ext_iff] using hne)))

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.isLongestMatchAt`
theorem pm_lma_h2 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.isLongestMatchAt 2 := fun h =>
  absurd (h (pat := "".toSlice) (s := "".toSlice) (pos := ⟨0⟩) (by decide) (by decide)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.isLongestMatchAt`
theorem pm_lma_h4 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.isLongestMatchAt 4 := fun h =>
  absurd (h (pat := "a".toSlice) (s := "".toSlice) (by decide) (pos := ⟨0⟩) (by decide)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.isLongestMatchAt`: `h'` follows from
-- `hpat` and `h` (the window starts with the pattern's first byte, a UTF-8 first byte)
theorem pm_lma_h5 : indep% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.isLongestMatchAt 5 := by
  intro pat s hpat pos h
  exact pm_valid_start hpat h

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.isValidForSlice`: for an empty pattern
-- `pos.unoffsetBy pat.rawEndPos = pos`, so the conclusion is `h'`
theorem pm_valid_h2 : drop% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.isValidForSlice 2 := by
  intro pat s pos h h'
  cases hp : pat.isEmpty
  · exact (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.isValidForSlice) hp h h'
  · have h0 : pat.utf8ByteSize = 0 := Slice.isEmpty_iff.1 hp
    have e : pos.unoffsetBy pat.rawEndPos = pos := by simp [Pos.Raw.ext_iff, h0]
    rwa [e] at h'

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.isValidForSlice`
theorem pm_valid_h4 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.isValidForSlice 4 := fun h =>
  absurd (h (pat := "a".toSlice) (s := "é".toSlice) (by decide) (pos := ⟨1⟩) (by decide)) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.isValidForSlice`: `h'` follows from
-- `hpat` and `h`
theorem pm_valid_h5 : drop% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.isValidForSlice 5 := by
  intro pat s hpat pos h
  exact (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.isValidForSlice) hpat h (pm_valid_start hpat h)

/-- With an empty slice pattern the longest match at `p` is the empty one (copied from
`checks/StrPatternHand.lean`). -/
theorem fss_lma_empty {pat s : Slice} (hp : pat.isEmpty = true) {p q : s.Pos} :
    IsLongestMatchAt pat p q ↔ p = q := by
  have hc : pat.copy = "" := String.Slice.copy_eq_empty_iff.2 hp
  rw [ForwardSliceSearcher.isLongestMatchAt_iff_splits, hc]
  constructor
  · rintro ⟨t₁, t₂, h₁, h₂⟩
    simp only [String.empty_append, String.append_empty] at h₁ h₂
    exact h₁.pos_eq h₂
  · rintro rfl
    exact ⟨_, _, by simpa using p.splits, by simpa using p.splits⟩

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.matchesAt_iff_partialMatch`: for an empty pattern
-- both sides hold (the empty match, and the empty partial match ending at `pos`)
theorem matchesAt_pm_h2 : drop% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.matchesAt_iff_partialMatch 2 := by
  intro pat s pos
  cases hp : pat.isEmpty
  · exact (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.matchesAt_iff_partialMatch) hp
  · have hc : pat.copy = "" := String.Slice.copy_eq_empty_iff.2 hp
    refine ⟨fun _ => ?_, fun _ => ⟨⟨pos, (fss_lma_empty hp).2 rfl⟩⟩⟩
    simp only [hc, String.toByteArray_empty, ByteArray.size_empty, Nat.add_zero]
    exact pm_zero (by simpa [Pos.Raw.le_iff, Slice.Pos.le_iff] using pos.le_endPos)

/-! ### `isValidSearchFrom_toList` -/

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList`
theorem vsf_h5 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList 5 := fun h =>
  absurd (inv_pm (h (pat := "a".toSlice) (s := "".toSlice) (stackPos := ⟨1⟩) (needlePos := ⟨0⟩)
    _ (table := ForwardSliceSearcher.buildTable "a".toSlice) (ht := rfl) (hn := by decide) rfl
    (p := "".toSlice.startPos))) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList`
theorem vsf_h7 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList 7 := fun h => by
  have H : Inv "a".toSlice "".toSlice ⟨0⟩ ⟨0⟩ := InvMk (by decide) (by decide) (fun _ => by decide)
  have := congrArg (fun v => v[0]) (h (pat := "a".toSlice) (s := "".toSlice) (stackPos := ⟨0⟩)
    (needlePos := ⟨0⟩) ⟨.atEnd⟩ H (table := #v[1]) (hn := by decide) rfl)
  simp only [(priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.getElem_buildTable), pf_zero] at this
  exact absurd this (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList`
theorem vsf_h8 : ¬ indep0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList 8 := fun h =>
  absurd (h (pat := "a".toSlice) (s := "a".toSlice) (stackPos := ⟨1⟩) (needlePos := ⟨1⟩) ⟨.atEnd⟩
    (InvMk (by decide) (by decide) (fun e => absurd e (by decide))) (ht := rfl) rfl) (by decide)

theorem inv_a00 : Inv "a".toSlice "a".toSlice ⟨0⟩ ⟨0⟩ := InvMk (by decide) (by decide) (fun _ => by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList`
theorem vsf_h9 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList 9 := fun h => by
  have := h (pat := "a".toSlice) (s := "a".toSlice) (stackPos := ⟨0⟩) (needlePos := ⟨0⟩) ⟨.atEnd⟩ inv_a00
    (table := ForwardSliceSearcher.buildTable "a".toSlice) (ht := rfl) (hn := by decide) rfl
  rw [ForwardSliceSearcher.toList_atEnd_eq] at this
  exact absurd (vsf_unique this .endPos) (by decide)

-- `String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList`
theorem vsf_h11 : ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList 11 := fun h => by
  have h₁ := h (pat := "a".toSlice) (s := "a".toSlice) (stackPos := ⟨0⟩) (needlePos := ⟨0⟩)
    ⟨.proper "a".toSlice _ rfl ⟨0⟩ ⟨0⟩ (by decide)⟩ inv_a00 rfl (p := "a".toSlice.endPos)
  have h₂ := (priv% _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.«0».String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.isValidSearchFrom_toList)
    (⟨.proper "a".toSlice _ rfl ⟨0⟩ ⟨0⟩ (by decide)⟩ : Std.Iter (SearchStep "a".toSlice)) inv_a00 rfl rfl
  exact absurd (vsf_unique h₁ h₂) (by decide)

end StrLemHand

/-! # Independence support (Split.Basic, opaque collectors) -/

namespace StrLemHand
open String String.Slice.Pattern String.Slice.Pattern.Model

/-- A forward searcher that rejects the empty prefix forever (copied from `checks/OpEHand.lean`):
productive, not finite, so the collectors over it are opaque. -/
structure YSe (s : String.Slice) where u : Unit

instance YSe.inst (s : String.Slice) : Std.Iterator (YSe s) Id (SearchStep s) where
  IsPlausibleStep it st := st = .yield it (.rejected s.startPos s.startPos)
  step it := pure (.deflate ⟨.yield it (.rejected s.startPos s.startPos), rfl⟩)

instance YSe.searcher : ToForwardSearcher () YSe := ⟨fun _ => ⟨⟨()⟩⟩⟩

-- support for the independent row String.Slice.Pattern.Model.SplitIterator.toList_eq_splitFromSteps
-- idx 5: ¬T' from the assignment (split iterator over YSe).toList = [], (YSe iterator).toList = []
theorem SplitIterator.toList_eq_splitFromSteps.h5_neg
    (h₁ : (Std.Iter.mk (α := String.Slice.SplitIterator () "".toSlice)
      (.operating "".toSlice.startPos ⟨⟨()⟩⟩)).toList = [])
    (h₂ : (⟨⟨()⟩⟩ : Std.Iter (α := YSe "".toSlice) (SearchStep "".toSlice)).toList = []) :
    ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.Split.Basic.«0».String.Slice.Pattern.Model.SplitIterator.toList_eq_splitFromSteps 5 :=
  fun h => by
    have := h (pat := ()) (σ := YSe) (s := "".toSlice) ⟨⟨()⟩⟩ "".toSlice.startPos
    rw [h₁, h₂] at this
    exact List.cons_ne_nil _ _ this.symm

-- support for the independent row String.Slice.Pattern.Model.toList_splitToSubslice_eq_splitFromSteps
-- idx 5: ¬T' from the assignment (splitToSubslice over YSe).toList = [], (YSe searcher).toList = []
theorem toList_splitToSubslice_eq_splitFromSteps.h5_neg
    (h₁ : ("".toSlice.splitToSubslice ()).toList = [])
    (h₂ : (ToForwardSearcher.toSearcher () "".toSlice).toList = []) :
    ¬ drop0% _private.Init.Data.String.Lemmas.Pattern.Split.Basic.«0».String.Slice.Pattern.Model.toList_splitToSubslice_eq_splitFromSteps 5 :=
  fun h => by
    have := h (pat := ()) (σ := YSe) "".toSlice
    rw [h₁, h₂] at this
    exact List.cons_ne_nil _ _ this.symm

end StrLemHand
