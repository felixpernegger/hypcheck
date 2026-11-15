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

namespace W1c1
open Cslib Cslib.FLP
def flpA : Algorithm Unit Unit Unit := ⟨fun _ => (), fun _ _ => (), fun _ _ => 0, fun _ _ => none⟩
def flpE : Algorithm Empty Unit Unit := ⟨fun _ => (), fun _ _ => (), fun _ _ => 0, fun _ _ => none⟩
-- flpA never decides, along restricted reachability
theorem flpA_crv {ps : Set Unit} {t u : State Unit Unit Unit} (h : flpA.CanReachVia ps t u)
    (ht : (t.proc ()).out = none) : (u.proc ()).out = none := by
  induction h with
  | refl => exact ht
  | tail _ hst ih =>
    obtain ⟨x, -, htr⟩ := hst
    cases x with
    | none => cases htr; exact ih
    | some m => obtain ⟨-, rfl⟩ := htr; simp_all [Algorithm.recvMsg, flpA]
-- ZeroFaultAlg states on Fin 1 (no process decided)
def zs (l : List (Message (Fin 1) Bool)) : State (Fin 1) Bool Unit := ⟨l, fun _ => ⟨(), none⟩⟩
def zss (l : List (Message (Fin 1) Bool)) : ωSequence (State (Fin 1) Bool Unit) := ⟨fun _ => zs l⟩
def zs0 : State (Fin 0) Bool Unit := ⟨0, fun p => p.elim0⟩
end W1c1

namespace W1c1
open Cslib
-- Buchi automata on Unit: no transitions (all states accepting) / all transitions (no accepting state)
def bE : Automata.NA.Buchi Unit Unit := { Tr := fun _ _ _ => False, start := ∅, accept := Set.univ }
def bA : Automata.NA.Buchi Unit Unit := { Tr := fun _ _ _ => True, start := ∅, accept := ∅ }
-- successor automaton on ℕ
def bS : Automata.NA.Buchi ℕ Unit := { Tr := fun s _ t => t = s + 1, start := ∅, accept := ∅ }
theorem bE_mtr {s t : Unit} {l : List Unit} (h : bE.MTr s l t) : l = [] := by
  cases h with
  | refl => rfl
  | stepL htr _ => exact (htr : False).elim
theorem bS_mtr {s t : ℕ} {l : List Unit} (h : bS.MTr s l t) : t = s + l.length := by
  induction h with
  | refl => simp
  | stepL htr _ ih => have : _ = _ + 1 := htr; subst this; simp [ih]; omega
theorem bS_rep (i : ℕ) : ∀ s, bS.MTr s (List.replicate i ()) (s + i) := by
  induction i with
  | zero => intro s; exact .refl
  | succ i ih =>
    intro s
    have := ih (s + 1)
    rw [show s + 1 + i = s + (i + 1) by omega] at this
    exact .stepL (rfl : s + 1 = s + 1) this
end W1c1

namespace W1c1
open Cslib
def lnn : Language ℕ := {u | ∃ n, u = [n, n]}
theorem nfa_mem {S L : Type} (a : Automata.NA.FinAcc S L) (xs : List L) :
    xs ∈ Automata.Acceptor.language a ↔ ∃ s ∈ a.start, ∃ s' ∈ a.accept, a.MTr s xs s' := Iff.rfl
theorem mtr_nil {S L : Type} {lts : LTS S L} {s t : S} (h : lts.MTr s [] t) : s = t := by
  cases h; rfl
def lE1 : LTS (Fin 1) Unit := ⟨fun _ _ _ => False⟩
def lT (n : ℕ) : LTS (Fin n) Unit := ⟨fun _ _ _ => True⟩
-- in the empty LTS, bddLang only holds the empty word
theorem lE1_bdd {xs : List Unit} {b : ℕ} (h : xs ∈ lE1.bddLang 0 0 b) : xs = [] := by
  obtain ⟨ss, hex, -⟩ := h
  cases hex.to_mTr with
  | refl => rfl
  | stepL htr _ => exact (htr : False).elim
end W1c1

namespace W1c1
open Cslib
-- lnn is not regular (its Myhill quotient is infinite)
theorem lnn_nonreg : ¬ lnn.IsRegular := fun h => by
  have := Language.IsRegular.finite_myhillQuotient h
  refine not_injective_infinite_finite
    (fun i : ℕ => Quotient.mk (W1c1.lnn.MyhillCongruence.eq) [i]) ?_
  intro i j hij
  have h2 := (Quotient.exact hij [] [i]).1 (show ∃ k, [] ++ [i] ++ [i] = [k, k] from ⟨i, rfl⟩)
  obtain ⟨k, hk⟩ := (h2 : ∃ k, [] ++ [j] ++ [i] = [k, k])
  simp at hk; omega
-- an upper bound on the characters of a regular expression over ℕ
def rb : RegularExpression ℕ → ℕ
  | .zero => 0
  | .epsilon => 0
  | .char a => a
  | .plus p q => max (rb p) (rb q)
  | .comp p q => max (rb p) (rb q)
  | .star p => rb p
theorem rb_le (r : RegularExpression ℕ) : ∀ w ∈ r.matches', ∀ x ∈ w, x ≤ rb r := by
  induction r with
  | zero => intro w hw; simp [RegularExpression.matches'] at hw
  | epsilon => intro w hw; simp [RegularExpression.matches'] at hw; subst hw; simp
  | char a => intro w hw x hx; simp [RegularExpression.matches'] at hw; subst hw; simp at hx; simp [rb, hx]
  | plus p q ihp ihq =>
    intro w hw x hx
    simp only [RegularExpression.matches', Language.mem_add] at hw
    rcases hw with hw | hw
    · exact le_max_of_le_left (ihp w hw x hx)
    · exact le_max_of_le_right (ihq w hw x hx)
  | comp p q ihp ihq =>
    intro w hw x hx
    simp only [RegularExpression.matches', Language.mem_mul] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hw
    rcases List.mem_append.1 hx with hx | hx
    · exact le_max_of_le_left (ihp a ha x hx)
    · exact le_max_of_le_right (ihq b hb x hx)
  | star p ih =>
    intro w hw x hx
    simp only [RegularExpression.matches', Language.mem_kstar] at hw
    obtain ⟨L, rfl, hL⟩ := hw
    obtain ⟨y, hy, hxy⟩ := List.mem_flatten.1 hx
    exact ih y (hL y hy) x hxy
-- no regular expression over ℕ matches a language containing every word
theorem no_regex_all (L : Language ℕ) (hL : ∀ w, w ∈ L) (r : RegularExpression ℕ) : L ≠ r.matches' :=
  fun h => by
    have h1 : [rb r + 1] ∈ r.matches' := h ▸ hL _
    have := rb_le r _ h1 _ (List.mem_singleton_self _)
    omega
-- one-state NFA over ℕ accepting every word
def nTop : Automata.NA.FinAcc Unit ℕ := ⟨⟨⟨fun _ _ _ => True⟩, {()}⟩, {()}⟩
theorem nTop_all (w : List ℕ) : w ∈ Automata.Acceptor.language nTop := by
  rw [nfa_mem]
  refine ⟨(), rfl, (), rfl, ?_⟩
  induction w with
  | nil => exact .refl
  | cons a w ih => exact .stepL trivial ih
-- counter NFA over Bool on ℤ: accepts the words with as many `true` as `false`
def cnt (w : List Bool) : ℤ := (w.map (fun b => if b then (1 : ℤ) else -1)).sum
def nC : Automata.NA.FinAcc ℤ Bool := ⟨⟨⟨fun s b t => t = if b then s + 1 else s - 1⟩, {0}⟩, {0}⟩
theorem nC_mtr {s t : ℤ} {w : List Bool} (h : nC.MTr s w t) : t = s + cnt w := by
  induction h with
  | refl => simp [cnt]
  | @stepL s1 b s2 _ _ htr _ ih =>
    have : s2 = if b then s1 + 1 else s1 - 1 := htr
    subst this; rw [ih]; cases b <;> simp [cnt] <;> ring
theorem nC_mtr' (w : List Bool) : ∀ s, nC.MTr s w (s + cnt w) := by
  induction w with
  | nil => intro s; simp only [cnt, List.map_nil, List.sum_nil, add_zero]; exact LTS.MTr.refl
  | cons b w ih =>
    intro s
    have := ih (if b then s + 1 else s - 1)
    refine .stepL rfl ?_
    convert this using 1
    cases b <;> simp [cnt] <;> ring
theorem nC_mem (w : List Bool) : w ∈ Automata.Acceptor.language nC ↔ cnt w = 0 := by
  rw [nfa_mem]
  constructor
  · rintro ⟨s, hs, t, ht, h⟩
    have := nC_mtr h
    simp [nC] at hs ht; subst hs ht; omega
  · intro h
    exact ⟨0, rfl, 0, rfl, by simpa [h] using nC_mtr' w 0⟩
theorem nC_nonreg : ¬ (Automata.Acceptor.language nC).IsRegular := fun h => by
  have := Language.IsRegular.finite_myhillQuotient h
  refine not_injective_infinite_finite
    (fun i : ℕ => Quotient.mk ((Automata.Acceptor.language nC).MyhillCongruence.eq)
      (List.replicate i true)) ?_
  intro i j hij
  have h2 := (Quotient.exact hij [] (List.replicate i false)).1
    (by rw [nC_mem]; simp [cnt, List.sum_replicate])
  rw [nC_mem] at h2
  simp [cnt, List.sum_replicate] at h2
  omega
end W1c1

namespace W1c1
open Cslib
-- a language over ℕ holding [i, i] but no [j, i] with j ≠ i is not regular (infinite Myhill quotient)
theorem nonreg_of (l : Language ℕ) (h1 : ∀ i, [i, i] ∈ l) (h2 : ∀ i j, [j, i] ∈ l → j = i) :
    ¬ l.IsRegular := fun h => by
  have := Language.IsRegular.finite_myhillQuotient h
  refine not_injective_infinite_finite
    (fun i : ℕ => Quotient.mk (l.MyhillCongruence.eq) [i]) ?_
  intro i j hij
  exact (h2 i j ((Quotient.exact hij [] [i]).1 (h1 i))).symm
theorem lnn_kstar_nonreg : ¬ (KStar.kstar lnn).IsRegular := by
  refine nonreg_of _ (fun i => ⟨[[i, i]], by simp, fun y hy => by simp at hy; exact ⟨i, hy⟩⟩) ?_
  intro i j ⟨L, hL, hy⟩
  match L, hL, hy with
  | [], hL, _ => simp at hL
  | y :: L', hL, hy =>
    obtain ⟨k, rfl⟩ := hy y (by simp)
    simp at hL; omega
-- x ++ [a, b] ++ z ∈ lnn forces x = z = [] and a = b
theorem lnn_mid {x z : List ℕ} {a b : ℕ} : x ++ [a, b] ++ z ∈ lnn ↔ x = [] ∧ z = [] ∧ a = b := by
  constructor
  · rintro ⟨k, hk⟩
    have hl := congrArg List.length hk
    simp at hl
    have hx : x = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hz : z = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx hz; simp at hk; exact ⟨rfl, rfl, by omega⟩
  · rintro ⟨rfl, rfl, rfl⟩; exact ⟨a, rfl⟩
def idH : Language.Hom ℕ ℕ := ⟨id, rfl, fun _ _ => rfl⟩
theorem lnn_eq : (⨆ n ∈ (Set.univ : Set ℕ), ({[n]} * {[n]} : Language ℕ)) = lnn := by
  ext w
  simp only [Language.mem_iSup, Set.mem_univ, exists_const, Language.mem_mul]
  constructor
  · rintro ⟨n, a, ha, b, hb, rfl⟩
    exact ⟨n, by rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]; rfl⟩
  · rintro ⟨n, rfl⟩; exact ⟨n, [n], rfl, [n], rfl, rfl⟩
-- DFAs on Unit/Bool/ℕ
def M1 : Automata.DA.FinAcc Unit Unit := ⟨⟨⟨fun _ _ => ()⟩, ()⟩, ∅⟩
def MN : Automata.DA.FinAcc ℕ Unit := ⟨⟨⟨fun s _ => s⟩, 0⟩, ∅⟩
theorem MN_empty (w : List Unit) : w ∉ Automata.Acceptor.language MN := fun hw => hw
def Mb : Automata.DA.FinAcc Bool Unit := ⟨⟨⟨fun _ _ => true⟩, false⟩, {false}⟩
def Mt : Automata.DA.FinAcc Bool Unit := ⟨⟨⟨fun _ _ => true⟩, false⟩, Set.univ⟩
end W1c1

namespace W1c1
open Cslib
def u0 : ωSequence Unit := ⟨fun _ => ()⟩
theorem top_ne_bot : (⊤ : ωLanguage Unit) ≠ ⊥ := fun e => by
  have := ωLanguage.mem_top u0
  rw [e] at this
  exact this
-- the ω-power of the empty language is empty
theorem zero_omegaPow (s : ωSequence Unit) : s ∉ ωLanguage.omegaPow (0 : Language Unit) := fun h => by
  obtain ⟨xs, -, hx⟩ := ωLanguage.mem_omegaPow.1 h
  exact (Language.notMem_zero _) ((Language.mem_sub _ _ _).1 (hx 0)).1
-- ⊤^ω over Unit is nonempty
theorem top_omegaPow : (⟨fun _ => [()]⟩ : ωSequence (List Unit)).flatten ∈ ωLanguage.omegaPow (⊤ : Language Unit) :=
  ωLanguage.mem_omegaPow.2 ⟨_, rfl, fun _ => (Language.mem_sub _ _ _).2 ⟨trivial, by simp⟩⟩
theorem zero_hmul {p : ωLanguage Unit} (s : ωSequence Unit) : s ∉ (0 : Language Unit) * p := fun h => by
  obtain ⟨x, hx, -⟩ := ωLanguage.mem_hmul.1 h
  exact (Language.notMem_zero _) hx
theorem one_hmul_top (s : ωSequence Unit) : s ∈ (1 : Language Unit) * (⊤ : ωLanguage Unit) := by
  have := ωLanguage.append_mem_hmul (l := (1 : Language Unit)) (Language.nil_mem_one) (ωLanguage.mem_top s)
  rwa [ωSequence.nil_append_ωSequence] at this
theorem hmul_bot {l : Language Unit} (s : ωSequence Unit) : s ∉ l * (⊥ : ωLanguage Unit) := fun h => by
  obtain ⟨x, -, t, ht, -⟩ := ωLanguage.mem_hmul.1 h
  exact ht
theorem no_regex_single (L : Language ℕ) (hL : ∀ n, [n] ∈ L) (r : RegularExpression ℕ) : L ≠ r.matches' :=
  fun h => by
    have h1 : [rb r + 1] ∈ r.matches' := h ▸ hL _
    have := rb_le r _ h1 _ (List.mem_singleton_self _)
    omega
end W1c1

namespace W1c1
open Cslib
-- ω-sequences over ℕ whose first two letters are equal
def p0 : ωLanguage ℕ := lnn * (⊤ : ωLanguage ℕ)
theorem seq_tail (m n : ℕ) (t : ωSequence ℕ) (k : ℕ) :
    ([m, n] ++ω t) (k + 1) = ([n, n] ++ω t) (k + 1) := by
  rcases k with _ | k
  · simp [ωSequence.get_append_left]
  · rw [ωSequence.get_append_right' (by simp), ωSequence.get_append_right' (by simp)]; simp
-- splicing: a finite-state Büchi language containing every a a t contains some a b t with a ≠ b
theorem nonreg (p : ωLanguage ℕ) (t : ωSequence ℕ) (hin : ∀ a, [a, a] ++ω t ∈ p)
    (hout : ∀ a b, [a, b] ++ω t ∈ p → a = b) : ¬ p.IsRegular := by
  rintro ⟨State, hfin, na, hl⟩
  have hacc : ∀ a, ∃ ss, na.Run ([a, a] ++ω t) ss ∧ ∃ᶠ k in Filter.atTop, ss k ∈ na.accept :=
    fun a => by have := hin a; rw [← hl] at this; exact this
  choose ss hrun hfr using hacc
  obtain ⟨m, n, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun a => ss a 1)
  let ss' : ωSequence State := ⟨fun k => if k = 0 then ss m 0 else ss n k⟩
  have hmem : [m, n] ++ω t ∈ Automata.ωAcceptor.language na := by
    refine ⟨ss', ⟨(hrun m).start, ?_⟩, ?_⟩
    · intro k
      rcases k with _ | k
      · have := (hrun m).trans 0
        show na.Tr (ss m 0) (([m, n] ++ω t) 0) (ss n 1)
        rw [← heq]
        simpa [ωSequence.get_append_left] using this
      · have := (hrun n).trans (k + 1)
        show na.Tr (ss n (k + 1)) (([m, n] ++ω t) (k + 1)) (ss n (k + 1 + 1))
        rw [seq_tail]; exact this
    · have hf := hfr n
      rw [Filter.frequently_atTop] at hf ⊢
      intro N
      obtain ⟨k, hk, hacc⟩ := hf (N + 1)
      refine ⟨k, by omega, ?_⟩
      show (if k = 0 then ss m 0 else ss n k) ∈ na.accept
      have hk0 : ¬ k = 0 := by omega
      simp only [hk0, ↓reduceIte]; exact hacc
  rw [hl] at hmem
  exact hne (hout m n hmem)
theorem p0_in (a : ℕ) (t : ωSequence ℕ) : [a, a] ++ω t ∈ p0 :=
  ωLanguage.append_mem_hmul ⟨a, rfl⟩ (ωLanguage.mem_top t)
theorem p0_out (a b : ℕ) (t : ωSequence ℕ) (h : [a, b] ++ω t ∈ p0) : a = b := by
  obtain ⟨x, ⟨k, rfl⟩, s, -, he⟩ := ωLanguage.mem_hmul.1 h
  have h0 := congrArg (fun z : ωSequence ℕ => z 0) he
  have h1 := congrArg (fun z : ωSequence ℕ => z 1) he
  simp [ωSequence.get_append_left] at h0 h1
  omega
theorem p0_nonreg : ¬ p0.IsRegular :=
  nonreg p0 (ωSequence.const 0) (fun a => p0_in a _) (fun a b h => p0_out a b _ h)
theorem p0c_nonreg : ¬ p0ᶜ.IsRegular := fun h => p0_nonreg (by simpa using h.compl)
end W1c1

namespace W1c1
open Cslib
-- the union of the regular ω-languages {[n]} * {[n]} * ⊤ over all n is not ω-regular
def pn (n : ℕ) : ωLanguage ℕ := ({[n]} * {[n]} : Language ℕ) * (⊤ : ωLanguage ℕ)
theorem pn_reg (n : ℕ) : (pn n).IsRegular :=
  ωLanguage.IsRegular.hmul (Language.IsRegular.mul (Language.IsRegular.char n)
    (Language.IsRegular.char n)) ωLanguage.IsRegular.top
theorem qS_nonreg : ¬ (⨆ n, pn n).IsRegular := by
  refine nonreg _ (ωSequence.const 0) (fun a => ωLanguage.mem_iSup.2 ⟨a, ?_⟩) (fun a b h => ?_)
  · exact ωLanguage.append_mem_hmul ⟨[a], rfl, [a], rfl, rfl⟩ (ωLanguage.mem_top _)
  · obtain ⟨n, hn⟩ := ωLanguage.mem_iSup.1 h
    obtain ⟨x, ⟨u, hu, v, hv, rfl⟩, s, -, he⟩ := ωLanguage.mem_hmul.1 hn
    rw [Set.mem_singleton_iff.1 hu, Set.mem_singleton_iff.1 hv] at he
    have h0 := congrArg (fun z : ωSequence ℕ => z 0) he
    have h1 := congrArg (fun z : ωSequence ℕ => z 1) he
    simp [ωSequence.get_append_left] at h0 h1
    omega
-- the ω-limit of {a :: a :: v} is not ω-regular
def lpre : Language ℕ := {u | ∃ a v, u = a :: a :: v}
theorem lpre_lim_nonreg : ¬ (lpre↗ω).IsRegular := by
  refine nonreg _ (ωSequence.const 0) (fun a => ?_) (fun a b h => ?_)
  · rw [ωLanguage.mem_omegaLim, Filter.frequently_atTop]
    intro N
    refine ⟨[a, a].length + N, by simp, ?_⟩
    rw [ωSequence.extract_eq_take, ← ωSequence.append_take]
    exact ⟨a, _, rfl⟩
  · rw [ωLanguage.mem_omegaLim] at h
    obtain ⟨m, ⟨c, v, hv⟩⟩ := h.exists
    rw [ωSequence.extract_eq_take] at hv
    have hl := congrArg List.length hv
    simp at hl
    rw [show m = [a, b].length + (m - 2) by simp; omega, ← ωSequence.append_take] at hv
    simp at hv
    omega
end W1c1

namespace W1c1
open Cslib
-- lnn^ω (blocks [n, n]) is not ω-regular
theorem lnn_omegaPow_nonreg : ¬ (ωLanguage.omegaPow lnn).IsRegular := by
  refine nonreg _ (ωSequence.const [0, 0]).flatten (fun a => ?_) (fun a b h => ?_)
  · let ls : ωSequence (List ℕ) := ⟨fun k => if k = 0 then [a, a] else [0, 0]⟩
    have hpos : ∀ k, 0 < (ls k).length := fun k => by
      show 0 < (if k = 0 then [a, a] else [0, 0]).length; split <;> simp
    refine ωLanguage.mem_omegaPow.2 ⟨ls, ?_, fun k => (Language.mem_sub _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [← ωSequence.cons_flatten hpos]
      have : ls.tail = ωSequence.const [0, 0] := by
        ext k; simp [ls, ωSequence.tail]
      rw [this]; rfl
    · show (if k = 0 then [a, a] else [0, 0]) ∈ lnn
      split
      · exact ⟨a, rfl⟩
      · exact ⟨0, rfl⟩
    · show (if k = 0 then [a, a] else [0, 0]) ∉ (1 : Language ℕ)
      split <;> simp
  · obtain ⟨ls, hls, hk⟩ := ωLanguage.mem_omegaPow.1 h
    have hpos : ∀ k, 0 < (ls k).length := fun k => by
      obtain ⟨c, hc⟩ := ((Language.mem_sub _ _ _).1 (hk k)).1
      rw [hc]; simp
    obtain ⟨c, hc⟩ := ((Language.mem_sub _ _ _).1 (hk 0)).1
    rw [← ωSequence.cons_flatten hpos] at hls
    change ls 0 ++ω _ = _ at hls
    rw [hc] at hls
    have h0 := congrArg (fun z : ωSequence ℕ => z 0) hls
    have h1 := congrArg (fun z : ωSequence ℕ => z 1) hls
    simp [ωSequence.get_append_left] at h0 h1
    omega
-- cover of ω-words over ℕ by their first two letters
def pab (i : ℕ × ℕ) : ωLanguage ℕ := ({[i.1]} * {[i.2]} : Language ℕ) * (⊤ : ωLanguage ℕ)
theorem pab_mem {i : ℕ × ℕ} {y : ωSequence ℕ} (h : y ∈ pab i) : ∃ s, y = [i.1, i.2] ++ω s := by
  obtain ⟨x, ⟨u, hu, v, hv, rfl⟩, s, -, he⟩ := ωLanguage.mem_hmul.1 h
  rw [Set.mem_singleton_iff.1 hu, Set.mem_singleton_iff.1 hv] at he
  exact ⟨s, he.symm⟩
theorem pab_cover : ⨆ i, pab i = ⊤ := by
  refine ωLanguage.mem_ext fun s => ⟨fun _ => ωLanguage.mem_top s, fun _ => ?_⟩
  refine ωLanguage.mem_iSup.2 ⟨(s 0, s 1), ?_⟩
  have e := ωSequence.append_take_drop 2 s
  have ht : s.take 2 = [s 0, s 1] := by simp [ωSequence.take_succ', ωSequence.take_zero]
  rw [ht] at e
  rw [← e]
  exact ωLanguage.append_mem_hmul ⟨[s 0], rfl, [s 1], rfl, rfl⟩ (ωLanguage.mem_top _)
theorem pab_sat : Set.Saturates (fun i => (pab i).toSet) p0.toSet := by
  rintro ⟨a, b⟩ ⟨x, hx, hx0⟩
  obtain ⟨s, rfl⟩ := pab_mem hx
  have hab : a = b := p0_out a b s hx0
  subst hab
  intro y hy
  obtain ⟨s', rfl⟩ := pab_mem hy
  exact p0_in a s'
theorem pab_reg (i : ℕ × ℕ) : (pab i).IsRegular :=
  ωLanguage.IsRegular.hmul (Language.IsRegular.mul (Language.IsRegular.char _)
    (Language.IsRegular.char _)) ωLanguage.IsRegular.top
end W1c1

namespace W1c1
open Cslib
-- Büchi automaton on List ℕ remembering the whole input: its Büchi congruence is equality
def bL : Automata.NA.Buchi (List ℕ) ℕ := { Tr := fun s x t => t = s ++ [x], start := ∅, accept := ∅ }
theorem bL_mtr {s t : List ℕ} {u : List ℕ} (h : bL.MTr s u t) : t = s ++ u := by
  induction h with
  | refl => simp
  | stepL htr _ ih => have : _ = _ ++ [_] := htr; subst this; simp [ih]
theorem bL_mtr' (u : List ℕ) : ∀ s, bL.MTr s u (s ++ u) := by
  induction u with
  | nil => intro s; simp only [List.append_nil]; exact LTS.MTr.refl
  | cons x u ih =>
    intro s
    have := ih (s ++ [x])
    simp only [List.append_assoc, List.singleton_append] at this
    exact .stepL rfl this
theorem bL_eq {u v : List ℕ} (h : bL.BuchiCongruence.eq u v) : u = v := by
  have := (h [] u).1.1 (by simpa using bL_mtr' u [])
  simpa using bL_mtr this
end W1c1

namespace W1c1
open Cslib
-- deterministic Büchi automaton on List ℕ remembering the input, accepting prefixes in lpre
def dL : Automata.DA.Buchi (List ℕ) ℕ := ⟨⟨⟨fun s x => s ++ [x]⟩, []⟩, {u | ∃ a v, u = a :: a :: v}⟩
theorem dL_run (xs : ωSequence ℕ) (n : ℕ) : dL.run xs n = xs.extract 0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Automata.DA.run_succ, ih, ωSequence.extract_eq_take, ωSequence.extract_eq_take,
      ωSequence.take_succ']
    rfl
theorem dL_lang : Automata.ωAcceptor.language dL = lpre↗ω := by
  refine ωLanguage.mem_ext fun xs => ?_
  rw [ωLanguage.mem_omegaLim]
  show (∃ᶠ k in Filter.atTop, dL.run xs k ∈ dL.accept) ↔ _
  simp only [dL_run]
  rfl
end W1c1

open Cslib.FLP in
-- `Cslib.FLP.PseudoConsensus.of_consensus` idx 8: necessary (P empty, f = 0: consensus vacuous, no process can decide)
theorem ofc8 : ¬ drop0% Cslib.FLP.PseudoConsensus.of_consensus 8 := fun h => by
  obtain ⟨-, h2⟩ := @h Empty Unit Unit _ _ W1c1.flpE _ 0
    ⟨fun _ _ _ => ⟨fun _ _ ⟨⟨p, _⟩, _⟩ => p.elim, fun _ ⟨p, _⟩ => p.elim⟩, fun _ _ _ _ p => p.elim⟩
  obtain ⟨_, _, _, ⟨p, _⟩⟩ := h2 (fun e => e.elim) _ Algorithm.reachable_start ∅ (by simp)
  exact p.elim

open Cslib.FLP in
-- `Cslib.FLP.PseudoConsensus.of_consensus` idx 9: necessary (one process that never decides, f = 0)
theorem ofc9 : ¬ drop0% Cslib.FLP.PseudoConsensus.of_consensus 9 := fun h => by
  obtain ⟨-, h2⟩ := @h Unit Unit Unit _ _ W1c1.flpA _ 0 (by simp)
  obtain ⟨s', b, hc, ⟨p, hp⟩⟩ := h2 (fun _ => true) _ Algorithm.reachable_start Set.univ (by simp)
  have := W1c1.flpA_crv hc (by simp [Algorithm.start, W1c1.flpA])
  cases p; simp_all

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.inv_tr_left` idx 1: removable (the message m has a destination in Fin n)
theorem itl1 : indep% Cslib.FLP.ZeroFaultAlg.inv_tr_left 1 := @fun _ _ _ _ m _ => m.dest.pos

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.inv_tr_left` idx 6: necessary (message inl false while inp = true)
theorem itl6 : ¬ drop0% Cslib.FLP.ZeroFaultAlg.inv_tr_left 6 := fun h => by
  have := (@h 1 (by decide) (fun _ => true) (W1c1.zs [⟨0, .inl false⟩]) _ ⟨0, .inl false⟩
    ⟨by simp [W1c1.zs], rfl⟩ rfl).1
  simp [W1c1.zs, Algorithm.recvMsg, ZeroFaultAlg.alg] at this

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.inv_tr_left` idx 7: necessary (no transition: t = s = empty state)
theorem itl7 : ¬ drop0% Cslib.FLP.ZeroFaultAlg.inv_tr_left 7 := fun h => by
  have := (@h 1 (by decide) (fun _ => true) (W1c1.zs []) (W1c1.zs []) ⟨0, .inl true⟩
    ⟨fun m hm => by simp [W1c1.zs] at hm, fun _ => Or.inl rfl⟩ rfl).1
  simp [W1c1.zs] at this

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.inv_tr_left` idx 8: necessary (an inr message)
theorem itl8 : ¬ drop0% Cslib.FLP.ZeroFaultAlg.inv_tr_left 8 := fun h => by
  have := (@h 1 (by decide) (fun _ => true) (W1c1.zs [⟨0, .inr true⟩]) _ ⟨0, .inr true⟩
    ⟨fun m hm => by simp [W1c1.zs] at hm; simp [hm], fun _ => Or.inl rfl⟩ ⟨by simp [W1c1.zs], rfl⟩).1
  simp [W1c1.zs, Algorithm.recvMsg, ZeroFaultAlg.alg] at this

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.inv_tr_right` idx 1: removable (the message m has a destination in Fin n)
theorem itr1 : indep% Cslib.FLP.ZeroFaultAlg.inv_tr_right 1 := @fun _ _ _ _ m _ => m.dest.pos

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.inv_tr_right` idx 6: necessary (message inr false while inp = true)
theorem itr6 : ¬ drop0% Cslib.FLP.ZeroFaultAlg.inv_tr_right 6 := fun h => by
  have := (@h 1 (by decide) (fun _ => true) (W1c1.zs [⟨0, .inr false⟩]) _ ⟨0, .inr false⟩
    ⟨by simp [W1c1.zs], rfl⟩ rfl).2.1
  simp [W1c1.zs, Algorithm.recvMsg, ZeroFaultAlg.alg] at this

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.inv_tr_right` idx 7: necessary (no transition)
theorem itr7 : ¬ drop0% Cslib.FLP.ZeroFaultAlg.inv_tr_right 7 := fun h => by
  have := (@h 1 (by decide) (fun _ => true) (W1c1.zs []) (W1c1.zs []) ⟨0, .inr true⟩
    ⟨fun m hm => by simp [W1c1.zs] at hm, fun _ => Or.inl rfl⟩ rfl).2.1
  simp [W1c1.zs] at this

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.inv_tr_right` idx 8: necessary (an inl message does not decide)
theorem itr8 : ¬ drop0% Cslib.FLP.ZeroFaultAlg.inv_tr_right 8 := fun h => by
  have := (@h 1 (by decide) (fun _ => true) (W1c1.zs [⟨0, .inl true⟩]) _ ⟨0, .inl true⟩
    ⟨fun m hm => by simp [W1c1.zs] at hm; simp [hm], fun _ => Or.inl rfl⟩ ⟨by simp [W1c1.zs], rfl⟩).2.1
  simp [W1c1.zs, Algorithm.recvMsg, ZeroFaultAlg.alg] at this

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.reachable_inv` idx 1: necessary (n = 0)
theorem ri1 : ¬ indep0% Cslib.FLP.ZeroFaultAlg.reachable_inv 1 := fun h =>
  absurd (@h 0 (fun _ => true) W1c1.zs0) (by decide)

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.reachable_inv` idx 4: necessary (unreachable state with a wrong message)
theorem ri4 : ¬ drop0% Cslib.FLP.ZeroFaultAlg.reachable_inv 4 := fun h => by
  have := (@h 1 (by decide) (fun _ => true) (W1c1.zs [⟨0, .inl false⟩])).1 ⟨0, .inl false⟩ (by simp [W1c1.zs])
  simp at this

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.always_inv` idx 1: necessary (n = 0)
theorem ai1 : ¬ indep0% Cslib.FLP.ZeroFaultAlg.always_inv 1 := fun h =>
  absurd (@h 0 (fun _ => true) ⟨fun _ => W1c1.zs0⟩ ⟨fun _ => none⟩ 0) (by decide)

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.always_inv` idx 5: necessary (constant non-run with a wrong message)
theorem ai5 : ¬ drop0% Cslib.FLP.ZeroFaultAlg.always_inv 5 := fun h => by
  have := (@h 1 (by decide) (fun _ => true) (W1c1.zss [⟨0, .inl false⟩]) ⟨fun _ => none⟩ 0).1
    ⟨0, .inl false⟩ (by simp [W1c1.zss, W1c1.zs])
  simp at this

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.init_left` idx 1: necessary (n = 0)
theorem il1 : ¬ indep0% Cslib.FLP.ZeroFaultAlg.init_left 1 := fun h =>
  absurd (@h 0 (fun _ => true) ⟨fun _ => W1c1.zs0⟩ ⟨fun _ => none⟩) (by decide)

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.init_left` idx 5: necessary (constant empty state)
theorem il5 : ¬ drop0% Cslib.FLP.ZeroFaultAlg.init_left 5 := fun h => by
  have := @h 1 (by decide) (fun _ => true) (W1c1.zss []) ⟨fun _ => none⟩
  simp [W1c1.zss, W1c1.zs] at this

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.left_leadsTo_right` idx 1: removable (p : Fin n gives 0 < n)
theorem llr1 : indep% Cslib.FLP.ZeroFaultAlg.left_leadsTo_right 1 := @fun _ _ _ _ p => p.pos

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.left_leadsTo_right` idx 5: necessary (constant state with the inl message only)
theorem llr5 : ¬ drop0% Cslib.FLP.ZeroFaultAlg.left_leadsTo_right 5 := fun h => by
  obtain ⟨k, -, hk⟩ := @h 1 (by decide) (fun _ => true) (W1c1.zss [⟨0, .inl true⟩]) ⟨fun _ => none⟩ 0 0
    (by simp [W1c1.zss, W1c1.zs])
  simp [W1c1.zss, W1c1.zs] at hk

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.right_leadsTo_out` idx 1: removable (p : Fin n gives 0 < n)
theorem rlo1 : indep% Cslib.FLP.ZeroFaultAlg.right_leadsTo_out 1 := @fun _ _ _ _ p => p.pos

open Cslib.FLP in
-- `Cslib.FLP.ZeroFaultAlg.right_leadsTo_out` idx 5: necessary (constant undecided state with the inr message)
theorem rlo5 : ¬ drop0% Cslib.FLP.ZeroFaultAlg.right_leadsTo_out 5 := fun h => by
  obtain ⟨k, -, hk⟩ := @h 1 (by decide) (fun _ => true) (W1c1.zss [⟨0, .inr true⟩]) ⟨fun _ => none⟩ 0 0
    (by simp [W1c1.zss, W1c1.zs])
  simp [W1c1.zss, W1c1.zs] at hk

-- `Cslib.Automata.NA.Buchi.buchiCongruence_fin_index` idx 3: necessary (successor automaton on ℕ: word lengths are separated)
theorem bcfi3 : ¬ drop0% Cslib.Automata.NA.Buchi.buchiCongruence_fin_index 3 := fun h => by
  have := @h Unit ℕ W1c1.bS
  refine not_injective_infinite_finite
    (fun i : ℕ => Quotient.mk (W1c1.bS.BuchiCongruence.eq) (List.replicate i ())) ?_
  intro i j hij
  have h2 := ((Quotient.exact hij 0 i).1.mp (by simpa using W1c1.bS_rep i 0))
  have := W1c1.bS_mtr h2
  simp at this; omega

-- `Cslib.Automata.NA.Buchi.buchiCongruence_transfer` idx 8: necessary (no transitions; xl = [] outside the class of yl = [()])
theorem bct8 : ¬ drop0% Cslib.Automata.NA.Buchi.buchiCongruence_transfer 8 := fun h => by
  obtain ⟨sl, he, -⟩ := @h Unit Unit W1c1.bE (Quotient.mk _ [()]) [] [()] () () rfl .refl
  exact absurd (W1c1.bE_mtr he.to_mTr) (by simp)

-- `Cslib.Automata.NA.Buchi.buchiCongruence_transfer` idx 9: necessary (no transitions; yl = [()] outside the class of xl = [])
theorem bct9 : ¬ drop0% Cslib.Automata.NA.Buchi.buchiCongruence_transfer 9 := fun h => by
  obtain ⟨sl, he, -⟩ := @h Unit Unit W1c1.bE (Quotient.mk _ []) [] [()] () () rfl .refl
  exact absurd (W1c1.bE_mtr he.to_mTr) (by simp)

-- `Cslib.Automata.NA.Buchi.buchiCongruence_transfer` idx 10: necessary (no transitions; xl = yl = [()])
theorem bct10 : ¬ drop0% Cslib.Automata.NA.Buchi.buchiCongruence_transfer 10 := fun h => by
  obtain ⟨sl, he, -⟩ := @h Unit Unit W1c1.bE (Quotient.mk _ [()]) [()] [()] () () rfl rfl
  exact absurd (W1c1.bE_mtr he.to_mTr) (by simp)

-- `_private.Cslib.Computability.Languages.Congruences.BuchiCongruence.0.Cslib.Automata.NA.Buchi.frequently_via_accept` idx 7: necessary (all transitions, no accepting state)
theorem fva7 : ¬ drop0% _private.Cslib.Computability.Languages.Congruences.BuchiCongruence.«0».Cslib.Automata.NA.Buchi.frequently_via_accept 7 := fun h => by
  have := @h Unit Unit W1c1.bA _ [] ⟨fun _ => [()]⟩ ⟨fun _ => ()⟩ (fun _ => trivial) (fun _ => by simp)
  obtain ⟨k, hk⟩ := this.exists
  rw [Cslib.LTS.mem_pairViaLang] at hk
  obtain ⟨r, hr, -⟩ := hk
  exact hr

-- `_private.Cslib.Computability.Languages.Congruences.BuchiCongruence.0.Cslib.Automata.NA.Buchi.frequently_via_accept` idx 8: necessary (no transitions, all states accepting)
theorem fva8 : ¬ drop0% _private.Cslib.Computability.Languages.Congruences.BuchiCongruence.«0».Cslib.Automata.NA.Buchi.frequently_via_accept 8 := fun h => by
  have := @h Unit Unit W1c1.bE _ [] ⟨fun _ => [()]⟩ ⟨fun _ => ()⟩
    (Filter.Frequently.of_forall (fun _ => Set.mem_univ _)) (fun _ => by simp)
  obtain ⟨k, hk⟩ := this.exists
  rw [Cslib.LTS.mem_pairViaLang] at hk
  obtain ⟨r, -, xs1, xs2, h1, h2, he⟩ := hk
  rw [W1c1.bE_mtr h1, W1c1.bE_mtr h2] at he
  simp at he

-- `Language.IsRegular.finite_myhillQuotient` idx 2: necessary (alphabet ℕ, l = {[n, n]}: the words [n] are pairwise inequivalent)
theorem fmq2 : ¬ drop0% Language.IsRegular.finite_myhillQuotient 2 := fun h => by
  have := @h ℕ W1c1.lnn
  refine not_injective_infinite_finite
    (fun i : ℕ => Quotient.mk (W1c1.lnn.MyhillCongruence.eq) [i]) ?_
  intro i j hij
  have h2 := (Quotient.exact hij [] [i]).1 (show ∃ k, [] ++ [i] ++ [i] = [k, k] from ⟨i, rfl⟩)
  obtain ⟨k, hk⟩ := (h2 : ∃ k, [] ++ [j] ++ [i] = [k, k])
  simp at hk; omega

-- `_private.Cslib.Computability.Languages.ExampleEventuallyZero.0.Cslib.ωLanguage.Example.extend_by_hyp` idx 1: necessary (l = 0)
theorem ebh1 : ¬ drop0% _private.Cslib.Computability.Languages.ExampleEventuallyZero.«0».Cslib.ωLanguage.Example.extend_by_hyp 1 := fun h => by
  obtain ⟨v, -, hv⟩ := @h 0 []
  exact (Language.notMem_zero _) hv

-- `_private.Cslib.Computability.Languages.ExampleEventuallyZero.0.Cslib.ωLanguage.Example.oneSegs_lemma` idx 1: necessary (l = 0: its ω-limit is empty)
theorem osl1 : ¬ indep0% _private.Cslib.Computability.Languages.ExampleEventuallyZero.«0».Cslib.ωLanguage.Example.oneSegs_lemma 1 := fun h => by
  have e := @h 0 0
  rw [Cslib.ωLanguage.omegaLim_zero] at e
  have : (⟨fun _ => 0⟩ : Cslib.ωSequence (Fin 2)) ∈ Cslib.ωLanguage.Example.eventuallyZero :=
    Filter.Eventually.of_forall (fun _ => rfl)
  rw [← e] at this
  exact this

-- `List.allButFirstLast_imp` idx 5: necessary (p = q = false on a 3-element list)
theorem abfi5 : ¬ drop0% List.allButFirstLast_imp 5 := fun h =>
  absurd (@h Unit (fun _ => false) (fun _ => false) [(), (), ()] (fun _ hx => hx) () (by simp)) (by simp)

-- `List.allButFirstLast_append` idx 4: necessary (as = bs = [])
theorem abfa4 : ¬ indep0% List.allButFirstLast_append 4 := fun h =>
  absurd (@h Unit (fun _ => true) [] [] (by simp [List.AllButFirstLast]) (by simp [List.AllButFirstLast])) (by simp)

-- `List.allButFirstLast_append` idx 5: necessary (as = [true, false], bs = [true, true], p = id)
theorem abfa5 : ¬ drop0% List.allButFirstLast_append 5 := fun h =>
  absurd (@h Bool id [true, false] [true, true] (by simp) (by simp [List.AllButFirstLast])
    (by simp [List.AllButFirstLast])) (by simp [List.AllButFirstLast])

-- `List.allButFirstLast_append` idx 6: necessary (as = [true, false, true], bs = [true], p = id)
theorem abfa6 : ¬ drop0% List.allButFirstLast_append 6 := fun h =>
  absurd (@h Bool id [true, false, true] [true] (by simp) rfl
    (by simp [List.AllButFirstLast])) (by simp [List.AllButFirstLast])

-- `List.allButFirstLast_append` idx 7: necessary (as = [true], bs = [true, true, false, true], p = id)
theorem abfa7 : ¬ drop0% List.allButFirstLast_append 7 := fun h =>
  absurd (@h Bool id [true] [true, true, false, true] (by simp) rfl
    (by simp [List.AllButFirstLast])) (by simp [List.AllButFirstLast])

-- `Cslib.LTS.bddLang_bound_zero` idx 6: necessary (xs = [], s = t)
theorem bbz6 : ¬ drop0% Cslib.LTS.bddLang_bound_zero 6 := fun h => by
  obtain ⟨a, -, ha⟩ := (@h Unit 1 W1c1.lE1 0 0 []).1
    ⟨[0], Cslib.LTS.Execution.refl 0, by simp [List.AllButFirstLast]⟩
  simp at ha

-- `Cslib.LTS.bddLang_eq_nfa` idx 6: necessary (r = 0, total LTS on Fin 1: the word [(), ()] needs an interior state)
theorem ben6 : ¬ drop0% Cslib.LTS.bddLang_eq_nfa 6 := fun h => by
  have e := @h Unit 1 (W1c1.lT 1) 0 0 0
  have h2 : [(), ()] ∈ (W1c1.lT 1).bddLang 0 0 0 := by
    rw [e, W1c1.nfa_mem]; exact ⟨0, rfl, 0, rfl, .stepL (s2 := 0) trivial (.stepL (s2 := 0) trivial .refl)⟩
  rw [Cslib.LTS.bddLang_bound_zero _ _ _ (by simp)] at h2
  obtain ⟨a, -, ha⟩ := h2
  simp at ha

-- `Cslib.LTS.splitFirst_mem` idx 8: necessary (no execution: empty LTS, xs = [()], ss = [0, 0, 0])
theorem sfm8 : ¬ drop0% Cslib.LTS.splitFirst_mem 8 := fun h => by
  have := (@h Unit 1 W1c1.lE1 0 0 0 [()] [0, 0, 0] (by simp [List.AllButFirstLast])
    (by simp [List.AllButFirstLast])).1
  rw [show Cslib.LTS.splitFirstTake [()] [(0 : Fin 1), 0, 0] 0 = [()] from rfl] at this
  exact absurd (W1c1.lE1_bdd this) (by simp)

-- `Cslib.LTS.splitFirst_mem` idx 10: necessary (r never visited: xs = [], ss = [0], r = 1)
theorem sfm10 : ¬ drop0% Cslib.LTS.splitFirst_mem 10 := fun h => by
  have := (@h Unit 2 (W1c1.lT 2) 0 0 1 [] [0] (.refl 0) (by simp [List.AllButFirstLast])).1
  rw [show Cslib.LTS.splitFirstTake ([] : List Unit) [(0 : Fin 2)] 1 = [] from rfl] at this
  obtain ⟨ss, hex, -⟩ := this
  exact absurd (W1c1.mtr_nil hex.to_mTr) (by decide)

-- `Cslib.LTS.splitLast_mem` idx 7: necessary (no execution: empty LTS, xs = [()], ss = [0])
theorem slm7 : ¬ drop0% Cslib.LTS.splitLast_mem 7 := fun h => by
  have := (@h Unit 1 W1c1.lE1 0 0 [()] [0] (by simp [List.AllButFirstLast])).2
  rw [show Cslib.LTS.splitLastDrop [()] [(0 : Fin 1)] 0 = [()] from rfl] at this
  exact absurd (W1c1.lE1_bdd this) (by simp)

-- `Cslib.LTS.splitLast_mem` idx 8: necessary (interior state 1 > r = 0 on 0 → 1 → 0)
theorem slm8 : ¬ drop0% Cslib.LTS.splitLast_mem 8 := fun h => by
  have := (@h Unit 2 (W1c1.lT 2) 0 0 [(), ()] [0, 1, 0]
    (.stepL trivial (.stepL trivial (.refl 0)))).2
  change [(), ()] ∈ (W1c1.lT 2).bddLang 0 0 0 at this
  rw [Cslib.LTS.bddLang_bound_zero _ _ _ (by simp)] at this
  obtain ⟨a, -, ha⟩ := this
  simp at ha

-- `Cslib.LTS.splitLastDrop_mem_nonempty` idx 7: necessary (xs = [])
theorem sldm7 : ¬ drop0% Cslib.LTS.splitLastDrop_mem_nonempty 7 := fun h => by
  have := @h Unit 1 W1c1.lE1 0 0 [] [0] (.refl 0) (by simp [List.AllButFirstLast])
  rw [Language.mem_sub] at this
  exact this.2 (by rw [show Cslib.LTS.splitLastDrop ([] : List Unit) [(0 : Fin 1)] 0 = [] from rfl]; exact rfl)

-- `Cslib.LTS.splitLastDrop_mem_nonempty` idx 8: necessary (no execution: empty LTS, xs = [()], ss = [0])
theorem sldm8 : ¬ drop0% Cslib.LTS.splitLastDrop_mem_nonempty 8 := fun h => by
  have := (Language.mem_sub _ _ _).1 (@h Unit 1 W1c1.lE1 0 0 [()] [0] (by simp) (by simp [List.AllButFirstLast]))
  rw [show Cslib.LTS.splitLastDrop [()] [(0 : Fin 1)] 0 = [()] from rfl] at this
  exact absurd (W1c1.lE1_bdd this.1) (by simp)

-- `Cslib.LTS.splitLastDrop_mem_nonempty` idx 9: necessary (interior state 1 > r = 0 on 0 → 1 → 0)
theorem sldm9 : ¬ drop0% Cslib.LTS.splitLastDrop_mem_nonempty 9 := fun h => by
  have := ((Language.mem_sub _ _ _).1 (@h Unit 2 (W1c1.lT 2) 0 0 [(), ()] [0, 1, 0] (by simp)
    (.stepL trivial (.stepL trivial (.refl 0))))).1
  change [(), ()] ∈ (W1c1.lT 2).bddLang 0 0 0 at this
  rw [Cslib.LTS.bddLang_bound_zero _ _ _ (by simp)] at this
  obtain ⟨a, -, ha⟩ := this
  simp at ha

-- `Cslib.LTS.fin_nfa_single_start_accept_eq_regex` idx 2: necessary (Symbol = ℕ is infinite)
theorem fnr2 : ¬ indep0% Cslib.LTS.fin_nfa_single_start_accept_eq_regex 2 := fun h =>
  @not_finite ℕ _ (@h ℕ 1 ⟨fun _ _ _ => False⟩ 0 0)

-- `Cslib.Automata.NA.FinAcc.nfa_single_start_accept_reindex` idx 7: necessary (no start state)
theorem nsar7 : ¬ drop0% Cslib.Automata.NA.FinAcc.nfa_single_start_accept_reindex 7 := fun h => by
  have e := @h Unit Unit Unit ⟨⟨⟨fun _ _ _ => False⟩, ∅⟩, {()}⟩ (Equiv.refl _) () () rfl
  have h2 : [] ∈ Cslib.Automata.Acceptor.language
      (⟨⟨⟨fun _ _ _ => False⟩, ∅⟩, {()}⟩ : Cslib.Automata.NA.FinAcc Unit Unit) := by
    rw [e, W1c1.nfa_mem]; exact ⟨(), rfl, (), rfl, .refl⟩
  rw [W1c1.nfa_mem] at h2
  obtain ⟨_, hs, -⟩ := h2
  exact hs

-- `Cslib.Automata.NA.FinAcc.nfa_single_start_accept_reindex` idx 8: necessary (no accepting state)
theorem nsar8 : ¬ drop0% Cslib.Automata.NA.FinAcc.nfa_single_start_accept_reindex 8 := fun h => by
  have e := @h Unit Unit Unit ⟨⟨⟨fun _ _ _ => False⟩, {()}⟩, ∅⟩ (Equiv.refl _) () () rfl
  have h2 : [] ∈ Cslib.Automata.Acceptor.language
      (⟨⟨⟨fun _ _ _ => False⟩, {()}⟩, ∅⟩ : Cslib.Automata.NA.FinAcc Unit Unit) := by
    rw [e, W1c1.nfa_mem]; exact ⟨(), rfl, (), rfl, .refl⟩
  rw [W1c1.nfa_mem] at h2
  obtain ⟨_, -, _, ht, -⟩ := h2
  exact ht

universe u v in
-- `Cslib.Automata.NA.FinAcc.nfa_single_start_accept_eq_regex` idx 7: removable (Kleene: `Cslib.Automata.NA.FinAcc.nfa_eq_regex` needs no start condition)
theorem nsaer7 : drop% Cslib.Automata.NA.FinAcc.nfa_single_start_accept_eq_regex 7 :=
  fun nfa _ _ _ => Cslib.Automata.NA.FinAcc.nfa_eq_regex nfa

universe u v in
-- `Cslib.Automata.NA.FinAcc.nfa_single_start_accept_eq_regex` idx 8: removable (Kleene: `Cslib.Automata.NA.FinAcc.nfa_eq_regex` needs no accept condition)
theorem nsaer8 : drop% Cslib.Automata.NA.FinAcc.nfa_single_start_accept_eq_regex 8 :=
  fun nfa _ _ _ => Cslib.Automata.NA.FinAcc.nfa_eq_regex nfa

-- `Cslib.Language.IsRegular.iff_regex` idx 1: necessary (alphabet ℕ: ⊤ is regular but no regex mentions every character)
theorem ifr1 : ¬ drop0% Cslib.Language.IsRegular.iff_regex 1 := fun h => by
  obtain ⟨r, hr⟩ := (@h ℕ ⊤).1 Cslib.Language.IsRegular.top
  exact W1c1.no_regex_all ⊤ (fun _ => trivial) r hr

-- `Cslib.Automata.NA.FinAcc.nfa_eq_regex` idx 2: necessary (alphabet ℕ, one-state NFA accepting every word)
theorem ner2 : ¬ drop0% Cslib.Automata.NA.FinAcc.nfa_eq_regex 2 := fun h => by
  obtain ⟨r, hr⟩ := @h ℕ Unit _ W1c1.nTop
  exact W1c1.no_regex_all _ W1c1.nTop_all r hr

-- `Cslib.Automata.NA.FinAcc.nfa_single_start_accept_eq_regex` idx 2: necessary (alphabet ℕ, one-state NFA accepting every word)
theorem nsaer2 : ¬ drop0% Cslib.Automata.NA.FinAcc.nfa_single_start_accept_eq_regex 2 := fun h => by
  obtain ⟨r, hr⟩ := @h ℕ Unit _ W1c1.nTop () () rfl rfl
  exact W1c1.no_regex_all _ W1c1.nTop_all r hr

-- `Cslib.Automata.NA.FinAcc.nfa_eq_regex` idx 3: necessary (counter NFA on ℤ: equal numbers of true and false, not regular)
theorem ner3 : ¬ drop0% Cslib.Automata.NA.FinAcc.nfa_eq_regex 3 := fun h => by
  obtain ⟨r, hr⟩ := @h Bool ℤ _ W1c1.nC
  exact W1c1.nC_nonreg (hr ▸ Cslib.Language.IsRegular.regex r)

-- `Cslib.Automata.NA.FinAcc.nfa_single_start_accept_eq_regex` idx 3: necessary (counter NFA on ℤ, not regular)
theorem nsaer3 : ¬ drop0% Cslib.Automata.NA.FinAcc.nfa_single_start_accept_eq_regex 3 := fun h => by
  obtain ⟨r, hr⟩ := @h Bool ℤ _ W1c1.nC 0 0 rfl rfl
  exact W1c1.nC_nonreg (hr ▸ Cslib.Language.IsRegular.regex r)

-- `Language.eq_zero_or_one_ofIsEmpty` idx 1: necessary (α = Unit, l = {[()]})
theorem ezo1 : ¬ drop0% Language.eq_zero_or_one_ofIsEmpty 1 := fun h => by
  have hm : [()] ∈ ({[()]} : Language Unit) := rfl
  rcases @h Unit {[()]} with e | e <;> rw [e] at hm <;> simp at hm

-- `Language.self_eq_add_mul_iff` idx 4: necessary (l = ⊤, m = 1, n = 0)
theorem seam4 : ¬ drop0% Language.self_eq_add_mul_iff 4 := fun h => by
  have e := (@h Unit ⊤ 1 0).1 (by simp)
  have hm : ([] : List Unit) ∈ (⊤ : Language Unit) := trivial
  rw [e] at hm; simp at hm

-- `Language.IsRegular.finite_nerodeQuotient` idx 2: necessary (alphabet ℕ, l = {[n, n]})
theorem fnq2 : ¬ drop0% Language.IsRegular.finite_nerodeQuotient 2 := fun h => by
  have := @h ℕ W1c1.lnn
  refine not_injective_infinite_finite
    (fun i : ℕ => Quotient.mk (W1c1.lnn.NerodeCongruence.eq) [i]) ?_
  intro i j hij
  obtain ⟨k, hk⟩ := (Quotient.exact hij [i]).1 ⟨i, rfl⟩
  simp at hk; omega

-- `Language.dfa_num_state_ge` idx 4: necessary (two equivalent words, one-state DFA)
theorem dnsg4 : ¬ drop0% Language.dfa_num_state_ge 4 := fun h => by
  have := @h Unit _ {[], [()]} _ Unit _ W1c1.M1 rfl
  rw [Nat.card_coe_set_eq, Set.ncard_pair (by simp)] at this
  simp at this

-- `Language.dfa_num_state_ge` idx 6: necessary (State = ℕ has Nat.card 0, ws = {[]})
theorem dnsg6 : ¬ drop0% Language.dfa_num_state_ge 6 := fun h => by
  have := @h Unit _ {[]} _ (Set.pairwise_singleton _ _) ℕ W1c1.MN rfl
  rw [Nat.card_coe_set_eq, Set.ncard_singleton, Nat.card_eq_zero_of_infinite (α := ℕ)] at this
  simp at this

-- `Language.dfa_num_state_ge` idx 8: necessary (l = 1 separates [] and [()], DFA has one state)
theorem dnsg8 : ¬ drop0% Language.dfa_num_state_ge 8 := fun h => by
  have := @h Unit 1 {[], [()]} _
    (Set.pairwise_pair.2 fun _ => ⟨fun e => by simpa using (e []).1 rfl,
      fun e => by simpa using (e []).2 rfl⟩) Unit _ W1c1.M1
  rw [Nat.card_coe_set_eq, Set.ncard_pair (by simp)] at this
  simp at this

-- `Language.dfa_num_state_min` idx 3: necessary (State = ℕ, empty language: one Nerode class, Nat.card ℕ = 0)
theorem dnsm3 : ¬ drop0% Language.dfa_num_state_min 3 := fun h => by
  have := @h Unit ℕ W1c1.MN
  rw [Nat.card_eq_zero_of_infinite (α := ℕ)] at this
  have hs : Subsingleton (Cslib.Automata.Acceptor.language W1c1.MN).NerodeQuotient :=
    ⟨fun q1 q2 => Quotient.inductionOn₂ q1 q2 fun x y => Quotient.sound fun z =>
      ⟨fun hx => (W1c1.MN_empty _ hx).elim, fun hy => (W1c1.MN_empty _ hy).elim⟩⟩
  have : 0 < Nat.card (Cslib.Automata.Acceptor.language W1c1.MN).NerodeQuotient := Nat.card_pos
  omega

-- `Cslib.Automata.DA.FinAcc.stateCongruence_le_nerodeCongruence` idx 5: necessary (language {[]} separates [] and [()])
theorem sclnc5 : ¬ drop0% Cslib.Automata.DA.FinAcc.stateCongruence_le_nerodeCongruence 5 := fun h => by
  have := (@h Bool Unit W1c1.Mb [] [()] []).1 (show W1c1.Mb.mtr W1c1.Mb.start ([] ++ []) ∈ W1c1.Mb.accept from rfl)
  cases (this : true = false)

-- `Cslib.Automata.DA.FinAcc.unique_minimal` idx 6: necessary (2-state DFA for ⊤, which has one Nerode class)
theorem um6 : ¬ drop0% Cslib.Automata.DA.FinAcc.unique_minimal 6 := fun h => by
  obtain ⟨φ, -, -⟩ := @h Bool Unit W1c1.Mt _ ⊤ Cslib.Language.IsRegular.top
  have hs : Subsingleton (⊤ : Language Unit).NerodeQuotient :=
    ⟨fun q1 q2 => Quotient.inductionOn₂ q1 q2 fun x y => Quotient.sound fun z =>
      ⟨fun _ => trivial, fun _ => trivial⟩⟩
  exact absurd (φ.injective (Subsingleton.elim (φ true) (φ false))) (by decide)

-- `Cslib.Language.IsRegular.compl` idx 2: necessary (l = {[n, n]}ᶜ over ℕ)
theorem rcompl2 : ¬ drop0% Cslib.Language.IsRegular.compl 2 := fun h =>
  W1c1.lnn_nonreg (by simpa using @h ℕ W1c1.lnnᶜ)

-- `Cslib.Language.IsRegular.inf` idx 3: necessary (l1 = {[n, n]} over ℕ, l2 = ⊤)
theorem rinf3 : ¬ drop0% Cslib.Language.IsRegular.inf 3 := fun h =>
  W1c1.lnn_nonreg (by simpa using @h ℕ W1c1.lnn ⊤ Cslib.Language.IsRegular.top)

-- `Cslib.Language.IsRegular.inf` idx 4: necessary (l1 = ⊤, l2 = {[n, n]} over ℕ)
theorem rinf4 : ¬ drop0% Cslib.Language.IsRegular.inf 4 := fun h =>
  W1c1.lnn_nonreg (by simpa using @h ℕ ⊤ W1c1.lnn Cslib.Language.IsRegular.top)

-- `Cslib.Language.IsRegular.add` idx 3: necessary (l1 = {[n, n]} over ℕ, l2 = 0)
theorem radd3 : ¬ drop0% Cslib.Language.IsRegular.add 3 := fun h =>
  W1c1.lnn_nonreg (by simpa using @h ℕ W1c1.lnn 0 Cslib.Language.IsRegular.zero)

-- `Cslib.Language.IsRegular.add` idx 4: necessary (l1 = 0, l2 = {[n, n]} over ℕ)
theorem radd4 : ¬ drop0% Cslib.Language.IsRegular.add 4 := fun h =>
  W1c1.lnn_nonreg (by simpa using @h ℕ 0 W1c1.lnn Cslib.Language.IsRegular.zero)

-- `Cslib.Language.IsRegular.mul` idx 3: necessary (l1 = {[n, n]} over ℕ, l2 = 1)
theorem rmul3 : ¬ drop0% Cslib.Language.IsRegular.mul 3 := fun h =>
  W1c1.lnn_nonreg (by simpa using @h ℕ W1c1.lnn 1 Cslib.Language.IsRegular.one)

-- `Cslib.Language.IsRegular.mul` idx 4: necessary (l1 = 1, l2 = {[n, n]} over ℕ)
theorem rmul4 : ¬ drop0% Cslib.Language.IsRegular.mul 4 := fun h =>
  W1c1.lnn_nonreg (by simpa using @h ℕ 1 W1c1.lnn Cslib.Language.IsRegular.one)

-- `Cslib.Language.IsRegular.iSup` idx 5: necessary (constant family {[n, n]} over ℕ)
theorem risup5 : ¬ drop0% Cslib.Language.IsRegular.iSup 5 := fun h =>
  W1c1.lnn_nonreg (by simpa using @h ℕ Unit _ Set.univ (fun _ => W1c1.lnn))

-- `Cslib.Language.IsRegular.iInf` idx 5: necessary (constant family {[n, n]} over ℕ)
theorem riinf5 : ¬ drop0% Cslib.Language.IsRegular.iInf 5 := fun h =>
  W1c1.lnn_nonreg (by simpa using @h ℕ Unit _ Set.univ (fun _ => W1c1.lnn))

-- `Cslib.Language.IsRegular.iSup` idx 2: necessary (I = ℕ, l n = {[n]} * {[n]}: the union is {[n, n]})
theorem risup2 : ¬ drop0% Cslib.Language.IsRegular.iSup 2 := fun h => by
  have := @h ℕ ℕ Set.univ (fun n => {[n]} * {[n]})
    (fun n _ => Cslib.Language.IsRegular.mul (Cslib.Language.IsRegular.char n) (Cslib.Language.IsRegular.char n))
  rw [W1c1.lnn_eq] at this
  exact W1c1.lnn_nonreg this

-- `Cslib.Language.IsRegular.iInf` idx 2: necessary (I = ℕ, l n = ({[n]} * {[n]})ᶜ: the intersection is {[n, n]}ᶜ)
theorem riinf2 : ¬ drop0% Cslib.Language.IsRegular.iInf 2 := fun h => by
  have := @h ℕ ℕ Set.univ (fun n => ({[n]} * {[n]})ᶜ)
    (fun n _ => Cslib.Language.IsRegular.compl (Cslib.Language.IsRegular.mul (Cslib.Language.IsRegular.char n) (Cslib.Language.IsRegular.char n)))
  have e : (⨅ i ∈ (Set.univ : Set ℕ), ({[i]} * {[i]} : Language ℕ)ᶜ) = W1c1.lnnᶜ := by
    rw [← W1c1.lnn_eq]; simp [compl_iSup]
  rw [e] at this
  exact W1c1.lnn_nonreg (by simpa using this.compl)

-- `Cslib.Language.IsRegular.kstar` idx 2: necessary (l = {[n, n]} over ℕ: l∗ is not regular)
theorem rkstar2 : ¬ drop0% Cslib.Language.IsRegular.kstar 2 := fun h =>
  W1c1.lnn_kstar_nonreg (@h ℕ W1c1.lnn)

-- `Cslib.Language.IsRegular.reverse` idx 2: necessary (l = {[n, n]} over ℕ)
theorem rrev2 : ¬ drop0% Cslib.Language.IsRegular.reverse 2 := fun h =>
  W1c1.lnn_nonreg (Cslib.Language.IsRegular.reverse_iff.1 (@h ℕ W1c1.lnn))

-- `Cslib.Language.IsRegular.preimage` idx 4: necessary (identity homomorphism, l = {[n, n]} over ℕ)
theorem rpre4 : ¬ drop0% Cslib.Language.IsRegular.preimage 4 := fun h =>
  W1c1.lnn_nonreg (@h ℕ ℕ W1c1.idH W1c1.lnn)

-- `Cslib.Language.IsRegular.congr_fin_index` idx 2: necessary (Myhill congruence of {[n, n]} over ℕ: the class of [0, 0] is {[n, n]})
theorem rcfi2 : ¬ drop0% Cslib.Language.IsRegular.congr_fin_index 2 := fun h => by
  have := @h ℕ W1c1.lnn.MyhillCongruence.toRightCongruence
    (Quotient.mk W1c1.lnn.MyhillCongruence.eq [0, 0])
  refine W1c1.nonreg_of _ (fun i => ?_) (fun i j hj => ?_) this
  · show Quotient.mk _ _ = Quotient.mk _ _
    exact Quotient.sound fun x z => by rw [W1c1.lnn_mid, W1c1.lnn_mid]; simp
  · have := (Quotient.exact hj [] []).2 ⟨0, rfl⟩
    simp at this
    obtain ⟨k, hk⟩ := this
    simp at hk; omega

-- `Language.Hom.ext` idx 4: necessary (identity and erasing homomorphisms on Unit)
theorem hext4 : ¬ drop0% Language.Hom.ext 4 := fun h => by
  have := congrArg (fun f : Language.Hom Unit Unit => f.toFun [()])
    (@h Unit Unit ⟨id, rfl, fun _ _ => rfl⟩ ⟨fun _ => [], rfl, fun _ _ => rfl⟩)
  simp at this

-- `RegularExpression.iSup_matches'` idx 5: necessary (alphabet ℕ, constant family ⊤)
theorem rism5 : ¬ drop0% RegularExpression.iSup_matches' 5 := fun h => by
  obtain ⟨r, hr⟩ := @h ℕ Unit _ Set.univ (fun _ => ⊤)
  exact W1c1.no_regex_single _ (fun n => by simp; trivial) r hr

-- `RegularExpression.iSup_matches'` idx 2: necessary (I = ℕ, l n = {[n]}: the union mentions every character)
theorem rism2 : ¬ drop0% RegularExpression.iSup_matches' 2 := fun h => by
  obtain ⟨r, hr⟩ := @h ℕ ℕ Set.univ (fun n => {[n]}) (fun n _ => ⟨.char n, by simp⟩)
  exact W1c1.no_regex_single _ (fun n => Language.mem_iSup.2 ⟨n, Language.mem_iSup.2 ⟨trivial, rfl⟩⟩) r hr

-- `Cslib.ωLanguage.ext` idx 3: necessary (⊤ ≠ ⊥ over Unit)
theorem oext3 : ¬ drop0% Cslib.ωLanguage.ext 3 := fun h => W1c1.top_ne_bot (@h Unit ⊤ ⊥)

-- `Cslib.ωLanguage.eq_bot_ofIsEmpty` idx 1: necessary (⊤ over Unit)
theorem oebe1 : ¬ drop0% Cslib.ωLanguage.eq_bot_ofIsEmpty 1 := fun h => W1c1.top_ne_bot (@h Unit ⊤)

-- `Cslib.ωLanguage.mem_ext` idx 3: necessary (⊤ ≠ ⊥ over Unit)
theorem omext3 : ¬ drop0% Cslib.ωLanguage.mem_ext 3 := fun h => W1c1.top_ne_bot (@h Unit ⊤ ⊥)

-- `Cslib.ωLanguage.append_mem_hmul` idx 5: necessary (l = 0, p = ⊤)
theorem oamh5 : ¬ drop0% Cslib.ωLanguage.append_mem_hmul 5 := fun h =>
  W1c1.zero_hmul _ (@h Unit 0 ⊤ [] W1c1.u0 (Cslib.ωLanguage.mem_top _))

-- `Cslib.ωLanguage.append_mem_hmul` idx 6: necessary (l = 1, p = ⊥)
theorem oamh6 : ¬ drop0% Cslib.ωLanguage.append_mem_hmul 6 := fun h =>
  W1c1.hmul_bot _ (@h Unit 1 ⊥ [] W1c1.u0 Language.nil_mem_one)

-- `Cslib.ωLanguage.flatten_mem_omegaPow` idx 4: necessary (l = 0)
theorem ofmo4 : ¬ drop0% Cslib.ωLanguage.flatten_mem_omegaPow 4 := fun h =>
  W1c1.zero_omegaPow _ (@h Unit 0 _ ⟨fun _ => [()]⟩)

-- `Cslib.ωLanguage.le_hmul_congr` idx 5: necessary (l1 = 1, l2 = 0, p1 = p2 = ⊤)
theorem olhc5 : ¬ drop0% Cslib.ωLanguage.le_hmul_congr 5 := fun h =>
  W1c1.zero_hmul _ (@h Unit 1 0 ⊤ ⊤ le_rfl _ (W1c1.one_hmul_top W1c1.u0))

-- `Cslib.ωLanguage.le_hmul_congr` idx 6: necessary (l1 = l2 = 1, p1 = ⊤, p2 = ⊥)
theorem olhc6 : ¬ drop0% Cslib.ωLanguage.le_hmul_congr 6 := fun h =>
  W1c1.hmul_bot _ (@h Unit 1 1 ⊤ ⊥ le_rfl _ (W1c1.one_hmul_top W1c1.u0))

-- `Cslib.ωLanguage.le_omegaPow_congr` idx 4: necessary (l1 = ⊤, l2 = 0)
theorem oloc4 : ¬ drop0% Cslib.ωLanguage.le_omegaPow_congr 4 := fun h =>
  W1c1.zero_omegaPow _ (@h Unit _ ⊤ 0 _ W1c1.top_omegaPow)

-- `Cslib.ωLanguage.omegaPow_of_le_one` idx 3: necessary (l = ⊤)
theorem opolo3 : ¬ drop0% Cslib.ωLanguage.omegaPow_of_le_one 3 := fun h => by
  have m : _ ∈ (⊤ : Language Unit)^ω := W1c1.top_omegaPow
  rw [@h Unit ⊤ _] at m
  exact m

-- `Cslib.ωLanguage.omegaPow_eq_empty` idx 3: necessary (l = ⊤)
theorem opee3 : ¬ drop0% Cslib.ωLanguage.omegaPow_eq_empty 3 := fun h => by
  have := @h Unit ⊤ _ [()] trivial
  exact absurd ((Language.mem_one _).1 this) (by simp)

-- `Cslib.ωLanguage.omegaPow_coind'` idx 4: necessary (l = 1, p = ⊤)
theorem opci4 : ¬ drop0% Cslib.ωLanguage.omegaPow_coind' 4 := fun h => by
  have := @h Unit 1 ⊤ _ (fun s _ => W1c1.one_hmul_top s) W1c1.u0 (Cslib.ωLanguage.mem_top _)
  obtain ⟨xs, -, hx⟩ := Cslib.ωLanguage.mem_omegaPow.1 this
  have := (Language.mem_sub _ _ _).1 (hx 0)
  exact this.2 this.1

-- `Cslib.ωLanguage.omegaPow_coind'` idx 5: necessary (l = 0, p = ⊤)
theorem opci5 : ¬ drop0% Cslib.ωLanguage.omegaPow_coind' 5 := fun h =>
  W1c1.zero_omegaPow _ (@h Unit 0 ⊤ _ (Language.notMem_zero _) W1c1.u0 (Cslib.ωLanguage.mem_top _))

-- `Cslib.ωLanguage.omegaPow_coind` idx 4: necessary (l = 0, p = ⊤)
theorem opc4 : ¬ drop0% Cslib.ωLanguage.omegaPow_coind 4 := fun h =>
  W1c1.zero_omegaPow _ (@h Unit 0 ⊤ _ W1c1.u0 (Cslib.ωLanguage.mem_top _))

-- `_private.Cslib.Computability.Languages.OmegaRegularLanguage.0.Cslib.ωLanguage.isRegular_iff.helper` idx 2: necessary (p = sequences over ℕ with equal first two letters, not ω-regular)
theorem irh2 : ¬ drop0% _private.Cslib.Computability.Languages.OmegaRegularLanguage.«0».Cslib.ωLanguage.isRegular_iff.helper 2 :=
  fun h => W1c1.p0_nonreg (@h ℕ W1c1.p0)

-- `Cslib.ωLanguage.IsRegular.sup` idx 3: necessary (p1 = equal-first-two-letters over ℕ, p2 = ⊥)
theorem ors3 : ¬ drop0% Cslib.ωLanguage.IsRegular.sup 3 := fun h =>
  W1c1.p0_nonreg (by simpa using @h ℕ W1c1.p0 ⊥ Cslib.ωLanguage.IsRegular.bot)

-- `Cslib.ωLanguage.IsRegular.sup` idx 4: necessary (p1 = ⊥, p2 = equal-first-two-letters over ℕ)
theorem ors4 : ¬ drop0% Cslib.ωLanguage.IsRegular.sup 4 := fun h =>
  W1c1.p0_nonreg (by simpa using @h ℕ ⊥ W1c1.p0 Cslib.ωLanguage.IsRegular.bot)

-- `Cslib.ωLanguage.IsRegular.inf` idx 3: necessary (p1 = equal-first-two-letters over ℕ, p2 = ⊤)
theorem ori3 : ¬ drop0% Cslib.ωLanguage.IsRegular.inf 3 := fun h =>
  W1c1.p0_nonreg (by simpa using @h ℕ W1c1.p0 ⊤ Cslib.ωLanguage.IsRegular.top)

-- `Cslib.ωLanguage.IsRegular.inf` idx 4: necessary (p1 = ⊤, p2 = equal-first-two-letters over ℕ)
theorem ori4 : ¬ drop0% Cslib.ωLanguage.IsRegular.inf 4 := fun h =>
  W1c1.p0_nonreg (by simpa using @h ℕ ⊤ W1c1.p0 Cslib.ωLanguage.IsRegular.top)

-- `Cslib.ωLanguage.IsRegular.iSup` idx 5: necessary (constant family: equal-first-two-letters over ℕ)
theorem orisup5 : ¬ drop0% Cslib.ωLanguage.IsRegular.iSup 5 := fun h =>
  W1c1.p0_nonreg (by simpa using @h ℕ Unit _ Set.univ (fun _ => W1c1.p0))

-- `Cslib.ωLanguage.IsRegular.iInf` idx 5: necessary (constant family: equal-first-two-letters over ℕ)
theorem oriinf5 : ¬ drop0% Cslib.ωLanguage.IsRegular.iInf 5 := fun h =>
  W1c1.p0_nonreg (by simpa using @h ℕ Unit _ Set.univ (fun _ => W1c1.p0))

-- `Cslib.ωLanguage.IsRegular.hmul` idx 3: necessary (l = {[n, n]} over ℕ, p = ⊤)
theorem orh3 : ¬ drop0% Cslib.ωLanguage.IsRegular.hmul 3 := fun h =>
  W1c1.p0_nonreg (@h ℕ W1c1.lnn ⊤ Cslib.ωLanguage.IsRegular.top)

-- `Cslib.ωLanguage.IsRegular.hmul` idx 4: necessary (l = 1, p = equal-first-two-letters over ℕ)
theorem orh4 : ¬ drop0% Cslib.ωLanguage.IsRegular.hmul 4 := fun h =>
  W1c1.p0_nonreg (by simpa [Cslib.ωLanguage.one_hmul] using @h ℕ 1 W1c1.p0 Cslib.Language.IsRegular.one)

-- `Cslib.ωLanguage.IsRegular.compl` idx 3: necessary (p = complement of equal-first-two-letters over ℕ)
theorem orc3 : ¬ drop0% Cslib.ωLanguage.IsRegular.compl 3 := fun h =>
  W1c1.p0_nonreg (by simpa using @h ℕ _ W1c1.p0ᶜ)

-- `Cslib.ωLanguage.IsRegular.fin_cover_saturates` idx 5: necessary (cover {⊤}, q = equal-first-two-letters over ℕ)
theorem ofcs5 : ¬ drop0% Cslib.ωLanguage.IsRegular.fin_cover_saturates 5 := fun h =>
  W1c1.p0_nonreg (@h ℕ Unit _ (fun _ => ⊤) W1c1.p0 (by simp) (fun _ => Cslib.ωLanguage.IsRegular.top))

-- `Cslib.ωLanguage.IsRegular.fin_cover_saturates_compl` idx 5: necessary (cover {⊤}, q = complement of equal-first-two-letters over ℕ)
theorem ofcsc5 : ¬ drop0% Cslib.ωLanguage.IsRegular.fin_cover_saturates_compl 5 := fun h => by
  have := @h ℕ Unit _ (fun _ => ⊤) W1c1.p0ᶜ (by simp) (fun _ => Cslib.ωLanguage.IsRegular.top)
  exact W1c1.p0_nonreg (by simpa using this)

-- `Cslib.ωLanguage.IsRegular.fin_cover_saturates` idx 6: necessary (family {⊥} is no cover, q = equal-first-two-letters over ℕ)
theorem ofcs6 : ¬ drop0% Cslib.ωLanguage.IsRegular.fin_cover_saturates 6 := fun h =>
  W1c1.p0_nonreg (@h ℕ Unit _ (fun _ => ⊥) W1c1.p0 (fun _ ⟨_, hx, _⟩ => (show False from hx).elim)
    (fun _ => Cslib.ωLanguage.IsRegular.bot))

-- `Cslib.ωLanguage.IsRegular.fin_cover_saturates_compl` idx 6: necessary (family {⊥} is no cover, q = complement of equal-first-two-letters)
theorem ofcsc6 : ¬ drop0% Cslib.ωLanguage.IsRegular.fin_cover_saturates_compl 6 := fun h => by
  have := @h ℕ Unit _ (fun _ => ⊥) W1c1.p0ᶜ
    (fun _ ⟨_, hx, _⟩ => (show False from hx).elim) (fun _ => Cslib.ωLanguage.IsRegular.bot)
  exact W1c1.p0_nonreg (by simpa using this)

-- `Cslib.ωLanguage.IsRegular.fin_cover_saturates` idx 7: necessary (cover {p0, p0ᶜ} with p0 = equal-first-two-letters, q = p0)
theorem ofcs7 : ¬ drop0% Cslib.ωLanguage.IsRegular.fin_cover_saturates 7 := fun h => by
  refine W1c1.p0_nonreg (@h ℕ Bool _ (fun b => if b then W1c1.p0 else W1c1.p0ᶜ) W1c1.p0 ?_ ?_)
  · rintro (_ | _) ⟨x, h1, h2⟩
    · exact absurd h2 h1
    · exact subset_rfl
  · rw [iSup_bool_eq]; simp
-- `Cslib.ωLanguage.IsRegular.fin_cover_saturates_compl` idx 7: necessary (cover {p0, p0ᶜ}, q = p0ᶜ)
theorem ofcsc7 : ¬ drop0% Cslib.ωLanguage.IsRegular.fin_cover_saturates_compl 7 := fun h => by
  have := @h ℕ Bool _ (fun b => if b then W1c1.p0 else W1c1.p0ᶜ) W1c1.p0ᶜ ?_ ?_
  · exact W1c1.p0_nonreg (by simpa using this)
  · rintro (_ | _) ⟨x, h1, h2⟩
    · exact subset_rfl
    · exact absurd h1 h2
  · rw [iSup_bool_eq]; simp

-- `Cslib.Automata.DA.FinAcc.unique_minimal` idx 3: removable (regularity makes the Nerode quotient finite and nonempty, so Nat.card State ≠ 0 forces State finite)
theorem um3 : drop% Cslib.Automata.DA.FinAcc.unique_minimal 3 := @fun State α M l hr hm => by
  have : Finite l.NerodeQuotient := Language.IsRegular.finite_nerodeQuotient hr
  have : Finite State := Nat.finite_of_card_ne_zero (by rw [hm.2]; exact Nat.card_pos.ne')
  exact Cslib.Automata.DA.FinAcc.unique_minimal l hr hm

-- `Cslib.Automata.DA.FinAcc.unique_minimal` idx 5: removable (a finite DFA accepting l makes l regular)
theorem um5 : drop% Cslib.Automata.DA.FinAcc.unique_minimal 5 := @fun State α M _ l hm => by
  have hr : (Cslib.Automata.Acceptor.language M).IsRegular :=
    Language.isRegular_iff.2 ⟨State, Fintype.ofFinite State, ⟨M.tr, M.start, M.accept⟩, rfl⟩
  exact Cslib.Automata.DA.FinAcc.unique_minimal l (hm.1 ▸ hr) hm

-- `Cslib.ωLanguage.IsRegular.iSup` idx 2: necessary (I = ℕ, p n = {[n]} * {[n]} * ⊤: the union is not ω-regular)
theorem orisup2 : ¬ drop0% Cslib.ωLanguage.IsRegular.iSup 2 := fun h => by
  have := @h ℕ ℕ Set.univ W1c1.pn (fun n _ => W1c1.pn_reg n)
  exact W1c1.qS_nonreg (by simpa using this)

-- `Cslib.ωLanguage.IsRegular.iInf` idx 2: necessary (I = ℕ, p n = ({[n]} * {[n]} * ⊤)ᶜ)
theorem oriinf2 : ¬ drop0% Cslib.ωLanguage.IsRegular.iInf 2 := fun h => by
  have := @h ℕ ℕ Set.univ (fun n => (W1c1.pn n)ᶜ) (fun n _ => (W1c1.pn_reg n).compl)
  exact W1c1.qS_nonreg (by simpa [← compl_iSup] using this.compl)

-- `Cslib.ωLanguage.IsRegular.regular_omegaLim` idx 2: necessary (l = words starting with two equal letters over ℕ)
theorem orrol2 : ¬ drop0% Cslib.ωLanguage.IsRegular.regular_omegaLim 2 := fun h =>
  W1c1.lpre_lim_nonreg (@h ℕ W1c1.lpre)

-- `Cslib.ωLanguage.IsRegular.omegaPow` idx 3: necessary (l = {[n, n]} over ℕ: l^ω is not ω-regular)
theorem orop3 : ¬ drop0% Cslib.ωLanguage.IsRegular.omegaPow 3 := fun h =>
  W1c1.lnn_omegaPow_nonreg (@h ℕ _ W1c1.lnn)

-- `Cslib.ωLanguage.IsRegular.fin_cover_saturates` idx 2: necessary (infinite cover by first two letters over ℕ saturating equal-first-two-letters)
theorem ofcs2 : ¬ drop0% Cslib.ωLanguage.IsRegular.fin_cover_saturates 2 := fun h =>
  W1c1.p0_nonreg (@h ℕ (ℕ × ℕ) W1c1.pab W1c1.p0 W1c1.pab_sat W1c1.pab_cover W1c1.pab_reg)

-- `Cslib.ωLanguage.IsRegular.fin_cover_saturates_compl` idx 2: necessary (same infinite cover; complement not ω-regular)
theorem ofcsc2 : ¬ drop0% Cslib.ωLanguage.IsRegular.fin_cover_saturates_compl 2 := fun h =>
  W1c1.p0c_nonreg (@h ℕ (ℕ × ℕ) W1c1.pab W1c1.p0 W1c1.pab_sat W1c1.pab_cover W1c1.pab_reg)

-- `Cslib.Automata.NA.Buchi.buchiFamily_cover` idx 4: necessary (infinite automaton remembering the input: families are ultimately periodic words, which miss 0, 1, 2, ...)
theorem bfc4 : ¬ drop0% Cslib.Automata.NA.Buchi.buchiFamily_cover 4 := fun h => by
  have e := @h ℕ (List ℕ) W1c1.bL _
  have hm : (⟨fun k => k⟩ : Cslib.ωSequence ℕ) ∈ (⨆ i, W1c1.bL.buchiFamily i) := by
    rw [e]; exact Cslib.ωLanguage.mem_top _
  obtain ⟨⟨a, b⟩, hi⟩ := Cslib.ωLanguage.mem_iSup.1 hm
  obtain ⟨xl, xls, -, hk, he⟩ := Cslib.Automata.NA.Buchi.mem_buchiFamily.1 hi
  have hk' : ∀ k, xls k = xls 0 ∧ xls 0 ≠ [] := fun k => by
    have h1 := (Language.mem_sub_one _).1 (hk k)
    have h2 := (Language.mem_sub_one _).1 (hk 0)
    refine ⟨W1c1.bL_eq (Quotient.exact (h1.1.trans h2.1.symm)), h2.2⟩
  have hpos : ∀ k, 0 < (xls k).length := fun k => by
    rw [(hk' k).1]; exact List.length_pos_iff.2 (hk' 0).2
  have hpos' : ∀ k, 0 < (xls.tail k).length := fun k => hpos (k + 1)
  set w := xls 0 with hw
  have hF := Cslib.ωSequence.cons_flatten hpos
  have hT := Cslib.ωSequence.cons_flatten hpos'
  have p0 := congrArg (fun z : Cslib.ωSequence ℕ => z xl.length) he
  have p1 := congrArg (fun z : Cslib.ωSequence ℕ => z (xl.length + w.length)) he
  rw [Cslib.ωSequence.get_append_length, ← hF] at p0
  rw [Cslib.ωSequence.get_append_right, ← hF] at p1
  change (w ++ω xls.tail.flatten) 0 = xl.length at p0
  change (w ++ω xls.tail.flatten) (w.length + 0) = xl.length + w.length at p1
  rw [Cslib.ωSequence.get_append_right, ← hT] at p1
  change (xls 1 ++ω _) 0 = _ at p1
  rw [(hk' 1).1, Cslib.ωSequence.get_append_left _ _ _ (hpos 0)] at p1
  rw [Cslib.ωSequence.get_append_left _ _ _ (hpos 0)] at p0
  have := List.length_pos_iff.2 (hk' 0).2
  omega

-- `Cslib.ωLanguage.IsRegular.of_da_buchi` idx 2: necessary (infinite DA remembering the input, accepting words starting with two equal letters over ℕ)
theorem orodb2 : ¬ drop0% Cslib.ωLanguage.IsRegular.of_da_buchi 2 := fun h =>
  W1c1.lpre_lim_nonreg (W1c1.dL_lang ▸ @h ℕ (List ℕ) W1c1.dL)
