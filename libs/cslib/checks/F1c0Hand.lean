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

/-! # F1c0: the 16 FLP rows that keep `hpc1 : a.PseudoConsensus 1`

A concrete algorithm with `PseudoConsensus 1`: single-decree Paxos for 3 processes.
* Ballot `b` belongs to process `b % 3`. On its self-addressed `tick` a process starts a fresh ballot
  above everything it has seen, promises it to itself, and sends `prepare b` to the other two.
* An acceptor promises a strictly higher ballot and reports its latest vote (`promise b acc`).
* The owner, on the first promise for its current ballot, votes for the value of the highest
  reported vote (its own or the promiser's; else its input) and sends `accept b v` to the others.
* An acceptor votes for `accept b v` if `b ≥ prom` and decides `v` at once: the owner has already
  voted `(b, v)`, so the owner and the acceptor form a quorum (any two of three processes).
Votes are kept as ghost history (`votes`) so that the Paxos invariant `SafeAt` is expressible. -/

namespace F1c0
open Cslib Cslib.FLP

abbrev Pr := Fin 3

inductive Msg where
  | tick
  | prepare (b : ℕ)
  | promise (b : ℕ) (r : Option (ℕ × Bool))
  | accept (b : ℕ) (v : Bool)
  deriving DecidableEq

structure PS where
  inp : Option Bool
  prom : ℕ
  cur : ℕ
  sent : Bool
  acc : Option (ℕ × Bool)
  votes : List (ℕ × Bool)

def PS.init : PS := ⟨none, 0, 0, false, none, []⟩

def owner (b : ℕ) : Pr := ⟨b % 3, Nat.mod_lt _ (by decide)⟩
def nextBallot (p : Pr) (x : ℕ) : ℕ := 3 * (x / 3 + 1) + p.val
abbrev Mg := Message Pr Msg
def bcast (me : Pr) (k : Msg) : Multiset Mg :=
  (Finset.univ.erase me).val.map (fun d => (⟨d, .inr k⟩ : Mg))

def best : Option (ℕ × Bool) → Option (ℕ × Bool) → Option (ℕ × Bool)
  | some x, some y => if x.1 < y.1 then some y else some x
  | some x, none => some x
  | none, o => o

-- one step of process `me`: new internal state, messages sent, decision
def handle (me : Pr) : Bool ⊕ Msg → PS → PS × Multiset Mg × Option Bool
  | .inl x, st =>
    if st.inp = none then ({st with inp := some x}, {⟨me, .inr .tick⟩}, none) else (st, 0, none)
  | .inr .tick, st =>
    let b := nextBallot me (max st.prom st.cur)
    ({st with cur := b, prom := b, sent := false}, ⟨me, .inr .tick⟩ ::ₘ bcast me (.prepare b), none)
  | .inr (.prepare b), st =>
    if st.prom < b then ({st with prom := b}, {⟨owner b, .inr (.promise b st.acc)⟩}, none)
    else (st, 0, none)
  | .inr (.promise b r), st =>
    if st.cur = b ∧ st.prom = b ∧ st.sent = false ∧ st.inp ≠ none then
      let v := ((best st.acc r).map Prod.snd).getD (st.inp.getD false)
      ({st with sent := true, acc := some (b, v), votes := (b, v) :: st.votes},
        bcast me (.accept b v), none)
    else (st, 0, none)
  | .inr (.accept b v), st =>
    if st.prom ≤ b then ({st with prom := b, acc := some (b, v), votes := (b, v) :: st.votes}, 0, some v)
    else (st, 0, none)

def alg : Algorithm Pr Msg PS where
  init _ := PS.init
  next m ps := (handle m.dest m.msg ps.state).1
  send m ps := (handle m.dest m.msg ps.state).2.1
  out m ps := (handle m.dest m.msg ps.state).2.2

abbrev St := State Pr Msg PS
abbrev V (s : St) (y : Pr) : List (ℕ × Bool) := (s.proc y).state.votes
abbrev Pm (s : St) (y : Pr) : ℕ := (s.proc y).state.prom

/-! ## Step helpers -/

theorem recv_msgs (m : Mg) (s : St) :
    (alg.recvMsg m s).msgs = s.msgs.erase m + (handle m.dest m.msg (s.proc m.dest).state).2.1 := rfl

theorem recv_proc_ne {m : Mg} {s : St} {y : Pr} (hy : y ≠ m.dest) : (alg.recvMsg m s).proc y = s.proc y := by
  simp [Algorithm.recvMsg, hy]

theorem recv_proc_eq (m : Mg) (s : St) : (alg.recvMsg m s).proc m.dest =
    ⟨(handle m.dest m.msg (s.proc m.dest).state).1,
      if (s.proc m.dest).out.isNone then (handle m.dest m.msg (s.proc m.dest).state).2.2
      else (s.proc m.dest).out⟩ := by
  simp [Algorithm.recvMsg, alg]

theorem via1 {ps : Set Pr} {m : Mg} {s : St} (hd : m.dest ∈ ps) (hm : m ∈ s.msgs) :
    alg.CanReachVia ps s (alg.recvMsg m s) := .single ⟨some m, hd, hm, rfl⟩

-- if no message to `ps` is ever in flight, `ps` alone cannot move
theorem via_eq {ps : Set Pr} {J : St → Prop} (hJ : ∀ s x s', J s → alg.lts.Tr s x s' → J s')
    (hno : ∀ u, J u → ∀ m ∈ u.msgs, m.dest ∉ ps) {t t' : St} (ht : J t)
    (h : alg.CanReachVia ps t t') : t' = t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hst _ ih =>
    obtain ⟨x, hx, htr⟩ := hst
    cases x with
    | none => rw [ih (by rwa [← Algorithm.tr_none htr])]; exact (Algorithm.tr_none htr).symm
    | some m => exact absurd hx (hno _ ht m htr.1)

-- what each message kind does
theorem h_inl_out (me : Pr) (x : Bool) (st : PS) : (handle me (.inl x) st).2.2 = none := by
  simp only [handle]; split <;> rfl
theorem h_tick_out (me : Pr) (st : PS) : (handle me (.inr .tick) st).2.2 = none := rfl
theorem h_prep_out (me : Pr) (b : ℕ) (st : PS) : (handle me (.inr (.prepare b)) st).2.2 = none := by
  simp only [handle]; split <;> rfl
theorem h_prep_send (me : Pr) (b : ℕ) (st : PS) : (handle me (.inr (.prepare b)) st).2.1 =
    if st.prom < b then {⟨owner b, .inr (.promise b st.acc)⟩} else 0 := by
  simp only [handle]; split <;> rfl
theorem h_prep_st (me : Pr) (b : ℕ) (st : PS) : (handle me (.inr (.prepare b)) st).1 =
    if st.prom < b then {st with prom := b} else st := by
  simp only [handle]; split <;> rfl
theorem h_prom_out (me : Pr) (b : ℕ) (r) (st : PS) : (handle me (.inr (.promise b r)) st).2.2 = none := by
  simp only [handle]; split <;> rfl
theorem h_prom_ign {me : Pr} {b : ℕ} {r} {st : PS}
    (h : ¬ (st.cur = b ∧ st.prom = b ∧ st.sent = false ∧ st.inp ≠ none)) :
    handle me (.inr (.promise b r)) st = (st, 0, none) := by
  simp only [handle]; rw [ite_eq_right_iff.2 (fun h' => absurd h' h)]
theorem h_acc_send (me : Pr) (b : ℕ) (v : Bool) (st : PS) : (handle me (.inr (.accept b v)) st).2.1 = 0 := by
  simp only [handle]; split <;> rfl
theorem h_acc_out (me : Pr) (b : ℕ) (v : Bool) (st : PS) : (handle me (.inr (.accept b v)) st).2.2 =
    if st.prom ≤ b then some v else none := by
  simp only [handle]; split <;> rfl
theorem h_acc_ign {me : Pr} {b : ℕ} {v : Bool} {st : PS} (h : ¬ st.prom ≤ b) :
    handle me (.inr (.accept b v)) st = (st, 0, none) := by
  simp only [handle]; rw [ite_eq_right_iff.2 (fun h' => absurd h' h)]

theorem recv_out_ne {m : Mg} {s : St} {b : Bool} (ho : ∀ y, (s.proc y).out ≠ some b)
    (hn : (handle m.dest m.msg (s.proc m.dest).state).2.2 ≠ some b) :
    ∀ y, ((alg.recvMsg m s).proc y).out ≠ some b := by
  intro y
  by_cases hy : y = m.dest
  · subst hy; rw [recv_proc_eq]; dsimp only; split
    · exact hn
    · exact ho _
  · rw [recv_proc_ne hy]; exact ho y

theorem mem_recv {m m' : Mg} {s : St} (h : m' ∈ (alg.recvMsg m s).msgs) :
    m' ∈ s.msgs ∨ m' ∈ (handle m.dest m.msg (s.proc m.dest).state).2.1 := by
  rw [recv_msgs, Multiset.mem_add] at h
  exact h.imp_left Multiset.mem_of_mem_erase

theorem recv_dest (d : Pr) (x : Bool ⊕ Msg) (s : St) : (alg.recvMsg ⟨d, x⟩ s).proc d =
    ⟨(handle d x (s.proc d).state).1,
      if (s.proc d).out.isNone then (handle d x (s.proc d).state).2.2 else (s.proc d).out⟩ :=
  recv_proc_eq _ _

theorem mem_send {m m' : Mg} {s : St} (h : m' ∈ (handle m.dest m.msg (s.proc m.dest).state).2.1) :
    m' ∈ (alg.recvMsg m s).msgs := by
  rw [recv_msgs]; exact Multiset.mem_add.2 (Or.inr h)

theorem owner_next (p : Pr) (x : ℕ) : owner (nextBallot p x) = p := by
  ext; simp only [owner, nextBallot]; omega

theorem lt_next (p : Pr) (x : ℕ) : x < nextBallot p x := by
  simp only [nextBallot]; omega

theorem mem_bcast {me d : Pr} {k : Msg} (h : d ≠ me) : (⟨d, .inr k⟩ : Mg) ∈ bcast me k :=
  Multiset.mem_map.2 ⟨d, by rw [Finset.mem_val]; exact Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩, rfl⟩

/-! ## Safety invariant -/

-- no quorum can still choose a value other than `v` at a ballot below `b`
def SafeAt (s : St) (b : ℕ) (v : Bool) : Prop :=
  ∀ c < b, ∃ y z, y ≠ z ∧ c < Pm s y ∧ c < Pm s z ∧
    (∀ w, (c, w) ∈ V s y → w = v) ∧ (∀ w, (c, w) ∈ V s z → w = v)

-- a promise for `b` carrying `r` was sent by some non-owner `x` whose highest vote below `b` is `r`
def PromOK (s : St) (b : ℕ) (r : Option (ℕ × Bool)) : Prop :=
  ∃ x, x ≠ owner b ∧ b ≤ Pm s x ∧
    (∀ c w, (c, w) ∈ V s x → c < b → ∃ c' w', r = some (c', w') ∧ c ≤ c') ∧
    (∀ c' w', r = some (c', w') → (c', w') ∈ V s x ∧ c' < b)

structure Inv (inp : Pr → Bool) (s : St) : Prop where
  inl_ok : ∀ m ∈ s.msgs, ∀ x, m.msg = .inl x → x = inp m.dest
  inp_ok : ∀ y x, (s.proc y).state.inp = some x → x = inp y
  live : ∀ y, ((s.proc y).state.inp = none ∧ (⟨y, .inl (inp y)⟩ : Mg) ∈ s.msgs) ∨
    ((s.proc y).state.inp ≠ none ∧ (⟨y, .inr .tick⟩ : Mg) ∈ s.msgs)
  votes_le : ∀ y c w, (c, w) ∈ V s y → c ≤ Pm s y
  cur_le : ∀ y, (s.proc y).state.cur ≤ Pm s y
  acc_none : ∀ y, (s.proc y).state.acc = none → V s y = []
  acc_some : ∀ y c w, (s.proc y).state.acc = some (c, w) → (c, w) ∈ V s y ∧ ∀ c' w', (c', w') ∈ V s y → c' ≤ c
  own_votes : ∀ y c w, (c, w) ∈ V s y → owner c = y →
    c ≤ (s.proc y).state.cur ∧ (c = (s.proc y).state.cur → (s.proc y).state.sent = true)
  vote_owner : ∀ y c w, (c, w) ∈ V s y → (c, w) ∈ V s (owner c)
  own_unique : ∀ c w w', (c, w) ∈ V s (owner c) → (c, w') ∈ V s (owner c) → w = w'
  safe : ∀ y c w, (c, w) ∈ V s y → SafeAt s c w
  valid : ∀ y c w, (c, w) ∈ V s y → ∃ q, inp q = w
  m_prepare : ∀ m ∈ s.msgs, ∀ b, m.msg = .inr (.prepare b) → m.dest ≠ owner b
  m_promise : ∀ m ∈ s.msgs, ∀ b r, m.msg = .inr (.promise b r) → m.dest = owner b ∧ PromOK s b r
  m_accept : ∀ m ∈ s.msgs, ∀ b v, m.msg = .inr (.accept b v) → m.dest ≠ owner b ∧ (b, v) ∈ V s (owner b)
  decided : ∀ y v, (s.proc y).out = some v → ∃ c, (c, v) ∈ V s y ∧ y ≠ owner c

theorem inv_start (inp : Pr → Bool) : Inv inp (alg.start inp) := by
  have hmsg : ∀ m ∈ (alg.start inp).msgs, m = ⟨m.dest, .inl (inp m.dest)⟩ := by
    intro m hm
    obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1
      (show m ∈ Multiset.map (fun p => (⟨p, .inl (inp p)⟩ : Mg)) Finset.univ.val from hm)
    rfl
  refine ⟨fun m hm x hx => ?_, fun y x h => (by cases h), fun y => Or.inl ⟨rfl, ?_⟩,
    fun y c w h => (by cases h), fun y => le_refl _, fun y _ => rfl,
    fun y c w h => (by cases h), fun y c w h => (by cases h),
    fun y c w h => (by cases h), fun c w w' h => (by cases h),
    fun y c w h => (by cases h), fun y c w h => (by cases h),
    fun m hm b hb => ?_, fun m hm b r hb => ?_, fun m hm b v hb => ?_, fun y v h => (by cases h)⟩
  · rw [hmsg m hm] at hx; simp at hx; exact hx.symm
  · exact Multiset.mem_map.2 ⟨y, Finset.mem_univ_val y, rfl⟩
  all_goals rw [hmsg m hm] at hb; simp at hb

/-! ## Invariant preservation -/

structure Grow (s s' : St) : Prop where
  prom : ∀ y, Pm s y ≤ Pm s' y
  sub : ∀ y c w, (c, w) ∈ V s y → (c, w) ∈ V s' y
  new : ∀ y c w, (c, w) ∈ V s' y → (c, w) ∉ V s y → Pm s y ≤ c

theorem safeAt_mono {s s' : St} {b : ℕ} {v : Bool} (hg : Grow s s') (h : SafeAt s b v) : SafeAt s' b v := by
  intro c hc
  obtain ⟨y, z, hyz, hy, hz, hvy, hvz⟩ := h c hc
  refine ⟨y, z, hyz, lt_of_lt_of_le hy (hg.prom y), lt_of_lt_of_le hz (hg.prom z),
    fun w hw => ?_, fun w hw => ?_⟩
  · by_cases ho : (c, w) ∈ V s y
    · exact hvy w ho
    · exact absurd (hg.new y c w hw ho) (by omega)
  · by_cases ho : (c, w) ∈ V s z
    · exact hvz w ho
    · exact absurd (hg.new z c w hw ho) (by omega)

theorem promOK_mono {s s' : St} {b : ℕ} {r : Option (ℕ × Bool)} (hg : Grow s s') (h : PromOK s b r) :
    PromOK s' b r := by
  obtain ⟨x, hx, hb, h1, h2⟩ := h
  refine ⟨x, hx, hb.trans (hg.prom x), fun c w hw hc => ?_, fun c' w' hr => ?_⟩
  · by_cases ho : (c, w) ∈ V s x
    · exact h1 c w ho hc
    · exact absurd (hg.new x c w hw ho) (by omega)
  · obtain ⟨hm, hlt⟩ := h2 c' w' hr
    exact ⟨hg.sub x c' w' hm, hlt⟩

theorem st_recv (m : Mg) (s : St) (y : Pr) : ((alg.recvMsg m s).proc y).state =
    if y = m.dest then (handle m.dest m.msg (s.proc m.dest).state).1 else (s.proc y).state := by
  split
  · rename_i h; subst h; rw [recv_proc_eq]
  · rw [recv_proc_ne ‹_›]

theorem out_recv (m : Mg) (s : St) (y : Pr) : ((alg.recvMsg m s).proc y).out =
    if y = m.dest then (if (s.proc m.dest).out.isNone then (handle m.dest m.msg (s.proc m.dest).state).2.2
      else (s.proc m.dest).out) else (s.proc y).out := by
  split
  · rename_i h; subst h; rw [recv_proc_eq]
  · rw [recv_proc_ne ‹_›]

-- growth only at the receiving process
theorem grow_of {m : Mg} {s : St}
    (h1 : (s.proc m.dest).state.prom ≤ (handle m.dest m.msg (s.proc m.dest).state).1.prom)
    (h2 : ∀ c w, (c, w) ∈ (s.proc m.dest).state.votes → (c, w) ∈ (handle m.dest m.msg (s.proc m.dest).state).1.votes)
    (h3 : ∀ c w, (c, w) ∈ (handle m.dest m.msg (s.proc m.dest).state).1.votes →
      (c, w) ∉ (s.proc m.dest).state.votes → (s.proc m.dest).state.prom ≤ c) :
    Grow s (alg.recvMsg m s) := by
  refine ⟨fun y => ?_, fun y c w h => ?_, fun y c w h hn => ?_⟩ <;> simp only [V, Pm, st_recv] at * <;> split at *
  all_goals first | (rename_i hy; subst hy; first | exact h1 | exact h2 c w h | exact h3 c w h hn) | simp_all

-- ignored messages: only the message disappears
theorem inv_ign {inp : Pr → Bool} {s : St} {m : Mg} (hi : Inv inp s) (hm : m ∈ s.msgs)
    (hh : handle m.dest m.msg (s.proc m.dest).state = ((s.proc m.dest).state, 0, none))
    (hnt : m.msg ≠ .inr .tick) (hni : ∀ x, m.msg = .inl x → (s.proc m.dest).state.inp ≠ none) :
    Inv inp (alg.recvMsg m s) := by
  have hproc : (alg.recvMsg m s).proc = s.proc := by
    funext y
    by_cases hy : y = m.dest
    · subst hy; rw [recv_proc_eq, hh]
      conv_rhs => rw [show s.proc m.dest = ⟨(s.proc m.dest).state, (s.proc m.dest).out⟩ from rfl]
      congr 1; cases (s.proc m.dest).out <;> rfl
    · exact recv_proc_ne hy
  have hmsgs : (alg.recvMsg m s).msgs = s.msgs.erase m := by rw [recv_msgs, hh]; simp
  rw [show alg.recvMsg m s = ⟨s.msgs.erase m, s.proc⟩ from by rw [← hmsgs, ← hproc]]
  have he : ∀ m', m' ∈ s.msgs.erase m → m' ∈ s.msgs := fun _ => Multiset.mem_of_mem_erase
  refine ⟨fun m' h => hi.inl_ok m' (he m' h), hi.inp_ok, fun y => ?_, hi.votes_le, hi.cur_le, hi.acc_none,
    hi.acc_some, hi.own_votes, hi.vote_owner, hi.own_unique, hi.safe, hi.valid,
    fun m' h => hi.m_prepare m' (he m' h), fun m' h => hi.m_promise m' (he m' h),
    fun m' h => hi.m_accept m' (he m' h), hi.decided⟩
  rcases hi.live y with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1, (Multiset.mem_erase_of_ne ?_).2 h2⟩
    rintro rfl; exact hni _ rfl h1
  · exact Or.inr ⟨h1, (Multiset.mem_erase_of_ne (fun h => hnt (by rw [← h]))).2 h2⟩

theorem keep {m m' : Mg} {s : St} (h : m' ∈ s.msgs) (hne : m' ≠ m) : m' ∈ (alg.recvMsg m s).msgs := by
  rw [recv_msgs]; exact Multiset.mem_add.2 (Or.inl ((Multiset.mem_erase_of_ne hne).2 h))

theorem uniq {inp : Pr → Bool} {s : St} (hi : Inv inp s) {y z : Pr} {c : ℕ} {w w' : Bool}
    (h : (c, w) ∈ V s y) (h' : (c, w') ∈ V s z) : w = w' :=
  hi.own_unique c w w' (hi.vote_owner y c w h) (hi.vote_owner z c w' h')

theorem grow_eq {s s' : St} (hV : ∀ y, V s' y = V s y) (hP : ∀ y, Pm s' y = Pm s y) : Grow s s' :=
  ⟨fun y => (hP y).ge, fun y c w h => (hV y) ▸ h, fun y c w h hn => absurd ((hV y) ▸ h) hn⟩

-- receiving its input: only `inp` changes, a tick is sent
theorem inv_inl {inp : Pr → Bool} {s : St} {d : Pr} {x : Bool} (hi : Inv inp s)
    (hm : (⟨d, .inl x⟩ : Mg) ∈ s.msgs) : Inv inp (alg.recvMsg ⟨d, .inl x⟩ s) := by
  by_cases hc : (s.proc d).state.inp = none
  swap
  · exact inv_ign hi hm (by simp [handle, hc]) (by simp) (fun _ _ => hc)
  have hx : x = inp d := hi.inl_ok _ hm x rfl
  set s' := alg.recvMsg ⟨d, .inl x⟩ s with hs'
  have hst : ∀ y, (s'.proc y).state = if y = d then {(s.proc d).state with inp := some x}
      else (s.proc y).state := by
    intro y; rw [hs', st_recv]; simp [handle, hc]
  have hout : ∀ y, (s'.proc y).out = (s.proc y).out := by
    intro y; rw [hs', out_recv]; split
    · rename_i h; subst h; simp only [h_inl_out]; cases (s.proc y).out <;> rfl
    · rfl
  have hsm : ∀ y, (s'.proc y).state.prom = (s.proc y).state.prom ∧ (s'.proc y).state.cur = (s.proc y).state.cur ∧
      (s'.proc y).state.sent = (s.proc y).state.sent ∧ (s'.proc y).state.acc = (s.proc y).state.acc ∧
      (s'.proc y).state.votes = (s.proc y).state.votes := by
    intro y; rw [hst]; split <;> simp_all
  have hV : ∀ y, V s' y = V s y := fun y => (hsm y).2.2.2.2
  have hP : ∀ y, Pm s' y = Pm s y := fun y => (hsm y).1
  have hg := grow_eq hV hP
  have hsnd : (handle d (.inl x) (s.proc d).state).2.1 = {⟨d, .inr .tick⟩} := by simp [handle, hc]
  refine ⟨fun m' h x' hx' => ?_, fun y x' h => ?_, fun y => ?_, fun y c w h => ?_, fun y => ?_,
    fun y h => ?_, fun y c w h => ?_, fun y c w h ho => ?_, fun y c w h => ?_, fun c w w' h h' => ?_,
    fun y c w h => ?_, fun y c w h => ?_, fun m' h b hb => ?_, fun m' h b r hb => ?_,
    fun m' h b v hb => ?_, fun y v h => ?_⟩
  · rcases mem_recv h with h | h
    · exact hi.inl_ok m' h x' hx'
    · rw [hsnd, Multiset.mem_singleton] at h; subst h; simp at hx'
  · rw [hst] at h; split at h
    · rename_i hy; subst hy; simp at h; rw [← h, hx]
    · exact hi.inp_ok y x' h
  · by_cases hy : y = d
    · subst hy; refine Or.inr ⟨by rw [hst]; simp, mem_send (by rw [hsnd]; simp)⟩
    · rw [show (s'.proc y).state = (s.proc y).state by rw [hst]; simp [hy]]
      rcases hi.live y with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, keep h2 (by simp [hy])⟩
      · exact Or.inr ⟨h1, keep h2 (by simp)⟩
  · rw [hV] at h; rw [hP]; exact hi.votes_le y c w h
  · rw [(hsm y).2.1, hP]; exact hi.cur_le y
  · rw [hV]; exact hi.acc_none y (by rw [← (hsm y).2.2.2.1]; exact h)
  · rw [hV]; exact hi.acc_some y c w (by rw [← (hsm y).2.2.2.1]; exact h)
  · rw [hV] at h; rw [(hsm y).2.1, (hsm y).2.2.1]; exact hi.own_votes y c w h ho
  · rw [hV] at h; rw [hV]; exact hi.vote_owner y c w h
  · rw [hV] at h h'; exact hi.own_unique c w w' h h'
  · rw [hV] at h; exact safeAt_mono hg (hi.safe y c w h)
  · rw [hV] at h; exact hi.valid y c w h
  · rcases mem_recv h with h | h
    · exact hi.m_prepare m' h b hb
    · rw [hsnd, Multiset.mem_singleton] at h; subst h; simp at hb
  · rcases mem_recv h with h | h
    · exact (hi.m_promise m' h b r hb).imp_right (promOK_mono hg)
    · rw [hsnd, Multiset.mem_singleton] at h; subst h; simp at hb
  · rcases mem_recv h with h | h
    · obtain ⟨h1, h2⟩ := hi.m_accept m' h b v hb; exact ⟨h1, hg.sub _ _ _ h2⟩
    · rw [hsnd, Multiset.mem_singleton] at h; subst h; simp at hb
  · rw [hout] at h; obtain ⟨c, hc, hco⟩ := hi.decided y v h; exact ⟨c, hg.sub _ _ _ hc, hco⟩

theorem of_bcast {me : Pr} {k : Msg} {m' : Mg} (h : m' ∈ bcast me k) : m'.dest ≠ me ∧ m'.msg = .inr k := by
  obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 h
  have he' : e ∈ Finset.univ.erase me := he
  exact ⟨(Finset.mem_erase.1 he').1, rfl⟩

-- tick: a fresh ballot b, prom := b, prepare b to the others
theorem inv_tick {inp : Pr → Bool} {s : St} {d : Pr} (hi : Inv inp s)
    (hm : (⟨d, .inr .tick⟩ : Mg) ∈ s.msgs) : Inv inp (alg.recvMsg ⟨d, .inr .tick⟩ s) := by
  set st := (s.proc d).state with hst0
  set b := nextBallot d (max st.prom st.cur) with hb
  have hbp : st.prom < b := lt_of_le_of_lt (le_max_left _ _) (lt_next _ _)
  have hbc : st.cur < b := lt_of_le_of_lt (le_max_right _ _) (lt_next _ _)
  set s' := alg.recvMsg ⟨d, .inr .tick⟩ s with hs'
  have hst : ∀ y, (s'.proc y).state = if y = d then {st with cur := b, prom := b, sent := false}
      else (s.proc y).state := by
    intro y; rw [hs', st_recv]; rfl
  have hout : ∀ y, (s'.proc y).out = (s.proc y).out := by
    intro y; rw [hs', out_recv]; split
    · rename_i h; subst h; simp only [h_tick_out]; cases (s.proc y).out <;> rfl
    · rfl
  have hsm : ∀ y, (s'.proc y).state.inp = (s.proc y).state.inp ∧ (s'.proc y).state.acc = (s.proc y).state.acc ∧
      (s'.proc y).state.votes = (s.proc y).state.votes := by
    intro y; rw [hst]; split <;> simp_all
  have hV : ∀ y, V s' y = V s y := fun y => (hsm y).2.2
  have hPd : Pm s' d = b := by show (s'.proc d).state.prom = b; rw [hst, if_pos rfl]
  have hPo : ∀ y, y ≠ d → (s'.proc y).state = (s.proc y).state := fun y hy => by rw [hst, if_neg hy]
  have hg : Grow s s' := by
    refine ⟨fun y => ?_, fun y c w h => (hV y) ▸ h, fun y c w h hn => absurd ((hV y) ▸ h) hn⟩
    by_cases hy : y = d
    · subst hy; rw [hPd]; exact hbp.le
    · simp only [Pm, hPo y hy]; exact le_refl _
  have hsnd : (handle d (.inr .tick) st).2.1 = ⟨d, .inr .tick⟩ ::ₘ bcast d (.prepare b) := rfl
  have hnew : ∀ m', m' ∈ (handle d (.inr .tick) st).2.1 →
      m' = ⟨d, .inr .tick⟩ ∨ (m'.dest ≠ d ∧ m'.msg = .inr (.prepare b)) := by
    intro m' h; rw [hsnd, Multiset.mem_cons] at h
    exact h.imp_right of_bcast
  refine ⟨fun m' h x' hx' => ?_, fun y x' h => ?_, fun y => ?_, fun y c w h => ?_, fun y => ?_,
    fun y h => ?_, fun y c w h => ?_, fun y c w h ho => ?_, fun y c w h => ?_, fun c w w' h h' => ?_,
    fun y c w h => ?_, fun y c w h => ?_, fun m' h b' hb' => ?_, fun m' h b' r hb' => ?_,
    fun m' h b' v hb' => ?_, fun y v h => ?_⟩
  · rcases mem_recv h with h | h
    · exact hi.inl_ok m' h x' hx'
    · rcases hnew m' h with rfl | ⟨-, h2⟩ <;> simp_all
  · rw [(hsm y).1] at h; exact hi.inp_ok y x' h
  · rw [(hsm y).1]
    rcases hi.live y with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, keep h2 (by simp)⟩
    · by_cases hy : y = d
      · subst hy; exact Or.inr ⟨h1, mem_send (by rw [hsnd]; exact Multiset.mem_cons_self _ _)⟩
      · exact Or.inr ⟨h1, keep h2 (by simp [hy])⟩
  · rw [hV] at h
    by_cases hy : y = d
    · subst hy; rw [hPd]; exact (hi.votes_le _ c w h).trans hbp.le
    · simp only [Pm, hPo y hy]; exact hi.votes_le y c w h
  · by_cases hy : y = d
    · subst hy; rw [hPd, hst, if_pos rfl]
    · simp only [Pm, hPo y hy]; exact hi.cur_le y
  · rw [hV]; exact hi.acc_none y (by rw [← (hsm y).2.1]; exact h)
  · rw [hV]; exact hi.acc_some y c w (by rw [← (hsm y).2.1]; exact h)
  · rw [hV] at h
    by_cases hy : y = d
    · rw [hy] at h ho ⊢
      have h1 := (hi.own_votes d c w h ho).1
      have hcur : (s'.proc d).state.cur = b := by rw [hst, if_pos rfl]
      rw [hcur]
      exact ⟨le_of_lt (lt_of_le_of_lt h1 hbc), fun h2 => absurd h2 (ne_of_lt (lt_of_le_of_lt h1 hbc))⟩
    · rw [hPo y hy]; exact hi.own_votes y c w h ho
  · rw [hV] at h; rw [hV]; exact hi.vote_owner y c w h
  · rw [hV] at h h'; exact hi.own_unique c w w' h h'
  · rw [hV] at h; exact safeAt_mono hg (hi.safe y c w h)
  · rw [hV] at h; exact hi.valid y c w h
  · rcases mem_recv h with h | h
    · exact hi.m_prepare m' h b' hb'
    · rcases hnew m' h with rfl | ⟨h1, h2⟩
      · simp at hb'
      · rw [h2] at hb'; simp at hb'; subst hb'; rw [owner_next]; exact h1
  · rcases mem_recv h with h | h
    · exact (hi.m_promise m' h b' r hb').imp_right (promOK_mono hg)
    · rcases hnew m' h with rfl | ⟨-, h2⟩ <;> simp_all
  · rcases mem_recv h with h | h
    · obtain ⟨h1, h2⟩ := hi.m_accept m' h b' v hb'; exact ⟨h1, hg.sub _ _ _ h2⟩
    · rcases hnew m' h with rfl | ⟨-, h2⟩ <;> simp_all
  · rw [hout] at h; obtain ⟨c, hc, hco⟩ := hi.decided y v h; exact ⟨c, hg.sub _ _ _ hc, hco⟩

-- prepare b with b above the promise: promise b, report the latest vote
theorem inv_prep {inp : Pr → Bool} {s : St} {d : Pr} {b : ℕ} (hi : Inv inp s)
    (hm : (⟨d, .inr (.prepare b)⟩ : Mg) ∈ s.msgs) : Inv inp (alg.recvMsg ⟨d, .inr (.prepare b)⟩ s) := by
  set st := (s.proc d).state with hst0
  by_cases hc : st.prom < b
  swap
  · exact inv_ign hi hm (by simp [handle, hc, st]) (by simp) (by simp)
  have hdo : d ≠ owner b := hi.m_prepare _ hm b rfl
  set s' := alg.recvMsg ⟨d, .inr (.prepare b)⟩ s with hs'
  have hst : ∀ y, (s'.proc y).state = if y = d then {st with prom := b} else (s.proc y).state := by
    intro y; rw [hs', st_recv]; simp [h_prep_st, hc, st]
  have hout : ∀ y, (s'.proc y).out = (s.proc y).out := by
    intro y; rw [hs', out_recv]; split
    · rename_i h; subst h; simp only [h_prep_out]; cases (s.proc y).out <;> rfl
    · rfl
  have hsm : ∀ y, (s'.proc y).state.inp = (s.proc y).state.inp ∧ (s'.proc y).state.acc = (s.proc y).state.acc ∧
      (s'.proc y).state.votes = (s.proc y).state.votes ∧ (s'.proc y).state.cur = (s.proc y).state.cur ∧
      (s'.proc y).state.sent = (s.proc y).state.sent := by
    intro y; rw [hst]; split <;> simp_all
  have hV : ∀ y, V s' y = V s y := fun y => (hsm y).2.2.1
  have hPd : Pm s' d = b := by show (s'.proc d).state.prom = b; rw [hst, if_pos rfl]
  have hPo : ∀ y, y ≠ d → (s'.proc y).state = (s.proc y).state := fun y hy => by rw [hst, if_neg hy]
  have hg : Grow s s' := by
    refine ⟨fun y => ?_, fun y c w h => (hV y) ▸ h, fun y c w h hn => absurd ((hV y) ▸ h) hn⟩
    by_cases hy : y = d
    · rw [hy, hPd]; exact hc.le
    · simp only [Pm, hPo y hy]; exact le_refl _
  have hsnd : (handle d (.inr (.prepare b)) st).2.1 = {⟨owner b, .inr (.promise b st.acc)⟩} := by
    simp [h_prep_send, hc]
  refine ⟨fun m' h x' hx' => ?_, fun y x' h => ?_, fun y => ?_, fun y c w h => ?_, fun y => ?_,
    fun y h => ?_, fun y c w h => ?_, fun y c w h ho => ?_, fun y c w h => ?_, fun c w w' h h' => ?_,
    fun y c w h => ?_, fun y c w h => ?_, fun m' h b' hb' => ?_, fun m' h b' r hb' => ?_,
    fun m' h b' v hb' => ?_, fun y v h => ?_⟩
  · rcases mem_recv h with h | h
    · exact hi.inl_ok m' h x' hx'
    · rw [hsnd, Multiset.mem_singleton] at h; subst h; simp at hx'
  · rw [(hsm y).1] at h; exact hi.inp_ok y x' h
  · rw [(hsm y).1]
    rcases hi.live y with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, keep h2 (by simp)⟩
    · exact Or.inr ⟨h1, keep h2 (by simp)⟩
  · rw [hV] at h
    by_cases hy : y = d
    · rw [hy] at h ⊢; rw [hPd]; exact (hi.votes_le _ c w h).trans hc.le
    · simp only [Pm, hPo y hy]; exact hi.votes_le y c w h
  · by_cases hy : y = d
    · rw [hy, hPd, (hsm d).2.2.2.1]; exact (hi.cur_le d).trans hc.le
    · simp only [Pm, hPo y hy]; exact hi.cur_le y
  · rw [hV]; exact hi.acc_none y (by rw [← (hsm y).2.1]; exact h)
  · rw [hV]; exact hi.acc_some y c w (by rw [← (hsm y).2.1]; exact h)
  · rw [hV] at h; rw [(hsm y).2.2.2.1, (hsm y).2.2.2.2]; exact hi.own_votes y c w h ho
  · rw [hV] at h; rw [hV]; exact hi.vote_owner y c w h
  · rw [hV] at h h'; exact hi.own_unique c w w' h h'
  · rw [hV] at h; exact safeAt_mono hg (hi.safe y c w h)
  · rw [hV] at h; exact hi.valid y c w h
  · rcases mem_recv h with h | h
    · exact hi.m_prepare m' h b' hb'
    · rw [hsnd, Multiset.mem_singleton] at h; subst h; simp at hb'
  · rcases mem_recv h with h | h
    · exact (hi.m_promise m' h b' r hb').imp_right (promOK_mono hg)
    · rw [hsnd, Multiset.mem_singleton] at h; subst h
      simp only [Sum.inr.injEq, Msg.promise.injEq] at hb'; obtain ⟨rfl, rfl⟩ := hb'
      refine ⟨rfl, d, hdo, hPd.ge, fun c w hw hcb => ?_, fun c' w' hr => ?_⟩
      · rw [hV] at hw
        cases ha : st.acc with
        | none => rw [hi.acc_none d ha] at hw; simp at hw
        | some a => exact ⟨a.1, a.2, rfl, (hi.acc_some d a.1 a.2 ha).2 c w hw⟩
      · have := hi.acc_some d c' w' hr
        rw [hV]; exact ⟨this.1, lt_of_le_of_lt (hi.votes_le d c' w' this.1) hc⟩
  · rcases mem_recv h with h | h
    · obtain ⟨h1, h2⟩ := hi.m_accept m' h b' v hb'; exact ⟨h1, hg.sub _ _ _ h2⟩
    · rw [hsnd, Multiset.mem_singleton] at h; subst h; simp at hb'
  · rw [hout] at h; obtain ⟨c, hc, hco⟩ := hi.decided y v h; exact ⟨c, hg.sub _ _ _ hc, hco⟩

-- accept b v with b ≥ prom: vote (b, v) and decide v
theorem inv_acc {inp : Pr → Bool} {s : St} {d : Pr} {b : ℕ} {v : Bool} (hi : Inv inp s)
    (hm : (⟨d, .inr (.accept b v)⟩ : Mg) ∈ s.msgs) : Inv inp (alg.recvMsg ⟨d, .inr (.accept b v)⟩ s) := by
  set st := (s.proc d).state with hst0
  by_cases hc : st.prom ≤ b
  swap
  · exact inv_ign hi hm (h_acc_ign hc) (by simp) (by simp)
  obtain ⟨hdo, hov⟩ := hi.m_accept _ hm b v rfl
  set s' := alg.recvMsg ⟨d, .inr (.accept b v)⟩ s with hs'
  have hst : ∀ y, (s'.proc y).state = if y = d then
      {st with prom := b, acc := some (b, v), votes := (b, v) :: st.votes} else (s.proc y).state := by
    intro y; rw [hs', st_recv]; simp [handle, hc, st]
  have hout : ∀ y, (s'.proc y).out = if y = d then (if (s.proc d).out.isNone then some v else (s.proc d).out)
      else (s.proc y).out := by
    intro y; rw [hs', out_recv]; simp [h_acc_out, hc, st]
  have hPo : ∀ y, y ≠ d → (s'.proc y).state = (s.proc y).state := fun y hy => by rw [hst, if_neg hy]
  have hsd : (s'.proc d).state = {st with prom := b, acc := some (b, v), votes := (b, v) :: st.votes} := by
    rw [hst, if_pos rfl]
  have hVd : V s' d = (b, v) :: V s d := by show (s'.proc d).state.votes = _; rw [hsd]
  have hPd : Pm s' d = b := by simp only [Pm, hsd]
  have hVo : ∀ y, y ≠ d → V s' y = V s y := fun y hy => by simp only [V, hPo y hy]
  have hg : Grow s s' := by
    refine ⟨fun y => ?_, fun y c w h => ?_, fun y c w h hn => ?_⟩
    · by_cases hy : y = d
      · rw [hy, hPd]; exact hc
      · simp only [Pm, hPo y hy]; exact le_refl _
    · by_cases hy : y = d
      · rw [hy] at h ⊢; rw [hVd]; exact List.mem_cons_of_mem _ h
      · rw [hVo y hy]; exact h
    · by_cases hy : y = d
      · rw [hy] at h hn ⊢; rw [hVd] at h
        rcases List.mem_cons.1 h with h | h
        · simp only [Prod.mk.injEq] at h; rw [h.1]; exact hc
        · exact absurd h hn
      · rw [hVo y hy] at h; exact absurd h hn
  have hsafe : SafeAt s' b v := safeAt_mono hg (hi.safe _ b v hov)
  have hVown : ∀ c w, (c, w) ∈ V s' (owner c) → (c, w) ∈ V s (owner c) := by
    intro c w h
    by_cases hy : owner c = d
    · rw [hy] at h ⊢; rw [hVd] at h
      rcases List.mem_cons.1 h with h | h
      · simp only [Prod.mk.injEq] at h; rw [h.1] at hy; exact absurd hy.symm hdo
      · exact h
    · rw [hVo _ hy] at h; exact h
  -- votes of s' are old ones or (b, v) at d
  have hVcase : ∀ y c w, (c, w) ∈ V s' y → (c, w) ∈ V s y ∨ (y = d ∧ c = b ∧ w = v) := by
    intro y c w h
    by_cases hy : y = d
    · rw [hy] at h; rw [hVd] at h
      rcases List.mem_cons.1 h with h | h
      · simp only [Prod.mk.injEq] at h; exact Or.inr ⟨hy, h.1, h.2⟩
      · rw [hy]; exact Or.inl h
    · rw [hVo y hy] at h; exact Or.inl h
  refine ⟨fun m' h x' hx' => ?_, fun y x' h => ?_, fun y => ?_, fun y c w h => ?_, fun y => ?_,
    fun y h => ?_, fun y c w h => ?_, fun y c w h ho => ?_, fun y c w h => ?_, fun c w w' h h' => ?_,
    fun y c w h => ?_, fun y c w h => ?_, fun m' h b' hb' => ?_, fun m' h b' r hb' => ?_,
    fun m' h b' v' hb' => ?_, fun y v' h => ?_⟩
  · rcases mem_recv h with h | h
    · exact hi.inl_ok m' h x' hx'
    · simp [h_acc_send] at h
  · by_cases hy : y = d
    · rw [hy, hsd] at h; exact hy ▸ hi.inp_ok d x' h
    · rw [hPo y hy] at h; exact hi.inp_ok y x' h
  · have hsi : (s'.proc y).state.inp = (s.proc y).state.inp := by
      by_cases hy : y = d
      · rw [hy, hsd]
      · rw [hPo y hy]
    rw [hsi]
    rcases hi.live y with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, keep h2 (by simp)⟩
    · exact Or.inr ⟨h1, keep h2 (by simp)⟩
  · by_cases hy : y = d
    · rw [hy] at h ⊢; rw [hPd]; rw [hVd] at h
      rcases List.mem_cons.1 h with h | h
      · simp only [Prod.mk.injEq] at h; rw [h.1]
      · exact (hi.votes_le d c w h).trans hc
    · rw [hVo y hy] at h; simp only [Pm, hPo y hy]; exact hi.votes_le y c w h
  · by_cases hy : y = d
    · rw [hy, hPd, hsd]; exact (hi.cur_le d).trans hc
    · simp only [Pm, hPo y hy]; exact hi.cur_le y
  · by_cases hy : y = d
    · rw [hy, hsd] at h; simp at h
    · rw [hPo y hy] at h; rw [hVo y hy]; exact hi.acc_none y h
  · by_cases hy : y = d
    · rw [hy] at h ⊢; rw [hsd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rw [hVd]
      refine ⟨List.mem_cons_self, fun c' w' h' => ?_⟩
      rcases List.mem_cons.1 h' with h' | h'
      · simp only [Prod.mk.injEq] at h'; rw [h'.1]
      · exact (hi.votes_le d c' w' h').trans hc
    · rw [hPo y hy] at h; rw [hVo y hy]; exact hi.acc_some y c w h
  · rcases hVcase y c w h with h | ⟨rfl, rfl, rfl⟩
    · by_cases hy : y = d
      · rw [hy] at h ho ⊢; rw [hsd]; exact hi.own_votes d c w h ho
      · rw [hPo y hy]; exact hi.own_votes y c w h ho
    · exact absurd ho.symm hdo
  · rcases hVcase y c w h with h | ⟨rfl, rfl, rfl⟩
    · exact hg.sub _ _ _ (hi.vote_owner y c w h)
    · exact hg.sub _ _ _ hov
  · exact hi.own_unique c w w' (hVown c w h) (hVown c w' h')
  · rcases hVcase y c w h with h | ⟨rfl, rfl, rfl⟩
    · exact safeAt_mono hg (hi.safe y c w h)
    · exact hsafe
  · rcases hVcase y c w h with h | ⟨rfl, rfl, rfl⟩
    · exact hi.valid y c w h
    · exact hi.valid _ _ _ hov
  · rcases mem_recv h with h | h
    · exact hi.m_prepare m' h b' hb'
    · simp [h_acc_send] at h
  · rcases mem_recv h with h | h
    · exact (hi.m_promise m' h b' r hb').imp_right (promOK_mono hg)
    · simp [h_acc_send] at h
  · rcases mem_recv h with h | h
    · obtain ⟨h1, h2⟩ := hi.m_accept m' h b' v' hb'; exact ⟨h1, hg.sub _ _ _ h2⟩
    · simp [h_acc_send] at h
  · rw [hout] at h
    split at h
    · rename_i hy; rw [hy]
      split at h
      · simp only [Option.some.injEq] at h; subst h
        exact ⟨b, by rw [hVd]; exact List.mem_cons_self, hdo⟩
      · obtain ⟨c, hc, hco⟩ := hi.decided d v' h; exact ⟨c, hg.sub _ _ _ hc, hco⟩
    · obtain ⟨c, hc, hco⟩ := hi.decided y v' h; exact ⟨c, hg.sub _ _ _ hc, hco⟩

theorem best_none {o1 o2 : Option (ℕ × Bool)} (h : best o1 o2 = none) : o1 = none ∧ o2 = none := by
  rcases o1 with _ | ⟨k1, w1⟩ <;> rcases o2 with _ | ⟨k2, w2⟩ <;> simp only [best] at h
  · exact ⟨rfl, rfl⟩
  · simp at h
  · simp at h
  · split at h <;> simp at h

theorem best_some {o1 o2 : Option (ℕ × Bool)} {k : ℕ} {w : Bool} (h : best o1 o2 = some (k, w)) :
    (o1 = some (k, w) ∨ o2 = some (k, w)) ∧ (∀ k1 w1, o1 = some (k1, w1) → k1 ≤ k) ∧
    (∀ k2 w2, o2 = some (k2, w2) → k2 ≤ k) := by
  rcases o1 with _ | ⟨k1, w1⟩ <;> rcases o2 with _ | ⟨k2, w2⟩ <;> simp only [best] at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
  · split at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      simp <;> omega

-- the Paxos argument: the value picked from a quorum {owner, promiser} is safe at b
theorem safe_pick {inp : Pr → Bool} {s : St} {d : Pr} {b : ℕ} {r : Option (ℕ × Bool)} (hi : Inv inp s)
    (hd : d = owner b) (hP : PromOK s b r) (hprom : Pm s d = b) (dflt : Bool) :
    SafeAt s b (((best (s.proc d).state.acc r).map Prod.snd).getD dflt) := by
  obtain ⟨x, hx, hbx, hx1, hx2⟩ := hP
  have hdx : d ≠ x := fun h => hx (h ▸ hd)
  intro c hc
  have hcd : c < Pm s d := hprom ▸ hc
  have hcx : c < Pm s x := lt_of_lt_of_le hc hbx
  cases hbest : best (s.proc d).state.acc r with
  | none =>
    obtain ⟨ha, hr⟩ := best_none hbest
    refine ⟨d, x, hdx, hcd, hcx, fun w hw => ?_, fun w hw => ?_⟩
    · rw [hi.acc_none d ha] at hw; simp at hw
    · obtain ⟨c', w', hr', -⟩ := hx1 c w hw hc; rw [hr] at hr'; simp at hr'
  | some kw =>
    obtain ⟨k, w⟩ := kw
    simp only [Option.map_some, Option.getD_some]
    obtain ⟨hor, hk1, hk2⟩ := best_some hbest
    have hvote : (k, w) ∈ V s d ∨ (k, w) ∈ V s x := by
      rcases hor with h | h
      · exact Or.inl (hi.acc_some d k w h).1
      · exact Or.inr (hx2 k w h).1
    have hsk : SafeAt s k w := by rcases hvote with h | h <;> exact hi.safe _ k w h
    rcases lt_trichotomy c k with hlt | rfl | hgt
    · exact hsk c hlt
    · refine ⟨d, x, hdx, hcd, hcx, fun w' hw' => ?_, fun w' hw' => ?_⟩ <;>
        rcases hvote with h | h <;> exact uniq hi hw' h
    · refine ⟨d, x, hdx, hcd, hcx, fun w' hw' => ?_, fun w' hw' => ?_⟩
      · exfalso
        cases ha : (s.proc d).state.acc with
        | none => rw [hi.acc_none d ha] at hw'; simp at hw'
        | some a =>
          have h1 := (hi.acc_some d a.1 a.2 ha).2 c w' hw'
          have h2 := hk1 a.1 a.2 ha
          omega
      · exfalso
        obtain ⟨c', w'', hr', hle⟩ := hx1 c w' hw' hc
        have := hk2 c' w'' hr'
        omega

-- promise for the owner's current ballot: vote for the picked value, send accepts
theorem inv_prom {inp : Pr → Bool} {s : St} {d : Pr} {b : ℕ} {r : Option (ℕ × Bool)} (hi : Inv inp s)
    (hm : (⟨d, .inr (.promise b r)⟩ : Mg) ∈ s.msgs) : Inv inp (alg.recvMsg ⟨d, .inr (.promise b r)⟩ s) := by
  set st := (s.proc d).state with hst0
  by_cases hc : st.cur = b ∧ st.prom = b ∧ st.sent = false ∧ st.inp ≠ none
  swap
  · exact inv_ign hi hm (h_prom_ign hc) (by simp) (by simp)
  obtain ⟨hcur, hpr, hsent, hinp⟩ := hc
  obtain ⟨hdo, hP⟩ := hi.m_promise _ hm b r rfl
  simp only at hdo
  set v := ((best st.acc r).map Prod.snd).getD (st.inp.getD false) with hv
  set s' := alg.recvMsg ⟨d, .inr (.promise b r)⟩ s with hs'
  have hhd : handle d (.inr (.promise b r)) st =
      ({st with sent := true, acc := some (b, v), votes := (b, v) :: st.votes}, bcast d (.accept b v), none) := by
    simp only [handle]; rw [if_pos ⟨hcur, hpr, hsent, hinp⟩]
  have hst : ∀ y, (s'.proc y).state = if y = d then
      {st with sent := true, acc := some (b, v), votes := (b, v) :: st.votes} else (s.proc y).state := by
    intro y; rw [hs', st_recv]; simp only; rw [hhd]
  have hout : ∀ y, (s'.proc y).out = (s.proc y).out := by
    intro y; rw [hs', out_recv]; split
    · rename_i h; subst h; simp only [h_prom_out]; cases (s.proc y).out <;> rfl
    · rfl
  have hPo : ∀ y, y ≠ d → (s'.proc y).state = (s.proc y).state := fun y hy => by rw [hst, if_neg hy]
  have hsd : (s'.proc d).state = {st with sent := true, acc := some (b, v), votes := (b, v) :: st.votes} := by
    rw [hst, if_pos rfl]
  have hVd : V s' d = (b, v) :: V s d := by show (s'.proc d).state.votes = _; rw [hsd]
  have hVo : ∀ y, y ≠ d → V s' y = V s y := fun y hy => by simp only [V, hPo y hy]
  have hP' : ∀ y, Pm s' y = Pm s y := fun y => by
    by_cases hy : y = d
    · rw [hy]; show (s'.proc d).state.prom = _; rw [hsd]
    · simp only [Pm, hPo y hy]
  have hnob : ∀ c w, (c, w) ∈ V s d → c < b := by
    intro c w h
    rcases (hi.votes_le d c w h).lt_or_eq with h1 | h1
    · rwa [← hpr]
    · exfalso
      have hcb : c = b := h1.trans hpr
      have := (hi.own_votes d c w h (by rw [hcb, hdo])).2 (by rw [hcb, hcur])
      rw [hsent] at this; simp at this
  have hVcase : ∀ y c w, (c, w) ∈ V s' y → (c, w) ∈ V s y ∨ (y = d ∧ c = b ∧ w = v) := by
    intro y c w h
    by_cases hy : y = d
    · rw [hy] at h; rw [hVd] at h
      rcases List.mem_cons.1 h with h | h
      · simp only [Prod.mk.injEq] at h; exact Or.inr ⟨hy, h.1, h.2⟩
      · rw [hy]; exact Or.inl h
    · rw [hVo y hy] at h; exact Or.inl h
  have hg : Grow s s' := by
    refine ⟨fun y => (hP' y).ge, fun y c w h => ?_, fun y c w h hn => ?_⟩
    · by_cases hy : y = d
      · rw [hy] at h ⊢; rw [hVd]; exact List.mem_cons_of_mem _ h
      · rw [hVo y hy]; exact h
    · rcases hVcase y c w h with h | ⟨rfl, rfl, -⟩
      · exact absurd h hn
      · exact hpr.le
  have hsafe : SafeAt s' b v := safeAt_mono hg (safe_pick hi hdo hP hpr _)
  have hvalid : ∃ q, inp q = v := by
    cases hbest : best st.acc r with
    | none =>
      obtain ⟨x0, hx0⟩ := Option.ne_none_iff_exists'.1 hinp
      refine ⟨d, ?_⟩
      rw [hv, hbest, hx0]; exact (hi.inp_ok d x0 hx0).symm
    | some kw =>
      obtain ⟨k, w⟩ := kw
      obtain ⟨hor, -, -⟩ := best_some hbest
      rw [hv, hbest]; simp only [Option.map_some, Option.getD_some]
      rcases hor with h | h
      · exact hi.valid d k w (hi.acc_some d k w h).1
      · obtain ⟨x, -, -, -, hx2⟩ := hP; exact hi.valid x k w (hx2 k w h).1
  refine ⟨fun m' h x' hx' => ?_, fun y x' h => ?_, fun y => ?_, fun y c w h => ?_, fun y => ?_,
    fun y h => ?_, fun y c w h => ?_, fun y c w h ho => ?_, fun y c w h => ?_, fun c w w' h h' => ?_,
    fun y c w h => ?_, fun y c w h => ?_, fun m' h b' hb' => ?_, fun m' h b' r' hb' => ?_,
    fun m' h b' v' hb' => ?_, fun y v' h => ?_⟩
  · rcases mem_recv h with h | h
    · exact hi.inl_ok m' h x' hx'
    · rw [hhd] at h; rw [(of_bcast h).2] at hx'; simp at hx'
  · by_cases hy : y = d
    · rw [hy, hsd] at h; exact hy ▸ hi.inp_ok d x' h
    · rw [hPo y hy] at h; exact hi.inp_ok y x' h
  · have hsi : (s'.proc y).state.inp = (s.proc y).state.inp := by
      by_cases hy : y = d
      · rw [hy, hsd]
      · rw [hPo y hy]
    rw [hsi]
    rcases hi.live y with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, keep h2 (by simp)⟩
    · exact Or.inr ⟨h1, keep h2 (by simp)⟩
  · rw [hP']
    rcases hVcase y c w h with h | ⟨rfl, rfl, -⟩
    · exact hi.votes_le y c w h
    · exact hpr.ge
  · rw [hP']
    by_cases hy : y = d
    · rw [hy, hsd]; exact hi.cur_le d
    · rw [hPo y hy]; exact hi.cur_le y
  · by_cases hy : y = d
    · rw [hy, hsd] at h; simp at h
    · rw [hPo y hy] at h; rw [hVo y hy]; exact hi.acc_none y h
  · by_cases hy : y = d
    · rw [hy] at h ⊢; rw [hsd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [hVd]
      refine ⟨List.mem_cons_self, fun c' w' h' => ?_⟩
      rcases List.mem_cons.1 h' with h' | h'
      · simp only [Prod.mk.injEq] at h'; rw [h'.1]
      · exact (hnob c' w' h').le
    · rw [hPo y hy] at h; rw [hVo y hy]; exact hi.acc_some y c w h
  · rcases hVcase y c w h with h | ⟨rfl, rfl, rfl⟩
    · by_cases hy : y = d
      · rw [hy] at h ho ⊢; rw [hsd]
        exact ⟨(hi.own_votes d c w h ho).1, fun _ => rfl⟩
      · rw [hPo y hy]; exact hi.own_votes y c w h ho
    · rw [hsd]; exact ⟨hcur.ge, fun _ => rfl⟩
  · rcases hVcase y c w h with h | ⟨rfl, rfl, rfl⟩
    · exact hg.sub _ _ _ (hi.vote_owner y c w h)
    · rw [← hdo, hVd]; exact List.mem_cons_self
  · rcases hVcase _ c w h with h1 | ⟨h1, rfl, rfl⟩ <;> rcases hVcase _ c w' h' with h2 | ⟨h2, h3, rfl⟩
    · exact hi.own_unique c w w' h1 h2
    · rw [h2] at h1; exact absurd (hnob _ _ h1) (by rw [h3]; exact lt_irrefl _)
    · rw [h1] at h2; exact absurd (hnob _ _ h2) (lt_irrefl _)
    · rfl
  · rcases hVcase y c w h with h | ⟨rfl, rfl, rfl⟩
    · exact safeAt_mono hg (hi.safe y c w h)
    · exact hsafe
  · rcases hVcase y c w h with h | ⟨rfl, rfl, rfl⟩
    · exact hi.valid y c w h
    · exact hvalid
  · rcases mem_recv h with h | h
    · exact hi.m_prepare m' h b' hb'
    · rw [hhd] at h; rw [(of_bcast h).2] at hb'; simp at hb'
  · rcases mem_recv h with h | h
    · exact (hi.m_promise m' h b' r' hb').imp_right (promOK_mono hg)
    · rw [hhd] at h; rw [(of_bcast h).2] at hb'; simp at hb'
  · rcases mem_recv h with h | h
    · obtain ⟨h1, h2⟩ := hi.m_accept m' h b' v' hb'; exact ⟨h1, hg.sub _ _ _ h2⟩
    · rw [hhd] at h; obtain ⟨h1, h2⟩ := of_bcast h
      rw [h2] at hb'; simp only [Sum.inr.injEq, Msg.accept.injEq] at hb'; obtain ⟨rfl, rfl⟩ := hb'
      exact ⟨hdo ▸ h1, by rw [← hdo, hVd]; exact List.mem_cons_self⟩
  · rw [hout] at h; obtain ⟨c, hc, hco⟩ := hi.decided y v' h; exact ⟨c, hg.sub _ _ _ hc, hco⟩

theorem inv_step {inp : Pr → Bool} {s s' : St} {x : Action Pr Msg}
    (hi : Inv inp s) (ht : alg.lts.Tr s x s') : Inv inp s' := by
  rcases x with _ | m
  · rw [← Algorithm.tr_none ht]; exact hi
  · obtain ⟨hm, rfl⟩ := ht
    obtain ⟨d, k⟩ := m
    rcases k with x | (_ | b | ⟨b, r⟩ | ⟨b, v⟩)
    · exact inv_inl hi hm
    · exact inv_tick hi hm
    · exact inv_prep hi hm
    · exact inv_prom hi hm
    · exact inv_acc hi hm

theorem inv_mtr {inp : Pr → Bool} {s s' : St} {xs : List (Action Pr Msg)}
    (hi : Inv inp s) (h : alg.lts.MTr s xs s') : Inv inp s' := by
  induction h with
  | refl => exact hi
  | stepL ht _ ih => exact ih (inv_step hi ht)

theorem inv_reach {inp : Pr → Bool} {s : St} (h : alg.Reachable inp s) : Inv inp s := by
  obtain ⟨xs, h⟩ := h
  exact inv_mtr (inv_start inp) h

-- any two quorums of Fin 3 intersect
theorem inter3 (y1 z1 y2 z2 : Pr) (h1 : y1 ≠ z1) (h2 : y2 ≠ z2) :
    y1 = y2 ∨ y1 = z2 ∨ z1 = y2 ∨ z1 = z2 := by
  revert y1 z1 y2 z2; decide

-- a value chosen at ballot c (two distinct voters) is the value of every vote at ballots ≥ c
theorem chosen_le {inp : Pr → Bool} {s : St} (hi : Inv inp s) {c c' : ℕ} {v v' : Bool} {y y' z : Pr}
    (hy : (c, v) ∈ V s y) (hy' : (c, v) ∈ V s y') (hyy : y ≠ y') (hz : (c', v') ∈ V s z)
    (hc : c ≤ c') : v' = v := by
  rcases hc.lt_or_eq with hlt | heq
  · obtain ⟨y1, z1, h1, -, -, hy1, hz1⟩ := hi.safe z c' v' hz c hlt
    rcases inter3 y1 z1 y y' h1 hyy with rfl | rfl | rfl | rfl
    · exact (hy1 v hy).symm
    · exact (hy1 v hy').symm
    · exact (hz1 v hy).symm
    · exact (hz1 v hy').symm
  · subst heq; exact hi.own_unique c v' v (hi.vote_owner z c v' hz) (hi.vote_owner y c v hy)

theorem safe : alg.SafeConsensus := by
  intro inp s hr
  have hi := inv_reach hr
  refine ⟨?_, ?_⟩
  · rintro b b' ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩
    obtain ⟨c, hc, hco⟩ := hi.decided y b hy
    obtain ⟨c', hc', hco'⟩ := hi.decided y' b' hy'
    rcases le_total c c' with h | h
    · exact (chosen_le hi hc (hi.vote_owner y c b hc) hco hc' h).symm
    · exact chosen_le hi hc' (hi.vote_owner y' c' b' hc') hco' hc h
  · rintro b ⟨y, hy⟩
    obtain ⟨c, hc, -⟩ := hi.decided y b hy
    exact hi.valid y c b hc

/-! ## Liveness: any two processes can reach a decision -/

theorem step1' {m : Mg} {s : St} (hm : m ∈ s.msgs) : alg.lts.Tr s (some m) (alg.recvMsg m s) := ⟨hm, rfl⟩

theorem reach1 {inp : Pr → Bool} {s : St} {m : Mg} (hr : alg.Reachable inp s) (hm : m ∈ s.msgs) :
    alg.Reachable inp (alg.recvMsg m s) :=
  Algorithm.reachable_stable hr ⟨_, LTS.MTr.single _ (step1' hm)⟩

-- one tick at p: a fresh ballot above everything p has seen, owned by p, prepare sent to q
theorem tick1 {inp : Pr → Bool} {s : St} {p q : Pr} (hpq : p ≠ q) (hr : alg.Reachable inp s)
    (hin : (s.proc p).state.inp ≠ none) :
    (⟨p, .inr .tick⟩ : Mg) ∈ s.msgs ∧
    ((alg.recvMsg ⟨p, .inr .tick⟩ s).proc p).state.inp ≠ none ∧
    max (Pm s p) (s.proc p).state.cur < ((alg.recvMsg ⟨p, .inr .tick⟩ s).proc p).state.cur ∧
    Pm (alg.recvMsg ⟨p, .inr .tick⟩ s) p = ((alg.recvMsg ⟨p, .inr .tick⟩ s).proc p).state.cur ∧
    ((alg.recvMsg ⟨p, .inr .tick⟩ s).proc p).state.sent = false ∧
    owner ((alg.recvMsg ⟨p, .inr .tick⟩ s).proc p).state.cur = p ∧
    (⟨q, .inr (.prepare ((alg.recvMsg ⟨p, .inr .tick⟩ s).proc p).state.cur)⟩ : Mg) ∈
      (alg.recvMsg ⟨p, .inr .tick⟩ s).msgs ∧
    (alg.recvMsg ⟨p, .inr .tick⟩ s).proc q = s.proc q := by
  have ht : (⟨p, .inr .tick⟩ : Mg) ∈ s.msgs := by
    rcases (inv_reach hr).live p with ⟨hn, -⟩ | ⟨-, hm⟩
    · exact absurd hn hin
    · exact hm
  simp only [Pm, recv_dest]
  refine ⟨ht, hin, lt_next _ _, rfl, rfl, owner_next _ _, mem_send ?_, recv_proc_ne (Ne.symm hpq)⟩
  exact Multiset.mem_cons_of_mem (mem_bcast (Ne.symm hpq))

theorem tickN {inp : Pr → Bool} {ps : Set Pr} {p q : Pr} (hpq : p ≠ q) (hp : p ∈ ps) (n : ℕ) :
    ∀ {s : St}, alg.Reachable inp s → (s.proc p).state.inp ≠ none →
    ∃ s1, alg.CanReachVia ps s s1 ∧ alg.Reachable inp s1 ∧ (s1.proc p).state.inp ≠ none ∧
      n ≤ (s1.proc p).state.cur ∧ Pm s1 p = (s1.proc p).state.cur ∧ (s1.proc p).state.sent = false ∧
      owner (s1.proc p).state.cur = p ∧
      (⟨q, .inr (.prepare (s1.proc p).state.cur)⟩ : Mg) ∈ s1.msgs ∧ s1.proc q = s.proc q := by
  induction n with
  | zero =>
    intro s hr hin
    obtain ⟨ht, h1, -, h3, h4, h5, h6, h7⟩ := tick1 hpq hr hin
    exact ⟨_, via1 hp ht, reach1 hr ht, h1, Nat.zero_le _, h3, h4, h5, h6, h7⟩
  | succ n ih =>
    intro s hr hin
    obtain ⟨s1, hv, hr1, hin1, hn, hpc, -, -, -, hq1⟩ := ih hr hin
    obtain ⟨ht, h1, h2, h3, h4, h5, h6, h7⟩ := tick1 hpq hr1 hin1
    refine ⟨_, hv.trans (via1 hp ht), reach1 hr1 ht, h1, ?_, h3, h4, h5, h6, h7.trans hq1⟩
    omega

-- any two processes p ≠ q can reach a decision by themselves
theorem live2 {inp : Pr → Bool} {s : St} {ps : Set Pr} {p q : Pr} (hpq : p ≠ q) (hp : p ∈ ps)
    (hq : q ∈ ps) (hr : alg.Reachable inp s) : ∃ s' b, alg.CanReachVia ps s s' ∧ s'.Decided b := by
  -- p gets its input
  obtain ⟨s0, h0, hr0, hin0⟩ : ∃ s0, alg.CanReachVia ps s s0 ∧ alg.Reachable inp s0 ∧
      (s0.proc p).state.inp ≠ none := by
    rcases (inv_reach hr).live p with ⟨hn, hm⟩ | ⟨hn, -⟩
    · refine ⟨_, via1 hp hm, reach1 hr hm, ?_⟩
      rw [recv_dest]; simp [handle, hn]
    · exact ⟨s, .refl, hr, hn⟩
  -- p ticks until its ballot b is above q's promise
  obtain ⟨s1, h1, hr1, hin1, hcur, hprom, hsent, hown, hprep, hq1⟩ := tickN hpq hp (Pm s0 q + 1) hr0 hin0
  have hqb : Pm s1 q < (s1.proc p).state.cur := by simp only [Pm] at hcur ⊢; rw [hq1]; omega
  -- q receives prepare b and promises
  set b := (s1.proc p).state.cur with hb
  set S2 := alg.recvMsg ⟨q, .inr (.prepare b)⟩ s1 with hS2
  have hp2 : S2.proc p = s1.proc p := recv_proc_ne hpq
  have hq2 : Pm S2 q = b := by
    simp only [hS2, Pm, recv_dest, h_prep_st, if_pos hqb]
  have hpm : (⟨p, .inr (.promise b (s1.proc q).state.acc)⟩ : Mg) ∈ S2.msgs := by
    apply mem_send; simp only [h_prep_send, if_pos hqb, hown, Multiset.mem_singleton]
  -- p receives the promise and votes
  set v := ((best (s1.proc p).state.acc (s1.proc q).state.acc).map Prod.snd).getD
      ((s1.proc p).state.inp.getD false) with hv
  set S3 := alg.recvMsg ⟨p, .inr (.promise b (s1.proc q).state.acc)⟩ S2 with hS3
  have hq3 : S3.proc q = S2.proc q := recv_proc_ne (Ne.symm hpq)
  have hav : (⟨q, .inr (.accept b v)⟩ : Mg) ∈ S3.msgs := by
    apply mem_send
    simp only [hp2, handle]
    split
    · exact mem_bcast (Ne.symm hpq)
    · rename_i hn; exact absurd ⟨rfl, hprom, hsent, hin1⟩ hn
  -- q receives the accept and decides
  obtain ⟨w, hw⟩ : ∃ w, ((alg.recvMsg ⟨q, .inr (.accept b v)⟩ S3).proc q).out = some w := by
    rw [recv_dest, hq3]
    simp only [h_acc_out]
    rw [if_pos (le_of_eq hq2)]
    cases (S2.proc q).out <;> simp
  exact ⟨_, w, h0.trans (h1.trans ((via1 hq hprep).trans ((via1 hp hpm).trans (via1 hq hav)))), q, hw⟩

theorem pterm : alg.PseudoTermination 1 := by
  intro inp s hr ps hps
  have h2 : 1 < ps.ncard := by simp at hps; omega
  obtain ⟨p, q, hp, hq, hpq⟩ := (Set.one_lt_ncard_iff (Set.toFinite ps)).1 h2
  exact live2 hpq hp hq hr

theorem hpc : alg.PseudoConsensus 1 := ⟨safe, pterm⟩

/-! ## General tools -/

-- a predicate preserved by every transition holds along every execution
theorem jinv {J : St → Prop} (hJ : ∀ s x s', J s → alg.lts.Tr s x s' → J s') {s t : St}
    (hs : J s) (h : alg.lts.CanReach s t) : J t := by
  obtain ⟨xs, h⟩ := h
  induction h with
  | refl => exact hs
  | stepL ht _ ih => exact ih (hJ _ _ _ hs ht)

-- a message received along an execution was in flight in some state on the way
theorem mem_of_mtr {s t : St} {xl : List (Action Pr Msg)} {m : Mg}
    (h : alg.lts.MTr s xl t) (hm : some m ∈ xl) : ∃ u, alg.lts.CanReach s u ∧ m ∈ u.msgs := by
  induction h with
  | refl => simp at hm
  | @stepL s1 x s2 xl t htr _ ih =>
    rcases List.mem_cons.1 hm with hx | hx
    · subst hx; exact ⟨s1, LTS.CanReach.refl _ _, htr.1⟩
    · obtain ⟨u, ⟨ys, hys⟩, hu⟩ := ih hx
      exact ⟨u, ⟨x :: ys, hys.stepL htr⟩, hu⟩

end F1c0

/-! ## Conditional refutations (copied from T1c0, generic in the algorithm) -/

namespace F1c0G
open Cslib Cslib.FLP
variable {P M S : Type} [DecidableEq P] [DecidableEq M]

-- the state with no messages and no decisions
def emptyS (a : Algorithm P M S) : State P M S := ⟨0, fun r => ⟨a.init r, none⟩⟩

-- a state where p decided true and everybody else false, with one message m in flight
def confS (a : Algorithm P M S) (p : P) (m : Message P M) : State P M S :=
  ⟨{m}, fun r => ⟨a.init r, some (decide (r = p))⟩⟩

theorem emptyS_mtr {a : Algorithm P M S} {xl : List (Action P M)} {t : State P M S}
    (h : a.lts.MTr (emptyS a) xl t) : t = emptyS a := by
  generalize hs : emptyS a = s at h
  induction h with
  | refl => rfl
  | @stepL s1 x s2 xl t htr _ ih =>
    subst hs
    cases x with
    | none => exact (ih (Algorithm.tr_none htr)).trans (Algorithm.tr_none htr).symm
    | some m => exact absurd htr.1 (by simp [emptyS])

theorem emptyS_noCDW {a : Algorithm P M S} (p : P) (b : Bool) : ¬ a.CanDecideWithout (emptyS a) p b := by
  rintro ⟨t, hc, r, hr⟩
  obtain ⟨xl, h⟩ := CanReachVia.canReach hc
  rw [emptyS_mtr h] at hr
  simp [emptyS, State.ProcDecided] at hr

theorem confS_dec {a : Algorithm P M S} {p q : P} (hpq : p ≠ q) (m : Message P M) (b : Bool) :
    (confS a p m).Decided b := by
  cases b
  · exact ⟨q, by simp [confS, State.ProcDecided, Ne.symm hpq]⟩
  · exact ⟨p, by simp [confS, State.ProcDecided]⟩

theorem confS_unreach [Fintype P] {a : Algorithm P M S} (hpc : a.PseudoConsensus 1) {p q : P} (hpq : p ≠ q)
    (m : Message P M) {inp : P → Bool} {t : State P M S} (hc : a.lts.CanReach (confS a p m) t) :
    ¬ a.Reachable inp t := fun hr =>
  absurd ((hpc.1 inp t hr).1 true false ⟨Algorithm.decided_stable (confS_dec hpq m true) hc,
    Algorithm.decided_stable (confS_dec hpq m false) hc⟩) (by decide)

-- a reachable decided state exists
theorem reachDec [Fintype P] {a : Algorithm P M S} (hpc : a.PseudoConsensus 1) (inp : P → Bool) (p : P) :
    ∃ s b, a.Reachable inp s ∧ s.Decided b := by
  obtain ⟨s', b, hc, hd⟩ := OnePseudoConsensus.pseudoTermination hpc (Algorithm.reachable_start (inp := inp)) p
  exact ⟨s', b, Algorithm.reachable_stable Algorithm.reachable_start (CanReachVia.canReach hc), hd⟩

end F1c0G

namespace F1c0
open Cslib Cslib.FLP F1c0G

abbrev m0 : Mg := ⟨0, .inr .tick⟩

-- `Cslib.FLP.OnePseudoConsensus.pseudoTermination` idx 10: necessary (Paxos on Fin 3; the empty state is unreachable and undecidable)
theorem pt10 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.pseudoTermination 10 := fun h => by
  obtain ⟨s', b, hc, hd⟩ := @h Pr Msg PS _ _ alg (fun _ => true) _ hpc (emptyS alg) 0
  exact emptyS_noCDW 0 b ⟨s', hc, hd⟩

-- `Cslib.FLP.OnePseudoConsensus.canDecideWithout_exists` idx 10: necessary (Paxos on Fin 3, empty state)
theorem cdwe10 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.canDecideWithout_exists 10 := fun h => by
  obtain ⟨b, hb⟩ := @h Pr Msg PS _ _ alg (fun _ => true) _ hpc (emptyS alg) 0
  exact emptyS_noCDW 0 b hb

-- `Cslib.FLP.OnePseudoConsensus.uniform_or_nonUniform` idx 10: necessary (Paxos on Fin 3, empty state)
theorem uon10 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.uniform_or_nonUniform 10 := fun h => by
  rcases @h Pr Msg PS _ _ alg (fun _ => true) _ hpc (emptyS alg) with h | h | h
  · exact emptyS_noCDW 0 _ (h 0).1
  · exact emptyS_noCDW 0 _ (h 0).1
  · obtain ⟨r, hr⟩ := h true; exact emptyS_noCDW r _ hr

-- `Cslib.FLP.OnePseudoConsensus.decided_eq_canDecideWithout` idx 10: necessary (Paxos on Fin 3, a state decided both ways)
theorem dec10 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.decided_eq_canDecideWithout 10 := fun h =>
  absurd (@h Pr Msg PS _ _ alg (fun _ => true) _ hpc (confS alg 0 m0) true false 0
    (confS_dec (by decide : (0 : Pr) ≠ 1) m0 true)
    ⟨_, CanReachVia.refl _ _, confS_dec (by decide : (0 : Pr) ≠ 1) m0 false⟩) (by decide)

-- `Cslib.FLP.OnePseudoConsensus.decided_eq_canDecideWithout` idx 14: necessary (Paxos on Fin 3, start state)
theorem dec14 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.decided_eq_canDecideWithout 14 := fun h => by
  obtain ⟨b, hb⟩ := OnePseudoConsensus.canDecideWithout_exists hpc
    (Algorithm.reachable_start (a := alg) (inp := fun _ => true)) 0
  exact absurd (@h Pr Msg PS _ _ alg (fun _ => true) _ hpc _ Algorithm.reachable_start (!b) b 0 hb)
    (by cases b <;> decide)

-- `Cslib.FLP.OnePseudoConsensus.decided_eq_canDecideWithout` idx 15: necessary (Paxos on Fin 3, a reachable decided state)
theorem dec15 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.decided_eq_canDecideWithout 15 := fun h => by
  obtain ⟨s, b, hr, hd⟩ := reachDec hpc (fun _ => true) (0 : Pr)
  exact absurd (@h Pr Msg PS _ _ alg (fun _ => true) _ hpc s hr b (!b) 0 hd) (by cases b <;> decide)

-- `Cslib.FLP.OnePseudoConsensus.decided_imp_uniform` idx 10: necessary (Paxos on Fin 3, a state decided both ways)
theorem diu10 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.decided_imp_uniform 10 := fun h =>
  ((@h Pr Msg PS _ _ alg (fun _ => true) _ hpc (confS alg 0 m0) true
    (confS_dec (by decide : (0 : Pr) ≠ 1) m0 true)) 0).2
    ⟨_, CanReachVia.refl _ _, confS_dec (by decide : (0 : Pr) ≠ 1) m0 false⟩

-- `Cslib.FLP.OnePseudoConsensus.decided_imp_uniform` idx 12: necessary (Paxos on Fin 3, start state)
theorem diu12 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.decided_imp_uniform 12 := fun h => by
  have h1 := @h Pr Msg PS _ _ alg (fun _ => true) _ hpc _ Algorithm.reachable_start true
  have h0 := @h Pr Msg PS _ _ alg (fun _ => true) _ hpc _ Algorithm.reachable_start false
  exact (h0 0).2 (h1 0).1

-- `Cslib.FLP.OnePseudoConsensus.fair_nonUniform` idx 10: necessary (Paxos on Fin 3, a state decided both ways)
theorem fnu10 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.fair_nonUniform 10 := fun h => by
  obtain ⟨ss, xs, he, h0, -, hf⟩ := @h Pr Msg PS _ _ alg _ (fun _ => true) hpc (confS alg 0 m0)
  obtain ⟨n, hn, -⟩ := hf.exists
  refine confS_unreach hpc (by decide : (0 : Pr) ≠ 1) m0 ⟨xs.extract 0 n, ?_⟩ hn
  rw [← h0]; exact he.extract_mTr (Nat.zero_le n)

-- `Cslib.FLP.OnePseudoConsensus.canDecideWithout_uniform` idx 14: necessary (Paxos on Fin 3, s' = empty state)
theorem cdu14 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.canDecideWithout_uniform 14 := fun h => by
  obtain ⟨s, b, hr, hd⟩ := reachDec hpc (fun _ => true) (0 : Pr)
  have hu := OnePseudoConsensus.decided_imp_uniform hpc hr hd 0
  exact emptyS_noCDW 0 b (@h Pr Msg PS _ _ alg (fun _ => true) _ hpc s (emptyS alg) m0 b hr 0 hu.1 hu.2)

-- `Cslib.FLP.OnePseudoConsensus.nonUniform_step` idx 11: necessary (Paxos on Fin 3, a reachable decided state)
theorem nus11 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.nonUniform_step 11 := fun h => by
  obtain ⟨s, b, hr, hd⟩ := reachDec hpc (fun _ => true) (0 : Pr)
  obtain ⟨s', hc, hall⟩ := @h Pr Msg PS _ _ alg (fun _ => true) _ hpc s hr 0
  obtain ⟨t, hct, hdt⟩ := hall (!b)
  have hc2 : alg.lts.CanReach s t := by
    obtain ⟨x1, h1⟩ := hc; obtain ⟨x2, h2⟩ := CanReachVia.canReach hct
    exact ⟨x1 ++ x2, LTS.MTr.comp _ h1 h2⟩
  exact absurd ((hpc.1 _ t (Algorithm.reachable_stable hr hc2)).1 b (!b)
    ⟨Algorithm.decided_stable hd hc2, hdt⟩) (by cases b <;> decide)

-- `Cslib.FLP.OnePseudoConsensus.nonUniform_step_exists` idx 11: necessary (Paxos on Fin 3, a state decided both ways)
theorem nuse11 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.nonUniform_step_exists 11 := fun h => by
  obtain ⟨xl, t, hmtr, -, hr, -⟩ := @h Pr Msg PS _ _ alg _ (fun _ => true) hpc (confS alg 0 m0) m0
    (by simp [confS])
  exact confS_unreach hpc (by decide : (0 : Pr) ≠ 1) m0 ⟨xl, hmtr⟩ hr

/-! ## The four rows that need this algorithm's behaviour -/

-- an accept addressed to the owner of its ballot is never sent
-- `Cslib.FLP.OnePseudoConsensus.nonUniform_step_exists` idx 12: necessary (Paxos on Fin 3, m = accept to the owner of its ballot, never in flight)
theorem nuse12 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.nonUniform_step_exists 12 := fun h => by
  obtain ⟨inp, hnu⟩ := OnePseudoConsensus.nonUniform_inp hpc (by simp : 2 ≤ Fintype.card Pr)
  obtain ⟨xl, t, hmtr, hm, -⟩ := @h Pr Msg PS _ _ alg _ inp hpc (alg.start inp) ⟨0, .inr (.accept 0 true)⟩
    ⟨Algorithm.reachable_start, hnu⟩
  obtain ⟨u, hu, hmu⟩ := mem_of_mtr hmtr hm
  exact ((inv_reach (Algorithm.reachable_stable Algorithm.reachable_start hu)).m_accept _ hmu 0 true rfl).1 rfl

-- unreachable state: process 0 holds accept(1, true) and accept(1, false); its first one decides
def sA : St := ⟨{⟨0, .inr (.accept 1 true)⟩, ⟨0, .inr (.accept 1 false)⟩}, fun _ => ⟨PS.init, none⟩⟩

theorem sA_nonUniform : alg.NonUniform sA := by
  intro b
  refine ⟨1, alg.recvMsg ⟨0, .inr (.accept 1 b)⟩ sA, via1 (by simp) (by cases b <;> simp [sA]), 0, ?_⟩
  cases b <;> rfl

def JA (t : St) : Prop :=
  (∀ m ∈ t.msgs, m.dest = 0 ∧ ∃ v, m.msg = .inr (.accept 1 v)) ∧ ∀ y, y ≠ 0 → (t.proc y).out = none

theorem JA_step : ∀ s x s', JA s → alg.lts.Tr s x s' → JA s' := by
  rintro s (_ | m) s' ⟨hm, ho⟩ ht
  · rw [← Algorithm.tr_none ht]; exact ⟨hm, ho⟩
  · obtain ⟨hms, rfl⟩ := ht
    obtain ⟨hd, v, hv⟩ := hm m hms
    have hsend : (handle m.dest m.msg (s.proc m.dest).state).2.1 = 0 := by
      rw [hv]; simp only [handle]; split <;> rfl
    refine ⟨fun m' hm' => ?_, fun y hy => ?_⟩
    · rw [recv_msgs, hsend, add_zero] at hm'
      exact hm m' (Multiset.mem_of_mem_erase hm')
    · rw [recv_proc_ne (by rw [hd]; exact hy)]; exact ho y hy

theorem sA_noBoth {t : St} (h : alg.lts.CanReach sA t) :
    ¬ (alg.CanDecideWithout t 0 true ∧ alg.CanDecideWithout t 0 false) := by
  have hJ : JA t := jinv JA_step ⟨by simp [sA], fun y _ => rfl⟩ h
  have hno : ∀ u, JA u → ∀ m ∈ u.msgs, m.dest ∉ ({0}ᶜ : Set Pr) := fun u hu m hm => by
    simp [(hu.1 m hm).1]
  rintro ⟨⟨t1, h1, y1, hy1⟩, ⟨t2, h2, y2, hy2⟩⟩
  rw [via_eq JA_step hno hJ h1] at hy1
  rw [via_eq JA_step hno hJ h2] at hy2
  simp only [State.ProcDecided] at hy1 hy2
  have e1 : y1 = 0 := by by_contra hne; simp [hJ.2 y1 hne] at hy1
  have e2 : y2 = 0 := by by_contra hne; simp [hJ.2 y2 hne] at hy2
  subst e1 e2
  rw [hy1] at hy2; simp at hy2

-- `Cslib.FLP.OnePseudoConsensus.nonUniform_step` idx 10: necessary (Paxos on Fin 3, unreachable s = process 0 holding accept(1,true) and accept(1,false), p = 0)
theorem nus10 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.nonUniform_step 10 := fun h => by
  obtain ⟨t, hc, hall⟩ := @h Pr Msg PS _ _ alg (fun _ => true) _ hpc sA sA_nonUniform 0
  exact sA_noBoth hc ⟨hall true, hall false⟩

-- unreachable state: process 0 holds accept(1, true) and prepare 5; prepare 5 blocks the accept
def sB : St := ⟨{⟨0, .inr (.accept 1 true)⟩, ⟨0, .inr (.prepare 5)⟩}, fun _ => ⟨PS.init, none⟩⟩
abbrev mB : Mg := ⟨0, .inr (.prepare 5)⟩

theorem sB_tr : alg.lts.Tr sB (some mB) (alg.recvMsg mB sB) := ⟨by simp [sB], rfl⟩
theorem sB_true : alg.CanDecideWithout sB 1 true :=
  ⟨_, via1 (m := ⟨0, .inr (.accept 1 true)⟩) (by simp) (by simp [sB]), 0, rfl⟩

def JB (t : St) : Prop :=
  (∀ m ∈ t.msgs, m = ⟨0, .inr (.accept 1 true)⟩ ∨ m = ⟨0, .inr (.prepare 5)⟩ ∨
    (m.dest = 2 ∧ ∃ r, m.msg = .inr (.promise 5 r))) ∧
  (t.proc 2).state.cur = 0 ∧ ∀ y, (t.proc y).out ≠ some false

theorem JB_step : ∀ s x s', JB s → alg.lts.Tr s x s' → JB s' := by
  rintro s (_ | m) s' ⟨hm, hc, ho⟩ ht
  · rw [← Algorithm.tr_none ht]; exact ⟨hm, hc, ho⟩
  · obtain ⟨hms, rfl⟩ := ht
    rcases hm m hms with rfl | rfl | ⟨hd, r, hr⟩
    · refine ⟨fun m' hm' => ?_, by rw [recv_proc_ne (by decide)]; exact hc, recv_out_ne ho ?_⟩
      · rcases mem_recv hm' with h | h
        · exact hm m' h
        · simp [h_acc_send] at h
      · rw [h_acc_out]; split <;> simp
    · refine ⟨fun m' hm' => ?_, by rw [recv_proc_ne (by decide)]; exact hc, recv_out_ne ho ?_⟩
      · rcases mem_recv hm' with h | h
        · exact hm m' h
        · rw [h_prep_send] at h; split at h
          · rw [Multiset.mem_singleton] at h; subst h
            exact Or.inr (Or.inr ⟨rfl, _, rfl⟩)
          · simp at h
      · rw [h_prep_out]; simp
    · obtain ⟨d, msg⟩ := m
      simp only at hd hr; subst hd hr
      have hign := h_prom_ign (me := 2) (b := 5) (r := r) (st := (s.proc 2).state) (by simp [hc])
      refine ⟨fun m' hm' => ?_, ?_, recv_out_ne ho (by simp [hign])⟩
      · rcases mem_recv hm' with h | h
        · exact hm m' h
        · simp [hign] at h
      · rw [recv_proc_eq]; simp [hign, hc]

theorem sB_not_false : ¬ alg.CanDecideWithout sB 1 false := by
  rintro ⟨t, h, y, hy⟩
  have hJ : JB t := jinv JB_step ⟨by simp [sB], rfl, fun y => by simp [sB]⟩ (CanReachVia.canReach h)
  exact hJ.2.2 y hy

def JB' (t : St) : Prop :=
  (∀ m ∈ t.msgs, m = ⟨0, .inr (.accept 1 true)⟩ ∨ (m.dest = 2 ∧ ∃ r, m.msg = .inr (.promise 5 r))) ∧
  (t.proc 2).state.cur = 0 ∧ 5 ≤ Pm t 0 ∧ ∀ y, (t.proc y).out ≠ some true

theorem JB'_step : ∀ s x s', JB' s → alg.lts.Tr s x s' → JB' s' := by
  rintro s (_ | m) s' ⟨hm, hc, hp, ho⟩ ht
  · rw [← Algorithm.tr_none ht]; exact ⟨hm, hc, hp, ho⟩
  · obtain ⟨hms, rfl⟩ := ht
    rcases hm m hms with rfl | ⟨hd, r, hr⟩
    · have hign := h_acc_ign (me := 0) (b := 1) (v := true) (st := (s.proc 0).state) (by simp [Pm] at hp ⊢; omega)
      refine ⟨fun m' hm' => ?_, by rw [recv_proc_ne (by decide)]; exact hc, ?_,
        recv_out_ne ho (by simp [hign])⟩
      · rcases mem_recv hm' with h | h
        · exact hm m' h
        · simp [hign] at h
      · simp only [Pm]; rw [recv_proc_eq]; simpa [hign] using hp
    · obtain ⟨d, msg⟩ := m
      simp only at hd hr; subst hd hr
      have hign := h_prom_ign (me := 2) (b := 5) (r := r) (st := (s.proc 2).state) (by simp [hc])
      refine ⟨fun m' hm' => ?_, ?_, ?_, recv_out_ne ho (by simp [hign])⟩
      · rcases mem_recv hm' with h | h
        · exact hm m' h
        · simp [hign] at h
      · rw [recv_proc_eq]; simp [hign, hc]
      · simp only [Pm]; rw [recv_proc_ne (by simp)]; exact hp

theorem sB'_not_true : ¬ alg.CanDecideWithout (alg.recvMsg mB sB) 1 true := by
  rintro ⟨t, h, y, hy⟩
  have h0 : JB' (alg.recvMsg mB sB) := by
    refine ⟨fun m hm => ?_, rfl, by decide, fun y => ?_⟩
    · have e : (alg.recvMsg mB sB).msgs = {⟨0, .inr (.accept 1 true)⟩, ⟨2, .inr (.promise 5 none)⟩} := by
        decide
      rw [e] at hm; simp at hm
      rcases hm with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨rfl, _, rfl⟩
    · fin_cases y <;> decide
  exact (jinv JB'_step h0 (CanReachVia.canReach h)).2.2.2 y hy

-- `Cslib.FLP.OnePseudoConsensus.canDecideWithout_uniform` idx 13: necessary (Paxos on Fin 3, unreachable s: process 0 holds accept(1,true) and prepare 5, m = prepare 5, p = 1, b = true)
theorem cdu13 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.canDecideWithout_uniform 13 := fun h =>
  sB'_not_true (@h Pr Msg PS _ _ alg (fun _ => true) _ hpc sB _ mB true sB_tr 1 sB_true sB_not_false)

-- reachable state: 2 (input false) ran ballot 5 with 0's promise and voted (5, false); accept(5,false) in flight
abbrev inpC : Pr → Bool := ![true, true, false]
-- the run: 2 gets its input, ticks (ballot 5), 0 promises 5, 2 votes (5, false)
def sC1 : St := alg.recvMsg ⟨2, .inl false⟩ (alg.start inpC)
def sC2 : St := alg.recvMsg ⟨2, .inr .tick⟩ sC1
def sC3 : St := alg.recvMsg ⟨0, .inr (.prepare 5)⟩ sC2
def sC : St := alg.recvMsg ⟨2, .inr (.promise 5 none)⟩ sC3
abbrev mC : Mg := ⟨0, .inr (.accept 5 false)⟩

theorem step1 {m : Mg} {s : St} (hm : m ∈ s.msgs) : alg.lts.Tr s (some m) (alg.recvMsg m s) := ⟨hm, rfl⟩

theorem sC_reach : alg.Reachable inpC sC := by
  refine ⟨[some ⟨2, .inl false⟩, some ⟨2, .inr .tick⟩, some ⟨0, .inr (.prepare 5)⟩,
    some ⟨2, .inr (.promise 5 none)⟩], ?_⟩
  refine LTS.MTr.stepL (step1 ?_) (LTS.MTr.stepL (step1 ?_) (LTS.MTr.stepL (step1 ?_)
    (LTS.MTr.stepL (step1 ?_) LTS.MTr.refl)))
  · decide
  · show _ ∈ sC1.msgs; decide
  · show _ ∈ sC2.msgs; decide
  · show _ ∈ sC3.msgs; decide

theorem sC_tr : alg.lts.Tr sC (some mC) (alg.recvMsg mC sC) := step1 (by decide)

-- without 2: 1 gets its input (true), ticks twice (ballots 4, 7), 0 promises 7, 1 votes (7, true), 0 accepts
def sD1 : St := alg.recvMsg ⟨1, .inl true⟩ sC
def sD2 : St := alg.recvMsg ⟨1, .inr .tick⟩ sD1
def sD3 : St := alg.recvMsg ⟨1, .inr .tick⟩ sD2
def sD4 : St := alg.recvMsg ⟨0, .inr (.prepare 7)⟩ sD3
def sD5 : St := alg.recvMsg ⟨1, .inr (.promise 7 none)⟩ sD4
def sD6 : St := alg.recvMsg ⟨0, .inr (.accept 7 true)⟩ sD5

theorem sC_true : alg.CanDecideWithout sC 2 true := by
  refine ⟨sD6, ?_, 0, by decide⟩
  refine (via1 (by simp) ?_).trans ((via1 (by simp) ?_).trans ((via1 (by simp) ?_).trans
    ((via1 (by simp) ?_).trans ((via1 (by simp) ?_).trans (via1 (by simp) ?_)))))
  · decide
  · show _ ∈ sD1.msgs; decide
  · show _ ∈ sD2.msgs; decide
  · show _ ∈ sD3.msgs; decide
  · show _ ∈ sD4.msgs; decide
  · show _ ∈ sD5.msgs; decide

-- after 0 accepts (5, false), false is decided, so true can never be decided (safety)
theorem sC'_not_true : ¬ alg.CanDecideWithout (alg.recvMsg mC sC) 2 true := by
  rintro ⟨t, h, hd⟩
  have hc := CanReachVia.canReach h
  have hr : alg.Reachable inpC t :=
    Algorithm.reachable_stable (Algorithm.reachable_stable sC_reach ⟨_, LTS.MTr.single _ sC_tr⟩) hc
  have hf : t.Decided false := Algorithm.decided_stable ⟨0, by decide⟩ hc
  exact absurd ((safe inpC t hr).1 true false ⟨hd, hf⟩) (by decide)

-- `Cslib.FLP.OnePseudoConsensus.canDecideWithout_uniform` idx 17: necessary (Paxos on Fin 3, inputs (t,t,f): 2 voted (5,false), m = accept(5,false) to 0 decides false; before it, 1 and 0 can still decide true without 2)
theorem cdu17 : ¬ drop0% Cslib.FLP.OnePseudoConsensus.canDecideWithout_uniform 17 := fun h =>
  sC'_not_true (@h Pr Msg PS _ _ alg inpC _ hpc sC _ mC true sC_reach sC_tr 2 sC_true)

end F1c0
