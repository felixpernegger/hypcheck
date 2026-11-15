import Lean.Elab.Command
-- add the library modules your rows need here (e.g. `import Init`, `import Std.Sat.AIG.CNF`); avoid `import Lean`/`import Std` (1.5 GB)
import Init
import Batteries.Control.AlternativeMonad
import Batteries.Control.LawfulMonadState
import Batteries.Control.OptionT
import Batteries.Data.Except
import Batteries.Lean.EStateM
import Batteries.Logic
import Batteries.Classes.Order
import Batteries.Util.Cache

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

set_option linter.deprecated false

namespace HCControl

/-- drop1% T i: drop% T i with all universe parameters of T set to 1 (for refutations
where universe 0 makes the statement hold by proof irrelevance). -/
elab "drop1% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.one
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- indep1% T i: indep% T i with all universe parameters of T set to 1. -/
elab "indep1% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.one
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

/-! ### State-monad models: StateT Nat Id with a tagged, unlawful MonadStateOf Nat -/

/-- StateT Nat Id, tagged by k so that each tag carries its own state instance. -/
def SM (k : Nat) (α : Type) : Type := StateT Nat Id α
instance : Monad (SM k) := inferInstanceAs (Monad (StateT Nat Id))
instance : LawfulMonad (SM k) := inferInstanceAs (LawfulMonad (StateT Nat Id))
/-- Run from state s. -/
def SM.ev (x : SM k α) (s : Nat) : α × Nat := x s
/-- get always returns 0 -/
instance : MonadStateOf Nat (SM 1) where
  get := fun s => (0, s)
  set s := fun _ => (⟨⟩, s)
  modifyGet f := fun s => f s
/-- set is ignored -/
instance : MonadStateOf Nat (SM 2) where
  get := fun s => (s, s)
  set _ := fun s => (⟨⟩, s)
  modifyGet f := fun s => f s
/-- get increments the state -/
instance : MonadStateOf Nat (SM 3) where
  get := fun s => (s, s + 1)
  set s := fun _ => (⟨⟩, s)
  modifyGet f := fun s => f s
/-- modifyGet adds 1 to the new state -/
instance : MonadStateOf Nat (SM 4) where
  get := fun s => (s, s)
  set s := fun _ => (⟨⟩, s)
  modifyGet f := fun s => ((f s).1, (f s).2 + 1)
/-- set adds to the old state -/
instance : MonadStateOf Nat (SM 5) where
  get := fun s => (s, s)
  set s := fun t => (⟨⟩, s + t)
  modifyGet f := fun s => f s
/-- modifyGet doubles the new state -/
instance : MonadStateOf Nat (SM 6) where
  get := fun s => (s, s)
  set s := fun _ => (⟨⟩, s)
  modifyGet f := fun s => ((f s).1, 2 * (f s).2)

/-- Option whose bind always fails (unlawful monad), with a trivial Unit state. -/
def OB (α : Type) : Type := Option α
instance : Monad OB where
  pure := Option.some
  bind _ _ := Option.none
instance : MonadStateOf Unit OB where
  get := Option.some ()
  set _ := Option.some ⟨⟩
  modifyGet f := Option.some (f ()).1
/-- view as an Option -/
def OB.ev (x : OB α) : Option α := x

/-- bind-counting monad: lawful up to a counter that each bind increments. -/
def NC (α : Type) : Type := Nat × α
instance : Monad NC where
  pure a := (0, a)
  bind x f := ((f x.2).1 + x.1 + 1, (f x.2).2)
/-- view as a pair -/
def NC.ev (x : NC α) : Nat × α := x

/-! ### Alternative models: Nat × Option α (a counter and a result), tagged -/

/-- counter + optional result -/
def C (k : Nat) (α : Type) : Type := Nat × Option α
/-- view as a pair -/
def C.ev (x : C k α) : Nat × Option α := x
/-- lawful writer-over-option operations, except map increments the counter -/
instance : Alternative (C 1) where
  pure a := (0, some a)
  map f x := (x.1 + 1, x.2.map f)
  mapConst b x := (x.1 + 1, x.2.map fun _ => b)
  seq f x := ((f : Nat × Option _).1 + (x () : Nat × Option _).1, (f : Nat × Option _).2 <*> (x () : Nat × Option _).2)
  failure := (0, none)
  orElse x y := match (x : Nat × Option _) with
    | (n, some a) => (n, some a)
    | (n, none) => ((y () : Nat × Option _).1 + n, (y () : Nat × Option _).2)
/-- seq increments the counter -/
instance : Alternative (C 2) where
  pure a := (0, some a)
  map f x := ((x : Nat × Option _).1, (x : Nat × Option _).2.map f)
  seq f x := ((f : Nat × Option _).1 + (x () : Nat × Option _).1 + 1, (f : Nat × Option _).2 <*> (x () : Nat × Option _).2)
  failure := (0, none)
  orElse x _ := x
/-- lawful-looking operations, orElse adds the counters non-associatively -/
instance : Alternative (C 5) where
  pure a := (0, some a)
  map f x := ((x : Nat × Option _).1, (x : Nat × Option _).2.map f)
  seq f x := ((f : Nat × Option _).1 + (x () : Nat × Option _).1, (f : Nat × Option _).2 <*> (x () : Nat × Option _).2)
  failure := (0, none)
  orElse x y := ((x : Nat × Option _).1 + 2 * (y () : Nat × Option _).1, (x : Nat × Option _).2 <|> (y () : Nat × Option _).2)
/-- the writer-over-option alternative (lawful) -/
instance : Alternative (C 0) where
  pure a := (0, some a)
  map f x := ((x : Nat × Option _).1, (x : Nat × Option _).2.map f)
  seq f x := ((f : Nat × Option _).1 + (x () : Nat × Option _).1, (f : Nat × Option _).2 <*> (x () : Nat × Option _).2)
  failure := (0, none)
  orElse x y := match (x : Nat × Option _) with
    | (n, some a) => (n, some a)
    | (n, none) => ((y () : Nat × Option _).1 + n, (y () : Nat × Option _).2)
/-- lifting Option into C 0 sets the counter to 1 -/
instance : MonadLift Option (C 0) where
  monadLift x := (1, x)

/-- Option monad whose orElse ignores its second argument (lawful monad). -/
def OA (α : Type) : Type := Option α
instance : AlternativeMonad OA where
  pure := Option.some
  bind := Option.bind
  failure := Option.none
  orElse x _ := x
instance : LawfulMonad OA := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)
/-- Option monad whose orElse ignores its first argument (lawful monad). -/
def OA' (α : Type) : Type := Option α
instance : AlternativeMonad OA' where
  pure := Option.some
  bind := Option.bind
  failure := Option.none
  orElse _ y := y ()
/-- view as an Option -/
def OA.ev (x : OA α) : Option α := x
/-- view as an Option -/
def OA'.ev (x : OA' α) : Option α := x

/-- OptionT (StateT Nat Id) whose bind increments the state after a failure; its applicative
and alternative parts are those of OptionT, so it is LawfulAlternative but not LawfulMonad. -/
def BB (α : Type) : Type := OptionT (StateT Nat Id) α
/-- the OptionT (StateT Nat Id) view -/
abbrev BB.o (x : BB α) : OptionT (StateT Nat Id) α := x
instance : AlternativeMonad BB where
  pure a := (pure a : OptionT (StateT Nat Id) _)
  map f x := (f <$> BB.o x : OptionT (StateT Nat Id) _)
  mapConst b x := (Functor.mapConst b (BB.o x) : OptionT (StateT Nat Id) _)
  seq f x := (BB.o f <*> BB.o (x ()) : OptionT (StateT Nat Id) _)
  seqLeft x y := (BB.o x <* BB.o (y ()) : OptionT (StateT Nat Id) _)
  seqRight x y := (BB.o x *> BB.o (y ()) : OptionT (StateT Nat Id) _)
  failure {α} := (failure : OptionT (StateT Nat Id) α)
  orElse x y := (BB.o x <|> BB.o (y ()) : OptionT (StateT Nat Id) _)
  bind := fun x f => fun s => match (x : Nat → Option _ × Nat) s with
      | (none, s') => (none, s' + 1)
      | (some a, s') => (f a : Nat → Option _ × Nat) s'
instance : LawfulAlternative BB := inferInstanceAs (LawfulAlternative (OptionT (StateT Nat Id)))
/-- run from state s -/
def BB.ev (x : BB α) (s : Nat) : Option α × Nat := x s

/-- failure is not natural: some arbitrary element if the type is nonempty -/
noncomputable def ocFail (α : Type) : Option α :=
  open Classical in
  if h : Nonempty α then some (Classical.choice h) else none
/-- Option with a non-natural failure (lawful monad). -/
def OC (α : Type) : Type := Option α
noncomputable instance : AlternativeMonad OC where
  pure := Option.some
  bind := Option.bind
  failure {α} := ocFail α
  orElse := Option.orElse
instance : LawfulMonad OC := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)
/-- the lawful state instance of StateT Nat Id -/
instance : MonadStateOf Nat (SM 0) := inferInstanceAs (MonadStateOf Nat (StateT Nat Id))
instance : LawfulMonadStateOf Nat (SM 0) := inferInstanceAs (LawfulMonadStateOf Nat (StateT Nat Id))
/-- Option monad whose map always fails (not the bind-derived one). -/
def OM (α : Type) : Type := Option α
instance : Monad OM where
  pure := Option.some
  bind := Option.bind
  map _ _ := Option.none
/-- view as an Option -/
def OM.ev (x : OM α) : Option α := x


-- `LawfulMonadStateOf.toLawfulMonad`: Option with bind always none (OB) and a trivial Unit state: pure_bind fails
theorem c3 : ¬ drop0% LawfulMonadStateOf.toLawfulMonad 4 := fun h =>
  absurd (congrArg OB.ev ((@h Unit OB inferInstance inferInstance).pure_bind 0 (fun n => (pure n : OB Nat)))) (by decide)

-- `LawfulMonadStateOf.modify_comm_of_comp_comm`: lawful StateT Nat Id (SM 0), f = (+1), g = (2*): modify f; modify g differs from modify g; modify f at state 1
theorem a1 : ¬ drop0% LawfulMonadStateOf.modify_comm_of_comp_comm 7 := fun h =>
  absurd (congrArg (SM.ev · 1) (h (σ := Nat) (m := SM 0) (f := (· + 1)) (g := (2 * ·)))) (by decide)

-- `LawfulMonadStateOf.instStateTOfLawfulMonad`: m = Option with bind always none (OB): StateT Unit OB violates pure_bind
theorem a2 : ¬ drop0% LawfulMonadStateOf.instStateTOfLawfulMonad 3 := fun h =>
  absurd (congrArg (fun x => OB.ev (StateT.run x ()))
    ((h (m := OB) (σ := Unit)).pure_bind 0 (fun n => (pure n : StateT Unit OB Nat)))) (by decide)

-- `LawfulMonadStateOf.instReaderTOfLawfulMonad`: m = StateT Nat Id with set ignored (SM 2): ReaderT Unit m violates set_bind_get
theorem a3 : ¬ drop0% LawfulMonadStateOf.instReaderTOfLawfulMonad 6 := fun h =>
  absurd (congrArg (fun x => SM.ev (ReaderT.run x ()) 5)
    ((h (m := SM 2) (σ := Nat) (ρ := Unit)).set_bind_get 3)) (by decide)

-- `LawfulMonadStateOf.instStateRefT'OfLawfulMonad`: m = StateT Nat Id with set ignored (SM 2): StateRefT' Unit Nat m (lifted state) violates set_bind_get, run with an arbitrary ref
theorem a4 : ¬ drop0% LawfulMonadStateOf.instStateRefT'OfLawfulMonad 6 := fun h =>
  absurd (congrArg (fun x => SM.ev (ReaderT.run (x : ReaderT (ST.Ref Unit Nat) (SM 2) Nat) (Classical.ofNonempty)) 5)
    ((h (m := SM 2) (σ := Nat) (ω := Unit)).set_bind_get 3)) (by decide)

-- `OptionT.instLawfulMonadStateOfOfLawfulMonad`: m = StateT Nat Id with set ignored (SM 2): OptionT m violates set_bind_get
theorem a5 : ¬ drop0% OptionT.instLawfulMonadStateOfOfLawfulMonad 5 := fun h =>
  absurd (congrArg (fun x => SM.ev (OptionT.run x) 5)
    ((h (m := SM 2) (σ := Nat)).set_bind_get 3)) (by decide)

-- `OptionT.run_mapConst`: m = Option with map always none (OM): lhs some (some 1), rhs none
theorem a6 : ¬ drop0% OptionT.run_mapConst 4 := fun h =>
  absurd (congrArg OM.ev (h (m := OM) (pure 0 : OptionT OM Nat) 1)) (by decide)

-- `ExceptT.map_mk`: m = Option with map always none (OM): lhs uses bind, rhs uses the broken map
theorem a7 : ¬ drop0% ExceptT.map_mk 5 := fun h =>
  absurd (congrArg (fun x => OM.ev (ExceptT.run x)) (h (m := OM) (ε := Unit) (fun n : Nat => n) (some (Except.ok 0)))) (by decide)

-- `LawfulAlternative.toLawfulApplicative`: Nat x Option alternative whose map increments the counter (C 1): id_map fails
theorem b1 : ¬ drop0% LawfulAlternative.toLawfulApplicative 2 := fun h =>
  absurd (congrArg C.ev ((@h (C 1) inferInstance).id_map (failure : C 1 Nat))) (by decide)

-- `LawfulAlternative.map_failure`: map increments the counter (C 1)
theorem b2 : ¬ drop0% LawfulAlternative.map_failure 2 := fun h =>
  absurd (congrArg C.ev (@h (C 1) inferInstance Nat Nat id)) (by decide)

-- `LawfulAlternative.failure_seq`: seq increments the counter (C 2)
theorem b3 : ¬ drop0% LawfulAlternative.failure_seq 2 := fun h =>
  absurd (congrArg C.ev (@h (C 2) inferInstance Nat Nat (failure : C 2 Nat))) (by decide)

-- `LawfulAlternative.orElse_failure`: Option monad whose orElse ignores its first argument (OA'): some 1 <|> none = none
theorem b4 : ¬ drop0% LawfulAlternative.orElse_failure 2 := fun h =>
  absurd (congrArg OA'.ev (@h OA' inferInstance Nat (pure 1))) (by decide)

-- `LawfulAlternative.failure_orElse`: Option monad whose orElse ignores its second argument (OA): none <|> some 1 = none
theorem b5 : ¬ drop0% LawfulAlternative.failure_orElse 2 := fun h =>
  absurd (congrArg OA.ev (@h OA inferInstance Nat (pure 1))) (by decide)

-- `LawfulAlternative.orElse_assoc`: orElse adds counters as x + 2y (C 5): not associative
theorem b6 : ¬ drop0% LawfulAlternative.orElse_assoc 2 := fun h =>
  absurd (congrArg C.ev (@h (C 5) inferInstance Nat failure failure ((1, none) : Nat × Option Nat))) (by decide)

-- `LawfulAlternative.map_orElse`: map increments the counter (C 1): counts 1 vs 2
theorem b7 : ¬ drop0% LawfulAlternative.map_orElse 2 := fun h =>
  absurd (congrArg C.ev (@h (C 1) inferInstance Nat Nat failure failure id)) (by decide)

-- `mapConst_failure`: mapConst increments the counter (C 1)
theorem b8 : ¬ drop0% mapConst_failure 4 := fun h =>
  absurd (congrArg C.ev (h (m := C 1) (α := Nat) (0 : Nat))) (by decide)

-- `mapConst_orElse`: mapConst increments the counter (C 1): counts 1 vs 2
theorem b9 : ¬ drop0% mapConst_orElse 4 := fun h =>
  absurd (congrArg C.ev (h (m := C 1) (failure : C 1 Nat) failure (0 : Nat))) (by decide)

-- `failure_seqLeft`: seq increments the counter (C 2)
theorem b10 : ¬ drop0% failure_seqLeft 4 := fun h =>
  absurd (congrArg C.ev (h (m := C 2) (β := Nat) (failure : C 2 Nat))) (by decide)

-- `failure_seqRight`: seq increments the counter (C 2)
theorem b11 : ¬ drop0% failure_seqRight 4 := fun h =>
  absurd (congrArg C.ev (h (m := C 2) (β := Nat) (failure : C 2 Nat))) (by decide)

-- `failure_bind`: OptionT (StateT Nat Id) with its own lawful alternative part but a bind that increments the state after a failure (BB)
theorem b12 : ¬ drop0% failure_bind 5 := fun h =>
  absurd (congrArg (BB.ev · 0) (h (m := BB) (α := Nat) (β := Nat) (fun n => pure n))) (by decide)

-- `LawfulAlternativeLift.monadLift_failure`: lift Option -> Nat x Option (C 0) sets the counter to 1
theorem b13 : ¬ drop0% LawfulAlternativeLift.monadLift_failure 5 := fun h =>
  absurd (congrArg C.ev (@h Option (C 0) inferInstance inferInstance inferInstance Nat)) (by decide)

-- `LawfulAlternativeLift.monadLift_orElse`: lift Option -> Nat x Option (C 0) sets the counter to 1: none <|> none gives counts 1 vs 2
theorem b14 : ¬ drop0% LawfulAlternativeLift.monadLift_orElse 5 := fun h =>
  absurd (congrArg C.ev (@h Option (C 0) inferInstance inferInstance inferInstance Nat none none)) (by decide)

-- `OptionT.instLawfulAlternativeOfLawfulMonad`: m = bind-counting monad Nat x a (NC): f <$> failure costs a bind, failure does not
theorem b15 : ¬ drop0% OptionT.instLawfulAlternativeOfLawfulMonad 2 := fun h =>
  absurd (congrArg (fun x => NC.ev (OptionT.run x)) ((h NC).map_failure (α := Nat) id)) (by decide)

-- `StateT.instLawfulAlternativeOfLawfulMonad`: m = Option monad with orElse ignoring its second argument (OA): failure_orElse fails in StateT Unit m
theorem b16 : ¬ drop0% StateT.instLawfulAlternativeOfLawfulMonad 3 := fun h =>
  absurd (congrArg (fun x => OA.ev (StateT.run x ()))
    ((h (σ := Unit) OA).failure_orElse (pure 1 : StateT Unit OA Nat))) (by decide)

-- `StateT.instLawfulAlternativeOfLawfulMonad`: m = BB (lawful alternative, bind increments the state after failure): failure_seq fails in StateT Unit m
theorem b17 : ¬ drop0% StateT.instLawfulAlternativeOfLawfulMonad 4 := fun h =>
  absurd (congrArg (fun x => BB.ev (StateT.run x ()) 0)
    ((h (σ := Unit) BB).failure_seq (β := Nat) (pure 0 : StateT Unit BB Nat))) (by decide)

-- `StateT.instLawfulAlternativeLiftOfLawfulAlternativeOfLawfulMonad`: m = BB: StateT.lift failure binds and increments the state, monadLift_failure fails
theorem b18 : ¬ drop0% StateT.instLawfulAlternativeLiftOfLawfulAlternativeOfLawfulMonad 4 := fun h =>
  absurd (congrArg (fun x => BB.ev (StateT.run x ()) 0)
    ((h (σ := Unit) BB).monadLift_failure (α := Nat))) (by decide)

-- `ReaderT.instLawfulAlternative`: m = OA (orElse ignores its second argument): failure_orElse fails
theorem b19 : ¬ drop0% ReaderT.instLawfulAlternative 3 := fun h =>
  absurd (congrArg (fun x => OA.ev (ReaderT.run x ()))
    ((h (ρ := Unit) (m := OA)).failure_orElse (pure 1 : ReaderT Unit OA Nat))) (by decide)

-- `StateRefT'.instLawfulAlternative`: m = OA (orElse ignores its second argument): failure_orElse fails, run with an arbitrary ref
theorem b20 : ¬ drop0% StateRefT'.instLawfulAlternative 4 := fun h =>
  absurd (congrArg (fun x => OA.ev (ReaderT.run (x : ReaderT (ST.Ref Unit Nat) OA Nat) Classical.ofNonempty))
    ((h (ω := Unit) (σ := Nat) (m := OA)).failure_orElse (pure 1))) (by decide)

-- `failure_bind`: Option monad (lawful) with a non-natural failure some (choice) on nonempty types (OC): failure >>= (fun _ => none) = none
theorem o1 : ¬ drop0% failure_bind 4 := fun h => by
  have e := h (m := OC) (α := Nat) (β := Nat) (fun _ => (Option.none : Option Nat))
  change Option.bind (ocFail Nat) _ = ocFail Nat at e
  rw [ocFail, dif_pos ⟨0⟩] at e
  cases e

-- `seq_failure`: OC (non-natural failure some c): pure (+1) <*> failure = some (c+1), pure (+1) *> failure = some c
theorem o2 : ¬ drop0% seq_failure 4 := fun h => by
  have e := h (m := OC) (α := Nat) (β := Nat) (pure (fun n => n + 1))
  change Option.bind (some (fun n : Nat => n + 1)) (fun g => Option.bind (ocFail Nat) (fun a => some (g a))) =
    Option.bind (some (fun n : Nat => n + 1)) (fun _ => ocFail Nat) at e
  rw [ocFail, dif_pos ⟨0⟩] at e
  exact Nat.succ_ne_self _ (Option.some.inj e)

-- `StateT.instLawfulAlternativeLiftOfLawfulAlternativeOfLawfulMonad`: m = OC, sigma = Bool, alpha = Unit: lift failure at state b is some ((), b) for both b, but failure is a single value
theorem o3 : ¬ drop0% StateT.instLawfulAlternativeLiftOfLawfulAlternativeOfLawfulMonad 3 := fun h => by
  have e := (h (σ := Bool) OC).monadLift_failure (α := Unit)
  have k : ∀ b : Bool, ocFail (Unit × Bool) = some ((), b) := by
    intro b
    have e1 := congrArg (fun x => StateT.run x b) e
    have hU : ocFail Unit = some () := by rw [ocFail, dif_pos ⟨()⟩]
    change Option.bind (ocFail Unit) (fun a => some (a, b)) = ocFail (Unit × Bool) at e1
    rw [hU] at e1
    exact e1.symm
  have := (k true).symm.trans (k false)
  simp at this

-- `seq_failure`: LawfulMonad not needed: write failure = PEmpty.elim <$> failure (map_failure), then x <*> failure and x *> failure both equal (fun _ => PEmpty.elim) <$> x <*> failure by the LawfulApplicative laws
theorem r1 : drop% seq_failure 5 := by
  intro m α β _ _ x
  have h1 : ∀ {γ}, (failure : m γ) = PEmpty.elim <$> (failure : m PEmpty) :=
    (map_failure _).symm
  have h2 : ∀ {γ δ} (y : m (γ → δ)), y <*> (PEmpty.elim <$> (failure : m PEmpty)) =
      ((fun f => f ∘ PEmpty.elim) <$> y) <*> failure := by
    intro γ δ y
    rw [← pure_seq, seq_assoc, seq_pure, ← comp_map]; rfl
  have e1 : x <*> (failure : m α) = ((fun f => f ∘ PEmpty.elim) <$> x) <*> failure := by
    rw [h1]; exact h2 x
  have e2 : (Function.const _ id <$> x) <*> (failure : m β) =
      ((fun f => f ∘ PEmpty.elim) <$> (Function.const _ id <$> x)) <*> failure := by
    rw [h1]; exact h2 _
  rw [seqRight_eq, e1, e2, ← comp_map]
  congr 2
  funext f e
  exact e.elim

/-- Unit ≠ Bool -/

theorem unit_ne_bool : Unit ≠ Bool := fun e => by
  have h2 : ∀ x y : Unit, x = y := fun _ _ => rfl
  rw [e] at h2
  exact absurd (h2 true false) (by decide)

-- `congrFun₂`: universe 1, f = fun _ _ => true, g = fun _ _ => false on Bool
theorem l1 : ¬ drop1% congrFun₂ 5 := fun h =>
  absurd (h (f := fun (_ : Bool) (_ : Bool) => true) (g := fun _ _ => false) true true) (by decide)

-- `congr_fun₂`: twin of congrFun₂: same Bool counterexample
theorem l2 : ¬ drop1% congr_fun₂ 5 := fun h =>
  absurd (h (f := fun (_ : Bool) (_ : Bool) => true) (g := fun _ _ => false) true true) (by decide)

-- `congrFun₃`: universe 1, constant true/false functions on Bool
theorem l3 : ¬ drop1% congrFun₃ 6 := fun h =>
  absurd (h (f := fun (_ : Bool) (_ : Bool) (_ : Bool) => true) (g := fun _ _ _ => false) true true true) (by decide)

-- `congr_fun₃`: twin of congrFun₃: same Bool counterexample
theorem l4 : ¬ drop1% congr_fun₃ 6 := fun h =>
  absurd (h (f := fun (_ : Bool) (_ : Bool) (_ : Bool) => true) (g := fun _ _ _ => false) true true true) (by decide)

-- `congr_fun`: universe 1, constant true/false functions on Bool
theorem l5 : ¬ drop1% congr_fun 4 := fun h =>
  absurd (h (f := fun (_ : Bool) => true) (g := fun _ => false) true) (by decide)

-- `funext₂`: universe 1, constant true/false functions on Bool are not equal
theorem l6 : ¬ drop1% funext₂ 5 := fun h =>
  absurd (congrFun (congrFun (h (f := fun (_ : Bool) (_ : Bool) => true) (g := fun _ _ => false)) true) true) (by decide)

-- `funext₃`: universe 1, constant true/false functions on Bool are not equal
theorem l7 : ¬ drop1% funext₃ 6 := fun h =>
  absurd (congrFun (congrFun (congrFun
    (h (f := fun (_ : Bool) (_ : Bool) (_ : Bool) => true) (g := fun _ _ _ => false)) true) true) true) (by decide)

-- `heq_of_cast_eq`: alpha = Unit, beta = Bool (Unit ≠ Bool by cardinality)
theorem l8 : ¬ indep1% heq_of_cast_eq 4 := fun h =>
  unit_ne_bool (h (α := Unit) (β := Bool) (a := ()) (a' := true))

-- `cast_eq_iff_heq`: alpha = Unit, beta = Bool (Unit ≠ Bool by cardinality)
theorem l9 : ¬ indep1% cast_eq_iff_heq 2 := fun h =>
  unit_ne_bool (@h Unit Bool () true)

-- `eqRec_eq_cast`: alpha = Bool, a = true, a' = false, motive Unit
theorem l10 : ¬ indep1% eqRec_eq_cast 5 := fun h =>
  absurd (h (α := Bool) (a := true) (motive := fun _ _ => Unit) () (a' := false)) (by decide)

-- `eqRec_heq_self`: alpha = Bool, a = true, a' = false, motive Unit
theorem l11 : ¬ indep1% eqRec_heq_self 5 := fun h =>
  absurd (h (α := Bool) (a := true) (motive := fun _ _ => Unit) () (a' := false)) (by decide)

-- `eqRec_heq_iff_heq`: alpha = Bool, a = true, a' = false, motive Unit
theorem l12 : ¬ indep1% eqRec_heq_iff_heq 5 := fun h =>
  absurd (h (α := Bool) (a := true) (motive := fun _ _ => Unit) (x := ()) (a' := false) (β := Unit) (y := ())) (by decide)

-- `heq_eqRec_iff_heq`: alpha = Bool, a = true, a' = false, motive Unit
theorem l13 : ¬ indep1% heq_eqRec_iff_heq 5 := fun h =>
  absurd (h (α := Bool) (a := true) (motive := fun _ _ => Unit) (x := ()) (a' := false) (β := Unit) (y := ())) (by decide)

-- `congr_eqRec`: alpha = Bool, x = true, x' = false
theorem l14 : ¬ indep1% congr_eqRec 6 := fun h =>
  absurd (h (α := Bool) (γ := Bool) (x := true) (x' := false) (β := fun _ => Unit) (fun _ _ => true) ()) (by decide)

-- `EStateM.ext`: pure true ≠ pure false in EStateM Unit Unit Bool
theorem e1 : ¬ drop0% EStateM.ext 5 := fun h =>
  absurd (congrArg (fun z => EStateM.run z ()) (h (ε := Unit) (x := (pure true : EStateM Unit Unit Bool)) (y := pure false)))
    (by intro e; cases e)

-- `Batteries.Tactic.instNonemptyDeclCache`: DeclCache α is always nonempty: Cache α is an IO.Ref of a nonempty sum (MetaM α via throwError), and both functions can be fun _ _ a => pure a
theorem d1 : drop% Batteries.Tactic.instNonemptyDeclCache 1 := fun {α} =>
  have : Nonempty (MetaM α ⊕ Task (Except Exception α)) := ⟨.inl (throwError "")⟩
  ⟨⟨Classical.ofNonempty, fun _ _ a => pure a, fun _ _ a => pure a⟩⟩

/-- an Ord Nat that is not oriented -/

@[instance_reducible] def badOrd : Ord Nat := ⟨fun a b => if a = b then .eq else .lt⟩

/-- the constant Ord Nat (oriented) -/

@[instance_reducible] def eqOrd : Ord Nat := ⟨fun _ _ => .eq⟩

theorem eqOrd_oriented : @Std.OrientedOrd Nat eqOrd := ⟨fun {_ _} => rfl⟩

-- `Std.OrientedOrd.instOn`: beta = Nat with compare a b = if a = b then eq else lt, f = id: compare 0 1 = lt, swap of compare 1 0 = gt
theorem k1 : ¬ drop0% Std.OrientedOrd.instOn 3 := fun h =>
  absurd (@Std.OrientedCmp.eq_swap Nat _ (h (ord := badOrd) (id : Nat → Nat)) 0 1) (by decide)

-- `Std.OrientedOrd.instOrdLex'`: ord1 = unoriented (eq if equal else lt), ord2 = Nat order: lex compares 0 1 and 1 0 both as lt
theorem k2 : ¬ drop0% Std.OrientedOrd.instOrdLex' 3 := fun h =>
  absurd (@Std.OrientedCmp.eq_swap Nat _ (@h Nat badOrd instOrdNat inferInstance) 0 1) (by decide)

-- `Std.OrientedOrd.instOrdLex'`: ord1 = constant eq (oriented), ord2 = unoriented: lex compares 0 1 and 1 0 both as lt
theorem k3 : ¬ drop0% Std.OrientedOrd.instOrdLex' 4 := fun h =>
  absurd (@Std.OrientedCmp.eq_swap Nat _ (@h Nat eqOrd badOrd eqOrd_oriented) 0 1) (by decide)

/-- Bool with an empty < -/

def B2 : Type := Bool

instance : LT B2 := ⟨fun _ _ => False⟩

instance : DecidableEq B2 := inferInstanceAs (DecidableEq Bool)

instance (x y : B2) : Decidable (x < y) := isFalse id

theorem B2_lawful : Std.LawfulLTCmp (fun _ _ : B2 => Ordering.eq) :=
  { toOrientedCmp := ⟨fun {_ _} => rfl⟩, eq_lt_iff_lt := fun {_ _} => ⟨fun h => (nomatch h), fun h => (h : False).elim⟩ }

-- `Std.LawfulLTCmp.eq_compareOfLessAndEq`: Bool with empty <, cmp = constant eq (oriented, LawfulLTCmp): cmp true false = eq but compareOfLessAndEq = gt
theorem k4 : ¬ drop0% Std.LawfulLTCmp.eq_compareOfLessAndEq 4 := fun h =>
  absurd (@h B2 (fun _ _ => .eq) inferInstance inferInstance B2_lawful true false (isFalse id)) (by decide)

/-- Bool with < always true and ≤ always false -/

def B3 : Type := Bool

instance : LT B3 := ⟨fun _ _ => True⟩

instance : LE B3 := ⟨fun _ _ => False⟩

instance : DecidableEq B3 := inferInstanceAs (DecidableEq Bool)

instance : DecidableLT B3 := fun _ _ => instDecidableTrue

-- `Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm`: Bool with < always True and ≤ always False (tool witness): compareOfLessAndEq is constant lt, not oriented
theorem k5 : ¬ drop0% Std.LawfulLECmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm 5 := fun h => by
  haveI := h (α := B3) (fun _ _ => trivial) ⟨fun h => (h trivial).elim, fun h => h.elim⟩ (fun h _ => h.elim)
  exact absurd (Std.OrientedCmp.eq_swap (cmp := fun x y : B3 => compareOfLessAndEq x y) (a := true) (b := true)) (by decide)

-- `Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm`: Bool with < always True and ≤ always False (tool witness): compareOfLessAndEq is constant lt, not oriented
theorem k6 : ¬ drop0% Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm 5 := fun h => by
  haveI := h (α := B3) (fun _ _ => trivial) ⟨fun h => (h trivial).elim, fun h => h.elim⟩ (fun h _ => h.elim)
  exact absurd (Std.OrientedCmp.eq_swap (cmp := fun x y : B3 => compareOfLessAndEq x y) (a := true) (b := true)) (by decide)

-- `LawfulMonadStateOf.modifyGet_eq`: get returns 0 (SM 1): modifyGet reads the real state, the get-based form reads 0
theorem s0 : ¬ drop0% LawfulMonadStateOf.modifyGet_eq 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (@h Nat (SM 1) inferInstance inferInstance Nat (fun s => (s, s)))) (by decide)

-- `LawfulMonadStateOf.get_bind_const`: get increments the state (SM 3)
theorem s1 : ¬ drop0% LawfulMonadStateOf.get_bind_const 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (@h Nat (SM 3) inferInstance inferInstance Nat (pure 0))) (by decide)

-- `LawfulMonadStateOf.get_bind_get_bind`: get increments the state (SM 3)
theorem s2 : ¬ drop0% LawfulMonadStateOf.get_bind_get_bind 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (@h Nat (SM 3) inferInstance inferInstance Nat (fun _ s' => pure s'))) (by decide)

-- `LawfulMonadStateOf.get_bind_set_bind`: get returns 0 (SM 1), so set (← get) resets the state
theorem s3 : ¬ drop0% LawfulMonadStateOf.get_bind_set_bind 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (@h Nat (SM 1) inferInstance inferInstance Nat (fun s _ => pure s))) (by decide)

-- `LawfulMonadStateOf.set_bind_get`: set is ignored (SM 2)
theorem s4 : ¬ drop0% LawfulMonadStateOf.set_bind_get 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (@h Nat (SM 2) inferInstance inferInstance 3)) (by decide)

-- `LawfulMonadStateOf.set_bind_set`: set adds to the old state (SM 5)
theorem s5 : ¬ drop0% LawfulMonadStateOf.set_bind_set 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (@h Nat (SM 5) inferInstance inferInstance 1 2)) (by decide)

-- `LawfulMonadStateOf.get_seqRight`: get increments the state (SM 3)
theorem s6 : ¬ drop0% LawfulMonadStateOf.get_seqRight 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 3) (pure 0))) (by decide)

-- `LawfulMonadStateOf.seqLeft_get`: get increments the state (SM 3)
theorem s7 : ¬ drop0% LawfulMonadStateOf.seqLeft_get 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 3) (pure 0))) (by decide)

-- `LawfulMonadStateOf.get_map_const`: get increments the state (SM 3)
theorem s8 : ¬ drop0% LawfulMonadStateOf.get_map_const 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 3) 0)) (by decide)

-- `LawfulMonadStateOf.get_bind_get`: get increments the state (SM 3)
theorem s9 : ¬ drop0% LawfulMonadStateOf.get_bind_get 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 3) )) (by decide)

-- `LawfulMonadStateOf.get_bind_set`: get returns 0 (SM 1)
theorem s10 : ¬ drop0% LawfulMonadStateOf.get_bind_set 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 1) )) (by decide)

-- `LawfulMonadStateOf.get_bind_map_set`: get returns 0 (SM 1)
theorem s11 : ¬ drop0% LawfulMonadStateOf.get_bind_map_set 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 1) (fun _ _ => (0 : Nat)))) (by decide)

-- `LawfulMonadStateOf.set_bind_get_bind`: set is ignored (SM 2)
theorem s12 : ¬ drop0% LawfulMonadStateOf.set_bind_get_bind 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 2) 3 pure)) (by decide)

-- `LawfulMonadStateOf.set_bind_map_get`: set is ignored (SM 2)
theorem s13 : ¬ drop0% LawfulMonadStateOf.set_bind_map_get 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 2) id 3)) (by decide)

-- `LawfulMonadStateOf.set_bind_set_bind`: set adds to the old state (SM 5)
theorem s14 : ¬ drop0% LawfulMonadStateOf.set_bind_set_bind 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 5) 1 2 (pure 0))) (by decide)

-- `LawfulMonadStateOf.set_bind_map_set`: set adds to the old state (SM 5)
theorem s15 : ¬ drop0% LawfulMonadStateOf.set_bind_map_set 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 5) 1 2 id)) (by decide)

-- `LawfulMonadStateOf.modifyGetThe_eq`: get returns 0 (SM 1)
theorem s16 : ¬ drop0% LawfulMonadStateOf.modifyGetThe_eq 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 1) (fun s => (s, s)))) (by decide)

-- `LawfulMonadStateOf.modify_eq`: get returns 0 (SM 1)
theorem s17 : ¬ drop0% LawfulMonadStateOf.modify_eq 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 1) id)) (by decide)

-- `LawfulMonadStateOf.modifyThe_eq`: get returns 0 (SM 1)
theorem s18 : ¬ drop0% LawfulMonadStateOf.modifyThe_eq 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 1) id)) (by decide)

-- `LawfulMonadStateOf.getModify_eq`: get returns 0 (SM 1)
theorem s19 : ¬ drop0% LawfulMonadStateOf.getModify_eq 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 1) id)) (by decide)

-- `LawfulMonadStateOf.modifyGet_eq'`: get returns 0 (SM 1)
theorem s20 : ¬ drop0% LawfulMonadStateOf.modifyGet_eq' 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 1) (fun s => (s, s)))) (by decide)

-- `LawfulMonadStateOf.modify_id`: modifyGet adds 1 to the new state (SM 4)
theorem s21 : ¬ drop0% LawfulMonadStateOf.modify_id 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 4) )) (by decide)

-- `LawfulMonadStateOf.getModify_id`: modifyGet adds 1 to the new state (SM 4)
theorem s22 : ¬ drop0% LawfulMonadStateOf.getModify_id 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 4) )) (by decide)

-- `LawfulMonadStateOf.set_bind_modify`: modifyGet adds 1 to the new state (SM 4)
theorem s23 : ¬ drop0% LawfulMonadStateOf.set_bind_modify 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 4) 3 id)) (by decide)

-- `LawfulMonadStateOf.set_bind_modify_bind`: modifyGet adds 1 to the new state (SM 4)
theorem s24 : ¬ drop0% LawfulMonadStateOf.set_bind_modify_bind 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 4) 3 id (fun _ => pure 0))) (by decide)

-- `LawfulMonadStateOf.set_bind_modifyGet`: modifyGet adds 1 to the new state (SM 4)
theorem s25 : ¬ drop0% LawfulMonadStateOf.set_bind_modifyGet 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 4) 3 (fun s => (s, s)))) (by decide)

-- `LawfulMonadStateOf.set_bind_modifyGet_bind`: modifyGet adds 1 to the new state (SM 4)
theorem s26 : ¬ drop0% LawfulMonadStateOf.set_bind_modifyGet_bind 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 4) 3 (fun s => (s, s)) pure)) (by decide)

-- `LawfulMonadStateOf.set_bind_getModify`: modifyGet adds 1 to the new state (SM 4)
theorem s27 : ¬ drop0% LawfulMonadStateOf.set_bind_getModify 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 4) 3 id)) (by decide)

-- `LawfulMonadStateOf.set_bind_getModify_bind`: modifyGet adds 1 to the new state (SM 4)
theorem s28 : ¬ drop0% LawfulMonadStateOf.set_bind_getModify_bind 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 4) 3 id pure)) (by decide)

-- `LawfulMonadStateOf.modify_bind_modify`: modifyGet adds 1 to the new state (SM 4)
theorem s29 : ¬ drop0% LawfulMonadStateOf.modify_bind_modify 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 4) id id)) (by decide)

-- `LawfulMonadStateOf.modify_bind_modifyGet`: modifyGet adds 1 to the new state (SM 4)
theorem s30 : ¬ drop0% LawfulMonadStateOf.modify_bind_modifyGet 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 4) id (fun s => (s, s)))) (by decide)

-- `LawfulMonadStateOf.getModify_bind_modify`: modifyGet adds 1 to the new state (SM 4)
theorem s31 : ¬ drop0% LawfulMonadStateOf.getModify_bind_modify 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 4) id (fun _ => id))) (by decide)

-- `LawfulMonadStateOf.modify_comm_of_comp_comm`: modifyGet doubles the new state (SM 6); f = id, g = (· + 1) commute
theorem s32 : ¬ drop0% LawfulMonadStateOf.modify_comm_of_comp_comm 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 6) (f := id) (g := (· + 1)) rfl)) (by decide)

-- `LawfulMonadStateOf.modify_bind_get`: modifyGet adds 1 to the new state (SM 4)
theorem s33 : ¬ drop0% LawfulMonadStateOf.modify_bind_get 4 := fun h =>
  absurd (congrArg (SM.ev · 5) (h (σ := Nat) (m := SM 4) id)) (by decide)

end HCControl
