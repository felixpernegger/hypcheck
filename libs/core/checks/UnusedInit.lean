import Lean
/-!
Removable hypotheses that the library's own proof does not use (`scripts/Unused.lean`). Generated
by `scripts/unused_proofs.py`; do not edit by hand.

`drop_unused% T i` is the proof term of `T` with binder `i` dropped. It fails unless binder `i`
does not occur in the proof, nothing in the statement depends on it, and the result has exactly the
stated type `T'` (checked with `isDefEq`); the kernel then checks the declaration as usual.
-/

open Lean Elab Term Meta in
/-- `T'`: the statement of `T` without binder `i`. Used as the statement where the printed one does
not elaborate back. -/
elab "drop_type% " id:ident i:num : term => do
  let ci ← getConstInfo id.getId
  forallTelescope ci.type fun xs body => mkForallFVars (xs.eraseIdxIfInBounds i.getNat) body

open Lean Elab Term Meta in
elab "drop_unused% " id:ident i:num : term <= expectedType => do
  let n := id.getId
  let i := i.getNat
  let ci ← getConstInfo n
  let some v := ci.value? (allowOpaque := true) | throwError "{n} has no proof term"
  forallTelescope ci.type fun xs body => lambdaBoundedTelescope v xs.size fun ys b => do
    unless ys.size == xs.size do throwError "the proof of {n} has fewer binders than its statement"
    let some x := ys[i]? | throwError "{n} has no binder {i}"
    if b.containsFVar x.fvarId! then throwError "binder {i} of {n} is used in its proof"
    let rest := ys.eraseIdxIfInBounds i
    let ty ← mkForallFVars rest (body.replaceFVars xs ys)
    unless ← isDefEq ty expectedType do
      throwError "{n} without binder {i} is{indentExpr ty}\nnot the stated{indentExpr expectedType}"
    -- universe parameters that only the proof uses (not `T'`) are set to 0
    let pf ← mkLambdaFVars rest b
    let inTy := (collectLevelParams {} ty).params
    let extra := ci.levelParams.filter (!inTy.contains ·)
    return pf.instantiateLevelParams extra (extra.map fun _ => Level.zero)

-- `Std.Iter.foldM_mapWithPostcondition` idx 12: unused in the library's proof
theorem HypCheckProof.Std.Iter.foldM_mapWithPostcondition.h12.{w, w', w'', w'''} :
    ∀ {m : Type w → Type w'} {α β γ δ : Type w} {n : Type w → Type w''} {o : Type w → Type w'''}
      [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst] [inst_2 : Monad m] [inst_3 : Monad n]
      [inst_4 : Monad o] [inst_5 : @LawfulMonad n inst_3] [inst_6 : @LawfulMonad o inst_4]
      [inst_7 : @Std.IteratorLoop α Id β inst n] [inst_8 : @Std.IteratorLoop α Id β inst o]
      [inst_9 : @Std.LawfulIteratorLoop β α Id n Id.instMonad inst_3 inst inst_7]
      [inst_10 : @Std.LawfulIteratorLoop β α Id o Id.instMonad inst_4 inst inst_8] [inst_11 : MonadLiftT n o]
      [inst_12 : @LawfulMonadLiftT n o inst_3 inst_4 inst_11] {f : β → Std.Iterators.PostconditionT n γ} {g : δ → γ → o δ}
      {init : δ} {it : @Std.Iter α β},
      @Eq (o δ)
        (@Std.IterM.foldM n o inst_4
          (@Std.Iterators.Types.Map α β γ Id n
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id n
                (@Id.instMonadLiftTOfPure n (@Applicative.toPure n (@Monad.toApplicative n inst_3))) x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_3)) f)
          γ δ
          (@Std.Iterators.Types.Map.instIterator α β γ Id n inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id n
                (@Id.instMonadLiftTOfPure n (@Applicative.toPure n (@Monad.toApplicative n inst_3))) x)
            f)
          (@Std.Iterators.Types.Map.instIteratorLoop α β γ Id n o inst_3 inst_4 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id n
                (@Id.instMonadLiftTOfPure n (@Applicative.toPure n (@Monad.toApplicative n inst_3))) x)
            f)
          inst_11 g init (@Std.Iter.mapWithPostcondition α β γ inst n inst_3 f it))
        (@Std.Iter.foldM o inst_4 α β δ inst inst_8
          (fun (d : δ) (b : β) =>
            @Bind.bind o (@Monad.toBind o inst_4) γ δ
              (@liftM n o inst_11 γ (@Std.Iterators.PostconditionT.run n inst_3 γ (f b))) fun (c : γ) => g d c)
          init it) :=
  no_implicit_lambda% (drop_unused% Std.Iter.foldM_mapWithPostcondition 12)

-- `Std.IterM.all_mapM` idx 16: unused in the library's proof
theorem HypCheckProof.Std.IterM.all_mapM.h16.{w, w', w''} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : @Std.IteratorLoop α m β inst m]
      [inst_4 : Monad m] [inst_5 : @LawfulMonad m inst_4] [inst_6 : Monad n] [inst_7 : MonadAttach n]
      [inst_8 : @LawfulMonad n inst_6] [inst_9 : @WeaklyLawfulMonadAttach n inst_6 inst_7]
      [inst_10 : @LawfulMonadLiftT m n inst_4 inst_6 inst_2] {it : @Std.IterM α m β} {f : β → n β'} {p : β' → Bool},
      @Eq (n (ULift Bool))
        (@Std.IterM.all
          (@Std.Iterators.Types.Map α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_7 (f b))
          β' n inst_6
          (@Std.Iterators.Types.Map.instIterator α β β' m n inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_7 (f b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β' m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_7 (f b))
          p (@Std.IterM.mapM α β β' m n inst inst_6 inst_7 inst_2 f it))
        (@Std.IterM.allM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          β n inst_6
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (fun (x : β) =>
            @Functor.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) β' (ULift Bool)
              (fun (x : β') => @ULift.up Bool (p x)) (f x))
          (@Std.IterM.mapM α β β m n inst inst_6 inst_7 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.all_mapM 16)

-- `Std.IterM.all_filterM` idx 15: unused in the library's proof
theorem HypCheckProof.Std.IterM.all_filterM.h15.{w, w', w''} :
    ∀ {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : @Std.IteratorLoop α m β inst m]
      [inst_4 : Monad m] [inst_5 : @LawfulMonad m inst_4] [inst_6 : Monad n] [inst_7 : MonadAttach n]
      [inst_8 : @LawfulMonad n inst_6] [inst_9 : @WeaklyLawfulMonadAttach n inst_6 inst_7]
      [inst_10 : @LawfulMonadLiftT m n inst_4 inst_6 inst_2] {it : @Std.IterM α m β} {f : β → n (ULift Bool)}
      {p : β → Bool},
      @Eq (n (ULift Bool))
        (@Std.IterM.all
          (@Std.Iterators.Types.FilterMap α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_7 (f b)))
          β n inst_6
          (@Std.Iterators.Types.FilterMap.instIterator α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (fun (b : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) (ULift Bool)
                (Option β)
                (fun (x : ULift Bool) =>
                  @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                    (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_7 (f b)))
            inst inst_6)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_7 (f b)))
          p (@Std.IterM.filterM α β m n inst inst_6 inst_7 inst_2 f it))
        (@Std.IterM.allM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          β n inst_6
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (fun (x : β) =>
            @Bind.bind n (@Monad.toBind n inst_6) (ULift Bool) (ULift Bool) (f x) fun (__do_lift : ULift Bool) =>
              @ite (n (ULift Bool)) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
                (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true)
                (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) (ULift Bool) (@ULift.up Bool (p x)))
                (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) (ULift Bool)
                  (@ULift.up Bool Bool.true)))
          (@Std.IterM.mapM α β β m n inst inst_6 inst_7 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.all_filterM 15)

-- `Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition.h6.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : Monad n]
      [inst_2 : MonadAttach n] [inst_3 : @LawfulMonad n inst_1] [inst_4 : @WeaklyLawfulMonadAttach n inst_1 inst_2]
      [inst_5 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_1 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n (Option γ)} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b))
          n inst_1 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b)) inst inst_1)
          (@Std.IterM.filterMapM α β γ m n inst inst_1 inst_2 inst_5 f it))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b))
          n inst_1 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b)) inst inst_1)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition 6)

-- `Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition` idx 9: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition.h9.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @WeaklyLawfulMonadAttach n inst_2 inst_3]
      [inst_5 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_2 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n (Option γ)} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapM α β γ m n inst inst_2 inst_3 inst_5 f it))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition 9)

-- `Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition` idx 10: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition.h10.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @LawfulMonad n inst_2] [inst_5 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n (Option γ)} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapM α β γ m n inst inst_2 inst_3 inst_5 f it))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition 10)

-- `Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition` idx 12: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition.h12.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst : @LawfulMonad m inst]
      [inst : Monad n] [inst_1 : MonadAttach n] [inst_2 : @LawfulMonad n inst]
      [inst_3 : @WeaklyLawfulMonadAttach n inst inst_1] [inst_4 : MonadLiftT m n] [inst_5 : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst_5] {f : β → n (Option γ)} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b))
          n inst γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b)) inst_5 inst)
          (@Std.IterM.filterMapM α β γ m n inst_5 inst inst_1 inst_4 f it))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b))
          n inst γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b)) inst_5 inst)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_4 inst_5
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition 12)

-- `Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition` idx 14: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition.h14.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @LawfulMonad n inst_2]
      [inst_5 : @WeaklyLawfulMonadAttach n inst_2 inst_3] [inst_6 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_6] [inst : Std.Iterator α m β] {f : β → n (Option γ)}
      {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapM α β γ m n inst inst_2 inst_3 inst_6 f it))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_6 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_filterMapM_eq_toListRev_filterMapWithPostcondition 14)

-- `Std.Rco.mem_succ_succ_iff` idx 9: unused in the library's proof
theorem HypCheckProof.Std.Rco.mem_succ_succ_iff.h9.{u} :
    ∀ {α : Type u} [inst : LE α] [inst_1 : LT α] [inst_2 : DecidableLT α] [inst_3 : Std.PRange.UpwardEnumerable α]
      [inst_4 : Std.PRange.LinearlyUpwardEnumerable α] [inst_5 : Std.PRange.LawfulUpwardEnumerableLT α]
      [inst_6 : Std.PRange.LawfulUpwardEnumerableLE α] [inst_7 : Std.PRange.InfinitelyUpwardEnumerable α]
      [inst_8 : Std.PRange.LawfulUpwardEnumerable α] {lo hi a : α},
      a ∈ Std.PRange.UpwardEnumerable.succ lo...Std.PRange.UpwardEnumerable.succ hi ↔
        ∃ (a' : α), a = Std.PRange.UpwardEnumerable.succ a' ∧ a' ∈ lo...hi :=
  no_implicit_lambda% (drop_unused% Std.Rco.mem_succ_succ_iff 9)

-- `Std.Roo.mem_of_mem_of_le` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Roo.mem_of_mem_of_le.h5.{u} :
    ∀ {α : Type u} {r : Std.Roo α} [inst : LT α] [inst_1 : Std.PRange.UpwardEnumerable α]
      [inst_2 : Std.PRange.LawfulUpwardEnumerableLT α] [inst_3 : Std.PRange.LawfulUpwardEnumerable α] {a b : α},
      Std.PRange.UpwardEnumerable.LE r.lower b → a ∈ b<...r.upper → a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Roo.mem_of_mem_of_le 5)

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMapM` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMapM.h7.{w, w'} :
    ∀ {α β α₂ γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : MonadAttach m] [inst_2 : Std.Iterator α m β]
      [inst_3 : Std.Iterator α₂ m γ] {f : β → m (@Std.IterM α₂ m γ)} {it₁ : @Std.IterM α m β},
      @Std.IterM.IsPlausibleStep α m β inst_2 it₁ (@Std.IterStep.done (@Std.IterM α m β) β) →
        @Std.IterM.IsPlausibleStep
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            α₂ γ m)
          m γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_2
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            inst_3)
          (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_2 inst_3 f it₁ (@Option.none (@Std.IterM α₂ m γ)))
          (@Std.IterStep.done
            (@Std.IterM
              (Std.Iterators.Types.Flatten
                (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                  (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                  @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                α₂ γ m)
              m γ)
            γ) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMapM 7)

-- `Std.Roi.getElem?_toList_eq` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Roi.getElem?_toList_eq.h6.{u} :
    ∀ {α : Type u} {r : Std.Roi α} [inst : LT α] [inst : DecidableLT α] [inst : Std.PRange.UpwardEnumerable α]
      [inst_1 : Std.PRange.LawfulUpwardEnumerable α] [inst_2 : Std.Rxi.IsAlwaysFinite α] {i : Nat},
      r.toList[i]? = Std.PRange.UpwardEnumerable.succMany? (i + 1) r.lower :=
  no_implicit_lambda% (drop_unused% Std.Roi.getElem?_toList_eq 6)

-- `Std.Rii.size_eq_match_rci` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Rii.size_eq_match_rci.h5.{u} :
    ∀ {α : Type u} {r : Std.Rii α} [inst : Std.PRange.Least? α] [inst_1 : Std.PRange.UpwardEnumerable α]
      [inst_2 : Std.Rxi.HasSize α] [inst_3 : @Std.Rxi.IsAlwaysFinite α inst_1]
      [inst_4 : @Std.Rxi.LawfulHasSize α inst_1 inst_2],
      @Eq Nat (@Std.Rii.size α r inst inst_2)
        (@Std.Rxc.Iterator.toList_eq_match.match_1 α (fun (x : Option α) => Nat) (@Std.PRange.Least?.least? α inst)
          (fun (_ : Unit) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun (next : α) =>
          @Std.Rci.size α inst_2 (@Std.Rci.mk α next)) :=
  no_implicit_lambda% (drop_unused% Std.Rii.size_eq_match_rci 5)

-- `Std.Rii.size_eq_match_rci` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Rii.size_eq_match_rci.h6.{u} :
    ∀ {α : Type u} {r : Std.Rii α} [inst : Std.PRange.Least? α] [inst_1 : Std.PRange.UpwardEnumerable α]
      [inst_2 : Std.Rxi.HasSize α] [inst_3 : @Std.PRange.LawfulUpwardEnumerable α inst_1]
      [inst_4 : @Std.Rxi.LawfulHasSize α inst_1 inst_2],
      @Eq Nat (@Std.Rii.size α r inst inst_2)
        (@Std.Rxc.Iterator.toList_eq_match.match_1 α (fun (x : Option α) => Nat) (@Std.PRange.Least?.least? α inst)
          (fun (_ : Unit) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun (next : α) =>
          @Std.Rci.size α inst_2 (@Std.Rci.mk α next)) :=
  no_implicit_lambda% (drop_unused% Std.Rii.size_eq_match_rci 6)

-- `Std.Rii.size_eq_match_rci` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Rii.size_eq_match_rci.h7.{u} :
    ∀ {α : Type u} {r : Std.Rii α} [inst : Std.PRange.Least? α] [inst_1 : Std.PRange.UpwardEnumerable α]
      [inst_2 : Std.Rxi.HasSize α] [inst_3 : @Std.PRange.LawfulUpwardEnumerable α inst_1]
      [inst_4 : @Std.Rxi.IsAlwaysFinite α inst_1],
      @Eq Nat (@Std.Rii.size α r inst inst_2)
        (@Std.Rxc.Iterator.toList_eq_match.match_1 α (fun (x : Option α) => Nat) (@Std.PRange.Least?.least? α inst)
          (fun (_ : Unit) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun (next : α) =>
          @Std.Rci.size α inst_2 (@Std.Rci.mk α next)) :=
  no_implicit_lambda% (drop_unused% Std.Rii.size_eq_match_rci 7)

-- `Std.Iter.forIn_pure_yield_eq_fold` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iter.forIn_pure_yield_eq_fold.h6.{w, x} :
    ∀ {α β : Type w} {γ : Type x} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      [inst_2 : @Std.IteratorLoop α Id β inst Id] {f : β → γ → γ} {init : γ} {it : @Std.Iter α β},
      @Eq (Id γ)
        (@ForIn.forIn Id (@Std.Iter α β) β (@Std.instForInIterOfMonadOfIteratorLoopId α β Id Id.instMonad inst inst_2) γ it
          init fun (c : β) (b : γ) =>
          @Pure.pure Id (@Applicative.toPure Id (@Monad.toApplicative Id Id.instMonad)) (ForInStep γ)
            (@ForInStep.yield γ (f c b)))
        (@Pure.pure Id (@Applicative.toPure Id (@Monad.toApplicative Id Id.instMonad)) γ
          (@Std.Iter.fold α β γ inst inst_2 (fun (b : γ) (c : β) => f c b) init it)) :=
  no_implicit_lambda% (drop_unused% Std.Iter.forIn_pure_yield_eq_fold 6)

-- `Std.Roi.size_eq_match_rci` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Roi.size_eq_match_rci.h4.{u} :
    ∀ {α : Type u} {r : Std.Roi α} [inst : Std.PRange.UpwardEnumerable α] [inst_1 : Std.Rxi.HasSize α]
      [inst_2 : Std.Rxi.IsAlwaysFinite α] [inst_3 : Std.Rxi.LawfulHasSize α],
      r.size =
        match Std.PRange.UpwardEnumerable.succ? r.lower with
        | Option.none => 0
        | Option.some next => next...*.size :=
  no_implicit_lambda% (drop_unused% Std.Roi.size_eq_match_rci 4)

-- `Std.Roi.size_eq_match_rci` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Roi.size_eq_match_rci.h5.{u} :
    ∀ {α : Type u} {r : Std.Roi α} [inst : Std.PRange.UpwardEnumerable α] [inst_1 : Std.Rxi.HasSize α]
      [inst_2 : Std.PRange.LawfulUpwardEnumerable α] [inst_3 : Std.Rxi.LawfulHasSize α],
      r.size =
        match Std.PRange.UpwardEnumerable.succ? r.lower with
        | Option.none => 0
        | Option.some next => next...*.size :=
  no_implicit_lambda% (drop_unused% Std.Roi.size_eq_match_rci 5)

-- `Std.Roi.size_eq_match_rci` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Roi.size_eq_match_rci.h6.{u} :
    ∀ {α : Type u} {r : Std.Roi α} [inst : Std.PRange.UpwardEnumerable α] [inst_1 : Std.Rxi.HasSize α]
      [inst_2 : Std.PRange.LawfulUpwardEnumerable α] [inst_3 : Std.Rxi.IsAlwaysFinite α],
      r.size =
        match Std.PRange.UpwardEnumerable.succ? r.lower with
        | Option.none => 0
        | Option.some next => next...*.size :=
  no_implicit_lambda% (drop_unused% Std.Roi.size_eq_match_rci 6)

-- `Std.Rci.size_eq_size_roi` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Rci.size_eq_size_roi.h4.{u} :
    ∀ {α : Type u} {r : Std.Rci α} [inst : Std.PRange.UpwardEnumerable α] [inst_1 : Std.Rxi.HasSize α]
      [inst_2 : Std.Rxi.IsAlwaysFinite α] [inst_3 : Std.Rxi.LawfulHasSize α], r.size = r.lower<...*.size + 1 :=
  no_implicit_lambda% (drop_unused% Std.Rci.size_eq_size_roi 4)

-- `Std.Rci.size_eq_size_roi` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Rci.size_eq_size_roi.h5.{u} :
    ∀ {α : Type u} {r : Std.Rci α} [inst : Std.PRange.UpwardEnumerable α] [inst_1 : Std.Rxi.HasSize α]
      [inst_2 : Std.PRange.LawfulUpwardEnumerable α] [inst_3 : Std.Rxi.LawfulHasSize α], r.size = r.lower<...*.size + 1 :=
  no_implicit_lambda% (drop_unused% Std.Rci.size_eq_size_roi 5)

-- `Std.Rii.toArray_eq_match_rci` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Rii.toArray_eq_match_rci.h5.{u} :
    ∀ {α : Type u} {r : Std.Rii α} [inst : Std.PRange.Least? α] [inst_1 : Std.PRange.UpwardEnumerable α]
      [inst_2 : @Std.PRange.LawfulUpwardEnumerable α inst_1] [inst_3 : @Std.Rxi.IsAlwaysFinite α inst_1],
      @Eq (Array α)
        (@Std.Rii.toArray α inst_1 inst r (@Std.Rxi.instIteratorIteratorIdOfUpwardEnumerable α inst_1)
          (@Std.Rxi.Iterator.instFinite α inst_1 inst_2 inst_3))
        (@Std.Rxc.Iterator.toList_eq_match.match_1 α (fun (x : Option α) => Array α) (@Std.PRange.Least?.least? α inst)
          (fun (_ : Unit) => @List.toArray α (@List.nil α)) fun (init : α) =>
          @Std.Rci.toArray α inst_1 inst_2 inst_3 (@Std.Rci.mk α init)) :=
  no_implicit_lambda% (drop_unused% Std.Rii.toArray_eq_match_rci 5)

-- `Std.IterM.foldM_eq_forIn` idx 5: unused in the library's proof
theorem HypCheckProof.Std.IterM.foldM_eq_forIn.h5.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] {n : Type w → Type w''} [inst_1 : Monad n]
      [inst_2 : @Std.IteratorLoop α m β inst n] [inst_3 : MonadLiftT m n] {f : γ → β → n γ} {init : γ}
      {it : @Std.IterM α m β},
      @Eq (n γ) (@Std.IterM.foldM m n inst_1 α β γ inst inst_2 inst_3 f init it)
        (@ForIn.forIn n (@Std.IterM α m β) β (@Std.IterM.instForInOfIteratorLoop m n α β inst inst_2 inst_3 inst_1) γ it
          init fun (x : β) (acc : γ) =>
          @Functor.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) γ (ForInStep γ) (@ForInStep.yield γ)
            (f acc x)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.foldM_eq_forIn 5)

-- `Std.IterM.foldM_filterMapWithPostcondition` idx 17: unused in the library's proof
theorem HypCheckProof.Std.IterM.foldM_filterMapWithPostcondition.h17.{w, w', w'', w'''} :
    ∀ {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : Monad m] [inst_3 : Monad n] [inst_4 : Monad o]
      [inst_5 : @LawfulMonad m inst_2] [inst_6 : @LawfulMonad n inst_3] [inst_7 : @LawfulMonad o inst_4]
      [inst_8 : @Std.IteratorLoop α m β inst n] [inst_9 : @Std.IteratorLoop α m β inst o]
      [inst_10 : @Std.LawfulIteratorLoop β α m o inst_2 inst_4 inst inst_9] [inst_11 : MonadLiftT m n]
      [inst_12 : MonadLiftT n o] [inst_13 : @LawfulMonadLiftT m n inst_2 inst_3 inst_11]
      [inst_14 : @LawfulMonadLiftT n o inst_3 inst_4 inst_12] {f : β → Std.Iterators.PostconditionT n (Option γ)}
      {g : δ → γ → o δ} {init : δ} {it : @Std.IterM α m β},
      @Eq (o δ)
        (@Std.IterM.foldM n o inst_4
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_11 x) f) γ δ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_11 x) f
            inst inst_3)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β γ m n o inst_3 inst_4 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_11 x) f)
          inst_12 g init (@Std.IterM.filterMapWithPostcondition α β γ m n inst_11 inst f it))
        (@Std.IterM.foldM m o inst_4 α β δ inst inst_9
          (@instMonadLiftTOfMonadLift m n o (@MonadLift.mk n o fun {α : Type w} => @MonadLiftT.monadLift n o inst_12 α)
            inst_11)
          (fun (d : δ) (b : β) =>
            @Bind.bind o (@Monad.toBind o inst_4) (Option γ) δ
              (@liftM n o inst_12 (Option γ) (@Std.Iterators.PostconditionT.run n inst_3 (Option γ) (f b)))
              fun (__x : Option γ) =>
              @Std.IterM.foldM_filterMapWithPostcondition.match_1 γ (fun (__x : Option γ) => o δ) __x (fun (c : γ) => g d c)
                fun (x : Option γ) => @Pure.pure o (@Applicative.toPure o (@Monad.toApplicative o inst_4)) δ d)
          init it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.foldM_filterMapWithPostcondition 17)

-- `Std.IterM.toList_filterMapM_map` idx 11: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_filterMapM_map.h11.{w, w', w''} :
    ∀ {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @LawfulMonad n inst_2] [inst_5 : MonadLiftT m n]
      [inst_6 : @LawfulMonadLiftT m n inst inst_2 inst_5] [inst_7 : Std.Iterator α m β]
      [inst_8 : @Std.Iterators.Finite α m β inst_7] {f : β → γ} {g : γ → n (Option δ)} {it : @Std.IterM α m β},
      @Eq (n (List δ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap
            (@Std.Iterators.Types.Map α β γ m m (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                γ (f b))
            γ δ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : γ) =>
            @Std.Iterators.PostconditionT.attachLift (Option δ) n inst_3 (g b))
          n inst_2 δ
          (@Std.Iterators.Types.FilterMap.instIterator
            (@Std.Iterators.Types.Map α β γ m m (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                γ (f b))
            γ δ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : γ) => @Std.Iterators.PostconditionT.attachLift (Option δ) n inst_3 (g b))
            (@Std.Iterators.Types.Map.instIterator α β γ m m inst inst_7
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                γ (f b))
            inst_2)
          (@Std.IterM.filterMapM
            (@Std.Iterators.Types.Map α β γ m m (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                γ (f b))
            γ δ m n
            (@Std.Iterators.Types.Map.instIterator α β γ m m inst inst_7
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                γ (f b))
            inst_2 inst_3 inst_5 g (@Std.IterM.map α β γ m inst_7 inst f it)))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β δ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option δ) n inst_3 (g (f b)))
          n inst_2 δ
          (@Std.Iterators.Types.FilterMap.instIterator α β δ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option δ) n inst_3 (g (f b))) inst_7 inst_2)
          (@Std.IterM.filterMapM α β δ m n inst_7 inst_2 inst_3 inst_5 (fun (b : β) => g (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_filterMapM_map 11)

-- `Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition.h6.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : Monad n]
      [inst_2 : MonadAttach n] [inst_3 : @LawfulMonad n inst_1] [inst_4 : @WeaklyLawfulMonadAttach n inst_1 inst_2]
      [inst_5 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_1 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n (Option γ)} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b))
          n inst_1 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b)) inst inst_1)
          (@Std.IterM.filterMapM α β γ m n inst inst_1 inst_2 inst_5 f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b))
          n inst_1 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b)) inst inst_1)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition 6)

-- `Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition` idx 9: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition.h9.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @WeaklyLawfulMonadAttach n inst_2 inst_3]
      [inst_5 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_2 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n (Option γ)} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapM α β γ m n inst inst_2 inst_3 inst_5 f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition 9)

-- `Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition` idx 10: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition.h10.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @LawfulMonad n inst_2] [inst_5 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n (Option γ)} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapM α β γ m n inst inst_2 inst_3 inst_5 f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition 10)

-- `Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition` idx 12: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition.h12.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst : @LawfulMonad m inst]
      [inst : Monad n] [inst_1 : MonadAttach n] [inst_2 : @LawfulMonad n inst]
      [inst_3 : @WeaklyLawfulMonadAttach n inst inst_1] [inst_4 : MonadLiftT m n] [inst_5 : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst_5] {f : β → n (Option γ)} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b))
          n inst γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b)) inst_5 inst)
          (@Std.IterM.filterMapM α β γ m n inst_5 inst inst_1 inst_4 f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b))
          n inst γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b)) inst_5 inst)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_4 inst_5
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition 12)

-- `Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition` idx 14: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition.h14.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @LawfulMonad n inst_2]
      [inst_5 : @WeaklyLawfulMonadAttach n inst_2 inst_3] [inst_6 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_6] [inst : Std.Iterator α m β] {f : β → n (Option γ)}
      {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapM α β γ m n inst inst_2 inst_3 inst_6 f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_6 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_filterMapM_eq_toList_filterMapWithPostcondition 14)

-- `Lean.Grind.CommRing.lt_false_of_kronS` idx 6: unused in the library's proof
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h6.{u_1} :
    ∀ {α : Type u_1} [inst : Lean.Grind.CommSemiring α] [inst_1 : Lean.Grind.AddRightCancel α] [inst_2 : LE α]
      [inst_3 : LT α] [inst_4 : Std.LawfulOrderLT α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
      (a b : Lean.Grind.CommRing.Expr),
      Lean.Grind.CommRing.Expr.degSOk_k B a b = Bool.true →
        Lean.Grind.CommRing.Expr.kronOk_k K a b = Bool.true →
          Lean.Grind.CommRing.Expr.kronEval_k K B a = Lean.Grind.CommRing.Expr.kronEval_k K B b →
            (Lean.Grind.CommRing.Expr.denoteS ctx a < Lean.Grind.CommRing.Expr.denoteS ctx b) = False :=
  no_implicit_lambda% (drop_unused% Lean.Grind.CommRing.lt_false_of_kronS 6)

-- `Std.Iter.forIn_congr` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iter.forIn_congr.h6.{w, w'} :
    ∀ {γ α β : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : Std.Iterator α Id β]
      [inst_2 : @Std.IteratorLoop α Id β inst_1 m] {ita itb : @Std.Iter α β},
      @Eq (@Std.Iter α β) ita itb →
        ∀ {b b' : γ},
          @Eq γ b b' →
            ∀ {f g : β → γ → m (ForInStep γ)},
              (∀ (a : β) (b : γ), @Eq (m (ForInStep γ)) (f a b) (g a b)) →
                @Eq (m γ)
                  (@ForIn.forIn m (@Std.Iter α β) β (@Std.instForInIterOfMonadOfIteratorLoopId α β m inst inst_1 inst_2) γ
                    ita b f)
                  (@ForIn.forIn m (@Std.Iter α β) β (@Std.instForInIterOfMonadOfIteratorLoopId α β m inst inst_1 inst_2) γ
                    itb b' g) :=
  no_implicit_lambda% (drop_unused% Std.Iter.forIn_congr 6)

-- `Std.Rii.forIn'_toList_eq_forIn'` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Rii.forIn'_toList_eq_forIn'.h5.{u, w} :
    ∀ {α : Type u} {r : Std.Rii α} [inst : LT α] [inst : Std.PRange.Least? α] [inst_1 : Std.PRange.UpwardEnumerable α]
      [inst_2 : Std.PRange.LawfulUpwardEnumerableLeast? α] [inst_3 : Std.Rxi.IsAlwaysFinite α]
      [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w} [inst_5 : Monad m]
      [inst_6 : LawfulMonad m] {f : (a : α) → a ∈ r.toList → γ → m (ForInStep γ)},
      ForIn'.forIn' r.toList init f = ForIn'.forIn' r init fun (a : α) (x : a ∈ r) (acc : γ) => f a Std.Rii.mem_toList acc :=
  no_implicit_lambda% (drop_unused% Std.Rii.forIn'_toList_eq_forIn' 5)

-- `Lean.Grind.CommRing.lt_false_of_kronLinS` idx 6: unused in the library's proof
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h6.{u_1} :
    ∀ {α : Type u_1} [inst : Lean.Grind.CommSemiring α] [inst_1 : Lean.Grind.AddRightCancel α] [inst_2 : LE α]
      [inst_3 : LT α] [inst_4 : Std.LawfulOrderLT α] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
      (a b : Lean.Grind.CommRing.Expr),
      a.linSOk_k b = Bool.true →
        Lean.Grind.CommRing.Expr.kronOk_k K a b = Bool.true →
          Lean.Grind.CommRing.Expr.kronLinEval_k K a = Lean.Grind.CommRing.Expr.kronLinEval_k K b →
            (Lean.Grind.CommRing.Expr.denoteS ctx a < Lean.Grind.CommRing.Expr.denoteS ctx b) = False :=
  no_implicit_lambda% (drop_unused% Lean.Grind.CommRing.lt_false_of_kronLinS 6)

-- `Lean.Grind.CommRing.lt_false_of_kronSN` idx 5: unused in the library's proof
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Lean.Grind.CommSemiring α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
      (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
      Lean.Grind.CommRing.Expr.degSOk_k B a b = Bool.true →
        Lean.Grind.CommRing.Expr.kronOk_k K a b = Bool.true →
          Lean.Grind.CommRing.Expr.kronEval_k K B a = Lean.Grind.CommRing.Expr.kronEval_k K B b →
            (Lean.Grind.CommRing.Expr.denoteS ctx a < Lean.Grind.CommRing.Expr.denoteS ctx b) = False :=
  no_implicit_lambda% (drop_unused% Lean.Grind.CommRing.lt_false_of_kronSN 5)

-- `Lean.Grind.CommRing.lt_false_of_kron` idx 5: unused in the library's proof
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
      (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
      Lean.Grind.CommRing.Expr.degOk_k B a b = Bool.true →
        Lean.Grind.CommRing.Expr.kronOk_k K a b = Bool.true →
          Lean.Grind.CommRing.Expr.kronEval_k K B a = Lean.Grind.CommRing.Expr.kronEval_k K B b →
            (Lean.Grind.CommRing.Expr.denote ctx a < Lean.Grind.CommRing.Expr.denote ctx b) = False :=
  no_implicit_lambda% (drop_unused% Lean.Grind.CommRing.lt_false_of_kron 5)

-- `Std.Iter.all_mapM` idx 11: unused in the library's proof
theorem HypCheckProof.Std.Iter.all_mapM.h11.{w, w'} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      [inst_2 : @Std.IteratorLoop α Id β inst m] [inst_3 : Monad m] [inst_4 : MonadAttach m]
      [inst_5 : @LawfulMonad m inst_3] [inst_6 : @WeaklyLawfulMonadAttach m inst_3 inst_4] {it : @Std.Iter α β}
      {f : β → m β'} {p : β' → Bool},
      @Eq (m (ULift Bool))
        (@Std.IterM.all
          (@Std.Iterators.Types.Map α β β' Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' m inst_4 (f b))
          β' m inst_3
          (@Std.Iterators.Types.Map.instIterator α β β' Id m inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) => @Std.Iterators.PostconditionT.attachLift β' m inst_4 (f b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β' Id m m inst_3 inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) => @Std.Iterators.PostconditionT.attachLift β' m inst_4 (f b))
          p (@Std.Iter.mapM α β β' inst m inst_3 inst_4 f it))
        (@Std.IterM.allM
          (@Std.Iterators.Types.Map α β β Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          β m inst_3
          (@Std.Iterators.Types.Map.instIterator α β β Id m inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β Id m m inst_3 inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          (fun (x : β) =>
            @Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) β' (ULift Bool)
              (fun (x : β') => @ULift.up Bool (p x)) (f x))
          (@Std.Iter.mapM α β β inst m inst_3 inst_4
            (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.Iter.all_mapM 11)

-- `Std.Iter.any_mapM` idx 11: unused in the library's proof
theorem HypCheckProof.Std.Iter.any_mapM.h11.{w, w'} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      [inst_2 : @Std.IteratorLoop α Id β inst m] [inst_3 : Monad m] [inst_4 : MonadAttach m]
      [inst_5 : @LawfulMonad m inst_3] [inst_6 : @WeaklyLawfulMonadAttach m inst_3 inst_4] {it : @Std.Iter α β}
      {f : β → m β'} {p : β' → Bool},
      @Eq (m (ULift Bool))
        (@Std.IterM.any
          (@Std.Iterators.Types.Map α β β' Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' m inst_4 (f b))
          β' m inst_3
          (@Std.Iterators.Types.Map.instIterator α β β' Id m inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) => @Std.Iterators.PostconditionT.attachLift β' m inst_4 (f b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β' Id m m inst_3 inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) => @Std.Iterators.PostconditionT.attachLift β' m inst_4 (f b))
          p (@Std.Iter.mapM α β β' inst m inst_3 inst_4 f it))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.Map α β β Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          β m inst_3
          (@Std.Iterators.Types.Map.instIterator α β β Id m inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β Id m m inst_3 inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          (fun (x : β) =>
            @Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) β' (ULift Bool)
              (fun (x : β') => @ULift.up Bool (p x)) (f x))
          (@Std.Iter.mapM α β β inst m inst_3 inst_4
            (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.Iter.any_mapM 11)

-- `Std.Rcc.mem_of_mem_roc` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Rcc.mem_of_mem_roc.h7.{u} :
    ∀ {α : Type u} {r : Std.Rcc α} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLE α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLT α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] {a b : α}, r.lower ≤ b → a ∈ b<...=r.upper → a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Rcc.mem_of_mem_roc 7)

-- `Lean.Grind.CommRing.lt_false_of_kronLin` idx 5: unused in the library's proof
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLin.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
      (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b : Lean.Grind.CommRing.Expr),
      a.linOk_k b = Bool.true →
        Lean.Grind.CommRing.Expr.kronOk_k K a b = Bool.true →
          Lean.Grind.CommRing.Expr.kronLinEval_k K a = Lean.Grind.CommRing.Expr.kronLinEval_k K b →
            (Lean.Grind.CommRing.Expr.denote ctx a < Lean.Grind.CommRing.Expr.denote ctx b) = False :=
  no_implicit_lambda% (drop_unused% Lean.Grind.CommRing.lt_false_of_kronLin 5)

-- `Std.Iter.forIn_yield_eq_foldM` idx 10: unused in the library's proof
theorem HypCheckProof.Std.Iter.forIn_yield_eq_foldM.h10.{w, x, x'} :
    ∀ {α β : Type w} {γ δ : Type x} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      {m : Type x → Type x'} [inst_2 : Monad m] [inst_3 : @LawfulMonad m inst_2] [inst_4 : @Std.IteratorLoop α Id β inst m]
      {f : β → γ → m δ} {g : β → γ → δ → γ} {init : γ} {it : @Std.Iter α β},
      @Eq (m γ)
        (@ForIn.forIn m (@Std.Iter α β) β (@Std.instForInIterOfMonadOfIteratorLoopId α β m inst_2 inst inst_4) γ it init
          fun (c : β) (b : γ) =>
          @Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst_2)) δ (ForInStep γ)
            (fun (d : δ) => @ForInStep.yield γ (g c b d)) (f c b))
        (@Std.Iter.foldM m inst_2 α β γ inst inst_4
          (fun (b : γ) (c : β) =>
            @Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst_2)) δ γ (g c b) (f c b))
          init it) :=
  no_implicit_lambda% (drop_unused% Std.Iter.forIn_yield_eq_foldM 10)

-- `Std.Rii.mem_iff_mem_rci` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Rii.mem_iff_mem_rci.h5.{u} :
    ∀ {α : Type u} {r : Std.Rii α} [inst : LE α] [inst_1 : Std.PRange.Least? α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : @Std.PRange.LawfulUpwardEnumerableLE α inst_2 inst]
      [inst_4 : @Std.PRange.LawfulUpwardEnumerableLeast? α inst_2 inst_1] [inst_5 : @Std.Rxi.IsAlwaysFinite α inst_2]
      {a : α},
      Iff (@Membership.mem α (Std.Rii α) (@Std.Rii.instMembership α) r a)
        (@Membership.mem α (Std.Rci α) (@Std.Rci.instMembershipOfLE α inst)
          (@Std.Rci.mk α (@Std.PRange.UpwardEnumerable.least α inst_2 inst_1 inst_4 (@Nonempty.intro α a))) a) :=
  no_implicit_lambda% (drop_unused% Std.Rii.mem_iff_mem_rci 5)

-- `Std.Rii.mem_iff_mem_rci` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Rii.mem_iff_mem_rci.h8.{u} :
    ∀ {α : Type u} {r : Std.Rii α} [inst : LE α] [inst_1 : Std.PRange.Least? α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : @Std.PRange.LawfulUpwardEnumerable α inst_2] [inst_4 : @Std.PRange.LawfulUpwardEnumerableLE α inst_2 inst]
      [inst_5 : @Std.PRange.LawfulUpwardEnumerableLeast? α inst_2 inst_1] {a : α},
      Iff (@Membership.mem α (Std.Rii α) (@Std.Rii.instMembership α) r a)
        (@Membership.mem α (Std.Rci α) (@Std.Rci.instMembershipOfLE α inst)
          (@Std.Rci.mk α (@Std.PRange.UpwardEnumerable.least α inst_2 inst_1 inst_5 (@Nonempty.intro α a))) a) :=
  no_implicit_lambda% (drop_unused% Std.Rii.mem_iff_mem_rci 8)

-- `Std.Roi.isEmpty_iff_forall_not_mem` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Roi.isEmpty_iff_forall_not_mem.h6.{u} :
    ∀ {α : Type u} {r : Std.Roi α} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxi.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLT α] [inst_5 : Std.Rxi.IsAlwaysFinite α]
      [inst_6 : Std.PRange.LawfulUpwardEnumerable α], r.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Roi.isEmpty_iff_forall_not_mem 6)

-- `Std.Roi.isEmpty_iff_forall_not_mem` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Roi.isEmpty_iff_forall_not_mem.h8.{u} :
    ∀ {α : Type u} {r : Std.Roi α} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxi.HasSize α] [inst_4 : Std.Rxi.LawfulHasSize α] [inst_5 : Std.PRange.LawfulUpwardEnumerableLT α]
      [inst_6 : Std.PRange.LawfulUpwardEnumerable α], r.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Roi.isEmpty_iff_forall_not_mem 8)

-- `Std.Rci.isEmpty_iff_forall_not_mem` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Rci.isEmpty_iff_forall_not_mem.h5.{u} :
    ∀ {α : Type u} {r : Std.Rci α} [inst : LE α] [inst_1 : Std.PRange.UpwardEnumerable α] [inst_2 : Std.Rxi.HasSize α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLE α] [inst_4 : Std.Rxi.IsAlwaysFinite α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α], r.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Rci.isEmpty_iff_forall_not_mem 5)

-- `Std.Rci.isEmpty_iff_forall_not_mem` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Rci.isEmpty_iff_forall_not_mem.h7.{u} :
    ∀ {α : Type u} {r : Std.Rci α} [inst : LE α] [inst_1 : Std.PRange.UpwardEnumerable α] [inst_2 : Std.Rxi.HasSize α]
      [inst_3 : Std.Rxi.LawfulHasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLE α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α], r.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Rci.isEmpty_iff_forall_not_mem 7)

-- `Std.Rii.isEmpty_iff_forall_not_mem` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Rii.isEmpty_iff_forall_not_mem.h6.{u} :
    ∀ {α : Type u} {r : Std.Rii α} [inst : LT α] [inst : DecidableLT α] [inst : Std.PRange.Least? α]
      [inst_1 : Std.PRange.UpwardEnumerable α] [inst_2 : Std.PRange.LawfulUpwardEnumerableLeast? α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerable α], r.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Rii.isEmpty_iff_forall_not_mem 6)

-- `Std.Rii.isEmpty_iff_forall_not_mem` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Rii.isEmpty_iff_forall_not_mem.h8.{u} :
    ∀ {α : Type u} {r : Std.Rii α} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.Least? α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst : Std.PRange.LawfulUpwardEnumerableLT α]
      [inst : Std.PRange.LawfulUpwardEnumerableLeast? α], r.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Rii.isEmpty_iff_forall_not_mem 8)

-- `Std.Rxc.Iterator.toList_eq_match` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Rxc.Iterator.toList_eq_match.h6.{u} :
    ∀ {α : Type u} [inst : LE α] [inst_1 : @DecidableLE α inst] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : @Std.Rxc.IsAlwaysFinite α inst_2 inst] [inst_4 : @Std.PRange.LawfulUpwardEnumerable α inst_2]
      {it : @Std.Iter (Std.Rxc.Iterator α) α},
      @Eq (List α)
        (@Std.Iter.toList (Std.Rxc.Iterator α) α
          (@Std.Rxc.instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE α inst_2 inst inst_1) it)
        (@Std.Rxc.Iterator.toList_eq_match.match_1 α (fun (x : Option α) => List α)
          (@Std.Rxc.Iterator.next α (@Std.Iter.internalState (Std.Rxc.Iterator α) α it)) (fun (_ : Unit) => @List.nil α)
          fun (a : α) =>
          @ite (List α)
            (@LE.le α inst a (@Std.Rxc.Iterator.upperBound α (@Std.Iter.internalState (Std.Rxc.Iterator α) α it)))
            (inst_1 a (@Std.Rxc.Iterator.upperBound α (@Std.Iter.internalState (Std.Rxc.Iterator α) α it)))
            (@List.cons α a
              (@Std.Iter.toList (Std.Rxc.Iterator α) α
                (@Std.Rxc.instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE α inst_2 inst inst_1)
                (@Std.Iter.mk (Std.Rxc.Iterator α) α
                  (@Std.Rxc.Iterator.mk α (@Std.PRange.UpwardEnumerable.succ? α inst_2 a)
                    (@Std.Rxc.Iterator.upperBound α (@Std.Iter.internalState (Std.Rxc.Iterator α) α it))))))
            (@List.nil α)) :=
  no_implicit_lambda% (drop_unused% Std.Rxc.Iterator.toList_eq_match 6)

-- `Std.IterM.length_eq_forIn` idx 4: unused in the library's proof
theorem HypCheckProof.Std.IterM.length_eq_forIn.h4.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : Monad m] [inst_2 : @LawfulMonad m inst_1]
      [inst_3 : @Std.IteratorLoop α m β inst m] {it : @Std.IterM α m β},
      @Eq (m (ULift Nat)) (@Std.IterM.length α m β inst inst_3 inst_1 it)
        (@ForIn.forIn m (@Std.IterM α m β) β
          (@Std.IterM.instForInOfIteratorLoop m m α β inst inst_3 (instMonadLiftT m) inst_1) (ULift Nat) it
          (@ULift.up Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) fun (x : β) (acc : ULift Nat) =>
          @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_1)) (ForInStep (ULift Nat))
            (@ForInStep.yield (ULift Nat)
              (@ULift.up Nat
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@ULift.down Nat acc)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.length_eq_forIn 4)

-- `Std.IterM.length_eq_forIn` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.length_eq_forIn.h6.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      [inst_2 : Monad m] [inst_3 : @Std.IteratorLoop α m β inst m] {it : @Std.IterM α m β},
      @Eq (m (ULift Nat)) (@Std.IterM.length α m β inst inst_3 inst_2 it)
        (@ForIn.forIn m (@Std.IterM α m β) β
          (@Std.IterM.instForInOfIteratorLoop m m α β inst inst_3 (instMonadLiftT m) inst_2) (ULift Nat) it
          (@ULift.up Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) fun (x : β) (acc : ULift Nat) =>
          @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep (ULift Nat))
            (@ForInStep.yield (ULift Nat)
              (@ULift.up Nat
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@ULift.down Nat acc)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.length_eq_forIn 6)

-- `Std.IterM.length_eq_fold` idx 4: unused in the library's proof
theorem HypCheckProof.Std.IterM.length_eq_fold.h4.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : Monad m] [inst_2 : @LawfulMonad m inst_1]
      [inst_3 : @Std.IteratorLoop α m β inst m] {it : @Std.IterM α m β},
      @Eq (m (ULift Nat)) (@Std.IterM.length α m β inst inst_3 inst_1 it)
        (@Std.IterM.fold m α β (ULift Nat) inst_1 inst inst_3
          (fun (acc : ULift Nat) (x : β) =>
            @ULift.up Nat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@ULift.down Nat acc)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@ULift.up Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.length_eq_fold 4)

-- `Std.IterM.length_eq_fold` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.length_eq_fold.h6.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      [inst_2 : Monad m] [inst_3 : @Std.IteratorLoop α m β inst m] {it : @Std.IterM α m β},
      @Eq (m (ULift Nat)) (@Std.IterM.length α m β inst inst_3 inst_2 it)
        (@Std.IterM.fold m α β (ULift Nat) inst_2 inst inst_3
          (fun (acc : ULift Nat) (x : β) =>
            @ULift.up Nat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@ULift.down Nat acc)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@ULift.up Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.length_eq_fold 6)

-- `Std.Rii.pairwise_toList_upwardEnumerableLt` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Rii.pairwise_toList_upwardEnumerableLt.h5.{u} :
    ∀ {α : Type u} {r : Std.Rii α} [inst : Std.PRange.Least? α] [inst_1 : Std.PRange.UpwardEnumerable α]
      [inst_2 : Std.PRange.LawfulUpwardEnumerable α] [inst_3 : Std.Rxi.IsAlwaysFinite α],
      List.Pairwise (fun (a b : α) => Std.PRange.UpwardEnumerable.LT a b) r.toList :=
  no_implicit_lambda% (drop_unused% Std.Rii.pairwise_toList_upwardEnumerableLt 5)

-- `Array.le_iff_lt_or_eq` idx 2: unused in the library's proof
theorem HypCheckProof.Array.le_iff_lt_or_eq.h2.{u_1} :
    ∀ {α : Type u_1} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2]
      [inst_2 : Std.Asymm fun (x1 x2 : α) => x1 < x2] {xs ys : Array α}, xs ≤ ys ↔ xs < ys ∨ xs = ys :=
  no_implicit_lambda% (drop_unused% Array.le_iff_lt_or_eq 2)

-- `Std.IterM.any_filterMapM` idx 15: unused in the library's proof
theorem HypCheckProof.Std.IterM.any_filterMapM.h15.{w, w', w''} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : @Std.IteratorLoop α m β inst m]
      [inst_4 : Monad m] [inst_5 : @LawfulMonad m inst_4] [inst_6 : Monad n] [inst_7 : MonadAttach n]
      [inst_8 : @LawfulMonad n inst_6] [inst_9 : @WeaklyLawfulMonadAttach n inst_6 inst_7]
      [inst_10 : @Std.LawfulIteratorLoop β α m m inst_4 inst_4 inst inst_3] {it : @Std.IterM α m β} {f : β → n (Option β')}
      {p : β' → Bool},
      @Eq (n (ULift Bool))
        (@Std.IterM.any
          (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_7 (f b))
          β' n inst_6
          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_7 (f b)) inst inst_6)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β' m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_7 (f b))
          p (@Std.IterM.filterMapM α β β' m n inst inst_6 inst_7 inst_2 f it))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          β n inst_6
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (fun (x : β) =>
            @Bind.bind n (@Monad.toBind n inst_6) (Option β') (ULift Bool) (f x) fun (__do_lift : Option β') =>
              @Std.IterM.forIn_filterMapWithPostcondition.match_1 β' (fun (__do_lift : Option β') => n (ULift Bool))
                __do_lift
                (fun (fx : β') =>
                  @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) (ULift Bool) (@ULift.up Bool (p fx)))
                fun (_ : Unit) =>
                @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) (ULift Bool)
                  (@ULift.up Bool Bool.false))
          (@Std.IterM.mapM α β β m n inst inst_6 inst_7 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.any_filterMapM 15)

-- `Std.IterM.any_filterMapM` idx 16: unused in the library's proof
theorem HypCheckProof.Std.IterM.any_filterMapM.h16.{w, w', w''} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : @Std.IteratorLoop α m β inst m]
      [inst_4 : Monad m] [inst_5 : @LawfulMonad m inst_4] [inst_6 : Monad n] [inst_7 : MonadAttach n]
      [inst_8 : @LawfulMonad n inst_6] [inst_9 : @WeaklyLawfulMonadAttach n inst_6 inst_7]
      [inst_10 : @LawfulMonadLiftT m n inst_4 inst_6 inst_2] {it : @Std.IterM α m β} {f : β → n (Option β')}
      {p : β' → Bool},
      @Eq (n (ULift Bool))
        (@Std.IterM.any
          (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_7 (f b))
          β' n inst_6
          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_7 (f b)) inst inst_6)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β' m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_7 (f b))
          p (@Std.IterM.filterMapM α β β' m n inst inst_6 inst_7 inst_2 f it))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          β n inst_6
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (fun (x : β) =>
            @Bind.bind n (@Monad.toBind n inst_6) (Option β') (ULift Bool) (f x) fun (__do_lift : Option β') =>
              @Std.IterM.forIn_filterMapWithPostcondition.match_1 β' (fun (__do_lift : Option β') => n (ULift Bool))
                __do_lift
                (fun (fx : β') =>
                  @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) (ULift Bool) (@ULift.up Bool (p fx)))
                fun (_ : Unit) =>
                @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) (ULift Bool)
                  (@ULift.up Bool Bool.false))
          (@Std.IterM.mapM α β β m n inst inst_6 inst_7 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.any_filterMapM 16)

-- `Std.IterM.allM_mapM` idx 14: unused in the library's proof
theorem HypCheckProof.Std.IterM.allM_mapM.h14.{w, w', w''} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : Monad m]
      [inst_4 : @LawfulMonad m inst_3] [inst_5 : Monad n] [inst_6 : MonadAttach n] [inst_7 : @LawfulMonad n inst_5]
      [inst_8 : @WeaklyLawfulMonadAttach n inst_5 inst_6] {it : @Std.IterM α m β} {f : β → n β'} {p : β' → n (ULift Bool)},
      @Eq (n (ULift Bool))
        (@Std.IterM.allM
          (@Std.Iterators.Types.Map α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_5)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_6 (f b))
          β' n inst_5
          (@Std.Iterators.Types.Map.instIterator α β β' m n inst_5 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_6 (f b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β' m n n inst_5 inst_5 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_6 (f b))
          p (@Std.IterM.mapM α β β' m n inst inst_5 inst_6 inst_2 f it))
        (@Std.IterM.allM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_5)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_6
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_5)) β b))
          β n inst_5
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_5 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_6
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_5)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_5 inst_5 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_6
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_5)) β b))
          (fun (x : β) => @Bind.bind n (@Monad.toBind n inst_5) β' (ULift Bool) (f x) fun (__do_lift : β') => p __do_lift)
          (@Std.IterM.mapM α β β m n inst inst_5 inst_6 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_5)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.allM_mapM 14)

-- `Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition.h6.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : Monad n]
      [inst_2 : MonadAttach n] [inst_3 : @LawfulMonad n inst_1] [inst_4 : @WeaklyLawfulMonadAttach n inst_1 inst_2]
      [inst_5 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_1 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b))
          n inst_1 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_1 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b))
          (@Std.IterM.mapM α β γ m n inst inst_1 inst_2 inst_5 f it))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b))
          n inst_1 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_1 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst_1 inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition 6)

-- `Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition` idx 9: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition.h9.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @WeaklyLawfulMonadAttach n inst_2 inst_3]
      [inst_5 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_2 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapM α β γ m n inst inst_2 inst_3 inst_5 f it))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition 9)

-- `Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition` idx 10: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition.h10.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @LawfulMonad n inst_2] [inst_5 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapM α β γ m n inst inst_2 inst_3 inst_5 f it))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition 10)

-- `Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition` idx 12: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition.h12.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst : @LawfulMonad m inst]
      [inst : Monad n] [inst_1 : MonadAttach n] [inst_2 : @LawfulMonad n inst]
      [inst_3 : @WeaklyLawfulMonadAttach n inst inst_1] [inst_4 : MonadLiftT m n] [inst_5 : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst_5] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b))
          n inst γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst inst_5
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b))
          (@Std.IterM.mapM α β γ m n inst_5 inst inst_1 inst_4 f it))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b))
          n inst γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst inst_5
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst inst_4 inst_5
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition 12)

-- `Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition` idx 14: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition.h14.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @LawfulMonad n inst_2]
      [inst_5 : @WeaklyLawfulMonadAttach n inst_2 inst_3] [inst_6 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_6] [inst : Std.Iterator α m β] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapM α β γ m n inst inst_2 inst_3 inst_6 f it))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_6 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_mapM_eq_toListRev_mapWithPostcondition 14)

-- `Std.Rci.mem_of_mem_roi` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Rci.mem_of_mem_roi.h7.{u} :
    ∀ {α : Type u} {r : Std.Rci α} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLE α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLT α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] {a b : α}, r.lower ≤ b → a ∈ b<...* → a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Rci.mem_of_mem_roi 7)

-- `Std.IterM.forIn_yield_eq_foldM` idx 12: unused in the library's proof
theorem HypCheckProof.Std.IterM.forIn_yield_eq_foldM.h12.{w, w', w''} :
    ∀ {α β γ δ : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      {n : Type w → Type w''} [inst_2 : Monad m] [inst_3 : Monad n] [inst_4 : @LawfulMonad n inst_3]
      [inst_5 : @Std.IteratorLoop α m β inst n] [inst_6 : MonadLiftT m n] {f : β → γ → n δ} {g : β → γ → δ → γ} {init : γ}
      {it : @Std.IterM α m β},
      @Eq (n γ)
        (@ForIn.forIn n (@Std.IterM α m β) β (@Std.IterM.instForInOfIteratorLoop m n α β inst inst_5 inst_6 inst_3) γ it
          init fun (c : β) (b : γ) =>
          @Functor.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_3)) δ (ForInStep γ)
            (fun (d : δ) => @ForInStep.yield γ (g c b d)) (f c b))
        (@Std.IterM.foldM m n inst_3 α β γ inst inst_5 inst_6
          (fun (b : γ) (c : β) =>
            @Functor.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_3)) δ γ (g c b) (f c b))
          init it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.forIn_yield_eq_foldM 12)

-- `Std.Rco.mem_of_mem_roo` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Rco.mem_of_mem_roo.h7.{u} :
    ∀ {α : Type u} {r : Std.Rco α} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLE α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLT α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] {a b : α}, r.lower ≤ b → a ∈ b<...r.upper → a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Rco.mem_of_mem_roo 7)

-- `Std.Iter.any_filterM` idx 10: unused in the library's proof
theorem HypCheckProof.Std.Iter.any_filterM.h10.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      [inst_2 : @Std.IteratorLoop α Id β inst m] [inst_3 : Monad m] [inst_4 : MonadAttach m]
      [inst_5 : @LawfulMonad m inst_3] [inst_6 : @WeaklyLawfulMonadAttach m inst_3 inst_4] {it : @Std.Iter α β}
      {f : β → m (ULift Bool)} {p : β → Bool},
      @Eq (m (ULift Bool))
        (@Std.IterM.any
          (@Std.Iterators.Types.FilterMap α β β Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_4 (f b)))
          β m inst_3
          (@Std.Iterators.Types.FilterMap.instIterator α β β Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            (fun (b : β) =>
              @Std.Iterators.PostconditionT.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) (ULift Bool)
                (Option β)
                (fun (x : ULift Bool) =>
                  @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                    (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_4 (f b)))
            inst inst_3)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β Id m m inst_3 inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_4 (f b)))
          p (@Std.Iter.filterM α β inst m inst_3 inst_4 f it))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.Map α β β Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          β m inst_3
          (@Std.Iterators.Types.Map.instIterator α β β Id m inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β Id m m inst_3 inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          (fun (x : β) =>
            @Bind.bind m (@Monad.toBind m inst_3) (ULift Bool) (ULift Bool) (f x) fun (__do_lift : ULift Bool) =>
              @ite (m (ULift Bool)) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
                (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true)
                (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) (ULift Bool) (@ULift.up Bool (p x)))
                (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) (ULift Bool)
                  (@ULift.up Bool Bool.false)))
          (@Std.Iter.mapM α β β inst m inst_3 inst_4
            (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.Iter.any_filterM 10)

-- `Std.Iter.all_filterM` idx 10: unused in the library's proof
theorem HypCheckProof.Std.Iter.all_filterM.h10.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      [inst_2 : @Std.IteratorLoop α Id β inst m] [inst_3 : Monad m] [inst_4 : MonadAttach m]
      [inst_5 : @LawfulMonad m inst_3] [inst_6 : @WeaklyLawfulMonadAttach m inst_3 inst_4] {it : @Std.Iter α β}
      {f : β → m (ULift Bool)} {p : β → Bool},
      @Eq (m (ULift Bool))
        (@Std.IterM.all
          (@Std.Iterators.Types.FilterMap α β β Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_4 (f b)))
          β m inst_3
          (@Std.Iterators.Types.FilterMap.instIterator α β β Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            (fun (b : β) =>
              @Std.Iterators.PostconditionT.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) (ULift Bool)
                (Option β)
                (fun (x : ULift Bool) =>
                  @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                    (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_4 (f b)))
            inst inst_3)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β Id m m inst_3 inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) m inst_4 (f b)))
          p (@Std.Iter.filterM α β inst m inst_3 inst_4 f it))
        (@Std.IterM.allM
          (@Std.Iterators.Types.Map α β β Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          β m inst_3
          (@Std.Iterators.Types.Map.instIterator α β β Id m inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β Id m m inst_3 inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          (fun (x : β) =>
            @Bind.bind m (@Monad.toBind m inst_3) (ULift Bool) (ULift Bool) (f x) fun (__do_lift : ULift Bool) =>
              @ite (m (ULift Bool)) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
                (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true)
                (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) (ULift Bool) (@ULift.up Bool (p x)))
                (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) (ULift Bool)
                  (@ULift.up Bool Bool.true)))
          (@Std.Iter.mapM α β β inst m inst_3 inst_4
            (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.Iter.all_filterM 10)

-- `Lean.Grind.CommRing.lt_false_of_toPolyS` idx 5: unused in the library's proof
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPolyS.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Lean.Grind.CommSemiring α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
      (ctx : Lean.Grind.CommRing.Context α) (bal₁ bal₂ : Bool) (lhs rhs : Lean.Grind.CommRing.Expr)
      (p : Lean.Grind.CommRing.Poly),
      p = Lean.Grind.CommRing.Expr.toPolySX_k bal₁ lhs →
        p = Lean.Grind.CommRing.Expr.toPolySX_k bal₂ rhs →
          (Lean.Grind.CommRing.Expr.denoteS ctx lhs < Lean.Grind.CommRing.Expr.denoteS ctx rhs) = False :=
  no_implicit_lambda% (drop_unused% Lean.Grind.CommRing.lt_false_of_toPolyS 5)

-- `Std.Iter.toList_flatMap` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iter.toList_flatMap.h6.{w} :
    ∀ {α α₂ β γ : Type w} [inst : Std.Iterator α Id β] [inst : Std.Iterator α₂ Id γ]
      [inst : @Std.Iterators.Finite α₂ Id γ inst] [inst : Std.Iterator α Id β] [inst_1 : Std.Iterator α₂ Id γ]
      [inst_2 : @Std.Iterators.Finite α Id β inst] [inst_3 : @Std.Iterators.Finite α₂ Id γ inst_1] {f : β → @Std.Iter α₂ γ}
      {it₁ : @Std.Iter α β},
      @Eq (List γ)
        (@Std.Iter.toList
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ Id γ) Id Id
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x)
              (@Applicative.toFunctor Id (@Monad.toApplicative Id Id.instMonad)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (@Std.IterM α₂ Id γ) (@Std.Iter.toIterM α₂ γ (f b)))
            α₂ γ Id)
          γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ Id γ) Id Id
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x)
              (@Applicative.toFunctor Id (@Monad.toApplicative Id Id.instMonad)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (@Std.IterM α₂ Id γ) (@Std.Iter.toIterM α₂ γ (f b)))
            α₂ γ Id Id.instMonad
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ Id γ) Id Id Id.instMonad inst
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (@Std.IterM α₂ Id γ) (@Std.Iter.toIterM α₂ γ (f b)))
            inst_1)
          (@Std.Iter.flatMap α β α₂ γ inst inst_1 f it₁))
        (@List.flatten γ
          (@Std.Iter.toList
            (@Std.Iterators.Types.Map α β (List γ) Id Id
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x)
              (@Applicative.toFunctor Id (@Monad.toApplicative Id Id.instMonad)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (List γ) (@Std.Iter.toList α₂ γ inst_1 (f b)))
            (List γ)
            (@Std.Iterators.Types.Map.instIterator α β (List γ) Id Id Id.instMonad inst
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (List γ) (@Std.Iter.toList α₂ γ inst_1 (f b)))
            (@Std.Iter.map α β (List γ) inst (fun (b : β) => @Std.Iter.toList α₂ γ inst_1 (f b)) it₁))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.toList_flatMap 6)

-- `Std.Iter.toList_flatMap` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Iter.toList_flatMap.h7.{w} :
    ∀ {α α₂ β γ : Type w} [inst : Std.Iterator α Id β] [inst_1 : Std.Iterator α₂ Id γ]
      [inst : @Std.Iterators.Finite α Id β inst] [inst : Std.Iterator α Id β] [inst_2 : Std.Iterator α₂ Id γ]
      [inst_3 : @Std.Iterators.Finite α Id β inst] [inst_4 : @Std.Iterators.Finite α₂ Id γ inst_2] {f : β → @Std.Iter α₂ γ}
      {it₁ : @Std.Iter α β},
      @Eq (List γ)
        (@Std.Iter.toList
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ Id γ) Id Id
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x)
              (@Applicative.toFunctor Id (@Monad.toApplicative Id Id.instMonad)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (@Std.IterM α₂ Id γ) (@Std.Iter.toIterM α₂ γ (f b)))
            α₂ γ Id)
          γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ Id γ) Id Id
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x)
              (@Applicative.toFunctor Id (@Monad.toApplicative Id Id.instMonad)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (@Std.IterM α₂ Id γ) (@Std.Iter.toIterM α₂ γ (f b)))
            α₂ γ Id Id.instMonad
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ Id γ) Id Id Id.instMonad inst
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (@Std.IterM α₂ Id γ) (@Std.Iter.toIterM α₂ γ (f b)))
            inst_2)
          (@Std.Iter.flatMap α β α₂ γ inst inst_2 f it₁))
        (@List.flatten γ
          (@Std.Iter.toList
            (@Std.Iterators.Types.Map α β (List γ) Id Id
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x)
              (@Applicative.toFunctor Id (@Monad.toApplicative Id Id.instMonad)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (List γ) (@Std.Iter.toList α₂ γ inst_2 (f b)))
            (List γ)
            (@Std.Iterators.Types.Map.instIterator α β (List γ) Id Id Id.instMonad inst
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (List γ) (@Std.Iter.toList α₂ γ inst_2 (f b)))
            (@Std.Iter.map α β (List γ) inst (fun (b : β) => @Std.Iter.toList α₂ γ inst_2 (f b)) it₁))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.toList_flatMap 7)

-- `Std.IterM.DefaultConsumers.forIn'_eq_wf` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.DefaultConsumers.forIn'_eq_wf.h6.{w, w', x, x'} :
    ∀ {m : Type w → Type w'} {α β : Type w} [inst : Std.Iterator α m β] {n : Type x → Type x'} [inst_1 : Monad n]
      {lift : (γ : Type w) → (δ : Type x) → (γ → n δ) → m γ → n δ} {γ : Type x} (Pl : β → γ → ForInStep γ → Prop)
      (wf : Std.IteratorLoop.WellFounded α m Pl) {it : Std.IterM m β} {init : γ} {P : β → Prop}
      {hP : ∀ (b : β), it.IsPlausibleIndirectOutput b → P b} (f : (b : β) → P b → (c : γ) → n (Subtype (Pl b c))),
      Std.IterM.DefaultConsumers.forIn' lift γ Pl it init P hP f =
        Std.IterM.DefaultConsumers.forIn'.wf lift γ Pl wf it init P hP f :=
  no_implicit_lambda% (drop_unused% Std.IterM.DefaultConsumers.forIn'_eq_wf 6)

-- `Std.IterM.DefaultConsumers.forIn'_eq_match_step` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.DefaultConsumers.forIn'_eq_match_step.h6.{w, w', x, x'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] {n : Type x → Type x'} [inst_1 : Monad n]
      {lift : (γ : Type w) → (δ : Type x) → (γ → n δ) → m γ → n δ} {γ : Type x} {it : @Std.IterM α m β} {init : γ}
      {P : β → Prop} {hP : ∀ (b : β), @Std.IterM.IsPlausibleIndirectOutput α β m inst it b → P b}
      (PlausibleForInStep : β → γ → ForInStep γ → Prop)
      {f : (b : β) → P b → (c : γ) → n (@Subtype (ForInStep γ) (PlausibleForInStep b c))},
      @Std.IteratorLoop.WellFounded α m β inst γ PlausibleForInStep →
        @Eq (n γ) (@Std.IterM.DefaultConsumers.forIn' m α β inst n inst_1 lift γ PlausibleForInStep it init P hP f)
          ((fun (x : Std.Shrink (@Std.IterM.Step α m β inst it) → n γ) =>
              lift (Std.Shrink (@Std.IterM.Step α m β inst it)) γ x (@Std.IterM.step α m β inst it))
            fun (s : Std.Shrink (@Std.IterM.Step α m β inst it)) =>
            @Std.IterM.DefaultConsumers.forIn'_eq_match_step.match_3 α β m inst it
              (fun (x : @Std.IterM.Step α m β inst it) => n γ) (@Std.Shrink.inflate (@Std.IterM.Step α m β inst it) s)
              (fun (it' : @Std.IterM α m β) (out : β)
                  (h : @Std.IterM.IsPlausibleStep α m β inst it (@Std.IterStep.yield (@Std.IterM α m β) β it' out)) =>
                @Bind.bind n (@Monad.toBind n inst_1) (@Subtype (ForInStep γ) (PlausibleForInStep out init)) γ
                  (f out
                    (hP out
                      (@Std.IterM.IsPlausibleIndirectOutput.direct α β m inst it out
                        (@Exists.intro (@Std.IterM α m β)
                          (fun (it' : @Std.IterM α m β) =>
                            @Std.IterM.IsPlausibleStep α m β inst it (@Std.IterStep.yield (@Std.IterM α m β) β it' out))
                          it' h)))
                    init)
                  fun (__do_lift : @Subtype (ForInStep γ) (PlausibleForInStep out init)) =>
                  @Std.IterM.DefaultConsumers.forIn'_eq_match_step.match_1 β γ init PlausibleForInStep out
                    (fun (__do_lift : @Subtype (ForInStep γ) (PlausibleForInStep out init)) => n γ) __do_lift
                    (fun (c : γ) (property : PlausibleForInStep out init (@ForInStep.yield γ c)) =>
                      @Std.IterM.DefaultConsumers.forIn' m α β inst n inst_1 lift γ PlausibleForInStep it' c P
                        (fun (x : β) (h' : @Std.IterM.IsPlausibleIndirectOutput α β m inst it' x) =>
                          hP x
                            (@Std.IterM.IsPlausibleIndirectOutput.indirect α β m inst it it' x
                              (@Exists.intro (Std.IterStep (@Std.IterM α m β) β)
                                (fun (step : Std.IterStep (@Std.IterM α m β) β) =>
                                  And
                                    (@Eq (Option (@Std.IterM α m β)) (@Std.IterStep.successor (@Std.IterM α m β) β step)
                                      (@Option.some (@Std.IterM α m β) it'))
                                    (@Std.IterM.IsPlausibleStep α m β inst it step))
                                (@Std.IterStep.yield (@Std.IterM α m β) β it' out)
                                (@And.intro
                                  (@Eq (Option (@Std.IterM α m β))
                                    (@Std.IterStep.successor (@Std.IterM α m β) β
                                      (@Std.IterStep.yield (@Std.IterM α m β) β it' out))
                                    (@Option.some (@Std.IterM α m β) it'))
                                  (@Std.IterM.IsPlausibleStep α m β inst it
                                    (@Std.IterStep.yield (@Std.IterM α m β) β it' out))
                                  (@rfl (Option (@Std.IterM α m β))
                                    (@Std.IterStep.successor (@Std.IterM α m β) β
                                      (@Std.IterStep.yield (@Std.IterM α m β) β it' out)))
                                  h))
                              h'))
                        f)
                    fun (c : γ) (property : PlausibleForInStep out init (@ForInStep.done γ c)) =>
                    @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_1)) γ c)
              (fun (it' : @Std.IterM α m β)
                  (h : @Std.IterM.IsPlausibleStep α m β inst it (@Std.IterStep.skip (@Std.IterM α m β) β it')) =>
                @Std.IterM.DefaultConsumers.forIn' m α β inst n inst_1 lift γ PlausibleForInStep it' init P
                  (fun (x : β) (h' : @Std.IterM.IsPlausibleIndirectOutput α β m inst it' x) =>
                    hP x
                      (@Std.IterM.IsPlausibleIndirectOutput.indirect α β m inst it it' x
                        (@Exists.intro (Std.IterStep (@Std.IterM α m β) β)
                          (fun (step : Std.IterStep (@Std.IterM α m β) β) =>
                            And
                              (@Eq (Option (@Std.IterM α m β)) (@Std.IterStep.successor (@Std.IterM α m β) β step)
                                (@Option.some (@Std.IterM α m β) it'))
                              (@Std.IterM.IsPlausibleStep α m β inst it step))
                          (@Std.IterStep.skip (@Std.IterM α m β) β it')
                          (@And.intro
                            (@Eq (Option (@Std.IterM α m β))
                              (@Std.IterStep.successor (@Std.IterM α m β) β (@Std.IterStep.skip (@Std.IterM α m β) β it'))
                              (@Option.some (@Std.IterM α m β) it'))
                            (@Std.IterM.IsPlausibleStep α m β inst it (@Std.IterStep.skip (@Std.IterM α m β) β it'))
                            (@rfl (Option (@Std.IterM α m β))
                              (@Std.IterStep.successor (@Std.IterM α m β) β (@Std.IterStep.skip (@Std.IterM α m β) β it')))
                            h))
                        h'))
                  f)
              fun (property : @Std.IterM.IsPlausibleStep α m β inst it (@Std.IterStep.done (@Std.IterM α m β) β)) =>
              @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_1)) γ init) :=
  no_implicit_lambda% (drop_unused% Std.IterM.DefaultConsumers.forIn'_eq_match_step 6)

-- `Std.Rco.isEmpty_iff_forall_not_mem` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Rco.isEmpty_iff_forall_not_mem.h7.{u} :
    ∀ {α : Type u} {r : Std.Rco α} [inst : LE α] [inst_1 : LT α] [inst_2 : DecidableLT α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxo.HasSize α] [inst_5 : Std.PRange.LawfulUpwardEnumerableLE α]
      [inst_6 : Std.PRange.LawfulUpwardEnumerableLT α] [inst_7 : Std.Rxo.IsAlwaysFinite α]
      [inst_8 : Std.PRange.LawfulUpwardEnumerable α], r.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Rco.isEmpty_iff_forall_not_mem 7)

-- `Std.Rco.isEmpty_iff_forall_not_mem` idx 10: unused in the library's proof
theorem HypCheckProof.Std.Rco.isEmpty_iff_forall_not_mem.h10.{u} :
    ∀ {α : Type u} {r : Std.Rco α} [inst : LE α] [inst_1 : LT α] [inst_2 : DecidableLT α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxo.HasSize α] [inst_5 : Std.Rxo.LawfulHasSize α]
      [inst_6 : Std.PRange.LawfulUpwardEnumerableLE α] [inst_7 : Std.PRange.LawfulUpwardEnumerableLT α]
      [inst_8 : Std.PRange.LawfulUpwardEnumerable α], r.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Rco.isEmpty_iff_forall_not_mem 10)

-- `Std.Rcc.mem_succ_succ_iff` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Rcc.mem_succ_succ_iff.h7.{u} :
    ∀ {α : Type u} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LinearlyUpwardEnumerable α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLE α]
      [inst_5 : Std.PRange.InfinitelyUpwardEnumerable α] [inst_6 : Std.PRange.LawfulUpwardEnumerable α] {lo hi a : α},
      a ∈ Std.PRange.UpwardEnumerable.succ lo...=Std.PRange.UpwardEnumerable.succ hi ↔
        ∃ (a' : α), a = Std.PRange.UpwardEnumerable.succ a' ∧ a' ∈ lo...=hi :=
  no_implicit_lambda% (drop_unused% Std.Rcc.mem_succ_succ_iff 7)

-- `Std.Rio.mem_iff_mem_rco` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Rio.mem_iff_mem_rco.h6.{u} :
    ∀ {α : Type u} {r : Std.Rio α} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.PRange.Least? α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : @Std.PRange.LawfulUpwardEnumerableLE α inst_3 inst]
      [inst_5 : @Std.PRange.LawfulUpwardEnumerableLeast? α inst_3 inst_2] [inst_6 : @Std.Rxo.IsAlwaysFinite α inst_3 inst_1]
      {a : α},
      Iff (@Membership.mem α (Std.Rio α) (@Std.Rio.instMembershipOfLT α inst_1) r a)
        (@Membership.mem α (Std.Rco α) (@Std.Rco.instMembershipOfLEOfLT α inst inst_1)
          (@Std.Rco.mk α
            (@Std.PRange.UpwardEnumerable.least α inst_3 inst_2 inst_5 (@Nonempty.intro α (@Std.Rio.upper α r)))
            (@Std.Rio.upper α r))
          a) :=
  no_implicit_lambda% (drop_unused% Std.Rio.mem_iff_mem_rco 6)

-- `Std.Rio.mem_iff_mem_rco` idx 9: unused in the library's proof
theorem HypCheckProof.Std.Rio.mem_iff_mem_rco.h9.{u} :
    ∀ {α : Type u} {r : Std.Rio α} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.PRange.Least? α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : @Std.PRange.LawfulUpwardEnumerable α inst_3]
      [inst_5 : @Std.PRange.LawfulUpwardEnumerableLE α inst_3 inst]
      [inst_6 : @Std.PRange.LawfulUpwardEnumerableLeast? α inst_3 inst_2] {a : α},
      Iff (@Membership.mem α (Std.Rio α) (@Std.Rio.instMembershipOfLT α inst_1) r a)
        (@Membership.mem α (Std.Rco α) (@Std.Rco.instMembershipOfLEOfLT α inst inst_1)
          (@Std.Rco.mk α
            (@Std.PRange.UpwardEnumerable.least α inst_3 inst_2 inst_6 (@Nonempty.intro α (@Std.Rio.upper α r)))
            (@Std.Rio.upper α r))
          a) :=
  no_implicit_lambda% (drop_unused% Std.Rio.mem_iff_mem_rco 9)

-- `Std.Roi.mem_succ_iff` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Roi.mem_succ_iff.h6.{u} :
    ∀ {α : Type u} [inst : LT α] [inst_1 : Std.PRange.UpwardEnumerable α] [inst_2 : Std.PRange.LinearlyUpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLT α] [inst_4 : Std.PRange.InfinitelyUpwardEnumerable α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] {lo a : α},
      a ∈ Std.PRange.UpwardEnumerable.succ lo<...* ↔ ∃ (a' : α), a = Std.PRange.UpwardEnumerable.succ a' ∧ a' ∈ lo<...* :=
  no_implicit_lambda% (drop_unused% Std.Roi.mem_succ_iff 6)

-- `Std.Iter.all_eq_not_any_not` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iter.all_eq_not_any_not.h6.{w, u_1, u_2} :
    ∀ {m : Type u_1 → Type u_2} {α β : Type w} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      [inst_2 : Monad m] [inst_3 : @Std.IteratorLoop α Id β inst Id]
      [inst_4 : @Std.LawfulIteratorLoop β α Id Id Id.instMonad Id.instMonad inst inst_3] {it : @Std.Iter α β}
      {p : β → Bool},
      @Eq Bool (@Std.Iter.all α β inst inst_3 p it) (@Std.Iter.any α β inst inst_3 (fun (x : β) => (p x).not) it).not :=
  no_implicit_lambda% (drop_unused% Std.Iter.all_eq_not_any_not 6)

-- `Std.IterM.allM_eq_forIn` idx 4: unused in the library's proof
theorem HypCheckProof.Std.IterM.allM_eq_forIn.h4.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : Monad m] [inst_2 : @LawfulMonad m inst_1]
      [inst_3 : @Std.IteratorLoop α m β inst m] [inst_4 : @Std.LawfulIteratorLoop β α m m inst_1 inst_1 inst inst_3]
      {it : @Std.IterM α m β} {p : β → m (ULift Bool)},
      @Eq (m (ULift Bool)) (@Std.IterM.allM α β m inst_1 inst inst_3 p it)
        (@ForIn.forIn m (@Std.IterM α m β) β
          (@Std.IterM.instForInOfIteratorLoop m m α β inst inst_3 (instMonadLiftT m) inst_1) (ULift Bool) it
          (@ULift.up Bool Bool.true) fun (x : β) (x_1 : ULift Bool) =>
          @Bind.bind m (@Monad.toBind m inst_1) (ULift Bool) (ForInStep (ULift Bool)) (p x) fun (__do_lift : ULift Bool) =>
            @ite (m (ForInStep (ULift Bool))) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
              (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true)
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_1)) (ForInStep (ULift Bool))
                (@ForInStep.yield (ULift Bool) (@ULift.up Bool Bool.true)))
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_1)) (ForInStep (ULift Bool))
                (@ForInStep.done (ULift Bool) (@ULift.up Bool Bool.false)))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.allM_eq_forIn 4)

-- `Std.IterM.allM_eq_forIn` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.allM_eq_forIn.h6.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      [inst_2 : Monad m] [inst_3 : @Std.IteratorLoop α m β inst m]
      [inst_4 : @Std.LawfulIteratorLoop β α m m inst_2 inst_2 inst inst_3] {it : @Std.IterM α m β} {p : β → m (ULift Bool)},
      @Eq (m (ULift Bool)) (@Std.IterM.allM α β m inst_2 inst inst_3 p it)
        (@ForIn.forIn m (@Std.IterM α m β) β
          (@Std.IterM.instForInOfIteratorLoop m m α β inst inst_3 (instMonadLiftT m) inst_2) (ULift Bool) it
          (@ULift.up Bool Bool.true) fun (x : β) (x_1 : ULift Bool) =>
          @Bind.bind m (@Monad.toBind m inst_2) (ULift Bool) (ForInStep (ULift Bool)) (p x) fun (__do_lift : ULift Bool) =>
            @ite (m (ForInStep (ULift Bool))) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
              (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true)
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep (ULift Bool))
                (@ForInStep.yield (ULift Bool) (@ULift.up Bool Bool.true)))
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep (ULift Bool))
                (@ForInStep.done (ULift Bool) (@ULift.up Bool Bool.false)))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.allM_eq_forIn 6)

-- `Std.IterM.allM_eq_forIn` idx 8: unused in the library's proof
theorem HypCheckProof.Std.IterM.allM_eq_forIn.h8.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      [inst_2 : Monad m] [inst_3 : @LawfulMonad m inst_2] [inst_4 : @Std.IteratorLoop α m β inst m] {it : @Std.IterM α m β}
      {p : β → m (ULift Bool)},
      @Eq (m (ULift Bool)) (@Std.IterM.allM α β m inst_2 inst inst_4 p it)
        (@ForIn.forIn m (@Std.IterM α m β) β
          (@Std.IterM.instForInOfIteratorLoop m m α β inst inst_4 (instMonadLiftT m) inst_2) (ULift Bool) it
          (@ULift.up Bool Bool.true) fun (x : β) (x_1 : ULift Bool) =>
          @Bind.bind m (@Monad.toBind m inst_2) (ULift Bool) (ForInStep (ULift Bool)) (p x) fun (__do_lift : ULift Bool) =>
            @ite (m (ForInStep (ULift Bool))) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
              (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true)
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep (ULift Bool))
                (@ForInStep.yield (ULift Bool) (@ULift.up Bool Bool.true)))
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep (ULift Bool))
                (@ForInStep.done (ULift Bool) (@ULift.up Bool Bool.false)))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.allM_eq_forIn 8)

-- `Std.Iter.anyM_eq_forIn` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Iter.anyM_eq_forIn.h4.{w, w'} :
    ∀ {α β : Type w} {m : Type → Type w'} [inst : Std.Iterator α Id β] [inst_1 : Monad m] [inst_2 : @LawfulMonad m inst_1]
      [inst_3 : @Std.IteratorLoop α Id β inst m] [inst_4 : @Std.LawfulIteratorLoop β α Id m Id.instMonad inst_1 inst inst_3]
      {it : @Std.Iter α β} {p : β → m Bool},
      @Eq (m Bool) (@Std.Iter.anyM α β m inst_1 inst inst_3 p it)
        (@ForIn.forIn m (@Std.Iter α β) β (@Std.instForInIterOfMonadOfIteratorLoopId α β m inst_1 inst inst_3) Bool it
          Bool.false fun (x : β) (x_1 : Bool) =>
          @Bind.bind m (@Monad.toBind m inst_1) Bool (ForInStep Bool) (p x) fun (__do_lift : Bool) =>
            @ite (m (ForInStep Bool)) (@Eq Bool __do_lift Bool.true) (instDecidableEqBool __do_lift Bool.true)
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_1)) (ForInStep Bool)
                (@ForInStep.done Bool Bool.true))
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_1)) (ForInStep Bool)
                (@ForInStep.yield Bool Bool.false))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.anyM_eq_forIn 4)

-- `Std.Iter.anyM_eq_forIn` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iter.anyM_eq_forIn.h6.{w, w'} :
    ∀ {α β : Type w} {m : Type → Type w'} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      [inst_2 : Monad m] [inst_3 : @Std.IteratorLoop α Id β inst m]
      [inst_4 : @Std.LawfulIteratorLoop β α Id m Id.instMonad inst_2 inst inst_3] {it : @Std.Iter α β} {p : β → m Bool},
      @Eq (m Bool) (@Std.Iter.anyM α β m inst_2 inst inst_3 p it)
        (@ForIn.forIn m (@Std.Iter α β) β (@Std.instForInIterOfMonadOfIteratorLoopId α β m inst_2 inst inst_3) Bool it
          Bool.false fun (x : β) (x_1 : Bool) =>
          @Bind.bind m (@Monad.toBind m inst_2) Bool (ForInStep Bool) (p x) fun (__do_lift : Bool) =>
            @ite (m (ForInStep Bool)) (@Eq Bool __do_lift Bool.true) (instDecidableEqBool __do_lift Bool.true)
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep Bool)
                (@ForInStep.done Bool Bool.true))
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep Bool)
                (@ForInStep.yield Bool Bool.false))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.anyM_eq_forIn 6)

-- `Std.Iter.anyM_eq_forIn` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Iter.anyM_eq_forIn.h8.{w, w'} :
    ∀ {α β : Type w} {m : Type → Type w'} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      [inst_2 : Monad m] [inst_3 : @LawfulMonad m inst_2] [inst_4 : @Std.IteratorLoop α Id β inst m] {it : @Std.Iter α β}
      {p : β → m Bool},
      @Eq (m Bool) (@Std.Iter.anyM α β m inst_2 inst inst_4 p it)
        (@ForIn.forIn m (@Std.Iter α β) β (@Std.instForInIterOfMonadOfIteratorLoopId α β m inst_2 inst inst_4) Bool it
          Bool.false fun (x : β) (x_1 : Bool) =>
          @Bind.bind m (@Monad.toBind m inst_2) Bool (ForInStep Bool) (p x) fun (__do_lift : Bool) =>
            @ite (m (ForInStep Bool)) (@Eq Bool __do_lift Bool.true) (instDecidableEqBool __do_lift Bool.true)
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep Bool)
                (@ForInStep.done Bool Bool.true))
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep Bool)
                (@ForInStep.yield Bool Bool.false))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.anyM_eq_forIn 8)

-- `Std.IterM.any_eq_anyM` idx 4: unused in the library's proof
theorem HypCheckProof.Std.IterM.any_eq_anyM.h4.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : Monad m] [inst_2 : @LawfulMonad m inst_1]
      [inst_3 : @Std.IteratorLoop α m β inst m] [inst_4 : @Std.LawfulIteratorLoop β α m m inst_1 inst_1 inst inst_3]
      {it : @Std.IterM α m β} {p : β → Bool},
      @Eq (m (ULift Bool)) (@Std.IterM.any α β m inst_1 inst inst_3 p it)
        (@Std.IterM.anyM α β m inst_1 inst inst_3
          (fun (x : β) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_1)) (ULift Bool) (@ULift.up Bool (p x)))
          it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.any_eq_anyM 4)

-- `Std.IterM.any_eq_anyM` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.any_eq_anyM.h6.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      [inst_2 : Monad m] [inst_3 : @Std.IteratorLoop α m β inst m]
      [inst_4 : @Std.LawfulIteratorLoop β α m m inst_2 inst_2 inst inst_3] {it : @Std.IterM α m β} {p : β → Bool},
      @Eq (m (ULift Bool)) (@Std.IterM.any α β m inst_2 inst inst_3 p it)
        (@Std.IterM.anyM α β m inst_2 inst inst_3
          (fun (x : β) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ULift Bool) (@ULift.up Bool (p x)))
          it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.any_eq_anyM 6)

-- `Std.IterM.any_eq_anyM` idx 8: unused in the library's proof
theorem HypCheckProof.Std.IterM.any_eq_anyM.h8.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      [inst_2 : Monad m] [inst_3 : @LawfulMonad m inst_2] [inst_4 : @Std.IteratorLoop α m β inst m] {it : @Std.IterM α m β}
      {p : β → Bool},
      @Eq (m (ULift Bool)) (@Std.IterM.any α β m inst_2 inst inst_4 p it)
        (@Std.IterM.anyM α β m inst_2 inst inst_4
          (fun (x : β) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ULift Bool) (@ULift.up Bool (p x)))
          it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.any_eq_anyM 8)

-- `Std.IterM.toArray_toList` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_toList.h6.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : @LawfulMonad m inst] [inst_2 : Std.Iterator α m β]
      {it : @Std.IterM α m β},
      @Eq (m (Array β))
        (@Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst)) (List β) (Array β) (@List.toArray β)
          (@Std.IterM.toList α m inst β inst_2 it))
        (@Std.IterM.toArray α β m inst inst_2 it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_toList 6)

-- `Std.Iter.all_eq_allM` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Iter.all_eq_allM.h3.{w} :
    ∀ {α β : Type w} [inst : Std.Iterator α Id β] [inst_1 : @Std.IteratorLoop α Id β inst Id]
      [inst_2 : @Std.LawfulIteratorLoop β α Id Id Id.instMonad Id.instMonad inst inst_1] {it : @Std.Iter α β}
      {p : β → Bool},
      @Eq Bool (@Std.Iter.all α β inst inst_1 p it)
        (@Id.run Bool
          (@Std.Iter.allM α β Id Id.instMonad inst inst_1
            (fun (x : β) => @Pure.pure Id (@Applicative.toPure Id (@Monad.toApplicative Id Id.instMonad)) Bool (p x)) it)) :=
  no_implicit_lambda% (drop_unused% Std.Iter.all_eq_allM 3)

-- `Std.Iter.all_eq_allM` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Iter.all_eq_allM.h5.{w} :
    ∀ {α β : Type w} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      [inst_2 : @Std.IteratorLoop α Id β inst Id] {it : @Std.Iter α β} {p : β → Bool},
      @Eq Bool (@Std.Iter.all α β inst inst_2 p it)
        (@Id.run Bool
          (@Std.Iter.allM α β Id Id.instMonad inst inst_2
            (fun (x : β) => @Pure.pure Id (@Applicative.toPure Id (@Monad.toApplicative Id Id.instMonad)) Bool (p x)) it)) :=
  no_implicit_lambda% (drop_unused% Std.Iter.all_eq_allM 5)

-- `List.anyM_toArray'` idx 3: unused in the library's proof
theorem HypCheckProof.List.anyM_toArray'.h3.{u_1, u_2} :
    ∀ {m : Type → Type u_1} {α : Type u_2} [inst : Monad m] {p : α → m Bool} {l : List α} {stop : Nat},
      stop = l.toArray.size → Array.anyM p l.toArray 0 stop = List.anyM p l :=
  no_implicit_lambda% (drop_unused% List.anyM_toArray' 3)

-- `Std.IterM.foldM_filterWithPostcondition` idx 16: unused in the library's proof
theorem HypCheckProof.Std.IterM.foldM_filterWithPostcondition.h16.{w, w', w'', w'''} :
    ∀ {α β δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : Monad m] [inst_3 : Monad n] [inst_4 : Monad o]
      [inst_5 : @LawfulMonad m inst_2] [inst_6 : @LawfulMonad n inst_3] [inst_7 : @LawfulMonad o inst_4]
      [inst_8 : @Std.IteratorLoop α m β inst n] [inst_9 : @Std.IteratorLoop α m β inst o]
      [inst_10 : @Std.LawfulIteratorLoop β α m o inst_2 inst_4 inst inst_9] [inst_11 : MonadLiftT m n]
      [inst_12 : MonadLiftT n o] [inst_13 : @LawfulMonadLiftT m n inst_2 inst_3 inst_11]
      [inst_14 : @LawfulMonadLiftT n o inst_3 inst_4 inst_12] {f : β → Std.Iterators.PostconditionT n (ULift Bool)}
      {g : δ → β → o δ} {init : δ} {it : @Std.IterM α m β},
      @Eq (o δ)
        (@Std.IterM.foldM n o inst_4
          (@Std.Iterators.Types.FilterMap α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_11 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_3)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (f b))
          β δ
          (@Std.Iterators.Types.FilterMap.instIterator α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_11 x)
            (fun (b : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_3)) (ULift Bool)
                (Option β)
                (fun (x : ULift Bool) =>
                  @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                    (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
                (f b))
            inst inst_3)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β m n o inst_3 inst_4 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_11 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_3)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (f b))
          inst_12 g init (@Std.IterM.filterWithPostcondition α β m n inst_3 inst_11 inst f it))
        (@Std.IterM.foldM m o inst_4 α β δ inst inst_9
          (@instMonadLiftTOfMonadLift m n o (@MonadLift.mk n o fun {α : Type w} => @MonadLiftT.monadLift n o inst_12 α)
            inst_11)
          (fun (d : δ) (b : β) =>
            @Bind.bind o (@Monad.toBind o inst_4) (ULift Bool) δ
              (@liftM n o inst_12 (ULift Bool) (@Std.Iterators.PostconditionT.run n inst_3 (ULift Bool) (f b)))
              fun (__do_lift : ULift Bool) =>
              @ite (o δ) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
                (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true) (g d b)
                (@Pure.pure o (@Applicative.toPure o (@Monad.toApplicative o inst_4)) δ d))
          init it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.foldM_filterWithPostcondition 16)

-- `Std.IterM.forIn_filterMapWithPostcondition` idx 8: unused in the library's proof
theorem HypCheckProof.Std.IterM.forIn_filterMapWithPostcondition.h8.{u_1, u_2, u_3, u_4} :
    ∀ {m : Type u_1 → Type u_2} {n : Type u_1 → Type u_3} {o : Type u_1 → Type u_4} {α β β₂ γ : Type u_1} [inst : Monad m]
      [inst_1 : Monad n] [inst_2 : @LawfulMonad n inst_1] [inst_3 : Monad o] [inst_4 : @LawfulMonad o inst_3]
      [inst_5 : MonadLiftT m n] [inst_6 : @LawfulMonadLiftT m n inst inst_1 inst_5] [inst_7 : MonadLiftT n o]
      [inst_8 : @LawfulMonadLiftT n o inst_1 inst_3 inst_7] [inst_9 : Std.Iterator α m β]
      [inst_10 : @Std.Iterators.Finite α m β inst_9] [inst_11 : @Std.IteratorLoop α m β inst_9 o]
      [inst : @Std.LawfulIteratorLoop β α m o inst inst_3 inst_9 inst_11] {it : @Std.IterM α m β}
      {f : β → Std.Iterators.PostconditionT n (Option β₂)} {init : γ} {g : β₂ → γ → o (ForInStep γ)},
      @Eq (o γ)
        (@ForIn.forIn o
          (@Std.IterM
            (@Std.Iterators.Types.FilterMap α β β₂ m n (fun ⦃x : Type u_1⦄ => @MonadLiftT.monadLift m n inst_5 x) f) n β₂)
          β₂
          (@Std.IterM.instForInOfIteratorLoop n o
            (@Std.Iterators.Types.FilterMap α β β₂ m n (fun ⦃x : Type u_1⦄ => @MonadLiftT.monadLift m n inst_5 x) f) β₂
            (@Std.Iterators.Types.FilterMap.instIterator α β β₂ m n
              (fun ⦃x : Type u_1⦄ => @MonadLiftT.monadLift m n inst_5 x) f inst_9 inst_1)
            (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β₂ m n o inst_1 inst_3 inst_9
              (fun ⦃x : Type u_1⦄ => @MonadLiftT.monadLift m n inst_5 x) f)
            inst_7 inst_3)
          γ (@Std.IterM.filterMapWithPostcondition α β β₂ m n inst_5 inst_9 f it) init g)
        (@ForIn.forIn o (@Std.IterM α m β) β
          (@Std.IterM.instForInOfIteratorLoop m o α β inst_9 inst_11
            (@instMonadLiftTOfMonadLift m n o (@MonadLift.mk n o fun {α : Type u_1} => @MonadLiftT.monadLift n o inst_7 α)
              inst_5)
            inst_3)
          γ it init fun (out : β) (acc : γ) =>
          @Bind.bind o (@Monad.toBind o inst_3) (Option β₂) (ForInStep γ)
            (@liftM n o inst_7 (Option β₂) (@Std.Iterators.PostconditionT.run n inst_1 (Option β₂) (f out)))
            fun (__do_lift : Option β₂) =>
            @Std.IterM.forIn_filterMapWithPostcondition.match_1 β₂ (fun (__do_lift : Option β₂) => o (ForInStep γ))
              __do_lift (fun (c : β₂) => g c acc) fun (_ : Unit) =>
              @Pure.pure o (@Applicative.toPure o (@Monad.toApplicative o inst_3)) (ForInStep γ) (@ForInStep.yield γ acc)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.forIn_filterMapWithPostcondition 8)

-- `Std.IterM.all_filterMapM` idx 16: unused in the library's proof
theorem HypCheckProof.Std.IterM.all_filterMapM.h16.{w, w', w''} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : @Std.IteratorLoop α m β inst m]
      [inst_4 : Monad m] [inst_5 : @LawfulMonad m inst_4] [inst_6 : Monad n] [inst_7 : MonadAttach n]
      [inst_8 : @LawfulMonad n inst_6] [inst_9 : @WeaklyLawfulMonadAttach n inst_6 inst_7]
      [inst_10 : @LawfulMonadLiftT m n inst_4 inst_6 inst_2] {it : @Std.IterM α m β} {f : β → n (Option β')}
      {p : β' → Bool},
      @Eq (n (ULift Bool))
        (@Std.IterM.all
          (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_7 (f b))
          β' n inst_6
          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_7 (f b)) inst inst_6)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β' m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_7 (f b))
          p (@Std.IterM.filterMapM α β β' m n inst inst_6 inst_7 inst_2 f it))
        (@Std.IterM.allM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          β n inst_6
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (fun (x : β) =>
            @Bind.bind n (@Monad.toBind n inst_6) (Option β') (ULift Bool) (f x) fun (__do_lift : Option β') =>
              @Std.IterM.forIn_filterMapWithPostcondition.match_1 β' (fun (__do_lift : Option β') => n (ULift Bool))
                __do_lift
                (fun (fx : β') =>
                  @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) (ULift Bool) (@ULift.up Bool (p fx)))
                fun (_ : Unit) =>
                @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) (ULift Bool)
                  (@ULift.up Bool Bool.true))
          (@Std.IterM.mapM α β β m n inst inst_6 inst_7 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.all_filterMapM 16)

-- `Std.IterM.toArray_flatMap` idx 11: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_flatMap.h11.{w, w'} :
    ∀ {α α₂ β γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : MonadAttach m] [inst_2 : @LawfulMonad m inst]
      [inst_3 : @WeaklyLawfulMonadAttach m inst inst_1] [inst_4 : Std.Iterator α m β] [inst_5 : Std.Iterator α₂ m γ]
      [inst_6 : @Std.Iterators.Finite α₂ m γ inst_5] [inst_7 : Std.Iterator α m β] [inst_8 : Std.Iterator α₂ m γ]
      [inst_9 : @Std.Iterators.Finite α m β inst_7] [inst_10 : @Std.Iterators.Finite α₂ m γ inst_8]
      {f : β → @Std.IterM α₂ m γ} {it₁ : @Std.IterM α m β},
      @Eq (m (Array γ))
        (@Std.IterM.toArray
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m)
          γ m inst
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_7
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            inst_8)
          (@Std.IterM.flatMap α β α₂ γ m inst inst_7 inst_8 f it₁))
        (@Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst)) (Array (Array γ)) (Array γ)
          (@Array.flatten γ)
          (@Std.IterM.toArray
            (@Std.Iterators.Types.Map α β (Array γ) m m (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (Array γ) m inst_1 (@Std.IterM.toArray α₂ γ m inst inst_8 (f b)))
            (Array γ) m inst
            (@Std.Iterators.Types.Map.instIterator α β (Array γ) m m inst inst_7
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (Array γ) m inst_1 (@Std.IterM.toArray α₂ γ m inst inst_8 (f b)))
            (@Std.IterM.mapM α β (Array γ) m m inst_7 inst inst_1 (instMonadLiftT m)
              (fun (b : β) => @Std.IterM.toArray α₂ γ m inst inst_8 (f b)) it₁))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_flatMap 11)

-- `Std.IterM.toArray_flatMap` idx 12: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_flatMap.h12.{w, w'} :
    ∀ {α α₂ β γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : MonadAttach m] [inst_2 : @LawfulMonad m inst]
      [inst_3 : @WeaklyLawfulMonadAttach m inst inst_1] [inst_4 : Std.Iterator α m β] [inst_5 : Std.Iterator α₂ m γ]
      [inst_6 : @Std.Iterators.Finite α m β inst_4] [inst_7 : Std.Iterator α m β] [inst_8 : Std.Iterator α₂ m γ]
      [inst_9 : @Std.Iterators.Finite α m β inst_7] [inst_10 : @Std.Iterators.Finite α₂ m γ inst_8]
      {f : β → @Std.IterM α₂ m γ} {it₁ : @Std.IterM α m β},
      @Eq (m (Array γ))
        (@Std.IterM.toArray
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m)
          γ m inst
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_7
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            inst_8)
          (@Std.IterM.flatMap α β α₂ γ m inst inst_7 inst_8 f it₁))
        (@Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst)) (Array (Array γ)) (Array γ)
          (@Array.flatten γ)
          (@Std.IterM.toArray
            (@Std.Iterators.Types.Map α β (Array γ) m m (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (Array γ) m inst_1 (@Std.IterM.toArray α₂ γ m inst inst_8 (f b)))
            (Array γ) m inst
            (@Std.Iterators.Types.Map.instIterator α β (Array γ) m m inst inst_7
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (Array γ) m inst_1 (@Std.IterM.toArray α₂ γ m inst inst_8 (f b)))
            (@Std.IterM.mapM α β (Array γ) m m inst_7 inst inst_1 (instMonadLiftT m)
              (fun (b : β) => @Std.IterM.toArray α₂ γ m inst inst_8 (f b)) it₁))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_flatMap 12)

-- `Lean.Grind.CommRing.lt_false_of_toPPX_eqS` idx 6: unused in the library's proof
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eqS.h6.{u_1} :
    ∀ {α : Type u_1} [inst : Lean.Grind.CommSemiring α] [inst_1 : Lean.Grind.AddRightCancel α] [inst_2 : LE α]
      [inst_3 : LT α] [inst_4 : Std.LawfulOrderLT α] (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool)
      (a b : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.PPoly),
      Lean.Grind.CommRing.Expr.degSOk_k B a b = Bool.true →
        p = Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a →
          p = Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b →
            (Lean.Grind.CommRing.Expr.denoteS ctx a < Lean.Grind.CommRing.Expr.denoteS ctx b) = False :=
  no_implicit_lambda% (drop_unused% Lean.Grind.CommRing.lt_false_of_toPPX_eqS 6)

-- `Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition.h6.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : Monad n]
      [inst_2 : MonadAttach n] [inst_3 : @LawfulMonad n inst_1] [inst_4 : @WeaklyLawfulMonadAttach n inst_1 inst_2]
      [inst_5 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_1 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (Array γ))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b))
          γ n inst_1
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_1 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b))
          (@Std.IterM.mapM α β γ m n inst inst_1 inst_2 inst_5 f it))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b))
          γ n inst_1
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_1 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst_1 inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition 6)

-- `Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition` idx 9: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition.h9.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @WeaklyLawfulMonadAttach n inst_2 inst_3]
      [inst_5 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_2 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (Array γ))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          γ n inst_2
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapM α β γ m n inst inst_2 inst_3 inst_5 f it))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          γ n inst_2
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition 9)

-- `Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition` idx 10: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition.h10.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @LawfulMonad n inst_2] [inst_5 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (Array γ))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          γ n inst_2
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapM α β γ m n inst inst_2 inst_3 inst_5 f it))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          γ n inst_2
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition 10)

-- `Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition` idx 12: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition.h12.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst : @LawfulMonad m inst]
      [inst : Monad n] [inst_1 : MonadAttach n] [inst_2 : @LawfulMonad n inst]
      [inst_3 : @WeaklyLawfulMonadAttach n inst inst_1] [inst_4 : MonadLiftT m n] [inst_5 : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst_5] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (Array γ))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b))
          γ n inst
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst inst_5
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b))
          (@Std.IterM.mapM α β γ m n inst_5 inst inst_1 inst_4 f it))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b))
          γ n inst
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst inst_5
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst inst_4 inst_5
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition 12)

-- `Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition` idx 14: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition.h14.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @LawfulMonad n inst_2]
      [inst_5 : @WeaklyLawfulMonadAttach n inst_2 inst_3] [inst_6 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_6] [inst : Std.Iterator α m β] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (Array γ))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          γ n inst_2
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapM α β γ m n inst inst_2 inst_3 inst_6 f it))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          γ n inst_2
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_6 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_mapM_eq_toArray_mapWithPostcondition 14)

-- `Std.IterM.toList_mapM_eq_toList_filterMapM` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_mapM_eq_toList_filterMapM.h6.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : Monad n]
      [inst_2 : MonadAttach n] [inst_3 : @LawfulMonad n inst_1] [inst_4 : @WeaklyLawfulMonadAttach n inst_1 inst_2]
      [inst_5 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_1 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b))
          n inst_1 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_1 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b))
          (@Std.IterM.mapM α β γ m n inst inst_1 inst_2 inst_5 f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2
              (@Functor.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) γ (Option γ) (@Option.some γ)
                (f b)))
          n inst_1 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2
                (@Functor.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) γ (Option γ) (@Option.some γ)
                  (f b)))
            inst inst_1)
          (@Std.IterM.filterMapM α β γ m n inst inst_1 inst_2 inst_5
            (fun (b : β) =>
              @Functor.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) γ (Option γ) (@Option.some γ) (f b))
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_mapM_eq_toList_filterMapM 6)

-- `Std.IterM.toList_mapM_eq_toList_filterMapM` idx 12: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_mapM_eq_toList_filterMapM.h12.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst : @LawfulMonad m inst]
      [inst : Monad n] [inst_1 : MonadAttach n] [inst_2 : @LawfulMonad n inst]
      [inst_3 : @WeaklyLawfulMonadAttach n inst inst_1] [inst_4 : MonadLiftT m n] [inst_5 : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst_5] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b))
          n inst γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst inst_5
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b))
          (@Std.IterM.mapM α β γ m n inst_5 inst inst_1 inst_4 f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1
              (@Functor.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst)) γ (Option γ) (@Option.some γ) (f b)))
          n inst γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1
                (@Functor.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst)) γ (Option γ) (@Option.some γ)
                  (f b)))
            inst_5 inst)
          (@Std.IterM.filterMapM α β γ m n inst_5 inst inst_1 inst_4
            (fun (b : β) =>
              @Functor.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst)) γ (Option γ) (@Option.some γ) (f b))
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_mapM_eq_toList_filterMapM 12)

-- `Std.Iter.forIn'_congr` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iter.forIn'_congr.h6.{w, w'} :
    ∀ {γ α β : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : Std.Iterator α Id β]
      [inst_2 : @Std.IteratorLoop α Id β inst_1 m] {ita itb : @Std.Iter α β} (w : @Eq (@Std.Iter α β) ita itb) {b b' : γ},
      @Eq γ b b' →
        ∀
          {f :
            (a' : β) →
              @Membership.mem β (@Std.Iter α β)
                  (@Membership.mk β (@Std.Iter α β) fun (it : @Std.Iter α β) (out : β) =>
                    @Std.Iter.IsPlausibleIndirectOutput α β inst_1 it out)
                  ita a' →
                γ → m (ForInStep γ)}
          {g :
            (a' : β) →
              @Membership.mem β (@Std.Iter α β)
                  (@Membership.mk β (@Std.Iter α β) fun (it : @Std.Iter α β) (out : β) =>
                    @Std.Iter.IsPlausibleIndirectOutput α β inst_1 it out)
                  itb a' →
                γ → m (ForInStep γ)},
          (∀ (a : β)
              (m_1 :
                @Membership.mem β (@Std.Iter α β)
                  (@Membership.mk β (@Std.Iter α β) fun (it : @Std.Iter α β) (out : β) =>
                    @Std.Iter.IsPlausibleIndirectOutput α β inst_1 it out)
                  itb a)
              (b : γ),
              @Eq (m (ForInStep γ)) (f a (@Std.Iter.forIn'_congr._proof_1 α β inst_1 ita itb w a m_1) b) (g a m_1 b)) →
            @Eq (m γ)
              (@ForIn'.forIn' m (@Std.Iter α β) β
                (@Membership.mk β (@Std.Iter α β) fun (it : @Std.Iter α β) (out : β) =>
                  @Std.Iter.IsPlausibleIndirectOutput α β inst_1 it out)
                (@Std.Iter.instForIn' α β m inst inst_1 inst_2) γ ita b f)
              (@ForIn'.forIn' m (@Std.Iter α β) β
                (@Membership.mk β (@Std.Iter α β) fun (it : @Std.Iter α β) (out : β) =>
                  @Std.Iter.IsPlausibleIndirectOutput α β inst_1 it out)
                (@Std.Iter.instForIn' α β m inst inst_1 inst_2) γ itb b' g) :=
  no_implicit_lambda% (drop_unused% Std.Iter.forIn'_congr 6)

-- `Std.Rii.forIn'_toArray_eq_forIn'` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Rii.forIn'_toArray_eq_forIn'.h5.{u, w} :
    ∀ {α : Type u} {r : Std.Rii α} [inst : LT α] [inst : Std.PRange.Least? α] [inst_1 : Std.PRange.UpwardEnumerable α]
      [inst_2 : Std.PRange.LawfulUpwardEnumerableLeast? α] [inst_3 : Std.Rxi.IsAlwaysFinite α]
      [inst_4 : Std.PRange.LawfulUpwardEnumerable α] {γ : Type u} {init : γ} {m : Type u → Type w} [inst_5 : Monad m]
      [inst_6 : LawfulMonad m] {f : (a : α) → a ∈ r.toArray → γ → m (ForInStep γ)},
      ForIn'.forIn' r.toArray init f = ForIn'.forIn' r init fun (a : α) (x : a ∈ r) (acc : γ) => f a Std.Rii.mem_toArray acc :=
  no_implicit_lambda% (drop_unused% Std.Rii.forIn'_toArray_eq_forIn' 5)

-- `Std.IterM.toArray_mapWithPostcondition_eq_toArray_filterMapWithPostcondition` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_mapWithPostcondition_eq_toArray_filterMapWithPostcondition.h6.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : Monad n]
      [inst_2 : @LawfulMonad n inst_1] [inst_3 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_1 inst_3]
      [inst : Std.Iterator α m β] [inst_4 : @Std.Iterators.Finite α m β inst] {f : β → Std.Iterators.PostconditionT n γ}
      {it : @Std.IterM α m β},
      @Eq (n (Array γ))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) f)
          γ n inst_1
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_1 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) f)
          (@Std.IterM.mapWithPostcondition α β γ m n inst_1 inst_3 inst f it))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) fun (x : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) γ (Option γ)
              (@Option.some γ) (f x))
          γ n inst_1
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) γ (Option γ)
                (@Option.some γ) (f x))
            inst inst_1)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_3 inst
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) γ (Option γ)
                (@Option.some γ) (f x))
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_mapWithPostcondition_eq_toArray_filterMapWithPostcondition 6)

-- `Std.IterM.toArray_mapWithPostcondition_eq_toArray_filterMapWithPostcondition` idx 8: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_mapWithPostcondition_eq_toArray_filterMapWithPostcondition.h8.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_2 inst_3]
      [inst : Std.Iterator α m β] [inst_4 : @Std.Iterators.Finite α m β inst] {f : β → Std.Iterators.PostconditionT n γ}
      {it : @Std.IterM α m β},
      @Eq (n (Array γ))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) f)
          γ n inst_2
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) f)
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_3 inst f it))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) fun (x : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
              (@Option.some γ) (f x))
          γ n inst_2
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
                (@Option.some γ) (f x))
            inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_3 inst
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
                (@Option.some γ) (f x))
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_mapWithPostcondition_eq_toArray_filterMapWithPostcondition 8)

-- `Std.IterM.toArray_mapWithPostcondition_eq_toArray_filterMapWithPostcondition` idx 10: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_mapWithPostcondition_eq_toArray_filterMapWithPostcondition.h10.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst : @LawfulMonad m inst]
      [inst : Monad n] [inst_1 : @LawfulMonad n inst] [inst_2 : MonadLiftT m n] [inst_3 : Std.Iterator α m β]
      [inst_4 : @Std.Iterators.Finite α m β inst_3] {f : β → Std.Iterators.PostconditionT n γ} {it : @Std.IterM α m β},
      @Eq (n (Array γ))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst)) f)
          γ n inst
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst inst_3
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f)
          (@Std.IterM.mapWithPostcondition α β γ m n inst inst_2 inst_3 f it))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (x : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst)) γ (Option γ)
              (@Option.some γ) (f x))
          γ n inst
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst)) γ (Option γ)
                (@Option.some γ) (f x))
            inst_3 inst)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_2 inst_3
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst)) γ (Option γ)
                (@Option.some γ) (f x))
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_mapWithPostcondition_eq_toArray_filterMapWithPostcondition 10)

-- `Std.IterM.toArray_mapWithPostcondition_eq_toArray_filterMapWithPostcondition` idx 12: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_mapWithPostcondition_eq_toArray_filterMapWithPostcondition.h12.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : @LawfulMonad n inst_2] [inst_4 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_4] [inst : Std.Iterator α m β]
      {f : β → Std.Iterators.PostconditionT n γ} {it : @Std.IterM α m β},
      @Eq (n (Array γ))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) f)
          γ n inst_2
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) f)
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_4 inst f it))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (x : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
              (@Option.some γ) (f x))
          γ n inst_2
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
                (@Option.some γ) (f x))
            inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_4 inst
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
                (@Option.some γ) (f x))
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_mapWithPostcondition_eq_toArray_filterMapWithPostcondition 12)

-- `Std.IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition.h6.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : Monad n]
      [inst_2 : @LawfulMonad n inst_1] [inst_3 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_1 inst_3]
      [inst : Std.Iterator α m β] [inst_4 : @Std.Iterators.Finite α m β inst] {f : β → Std.Iterators.PostconditionT n γ}
      {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) f)
          n inst_1 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_1 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) f)
          (@Std.IterM.mapWithPostcondition α β γ m n inst_1 inst_3 inst f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) fun (x : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) γ (Option γ)
              (@Option.some γ) (f x))
          n inst_1 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) γ (Option γ)
                (@Option.some γ) (f x))
            inst inst_1)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_3 inst
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) γ (Option γ)
                (@Option.some γ) (f x))
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition 6)

-- `Std.IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition` idx 8: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition.h8.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_2 inst_3]
      [inst : Std.Iterator α m β] [inst_4 : @Std.Iterators.Finite α m β inst] {f : β → Std.Iterators.PostconditionT n γ}
      {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) f)
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) f)
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_3 inst f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) fun (x : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
              (@Option.some γ) (f x))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
                (@Option.some γ) (f x))
            inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_3 inst
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
                (@Option.some γ) (f x))
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition 8)

-- `Std.IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition` idx 10: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition.h10.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst : @LawfulMonad m inst]
      [inst : Monad n] [inst_1 : @LawfulMonad n inst] [inst_2 : MonadLiftT m n] [inst_3 : Std.Iterator α m β]
      [inst_4 : @Std.Iterators.Finite α m β inst_3] {f : β → Std.Iterators.PostconditionT n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst)) f)
          n inst γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst inst_3
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f)
          (@Std.IterM.mapWithPostcondition α β γ m n inst inst_2 inst_3 f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (x : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst)) γ (Option γ)
              (@Option.some γ) (f x))
          n inst γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst)) γ (Option γ)
                (@Option.some γ) (f x))
            inst_3 inst)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_2 inst_3
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst)) γ (Option γ)
                (@Option.some γ) (f x))
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition 10)

-- `Std.IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition` idx 12: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition.h12.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : @LawfulMonad n inst_2] [inst_4 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_4] [inst : Std.Iterator α m β]
      {f : β → Std.Iterators.PostconditionT n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) f)
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) f)
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_4 inst f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (x : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
              (@Option.some γ) (f x))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
                (@Option.some γ) (f x))
            inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_4 inst
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
                (@Option.some γ) (f x))
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_mapWithPostcondition_eq_toList_filterMapWithPostcondition 12)

-- `Std.IterM.toListRev_mapWithPostcondition_eq_toListRev_filterMapWithPostcondition` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_mapWithPostcondition_eq_toListRev_filterMapWithPostcondition.h6.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : Monad n]
      [inst_2 : @LawfulMonad n inst_1] [inst_3 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_1 inst_3]
      [inst : Std.Iterator α m β] [inst_4 : @Std.Iterators.Finite α m β inst] {f : β → Std.Iterators.PostconditionT n γ}
      {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) f)
          n inst_1 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_1 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) f)
          (@Std.IterM.mapWithPostcondition α β γ m n inst_1 inst_3 inst f it))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) fun (x : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) γ (Option γ)
              (@Option.some γ) (f x))
          n inst_1 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) γ (Option γ)
                (@Option.some γ) (f x))
            inst inst_1)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_3 inst
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) γ (Option γ)
                (@Option.some γ) (f x))
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_mapWithPostcondition_eq_toListRev_filterMapWithPostcondition 6)

-- `Std.IterM.toListRev_mapWithPostcondition_eq_toListRev_filterMapWithPostcondition` idx 8: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_mapWithPostcondition_eq_toListRev_filterMapWithPostcondition.h8.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_2 inst_3]
      [inst : Std.Iterator α m β] [inst_4 : @Std.Iterators.Finite α m β inst] {f : β → Std.Iterators.PostconditionT n γ}
      {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) f)
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) f)
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_3 inst f it))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) fun (x : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
              (@Option.some γ) (f x))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
                (@Option.some γ) (f x))
            inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_3 inst
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
                (@Option.some γ) (f x))
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_mapWithPostcondition_eq_toListRev_filterMapWithPostcondition 8)

-- `Std.IterM.toListRev_mapWithPostcondition_eq_toListRev_filterMapWithPostcondition` idx 10: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_mapWithPostcondition_eq_toListRev_filterMapWithPostcondition.h10.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst : @LawfulMonad m inst]
      [inst : Monad n] [inst_1 : @LawfulMonad n inst] [inst_2 : MonadLiftT m n] [inst_3 : Std.Iterator α m β]
      [inst_4 : @Std.Iterators.Finite α m β inst_3] {f : β → Std.Iterators.PostconditionT n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst)) f)
          n inst γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst inst_3
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f)
          (@Std.IterM.mapWithPostcondition α β γ m n inst inst_2 inst_3 f it))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (x : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst)) γ (Option γ)
              (@Option.some γ) (f x))
          n inst γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst)) γ (Option γ)
                (@Option.some γ) (f x))
            inst_3 inst)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_2 inst_3
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst)) γ (Option γ)
                (@Option.some γ) (f x))
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_mapWithPostcondition_eq_toListRev_filterMapWithPostcondition 10)

-- `Std.IterM.toListRev_mapWithPostcondition_eq_toListRev_filterMapWithPostcondition` idx 12: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_mapWithPostcondition_eq_toListRev_filterMapWithPostcondition.h12.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : @LawfulMonad n inst_2] [inst_4 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_4] [inst : Std.Iterator α m β]
      {f : β → Std.Iterators.PostconditionT n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) f)
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) f)
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_4 inst f it))
        (@Std.IterM.toListRev
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (x : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
              (@Option.some γ) (f x))
          n inst_2 γ
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
                (@Option.some γ) (f x))
            inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_4 inst
            (fun (x : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) γ (Option γ)
                (@Option.some γ) (f x))
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_mapWithPostcondition_eq_toListRev_filterMapWithPostcondition 12)

-- `Std.Iter.any_filterMapM` idx 11: unused in the library's proof
theorem HypCheckProof.Std.Iter.any_filterMapM.h11.{w, w'} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      [inst_2 : @Std.IteratorLoop α Id β inst m] [inst_3 : Monad m] [inst_4 : MonadAttach m]
      [inst_5 : @LawfulMonad m inst_3] [inst_6 : @WeaklyLawfulMonadAttach m inst_3 inst_4] {it : @Std.Iter α β}
      {f : β → m (Option β')} {p : β' → Bool},
      @Eq (m (ULift Bool))
        (@Std.IterM.any
          (@Std.Iterators.Types.FilterMap α β β' Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') m inst_4 (f b))
          β' m inst_3
          (@Std.Iterators.Types.FilterMap.instIterator α β β' Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') m inst_4 (f b)) inst inst_3)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β' Id m m inst_3 inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') m inst_4 (f b))
          p (@Std.Iter.filterMapM α β β' inst m inst_3 inst_4 f it))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.Map α β β Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          β m inst_3
          (@Std.Iterators.Types.Map.instIterator α β β Id m inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β Id m m inst_3 inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          (fun (x : β) =>
            @Bind.bind m (@Monad.toBind m inst_3) (Option β') (ULift Bool) (f x) fun (__do_lift : Option β') =>
              @Std.Iter.forIn_filterMapWithPostcondition.match_1 β' (fun (__do_lift : Option β') => m (ULift Bool))
                __do_lift
                (fun (fx : β') =>
                  @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) (ULift Bool) (@ULift.up Bool (p fx)))
                fun (_ : Unit) =>
                @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) (ULift Bool)
                  (@ULift.up Bool Bool.false))
          (@Std.Iter.mapM α β β inst m inst_3 inst_4
            (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.Iter.any_filterMapM 11)

-- `Std.Iter.all_filterMapM` idx 11: unused in the library's proof
theorem HypCheckProof.Std.Iter.all_filterMapM.h11.{w, w'} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      [inst_2 : @Std.IteratorLoop α Id β inst m] [inst_3 : Monad m] [inst_4 : MonadAttach m]
      [inst_5 : @LawfulMonad m inst_3] [inst_6 : @WeaklyLawfulMonadAttach m inst_3 inst_4] {it : @Std.Iter α β}
      {f : β → m (Option β')} {p : β' → Bool},
      @Eq (m (ULift Bool))
        (@Std.IterM.all
          (@Std.Iterators.Types.FilterMap α β β' Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') m inst_4 (f b))
          β' m inst_3
          (@Std.Iterators.Types.FilterMap.instIterator α β β' Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') m inst_4 (f b)) inst inst_3)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β' Id m m inst_3 inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') m inst_4 (f b))
          p (@Std.Iter.filterMapM α β β' inst m inst_3 inst_4 f it))
        (@Std.IterM.allM
          (@Std.Iterators.Types.Map α β β Id m
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            (@Applicative.toFunctor m (@Monad.toApplicative m inst_3)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          β m inst_3
          (@Std.Iterators.Types.Map.instIterator α β β Id m inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β Id m m inst_3 inst_3 inst
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift Id m
                (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_3))) x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β m inst_4
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β b))
          (fun (x : β) =>
            @Bind.bind m (@Monad.toBind m inst_3) (Option β') (ULift Bool) (f x) fun (__do_lift : Option β') =>
              @Std.Iter.forIn_filterMapWithPostcondition.match_1 β' (fun (__do_lift : Option β') => m (ULift Bool))
                __do_lift
                (fun (fx : β') =>
                  @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) (ULift Bool) (@ULift.up Bool (p fx)))
                fun (_ : Unit) =>
                @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) (ULift Bool)
                  (@ULift.up Bool Bool.true))
          (@Std.Iter.mapM α β β inst m inst_3 inst_4
            (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_3)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.Iter.all_filterMapM 11)

-- `Std.Roo.mem_succ_succ_iff` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Roo.mem_succ_succ_iff.h7.{u} :
    ∀ {α : Type u} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LinearlyUpwardEnumerable α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLT α]
      [inst_5 : Std.PRange.InfinitelyUpwardEnumerable α] [inst_6 : Std.PRange.LawfulUpwardEnumerable α] {lo hi a : α},
      a ∈ Std.PRange.UpwardEnumerable.succ lo<...Std.PRange.UpwardEnumerable.succ hi ↔
        ∃ (a' : α), a = Std.PRange.UpwardEnumerable.succ a' ∧ a' ∈ lo<...hi :=
  no_implicit_lambda% (drop_unused% Std.Roo.mem_succ_succ_iff 7)

-- `Std.Rci.mem_succ_iff` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Rci.mem_succ_iff.h6.{u} :
    ∀ {α : Type u} [inst : LE α] [inst_1 : Std.PRange.UpwardEnumerable α] [inst_2 : Std.PRange.LinearlyUpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLE α] [inst_4 : Std.PRange.InfinitelyUpwardEnumerable α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α] {lo a : α},
      a ∈ Std.PRange.UpwardEnumerable.succ lo...* ↔ ∃ (a' : α), a = Std.PRange.UpwardEnumerable.succ a' ∧ a' ∈ lo...* :=
  no_implicit_lambda% (drop_unused% Std.Rci.mem_succ_iff 6)

-- `Std.Rco.size_eq_ite_roo` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Rco.size_eq_ite_roo.h6.{u} :
    ∀ {α : Type u} {r : Std.Rco α} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLT α] [inst_5 : Std.Rxo.IsAlwaysFinite α]
      [inst_6 : Std.Rxo.LawfulHasSize α], r.size = if r.lower < r.upper then (r.lower<...r.upper).size + 1 else 0 :=
  no_implicit_lambda% (drop_unused% Std.Rco.size_eq_ite_roo 6)

-- `Std.Rco.size_eq_ite_roo` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Rco.size_eq_ite_roo.h7.{u} :
    ∀ {α : Type u} {r : Std.Rco α} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] [inst_5 : Std.Rxo.IsAlwaysFinite α]
      [inst_6 : Std.Rxo.LawfulHasSize α], r.size = if r.lower < r.upper then (r.lower<...r.upper).size + 1 else 0 :=
  no_implicit_lambda% (drop_unused% Std.Rco.size_eq_ite_roo 7)

-- `Std.Rco.size_eq_ite_roo` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Rco.size_eq_ite_roo.h8.{u} :
    ∀ {α : Type u} {r : Std.Rco α} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerableLT α] [inst_6 : Std.Rxo.LawfulHasSize α],
      r.size = if r.lower < r.upper then (r.lower<...r.upper).size + 1 else 0 :=
  no_implicit_lambda% (drop_unused% Std.Rco.size_eq_ite_roo 8)

-- `Std.Rcc.size_eq_ite_roc` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Rcc.size_eq_ite_roc.h6.{u} :
    ∀ {α : Type u} {r : Std.Rcc α} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLE α] [inst_5 : Std.Rxc.IsAlwaysFinite α]
      [inst_6 : Std.Rxc.LawfulHasSize α], r.size = if r.lower ≤ r.upper then (r.lower<...=r.upper).size + 1 else 0 :=
  no_implicit_lambda% (drop_unused% Std.Rcc.size_eq_ite_roc 6)

-- `Std.Rcc.size_eq_ite_roc` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Rcc.size_eq_ite_roc.h7.{u} :
    ∀ {α : Type u} {r : Std.Rcc α} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] [inst_5 : Std.Rxc.IsAlwaysFinite α]
      [inst_6 : Std.Rxc.LawfulHasSize α], r.size = if r.lower ≤ r.upper then (r.lower<...=r.upper).size + 1 else 0 :=
  no_implicit_lambda% (drop_unused% Std.Rcc.size_eq_ite_roc 7)

-- `Std.Rcc.size_eq_ite_roc` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Rcc.size_eq_ite_roc.h8.{u} :
    ∀ {α : Type u} {r : Std.Rcc α} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerableLE α] [inst_6 : Std.Rxc.LawfulHasSize α],
      r.size = if r.lower ≤ r.upper then (r.lower<...=r.upper).size + 1 else 0 :=
  no_implicit_lambda% (drop_unused% Std.Rcc.size_eq_ite_roc 8)

-- `Std.Roo.size_eq_match_rcc` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Roo.size_eq_match_rcc.h6.{u} :
    ∀ {α : Type u} {r : Std.Roo α} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLT α] [inst_5 : Std.Rxo.IsAlwaysFinite α]
      [inst : Std.Rxo.LawfulHasSize α],
      r.size =
        match Std.PRange.UpwardEnumerable.succ? r.lower with
        | Option.none => 0
        | Option.some next => (next...r.upper).size :=
  no_implicit_lambda% (drop_unused% Std.Roo.size_eq_match_rcc 6)

-- `Std.Roo.size_eq_match_rcc` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Roo.size_eq_match_rcc.h7.{u} :
    ∀ {α : Type u} {r : Std.Roo α} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] [inst_5 : Std.Rxo.IsAlwaysFinite α]
      [inst : Std.Rxo.LawfulHasSize α],
      r.size =
        match Std.PRange.UpwardEnumerable.succ? r.lower with
        | Option.none => 0
        | Option.some next => (next...r.upper).size :=
  no_implicit_lambda% (drop_unused% Std.Roo.size_eq_match_rcc 7)

-- `Std.Roo.size_eq_match_rcc` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Roo.size_eq_match_rcc.h8.{u} :
    ∀ {α : Type u} {r : Std.Roo α} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerableLT α] [inst : Std.Rxo.LawfulHasSize α],
      r.size =
        match Std.PRange.UpwardEnumerable.succ? r.lower with
        | Option.none => 0
        | Option.some next => (next...r.upper).size :=
  no_implicit_lambda% (drop_unused% Std.Roo.size_eq_match_rcc 8)

-- `Std.Roo.size_eq_match_rcc` idx 9: unused in the library's proof
theorem HypCheckProof.Std.Roo.size_eq_match_rcc.h9.{u} :
    ∀ {α : Type u} {r : Std.Roo α} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerableLT α] [inst : Std.Rxo.IsAlwaysFinite α],
      r.size =
        match Std.PRange.UpwardEnumerable.succ? r.lower with
        | Option.none => 0
        | Option.some next => (next...r.upper).size :=
  no_implicit_lambda% (drop_unused% Std.Roo.size_eq_match_rcc 9)

-- `Std.toList_roc_eq_toList_rcc_of_isSome_succ?` idx 5: unused in the library's proof
theorem HypCheckProof.Std.toList_roc_eq_toList_rcc_of_isSome_succ?.h5.{u} :
    ∀ {α : Type u} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerable α] [inst_4 : Std.Rxc.IsAlwaysFinite α] {lo hi : α}
      (h : (Std.PRange.UpwardEnumerable.succ? lo).isSome = Bool.true),
      (lo<...=hi).toList = ((Std.PRange.UpwardEnumerable.succ? lo).get h...=hi).toList :=
  no_implicit_lambda% (drop_unused% Std.toList_roc_eq_toList_rcc_of_isSome_succ? 5)

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMapM` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMapM.h7.{w, w'} :
    ∀ {α β α₂ γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : MonadAttach m] [inst_2 : Std.Iterator α m β]
      [inst_3 : Std.Iterator α₂ m γ] {f : β → m (@Std.IterM α₂ m γ)} {it₁ : @Std.IterM α m β}
      {it₂ it₂' : @Std.IterM α₂ m γ},
      @Std.IterM.IsPlausibleStep α₂ m γ inst_3 it₂ (@Std.IterStep.skip (@Std.IterM α₂ m γ) γ it₂') →
        @Std.IterM.IsPlausibleStep
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            α₂ γ m)
          m γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_2
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            inst_3)
          (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_2 inst_3 f it₁ (@Option.some (@Std.IterM α₂ m γ) it₂))
          (@Std.IterStep.skip
            (@Std.IterM
              (Std.Iterators.Types.Flatten
                (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                  (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                  @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                α₂ γ m)
              m γ)
            γ (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_2 inst_3 f it₁ (@Option.some (@Std.IterM α₂ m γ) it₂'))) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMapM 7)

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMap` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMap.h6.{w, w'} :
    ∀ {α β α₂ γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : Std.Iterator α m β]
      [inst_2 : Std.Iterator α₂ m γ] {f : β → @Std.IterM α₂ m γ} {it₁ : @Std.IterM α m β} {it₂ it₂' : @Std.IterM α₂ m γ}
      {b : γ},
      @Std.IterM.IsPlausibleStep α₂ m γ inst_2 it₂ (@Std.IterStep.yield (@Std.IterM α₂ m γ) γ it₂' b) →
        @Std.IterM.IsPlausibleStep
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m)
          m γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_1
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            inst_2)
          (@Std.IterM.flatMapAfter α β α₂ γ m inst inst_1 inst_2 f it₁ (@Option.some (@Std.IterM α₂ m γ) it₂))
          (@Std.IterStep.yield
            (@Std.IterM
              (Std.Iterators.Types.Flatten
                (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                  (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                  @Pure.pure (Std.Iterators.PostconditionT m)
                    (@Applicative.toPure (Std.Iterators.PostconditionT m)
                      (@Monad.toApplicative (Std.Iterators.PostconditionT m)
                        (@Std.Iterators.instMonadPostconditionT m inst)))
                    (@Std.IterM α₂ m γ) (f b))
                α₂ γ m)
              m γ)
            γ (@Std.IterM.flatMapAfter α β α₂ γ m inst inst_1 inst_2 f it₁ (@Option.some (@Std.IterM α₂ m γ) it₂')) b) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMap 6)

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMap` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMap.h6.{w, w'} :
    ∀ {α β α₂ γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : Std.Iterator α m β]
      [inst_2 : Std.Iterator α₂ m γ] {f : β → @Std.IterM α₂ m γ} {it₁ : @Std.IterM α m β} {it₂ : @Std.IterM α₂ m γ},
      @Std.IterM.IsPlausibleStep α₂ m γ inst_2 it₂ (@Std.IterStep.done (@Std.IterM α₂ m γ) γ) →
        @Std.IterM.IsPlausibleStep
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m)
          m γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_1
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            inst_2)
          (@Std.IterM.flatMapAfter α β α₂ γ m inst inst_1 inst_2 f it₁ (@Option.some (@Std.IterM α₂ m γ) it₂))
          (@Std.IterStep.skip
            (@Std.IterM
              (Std.Iterators.Types.Flatten
                (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                  (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                  @Pure.pure (Std.Iterators.PostconditionT m)
                    (@Applicative.toPure (Std.Iterators.PostconditionT m)
                      (@Monad.toApplicative (Std.Iterators.PostconditionT m)
                        (@Std.Iterators.instMonadPostconditionT m inst)))
                    (@Std.IterM α₂ m γ) (f b))
                α₂ γ m)
              m γ)
            γ (@Std.IterM.flatMapAfter α β α₂ γ m inst inst_1 inst_2 f it₁ (@Option.none (@Std.IterM α₂ m γ)))) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMap 6)

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMap` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMap.h6.{w, w'} :
    ∀ {α β α₂ γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : Std.Iterator α m β]
      [inst_2 : Std.Iterator α₂ m γ] {f : β → @Std.IterM α₂ m γ} {it₁ it₁' : @Std.IterM α m β},
      @Std.IterM.IsPlausibleStep α m β inst_1 it₁ (@Std.IterStep.skip (@Std.IterM α m β) β it₁') →
        @Std.IterM.IsPlausibleStep
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m)
          m γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_1
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            inst_2)
          (@Std.IterM.flatMapAfter α β α₂ γ m inst inst_1 inst_2 f it₁ (@Option.none (@Std.IterM α₂ m γ)))
          (@Std.IterStep.skip
            (@Std.IterM
              (Std.Iterators.Types.Flatten
                (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                  (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                  @Pure.pure (Std.Iterators.PostconditionT m)
                    (@Applicative.toPure (Std.Iterators.PostconditionT m)
                      (@Monad.toApplicative (Std.Iterators.PostconditionT m)
                        (@Std.Iterators.instMonadPostconditionT m inst)))
                    (@Std.IterM α₂ m γ) (f b))
                α₂ γ m)
              m γ)
            γ (@Std.IterM.flatMapAfter α β α₂ γ m inst inst_1 inst_2 f it₁' (@Option.none (@Std.IterM α₂ m γ)))) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMap 6)

-- `Std.Iter.forIn'_eq_forIn'_toIterM` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Iter.forIn'_eq_forIn'_toIterM.h3.{w, w''} :
    ∀ {α β : Type w} [inst : Std.Iterator α Id β] {m : Type w → Type w''} [inst_1 : Monad m]
      [inst_2 : @LawfulMonad m inst_1] [inst_3 : @Std.IteratorLoop α Id β inst m] {γ : Type w} {it : @Std.Iter α β}
      {init : γ}
      {f :
        (out : β) →
          @Membership.mem β (@Std.Iter α β)
              (@Membership.mk β (@Std.Iter α β) fun (it : @Std.Iter α β) (out : β) =>
                @Std.Iter.IsPlausibleIndirectOutput α β inst it out)
              it out →
            γ → m (ForInStep γ)},
      @Eq (m γ)
        (@ForIn'.forIn' m (@Std.Iter α β) β
          (@Membership.mk β (@Std.Iter α β) fun (it : @Std.Iter α β) (out : β) =>
            @Std.Iter.IsPlausibleIndirectOutput α β inst it out)
          (@Std.Iter.instForIn' α β m inst_1 inst inst_3) γ it init f)
        (@ForIn'.forIn' m (@Std.IterM α Id β) β
          (@Membership.mk β (@Std.IterM α Id β) fun (it : @Std.IterM α Id β) (out : β) =>
            @Std.IterM.IsPlausibleIndirectOutput α β Id inst it out)
          (@Std.IterM.instForIn' Id m α β inst inst_3 inst_1
            (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst_1))))
          γ (@Std.Iter.toIterM α β it) init
          fun (out : β)
            (h :
              @Membership.mem β (@Std.IterM α Id β)
                (@Membership.mk β (@Std.IterM α Id β) fun (it : @Std.IterM α Id β) (out : β) =>
                  @Std.IterM.IsPlausibleIndirectOutput α β Id inst it out)
                (@Std.Iter.toIterM α β it) out)
            (acc : γ) =>
          f out
            (@Iff.mpr (@Std.Iter.IsPlausibleIndirectOutput α β inst it out)
              (@Std.IterM.IsPlausibleIndirectOutput α β Id inst (@Std.Iter.toIterM α β it) out)
              (@Std.Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM α β inst it out) h)
            acc) :=
  no_implicit_lambda% (drop_unused% Std.Iter.forIn'_eq_forIn'_toIterM 3)

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMap` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMap.h6.{w, w'} :
    ∀ {α β α₂ γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : Std.Iterator α m β]
      [inst_2 : Std.Iterator α₂ m γ] {f : β → @Std.IterM α₂ m γ} {it₁ : @Std.IterM α m β},
      @Std.IterM.IsPlausibleStep α m β inst_1 it₁ (@Std.IterStep.done (@Std.IterM α m β) β) →
        @Std.IterM.IsPlausibleStep
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m)
          m γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_1
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            inst_2)
          (@Std.IterM.flatMapAfter α β α₂ γ m inst inst_1 inst_2 f it₁ (@Option.none (@Std.IterM α₂ m γ)))
          (@Std.IterStep.done
            (@Std.IterM
              (Std.Iterators.Types.Flatten
                (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                  (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                  @Pure.pure (Std.Iterators.PostconditionT m)
                    (@Applicative.toPure (Std.Iterators.PostconditionT m)
                      (@Monad.toApplicative (Std.Iterators.PostconditionT m)
                        (@Std.Iterators.instMonadPostconditionT m inst)))
                    (@Std.IterM α₂ m γ) (f b))
                α₂ γ m)
              m γ)
            γ) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMap 6)

-- `Std.Rii.getElem?_toList_eq` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Rii.getElem?_toList_eq.h5.{u} :
    ∀ {α : Type u} {r : Std.Rii α} [inst : Std.PRange.Least? α] [inst_1 : Std.PRange.UpwardEnumerable α]
      [inst_2 : Std.PRange.LawfulUpwardEnumerable α] [inst_3 : Std.Rxi.IsAlwaysFinite α] {i : Nat},
      r.toList[i]? = Std.PRange.Least?.least?.bind (Std.PRange.UpwardEnumerable.succMany? i) :=
  no_implicit_lambda% (drop_unused% Std.Rii.getElem?_toList_eq 5)

-- `Std.Rxo.Iterator.toList_eq_match` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Rxo.Iterator.toList_eq_match.h6.{u} :
    ∀ {α : Type u} [inst : LT α] [inst_1 : @DecidableLT α inst] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : @Std.Rxo.IsAlwaysFinite α inst_2 inst] [inst_4 : @Std.PRange.LawfulUpwardEnumerable α inst_2]
      {it : @Std.Iter (Std.Rxo.Iterator α) α},
      @Eq (List α)
        (@Std.Iter.toList (Std.Rxo.Iterator α) α
          (@Std.Rxo.instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT α inst_2 inst inst_1) it)
        (@Std.Rxc.Iterator.toList_eq_match.match_1 α (fun (x : Option α) => List α)
          (@Std.Rxo.Iterator.next α (@Std.Iter.internalState (Std.Rxo.Iterator α) α it)) (fun (_ : Unit) => @List.nil α)
          fun (a : α) =>
          @ite (List α)
            (@LT.lt α inst a (@Std.Rxo.Iterator.upperBound α (@Std.Iter.internalState (Std.Rxo.Iterator α) α it)))
            (inst_1 a (@Std.Rxo.Iterator.upperBound α (@Std.Iter.internalState (Std.Rxo.Iterator α) α it)))
            (@List.cons α a
              (@Std.Iter.toList (Std.Rxo.Iterator α) α
                (@Std.Rxo.instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT α inst_2 inst inst_1)
                (@Std.Iter.mk (Std.Rxo.Iterator α) α
                  (@Std.Rxo.Iterator.mk α (@Std.PRange.UpwardEnumerable.succ? α inst_2 a)
                    (@Std.Rxo.Iterator.upperBound α (@Std.Iter.internalState (Std.Rxo.Iterator α) α it))))))
            (@List.nil α)) :=
  no_implicit_lambda% (drop_unused% Std.Rxo.Iterator.toList_eq_match 6)

-- `Std.IterM.any_mapM` idx 15: unused in the library's proof
theorem HypCheckProof.Std.IterM.any_mapM.h15.{w, w', w''} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : @Std.IteratorLoop α m β inst m]
      [inst_4 : Monad m] [inst_5 : @LawfulMonad m inst_4] [inst_6 : Monad n] [inst_7 : MonadAttach n]
      [inst_8 : @LawfulMonad n inst_6] [inst_9 : @WeaklyLawfulMonadAttach n inst_6 inst_7]
      [inst_10 : @Std.LawfulIteratorLoop β α m m inst_4 inst_4 inst inst_3] {it : @Std.IterM α m β} {f : β → n β'}
      {p : β' → Bool},
      @Eq (n (ULift Bool))
        (@Std.IterM.any
          (@Std.Iterators.Types.Map α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_7 (f b))
          β' n inst_6
          (@Std.Iterators.Types.Map.instIterator α β β' m n inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_7 (f b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β' m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_7 (f b))
          p (@Std.IterM.mapM α β β' m n inst inst_6 inst_7 inst_2 f it))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          β n inst_6
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (fun (x : β) =>
            @Functor.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) β' (ULift Bool)
              (fun (x : β') => @ULift.up Bool (p x)) (f x))
          (@Std.IterM.mapM α β β m n inst inst_6 inst_7 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.any_mapM 15)

-- `Std.IterM.any_mapM` idx 16: unused in the library's proof
theorem HypCheckProof.Std.IterM.any_mapM.h16.{w, w', w''} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : @Std.IteratorLoop α m β inst m]
      [inst_4 : Monad m] [inst_5 : @LawfulMonad m inst_4] [inst_6 : Monad n] [inst_7 : MonadAttach n]
      [inst_8 : @LawfulMonad n inst_6] [inst_9 : @WeaklyLawfulMonadAttach n inst_6 inst_7]
      [inst_10 : @LawfulMonadLiftT m n inst_4 inst_6 inst_2] {it : @Std.IterM α m β} {f : β → n β'} {p : β' → Bool},
      @Eq (n (ULift Bool))
        (@Std.IterM.any
          (@Std.Iterators.Types.Map α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_7 (f b))
          β' n inst_6
          (@Std.Iterators.Types.Map.instIterator α β β' m n inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_7 (f b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β' m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_7 (f b))
          p (@Std.IterM.mapM α β β' m n inst inst_6 inst_7 inst_2 f it))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          β n inst_6
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (fun (x : β) =>
            @Functor.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) β' (ULift Bool)
              (fun (x : β') => @ULift.up Bool (p x)) (f x))
          (@Std.IterM.mapM α β β m n inst inst_6 inst_7 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.any_mapM 16)

-- `Std.IterM.any_filterM` idx 14: unused in the library's proof
theorem HypCheckProof.Std.IterM.any_filterM.h14.{w, w', w''} :
    ∀ {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : @Std.IteratorLoop α m β inst m]
      [inst_4 : Monad m] [inst_5 : @LawfulMonad m inst_4] [inst_6 : Monad n] [inst_7 : MonadAttach n]
      [inst_8 : @LawfulMonad n inst_6] [inst_9 : @WeaklyLawfulMonadAttach n inst_6 inst_7]
      [inst_10 : @Std.LawfulIteratorLoop β α m m inst_4 inst_4 inst inst_3] {it : @Std.IterM α m β} {f : β → n (ULift Bool)}
      {p : β → Bool},
      @Eq (n (ULift Bool))
        (@Std.IterM.any
          (@Std.Iterators.Types.FilterMap α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_7 (f b)))
          β n inst_6
          (@Std.Iterators.Types.FilterMap.instIterator α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (fun (b : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) (ULift Bool)
                (Option β)
                (fun (x : ULift Bool) =>
                  @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                    (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_7 (f b)))
            inst inst_6)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_7 (f b)))
          p (@Std.IterM.filterM α β m n inst inst_6 inst_7 inst_2 f it))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          β n inst_6
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (fun (x : β) =>
            @Bind.bind n (@Monad.toBind n inst_6) (ULift Bool) (ULift Bool) (f x) fun (__do_lift : ULift Bool) =>
              @ite (n (ULift Bool)) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
                (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true)
                (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) (ULift Bool) (@ULift.up Bool (p x)))
                (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) (ULift Bool)
                  (@ULift.up Bool Bool.false)))
          (@Std.IterM.mapM α β β m n inst inst_6 inst_7 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.any_filterM 14)

-- `Std.IterM.any_filterM` idx 15: unused in the library's proof
theorem HypCheckProof.Std.IterM.any_filterM.h15.{w, w', w''} :
    ∀ {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : @Std.IteratorLoop α m β inst m]
      [inst_4 : Monad m] [inst_5 : @LawfulMonad m inst_4] [inst_6 : Monad n] [inst_7 : MonadAttach n]
      [inst_8 : @LawfulMonad n inst_6] [inst_9 : @WeaklyLawfulMonadAttach n inst_6 inst_7]
      [inst_10 : @LawfulMonadLiftT m n inst_4 inst_6 inst_2] {it : @Std.IterM α m β} {f : β → n (ULift Bool)}
      {p : β → Bool},
      @Eq (n (ULift Bool))
        (@Std.IterM.any
          (@Std.Iterators.Types.FilterMap α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_7 (f b)))
          β n inst_6
          (@Std.Iterators.Types.FilterMap.instIterator α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (fun (b : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) (ULift Bool)
                (Option β)
                (fun (x : ULift Bool) =>
                  @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                    (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_7 (f b)))
            inst inst_6)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_7 (f b)))
          p (@Std.IterM.filterM α β m n inst inst_6 inst_7 inst_2 f it))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_6)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          β n inst_6
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_6 inst_6 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_7
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β b))
          (fun (x : β) =>
            @Bind.bind n (@Monad.toBind n inst_6) (ULift Bool) (ULift Bool) (f x) fun (__do_lift : ULift Bool) =>
              @ite (n (ULift Bool)) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
                (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true)
                (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) (ULift Bool) (@ULift.up Bool (p x)))
                (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) (ULift Bool)
                  (@ULift.up Bool Bool.false)))
          (@Std.IterM.mapM α β β m n inst inst_6 inst_7 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_6)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.any_filterM 15)

-- `Std.IterM.toList_mapM_eq_toList_mapWithPostcondition` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_mapM_eq_toList_mapWithPostcondition.h6.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : Monad n]
      [inst_2 : MonadAttach n] [inst_3 : @LawfulMonad n inst_1] [inst_4 : @WeaklyLawfulMonadAttach n inst_1 inst_2]
      [inst_5 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_1 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b))
          n inst_1 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_1 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b))
          (@Std.IterM.mapM α β γ m n inst inst_1 inst_2 inst_5 f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_1)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b))
          n inst_1 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_1 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst_1 inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_2 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_mapM_eq_toList_mapWithPostcondition 6)

-- `Std.IterM.toList_mapM_eq_toList_mapWithPostcondition` idx 9: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_mapM_eq_toList_mapWithPostcondition.h9.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @WeaklyLawfulMonadAttach n inst_2 inst_3]
      [inst_5 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_2 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapM α β γ m n inst inst_2 inst_3 inst_5 f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_mapM_eq_toList_mapWithPostcondition 9)

-- `Std.IterM.toList_mapM_eq_toList_mapWithPostcondition` idx 10: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_mapM_eq_toList_mapWithPostcondition.h10.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @LawfulMonad n inst_2] [inst_5 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapM α β γ m n inst inst_2 inst_3 inst_5 f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_mapM_eq_toList_mapWithPostcondition 10)

-- `Std.IterM.toList_mapM_eq_toList_mapWithPostcondition` idx 12: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_mapM_eq_toList_mapWithPostcondition.h12.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst : @LawfulMonad m inst]
      [inst : Monad n] [inst_1 : MonadAttach n] [inst_2 : @LawfulMonad n inst]
      [inst_3 : @WeaklyLawfulMonadAttach n inst inst_1] [inst_4 : MonadLiftT m n] [inst_5 : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst_5] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b))
          n inst γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst inst_5
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b))
          (@Std.IterM.mapM α β γ m n inst_5 inst inst_1 inst_4 f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b))
          n inst γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst inst_5
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst inst_4 inst_5
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_1 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_mapM_eq_toList_mapWithPostcondition 12)

-- `Std.IterM.toList_mapM_eq_toList_mapWithPostcondition` idx 14: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_mapM_eq_toList_mapWithPostcondition.h14.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @LawfulMonad n inst_2]
      [inst_5 : @WeaklyLawfulMonadAttach n inst_2 inst_3] [inst_6 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_6] [inst : Std.Iterator α m β] {f : β → n γ} {it : @Std.IterM α m β},
      @Eq (n (List γ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapM α β γ m n inst inst_2 inst_3 inst_6 f it))
        (@Std.IterM.toList
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_2)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          n inst_2 γ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_2 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b))
          (@Std.IterM.mapWithPostcondition α β γ m n inst_2 inst_6 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift γ n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_mapM_eq_toList_mapWithPostcondition 14)

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM_pure` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM_pure.h8.{w, w'} :
    ∀ {α β α₂ γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : MonadAttach m] [inst_2 : @LawfulMonad m inst]
      [inst_3 : Std.Iterator α Id β] [inst_4 : Std.Iterator α₂ m γ] {f : β → m (@Std.IterM α₂ m γ)}
      {it₁ it₁' : @Std.Iter α β} {it₂' : @Std.IterM α₂ m γ} {b : β},
      @Std.Iter.IsPlausibleStep α β inst_3 it₁ (@Std.IterStep.yield (@Std.Iter α β) β it₁' b) →
        @MonadAttach.CanReturn m inst_1 (@Std.IterM α₂ m γ) (f b) it₂' →
          @Std.IterM.IsPlausibleStep
            (Std.Iterators.Types.Flatten
              (@Std.Iterators.Types.Map
                (@Std.Iterators.Types.Map α β β Id m
                  (fun ⦃x : Type w⦄ =>
                    @MonadLiftT.monadLift Id m
                      (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst))) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst))
                  (@Pure.pure (Std.Iterators.PostconditionT m)
                    (@Applicative.toPure (Std.Iterators.PostconditionT m)
                      (@Monad.toApplicative (Std.Iterators.PostconditionT m)
                        (@Std.Iterators.instMonadPostconditionT m inst)))
                    β))
                β (@Std.IterM α₂ m γ) m m (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
              α₂ γ m)
            m γ
            (@Std.Iterators.Types.Flatten.instIterator
              (@Std.Iterators.Types.Map
                (@Std.Iterators.Types.Map α β β Id m
                  (fun ⦃x : Type w⦄ =>
                    @MonadLiftT.monadLift Id m
                      (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst))) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst))
                  (@Pure.pure (Std.Iterators.PostconditionT m)
                    (@Applicative.toPure (Std.Iterators.PostconditionT m)
                      (@Monad.toApplicative (Std.Iterators.PostconditionT m)
                        (@Std.Iterators.instMonadPostconditionT m inst)))
                    β))
                β (@Std.IterM α₂ m γ) m m (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
              α₂ γ m inst
              (@Std.Iterators.Types.Map.instIterator
                (@Std.Iterators.Types.Map α β β Id m
                  (fun ⦃x : Type w⦄ =>
                    @MonadLiftT.monadLift Id m
                      (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst))) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst))
                  (@Pure.pure (Std.Iterators.PostconditionT m)
                    (@Applicative.toPure (Std.Iterators.PostconditionT m)
                      (@Monad.toApplicative (Std.Iterators.PostconditionT m)
                        (@Std.Iterators.instMonadPostconditionT m inst)))
                    β))
                β (@Std.IterM α₂ m γ) m m inst
                (@Std.Iterators.Types.Map.instIterator α β β Id m inst inst_3
                  (fun ⦃x : Type w⦄ =>
                    @MonadLiftT.monadLift Id m
                      (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst))) x)
                  (@Pure.pure (Std.Iterators.PostconditionT m)
                    (@Applicative.toPure (Std.Iterators.PostconditionT m)
                      (@Monad.toApplicative (Std.Iterators.PostconditionT m)
                        (@Std.Iterators.instMonadPostconditionT m inst)))
                    β))
                (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
              inst_4)
            (@Std.Iter.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁ (@Option.none (@Std.IterM α₂ m γ)))
            (@Std.IterStep.skip
              (@Std.IterM
                (Std.Iterators.Types.Flatten
                  (@Std.Iterators.Types.Map
                    (@Std.Iterators.Types.Map α β β Id m
                      (fun ⦃x : Type w⦄ =>
                        @MonadLiftT.monadLift Id m
                          (@Id.instMonadLiftTOfPure m (@Applicative.toPure m (@Monad.toApplicative m inst))) x)
                      (@Applicative.toFunctor m (@Monad.toApplicative m inst))
                      (@Pure.pure (Std.Iterators.PostconditionT m)
                        (@Applicative.toPure (Std.Iterators.PostconditionT m)
                          (@Monad.toApplicative (Std.Iterators.PostconditionT m)
                            (@Std.Iterators.instMonadPostconditionT m inst)))
                        β))
                    β (@Std.IterM α₂ m γ) m m (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                    (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                    @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                  α₂ γ m)
                m γ)
              γ
              (@Std.Iter.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁' (@Option.some (@Std.IterM α₂ m γ) it₂'))) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM_pure 8)

-- `Std.IterM.anyM_filterMapM` idx 9: unused in the library's proof
theorem HypCheckProof.Std.IterM.anyM_filterMapM.h9.{w, w', w''} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : Monad m] [inst_4 : Monad n]
      [inst_5 : MonadAttach n] [inst_6 : @LawfulMonad n inst_4] [inst_7 : @WeaklyLawfulMonadAttach n inst_4 inst_5]
      {it : @Std.IterM α m β} {f : β → n (Option β')} {p : β' → n (ULift Bool)},
      @Eq (n (ULift Bool))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_5 (f b))
          β' n inst_4
          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_5 (f b)) inst inst_4)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β' m n n inst_4 inst_4 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_5 (f b))
          p (@Std.IterM.filterMapM α β β' m n inst inst_4 inst_5 inst_2 f it))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_4)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_5
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_4)) β b))
          β n inst_4
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_4 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_5
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_4)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_4 inst_4 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_5
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_4)) β b))
          (fun (x : β) =>
            @Bind.bind n (@Monad.toBind n inst_4) (Option β') (ULift Bool) (f x) fun (__do_lift : Option β') =>
              @Std.IterM.forIn_filterMapWithPostcondition.match_1 β' (fun (__do_lift : Option β') => n (ULift Bool))
                __do_lift (fun (fx : β') => p fx) fun (_ : Unit) =>
                @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_4)) (ULift Bool)
                  (@ULift.up Bool Bool.false))
          (@Std.IterM.mapM α β β m n inst inst_4 inst_5 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_4)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.anyM_filterMapM 9)

-- `Std.IterM.anyM_filterM` idx 8: unused in the library's proof
theorem HypCheckProof.Std.IterM.anyM_filterM.h8.{w, w', w''} :
    ∀ {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : Monad m] [inst_4 : Monad n]
      [inst_5 : MonadAttach n] [inst_6 : @LawfulMonad n inst_4] [inst_7 : @WeaklyLawfulMonadAttach n inst_4 inst_5]
      {it : @Std.IterM α m β} {f p : β → n (ULift Bool)},
      @Eq (n (ULift Bool))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.FilterMap α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_4)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_5 (f b)))
          β n inst_4
          (@Std.Iterators.Types.FilterMap.instIterator α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (fun (b : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_4)) (ULift Bool)
                (Option β)
                (fun (x : ULift Bool) =>
                  @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                    (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_5 (f b)))
            inst inst_4)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β m n n inst_4 inst_4 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_4)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_5 (f b)))
          p (@Std.IterM.filterM α β m n inst inst_4 inst_5 inst_2 f it))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_4)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_5
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_4)) β b))
          β n inst_4
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_4 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_5
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_4)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_4 inst_4 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_5
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_4)) β b))
          (fun (x : β) =>
            @Bind.bind n (@Monad.toBind n inst_4) (ULift Bool) (ULift Bool) (f x) fun (__do_lift : ULift Bool) =>
              @ite (n (ULift Bool)) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
                (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true) (p x)
                (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_4)) (ULift Bool)
                  (@ULift.up Bool Bool.false)))
          (@Std.IterM.mapM α β β m n inst inst_4 inst_5 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_4)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.anyM_filterM 8)

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM.h7.{w, w'} :
    ∀ {α β α₂ γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : MonadAttach m] [inst_2 : Std.Iterator α m β]
      [inst_3 : Std.Iterator α₂ m γ] {f : β → m (@Std.IterM α₂ m γ)} {it₁ it₁' : @Std.IterM α m β}
      {it₂' : @Std.IterM α₂ m γ} {b : β},
      @Std.IterM.IsPlausibleStep α m β inst_2 it₁ (@Std.IterStep.yield (@Std.IterM α m β) β it₁' b) →
        @MonadAttach.CanReturn m inst_1 (@Std.IterM α₂ m γ) (f b) it₂' →
          @Std.IterM.IsPlausibleStep
            (Std.Iterators.Types.Flatten
              (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
              α₂ γ m)
            m γ
            (@Std.Iterators.Types.Flatten.instIterator
              (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
              α₂ γ m inst
              (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_2
                (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
              inst_3)
            (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_2 inst_3 f it₁ (@Option.none (@Std.IterM α₂ m γ)))
            (@Std.IterStep.skip
              (@Std.IterM
                (Std.Iterators.Types.Flatten
                  (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                    (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                    (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                    @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                  α₂ γ m)
                m γ)
              γ
              (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_2 inst_3 f it₁'
                (@Option.some (@Std.IterM α₂ m γ) it₂'))) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM 7)

-- `Lean.Grind.CommRing.lt_false_of_toPoly_eq` idx 5: unused in the library's proof
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPoly_eq.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
      (ctx : Lean.Grind.CommRing.Context α) (bal₁ bal₂ : Bool) (lhs rhs : Lean.Grind.CommRing.Expr)
      (p : Lean.Grind.CommRing.Poly),
      p = Lean.Grind.CommRing.Expr.toPolyX_k bal₁ lhs →
        p = Lean.Grind.CommRing.Expr.toPolyX_k bal₂ rhs →
          (Lean.Grind.CommRing.Expr.denote ctx lhs < Lean.Grind.CommRing.Expr.denote ctx rhs) = False :=
  no_implicit_lambda% (drop_unused% Lean.Grind.CommRing.lt_false_of_toPoly_eq 5)

-- `Std.Iter.toArray_flatMap` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iter.toArray_flatMap.h6.{w} :
    ∀ {α α₂ β γ : Type w} [inst : Std.Iterator α Id β] [inst : Std.Iterator α₂ Id γ]
      [inst : @Std.Iterators.Finite α₂ Id γ inst] [inst : Std.Iterator α Id β] [inst_1 : Std.Iterator α₂ Id γ]
      [inst_2 : @Std.Iterators.Finite α Id β inst] [inst_3 : @Std.Iterators.Finite α₂ Id γ inst_1] {f : β → @Std.Iter α₂ γ}
      {it₁ : @Std.Iter α β},
      @Eq (Array γ)
        (@Std.Iter.toArray
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ Id γ) Id Id
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x)
              (@Applicative.toFunctor Id (@Monad.toApplicative Id Id.instMonad)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (@Std.IterM α₂ Id γ) (@Std.Iter.toIterM α₂ γ (f b)))
            α₂ γ Id)
          γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ Id γ) Id Id
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x)
              (@Applicative.toFunctor Id (@Monad.toApplicative Id Id.instMonad)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (@Std.IterM α₂ Id γ) (@Std.Iter.toIterM α₂ γ (f b)))
            α₂ γ Id Id.instMonad
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ Id γ) Id Id Id.instMonad inst
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (@Std.IterM α₂ Id γ) (@Std.Iter.toIterM α₂ γ (f b)))
            inst_1)
          (@Std.Iter.flatMap α β α₂ γ inst inst_1 f it₁))
        (@Array.flatten γ
          (@Std.Iter.toArray
            (@Std.Iterators.Types.Map α β (Array γ) Id Id
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x)
              (@Applicative.toFunctor Id (@Monad.toApplicative Id Id.instMonad)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (Array γ) (@Std.Iter.toArray α₂ γ inst_1 (f b)))
            (Array γ)
            (@Std.Iterators.Types.Map.instIterator α β (Array γ) Id Id Id.instMonad inst
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (Array γ) (@Std.Iter.toArray α₂ γ inst_1 (f b)))
            (@Std.Iter.map α β (Array γ) inst (fun (b : β) => @Std.Iter.toArray α₂ γ inst_1 (f b)) it₁))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.toArray_flatMap 6)

-- `Std.Iter.toArray_flatMap` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Iter.toArray_flatMap.h7.{w} :
    ∀ {α α₂ β γ : Type w} [inst : Std.Iterator α Id β] [inst_1 : Std.Iterator α₂ Id γ]
      [inst : @Std.Iterators.Finite α Id β inst] [inst : Std.Iterator α Id β] [inst_2 : Std.Iterator α₂ Id γ]
      [inst_3 : @Std.Iterators.Finite α Id β inst] [inst_4 : @Std.Iterators.Finite α₂ Id γ inst_2] {f : β → @Std.Iter α₂ γ}
      {it₁ : @Std.Iter α β},
      @Eq (Array γ)
        (@Std.Iter.toArray
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ Id γ) Id Id
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x)
              (@Applicative.toFunctor Id (@Monad.toApplicative Id Id.instMonad)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (@Std.IterM α₂ Id γ) (@Std.Iter.toIterM α₂ γ (f b)))
            α₂ γ Id)
          γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ Id γ) Id Id
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x)
              (@Applicative.toFunctor Id (@Monad.toApplicative Id Id.instMonad)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (@Std.IterM α₂ Id γ) (@Std.Iter.toIterM α₂ γ (f b)))
            α₂ γ Id Id.instMonad
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ Id γ) Id Id Id.instMonad inst
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (@Std.IterM α₂ Id γ) (@Std.Iter.toIterM α₂ γ (f b)))
            inst_2)
          (@Std.Iter.flatMap α β α₂ γ inst inst_2 f it₁))
        (@Array.flatten γ
          (@Std.Iter.toArray
            (@Std.Iterators.Types.Map α β (Array γ) Id Id
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x)
              (@Applicative.toFunctor Id (@Monad.toApplicative Id Id.instMonad)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (Array γ) (@Std.Iter.toArray α₂ γ inst_2 (f b)))
            (Array γ)
            (@Std.Iterators.Types.Map.instIterator α β (Array γ) Id Id Id.instMonad inst
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift Id Id (instMonadLiftT Id) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT Id)
                (@Applicative.toPure (Std.Iterators.PostconditionT Id)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT Id)
                    (@Std.Iterators.instMonadPostconditionT Id Id.instMonad)))
                (Array γ) (@Std.Iter.toArray α₂ γ inst_2 (f b)))
            (@Std.Iter.map α β (Array γ) inst (fun (b : β) => @Std.Iter.toArray α₂ γ inst_2 (f b)) it₁))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.toArray_flatMap 7)

-- `Std.Rio.mem_succ_iff` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Rio.mem_succ_iff.h7.{u} :
    ∀ {α : Type u} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LinearlyUpwardEnumerable α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLT α]
      [inst_5 : Std.PRange.InfinitelyUpwardEnumerable α] [inst_6 : Std.PRange.LawfulUpwardEnumerable α] {hi a : α},
      a ∈ *...Std.PRange.UpwardEnumerable.succ hi ↔ a ∈ *...hi ∨ a = hi :=
  no_implicit_lambda% (drop_unused% Std.Rio.mem_succ_iff 7)

-- `Std.Roi.mem_of_mem_of_le` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Roi.mem_of_mem_of_le.h5.{u} :
    ∀ {α : Type u} {r : Std.Roi α} [inst : LT α] [inst_1 : Std.PRange.UpwardEnumerable α]
      [inst_2 : Std.PRange.LawfulUpwardEnumerableLT α] [inst_3 : Std.PRange.LawfulUpwardEnumerable α] {a b : α},
      Std.PRange.UpwardEnumerable.LE r.lower b → a ∈ b<...* → a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Roi.mem_of_mem_of_le 5)

-- `Std.Ric.mem_succ_iff` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Ric.mem_succ_iff.h7.{u} :
    ∀ {α : Type u} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LinearlyUpwardEnumerable α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLE α]
      [inst_5 : Std.PRange.InfinitelyUpwardEnumerable α] [inst_6 : Std.PRange.LawfulUpwardEnumerable α] {hi a : α},
      a ∈ *...=Std.PRange.UpwardEnumerable.succ hi ↔ a ∈ *...=hi ∨ a = Std.PRange.UpwardEnumerable.succ hi :=
  no_implicit_lambda% (drop_unused% Std.Ric.mem_succ_iff 7)

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMapM` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMapM.h7.{w, w'} :
    ∀ {α β α₂ γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : MonadAttach m] [inst_2 : Std.Iterator α m β]
      [inst_3 : Std.Iterator α₂ m γ] {f : β → m (@Std.IterM α₂ m γ)} {it₁ : @Std.IterM α m β} {it₂ it₂' : @Std.IterM α₂ m γ}
      {b : γ},
      @Std.IterM.IsPlausibleStep α₂ m γ inst_3 it₂ (@Std.IterStep.yield (@Std.IterM α₂ m γ) γ it₂' b) →
        @Std.IterM.IsPlausibleStep
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            α₂ γ m)
          m γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_2
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            inst_3)
          (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_2 inst_3 f it₁ (@Option.some (@Std.IterM α₂ m γ) it₂))
          (@Std.IterStep.yield
            (@Std.IterM
              (Std.Iterators.Types.Flatten
                (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                  (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                  @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                α₂ γ m)
              m γ)
            γ (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_2 inst_3 f it₁ (@Option.some (@Std.IterM α₂ m γ) it₂'))
            b) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMapM 7)

-- `Std.IterM.anyM_eq_forIn` idx 4: unused in the library's proof
theorem HypCheckProof.Std.IterM.anyM_eq_forIn.h4.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : Monad m] [inst_2 : @LawfulMonad m inst_1]
      [inst_3 : @Std.IteratorLoop α m β inst m] [inst_4 : @Std.LawfulIteratorLoop β α m m inst_1 inst_1 inst inst_3]
      {it : @Std.IterM α m β} {p : β → m (ULift Bool)},
      @Eq (m (ULift Bool)) (@Std.IterM.anyM α β m inst_1 inst inst_3 p it)
        (@ForIn.forIn m (@Std.IterM α m β) β
          (@Std.IterM.instForInOfIteratorLoop m m α β inst inst_3 (instMonadLiftT m) inst_1) (ULift Bool) it
          (@ULift.up Bool Bool.false) fun (x : β) (x_1 : ULift Bool) =>
          @Bind.bind m (@Monad.toBind m inst_1) (ULift Bool) (ForInStep (ULift Bool)) (p x) fun (__do_lift : ULift Bool) =>
            @ite (m (ForInStep (ULift Bool))) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
              (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true)
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_1)) (ForInStep (ULift Bool))
                (@ForInStep.done (ULift Bool) (@ULift.up Bool Bool.true)))
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_1)) (ForInStep (ULift Bool))
                (@ForInStep.yield (ULift Bool) (@ULift.up Bool Bool.false)))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.anyM_eq_forIn 4)

-- `Std.IterM.anyM_eq_forIn` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.anyM_eq_forIn.h6.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      [inst_2 : Monad m] [inst_3 : @Std.IteratorLoop α m β inst m]
      [inst_4 : @Std.LawfulIteratorLoop β α m m inst_2 inst_2 inst inst_3] {it : @Std.IterM α m β} {p : β → m (ULift Bool)},
      @Eq (m (ULift Bool)) (@Std.IterM.anyM α β m inst_2 inst inst_3 p it)
        (@ForIn.forIn m (@Std.IterM α m β) β
          (@Std.IterM.instForInOfIteratorLoop m m α β inst inst_3 (instMonadLiftT m) inst_2) (ULift Bool) it
          (@ULift.up Bool Bool.false) fun (x : β) (x_1 : ULift Bool) =>
          @Bind.bind m (@Monad.toBind m inst_2) (ULift Bool) (ForInStep (ULift Bool)) (p x) fun (__do_lift : ULift Bool) =>
            @ite (m (ForInStep (ULift Bool))) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
              (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true)
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep (ULift Bool))
                (@ForInStep.done (ULift Bool) (@ULift.up Bool Bool.true)))
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep (ULift Bool))
                (@ForInStep.yield (ULift Bool) (@ULift.up Bool Bool.false)))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.anyM_eq_forIn 6)

-- `Std.IterM.anyM_eq_forIn` idx 8: unused in the library's proof
theorem HypCheckProof.Std.IterM.anyM_eq_forIn.h8.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      [inst_2 : Monad m] [inst_3 : @LawfulMonad m inst_2] [inst_4 : @Std.IteratorLoop α m β inst m] {it : @Std.IterM α m β}
      {p : β → m (ULift Bool)},
      @Eq (m (ULift Bool)) (@Std.IterM.anyM α β m inst_2 inst inst_4 p it)
        (@ForIn.forIn m (@Std.IterM α m β) β
          (@Std.IterM.instForInOfIteratorLoop m m α β inst inst_4 (instMonadLiftT m) inst_2) (ULift Bool) it
          (@ULift.up Bool Bool.false) fun (x : β) (x_1 : ULift Bool) =>
          @Bind.bind m (@Monad.toBind m inst_2) (ULift Bool) (ForInStep (ULift Bool)) (p x) fun (__do_lift : ULift Bool) =>
            @ite (m (ForInStep (ULift Bool))) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
              (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true)
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep (ULift Bool))
                (@ForInStep.done (ULift Bool) (@ULift.up Bool Bool.true)))
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep (ULift Bool))
                (@ForInStep.yield (ULift Bool) (@ULift.up Bool Bool.false)))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.anyM_eq_forIn 8)

-- `Std.Iter.allM_eq_forIn` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Iter.allM_eq_forIn.h4.{w, w'} :
    ∀ {α β : Type w} {m : Type → Type w'} [inst : Std.Iterator α Id β] [inst_1 : Monad m] [inst_2 : @LawfulMonad m inst_1]
      [inst_3 : @Std.IteratorLoop α Id β inst m] [inst_4 : @Std.LawfulIteratorLoop β α Id m Id.instMonad inst_1 inst inst_3]
      {it : @Std.Iter α β} {p : β → m Bool},
      @Eq (m Bool) (@Std.Iter.allM α β m inst_1 inst inst_3 p it)
        (@ForIn.forIn m (@Std.Iter α β) β (@Std.instForInIterOfMonadOfIteratorLoopId α β m inst_1 inst inst_3) Bool it
          Bool.true fun (x : β) (x_1 : Bool) =>
          @Bind.bind m (@Monad.toBind m inst_1) Bool (ForInStep Bool) (p x) fun (__do_lift : Bool) =>
            @ite (m (ForInStep Bool)) (@Eq Bool __do_lift Bool.true) (instDecidableEqBool __do_lift Bool.true)
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_1)) (ForInStep Bool)
                (@ForInStep.yield Bool Bool.true))
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_1)) (ForInStep Bool)
                (@ForInStep.done Bool Bool.false))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.allM_eq_forIn 4)

-- `Std.Iter.allM_eq_forIn` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iter.allM_eq_forIn.h6.{w, w'} :
    ∀ {α β : Type w} {m : Type → Type w'} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      [inst_2 : Monad m] [inst_3 : @Std.IteratorLoop α Id β inst m]
      [inst_4 : @Std.LawfulIteratorLoop β α Id m Id.instMonad inst_2 inst inst_3] {it : @Std.Iter α β} {p : β → m Bool},
      @Eq (m Bool) (@Std.Iter.allM α β m inst_2 inst inst_3 p it)
        (@ForIn.forIn m (@Std.Iter α β) β (@Std.instForInIterOfMonadOfIteratorLoopId α β m inst_2 inst inst_3) Bool it
          Bool.true fun (x : β) (x_1 : Bool) =>
          @Bind.bind m (@Monad.toBind m inst_2) Bool (ForInStep Bool) (p x) fun (__do_lift : Bool) =>
            @ite (m (ForInStep Bool)) (@Eq Bool __do_lift Bool.true) (instDecidableEqBool __do_lift Bool.true)
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep Bool)
                (@ForInStep.yield Bool Bool.true))
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep Bool)
                (@ForInStep.done Bool Bool.false))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.allM_eq_forIn 6)

-- `Std.Iter.allM_eq_forIn` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Iter.allM_eq_forIn.h8.{w, w'} :
    ∀ {α β : Type w} {m : Type → Type w'} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      [inst_2 : Monad m] [inst_3 : @LawfulMonad m inst_2] [inst_4 : @Std.IteratorLoop α Id β inst m] {it : @Std.Iter α β}
      {p : β → m Bool},
      @Eq (m Bool) (@Std.Iter.allM α β m inst_2 inst inst_4 p it)
        (@ForIn.forIn m (@Std.Iter α β) β (@Std.instForInIterOfMonadOfIteratorLoopId α β m inst_2 inst inst_4) Bool it
          Bool.true fun (x : β) (x_1 : Bool) =>
          @Bind.bind m (@Monad.toBind m inst_2) Bool (ForInStep Bool) (p x) fun (__do_lift : Bool) =>
            @ite (m (ForInStep Bool)) (@Eq Bool __do_lift Bool.true) (instDecidableEqBool __do_lift Bool.true)
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep Bool)
                (@ForInStep.yield Bool Bool.true))
              (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep Bool)
                (@ForInStep.done Bool Bool.false))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.allM_eq_forIn 8)

-- `Std.IterM.step_flatMapAfterM` idx 8: unused in the library's proof
theorem HypCheckProof.Std.IterM.step_flatMapAfterM.h8.{w, w'} :
    ∀ {α β α₂ γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : MonadAttach m] [inst_2 : @LawfulMonad m inst]
      [inst_3 : Std.Iterator α m β] [inst_4 : Std.Iterator α₂ m γ] {f : β → m (@Std.IterM α₂ m γ)} {it₁ : @Std.IterM α m β}
      {it₂ : Option (@Std.IterM α₂ m γ)},
      @Eq
        (m
          (Std.Shrink
            (@Std.IterM.Step
              (Std.Iterators.Types.Flatten
                (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                  (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                  @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                α₂ γ m)
              m γ
              (@Std.Iterators.Types.Flatten.instIterator
                (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                  (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                  @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                α₂ γ m inst
                (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                  (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                  @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                inst_4)
              (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁ it₂))))
        (@Std.IterM.step
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            α₂ γ m)
          m γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            inst_4)
          (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁ it₂))
        (@Std.IterM.step_flatMapAfterM.match_3 α₂ γ m
          (fun (it₂ : Option (@Std.IterM α₂ m γ)) =>
            m
              (Std.Shrink
                (@Std.IterM.Step
                  (Std.Iterators.Types.Flatten
                    (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                      (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                      @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                    α₂ γ m)
                  m γ
                  (@Std.Iterators.Types.Flatten.instIterator
                    (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                      (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                      @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                    α₂ γ m inst
                    (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                      @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                    inst_4)
                  (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁ it₂))))
          it₂
          (fun (_ : Unit) =>
            @Bind.bind m (@Monad.toBind m inst) (Std.Shrink (@Std.IterM.Step α m β inst_3 it₁))
              (Std.Shrink
                (@Std.IterM.Step
                  (Std.Iterators.Types.Flatten
                    (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                      (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                      @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                    α₂ γ m)
                  m γ
                  (@Std.Iterators.Types.Flatten.instIterator
                    (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                      (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                      @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                    α₂ γ m inst
                    (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                      @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                    inst_4)
                  (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁ (@Option.none (@Std.IterM α₂ m γ)))))
              (@Std.IterM.step α m β inst_3 it₁) fun (__do_lift : Std.Shrink (@Std.IterM.Step α m β inst_3 it₁)) =>
              @Std.IterM.step_flatMapAfterM.match_1 α β m inst_3 it₁
                (fun (x : @Std.IterM.Step α m β inst_3 it₁) =>
                  m
                    (Std.Shrink
                      (@Std.IterM.Step
                        (Std.Iterators.Types.Flatten
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m)
                        m γ
                        (@Std.Iterators.Types.Flatten.instIterator
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m inst
                          (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          inst_4)
                        (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                          (@Option.none (@Std.IterM α₂ m γ))))))
                (@Std.Shrink.inflate (@Std.IterM.Step α m β inst_3 it₁) __do_lift)
                (fun (it₁' : @Std.IterM α m β) (b : β)
                    (h : @Std.IterM.IsPlausibleStep α m β inst_3 it₁ (@Std.IterStep.yield (@Std.IterM α m β) β it₁' b)) =>
                  @Bind.bind m (@Monad.toBind m inst)
                    (@Subtype (@Std.IterM α₂ m γ) (@MonadAttach.CanReturn m inst_1 (@Std.IterM α₂ m γ) (f b)))
                    (Std.Shrink
                      (@Std.IterM.Step
                        (Std.Iterators.Types.Flatten
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m)
                        m γ
                        (@Std.Iterators.Types.Flatten.instIterator
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m inst
                          (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          inst_4)
                        (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                          (@Option.none (@Std.IterM α₂ m γ)))))
                    (@MonadAttach.attach m inst_1 (@Std.IterM α₂ m γ) (f b))
                    fun (fx : @Subtype (@Std.IterM α₂ m γ) (@MonadAttach.CanReturn m inst_1 (@Std.IterM α₂ m γ) (f b))) =>
                    @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                      (Std.Shrink
                        (@Std.IterM.Step
                          (Std.Iterators.Types.Flatten
                            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                            α₂ γ m)
                          m γ
                          (@Std.Iterators.Types.Flatten.instIterator
                            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                            α₂ γ m inst
                            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                            inst_4)
                          (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                            (@Option.none (@Std.IterM α₂ m γ)))))
                      (@Std.Shrink.deflate
                        (@Std.IterM.Step
                          (Std.Iterators.Types.Flatten
                            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                            α₂ γ m)
                          m γ
                          (@Std.Iterators.Types.Flatten.instIterator
                            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                            α₂ γ m inst
                            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                            inst_4)
                          (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                            (@Option.none (@Std.IterM α₂ m γ))))
                        (@Std.PlausibleIterStep.skip
                          (@Std.IterM
                            (Std.Iterators.Types.Flatten
                              (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                                (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                                (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                                @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                              α₂ γ m)
                            m γ)
                          γ
                          (@Std.IterM.IsPlausibleStep
                            (Std.Iterators.Types.Flatten
                              (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                                (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                                (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                                @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                              α₂ γ m)
                            m γ
                            (@Std.Iterators.Types.Flatten.instIterator
                              (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                                (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                                (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                                @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                              α₂ γ m inst
                              (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                                (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                                @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                              inst_4)
                            (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                              (@Option.none (@Std.IterM α₂ m γ))))
                          (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁'
                            (@Option.some (@Std.IterM α₂ m γ)
                              (@Subtype.val (@Std.IterM α₂ m γ) (@MonadAttach.CanReturn m inst_1 (@Std.IterM α₂ m γ) (f b))
                                fx)))
                          (@Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM α β α₂ γ m inst inst_1 inst_2
                            inst_3 inst_4 f it₁ it₁'
                            (@Subtype.val (@Std.IterM α₂ m γ) (@MonadAttach.CanReturn m inst_1 (@Std.IterM α₂ m γ) (f b))
                              fx)
                            b h
                            (@Subtype.property (@Std.IterM α₂ m γ)
                              (@MonadAttach.CanReturn m inst_1 (@Std.IterM α₂ m γ) (f b)) fx)))))
                (fun (it₁' : @Std.IterM α m β)
                    (h : @Std.IterM.IsPlausibleStep α m β inst_3 it₁ (@Std.IterStep.skip (@Std.IterM α m β) β it₁')) =>
                  @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                    (Std.Shrink
                      (@Std.IterM.Step
                        (Std.Iterators.Types.Flatten
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m)
                        m γ
                        (@Std.Iterators.Types.Flatten.instIterator
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m inst
                          (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          inst_4)
                        (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                          (@Option.none (@Std.IterM α₂ m γ)))))
                    (@Std.Shrink.deflate
                      (@Std.IterM.Step
                        (Std.Iterators.Types.Flatten
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m)
                        m γ
                        (@Std.Iterators.Types.Flatten.instIterator
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m inst
                          (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          inst_4)
                        (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                          (@Option.none (@Std.IterM α₂ m γ))))
                      (@Std.PlausibleIterStep.skip
                        (@Std.IterM
                          (Std.Iterators.Types.Flatten
                            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                            α₂ γ m)
                          m γ)
                        γ
                        (@Std.IterM.IsPlausibleStep
                          (Std.Iterators.Types.Flatten
                            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                            α₂ γ m)
                          m γ
                          (@Std.Iterators.Types.Flatten.instIterator
                            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                            α₂ γ m inst
                            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                            inst_4)
                          (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                            (@Option.none (@Std.IterM α₂ m γ))))
                        (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁'
                          (@Option.none (@Std.IterM α₂ m γ)))
                        (@Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMapM α β α₂ γ m inst inst_1 inst_2
                          inst_3 inst_4 f it₁ it₁' h))))
                fun (h : @Std.IterM.IsPlausibleStep α m β inst_3 it₁ (@Std.IterStep.done (@Std.IterM α m β) β)) =>
                @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                  (Std.Shrink
                    (@Std.IterM.Step
                      (Std.Iterators.Types.Flatten
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m)
                      m γ
                      (@Std.Iterators.Types.Flatten.instIterator
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m inst
                        (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        inst_4)
                      (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                        (@Option.none (@Std.IterM α₂ m γ)))))
                  (@Std.Shrink.deflate
                    (@Std.IterM.Step
                      (Std.Iterators.Types.Flatten
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m)
                      m γ
                      (@Std.Iterators.Types.Flatten.instIterator
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m inst
                        (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        inst_4)
                      (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                        (@Option.none (@Std.IterM α₂ m γ))))
                    (@Std.PlausibleIterStep.done
                      (@Std.IterM
                        (Std.Iterators.Types.Flatten
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m)
                        m γ)
                      γ
                      (@Std.IterM.IsPlausibleStep
                        (Std.Iterators.Types.Flatten
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m)
                        m γ
                        (@Std.Iterators.Types.Flatten.instIterator
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m inst
                          (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          inst_4)
                        (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                          (@Option.none (@Std.IterM α₂ m γ))))
                      (@Std.Iterators.Types.Flatten.IsPlausibleStep.outerDone_flatMapM α β α₂ γ m inst inst_1 inst_2 inst_3
                        inst_4 f it₁ h))))
          fun (it₂ : @Std.IterM α₂ m γ) =>
          @Bind.bind m (@Monad.toBind m inst) (Std.Shrink (@Std.IterM.Step α₂ m γ inst_4 it₂))
            (Std.Shrink
              (@Std.IterM.Step
                (Std.Iterators.Types.Flatten
                  (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                    (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                    (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                    @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                  α₂ γ m)
                m γ
                (@Std.Iterators.Types.Flatten.instIterator
                  (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                    (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                    (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                    @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                  α₂ γ m inst
                  (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                    (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                    @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                  inst_4)
                (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                  (@Option.some (@Std.IterM α₂ m γ) it₂))))
            (@Std.IterM.step α₂ m γ inst_4 it₂) fun (__do_lift : Std.Shrink (@Std.IterM.Step α₂ m γ inst_4 it₂)) =>
            @Std.IterM.step_flatMapAfterM.match_1 α₂ γ m inst_4 it₂
              (fun (x : @Std.IterM.Step α₂ m γ inst_4 it₂) =>
                m
                  (Std.Shrink
                    (@Std.IterM.Step
                      (Std.Iterators.Types.Flatten
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m)
                      m γ
                      (@Std.Iterators.Types.Flatten.instIterator
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m inst
                        (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        inst_4)
                      (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                        (@Option.some (@Std.IterM α₂ m γ) it₂)))))
              (@Std.Shrink.inflate (@Std.IterM.Step α₂ m γ inst_4 it₂) __do_lift)
              (fun (it₂' : @Std.IterM α₂ m γ) (out : γ)
                  (h : @Std.IterM.IsPlausibleStep α₂ m γ inst_4 it₂ (@Std.IterStep.yield (@Std.IterM α₂ m γ) γ it₂' out)) =>
                @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                  (Std.Shrink
                    (@Std.IterM.Step
                      (Std.Iterators.Types.Flatten
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m)
                      m γ
                      (@Std.Iterators.Types.Flatten.instIterator
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m inst
                        (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        inst_4)
                      (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                        (@Option.some (@Std.IterM α₂ m γ) it₂))))
                  (@Std.Shrink.deflate
                    (@Std.IterM.Step
                      (Std.Iterators.Types.Flatten
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m)
                      m γ
                      (@Std.Iterators.Types.Flatten.instIterator
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m inst
                        (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        inst_4)
                      (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                        (@Option.some (@Std.IterM α₂ m γ) it₂)))
                    (@Std.PlausibleIterStep.yield
                      (@Std.IterM
                        (Std.Iterators.Types.Flatten
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m)
                        m γ)
                      γ
                      (@Std.IterM.IsPlausibleStep
                        (Std.Iterators.Types.Flatten
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m)
                        m γ
                        (@Std.Iterators.Types.Flatten.instIterator
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m inst
                          (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          inst_4)
                        (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                          (@Option.some (@Std.IterM α₂ m γ) it₂)))
                      (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                        (@Option.some (@Std.IterM α₂ m γ) it₂'))
                      out
                      (@Std.Iterators.Types.Flatten.IsPlausibleStep.innerYield_flatMapM α β α₂ γ m inst inst_1 inst_2 inst_3
                        inst_4 f it₁ it₂ it₂' out h))))
              (fun (it₂' : @Std.IterM α₂ m γ)
                  (h : @Std.IterM.IsPlausibleStep α₂ m γ inst_4 it₂ (@Std.IterStep.skip (@Std.IterM α₂ m γ) γ it₂')) =>
                @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                  (Std.Shrink
                    (@Std.IterM.Step
                      (Std.Iterators.Types.Flatten
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m)
                      m γ
                      (@Std.Iterators.Types.Flatten.instIterator
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m inst
                        (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        inst_4)
                      (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                        (@Option.some (@Std.IterM α₂ m γ) it₂))))
                  (@Std.Shrink.deflate
                    (@Std.IterM.Step
                      (Std.Iterators.Types.Flatten
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m)
                      m γ
                      (@Std.Iterators.Types.Flatten.instIterator
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m inst
                        (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        inst_4)
                      (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                        (@Option.some (@Std.IterM α₂ m γ) it₂)))
                    (@Std.PlausibleIterStep.skip
                      (@Std.IterM
                        (Std.Iterators.Types.Flatten
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m)
                        m γ)
                      γ
                      (@Std.IterM.IsPlausibleStep
                        (Std.Iterators.Types.Flatten
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m)
                        m γ
                        (@Std.Iterators.Types.Flatten.instIterator
                          (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                            (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          α₂ γ m inst
                          (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                          inst_4)
                        (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                          (@Option.some (@Std.IterM α₂ m γ) it₂)))
                      (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                        (@Option.some (@Std.IterM α₂ m γ) it₂'))
                      (@Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMapM α β α₂ γ m inst inst_1 inst_2 inst_3
                        inst_4 f it₁ it₂ it₂' h))))
              fun (h : @Std.IterM.IsPlausibleStep α₂ m γ inst_4 it₂ (@Std.IterStep.done (@Std.IterM α₂ m γ) γ)) =>
              @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
                (Std.Shrink
                  (@Std.IterM.Step
                    (Std.Iterators.Types.Flatten
                      (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                        (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                        (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                        @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                      α₂ γ m)
                    m γ
                    (@Std.Iterators.Types.Flatten.instIterator
                      (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                        (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                        (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                        @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                      α₂ γ m inst
                      (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                        (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                        @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                      inst_4)
                    (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                      (@Option.some (@Std.IterM α₂ m γ) it₂))))
                (@Std.Shrink.deflate
                  (@Std.IterM.Step
                    (Std.Iterators.Types.Flatten
                      (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                        (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                        (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                        @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                      α₂ γ m)
                    m γ
                    (@Std.Iterators.Types.Flatten.instIterator
                      (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                        (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                        (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                        @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                      α₂ γ m inst
                      (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                        (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                        @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                      inst_4)
                    (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                      (@Option.some (@Std.IterM α₂ m γ) it₂)))
                  (@Std.PlausibleIterStep.skip
                    (@Std.IterM
                      (Std.Iterators.Types.Flatten
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m)
                      m γ)
                    γ
                    (@Std.IterM.IsPlausibleStep
                      (Std.Iterators.Types.Flatten
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m)
                      m γ
                      (@Std.Iterators.Types.Flatten.instIterator
                        (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                          (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        α₂ γ m inst
                        (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_3
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
                          @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                        inst_4)
                      (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁
                        (@Option.some (@Std.IterM α₂ m γ) it₂)))
                    (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_3 inst_4 f it₁ (@Option.none (@Std.IterM α₂ m γ)))
                    (@Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMapM α β α₂ γ m inst inst_1 inst_2 inst_3
                      inst_4 f it₁ it₂ h)))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.step_flatMapAfterM 8)

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMapM` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMapM.h7.{w, w'} :
    ∀ {α β α₂ γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : MonadAttach m] [inst_2 : Std.Iterator α m β]
      [inst_3 : Std.Iterator α₂ m γ] {f : β → m (@Std.IterM α₂ m γ)} {it₁ : @Std.IterM α m β} {it₂ : @Std.IterM α₂ m γ},
      @Std.IterM.IsPlausibleStep α₂ m γ inst_3 it₂ (@Std.IterStep.done (@Std.IterM α₂ m γ) γ) →
        @Std.IterM.IsPlausibleStep
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            α₂ γ m)
          m γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_2
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            inst_3)
          (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_2 inst_3 f it₁ (@Option.some (@Std.IterM α₂ m γ) it₂))
          (@Std.IterStep.skip
            (@Std.IterM
              (Std.Iterators.Types.Flatten
                (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                  (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                  @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                α₂ γ m)
              m γ)
            γ (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_2 inst_3 f it₁ (@Option.none (@Std.IterM α₂ m γ)))) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.Types.Flatten.IsPlausibleStep.innerDone_flatMapM 7)

-- `Std.Ric.isEmpty_iff_forall_not_mem` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Ric.isEmpty_iff_forall_not_mem.h5.{u} :
    ∀ {α : Type u} {r : Std.Ric α} [inst : LE α] [inst_1 : Std.PRange.UpwardEnumerable α] [inst_2 : Std.Rxc.HasSize α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLE α] [inst_4 : Std.Rxc.IsAlwaysFinite α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α], r.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Ric.isEmpty_iff_forall_not_mem 5)

-- `Std.Ric.isEmpty_iff_forall_not_mem` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Ric.isEmpty_iff_forall_not_mem.h7.{u} :
    ∀ {α : Type u} {r : Std.Ric α} [inst : LE α] [inst_1 : Std.PRange.UpwardEnumerable α] [inst_2 : Std.Rxc.HasSize α]
      [inst_3 : Std.Rxc.LawfulHasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLE α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerable α], r.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Ric.isEmpty_iff_forall_not_mem 7)

-- `Std.Iter.any_eq_anyM` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Iter.any_eq_anyM.h3.{w} :
    ∀ {α β : Type w} [inst : Std.Iterator α Id β] [inst_1 : @Std.IteratorLoop α Id β inst Id]
      [inst_2 : @Std.LawfulIteratorLoop β α Id Id Id.instMonad Id.instMonad inst inst_1] {it : @Std.Iter α β}
      {p : β → Bool},
      @Eq Bool (@Std.Iter.any α β inst inst_1 p it)
        (@Id.run Bool
          (@Std.Iter.anyM α β Id Id.instMonad inst inst_1
            (fun (x : β) => @Pure.pure Id (@Applicative.toPure Id (@Monad.toApplicative Id Id.instMonad)) Bool (p x)) it)) :=
  no_implicit_lambda% (drop_unused% Std.Iter.any_eq_anyM 3)

-- `Std.Iter.any_eq_anyM` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Iter.any_eq_anyM.h5.{w} :
    ∀ {α β : Type w} [inst : Std.Iterator α Id β] [inst_1 : @Std.Iterators.Finite α Id β inst]
      [inst_2 : @Std.IteratorLoop α Id β inst Id] {it : @Std.Iter α β} {p : β → Bool},
      @Eq Bool (@Std.Iter.any α β inst inst_2 p it)
        (@Id.run Bool
          (@Std.Iter.anyM α β Id Id.instMonad inst inst_2
            (fun (x : β) => @Pure.pure Id (@Applicative.toPure Id (@Monad.toApplicative Id Id.instMonad)) Bool (p x)) it)) :=
  no_implicit_lambda% (drop_unused% Std.Iter.any_eq_anyM 5)

-- `Std.Slice.Internal.foldM_iter` idx 10: unused in the library's proof
theorem HypCheckProof.Std.Slice.Internal.foldM_iter.h10.{u, v, w, w'} :
    ∀ {γ : Type u} {α β : Type v} {δ : Type w} {init : δ} {m : Type w → Type w'} [inst : Monad m]
      [inst_1 : Std.ToIterator (Std.Slice γ) Id α β] [inst_2 : Std.Iterator α Id β] [inst_3 : Std.IteratorLoop α Id m]
      {s : Std.Slice γ} {f : δ → β → m δ}, Std.Iter.foldM f init (Std.Slice.Internal.iter s) = Std.Slice.foldlM f init s :=
  no_implicit_lambda% (drop_unused% Std.Slice.Internal.foldM_iter 10)

-- `Std.Rio.size_eq_match_rcc` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Rio.size_eq_match_rcc.h7.{u} :
    ∀ {α : Type u} {r : Std.Rio α} [inst : Std.PRange.Least? α] [inst_1 : LT α] [inst_2 : @DecidableLT α inst_1]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxo.HasSize α]
      [inst_5 : @Std.PRange.LawfulUpwardEnumerableLT α inst_3 inst_1] [inst_6 : @Std.Rxo.IsAlwaysFinite α inst_3 inst_1]
      [inst_7 : @Std.Rxo.LawfulHasSize α inst_1 inst_3 inst_4],
      @Eq Nat (@Std.Rio.size α inst_4 inst r)
        (@Std.Rxc.Iterator.toList_eq_match.match_1 α (fun (x : Option α) => Nat) (@Std.PRange.Least?.least? α inst)
          (fun (_ : Unit) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun (next : α) =>
          @Std.Rco.size α inst_4 (@Std.Rco.mk α next (@Std.Rio.upper α r))) :=
  no_implicit_lambda% (drop_unused% Std.Rio.size_eq_match_rcc 7)

-- `Std.Rio.size_eq_match_rcc` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Rio.size_eq_match_rcc.h8.{u} :
    ∀ {α : Type u} {r : Std.Rio α} [inst : Std.PRange.Least? α] [inst_1 : LT α] [inst_2 : @DecidableLT α inst_1]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxo.HasSize α]
      [inst_5 : @Std.PRange.LawfulUpwardEnumerable α inst_3] [inst_6 : @Std.Rxo.IsAlwaysFinite α inst_3 inst_1]
      [inst_7 : @Std.Rxo.LawfulHasSize α inst_1 inst_3 inst_4],
      @Eq Nat (@Std.Rio.size α inst_4 inst r)
        (@Std.Rxc.Iterator.toList_eq_match.match_1 α (fun (x : Option α) => Nat) (@Std.PRange.Least?.least? α inst)
          (fun (_ : Unit) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun (next : α) =>
          @Std.Rco.size α inst_4 (@Std.Rco.mk α next (@Std.Rio.upper α r))) :=
  no_implicit_lambda% (drop_unused% Std.Rio.size_eq_match_rcc 8)

-- `Std.Rio.size_eq_match_rcc` idx 9: unused in the library's proof
theorem HypCheckProof.Std.Rio.size_eq_match_rcc.h9.{u} :
    ∀ {α : Type u} {r : Std.Rio α} [inst : Std.PRange.Least? α] [inst_1 : LT α] [inst_2 : @DecidableLT α inst_1]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxo.HasSize α]
      [inst_5 : @Std.PRange.LawfulUpwardEnumerable α inst_3] [inst_6 : @Std.PRange.LawfulUpwardEnumerableLT α inst_3 inst_1]
      [inst_7 : @Std.Rxo.LawfulHasSize α inst_1 inst_3 inst_4],
      @Eq Nat (@Std.Rio.size α inst_4 inst r)
        (@Std.Rxc.Iterator.toList_eq_match.match_1 α (fun (x : Option α) => Nat) (@Std.PRange.Least?.least? α inst)
          (fun (_ : Unit) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun (next : α) =>
          @Std.Rco.size α inst_4 (@Std.Rco.mk α next (@Std.Rio.upper α r))) :=
  no_implicit_lambda% (drop_unused% Std.Rio.size_eq_match_rcc 9)

-- `Std.Rio.size_eq_match_rcc` idx 10: unused in the library's proof
theorem HypCheckProof.Std.Rio.size_eq_match_rcc.h10.{u} :
    ∀ {α : Type u} {r : Std.Rio α} [inst : Std.PRange.Least? α] [inst_1 : LT α] [inst_2 : @DecidableLT α inst_1]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxo.HasSize α]
      [inst_5 : @Std.PRange.LawfulUpwardEnumerable α inst_3] [inst_6 : @Std.PRange.LawfulUpwardEnumerableLT α inst_3 inst_1]
      [inst_7 : @Std.Rxo.IsAlwaysFinite α inst_3 inst_1],
      @Eq Nat (@Std.Rio.size α inst_4 inst r)
        (@Std.Rxc.Iterator.toList_eq_match.match_1 α (fun (x : Option α) => Nat) (@Std.PRange.Least?.least? α inst)
          (fun (_ : Unit) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun (next : α) =>
          @Std.Rco.size α inst_4 (@Std.Rco.mk α next (@Std.Rio.upper α r))) :=
  no_implicit_lambda% (drop_unused% Std.Rio.size_eq_match_rcc 10)

-- `Std.Rii.toList_eq_nil_iff` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Rii.toList_eq_nil_iff.h7.{u} :
    ∀ {α : Type u} {r : Std.Rii α} [inst : LT α] [inst : DecidableLT α] [inst : Std.PRange.Least? α]
      [inst_1 : Std.PRange.UpwardEnumerable α] [inst_2 : Std.PRange.LawfulUpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerableLeast? α] [inst_4 : Std.Rxi.IsAlwaysFinite α], r.toList = [] ↔ ¬Nonempty α :=
  no_implicit_lambda% (drop_unused% Std.Rii.toList_eq_nil_iff 7)

-- `Std.toList_roo_eq_toList_rco_of_isSome_succ?` idx 5: unused in the library's proof
theorem HypCheckProof.Std.toList_roo_eq_toList_rco_of_isSome_succ?.h5.{u} :
    ∀ {α : Type u} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LawfulUpwardEnumerable α] [inst_4 : Std.Rxo.IsAlwaysFinite α] {lo hi : α}
      (h : (Std.PRange.UpwardEnumerable.succ? lo).isSome = Bool.true),
      (lo<...hi).toList = ((Std.PRange.UpwardEnumerable.succ? lo).get h...hi).toList :=
  no_implicit_lambda% (drop_unused% Std.toList_roo_eq_toList_rco_of_isSome_succ? 5)

-- `List.min_map` idx 5: unused in the library's proof
theorem HypCheckProof.List.min_map.h5.{u_1, u_2} :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : Min β]
      [inst_3 : Std.LawfulOrderLeftLeaningMin β] {xs : List α} {f : α → β} (h : xs ≠ []),
      (List.map f xs).min (List.min_map._proof_1 h) = f (List.minOn f xs h) :=
  no_implicit_lambda% (drop_unused% List.min_map 5)

-- `Std.Rci.getElem?_toArray_eq` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Rci.getElem?_toArray_eq.h6.{u} :
    ∀ {α : Type u} {r : Std.Rci α} [inst : LT α] [inst : DecidableLT α] [inst : Std.PRange.UpwardEnumerable α]
      [inst_1 : Std.PRange.LawfulUpwardEnumerable α] [inst_2 : Std.Rxi.IsAlwaysFinite α] {i : Nat},
      r.toArray[i]? = Std.PRange.UpwardEnumerable.succMany? i r.lower :=
  no_implicit_lambda% (drop_unused% Std.Rci.getElem?_toArray_eq 6)

-- `Std.IterM.foldM_mapM` idx 19: unused in the library's proof
theorem HypCheckProof.Std.IterM.foldM_mapM.h19.{w, w', w'', w'''} :
    ∀ {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : Monad m] [inst_3 : @LawfulMonad m inst_2] [inst_4 : Monad n]
      [inst_5 : MonadAttach n] [inst_6 : @LawfulMonad n inst_4] [inst_7 : @WeaklyLawfulMonadAttach n inst_4 inst_5]
      [inst_8 : Monad o] [inst_9 : @LawfulMonad o inst_8] [inst_10 : @Std.IteratorLoop α m β inst n]
      [inst_11 : @Std.IteratorLoop α m β inst o] [inst_12 : @Std.LawfulIteratorLoop β α m o inst_2 inst_8 inst inst_11]
      [inst_13 : MonadLiftT m n] [inst_14 : MonadLiftT n o] [inst_15 : @LawfulMonadLiftT m n inst_2 inst_4 inst_13]
      [inst_16 : @LawfulMonadLiftT n o inst_4 inst_8 inst_14] {f : β → n γ} {g : δ → γ → o δ} {init : δ}
      {it : @Std.IterM α m β},
      @Eq (o δ)
        (@Std.IterM.foldM n o inst_8
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_13 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_4)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_5 (f b))
          γ δ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_4 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_13 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_5 (f b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β γ m n o inst_4 inst_8 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_13 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift γ n inst_5 (f b))
          inst_14 g init (@Std.IterM.mapM α β γ m n inst inst_4 inst_5 inst_13 f it))
        (@Std.IterM.foldM m o inst_8 α β δ inst inst_11
          (@instMonadLiftTOfMonadLift m n o (@MonadLift.mk n o fun {α : Type w} => @MonadLiftT.monadLift n o inst_14 α)
            inst_13)
          (fun (d : δ) (b : β) =>
            @Bind.bind o (@Monad.toBind o inst_8) γ δ (@liftM n o inst_14 γ (f b)) fun (c : γ) => g d c)
          init it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.foldM_mapM 19)

-- `Std.IterM.toList_filterMapM_filterMapWithPostcondition` idx 12: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_filterMapM_filterMapWithPostcondition.h12.{w, w', w'', w'''} :
    ∀ {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''} [inst : Monad m]
      [inst_1 : @LawfulMonad m inst] [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @LawfulMonad n inst_2]
      [inst_5 : Monad o] [inst_6 : MonadAttach o] [inst_7 : @LawfulMonad o inst_5]
      [inst_8 : @WeaklyLawfulMonadAttach o inst_5 inst_6] [inst_9 : MonadLiftT m n] [inst_10 : MonadLiftT n o]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_9] [inst : @LawfulMonadLiftT n o inst_2 inst_5 inst_10]
      [inst : Std.Iterator α m β] [inst_11 : @Std.Iterators.Finite α m β inst]
      {f : β → Std.Iterators.PostconditionT n (Option γ)} {g : γ → o (Option δ)} {it : @Std.IterM α m β},
      @Eq (o (List δ))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap
            (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_9 x) f) γ δ n o
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift n o inst_10 x) fun (b : γ) =>
            @Std.Iterators.PostconditionT.attachLift (Option δ) o inst_6 (g b))
          o inst_5 δ
          (@Std.Iterators.Types.FilterMap.instIterator
            (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_9 x) f) γ δ n o
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift n o inst_10 x)
            (fun (b : γ) => @Std.Iterators.PostconditionT.attachLift (Option δ) o inst_6 (g b))
            (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_9 x)
              f inst inst_2)
            inst_5)
          (@Std.IterM.filterMapM
            (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_9 x) f) γ δ n o
            (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_9 x)
              f inst inst_2)
            inst_5 inst_6 inst_10 g (@Std.IterM.filterMapWithPostcondition α β γ m n inst_9 inst f it)))
        (@Std.IterM.toList
          (@Std.Iterators.Types.FilterMap α β δ m o
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift m o
                (@instMonadLiftTOfMonadLift m n o
                  (@MonadLift.mk n o fun {α : Type w} => @MonadLiftT.monadLift n o inst_10 α) inst_9)
                x)
            fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option δ) o inst_6
              (@Bind.bind o (@Monad.toBind o inst_5) (Option γ) (Option δ)
                (@liftM n o inst_10 (Option γ) (@Std.Iterators.PostconditionT.run n inst_2 (Option γ) (f b)))
                fun (__do_lift : Option γ) =>
                @Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition.match_1 γ
                  (fun (__do_lift : Option γ) => o (Option δ)) __do_lift
                  (fun (_ : Unit) =>
                    @Pure.pure o (@Applicative.toPure o (@Monad.toApplicative o inst_5)) (Option δ) (@Option.none δ))
                  fun (fb : γ) => g fb))
          o inst_5 δ
          (@Std.Iterators.Types.FilterMap.instIterator α β δ m o
            (fun ⦃x : Type w⦄ =>
              @MonadLiftT.monadLift m o
                (@instMonadLiftTOfMonadLift m n o
                  (@MonadLift.mk n o fun {α : Type w} => @MonadLiftT.monadLift n o inst_10 α) inst_9)
                x)
            (fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (Option δ) o inst_6
                (@Bind.bind o (@Monad.toBind o inst_5) (Option γ) (Option δ)
                  (@liftM n o inst_10 (Option γ) (@Std.Iterators.PostconditionT.run n inst_2 (Option γ) (f b)))
                  fun (__do_lift : Option γ) =>
                  @Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition.match_1 γ
                    (fun (__do_lift : Option γ) => o (Option δ)) __do_lift
                    (fun (_ : Unit) =>
                      @Pure.pure o (@Applicative.toPure o (@Monad.toApplicative o inst_5)) (Option δ) (@Option.none δ))
                    fun (fb : γ) => g fb))
            inst inst_5)
          (@Std.IterM.filterMapM α β δ m o inst inst_5 inst_6
            (@instMonadLiftTOfMonadLift m n o (@MonadLift.mk n o fun {α : Type w} => @MonadLiftT.monadLift n o inst_10 α)
              inst_9)
            (fun (b : β) =>
              @Bind.bind o (@Monad.toBind o inst_5) (Option γ) (Option δ)
                (@liftM n o inst_10 (Option γ) (@Std.Iterators.PostconditionT.run n inst_2 (Option γ) (f b)))
                fun (__do_lift : Option γ) =>
                @Std.IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition.match_1 γ
                  (fun (__do_lift : Option γ) => o (Option δ)) __do_lift
                  (fun (_ : Unit) =>
                    @Pure.pure o (@Applicative.toPure o (@Monad.toApplicative o inst_5)) (Option δ) (@Option.none δ))
                  fun (fb : γ) => g fb)
            it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_filterMapM_filterMapWithPostcondition 12)

-- `Std.IterM.toList_flatMap` idx 11: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_flatMap.h11.{w, w'} :
    ∀ {α α₂ β γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : MonadAttach m] [inst_2 : @LawfulMonad m inst]
      [inst_3 : @WeaklyLawfulMonadAttach m inst inst_1] [inst_4 : Std.Iterator α m β] [inst_5 : Std.Iterator α₂ m γ]
      [inst_6 : @Std.Iterators.Finite α₂ m γ inst_5] [inst_7 : Std.Iterator α m β] [inst_8 : Std.Iterator α₂ m γ]
      [inst_9 : @Std.Iterators.Finite α m β inst_7] [inst_10 : @Std.Iterators.Finite α₂ m γ inst_8]
      {f : β → @Std.IterM α₂ m γ} {it₁ : @Std.IterM α m β},
      @Eq (m (List γ))
        (@Std.IterM.toList
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m)
          m inst γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_7
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            inst_8)
          (@Std.IterM.flatMap α β α₂ γ m inst inst_7 inst_8 f it₁))
        (@Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst)) (List (List γ)) (List γ) (@List.flatten γ)
          (@Std.IterM.toList
            (@Std.Iterators.Types.Map α β (List γ) m m (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (List γ) m inst_1 (@Std.IterM.toList α₂ m inst γ inst_8 (f b)))
            m inst (List γ)
            (@Std.Iterators.Types.Map.instIterator α β (List γ) m m inst inst_7
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (List γ) m inst_1 (@Std.IterM.toList α₂ m inst γ inst_8 (f b)))
            (@Std.IterM.mapM α β (List γ) m m inst_7 inst inst_1 (instMonadLiftT m)
              (fun (b : β) => @Std.IterM.toList α₂ m inst γ inst_8 (f b)) it₁))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_flatMap 11)

-- `Std.IterM.toList_flatMap` idx 12: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_flatMap.h12.{w, w'} :
    ∀ {α α₂ β γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : MonadAttach m] [inst_2 : @LawfulMonad m inst]
      [inst_3 : @WeaklyLawfulMonadAttach m inst inst_1] [inst_4 : Std.Iterator α m β] [inst_5 : Std.Iterator α₂ m γ]
      [inst_6 : @Std.Iterators.Finite α m β inst_4] [inst_7 : Std.Iterator α m β] [inst_8 : Std.Iterator α₂ m γ]
      [inst_9 : @Std.Iterators.Finite α m β inst_7] [inst_10 : @Std.Iterators.Finite α₂ m γ inst_8]
      {f : β → @Std.IterM α₂ m γ} {it₁ : @Std.IterM α m β},
      @Eq (m (List γ))
        (@Std.IterM.toList
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m)
          m inst γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_7
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            inst_8)
          (@Std.IterM.flatMap α β α₂ γ m inst inst_7 inst_8 f it₁))
        (@Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst)) (List (List γ)) (List γ) (@List.flatten γ)
          (@Std.IterM.toList
            (@Std.Iterators.Types.Map α β (List γ) m m (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (List γ) m inst_1 (@Std.IterM.toList α₂ m inst γ inst_8 (f b)))
            m inst (List γ)
            (@Std.Iterators.Types.Map.instIterator α β (List γ) m m inst inst_7
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (List γ) m inst_1 (@Std.IterM.toList α₂ m inst γ inst_8 (f b)))
            (@Std.IterM.mapM α β (List γ) m m inst_7 inst inst_1 (instMonadLiftT m)
              (fun (b : β) => @Std.IterM.toList α₂ m inst γ inst_8 (f b)) it₁))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_flatMap 12)

-- `Std.IterM.allM_filterMapM` idx 14: unused in the library's proof
theorem HypCheckProof.Std.IterM.allM_filterMapM.h14.{w, w', w''} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : Monad m]
      [inst_4 : @LawfulMonad m inst_3] [inst_5 : Monad n] [inst_6 : MonadAttach n] [inst_7 : @LawfulMonad n inst_5]
      [inst_8 : @WeaklyLawfulMonadAttach n inst_5 inst_6] {it : @Std.IterM α m β} {f : β → n (Option β')}
      {p : β' → n (ULift Bool)},
      @Eq (n (ULift Bool))
        (@Std.IterM.allM
          (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_6 (f b))
          β' n inst_5
          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_6 (f b)) inst inst_5)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β' m n n inst_5 inst_5 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_6 (f b))
          p (@Std.IterM.filterMapM α β β' m n inst inst_5 inst_6 inst_2 f it))
        (@Std.IterM.allM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_5)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_6
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_5)) β b))
          β n inst_5
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_5 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_6
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_5)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_5 inst_5 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_6
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_5)) β b))
          (fun (x : β) =>
            @Bind.bind n (@Monad.toBind n inst_5) (Option β') (ULift Bool) (f x) fun (__do_lift : Option β') =>
              @Std.IterM.forIn_filterMapWithPostcondition.match_1 β' (fun (__do_lift : Option β') => n (ULift Bool))
                __do_lift (fun (fx : β') => p fx) fun (_ : Unit) =>
                @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_5)) (ULift Bool)
                  (@ULift.up Bool Bool.true))
          (@Std.IterM.mapM α β β m n inst inst_5 inst_6 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_5)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.allM_filterMapM 14)

-- `Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition.h6.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : Monad n]
      [inst_2 : MonadAttach n] [inst_3 : @LawfulMonad n inst_1] [inst_4 : @WeaklyLawfulMonadAttach n inst_1 inst_2]
      [inst_5 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_1 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n (Option γ)} {it : @Std.IterM α m β},
      @Eq (n (Array γ))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b))
          γ n inst_1
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b)) inst inst_1)
          (@Std.IterM.filterMapM α β γ m n inst inst_1 inst_2 inst_5 f it))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b))
          γ n inst_1
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b)) inst inst_1)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_2 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition 6)

-- `Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition` idx 9: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition.h9.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @WeaklyLawfulMonadAttach n inst_2 inst_3]
      [inst_5 : MonadLiftT m n] [inst : @LawfulMonadLiftT m n inst inst_2 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n (Option γ)} {it : @Std.IterM α m β},
      @Eq (n (Array γ))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          γ n inst_2
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapM α β γ m n inst inst_2 inst_3 inst_5 f it))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          γ n inst_2
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition 9)

-- `Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition` idx 10: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition.h10.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @LawfulMonad n inst_2] [inst_5 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_5] [inst : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst] {f : β → n (Option γ)} {it : @Std.IterM α m β},
      @Eq (n (Array γ))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          γ n inst_2
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapM α β γ m n inst inst_2 inst_3 inst_5 f it))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          γ n inst_2
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_5 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_5 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition 10)

-- `Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition` idx 12: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition.h12.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst : @LawfulMonad m inst]
      [inst : Monad n] [inst_1 : MonadAttach n] [inst_2 : @LawfulMonad n inst]
      [inst_3 : @WeaklyLawfulMonadAttach n inst inst_1] [inst_4 : MonadLiftT m n] [inst_5 : Std.Iterator α m β]
      [inst_6 : @Std.Iterators.Finite α m β inst_5] {f : β → n (Option γ)} {it : @Std.IterM α m β},
      @Eq (n (Array γ))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b))
          γ n inst
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b)) inst_5 inst)
          (@Std.IterM.filterMapM α β γ m n inst_5 inst inst_1 inst_4 f it))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b))
          γ n inst
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_4 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b)) inst_5 inst)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_4 inst_5
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_1 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition 12)

-- `Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition` idx 14: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition.h14.{w, w', w''} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Monad m] [inst_1 : @LawfulMonad m inst]
      [inst_2 : Monad n] [inst_3 : MonadAttach n] [inst_4 : @LawfulMonad n inst_2]
      [inst_5 : @WeaklyLawfulMonadAttach n inst_2 inst_3] [inst_6 : MonadLiftT m n]
      [inst : @LawfulMonadLiftT m n inst inst_2 inst_6] [inst : Std.Iterator α m β] {f : β → n (Option γ)}
      {it : @Std.IterM α m β},
      @Eq (n (Array γ))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          γ n inst_2
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapM α β γ m n inst inst_2 inst_3 inst_6 f it))
        (@Std.IterM.toArray
          (@Std.Iterators.Types.FilterMap α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b))
          γ n inst_2
          (@Std.Iterators.Types.FilterMap.instIterator α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_6 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) inst inst_2)
          (@Std.IterM.filterMapWithPostcondition α β γ m n inst_6 inst
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option γ) n inst_3 (f b)) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_filterMapM_eq_toArray_filterMapWithPostcondition 14)

-- `Std.Ric.forIn'_eq_forIn'_rcc` idx 12: unused in the library's proof
theorem HypCheckProof.Std.Ric.forIn'_eq_forIn'_rcc.h12.{u, w} :
    ∀ {α : Type u} {r : Std.Ric α} [inst : LE α] [inst_1 : @DecidableLE α inst] [inst_2 : Std.PRange.Least? α]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : @Std.PRange.LawfulUpwardEnumerableLE α inst_3 inst]
      [inst_5 : @Std.PRange.LawfulUpwardEnumerableLeast? α inst_3 inst_2] [inst_6 : @Std.Rxc.IsAlwaysFinite α inst_3 inst]
      [inst_7 : @Std.PRange.LawfulUpwardEnumerable α inst_3] {m : Type u → Type w} [inst_8 : Monad m] {γ : Type u}
      {init : γ}
      {f :
        (a : α) →
          @Membership.mem α (Std.Ric α) (@inferInstance (Membership α (Std.Ric α)) (@Std.Ric.instMembershipOfLE α inst)) r
              a →
            γ → m (ForInStep γ)},
      @Eq (m γ)
        (@ForIn'.forIn' m (Std.Ric α) α (@inferInstance (Membership α (Std.Ric α)) (@Std.Ric.instMembershipOfLE α inst))
          (@Std.Ric.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLeast?OfMonadOfFiniteIteratorId
            α m inst_3 inst inst_1 inst_2 inst_7 inst_4 inst_5 inst_8
            (@Std.Rxc.Iterator.instFinite α inst_3 inst inst_1 inst_7 inst_6))
          γ r init f)
        (@ForIn'.forIn' m (Std.Rcc α) α (@Std.Rcc.instMembershipOfLE α inst)
          (@Std.Rcc.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfMonadOfFiniteIteratorId
            α m inst_3 inst inst_1 inst_7 inst_4 inst_8 (@Std.Rxc.Iterator.instFinite α inst_3 inst inst_1 inst_7 inst_6))
          γ
          (@Std.Rcc.mk α
            (@Std.PRange.UpwardEnumerable.least α inst_3 inst_2 inst_5 (@Nonempty.intro α (@Std.Ric.upper α r)))
            (@Std.Ric.upper α r))
          init
          fun (a : α)
            (ha :
              @Membership.mem α (Std.Rcc α) (@Std.Rcc.instMembershipOfLE α inst)
                (@Std.Rcc.mk α
                  (@Std.PRange.UpwardEnumerable.least α inst_3 inst_2 inst_5 (@Nonempty.intro α (@Std.Ric.upper α r)))
                  (@Std.Ric.upper α r))
                a)
            (acc : γ) =>
          f a
            (@Std.Ric.mem_of_mem_rcc α inst
              (@Std.PRange.UpwardEnumerable.least α inst_3 inst_2 inst_5 (@Nonempty.intro α (@Std.Ric.upper α r)))
              (@Std.Ric.upper α r) a ha)
            acc) :=
  no_implicit_lambda% (drop_unused% Std.Ric.forIn'_eq_forIn'_rcc 12)

-- `Std.IterM.anyM_mapM` idx 9: unused in the library's proof
theorem HypCheckProof.Std.IterM.anyM_mapM.h9.{w, w', w''} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : Monad m] [inst_4 : Monad n]
      [inst_5 : MonadAttach n] [inst_6 : @LawfulMonad n inst_4] [inst_7 : @WeaklyLawfulMonadAttach n inst_4 inst_5]
      {it : @Std.IterM α m β} {f : β → n β'} {p : β' → n (ULift Bool)},
      @Eq (n (ULift Bool))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.Map α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_4)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_5 (f b))
          β' n inst_4
          (@Std.Iterators.Types.Map.instIterator α β β' m n inst_4 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_5 (f b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β' m n n inst_4 inst_4 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β' n inst_5 (f b))
          p (@Std.IterM.mapM α β β' m n inst inst_4 inst_5 inst_2 f it))
        (@Std.IterM.anyM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_4)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_5
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_4)) β b))
          β n inst_4
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_4 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_5
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_4)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_4 inst_4 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_5
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_4)) β b))
          (fun (x : β) => @Bind.bind n (@Monad.toBind n inst_4) β' (ULift Bool) (f x) fun (__do_lift : β') => p __do_lift)
          (@Std.IterM.mapM α β β m n inst inst_4 inst_5 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_4)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.anyM_mapM 9)

-- `Std.Roc.mem_succ_succ_iff` idx 9: unused in the library's proof
theorem HypCheckProof.Std.Roc.mem_succ_succ_iff.h9.{u} :
    ∀ {α : Type u} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : LT α] [inst_3 : Std.PRange.UpwardEnumerable α]
      [inst_4 : Std.PRange.LinearlyUpwardEnumerable α] [inst_5 : Std.PRange.LawfulUpwardEnumerableLE α]
      [inst_6 : Std.PRange.LawfulUpwardEnumerableLT α] [inst_7 : Std.PRange.InfinitelyUpwardEnumerable α]
      [inst_8 : Std.PRange.LawfulUpwardEnumerable α] {lo hi a : α},
      a ∈ Std.PRange.UpwardEnumerable.succ lo<...=Std.PRange.UpwardEnumerable.succ hi ↔
        ∃ (a' : α), a = Std.PRange.UpwardEnumerable.succ a' ∧ a' ∈ lo<...=hi :=
  no_implicit_lambda% (drop_unused% Std.Roc.mem_succ_succ_iff 9)

-- `Lean.Grind.CommRing.lt_false_of_denote_eq` idx 5: unused in the library's proof
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_denote_eq.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
      (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
      Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Poly.denote ctx p →
        Lean.Grind.CommRing.Expr.denote ctx rhs = Lean.Grind.CommRing.Poly.denote ctx p →
          (Lean.Grind.CommRing.Expr.denote ctx lhs < Lean.Grind.CommRing.Expr.denote ctx rhs) = False :=
  no_implicit_lambda% (drop_unused% Lean.Grind.CommRing.lt_false_of_denote_eq 5)

-- `Lean.Grind.CommRing.lt_false_of_denoteS_eq` idx 5: unused in the library's proof
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_denoteS_eq.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Lean.Grind.CommSemiring α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
      (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
      Lean.Grind.CommRing.Expr.denoteS ctx lhs = Lean.Grind.CommRing.Poly.denoteS ctx p ∧ p.NonnegCoeffs →
        Lean.Grind.CommRing.Expr.denoteS ctx rhs = Lean.Grind.CommRing.Poly.denoteS ctx p ∧ p.NonnegCoeffs →
          (Lean.Grind.CommRing.Expr.denoteS ctx lhs < Lean.Grind.CommRing.Expr.denoteS ctx rhs) = False :=
  no_implicit_lambda% (drop_unused% Lean.Grind.CommRing.lt_false_of_denoteS_eq 5)

-- `Std.IterM.forM_eq_forIn` idx 4: unused in the library's proof
theorem HypCheckProof.Std.IterM.forM_eq_forIn.h4.{w, w', w''} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] {n : Type w → Type w''} [inst_1 : Monad m]
      [inst_2 : Monad n] [inst_3 : @LawfulMonad n inst_2] [inst_4 : @Std.IteratorLoop α m β inst n]
      [inst_5 : @Std.LawfulIteratorLoop β α m n inst_1 inst_2 inst inst_4] [inst_6 : MonadLiftT m n] {it : @Std.IterM α m β}
      {f : β → n PUnit},
      @Eq (n PUnit)
        (@ForM.forM n (@Std.IterM α m β) β (@Std.IterM.instForMOfIteratorLoop m n α β inst inst_4 inst_2 inst_6) it f)
        (@ForIn.forIn n (@Std.IterM α m β) β (@Std.IterM.instForInOfIteratorLoop m n α β inst inst_4 inst_6 inst_2) PUnit it
          PUnit.unit fun (out : β) (x : PUnit) =>
          @Bind.bind n (@Monad.toBind n inst_2) PUnit (ForInStep PUnit) (f out) fun (__r : PUnit) =>
            @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_2)) (ForInStep PUnit)
              (@ForInStep.yield PUnit PUnit.unit)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.forM_eq_forIn 4)

-- `Std.IterM.forM_eq_forIn` idx 8: unused in the library's proof
theorem HypCheckProof.Std.IterM.forM_eq_forIn.h8.{w, w', w''} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      {n : Type w → Type w''} [inst_2 : Monad m] [inst_3 : Monad n] [inst_4 : @Std.IteratorLoop α m β inst n]
      [inst_5 : @Std.LawfulIteratorLoop β α m n inst_2 inst_3 inst inst_4] [inst_6 : MonadLiftT m n] {it : @Std.IterM α m β}
      {f : β → n PUnit},
      @Eq (n PUnit)
        (@ForM.forM n (@Std.IterM α m β) β (@Std.IterM.instForMOfIteratorLoop m n α β inst inst_4 inst_3 inst_6) it f)
        (@ForIn.forIn n (@Std.IterM α m β) β (@Std.IterM.instForInOfIteratorLoop m n α β inst inst_4 inst_6 inst_3) PUnit it
          PUnit.unit fun (out : β) (x : PUnit) =>
          @Bind.bind n (@Monad.toBind n inst_3) PUnit (ForInStep PUnit) (f out) fun (__r : PUnit) =>
            @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_3)) (ForInStep PUnit)
              (@ForInStep.yield PUnit PUnit.unit)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.forM_eq_forIn 8)

-- `Std.IterM.forM_eq_forIn` idx 10: unused in the library's proof
theorem HypCheckProof.Std.IterM.forM_eq_forIn.h10.{w, w', w''} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      {n : Type w → Type w''} [inst_2 : Monad m] [inst_3 : Monad n] [inst_4 : @LawfulMonad n inst_3]
      [inst_5 : @Std.IteratorLoop α m β inst n] [inst_6 : MonadLiftT m n] {it : @Std.IterM α m β} {f : β → n PUnit},
      @Eq (n PUnit)
        (@ForM.forM n (@Std.IterM α m β) β (@Std.IterM.instForMOfIteratorLoop m n α β inst inst_5 inst_3 inst_6) it f)
        (@ForIn.forIn n (@Std.IterM α m β) β (@Std.IterM.instForInOfIteratorLoop m n α β inst inst_5 inst_6 inst_3) PUnit it
          PUnit.unit fun (out : β) (x : PUnit) =>
          @Bind.bind n (@Monad.toBind n inst_3) PUnit (ForInStep PUnit) (f out) fun (__r : PUnit) =>
            @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_3)) (ForInStep PUnit)
              (@ForInStep.yield PUnit PUnit.unit)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.forM_eq_forIn 10)

-- `Std.Rio.succ_mem_succ_iff` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Rio.succ_mem_succ_iff.h7.{u} :
    ∀ {α : Type u} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LinearlyUpwardEnumerable α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLT α]
      [inst_5 : Std.PRange.InfinitelyUpwardEnumerable α] [inst_6 : Std.PRange.LawfulUpwardEnumerable α] {hi a : α},
      Std.PRange.UpwardEnumerable.succ a ∈ *...Std.PRange.UpwardEnumerable.succ hi ↔ a ∈ *...hi :=
  no_implicit_lambda% (drop_unused% Std.Rio.succ_mem_succ_iff 7)

-- `Std.IterM.forIn_pure_yield_eq_fold` idx 7: unused in the library's proof
theorem HypCheckProof.Std.IterM.forIn_pure_yield_eq_fold.h7.{w, w'} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      [inst_2 : Monad m] [inst_3 : @Std.IteratorLoop α m β inst m]
      [inst_4 : @Std.LawfulIteratorLoop β α m m inst_2 inst_2 inst inst_3] {f : β → γ → γ} {init : γ}
      {it : @Std.IterM α m β},
      @Eq (m γ)
        (@ForIn.forIn m (@Std.IterM α m β) β
          (@Std.IterM.instForInOfIteratorLoop m m α β inst inst_3 (instMonadLiftT m) inst_2) γ it init
          fun (c : β) (b : γ) =>
          @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep γ) (@ForInStep.yield γ (f c b)))
        (@Std.IterM.fold m α β γ inst_2 inst inst_3 (fun (b : γ) (c : β) => f c b) init it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.forIn_pure_yield_eq_fold 7)

-- `Std.IterM.forIn_pure_yield_eq_fold` idx 9: unused in the library's proof
theorem HypCheckProof.Std.IterM.forIn_pure_yield_eq_fold.h9.{w, w'} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      [inst_2 : Monad m] [inst_3 : @LawfulMonad m inst_2] [inst_4 : @Std.IteratorLoop α m β inst m] {f : β → γ → γ}
      {init : γ} {it : @Std.IterM α m β},
      @Eq (m γ)
        (@ForIn.forIn m (@Std.IterM α m β) β
          (@Std.IterM.instForInOfIteratorLoop m m α β inst inst_4 (instMonadLiftT m) inst_2) γ it init
          fun (c : β) (b : γ) =>
          @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ForInStep γ) (@ForInStep.yield γ (f c b)))
        (@Std.IterM.fold m α β γ inst_2 inst inst_4 (fun (b : γ) (c : β) => f c b) init it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.forIn_pure_yield_eq_fold 9)

-- `Std.Ric.mem_iff_mem_rcc` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Ric.mem_iff_mem_rcc.h5.{u} :
    ∀ {α : Type u} {r : Std.Ric α} [inst : LE α] [inst_1 : Std.PRange.Least? α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : @Std.PRange.LawfulUpwardEnumerableLE α inst_2 inst]
      [inst_4 : @Std.PRange.LawfulUpwardEnumerableLeast? α inst_2 inst_1] [inst_5 : @Std.Rxc.IsAlwaysFinite α inst_2 inst]
      {a : α},
      Iff (@Membership.mem α (Std.Ric α) (@Std.Ric.instMembershipOfLE α inst) r a)
        (@Membership.mem α (Std.Rcc α) (@Std.Rcc.instMembershipOfLE α inst)
          (@Std.Rcc.mk α
            (@Std.PRange.UpwardEnumerable.least α inst_2 inst_1 inst_4 (@Nonempty.intro α (@Std.Ric.upper α r)))
            (@Std.Ric.upper α r))
          a) :=
  no_implicit_lambda% (drop_unused% Std.Ric.mem_iff_mem_rcc 5)

-- `Std.Ric.mem_iff_mem_rcc` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Ric.mem_iff_mem_rcc.h8.{u} :
    ∀ {α : Type u} {r : Std.Ric α} [inst : LE α] [inst_1 : Std.PRange.Least? α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : @Std.PRange.LawfulUpwardEnumerable α inst_2] [inst_4 : @Std.PRange.LawfulUpwardEnumerableLE α inst_2 inst]
      [inst_5 : @Std.PRange.LawfulUpwardEnumerableLeast? α inst_2 inst_1] {a : α},
      Iff (@Membership.mem α (Std.Ric α) (@Std.Ric.instMembershipOfLE α inst) r a)
        (@Membership.mem α (Std.Rcc α) (@Std.Rcc.instMembershipOfLE α inst)
          (@Std.Rcc.mk α
            (@Std.PRange.UpwardEnumerable.least α inst_2 inst_1 inst_5 (@Nonempty.intro α (@Std.Ric.upper α r)))
            (@Std.Ric.upper α r))
          a) :=
  no_implicit_lambda% (drop_unused% Std.Ric.mem_iff_mem_rcc 8)

-- `Std.Roo.isEmpty_iff_forall_not_mem` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Roo.isEmpty_iff_forall_not_mem.h6.{u} :
    ∀ {α : Type u} {r : Std.Roo α} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLT α] [inst_5 : Std.Rxo.IsAlwaysFinite α]
      [inst_6 : Std.PRange.LawfulUpwardEnumerable α], r.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Roo.isEmpty_iff_forall_not_mem 6)

-- `Std.Roo.isEmpty_iff_forall_not_mem` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Roo.isEmpty_iff_forall_not_mem.h8.{u} :
    ∀ {α : Type u} {r : Std.Roo α} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxo.HasSize α] [inst_4 : Std.Rxo.LawfulHasSize α] [inst_5 : Std.PRange.LawfulUpwardEnumerableLT α]
      [inst_6 : Std.PRange.LawfulUpwardEnumerable α], r.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Roo.isEmpty_iff_forall_not_mem 8)

-- `Std.IterM.foldM_mapWithPostcondition` idx 17: unused in the library's proof
theorem HypCheckProof.Std.IterM.foldM_mapWithPostcondition.h17.{w, w', w'', w'''} :
    ∀ {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : Monad m] [inst_3 : Monad n] [inst_4 : Monad o]
      [inst_5 : @LawfulMonad m inst_2] [inst_6 : @LawfulMonad n inst_3] [inst_7 : @LawfulMonad o inst_4]
      [inst_8 : @Std.IteratorLoop α m β inst n] [inst_9 : @Std.IteratorLoop α m β inst o]
      [inst_10 : @Std.LawfulIteratorLoop β α m o inst_2 inst_4 inst inst_9] [inst_11 : MonadLiftT m n]
      [inst_12 : MonadLiftT n o] [inst_13 : @LawfulMonadLiftT m n inst_2 inst_3 inst_11]
      [inst_14 : @LawfulMonadLiftT n o inst_3 inst_4 inst_12] {f : β → Std.Iterators.PostconditionT n γ} {g : δ → γ → o δ}
      {init : δ} {it : @Std.IterM α m β},
      @Eq (o δ)
        (@Std.IterM.foldM n o inst_4
          (@Std.Iterators.Types.Map α β γ m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_11 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_3)) f)
          γ δ
          (@Std.Iterators.Types.Map.instIterator α β γ m n inst_3 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_11 x) f)
          (@Std.Iterators.Types.Map.instIteratorLoop α β γ m n o inst_3 inst_4 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_11 x) f)
          inst_12 g init (@Std.IterM.mapWithPostcondition α β γ m n inst_3 inst_11 inst f it))
        (@Std.IterM.foldM m o inst_4 α β δ inst inst_9
          (@instMonadLiftTOfMonadLift m n o (@MonadLift.mk n o fun {α : Type w} => @MonadLiftT.monadLift n o inst_12 α)
            inst_11)
          (fun (d : δ) (b : β) =>
            @Bind.bind o (@Monad.toBind o inst_4) γ δ
              (@liftM n o inst_12 γ (@Std.Iterators.PostconditionT.run n inst_3 γ (f b))) fun (c : γ) => g d c)
          init it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.foldM_mapWithPostcondition 17)

-- `Lean.Grind.Order.le_trans_k` idx 3: unused in the library's proof
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h3.{u_1} :
    ∀ {α : Type u_1} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.IsPreorder α inst] [inst_3 : Lean.Grind.Ring α]
      [inst_4 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_3) inst inst_1 inst_2] {a b c : α}
      {k₁ k₂ : Int} (k : Int),
      @LE.le α inst a
          (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) b
            (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₁)) →
        @LE.le α inst b
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) c
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₂)) →
          @Eq Bool
              (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k
                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁))
              Bool.true →
            @LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k)) :=
  no_implicit_lambda% (drop_unused% Lean.Grind.Order.le_trans_k 3)

-- `Std.IterM.allM_filterM` idx 13: unused in the library's proof
theorem HypCheckProof.Std.IterM.allM_filterM.h13.{w, w', w''} :
    ∀ {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β]
      [inst_1 : @Std.Iterators.Finite α m β inst] [inst_2 : MonadLiftT m n] [inst_3 : Monad m]
      [inst_4 : @LawfulMonad m inst_3] [inst_5 : Monad n] [inst_6 : MonadAttach n] [inst_7 : @LawfulMonad n inst_5]
      [inst_8 : @WeaklyLawfulMonadAttach n inst_5 inst_6] {it : @Std.IterM α m β} {f p : β → n (ULift Bool)},
      @Eq (n (ULift Bool))
        (@Std.IterM.allM
          (@Std.Iterators.Types.FilterMap α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_5)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_6 (f b)))
          β n inst_5
          (@Std.Iterators.Types.FilterMap.instIterator α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (fun (b : β) =>
              @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_5)) (ULift Bool)
                (Option β)
                (fun (x : ULift Bool) =>
                  @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                    (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
                (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_6 (f b)))
            inst inst_5)
          (@Std.Iterators.Types.FilterMap.instIteratorLoop α β β m n n inst_5 inst_5 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.map n (@Applicative.toFunctor n (@Monad.toApplicative n inst_5)) (ULift Bool)
              (Option β)
              (fun (x : ULift Bool) =>
                @ite (Option β) (@Eq Bool (@ULift.down Bool x) Bool.true)
                  (instDecidableEqBool (@ULift.down Bool x) Bool.true) (@Option.some β b) (@Option.none β))
              (@Std.Iterators.PostconditionT.attachLift (ULift Bool) n inst_6 (f b)))
          p (@Std.IterM.filterM α β m n inst inst_5 inst_6 inst_2 f it))
        (@Std.IterM.allM
          (@Std.Iterators.Types.Map α β β m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
            (@Applicative.toFunctor n (@Monad.toApplicative n inst_5)) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_6
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_5)) β b))
          β n inst_5
          (@Std.Iterators.Types.Map.instIterator α β β m n inst_5 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_6
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_5)) β b))
          (@Std.Iterators.Types.Map.instIteratorLoop α β β m n n inst_5 inst_5 inst
            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift β n inst_6
              (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_5)) β b))
          (fun (x : β) =>
            @Bind.bind n (@Monad.toBind n inst_5) (ULift Bool) (ULift Bool) (f x) fun (__do_lift : ULift Bool) =>
              @ite (n (ULift Bool)) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
                (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true) (p x)
                (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_5)) (ULift Bool)
                  (@ULift.up Bool Bool.true)))
          (@Std.IterM.mapM α β β m n inst inst_5 inst_6 inst_2
            (@Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_5)) β) it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.allM_filterM 13)

-- `Lean.Grind.CommRing.lt_false_of_toPPX_eq` idx 5: unused in the library's proof
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h5.{u_1} :
    ∀ {α : Type u_1} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
      (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr)
      (p : Lean.Grind.CommRing.PPoly),
      Lean.Grind.CommRing.Expr.degOk_k B a b = Bool.true →
        p = Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a →
          p = Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b →
            (Lean.Grind.CommRing.Expr.denote ctx a < Lean.Grind.CommRing.Expr.denote ctx b) = False :=
  no_implicit_lambda% (drop_unused% Lean.Grind.CommRing.lt_false_of_toPPX_eq 5)

-- `Std.Ric.succ_mem_succ_iff` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Ric.succ_mem_succ_iff.h7.{u} :
    ∀ {α : Type u} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.PRange.LinearlyUpwardEnumerable α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLE α]
      [inst_5 : Std.PRange.InfinitelyUpwardEnumerable α] [inst_6 : Std.PRange.LawfulUpwardEnumerable α] {hi a : α},
      Std.PRange.UpwardEnumerable.succ a ∈ *...=Std.PRange.UpwardEnumerable.succ hi ↔ a ∈ *...=hi :=
  no_implicit_lambda% (drop_unused% Std.Ric.succ_mem_succ_iff 7)

-- `Std.Ric.size_eq_match_rcc` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Ric.size_eq_match_rcc.h7.{u} :
    ∀ {α : Type u} {r : Std.Ric α} [inst : Std.PRange.Least? α] [inst_1 : LE α] [inst_2 : @DecidableLE α inst_1]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxc.HasSize α]
      [inst_5 : @Std.PRange.LawfulUpwardEnumerableLE α inst_3 inst_1] [inst_6 : @Std.Rxc.IsAlwaysFinite α inst_3 inst_1]
      [inst_7 : @Std.Rxc.LawfulHasSize α inst_1 inst_3 inst_4],
      @Eq Nat (@Std.Ric.size α inst_4 inst r)
        (@Std.Rxc.Iterator.toList_eq_match.match_1 α (fun (x : Option α) => Nat) (@Std.PRange.Least?.least? α inst)
          (fun (_ : Unit) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun (next : α) =>
          @Std.Rcc.size α inst_4 (@Std.Rcc.mk α next (@Std.Ric.upper α r))) :=
  no_implicit_lambda% (drop_unused% Std.Ric.size_eq_match_rcc 7)

-- `Std.Ric.size_eq_match_rcc` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Ric.size_eq_match_rcc.h8.{u} :
    ∀ {α : Type u} {r : Std.Ric α} [inst : Std.PRange.Least? α] [inst_1 : LE α] [inst_2 : @DecidableLE α inst_1]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxc.HasSize α]
      [inst_5 : @Std.PRange.LawfulUpwardEnumerable α inst_3] [inst_6 : @Std.Rxc.IsAlwaysFinite α inst_3 inst_1]
      [inst_7 : @Std.Rxc.LawfulHasSize α inst_1 inst_3 inst_4],
      @Eq Nat (@Std.Ric.size α inst_4 inst r)
        (@Std.Rxc.Iterator.toList_eq_match.match_1 α (fun (x : Option α) => Nat) (@Std.PRange.Least?.least? α inst)
          (fun (_ : Unit) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun (next : α) =>
          @Std.Rcc.size α inst_4 (@Std.Rcc.mk α next (@Std.Ric.upper α r))) :=
  no_implicit_lambda% (drop_unused% Std.Ric.size_eq_match_rcc 8)

-- `Std.Ric.size_eq_match_rcc` idx 9: unused in the library's proof
theorem HypCheckProof.Std.Ric.size_eq_match_rcc.h9.{u} :
    ∀ {α : Type u} {r : Std.Ric α} [inst : Std.PRange.Least? α] [inst_1 : LE α] [inst_2 : @DecidableLE α inst_1]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxc.HasSize α]
      [inst_5 : @Std.PRange.LawfulUpwardEnumerable α inst_3] [inst_6 : @Std.PRange.LawfulUpwardEnumerableLE α inst_3 inst_1]
      [inst_7 : @Std.Rxc.LawfulHasSize α inst_1 inst_3 inst_4],
      @Eq Nat (@Std.Ric.size α inst_4 inst r)
        (@Std.Rxc.Iterator.toList_eq_match.match_1 α (fun (x : Option α) => Nat) (@Std.PRange.Least?.least? α inst)
          (fun (_ : Unit) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun (next : α) =>
          @Std.Rcc.size α inst_4 (@Std.Rcc.mk α next (@Std.Ric.upper α r))) :=
  no_implicit_lambda% (drop_unused% Std.Ric.size_eq_match_rcc 9)

-- `Std.Ric.size_eq_match_rcc` idx 10: unused in the library's proof
theorem HypCheckProof.Std.Ric.size_eq_match_rcc.h10.{u} :
    ∀ {α : Type u} {r : Std.Ric α} [inst : Std.PRange.Least? α] [inst_1 : LE α] [inst_2 : @DecidableLE α inst_1]
      [inst_3 : Std.PRange.UpwardEnumerable α] [inst_4 : Std.Rxc.HasSize α]
      [inst_5 : @Std.PRange.LawfulUpwardEnumerable α inst_3] [inst_6 : @Std.PRange.LawfulUpwardEnumerableLE α inst_3 inst_1]
      [inst_7 : @Std.Rxc.IsAlwaysFinite α inst_3 inst_1],
      @Eq Nat (@Std.Ric.size α inst_4 inst r)
        (@Std.Rxc.Iterator.toList_eq_match.match_1 α (fun (x : Option α) => Nat) (@Std.PRange.Least?.least? α inst)
          (fun (_ : Unit) => @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun (next : α) =>
          @Std.Rcc.size α inst_4 (@Std.Rcc.mk α next (@Std.Ric.upper α r))) :=
  no_implicit_lambda% (drop_unused% Std.Ric.size_eq_match_rcc 10)

-- `Lean.Grind.Order.le_of_offset_eq_2_k` idx 3: unused in the library's proof
theorem HypCheckProof.Lean.Grind.Order.le_of_offset_eq_2_k.h3.{u_1} :
    ∀ {α : Type u_1} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.IsPreorder α inst] [inst_3 : Lean.Grind.Ring α]
      [inst_4 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_3) inst inst_1 inst_2] {a b : α} {k : Int},
      @Eq α a
          (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) b
            (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k)) →
        @LE.le α inst b
          (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) a
            (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) (@Neg.neg Int Int.instNegInt k))) :=
  no_implicit_lambda% (drop_unused% Lean.Grind.Order.le_of_offset_eq_2_k 3)

-- `Lean.Grind.Order.le_of_offset_eq_2_k` idx 6: unused in the library's proof
theorem HypCheckProof.Lean.Grind.Order.le_of_offset_eq_2_k.h6.{u_1} :
    ∀ {α : Type u_1} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
      [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α] {a b : α} {k : Int},
      @Eq α a
          (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
            (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k)) →
        @LE.le α inst b
          (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
            (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) (@Neg.neg Int Int.instNegInt k))) :=
  no_implicit_lambda% (drop_unused% Lean.Grind.Order.le_of_offset_eq_2_k 6)

-- `Std.Rci.isSome_succMany?_of_lt_length_toList` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Rci.isSome_succMany?_of_lt_length_toList.h6.{u} :
    ∀ {α : Type u} {r : Std.Rci α} [inst : LT α] [inst : DecidableLT α] [inst : Std.PRange.UpwardEnumerable α]
      [inst_1 : Std.PRange.LawfulUpwardEnumerable α] [inst_2 : Std.Rxi.IsAlwaysFinite α] {i : Nat},
      i < r.toList.length → (Std.PRange.UpwardEnumerable.succMany? i r.lower).isSome = Bool.true :=
  no_implicit_lambda% (drop_unused% Std.Rci.isSome_succMany?_of_lt_length_toList 6)

-- `Std.Roc.size_eq_match_rcc` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Roc.size_eq_match_rcc.h6.{u} :
    ∀ {α : Type u} {r : Std.Roc α} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLE α] [inst_5 : Std.Rxc.IsAlwaysFinite α]
      [inst : Std.Rxc.LawfulHasSize α],
      r.size =
        match Std.PRange.UpwardEnumerable.succ? r.lower with
        | Option.none => 0
        | Option.some next => (next...=r.upper).size :=
  no_implicit_lambda% (drop_unused% Std.Roc.size_eq_match_rcc 6)

-- `Std.Roc.size_eq_match_rcc` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Roc.size_eq_match_rcc.h7.{u} :
    ∀ {α : Type u} {r : Std.Roc α} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α] [inst_5 : Std.Rxc.IsAlwaysFinite α]
      [inst : Std.Rxc.LawfulHasSize α],
      r.size =
        match Std.PRange.UpwardEnumerable.succ? r.lower with
        | Option.none => 0
        | Option.some next => (next...=r.upper).size :=
  no_implicit_lambda% (drop_unused% Std.Roc.size_eq_match_rcc 7)

-- `Std.Roc.size_eq_match_rcc` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Roc.size_eq_match_rcc.h8.{u} :
    ∀ {α : Type u} {r : Std.Roc α} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerableLE α] [inst : Std.Rxc.LawfulHasSize α],
      r.size =
        match Std.PRange.UpwardEnumerable.succ? r.lower with
        | Option.none => 0
        | Option.some next => (next...=r.upper).size :=
  no_implicit_lambda% (drop_unused% Std.Roc.size_eq_match_rcc 8)

-- `Std.Roc.size_eq_match_rcc` idx 9: unused in the library's proof
theorem HypCheckProof.Std.Roc.size_eq_match_rcc.h9.{u} :
    ∀ {α : Type u} {r : Std.Roc α} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerable α]
      [inst_5 : Std.PRange.LawfulUpwardEnumerableLE α] [inst : Std.Rxc.IsAlwaysFinite α],
      r.size =
        match Std.PRange.UpwardEnumerable.succ? r.lower with
        | Option.none => 0
        | Option.some next => (next...=r.upper).size :=
  no_implicit_lambda% (drop_unused% Std.Roc.size_eq_match_rcc 9)

-- `Std.Rcc.isEmpty_iff_forall_not_mem` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Rcc.isEmpty_iff_forall_not_mem.h6.{u} :
    ∀ {α : Type u} {r : Std.Rcc α} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.HasSize α] [inst_4 : Std.PRange.LawfulUpwardEnumerableLE α] [inst_5 : Std.Rxc.IsAlwaysFinite α]
      [inst_6 : Std.PRange.LawfulUpwardEnumerable α], r.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Rcc.isEmpty_iff_forall_not_mem 6)

-- `Std.Rcc.isEmpty_iff_forall_not_mem` idx 8: unused in the library's proof
theorem HypCheckProof.Std.Rcc.isEmpty_iff_forall_not_mem.h8.{u} :
    ∀ {α : Type u} {r : Std.Rcc α} [inst : LE α] [inst_1 : DecidableLE α] [inst_2 : Std.PRange.UpwardEnumerable α]
      [inst_3 : Std.Rxc.HasSize α] [inst_4 : Std.Rxc.LawfulHasSize α] [inst_5 : Std.PRange.LawfulUpwardEnumerableLE α]
      [inst_6 : Std.PRange.LawfulUpwardEnumerable α], r.isEmpty = Bool.true ↔ ∀ (a : α), ¬a ∈ r :=
  no_implicit_lambda% (drop_unused% Std.Rcc.isEmpty_iff_forall_not_mem 8)

-- `Std.IterM.all_eq_allM` idx 4: unused in the library's proof
theorem HypCheckProof.Std.IterM.all_eq_allM.h4.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : Monad m] [inst_2 : @LawfulMonad m inst_1]
      [inst_3 : @Std.IteratorLoop α m β inst m] [inst_4 : @Std.LawfulIteratorLoop β α m m inst_1 inst_1 inst inst_3]
      {it : @Std.IterM α m β} {p : β → Bool},
      @Eq (m (ULift Bool)) (@Std.IterM.all α β m inst_1 inst inst_3 p it)
        (@Std.IterM.allM α β m inst_1 inst inst_3
          (fun (x : β) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_1)) (ULift Bool) (@ULift.up Bool (p x)))
          it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.all_eq_allM 4)

-- `Std.IterM.all_eq_allM` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.all_eq_allM.h6.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      [inst_2 : Monad m] [inst_3 : @Std.IteratorLoop α m β inst m]
      [inst_4 : @Std.LawfulIteratorLoop β α m m inst_2 inst_2 inst inst_3] {it : @Std.IterM α m β} {p : β → Bool},
      @Eq (m (ULift Bool)) (@Std.IterM.all α β m inst_2 inst inst_3 p it)
        (@Std.IterM.allM α β m inst_2 inst inst_3
          (fun (x : β) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ULift Bool) (@ULift.up Bool (p x)))
          it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.all_eq_allM 6)

-- `Std.IterM.all_eq_allM` idx 8: unused in the library's proof
theorem HypCheckProof.Std.IterM.all_eq_allM.h8.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : @Std.Iterators.Finite α m β inst]
      [inst_2 : Monad m] [inst_3 : @LawfulMonad m inst_2] [inst_4 : @Std.IteratorLoop α m β inst m] {it : @Std.IterM α m β}
      {p : β → Bool},
      @Eq (m (ULift Bool)) (@Std.IterM.all α β m inst_2 inst inst_4 p it)
        (@Std.IterM.allM α β m inst_2 inst inst_4
          (fun (x : β) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_2)) (ULift Bool) (@ULift.up Bool (p x)))
          it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.all_eq_allM 8)

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMap` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMap.h6.{w, w'} :
    ∀ {α β α₂ γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : Std.Iterator α m β]
      [inst_2 : Std.Iterator α₂ m γ] {f : β → @Std.IterM α₂ m γ} {it₁ : @Std.IterM α m β} {it₂ it₂' : @Std.IterM α₂ m γ},
      @Std.IterM.IsPlausibleStep α₂ m γ inst_2 it₂ (@Std.IterStep.skip (@Std.IterM α₂ m γ) γ it₂') →
        @Std.IterM.IsPlausibleStep
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m)
          m γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_1
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            inst_2)
          (@Std.IterM.flatMapAfter α β α₂ γ m inst inst_1 inst_2 f it₁ (@Option.some (@Std.IterM α₂ m γ) it₂))
          (@Std.IterStep.skip
            (@Std.IterM
              (Std.Iterators.Types.Flatten
                (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                  (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                  @Pure.pure (Std.Iterators.PostconditionT m)
                    (@Applicative.toPure (Std.Iterators.PostconditionT m)
                      (@Monad.toApplicative (Std.Iterators.PostconditionT m)
                        (@Std.Iterators.instMonadPostconditionT m inst)))
                    (@Std.IterM α₂ m γ) (f b))
                α₂ γ m)
              m γ)
            γ (@Std.IterM.flatMapAfter α β α₂ γ m inst inst_1 inst_2 f it₁ (@Option.some (@Std.IterM α₂ m γ) it₂'))) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.Types.Flatten.IsPlausibleStep.innerSkip_flatMap 6)

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMap` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMap.h6.{w, w'} :
    ∀ {α β α₂ γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : Std.Iterator α m β]
      [inst_2 : Std.Iterator α₂ m γ] {f : β → @Std.IterM α₂ m γ} {it₁ it₁' : @Std.IterM α m β} {b : β},
      @Std.IterM.IsPlausibleStep α m β inst_1 it₁ (@Std.IterStep.yield (@Std.IterM α m β) β it₁' b) →
        @Std.IterM.IsPlausibleStep
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m)
          m γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_1
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Pure.pure (Std.Iterators.PostconditionT m)
                (@Applicative.toPure (Std.Iterators.PostconditionT m)
                  (@Monad.toApplicative (Std.Iterators.PostconditionT m) (@Std.Iterators.instMonadPostconditionT m inst)))
                (@Std.IterM α₂ m γ) (f b))
            inst_2)
          (@Std.IterM.flatMapAfter α β α₂ γ m inst inst_1 inst_2 f it₁ (@Option.none (@Std.IterM α₂ m γ)))
          (@Std.IterStep.skip
            (@Std.IterM
              (Std.Iterators.Types.Flatten
                (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                  (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                  @Pure.pure (Std.Iterators.PostconditionT m)
                    (@Applicative.toPure (Std.Iterators.PostconditionT m)
                      (@Monad.toApplicative (Std.Iterators.PostconditionT m)
                        (@Std.Iterators.instMonadPostconditionT m inst)))
                    (@Std.IterM α₂ m γ) (f b))
                α₂ γ m)
              m γ)
            γ (@Std.IterM.flatMapAfter α β α₂ γ m inst inst_1 inst_2 f it₁' (@Option.some (@Std.IterM α₂ m γ) (f b)))) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMap 6)

-- `Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMapM` idx 7: unused in the library's proof
theorem HypCheckProof.Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMapM.h7.{w, w'} :
    ∀ {α β α₂ γ : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : MonadAttach m] [inst_2 : Std.Iterator α m β]
      [inst_3 : Std.Iterator α₂ m γ] {f : β → m (@Std.IterM α₂ m γ)} {it₁ it₁' : @Std.IterM α m β},
      @Std.IterM.IsPlausibleStep α m β inst_2 it₁ (@Std.IterStep.skip (@Std.IterM α m β) β it₁') →
        @Std.IterM.IsPlausibleStep
          (Std.Iterators.Types.Flatten
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            α₂ γ m)
          m γ
          (@Std.Iterators.Types.Flatten.instIterator
            (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
              (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            α₂ γ m inst
            (@Std.Iterators.Types.Map.instIterator α β (@Std.IterM α₂ m γ) m m inst inst_2
              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x) fun (b : β) =>
              @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
            inst_3)
          (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_2 inst_3 f it₁ (@Option.none (@Std.IterM α₂ m γ)))
          (@Std.IterStep.skip
            (@Std.IterM
              (Std.Iterators.Types.Flatten
                (@Std.Iterators.Types.Map α β (@Std.IterM α₂ m γ) m m
                  (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m m (instMonadLiftT m) x)
                  (@Applicative.toFunctor m (@Monad.toApplicative m inst)) fun (b : β) =>
                  @Std.Iterators.PostconditionT.attachLift (@Std.IterM α₂ m γ) m inst_1 (f b))
                α₂ γ m)
              m γ)
            γ (@Std.IterM.flatMapAfterM α β α₂ γ m inst inst_1 inst_2 inst_3 f it₁' (@Option.none (@Std.IterM α₂ m γ)))) :=
  no_implicit_lambda% (drop_unused% Std.Iterators.Types.Flatten.IsPlausibleStep.outerSkip_flatMapM 7)

-- `Std.Iter.fold_eq_forIn` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Iter.fold_eq_forIn.h4.{w, x} :
    ∀ {α β : Type w} {γ : Type x} [inst : Std.Iterator α Id β] [inst_1 : @Std.IteratorLoop α Id β inst Id] {f : γ → β → γ}
      {init : γ} {it : @Std.Iter α β},
      @Eq γ (@Std.Iter.fold α β γ inst inst_1 f init it)
        (@Id.run γ
          (@ForIn.forIn Id (@Std.Iter α β) β (@Std.instForInIterOfMonadOfIteratorLoopId α β Id Id.instMonad inst inst_1) γ
            it init fun (x : β) (acc : γ) =>
            @Pure.pure Id (@Applicative.toPure Id (@Monad.toApplicative Id Id.instMonad)) (ForInStep γ)
              (@ForInStep.yield γ (f acc x)))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.fold_eq_forIn 4)

-- `Std.IterM.find?_eq_findM?` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.find?_eq_findM?.h6.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : Std.Iterator α m β]
      [inst_2 : @Std.IteratorLoop α m β inst_1 m] {it : @Std.IterM α m β} {f : β → Bool},
      @Eq (m (Option β)) (@Std.IterM.find? α β m inst inst_1 inst_2 it f)
        (@Std.IterM.findM? α β m inst inst_1 inst_2 it fun (x : β) =>
          @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (ULift Bool) (@ULift.up Bool (f x))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.find?_eq_findM? 6)

-- `Std.Iter.findSome?_eq_findSomeM?` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Iter.findSome?_eq_findSomeM?.h5.{w, x} :
    ∀ {α β : Type w} {γ : Type x} [inst : Std.Iterator α Id β] [inst_1 : @Std.IteratorLoop α Id β inst Id]
      {it : @Std.Iter α β} {f : β → Option γ},
      @Eq (Option γ) (@Std.Iter.findSome? α β γ inst inst_1 it f)
        (@Id.run (Option γ)
          (@Std.Iter.findSomeM? α β γ Id Id.instMonad inst inst_1 it fun (x : β) =>
            @Pure.pure Id (@Applicative.toPure Id (@Monad.toApplicative Id Id.instMonad)) (Option γ) (f x))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.findSome?_eq_findSomeM? 5)

-- `Array.flatMapM_wfParam` idx 4: unused in the library's proof
theorem HypCheckProof.Array.flatMapM_wfParam.h4.{u_1, u_2, u_3} :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {xs : Array α} {f : α → m (Array β)},
      Array.flatMapM f (wfParam xs) = Array.flatMapM f xs.attach.unattach :=
  no_implicit_lambda% (drop_unused% Array.flatMapM_wfParam 4)

-- `Std.Iter.find?_eq_find?_toIterM` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Iter.find?_eq_find?_toIterM.h4.{w} :
    ∀ {α β : Type w} [inst : Std.Iterator α Id β] [inst_1 : @Std.IteratorLoop α Id β inst Id] {it : @Std.Iter α β}
      {f : β → Bool},
      @Eq (Option β) (@Std.Iter.find? α β inst inst_1 it f)
        (@Id.run (Option β) (@Std.IterM.find? α β Id Id.instMonad inst inst_1 (@Std.Iter.toIterM α β it) f)) :=
  no_implicit_lambda% (drop_unused% Std.Iter.find?_eq_find?_toIterM 4)

-- `List.minOn?_eq_ite` idx 4: unused in the library's proof
theorem HypCheckProof.List.minOn?_eq_ite.h4.{u_1, u_2} :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {xs : List α},
      List.minOn? f xs = if h : xs ≠ [] then Option.some (List.minOn f xs h) else Option.none :=
  no_implicit_lambda% (drop_unused% List.minOn?_eq_ite 4)

-- `Std.Slice.Internal.toList_eq_toList_iter` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Slice.Internal.toList_eq_toList_iter.h6.{u, v} :
    ∀ {γ : Type u} {α β : Type v} {s : Std.Slice γ} [inst : Std.ToIterator (Std.Slice γ) Id α β]
      [inst_1 : Std.Iterator α Id β], s.toList = (Std.Slice.Internal.iter s).toList :=
  no_implicit_lambda% (drop_unused% Std.Slice.Internal.toList_eq_toList_iter 6)

-- `Std.Slice.Internal.toListRev_eq_toListRev_iter` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Slice.Internal.toListRev_eq_toListRev_iter.h6.{u, v} :
    ∀ {γ : Type u} {α β : Type v} {s : Std.Slice γ} [inst : Std.ToIterator (Std.Slice γ) Id α β]
      [inst_1 : Std.Iterator α Id β], s.toListRev = (Std.Slice.Internal.iter s).toListRev :=
  no_implicit_lambda% (drop_unused% Std.Slice.Internal.toListRev_eq_toListRev_iter 6)

-- `String.Slice.takeWhile_append_dropWhile` idx 4: unused in the library's proof
theorem HypCheckProof.String.Slice.takeWhile_append_dropWhile.h4 :
    ∀ {ρ : Type} {pat : ρ} [inst : String.Slice.Pattern.Model.PatternModel pat]
      [inst : String.Slice.Pattern.ForwardPattern pat] {s : String.Slice},
      (s.takeWhile pat).copy ++ (s.dropWhile pat).copy = s.copy :=
  no_implicit_lambda% (drop_unused% String.Slice.takeWhile_append_dropWhile 4)

-- `Option.forM_join` idx 3: unused in the library's proof
theorem HypCheckProof.Option.forM_join.h3.{u_1, u_2, u_3} :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} [inst : Monad m] (o : Option (Option α)) (f : α → m PUnit),
      ForM.forM o.join f = ForM.forM o fun (x : Option α) => ForM.forM x f :=
  no_implicit_lambda% (drop_unused% Option.forM_join 3)

-- `Std.Iter.toArray_eq_toArray_toIterM` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Iter.toArray_eq_toArray_toIterM.h3.{u_1} :
    ∀ {α β : Type u_1} [inst : Std.Iterator α Id β] {it : @Std.Iter α β},
      @Eq (Array β) (@Std.Iter.toArray α β inst it)
        (@Id.run (Array β) (@Std.IterM.toArray α β Id Id.instMonad inst (@Std.Iter.toIterM α β it))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.toArray_eq_toArray_toIterM 3)

-- `Lean.Grind.Fin.neg_mul` idx 1: unused in the library's proof
theorem HypCheckProof.Lean.Grind.Fin.neg_mul.h1 :
    ∀ {n : Nat} (a b : Fin n), -a * b = -(a * b) :=
  no_implicit_lambda% (drop_unused% Lean.Grind.Fin.neg_mul 1)

-- `Std.Iter.findM?_eq_findSomeM?` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Iter.findM?_eq_findSomeM?.h6.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : Std.Iterator α Id β]
      [inst_2 : @Std.IteratorLoop α Id β inst_1 m] {it : @Std.Iter α β} {f : β → m (ULift Bool)},
      @Eq (m (Option β)) (@Std.Iter.findM? α β m inst inst_1 inst_2 it f)
        (@Std.Iter.findSomeM? α β β m inst inst_1 inst_2 it fun (x : β) =>
          @Bind.bind m (@Monad.toBind m inst) (ULift Bool) (Option β) (f x) fun (__do_lift : ULift Bool) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (Option β)
              (@ite (Option β) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
                (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true) (@Option.some β x) (@Option.none β))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.findM?_eq_findSomeM? 6)

-- `List.anyM_toArray` idx 3: unused in the library's proof
theorem HypCheckProof.List.anyM_toArray.h3.{u_1, u_2} :
    ∀ {m : Type → Type u_1} {α : Type u_2} [inst : Monad m] {p : α → m Bool} {l : List α},
      Array.anyM p l.toArray = List.anyM p l :=
  no_implicit_lambda% (drop_unused% List.anyM_toArray 3)

-- `Std.Iter.toList_eq_toList_toIterM` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Iter.toList_eq_toList_toIterM.h3.{u_1} :
    ∀ {α β : Type u_1} [inst : Std.Iterator α Id β] {it : @Std.Iter α β},
      @Eq (List β) (@Std.Iter.toList α β inst it)
        (@Id.run (List β) (@Std.IterM.toList α Id Id.instMonad β inst (@Std.Iter.toIterM α β it))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.toList_eq_toList_toIterM 3)

-- `Std.Internal.LawfulMonadLiftBindFunction.id` idx 2: unused in the library's proof
theorem HypCheckProof.Std.Internal.LawfulMonadLiftBindFunction.id.h2.{u, v, u_1} :
    ∀ {m : Type u → Type v} [inst : Monad m],
      Std.Internal.LawfulMonadLiftBindFunction fun (x : Type u_1) (x_1 : Type u) (f : x → m x_1) (x_2 : Id x) => f x_2.run :=
  no_implicit_lambda% (drop_unused% Std.Internal.LawfulMonadLiftBindFunction.id 2)

-- `Std.Slice.Internal.fold_iter` idx 9: unused in the library's proof
theorem HypCheckProof.Std.Slice.Internal.fold_iter.h9.{u, v, u_1} :
    ∀ {γ : Type u} {α β : Type v} {α_1 : Type u_1} {f : α_1 → β → α_1} {init : α_1}
      [inst : Std.ToIterator (Std.Slice γ) Id α β] [inst_1 : Std.Iterator α Id β] [inst_2 : Std.IteratorLoop α Id Id]
      {s : Std.Slice γ}, Std.Iter.fold f init (Std.Slice.Internal.iter s) = Std.Slice.foldl f init s :=
  no_implicit_lambda% (drop_unused% Std.Slice.Internal.fold_iter 9)

-- `Std.instLawfulIteratorLoopDefaultImplementation` idx 7: unused in the library's proof
theorem HypCheckProof.Std.instLawfulIteratorLoopDefaultImplementation.h7.{w, w', x, x'} :
    ∀ {β : Type w} (α : Type w) (m : Type w → Type w') (n : Type x → Type x') [inst : Monad m] [inst_1 : Monad n]
      [inst_2 : Std.Iterator α m β],
      @Std.LawfulIteratorLoop β α m n inst inst_1 inst_2 (@Std.IteratorLoop.defaultImplementation β α m n inst_1 inst_2) :=
  no_implicit_lambda% (drop_unused% Std.instLawfulIteratorLoopDefaultImplementation 7)

-- `Array.foldrM_wfParam` idx 4: unused in the library's proof
theorem HypCheckProof.Array.foldrM_wfParam.h4.{u_1, u_2, u_3} :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {xs : Array α} {f : α → β → m β} {init : β},
      Array.foldrM f init (wfParam xs) = Array.foldrM f init xs.attach.unattach :=
  no_implicit_lambda% (drop_unused% Array.foldrM_wfParam 4)

-- `Std.IterM.drain_eq_fold` idx 4: unused in the library's proof
theorem HypCheckProof.Std.IterM.drain_eq_fold.h4.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : Monad m]
      [inst_2 : @Std.IteratorLoop α m β inst m] {it : @Std.IterM α m β},
      @Eq (m PUnit) (@Std.IterM.drain α m inst_1 β inst it inst_2)
        (@Std.IterM.fold m α β PUnit inst_1 inst inst_2 (fun (x : PUnit) (x_1 : β) => PUnit.unit) PUnit.unit it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.drain_eq_fold 4)

-- `Std.Iter.findSome?_eq_findSome?_toIterM` idx 5: unused in the library's proof
theorem HypCheckProof.Std.Iter.findSome?_eq_findSome?_toIterM.h5.{w} :
    ∀ {α β γ : Type w} [inst : Std.Iterator α Id β] [inst_1 : @Std.IteratorLoop α Id β inst Id] {it : @Std.Iter α β}
      {f : β → Option γ},
      @Eq (Option γ) (@Std.Iter.findSome? α β γ inst inst_1 it f)
        (@Id.run (Option γ) (@Std.IterM.findSome? α β γ Id Id.instMonad inst inst_1 (@Std.Iter.toIterM α β it) f)) :=
  no_implicit_lambda% (drop_unused% Std.Iter.findSome?_eq_findSome?_toIterM 5)

-- `List.forM_map` idx 4: unused in the library's proof
theorem HypCheckProof.List.forM_map.h4.{u_1, u_2, u_3, u_4} :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_4} [inst : Monad m] {l : List α} {g : α → β} {f : β → m PUnit},
      ForM.forM (List.map g l) f = ForM.forM l fun (a : α) => f (g a) :=
  no_implicit_lambda% (drop_unused% List.forM_map 4)

-- `List.foldrM_wfParam` idx 4: unused in the library's proof
theorem HypCheckProof.List.foldrM_wfParam.h4.{u_1, u_2, u_3} :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {xs : List α} {f : α → β → m β} {init : β},
      List.foldrM f init (wfParam xs) = List.foldrM f init xs.attach.unattach :=
  no_implicit_lambda% (drop_unused% List.foldrM_wfParam 4)

-- `Array.filterMapM_wfParam` idx 4: unused in the library's proof
theorem HypCheckProof.Array.filterMapM_wfParam.h4.{u_1, u_2, u_3} :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {xs : Array α} {f : α → m (Option β)},
      Array.filterMapM f (wfParam xs) = Array.filterMapM f xs.attach.unattach :=
  no_implicit_lambda% (drop_unused% Array.filterMapM_wfParam 4)

-- `Std.IterM.toList_toArray` idx 5: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_toArray.h5.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : Std.Iterator α m β] {it : @Std.IterM α m β},
      @Eq (m (List β))
        (@Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst)) (Array β) (List β) (@Array.toList β)
          (@Std.IterM.toArray α β m inst inst_1 it))
        (@Std.IterM.toList α m inst β inst_1 it) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_toArray 5)

-- `List.mapM_wfParam` idx 4: unused in the library's proof
theorem HypCheckProof.List.mapM_wfParam.h4.{u_1, u_2, u_3} :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {xs : List α} {f : α → m β},
      List.mapM f (wfParam xs) = List.mapM f xs.attach.unattach :=
  no_implicit_lambda% (drop_unused% List.mapM_wfParam 4)

-- `ExceptT.run_tryCatch` idx 4: unused in the library's proof
theorem HypCheckProof.ExceptT.run_tryCatch.h4.{u_1, u_2} :
    ∀ {m : Type u_1 → Type u_2} {ε α : Type u_1} [inst : Monad m] (x : ExceptT ε m α) (h : ε → ExceptT ε m α),
      @Eq (m (Except ε α))
        (@ExceptT.run ε m α
          (@MonadExcept.tryCatch ε (ExceptT ε m)
            (@instMonadExceptOfMonadExceptOf ε (ExceptT ε m) (@instMonadExceptOfExceptTOfMonad m ε inst)) α x h))
        (@Bind.bind m (@Monad.toBind m inst) (Except ε α) (Except ε α) (@ExceptT.run ε m α x) fun (r : Except ε α) =>
          @ExceptT.run_bind.match_1 ε α (fun (r : Except ε α) => m (Except ε α)) r
            (fun (a : α) =>
              @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (Except ε α) (@Except.ok ε α a))
            fun (e : ε) => @ExceptT.run ε m α (h e)) :=
  no_implicit_lambda% (drop_unused% ExceptT.run_tryCatch 4)

-- `Std.Iter.toListRev_eq_toListRev_toIterM` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Iter.toListRev_eq_toListRev_toIterM.h3.{u_1} :
    ∀ {α β : Type u_1} [inst : Std.Iterator α Id β] {it : @Std.Iter α β},
      @Eq (List β) (@Std.Iter.toListRev α β inst it)
        (@Id.run (List β) (@Std.IterM.toListRev α Id Id.instMonad β inst (@Std.Iter.toIterM α β it))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.toListRev_eq_toListRev_toIterM 3)

-- `Std.IterM.toList_toIter` idx 3: unused in the library's proof
theorem HypCheckProof.Std.IterM.toList_toIter.h3.{u_1} :
    ∀ {α β : Type u_1} [inst : Std.Iterator α Id β] {it : @Std.IterM α Id β},
      @Eq (List β) (@Std.Iter.toList α β inst (@Std.IterM.toIter α β it))
        (@Id.run (List β) (@Std.IterM.toList α Id Id.instMonad β inst it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toList_toIter 3)

-- `Std.Iter.isPlausibleStep_iff_step_eq` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Iter.isPlausibleStep_iff_step_eq.h3.{u_1} :
    ∀ {α β : Type u_1} [inst : Std.Iterator α Id β] [inst_1 : @Std.LawfulDeterministicIterator β α Id inst]
      {it : @Std.Iter α β} {step : Std.IterStep (@Std.Iter α β) β},
      Iff (@Std.Iter.IsPlausibleStep α β inst it step)
        (@Eq (Std.IterStep (@Std.Iter α β) β)
          (@Subtype.val (Std.IterStep (@Std.Iter α β) β) (@Std.Iter.IsPlausibleStep α β inst it)
            (@Std.Iter.step α β inst it))
          step) :=
  no_implicit_lambda% (drop_unused% Std.Iter.isPlausibleStep_iff_step_eq 3)

-- `List.forIn_map` idx 6: unused in the library's proof
theorem HypCheckProof.List.forIn_map.h6.{u_1, u_2, u_3, u_4} :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_4} {γ : Type u_1} {init : γ} [inst : Monad m] {l : List α}
      {g : α → β} {f : β → γ → m (ForInStep γ)},
      ForIn.forIn (List.map g l) init f = ForIn.forIn l init fun (a : α) (y : γ) => f (g a) y :=
  no_implicit_lambda% (drop_unused% List.forIn_map 6)

-- `List.flatMapM_wfParam` idx 4: unused in the library's proof
theorem HypCheckProof.List.flatMapM_wfParam.h4.{u_1, u_2, u_3} :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {xs : List α} {f : α → m (List β)},
      List.flatMapM f (wfParam xs) = List.flatMapM f xs.attach.unattach :=
  no_implicit_lambda% (drop_unused% List.flatMapM_wfParam 4)

-- `Std.Slice.Internal.toArray_eq_toArray_iter` idx 6: unused in the library's proof
theorem HypCheckProof.Std.Slice.Internal.toArray_eq_toArray_iter.h6.{u, v} :
    ∀ {γ : Type u} {α β : Type v} {s : Std.Slice γ} [inst : Std.ToIterator (Std.Slice γ) Id α β]
      [inst_1 : Std.Iterator α Id β], s.toArray = (Std.Slice.Internal.iter s).toArray :=
  no_implicit_lambda% (drop_unused% Std.Slice.Internal.toArray_eq_toArray_iter 6)

-- `Std.Iter.length_eq_length_toIterM` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Iter.length_eq_length_toIterM.h3.{w} :
    ∀ {α β : Type w} [inst : Std.Iterator α Id β] [inst_1 : @Std.IteratorLoop α Id β inst Id] {it : @Std.Iter α β},
      @Eq Nat (@Std.Iter.length α β inst inst_1 it)
        (@ULift.down Nat
          (@Id.run (ULift Nat) (@Std.IterM.length α Id β inst inst_1 Id.instMonad (@Std.Iter.toIterM α β it)))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.length_eq_length_toIterM 3)

-- `Std.Internal.instLawfulMonadLiftBindFunctionIdRunOfLawfulMonad` idx 2: unused in the library's proof
theorem HypCheckProof.Std.Internal.instLawfulMonadLiftBindFunctionIdRunOfLawfulMonad.h2.{u, w, u_1} :
    ∀ {n : Type u → Type w} [inst : Monad n],
      Std.Internal.LawfulMonadLiftBindFunction fun (γ : Type u_1) (δ : Type u) (f : γ → n δ) (x : Id γ) => f x.run :=
  no_implicit_lambda% (drop_unused% Std.Internal.instLawfulMonadLiftBindFunctionIdRunOfLawfulMonad 2)

-- `Std.IterM.step_filterMapM` idx 10: unused in the library's proof
theorem HypCheckProof.Std.IterM.step_filterMapM.h10.{w, w', w''} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β] {it : @Std.IterM α m β}
      {f : β → n (Option β')} [inst_1 : Monad n] [inst_2 : MonadAttach n] [inst_3 : MonadLiftT m n],
      @Eq
        (n
          (Std.Shrink
            (@Std.IterM.Step
              (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
              n β'
              (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst inst_1)
              (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it))))
        (@Std.IterM.step
          (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) fun (b : β) =>
            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
          n β'
          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst inst_1)
          (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it))
        (@Bind.bind n (@Monad.toBind n inst_1) (Std.Shrink (@Std.IterM.Step α m β inst it))
          (Std.Shrink
            (@Std.IterM.Step
              (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
              n β'
              (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst inst_1)
              (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it)))
          (@liftM m n inst_3 (Std.Shrink (@Std.IterM.Step α m β inst it)) (@Std.IterM.step α m β inst it))
          fun (__do_lift : Std.Shrink (@Std.IterM.Step α m β inst it)) =>
          @Std.IterM.step_filterMapWithPostcondition.match_3 α β m inst it
            (fun (x : @Std.IterM.Step α m β inst it) =>
              n
                (Std.Shrink
                  (@Std.IterM.Step
                    (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                      fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                    n β'
                    (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                      (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst inst_1)
                    (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it))))
            (@Std.Shrink.inflate (@Std.IterM.Step α m β inst it) __do_lift)
            (fun (it' : @Std.IterM α m β) (out : β)
                (h : @Std.IterM.IsPlausibleStep α m β inst it (@Std.IterStep.yield (@Std.IterM α m β) β it' out)) =>
              @Bind.bind n (@Monad.toBind n inst_1)
                (@Subtype (Option β') (@MonadAttach.CanReturn n inst_2 (Option β') (f out)))
                (Std.Shrink
                  (@Std.IterM.Step
                    (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                      fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                    n β'
                    (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                      (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst inst_1)
                    (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it)))
                (@MonadAttach.attach n inst_2 (Option β') (f out))
                fun (__do_lift : @Subtype (Option β') (@MonadAttach.CanReturn n inst_2 (Option β') (f out))) =>
                @Std.IterM.step_filterMapM.match_1 β β' n f inst_2 out
                  (fun (__do_lift : @Subtype (Option β') (@MonadAttach.CanReturn n inst_2 (Option β') (f out))) =>
                    n
                      (Std.Shrink
                        (@Std.IterM.Step
                          (@Std.Iterators.Types.FilterMap α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                          n β'
                          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst
                            inst_1)
                          (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it))))
                  __do_lift
                  (fun (hf : @MonadAttach.CanReturn n inst_2 (Option β') (f out) (@Option.none β')) =>
                    @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_1))
                      (Std.Shrink
                        (@Std.IterM.Step
                          (@Std.Iterators.Types.FilterMap α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                          n β'
                          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst
                            inst_1)
                          (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it)))
                      (@Std.Shrink.deflate
                        (@Std.IterM.Step
                          (@Std.Iterators.Types.FilterMap α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                          n β'
                          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst
                            inst_1)
                          (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it))
                        (@Std.PlausibleIterStep.skip
                          (@Std.IterM
                            (@Std.Iterators.Types.FilterMap α β β' m n
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) fun (b : β) =>
                              @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                            n β')
                          β'
                          (@Std.IterM.IsPlausibleStep
                            (@Std.Iterators.Types.FilterMap α β β' m n
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) fun (b : β) =>
                              @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                            n β'
                            (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                              (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst
                              inst_1)
                            (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it))
                          (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it')
                          (@Std.Iterators.Types.FilterMap.PlausibleStep.yieldNone α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst
                            (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it) it' out h hf))))
                  fun (out' : β') (hf : @MonadAttach.CanReturn n inst_2 (Option β') (f out) (@Option.some β' out')) =>
                  @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_1))
                    (Std.Shrink
                      (@Std.IterM.Step
                        (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                          fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                        n β'
                        (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                          (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst inst_1)
                        (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it)))
                    (@Std.Shrink.deflate
                      (@Std.IterM.Step
                        (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                          fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                        n β'
                        (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                          (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst inst_1)
                        (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it))
                      (@Std.PlausibleIterStep.yield
                        (@Std.IterM
                          (@Std.Iterators.Types.FilterMap α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                          n β')
                        β'
                        (@Std.IterM.IsPlausibleStep
                          (@Std.Iterators.Types.FilterMap α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x) fun (b : β) =>
                            @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                          n β'
                          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                            (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst
                            inst_1)
                          (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it))
                        (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it') out'
                        (@Std.Iterators.Types.FilterMap.PlausibleStep.yieldSome α β β' m n
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                          (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst
                          (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it) it' out out' h hf))))
            (fun (it' : @Std.IterM α m β)
                (h : @Std.IterM.IsPlausibleStep α m β inst it (@Std.IterStep.skip (@Std.IterM α m β) β it')) =>
              @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_1))
                (Std.Shrink
                  (@Std.IterM.Step
                    (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                      fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                    n β'
                    (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                      (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst inst_1)
                    (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it)))
                (@Std.Shrink.deflate
                  (@Std.IterM.Step
                    (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                      fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                    n β'
                    (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                      (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst inst_1)
                    (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it))
                  (@Std.PlausibleIterStep.skip
                    (@Std.IterM
                      (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                        fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                      n β')
                    β'
                    (@Std.IterM.IsPlausibleStep
                      (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                        fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                      n β'
                      (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                        (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                        (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst inst_1)
                      (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it))
                    (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it')
                    (@Std.Iterators.Types.FilterMap.PlausibleStep.skip α β β' m n
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                      (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst
                      (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it) it' h))))
            fun (h : @Std.IterM.IsPlausibleStep α m β inst it (@Std.IterStep.done (@Std.IterM α m β) β)) =>
            @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_1))
              (Std.Shrink
                (@Std.IterM.Step
                  (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                    fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                  n β'
                  (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                    (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                    (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst inst_1)
                  (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it)))
              (@Std.Shrink.deflate
                (@Std.IterM.Step
                  (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                    fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                  n β'
                  (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                    (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                    (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst inst_1)
                  (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it))
                (@Std.PlausibleIterStep.done
                  (@Std.IterM
                    (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                      fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                    n β')
                  β'
                  (@Std.IterM.IsPlausibleStep
                    (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                      fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b))
                    n β'
                    (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                      (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst inst_1)
                    (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it))
                  (@Std.Iterators.Types.FilterMap.PlausibleStep.done α β β' m n
                    (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_3 x)
                    (fun (b : β) => @Std.Iterators.PostconditionT.attachLift (Option β') n inst_2 (f b)) inst
                    (@Std.IterM.filterMapM α β β' m n inst inst_1 inst_2 inst_3 f it) h)))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.step_filterMapM 10)

-- `Std.IterM.findM?_eq_findSomeM?` idx 6: unused in the library's proof
theorem HypCheckProof.Std.IterM.findM?_eq_findSomeM?.h6.{w, w'} :
    ∀ {α β : Type w} {m : Type w → Type w'} [inst : Monad m] [inst_1 : Std.Iterator α m β]
      [inst_2 : @Std.IteratorLoop α m β inst_1 m] {it : @Std.IterM α m β} {f : β → m (ULift Bool)},
      @Eq (m (Option β)) (@Std.IterM.findM? α β m inst inst_1 inst_2 it f)
        (@Std.IterM.findSomeM? α β β m inst inst_1 inst_2 it fun (x : β) =>
          @Bind.bind m (@Monad.toBind m inst) (ULift Bool) (Option β) (f x) fun (__do_lift : ULift Bool) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (Option β)
              (@ite (Option β) (@Eq Bool (@ULift.down Bool __do_lift) Bool.true)
                (instDecidableEqBool (@ULift.down Bool __do_lift) Bool.true) (@Option.some β x) (@Option.none β))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.findM?_eq_findSomeM? 6)

-- `Option.forM_map` idx 4: unused in the library's proof
theorem HypCheckProof.Option.forM_map.h4.{u_1, u_2, u_3, u_4} :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_4} [inst : Monad m] (o : Option α) (g : α → β) (f : β → m PUnit),
      ForM.forM (Option.map g o) f = ForM.forM o fun (a : α) => f (g a) :=
  no_implicit_lambda% (drop_unused% Option.forM_map 4)

-- `Array.mapM_wfParam` idx 4: unused in the library's proof
theorem HypCheckProof.Array.mapM_wfParam.h4.{u_1, u_2, u_3} :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {xs : Array α} {f : α → m β},
      Array.mapM f (wfParam xs) = Array.mapM f xs.attach.unattach :=
  no_implicit_lambda% (drop_unused% Array.mapM_wfParam 4)

-- `Std.Iter.find?_eq_findM?` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Iter.find?_eq_findM?.h4.{w} :
    ∀ {α β : Type w} [inst : Std.Iterator α Id β] [inst_1 : @Std.IteratorLoop α Id β inst Id] {it : @Std.Iter α β}
      {f : β → Bool},
      @Eq (Option β) (@Std.Iter.find? α β inst inst_1 it f)
        (@Id.run (Option β)
          (@Std.Iter.findM? α β Id Id.instMonad inst inst_1 it fun (x : β) =>
            @Pure.pure Id (@Applicative.toPure Id (@Monad.toApplicative Id Id.instMonad)) (ULift Bool)
              (@ULift.up Bool (f x)))) :=
  no_implicit_lambda% (drop_unused% Std.Iter.find?_eq_findM? 4)

-- `List.filterMapM_wfParam` idx 4: unused in the library's proof
theorem HypCheckProof.List.filterMapM_wfParam.h4.{u_1, u_2, u_3} :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {xs : List α} {f : α → m (Option β)},
      List.filterMapM f (wfParam xs) = List.filterMapM f xs.attach.unattach :=
  no_implicit_lambda% (drop_unused% List.filterMapM_wfParam 4)

-- `String.Slice.dropEndWhile_append_takeEndWhile` idx 4: unused in the library's proof
theorem HypCheckProof.String.Slice.dropEndWhile_append_takeEndWhile.h4 :
    ∀ {ρ : Type} {pat : ρ} [inst : String.Slice.Pattern.Model.PatternModel pat]
      [inst : String.Slice.Pattern.BackwardPattern pat] {s : String.Slice},
      (s.dropEndWhile pat).copy ++ (s.takeEndWhile pat).copy = s.copy :=
  no_implicit_lambda% (drop_unused% String.Slice.dropEndWhile_append_takeEndWhile 4)

-- `Std.IterM.toArray_toIter` idx 3: unused in the library's proof
theorem HypCheckProof.Std.IterM.toArray_toIter.h3.{u_1} :
    ∀ {α β : Type u_1} [inst : Std.Iterator α Id β] {it : @Std.IterM α Id β},
      @Eq (Array β) (@Std.Iter.toArray α β inst (@Std.IterM.toIter α β it))
        (@Id.run (Array β) (@Std.IterM.toArray α β Id Id.instMonad inst it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toArray_toIter 3)

-- `Std.Iter.foldM_eq_forIn` idx 4: unused in the library's proof
theorem HypCheckProof.Std.Iter.foldM_eq_forIn.h4.{w, x, x'} :
    ∀ {α β : Type w} {γ : Type x} [inst : Std.Iterator α Id β] {m : Type x → Type x'} [inst_1 : Monad m]
      [inst_2 : @Std.IteratorLoop α Id β inst m] {f : γ → β → m γ} {init : γ} {it : @Std.Iter α β},
      @Eq (m γ) (@Std.Iter.foldM m inst_1 α β γ inst inst_2 f init it)
        (@ForIn.forIn m (@Std.Iter α β) β (@Std.instForInIterOfMonadOfIteratorLoopId α β m inst_1 inst inst_2) γ it init
          fun (x : β) (acc : γ) =>
          @Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst_1)) γ (ForInStep γ) (@ForInStep.yield γ)
            (f acc x)) :=
  no_implicit_lambda% (drop_unused% Std.Iter.foldM_eq_forIn 4)

-- `Std.IterM.fold_eq_forIn` idx 5: unused in the library's proof
theorem HypCheckProof.Std.IterM.fold_eq_forIn.h5.{w, w'} :
    ∀ {α β γ : Type w} {m : Type w → Type w'} [inst : Std.Iterator α m β] [inst_1 : Monad m]
      [inst_2 : @Std.IteratorLoop α m β inst m] {f : γ → β → γ} {init : γ} {it : @Std.IterM α m β},
      @Eq (m γ) (@Std.IterM.fold m α β γ inst_1 inst inst_2 f init it)
        (@ForIn.forIn m (@Std.IterM α m β) β
          (@Std.IterM.instForInOfIteratorLoop m m α β inst inst_2 (instMonadLiftT m) inst_1) γ it init
          fun (x : β) (acc : γ) =>
          @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst_1)) (ForInStep γ) (@ForInStep.yield γ (f acc x))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.fold_eq_forIn 5)

-- `Std.IterM.step_filterMapWithPostcondition` idx 9: unused in the library's proof
theorem HypCheckProof.Std.IterM.step_filterMapWithPostcondition.h9.{w, w', w''} :
    ∀ {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''} [inst : Std.Iterator α m β] {it : @Std.IterM α m β}
      {f : β → Std.Iterators.PostconditionT n (Option β')} [inst_1 : Monad n] [inst_2 : MonadLiftT m n],
      @Eq
        (n
          (Std.Shrink
            (@Std.IterM.Step
              (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f) n β'
              (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
              (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it))))
        (@Std.IterM.step
          (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f) n β'
          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f
            inst inst_1)
          (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it))
        (@Bind.bind n (@Monad.toBind n inst_1) (Std.Shrink (@Std.IterM.Step α m β inst it))
          (Std.Shrink
            (@Std.IterM.Step
              (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f) n β'
              (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
              (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it)))
          (@liftM m n inst_2 (Std.Shrink (@Std.IterM.Step α m β inst it)) (@Std.IterM.step α m β inst it))
          fun (__do_lift : Std.Shrink (@Std.IterM.Step α m β inst it)) =>
          @Std.IterM.step_filterMapWithPostcondition.match_3 α β m inst it
            (fun (x : @Std.IterM.Step α m β inst it) =>
              n
                (Std.Shrink
                  (@Std.IterM.Step
                    (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f) n
                    β'
                    (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                    (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it))))
            (@Std.Shrink.inflate (@Std.IterM.Step α m β inst it) __do_lift)
            (fun (it' : @Std.IterM α m β) (out : β)
                (h : @Std.IterM.IsPlausibleStep α m β inst it (@Std.IterStep.yield (@Std.IterM α m β) β it' out)) =>
              @Bind.bind n (@Monad.toBind n inst_1)
                (@Subtype (Option β') (@Std.Iterators.PostconditionT.Property n (Option β') (f out)))
                (Std.Shrink
                  (@Std.IterM.Step
                    (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f) n
                    β'
                    (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                    (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it)))
                (@Std.Iterators.PostconditionT.operation n (Option β') (f out))
                fun (__do_lift : @Subtype (Option β') (@Std.Iterators.PostconditionT.Property n (Option β') (f out))) =>
                @Std.IterM.step_filterMapWithPostcondition.match_1 β β' n f out
                  (fun (__do_lift : @Subtype (Option β') (@Std.Iterators.PostconditionT.Property n (Option β') (f out))) =>
                    n
                      (Std.Shrink
                        (@Std.IterM.Step
                          (@Std.Iterators.Types.FilterMap α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f)
                          n β'
                          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                          (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it))))
                  __do_lift
                  (fun (h' : @Std.Iterators.PostconditionT.Property n (Option β') (f out) (@Option.none β')) =>
                    @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_1))
                      (Std.Shrink
                        (@Std.IterM.Step
                          (@Std.Iterators.Types.FilterMap α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f)
                          n β'
                          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                          (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it)))
                      (@Std.Shrink.deflate
                        (@Std.IterM.Step
                          (@Std.Iterators.Types.FilterMap α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f)
                          n β'
                          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                          (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it))
                        (@Std.PlausibleIterStep.skip
                          (@Std.IterM
                            (@Std.Iterators.Types.FilterMap α β β' m n
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f)
                            n β')
                          β'
                          (@Std.IterM.IsPlausibleStep
                            (@Std.Iterators.Types.FilterMap α β β' m n
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f)
                            n β'
                            (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                              (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                            (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it))
                          (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it')
                          (@Std.Iterators.Types.FilterMap.PlausibleStep.yieldNone α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst
                            (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it) it' out h h'))))
                  fun (out' : β')
                    (h' : @Std.Iterators.PostconditionT.Property n (Option β') (f out) (@Option.some β' out')) =>
                  @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_1))
                    (Std.Shrink
                      (@Std.IterM.Step
                        (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
                          f)
                        n β'
                        (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                        (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it)))
                    (@Std.Shrink.deflate
                      (@Std.IterM.Step
                        (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x)
                          f)
                        n β'
                        (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                        (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it))
                      (@Std.PlausibleIterStep.yield
                        (@Std.IterM
                          (@Std.Iterators.Types.FilterMap α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f)
                          n β')
                        β'
                        (@Std.IterM.IsPlausibleStep
                          (@Std.Iterators.Types.FilterMap α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f)
                          n β'
                          (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                            (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                          (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it))
                        (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it') out'
                        (@Std.Iterators.Types.FilterMap.PlausibleStep.yieldSome α β β' m n
                          (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst
                          (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it) it' out out' h h'))))
            (fun (it' : @Std.IterM α m β)
                (h : @Std.IterM.IsPlausibleStep α m β inst it (@Std.IterStep.skip (@Std.IterM α m β) β it')) =>
              @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_1))
                (Std.Shrink
                  (@Std.IterM.Step
                    (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f) n
                    β'
                    (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                    (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it)))
                (@Std.Shrink.deflate
                  (@Std.IterM.Step
                    (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f) n
                    β'
                    (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                    (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it))
                  (@Std.PlausibleIterStep.skip
                    (@Std.IterM
                      (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f)
                      n β')
                    β'
                    (@Std.IterM.IsPlausibleStep
                      (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f)
                      n β'
                      (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                        (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                      (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it))
                    (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it')
                    (@Std.Iterators.Types.FilterMap.PlausibleStep.skip α β β' m n
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst
                      (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it) it' h))))
            fun (h : @Std.IterM.IsPlausibleStep α m β inst it (@Std.IterStep.done (@Std.IterM α m β) β)) =>
            @Pure.pure n (@Applicative.toPure n (@Monad.toApplicative n inst_1))
              (Std.Shrink
                (@Std.IterM.Step
                  (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f) n
                  β'
                  (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                    (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                  (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it)))
              (@Std.Shrink.deflate
                (@Std.IterM.Step
                  (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f) n
                  β'
                  (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                    (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                  (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it))
                (@Std.PlausibleIterStep.done
                  (@Std.IterM
                    (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f) n
                    β')
                  β'
                  (@Std.IterM.IsPlausibleStep
                    (@Std.Iterators.Types.FilterMap α β β' m n (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f) n
                    β'
                    (@Std.Iterators.Types.FilterMap.instIterator α β β' m n
                      (fun ⦃x : Type w⦄ => @MonadLiftT.monadLift m n inst_2 x) f inst inst_1)
                    (@Std.IterM.filterMapWithPostcondition α β β' m n inst_2 inst f it))
                  (@Std.IterM.step_filterMapWithPostcondition._proof_5 α β β' m n inst it f inst_1 inst_2 h)))) :=
  no_implicit_lambda% (drop_unused% Std.IterM.step_filterMapWithPostcondition 9)

-- `List.forIn'_map` idx 6: unused in the library's proof
theorem HypCheckProof.List.forIn'_map.h6.{u_1, u_2, u_3, u_4} :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_4} {γ : Type u_1} {init : γ} [inst : Monad m] {l : List α}
      (g : α → β) (f : (b : β) → b ∈ List.map g l → γ → m (ForInStep γ)),
      ForIn'.forIn' (List.map g l) init f =
        ForIn'.forIn' l init fun (a : α) (h : a ∈ l) (y : γ) => f (g a) (List.mem_map_of_mem h) y :=
  no_implicit_lambda% (drop_unused% List.forIn'_map 6)

-- `ExceptT.run_liftM` idx 4: unused in the library's proof
theorem HypCheckProof.ExceptT.run_liftM.h4.{u, v} :
    ∀ {α ε : Type u} {m : Type u → Type v} [inst : Monad m] (x : m α),
      @Eq (m (Except ε α))
        (@ExceptT.run ε m α
          (@liftM m (ExceptT ε m)
            (@instMonadLiftTOfMonadLift m m (ExceptT ε m) (@ExceptT.instMonadLift ε m inst) (instMonadLiftT m)) α x))
        (@Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst)) α (Except ε α) (@Except.ok ε α) x) :=
  no_implicit_lambda% (drop_unused% ExceptT.run_liftM 4)

-- `List.idxOf_le_length` idx 2: unused in the library's proof
theorem HypCheckProof.List.idxOf_le_length.h2.{u_1} :
    ∀ {α : Type u_1} [inst : BEq α] {l : List α} {a : α}, List.idxOf a l ≤ l.length :=
  no_implicit_lambda% (drop_unused% List.idxOf_le_length 2)

-- `Std.IterM.toListRev_toIter` idx 3: unused in the library's proof
theorem HypCheckProof.Std.IterM.toListRev_toIter.h3.{u_1} :
    ∀ {α β : Type u_1} [inst : Std.Iterator α Id β] {it : @Std.IterM α Id β},
      @Eq (List β) (@Std.Iter.toListRev α β inst (@Std.IterM.toIter α β it))
        (@Id.run (List β) (@Std.IterM.toListRev α Id Id.instMonad β inst it)) :=
  no_implicit_lambda% (drop_unused% Std.IterM.toListRev_toIter 3)

-- `Std.Identity.toRightIdentity` idx 3: unused in the library's proof
theorem HypCheckProof.Std.Identity.toRightIdentity.h3.{u} :
    ∀ {α : Sort u} {op : α → α → α} {o : outParam α}, Std.RightIdentity op o :=
  no_implicit_lambda% (drop_unused% Std.Identity.toRightIdentity 3)

