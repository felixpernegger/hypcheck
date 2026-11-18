import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.Surreal.Dyadic.0.Dyadic.toIGame_lt_toIGame_aux, hypothesis 2: removable
/- FAILED: 2:110: invalid binder annotation, type is not a class instance
  ?m.2

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 2:174: Type mismatch
  y
has type
  Dyadic
of sort `Type` but is expected to have type
  ?m.11
of sort `Type (u + 1)` | 4:18: invalid binder annotation, type is not a class instance
  ?m.2

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 4:18: invalid binder annotation, type is not a class instance
  ?m.2

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 4:18: invalid binder annotation, type is not a class instance
  ?m.2

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 4:18: invalid binder annotation, type is not a class instance
  ?m.2

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 2:110: invalid binder annotation, type is not a class instance
  ?m.2

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 4:18: invalid binder annotation, type is not a class instance
  ?m.2

Note: Use the command `set_option checkBinderAnnotations false` to disable the check
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.toIGame_lt_toIGame_aux.h2.gneg.{u} : ∀ {x y : Dyadic}, ¬(↑x).Numeric → ∀ [inst : (↑y).Numeric], x < y → ↑x < ↑y := by
  (intros; solve_by_elim)
theorem HypCheckProof.Dyadic.toIGame_lt_toIGame_aux.h2.{u} : ∀ {x y : Dyadic} [inst : (↑y).Numeric], x < y → ↑x < ↑y := by
  intro hc_x0 hc_x1 hc_x3 hc_x4
  exact Classical.byCases (fun hc_h => @Dyadic.toIGame_lt_toIGame_aux hc_x0 hc_x1 hc_h hc_x3 hc_x4) (fun hc_hn => @HypCheckProof.Dyadic.toIGame_lt_toIGame_aux.h2.gneg hc_x0 hc_x1 hc_hn hc_x3 hc_x4)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.toIGame_lt_toIGame_aux.h2.derivable.{u} : ∀ {x y : Dyadic} [inst : (↑y).Numeric], x < y → (↑x).Numeric := by
  (intros; infer_instance)
-/

-- _private.CombinatorialGames.Surreal.Dyadic.0.Dyadic.toIGame_lt_toIGame_aux, hypothesis 3: removable
/- FAILED: 2:91: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 2:171: Type mismatch
  y
has type
  Dyadic
of sort `Type` but is expected to have type
  ?m.7
of sort `Type (u + 1)` | 2:91: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 2:91: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 2:91: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 2:91: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 2:91: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 2:91: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.toIGame_lt_toIGame_aux.h3.gneg.{u} : ∀ {x y : Dyadic} [inst : (↑x).Numeric], ¬(↑y).Numeric → x < y → ↑x < ↑y := by
  (intros; solve_by_elim)
theorem HypCheckProof.Dyadic.toIGame_lt_toIGame_aux.h3.{u} : ∀ {x y : Dyadic} [inst : (↑x).Numeric], x < y → ↑x < ↑y := by
  intro hc_x0 hc_x1 hc_x2 hc_x4
  exact Classical.byCases (fun hc_h => @Dyadic.toIGame_lt_toIGame_aux hc_x0 hc_x1 hc_x2 hc_h hc_x4) (fun hc_hn => @HypCheckProof.Dyadic.toIGame_lt_toIGame_aux.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.toIGame_lt_toIGame_aux.h3.derivable.{u} : ∀ {x y : Dyadic} [inst : (↑x).Numeric], x < y → (↑y).Numeric := by
  (intros; infer_instance)
-/

-- _private.CombinatorialGames.Surreal.Dyadic.0.Dyadic.toIGame_lt_toIGame_aux, hypothesis 4: necessary
/- FAILED: 2:83: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 2:149: Type mismatch
  y
has type
  Dyadic
of sort `Type` but is expected to have type
  ?m.5
of sort `Type 1` | 3:32: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 3:32: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 3:32: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 3:32: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 2:83: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 3:32: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 4:83: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 2:86: Type mismatch
  Dyadic.zero
has type
  Dyadic
of sort `Type` but is expected to have type
  ?m.1
of sort `Type 1` | 5:32: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 5:32: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 5:32: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 5:32: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 4:83: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check | 5:32: invalid binder annotation, type is not a class instance
  ?m.1

Note: Use the command `set_option checkBinderAnnotations false` to disable the check
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.toIGame_lt_toIGame_aux.h4 : ¬∀ {x y : Dyadic} [inst : (↑x).Numeric] [inst : (↑y).Numeric], ↑x < ↑y := fun hc_h => absurd (@hc_h (Dyadic.zero) (Dyadic.zero) _ _) (by
  simp)
-/

-- _private.CombinatorialGames.Surreal.Dyadic.0.Dyadic.lower_lt_aux, hypothesis 1: removable
/- FAILED: 2:74: invalid coercion notation, expected type is not known | 2:119: Type mismatch
  x
has type
  Dyadic
of sort `Type` but is expected to have type
  ?m.5 x
of sort `Type (u + 1)` | 2:77: invalid coercion notation, expected type is not known | 3:11: invalid coercion notation, expected type is not known | 2:77: invalid coercion notation, expected type is not known | 3:11: invalid coercion notation, expected type is not known | 2:74: invalid coercion notation, expected type is not known | 2:77: invalid coercion notation, expected type is not known
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.lower_lt_aux.h1.gneg.{u} : ∀ (x : Dyadic), ¬(↑x).Numeric → ↑x.lower < ↑x := by
  (intros; solve_by_elim)
theorem HypCheckProof.Dyadic.lower_lt_aux.h1.{u} : ∀ (x : Dyadic), ↑x.lower < ↑x := by
  intro hc_x0
  exact Classical.byCases (fun hc_h => @Dyadic.lower_lt_aux hc_x0 hc_h) (fun hc_hn => @HypCheckProof.Dyadic.lower_lt_aux.h1.gneg hc_x0 hc_hn)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.lower_lt_aux.h1.derivable.{u} : ∀ (x : Dyadic), (↑x).Numeric := by
  (intros; infer_instance)
-/

-- _private.CombinatorialGames.Surreal.Dyadic.0.Dyadic.lt_upper_aux, hypothesis 1: removable
/- FAILED: 2:74: invalid coercion notation, expected type is not known | 2:113: Type mismatch
  x.upper
has type
  Dyadic
of sort `Type` but is expected to have type
  ?m.5 x
of sort `Type (u + 1)` | 2:77: invalid coercion notation, expected type is not known | 3:11: invalid coercion notation, expected type is not known | 2:77: invalid coercion notation, expected type is not known | 3:11: invalid coercion notation, expected type is not known | 2:74: invalid coercion notation, expected type is not known | 2:77: invalid coercion notation, expected type is not known
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.lt_upper_aux.h1.gneg.{u} : ∀ (x : Dyadic), ¬(↑x).Numeric → ↑x < ↑x.upper := by
  (intros; solve_by_elim)
theorem HypCheckProof.Dyadic.lt_upper_aux.h1.{u} : ∀ (x : Dyadic), ↑x < ↑x.upper := by
  intro hc_x0
  exact Classical.byCases (fun hc_h => @Dyadic.lt_upper_aux hc_x0 hc_h) (fun hc_hn => @HypCheckProof.Dyadic.lt_upper_aux.h1.gneg hc_x0 hc_hn)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.lt_upper_aux.h1.derivable.{u} : ∀ (x : Dyadic), (↑x).Numeric := by
  (intros; infer_instance)
-/

-- _private.CombinatorialGames.Surreal.Dyadic.0.Dyadic.numeric_upper, hypothesis 1: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.numeric_upper.h1.gneg.{u} : ∀ (x : Dyadic), ¬IGame.Numeric.{u} ↑x → IGame.Numeric.{u} ↑x.upper := by
  (intros; infer_instance)
theorem HypCheckProof.Dyadic.numeric_upper.h1.{u} : ∀ (x : Dyadic), IGame.Numeric.{u} ↑x.upper := by
  intro hc_x0
  exact Classical.byCases (fun hc_h => @Dyadic.numeric_upper hc_x0 hc_h) (fun hc_hn => @HypCheckProof.Dyadic.numeric_upper.h1.gneg hc_x0 hc_hn)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.numeric_upper.h1.derivable.{u} : ∀ (x : Dyadic), IGame.Numeric.{u} ↑x := by
  (intros; infer_instance)

-- _private.CombinatorialGames.Surreal.Dyadic.0.Dyadic.numeric_lower, hypothesis 1: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.numeric_lower.h1.gneg.{u} : ∀ (x : Dyadic), ¬IGame.Numeric.{u} ↑x → IGame.Numeric.{u} ↑x.lower := by
  (intros; infer_instance)
theorem HypCheckProof.Dyadic.numeric_lower.h1.{u} : ∀ (x : Dyadic), IGame.Numeric.{u} ↑x.lower := by
  intro hc_x0
  exact Classical.byCases (fun hc_h => @Dyadic.numeric_lower hc_x0 hc_h) (fun hc_hn => @HypCheckProof.Dyadic.numeric_lower.h1.gneg hc_x0 hc_hn)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.numeric_lower.h1.derivable.{u} : ∀ (x : Dyadic), IGame.Numeric.{u} ↑x := by
  (intros; infer_instance)

