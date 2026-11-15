import Init

noncomputable instance HypCheckDec.ppolyNonNeg (p : Lean.Grind.CommRing.PPoly) : Decidable p.NonNeg :=
  Lean.Grind.CommRing.PPoly.rec (motive := fun p => Decidable p.NonNeg)
    (fun k => (inferInstance : Decidable (0 ≤ k)))
    (fun k _ _ _ ih => @instDecidableAnd (0 ≤ k) _ inferInstance ih) p
noncomputable instance HypCheckDec.ppolyDeg (B D : Nat) (p : Lean.Grind.CommRing.PPoly) : Decidable (p.Deg B D) :=
  Lean.Grind.CommRing.PPoly.rec (motive := fun p => Decidable (p.Deg B D))
    (fun _ => isTrue trivial)
    (fun _ _ v _ ih => @instDecidableAnd (Lean.Grind.CommRing.PPoly.dsum B v ≤ D) _ (Nat.decLe _ _) ih) p
noncomputable instance HypCheckDec.polyNonnegCoeffs (p : Lean.Grind.CommRing.Poly) : Decidable p.NonnegCoeffs :=
  Lean.Grind.CommRing.Poly.rec (motive := fun p => Decidable p.NonnegCoeffs)
    (fun c => if h : c ≥ 0 then isTrue (.num c h) else isFalse (fun hc => by cases hc; contradiction))
    (fun a m p ih => if h : a ≥ 0 then
        (match ih with
         | isTrue hp => isTrue (.add a m p h hp)
         | isFalse hp => isFalse (fun hc => by cases hc; contradiction))
      else isFalse (fun hc => by cases hc; contradiction)) p
noncomputable instance HypCheckDec.polyNonnegList (ps : List Lean.Grind.CommRing.Poly) : Decidable (Lean.Grind.CommRing.Poly.NonnegList ps) :=
  List.rec (motive := fun ps => Decidable (Lean.Grind.CommRing.Poly.NonnegList ps)) (isTrue trivial)
    (fun p _ ih => @instDecidableAnd p.NonnegCoeffs _ inferInstance ih) ps
noncomputable instance HypCheckDec.klistAllZero {α : Type} [Lean.Grind.Ring α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (ls : Lean.Grind.CommRing.KList) : Decidable (ls.AllZero ctx) :=
  Lean.Grind.CommRing.KList.rec (motive := fun ls => Decidable (ls.AllZero ctx)) (isTrue trivial)
    (fun _ _ q _ ih => @instDecidableAnd (q.denote ctx = 0) _ inferInstance ih) ls
noncomputable instance HypCheckDec.mlistAllZero {α : Type} [Lean.Grind.Ring α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (ls : Lean.Grind.CommRing.MList) : Decidable (ls.AllZero ctx) :=
  Lean.Grind.CommRing.MList.rec (motive := fun ls => Decidable (ls.AllZero ctx)) (isTrue trivial)
    (fun _ q _ ih => @instDecidableAnd (q.denote ctx = 0) _ inferInstance ih) ls
noncomputable instance HypCheckDec.invAtomsOk {α : Type} [Lean.Grind.Ring α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (l : Lean.Grind.CommRing.InvAtoms) : Decidable (Lean.Grind.CommRing.InvAtoms.ok ctx l) :=
  List.rec (motive := fun l => Decidable (Lean.Grind.CommRing.InvAtoms.ok ctx l)) (isTrue trivial)
    (fun yx _ ih => @instDecidableAnd (yx.2.denote ctx * yx.1.denote ctx = 1) _ inferInstance ih) l
noncomputable instance HypCheckDec.invVarsOk {α : Type} [Lean.Grind.Field α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (invs : Lean.Grind.CommRing.InvVars) : Decidable (invs.ok ctx) :=
  (inferInstance : Decidable (invs.denoteVars ctx = invs.denoteInvs))
noncomputable instance HypCheckDec.ppolyDegList (B D : Nat) (ps : List Lean.Grind.CommRing.PPoly) : Decidable (Lean.Grind.CommRing.PPoly.DegList B D ps) :=
  (inferInstance : Decidable (∀ p ∈ ps, p.Deg B D))


/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/
-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.cooper_unsat', hypothesis 13: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.cooper_unsat'.h13 : ¬∀ {a c b d e α β x : Int}, d > 1 → d ∣ c * x + e → α * c + β * d = 1 → -1 * x + a ≤ 0 → x + b ≤ 0 → False := fun hc_h => absurd (@hc_h (0) (1) (0) (2) (0) (1) (0) (0) (by
  decide) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.cooper_unsat'_helper, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.cooper_unsat'_helper.h7 : ¬∀ {a b d c : Int} {k : Int} {x : Int}, d > 0 → a ≤ x → x ≤ b → ¬b < Int.Internal.Linear.cdiv (a - c) d * d + c := fun hc_h => absurd (@hc_h (0) (0) (2) (1) (0) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.cooper_unsat'_helper, hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.cooper_unsat'_helper.h8 : ¬∀ {a b d c k x : Int}, d > 0 → x = k * d + c → x ≤ b → ¬b < Int.Internal.Linear.cdiv (a - c) d * d + c := fun hc_h => absurd (@hc_h (1) (0) (1) (0) (0) _ (by
  decide) rfl (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.cooper_unsat'_helper, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.cooper_unsat'_helper.h9 : ¬∀ {a b d c k x : Int}, d > 0 → x = k * d + c → a ≤ x → ¬b < Int.Internal.Linear.cdiv (a - c) d * d + c := fun hc_h => absurd (@hc_h (0) (-1) (1) (0) (0) _ (by
  decide) rfl (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.dvd_solve_elim', hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.dvd_solve_elim'.h8 : ¬∀ {x d₁ a₁ p₁ d₂ a₂ p₂ d : Int}, d₁ ∣ a₁ * x + p₁ → d₂ ∣ a₂ * x + p₂ → d ∣ a₂ * p₁ - a₁ * p₂ := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (1) (0) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.dvd_solve_elim', hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.dvd_solve_elim'.h9 : ¬∀ {x d₁ a₁ p₁ d₂ a₂ p₂ d : Int}, d = ↑((a₁ * d₂).gcd (a₂ * d₁)) → d₂ ∣ a₂ * x + p₂ → d ∣ a₂ * p₁ - a₁ * p₂ := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (0) (1) (0) _ rfl (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.dvd_solve_elim', hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.dvd_solve_elim'.h10 : ¬∀ {x d₁ a₁ p₁ d₂ a₂ p₂ d : Int}, d = ↑((a₁ * d₂).gcd (a₂ * d₁)) → d₁ ∣ a₁ * x + p₁ → d ∣ a₂ * p₁ - a₁ * p₂ := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (0) (0) (1) _ rfl (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.ex_of_dvd, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.ex_of_dvd.h7 : ¬∀ {α β a b d x : Int}, d > 1 → α * a + β * d = 1 → ∃ (k : Int), x = k * d + -α * b % d := fun hc_h => absurd (@hc_h (1) (0) (1) (0) (2) (1) (by
  decide) (by
  decide)) (by
  omega)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.ex_of_dvd, hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.ex_of_dvd.h8 : ¬∀ {α : Int} {β : Int} {a b d x : Int}, d > 1 → d ∣ a * x + b → ∃ (k : Int), x = k * d + -α * b % d := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (2) (1) (by
  decide) (by
  decide)) (by
  omega)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.eq_of_norm_eq_of_divCoeffs, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_norm_eq_of_divCoeffs.h4 : ¬∀ {ctx : Int.Internal.Linear.Context} {p₁ p₂ : Int.Internal.Linear.Poly} {k : Int},
        Int.Internal.Linear.Poly.divCoeffs k p₁ = Bool.true →
          p₂ = Int.Internal.Linear.Poly.div k p₁ →
            (Int.Internal.Linear.Poly.denote ctx p₁ ≤ 0 ↔ Int.Internal.Linear.Poly.denote ctx p₂ ≤ 0) := fun hc_h => absurd (@hc_h (.leaf 1 : Lean.RArray Int) (.num 1 : Int.Internal.Linear.Poly) _ (0) (by
  decide) rfl) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.eq_of_norm_eq_of_divCoeffs, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_norm_eq_of_divCoeffs.h5 : ¬∀ {ctx : Int.Internal.Linear.Context} {p₁ p₂ : Int.Internal.Linear.Poly} {k : Int},
        k > 0 →
          p₂ = Int.Internal.Linear.Poly.div k p₁ →
            (Int.Internal.Linear.Poly.denote ctx p₁ ≤ 0 ↔ Int.Internal.Linear.Poly.denote ctx p₂ ≤ 0) := fun hc_h => absurd (@hc_h (.leaf 1 : Lean.RArray Int) (.add 1 0 (.num 0) : Int.Internal.Linear.Poly) _ (2) (by
  decide) rfl) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.eq_of_norm_eq_of_divCoeffs, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_norm_eq_of_divCoeffs.h6 : ¬∀ {ctx : Int.Internal.Linear.Context} {p₁ p₂ : Int.Internal.Linear.Poly} {k : Int},
        k > 0 →
          Int.Internal.Linear.Poly.divCoeffs k p₁ = Bool.true →
            (Int.Internal.Linear.Poly.denote ctx p₁ ≤ 0 ↔ Int.Internal.Linear.Poly.denote ctx p₂ ≤ 0) := fun hc_h => absurd (@hc_h (.leaf 1 : Lean.RArray Int) (.num 0 : Int.Internal.Linear.Poly) (.add 1 0 (.num 0) : Int.Internal.Linear.Poly) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.eq_dvd_subst', hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.eq_dvd_subst'.h6 : ¬∀ {a x p d b q : Int}, d ∣ b * x + q → a * d ∣ a * q - b * p := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.eq_dvd_subst', hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.eq_dvd_subst'.h7 : ¬∀ {a x p d b q : Int}, a * x + p = 0 → a * d ∣ a * q - b * p := fun hc_h => absurd (@hc_h (1) (0) (0) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.poly_eq_zero_eq_false, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.poly_eq_zero_eq_false.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) {p : Int.Internal.Linear.Poly} {k : Int},
        Int.Internal.Linear.Poly.divCoeffs k p = Bool.true → k > 0 → (Int.Internal.Linear.Poly.denote ctx p = 0) = False := fun hc_h => absurd (@hc_h (.leaf 1 : Lean.RArray Int) (.num 0 : Int.Internal.Linear.Poly) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.norm_le_coeff', hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.norm_le_coeff'.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly) (k : Int),
        k > 0 → (Int.Internal.Linear.Poly.denote ctx p ≤ 0 ↔ Int.Internal.Linear.Poly.denote ctx p' ≤ 0) := fun hc_h => absurd (@hc_h (.leaf 1 : Lean.RArray Int) (.num 0 : Int.Internal.Linear.Poly) (.add 1 0 (.num 0) : Int.Internal.Linear.Poly) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.norm_le_coeff', hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.norm_le_coeff'.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly) (k : Int),
        p = p'.mul k → (Int.Internal.Linear.Poly.denote ctx p ≤ 0 ↔ Int.Internal.Linear.Poly.denote ctx p' ≤ 0) := fun hc_h => absurd (@hc_h (.leaf 1 : Lean.RArray Int) _ (.add 1 0 (.num 0) : Int.Internal.Linear.Poly) (0) rfl) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.cdiv_le, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.cdiv_le.h3 : ¬∀ {a d k : Int}, a ≤ k * d → Int.Internal.Linear.cdiv a d ≤ k := fun hc_h => absurd (@hc_h (0) (0) (-1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.cdiv_le, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.cdiv_le.h4 : ¬∀ {a d k : Int}, d > 0 → Int.Internal.Linear.cdiv a d ≤ k := fun hc_h => absurd (@hc_h (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.dvd_gcd_of_dvd, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.dvd_gcd_of_dvd.h4 : ¬∀ (d a x p : Int), Int.Internal.Linear.gcd d a ∣ p := fun hc_h => absurd (@hc_h (0) (0) (0) (1)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.mul_dvd_mul_eq, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.mul_dvd_mul_eq.h3 : ¬∀ {a b c : Int}, a * b ∣ a * c ↔ b ∣ c := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.not_dvd_of_not_mod_zero, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.not_dvd_of_not_mod_zero.h2 : ¬∀ {a b : Int}, ¬a ∣ b := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.one_emod_eq_one, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.one_emod_eq_one.h1 : ¬∀ {a : Int}, 1 % a = 1 := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.dvd_solve_combine', hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.dvd_solve_combine'.h10 : ¬∀ {x d₁ a₁ p₁ d₂ a₂ p₂ α β d : Int}, d₁ ∣ a₁ * x + p₁ → d₂ ∣ a₂ * x + p₂ → d₁ * d₂ ∣ d * x + α * d₂ * p₁ + β * d₁ * p₂ := fun hc_h => absurd (@hc_h (1) (0) (0) (0) (0) (0) (0) (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.dvd_solve_combine', hypothesis 11: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.dvd_solve_combine'.h11 : ¬∀ {x d₁ a₁ p₁ d₂ a₂ p₂ α β d : Int},
        α * a₁ * d₂ + β * a₂ * d₁ = d → d₂ ∣ a₂ * x + p₂ → d₁ * d₂ ∣ d * x + α * d₂ * p₁ + β * d₁ * p₂ := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (1) (0) (0) (1) (0) _ rfl (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.dvd_solve_combine', hypothesis 12: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.dvd_solve_combine'.h12 : ¬∀ {x d₁ a₁ p₁ d₂ a₂ p₂ α β d : Int},
        α * a₁ * d₂ + β * a₂ * d₁ = d → d₁ ∣ a₁ * x + p₁ → d₁ * d₂ ∣ d * x + α * d₂ * p₁ + β * d₁ * p₂ := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (0) (0) (1) (0) (1) _ rfl (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.le_tight_mod', hypothesis 4: removable
/- FAILED: 6:70: unexpected identifier after decimal point; consider parenthesizing the number | 22:70: unexpected identifier after decimal point; consider parenthesizing the number | 6:70: unexpected identifier after decimal point; consider parenthesizing the number | 22:70: unexpected identifier after decimal point; consider parenthesizing the number
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Int.Internal.Linear.le_tight_mod'.h4.gneg : ∀ {g K cm P : Int}, ¬0 < g → -g < cm → P = g * K + cm → P ≤ 0 → P + -cm ≤ 0 := by
  (intros; omega)
theorem HypCheckProof.Int.Internal.Linear.le_tight_mod'.h4 : ∀ {g K cm P : Int}, -g < cm → P = g * K + cm → P ≤ 0 → P + -cm ≤ 0 := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x5 hc_x6 hc_x7
  exact Classical.byCases (fun hc_h => @_private.Init.Data.Int.Linear.0.Int.Internal.Linear.le_tight_mod' hc_x0 hc_x1 hc_x2 hc_x3 hc_h hc_x5 hc_x6 hc_x7) (fun hc_hn => @HypCheckProof.Int.Internal.Linear.le_tight_mod'.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn hc_x5 hc_x6 hc_x7)
-/

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.le_tight_mod', hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.le_tight_mod'.h5 : ¬∀ {g K cm P : Int}, 0 < g → P = g * K + cm → P ≤ 0 → P + -cm ≤ 0 := fun hc_h => absurd (@hc_h (1) (1) (-1) _ (by
  decide) rfl (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.le_tight_mod', hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.le_tight_mod'.h6 : ¬∀ {g : Int} {K : Int} {cm P : Int}, 0 < g → -g < cm → P ≤ 0 → P + -cm ≤ 0 := fun hc_h => absurd (@hc_h (2) (0) (-1) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.le_tight_mod', hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.le_tight_mod'.h7 : ¬∀ {g K cm P : Int}, 0 < g → -g < cm → P = g * K + cm → P + -cm ≤ 0 := fun hc_h => absurd (@hc_h (1) (1) (0) _ (by
  decide) (by
  decide) rfl) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.contra, hypothesis 3: removable
/- FAILED: 6:70: unexpected identifier after decimal point; consider parenthesizing the number | 21:70: unexpected identifier after decimal point; consider parenthesizing the number | 6:70: unexpected identifier after decimal point; consider parenthesizing the number | 21:70: unexpected identifier after decimal point; consider parenthesizing the number
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Int.Internal.Linear.contra.h3.gneg : ∀ {a b k : Int}, ¬0 < k → -k < b → b < 0 → a * k + b = 0 → False := by
  (intros; omega)
theorem HypCheckProof.Int.Internal.Linear.contra.h3 : ∀ {a b k : Int}, -k < b → b < 0 → a * k + b = 0 → False := by
  intro hc_x0 hc_x1 hc_x2 hc_x4 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @_private.Init.Data.Int.Linear.0.Int.Internal.Linear.contra hc_x0 hc_x1 hc_x2 hc_h hc_x4 hc_x5 hc_x6) (fun hc_hn => @HypCheckProof.Int.Internal.Linear.contra.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4 hc_x5 hc_x6)
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Int.Internal.Linear.contra.h3.derivable : ∀ {a b k : Int}, -k < b → b < 0 → a * k + b = 0 → 0 < k := by
  (intros; omega)
-/

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.contra, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.contra.h4 : ¬∀ {a b k : Int}, 0 < k → b < 0 → a * k + b = 0 → False := fun hc_h => absurd (@hc_h (1) (-1) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.contra, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.contra.h5 : ¬∀ {a b k : Int}, 0 < k → -k < b → a * k + b = 0 → False := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.contra, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.contra.h6 : ¬∀ {a : Int} {b k : Int}, 0 < k → -k < b → b < 0 → False := fun hc_h => absurd (@hc_h (0) (-1) (2) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.ofNat_lt, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.ofNat_lt.h2 : ¬∀ {a : Int} {n : Nat}, a < Int.ofNat n → a.toNat < n := fun hc_h => absurd (@hc_h (-1) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.ofNat_lt, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.ofNat_lt.h3 : ¬∀ {a : Int} {n : Nat}, a ≥ 0 → a.toNat < n := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.gcd_dvd_step, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.gcd_dvd_step.h4 : ¬∀ {k a b : Int} {x : Int}, Int.Internal.Linear.gcd a k ∣ b := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.mul_add_cmod_le_iff, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.mul_add_cmod_le_iff.h3 : ¬∀ {a k b : Int}, a * k + Int.Internal.Linear.cmod b k ≤ 0 ↔ a ≤ 0 := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.dvd_eq_false', hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.dvd_eq_false'.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (k : Int) (p : Int.Internal.Linear.Poly),
        (k ∣ Int.Internal.Linear.Poly.denote' ctx p) = False := fun hc_h => absurd (@hc_h (.leaf 1 : Lean.RArray Int) (0) (.num 0 : Int.Internal.Linear.Poly)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.abs_dvd, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.abs_dvd.h2 : ¬∀ {a p : Int}, Int.Internal.Linear.abs a ∣ p := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.mul_eq_zero_iff, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.mul_eq_zero_iff.h2 : ¬∀ (a k : Int), k * a = 0 ↔ a = 0 := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.mul_le_zero_iff, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.mul_le_zero_iff.h2 : ¬∀ (a k : Int), k * a ≤ 0 ↔ a ≤ 0 := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.ofNat_toNat, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.ofNat_toNat.h1 : ¬∀ {a : Int}, Int.ofNat a.toNat = a := fun hc_h => absurd (@hc_h (-1)) (by
  decide +kernel)

-- _private.Init.Data.Int.Linear.0.Int.Internal.Linear.cast_toNat, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int.Internal.Linear.cast_toNat.h1 : ¬∀ {a : Int}, ↑a.toNat = a := fun hc_h => absurd (@hc_h (-1)) (by
  decide +kernel)

