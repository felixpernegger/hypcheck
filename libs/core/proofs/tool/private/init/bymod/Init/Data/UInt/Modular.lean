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
-- _private.Init.Data.UInt.Modular.0.UInt64.inv_unique, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.inv_unique.h4 : ¬∀ {A x y m : Nat}, y < m → A * x % m = 1 % m → A * y % m = 1 % m → x = y := fun hc_h => absurd (@hc_h (0) (1) (0) (1) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.inv_unique, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.inv_unique.h5 : ¬∀ {A x y m : Nat}, x < m → A * x % m = 1 % m → A * y % m = 1 % m → x = y := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.inv_unique, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.inv_unique.h6 : ¬∀ {A x y m : Nat}, x < m → y < m → A * y % m = 1 % m → x = y := fun hc_h => absurd (@hc_h (1) (0) (1) (2) (by
  decide) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.inv_unique, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.inv_unique.h7 : ¬∀ {A x y m : Nat}, x < m → y < m → A * x % m = 1 % m → x = y := fun hc_h => absurd (@hc_h (1) (1) (0) (2) (by
  decide) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.toNat_powModChunk_snd, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.toNat_powModChunk_snd.h5 : ¬∀ (modulus : UInt64) (n : Nat) (base e result : UInt64),
        result.toNat < UInt64.wrapMod modulus →
          (modulus.powModChunk n base e result).snd.toNat = result.toNat * base.toNat ^ e.toNat % UInt64.wrapMod modulus := fun hc_h => absurd (@hc_h (UInt64.ofNat 0) (0) (UInt64.ofNat 0) (UInt64.ofNat 1) (UInt64.ofNat 1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.toNat_powModChunk_snd, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.toNat_powModChunk_snd.h6 : ¬∀ (modulus : UInt64) (n : Nat) (base e result : UInt64),
        e.toNat < 2 ^ n →
          (modulus.powModChunk n base e result).snd.toNat = result.toNat * base.toNat ^ e.toNat % UInt64.wrapMod modulus := fun hc_h => absurd (@hc_h (UInt64.ofNat 1) (0) (UInt64.ofNat 0) (UInt64.ofNat 0) (UInt64.ofNat 1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.gcd_eq_one_of_mul_mod, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.gcd_eq_one_of_mul_mod.h3 : ¬∀ {A : Nat} {x : Nat} {m : Nat}, A.gcd m = 1 := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.toNat_condSub, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.toNat_condSub.h3 : ¬∀ {a b modulus : UInt64},
        (if b ≤ a then a - b else modulus - (b - a)).toNat =
          if b.toNat ≤ a.toNat then a.toNat - b.toNat else modulus.toNat - (b.toNat - a.toNat) := fun hc_h => absurd (@hc_h (UInt64.ofNat 0) (UInt64.ofNat 1) (UInt64.ofNat 0)) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.invMod?_spec, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.invMod?_spec.h2 : ¬∀ {a modulus : UInt64},
        match UInt64.invMod?.go modulus (a.toNat % modulus.toNat) modulus.toNat (1 % modulus.toNat) 0 with
        | (gcd, inverse) =>
          gcd = a.toNat.gcd modulus.toNat ∧
            inverse < modulus.toNat ∧ inverse * a.toNat % modulus.toNat = a.toNat.gcd modulus.toNat % modulus.toNat := fun hc_h => absurd (@hc_h (UInt64.ofNat 0) (UInt64.ofNat 0)) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.invMod?_go_spec, hypothesis 1: removable
/- FAILED: 22:72: unexpected identifier after decimal point; consider parenthesizing the number | 44:72: unexpected identifier after decimal point; consider parenthesizing the number | 22:72: unexpected identifier after decimal point; consider parenthesizing the number | 44:72: unexpected identifier after decimal point; consider parenthesizing the number
set_option maxHeartbeats 1000 in
theorem HypCheckProof.UInt64.invMod?_go_spec.h1.gneg : ∀ (modulus : UInt64),
      ¬modulus ≠ 0 →
        ∀ (a oldR r oldS s : Nat),
          oldS < modulus.toNat →
            s < modulus.toNat →
              oldS * a % modulus.toNat = oldR % modulus.toNat →
                s * a % modulus.toNat = r % modulus.toNat →
                  match UInt64.invMod?.go modulus oldR r oldS s with
                  | (gcd, inverse) =>
                    gcd = oldR.gcd r ∧ inverse < modulus.toNat ∧ inverse * a % modulus.toNat = oldR.gcd r % modulus.toNat := by
  (intros; simp_all; done)
theorem HypCheckProof.UInt64.invMod?_go_spec.h1 : ∀ (modulus : UInt64) (a oldR r oldS s : Nat),
      oldS < modulus.toNat →
        s < modulus.toNat →
          oldS * a % modulus.toNat = oldR % modulus.toNat →
            s * a % modulus.toNat = r % modulus.toNat →
              match UInt64.invMod?.go modulus oldR r oldS s with
              | (gcd, inverse) =>
                gcd = oldR.gcd r ∧ inverse < modulus.toNat ∧ inverse * a % modulus.toNat = oldR.gcd r % modulus.toNat := by
  intro hc_x0 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10
  exact Classical.byCases (fun hc_h => @_private.Init.Data.UInt.Modular.0.UInt64.invMod?_go_spec hc_x0 hc_h hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10) (fun hc_hn => @HypCheckProof.UInt64.invMod?_go_spec.h1.gneg hc_x0 hc_hn hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10)
set_option maxHeartbeats 1000 in
theorem HypCheckProof.UInt64.invMod?_go_spec.h1.derivable : ∀ (modulus : UInt64) (a oldR r oldS s : Nat),
      oldS < modulus.toNat →
        s < modulus.toNat →
          oldS * a % modulus.toNat = oldR % modulus.toNat → s * a % modulus.toNat = r % modulus.toNat → modulus ≠ 0 := by
  (intros; grind)
-/

-- _private.Init.Data.UInt.Modular.0.UInt64.invMod?_go_spec, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.invMod?_go_spec.h7 : ¬∀ (modulus : UInt64),
        modulus ≠ 0 →
          ∀ (a oldR r oldS s : Nat),
            s < modulus.toNat →
              oldS * a % modulus.toNat = oldR % modulus.toNat →
                s * a % modulus.toNat = r % modulus.toNat →
                  match UInt64.invMod?.go modulus oldR r oldS s with
                  | (gcd, inverse) =>
                    gcd = oldR.gcd r ∧ inverse < modulus.toNat ∧ inverse * a % modulus.toNat = oldR.gcd r % modulus.toNat := fun hc_h => absurd (@hc_h (UInt64.ofNat 1) (by
  decide) (0) (0) (0) (1) (0) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.invMod?_go_spec, hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.invMod?_go_spec.h8 : ¬∀ (modulus : UInt64),
        modulus ≠ 0 →
          ∀ (a oldR r oldS s : Nat),
            oldS < modulus.toNat →
              oldS * a % modulus.toNat = oldR % modulus.toNat →
                s * a % modulus.toNat = r % modulus.toNat →
                  match UInt64.invMod?.go modulus oldR r oldS s with
                  | (gcd, inverse) =>
                    gcd = oldR.gcd r ∧ inverse < modulus.toNat ∧ inverse * a % modulus.toNat = oldR.gcd r % modulus.toNat := fun hc_h => absurd (@hc_h (UInt64.ofNat 1) (by
  decide) (0) (0) (1) (0) (1) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.invMod?_go_spec, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.invMod?_go_spec.h9 : ¬∀ (modulus : UInt64),
        modulus ≠ 0 →
          ∀ (a oldR r oldS s : Nat),
            oldS < modulus.toNat →
              s < modulus.toNat →
                s * a % modulus.toNat = r % modulus.toNat →
                  match UInt64.invMod?.go modulus oldR r oldS s with
                  | (gcd, inverse) =>
                    gcd = oldR.gcd r ∧ inverse < modulus.toNat ∧ inverse * a % modulus.toNat = oldR.gcd r % modulus.toNat := fun hc_h => absurd (@hc_h (UInt64.ofNat 2) (by
  decide) (0) (1) (0) (0) (0) (by
  decide) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.invMod?_go_spec, hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.invMod?_go_spec.h10 : ¬∀ (modulus : UInt64),
        modulus ≠ 0 →
          ∀ (a oldR r oldS s : Nat),
            oldS < modulus.toNat →
              s < modulus.toNat →
                oldS * a % modulus.toNat = oldR % modulus.toNat →
                  match UInt64.invMod?.go modulus oldR r oldS s with
                  | (gcd, inverse) =>
                    gcd = oldR.gcd r ∧ inverse < modulus.toNat ∧ inverse * a % modulus.toNat = oldR.gcd r % modulus.toNat := fun hc_h => absurd (@hc_h (UInt64.ofNat 2) (by
  decide) (0) (0) (1) (0) (0) (by
  decide) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.nextS_mul_mod, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.nextS_mul_mod.h5 : ¬∀ {m oldS product a X : Nat},
        oldS * a % m = (X + product * a) % m →
          (if product ≤ oldS then oldS - product else m - (product - oldS)) * a % m = X % m := fun hc_h => absurd (@hc_h (2) (0) (3) (1) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.nextS_mul_mod, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.nextS_mul_mod.h6 : ¬∀ {m oldS product a X : Nat},
        product < m → (if product ≤ oldS then oldS - product else m - (product - oldS)) * a % m = X % m := fun hc_h => absurd (@hc_h (2) (0) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.invMod?_eq_some_spec, hypothesis 3: removable
/- FAILED: 9:72: unexpected identifier after decimal point; consider parenthesizing the number | 21:72: unexpected identifier after decimal point; consider parenthesizing the number | 9:72: unexpected identifier after decimal point; consider parenthesizing the number | 21:72: unexpected identifier after decimal point; consider parenthesizing the number
set_option maxHeartbeats 1000 in
theorem HypCheckProof.UInt64.invMod?_eq_some_spec.h3.gneg : ∀ {a modulus x : UInt64},
      ¬modulus ≠ 0 →
        a.invMod? modulus = Option.some x → x.toNat < modulus.toNat ∧ a.toNat * x.toNat % modulus.toNat = 1 % modulus.toNat := by
  (intros; simp_all; done)
theorem HypCheckProof.UInt64.invMod?_eq_some_spec.h3 : ∀ {a modulus x : UInt64},
      a.invMod? modulus = Option.some x → x.toNat < modulus.toNat ∧ a.toNat * x.toNat % modulus.toNat = 1 % modulus.toNat := by
  intro hc_x0 hc_x1 hc_x2 hc_x4
  exact Classical.byCases (fun hc_h => @_private.Init.Data.UInt.Modular.0.UInt64.invMod?_eq_some_spec hc_x0 hc_x1 hc_x2 hc_h hc_x4) (fun hc_hn => @HypCheckProof.UInt64.invMod?_eq_some_spec.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4)
-/

-- _private.Init.Data.UInt.Modular.0.UInt64.invMod?_eq_some_spec, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.invMod?_eq_some_spec.h4 : ¬∀ {a modulus x : UInt64}, modulus ≠ 0 → x.toNat < modulus.toNat ∧ a.toNat * x.toNat % modulus.toNat = 1 % modulus.toNat := fun hc_h => absurd (@hc_h (UInt64.ofNat 0) (UInt64.ofNat 1) (UInt64.ofNat 1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.mul_pow_pow_mod, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.mul_pow_pow_mod.h6 : ¬∀ {a b c w k n : Nat}, a * c ^ k % n = a * b ^ (w * k) % n := fun hc_h => absurd (@hc_h (1) (0) (0) (0) (1) (0)) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.invModImpl_go_eq, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.invModImpl_go_eq.h1 : ¬∀ (modulus oldR r oldS s : UInt64),
        UInt64.invModImpl.go modulus oldR r oldS s =
          if (UInt64.invMod?.go modulus oldR.toNat r.toNat oldS.toNat s.toNat).fst = 1 then
            Option.some (UInt64.ofNat (UInt64.invMod?.go modulus oldR.toNat r.toNat oldS.toNat s.toNat).snd)
          else Option.none := fun hc_h => absurd (@hc_h (UInt64.ofNat 0) (UInt64.ofNat 2) (UInt64.ofNat 3) (UInt64.ofNat 1) (UInt64.ofNat 0)) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.toNat_powModWord, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.toNat_powModWord.h4 : ¬∀ (base e modulus result : UInt64),
        (base.powModWord e modulus result).toNat = result.toNat * base.toNat ^ e.toNat % UInt64.wrapMod modulus := fun hc_h => absurd (@hc_h (UInt64.ofNat 0) (UInt64.ofNat 0) (UInt64.ofNat 1) (UInt64.ofNat 1)) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.toNat_condMul, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.toNat_condMul.h4 : ¬∀ {base result modulus e : UInt64},
        (if e % 2 = 1 then result.mulMod base modulus else result).toNat =
          result.toNat * base.toNat ^ (e.toNat % 2) % UInt64.wrapMod modulus := fun hc_h => absurd (@hc_h (UInt64.ofNat 0) (UInt64.ofNat 1) (UInt64.ofNat 1) (UInt64.ofNat 0)) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.toNat_powModImpl_go, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.toNat_powModImpl_go.h4 : ¬∀ (modulus base : UInt64) (e : Nat) (result : UInt64),
        (UInt64.powModImpl.go modulus base e result).toNat = result.toNat * base.toNat ^ e % UInt64.wrapMod modulus := fun hc_h => absurd (@hc_h (UInt64.ofNat 1) (UInt64.ofNat 0) (0) (UInt64.ofNat 1)) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.toNat_condMul_lt, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.toNat_condMul_lt.h4 : ¬∀ {base result modulus e : UInt64},
        (if e % 2 = 1 then result.mulMod base modulus else result).toNat < UInt64.wrapMod modulus := fun hc_h => absurd (@hc_h (UInt64.ofNat 0) (UInt64.ofNat 1) (UInt64.ofNat 1) (UInt64.ofNat 0)) (by
  decide +kernel)

-- _private.Init.Data.UInt.Modular.0.UInt64.toNat_ne_zero, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt64.toNat_ne_zero.h1 : ¬∀ {modulus : UInt64}, modulus.toNat ≠ 0 := fun hc_h => absurd (@hc_h (UInt64.ofNat 0)) (by
  decide +kernel)

