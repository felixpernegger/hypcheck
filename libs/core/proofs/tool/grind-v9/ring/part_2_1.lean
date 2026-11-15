import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.CommRing.lt_normQ_expr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_normQ_expr.h6 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] [inst_2 : LE α] [inst_3 : LT α]
        [inst_4 : Std.LawfulOrderLT α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (invs : Lean.Grind.CommRing.InvVars),
        Lean.Grind.CommRing.InvVars.ok ctx invs →
          ∀ (ainvs : Lean.Grind.CommRing.InvAtoms),
            Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
              ∀ (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
                Lean.Grind.CommRing.normQ_cert bal invs ainvs lhs rhs lhs' rhs' = Bool.true → Std.IsLinearOrder α := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (⟨fun a b => a < b⟩ : LE Rat) (Rat.instLT) (@Std.LawfulOrderLT.mk (Rat) (Rat.instLT) (@LE.mk Rat fun (a b : Rat) => @LT.lt Rat Rat.instLT a b) (by (try dsimp only);   grind)) (.leaf 1 : Lean.RArray Rat) (Bool.false) ([]) (by
  rfl) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPartialOrder.toIsPreorder.le_refl (0 : Rat))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.CommRing.lt_normQ_expr, hypothesis 18: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_normQ_expr.h18 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] [inst_2 : LE α] [inst_3 : LT α]
        [inst_4 : Std.LawfulOrderLT α] [inst_5 : Std.IsLinearOrder α] [inst_6 : Lean.Grind.OrderedRing α]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (invs : Lean.Grind.CommRing.InvVars),
        Lean.Grind.CommRing.InvVars.ok ctx invs →
          ∀ (ainvs : Lean.Grind.CommRing.InvAtoms),
            Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
              ∀ (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
                (Lean.Grind.CommRing.Expr.denote ctx lhs < Lean.Grind.CommRing.Expr.denote ctx rhs) =
                  (Lean.Grind.CommRing.Expr.denote ctx lhs' < Lean.Grind.CommRing.Expr.denote ctx rhs') := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (Rat.instLE) (Rat.instLT) _ _ _ (.leaf 1 : Lean.RArray Rat) (Bool.false) ([]) (by
  rfl) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr)) (by
  decide +kernel)

-- Lean.Grind.CommRing.eq_true_of_denote_toPolyQ_eq, hypothesis 15: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_denote_toPolyQ_eq.h15 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (bal₁ bal₂ : Bool) (invs : Lean.Grind.CommRing.InvVars),
        Lean.Grind.CommRing.InvVars.ok ctx invs →
          ∀ (ainvs : Lean.Grind.CommRing.InvAtoms),
            Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
              ∀ (lhs rhs : Lean.Grind.CommRing.Expr) (pl pr : Lean.Grind.CommRing.Poly) (q : Lean.Grind.CommRing.PolyQ),
                Lean.Grind.CommRing.Expr.denote ctx rhs = Lean.Grind.CommRing.Poly.denote ctx pr →
                  q = Lean.Grind.CommRing.Poly.toPolyQX_k bal₁ pl invs ainvs →
                    q = Lean.Grind.CommRing.Poly.toPolyQX_k bal₂ pr invs ainvs →
                      (Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Expr.denote ctx rhs) = True := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 1 : Lean.RArray Rat) (Bool.false) (Bool.false) ([]) (by
  rfl) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.var 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) _ (by
  decide) rfl (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Lean.Grind.CommRing.eq_true_of_denote_toPolyQ_eq, hypothesis 16: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_denote_toPolyQ_eq.h16 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (bal₁ bal₂ : Bool) (invs : Lean.Grind.CommRing.InvVars),
        Lean.Grind.CommRing.InvVars.ok ctx invs →
          ∀ (ainvs : Lean.Grind.CommRing.InvAtoms),
            Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
              ∀ (lhs rhs : Lean.Grind.CommRing.Expr) (pl pr : Lean.Grind.CommRing.Poly) (q : Lean.Grind.CommRing.PolyQ),
                Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Poly.denote ctx pl →
                  q = Lean.Grind.CommRing.Poly.toPolyQX_k bal₁ pl invs ainvs →
                    q = Lean.Grind.CommRing.Poly.toPolyQX_k bal₂ pr invs ainvs →
                      (Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Expr.denote ctx rhs) = True := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 1 : Lean.RArray Rat) (Bool.false) (Bool.false) ([]) (by
  rfl) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) _ (by
  decide) rfl (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Lean.Grind.CommRing.eq_true_of_denote_toPolyQ_eq, hypothesis 17: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_denote_toPolyQ_eq.h17 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (bal₁ bal₂ : Bool) (invs : Lean.Grind.CommRing.InvVars),
        Lean.Grind.CommRing.InvVars.ok ctx invs →
          ∀ (ainvs : Lean.Grind.CommRing.InvAtoms),
            Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
              ∀ (lhs rhs : Lean.Grind.CommRing.Expr) (pl pr : Lean.Grind.CommRing.Poly) (q : Lean.Grind.CommRing.PolyQ),
                Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Poly.denote ctx pl →
                  Lean.Grind.CommRing.Expr.denote ctx rhs = Lean.Grind.CommRing.Poly.denote ctx pr →
                    q = Lean.Grind.CommRing.Poly.toPolyQX_k bal₂ pr invs ainvs →
                      (Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Expr.denote ctx rhs) = True := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 1 : Lean.RArray Rat) (Bool.false) (Bool.false) ([]) (by
  rfl) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) _ (by
  decide) (by
  decide +kernel) rfl) (by
  decide +kernel)

-- Lean.Grind.CommRing.eq_true_of_denote_toPolyQ_eq, hypothesis 18: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_denote_toPolyQ_eq.h18 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (bal₁ bal₂ : Bool) (invs : Lean.Grind.CommRing.InvVars),
        Lean.Grind.CommRing.InvVars.ok ctx invs →
          ∀ (ainvs : Lean.Grind.CommRing.InvAtoms),
            Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
              ∀ (lhs rhs : Lean.Grind.CommRing.Expr) (pl pr : Lean.Grind.CommRing.Poly) (q : Lean.Grind.CommRing.PolyQ),
                Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Poly.denote ctx pl →
                  Lean.Grind.CommRing.Expr.denote ctx rhs = Lean.Grind.CommRing.Poly.denote ctx pr →
                    q = Lean.Grind.CommRing.Poly.toPolyQX_k bal₁ pl invs ainvs →
                      (Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Expr.denote ctx rhs) = True := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 1 : Lean.RArray Rat) (Bool.false) (Bool.false) ([]) (by
  rfl) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) _ (by
  decide) (by
  decide +kernel) rfl) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.d_stepsKC, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsKC.h13 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k : Int) (init : Lean.Grind.CommRing.Poly) (K B : Nat)
        (p₁ p : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly) (ls : Lean.Grind.CommRing.KList),
        @Eq Bool
            ((Lean.Grind.CommRing.Poly.kron_k K B p).beq'
              (((Lean.Grind.CommRing.Poly.kron_k K B p₁).add_k (Lean.Grind.CommRing.KList.kron_k K B ls)).add_k
                ((Int.ofNat c).mul_k (Lean.Grind.CommRing.PPoly.kron_k K E))))
            Bool.true →
          @Lean.Grind.CommRing.KList.AllZero α (@Lean.Grind.CommRing.toRing α inst) ctx ls →
            @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁) →
              @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => absurd (@hc_h (Int : Type) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (.leaf 0 : Lean.RArray Int) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (.num 0 : Lean.Grind.CommRing.Poly) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 1 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.PPoly) (.nil : Lean.Grind.CommRing.KList) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.d_stepsKC, hypothesis 16: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsKC.h16 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k : Int) (init : Lean.Grind.CommRing.Poly) (K B : Nat)
        (p₁ p : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly) (ls : Lean.Grind.CommRing.KList),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.kronOk_k K B c p₁ p E ls) Bool.true →
          @Eq Bool
              ((Lean.Grind.CommRing.Poly.kron_k K B p).beq'
                (((Lean.Grind.CommRing.Poly.kron_k K B p₁).add_k (Lean.Grind.CommRing.KList.kron_k K B ls)).add_k
                  ((Int.ofNat c).mul_k (Lean.Grind.CommRing.PPoly.kron_k K E))))
              Bool.true →
            @Lean.Grind.CommRing.KList.AllZero α (@Lean.Grind.CommRing.toRing α inst) ctx ls →
              @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => absurd (@hc_h (Int : Type) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (.leaf 1 : Lean.RArray Int) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.PPoly) (.nil : Lean.Grind.CommRing.KList) (by
  decide) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  decide +kernel)

-- Lean.Grind.CommRing.eq_true_of_toPolyQ_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPolyQ_eq.h7 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (bal₁ bal₂ : Bool) (invs : Lean.Grind.CommRing.InvVars) (ainvs : Lean.Grind.CommRing.InvAtoms),
        Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
          ∀ (lhs rhs : Lean.Grind.CommRing.Expr) (q : Lean.Grind.CommRing.PolyQ),
            q = Lean.Grind.CommRing.Poly.toPolyQX_k bal₁ (Lean.Grind.CommRing.Expr.toPolyX_k bal₁ lhs) invs ainvs →
              q = Lean.Grind.CommRing.Poly.toPolyQX_k bal₂ (Lean.Grind.CommRing.Expr.toPolyX_k bal₂ rhs) invs ainvs →
                (Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Expr.denote ctx rhs) = True := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 0 : Lean.RArray Rat) (Bool.false) (Bool.false) ([(0, 1)]) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.var 0 : Lean.Grind.CommRing.Expr) (.num 1 : Lean.Grind.CommRing.Expr) _ rfl (by
  rfl)) (by
  decide +kernel)

-- Lean.Grind.CommRing.eq_true_of_toPolyQ_eq, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPolyQ_eq.h13 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (bal₁ bal₂ : Bool) (invs : Lean.Grind.CommRing.InvVars),
        Lean.Grind.CommRing.InvVars.ok ctx invs →
          ∀ (ainvs : Lean.Grind.CommRing.InvAtoms),
            Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
              ∀ (lhs rhs : Lean.Grind.CommRing.Expr) (q : Lean.Grind.CommRing.PolyQ),
                q = Lean.Grind.CommRing.Poly.toPolyQX_k bal₂ (Lean.Grind.CommRing.Expr.toPolyX_k bal₂ rhs) invs ainvs →
                  (Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Expr.denote ctx rhs) = True := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 1 : Lean.RArray Rat) (Bool.false) (Bool.false) ([]) (by
  rfl) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr) _ rfl) (by
  decide +kernel)

-- Lean.Grind.CommRing.eq_true_of_toPolyQ_eq, hypothesis 14: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPolyQ_eq.h14 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (bal₁ bal₂ : Bool) (invs : Lean.Grind.CommRing.InvVars),
        Lean.Grind.CommRing.InvVars.ok ctx invs →
          ∀ (ainvs : Lean.Grind.CommRing.InvAtoms),
            Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
              ∀ (lhs rhs : Lean.Grind.CommRing.Expr) (q : Lean.Grind.CommRing.PolyQ),
                q = Lean.Grind.CommRing.Poly.toPolyQX_k bal₁ (Lean.Grind.CommRing.Expr.toPolyX_k bal₁ lhs) invs ainvs →
                  (Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Expr.denote ctx rhs) = True := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 1 : Lean.RArray Rat) (Bool.false) (Bool.false) ([]) (by
  rfl) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr) _ rfl) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.simpsKC, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsKC.h11 : ¬∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] [inst_1 : Lean.Grind.IsCharP α c]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (p₁ p : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly)
        (ls : Lean.Grind.CommRing.KList),
        (Lean.Grind.CommRing.Poly.kron_k K B p).beq'
              (((Lean.Grind.CommRing.Poly.kron_k K B p₁).add_k (Lean.Grind.CommRing.KList.kron_k K B ls)).add_k
                ((Int.ofNat c).mul_k (Lean.Grind.CommRing.PPoly.kron_k K E))) =
            Bool.true →
          Lean.Grind.CommRing.KList.AllZero ctx ls →
            Lean.Grind.CommRing.Poly.denote ctx p₁ = 0 → Lean.Grind.CommRing.Poly.denote ctx p = 0 := fun hc_h => absurd (@hc_h (Int : Type) (0) (Lean.Grind.instCommRingInt) _ (.leaf 0 : Lean.RArray Int) (0) (0) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 1 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.PPoly) (.nil : Lean.Grind.CommRing.KList) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.simpsKC, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsKC.h12 : ¬∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] [inst_1 : Lean.Grind.IsCharP α c]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (p₁ p : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly)
        (ls : Lean.Grind.CommRing.KList),
        Lean.Grind.CommRing.Stepwise.kronOk_k K B c p₁ p E ls = Bool.true →
          Lean.Grind.CommRing.KList.AllZero ctx ls →
            Lean.Grind.CommRing.Poly.denote ctx p₁ = 0 → Lean.Grind.CommRing.Poly.denote ctx p = 0 := fun hc_h => absurd (@hc_h (Int : Type) (0) (Lean.Grind.instCommRingInt) _ (.leaf 1 : Lean.RArray Int) (2) (2) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.PPoly) (.nil : Lean.Grind.CommRing.KList) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.eq_normQ_expr, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_normQ_expr.h13 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (bal : Bool) (invs : Lean.Grind.CommRing.InvVars),
        Lean.Grind.CommRing.InvVars.ok ctx invs →
          ∀ (ainvs : Lean.Grind.CommRing.InvAtoms),
            Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
              ∀ (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
                (Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Expr.denote ctx rhs) =
                  (Lean.Grind.CommRing.Expr.denote ctx lhs' = Lean.Grind.CommRing.Expr.denote ctx rhs') := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 1 : Lean.RArray Rat) (Bool.false) ([]) (by
  rfl) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.d_stepsK, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsK.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (init : Lean.Grind.CommRing.Poly) (K B : Nat) (p₁ p : Lean.Grind.CommRing.Poly) (ls : Lean.Grind.CommRing.KList),
        @Eq Bool
            ((Lean.Grind.CommRing.Poly.kron_k K B p).beq'
              ((Lean.Grind.CommRing.Poly.kron_k K B p₁).add_k (Lean.Grind.CommRing.KList.kron_k K B ls)))
            Bool.true →
          @Lean.Grind.CommRing.KList.AllZero α (@Lean.Grind.CommRing.toRing α inst) ctx ls →
            @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁) →
              @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 0 : Lean.RArray Int) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (.num 0 : Lean.Grind.CommRing.Poly) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 1 : Lean.Grind.CommRing.Poly) (.nil : Lean.Grind.CommRing.KList) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.d_stepsK, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsK.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (init : Lean.Grind.CommRing.Poly) (K B : Nat) (p₁ p : Lean.Grind.CommRing.Poly) (ls : Lean.Grind.CommRing.KList),
        @Eq Bool
            (Lean.Grind.CommRing.Stepwise.kronOk_k K B (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p₁ p
              (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ls)
            Bool.true →
          @Lean.Grind.CommRing.KList.AllZero α (@Lean.Grind.CommRing.toRing α inst) ctx ls →
            @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁) →
              @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 1 : Lean.RArray Int) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (.num 0 : Lean.Grind.CommRing.Poly) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.nil : Lean.Grind.CommRing.KList) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.d_stepsK, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsK.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (init : Lean.Grind.CommRing.Poly) (K B : Nat) (p₁ p : Lean.Grind.CommRing.Poly) (ls : Lean.Grind.CommRing.KList),
        @Eq Bool
            (Lean.Grind.CommRing.Stepwise.kronOk_k K B (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p₁ p
              (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ls)
            Bool.true →
          @Eq Bool
              ((Lean.Grind.CommRing.Poly.kron_k K B p).beq'
                ((Lean.Grind.CommRing.Poly.kron_k K B p₁).add_k (Lean.Grind.CommRing.KList.kron_k K B ls)))
              Bool.true →
            @Lean.Grind.CommRing.KList.AllZero α (@Lean.Grind.CommRing.toRing α inst) ctx ls →
              @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 1 : Lean.RArray Int) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) (.nil : Lean.Grind.CommRing.KList) (by
  decide) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  decide +kernel)

-- Lean.Grind.CommRing.le_normA_expr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.le_normA_expr.h4 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] (ctx : Lean.Grind.CommRing.Context α)
        (ainvs : Lean.Grind.CommRing.InvAtoms),
        Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
          ∀ (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
            Lean.Grind.CommRing.normA_cert ainvs lhs rhs lhs' rhs' = Bool.true → Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (⟨fun _ _ => False⟩ : LE Int) (Int.instLTInt) (.leaf 1 : Lean.RArray Int) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.CommRing.le_normA_expr, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.le_normA_expr.h13 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.IsPreorder α]
        [inst_4 : Lean.Grind.OrderedRing α] (ctx : Lean.Grind.CommRing.Context α) (ainvs : Lean.Grind.CommRing.InvAtoms),
        Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
          ∀ (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
            (Lean.Grind.CommRing.Expr.denote ctx lhs ≤ Lean.Grind.CommRing.Expr.denote ctx rhs) =
              (Lean.Grind.CommRing.Expr.denote ctx lhs' ≤ Lean.Grind.CommRing.Expr.denote ctx rhs') := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (.leaf 1 : Lean.RArray Int) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr)) (by
  decide +kernel)

-- Lean.Grind.CommRing.le_false_of_poly, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_false_of_poly.h4.inst : ¬True = False := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_false_of_poly.h4.prem0 : Lean.Grind.CommRing.Expr.toPolyX_k Bool.false ((Lean.Grind.CommRing.Expr.num 1).sub (Lean.Grind.CommRing.Expr.num 0)) =
      Lean.Grind.CommRing.Poly.num (Int.ofNat (0 + 1)) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.le_false_of_poly.h4 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.IsPreorder α]
        [inst_4 : Lean.Grind.OrderedRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (lhs rhs : Lean.Grind.CommRing.Expr) (n : Nat),
        Lean.Grind.CommRing.Expr.toPolyX_k bal (lhs.sub rhs) = Lean.Grind.CommRing.Poly.num (Int.ofNat (n + 1)) →
          (Lean.Grind.CommRing.Expr.denote ctx lhs ≤ Lean.Grind.CommRing.Expr.denote ctx rhs) = False := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_false_of_poly.h4.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) ({ le := fun (x x_1 : Int) => True : LE Int }) (Int.instLTInt) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (x x_1 : Int) => True) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.OrderedRing.mk (Int) (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (x x_1 : Int) => True) (Int.instLTInt) (@Std.IsPreorder.mk Int (@LE.mk Int fun (x x_1 : Int) => True) (fun (a : Int) => True.intro)
      fun (a b c : Int) (a_1 a_2 : True) => a_2) (@Lean.Grind.OrderedAdd.mk (Int) (@instHAdd Int
      (@Lean.Grind.Semiring.toAdd Int
        (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))) (@LE.mk Int fun (x x_1 : Int) => True) (@Std.IsPreorder.mk Int (@LE.mk Int fun (x x_1 : Int) => True) (fun (a : Int) => True.intro)
      fun (a b c : Int) (a_1 a_2 : True) => a_2) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   decide) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (Lean.RArray.leaf 1) (Bool.false) (Lean.Grind.CommRing.Expr.num 1) (Lean.Grind.CommRing.Expr.num 0) (0) HypCheckProof.Lean.Grind.CommRing.le_false_of_poly.h4.prem0)

-- Lean.Grind.CommRing.eq_true_of_toPPX_eqS, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eqS.h10 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] [inst_1 : Lean.Grind.AddRightCancel α]
        (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.PPoly),
        p = Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a →
          p = Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b →
            (Lean.Grind.CommRing.Expr.denoteS ctx a = Lean.Grind.CommRing.Expr.denoteS ctx b) = True := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring) (@Lean.Grind.AddRightCancel.mk (Int) (@Lean.Grind.Semiring.toAdd Int
      (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))) (by (try dsimp only);   (intros; omega))) (.branch 1 (.leaf 1) (.leaf 2) : Lean.RArray Int) (1) (Bool.false) (Bool.false) (.var 0 : Lean.Grind.CommRing.Expr) (.var 1 : Lean.Grind.CommRing.Expr) _ rfl (by
  rfl)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.simpsM, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsM.h8 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (p₁ p : Lean.Grind.CommRing.Poly) (ls : Lean.Grind.CommRing.MList),
        (Lean.Grind.CommRing.Poly.kron_k K B p).beq'
              ((Lean.Grind.CommRing.Poly.kron_k K B p₁).add_k (Lean.Grind.CommRing.MList.kron_k K B ls)) =
            Bool.true →
          Lean.Grind.CommRing.MList.AllZero ctx ls →
            Lean.Grind.CommRing.Poly.denote ctx p₁ = 0 → Lean.Grind.CommRing.Poly.denote ctx p = 0 := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 0 : Lean.RArray Int) (0) (0) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 1 : Lean.Grind.CommRing.Poly) (.nil : Lean.Grind.CommRing.MList) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.simpsM, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsM.h9 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (p₁ p : Lean.Grind.CommRing.Poly) (ls : Lean.Grind.CommRing.MList),
        Lean.Grind.CommRing.Stepwise.kronOkM_k K B 0 p₁ p (Lean.Grind.CommRing.PPoly.num 0) ls = Bool.true →
          Lean.Grind.CommRing.MList.AllZero ctx ls →
            Lean.Grind.CommRing.Poly.denote ctx p₁ = 0 → Lean.Grind.CommRing.Poly.denote ctx p = 0 := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 1 : Lean.RArray Int) (2) (2) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.nil : Lean.Grind.CommRing.MList) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.simpsK, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsK.h8 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (p₁ p : Lean.Grind.CommRing.Poly) (ls : Lean.Grind.CommRing.KList),
        (Lean.Grind.CommRing.Poly.kron_k K B p).beq'
              ((Lean.Grind.CommRing.Poly.kron_k K B p₁).add_k (Lean.Grind.CommRing.KList.kron_k K B ls)) =
            Bool.true →
          Lean.Grind.CommRing.KList.AllZero ctx ls →
            Lean.Grind.CommRing.Poly.denote ctx p₁ = 0 → Lean.Grind.CommRing.Poly.denote ctx p = 0 := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 0 : Lean.RArray Int) (0) (0) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num 1 : Lean.Grind.CommRing.Poly) (.nil : Lean.Grind.CommRing.KList) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Stepwise.simpsK, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsK.h9 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (p₁ p : Lean.Grind.CommRing.Poly) (ls : Lean.Grind.CommRing.KList),
        Lean.Grind.CommRing.Stepwise.kronOk_k K B 0 p₁ p (Lean.Grind.CommRing.PPoly.num 0) ls = Bool.true →
          Lean.Grind.CommRing.KList.AllZero ctx ls →
            Lean.Grind.CommRing.Poly.denote ctx p₁ = 0 → Lean.Grind.CommRing.Poly.denote ctx p = 0 := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 1 : Lean.RArray Int) (2) (2) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.nil : Lean.Grind.CommRing.KList) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.denoteSN_eq_of_coeff, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denoteSN_eq_of_coeff.h10 : ¬∀ {α : Type} [inst : Lean.Grind.Semiring α] (f : Nat → α) (B n : Nat) (p q : Lean.Grind.CommRing.PPoly),
        p.size + q.size ≤ n →
          p.NonNeg → q.NonNeg → Lean.Grind.CommRing.PPoly.denoteSN f B p = Lean.Grind.CommRing.PPoly.denoteSN f B q := fun hc_h => absurd (@hc_h (Nat) (Lean.Grind.instCommSemiringNat.toSemiring) (fun n => n + 1 : Nat → Nat) (0) (0) (.num 0 : Lean.Grind.CommRing.PPoly) (.num 1 : Lean.Grind.CommRing.PPoly) (by
  decide) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denote_toPolyQX_k, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_toPolyQX_k.h8 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (bal : Bool) (p : Lean.Grind.CommRing.Poly) (invs : Lean.Grind.CommRing.InvVars)
        (ainvs : Lean.Grind.CommRing.InvAtoms),
        Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
          Lean.Grind.CommRing.PolyQ.denote ctx (Lean.Grind.CommRing.Poly.toPolyQX_k bal p invs ainvs) =
            Lean.Grind.CommRing.Poly.denote ctx p := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 0 : Lean.RArray Rat) (Bool.false) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) ([(0, 1)]) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denoteS_mulMon_nc_go, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_mulMon_nc_go.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (m : Lean.Grind.CommRing.Mon) (p acc : Lean.Grind.CommRing.Poly),
        p.NonnegCoeffs →
          acc.NonnegCoeffs →
            @Eq α (@Lean.Grind.CommRing.Poly.denoteS α inst ctx (Lean.Grind.CommRing.Poly.mulMon_nc.go k m p acc))
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α inst))
                (@HMul.hMul α α α (@instHMul α (@Lean.Grind.Semiring.toMul α inst))
                  (@HMul.hMul α α α (@instHMul α (@Lean.Grind.Semiring.toMul α inst))
                    (@Nat.cast α (@Lean.Grind.Semiring.natCast α inst) k.toNat)
                    (@Lean.Grind.CommRing.Mon.denote α inst ctx m))
                  (@Lean.Grind.CommRing.Poly.denoteS α inst ctx p))
                (@Lean.Grind.CommRing.Poly.denoteS α inst ctx acc))) := fun hc_h => absurd (@hc_h (Int : Type) (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)) (.leaf 1 : Lean.RArray Int) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (.unit : Lean.Grind.CommRing.Mon) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add))) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denoteS_mulMon_nc_go, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_mulMon_nc_go.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (m : Lean.Grind.CommRing.Mon) (p acc : Lean.Grind.CommRing.Poly),
        @GE.ge Int Int.instLEInt k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          acc.NonnegCoeffs →
            @Eq α (@Lean.Grind.CommRing.Poly.denoteS α inst ctx (Lean.Grind.CommRing.Poly.mulMon_nc.go k m p acc))
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α inst))
                (@HMul.hMul α α α (@instHMul α (@Lean.Grind.Semiring.toMul α inst))
                  (@HMul.hMul α α α (@instHMul α (@Lean.Grind.Semiring.toMul α inst))
                    (@Nat.cast α (@Lean.Grind.Semiring.natCast α inst) k.toNat)
                    (@Lean.Grind.CommRing.Mon.denote α inst ctx m))
                  (@Lean.Grind.CommRing.Poly.denoteS α inst ctx p))
                (@Lean.Grind.CommRing.Poly.denoteS α inst ctx acc))) := fun hc_h => absurd (@hc_h (Int : Type) (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)) (.leaf 1 : Lean.RArray Int) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (.unit : Lean.Grind.CommRing.Mon) (.num (-1) : Lean.Grind.CommRing.Poly) (.num 1 : Lean.Grind.CommRing.Poly) (by
  decide) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denoteS_mulMon_nc_go, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_mulMon_nc_go.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (m : Lean.Grind.CommRing.Mon) (p acc : Lean.Grind.CommRing.Poly),
        @GE.ge Int Int.instLEInt k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          p.NonnegCoeffs →
            @Eq α (@Lean.Grind.CommRing.Poly.denoteS α inst ctx (Lean.Grind.CommRing.Poly.mulMon_nc.go k m p acc))
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α inst))
                (@HMul.hMul α α α (@instHMul α (@Lean.Grind.Semiring.toMul α inst))
                  (@HMul.hMul α α α (@instHMul α (@Lean.Grind.Semiring.toMul α inst))
                    (@Nat.cast α (@Lean.Grind.Semiring.natCast α inst) k.toNat)
                    (@Lean.Grind.CommRing.Mon.denote α inst ctx m))
                  (@Lean.Grind.CommRing.Poly.denoteS α inst ctx p))
                (@Lean.Grind.CommRing.Poly.denoteS α inst ctx acc))) := fun hc_h => absurd (@hc_h (Int : Type) (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)) (.leaf 1 : Lean.RArray Int) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (.unit : Lean.Grind.CommRing.Mon) (.num 1 : Lean.Grind.CommRing.Poly) (.num (-1) : Lean.Grind.CommRing.Poly) (by
  decide) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denoteS_mul_nc_go, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_mul_nc_go.h6 : ¬∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α)
        (p₁ p₂ acc : Lean.Grind.CommRing.Poly),
        p₂.NonnegCoeffs →
          acc.NonnegCoeffs →
            Lean.Grind.CommRing.Poly.denoteS ctx (Lean.Grind.CommRing.Poly.mul_nc.go p₂ p₁ acc) =
              Lean.Grind.CommRing.Poly.denoteS ctx acc +
                Lean.Grind.CommRing.Poly.denoteS ctx p₁ * Lean.Grind.CommRing.Poly.denoteS ctx p₂ := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring.toSemiring) (.leaf 1 : Lean.RArray Int) (.num (-1) : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add))) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denoteS_mul_nc_go, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_mul_nc_go.h7 : ¬∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α)
        (p₁ p₂ acc : Lean.Grind.CommRing.Poly),
        p₁.NonnegCoeffs →
          acc.NonnegCoeffs →
            Lean.Grind.CommRing.Poly.denoteS ctx (Lean.Grind.CommRing.Poly.mul_nc.go p₂ p₁ acc) =
              Lean.Grind.CommRing.Poly.denoteS ctx acc +
                Lean.Grind.CommRing.Poly.denoteS ctx p₁ * Lean.Grind.CommRing.Poly.denoteS ctx p₂ := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring.toSemiring) (.leaf 1 : Lean.RArray Int) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.num (-1) : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add))) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denoteS_mul_nc_go, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_mul_nc_go.h8 : ¬∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α)
        (p₁ p₂ acc : Lean.Grind.CommRing.Poly),
        p₁.NonnegCoeffs →
          p₂.NonnegCoeffs →
            Lean.Grind.CommRing.Poly.denoteS ctx (Lean.Grind.CommRing.Poly.mul_nc.go p₂ p₁ acc) =
              Lean.Grind.CommRing.Poly.denoteS ctx acc +
                Lean.Grind.CommRing.Poly.denoteS ctx p₁ * Lean.Grind.CommRing.Poly.denoteS ctx p₂ := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring.toSemiring) (.leaf 1 : Lean.RArray Int) (.num 1 : Lean.Grind.CommRing.Poly) (.num 1 : Lean.Grind.CommRing.Poly) (.num (-1) : Lean.Grind.CommRing.Poly) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add))) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.PSumTree.leaf_zero, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PSumTree.leaf_zero.h7 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (B : Nat)
        (p : Lean.Grind.CommRing.Poly) (P : Lean.Grind.CommRing.PPoly),
        Bool.rec Bool.false (p.maxDeg_k.blt B) (Nat.blt 1 B) = Bool.true →
          Lean.Grind.CommRing.Poly.denote ctx p = 0 →
            Lean.Grind.CommRing.PPoly.denote (Lean.Grind.CommRing.Var.denote ctx) B P = 0 ∧
              Lean.Grind.CommRing.PPoly.Deg B p.maxDeg_k P := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 1 : Lean.RArray Int) (2) (.num 0 : Lean.Grind.CommRing.Poly) (.num 1 : Lean.Grind.CommRing.PPoly) (by
  decide) (by
  decide)) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))

-- Lean.Grind.CommRing.InvVars.lookup_k_spec, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.InvVars.lookup_k_spec.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (ctx : Lean.Grind.CommRing.Context α) (invs : Lean.Grind.CommRing.InvVars),
        @Eq Bool invs.nonzero_k Bool.true →
          ∀ (x : Lean.Grind.CommRing.Var) (c : Nat),
            @Eq (Option Nat) (invs.lookup_k x) (@Option.some Nat c) →
              And
                (@Eq α (@Lean.Grind.CommRing.Var.denote α ctx x)
                  (@Inv.inv α (@Lean.Grind.Field.toInv α inst)
                    (@Nat.cast α
                      (@Lean.Grind.Semiring.natCast α
                        (@Lean.Grind.CommSemiring.toSemiring α
                          (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
                      c)))
                (@Ne Nat c (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (.leaf 0 : Lean.RArray Rat) (@List.cons (Prod Lean.Grind.CommRing.Var Nat)
      (@Prod.mk Lean.Grind.CommRing.Var Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) (by
  decide) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.InvVars.lookup_k_spec, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.InvVars.lookup_k_spec.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (ctx : Lean.Grind.CommRing.Context α) (invs : Lean.Grind.CommRing.InvVars),
        @Lean.Grind.CommRing.InvVars.ok α inst ctx invs →
          ∀ (x : Lean.Grind.CommRing.Var) (c : Nat),
            @Eq (Option Nat) (invs.lookup_k x) (@Option.some Nat c) →
              And
                (@Eq α (@Lean.Grind.CommRing.Var.denote α ctx x)
                  (@Inv.inv α (@Lean.Grind.Field.toInv α inst)
                    (@Nat.cast α
                      (@Lean.Grind.Semiring.natCast α
                        (@Lean.Grind.CommSemiring.toSemiring α
                          (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
                      c)))
                (@Ne Nat c (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (.leaf 0 : Lean.RArray Rat) (@List.cons (Prod Lean.Grind.CommRing.Var Nat)
      (@Prod.mk Lean.Grind.CommRing.Var Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.eq_normA_expr, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_normA_expr.h9 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (ainvs : Lean.Grind.CommRing.InvAtoms),
        Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
          ∀ (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
            (Lean.Grind.CommRing.Expr.denote ctx lhs = Lean.Grind.CommRing.Expr.denote ctx rhs) =
              (Lean.Grind.CommRing.Expr.denote ctx lhs' = Lean.Grind.CommRing.Expr.denote ctx rhs') := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 1 : Lean.RArray Int) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr)) (by
  decide +kernel)

-- Lean.Grind.IsCharP.ofNat_eq_iff_of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IsCharP.ofNat_eq_iff_of_lt.h6 : Not
      (∀ {α : Type} (p : Nat) [inst : Lean.Grind.Semiring α] [inst_1 : @Lean.Grind.IsCharP α inst p] {x y : Nat},
        @LT.lt Nat instLTNat y p →
          Iff
            (@Eq α (@OfNat.ofNat α x (@Lean.Grind.Semiring.ofNat α inst x))
              (@OfNat.ofNat α y (@Lean.Grind.Semiring.ofNat α inst y)))
            (@Eq Nat x y)) := fun hc_h => absurd (@hc_h (Fin 2 : Type) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Lean.Grind.CommSemiring.toSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Lean.Grind.CommRing.toCommSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Lean.Grind.Fin.instCommRingFinOfNeZeroNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) _ (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.IsCharP.ofNat_eq_iff_of_lt, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IsCharP.ofNat_eq_iff_of_lt.h7 : Not
      (∀ {α : Type} (p : Nat) [inst : Lean.Grind.Semiring α] [inst_1 : @Lean.Grind.IsCharP α inst p] {x y : Nat},
        @LT.lt Nat instLTNat x p →
          Iff
            (@Eq α (@OfNat.ofNat α x (@Lean.Grind.Semiring.ofNat α inst x))
              (@OfNat.ofNat α y (@Lean.Grind.Semiring.ofNat α inst y)))
            (@Eq Nat x y)) := fun hc_h => absurd (@hc_h (Fin 2 : Type) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Lean.Grind.CommSemiring.toSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Lean.Grind.CommRing.toCommSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Lean.Grind.Fin.instCommRingFinOfNeZeroNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.IsCharP.natCast_eq_iff_of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IsCharP.natCast_eq_iff_of_lt.h6 : Not
      (∀ {α : Type} (p : Nat) [inst : Lean.Grind.Semiring α] [inst_1 : @Lean.Grind.IsCharP α inst p] {x y : Nat},
        @LT.lt Nat instLTNat y p →
          Iff
            (@Eq α (@Nat.cast α (@Lean.Grind.Semiring.natCast α inst) x)
              (@Nat.cast α (@Lean.Grind.Semiring.natCast α inst) y))
            (@Eq Nat x y)) := fun hc_h => absurd (@hc_h (Fin 2 : Type) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Lean.Grind.CommSemiring.toSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Lean.Grind.CommRing.toCommSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Lean.Grind.Fin.instCommRingFinOfNeZeroNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) _ (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.IsCharP.natCast_eq_iff_of_lt, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IsCharP.natCast_eq_iff_of_lt.h7 : Not
      (∀ {α : Type} (p : Nat) [inst : Lean.Grind.Semiring α] [inst_1 : @Lean.Grind.IsCharP α inst p] {x y : Nat},
        @LT.lt Nat instLTNat x p →
          Iff
            (@Eq α (@Nat.cast α (@Lean.Grind.Semiring.natCast α inst) x)
              (@Nat.cast α (@Lean.Grind.Semiring.natCast α inst) y))
            (@Eq Nat x y)) := fun hc_h => absurd (@hc_h (Fin 2 : Type) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Lean.Grind.CommSemiring.toSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Lean.Grind.CommRing.toCommSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Lean.Grind.Fin.instCommRingFinOfNeZeroNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PPoly.monDenote_add, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.monDenote_add.h8 : ¬∀ {B : Nat} {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Nat → α),
        1 < B →
          ∀ (i v₁ v₂ : Nat),
            Lean.Grind.CommRing.PPoly.monDenote ctx B i (v₁ + v₂) =
              Lean.Grind.CommRing.PPoly.monDenote ctx B i v₁ * Lean.Grind.CommRing.PPoly.monDenote ctx B i v₂ := fun hc_h => absurd (@hc_h (2) (Nat) (Lean.Grind.instCommSemiringNat) (fun n => n + 1 : Nat → Nat) (by
  decide) (0) (1) (1)) (by
  decide +kernel)

-- Lean.Grind.CommRing.PolyQ.denote_substInvB_k, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.PolyQ.denote_substInvB_k.h7 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (ctx : Lean.Grind.CommRing.Context α)
        (q : Lean.Grind.CommRing.PolyQ) (x : Lean.Grind.CommRing.Var) (c : Nat),
        Lean.Grind.CommRing.PolyQ.denote ctx (q.substInvB_k x c) = Lean.Grind.CommRing.PolyQ.denote ctx q := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) _ (.leaf 1 : Lean.RArray Rat) ({
      num :=
        Lean.Grind.CommRing.Poly.add 1
          (Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num 0),
      den := 1 : Lean.Grind.CommRing.PolyQ }) (0) (2)) (by
  decide +kernel)

-- Lean.Grind.CommRing.MList.allZero_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.MList.allZero_cons.h6 : ¬∀ {α : Type} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α) (M q : Lean.Grind.CommRing.Poly)
        (ls : Lean.Grind.CommRing.MList),
        Lean.Grind.CommRing.MList.AllZero ctx ls →
          Lean.Grind.CommRing.MList.AllZero ctx (Lean.Grind.CommRing.MList.cons M q ls) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (.leaf 1 : Lean.RArray Int) (.num 0 : Lean.Grind.CommRing.Poly) (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0) : Lean.Grind.CommRing.Poly) (.nil : Lean.Grind.CommRing.MList) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))

-- Lean.Grind.CommRing.MList.allZero_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.MList.allZero_cons.h7 : ¬∀ {α : Type} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α) (M q : Lean.Grind.CommRing.Poly)
        (ls : Lean.Grind.CommRing.MList),
        Lean.Grind.CommRing.Poly.denote ctx q = 0 →
          Lean.Grind.CommRing.MList.AllZero ctx (Lean.Grind.CommRing.MList.cons M q ls) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (.leaf 1 : Lean.RArray Int) (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) (.cons (.add 1 (.mult ⟨0, 1⟩ .unit) (.num 0)) (.num 1) .nil : Lean.Grind.CommRing.MList) (by
  decide)) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel))

-- Lean.Grind.CommRing.Expr.eq_of_cancelInvs_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_cancelInvs_eq.h7 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (ainvs : Lean.Grind.CommRing.InvAtoms),
        Lean.Grind.CommRing.InvAtoms.ok ctx ainvs →
          ∀ (a b : Lean.Grind.CommRing.Expr), Lean.Grind.CommRing.Expr.denote ctx a = Lean.Grind.CommRing.Expr.denote ctx b := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (.leaf 1 : Lean.RArray Int) ([]) (by
  (simp only [Lean.Grind.CommRing.PPoly.NonNeg, Lean.Grind.CommRing.PPoly.Deg, Lean.Grind.CommRing.PPoly.DegList,
        Lean.Grind.CommRing.KList.AllZero, Lean.Grind.CommRing.MList.AllZero, Lean.Grind.CommRing.InvAtoms.ok,
        Lean.Grind.CommRing.InvVars.ok, Lean.Grind.CommRing.InvVars.denoteVars,
        Lean.Grind.CommRing.InvVars.denoteInvs] <;>
      decide +kernel)) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr)) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denoteS_combine, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_combine.h5 : ¬∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        p₂.NonnegCoeffs →
          Lean.Grind.CommRing.Poly.denoteS ctx (p₁.combine p₂) =
            Lean.Grind.CommRing.Poly.denoteS ctx p₁ + Lean.Grind.CommRing.Poly.denoteS ctx p₂ := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring.toSemiring) (.leaf 1 : Lean.RArray Int) (.num (-1) : Lean.Grind.CommRing.Poly) (.num 1 : Lean.Grind.CommRing.Poly) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denoteS_combine, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_combine.h6 : ¬∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        p₁.NonnegCoeffs →
          Lean.Grind.CommRing.Poly.denoteS ctx (p₁.combine p₂) =
            Lean.Grind.CommRing.Poly.denoteS ctx p₁ + Lean.Grind.CommRing.Poly.denoteS ctx p₂ := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring.toSemiring) (.leaf 1 : Lean.RArray Int) (.num 1 : Lean.Grind.CommRing.Poly) (.num (-1) : Lean.Grind.CommRing.Poly) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denoteS_concat, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_concat.h5 : ¬∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        p₂.NonnegCoeffs →
          Lean.Grind.CommRing.Poly.denoteS ctx (p₁.concat p₂) =
            Lean.Grind.CommRing.Poly.denoteS ctx p₁ + Lean.Grind.CommRing.Poly.denoteS ctx p₂ := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring.toSemiring) (.leaf 1 : Lean.RArray Int) (.num (-1) : Lean.Grind.CommRing.Poly) (.num 1 : Lean.Grind.CommRing.Poly) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.CommRing.Poly.denoteS_concat, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_concat.h6 : ¬∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        p₁.NonnegCoeffs →
          Lean.Grind.CommRing.Poly.denoteS ctx (p₁.concat p₂) =
            Lean.Grind.CommRing.Poly.denoteS ctx p₁ + Lean.Grind.CommRing.Poly.denoteS ctx p₂ := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring.toSemiring) (.leaf 1 : Lean.RArray Int) (.num 1 : Lean.Grind.CommRing.Poly) (.num (-1) : Lean.Grind.CommRing.Poly) (by
  (repeat
      (first
        | decide
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.num
        | apply Lean.Grind.CommRing.Poly.NonnegCoeffs.add)))) (by
  decide +kernel)

-- Lean.Grind.IsCharP.ofNat_eq_zero_iff_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IsCharP.ofNat_eq_zero_iff_of_lt.h5 : Not
      (∀ {α : Type} (p : Nat) [inst : Lean.Grind.Semiring α] [inst_1 : @Lean.Grind.IsCharP α inst p] {x : Nat},
        Iff
          (@Eq α (@OfNat.ofNat α x (@Lean.Grind.Semiring.ofNat α inst x))
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.Semiring.toNatModule α inst))))))
          (@Eq Nat x (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := fun hc_h => absurd (@hc_h (Fin 2 : Type) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Lean.Grind.CommSemiring.toSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Lean.Grind.CommRing.toCommSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Lean.Grind.Fin.instCommRingFinOfNeZeroNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) _ (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (by
  decide +kernel)

-- Lean.Grind.Field.natCast_div_of_dvd, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Field.natCast_div_of_dvd.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] {x y : Nat},
        @Dvd.dvd Nat Nat.instDvd y x →
          @Eq α
            (@Nat.cast α
              (@Lean.Grind.Semiring.natCast α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
              (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) x y))
            (@HDiv.hDiv α α α (@instHDiv α (@Lean.Grind.Field.toDiv α inst))
              (@Nat.cast α
                (@Lean.Grind.Semiring.natCast α
                  (@Lean.Grind.CommSemiring.toSemiring α
                    (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
                x)
              (@Nat.cast α
                (@Lean.Grind.Semiring.natCast α
                  (@Lean.Grind.CommSemiring.toSemiring α
                    (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
                y))) := fun hc_h => absurd (@hc_h (Fin 2 : Type) ({ (inferInstance : Lean.Grind.CommRing (Fin 2)) with inv := id, div := (· * ·), zpow := ⟨fun a n => a ^ n.natAbs⟩, div_eq_mul_inv := (by decide), zero_ne_one := (by decide), inv_zero := (by decide), mul_inv_cancel := (by decide), zpow_zero := fun a => Lean.Grind.Semiring.pow_zero a, zpow_succ := fun a n => Lean.Grind.Semiring.pow_succ a n, zpow_neg := (by intro a n; show a ^ (-n).natAbs = a ^ n.natAbs; rw [Int.natAbs_neg]) } : Lean.Grind.Field (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

