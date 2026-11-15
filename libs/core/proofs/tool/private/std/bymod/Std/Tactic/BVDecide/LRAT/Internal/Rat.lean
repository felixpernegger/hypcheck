import Std

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
-- _private.Std.Tactic.BVDecide.LRAT.Internal.Rat.0.Std.Tactic.BVDecide.LRAT.Internal.State.checkRatHintsExhaustive_spec, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Tactic.BVDecide.LRAT.Internal.State.checkRatHintsExhaustive_spec.h5 : Not
      (∀ {s : Std.Tactic.BVDecide.LRAT.Internal.State} {ratHints : Array (Prod Nat (Array Nat))}
        {negPivot : Std.Sat.Literal Nat},
        @Eq Bool (Std.Tactic.BVDecide.LRAT.Internal.State.checkRatHintsExhaustive s ratHints negPivot) Bool.true →
          ∀ (c : Std.Sat.CNF.Clause Nat),
            @Membership.mem (Std.Sat.Literal Nat) (Std.Sat.CNF.Clause Nat) (@Std.Sat.CNF.Clause.instMembershipLiteral Nat) c
                negPivot →
              @Exists Nat fun (idx : Nat) =>
                @Exists (Array Nat) fun (hints : Array Nat) =>
                  And (@Eq (Option (Std.Sat.CNF.Clause Nat)) (s.get? idx) (@Option.some (Std.Sat.CNF.Clause Nat) c))
                    (@Membership.mem (Prod Nat (Array Nat)) (Array (Prod Nat (Array Nat)))
                      (@Array.instMembership (Prod Nat (Array Nat))) ratHints (@Prod.mk Nat (Array Nat) idx hints))) := fun hc_h => absurd (@hc_h ({ formula := @List.toArray (Option (Std.Sat.CNF.Clause Nat)) (@List.nil (Option (Std.Sat.CNF.Clause Nat))) :
      Std.Tactic.BVDecide.LRAT.Internal.State }) (@List.toArray (Prod Nat (Array Nat)) (@List.nil (Prod Nat (Array Nat)))) (@Prod.mk Nat Bool (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) Bool.false) (by
  decide +kernel) (@Std.Sat.CNF.Clause.mk Nat
      (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))
      {
        data :=
          @List.toArray UInt8
            (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@List.nil UInt8)) :
        ByteArray }
      (@of_decide_eq_true
        (@Eq Nat
          {
              data :=
                @List.toArray UInt8
                  (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@List.nil UInt8)) :
              ByteArray }.size
          (@Array.size Nat
            (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))))
        (instDecidableEqNat
          {
              data :=
                @List.toArray UInt8
                  (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@List.nil UInt8)) :
              ByteArray }.size
          (@Array.size Nat
            (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Eq Nat
                {
                    data :=
                      @List.toArray UInt8
                        (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@List.nil UInt8)) :
                    ByteArray }.size
                (@Array.size Nat
                  (@List.toArray Nat
                    (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))))
              (instDecidableEqNat
                {
                    data :=
                      @List.toArray UInt8
                        (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@List.nil UInt8)) :
                    ByteArray }.size
                (@Array.size Nat
                  (@List.toArray Nat
                    (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ (i : Nat)
          (h :
            @LT.lt Nat instLTNat i
              {
                  data :=
                    @List.toArray UInt8
                      (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@List.nil UInt8)) :
                  ByteArray }.size),
          Or
            (@Eq UInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize
                {
                  data :=
                    @List.toArray UInt8
                      (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@List.nil UInt8)) :
                  ByteArray }
                i h)
              (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
            (@Eq UInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize
                {
                  data :=
                    @List.toArray UInt8
                      (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@List.nil UInt8)) :
                  ByteArray }
                i h)
              (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
        (@Nat.decidableBallLT
          {
              data :=
                @List.toArray UInt8
                  (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@List.nil UInt8)) :
              ByteArray }.size
          (fun (i : Nat)
              (h :
                @LT.lt Nat instLTNat i
                  {
                      data :=
                        @List.toArray UInt8
                          (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (@List.nil UInt8)) :
                      ByteArray }.size) =>
            Or
              (@Eq UInt8
                (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                  ByteArray.instGetElemNatUInt8LtSize
                  {
                    data :=
                      @List.toArray UInt8
                        (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@List.nil UInt8)) :
                    ByteArray }
                  i h)
                (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
              (@Eq UInt8
                (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                  ByteArray.instGetElemNatUInt8LtSize
                  {
                    data :=
                      @List.toArray UInt8
                        (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@List.nil UInt8)) :
                    ByteArray }
                  i h)
                (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
          fun (n : Nat)
            (h :
              @LT.lt Nat instLTNat n
                {
                    data :=
                      @List.toArray UInt8
                        (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@List.nil UInt8)) :
                    ByteArray }.size) =>
          @instDecidableOr
            (@Eq UInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize
                {
                  data :=
                    @List.toArray UInt8
                      (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@List.nil UInt8)) :
                  ByteArray }
                n h)
              (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
            (@Eq UInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize
                {
                  data :=
                    @List.toArray UInt8
                      (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@List.nil UInt8)) :
                  ByteArray }
                n h)
              (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
            (instDecidableEqUInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize
                {
                  data :=
                    @List.toArray UInt8
                      (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@List.nil UInt8)) :
                  ByteArray }
                n h)
              (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
            (instDecidableEqUInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize
                {
                  data :=
                    @List.toArray UInt8
                      (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@List.nil UInt8)) :
                  ByteArray }
                n h)
              (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ (i : Nat)
                (h :
                  @LT.lt Nat instLTNat i
                    {
                        data :=
                          @List.toArray UInt8
                            (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@List.nil UInt8)) :
                        ByteArray }.size),
                Or
                  (@Eq UInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize
                      {
                        data :=
                          @List.toArray UInt8
                            (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@List.nil UInt8)) :
                        ByteArray }
                      i h)
                    (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                  (@Eq UInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize
                      {
                        data :=
                          @List.toArray UInt8
                            (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@List.nil UInt8)) :
                        ByteArray }
                      i h)
                    (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
              (@Nat.decidableBallLT
                {
                    data :=
                      @List.toArray UInt8
                        (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (@List.nil UInt8)) :
                    ByteArray }.size
                (fun (i : Nat)
                    (h :
                      @LT.lt Nat instLTNat i
                        {
                            data :=
                              @List.toArray UInt8
                                (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                  (@List.nil UInt8)) :
                            ByteArray }.size) =>
                  Or
                    (@Eq UInt8
                      (@GetElem.getElem ByteArray Nat UInt8
                        (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                        ByteArray.instGetElemNatUInt8LtSize
                        {
                          data :=
                            @List.toArray UInt8
                              (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (@List.nil UInt8)) :
                          ByteArray }
                        i h)
                      (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                    (@Eq UInt8
                      (@GetElem.getElem ByteArray Nat UInt8
                        (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                        ByteArray.instGetElemNatUInt8LtSize
                        {
                          data :=
                            @List.toArray UInt8
                              (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (@List.nil UInt8)) :
                          ByteArray }
                        i h)
                      (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
                fun (n : Nat)
                  (h :
                    @LT.lt Nat instLTNat n
                      {
                          data :=
                            @List.toArray UInt8
                              (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (@List.nil UInt8)) :
                          ByteArray }.size) =>
                @instDecidableOr
                  (@Eq UInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize
                      {
                        data :=
                          @List.toArray UInt8
                            (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@List.nil UInt8)) :
                        ByteArray }
                      n h)
                    (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                  (@Eq UInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize
                      {
                        data :=
                          @List.toArray UInt8
                            (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@List.nil UInt8)) :
                        ByteArray }
                      n h)
                    (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
                  (instDecidableEqUInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize
                      {
                        data :=
                          @List.toArray UInt8
                            (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@List.nil UInt8)) :
                        ByteArray }
                      n h)
                    (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                  (instDecidableEqUInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize
                      {
                        data :=
                          @List.toArray UInt8
                            (@List.cons UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@List.nil UInt8)) :
                        ByteArray }
                      n h)
                    (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide +kernel)) (by
  simp)

-- _private.Std.Tactic.BVDecide.LRAT.Internal.Rat.0.Std.Tactic.BVDecide.LRAT.Internal.State.checkRatHintsExhaustive_spec, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Tactic.BVDecide.LRAT.Internal.State.checkRatHintsExhaustive_spec.h6 : Not
      (∀ {s : Std.Tactic.BVDecide.LRAT.Internal.State} {ratHints : Array (Prod Nat (Array Nat))}
        {negPivot : Std.Sat.Literal Nat},
        @Eq Bool (Std.Tactic.BVDecide.LRAT.Internal.State.checkRatHintsExhaustive s ratHints negPivot) Bool.true →
          ∀ (c : Std.Sat.CNF.Clause Nat),
            @Membership.mem (Std.Sat.CNF.Clause Nat) (Std.Sat.CNF Nat) (@Std.Sat.CNF.instMembershipClause Nat) s.toCNF c →
              @Exists Nat fun (idx : Nat) =>
                @Exists (Array Nat) fun (hints : Array Nat) =>
                  And (@Eq (Option (Std.Sat.CNF.Clause Nat)) (s.get? idx) (@Option.some (Std.Sat.CNF.Clause Nat) c))
                    (@Membership.mem (Prod Nat (Array Nat)) (Array (Prod Nat (Array Nat)))
                      (@Array.instMembership (Prod Nat (Array Nat))) ratHints (@Prod.mk Nat (Array Nat) idx hints))) := fun hc_h => absurd (@hc_h ({
      formula :=
        @List.toArray (Option (Std.Sat.CNF.Clause Nat))
          (@List.cons (Option (Std.Sat.CNF.Clause Nat))
            (@Option.some (Std.Sat.CNF.Clause Nat)
              (@Std.Sat.CNF.Clause.mk Nat (@List.toArray Nat (@List.nil Nat))
                { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }
                (@of_decide_eq_true
                  (@Eq Nat { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
                    (@Array.size Nat (@List.toArray Nat (@List.nil Nat))))
                  (instDecidableEqNat { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
                    (@Array.size Nat (@List.toArray Nat (@List.nil Nat))))
                  (@id
                    (@Eq Bool
                      (@Decidable.decide
                        (@Eq Nat { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
                          (@Array.size Nat (@List.toArray Nat (@List.nil Nat))))
                        (instDecidableEqNat { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
                          (@Array.size Nat (@List.toArray Nat (@List.nil Nat)))))
                      Bool.true)
                    (@Eq.refl Bool Bool.true)))
                (@of_decide_eq_true
                  (∀ (i : Nat)
                    (h : @LT.lt Nat instLTNat i { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size),
                    Or
                      (@Eq UInt8
                        (@GetElem.getElem ByteArray Nat UInt8
                          (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                          ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }
                          i h)
                        (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                      (@Eq UInt8
                        (@GetElem.getElem ByteArray Nat UInt8
                          (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                          ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }
                          i h)
                        (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
                  (@Nat.decidableBallLT { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
                    (fun (i : Nat)
                        (h : @LT.lt Nat instLTNat i { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size) =>
                      Or
                        (@Eq UInt8
                          (@GetElem.getElem ByteArray Nat UInt8
                            (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                            ByteArray.instGetElemNatUInt8LtSize
                            { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
                          (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                        (@Eq UInt8
                          (@GetElem.getElem ByteArray Nat UInt8
                            (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                            ByteArray.instGetElemNatUInt8LtSize
                            { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
                          (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
                    fun (n : Nat)
                      (h : @LT.lt Nat instLTNat n { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size) =>
                    @instDecidableOr
                      (@Eq UInt8
                        (@GetElem.getElem ByteArray Nat UInt8
                          (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                          ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }
                          n h)
                        (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                      (@Eq UInt8
                        (@GetElem.getElem ByteArray Nat UInt8
                          (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                          ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }
                          n h)
                        (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
                      (instDecidableEqUInt8
                        (@GetElem.getElem ByteArray Nat UInt8
                          (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                          ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }
                          n h)
                        (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                      (instDecidableEqUInt8
                        (@GetElem.getElem ByteArray Nat UInt8
                          (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                          ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }
                          n h)
                        (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
                  (@id
                    (@Eq Bool
                      (@Decidable.decide
                        (∀ (i : Nat)
                          (h : @LT.lt Nat instLTNat i { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size),
                          Or
                            (@Eq UInt8
                              (@GetElem.getElem ByteArray Nat UInt8
                                (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                                ByteArray.instGetElemNatUInt8LtSize
                                { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
                              (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                            (@Eq UInt8
                              (@GetElem.getElem ByteArray Nat UInt8
                                (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                                ByteArray.instGetElemNatUInt8LtSize
                                { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
                              (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
                        (@Nat.decidableBallLT { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
                          (fun (i : Nat)
                              (h :
                                @LT.lt Nat instLTNat i
                                  { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size) =>
                            Or
                              (@Eq UInt8
                                (@GetElem.getElem ByteArray Nat UInt8
                                  (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                                  ByteArray.instGetElemNatUInt8LtSize
                                  { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
                                (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                              (@Eq UInt8
                                (@GetElem.getElem ByteArray Nat UInt8
                                  (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                                  ByteArray.instGetElemNatUInt8LtSize
                                  { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
                                (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
                          fun (n : Nat)
                            (h :
                              @LT.lt Nat instLTNat n { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size) =>
                          @instDecidableOr
                            (@Eq UInt8
                              (@GetElem.getElem ByteArray Nat UInt8
                                (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                                ByteArray.instGetElemNatUInt8LtSize
                                { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
                              (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                            (@Eq UInt8
                              (@GetElem.getElem ByteArray Nat UInt8
                                (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                                ByteArray.instGetElemNatUInt8LtSize
                                { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
                              (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
                            (instDecidableEqUInt8
                              (@GetElem.getElem ByteArray Nat UInt8
                                (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                                ByteArray.instGetElemNatUInt8LtSize
                                { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
                              (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                            (instDecidableEqUInt8
                              (@GetElem.getElem ByteArray Nat UInt8
                                (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                                ByteArray.instGetElemNatUInt8LtSize
                                { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
                              (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))))
                      Bool.true)
                    (@Eq.refl Bool Bool.true)))))
            (@List.nil (Option (Std.Sat.CNF.Clause Nat)))) :
      Std.Tactic.BVDecide.LRAT.Internal.State }) (@List.toArray (Prod Nat (Array Nat)) (@List.nil (Prod Nat (Array Nat)))) (@Prod.mk Nat Bool (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) Bool.false) (by
  decide +kernel) (@Std.Sat.CNF.Clause.mk Nat (@List.toArray Nat (@List.nil Nat))
      { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }
      (@of_decide_eq_true
        (@Eq Nat { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
          (@Array.size Nat (@List.toArray Nat (@List.nil Nat))))
        (instDecidableEqNat { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
          (@Array.size Nat (@List.toArray Nat (@List.nil Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Eq Nat { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
                (@Array.size Nat (@List.toArray Nat (@List.nil Nat))))
              (instDecidableEqNat { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
                (@Array.size Nat (@List.toArray Nat (@List.nil Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ (i : Nat) (h : @LT.lt Nat instLTNat i { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size),
          Or
            (@Eq UInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
              (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
            (@Eq UInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
              (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
        (@Nat.decidableBallLT { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
          (fun (i : Nat) (h : @LT.lt Nat instLTNat i { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size) =>
            Or
              (@Eq UInt8
                (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                  ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
                (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
              (@Eq UInt8
                (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                  ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
                (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
          fun (n : Nat) (h : @LT.lt Nat instLTNat n { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size) =>
          @instDecidableOr
            (@Eq UInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
              (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
            (@Eq UInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
              (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
            (instDecidableEqUInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
              (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
            (instDecidableEqUInt8
              (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
              (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ (i : Nat) (h : @LT.lt Nat instLTNat i { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size),
                Or
                  (@Eq UInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
                    (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                  (@Eq UInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i h)
                    (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
              (@Nat.decidableBallLT { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size
                (fun (i : Nat)
                    (h : @LT.lt Nat instLTNat i { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size) =>
                  Or
                    (@Eq UInt8
                      (@GetElem.getElem ByteArray Nat UInt8
                        (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                        ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i
                        h)
                      (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                    (@Eq UInt8
                      (@GetElem.getElem ByteArray Nat UInt8
                        (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                        ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } i
                        h)
                      (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))))
                fun (n : Nat)
                  (h : @LT.lt Nat instLTNat n { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }.size) =>
                @instDecidableOr
                  (@Eq UInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
                    (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                  (@Eq UInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
                    (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
                  (instDecidableEqUInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
                    (@OfNat.ofNat UInt8 (nat_lit 0) (@UInt8.instOfNat (nat_lit 0))))
                  (instDecidableEqUInt8
                    (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
                      ByteArray.instGetElemNatUInt8LtSize { data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray } n h)
                    (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide +kernel)) (by
  simp)

