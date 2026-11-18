module
public import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Surreal.ofSets_eq_of_forall_birthday_le, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Surreal.ofSets_eq_of_forall_birthday_le.h5.der.{u} : ∀ {s t : Set.{u + 1} Surreal.{u}} {z : Surreal.{u}} [inst : Small.{u, u + 1} (@Set.Elem.{u + 1} Surreal.{u} s)]
      [inst : Small.{u, u + 1} (@Set.Elem.{u + 1} Surreal.{u} t)],
      (∀ (x : Surreal.{u}),
          @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u}) s
              x →
            @LT.lt.{u + 1} Surreal.{u}
              (@Preorder.toLT.{u + 1} Surreal.{u}
                (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
              x z) →
        (∀ (y : Surreal.{u}),
            @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u}) t
                y →
              @LT.lt.{u + 1} Surreal.{u}
                (@Preorder.toLT.{u + 1} Surreal.{u}
                  (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                z y) →
          (∀ (w : Surreal.{u}),
              (∀ (x : Surreal.{u}),
                  @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                      (@Set.instMembership.{u + 1} Surreal.{u}) s x →
                    @LT.lt.{u + 1} Surreal.{u}
                      (@Preorder.toLT.{u + 1} Surreal.{u}
                        (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                      x w) →
                (∀ (y : Surreal.{u}),
                    @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                        (@Set.instMembership.{u + 1} Surreal.{u}) t y →
                      @LT.lt.{u + 1} Surreal.{u}
                        (@Preorder.toLT.{u + 1} Surreal.{u}
                          (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                        w y) →
                  @LE.le.{u + 1} NatOrdinal.{u}
                    (@Preorder.toLE.{u + 1} NatOrdinal.{u}
                      (@PartialOrder.toPreorder.{u + 1} NatOrdinal.{u} NatOrdinal.instPartialOrder.{u}))
                    z.birthday w.birthday) →
            ∀ (x : Surreal.{u}),
              @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u})
                  s x →
                ∀ (y : Surreal.{u}),
                  @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                      (@Set.instMembership.{u + 1} Surreal.{u}) t y →
                    @LT.lt.{u + 1} Surreal.{u}
                      (@Preorder.toLT.{u + 1} Surreal.{u}
                        (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                      x y := by
  (intros; grind)
theorem HypCheckProof.Surreal.ofSets_eq_of_forall_birthday_le.h5.{u} : ∀ {s t : Set.{u + 1} Surreal.{u}} {z : Surreal.{u}} [inst : Small.{u, u + 1} (@Set.Elem.{u + 1} Surreal.{u} s)]
      [inst_1 : Small.{u, u + 1} (@Set.Elem.{u + 1} Surreal.{u} t)]
      (hL :
        ∀ (x : Surreal.{u}),
          @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u}) s
              x →
            @LT.lt.{u + 1} Surreal.{u}
              (@Preorder.toLT.{u + 1} Surreal.{u}
                (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
              x z)
      (hR :
        ∀ (y : Surreal.{u}),
          @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u}) t
              y →
            @LT.lt.{u + 1} Surreal.{u}
              (@Preorder.toLT.{u + 1} Surreal.{u}
                (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
              z y)
      (h :
        ∀ (w : Surreal.{u}),
          (∀ (x : Surreal.{u}),
              @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u})
                  s x →
                @LT.lt.{u + 1} Surreal.{u}
                  (@Preorder.toLT.{u + 1} Surreal.{u}
                    (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                  x w) →
            (∀ (y : Surreal.{u}),
                @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                    (@Set.instMembership.{u + 1} Surreal.{u}) t y →
                  @LT.lt.{u + 1} Surreal.{u}
                    (@Preorder.toLT.{u + 1} Surreal.{u}
                      (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                    w y) →
              @LE.le.{u + 1} NatOrdinal.{u}
                (@Preorder.toLE.{u + 1} NatOrdinal.{u}
                  (@PartialOrder.toPreorder.{u + 1} NatOrdinal.{u} NatOrdinal.instPartialOrder.{u}))
                z.birthday w.birthday),
      @Eq.{u + 2} Surreal.{u}
        (@OfSets.ofSets.{u} Surreal.{u}
          (fun (st : Player → Set.{u + 1} Surreal.{u}) =>
            ∀ (x : Surreal.{u}),
              @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u})
                  (st Player.left) x →
                ∀ (y : Surreal.{u}),
                  @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                      (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.right) y →
                    @LT.lt.{u + 1} Surreal.{u}
                      (@Preorder.toLT.{u + 1} Surreal.{u}
                        (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                      x y)
          Surreal.instOfSetsForallForallMemSetLeftForallForallRightLt.{u}
          (@Player.cases.{u + 2} (Set.{u + 1} Surreal.{u}) s t)
          (@HypCheckProof.Surreal.ofSets_eq_of_forall_birthday_le.h5.der.{u} s t z inst inst_1 hL hR h) inst inst_1)
        z := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact @Surreal.ofSets_eq_of_forall_birthday_le hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Surreal.ofSets_eq_of_forall_birthday_le.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7) hc_x5 hc_x6 hc_x7

-- Surreal.ofSets_eq_of_forall_birthday_le', hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Surreal.ofSets_eq_of_forall_birthday_le'.h4.der.{u} : ∀ {st : Player → Set.{u + 1} Surreal.{u}} {z : Surreal.{u}}
      [inst : Small.{u, u + 1} (@Set.Elem.{u + 1} Surreal.{u} (st Player.left))]
      [inst : Small.{u, u + 1} (@Set.Elem.{u + 1} Surreal.{u} (st Player.right))],
      (∀ (x : Surreal.{u}),
          @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u})
              (st Player.left) x →
            @LT.lt.{u + 1} Surreal.{u}
              (@Preorder.toLT.{u + 1} Surreal.{u}
                (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
              x z) →
        (∀ (y : Surreal.{u}),
            @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u})
                (st Player.right) y →
              @LT.lt.{u + 1} Surreal.{u}
                (@Preorder.toLT.{u + 1} Surreal.{u}
                  (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                z y) →
          (∀ (w : Surreal.{u}),
              (∀ (x : Surreal.{u}),
                  @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                      (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.left) x →
                    @LT.lt.{u + 1} Surreal.{u}
                      (@Preorder.toLT.{u + 1} Surreal.{u}
                        (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                      x w) →
                (∀ (y : Surreal.{u}),
                    @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                        (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.right) y →
                      @LT.lt.{u + 1} Surreal.{u}
                        (@Preorder.toLT.{u + 1} Surreal.{u}
                          (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                        w y) →
                  @LE.le.{u + 1} NatOrdinal.{u}
                    (@Preorder.toLE.{u + 1} NatOrdinal.{u}
                      (@PartialOrder.toPreorder.{u + 1} NatOrdinal.{u} NatOrdinal.instPartialOrder.{u}))
                    z.birthday w.birthday) →
            ∀ (x : Surreal.{u}),
              @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u})
                  (st Player.left) x →
                ∀ (y : Surreal.{u}),
                  @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                      (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.right) y →
                    @LT.lt.{u + 1} Surreal.{u}
                      (@Preorder.toLT.{u + 1} Surreal.{u}
                        (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                      x y := by
  (intros; grind)
theorem HypCheckProof.Surreal.ofSets_eq_of_forall_birthday_le'.h4.{u} : ∀ {st : Player → Set.{u + 1} Surreal.{u}} {z : Surreal.{u}}
      [inst : Small.{u, u + 1} (@Set.Elem.{u + 1} Surreal.{u} (st Player.left))]
      [inst_1 : Small.{u, u + 1} (@Set.Elem.{u + 1} Surreal.{u} (st Player.right))]
      (hL :
        ∀ (x : Surreal.{u}),
          @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u})
              (st Player.left) x →
            @LT.lt.{u + 1} Surreal.{u}
              (@Preorder.toLT.{u + 1} Surreal.{u}
                (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
              x z)
      (hR :
        ∀ (y : Surreal.{u}),
          @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u})
              (st Player.right) y →
            @LT.lt.{u + 1} Surreal.{u}
              (@Preorder.toLT.{u + 1} Surreal.{u}
                (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
              z y)
      (h :
        ∀ (w : Surreal.{u}),
          (∀ (x : Surreal.{u}),
              @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u})
                  (st Player.left) x →
                @LT.lt.{u + 1} Surreal.{u}
                  (@Preorder.toLT.{u + 1} Surreal.{u}
                    (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                  x w) →
            (∀ (y : Surreal.{u}),
                @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                    (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.right) y →
                  @LT.lt.{u + 1} Surreal.{u}
                    (@Preorder.toLT.{u + 1} Surreal.{u}
                      (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                    w y) →
              @LE.le.{u + 1} NatOrdinal.{u}
                (@Preorder.toLE.{u + 1} NatOrdinal.{u}
                  (@PartialOrder.toPreorder.{u + 1} NatOrdinal.{u} NatOrdinal.instPartialOrder.{u}))
                z.birthday w.birthday),
      @Eq.{u + 2} Surreal.{u}
        (@OfSets.ofSets.{u} Surreal.{u}
          (fun (st : Player → Set.{u + 1} Surreal.{u}) =>
            ∀ (x : Surreal.{u}),
              @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u})
                  (st Player.left) x →
                ∀ (y : Surreal.{u}),
                  @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                      (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.right) y →
                    @LT.lt.{u + 1} Surreal.{u}
                      (@Preorder.toLT.{u + 1} Surreal.{u}
                        (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                      x y)
          Surreal.instOfSetsForallForallMemSetLeftForallForallRightLt.{u} st
          (@HypCheckProof.Surreal.ofSets_eq_of_forall_birthday_le'.h4.der.{u} st z inst inst_1 hL hR h) inst inst_1)
        z := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Surreal.ofSets_eq_of_forall_birthday_le' hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Surreal.ofSets_eq_of_forall_birthday_le'.h4.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x4 hc_x5 hc_x6

