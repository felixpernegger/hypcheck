module
public import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Surreal.birthday_ofSets_lt_of_btwn, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn.h5.der.{u} : ∀ {s t : Set.{u + 1} Surreal.{u}} {z : Surreal.{u}} [inst : Small.{u, u + 1} (@Set.Elem.{u + 1} Surreal.{u} s)]
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
          ∀ (x : Surreal.{u}),
            @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u}) s
                x →
              ∀ (y : Surreal.{u}),
                @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                    (@Set.instMembership.{u + 1} Surreal.{u}) t y →
                  @LT.lt.{u + 1} Surreal.{u}
                    (@Preorder.toLT.{u + 1} Surreal.{u}
                      (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                    x y := by
  (intros; grind)
theorem HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn.h5.{u} : ∀ {s t : Set.{u + 1} Surreal.{u}} {z : Surreal.{u}} [inst : Small.{u, u + 1} (@Set.Elem.{u + 1} Surreal.{u} s)]
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
              z y),
      @Ne.{u + 2} Surreal.{u}
          (@OfSets.ofSets.{u} Surreal.{u}
            (fun (st : Player → Set.{u + 1} Surreal.{u}) =>
              ∀ (x : Surreal.{u}),
                @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                    (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.left) x →
                  ∀ (y : Surreal.{u}),
                    @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                        (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.right) y →
                      @LT.lt.{u + 1} Surreal.{u}
                        (@Preorder.toLT.{u + 1} Surreal.{u}
                          (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                        x y)
            Surreal.instOfSetsForallForallMemSetLeftForallForallRightLt.{u}
            (@Player.cases.{u + 2} (Set.{u + 1} Surreal.{u}) s t)
            (@HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn.h5.der.{u} s t z inst inst_1 hL hR) inst inst_1)
          z →
        @LT.lt.{u + 1} NatOrdinal.{u}
          (@Preorder.toLT.{u + 1} NatOrdinal.{u}
            (@PartialOrder.toPreorder.{u + 1} NatOrdinal.{u} NatOrdinal.instPartialOrder.{u}))
          (@OfSets.ofSets.{u} Surreal.{u}
              (fun (st : Player → Set.{u + 1} Surreal.{u}) =>
                ∀ (x : Surreal.{u}),
                  @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                      (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.left) x →
                    ∀ (y : Surreal.{u}),
                      @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                          (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.right) y →
                        @LT.lt.{u + 1} Surreal.{u}
                          (@Preorder.toLT.{u + 1} Surreal.{u}
                            (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                          x y)
              Surreal.instOfSetsForallForallMemSetLeftForallForallRightLt.{u}
              (@Player.cases.{u + 2} (Set.{u + 1} Surreal.{u}) s t)
              (@HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn.h5.der.{u} s t z inst inst_1 hL hR) inst inst_1).birthday
          z.birthday := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact @Surreal.birthday_ofSets_lt_of_btwn hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x5 hc_x6 hc_x7

-- Surreal.birthday_ofSets_le_of_btwn, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Surreal.birthday_ofSets_le_of_btwn.h5.der.{u} : ∀ {s t : Set.{u + 1} Surreal.{u}} {z : Surreal.{u}} [inst : Small.{u, u + 1} (@Set.Elem.{u + 1} Surreal.{u} s)]
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
          ∀ (x : Surreal.{u}),
            @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u}) (@Set.instMembership.{u + 1} Surreal.{u}) s
                x →
              ∀ (y : Surreal.{u}),
                @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                    (@Set.instMembership.{u + 1} Surreal.{u}) t y →
                  @LT.lt.{u + 1} Surreal.{u}
                    (@Preorder.toLT.{u + 1} Surreal.{u}
                      (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                    x y := by
  (intros; grind)
theorem HypCheckProof.Surreal.birthday_ofSets_le_of_btwn.h5.{u} : ∀ {s t : Set.{u + 1} Surreal.{u}} {z : Surreal.{u}} [inst : Small.{u, u + 1} (@Set.Elem.{u + 1} Surreal.{u} s)]
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
              z y),
      @LE.le.{u + 1} NatOrdinal.{u}
        (@Preorder.toLE.{u + 1} NatOrdinal.{u}
          (@PartialOrder.toPreorder.{u + 1} NatOrdinal.{u} NatOrdinal.instPartialOrder.{u}))
        (@OfSets.ofSets.{u} Surreal.{u}
            (fun (st : Player → Set.{u + 1} Surreal.{u}) =>
              ∀ (x : Surreal.{u}),
                @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                    (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.left) x →
                  ∀ (y : Surreal.{u}),
                    @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                        (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.right) y →
                      @LT.lt.{u + 1} Surreal.{u}
                        (@Preorder.toLT.{u + 1} Surreal.{u}
                          (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                        x y)
            Surreal.instOfSetsForallForallMemSetLeftForallForallRightLt.{u}
            (@Player.cases.{u + 2} (Set.{u + 1} Surreal.{u}) s t)
            (@HypCheckProof.Surreal.birthday_ofSets_le_of_btwn.h5.der.{u} s t z inst inst_1 hL hR) inst inst_1).birthday
        z.birthday := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Surreal.birthday_ofSets_le_of_btwn hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Surreal.birthday_ofSets_le_of_btwn.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x5 hc_x6

-- Surreal.birthday_ofSets_lt_of_btwn', hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn'.h4.der.{u} : ∀ {st : Player → Set.{u + 1} Surreal.{u}} {z : Surreal.{u}}
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
theorem HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn'.h4.{u} : ∀ {st : Player → Set.{u + 1} Surreal.{u}} {z : Surreal.{u}}
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
              z y),
      @Ne.{u + 2} Surreal.{u}
          (@OfSets.ofSets.{u} Surreal.{u}
            (fun (st : Player → Set.{u + 1} Surreal.{u}) =>
              ∀ (x : Surreal.{u}),
                @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                    (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.left) x →
                  ∀ (y : Surreal.{u}),
                    @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                        (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.right) y →
                      @LT.lt.{u + 1} Surreal.{u}
                        (@Preorder.toLT.{u + 1} Surreal.{u}
                          (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                        x y)
            Surreal.instOfSetsForallForallMemSetLeftForallForallRightLt.{u} st
            (@HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn'.h4.der.{u} st z inst inst_1 hL hR) inst inst_1)
          z →
        @LT.lt.{u + 1} NatOrdinal.{u}
          (@Preorder.toLT.{u + 1} NatOrdinal.{u}
            (@PartialOrder.toPreorder.{u + 1} NatOrdinal.{u} NatOrdinal.instPartialOrder.{u}))
          (@OfSets.ofSets.{u} Surreal.{u}
              (fun (st : Player → Set.{u + 1} Surreal.{u}) =>
                ∀ (x : Surreal.{u}),
                  @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                      (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.left) x →
                    ∀ (y : Surreal.{u}),
                      @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                          (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.right) y →
                        @LT.lt.{u + 1} Surreal.{u}
                          (@Preorder.toLT.{u + 1} Surreal.{u}
                            (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                          x y)
              Surreal.instOfSetsForallForallMemSetLeftForallForallRightLt.{u} st
              (@HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn'.h4.der.{u} st z inst inst_1 hL hR) inst inst_1).birthday
          z.birthday := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Surreal.birthday_ofSets_lt_of_btwn' hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn'.h4.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x4 hc_x5 hc_x6

-- Surreal.birthday_ofSets_le_of_btwn', hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Surreal.birthday_ofSets_le_of_btwn'.h4.der.{u} : ∀ {st : Player → Set.{u + 1} Surreal.{u}} {z : Surreal.{u}}
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
theorem HypCheckProof.Surreal.birthday_ofSets_le_of_btwn'.h4.{u} : ∀ {st : Player → Set.{u + 1} Surreal.{u}} {z : Surreal.{u}}
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
              z y),
      @LE.le.{u + 1} NatOrdinal.{u}
        (@Preorder.toLE.{u + 1} NatOrdinal.{u}
          (@PartialOrder.toPreorder.{u + 1} NatOrdinal.{u} NatOrdinal.instPartialOrder.{u}))
        (@OfSets.ofSets.{u} Surreal.{u}
            (fun (st : Player → Set.{u + 1} Surreal.{u}) =>
              ∀ (x : Surreal.{u}),
                @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                    (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.left) x →
                  ∀ (y : Surreal.{u}),
                    @Membership.mem.{u + 1, u + 1} Surreal.{u} (Set.{u + 1} Surreal.{u})
                        (@Set.instMembership.{u + 1} Surreal.{u}) (st Player.right) y →
                      @LT.lt.{u + 1} Surreal.{u}
                        (@Preorder.toLT.{u + 1} Surreal.{u}
                          (@PartialOrder.toPreorder.{u + 1} Surreal.{u} Surreal.instPartialOrder.{u}))
                        x y)
            Surreal.instOfSetsForallForallMemSetLeftForallForallRightLt.{u} st
            (@HypCheckProof.Surreal.birthday_ofSets_le_of_btwn'.h4.der.{u} st z inst inst_1 hL hR) inst inst_1).birthday
        z.birthday := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Surreal.birthday_ofSets_le_of_btwn' hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Surreal.birthday_ofSets_le_of_btwn'.h4.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x4 hc_x5

