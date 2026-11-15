# Removable hypotheses in iris-lean: review list

195 removable hypotheses (10 in private theorems) in 147 theorems. Each has a stored, kernel-checked proof of the theorem without it (file and declaration in the last column; standard axioms only). "Derivable" means the hypothesis itself follows from the other binders, so it can never fail where the theorem applies; otherwise it is just unneeded. Removing a hypothesis from a public lemma breaks callers that pass it explicitly: these are candidates, not patches.

## Iris.Algebra.Agree

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.Agree.agree_map_ext` | 6 | `inst : Iris.OFE.NonExpansive f` | yes | removable: H gives f = g by funext, so NonExpansive f is NonExpansive g (w0_55) | `checks/W1c0Hand.lean` w0_55 |
| `Iris.Agree.agree_map_ext` | 7 | `inst : Iris.OFE.NonExpansive g` | yes | removable: H gives f = g by funext, so NonExpansive g is NonExpansive f (w0_56) | `checks/W1c0Hand.lean` w0_56 |

## Iris.Algebra.Auth

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `AuthViewRel.instIsViewRelDiscreteOfDiscreteOfDiscrete` | 2 | `inst : Iris.OFE.Discrete A` |  | unused in the library's own proof (directly or transitively); stored proof `drop_unused%` | `checks/UnusedHand.lean` HypCheckProof.AuthViewRel.instIsViewRelDiscreteOfDiscreteOfDiscrete.h2 |
| `Auth.auth_update_alloc` | 2 | `inst : Iris.OrdInc A` |  | removable: the local update at the frame some a gives a' =n= b' • a and valid a', which is the order-based premise of auth_update_alloc_ord (no OrdInc needed) (w0_105) | `checks/W1c0Hand.lean` w0_105 |
| `Auth.auth_update_auth` | 2 | `inst : Iris.OrdInc A` |  | removable: the removable variant of auth_update_alloc (no OrdInc) followed by Update.op_l (w0_119) | `checks/W1c0Hand.lean` w0_119 |

## Iris.Algebra.BigOp

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.Algebra.BigOpM.bigOpM_gen_proper_2` | 15 | `hR_sub : ∀ {x y : M}, x = y → R x y` | yes | derivable: hR_sub follows from reflexivity in hR_eqv | `checks/W1c1Hand.lean` c1_r1 |
| `Iris.Algebra.BigOpM.bigOpM_gen_proper_2` | 16 | `hR_eqv : Equivalence R` |  | the library proof uses transitivity only to chain the equalities given by hR_sub; rewriting them instead needs no Equivalence | `checks/W1c1Hand.lean` c1_r2 |
| `Iris.Algebra.BigOpM.bigOpM_filterMap_eq` | 12 | `hinj : Function.Injective h` |  | keys of a map are distinct, so injectivity of h is not needed; induction on m | `checks/W1c1Hand.lean` c1_r3 |

## Iris.Algebra.CMRA

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.ORA.validN_core` | 2 | `inst : Iris.IsTotal α` |  | without a core core x = x, else pcore_validN | `checks/W1c3Hand.lean` c3_63 |
| `Iris.ORA.valid_core` | 2 | `inst : Iris.IsTotal α` |  | without a core core x = x, else pcore_valid | `checks/W1c3Hand.lean` c3_65 |
| `Iris.ORA.core_ne` | 2 | `inst : Iris.IsTotal α` |  | core is non-expansive by pcore_ne alone (helper core_dist) | `checks/W1c3Hand.lean` c3_67 |
| `Iris.OFE.Dist.core` | 2 | `inst : Iris.IsTotal α` |  | helper core_dist | `checks/W1c3Hand.lean` c3_68 |
| `Iris.ORA.core_eqv_self` | 2 | `inst : Iris.IsTotal α` |  | CoreId gives pcore x = some x | `checks/W1c3Hand.lean` c3_70 |
| `Iris.ORA.core_idem` | 2 | `inst : Iris.IsTotal α` |  | by cases on pcore x and pcore_idem | `checks/W1c3Hand.lean` c3_73 |
| `Iris.ORA.core_idem_L` | 3 | `inst : Iris.IsTotal α` |  | core x = (pcore x).getD x; if pcore x = some cx then pcore cx = some cx (pcore_idem), else core x = x (the IsTotal sibling core_idem / core_eqv_self has no IsTotal-free variant in the library) | `checks/RemTrans1g0Hand.lean` rt1g0_0 |
| `Iris.ORA.core_eq_self` | 3 | `inst : Iris.IsTotal α` |  | CoreId x gives pcore x = some x, so core x = x without IsTotal (the IsTotal sibling core_idem / core_eqv_self has no IsTotal-free variant in the library) | `checks/W1c5Hand.lean` w5_55 |
| `Iris.DiscreteFun.instOrderRefl` | 4 | `inst : ∀ (x : α), Iris.OrderRefl (β x)` | yes | derivable by instance resolution from the other binders | `checks/InstDerivHand.lean` HypCheckProof.Iris.DiscreteFun.instOrderRefl.h4 |

## Iris.Algebra.DynReservationMap

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.DynReservationMap.increasing_token` | 5 | `h : Iris.Increasing v` |  | the token CMRA (DisjointLeibnizSet) orders by inclusion, so every token is increasing | `checks/W2c1Hand.lean` w21_20 |
| `Iris.DynReservationMap.increasing_mk` | 6 | `ht : Iris.Increasing v.token` | yes | every DisjointLeibnizSet token is increasing (inclusion order) | `checks/W2c1Hand.lean` w21_22 |

## Iris.Algebra.GenMap

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.GenMap.valid_exists_fresh` | 4 | `_Hv : ✓{n} g` |  | unused in the library's own proof (directly or transitively); stored proof `drop_unused%` | `checks/UnusedHand.lean` HypCheckProof.Iris.GenMap.valid_exists_fresh.h4 |

## Iris.Algebra.Mra

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.Mra.local_update_get_frag` | 2 | `inst : Std.Refl R` |  | unused in the library's own proof (directly or transitively); stored proof `drop_unused%` | `checks/UnusedHand.lean` HypCheckProof.Iris.Mra.local_update_get_frag.h2 |

## Iris.Algebra.Numbers

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `OrdCommMonoidLike.instCancelable` | 2 | `inst : Iris.OFE.Discrete α` | yes | derivable: left cancellation plus idempotence and commutativity force y + x = x = x + y, so the type is a subsingleton and trivially discrete | `checks/W3c0Hand.lean` w3c0_r1 |

## Iris.Algebra.OFE

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.OFE.Iso.ext` | 6 | `hom : x.hom = y.hom` |  | the hom of an isomorphism is determined by its inverse | `checks/W3c1Hand.lean` w3c1_81 |
| `Iris.OFE.Iso.ext` | 7 | `inv : x.inv = y.inv` |  | the inverse of an isomorphism is determined by its hom | `checks/W3c1Hand.lean` w3c1_82 |
| `Iris.fixpoint_proper` | 5 | `inst : Iris.OFE.Contractive f` | yes | the equation hypothesis makes f = g, so Contractive f is Contractive g | `checks/W3c1Hand.lean` w3c1_114 |
| `Iris.fixpoint_proper` | 6 | `inst : Iris.OFE.Contractive g` | yes | the equation hypothesis makes f = g, so Contractive g is Contractive f | `checks/W3c1Hand.lean` w3c1_115 |
| `Iris.fixpointK_proper` | 6 | `inst : Iris.OFE.Contractive (Nat.repeat f k)` | yes | the equation hypothesis makes f = g | `checks/W3c1Hand.lean` w3c1_128 |
| `Iris.fixpointK_proper` | 7 | `inst : Iris.OFE.Contractive (Nat.repeat g k)` | yes | the equation hypothesis makes f = g | `checks/W3c1Hand.lean` w3c1_129 |
| `Iris.fixpointK_proper` | 8 | `inst : Iris.OFE.NonExpansive f` |  | Hfg gives f = g by funext; the Contractive instances are Props, so rfl | `checks/Probe1Hand.lean` Probe1.p1_43 |

## Iris.Algebra.ReservationMap

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.ReservationMap.increasing_token` | 5 | `h : Iris.Increasing v` |  | the token CMRA (DisjointLeibnizSet) orders by inclusion, so every token is increasing (w32_r15) | `checks/W3c2Hand.lean` w32_r15 |
| `Iris.ReservationMap.increasing_mk` | 6 | `ht : Iris.Increasing v.token` |  | every DisjointLeibnizSet token is increasing (inclusion order) (w32_r17) | `checks/W3c2Hand.lean` w32_r17 |

## Iris.Algebra.UPred

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.ValidAt.le_rfl` | 3 | `Hle : n ≤ n` | yes | HypCheck proved the theorem without it by `omega` | ``  |
| `Iris.uPred_holds_ne` | 9 | `Hx : ✓{n₂} x` | yes | validity at n2 follows from validity at n1 since n2 ≤ n1 (w32_p13) | `checks/W3c2Hand.lean` w32_p13 |

## Iris.Algebra.View

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `View.increasing_auth` | 6 | `h : Iris.Increasing v` |  | Option (DFrac × Agree A) is IncOrd, so every auth part is increasing | `checks/W3c4Hand.lean` w3c4_39 |
| `View.increasing_mk` | 6 | `ha : Iris.Increasing v.auth` | yes | the auth part is always increasing: Option (DFrac × Agree A) is IncOrd | `checks/W3c4Hand.lean` w3c4_41 |
| `View.instDiscreteOfDiscreteOfIsViewRelDiscrete` | 5 | `inst : IsViewRel R` | yes | IsViewRel R follows from the binder IsViewRelDiscrete R | `checks/W3c4Hand.lean` w3c4_52 |
| `View.map_ne` | 14 | `inst : Iris.OFE.NonExpansive f1` |  | the proof only needs pointwise f1 a =n= f2 a for Agree.map'; NonExpansive f1 is used only to form the coerced Agree.map in Agree.map_ne, whose proof does not use it | `checks/Probe2Hand.lean` Probe2.p2_39 |
| `View.map_ne` | 15 | `inst : Iris.OFE.NonExpansive f2` |  | the proof only needs pointwise f1 a =n= f2 a for Agree.map' | `checks/W3c4Hand.lean` w3c4_131 |

## Iris.BI.BI

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.BI.BIBase.BiEntails.ofMono` | 5 | `mono : ∀ {P Q : PROP1}, (P ⊢ Q) → mod P ⊢ mod Q` |  | bi-entailment is equality in every BI, `BiEntails.to_eq`, so mod P = mod Q | `checks/W4c0Hand.lean` w4c0_24 |

## Iris.BI.BigOp.BigAndMap

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.BI.BigAndM.bigAndM_filterMap` | 9 | `hinj : Function.Injective f` |  | only passed on to removable hypotheses of other theorems (removable by transitivity) | `checks/RemTrans2g0Hand.lean` rt2g0_0 |

## Iris.BI.BigOp.BigSepList

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.BI.BigSepL.bigSepL_forall_intro` | 6 | `inst : ∀ (k : Nat) (x : A), Iris.BI.Persistent (Φ k x)` |  | in an affine BI every element of the big separating conjunction can be extracted by bigSepL_lookup; persistence is only needed for the converse | `checks/W4c1Hand.lean` w4c1_106 |
| `(private) Iris.BI.BigOp.BigSepList.0.Iris.BI.BigSepL2.zip_set` | 5 | `hi1 : i < l1.length` |  | zip and set commute for every index: out of range both sides are unchanged; induction on the lists | `checks/W4c1Hand.lean` w4c1_107 |
| `(private) Iris.BI.BigOp.BigSepList.0.Iris.BI.BigSepL2.zip_set` | 6 | `hi2 : i < l2.length` |  | zip and set commute for every index: out of range both sides are unchanged; induction on the lists | `checks/W4c1Hand.lean` w4c1_108 |
| `Iris.BI.BigSepL2.bigSepL2_sep_sepL_left` | 4 | `inst : Iris.BI.BIAffine PROP` |  | holds in every BI: induction on the lists; equal heads by sep_sep_sep_comm, different lengths give False on both sides | `checks/W4c1Hand.lean` w4c1_109 |
| `Iris.BI.BigSepL2.bigSepL2_sep_sepL_right` | 4 | `inst : Iris.BI.BIAffine PROP` |  | the library derivation from bigSepL2_sep_sepL_left goes through with the BIAffine-free version | `checks/W4c1Hand.lean` w4c1_110 |

## Iris.BI.BigOp.BigSepMap

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.BI.BigSepM.bigSepM_absorbing` | 9 | `h : ∀ {k : K} {x : V}, Iris.Std.get? m k = some x → Iris.BI.Absorbing (Φ …` |  | BIAffine is kept, and in an affine BI every proposition is absorbing | `checks/W4c2Hand.lean` W4c2.w4c2_19 |
| `Iris.BI.BigSepM.bigSepM_absorbing_inst` | 9 | `inst : ∀ (k : K) (x : V), Iris.BI.Absorbing (Φ k x)` | yes | derivable by instance resolution from the other binders | `checks/InstDerivHand.lean` HypCheckProof.Iris.BI.BigSepM.bigSepM_absorbing_inst.h9 |
| `Iris.BI.BigSepM.bigSepM_forall_intro` | 9 | `inst : ∀ (k : K) (v : V), Iris.BI.Persistent (Φ k v)` |  | BIAffine is kept: each conjunct is extracted by bigSepM_lookup, whose Affine side condition BIAffine provides | `checks/W4c2Hand.lean` W4c2.w4c2_35 |
| `Iris.BI.BigSepM.bigSepM_filterMap` | 9 | `hinj : Function.Injective f` |  | only passed on to removable hypotheses of other theorems (removable by transitivity) | `checks/RemTrans2g0Hand.lean` rt2g0_1 |

## Iris.BI.BigOp.BigSepMap2

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.BI.BigSepM2.bigSepM2_closed` | 11 | `hproper : ∀ {Q1 Q2 : PROP}, Q1 ⊣⊢ Q2 → (P Q1 ↔ P Q2)` | yes | derivable: BI.equiv_iff makes bi-entailment equality, so every predicate respects it | `checks/W4c2Hand.lean` W4c2.w4c2_130 |

## Iris.BI.DerivedLaws

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.BI.affinelyIf_idem` | 3 | `inst : Iris.BI.BIPositive PROP` |  | unused in the library's own proof (directly or transitively); stored proof `drop_unused%` | `checks/UnusedHand.lean` HypCheckProof.Iris.BI.affinelyIf_idem.h3 |
| `Iris.BI.persistentlyIf_idem` | 3 | `inst : Iris.BI.BIPositive PROP` |  | unused in the library's own proof (directly or transitively); stored proof `drop_unused%` | `checks/UnusedHand.lean` HypCheckProof.Iris.BI.persistentlyIf_idem.h3 |

## Iris.BI.DerivedLawsLater

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.BI.loeb_alt_wand` | 2 | `inst : Iris.BI.BIAffine PROP` |  | no affinity needed: for ▷P ⊢ P put Q := True -∗ P; then ▷Q ⊢ Q, so emp ⊢ □(▷Q -∗ Q) ⊢ Q and True ⊢ emp ∗ True ⊢ P; the other direction is loeb_wand | `checks/T1c1Hand.lean` t1c1_1 |
| `Iris.BI.impl_timeless` | 2 | `inst : Iris.BI.BILoeb PROP` |  | no Loeb needed: ▷(P→Q) ⊢ ▷False ∨ (▷False → P → Q) (later_false_em) and ⊢ P → ▷False ∨ Q (Timeless Q); combine | `checks/T1c1Hand.lean` t1c1_4 |
| `Iris.BI.wand_timeless` | 2 | `inst : Iris.BI.BILoeb PROP` |  | no Loeb needed: later_false_em plus P -∗ ▷False ∨ Q, ▷False persistent (helper wandT) | `checks/T1c1Hand.lean` t1c1_5 |
| `Iris.BI.wandIff_timeless` | 2 | `inst : Iris.BI.BILoeb PROP` |  | both wands timeless by wandT, then and_timeless | `checks/T1c1Hand.lean` t1c1_6 |
| `Iris.BI.only0_intuitionistically_mpr` | 2 | `inst : Iris.BI.BILoeb PROP` |  | only0_persistently_mpr plus the mpr half of only0_affinely, which needs neither Loeb nor Timeless emp | `checks/T1c1Hand.lean` t1c1_8 |
| `Iris.BI.only0_intuitionistically_mpr` | 3 | `inst : Iris.BI.Timeless iprop(emp)` |  | same proof as idx 2: Timeless emp unused | `checks/T1c1Hand.lean` t1c1_9 |
| `Iris.BI.only0_except0` | 2 | `inst : Iris.BI.BILoeb PROP` |  | ▷False → ▷False ∨ P is valid in every BI | `checks/T1c1Hand.lean` t1c1_7 |

## Iris.BI.Lib.Counterexamples

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.AffineEM.sep_dup` | 2 | `inst : Iris.BI.BIPersistentlyExist PROP` |  | case split on em P without destructing under the box: P ∧ (P ∗ ¬P) ⊢ P ∧ ¬P by affinity of P | `checks/W5c2Hand.lean` w5c2_104 |
| `Iris.AffineEM.and_sep` | 2 | `inst : Iris.BI.BIPersistentlyExist PROP` |  | the same duplication of the affine P ∧ Q, then split | `checks/W5c2Hand.lean` w5c2_105 |
| `Iris.LoebEM.later_anything` | 3 | `inst : Iris.BI.BIPersistentlyExist PROP` |  | case split on em (later False); the negative case is Löb for False | `checks/W5c2Hand.lean` w5c2_38 |
| `Iris.LoebEM.later_inconsistent` | 2 | `inst : Iris.BI.BIPersistentlyExist PROP` |  | same argument, Löb from Sbi, then later soundness | `checks/W5c2Hand.lean` w5c2_39 |
| `Iris.SavedProp.saved_NA` | 2 | `instPersExist : Iris.BI.BIPersistentlyExist PROP` |  | A i is used only under ∧; agree makes saved affine, persistence gives saved i P from the box | `checks/W5c2Hand.lean` w5c2_97 |
| `Iris.SavedProp.saved_NA` | 3 | `instAffine : Iris.BI.BIAffine PROP` |  | agree makes saved affine; persistence gives saved i P from the box | `checks/W5c2Hand.lean` w5c2_98 |
| `Iris.SavedProp.saved_NA` | 6 | `instPers : ∀ (i : ident) (P : PROP), Iris.BI.Persistent (saved i P)` |  | with BIAffine both halves of the boxed separating conjunction are available; only ∧-reasoning | `checks/W5c2Hand.lean` w5c2_99 |
| `Iris.SavedProp.saved_A` | 2 | `instPersExist : Iris.BI.BIPersistentlyExist PROP` |  | agree makes saved affine, so saved i (A i) is intuitionistic; then saved_NA without BIPersistentlyExist | `checks/W5c2Hand.lean` w5c2_100 |
| `Iris.SavedProp.saved_A` | 3 | `instAffine : Iris.BI.BIAffine PROP` |  | same proof; affinity of saved i P follows from agree | `checks/W5c2Hand.lean` w5c2_101 |
| `Iris.SavedProp.contradiction` | 2 | `instPersExist : Iris.BI.BIPersistentlyExist PROP` |  | saved_NA and saved_A hold without BIPersistentlyExist and BIAffine, so the allocated proposition equals False and alloc plus consistency suffice | `checks/W5c2Hand.lean` w5c2_102 |
| `Iris.SavedProp.contradiction` | 3 | `instAffine : Iris.BI.BIAffine PROP` |  | saved_NA and saved_A hold without BIPersistentlyExist and BIAffine, so the allocated proposition equals False and alloc plus consistency suffice | `checks/W5c2Hand.lean` w5c2_103 |
| `Iris.SavedProp.contradiction` | 7 | `instPers : ∀ (i : ident) (P : PROP), Iris.BI.Persistent (saved i P)` |  | persistence of saved not needed: with A' i := ∃ Q, ¬Q ∧ saved i Q (∧ instead of □(¬Q ∗ saved i Q)) agreement gives saved i (A' i) ∧ A' i ⊢ False and saved i (A' i) ⊢ A' i by ∧-duplication; sprop_alloc_dep with A', bupd_… | `checks/T1c2Hand.lean` t1c2_16 |
| `Iris.SavedProp.contradiction` | 8 | `bupd_intro : ∀ {P : PROP}, P ⊢ bupd P` |  | saved_A and saved_NA make the allocated name contradictory, so the allocated proposition equals False and alloc plus consistency suffice | `checks/W5c2Hand.lean` w5c2_48 |
| `Iris.SavedProp.contradiction` | 9 | `bupd_mono : ∀ {P Q : PROP}, (P ⊢ Q) → bupd P ⊢ bupd Q` |  | saved_A and saved_NA make the allocated name contradictory, so the allocated proposition equals False and alloc plus consistency suffice | `checks/W5c2Hand.lean` w5c2_49 |
| `Iris.SavedProp.contradiction` | 10 | `bupd_trans : ∀ {P : PROP}, bupd (bupd P) ⊢ bupd P` |  | saved_A and saved_NA make the allocated name contradictory, so the allocated proposition equals False and alloc plus consistency suffice | `checks/W5c2Hand.lean` w5c2_50 |
| `Iris.SavedProp.contradiction` | 11 | `bupd_frame_right : ∀ {P R : PROP}, bupd P ∗ R ⊢ bupd iprop(P ∗ R)` |  | saved_A and saved_NA make the allocated name contradictory, so the allocated proposition equals False and alloc plus consistency suffice | `checks/W5c2Hand.lean` w5c2_51 |
| `Iris.Inv.inv_fupd'` | 2 | `instAffine : Iris.BI.BIAffine PROP` |  | inv_fupd with Q the wand and wand elimination, then fupd_fupd; no affinity used | `checks/W5c2Hand.lean` w5c2_40 |
| `Iris.Inv.inv_fupd'` | 8 | `inst : ∀ (i : name) (P : PROP), Iris.BI.Persistent (inv i P)` |  | same proof; persistence of inv unused | `checks/W5c2Hand.lean` w5c2_41 |
| `Iris.Inv.fupd_proper` | 5 | `fupd_mono : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, (P ⊢ Q) → fupd E P ⊢ fupd E Q` |  | P ⊣⊢ Q gives P = Q, `BiEntails.to_eq` | `checks/W5c2Hand.lean` w5c2_14 |
| `Iris.Inv.fupd_frame_right` | 5 | `fupd_mono : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, (P ⊢ Q) → fupd E P ⊢ fupd E Q` |  | frame_left plus commutativity; Q ∗ P = P ∗ Q by `BiEntails.to_eq` | `checks/W5c2Hand.lean` w5c2_16 |
| `Iris.Inv.saved_alloc` | 2 | `instAffine : Iris.BI.BIAffine PROP` |  | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; no affinity used | `checks/W5c2Hand.lean` w5c2_55 |
| `Iris.Inv.saved_alloc` | 6 | `inst : ∀ (i : name) (P : PROP), Iris.BI.Persistent (inv i P)` |  | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; persistence of inv unused | `checks/W5c2Hand.lean` w5c2_56 |
| `Iris.Inv.saved_alloc` | 7 | `fupd_intro : ∀ {E : Iris.Inv.Mask} {P : PROP}, P ⊢ fupd E P` |  | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; fupd_intro unused | `checks/W5c2Hand.lean` w5c2_57 |
| `Iris.Inv.saved_alloc` | 10 | `fupd_frame_left : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, P ∗ fupd E Q ⊢ fupd E iprop(P ∗ Q)` |  | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; fupd_frame_left unused | `checks/W5c2Hand.lean` w5c2_58 |
| `Iris.Inv.A_alloc` | 2 | `instAffine : Iris.BI.BIAffine PROP` |  | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; no affinity used | `checks/W5c2Hand.lean` w5c2_59 |
| `Iris.Inv.A_alloc` | 6 | `inst : ∀ (i : name) (P : PROP), Iris.BI.Persistent (inv i P)` |  | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; persistence of inv unused | `checks/W5c2Hand.lean` w5c2_60 |
| `Iris.Inv.A_alloc` | 7 | `fupd_intro : ∀ {E : Iris.Inv.Mask} {P : PROP}, P ⊢ fupd E P` |  | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; fupd_intro unused | `checks/W5c2Hand.lean` w5c2_61 |
| `Iris.Inv.A_alloc` | 10 | `fupd_frame_left : ∀ {E : Iris.Inv.Mask} {P Q : PROP}, P ∗ fupd E Q ⊢ fupd E iprop(P ∗ Q)` |  | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; fupd_frame_left unused | `checks/W5c2Hand.lean` w5c2_62 |
| `Iris.Inv.contradiction` | 2 | `instAffine : Iris.BI.BIAffine PROP` |  | removable: Inv1 paradox in any BI: saved γ P := ∃ i, inv i (start γ ∨ finished γ ∗ <pers>P), A γ := ∃ P, <pers>(P -∗ fupd M1 False) ∗ saved γ P; the extra finished token is carried along and finally absorbed by False ∗ … | `checks/T2c1Hand.lean` t2c1_9 |
| `Iris.Inv.contradiction` | 7 | `fupd_intro : ∀ {E : Iris.Inv.Mask} {P : PROP}, P ⊢ fupd E P` |  | fupd_intro derived: X ⊢ X ∗ fupd M0 (∃ γ, start γ) (sts_alloc), frame, mono with affinity gives fupd M0 X; mask_mono gives M1 | `checks/T1c2Hand.lean` t1c2_10 |
| `Iris.Inv.contradiction` | 11 | `fupd_mask_mono : ∀ {P : PROP}, fupd Iris.Inv.Mask.M0 P ⊢ fupd Iris.Inv.Mask.M1 P` |  | mask_mono derived: inv_alloc True framed into fupd M1, then inv_fupd with P = True turns fupd M0 X into fupd M1 X, fupd_fupd | `checks/T1c2Hand.lean` t1c2_1 |
| `Iris.Inv.contradiction'` | 2 | `instAffine : Iris.BI.BIAffine PROP` |  | removable: the Inv2 paradox goes through in any BI with B := <pers>(fupd M1 False) (leftovers absorbed by persistently_absorb_l, <pers>X ⊢ X ∗ <pers>X), so BIAffine is not needed | `checks/T2c1Hand.lean` t2c1_8 |
| `Iris.Inv.contradiction'` | 7 | `fupd_intro : ∀ {E : Iris.Inv.Mask} {P : PROP}, P ⊢ fupd E P` |  | fupd_intro derived: X ⊢ X ∗ fupd M0 (∃ γ, start γ) (sts_alloc), frame, mono with affinity gives fupd M0 X; mask_mono gives M1 | `checks/T1c2Hand.lean` t1c2_11 |
| `Iris.Inv.contradiction'` | 11 | `fupd_mask_mono : ∀ {P : PROP}, fupd Iris.Inv.Mask.M0 P ⊢ fupd Iris.Inv.Mask.M1 P` |  | mask_mono derived: inv_alloc True framed into fupd M1, then inv_fupd with P = True turns fupd M0 X into fupd M1 X, fupd_fupd | `checks/T1c2Hand.lean` t1c2_2 |
| `Iris.Linear.fupd_proper` | 5 | `fupd_mono : ∀ {E1 E2 : Iris.Linear.Mask} {P Q : PROP}, (P ⊢ Q) → fupd E1 E2 P ⊢ f…` |  | P ⊣⊢ Q gives P = Q, `BiEntails.to_eq` | `checks/W5c2Hand.lean` w5c2_31 |
| `Iris.Linear.fupd_frame_right` | 5 | `fupd_mono : ∀ {E1 E2 : Iris.Linear.Mask} {P Q : PROP}, (P ⊢ Q) → fupd E1 E2 P ⊢ f…` |  | frame_left plus commutativity; Q ∗ P = P ∗ Q by `BiEntails.to_eq` | `checks/W5c2Hand.lean` w5c2_33 |
| `Iris.Linear.leak` | 11 | `fupd_frame_left : ∀ {E1 E2 : Iris.Linear.Mask} {P Q : PROP}, P ∗ fupd E1 E2 Q ⊢ fupd E1…` |  | frame not needed: ▷True is absorbing, so ▷True ∗ cinv_own ⊢ ▷True feeds the closing wand directly; P ⊢ True ⊢ ▷True, cinv_alloc, cinv_acc, fupd_mono, fupd_fupd twice | `checks/T1c2Hand.lean` t1c2_9 |
| `Iris.LaterCreditsPlain.lc_fupd_elim_later_keep` | 8 | `inst1 : Iris.BI.Plain P` |  | removable: lc_fupd_elim_later and fupd_keep_si_pure' give lc ⊢ \|={E}=> False (Löb from Sbi, library lemma for P = ▷^n False), so lc ∗ ▷P ⊢ \|={E}=> lc ∗ P for every P | `checks/T2c1Hand.lean` t2c1_1 |
| `Iris.LaterCreditsPlain.lc_fupd_elim_later_keep` | 9 | `inst2 : Iris.BI.Absorbing P` |  | removable: same derivation as idx 8 (lc ⊢ \|={E}=> False from the two hypotheses), Absorbing P unused | `checks/T2c1Hand.lean` t2c1_2 |
| `Iris.LaterCreditsPlain.laterN_False` | 2 | `instPersExist : Iris.BI.BIPersistentlyExist PROP` |  | later of an existential splits into later False or an existential of laters, so the predicate is closed under later; weak Löb | `checks/W5c2Hand.lean` w5c2_77 |
| `Iris.LaterCreditsPlain.laterN_False` | 3 | `inst : Iris.BI.BILoeb PROP` | yes | derivable by instance resolution from the other binders | `checks/InstDerivHand.lean` HypCheckProof.Iris.LaterCreditsPlain.laterN_False.h3 |
| `Iris.LaterCreditsPlain.contradiction` | 2 | `instPersExist : Iris.BI.BIPersistentlyExist PROP` |  | laterN_False holds without BIPersistentlyExist; the induction over n uses lc_fupd_elim_later_keep, which does not need it | `checks/W5c2Hand.lean` w5c2_110 |
| `Iris.LaterCreditsPlain.contradiction` | 8 | `inst : Iris.BI.BILoeb PROP` | yes | derivable by instance resolution from the other binders | `checks/InstDerivHand.lean` HypCheckProof.Iris.LaterCreditsPlain.contradiction.h8 |

## Iris.BI.Lib.Fixpoint

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.least_fixpoint_persistent_affine` | 6 | `inst : ∀ (Φ : A → PROP) [∀ (x : A), Iris.BI.Affine (Φ x)] (x : A), Iris.BI.A…` |  | lfp ∧ <pers> lfp is persistent and F-closed (F preserves persistence, is monotone), so lfp ⊢ <pers> lfp by least_fixpoint_iter; Affine preservation unused | `checks/T1c1Hand.lean` t1c1_2 |
| `Iris.least_fixpoint_persistent_absorbing` | 6 | `Habsorb : ∀ (Φ : A → PROP) [∀ (x : A), Iris.BI.Absorbing (Φ x)] (x : A), Iris.B…` |  | same proof as least_fixpoint_persistent_affine idx 6 (helper lfp_pers); Absorbing preservation unused | `checks/T1c1Hand.lean` t1c1_3 |
| `Iris.least_fixpoint_strong_mono` | 6 | `inst : Iris.BIMonoPred G` |  | the premise turns every G-prefixpoint into an F-prefixpoint | `checks/W5c3Hand.lean` W5c3.w5c3_13 |
| `Iris.least_fixpoint_ind_wf` | 7 | `IN : Iris.OFE.NonExpansive Φ` |  | the inner least fixpoint L is non-expansive for any F, F L ⊢ L follows from the premise, so lfp F ⊢ F (lfp F) ⊢ F L ⊢ Φ | `checks/W5c3Hand.lean` W5c3.w5c3_90 |
| `Iris.greatest_fixpoint_strong_mono` | 6 | `inst : Iris.BIMonoPred F` |  | the premise turns every F-postfixpoint into a G-postfixpoint | `checks/W5c3Hand.lean` W5c3.w5c3_14 |
| `Iris.greatest_fixpoint_paco` | 7 | `IN : Iris.OFE.NonExpansive Φ` |  | the inner greatest fixpoint U is non-expansive for any F, U ⊢ F U follows from the premise, so Φ ⊢ F U ⊢ F (gfp F) ⊢ gfp F | `checks/W5c3Hand.lean` W5c3.w5c3_91 |
| `Iris.greatest_fixpoint_coind` | 8 | `_HF : Iris.OFE.NonExpansive F` |  | unused in the library's own proof (directly or transitively); stored proof `drop_unused%` | `checks/UnusedHand.lean` HypCheckProof.Iris.greatest_fixpoint_coind.h8 |

## Iris.BI.Lib.Fractional

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.fractional_merge` | 9 | `inst : Iris.Fractional Φ` |  | Fractional Φ is a field of the kept AsFractional instance hP1 | `checks/W5c3Hand.lean` W5c3.w5c3_52 |

## Iris.BI.Lib.Relations

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.bi_rtc_strong_ind_left` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | Φ ∧ biRtc R · x₂ is non-expansive and closed under the step, so plain induction applies; no non-expansiveness of R needed | `checks/W5c4Hand.lean` w5c4_24 |
| `Iris.bi_rtc_strong_ind_left` | 8 | `inst : Iris.OFE.NonExpansive Φ` |  | given NonExpansive₂ R, biRtc R · x₂ entails ∃ k, k-fold unrolling of the step, a non-expansive predicate closed under the step; each unrolling entails Φ by induction on k using the premise | `checks/W5c4Hand.lean` w5c4_57 |
| `Iris.bi_rtc_refl` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | biRtc R x x is introduced by the left disjunct of the fixpoint; only closure of the fixpoint under its step is used, which needs no non-expansiveness of R | `checks/W5c4Hand.lean` w5c4_19 |
| `Iris.bi_rtc_left` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | introduction rule of the least fixpoint, proved by unfolding its definition; no non-expansiveness of R needed | `checks/W5c4Hand.lean` w5c4_20 |
| `Iris.bi_rtc_once` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | from the non-expansiveness-free refl and left rules | `checks/W5c4Hand.lean` w5c4_21 |
| `Iris.bi_rtc_trans` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | induction on the first closure with a predicate non-expansive by bi_rtc_ne, which has no hypothesis; step by the hypothesis-free left rule | `checks/W5c4Hand.lean` w5c4_22 |
| `Iris.bi_rtc_right` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | from the hypothesis-free trans and once rules | `checks/W5c4Hand.lean` w5c4_23 |
| `Iris.bi_rtc_persistent` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | the library induction goes through with the hypothesis-free refl and left rules | `checks/W5c4Hand.lean` w5c4_26 |
| `Iris.bi_tc_strong_ind_left` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | Φ ∧ biTc R · x₂ is non-expansive in the first argument without hypotheses and closed under the step | `checks/W5c4Hand.lean` w5c4_27 |
| `Iris.bi_tc_strong_ind_left` | 8 | `hΦ : Iris.OFE.NonExpansive Φ` |  | given NonExpansive₂ R, biTc R · x₂ entails ∃ k, k-fold unrolling of the step, a non-expansive predicate closed under the step; each unrolling entails Φ by induction on k using the premise, so Φ need not be non-expansive | `checks/W5c4Hand.lean` w5c4_56 |
| `Iris.bi_tc_left` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | introduction rule of the least fixpoint, proved by unfolding its definition | `checks/W5c4Hand.lean` w5c4_28 |
| `Iris.bi_tc_once` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | introduction rule of the least fixpoint, proved by unfolding its definition | `checks/W5c4Hand.lean` w5c4_29 |
| `Iris.bi_tc_trans` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | induction on the first closure; biTc R · z is non-expansive in its first argument for every R | `checks/W5c4Hand.lean` w5c4_30 |
| `Iris.bi_tc_right` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | from the hypothesis-free trans and once rules | `checks/W5c4Hand.lean` w5c4_31 |
| `Iris.bi_tc_rtc_left` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | induction on biRtc; rewriting along x ≡ y only needs non-expansiveness of biTc R · z in its first argument, which holds for every R | `checks/W5c4Hand.lean` w5c4_32 |
| `Iris.bi_tc_rtc` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | induction on biTc with the hypothesis-free once and left rules of biRtc | `checks/W5c4Hand.lean` w5c4_33 |
| `Iris.bi_tc_absorbing` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | induction with True -∗ biTc R · y, non-expansive for every R; steps by the hypothesis-free once and left rules | `checks/W5c4Hand.lean` w5c4_35 |
| `Iris.bi_tc_persistent` | 5 | `inst : Iris.OFE.NonExpansive₂ R` |  | the library induction goes through with the hypothesis-free once and left rules | `checks/W5c4Hand.lean` w5c4_36 |
| `Iris.bi_rtc_timeless` | 7 | `inst : Iris.OFE.NonExpansive₂ R` | yes | A is a discrete OFE ([OFE.Discrete A]), so every R : A → A → PROP is non-expansive; NonExpansive₂ R is derivable | `checks/Probe3Hand.lean` p3_15 |
| `Iris.bi_tc_timeless` | 3 | `inst : Iris.BI.Timeless iprop(emp)` |  | given NonExpansive₂ R, biTc R x y = ∃ k, k-fold unrolling built from R by ∨, ∃, ∗ and False only, all timeless; emp does not occur | `checks/W5c4Hand.lean` w5c4_58 |
| `Iris.bi_tc_timeless` | 5 | `inst : Iris.OFE.Discrete A` |  | given NonExpansive₂ R, biTc R x y = ∃ k, k-fold unrolling built from timeless R by ∨, ∃, ∗ and False; no internal equality occurs, so discreteness of A is not needed | `checks/W5c4Hand.lean` w5c4_59 |
| `Iris.bi_tc_timeless` | 7 | `inst : Iris.OFE.NonExpansive₂ R` | yes | derivable: OFE.Discrete A with Leibniz equality makes every R non-expansive | `checks/W5c4Hand.lean` w5c4_45 |

## Iris.BI.MonPred

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.BI.MonPred.monPred_at_hom` | 8 | `inst : Iris.Algebra.MonoidOps op₂ u₂` | yes | derivable: by hop every op₂ a b is (op₁ ⎡a⎤ ⎡b⎤) at i, so op₂ inherits the monoid laws of op₁ (unit by hunit) | `checks/W5c5Hand.lean` w5c5_71 |
| `Iris.BI.MonPred.monPred_at_hom` | 11 | `hunit : u₁.monPred_at i = u₂` | yes | derivable: u₁ i = op₂ u₂ (u₁ i) = (op₁ ⎡u₂⎤ u₁) i = ⎡u₂⎤ i = u₂ by hop and the unit laws | `checks/W5c5Hand.lean` w5c5_73 |

## Iris.BI.Plainly

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.BI.plainly_sep_weak_homomorphism` | 2 | `inst : Iris.BI.BIPositive PROP` | yes | derivable by instance resolution from the other binders | `checks/InstDerivHand.lean` HypCheckProof.Iris.BI.plainly_sep_weak_homomorphism.h2 |
| `Iris.BI.plainly_sep_weak_homomorphism` | 3 | `inst : Iris.BI.BIAffine PROP` |  | unused in the library's own proof (directly or transitively); stored proof `drop_unused%` | `checks/UnusedHand.lean` HypCheckProof.Iris.BI.plainly_sep_weak_homomorphism.h3 |
| `Iris.BI.plainly_sep_entails_homomorphism` | 2 | `inst : Iris.BI.BIAffine PROP` |  | map_unit is emp ⊢ ■ emp, which is plainly_emp_intro and needs no BIAffine; rest from plainly_sep_entails_weak_homomorphism | `checks/Probe3Hand.lean` p3_19 |

## Iris.BI.Sbi

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.only0_intuitionistically` | 2 | `inst : Iris.BI.BILoeb PROP` | yes | derivable by instance resolution from the other binders | `checks/InstDerivHand.lean` HypCheckProof.Iris.only0_intuitionistically.h2 |

## Iris.BI.Updates

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.bupd_plain_forall` | 3 | `inst : Iris.BIBUpdateSbi PROP` |  | plain absorbing Phi x is equivalent to the SiProp proposition emp-valid Phi x; SiProp is a well-ordered chain, so for nonempty A some Phi a0 entails all Phi x; empty A: BIUpdate.intro | `checks/T1c0Hand.lean` t1c0_31 |
| `Iris.step_fupd_mask_frame_right` | 8 | `hEi : Ei ## Ef` |  | frame with Ef minus Ei (disjoint from Eo and Ei) by the library lemma, then step_fupd_mask_mono (inner mask shrinks from Ei u Ef to Ei u (Ef minus Ei), outer grows) | `checks/W6c1Hand.lean` w6c1_54 |
| `Iris.fupd_siPure_forall_2` | 3 | `inst : Iris.BIFUpdateSbi PROP` |  | SiProp is a well-ordered chain: the least member Φi a0 of the family entails all, so the update for a0 suffices; empty family: fupd_intro | `checks/T1c0Hand.lean` t1c0_25 |
| `Iris.fupd_plainly_forall_2` | 3 | `inst : Iris.BIFUpdateSbi PROP` |  | fupd_siPure_forall_2 without BIFUpdateSbi (least member of a SiProp family), then plainly elimination by BIAffine | `checks/T1c0Hand.lean` t1c0_26 |
| `Iris.fupd_plain_forall_2` | 3 | `inst : Iris.BIFUpdateSbi PROP` |  | Plain to plainly, then as for fupd_plainly_forall_2 via the least member of a SiProp family | `checks/T1c0Hand.lean` t1c0_27 |
| `Iris.fupd_plain_forall` | 3 | `inst : Iris.BIFUpdateSbi PROP` |  | nonempty alpha: some Phi a0 entails all Phi a (least emp-validity, Plain, BIAffine); empty alpha: fupd_mask_intro_discard with E2 below E1 | `checks/T1c0Hand.lean` t1c0_28 |
| `Iris.fupd_plain_forall'` | 3 | `inst : Iris.BIFUpdateSbi PROP` |  | as fupd_plain_forall idx 3 with E1 = E2 | `checks/T1c0Hand.lean` t1c0_29 |
| `Iris.step_fupd_plain_forall` | 3 | `inst : Iris.BIFUpdateSbi PROP` |  | nonempty alpha: some Phi a0 entails all Phi a, then step_fupd_mono; empty alpha: step_fupd_intro with Ei below Eo | `checks/T1c0Hand.lean` t1c0_30 |

## Iris.Examples.Proofs

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.Examples.proof_example_1` | 3 | `inst : Iris.BI.BIPersistentlyExist PROP` |  | holds in every BI: the boxed wand is used by intuitionistically_elim, the existential is destructed in the spatial context | `checks/W6c1Hand.lean` w6c1_18 |

## Iris.HeapLang.Completeness

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.HeapLang.wp_base_pure` | 6 | `hpe : Iris.ProgramLogic.Language.PureExec φ 1 e₁ e₂` | yes | hbase (a base step in every state, no effect) forces e1 to be a pure redex: PureExec True 1 e1 e2 by case analysis (pe_of_base), then the library lemma | `checks/T1c3Hand.lean` T1c3.t1c3_16 |
| `Iris.HeapLang.wp_base_pure` | 7 | `hφ : φ` |  | same as idx 6: PureExec True 1 e1 e2 from hbase, so hphi is not needed | `checks/T1c3Hand.lean` T1c3.t1c3_17 |
| `Iris.HeapLang.wp_base_pure` | 10 | `hbase : ∀ (σ' : Iris.HeapLang.State), Iris.HeapLang.BaseStep e₁ σ' [] e₂ σ' []` |  | hbase is only used for the PrimSteps trajectory, which also follows from PureExec (pure step at every state); library proof re-run | `checks/T1c3Hand.lean` T1c3.t1c3_18 |
| `Iris.HeapLang.wp_base_atomic` | 10 | `hatom : Iris.ProgramLogic.Language.Atomic Iris.ProgramLogic.Language.Atomicit…` | yes | hatom follows from hbase sigma hcell by base_step_to_val_atomic | `checks/T1c3Hand.lean` T1c3.t1c3_11 |
| `Iris.HeapLang.wp_base_atomic` | 13 | `hdet : ∀ {σ'' : Iris.HeapLang.State} {obs : List Iris.HeapLang.Observation} …` | yes | hdet follows from hbase as for nochange idx 12 (alloc at a fresh cell cannot equal the one-cell update of an allocated cell) | `checks/T1c3Hand.lean` T1c3.t1c3_20 |
| `Iris.HeapLang.wp_base_atomic_nochange` | 9 | `hatom : Iris.ProgramLogic.Language.Atomic Iris.ProgramLogic.Language.Atomicit…` | yes | hatom follows from hbase sigma hcell by base_step_to_val_atomic | `checks/T1c3Hand.lean` T1c3.t1c3_10 |
| `Iris.HeapLang.wp_base_atomic_nochange` | 12 | `hdet : ∀ {σ'' : Iris.HeapLang.State} {obs : List Iris.HeapLang.Observation} …` | yes | hdet follows from hbase: HeapLang base steps without effect are deterministic (alloc/newProph change the state, resolve observes, fork forks; det2) | `checks/T1c3Hand.lean` T1c3.t1c3_19 |

## Iris.HeapLang.Instances

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.HeapLang.mk_pure_prim_step` | 3 | `hpure : ∀ {σ1 : Iris.HeapLang.State} {κs : List Iris.HeapLang.Observation} {e…` | yes | removable: every HeapLang base step that exists in all states without changing them is deterministic (case analysis on both steps; impure rules contradict hstep at the empty state) | `checks/W6c2Hand.lean` w6c2_55 |
| `Iris.HeapLang.mk_pure_prim_step` | 4 | `hsub : Iris.ProgramLogic.EctxLanguage.SubredexesAreValues e1` | yes | removable: SubredexesAreValues e1 follows from hstep default via base_ctx_step_val and subredexes_are_values | `checks/W6c2Hand.lean` w6c2_32 |

## Iris.HeapLang.ProphErasure

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `(private) Iris.HeapLang.ProphErasure.0.Iris.HeapLang.resolve_fst_primStepMatched` | 10 | `bstep : Iris.HeapLang.BaseStep e1' (Iris.HeapLang.eraseState σ1) κ e2' σ2 efs` |  | IHapp at K' := Ks, e0 := fst((r0, r1), r2) (its erasure is heq_e's left side; not stuck because Resolve r0 r1 r2 is not) gives a matched step of fst((r0, r1), r2); every such step carries over to Resolve r0 r1 r2 under … | `checks/T3c0Hand.lean` T3c0.t3c0_0 |
| `(private) Iris.HeapLang.ProphErasure.0.Iris.HeapLang.resolve_fst_primStepMatched` | 13 | `IHapp : ∀ {K' : List Iris.HeapLang.ECtxItem} {e0 : Iris.HeapLang.Exp}, K'.len…` |  | IHapp unneeded: the erased base step under fill (Ks ++ [fst]) is a prim step of the erased resolve, so the public theorem erased_primStep_primStep (with hns) gives the conclusion directly | `checks/W6c3Hand.lean` W6c3.w6c3_120 |

## Iris.Instances.Data.State

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.Instances.Data.disjoint_assoc` | 5 | `a : a \|\| b` |  | a ∪ b is unknown only where a and b both are | `checks/W6c4Hand.lean` w6c4_7 |

## Iris.Instances.IProp.Instance

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.validN_of_iSingleton_op_free` | 9 | `Hfree : Iris.IsFree (mf (Iris.ElemG.τ GF F)).car γ` |  | validity of a product implies validity of the left factor | `checks/W6c4Hand.lean` w6c4_37 |
| `Iris.validN_mf_at_E_τ_of_iSingleton_op_free` | 9 | `Hfree : Iris.IsFree (mf (Iris.ElemG.τ GF F)).car γ` |  | validity of a product implies validity of the right factor | `checks/W6c4Hand.lean` w6c4_39 |
| `Iris.validN_mf_at_ne_of_iSingleton_op` | 10 | `h : τ' ≠ Iris.ElemG.τ GF F` |  | validity of a product implies validity of the right factor | `checks/W6c4Hand.lean` w6c4_41 |
| `Iris.iSingleton_op_validN_free` | 9 | `a : Iris.IsFree (mf (Iris.ElemG.τ GF F)).car γ` |  | both factors of a valid product are valid | `checks/W6c4Hand.lean` w6c4_43 |
| `Iris.IResUR.valid_exists_fresh` | 6 | `_Hv : ✓{n} mf` |  | unused in the library's own proof (directly or transitively); stored proof `drop_unused%` | `checks/UnusedHand.lean` HypCheckProof.Iris.IResUR.valid_exists_fresh.h6 |

## Iris.Instances.Lib.Boxes

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.slice_insert_full` | 12 | `HE : ↑N ⊆ E` |  | re-proof of slice_insert_empty allocating the slice already full (flag true, ▷ Q stored by inv_alloc, which works at any mask); slice_fill and its mask condition are not needed | `checks/W7c0Hand.lean` bx_ins_full |

## Iris.Instances.Lib.FUpdFromViewShift

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.fupd_vs_trans` | 3 | `inst : Iris.IncOrd M` |  | the lemma follows from Persistent vs, trans, exists and persistent_intro_r in any BI (model proposed by an external model, checked here): persistent_intro_r gives emp ⊢ vs(A ∗ vs(A,… | `checks/T3c6Hand.lean` T3c6.t3c6_0 |
| `Iris.fupd_vs_trans` | 12 | `vs_impl : ∀ (E : CoPset) (P Q : Iris.UPred M), □ (P → Q) ⊢ vs E E P Q` |  | the library proof ends with vs_trans + vs_impl to close vs E2 E3 R P from the same hypothesis; iexact suffices | `checks/Probe3Hand.lean` p3_43 |

## Iris.ProgramLogic.AbstractWeakestPre

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.inv_open_maybe_ectxlang` | 16 | `Hred : ∃ σ, Iris.ProgramLogic.PrimStep.Reducible (e, σ)` |  | without reducibility of e, the left disjunct is impossible since e = fill K e' with e' base-reducible; the right disjunct closes by fupd_wp | `checks/W7c1Hand.lean` W7c1.w7c1_35 |
| `Iris.inv_open_maybe_ectxlang_inv` | 17 | `Hred : ∃ σ, Iris.ProgramLogic.PrimStep.Reducible (e, σ)` |  | the library proof goes through with the hypothesis-free version of inv_open_maybe_ectxlang above | `checks/W7c1Hand.lean` W7c1.w7c1_38 |
| `Iris.wp_inv_open_maybe_of_not_val` | 12 | `Hnv : Iris.ProgramLogic.toVal e = none` |  | the library's `Iris.wp_inv_open_maybe` states the same without the hypothesis | `checks/W7c1Hand.lean` W7c1.w7c1_39 |

## Iris.ProgramLogic.EctxLifting

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Rocq.wp_lift_pure_det_base_step_no_fork` | 16 | `h : Iris.ProgramLogic.toVal e₁ = none` |  | toVal e₁ = none follows from Hbred at the default state by val_stuck | `checks/W7c1Hand.lean` W7c1.w7c1_137 |
| `(private) Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork` | 16 | `h : Iris.ProgramLogic.toVal e₁ = none` |  | toVal e₁ = none follows from Hbred at the default state by val_stuck | `checks/W7c1Hand.lean` W7c1.w7c1_140 |
| `Rocq.wp_lift_pure_det_base_step_no_fork'` | 15 | `h : Iris.ProgramLogic.toVal e₁ = none` |  | toVal e₁ = none follows from Hbred at the default state by val_stuck | `checks/W7c1Hand.lean` W7c1.w7c1_143 |
| `(private) Iris.ProgramLogic.EctxLifting.0.Iris.ProgramLogic.wp_lift_pure_det_base_step_no_fork'` | 15 | `h : Iris.ProgramLogic.toVal e₁ = none` |  | toVal e₁ = none follows from Hbred at the default state by val_stuck | `checks/W7c1Hand.lean` W7c1.w7c1_146 |

## Iris.ProgramLogic.TotalEctxLifting

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.ProgramLogic.twp.lift_pure_det_base_step_no_fork` | 15 | `_h : Iris.ProgramLogic.toVal e₁ = none` |  | unused in the library's own proof (directly or transitively); stored proof `drop_unused%` | `checks/UnusedHand.lean` HypCheckProof.Iris.ProgramLogic.twp.lift_pure_det_base_step_no_fork.h15 |

## Iris.ProgramLogic.TotalWeakestPre

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.twp.induction` | 10 | `HΨ : Iris.OFE.NonExpansive fun x => Ψ x.fst x.snd.fst x.snd.snd` |  | removable: apply twp.induction to the NE interior Ψ' x := ∀ y, x ≡ y -∗ Ψ y; Ψ' ⊢ Ψ and its premise follows by internal-eq rewriting in pre' plus pre_mono | `checks/T2c3Hand.lean` t2c3_1 |

## Iris.ProofMode.Instances

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.ProofMode.intoForall_persistently` | 3 | `inst : Iris.BI.BIPersistentlyForall PROP` |  | unused in the library's own proof (directly or transitively); stored proof `drop_unused%` | `checks/UnusedHand.lean` HypCheckProof.Iris.ProofMode.intoForall_persistently.h3 |
| `Iris.ProofMode.fromAffinely_affine` | 3 | `inst : Iris.BI.Affine P` |  | unused in the library's own proof (directly or transitively); stored proof `drop_unused%` | `checks/UnusedHand.lean` HypCheckProof.Iris.ProofMode.fromAffinely_affine.h3 |
| `Iris.ProofMode.intoAbsorbingly_absorbing` | 3 | `inst : Iris.BI.Absorbing P` |  | P ⊢ <absorb> P holds in every BI (absorbingly_intro), so the instance needs no Absorbing P | `checks/W8c0Hand.lean` w8c0_14 |

## Iris.ProofMode.InstancesEmbedding

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.ProofMode.intoEmbed_affinely` | 7 | `inst : Iris.BI.BiEmbedBUpd PROP1 PROP2` |  | unused in the library's own proof (directly or transitively); stored proof `drop_unused%` | `checks/UnusedHand.lean` HypCheckProof.Iris.ProofMode.intoEmbed_affinely.h7 |

## Iris.ProofMode.InstancesFrame

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.ProofMode.frame_eq_embed` | 5 | `inst : Iris.BI.BiEmbedSbi P1 P2` |  | a ≡ b ⊢ ⎡a ≡ b⎤ holds for every embedding: rewrite with z ↦ ⎡a ≡ z⎤ and ⎡a ≡ a⎤ ⊣ ⎡True⎤ = True | `checks/W8c1Hand.lean` w8c1_35 |

## Iris.ProofMode.InstancesUpdates

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.ProofMode.fromForall_fupd` | 3 | `inst : Iris.BIFUpdateSbi PROP` |  | plain props are siPure of initial segments of Nat, so a nonempty family of plain props has a least member a0; the update of the forall follows from the update of Phi a0 by monotonicity (no BIFUpdateSbi needed); empty al… | `checks/W8c3Hand.lean` W8c3.w8c3_r1 |
| `Iris.ProofMode.fromForall_stepFupd` | 3 | `inst : Iris.BIFUpdateSbi PROP` |  | same least-member argument with step_fupd_mono (no BIFUpdateSbi needed); empty alpha by later_intro and step_fupd_intro | `checks/W8c3Hand.lean` W8c3.w8c3_r2 |

## Iris.Std.FromMathlib

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `FromMathlib.Pairwise.forall` | 4 | `hl : List.Pairwise (fun x1 x2 => x1 ≠ x2) l` |  | HypCheck proved the theorem without it by `simp_all` | ``  |
| `FromMathlib.Pairwise.forall` | 6 | `a : a ∈ l` |  | HypCheck proved the theorem without it by `simp_all` | ``  |
| `FromMathlib.Pairwise.forall` | 8 | `a : b ∈ l` |  | HypCheck proved the theorem without it by `simp_all` | ``  |

## Iris.Std.GenSetsInstances

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.Std.insert_eq_singleton_union_extTreeSet` | 3 | `inst : Std.LawfulEqCmp cmp` |  | removable (set insert is insertIfNew and the union of a one-element set into a nonempty set is insertIfNew; true for any TransCmp) | `checks/W9c2Hand.lean` w9c2_1 |

## Iris.Std.HeapInstances

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `(private) Iris.Std.HeapInstances.0.Std.TreeMap.get?_foldl_alter_impl_sigma` | 4 | `inst : Std.LawfulEqOrd K` |  | removable (transitivity suffices where the proof used LawfulEqOrd) | `checks/W9c2Hand.lean` w9c2_3 |
| `(private) Iris.Std.HeapInstances.0.Std.TreeMap.getElem?_foldl_alter` | 4 | `inst : Std.LawfulEqOrd K` |  | removable (transitivity suffices where the proof used LawfulEqOrd) | `checks/W9c2Hand.lean` w9c2_7 |
| `(private) Iris.Std.HeapInstances.0.Std.TreeMap.getElem?_mergeWith_eq_foldl` | 3 | `inst : Std.TransOrd K` |  | removable (both sides are the same tree: mergeWith folds alter over the entries of t₂; no order laws needed) | `checks/W9c2Hand.lean` w9c2_8 |
| `(private) Iris.Std.HeapInstances.0.Std.TreeMap.getElem?_mergeWith_eq_foldl` | 4 | `inst : Std.LawfulEqOrd K` |  | removable (both sides are the same tree: mergeWith folds alter over the entries of t₂; no order laws needed) | `checks/W9c2Hand.lean` w9c2_9 |

## Iris.Std.PartialMap

| Theorem | # | Hypothesis | Derivable | Why removable | Proof |
|---|---|---|---|---|---|
| `Iris.Std.LawfulPartialMap.disjoint_insert_left_iff` | 8 | `hi : Iris.Std.get? m₁ i = none` |  | removable (at key i the left side already forces get? m₂ i = none) | `checks/W9c2Hand.lean` w9c2_57 |
| `Iris.Std.LawfulPartialMap.zipWith_comm` | 9 | `a : ∀ (v : V) (v' : V'), f v v' = f v v'` |  | unused in the library's own proof (directly or transitively); stored proof `drop_unused%` | `checks/UnusedHand.lean` HypCheckProof.Iris.Std.LawfulPartialMap.zipWith_comm.h9 |
| `Iris.Std.LawfulPartialMap.get?_ofList_none` | 7 | `Hdup : Iris.Std.NoDupKeys L` |  | removable (induction on L; NoDupKeys unused) | `checks/W9c2Hand.lean` w9c2_78 |
| `Iris.Std.LawfulFiniteMap.toList_filterMap` | 6 | `HI : Function.Injective f` |  | removable (the right side has distinct keys since toList m has) | `checks/W9c2Hand.lean` w9c2_91 |

## Joint removal

75 pairs of individually removable hypotheses checked (`checks/J*Hand.lean`, `scripts/check_pairs.py`): 61 jointly removable, 14 not.

| Theorem | Pair | Verdict | Reason |
|---|---|---|---|
| `FromMathlib.Pairwise.forall` | 4, 6 | jointly | hR alone turns the goal R a b into the premise a ≠ b; the list facts are unused |
| `FromMathlib.Pairwise.forall` | 4, 8 | jointly | hR alone turns the goal R a b into the premise a ≠ b; the list facts are unused |
| `FromMathlib.Pairwise.forall` | 6, 8 | jointly | hR alone turns the goal R a b into the premise a ≠ b; the list facts are unused |
| `Iris.Agree.agree_map_ext` | 6, 7 | not jointly | TN, f = g = bad: H holds but bad is not non-expansive (1, 2 are 0-close, images 0, 1 are not) |
| `Iris.Algebra.BigOpM.bigOpM_gen_proper_2` | 15, 16 | not jointly | R = empty relation (vacuously a congruence), m1 = m2 = ∅: R unit unit fails |
| `Iris.BI.MonPred.monPred_at_hom` | 8, 11 | not jointly | UIdx, SiProp, op₁ = op₂ = ∗, u₁ = emp, u₂ = False: hop holds by rfl but emp at 0 is not False |
| `Iris.BI.only0_intuitionistically_mpr` | 2, 3 | jointly | only0_persistently_mpr plus the mpr half of only0_affinely; neither BILoeb nor Timeless emp is used |
| `Iris.BI.plainly_sep_weak_homomorphism` | 2, 3 | not jointly | non-positive Sbi UPred X2 (xor), x = y = ownM i: ■ (x ∗ y) holds at the unit but ■ x ∗ ■ y does not, so map_op fails |
| `Iris.HeapLang.mk_pure_prim_step` | 3, 4 | jointly | determinism follows by case analysis on base steps (impure rules contradict hstep at the empty state) and subredexes are values by base_ctx_step_val, both from hstep |
| `Iris.HeapLang.wp_base_atomic` | 10, 13 | jointly | hbase gives atomicity (a base step to a value) and determinism (det2: a base step that only rewrites one allocated cell is deterministic) |
| `Iris.HeapLang.wp_base_atomic_nochange` | 9, 12 | jointly | hbase gives atomicity (a base step to a value) and determinism (det2: a base step that leaves the state alone is deterministic) |
| `Iris.HeapLang.wp_base_pure` | 6, 7 | jointly | hbase alone: a state-free base step in every state is a PureExec True step, so instantiate φ := True |
| `Iris.HeapLang.wp_base_pure` | 6, 10 | not jointly | e₁ = e₂ = var "a" (stuck), φ = True: the WP of a stuck expression would be adequate |
| `Iris.HeapLang.wp_base_pure` | 7, 10 | not jointly | e₁ = e₂ = var "a" (stuck), φ = False makes PureExec vacuous: the WP of a stuck expression would be adequate |
| `Iris.Inv.A_alloc` | 2, 6 | jointly | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused |
| `Iris.Inv.A_alloc` | 2, 7 | jointly | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused |
| `Iris.Inv.A_alloc` | 2, 10 | jointly | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused |
| `Iris.Inv.A_alloc` | 6, 7 | jointly | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused |
| `Iris.Inv.A_alloc` | 6, 10 | jointly | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused |
| `Iris.Inv.A_alloc` | 7, 10 | jointly | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused |
| `Iris.Inv.contradiction` | 2, 7 | jointly | run the non-affine paradox t2c1_9 with fupd' E P := fupd E (P ∗ True): fupd'_intro comes from sts_alloc, framing and mask_mono (the start token is absorbed into True), every other hypothesis carries over, and consistenc… |
| `Iris.Inv.contradiction` | 2, 11 | jointly | mask_mono from inv_alloc True and inv_fupd without affinity (as in J2c0 j2_7), then the non-affine paradox t2c1_9 |
| `Iris.Inv.contradiction` | 7, 11 | jointly | mask_mono from inv_alloc True and inv_fupd (no fupd_intro used); then fupd_intro from sts_alloc, framing, mono and affinity at M0, mask_mono for M1 |
| `Iris.Inv.contradiction'` | 2, 7 | jointly | run the non-affine paradox t2c1_8 with fupd' E P := fupd E (P ∗ True): fupd'_intro comes from sts_alloc, framing and mask_mono (the start token is absorbed into True), every other hypothesis carries over, and consistenc… |
| `Iris.Inv.contradiction'` | 2, 11 | jointly | mask_mono from inv_alloc True and inv_fupd without affinity (as in J2c0 j2_8), then the non-affine paradox t2c1_8 |
| `Iris.Inv.contradiction'` | 7, 11 | jointly | mask_mono from inv_alloc True and inv_fupd (no fupd_intro used); then fupd_intro from sts_alloc, framing, mono and affinity at M0, mask_mono for M1 |
| `Iris.Inv.inv_fupd'` | 2, 8 | jointly | inv_fupd with Q the wand and wand elimination, then fupd_fupd; neither affinity nor persistence of inv used |
| `Iris.Inv.saved_alloc` | 2, 6 | jointly | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused |
| `Iris.Inv.saved_alloc` | 2, 7 | jointly | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused |
| `Iris.Inv.saved_alloc` | 2, 10 | jointly | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused |
| `Iris.Inv.saved_alloc` | 6, 7 | jointly | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused |
| `Iris.Inv.saved_alloc` | 6, 10 | jointly | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused |
| `Iris.Inv.saved_alloc` | 7, 10 | jointly | sts_alloc, mask_mono, inv_alloc of the left disjunct, mono, fupd_fupd; affinity, persistence of inv, fupd_intro and fupd_frame_left all unused |
| `Iris.LaterCreditsPlain.contradiction` | 2, 8 | jointly | BILoeb comes from Sbi by instance resolution; laterN_False holds without BIPersistentlyExist (weak Löb), then lc_fupd_elim_later_keep induction |
| `Iris.LaterCreditsPlain.laterN_False` | 2, 3 | jointly | BILoeb comes from Sbi by instance resolution; weak Löb on the existential needs no BIPersistentlyExist |
| `Iris.LaterCreditsPlain.lc_fupd_elim_later_keep` | 8, 9 | jointly | keepG uses neither instance: lc ⊢ fupd False from lc_fupd_elim_later and fupd_keep_si_pure' via Löb, then frame, for every P |
| `Iris.OFE.Iso.ext` | 6, 7 | not jointly | DB, the identity iso and the negation iso are different |
| `Iris.SavedProp.contradiction` | 2, 3 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.contradiction` | 2, 7 | jointly | with A' i := ∃ Q, ¬Q ∧ saved i Q, agreement alone gives ∃ i, saved i (A' i) ⊣⊢ False, so alloc yields ⊢ bupd False against consistency; neither persistence of saved nor instPersExist is used |
| `Iris.SavedProp.contradiction` | 2, 8 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.contradiction` | 2, 9 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.contradiction` | 2, 10 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.contradiction` | 2, 11 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.contradiction` | 3, 7 | jointly | with A' i := ∃ Q, ¬Q ∧ saved i Q, agreement alone gives ∃ i, saved i (A' i) ⊣⊢ False, so alloc yields ⊢ bupd False against consistency; neither persistence of saved nor instAffine is used |
| `Iris.SavedProp.contradiction` | 3, 8 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.contradiction` | 3, 9 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.contradiction` | 3, 10 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.contradiction` | 3, 11 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.contradiction` | 7, 8 | jointly | with A' i := ∃ Q, ¬Q ∧ saved i Q, agreement alone gives ∃ i, saved i (A' i) ⊣⊢ False, so alloc yields ⊢ bupd False against consistency; neither persistence of saved nor bupd_intro is used |
| `Iris.SavedProp.contradiction` | 7, 9 | jointly | with A' i := ∃ Q, ¬Q ∧ saved i Q, agreement alone gives ∃ i, saved i (A' i) ⊣⊢ False, so alloc yields ⊢ bupd False against consistency; neither persistence of saved nor bupd_mono is used |
| `Iris.SavedProp.contradiction` | 7, 10 | jointly | with A' i := ∃ Q, ¬Q ∧ saved i Q, agreement alone gives ∃ i, saved i (A' i) ⊣⊢ False, so alloc yields ⊢ bupd False against consistency; neither persistence of saved nor bupd_trans is used |
| `Iris.SavedProp.contradiction` | 7, 11 | jointly | with A' i := ∃ Q, ¬Q ∧ saved i Q, agreement alone gives ∃ i, saved i (A' i) ⊣⊢ False, so alloc yields ⊢ bupd False against consistency; neither persistence of saved nor bupd_frame_right is used |
| `Iris.SavedProp.contradiction` | 8, 9 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.contradiction` | 8, 10 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.contradiction` | 8, 11 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.contradiction` | 9, 10 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.contradiction` | 9, 11 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.contradiction` | 10, 11 | jointly | saved_NA and saved_A hold from agree and persistence of saved alone, so the allocated proposition is False; alloc plus consistency; no bupd law, affinity or BIPersistentlyExist used |
| `Iris.SavedProp.saved_A` | 2, 3 | jointly | agree makes saved affine, so with persistence saved i (A i) is intuitionistic; saved_NA without BIAffine/BIPersistentlyExist |
| `Iris.SavedProp.saved_NA` | 2, 3 | jointly | persistence of saved plus affinity from agree; only ∧-reasoning |
| `Iris.SavedProp.saved_NA` | 2, 6 | jointly | with BIAffine both halves of the boxed separating conjunction are available; only ∧-reasoning |
| `Iris.SavedProp.saved_NA` | 3, 6 | jointly | agree makes saved affine; □(¬P ∗ saved i P) gives <pers> ¬P and <pers> A, with saved i (A i) also <pers> (P ↔ A) (stray ¬P absorbed by <pers>); all meet under <pers>: <pers> False |
| `Iris.bi_rtc_strong_ind_left` | 5, 8 | not jointly | SiProp, TN, R x _ = ⌜x = 1⌝, x₂ = 0, Φ x = ⌜x = 1 ∨ x = 0⌝ (closed, not NE): biRtc R 2 0 holds at step 0 but Φ 2 does not |
| `Iris.bi_tc_strong_ind_left` | 5, 8 | not jointly | SiProp, TN, R x _ = ⌜x = 1⌝, x₂ = 0, Φ x = ⌜x = 1⌝ (closed, not NE): biTc R 2 0 holds at step 0 but Φ 2 does not |
| `Iris.bi_tc_timeless` | 3, 5 | jointly | given NonExpansive₂ R, biTc R x y = ∃ k, k-fold unrolling built from timeless R by ∨, ∃, ∗, False: neither emp nor internal equality occurs |
| `Iris.bi_tc_timeless` | 3, 7 | jointly | Discrete A makes R NonExpansive₂; then biTc R x y is the timeless k-fold unrolling (emp does not occur) |
| `Iris.bi_tc_timeless` | 5, 7 | not jointly | SiProp (emp timeless), TN, R x _ = ⌜x = 1⌝ (timeless, not NE): biTc R 2 0 holds at step 0 but not at step 1 |
| `Iris.fixpointK_proper` | 6, 7 | not jointly | CS, k = 0, f = g = id: the identity is not contractive |
| `Iris.fixpointK_proper` | 6, 8 | not jointly | CS, k = 2, f = g = kf: kf∘kf is constant (contractive) but kf is not non-expansive |
| `Iris.fixpointK_proper` | 7, 8 | not jointly | CS, k = 2, f = g = kf: kf∘kf is constant (contractive) but kf is not non-expansive |
| `Iris.fixpoint_proper` | 5, 6 | not jointly | CS, f = g = id: the identity is not contractive |
| `Iris.fupd_vs_trans` | 3, 12 | jointly | T3c6's proof (witness W := A ∗ vs12(A,Q), key fact from exists + persistent_intro_r under emp) uses neither IncOrd nor vs_impl |
| `View.map_ne` | 14, 15 | jointly | the proof only needs pointwise f1 a =n= f2 a for Agree.map'; neither NonExpansive instance is used |
| `_private.Iris.BI.BigOp.BigSepList.0.Iris.BI.BigSepL2.zip_set` | 5, 6 | jointly | zip and set commute for every index (out of range both sides are unchanged); induction on the lists |
| `_private.Iris.Std.HeapInstances.0.Std.TreeMap.getElem?_mergeWith_eq_foldl` | 3, 4 | jointly | both sides are the same tree: mergeWith folds alter over the entries of t₂; no order laws needed |

## Independent (argued, not certified)

| Theorem | # | Kind | Argument |
|---|---|---|---|
| `Iris.OFE.transpAp_eqv_mp` | 7 | type-identity | independent: ∀ indep, F₁ = F₂ where the independent binders include RF₁ ≍ RF₂ for RF₁ : RFunctorContractive F₁, RF₂ : RFunctorContractive F₂. Refuting needs F₁ ≠ F₂ with RFunctorContractive F₁ = RFunctorContractive F₂ (… |
| `Iris.OFE.transpAp_validN_mp` | 7 | type-identity | independent: ∀ indep, F₁ = F₂ where the independent binders include RF₁ ≍ RF₂ for RF₁ : RFunctorContractive F₁, RF₂ : RFunctorContractive F₂. Refuting needs F₁ ≠ F₂ with RFunctorContractive F₁ = RFunctorContractive F₂ (… |
| `Iris.OFE.transpAp_op_mp` | 6 | type-identity | independent: ∀ indep, F₁ = F₂ where the independent binders include RF₁ ≍ RF₂ for RF₁ : RFunctorContractive F₁, RF₂ : RFunctorContractive F₂. Refuting needs F₁ ≠ F₂ with RFunctorContractive F₁ = RFunctorContractive F₂ (… |
| `Iris.OFE.transpAp_pcore_mp` | 6 | type-identity | independent: ∀ indep, F₁ = F₂ where the independent binders include RF₁ ≍ RF₂ for RF₁ : RFunctorContractive F₁, RF₂ : RFunctorContractive F₂. Refuting needs F₁ ≠ F₂ with RFunctorContractive F₁ = RFunctorContractive F₂ (… |
| `Iris.OFE.validN_transpAp_mp` | 7 | type-identity | independent: ∀ indep, F₁ = F₂ where the independent binders include RF₁ ≍ RF₂ for RF₁ : RFunctorContractive F₁, RF₂ : RFunctorContractive F₂. Refuting needs F₁ ≠ F₂ with RFunctorContractive F₁ = RFunctorContractive F₂ (… |

