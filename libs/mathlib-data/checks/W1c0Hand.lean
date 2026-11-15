module
public import HCHeaderM
import all Mathlib.Data.Analysis.Filter
import all Mathlib.Data.Analysis.Topology
import all Mathlib.Data.BitVec
import all Mathlib.Data.Bool.AllAny
import all Mathlib.Data.Bool.Basic
import all Mathlib.Data.Bool.Count
import all Mathlib.Data.Bool.Set
import all Mathlib.Data.Bundle
import all Mathlib.Data.Char
import all Mathlib.Data.DFinsupp.BigOperators
import all Mathlib.Data.DFinsupp.Defs
import all Mathlib.Data.DFinsupp.Encodable
import all Mathlib.Data.DFinsupp.Ext
import all Mathlib.Data.DFinsupp.FiniteInfinite
import all Mathlib.Data.DFinsupp.Interval
import all Mathlib.Data.DFinsupp.Lex
import all Mathlib.Data.DFinsupp.Module
import all Mathlib.Data.DFinsupp.Multiset
import all Mathlib.Data.DFinsupp.NeLocus
import all Mathlib.Data.DFinsupp.Notation
import all Mathlib.Data.DFinsupp.Order
import all Mathlib.Data.DFinsupp.Sigma
import all Mathlib.Data.DFinsupp.Small
import all Mathlib.Data.DFinsupp.Submonoid
import all Mathlib.Data.DFinsupp.WellFounded
import all Mathlib.Data.DList.Instances
import all Mathlib.Data.Dyadic.Basic
import all Mathlib.Data.ENat.Basic
import all Mathlib.Data.ENat.BigOperators
import all Mathlib.Data.ENat.Defs
import all Mathlib.Data.ENat.Lattice
import all Mathlib.Data.ENat.Monoid
import all Mathlib.Data.ENat.Pow
import all Mathlib.Data.Erased
import all Mathlib.Data.EReal.Basic
import all Mathlib.Data.EReal.BigOperators
import all Mathlib.Data.EReal.DedekindCut
import all Mathlib.Data.EReal.Inv
import all Mathlib.Data.EReal.Operations
import all Mathlib.Data.Fin.Basic
import all Mathlib.Data.Fin.Embedding
import all Mathlib.Data.FinEnum
import all Mathlib.Data.FinEnum.Option
import all Mathlib.Data.Fin.Fin2
import all Mathlib.Data.Fin.FlagRange
import all Mathlib.Data.Fin.Init
import all Mathlib.Data.Finite.Perm
import all Mathlib.Data.Finmap
import all Mathlib.Data.Fin.Parity
import all Mathlib.Data.Fin.Pigeonhole
import all Mathlib.Data.Fin.Rev
import all Mathlib.Data.Finset.Attach
import all Mathlib.Data.Finset.Attr
import all Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.BooleanAlgebra
import all Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.CastCard
import all Mathlib.Data.Finset.Dedup
import all Mathlib.Data.Finset.Defs
import all Mathlib.Data.Finset.DenselyOrdered
import all Mathlib.Data.Finset.Density
import all Mathlib.Data.Finset.Disjoint
import all Mathlib.Data.Finset.Empty
import all Mathlib.Data.Finset.Erase
import all Mathlib.Data.Finset.Filter
import all Mathlib.Data.Finset.Fin
import all Mathlib.Data.Finset.Finsupp
import all Mathlib.Data.Finset.Fold
import all Mathlib.Data.Finset.Functor
import all Mathlib.Data.Finset.Grade
import all Mathlib.Data.Finset.Image
import all Mathlib.Data.Finset.Insert
import all Mathlib.Data.Finset.Interval
import all Mathlib.Data.Finset.Lattice.Basic
import all Mathlib.Data.Finset.Lattice.Fold
import all Mathlib.Data.Finset.Lattice.Lemmas
import all Mathlib.Data.Finset.Lattice.Pi
import all Mathlib.Data.Finset.Lattice.Prod
import all Mathlib.Data.Finset.Lattice.Union
import all Mathlib.Data.Finset.Max
import all Mathlib.Data.Finset.MulAntidiagonal
import all Mathlib.Data.Finset.NAry
import all Mathlib.Data.Finset.NatAntidiagonal
import all Mathlib.Data.Finset.NatDivisors
import all Mathlib.Data.Finset.NoncommProd
import all Mathlib.Data.Finset.Option
import all Mathlib.Data.Finset.Order
import all Mathlib.Data.Finset.Pairwise
import all Mathlib.Data.Finset.Pi
import all Mathlib.Data.Finset.Piecewise
import all Mathlib.Data.Finset.PiInduction
import all Mathlib.Data.Finset.PImage
import all Mathlib.Data.Finset.Powerset
import all Mathlib.Data.Finset.Preimage
import all Mathlib.Data.Finset.Prod
import all Mathlib.Data.Finset.Range
import all Mathlib.Data.Finset.SDiff
import all Mathlib.Data.Finset.Sigma
import all Mathlib.Data.Finset.Slice
import all Mathlib.Data.Finset.SMulAntidiagonal
import all Mathlib.Data.Finset.Sort
import all Mathlib.Data.Finset.Sum
import all Mathlib.Data.Finset.Sups
import all Mathlib.Data.Finset.Sym
import all Mathlib.Data.Finset.SymmDiff
import all Mathlib.Data.Finset.Union
import all Mathlib.Data.Finset.Update
import all Mathlib.Data.Fin.SuccPred
import all Mathlib.Data.Finsupp.AList
import all Mathlib.Data.Finsupp.Antidiagonal
import all Mathlib.Data.Finsupp.Basic
import all Mathlib.Data.Finsupp.BigOperators
import all Mathlib.Data.Finsupp.Defs
import all Mathlib.Data.Finsupp.Encodable
import all Mathlib.Data.Finsupp.Ext
import all Mathlib.Data.Finsupp.Fin
import all Mathlib.Data.Finsupp.Fintype
import all Mathlib.Data.Finsupp.Indicator
import all Mathlib.Data.Finsupp.Interval
import all Mathlib.Data.Finsupp.Lex
import all Mathlib.Data.Finsupp.MonomialOrder
import all Mathlib.Data.Finsupp.MonomialOrder.DegLex
import all Mathlib.Data.Finsupp.Multiset
import all Mathlib.Data.Finsupp.NeLocus
import all Mathlib.Data.Finsupp.Notation
import all Mathlib.Data.Finsupp.Option
import all Mathlib.Data.Finsupp.Order
import all Mathlib.Data.Finsupp.Pointwise
import all Mathlib.Data.Finsupp.PWO
import all Mathlib.Data.Finsupp.Quotient
import all Mathlib.Data.Finsupp.Sigma
import all Mathlib.Data.Finsupp.Single
import all Mathlib.Data.Finsupp.SMul
import all Mathlib.Data.Finsupp.SMulWithZero
import all Mathlib.Data.Finsupp.ToDFinsupp
import all Mathlib.Data.Finsupp.Weight
import all Mathlib.Data.Finsupp.WellFounded
import all Mathlib.Data.Fin.Tuple.Basic
import all Mathlib.Data.Fin.Tuple.BubbleSortInduction
import all Mathlib.Data.Fin.Tuple.Curry
import all Mathlib.Data.Fin.Tuple.Embedding
import all Mathlib.Data.Fin.Tuple.Finset
import all Mathlib.Data.Fin.Tuple.NatAntidiagonal
import all Mathlib.Data.Fin.Tuple.Reflection
import all Mathlib.Data.Fin.Tuple.Sort
import all Mathlib.Data.Fin.Tuple.Take
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Data.Fintype.BigOperators
import all Mathlib.Data.Fintype.Card
import all Mathlib.Data.Fintype.CardEmbedding
import all Mathlib.Data.Fintype.Defs
import all Mathlib.Data.Fintype.EquivFin
import all Mathlib.Data.Fintype.Fin
import all Mathlib.Data.Fintype.Inv
import all Mathlib.Data.Fintype.Lattice
import all Mathlib.Data.Fintype.List
import all Mathlib.Data.Fintype.OfMap
import all Mathlib.Data.Fintype.Option
import all Mathlib.Data.Fintype.Order
import all Mathlib.Data.Fintype.Parity
import all Mathlib.Data.Fintype.Perm
import all Mathlib.Data.Fintype.Pi
import all Mathlib.Data.Fintype.Pigeonhole
import all Mathlib.Data.Fintype.Powerset
import all Mathlib.Data.Fintype.Prod
import all Mathlib.Data.Fintype.Quotient
import all Mathlib.Data.Fintype.Sets
import all Mathlib.Data.Fintype.Shrink
import all Mathlib.Data.Fintype.Sigma
import all Mathlib.Data.Fintype.Sort
import all Mathlib.Data.Fintype.Sum
import all Mathlib.Data.Fintype.Vector
import all Mathlib.Data.Fintype.WithTopBot
import all Mathlib.Data.Fin.VecNotation
import all Mathlib.Data.FunLike.Fintype
import all Mathlib.Data.Holor
import all Mathlib.Data.Ineq
import all Mathlib.Data.Int.Associated
import all Mathlib.Data.Int.Basic
import all Mathlib.Data.Int.Bitwise
import all Mathlib.Data.Int.CardIntervalMod
import all Mathlib.Data.Int.Cast.Basic
import all Mathlib.Data.Int.Cast.Defs
import all Mathlib.Data.Int.Cast.Field
import all Mathlib.Data.Int.Cast.Lemmas
import all Mathlib.Data.Int.Cast.Pi
import all Mathlib.Data.Int.Cast.Prod
import all Mathlib.Data.Int.CharZero
import all Mathlib.Data.Int.DivMod
import all Mathlib.Data.Int.Fib.Basic
import all Mathlib.Data.Int.Fib.Lemmas
import all Mathlib.Data.Int.GCD
import all Mathlib.Data.Int.Init
import all Mathlib.Data.Int.Interval
import all Mathlib.Data.Int.Lemmas
import all Mathlib.Data.Int.Log
import all Mathlib.Data.Int.ModEq
import all Mathlib.Data.Int.NatAbs
import all Mathlib.Data.Int.NatPrime
import all Mathlib.Data.Int.Notation
import all Mathlib.Data.Int.Order.Basic
import all Mathlib.Data.Int.Order.Lemmas
import all Mathlib.Data.Int.Order.Units
import all Mathlib.Data.Int.Range
import all Mathlib.Data.Int.Sqrt
import all Mathlib.Data.Int.WithZero
import all Mathlib.Data.LawfulXor.Basic
import all Mathlib.Data.LawfulXor.Equiv
import all Mathlib.Data.List.AList
import all Mathlib.Data.List.Basic
import all Mathlib.Data.List.Chain
import all Mathlib.Data.List.ChainOfFn
import all Mathlib.Data.List.Count
import all Mathlib.Data.List.Cycle
import all Mathlib.Data.List.Dedup
import all Mathlib.Data.List.Defs
import all Mathlib.Data.List.Destutter
import all Mathlib.Data.List.DropRight
import all Mathlib.Data.List.Duplicate
import all Mathlib.Data.List.Enum
import all Mathlib.Data.List.Find
import all Mathlib.Data.List.FinRange
import all Mathlib.Data.List.Flatten
import all Mathlib.Data.List.Fold
import all Mathlib.Data.List.Forall2
import all Mathlib.Data.List.GetD
import all Mathlib.Data.List.Indexes
import all Mathlib.Data.List.Induction
import all Mathlib.Data.List.Infix
import all Mathlib.Data.List.InsertIdx
import all Mathlib.Data.List.Interleave
import all Mathlib.Data.List.Intervals
import all Mathlib.Data.List.Iterate
import all Mathlib.Data.List.Lattice
import all Mathlib.Data.List.Lemmas
import all Mathlib.Data.List.Lex
import all Mathlib.Data.List.Lookmap
import all Mathlib.Data.List.Map2
import all Mathlib.Data.List.MinMax
import all Mathlib.Data.List.ModifyLast
import all Mathlib.Data.List.Monad
import all Mathlib.Data.List.NatAntidiagonal
import all Mathlib.Data.List.Nodup
import all Mathlib.Data.List.NodupEquivFin
import all Mathlib.Data.List.OffDiag
import all Mathlib.Data.List.OfFn
import all Mathlib.Data.List.Pairwise
import all Mathlib.Data.List.Palindrome
import all Mathlib.Data.List.PeriodicityLemma
import all Mathlib.Data.List.Perm.Basic
import all Mathlib.Data.List.Perm.Lattice
import all Mathlib.Data.List.Perm.Subperm
import all Mathlib.Data.List.Permutation
import all Mathlib.Data.List.Pi
import all Mathlib.Data.List.Prime
import all Mathlib.Data.List.ProdSigma
import all Mathlib.Data.List.Range
import all Mathlib.Data.List.ReduceOption
import all Mathlib.Data.List.Rotate
import all Mathlib.Data.List.Sections
import all Mathlib.Data.List.Shortlex
import all Mathlib.Data.List.Sigma
import all Mathlib.Data.List.SignVariations
import all Mathlib.Data.List.Sort
import all Mathlib.Data.List.SplitBy
import all Mathlib.Data.List.SplitLengths
import all Mathlib.Data.List.Sublists
import all Mathlib.Data.List.Sym
import all Mathlib.Data.List.TakeDrop
import all Mathlib.Data.List.TakeWhile
import all Mathlib.Data.List.TFAE
import all Mathlib.Data.List.ToFinsupp
import all Mathlib.Data.List.Triplewise
import all Mathlib.Data.List.Zip
import all Mathlib.Data.Matrix.Auto
import all Mathlib.Data.Matrix.Basic
import all Mathlib.Data.Matrix.Basis
import all Mathlib.Data.Matrix.Block
import all Mathlib.Data.Matrix.ColumnRowPartitioned
import all Mathlib.Data.Matrix.Composition
import all Mathlib.Data.Matrix.Diagonal
import all Mathlib.Data.Matrix.DMatrix
import all Mathlib.Data.Matrix.Mul
import all Mathlib.Data.Matrix.PEquiv
import all Mathlib.Data.Matrix.Reflection
import all Mathlib.Data.Multiset.AddSub
import all Mathlib.Data.Multiset.Antidiagonal
import all Mathlib.Data.Multiset.Basic
import all Mathlib.Data.Multiset.Bind
import all Mathlib.Data.Multiset.Count
import all Mathlib.Data.Multiset.Dedup
import all Mathlib.Data.Multiset.Defs
import all Mathlib.Data.Multiset.DershowitzManna
import all Mathlib.Data.Multiset.Filter
import all Mathlib.Data.Multiset.Find
import all Mathlib.Data.Multiset.FinsetOps
import all Mathlib.Data.Multiset.Fintype
import all Mathlib.Data.Multiset.Fold
import all Mathlib.Data.Multiset.Functor
import all Mathlib.Data.Multiset.Interval
import all Mathlib.Data.Multiset.Lattice
import all Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.NatAntidiagonal
import all Mathlib.Data.Multiset.Pairwise
import all Mathlib.Data.Multiset.Pi
import all Mathlib.Data.Multiset.Powerset
import all Mathlib.Data.Multiset.Range
import all Mathlib.Data.Multiset.Replicate
import all Mathlib.Data.Multiset.Sections
import all Mathlib.Data.Multiset.Sort
import all Mathlib.Data.Multiset.Sum
import all Mathlib.Data.Multiset.Sym
import all Mathlib.Data.Multiset.UnionInter
import all Mathlib.Data.Multiset.ZeroCons
import all Mathlib.Data.Nat.Basic
import all Mathlib.Data.Nat.BinaryRec
import all Mathlib.Data.Nat.BitIndices
import all Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Cast.Basic
import all Mathlib.Data.Nat.Cast.Commute
import all Mathlib.Data.Nat.Cast.Defs
import all Mathlib.Data.Nat.Cast.Field
import all Mathlib.Data.Nat.Cast.NeZero
import all Mathlib.Data.Nat.Cast.Order.Basic
import all Mathlib.Data.Nat.Cast.Order.Field
import all Mathlib.Data.Nat.Cast.Order.Ring
import all Mathlib.Data.Nat.Cast.Pi
import all Mathlib.Data.Nat.Cast.Prod
import all Mathlib.Data.Nat.Cast.SetInterval
import all Mathlib.Data.Nat.Cast.WithTop
import all Mathlib.Data.Nat.ChineseRemainder
import all Mathlib.Data.Nat.Choose.Basic
import all Mathlib.Data.Nat.Choose.Bounds
import all Mathlib.Data.Nat.Choose.Cast
import all Mathlib.Data.Nat.Choose.Central
import all Mathlib.Data.Nat.Choose.Consecutive
import all Mathlib.Data.Nat.Choose.Dvd
import all Mathlib.Data.Nat.Choose.Factorization
import all Mathlib.Data.Nat.Choose.Lucas
import all Mathlib.Data.Nat.Choose.Multinomial
import all Mathlib.Data.Nat.Choose.Sum
import all Mathlib.Data.Nat.Choose.Vandermonde
import all Mathlib.Data.Nat.Count
import all Mathlib.Data.Nat.Digits.Defs
import all Mathlib.Data.Nat.Digits.Div
import all Mathlib.Data.Nat.Digits.Lemmas
import all Mathlib.Data.Nat.Dist
import all Mathlib.Data.Nat.DvdSequence
import all Mathlib.Data.Nat.EvenOddRec
import all Mathlib.Data.Nat.Factorial.Basic
import all Mathlib.Data.Nat.Factorial.BigOperators
import all Mathlib.Data.Nat.Factorial.Cast
import all Mathlib.Data.Nat.Factorial.DoubleFactorial
import all Mathlib.Data.Nat.Factorial.NatCast
import all Mathlib.Data.Nat.Factorial.SuperFactorial
import all Mathlib.Data.Nat.Factorization.Basic
import all Mathlib.Data.Nat.Factorization.Defs
import all Mathlib.Data.Nat.Factorization.Divisors
import all Mathlib.Data.Nat.Factorization.Induction
import all Mathlib.Data.Nat.Factorization.LCM
import all Mathlib.Data.Nat.Factorization.PrimePow
import all Mathlib.Data.Nat.Factorization.Root
import all Mathlib.Data.Nat.Factors
import all Mathlib.Data.Nat.Fib.Basic
import all Mathlib.Data.Nat.Fib.Zeckendorf
import all Mathlib.Data.Nat.Find
import all Mathlib.Data.Nat.GCD.Basic
import all Mathlib.Data.Nat.GCD.BigOperators
import all Mathlib.Data.Nat.GCD.Prime
import all Mathlib.Data.Nat.Hyperoperation
import all Mathlib.Data.Nat.Init
import all Mathlib.Data.Nat.Log
import all Mathlib.Data.Nat.MaxPowDiv
import all Mathlib.Data.Nat.MaxPrimeFac
import all Mathlib.Data.Nat.ModEq
import all Mathlib.Data.Nat.Multiplicity
import all Mathlib.Data.Nat.Notation
import all Mathlib.Data.Nat.Nth
import all Mathlib.Data.Nat.NthRoot.Defs
import all Mathlib.Data.Nat.Order.Lemmas
import all Mathlib.Data.Nat.PadicValNat
import all Mathlib.Data.Nat.Pairing
import all Mathlib.Data.Nat.Periodic
import all Mathlib.Data.Nat.Prime.Basic
import all Mathlib.Data.Nat.Prime.Defs
import all Mathlib.Data.Nat.Prime.Factorial
import all Mathlib.Data.Nat.PrimeFin
import all Mathlib.Data.Nat.Prime.Infinite
import all Mathlib.Data.Nat.Prime.Int
import all Mathlib.Data.Nat.Prime.Nth
import all Mathlib.Data.Nat.Prime.Pow
import all Mathlib.Data.Nat.PSub
import all Mathlib.Data.Nat.Set
import all Mathlib.Data.Nat.Size
import all Mathlib.Data.Nat.Sqrt
import all Mathlib.Data.Nat.Squarefree
import all Mathlib.Data.Nat.Totient
import all Mathlib.Data.Nat.Upto
import all Mathlib.Data.Nat.WithBot
import all Mathlib.Data.NNRat.BigOperators
import all Mathlib.Data.NNRat.Defs
import all Mathlib.Data.NNRat.Encodable
import all Mathlib.Data.NNRat.Floor
import all Mathlib.Data.NNRat.Lemmas
import all Mathlib.Data.Num.Basic
import all Mathlib.Data.Num.Bitwise
import all Mathlib.Data.Num.Lemmas
import all Mathlib.Data.Num.Prime
import all Mathlib.Data.Num.ZNum
import all Mathlib.Data.Option.Basic
import all Mathlib.Data.Option.Defs
import all Mathlib.Data.Option.NAry
import all Mathlib.Data.Ordering.Basic
import all Mathlib.Data.Ordering.Lemmas
import all Mathlib.Data.Ordmap.Invariants
import all Mathlib.Data.Ordmap.Ordnode
import all Mathlib.Data.Ordmap.Ordset
import all Mathlib.Data.Part
import all Mathlib.Data.PFun
import all Mathlib.Data.PFunctor.Multivariate.Basic
import all Mathlib.Data.PFunctor.Multivariate.M
import all Mathlib.Data.PFunctor.Multivariate.W
import all Mathlib.Data.PFunctor.Univariate.Basic
import all Mathlib.Data.PFunctor.Univariate.M
import all Mathlib.Data.Pi.Interval
import all Mathlib.Data.PNat.Basic
import all Mathlib.Data.PNat.Defs
import all Mathlib.Data.PNat.Equiv
import all Mathlib.Data.PNat.Factors
import all Mathlib.Data.PNat.Find
import all Mathlib.Data.PNat.Interval
import all Mathlib.Data.PNat.Notation
import all Mathlib.Data.PNat.Prime
import all Mathlib.Data.PNat.Xgcd
import all Mathlib.Data.Prod.Basic
import all Mathlib.Data.Prod.PProd
import all Mathlib.Data.Prod.TProd
import all Mathlib.Data.QPF.Multivariate.Basic
import all Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import all Mathlib.Data.QPF.Multivariate.Constructions.Comp
import all Mathlib.Data.QPF.Multivariate.Constructions.Const
import all Mathlib.Data.QPF.Multivariate.Constructions.Fix
import all Mathlib.Data.QPF.Multivariate.Constructions.Prj
import all Mathlib.Data.QPF.Multivariate.Constructions.Quot
import all Mathlib.Data.QPF.Multivariate.Constructions.Sigma
import all Mathlib.Data.QPF.Univariate.Basic
import all Mathlib.Data.Quot
import all Mathlib.Data.Rat.BigOperators
import all Mathlib.Data.Rat.Cast.CharZero
import all Mathlib.Data.Rat.Cast.Defs
import all Mathlib.Data.Rat.Cast.Lemmas
import all Mathlib.Data.Rat.Cast.OfScientific
import all Mathlib.Data.Rat.Cast.Order
import all Mathlib.Data.Rat.Defs
import all Mathlib.Data.Rat.Denumerable
import all Mathlib.Data.Rat.Encodable
import all Mathlib.Data.Rat.Floor
import all Mathlib.Data.Rat.Init
import all Mathlib.Data.Rat.Lemmas
import all Mathlib.Data.Rat.NatSqrt.Defs
import all Mathlib.Data.Rat.Sqrt
import all Mathlib.Data.Rat.Squarefree
import all Mathlib.Data.Semiquot
import all Mathlib.Data.Seq.Basic
import all Mathlib.Data.Seq.Computation
import all Mathlib.Data.Seq.Defs
import all Mathlib.Data.Seq.Parallel
import all Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.BooleanAlgebra
import all Mathlib.Data.Set.BoolIndicator
import all Mathlib.Data.Set.Card
import all Mathlib.Data.Set.Card.Arithmetic
import all Mathlib.Data.Set.CoeSort
import all Mathlib.Data.Set.Constructions
import all Mathlib.Data.Set.Countable
import all Mathlib.Data.Set.Defs
import all Mathlib.Data.Set.Disjoint
import all Mathlib.Data.Set.Enumerate
import all Mathlib.Data.Set.Equitable
import all Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.FiniteExhaustion
import all Mathlib.Data.Set.Finite.Lattice
import all Mathlib.Data.Set.Finite.Lemmas
import all Mathlib.Data.Set.Finite.List
import all Mathlib.Data.Set.Finite.Monad
import all Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Range
import all Mathlib.Data.Set.Function
import all Mathlib.Data.Set.Functor
import all Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Inclusion
import all Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Lattice.Bounded
import all Mathlib.Data.Set.Lattice.Disjoint
import all Mathlib.Data.Set.Lattice.Image
import all Mathlib.Data.Set.Lattice.Indexed
import all Mathlib.Data.Set.Lattice.Order
import all Mathlib.Data.SetLike.Fintype
import all Mathlib.Data.Set.List
import all Mathlib.Data.Set.MemPartition
import all Mathlib.Data.Set.Monotone
import all Mathlib.Data.Set.MulAntidiagonal
import all Mathlib.Data.Set.NAry
import all Mathlib.Data.Set.Notation
import all Mathlib.Data.Set.Operations
import all Mathlib.Data.Set.Opposite
import all Mathlib.Data.Set.Order
import all Mathlib.Data.Set.Pairwise.Basic
import all Mathlib.Data.Set.Pairwise.Lattice
import all Mathlib.Data.Set.Pairwise.List
import all Mathlib.Data.Set.Piecewise
import all Mathlib.Data.Set.Pointwise.Support
import all Mathlib.Data.Set.PowersetCard
import all Mathlib.Data.Set.Prod
import all Mathlib.Data.Set.Restrict
import all Mathlib.Data.Set.Semiring
import all Mathlib.Data.Set.Sigma
import all Mathlib.Data.Set.SMulAntidiagonal
import all Mathlib.Data.Set.Subset
import all Mathlib.Data.Set.Subsingleton
import all Mathlib.Data.Set.Sups
import all Mathlib.Data.Set.SymmDiff
import all Mathlib.Data.Set.UnionLift
import all Mathlib.Data.Sigma.Basic
import all Mathlib.Data.Sigma.Interval
import all Mathlib.Data.Stream.Defs
import all Mathlib.Data.Stream.Init
import all Mathlib.Data.String.Basic
import all Mathlib.Data.String.Defs
import all Mathlib.Data.String.Lemmas
import all Mathlib.Data.Subtype
import all Mathlib.Data.SubtypeNeLift
import all Mathlib.Data.Sum.Basic
import all Mathlib.Data.Sum.Interval
import all Mathlib.Data.Sym.Basic
import all Mathlib.Data.Sym.Card
import all Mathlib.Data.Sym.NatCard
import all Mathlib.Data.Sym.Sym2
import all Mathlib.Data.Sym.Sym2.Card
import all Mathlib.Data.Sym.Sym2.Finsupp
import all Mathlib.Data.Sym.Sym2.Init
import all Mathlib.Data.Tree.Basic
import all Mathlib.Data.Tree.Get
import all Mathlib.Data.Tree.Traversable
import all Mathlib.Data.TypeVec
import all Mathlib.Data.UInt
import all Mathlib.Data.ULift
import all Mathlib.Data.Vector3
import all Mathlib.Data.Vector.Basic
import all Mathlib.Data.Vector.Defs
import all Mathlib.Data.Vector.MapLemmas
import all Mathlib.Data.Vector.Mem
import all Mathlib.Data.Vector.Snoc
import all Mathlib.Data.Vector.Zip
import all Mathlib.Data.W.Basic
import all Mathlib.Data.W.Cardinal
import all Mathlib.Data.W.Constructions
import all Mathlib.Data.WSeq.Basic
import all Mathlib.Data.WSeq.Defs
import all Mathlib.Data.WSeq.Productive
import all Mathlib.Data.WSeq.Relation
import all Mathlib.Data.ZMod.Aut
import all Mathlib.Data.ZMod.Basic
import all Mathlib.Data.ZMod.Coprime
import all Mathlib.Data.ZMod.Defs
import all Mathlib.Data.ZMod.Factorial
import all Mathlib.Data.ZMod.IntUnitsPower
import all Mathlib.Data.ZMod.QuotientGroup
import all Mathlib.Data.ZMod.QuotientRing
import all Mathlib.Data.ZMod.Units
import all Mathlib.Data.ZMod.ValMinAbs
import all Mathlib.Data.Fin.EquivOfInjective
-- hypkit toolkit header (mathlib-data, module system, from wave W2 on): HCHeaderM = all Mathlib.Data
-- modules + Mathlib.Analysis.Real.Cardinality + Mathlib.Topology.Sets.Closeds (public parts) and the
-- drop%/indep%/drop0%/indep0%/drop1%/priv% elaborators; `import all` gives the private parts of every
-- Data module (private constants, bodies of non-exposed definitions). Do NOT open a `public section`:
-- your declarations stay private, so they may mention private library constants.
-- Agents copy this file unchanged as the start of their output file (scripts/verify.sh checks it).
-- Need a module outside Mathlib.Data? Log the row as gave_up with obstruction "needs import <Module>".

set_option linter.unusedVariables false

open Lean Meta Elab Term

namespace W1c0

/-- Commutativity of a cyclic group, from the generator. -/
theorem cyc_comm {G : Type} [Group G] (h : IsCyclic G) (x y : G) : x * y = y * x := by
  obtain ⟨g, hg⟩ := h.exists_zpow_surjective
  obtain ⟨m, rfl⟩ := hg x
  obtain ⟨n, rfl⟩ := hg y
  exact (zpow_mul_comm g m n)

/-- Perm ℕ is not commutative. -/
theorem permN_not_comm : (Equiv.swap (0:ℕ) 1 * Equiv.swap 1 2) ≠ Equiv.swap 1 2 * Equiv.swap 0 1 := by
  intro h
  have := congrArg (fun e => e 0) h
  simp [Equiv.swap_apply_of_ne_of_ne] at this

theorem perm3_not_comm : (Equiv.swap (0:Fin 3) 1 * Equiv.swap 1 2) ≠ Equiv.swap 1 2 * Equiv.swap 0 1 := by
  decide

/-- Left projection: associative, not commutative. -/
def lp (a _ : ℕ) : ℕ := a
instance lpA : Std.Associative lp := ⟨fun _ _ _ => rfl⟩
theorem lp_not_comm : ¬ Std.Commutative lp := fun h => absurd (h.comm 0 1) (by decide)

/-- Midpoint on ℚ: commutative, idempotent, not associative. -/
def md (a b : ℚ) : ℚ := (a + b) / 2
instance mdC : Std.Commutative md := ⟨fun a b => by simp [md, add_comm]⟩
instance mdI : Std.IdempotentOp md := ⟨fun a => by simp [md]⟩
theorem md_not_assoc : ¬ Std.Associative md := fun h => by
  have := h.assoc 0 0 2
  simp [md] at this

/-- Two ALists whose entries are permutations but which differ. -/
def al1 : AList (fun _ : ℕ => ℕ) := ⟨[⟨0,0⟩,⟨1,0⟩], by simp [List.NodupKeys, List.keys]⟩
def al2 : AList (fun _ : ℕ => ℕ) := ⟨[⟨1,0⟩,⟨0,0⟩], by simp [List.NodupKeys, List.keys]⟩
theorem al_perm : al1.entries.Perm al2.entries := by
  simp [al1, al2]; exact List.Perm.swap _ _ _
theorem al_ne : al1.entries ≠ al2.entries := by simp [al1, al2]

theorem fm_ne (a : ℕ) (b : ℕ) : (∅ : Finmap (fun _ : ℕ => ℕ)) ≠ Finmap.singleton a b := by
  intro h; have := congrArg (Finmap.lookup a) h; simp at this

theorem ss_union : (Finmap.singleton 0 0 : Finmap (fun _ : ℕ => ℕ)) ∪ Finmap.singleton 0 0 =
    Finmap.singleton 0 0 := Finmap.ext_lookup fun x => by
  by_cases hx : x = 0
  · subst hx; rw [Finmap.lookup_union_left (by simp [Finmap.mem_singleton])]
  · rw [Finmap.lookup_union_right (by simp [Finmap.mem_singleton, hx])]

end W1c0

open W1c0

-- `Equiv.Perm.isCyclic_of_card_le_two` idx 1: necessary (alpha = Nat: Nat.card = 0 but Perm Nat is not commutative)
theorem w0_1 : ¬ drop0% Equiv.Perm.isCyclic_of_card_le_two 1 := fun h =>
  permN_not_comm (cyc_comm (@h ℕ (by simp)) _ _)

-- `Equiv.Perm.isCyclic_of_card_le_two` idx 2: necessary (alpha = Fin 3)
theorem w0_2 : ¬ drop0% Equiv.Perm.isCyclic_of_card_le_two 2 := fun h =>
  perm3_not_comm (cyc_comm (@h (Fin 3) _) _ _)

-- `Equiv.Perm.isMulCommutative_iff_card_le_two` idx 1: necessary (alpha = Nat)
theorem w0_3 : ¬ drop0% Equiv.Perm.isMulCommutative_iff_card_le_two 1 := fun h =>
  permN_not_comm (((@h ℕ).2 (by simp)).is_comm.comm _ _)

-- `Equiv.Perm.isCyclic_iff_card_le_two` idx 1: necessary (alpha = Nat)
theorem w0_4 : ¬ drop0% Equiv.Perm.isCyclic_iff_card_le_two 1 := fun h =>
  permN_not_comm (cyc_comm ((@h ℕ).2 (by simp)) _ _)

-- `Multiset.NodupKeys.nodup_keys` idx 3: necessary (m = {(0,0),(0,1)})
theorem w0_5 : ¬ drop0% Multiset.NodupKeys.nodup_keys 3 := fun h => by
  have := @h ℕ (fun _ => ℕ) {⟨0,0⟩, ⟨0,1⟩}
  simp [Multiset.keys] at this

-- `Multiset.NodupKeys.nodup` idx 3: necessary (m = {(0,0),(0,0)})
theorem w0_6 : ¬ drop0% Multiset.NodupKeys.nodup 3 := fun h => by
  have := @h ℕ (fun _ => ℕ) {⟨0,0⟩, ⟨0,0⟩}
  simp at this

-- `Finmap.liftOn_toFinmap` idx 5: necessary (f = entries, two permuted ALists)
theorem w0_7 : ¬ indep0% Finmap.liftOn_toFinmap 5 := fun h =>
  al_ne (@h ℕ (fun _ => ℕ) _ al1 AList.entries al1 al2 al_perm)

-- `Finmap.liftOn₂_toFinmap` idx 6: necessary (f = first entries)
theorem w0_8 : ¬ indep0% Finmap.liftOn₂_toFinmap 6 := fun h =>
  al_ne (@h ℕ (fun _ => ℕ) _ al1 al1 (fun a _ => a.entries) al1 al1 al2 al1 al_perm (List.Perm.refl _))

-- `Finmap.induction_on` idx 4: necessary (C = False)
theorem w0_9 : ¬ drop0% Finmap.induction_on 4 := fun h => @h ℕ (fun _ => ℕ) (fun _ => False) ∅

-- `Finmap.induction_on₂` idx 5: necessary (C = False)
theorem w0_10 : ¬ drop0% Finmap.induction_on₂ 5 := fun h => @h ℕ (fun _ => ℕ) (fun _ _ => False) ∅ ∅

-- `Finmap.induction_on₃` idx 6: necessary (C = False)
theorem w0_11 : ¬ drop0% Finmap.induction_on₃ 6 := fun h =>
  @h ℕ (fun _ => ℕ) (fun _ _ _ => False) ∅ ∅ ∅

-- `Finmap.ext` idx 4: necessary (empty vs singleton)
theorem w0_12 : ¬ drop0% Finmap.ext 4 := fun h => fm_ne 0 0 (@h ℕ (fun _ => ℕ) _ _)

-- `Finmap.mem_of_lookup_eq_some` idx 6: necessary (s = empty)
theorem w0_13 : ¬ drop0% Finmap.mem_of_lookup_eq_some 6 := fun h => by
  exact Finmap.notMem_empty (@h ℕ (fun _ => ℕ) _ 0 0 ∅)

-- `Finmap.ext_lookup` idx 5: necessary (empty vs singleton)
theorem w0_14 : ¬ drop0% Finmap.ext_lookup 5 := fun h => fm_ne 0 0 (@h ℕ (fun _ => ℕ) _ _ _)

-- `Finmap.lookup_erase_ne` idx 6: necessary (a = a', s = singleton a 0)
theorem w0_15 : ¬ drop0% Finmap.lookup_erase_ne 6 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ 0 0 (Finmap.singleton 0 0)
  simp at this

-- `Finmap.entries_insert_of_notMem` idx 6: necessary (s = singleton a b)
theorem w0_16 : ¬ drop0% Finmap.entries_insert_of_notMem 6 := fun h => by
  have := congrArg Multiset.card (@h ℕ (fun _ => ℕ) _ 0 0 (Finmap.singleton 0 0))
  simp at this

-- `Finmap.lookup_insert_of_ne` idx 7: necessary (a' = a, s = empty)
theorem w0_17 : ¬ drop0% Finmap.lookup_insert_of_ne 7 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ 0 0 0 ∅
  simp at this

-- `Finmap.insert_insert_of_ne` idx 8: necessary (a = a', b = 0, b' = 1)
theorem w0_18 : ¬ drop0% Finmap.insert_insert_of_ne 8 := fun h => by
  have := congrArg (Finmap.lookup 0) (@h ℕ (fun _ => ℕ) _ 0 0 0 1 ∅)
  simp at this

-- `Finmap.lookup_union_left` idx 6: necessary (s1 = empty, s2 = singleton)
theorem w0_19 : ¬ drop0% Finmap.lookup_union_left 6 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ 0 ∅ (Finmap.singleton 0 0)
  simp at this

-- `Finmap.lookup_union_right` idx 6: necessary (s1 = singleton, s2 = empty)
theorem w0_20 : ¬ drop0% Finmap.lookup_union_right 6 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ 0 (Finmap.singleton 0 0) ∅
  simp at this

-- `Finmap.lookup_union_left_of_not_in` idx 6: necessary (s1 = empty, s2 = singleton)
theorem w0_21 : ¬ drop0% Finmap.lookup_union_left_of_not_in 6 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ 0 ∅ (Finmap.singleton 0 0)
  simp at this

-- `Finmap.mem_lookup_union_middle` idx 8: necessary (all empty)
theorem w0_22 : ¬ drop0% Finmap.mem_lookup_union_middle 8 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ 0 0 ∅ ∅ ∅ Finmap.notMem_empty
  simp at this

-- `Finmap.mem_lookup_union_middle` idx 9: necessary (s1 = empty, s2 = singleton 0 1, s3 = singleton 0 0)
theorem w0_23 : ¬ drop0% Finmap.mem_lookup_union_middle 9 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ 0 0 ∅ (Finmap.singleton 0 1) (Finmap.singleton 0 0) (by simp)
  simp at this

-- `Finmap.Disjoint.symm` idx 4: necessary (x = y = singleton)
theorem w0_24 : ¬ drop0% Finmap.Disjoint.symm 4 := fun h => by
  have := @h ℕ (fun _ => ℕ) (Finmap.singleton 0 0) (Finmap.singleton 0 0)
  exact this 0 (by simp) (by simp)

-- `Finmap.union_comm_of_disjoint` idx 5: necessary (singleton 0 0, singleton 0 1)
theorem w0_25 : ¬ drop0% Finmap.union_comm_of_disjoint 5 := fun h => by
  have := congrArg (Finmap.lookup 0) (@h ℕ (fun _ => ℕ) _ (Finmap.singleton 0 0) (Finmap.singleton 0 1))
  simp at this

-- `Finmap.union_cancel` idx 6: necessary (s1 = s3 = singleton, s2 = empty)
theorem w0_26 : ¬ drop0% Finmap.union_cancel 6 := fun h => by
  have := (@h ℕ (fun _ => ℕ) _ (Finmap.singleton 0 0) ∅ (Finmap.singleton 0 0)
    (fun _ h1 => absurd h1 Finmap.notMem_empty)).1 (by rw [ss_union, Finmap.empty_union])
  exact fm_ne 0 0 this.symm

-- `Finmap.union_cancel` idx 7: necessary (s2 = s3 = singleton, s1 = empty)
theorem w0_27 : ¬ drop0% Finmap.union_cancel 7 := fun h => by
  have := (@h ℕ (fun _ => ℕ) _ ∅ (Finmap.singleton 0 0) (Finmap.singleton 0 0)
    (fun _ h1 => absurd h1 Finmap.notMem_empty)).1 (by rw [ss_union, Finmap.empty_union])
  exact fm_ne 0 0 this

-- `Finset.erase_eq_iff_eq_insert` idx 6: necessary (s = t = {0}, a = 0)
theorem w0_28 : ¬ drop0% Finset.erase_eq_iff_eq_insert 6 := fun h =>
  absurd (@h ℕ _ {0} {0} 0 (by simp)) (by decide)

-- `Finset.sdiff_insert_insert_of_mem_of_notMem` idx 6: necessary (s = t = {0}, x = 0)
theorem w0_29 : ¬ drop0% Finset.sdiff_insert_insert_of_mem_of_notMem 6 := fun h =>
  absurd (@h ℕ _ {0} {0} 0 (by simp)) (by decide)

-- `Finset.disjoint_filter_filter'` idx 7: necessary (s = t = {0}, p = q = True)
theorem w0_30 : ¬ drop0% Finset.disjoint_filter_filter' 7 := fun h =>
  absurd (@h ℕ {0} {0} (fun _ => True) (fun _ => True) _ _) (by decide)

-- `Finset.subset_union_elim` idx 5: necessary (s = {0}, t1 = t2 = empty)
theorem w0_31 : ¬ drop0% Finset.subset_union_elim 5 := fun h => by
  obtain ⟨s₁, s₂, h1, h2, h3⟩ := @h ℕ _ {0} ∅ ∅
  simp at h2 h3; subst h2; subst h3; simp at h1

-- `Equiv.Finset.union_inl` idx 4: necessary (s = t = {0})
theorem w0_32 : ¬ indep0% Equiv.Finset.union_inl 4 := fun h =>
  absurd (@h ℕ _ {0} {0} ⟨0, by simp⟩) (by decide)

-- `Equiv.Finset.union_inr` idx 4: necessary (s = t = {0})
theorem w0_33 : ¬ indep0% Equiv.Finset.union_inr 4 := fun h =>
  absurd (@h ℕ _ {0} {0} ⟨0, by simp⟩) (by decide)

-- `Equiv.Finset.disjUnionEquiv_inl` idx 4: necessary (s = t = {0})
theorem w0_34 : ¬ indep0% Equiv.Finset.disjUnionEquiv_inl 4 := fun h =>
  absurd (@h ℕ _ {0} {0} ⟨0, by simp⟩) (by decide)

-- `Equiv.Finset.disjUnionEquiv_inr` idx 4: necessary (s = t = {0})
theorem w0_35 : ¬ indep0% Equiv.Finset.disjUnionEquiv_inr 4 := fun h =>
  absurd (@h ℕ _ {0} {0} ⟨0, by simp⟩) (by decide)

-- `Equiv.piFinsetUnion_left` idx 5: necessary (s = t = {0}, i = 0)
theorem w0_36 : ¬ indep0% Equiv.piFinsetUnion_left 5 := fun h =>
  absurd (@h ℕ _ (fun _ => ℕ) {0} {0} (fun _ => 0) (fun _ => 0) 0 (by simp) (by simp)) (by decide)

-- `Equiv.piFinsetUnion_left` idx 9: necessary (s = empty, t = {0}, i = 0)
theorem w0_37 : ¬ indep0% Equiv.piFinsetUnion_left 9 := fun h =>
  absurd (@h ℕ _ (fun _ => ℕ) ∅ {0} (by simp) (fun _ => 0) (fun _ => 0) 0 (by simp)) (by simp)

-- `Equiv.piFinsetUnion_right` idx 5: necessary (s = t = {0}, i = 0)
theorem w0_38 : ¬ indep0% Equiv.piFinsetUnion_right 5 := fun h =>
  absurd (@h ℕ _ (fun _ => ℕ) {0} {0} (fun _ => 0) (fun _ => 0) 0 (by simp) (by simp)) (by decide)

-- `Equiv.piFinsetUnion_right` idx 9: necessary (s = {0}, t = empty, i = 0)
theorem w0_39 : ¬ indep0% Equiv.piFinsetUnion_right 9 := fun h =>
  absurd (@h ℕ _ (fun _ => ℕ) {0} ∅ (by simp) (fun _ => 0) (fun _ => 0) 0 (by simp)) (by simp)

-- `Finset.univ_nonempty` idx 2: necessary (alpha = Empty)
theorem w0_40 : ¬ drop0% Finset.univ_nonempty 2 := fun h => by
  obtain ⟨x, _⟩ := @h Empty _
  exact x.elim

-- `Finset.univ_neq_empty` idx 2: necessary (alpha = Empty)
theorem w0_41 : ¬ drop0% Finset.univ_neq_empty 2 := fun h => @h Empty _ (by simp)

-- `Finset.card_eq_of_bijective` idx 4: necessary (s = {0,1}, n = 0)
theorem w0_42 : ¬ drop0% Finset.card_eq_of_bijective 4 := fun h =>
  absurd (@h ℕ {0, 1} 0 (fun _ _ => 0) (by simp) (by simp)) (by decide)

-- `Finset.card_eq_of_bijective` idx 5: necessary (s = empty, n = 1)
theorem w0_43 : ¬ drop0% Finset.card_eq_of_bijective 5 := fun h =>
  absurd (@h ℕ ∅ 1 (fun _ _ => 0) (by simp) (by omega)) (by decide)

-- `Finset.card_eq_of_bijective` idx 6: necessary (s = {0}, n = 2, f = 0)
theorem w0_44 : ¬ drop0% Finset.card_eq_of_bijective 6 := fun h =>
  absurd (@h ℕ {0} 2 (fun _ _ => 0) (by simp; exact ⟨0, by omega⟩) (by simp)) (by decide)

-- `Finset.card_bij` idx 6: necessary (s = {0,1}, t = {0}, i = 0)
theorem w0_45 : ¬ drop0% Finset.card_bij 6 := fun h =>
  absurd (@h ℕ ℕ {0, 1} {0} (fun _ _ => 0) (by simp) (by simp)) (by decide)

-- `Finset.card_bij` idx 7: necessary (s = empty, t = {0})
theorem w0_46 : ¬ drop0% Finset.card_bij 7 := fun h =>
  absurd (@h ℕ ℕ ∅ {0} (fun _ _ => 0) (by simp) (by simp)) (by decide)

-- `Finset.card_bij'` idx 6: necessary (s = {0,1}, t = {0}, i = id, j = 0)
theorem w0_47 : ¬ indep0% Finset.card_bij' 6 := fun h =>
  absurd (@h ℕ ℕ {0, 1} {0} (fun a _ => a) (fun _ _ => 0) (by simp) (by simp) 1 (by simp)) (by simp)

-- `Finset.card_bij'` idx 7: necessary (s = {0}, t = {0,1}, i = 0, j = id)
theorem w0_48 : ¬ indep0% Finset.card_bij' 7 := fun h =>
  absurd (@h ℕ ℕ {0} {0, 1} (fun _ _ => 0) (fun a _ => a) (by simp) (by simp) 1 (by simp)) (by simp)

-- `Finset.card_bij'` idx 8: necessary (s = {0,1}, t = {0}, i = j = 0)
theorem w0_49 : ¬ drop0% Finset.card_bij' 8 := fun h =>
  absurd (@h ℕ ℕ {0, 1} {0} (fun _ _ => 0) (fun _ _ => 0) (by simp) (by simp) (by simp)) (by decide)

-- `Finset.card_nbij` idx 6: necessary (s = {0,1}, t = {0}, i = 0)
theorem w0_50 : ¬ drop0% Finset.card_nbij 6 := fun h =>
  absurd (@h ℕ ℕ {0, 1} {0} (fun _ => 0) (by simp [Set.MapsTo]) (by simp [Set.SurjOn])) (by decide)

-- `Finset.card_nbij'` idx 6: necessary (s = {0,1}, t = {0}, i = j = id)
theorem w0_51 : ¬ drop0% Finset.card_nbij' 6 := fun h =>
  absurd (@h ℕ ℕ {0, 1} {0} id id (by simp [Set.MapsTo]) (fun _ _ => rfl) (fun _ _ => rfl)) (by decide)

-- `Finset.card_nbij'` idx 7: necessary (s = {0}, t = {0,1}, i = j = id)
theorem w0_52 : ¬ drop0% Finset.card_nbij' 7 := fun h =>
  absurd (@h ℕ ℕ {0} {0, 1} id id (by simp [Set.MapsTo]) (fun _ _ => rfl) (fun _ _ => rfl)) (by decide)

-- `Finset.card_nbij'` idx 8: necessary (s = {0,1}, t = {0}, i = j = 0)
theorem w0_53 : ¬ drop0% Finset.card_nbij' 8 := fun h =>
  absurd (@h ℕ ℕ {0, 1} {0} (fun _ => 0) (fun _ => 0) (by simp [Set.MapsTo]) (by simp [Set.MapsTo])
    (by simp [Set.RightInvOn, Set.LeftInvOn])) (by decide)

-- `Finset.card_nbij'` idx 9: necessary (s = {0}, t = {0,1}, i = j = 0)
theorem w0_54 : ¬ drop0% Finset.card_nbij' 9 := fun h =>
  absurd (@h ℕ ℕ {0} {0, 1} (fun _ => 0) (fun _ => 0) (by simp [Set.MapsTo]) (by simp [Set.MapsTo])
    (by simp [Set.LeftInvOn])) (by decide)

-- `Finset.card_le_card_of_injOn` idx 6: necessary (s = {0,1}, t = {0}, f = 0)
theorem w0_55 : ¬ drop0% Finset.card_le_card_of_injOn 6 := fun h =>
  absurd (@h ℕ ℕ {0, 1} {0} (fun _ => 0) (by simp [Set.MapsTo])) (by decide)

-- `Finset.card_le_card_of_injective` idx 5: necessary (s = {0,1}, t = {0})
theorem w0_56 : ¬ drop0% Finset.card_le_card_of_injective 5 := fun h =>
  absurd (@h ℕ ℕ {0, 1} {0} (fun _ => ⟨0, by simp⟩)) (by decide)

-- `Finset.card_le_card_of_surjective` idx 5: necessary (s = {0}, t = {0,1})
theorem w0_57 : ¬ drop0% Finset.card_le_card_of_surjective 5 := fun h =>
  absurd (@h ℕ ℕ {0} {0, 1} (fun _ => ⟨0, by simp⟩)) (by decide)

-- `Finset.surjOn_of_injOn_of_card_le` idx 5: necessary (s = {0}, t = {1}, f = id)
theorem w0_58 : ¬ drop0% Finset.surjOn_of_injOn_of_card_le 5 := fun h => by
  have := @h ℕ ℕ {0} {1} id (by simp [Set.InjOn]) (by decide) 1 (show (1:ℕ) ∈ (({1} : Finset ℕ) : Set ℕ) by simp)
  simp at this

-- `Finset.surjOn_of_injOn_of_card_le` idx 6: necessary (s = t = {0,1}, f = 0)
theorem w0_59 : ¬ drop0% Finset.surjOn_of_injOn_of_card_le 6 := fun h => by
  have := @h ℕ ℕ {0, 1} {0, 1} (fun _ => 0) (by simp [Set.MapsTo]) (by decide)
    1 (show (1:ℕ) ∈ (({0, 1} : Finset ℕ) : Set ℕ) by simp)
  simp at this

-- `Finset.surj_on_of_inj_on_of_card_le` idx 5: necessary (s = {0}, t = {1}, f = id)
theorem w0_60 : ¬ drop0% Finset.surj_on_of_inj_on_of_card_le 5 := fun h => by
  have := @h ℕ ℕ {0} {1} (fun a _ => a) (by simp) (by decide) 1 (by simp)
  simp at this

-- `Finset.surj_on_of_inj_on_of_card_le` idx 6: necessary (s = t = {0,1}, f = 0)
theorem w0_61 : ¬ drop0% Finset.surj_on_of_inj_on_of_card_le 6 := fun h => by
  have := @h ℕ ℕ {0, 1} {0, 1} (fun _ _ => 0) (by simp) (by decide) 1 (by simp)
  simp at this

-- `Finset.surj_on_of_inj_on_of_card_le` idx 7: necessary (s = empty, t = {0})
theorem w0_62 : ¬ drop0% Finset.surj_on_of_inj_on_of_card_le 7 := fun h => by
  have := @h ℕ ℕ ∅ {0} (fun _ _ => 0) (by simp) (by simp) 0 (by simp)
  simp at this

-- `Finset.surj_on_of_inj_on_of_card_le` idx 9: necessary (s = t = {0}, f = id, b = 1)
theorem w0_63 : ¬ drop0% Finset.surj_on_of_inj_on_of_card_le 9 := fun h => by
  have := @h ℕ ℕ {0} {0} (fun a _ => a) (by simp) (by simp) (by decide) 1
  simp at this

-- `Finset.injOn_of_surjOn_of_card_le` idx 6: necessary (s = t = {0,1}, f = 0)
theorem w0_64 : ¬ drop0% Finset.injOn_of_surjOn_of_card_le 6 := fun h => by
  have := @h ℕ ℕ {0, 1} {0, 1} (fun _ => 0) (by simp [Set.MapsTo]) (by decide)
    0 (show (0:ℕ) ∈ (({0, 1} : Finset ℕ) : Set ℕ) by simp) 1 (show (1:ℕ) ∈ (({0, 1} : Finset ℕ) : Set ℕ) by simp) rfl
  simp at this

-- `Finset.injOn_of_surjOn_of_card_le` idx 7: necessary (s = {0,1}, t = {0}, f = 0)
theorem w0_65 : ¬ drop0% Finset.injOn_of_surjOn_of_card_le 7 := fun h => by
  have := @h ℕ ℕ {0, 1} {0} (fun _ => 0) (by simp [Set.MapsTo]) (by simp [Set.SurjOn])
    0 (show (0:ℕ) ∈ (({0, 1} : Finset ℕ) : Set ℕ) by simp) 1 (show (1:ℕ) ∈ (({0, 1} : Finset ℕ) : Set ℕ) by simp) rfl
  simp at this

-- `Finset.inj_on_of_surj_on_of_card_le` idx 6: necessary (s = t = {0,1}, f = 0)
theorem w0_66 : ¬ drop0% Finset.inj_on_of_surj_on_of_card_le 6 := fun h => by
  have := @h ℕ ℕ {0, 1} {0, 1} (fun _ _ => 0) (by simp) (by decide) 0 (by simp) 1 (by simp) rfl
  simp at this

-- `Finset.inj_on_of_surj_on_of_card_le` idx 7: necessary (s = {0,1}, t = {0}, f = 0)
theorem w0_67 : ¬ drop0% Finset.inj_on_of_surj_on_of_card_le 7 := fun h => by
  have := @h ℕ ℕ {0, 1} {0} (fun _ _ => 0) (by simp) (by simp) 0 (by simp) 1 (by simp) rfl
  simp at this

-- `Finset.inj_on_of_surj_on_of_card_le` idx 9: necessary (s = t = {0}, a2 = 0, a1 = 1)
theorem w0_68 : ¬ indep0% Finset.inj_on_of_surj_on_of_card_le 9 := fun h => by
  have := @h ℕ ℕ {0} {0} (fun _ _ => 0) (by simp) (by simp) (by simp) 1 0 (by simp)
  simp at this

-- `Finset.inj_on_of_surj_on_of_card_le` idx 11: necessary (s = t = {0}, a1 = 0, a2 = 1)
theorem w0_69 : ¬ indep0% Finset.inj_on_of_surj_on_of_card_le 11 := fun h => by
  have := @h ℕ ℕ {0} {0} (fun _ _ => 0) (by simp) (by simp) (by simp) 0 (by simp) 1
  simp at this

-- `Finset.inj_on_of_surj_on_of_card_le` idx 12: necessary (s = t = {0,1}, f = id)
theorem w0_70 : ¬ drop0% Finset.inj_on_of_surj_on_of_card_le 12 := fun h => by
  have := @h ℕ ℕ {0, 1} {0, 1} (fun a _ => a) (by simp) (by simp) (by simp) 0 (by simp) 1 (by simp)
  simp at this

-- `Finset.injOn_of_surjOn_of_card_le` idx 5: removable (t ⊆ f '' s gives #t ≤ #(s.image f) ≤ #s, so apply the theorem with t := s.image f)
theorem w0_71 : drop% Finset.injOn_of_surjOn_of_card_le 5 := by
  intro α β s t f hsurj hst
  classical
  have ht : t ⊆ s.image f := fun b hb => by
    obtain ⟨a, ha, rfl⟩ := hsurj (Finset.mem_coe.2 hb)
    exact Finset.mem_image_of_mem f ha
  exact Finset.injOn_of_surjOn_of_card_le f (fun a ha => Finset.mem_coe.2 (Finset.mem_image_of_mem f (Finset.mem_coe.1 ha)))
    (fun b hb => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
      exact ⟨a, ha, rfl⟩)
    (hst.trans (Finset.card_le_card ht))

-- `Finset.inj_on_of_surj_on_of_card_le` idx 5: removable (same argument with t := image of s.attach)
theorem w0_72 : drop% Finset.inj_on_of_surj_on_of_card_le 5 := by
  intro α β s t f hsurj hst a₁ ha₁ a₂ ha₂ he
  classical
  let u : Finset β := s.attach.image (fun a => f a.1 a.2)
  have ht : t ⊆ u := fun b hb => by
    obtain ⟨a, ha, rfl⟩ := hsurj b hb
    exact Finset.mem_image.2 ⟨⟨a, ha⟩, by simp, rfl⟩
  exact Finset.inj_on_of_surj_on_of_card_le (t := u) f
    (fun a ha => Finset.mem_image.2 ⟨⟨a, ha⟩, by simp, rfl⟩)
    (fun b hb => by
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hb
      exact ⟨a.1, a.2, rfl⟩)
    (hst.trans (Finset.card_le_card ht)) ha₁ ha₂ he

namespace W1c0
instance emptyDense : DenselyOrdered Empty := ⟨fun a => a.elim⟩
instance emptyNoMax : NoMaxOrder Empty := ⟨fun a => a.elim⟩
instance emptyNoMin : NoMinOrder Empty := ⟨fun a => a.elim⟩
/-- ZMod 2 as a field (the library instance lives outside Mathlib.Data). -/
@[instance_reducible] noncomputable def z2F : Field (ZMod 2) := Field.ofIsUnitOrEqZero (by decide)
theorem one_ne_zz (K : Type) [Semifield K] [Nontrivial K] : (1:K) ≠ 0 / 0 := by simp
theorem z2_two : ((2 : ℕ) : ZMod 2) = 0 := rfl
end W1c0

-- `Finset.image_eq_iff_bijOn_of_card` idx 6: necessary (s = {0,1}, f = 0, t = {0})
theorem w0_73 : ¬ drop0% Finset.image_eq_iff_bijOn_of_card 6 := fun h => by
  have := ((@h ℕ ℕ {0, 1} (fun _ => 0) {0} _).1 (by decide)).2.1
    (show (0:ℕ) ∈ (({0, 1} : Finset ℕ) : Set ℕ) by simp) (show (1:ℕ) ∈ (({0, 1} : Finset ℕ) : Set ℕ) by simp) rfl
  simp at this

-- `Finset.exists_subsuperset_card_eq` idx 4: necessary (s = {0}, t = {1}, n = 1)
theorem w0_74 : ¬ drop0% Finset.exists_subsuperset_card_eq 4 := fun h => by
  obtain ⟨u, h1, h2, -⟩ := @h ℕ {0} {1} 1 (by decide) (by decide)
  have := h2 (h1 (Finset.mem_singleton_self 0))
  simp at this

-- `Finset.card_le_one_iff_subset_singleton` idx 2: necessary (alpha = Empty)
theorem w0_75 : ¬ drop0% Finset.card_le_one_iff_subset_singleton 2 := fun h => by
  obtain ⟨x, -⟩ := (@h Empty ∅).1 (by simp)
  exact x.elim

-- `Finset.existsUnique_notMem_image_of_injOn_of_card_eq_add_one` idx 6: necessary (s = {0,1}, f = 0, t = {0,1,2})
theorem w0_76 : ¬ drop0% Finset.existsUnique_notMem_image_of_injOn_of_card_eq_add_one 6 := fun h => by
  obtain ⟨x, -, hu⟩ := @h ℕ ℕ {0, 1} (fun _ => 0) {0, 1, 2} _ (by simp [Set.MapsTo]) (by decide)
  have h1 := hu 1 (by decide)
  have h2 := hu 2 (by decide)
  omega

-- `Finset.existsUnique_notMem_image_of_injOn_of_card_eq_add_one` idx 7: necessary (s = {0}, f = id, t = {1,2})
theorem w0_77 : ¬ drop0% Finset.existsUnique_notMem_image_of_injOn_of_card_eq_add_one 7 := fun h => by
  obtain ⟨x, -, hu⟩ := @h ℕ ℕ {0} id {1, 2} _ (by simp [Set.InjOn]) (by decide)
  have h1 := hu 1 (by decide)
  have h2 := hu 2 (by decide)
  omega

-- `Finset.case_strong_induction_on` idx 4: necessary (p = (· ≠ ∅), s = ∅)
theorem w0_78 : ¬ drop0% Finset.case_strong_induction_on 4 := fun h =>
  @h ℕ _ (fun s => s ≠ ∅) ∅ (fun a s _ _ => Finset.insert_ne_empty a s) rfl

-- `Finset.case_strong_induction_on` idx 5: necessary (p = (· = ∅), s = {0})
theorem w0_79 : ¬ drop0% Finset.case_strong_induction_on 5 := fun h =>
  absurd (@h ℕ _ (· = ∅) {0} rfl) (by decide)

-- `Finset.Nonempty.strong_induction` idx 2: necessary (p s = s.Nontrivial, s = {0})
theorem w0_80 : ¬ drop0% Finset.Nonempty.strong_induction 2 := fun h => by
  have := @h ℕ (fun s _ => s.Nontrivial) (fun s hs _ => hs) {0} (by simp)
  simp at this

-- `Finset.Nonempty.strong_induction` idx 3: necessary (p s = (#s = 1), s = {0,1})
theorem w0_81 : ¬ drop0% Finset.Nonempty.strong_induction 3 := fun h => by
  have := @h ℕ (fun s _ => s.card = 1) (fun a => by simp) {0, 1} (by simp)
  simp at this

-- `Finset.Nonempty.strong_induction` idx 5: necessary (p = True, s = ∅)
theorem w0_82 : ¬ indep0% Finset.Nonempty.strong_induction 5 := fun h => by
  have := @h ℕ (fun _ _ => True) (fun _ => trivial) (fun _ _ _ => trivial) ∅
  simp at this

-- `Finset.eraseInduction` idx 3: necessary (p = False)
theorem w0_83 : ¬ drop0% Finset.eraseInduction 3 := fun h => @h ℕ _ (fun _ => False) ∅

-- `Finset.image_iterate_stabilises_lt_card` idx 4: necessary (f = succ, s = {0})
theorem w0_84 : ¬ drop0% Finset.image_iterate_stabilises_lt_card 4 := fun h => by
  obtain ⟨n, hn, hm⟩ := @h ℕ _ Nat.succ {0} (by simp)
  have := hm (n + 1) (by omega)
  simp [Finset.image_singleton, Nat.succ_iterate] at this

-- `Finset.image_iterate_stabilises_le_card` idx 4: necessary (f = succ, s = {0})
theorem w0_85 : ¬ drop0% Finset.image_iterate_stabilises_le_card 4 := fun h => by
  obtain ⟨n, hn, hm⟩ := @h ℕ _ Nat.succ {0}
  have := hm (n + 1) (by omega)
  simp [Finset.image_singleton, Nat.succ_iterate] at this

-- `Finset.PiFinsetCoe.canLift` idx 2: necessary (iota = Unit, alpha = Empty, s = ∅)
theorem w0_86 : ¬ drop0% Finset.PiFinsetCoe.canLift 2 := fun h => by
  obtain ⟨y, -⟩ := (@h Unit (fun _ => Empty) ∅).prf (fun i => absurd i.2 (Finset.notMem_empty _)) trivial
  exact (y ()).elim

-- `Finset.PiFinsetCoe.canLift'` idx 2: necessary (iota = Unit, alpha = Empty, s = ∅)
theorem w0_87 : ¬ drop0% Finset.PiFinsetCoe.canLift' 2 := fun h => by
  obtain ⟨y, -⟩ := (@h Unit Empty ∅).prf (fun i => absurd i.2 (Finset.notMem_empty _)) trivial
  exact (y ()).elim

-- `Finset.Superset.trans` idx 4: necessary (s1 = ∅, s2 = s3 = {0})
theorem w0_88 : ¬ drop0% Finset.Superset.trans 4 := fun h =>
  absurd (@h ℕ ∅ {0} {0} (subset_refl _)) (by decide)

-- `Finset.ssubset_of_subset_of_ssubset` idx 4: necessary (s1 = {0,1}, s2 = ∅, s3 = {0})
theorem w0_89 : ¬ drop0% Finset.ssubset_of_subset_of_ssubset 4 := fun h =>
  absurd (@h ℕ {0, 1} ∅ {0} (by decide)) (by decide)

-- `Finset.exists_between` idx 5: necessary (Unit, s = ∅, t = {()})
theorem w0_90 : ¬ drop0% Finset.exists_between 5 := fun h => by
  obtain ⟨b, -, hb⟩ := @h Unit _ _ ∅ {()} (by simp) (by simp)
  exact (hb () (by simp)).ne (Subsingleton.elim _ _)

-- `Finset.exists_between` idx 6: necessary (Unit, s = {()}, t = ∅)
theorem w0_91 : ¬ drop0% Finset.exists_between 6 := fun h => by
  obtain ⟨b, hb, -⟩ := @h Unit _ _ {()} ∅ (by simp) (by simp)
  exact (hb () (by simp)).ne (Subsingleton.elim _ _)

-- `Finset.exists_between` idx 7: necessary (Unit, s = t = {()})
theorem w0_92 : ¬ drop0% Finset.exists_between 7 := fun h => by
  obtain ⟨b, hb, -⟩ := @h Unit _ _ {()} {()} (by simp) (by simp)
  exact (hb () (by simp)).ne (Subsingleton.elim _ _)

-- `Finset.exists_between'` idx 2: necessary (Int, s = {0}, t = {1})
theorem w0_93 : ¬ drop0% Finset.exists_between' 2 := fun h => by
  obtain ⟨b, h1, h2⟩ := @h ℤ _ {0} {1} _ _ _ (by simp)
  have := h1 0 (by simp); have := h2 1 (by simp); omega

-- `Finset.exists_between'` idx 5: necessary (alpha = order dual of NNRat, s = {toDual 0}, t = ∅)
theorem w0_94 : ¬ drop0% Finset.exists_between' 5 := fun h => by
  obtain ⟨b, hb, -⟩ := @h ℚ≥0ᵒᵈ _ _ {OrderDual.toDual 0} ∅ _ _ (by simp)
  have := hb _ (Finset.mem_singleton_self _)
  exact not_lt_zero' (α := ℚ≥0) this

-- `Finset.exists_between'` idx 6: necessary (NNRat, s = ∅, t = {0})
theorem w0_95 : ¬ drop0% Finset.exists_between' 6 := fun h => by
  obtain ⟨b, -, hb⟩ := @h ℚ≥0 _ _ ∅ {0} _ _ (by simp)
  exact not_lt_zero' (hb 0 (by simp))

-- `Finset.exists_between'` idx 7: necessary (alpha = Empty)
theorem w0_96 : ¬ drop0% Finset.exists_between' 7 := fun h => by
  obtain ⟨b, -⟩ := @h Empty _ _ ∅ ∅ _ _ (by simp)
  exact b.elim

-- `Finset.exists_between'` idx 8: necessary (Rat, s = {1}, t = {0})
theorem w0_97 : ¬ drop0% Finset.exists_between' 8 := fun h => by
  obtain ⟨b, h1, h2⟩ := @h ℚ _ _ {1} {0} _ _ _
  have := h1 1 (by simp); have := h2 0 (by simp); linarith

-- `Set.Finite.exists_between` idx 5: necessary (Rat, s = Iio 0, t = {0})
theorem w0_98 : ¬ drop0% Set.Finite.exists_between 5 := fun h => by
  obtain ⟨b, h1, h2⟩ := @h ℚ _ _ (Set.Iio 0) {0} ⟨-1, by simp⟩ (Set.finite_singleton _) ⟨0, rfl⟩
    (fun x hx y hy => by simp at hx hy; subst hy; exact hx)
  have := h2 0 rfl
  exact lt_irrefl _ (h1 b this)

-- `Set.Finite.exists_between` idx 6: necessary (Unit, s = ∅, t = {()})
theorem w0_99 : ¬ drop0% Set.Finite.exists_between 6 := fun h => by
  obtain ⟨b, -, hb⟩ := @h Unit _ _ ∅ {()} Set.finite_empty (Set.finite_singleton _) ⟨(), rfl⟩ (by simp)
  exact (hb () rfl).ne (Subsingleton.elim _ _)

-- `Set.Finite.exists_between` idx 7: necessary (Rat, s = {0}, t = Ioi 0)
theorem w0_100 : ¬ drop0% Set.Finite.exists_between 7 := fun h => by
  obtain ⟨b, h1, h2⟩ := @h ℚ _ _ {0} (Set.Ioi 0) (Set.finite_singleton _) ⟨0, rfl⟩ ⟨1, by simp⟩
    (fun x hx y hy => by simp at hx hy; subst hx; exact hy)
  have := h1 0 rfl
  exact lt_irrefl _ (h2 b this)

-- `Set.Finite.exists_between` idx 8: necessary (Unit, s = {()}, t = ∅)
theorem w0_101 : ¬ drop0% Set.Finite.exists_between 8 := fun h => by
  obtain ⟨b, hb, -⟩ := @h Unit _ _ {()} ∅ (Set.finite_singleton _) ⟨(), rfl⟩ Set.finite_empty (by simp)
  exact (hb () rfl).ne (Subsingleton.elim _ _)

-- `Set.Finite.exists_between` idx 9: necessary (Unit, s = t = {()})
theorem w0_102 : ¬ drop0% Set.Finite.exists_between 9 := fun h => by
  obtain ⟨b, hb, -⟩ := @h Unit _ _ {()} {()} (Set.finite_singleton _) ⟨(), rfl⟩ (Set.finite_singleton _)
    ⟨(), rfl⟩
  exact (hb () rfl).ne (Subsingleton.elim _ _)

-- `Set.Finite.exists_between'` idx 2: necessary (Int, s = {0}, t = {1})
theorem w0_103 : ¬ drop0% Set.Finite.exists_between' 2 := fun h => by
  obtain ⟨b, h1, h2⟩ := @h ℤ _ _ _ _ {0} {1} (Set.finite_singleton _) (Set.finite_singleton _)
    (fun x hx y hy => by simp at hx hy; omega)
  have := h1 0 rfl; have := h2 1 rfl; omega

-- `Set.Finite.exists_between'` idx 3: necessary (order dual of NNRat, s = {toDual 0}, t = ∅)
theorem w0_104 : ¬ drop0% Set.Finite.exists_between' 3 := fun h => by
  obtain ⟨b, hb, -⟩ := @h ℚ≥0ᵒᵈ _ _ _ _ {OrderDual.toDual 0} ∅ (Set.finite_singleton _) Set.finite_empty
    (by simp)
  exact not_lt_zero' (α := ℚ≥0) (hb _ rfl)

-- `Set.Finite.exists_between'` idx 4: necessary (NNRat, s = ∅, t = {0})
theorem w0_105 : ¬ drop0% Set.Finite.exists_between' 4 := fun h => by
  obtain ⟨b, -, hb⟩ := @h ℚ≥0 _ _ _ _ ∅ {0} Set.finite_empty (Set.finite_singleton _) (by simp)
  exact not_lt_zero' (hb 0 rfl)

-- `Set.Finite.exists_between'` idx 5: necessary (alpha = Empty)
theorem w0_106 : ¬ drop0% Set.Finite.exists_between' 5 := fun h => by
  obtain ⟨b, -⟩ := @h Empty _ _ _ _ ∅ ∅ Set.finite_empty Set.finite_empty (by simp)
  exact b.elim

-- `Set.Finite.exists_between'` idx 8: necessary (Rat, s = univ, t = ∅)
theorem w0_107 : ¬ drop0% Set.Finite.exists_between' 8 := fun h => by
  obtain ⟨b, hb, -⟩ := @h ℚ _ _ _ _ _ Set.univ ∅ Set.finite_empty (by simp)
  exact lt_irrefl _ (hb b trivial)

-- `Set.Finite.exists_between'` idx 9: necessary (Rat, s = ∅, t = univ)
theorem w0_108 : ¬ drop0% Set.Finite.exists_between' 9 := fun h => by
  obtain ⟨b, -, hb⟩ := @h ℚ _ _ _ _ _ ∅ Set.univ Set.finite_empty (by simp)
  exact lt_irrefl _ (hb b trivial)

-- `Set.Finite.exists_between'` idx 10: necessary (Rat, s = {1}, t = {0})
theorem w0_109 : ¬ drop0% Set.Finite.exists_between' 10 := fun h => by
  obtain ⟨b, h1, h2⟩ := @h ℚ _ _ _ _ _ {1} {0} (Set.finite_singleton _) (Set.finite_singleton _)
  have := h1 1 rfl; have := h2 0 rfl; linarith

-- `Finset.dens_image` idx 6: necessary (Bool, f = const false, s = univ)
theorem w0_110 : ¬ drop0% Finset.dens_image 6 := fun h => by
  have := @h Bool Bool _ _ _ (fun _ => false) Finset.univ
  simp [Finset.dens] at this

-- `Finset.natCast_card_mul_nnratCast_dens` idx 4: necessary (ZMod 2, Bool, s = {true})
theorem w0_111 : ¬ drop0% Finset.natCast_card_mul_nnratCast_dens 4 := fun h => by
  have := @h (ZMod 2) Bool _ z2F.toSemifield {true}
  rw [Fintype.card_bool, Finset.card_singleton] at this
  rw [z2_two, zero_mul, Nat.cast_one] at this
  exact zero_ne_one this

-- `Finset.nnratCast_dens_mul_natCast_card` idx 4: necessary (ZMod 2, Bool, s = {true})
theorem w0_112 : ¬ drop0% Finset.nnratCast_dens_mul_natCast_card 4 := fun h => by
  have := @h (ZMod 2) Bool _ z2F.toSemifield {true}
  rw [Fintype.card_bool, Finset.card_singleton] at this
  rw [z2_two, mul_zero, Nat.cast_one] at this
  exact zero_ne_one this

-- `Finset.nnratCast_dens` idx 4: necessary (ZMod 2, Bool, s = univ: 1 vs 2/2 = 0)
theorem w0_113 : ¬ drop0% Finset.nnratCast_dens 4 := fun h => by
  have := @h (ZMod 2) Bool _ z2F.toSemifield Finset.univ
  rw [Finset.dens_univ, Finset.card_univ, Fintype.card_bool, z2_two] at this
  simp only [NNRat.cast_one] at this
  exact @one_ne_zz (ZMod 2) z2F.toSemifield _ this

-- `Finset.dens_univ` idx 2: necessary (alpha = Empty)
theorem w0_114 : ¬ drop0% Finset.dens_univ 2 := fun h => by
  have := @h Empty _
  rw [Finset.univ_eq_empty, Finset.dens_empty] at this
  exact zero_ne_one this

-- `Finset.dens_eq_one` idx 3: necessary (alpha = Empty)
theorem w0_115 : ¬ drop0% Finset.dens_eq_one 3 := fun h => by
  have := (@h Empty _ ∅).2 (Subsingleton.elim _ _)
  rw [Finset.dens_empty] at this
  exact zero_ne_one this

-- `Finset.dens_ne_one` idx 3: necessary (alpha = Empty)
theorem w0_116 : ¬ drop0% Finset.dens_ne_one 3 := fun h =>
  (@h Empty _ ∅).1 (by rw [Finset.dens_empty]; exact zero_ne_one) (Subsingleton.elim _ _)

-- `Finset.disjoint_of_subset_left` idx 5: necessary (s = t = u = {0})
theorem w0_117 : ¬ drop0% Finset.disjoint_of_subset_left 5 := fun h =>
  absurd (@h ℕ {0} {0} {0} (subset_refl _)) (by decide)

-- `Finset.disjoint_of_subset_right` idx 5: necessary (s = t = u = {0})
theorem w0_118 : ¬ drop0% Finset.disjoint_of_subset_right 5 := fun h =>
  absurd (@h ℕ {0} {0} {0} (subset_refl _)) (by decide)

-- `Finset.Nonempty.mono` idx 3: necessary (s = {0}, t = ∅)
theorem w0_119 : ¬ drop0% Finset.Nonempty.mono 3 := fun h =>
  absurd (@h ℕ {0} ∅ (by simp)) (by simp)

-- `Finset.Nonempty.to_type` idx 2: necessary (alpha = Empty)
theorem w0_120 : ¬ drop0% Finset.Nonempty.to_type 2 := fun h =>
  (@h Empty ∅).elim (fun x => x.elim)

-- `Finset.mem_erase_of_ne_of_mem` idx 5: necessary (a = b = 0, s = {0})
theorem w0_121 : ¬ drop0% Finset.mem_erase_of_ne_of_mem 5 := fun h =>
  absurd (@h ℕ _ {0} 0 0 (by simp)) (by decide)

-- `Finset.subset_coe_filter_of_subset_forall` idx 6: necessary (p = False, s = t = {0})
theorem w0_122 : ¬ drop0% Finset.subset_coe_filter_of_subset_forall 6 := fun h => by
  have := @h ℕ (fun _ => False) _ {0} {0} (by simp) 0 (Set.mem_singleton 0)
  simp at this

-- `Finset.disjoint_filter_filter` idx 7: necessary (s = t = {0}, p = q = True)
theorem w0_123 : ¬ drop0% Finset.disjoint_filter_filter 7 := fun h =>
  absurd (@h ℕ {0} {0} (fun _ => True) (fun _ => True) _ _) (by decide)

namespace W1c0
def succE : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
/-- Addition on ℕ as a named operation with its law instances. -/
def ad (a b : ℕ) : ℕ := a + b
instance adC : Std.Commutative ad := ⟨Nat.add_comm⟩
instance adA : Std.Associative ad := ⟨Nat.add_assoc⟩
end W1c0

-- `Finset.mem_attachFin` idx 2: necessary (n = 1, s = {1})
theorem w0_124 : ¬ indep0% Finset.mem_attachFin 2 := fun h =>
  absurd (@h 1 {1} 0 1 (by simp)) (by decide)

-- `Finset.coe_attachFin` idx 2: necessary (n = 0, s = {0})
theorem w0_125 : ¬ indep0% Finset.coe_attachFin 2 := fun h =>
  absurd (@h 0 {0} 0 (by simp)) (by decide)

-- `Finset.card_attachFin` idx 2: necessary (n = 0, s = {0})
theorem w0_126 : ¬ indep0% Finset.card_attachFin 2 := fun h =>
  absurd (@h 0 {0} 0 (by simp)) (by decide)

-- `Finset.image_val_attachFin` idx 2: necessary (n = 0, s = {0})
theorem w0_127 : ¬ indep0% Finset.image_val_attachFin 2 := fun h =>
  absurd (@h 0 {0} 0 (by simp)) (by decide)

-- `Finset.map_valEmbedding_attachFin` idx 2: necessary (n = 0, s = {0})
theorem w0_128 : ¬ indep0% Finset.map_valEmbedding_attachFin 2 := fun h =>
  absurd (@h 0 {0} 0 (by simp)) (by decide)

-- `Finset.attachFin_subset_attachFin_iff` idx 3: necessary (n = 0, s = {0}, t = ∅)
theorem w0_129 : ¬ indep0% Finset.attachFin_subset_attachFin_iff 3 := fun h =>
  absurd (@h 0 {0} ∅ (by simp) 0 (by simp)) (by decide)

-- `Finset.attachFin_subset_attachFin_iff` idx 4: necessary (n = 0, s = ∅, t = {0})
theorem w0_130 : ¬ indep0% Finset.attachFin_subset_attachFin_iff 4 := fun h =>
  absurd (@h 0 ∅ {0} (by simp) 0 (by simp)) (by decide)

-- `Finset.attachFin_subset_attachFin` idx 3: necessary (n = 0, s = {0}, t = ∅)
theorem w0_131 : ¬ indep0% Finset.attachFin_subset_attachFin 3 := fun h =>
  absurd (@h 0 {0} ∅ (by simp)) (by decide)

-- `Finset.attachFin_subset_attachFin` idx 4: necessary (n = 0, s = ∅, t = {0})
theorem w0_132 : ¬ indep0% Finset.attachFin_subset_attachFin 4 := fun h =>
  absurd (@h 0 ∅ {0} (by simp) 0 (by simp)) (by decide)

-- `Finset.attachFin_ssubset_attachFin_iff` idx 3: necessary (n = 0, s = {0}, t = ∅)
theorem w0_133 : ¬ indep0% Finset.attachFin_ssubset_attachFin_iff 3 := fun h =>
  absurd (@h 0 {0} ∅ (by simp) 0 (by simp)) (by decide)

-- `Finset.attachFin_ssubset_attachFin_iff` idx 4: necessary (n = 0, s = ∅, t = {0})
theorem w0_134 : ¬ indep0% Finset.attachFin_ssubset_attachFin_iff 4 := fun h =>
  absurd (@h 0 ∅ {0} (by simp) 0 (by simp)) (by decide)

-- `Finset.attachFin_ssubset_attachFin` idx 4: necessary (n = 0, s = ∅, t = {0})
theorem w0_135 : ¬ indep0% Finset.attachFin_ssubset_attachFin 4 := fun h =>
  absurd (@h 0 ∅ {0} (by decide) 0 (by simp)) (by decide)

-- `Finset.fold_insert` idx 10: necessary (op = +, s = {0}, a = 0, f = 1)
theorem w0_136 : ¬ drop0% Finset.fold_insert 10 := fun h =>
  absurd (@h ℕ ℕ (· + ·) _ _ (fun _ => 1) 0 {0} 0 _) (by decide)

-- `Finset.fold_map` idx 4: necessary (op = left projection)
theorem w0_137 : ¬ indep0% Finset.fold_map 4 := fun h =>
  lp_not_comm (@h ℕ ℕ ℕ lp lpA id 0 (Function.Embedding.refl ℕ) ∅)

-- `Finset.fold_map` idx 5: necessary (op = midpoint on Rat)
theorem w0_138 : ¬ indep0% Finset.fold_map 5 := fun h =>
  md_not_assoc (@h ℕ ℚ ℕ md mdC (fun _ => 0) 0 (Function.Embedding.refl ℕ) ∅)

-- `Finset.fold_image` idx 4: necessary (op = left projection, s = ∅)
theorem w0_139 : ¬ indep0% Finset.fold_image 4 := fun h =>
  lp_not_comm (@h ℕ ℕ ℕ lp lpA id 0 _ id ∅ (by simp))

-- `Finset.fold_image` idx 11: necessary (op = +, g = 0, s = {0,1}, f = 1)
theorem w0_140 : ¬ drop0% Finset.fold_image 11 := fun h =>
  absurd (@h ℕ ℕ ℕ (· + ·) _ _ (fun _ => 1) 0 _ (fun _ => 0) {0, 1}) (by decide)

-- `Finset.fold_congr` idx 3: necessary (op = left projection)
theorem w0_141 : ¬ indep0% Finset.fold_congr 3 := fun h =>
  lp_not_comm (@h ℕ ℕ lp lpA id 0 ∅ id (by simp))

-- `Finset.fold_congr` idx 9: necessary (op = +, f = 0, g = 1, s = {0})
theorem w0_142 : ¬ drop0% Finset.fold_congr 9 := fun h =>
  absurd (@h ℕ ℕ (· + ·) _ _ (fun _ => 0) 0 {0} (fun _ => 1)) (by decide)

-- `Finset.fold_const` idx 9: necessary (op = +, b = 0, c = 1, s = {0,1})
theorem w0_143 : ¬ drop0% Finset.fold_const 9 := fun h =>
  absurd (@h ℕ ℕ (· + ·) _ _ 0 {0, 1} _ 1) (by decide)

-- `Finset.fold_hom` idx 4: necessary (op = left projection, op' = +, m = 0)
theorem w0_144 : ¬ indep0% Finset.fold_hom 4 := fun h =>
  lp_not_comm (@h ℕ ℕ ℕ lp lpA id 0 ∅ ad adC adA (fun _ => 0) (fun _ _ => rfl))

-- `Finset.fold_hom` idx 5: necessary (op = midpoint, op' = +, m = 0)
theorem w0_145 : ¬ indep0% Finset.fold_hom 5 := fun h =>
  md_not_assoc (@h ℕ ℚ ℕ md mdC (fun _ => 0) 0 ∅ ad adC adA (fun _ => 0) (fun _ _ => rfl))

-- `Finset.fold_hom` idx 10: necessary (op = +, op' = left projection, m = 0)
theorem w0_146 : ¬ indep0% Finset.fold_hom 10 := fun h =>
  lp_not_comm (@h ℕ ℕ ℕ ad adC adA id 0 ∅ lp lpA (fun _ => 0) (fun _ _ => rfl))

-- `Finset.fold_hom` idx 11: necessary (op = +, op' = midpoint, m = 0)
theorem w0_147 : ¬ indep0% Finset.fold_hom 11 := fun h =>
  md_not_assoc (@h ℕ ℕ ℚ ad adC adA id 0 ∅ md mdC (fun _ => 0) (fun _ _ => by simp [md]))

-- `Finset.fold_hom` idx 13: necessary (op = op' = +, m = succ, s = {0})
theorem w0_148 : ¬ drop0% Finset.fold_hom 13 := fun h =>
  absurd (@h ℕ ℕ ℕ (· + ·) _ _ (fun _ => 0) 0 {0} (· + ·) _ _ Nat.succ) (by decide)

-- `Finset.fold_disjUnion` idx 10: necessary (s1 = s2 = {0})
theorem w0_149 : ¬ indep0% Finset.fold_disjUnion 10 := fun h =>
  absurd (@h ℕ ℕ (· + ·) _ _ id {0} {0} 0 0) (by decide)

-- `Finset.fold_insert_idem` idx 4: necessary (op = midpoint)
theorem w0_150 : ¬ indep0% Finset.fold_insert_idem 4 := fun h =>
  md_not_assoc (@h ℕ ℚ md mdC (fun _ => 0) 0 ∅ 0 _ mdI)

-- `Finset.fold_insert_idem` idx 10: necessary (op = +, s = {0}, a = 0, f = 1)
theorem w0_151 : ¬ drop0% Finset.fold_insert_idem 10 := fun h =>
  absurd (@h ℕ ℕ (· + ·) _ _ (fun _ => 1) 0 {0} 0 _) (by decide)

-- `Finset.fold_image_idem` idx 5: necessary (op = midpoint)
theorem w0_152 : ¬ indep0% Finset.fold_image_idem 5 := fun h =>
  md_not_assoc (@h ℕ ℚ ℕ md mdC (fun _ => 0) 0 _ id ∅ mdI)

-- `Finset.fold_image_idem` idx 11: necessary (op = +, g = 0, s = {0,1}, f = 1)
theorem w0_153 : ¬ drop0% Finset.fold_image_idem 11 := fun h =>
  absurd (@h ℕ ℕ ℕ (· + ·) _ _ (fun _ => 1) 0 _ (fun _ => 0) {0, 1}) (by decide)

-- `Finset.fold_ite'` idx 9: necessary (op = +, b = 1, s = ∅)
theorem w0_154 : ¬ drop0% Finset.fold_ite' 9 := fun h =>
  absurd (@h ℕ ℕ (· + ·) _ _ id 1 ∅ id (fun _ => True) _) (by decide)

-- `Finset.fold_ite` idx 4: necessary (op = midpoint)
theorem w0_155 : ¬ indep0% Finset.fold_ite 4 := fun h =>
  md_not_assoc (@h ℕ ℚ md mdC (fun _ => 0) 0 ∅ mdI (fun _ => 0) (fun _ => True) _)

-- `Finset.fold_ite` idx 8: necessary (op = +, b = 1, s = ∅)
theorem w0_156 : ¬ drop0% Finset.fold_ite 8 := fun h =>
  absurd (@h ℕ ℕ (· + ·) _ _ id 1 ∅ id (fun _ => True) _) (by decide)

-- `Finset.fold_op_rel_iff_and` idx 3: necessary (op = left projection, r = True)
theorem w0_157 : ¬ indep0% Finset.fold_op_rel_iff_and 3 := fun h =>
  lp_not_comm (@h ℕ ℕ lp lpA id 0 ∅ (fun _ _ => True) (fun {_ _ _} => by simp) 0)

-- `Finset.fold_op_rel_iff_and` idx 4: necessary (op = midpoint, r = True)
theorem w0_158 : ¬ indep0% Finset.fold_op_rel_iff_and 4 := fun h =>
  md_not_assoc (@h ℕ ℚ md mdC (fun _ => 0) 0 ∅ (fun _ _ => True) (fun {_ _ _} => by simp) 0)

-- `Finset.fold_op_rel_iff_and` idx 9: necessary (op = +, f = 1, b = 0, s = {0}, r x y = (y = 1))
theorem w0_159 : ¬ drop0% Finset.fold_op_rel_iff_and 9 := fun h =>
  absurd (@h ℕ ℕ (· + ·) _ _ (fun _ => 1) 0 {0} (fun _ y => y = 1) 0) (by decide)

-- `Finset.fold_op_rel_iff_or` idx 3: necessary (op = left projection, r = False)
theorem w0_160 : ¬ indep0% Finset.fold_op_rel_iff_or 3 := fun h =>
  lp_not_comm (@h ℕ ℕ lp lpA id 0 ∅ (fun _ _ => False) (fun {_ _ _} => by simp) 0)

-- `Finset.fold_op_rel_iff_or` idx 4: necessary (op = midpoint, r = False)
theorem w0_161 : ¬ indep0% Finset.fold_op_rel_iff_or 4 := fun h =>
  md_not_assoc (@h ℕ ℚ md mdC (fun _ => 0) 0 ∅ (fun _ _ => False) (fun {_ _ _} => by simp) 0)

-- `Finset.fold_op_rel_iff_or` idx 9: necessary (op = +, f = 1, b = 1, s = {0}, r x y = (y = 1))
theorem w0_162 : ¬ drop0% Finset.fold_op_rel_iff_or 9 := fun h =>
  absurd (@h ℕ ℕ (· + ·) _ _ (fun _ => 1) 1 {0} (fun _ y => y = 1) 0) (by decide)

-- `Finset.map_traverse` idx 5: necessary (G = StateM Nat: get and set 1 do not commute)
theorem w0_163 : ¬ indep0% Finset.map_traverse 5 := fun h => by
  have c := @h ℕ ℕ ℕ (StateM ℕ) _ (fun _ => pure 0) id ∅
  have := congrArg (fun x => (x.run 0).1) (c.commutative_prod (get : StateM ℕ ℕ) (set 1 : StateM ℕ PUnit))
  revert this
  decide

-- `WCovBy.finset_val` idx 3: necessary (s = ∅, t = {0,1}, c = {0})
theorem w0_164 : ¬ drop0% WCovBy.finset_val 3 := fun h =>
  (@h ℕ ∅ {0, 1}).2 (c := ({0} : Finset ℕ).val) (Finset.val_lt_iff.2 (by decide))
    (Finset.val_lt_iff.2 (by decide))

-- `WCovBy.finset_coe` idx 3: necessary (s = ∅, t = {0,1}, c = {0})
theorem w0_165 : ¬ drop0% WCovBy.finset_coe 3 := fun h =>
  (@h ℕ ∅ {0, 1}).2 (c := ((({0} : Finset ℕ)) : Set ℕ)) (Finset.coe_ssubset.2 (by decide))
    (Finset.coe_ssubset.2 (by decide))

-- `Finset.map_cast_heq` idx 2: necessary (alpha = Unit, beta = Empty)
theorem w0_166 : ¬ indep0% Finset.map_cast_heq 2 := fun h => (cast (@h Unit Empty ∅) ()).elim

-- `Finset.map_comm` idx 9: necessary (f = g = f' = id, g' = succ, s = {0})
theorem w0_167 : ¬ drop0% Finset.map_comm 9 := fun h => by
  have := @h ℕ ℕ ℕ {0} ℕ (Function.Embedding.refl ℕ) (Function.Embedding.refl ℕ)
    (Function.Embedding.refl ℕ) succE
  simp [succE] at this

-- `Function.Semiconj.finset_map` idx 5: necessary (f = ga = id, gb = succ, x = {0})
theorem w0_168 : ¬ drop0% Function.Semiconj.finset_map 5 := fun h => by
  have := @h ℕ ℕ (Function.Embedding.refl ℕ) (Function.Embedding.refl ℕ) succE {0}
  simp [succE] at this

-- `Function.Commute.finset_map` idx 3: necessary (f = succ, g = swap 0 1, x = {0})
theorem w0_169 : ¬ drop0% Function.Commute.finset_map 3 := fun h => by
  have := @h ℕ succE (Equiv.swap 0 1).toEmbedding {0}
  simp [succE] at this

-- `Finset.canLift` idx 5: necessary (alpha = Empty, beta = Unit)
theorem w0_170 : ¬ drop0% Finset.canLift 5 := fun h => by
  obtain ⟨y, hy⟩ := (@h Empty Unit _ Empty.elim (fun _ => True)).prf {()} (by simp)
  rw [Finset.eq_empty_of_forall_notMem (s := y) (fun x => x.elim)] at hy
  simp at hy

-- `Finset.image_comm` idx 12: necessary (f = g = f' = id, g' = succ, s = {0})
theorem w0_171 : ¬ drop0% Finset.image_comm 12 := fun h =>
  absurd (@h ℕ ℕ ℕ _ {0} ℕ _ _ id id id Nat.succ) (by decide)

-- `Function.Semiconj.finset_image` idx 7: necessary (f = ga = id, gb = succ, x = {0})
theorem w0_172 : ¬ drop0% Function.Semiconj.finset_image 7 := fun h =>
  absurd (@h ℕ ℕ _ _ id id Nat.succ {0}) (by decide)

-- `Function.Commute.finset_image` idx 4: necessary (f = succ, g = 0, x = {0})
theorem w0_173 : ¬ drop0% Function.Commute.finset_image 4 := fun h =>
  absurd (@h ℕ _ Nat.succ (fun _ => 0) {0}) (by decide)

-- `Finset.image_inj` idx 6: necessary (f = 0, s = {0}, t = {1})
theorem w0_174 : ¬ drop0% Finset.image_inj 6 := fun h =>
  absurd ((@h ℕ ℕ _ (fun _ => 0) {0} {1}).1 (by decide)) (by decide)

-- `Finset.image_subset_image_iff` idx 6: necessary (f = 0, s = {0}, t = {1})
theorem w0_175 : ¬ drop0% Finset.image_subset_image_iff 6 := fun h =>
  absurd ((@h ℕ ℕ _ (fun _ => 0) {0} {1}).1 (by decide)) (by decide)

-- `Finset.image_subset_image_iff_of_injOn` idx 7: necessary (f = 0, s = {0,1}, s1 = {0}, s2 = {1})
theorem w0_176 : ¬ drop0% Finset.image_subset_image_iff_of_injOn 7 := fun h =>
  absurd ((@h ℕ ℕ _ (fun _ => 0) {0, 1} {0} {1} (by decide) (by decide)).1 (by decide)) (by decide)

-- `Finset.image_subset_image_iff_of_injOn` idx 8: necessary (f = (· % 2), s = s2 = {0}, s1 = {2})
theorem w0_177 : ¬ drop0% Finset.image_subset_image_iff_of_injOn 8 := fun h =>
  absurd ((@h ℕ ℕ _ (· % 2) {0} {2} {0} (by simp [Set.InjOn]) (by decide)).1 (by decide)) (by decide)

-- `Finset.image_subset_image_iff_of_injOn` idx 9: necessary (f = (· % 2), s = s1 = {0}, s2 = {2})
theorem w0_178 : ¬ drop0% Finset.image_subset_image_iff_of_injOn 9 := fun h =>
  absurd ((@h ℕ ℕ _ (· % 2) {0} {0} {2} (by simp [Set.InjOn]) (by decide)).1 (by decide)) (by decide)

-- `Finset.image_eq_image_iff_of_injOn` idx 7: necessary (f = 0, s = {0,1}, s1 = {0}, s2 = {1})
theorem w0_179 : ¬ drop0% Finset.image_eq_image_iff_of_injOn 7 := fun h =>
  absurd ((@h ℕ ℕ _ (fun _ => 0) {0, 1} {0} {1} (by decide) (by decide)).1 (by decide)) (by decide)

-- `Finset.image_eq_image_iff_of_injOn` idx 8: necessary (f = (· % 2), s = s2 = {0}, s1 = {2})
theorem w0_180 : ¬ drop0% Finset.image_eq_image_iff_of_injOn 8 := fun h =>
  absurd ((@h ℕ ℕ _ (· % 2) {0} {2} {0} (by simp [Set.InjOn]) (by decide)).1 (by decide)) (by decide)

-- `Finset.image_eq_image_iff_of_injOn` idx 9: necessary (f = (· % 2), s = s1 = {0}, s2 = {2})
theorem w0_181 : ¬ drop0% Finset.image_eq_image_iff_of_injOn 9 := fun h =>
  absurd ((@h ℕ ℕ _ (· % 2) {0} {0} {2} (by simp [Set.InjOn]) (by decide)).1 (by decide)) (by decide)

-- `Finset.image_ssubset_image` idx 6: necessary (f = 0, s = {0}, t = {0,1})
theorem w0_182 : ¬ drop0% Finset.image_ssubset_image 6 := fun h =>
  absurd ((@h ℕ ℕ _ (fun _ => 0) {0} {0, 1}).2 (by decide)) (by decide)

-- `Finset.image_inter_of_injOn` idx 7: necessary (f = 0, s = {0}, t = {1})
theorem w0_183 : ¬ drop0% Finset.image_inter_of_injOn 7 := fun h =>
  absurd (@h ℕ ℕ _ _ (fun _ => 0) {0} {1}) (by decide)

-- `Finset.image_inter` idx 7: necessary (f = 0, s1 = {0}, s2 = {1})
theorem w0_184 : ¬ drop0% Finset.image_inter 7 := fun h =>
  absurd (@h ℕ ℕ _ (fun _ => 0) _ {0} {1}) (by decide)

-- `Finset.image_sdiff` idx 7: necessary (f = 0, s = {0}, t = {1})
theorem w0_185 : ¬ drop0% Finset.image_sdiff 7 := fun h =>
  absurd (@h ℕ ℕ _ _ (fun _ => 0) {0} {1}) (by decide)

-- `Finset.image_sdiff_of_injOn` idx 7: necessary (f = 0, s = {0,1}, t = {1})
theorem w0_186 : ¬ drop0% Finset.image_sdiff_of_injOn 7 := fun h =>
  absurd (@h ℕ ℕ _ (fun _ => 0) {0, 1} _ {1} (by decide)) (by decide)

-- `Finset.image_sdiff_of_injOn` idx 8: necessary (f = 0, s = {0}, t = {1})
theorem w0_187 : ¬ drop0% Finset.image_sdiff_of_injOn 8 := fun h =>
  absurd (@h ℕ ℕ _ (fun _ => 0) {0} _ {1} (by simp [Set.InjOn])) (by decide)

-- `Finset.mem_range_iff_mem_finset_range_of_mod_eq` idx 6: necessary (f = id, n = 1, a = 5)
theorem w0_188 : ¬ drop0% Finset.mem_range_iff_mem_finset_range_of_mod_eq 6 := fun h => by
  have := (@h ℤ _ id 5 1 (by decide)).1 ⟨5, rfl⟩
  simp at this

-- `Finset.filterMap_mono` idx 6: necessary (f = some, s = {0}, t = ∅)
theorem w0_189 : ¬ drop0% Finset.filterMap_mono 6 := fun h => by
  have := @h ℕ ℕ some {0} ∅ (by simp) 0 ((Finset.mem_filterMap _).2 ⟨0, by simp, rfl⟩)
  simp at this

-- `Finset.notMem_map_subtype_of_not_property` idx 4: necessary (p = True, s = {0})
theorem w0_190 : ¬ drop0% Finset.notMem_map_subtype_of_not_property 4 := fun h =>
  @h ℕ (fun _ => True) {⟨0, trivial⟩} 0 (by simp)

-- `Finset.equivOfEq_symm_apply_coe` idx 3: necessary (s = ∅, t = {0})
theorem w0_191 : ¬ indep0% Finset.equivOfEq_symm_apply_coe 3 := fun h =>
  absurd (@h ℕ ∅ {0} ⟨0, by simp⟩) (by decide)

-- `Finset.equivOfEq_apply_coe` idx 3: necessary (s = {0}, t = ∅)
theorem w0_192 : ¬ indep0% Finset.equivOfEq_apply_coe 3 := fun h =>
  absurd (@h ℕ {0} ∅ ⟨0, by simp⟩) (by decide)

-- `Equiv.Finset.congr_apply_coe` idx 3: necessary (s = {0}, t = ∅)
theorem w0_193 : ¬ indep0% Equiv.Finset.congr_apply_coe 3 := fun h =>
  absurd (@h ℕ {0} ∅ ⟨0, by simp⟩) (by decide)

-- `Equiv.Finset.congr_symm_apply_coe` idx 3: necessary (s = ∅, t = {0})
theorem w0_194 : ¬ indep0% Equiv.Finset.congr_symm_apply_coe 3 := fun h =>
  absurd (@h ℕ ∅ {0} ⟨0, by simp⟩) (by decide)

open scoped Pointwise

-- `Finset.mem_finsupp_iff_of_support_subset` idx 6: necessary (Unit, s = ∅, f = 0, t = single () {1}, pointwise Zero)
theorem w0_195 : ¬ drop0% Finset.mem_finsupp_iff_of_support_subset 6 := fun h => by
  have := @h Unit ℕ _ ∅ 0 (Finsupp.single () {1})
  simp [Finset.finsupp, Finsupp.ext_iff, Finsupp.indicator_apply] at this
