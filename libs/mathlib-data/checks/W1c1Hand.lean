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

namespace W1c1
open Finsupp

/-- rotated order on Fin 3: rank 1 < 0 < 2, so 0 ≤ 2 but 2 + 2 = 1 < 0 -/
def W := Fin 3
instance : AddCommMonoid W := inferInstanceAs (AddCommMonoid (Fin 3))
instance : DecidableEq W := inferInstanceAs (DecidableEq (Fin 3))
instance : Fintype W := inferInstanceAs (Fintype (Fin 3))
def rk : W → ℕ := fun x : Fin 3 => if x = 0 then 1 else if x = 1 then 0 else 2
theorem rk_inj : Function.Injective rk := by decide +kernel
instance : PartialOrder W := PartialOrder.lift rk rk_inj
instance : DecidableLE W := fun a b => inferInstanceAs (Decidable (rk a ≤ rk b))
def w1 : W := (1 : Fin 3)
def w2 : W := (2 : Fin 3)
theorem w0_le_w2 : (0 : W) ≤ w2 := by decide +kernel
theorem w1_le_w0 : w1 ≤ (0 : W) := by decide +kernel
theorem w22 : w2 + w2 = w1 := by decide +kernel
theorem w11 : w1 + w1 = w2 := by decide +kernel
theorem not_w0_le_w1 : ¬ (0 : W) ≤ w1 := by decide +kernel
theorem not_w2_le_w0 : ¬ w2 ≤ (0 : W) := by decide +kernel
theorem not_w2_le_w1 : ¬ w2 ≤ w1 := by decide +kernel
theorem w2_ne : w2 ≠ 0 := by decide +kernel
theorem w1_ne : w1 ≠ 0 := by decide +kernel
theorem two_smul_w2 : (2 : ℕ) • w2 = w1 := by decide +kernel
theorem one_smul_w2 : (1 : ℕ) • w2 = w2 := by decide +kernel
theorem two_smul_fin2 : (2 : ℕ) • (single () (1 : Fin 2)) = 0 := by
  rw [Finsupp.smul_single]; rw [show (2:ℕ) • (1 : Fin 2) = 0 by decide]; simp

/-- two-point finsupp on Bool -/
theorem p2_sum {M N : Type} [AddCommMonoid M] [AddCommMonoid N] (a b : M) (ha : a ≠ 0) (hb : b ≠ 0)
    (g : Bool → M → N) : (single true a + single false b).sum g = g true a + g false b := by
  have hs : (single true a + single false b).support = Finset.univ := by
    ext x; cases x <;> simp [ha, hb]
  rw [Finsupp.sum, hs, Fintype.sum_bool]; simp

end W1c1
open Finsupp W1c1

-- `Finsupp.card_Iic` idx 4: necessary (alpha = (Fin 2)ᵒᵈ: 0 is the top)
theorem c1_1 : ¬ indep0% Finsupp.card_Iic 4 := fun h => by
  have := (@h Unit (Fin 2)ᵒᵈ _ _ _ _ _ _ 0).isBot_zero (OrderDual.toDual (1 : Fin 2))
  exact absurd this (by decide)

-- `Finsupp.card_Iio` idx 4: necessary (alpha = (Fin 2)ᵒᵈ: 0 is the top)
theorem c1_2 : ¬ indep0% Finsupp.card_Iio 4 := fun h => by
  have := (@h Unit (Fin 2)ᵒᵈ _ _ _ _ _ _ 0).isBot_zero (OrderDual.toDual (1 : Fin 2))
  exact absurd this (by decide)

-- `Finsupp.sum_id_lt_of_lt` idx 3: necessary (m = n = 0)
theorem c1_3 : ¬ drop0% Finsupp.sum_id_lt_of_lt 3 := fun h => by
  have := @h Unit 0 0; simp at this

-- `Finsupp.subset_mapRange_neLocus` idx 11: necessary (F = const 1)
theorem c1_4 : ¬ indep0% Finsupp.subset_mapRange_neLocus 11 := fun h => by
  have := @h Unit ℕ ℕ _ _ _ _ _ 0 0 (fun _ => 1); simp at this

-- `Finsupp.zipWith_neLocus_eq_left` idx 11: necessary (F f g = g + 1 is injective in g, F 0 0 = 1)
theorem c1_5 : ¬ indep0% Finsupp.zipWith_neLocus_eq_left 11 := fun h => by
  have := @h Unit ℕ ℕ ℕ _ _ _ _ _ _ (fun _ g => g + 1) 0 0 0 (fun _ _ _ h => by simpa using h); simp at this

-- `Finsupp.zipWith_neLocus_eq_left` idx 15: necessary (F = 0, g1 = 0, g2 = single 1)
theorem c1_6 : ¬ drop0% Finsupp.zipWith_neLocus_eq_left 15 := fun h => by
  have := @h Unit ℕ ℕ ℕ _ _ _ _ _ _ (fun _ _ => 0) rfl 0 0 (single () 1)
  have h2 := congrArg (fun s => () ∈ s) this
  simp at h2

-- `Finsupp.zipWith_neLocus_eq_right` idx 11: necessary (F f g = f + 1)
theorem c1_7 : ¬ indep0% Finsupp.zipWith_neLocus_eq_right 11 := fun h => by
  have := @h Unit ℕ ℕ ℕ _ _ _ _ _ _ (fun f _ => f + 1) 0 0 0 (fun _ _ _ h => by simpa using h); simp at this

-- `Finsupp.zipWith_neLocus_eq_right` idx 15: necessary (F = 0, f1 = 0, f2 = single 1)
theorem c1_8 : ¬ drop0% Finsupp.zipWith_neLocus_eq_right 15 := fun h => by
  have := @h Unit ℕ ℕ ℕ _ _ _ _ _ _ (fun _ _ => 0) rfl 0 (single () 1) 0
  have h2 := congrArg (fun s => () ∈ s) this
  simp at h2

-- `Finsupp.mapRange_neLocus_eq` idx 11: necessary (F = succ)
theorem c1_9 : ¬ indep0% Finsupp.mapRange_neLocus_eq 11 := fun h => by
  have := @h Unit ℕ ℕ _ _ _ _ _ 0 0 Nat.succ Nat.succ_injective; simp at this

-- `Finsupp.mapRange_neLocus_eq` idx 12: necessary (F = 0, f = 0, g = single 1)
theorem c1_10 : ¬ drop0% Finsupp.mapRange_neLocus_eq 12 := fun h => by
  have := @h Unit ℕ ℕ _ _ _ _ _ 0 (single () 1) (fun _ => 0) rfl
  have h2 := congrArg (fun s => () ∈ s) this
  simp at h2

-- `Finsupp.sum_option_index` idx 7: necessary (N = ENat, b = const top is additive, f = 0)
theorem c1_11 : ¬ drop0% Finsupp.sum_option_index 7 := fun h => by
  have := @h Unit ℕ ℕ∞ _ _ 0 (fun _ _ => ⊤) (fun _ _ _ => by simp); simp at this

-- `Finsupp.prod_option_index` idx 7: necessary (N = ℕ, b = 0 is multiplicative, f = 0)
theorem c1_12 : ¬ drop0% Finsupp.prod_option_index 7 := fun h => by
  have := @h Unit ℕ ℕ _ _ 0 (fun _ _ => 0) (fun _ _ _ => by simp); simp at this

-- `Finsupp.sum_pos` idx 10: necessary (g = 0, f = single 1)
theorem c1_13 : ¬ drop0% Finsupp.sum_pos 10 := fun h => by
  have := @h Unit ℕ ℕ _ _ _ _ _ (single () 1) (fun _ _ => 0) (by simp); simp at this

-- `Finsupp.sum_pos` idx 11: necessary (f = 0)
theorem c1_14 : ¬ drop0% Finsupp.sum_pos 11 := fun h => by
  have := @h Unit ℕ ℕ _ _ _ _ _ 0 (fun _ _ => 0) (by simp); simp at this

-- `Finsupp.sum_pos'` idx 11: necessary (f = 0)
theorem c1_15 : ¬ drop0% Finsupp.sum_pos' 11 := fun h => by
  have := @h Unit ℕ ℕ _ _ _ _ _ 0 (fun _ _ => 0) (by simp); simp at this

-- `Finsupp.sum_le_sum` idx 10: necessary (h1 = 1, h2 = 0, f = single 1)
theorem c1_16 : ¬ drop0% Finsupp.sum_le_sum 10 := fun h => by
  have := @h Unit ℕ ℕ _ _ _ _ (single () 1) (fun _ v => v) (fun _ _ => 0); simp at this

-- `Finsupp.sum_nonneg` idx 9: necessary (int, h = -1)
theorem c1_17 : ¬ drop0% Finsupp.sum_nonneg 9 := fun h => by
  have := @h Unit ℕ ℤ _ _ _ _ (single () 1) (fun _ v => -(v : ℤ)); simp at this

-- `Finsupp.sum_nonneg'` idx 9: necessary (int, h = -1)
theorem c1_18 : ¬ drop0% Finsupp.sum_nonneg' 9 := fun h => by
  have := @h Unit ℕ ℤ _ _ _ _ (single () 1) (fun _ v => -(v : ℤ)); simp at this

-- `Finsupp.sum_nonpos` idx 9: necessary (h = 1)
theorem c1_19 : ¬ drop0% Finsupp.sum_nonpos 9 := fun h => by
  have := @h Unit ℕ ℤ _ _ _ _ (single () 1) (fun _ v => (v : ℤ)); simp at this

-- `Finsupp.sum_pos'` idx 10: necessary (int, g = (-5, 1) on Bool)
theorem c1_20 : ¬ drop0% Finsupp.sum_pos' 10 := fun h => by
  have := @h Bool ℕ ℤ _ _ _ _ _ (single true 1 + single false 1) (fun i _ => if i then -5 else 1)
    ⟨false, by simp, by simp⟩
  rw [p2_sum _ _ one_ne_zero one_ne_zero] at this; simp at this

-- `Finsupp.sum_le_sum_index` idx 12: necessary (f1 = single 1, f2 = 0, h = id)
theorem c1_21 : ¬ drop0% Finsupp.sum_le_sum_index 12 := fun h => by
  have := @h Unit ℕ ℕ _ _ _ _ _ _ (single () 1) 0 (fun _ v => v) (fun _ _ => monotone_id) (by simp); simp at this

-- `Finsupp.sum_le_sum_index` idx 13: necessary (int, h = neg, f1 = 0, f2 = single 1)
theorem c1_22 : ¬ drop0% Finsupp.sum_le_sum_index 13 := fun h => by
  have := @h Unit ℕ ℤ _ _ _ _ _ _ 0 (single () 1) (fun _ v => -(v : ℤ)) (by simp) (by simp); simp at this

-- `Finsupp.sum_le_sum_index` idx 14: necessary (int values, f1 = single (-1) <= f2 = 0, h = const 1)
theorem c1_23 : ¬ drop0% Finsupp.sum_le_sum_index 14 := fun h => by
  have := @h Unit ℤ ℕ _ _ _ _ _ _ (single () (-1)) 0 (fun _ _ => 1) (by simp) (fun _ _ => monotone_const); simp [Finsupp.sum] at this

-- `Finsupp.sum_nonneg` idx 6: necessary (beta = W (0 ≤ w2, w2 + w2 = w1 < 0), two-point f, h = w2)
theorem c1_24 : ¬ drop0% Finsupp.sum_nonneg 6 := fun h => by
  have := @h Bool ℕ W _ _ _ (single true 1 + single false 1) (fun _ _ => w2) (fun _ _ => w0_le_w2)
  rw [p2_sum _ _ one_ne_zero one_ne_zero, w22] at this; exact not_w0_le_w1 this

-- `Finsupp.sum_nonneg'` idx 6: necessary (beta = W, two-point f, h = w2)
theorem c1_25 : ¬ drop0% Finsupp.sum_nonneg' 6 := fun h => by
  have := @h Bool ℕ W _ _ _ (single true 1 + single false 1) (fun _ _ => w2) (fun _ => w0_le_w2)
  rw [p2_sum _ _ one_ne_zero one_ne_zero, w22] at this; exact not_w0_le_w1 this

-- `Finsupp.sum_nonpos` idx 6: necessary (beta = W (w1 ≤ 0, w1 + w1 = w2 > 0), two-point f, h = w1)
theorem c1_26 : ¬ drop0% Finsupp.sum_nonpos 6 := fun h => by
  have := @h Bool ℕ W _ _ _ (single true 1 + single false 1) (fun _ _ => w1) (fun _ _ => w1_le_w0)
  rw [p2_sum _ _ one_ne_zero one_ne_zero, w11] at this; exact not_w2_le_w0 this

-- `Finsupp.sum_le_sum` idx 6: necessary (beta = W, two-point f, h1 = 0, h2 = w2)
theorem c1_27 : ¬ drop0% Finsupp.sum_le_sum 6 := fun h => by
  have := @h Bool ℕ W _ _ _ (single true 1 + single false 1) (fun _ _ => 0) (fun _ _ => w2) (fun _ _ => w0_le_w2)
  rw [p2_sum _ _ one_ne_zero one_ne_zero, p2_sum _ _ one_ne_zero one_ne_zero, w22, add_zero] at this
  exact not_w0_le_w1 this

-- `Finsupp.sum_le_sum_index` idx 7: necessary (beta = W, f1 = 0 ≤ f2 two-point, h v = if v = 0 then 0 else w2)
theorem c1_28 : ¬ drop0% Finsupp.sum_le_sum_index 7 := fun h => by
  have := @h Bool ℕ W _ _ _ _ _ 0 (single true 1 + single false 1) (fun _ v => if v = 0 then 0 else w2)
    (Finsupp.le_def.2 fun i => by simp)
    (fun _ _ a b hab => by
      by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb, w0_le_w2] <;> omega)
    (by simp)
  rw [p2_sum _ _ one_ne_zero one_ne_zero, Finsupp.sum_zero_index] at this
  simp only [one_ne_zero, if_false, w22] at this; exact not_w0_le_w1 this

namespace W1c1
theorem p2W_nonneg : (0 : Bool →₀ W) ≤ single true w2 + single false w2 :=
  Finsupp.le_def.2 fun i => by cases i <;> simp [w0_le_w2]
end W1c1

-- `Finsupp.mapDomain_mono` idx 5: necessary (alpha = W, g = (w2, w2) ≥ 0 maps to single () w1, not ≥ 0)
theorem c1_29 : ¬ drop0% Finsupp.mapDomain_mono 5 := fun h => by
  have := @h Bool Unit W _ _ (fun _ => ()) _ _ p2W_nonneg
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, ← Finsupp.single_add, w22,
    Finsupp.mapDomain_zero] at this
  exact not_w0_le_w1 (by simpa using Finsupp.le_def.1 this ())

-- `Finsupp.mapDomain_nonneg` idx 5: necessary (alpha = W, g = (w2, w2))
theorem c1_30 : ¬ drop0% Finsupp.mapDomain_nonneg 5 := fun h => by
  have := @h Bool Unit W _ _ (fun _ => ()) _ p2W_nonneg
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, ← Finsupp.single_add, w22] at this
  exact not_w0_le_w1 (by simpa using Finsupp.le_def.1 this ())

-- `Finsupp.mapDomain_nonpos` idx 5: necessary (alpha = W, g = (w1, w1) ≤ 0 maps to single () w2)
theorem c1_31 : ¬ drop0% Finsupp.mapDomain_nonpos 5 := fun h => by
  have := @h Bool Unit W _ _ (fun _ => ()) (single true w1 + single false w1)
    (Finsupp.le_def.2 fun i => by cases i <;> simp [w1_le_w0])
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, ← Finsupp.single_add, w11] at this
  exact not_w2_le_w0 (by simpa using Finsupp.le_def.1 this ())

-- `Finsupp.mapDomain_nonneg` idx 8: necessary (int, g = single (-1), f = id)
theorem c1_32 : ¬ drop0% Finsupp.mapDomain_nonneg 8 := fun h => by
  have := @h Unit Unit ℤ _ _ _ id (single () (-1))
  rw [Finsupp.mapDomain_id] at this; simpa using Finsupp.le_def.1 this ()

-- `Finsupp.mapDomain_nonpos` idx 8: necessary (int, g = single 1, f = id)
theorem c1_33 : ¬ drop0% Finsupp.mapDomain_nonpos 8 := fun h => by
  have := @h Unit Unit ℤ _ _ _ id (single () 1)
  rw [Finsupp.mapDomain_id] at this; simpa using Finsupp.le_def.1 this ()

-- `Finsupp.isOrderedAddMonoid` idx 4: necessary (alpha = W: 0 ≤ w2 but w2 + 0 ≰ w2 + w2 = w1)
theorem c1_34 : ¬ drop0% Finsupp.isOrderedAddMonoid 4 := fun h => by
  have := @IsOrderedAddMonoid.add_le_add_left _ _ _ (@h Unit W _ _) 0 (single () w2)
    (Finsupp.le_def.2 fun i => by simp [w0_le_w2]) (single () w2)
  rw [zero_add, ← Finsupp.single_add, w22] at this
  exact not_w2_le_w1 (by simpa using Finsupp.le_def.1 this ())

-- `Finsupp.isOrderedCancelAddMonoid` idx 4: necessary (alpha = W as for isOrderedAddMonoid)
theorem c1_35 : ¬ drop0% Finsupp.isOrderedCancelAddMonoid 4 := fun h => by
  have := @IsOrderedAddMonoid.add_le_add_left _ _ _ (@h Unit W _ _).toIsOrderedAddMonoid 0 (single () w2)
    (Finsupp.le_def.2 fun i => by simp [w0_le_w2]) (single () w2)
  rw [zero_add, ← Finsupp.single_add, w22] at this
  exact not_w2_le_w1 (by simpa using Finsupp.le_def.1 this ())

-- `Finsupp.single_le_sum` idx 6: necessary (N = W, f two-point, g = w2 off zero: w2 ≰ w2 + w2 = w1)
theorem c1_36 : ¬ drop0% Finsupp.single_le_sum 6 := fun h => by
  have := @h Bool ℕ W _ _ _ (single true 1 + single false 1) (fun _ m => if m = 0 then 0 else w2)
    (fun i m => by by_cases hm : m = 0 <;> simp [hm, w0_le_w2]) true
  rw [p2_sum _ _ one_ne_zero one_ne_zero, Finsupp.sum_single_index (by simp)] at this
  have e : (single true 1 + single false 1 : Bool →₀ ℕ) true = 1 := by simp
  rw [e] at this
  simp only [one_ne_zero, if_false, w22] at this
  exact not_w2_le_w1 this

-- `Finsupp.single_eval_le_sum` idx 6: necessary (N = W, f two-point, g = w2 off zero)
theorem c1_37 : ¬ drop0% Finsupp.single_eval_le_sum 6 := fun h => by
  have := @h Bool ℕ W _ _ _ (single true 1 + single false 1) (fun m => if m = 0 then 0 else w2) (by simp)
    (fun m => by by_cases hm : m = 0 <;> simp [hm, w0_le_w2]) true
  rw [p2_sum _ _ one_ne_zero one_ne_zero] at this
  have e : (single true 1 + single false 1 : Bool →₀ ℕ) true = 1 := by simp
  rw [e] at this
  simp only [one_ne_zero, if_false, w22] at this
  exact not_w2_le_w1 this

-- `Finsupp.single_le_sum` idx 9: necessary (int, f two-point, g = -1 off zero)
theorem c1_38 : ¬ drop0% Finsupp.single_le_sum 9 := fun h => by
  have := @h Bool ℕ ℤ _ _ _ _ (single true 1 + single false 1) (fun _ m => if m = 0 then 0 else -1) true
  rw [p2_sum _ _ one_ne_zero one_ne_zero, Finsupp.sum_single_index (by simp)] at this
  simp at this

-- `Finsupp.single_eval_le_sum` idx 9: necessary (g = const 1, f = 0)
theorem c1_39 : ¬ drop0% Finsupp.single_eval_le_sum 9 := fun h => by
  have := @h Unit ℕ ℕ _ _ _ _ 0 (fun _ => 1) (fun _ => by simp) ()
  simp at this

-- `Finsupp.single_eval_le_sum` idx 10: necessary (int, f two-point, g = -1 off zero)
theorem c1_40 : ¬ drop0% Finsupp.single_eval_le_sum 10 := fun h => by
  have := @h Bool ℕ ℤ _ _ _ _ (single true 1 + single false 1) (fun m => if m = 0 then 0 else -1) (by simp) true
  rw [p2_sum _ _ one_ne_zero one_ne_zero] at this
  simp at this

-- `Finsupp.instPosSMulMono` idx 8: necessary (nat acting on W: 0 ≤ w2 but 2 • w2 = w1 < 0)
theorem c1_41 : ¬ drop0% Finsupp.instPosSMulMono 8 := fun h => by
  have := @h Unit ℕ W _ _ _ _ _
  have h3 := smul_le_smul_of_nonneg_left (a := (2:ℕ)) (Finsupp.le_def.2 fun i => by simp [w0_le_w2] :
    (0 : Unit →₀ W) ≤ single () w2) (by simp)
  rw [smul_zero, Finsupp.smul_single, two_smul_w2] at h3
  exact not_w0_le_w1 (by simpa using Finsupp.le_def.1 h3 ())

-- `Finsupp.instSMulPosMono` idx 7: necessary (nat acting on W: 1 ≤ 2 but w2 ≰ 2 • w2 = w1)
theorem c1_42 : ¬ drop0% Finsupp.instSMulPosMono 7 := fun h => by
  have := @h Unit ℕ W _ _ _ _
  have h3 := smul_le_smul_of_nonneg_right (b := single () w2) (show (1:ℕ) ≤ 2 by decide)
    (Finsupp.le_def.2 fun i => by simp [w0_le_w2])
  rw [Finsupp.smul_single, Finsupp.smul_single, two_smul_w2, one_smul_w2] at h3
  exact not_w2_le_w1 (by simpa using Finsupp.le_def.1 h3 ())

-- `Finsupp.instPosSMulReflectLE` idx 8: necessary (nat acting on Fin 2: 2 • single 1 = 0 ≤ 2 • 0)
theorem c1_43 : ¬ drop0% Finsupp.instPosSMulReflectLE 8 := fun h => by
  have := @h Unit ℕ (Fin 2) _ _ _ _ _
  have h3 := le_of_smul_le_smul_left (a := (2:ℕ)) (b₁ := single () (1 : Fin 2)) (b₂ := 0)
    (by rw [two_smul_fin2, smul_zero]) (by decide)
  have := Finsupp.le_def.1 h3 (); simp at this

-- `Finsupp.instSMulPosReflectLE` idx 7: necessary (nat acting on Fin 2: 2 • b = 0 • b for b = single 1)
theorem c1_44 : ¬ drop0% Finsupp.instSMulPosReflectLE 7 := fun h => by
  have := @h Unit ℕ (Fin 2) _ _ _ _
  have h3 := le_of_smul_le_smul_right (a₁ := (2:ℕ)) (a₂ := 0) (b := single () (1 : Fin 2))
    (by rw [two_smul_fin2, zero_smul]) (lt_of_le_of_ne (Finsupp.le_def.2 fun i => by simp)
      (fun e => by simpa using DFunLike.congr_fun e ()))
  exact absurd h3 (by decide)

-- `Finsupp.instPosSMulStrictMono` idx 8: necessary (nat acting on Fin 2: 0 < single 1 but 2 • single 1 = 0)
theorem c1_45 : ¬ drop0% Finsupp.instPosSMulStrictMono 8 := fun h => by
  have := @h Unit ℕ (Fin 2) _ _ _ _ _
  have h3 := smul_lt_smul_of_pos_left (a := (2:ℕ)) (b₁ := 0) (b₂ := single () (1 : Fin 2))
    (lt_of_le_of_ne (Finsupp.le_def.2 fun i => by simp) (fun e => by simpa using DFunLike.congr_fun e ()))
    (by decide)
  rw [two_smul_fin2, smul_zero] at h3; exact lt_irrefl _ h3

-- `Finsupp.instSMulPosStrictMono` idx 8: necessary (nat acting on Fin 2: 0 < 2 but 0 • b = 2 • b = 0)
theorem c1_46 : ¬ drop0% Finsupp.instSMulPosStrictMono 8 := fun h => by
  have := @h Unit ℕ (Fin 2) _ _ _ _ _
  have h3 := smul_lt_smul_of_pos_right (a₁ := (0:ℕ)) (a₂ := 2) (b := single () (1 : Fin 2)) (by decide)
    (lt_of_le_of_ne (Finsupp.le_def.2 fun i => by simp) (fun e => by simpa using DFunLike.congr_fun e ()))
  rw [two_smul_fin2, zero_smul] at h3; exact lt_irrefl _ h3

-- `Finsupp.instSMulPosReflectLT` idx 8: necessary (nat acting on Fin 2: 2 • b = 0 < 1 • b, but 2 ≮ 1)
theorem c1_47 : ¬ drop0% Finsupp.instSMulPosReflectLT 8 := fun h => by
  have := @h Unit ℕ (Fin 2) _ _ _ _ _
  have h3 := lt_of_smul_lt_smul_right (a₁ := (2:ℕ)) (a₂ := 1) (b := single () (1 : Fin 2))
    (by rw [two_smul_fin2, one_smul]
        exact lt_of_le_of_ne (Finsupp.le_def.2 fun i => by simp) (fun e => by simpa using DFunLike.congr_fun e ()))
    (Finsupp.le_def.2 fun i => by simp)
  exact absurd h3 (by decide)

-- `Finsupp.addLeftReflectLE` idx 4: necessary (alpha = Fin 2: 1 + 1 ≤ 1 + 0 but 1 ≰ 0)
theorem c1_48 : ¬ drop0% Finsupp.addLeftReflectLE 4 := fun h => by
  have := @h Unit (Fin 2) _ _
  have h3 := le_of_add_le_add_left (a := single () (1 : Fin 2)) (b := single () 1) (c := 0)
    (by rw [← Finsupp.single_add, add_zero, show (1 : Fin 2) + 1 = 0 by decide, Finsupp.single_zero]
        exact Finsupp.le_def.2 fun i => by simp)
  have := Finsupp.le_def.1 h3 (); simp at this


namespace W1c1
theorem notCanonInt : ¬ CanonicallyOrderedAdd ℤ := fun h => by
  have := h.le_self_add 0 (-1); simp at this
/-- truncated subtraction that is always 0 -/
def subZ : Sub ℕ := ⟨fun _ _ => 0⟩
theorem notOrdSubZ : ¬ @OrderedSub ℕ _ _ subZ := fun h => by
  have := (@OrderedSub.tsub_le_iff_right ℕ _ _ subZ h 1 0 0).1 (le_refl 0)
  simp at this
theorem posSum {ι β : Type*} [AddCommMonoid β] [Preorder β] [AddLeftStrictMono β] (s : Finset ι) (u : ι → β)
    (j : ι) (hj : j ∈ s) (h0 : ∀ i ∈ s, 0 ≤ u i) (hp : 0 < u j) : 0 < ∑ i ∈ s, u i := by
  classical
  rw [← Finset.add_sum_erase _ _ hj]
  suffices H : ∀ t : Finset ι, t ⊆ s.erase j → 0 < u j + ∑ i ∈ t, u i from H _ subset_rfl
  intro t
  induction t using Finset.induction_on with
  | empty => intro _; simpa using hp
  | insert k t hk ih =>
    intro hsub
    rw [Finset.sum_insert hk, add_left_comm]
    have h1 := ih ((Finset.subset_insert _ _).trans hsub)
    have h2 : 0 ≤ u k := h0 k (Finset.mem_of_mem_erase (hsub (Finset.mem_insert_self _ _)))
    have h3 : u k + 0 < u k + (u j + ∑ i ∈ t, u i) := CovariantClass.elim (u k) h1
    rw [add_zero] at h3
    exact lt_of_le_of_lt h2 h3
end W1c1

-- `Finsupp.orderedSub` idx 4: necessary (int is not canonically ordered)
theorem c1_49 : ¬ indep0% Finsupp.orderedSub 4 := fun h => notCanonInt (@h Unit ℤ _ _ _ _)

-- `Finsupp.orderedSub` idx 6: necessary (nat with subtraction always 0)
theorem c1_50 : ¬ indep0% Finsupp.orderedSub 6 := fun h => notOrdSubZ (@h Unit ℕ _ _ _ subZ)

-- `Finsupp.coe_tsub` idx 4: necessary (int)
theorem c1_51 : ¬ indep0% Finsupp.coe_tsub 4 := fun h => notCanonInt (@h Unit ℤ _ _ _ _ 0 0)

-- `Finsupp.coe_tsub` idx 6: necessary (nat with subtraction always 0)
theorem c1_52 : ¬ indep0% Finsupp.coe_tsub 6 := fun h => notOrdSubZ (@h Unit ℕ _ _ _ subZ 0 0)

-- `Finsupp.tsub_apply` idx 6: necessary (nat with subtraction always 0)
theorem c1_53 : ¬ indep0% Finsupp.tsub_apply 6 := fun h => notOrdSubZ (@h Unit ℕ _ _ _ subZ 0 0 ())

-- `Finsupp.single_tsub` idx 4: necessary (int)
theorem c1_54 : ¬ indep0% Finsupp.single_tsub 4 := fun h => notCanonInt (@h Unit ℤ _ _ _ _ () 0 0)

-- `Finsupp.single_tsub` idx 6: necessary (nat with subtraction always 0)
theorem c1_55 : ¬ indep0% Finsupp.single_tsub 6 := fun h => notOrdSubZ (@h Unit ℕ _ _ _ subZ () 0 0)

-- `Finsupp.support_tsub` idx 4: necessary (int)
theorem c1_56 : ¬ indep0% Finsupp.support_tsub 4 := fun h => notCanonInt (@h Unit ℤ _ _ _ _ 0 0)

-- `Finsupp.support_tsub` idx 6: necessary (nat with subtraction always 0)
theorem c1_57 : ¬ indep0% Finsupp.support_tsub 6 := fun h => notOrdSubZ (@h Unit ℕ _ _ _ subZ 0 0)

-- `Finsupp.subset_support_tsub` idx 4: necessary (int)
theorem c1_58 : ¬ indep0% Finsupp.subset_support_tsub 4 := fun h => notCanonInt (@h Unit ℤ _ _ _ _ _ 0 0)

-- `Finsupp.subset_support_tsub` idx 6: necessary (nat with subtraction always 0)
theorem c1_59 : ¬ indep0% Finsupp.subset_support_tsub 6 := fun h => notOrdSubZ (@h Unit ℕ _ _ _ subZ _ 0 0)

-- `Finsupp.mapDomain_tsub` idx 5: necessary (int)
theorem c1_60 : ¬ indep0% Finsupp.mapDomain_tsub 5 := fun h =>
  notCanonInt (@h Unit Unit ℤ _ _ _ _ id Function.injective_id 0 0)

-- `Finsupp.mapDomain_tsub` idx 7: necessary (nat with subtraction always 0)
theorem c1_61 : ¬ indep0% Finsupp.mapDomain_tsub 7 := fun h =>
  notOrdSubZ (@h Unit Unit ℕ _ _ _ subZ id Function.injective_id 0 0)

-- `Finsupp.embDomain_tsub` idx 5: necessary (int)
theorem c1_62 : ¬ indep0% Finsupp.embDomain_tsub 5 := fun h =>
  notCanonInt (@h Unit Unit ℤ _ _ _ _ (Function.Embedding.refl _) 0 0)

-- `Finsupp.embDomain_tsub` idx 7: necessary (nat with subtraction always 0)
theorem c1_63 : ¬ indep0% Finsupp.embDomain_tsub 7 := fun h =>
  notOrdSubZ (@h Unit Unit ℕ _ _ _ subZ (Function.Embedding.refl _) 0 0)

-- `Finsupp.mapDomain_tsub` idx 9: necessary (f : Bool → Unit, f1 = single true 1, f2 = single false 1)
theorem c1_64 : ¬ drop0% Finsupp.mapDomain_tsub 9 := fun h => by
  have := @h Bool Unit ℕ _ _ _ _ _ (fun _ => ()) (single true 1) (single false 1)
  have e : (single true 1 - single false 1 : Bool →₀ ℕ) = single true 1 := by
    ext i; cases i <;> simp [Finsupp.tsub_apply]
  rw [e] at this
  have := DFunLike.congr_fun this (); simp [Finsupp.mapDomain_single] at this

-- `Finsupp.instCanonicallyOrderedAddOfAddLeftMono` idx 4: necessary (int)
theorem c1_65 : ¬ drop0% Finsupp.instCanonicallyOrderedAddOfAddLeftMono 4 := fun h => by
  have := (@h Unit ℤ _ _ _ _ _).le_self_add 0 (single () (-1))
  simpa using Finsupp.le_def.1 this ()

-- `Finsupp.support_add_eq_union` idx 4: necessary (int, 1 + -1 = 0)
theorem c1_66 : ¬ drop0% Finsupp.support_add_eq_union 4 := fun h => by
  have := @h Unit ℤ _ _ _ _ (single () 1) (single () (-1)) _
  rw [← Finsupp.single_add] at this; simp at this

-- `Finsupp.support_add_eq_union` idx 6: removable (in a canonically ordered monoid a + b = 0 iff a = b = 0; OrderedSub is unused)
theorem c1_67 : drop% Finsupp.support_add_eq_union 6 := by
  intro ι α _ _ _ _ f1 f2 _
  ext i
  simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finset.mem_union, ne_eq]
  rw [← not_and_or, not_iff_not]
  constructor
  · intro h
    have h1 : f1 i ≤ 0 := h ▸ le_self_add
    have h2 : f2 i ≤ 0 := h ▸ le_add_self
    exact ⟨le_antisymm h1 zero_le, le_antisymm h2 zero_le⟩
  · rintro ⟨h1, h2⟩; simp [h1, h2]

-- `Finsupp.instCanonicallyOrderedAddOfAddLeftMono` idx 6: removable (the difference can be chosen pointwise with support in g.support; OrderedSub is not needed)
theorem c1_68 : drop% Finsupp.instCanonicallyOrderedAddOfAddLeftMono 6 := by
  intro ι α _ _ _ _ _
  classical
  refine { exists_add_of_le := ?_, le_add_self := ?_, le_self_add := ?_ }
  · intro f g h
    let d : α → α → α := fun a b => if hab : a ≤ b then Classical.choose (exists_add_of_le hab) else 0
    have hd : ∀ a b, a ≤ b → b = a + d a b := fun a b hab => by
      simp only [d, dif_pos hab]; exact Classical.choose_spec (exists_add_of_le hab)
    have hd0 : d 0 0 = 0 := by
      have := hd 0 0 le_rfl; rw [zero_add] at this; exact this.symm
    exact ⟨Finsupp.zipWith d hd0 f g, Finsupp.ext fun x => by
      rw [Finsupp.add_apply, Finsupp.zipWith_apply]; exact hd _ _ (Finsupp.le_def.1 h x)⟩
  · intro f g; exact Finsupp.le_def.2 fun x => by simp [le_add_self]
  · intro f g; exact Finsupp.le_def.2 fun x => by simp [le_self_add]

-- `Finsupp.sum_pos'` idx 6: removable (add the nonnegative terms one by one to the positive one: 0 ≤ a and 0 < y give 0 < a + y by strict monotonicity)
theorem c1_69 : drop% Finsupp.sum_pos' 6 := by
  intro ι α β _ _ _ _ f g h ⟨j, hj, hp⟩
  exact posSum f.support (fun i => g i (f i)) j hj h hp

-- `Finsupp.sum_pos` idx 6: removable (as for sum_pos', with all terms positive)
theorem c1_70 : drop% Finsupp.sum_pos 6 := by
  intro ι α β _ _ _ _ f g h hf
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.2 hf
  exact posSum f.support (fun i => g i (f i)) j hj (fun i hi => (h i hi).le) (h j hj)

-- `Finsupp.sum_pos` idx 7: removable (AddLeftStrictMono follows from IsOrderedCancelAddMonoid)
theorem c1_71 : drop% Finsupp.sum_pos 7 := by
  intro ι α β _ _ _ _ f g h hf
  haveI : AddLeftStrictMono β := ⟨fun a {b c} hbc => lt_iff_le_not_ge.2
    ⟨add_le_add_right hbc.le a, fun h' => (lt_iff_le_not_ge.1 hbc).2 (le_of_add_le_add_left h')⟩⟩
  exact Finsupp.sum_pos h hf

-- `Finsupp.sum_pos'` idx 7: removable (AddLeftStrictMono follows from IsOrderedCancelAddMonoid)
theorem c1_72 : drop% Finsupp.sum_pos' 7 := by
  intro ι α β _ _ _ _ f g h hf
  haveI : AddLeftStrictMono β := ⟨fun a {b c} hbc => lt_iff_le_not_ge.2
    ⟨add_le_add_right hbc.le a, fun h' => (lt_iff_le_not_ge.1 hbc).2 (le_of_add_le_add_left h')⟩⟩
  exact Finsupp.sum_pos' h hf


-- `Finsupp.lex_lt_of_lt_of_preorder` idx 5: necessary (r = all pairs on Unit)
theorem c1_73 : ¬ drop0% Finsupp.lex_lt_of_lt_of_preorder 5 := fun h => by
  obtain ⟨i, hi, hlt⟩ := @h Unit ℕ _ _ (fun _ _ => True) 0 (single () 1)
    (lt_of_le_of_ne (Finsupp.le_def.2 fun i => by simp) (fun e => by simpa using DFunLike.congr_fun e ()))
  exact absurd (hi i trivial).2 (not_le.2 hlt)

-- `Finsupp.lex_lt_of_lt_of_preorder` idx 8: necessary (x = y = 0)
theorem c1_74 : ¬ drop0% Finsupp.lex_lt_of_lt_of_preorder 8 := fun h => by
  obtain ⟨i, -, hlt⟩ := @h Unit ℕ _ _ (· < ·) _ 0 0
  exact lt_irrefl _ hlt

-- `Finsupp.lex_lt_of_lt` idx 5: necessary (r = all pairs on Unit)
theorem c1_75 : ¬ drop0% Finsupp.lex_lt_of_lt 5 := fun h => by
  obtain ⟨i, hi, hlt⟩ := @h Unit ℕ _ _ (fun _ _ => True) 0 (single () 1)
    (lt_of_le_of_ne (Finsupp.le_def.2 fun i => by simp) (fun e => by simpa using DFunLike.congr_fun e ()))
  exact absurd (hi i trivial) (ne_of_lt hlt)

-- `Finsupp.lex_lt_of_lt` idx 8: necessary (x = y = 0)
theorem c1_76 : ¬ drop0% Finsupp.lex_lt_of_lt 8 := fun h => by
  obtain ⟨i, -, hlt⟩ := @h Unit ℕ _ _ (· < ·) _ 0 0
  exact lt_irrefl _ hlt

-- `Finsupp.lex_iff_of_unique` idx 6: necessary (r = all pairs on Unit: Lex never holds, but 0 < 1)
theorem c1_77 : ¬ drop0% Finsupp.lex_iff_of_unique 6 := fun h => by
  obtain ⟨i, hi, hlt⟩ := (@h Unit ℕ _ _ _ (fun _ _ => True) 0 (single () 1)).2 (by simp)
  exact absurd (hi i trivial) (ne_of_lt hlt)

namespace W1c1
theorem lexU_lt (x y : Unit →₀ Fin 2) : toLex x < toLex y ↔ x () < y () := by
  rw [Finsupp.Lex.lt_iff_of_unique]; rfl
theorem lexU_le (x y : Unit →₀ Fin 2) : toLex x ≤ toLex y ↔ x () ≤ y () := by
  rw [Finsupp.Lex.le_iff_of_unique]; rfl
theorem colexU_lt (x y : Unit →₀ Fin 2) : toColex x < toColex y ↔ x () < y () := by
  rw [Finsupp.Colex.lt_iff_of_unique]; rfl
theorem colexU_le (x y : Unit →₀ Fin 2) : toColex x ≤ toColex y ↔ x () ≤ y () := by
  rw [Finsupp.Colex.le_iff_of_unique]; rfl
end W1c1

-- `Finsupp.Lex.addLeftStrictMono` idx 5: necessary (N = Fin 2, alpha = Unit: 0 < 1 but 1 + 0 = 1 ≮ 1 + 1 = 0)
theorem c1_78 : ¬ drop0% Finsupp.Lex.addLeftStrictMono 5 := fun h => by
  have := @h Unit (Fin 2) _ _ _
  have h3 : toLex (single () (1 : Fin 2)) + toLex 0 < toLex (single () 1) + toLex (single () 1) :=
    CovariantClass.elim _ ((lexU_lt _ _).2 (by simp))
  rw [← toLex_add, ← toLex_add, lexU_lt] at h3; revert h3; simp

-- `Finsupp.Colex.addLeftStrictMono` idx 5: necessary (N = Fin 2, alpha = Unit)
theorem c1_79 : ¬ drop0% Finsupp.Colex.addLeftStrictMono 5 := fun h => by
  have := @h Unit (Fin 2) _ _ _
  have h3 : toColex (single () (1 : Fin 2)) + toColex 0 < toColex (single () 1) + toColex (single () 1) :=
    CovariantClass.elim _ ((colexU_lt _ _).2 (by simp))
  rw [← toColex_add, ← toColex_add, colexU_lt] at h3; revert h3; simp

-- `Finsupp.Lex.addLeftMono` idx 5: necessary (N = Fin 2, alpha = Unit: 0 ≤ 1 but 1 + 0 ≰ 1 + 1 = 0)
theorem c1_80 : ¬ drop0% Finsupp.Lex.addLeftMono 5 := fun h => by
  have := @h Unit (Fin 2) _ _ _
  have h3 : toLex (single () (1 : Fin 2)) + toLex 0 ≤ toLex (single () 1) + toLex (single () 1) :=
    CovariantClass.elim _ ((lexU_le _ _).2 (by simp))
  rw [← toLex_add, ← toLex_add, lexU_le] at h3; revert h3; simp

-- `Finsupp.Colex.addLeftMono` idx 5: necessary (N = Fin 2, alpha = Unit)
theorem c1_81 : ¬ drop0% Finsupp.Colex.addLeftMono 5 := fun h => by
  have := @h Unit (Fin 2) _ _ _
  have h3 : toColex (single () (1 : Fin 2)) + toColex 0 ≤ toColex (single () 1) + toColex (single () 1) :=
    CovariantClass.elim _ ((colexU_le _ _).2 (by simp))
  rw [← toColex_add, ← toColex_add, colexU_le] at h3; revert h3; simp

-- `Finsupp.Lex.addRightMono` idx 5: necessary (N = Fin 2, alpha = Unit: 0 ≤ 1 but 0 + 1 ≰ 1 + 1 = 0)
theorem c1_82 : ¬ drop0% Finsupp.Lex.addRightMono 5 := fun h => by
  have := @h Unit (Fin 2) _ _ _
  have h3 : toLex 0 + toLex (single () (1 : Fin 2)) ≤ toLex (single () 1) + toLex (single () 1) :=
    CovariantClass.elim (μ := Function.swap (· + ·)) _ ((lexU_le _ _).2 (by simp))
  rw [← toLex_add, ← toLex_add, lexU_le] at h3; revert h3; simp

-- `Finsupp.Lex.isBotZeroClass` idx 5: necessary (N = int, alpha = Unit: single (-1) < 0)
theorem c1_83 : ¬ drop0% Finsupp.Lex.isBotZeroClass 5 := fun h => by
  have := (@h Unit ℤ _ _ _).isBot_zero (toLex (single () (-1)))
  rw [Finsupp.Lex.le_iff_of_unique] at this; simp at this

-- `Finsupp.Colex.isBotZeroClass` idx 5: necessary (N = int, alpha = Unit)
theorem c1_84 : ¬ drop0% Finsupp.Colex.isBotZeroClass 5 := fun h => by
  have := (@h Unit ℤ _ _ _).isBot_zero (toColex (single () (-1)))
  rw [Finsupp.Colex.le_iff_of_unique] at this; simp at this

-- `Finsupp.Lex.isOrderedCancelAddMonoid` idx 5: necessary (N = Fin 2, alpha = Unit)
theorem c1_85 : ¬ drop0% Finsupp.Lex.isOrderedCancelAddMonoid 5 := fun h => by
  have := @IsOrderedAddMonoid.add_le_add_left _ _ _ (@h Unit (Fin 2) _ _ _).toIsOrderedAddMonoid
    (toLex 0) (toLex (single () 1)) ((lexU_le _ _).2 (by simp)) (toLex (single () 1))
  rw [← toLex_add, ← toLex_add, lexU_le] at this; revert this; simp

-- `Finsupp.Colex.isOrderedCancelAddMonoid` idx 5: necessary (N = Fin 2, alpha = Unit)
theorem c1_86 : ¬ drop0% Finsupp.Colex.isOrderedCancelAddMonoid 5 := fun h => by
  have := @IsOrderedAddMonoid.add_le_add_left _ _ _ (@h Unit (Fin 2) _ _ _).toIsOrderedAddMonoid
    (toColex 0) (toColex (single () 1)) ((colexU_le _ _).2 (by simp)) (toColex (single () 1))
  rw [← toColex_add, ← toColex_add, colexU_le] at this; revert this; simp

-- `instIsOrderedCancelAddMonoidLexFinsupp` idx 5: necessary (N = Fin 2, alpha = Unit)
theorem c1_87 : ¬ drop0% instIsOrderedCancelAddMonoidLexFinsupp 5 := fun h => by
  have := @IsOrderedAddMonoid.add_le_add_left _ _ _ (@h Unit (Fin 2) _ _ _).toIsOrderedAddMonoid
    (toLex 0) (toLex (single () 1)) ((lexU_le _ _).2 (by simp)) (toLex (single () 1))
  rw [← toLex_add, ← toLex_add, lexU_le] at this; revert this; simp

namespace W1c1
theorem notWFGTNat : ¬ WellFoundedGT ℕ := fun h => by
  obtain ⟨m, -, hm⟩ := (@wellFounded_gt ℕ _ h).has_min Set.univ ⟨0, trivial⟩
  exact hm (m + 1) trivial (Nat.lt_succ_self m)
end W1c1

-- `MonomialOrder.lex_le_iff` idx 2: necessary (sigma = nat is not WellFoundedGT)
theorem c1_88 : ¬ indep0% MonomialOrder.lex_le_iff 2 := fun h => notWFGTNat (@h ℕ _ 0 0)
-- `MonomialOrder.lex_lt_iff` idx 2: necessary (sigma = nat)
theorem c1_89 : ¬ indep0% MonomialOrder.lex_lt_iff 2 := fun h => notWFGTNat (@h ℕ _ 0 0)
-- `MonomialOrder.degLex_le_iff` idx 2: necessary (sigma = nat)
theorem c1_90 : ¬ indep0% MonomialOrder.degLex_le_iff 2 := fun h => notWFGTNat (@h ℕ _ 0 0)
-- `MonomialOrder.degLex_lt_iff` idx 2: necessary (sigma = nat)
theorem c1_91 : ¬ indep0% MonomialOrder.degLex_lt_iff 2 := fun h => notWFGTNat (@h ℕ _ 0 0)
-- `MonomialOrder.degLex_single_le_iff` idx 2: necessary (sigma = nat)
theorem c1_92 : ¬ indep0% MonomialOrder.degLex_single_le_iff 2 := fun h => notWFGTNat (@h ℕ _ 0 0)
-- `MonomialOrder.degLex_single_lt_iff` idx 2: necessary (sigma = nat)
theorem c1_93 : ¬ indep0% MonomialOrder.degLex_single_lt_iff 2 := fun h => notWFGTNat (@h ℕ _ 0 0)

-- `Finsupp.embSigma_apply_of_ne` idx 7: necessary (k' = k)
theorem c1_94 : ¬ drop0% Finsupp.embSigma_apply_of_ne 7 := fun h => by
  have := @h Unit (fun _ => Unit) ℕ _ () () (single () 1) ()
  simp at this

-- `Finsupp.split_embSigma_of_ne` idx 7: necessary (k' = k)
theorem c1_95 : ¬ drop0% Finsupp.split_embSigma_of_ne 7 := fun h => by
  have := DFunLike.congr_fun (@h Unit (fun _ => Unit) ℕ _ () () (single () 1)) ()
  simp [Finsupp.split_apply] at this

-- `Finsupp.single_apply_left` idx 5: necessary (f : Bool → Unit constant)
theorem c1_96 : ¬ drop0% Finsupp.single_apply_left 5 := fun h => by
  have := @h Bool Unit ℕ _ (fun _ => ()) true false 1
  simp at this

-- `Finsupp.instNontrivial` idx 3: necessary (alpha empty)
theorem c1_97 : ¬ drop0% Finsupp.instNontrivial 3 := fun h => by
  obtain ⟨x, y, hxy⟩ := (@h Empty ℕ _ _).exists_pair_ne
  exact hxy (Subsingleton.elim x y)

-- `Finsupp.instNontrivial` idx 4: necessary (M = Unit)
theorem c1_98 : ¬ drop0% Finsupp.instNontrivial 4 := fun h => by
  obtain ⟨x, y, hxy⟩ := (@h Unit Unit _ _).exists_pair_ne
  exact hxy (Subsingleton.elim x y)

-- `Finsupp.card_support_le_one` idx 3: necessary (alpha empty)
theorem c1_99 : ¬ drop0% Finsupp.card_support_le_one 3 := fun h => by
  obtain ⟨a, -⟩ := (@h Empty ℕ _ 0).1 (by simp)
  exact a.elim

-- `Finsupp.card_support_le_one'` idx 3: necessary (alpha empty)
theorem c1_100 : ¬ drop0% Finsupp.card_support_le_one' 3 := fun h => by
  obtain ⟨a, -⟩ := (@h Empty ℕ _ 0).1 (by simp)
  exact a.elim

-- `Finsupp.equivFunOnFinite_single` idx 4: necessary (alpha = nat is infinite)
theorem c1_101 : ¬ indep0% Finsupp.equivFunOnFinite_single 4 := fun h =>
  @not_finite ℕ _ (@h ℕ ℕ _ _ 0 0)

-- `Finsupp.equivFunOnFinite_symm_single` idx 4: necessary (alpha = nat is infinite)
theorem c1_102 : ¬ indep0% Finsupp.equivFunOnFinite_symm_single 4 := fun h =>
  @not_finite ℕ _ (@h ℕ ℕ _ _ 0 0)

-- `Finsupp.support_update_ne_zero` idx 7: necessary (b = 0, f = 0)
theorem c1_103 : ¬ drop0% Finsupp.support_update_ne_zero 7 := fun h => by
  have := @h Unit ℕ _ 0 () 0 _
  simp at this

-- `Finsupp.update_comm` idx 6: necessary (a1 = a2, m1 = 0, m2 = 1)
theorem c1_104 : ¬ drop0% Finsupp.update_comm 6 := fun h => by
  have := DFunLike.congr_fun (@h Unit ℕ _ 0 () () 0 1) ()
  simp at this

-- `Finsupp.erase_ne` idx 6: necessary (a' = a, f = single a 1)
theorem c1_105 : ¬ drop0% Finsupp.erase_ne 6 := fun h => by
  have := @h Unit ℕ _ () () (single () 1)
  simp at this

-- `Finsupp.erase_single_ne` idx 6: necessary (a = a', b = 1)
theorem c1_106 : ¬ drop0% Finsupp.erase_single_ne 6 := fun h => by
  have := DFunLike.congr_fun (@h Unit ℕ _ () () 1) ()
  simp at this

-- `Finsupp.erase_of_notMem_support` idx 5: necessary (f = single a 1)
theorem c1_107 : ¬ drop0% Finsupp.erase_of_notMem_support 5 := fun h => by
  have := DFunLike.congr_fun (@h Unit ℕ _ (single () 1) ()) ()
  simp at this

-- `Finsupp.erase_update_of_ne` idx 6: necessary (a = a', b = 1, f = 0)
theorem c1_108 : ¬ drop0% Finsupp.erase_update_of_ne 6 := fun h => by
  have := DFunLike.congr_fun (@h Unit ℕ _ 0 () () 1) ()
  simp at this

-- `Finsupp.single_of_embDomain_single` idx 8: necessary (alpha empty, b = 0)
theorem c1_109 : ¬ drop0% Finsupp.single_of_embDomain_single 8 := fun h => by
  obtain ⟨x, -⟩ := @h Empty Unit ℕ _ 0 ⟨Empty.elim, fun a => a.elim⟩ () 0 (by ext; simp)
  exact x.elim

-- `Finsupp.single_of_embDomain_single` idx 9: necessary (alpha empty, b = 1)
theorem c1_110 : ¬ drop0% Finsupp.single_of_embDomain_single 9 := fun h => by
  obtain ⟨x, -⟩ := @h Empty Unit ℕ _ 0 ⟨Empty.elim, fun a => a.elim⟩ () 1 one_ne_zero
  exact x.elim

-- `Finsupp.add_sub_single_one` idx 4: necessary (u' = 0, u = single a 1)
theorem c1_111 : ¬ drop0% Finsupp.add_sub_single_one 4 := fun h => by
  have := DFunLike.congr_fun (@h Unit () (single () 1) 0) ()
  simp at this

-- `Finsupp.support_inf` idx 4: necessary (int, f = single (-1), g = 0)
theorem c1_112 : ¬ drop0% Finsupp.support_inf 4 := fun h => by
  have := congrArg (fun s => () ∈ s) (@h Unit ℤ _ _ _ (single () (-1)) 0)
  simp at this

-- `Finsupp.support_sup` idx 4: necessary (int, f = single (-1), g = 0)
theorem c1_113 : ¬ drop0% Finsupp.support_sup 4 := fun h => by
  have := congrArg (fun s => () ∈ s) (@h Unit ℤ _ _ _ (single () (-1)) 0)
  simp at this

namespace W1c1
theorem notBotInt : ¬ IsBotZeroClass ℤ := fun h => by
  have := h.isBot_zero (-1); simp at this
end W1c1

-- `Finsupp.disjoint_iff` idx 4: necessary (int)
theorem c1_114 : ¬ indep0% Finsupp.disjoint_iff 4 := fun h => notBotInt (@h Unit ℤ _ _ 0 0)

-- `Finsupp.bot_eq_zero` idx 4: necessary (int)
theorem c1_115 : ¬ indep0% Finsupp.bot_eq_zero 4 := fun h => notBotInt (@h Unit ℤ _ _)

-- `Finsupp.instIsBotZeroClass` idx 4: necessary (int, Unit index)
theorem c1_116 : ¬ drop0% Finsupp.instIsBotZeroClass 4 := fun h => by
  have := (@h Unit ℤ _ _).isBot_zero (single () (-1))
  simpa using Finsupp.le_def.1 this ()

-- `Finsupp.add_eq_zero_iff` idx 4: necessary (int, 1 + -1 = 0)
theorem c1_117 : ¬ drop0% Finsupp.add_eq_zero_iff 4 := fun h => by
  have := (@h Unit ℤ _ _ (single () 1) (single () (-1))).1 (by rw [← Finsupp.single_add]; simp)
  simp at this

-- `Finsupp.le_iff'` idx 4: necessary (int, f = 0, g = single (-1), s = empty)
theorem c1_118 : ¬ drop0% Finsupp.le_iff' 4 := fun h => by
  have := (@h Unit ℤ _ _ 0 (single () (-1)) ∅ (by simp)).2 (by simp)
  simpa using Finsupp.le_def.1 this ()

-- `Finsupp.le_iff'` idx 8: necessary (f = single 1, g = 0, s = empty)
theorem c1_119 : ¬ drop0% Finsupp.le_iff' 8 := fun h => by
  have := (@h Unit ℕ _ _ _ (single () 1) 0 ∅).2 (by simp)
  simpa using Finsupp.le_def.1 this ()

-- `Finsupp.le_iff` idx 4: necessary (int, f = 0, g = single (-1))
theorem c1_120 : ¬ drop0% Finsupp.le_iff 4 := fun h => by
  have := (@h Unit ℤ _ _ 0 (single () (-1))).2 (by simp)
  simpa using Finsupp.le_def.1 this ()

-- `Finsupp.support_monotone` idx 4: necessary (int, single (-1) ≤ 0)
theorem c1_121 : ¬ drop0% Finsupp.support_monotone 4 := fun h => by
  have := @h Unit ℤ _ _ (single () (-1)) 0 (Finsupp.le_def.2 fun i => by simp)
  simpa using this (show () ∈ (single () _).support by simp)

-- `Finsupp.support_mono` idx 6: necessary (int, single (-1) ≤ 0)
theorem c1_122 : ¬ drop0% Finsupp.support_mono 6 := fun h => by
  have := @h Unit ℤ _ _ (single () (-1)) 0 (Finsupp.le_def.2 fun i => by simp)
  simpa using this (show () ∈ (single () _).support by simp)

-- `Finsupp.support_mono` idx 7: necessary (f = single 1, g = 0)
theorem c1_123 : ¬ drop0% Finsupp.support_mono 7 := fun h => by
  have := @h Unit ℕ _ _ (single () 1) 0 _
  simpa using this (show () ∈ (single () _).support by simp)

-- `Finsupp.single_le_iff` idx 4: necessary (int, Bool index, x = 0, f = single false (-1))
theorem c1_124 : ¬ drop0% Finsupp.single_le_iff 4 := fun h => by
  have := (@h Bool ℤ _ _ true 0 (single false (-1))).2 (by simp)
  simpa using Finsupp.le_def.1 this false


namespace W1c1
theorem notWF {X : Type*} (r : X → X → Prop) (f : ℕ → X) (hf : ∀ n, r (f (n+1)) (f n)) : ¬ WellFounded r :=
  fun h => by
    obtain ⟨m, ⟨k, rfl⟩, hm⟩ := h.has_min (Set.range f) ⟨f 0, 0, rfl⟩
    exact hm (f (k+1)) ⟨k+1, rfl⟩ (hf k)
end W1c1

-- `Finsupp.DegLex.wellFounded` idx 2: necessary (alpha = Bool, r = empty relation: single true 1 and single false 1 are below each other)
theorem c1_125 : ¬ drop0% Finsupp.DegLex.wellFounded 2 := fun h => by
  have := @h Bool (fun _ _ => False) ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩ (· < ·) wellFounded_lt
    (fun n => Nat.not_lt_zero n)
  have h1 : Finsupp.DegLex (fun _ _ => False) (· < ·) (single true 1 : Bool →₀ ℕ) (single false 1) := by
    rw [Finsupp.degLex_def, Finsupp.degree_single, Finsupp.degree_single]
    exact Prod.Lex.right _ (Finsupp.lex_def.2 ⟨false, fun j hj => hj.elim, by simp⟩)
  have h2 : Finsupp.DegLex (fun _ _ => False) (· < ·) (single false 1 : Bool →₀ ℕ) (single true 1) := by
    rw [Finsupp.degLex_def, Finsupp.degree_single, Finsupp.degree_single]
    exact Prod.Lex.right _ (Finsupp.lex_def.2 ⟨true, fun j hj => hj.elim, by simp⟩)
  exact this.asymmetric _ _ h1 h2

-- `Finsupp.DegLex.wellFounded` idx 3: necessary (alpha = nat, r = <: single (n+1) 1 < single n 1 for all n)
theorem c1_126 : ¬ drop0% Finsupp.DegLex.wellFounded 3 := fun h => by
  refine notWF _ (fun n => (single n 1 : ℕ →₀ ℕ)) (fun n => ?_)
    (@h ℕ (· < ·) _ (· < ·) wellFounded_lt (fun n => Nat.not_lt_zero n))
  rw [Finsupp.degLex_def, Finsupp.degree_single, Finsupp.degree_single]
  refine Prod.Lex.right _ (Finsupp.lex_def.2 ⟨n, fun j hj => ?_, by simp⟩)
  simp [Finsupp.single_apply, show n + 1 ≠ j by omega, show n ≠ j by omega]

namespace W1c1
theorem trichUnit : Std.Trichotomous (fun _ _ : Unit => False) := ⟨fun a b _ _ => Subsingleton.elim a b⟩
end W1c1

-- `Finsupp.DegLex.wellFounded` idx 5: necessary (alpha = Unit, s a b := b < a ∧ b ≠ 0 is not well-founded; degrees increase)
theorem c1_127 : ¬ drop0% Finsupp.DegLex.wellFounded 5 := fun h => by
  refine notWF _ (fun n => (single () (n+1) : Unit →₀ ℕ)) (fun n => ?_)
    (@h Unit (fun _ _ => False) trichUnit ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩ (fun a b => b < a ∧ b ≠ 0)
      (fun n hn => hn.2 rfl))
  rw [Finsupp.degLex_def, Finsupp.degree_single, Finsupp.degree_single]
  exact Prod.Lex.left _ _ ⟨by omega, by omega⟩

-- `Finsupp.DegLex.wellFounded` idx 6: necessary (alpha = nat, r = >, s = {(1, 0)}: single (n+1) 1 < single n 1)
theorem c1_128 : ¬ drop0% Finsupp.DegLex.wellFounded 6 := fun h => by
  refine notWF _ (fun n => (single n 1 : ℕ →₀ ℕ)) (fun n => ?_)
    (@h ℕ (· > ·) _ ⟨fun a => (wellFounded_lt.apply a)⟩ (fun a b => a = 1 ∧ b = 0)
      ⟨fun a => ⟨a, fun b hb => ⟨b, fun c hc => by obtain ⟨h1, -⟩ := hb; obtain ⟨-, h2⟩ := hc; omega⟩⟩⟩)
  rw [Finsupp.degLex_def, Finsupp.degree_single, Finsupp.degree_single]
  refine Prod.Lex.right _ (Finsupp.lex_def.2 ⟨n + 1, fun j hj => ?_, by simp⟩)
  simp [Finsupp.single_apply, show n + 1 ≠ j by omega, show n ≠ j by omega]

-- `Finsupp.support_mapDomain_of_nonneg` idx 5: necessary (M = Fin 2, x = (1, 1) on Bool ≥ 0 maps to single () (1 + 1) = 0)
theorem c1_129 : ¬ drop0% Finsupp.support_mapDomain_of_nonneg 5 := fun h => by
  have := @h Bool Unit (Fin 2) _ _ _ (single true 1 + single false 1) (Finsupp.le_def.2 fun i => by simp)
    (fun _ => ())
  have hm : () ∈ Finset.image (fun _ : Bool => ()) (single true (1 : Fin 2) + single false 1).support :=
    Finset.mem_image.2 ⟨true, by simp, rfl⟩
  rw [← this, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, ← Finsupp.single_add,
    show (1 : Fin 2) + 1 = 0 by decide] at hm
  simp at hm

-- `Finsupp.support_mapDomain_of_nonneg` idx 8: necessary (int, x = (1, -1) on Bool maps to 0)
theorem c1_130 : ¬ drop0% Finsupp.support_mapDomain_of_nonneg 8 := fun h => by
  have := @h Bool Unit ℤ _ _ _ _ (single true 1 + single false (-1)) (fun _ => ())
  have hm : () ∈ Finset.image (fun _ : Bool => ()) (single true (1 : ℤ) + single false (-1)).support :=
    Finset.mem_image.2 ⟨true, by simp, rfl⟩
  rw [← this, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, ← Finsupp.single_add] at hm
  simp at hm

namespace W1c1
/-- nat with the strict order as `≤` (irreflexive) -/
def Ir := ℕ
instance : AddCommMonoid Ir := inferInstanceAs (AddCommMonoid ℕ)
instance : LE Ir := ⟨fun a b => Nat.lt a b⟩
end W1c1

-- `Finsupp.embDomain_le_embDomain_iff_le` idx 5: necessary (irreflexive ≤, empty source: 0 ≤ 0 fails only on the target)
theorem c1_131 : ¬ drop0% Finsupp.embDomain_le_embDomain_iff_le 5 := fun h => by
  have := (@h Empty Unit Ir _ _ ⟨Empty.elim, fun a => a.elim⟩ 0 0).2 (fun i => i.elim)
  rw [Finsupp.embDomain_zero] at this
  exact Nat.lt_irrefl 0 (this ())

-- `Finsupp.mapDomain_le_mapDomain_iff_le` idx 5: necessary (irreflexive ≤, f : Empty → Unit)
theorem c1_132 : ¬ drop0% Finsupp.mapDomain_le_mapDomain_iff_le 5 := fun h => by
  have := (@h Empty Unit Ir _ _ Empty.elim (fun a => a.elim) 0 0).2 (fun i => i.elim)
  rw [Finsupp.mapDomain_zero] at this
  exact Nat.lt_irrefl 0 (this ())

-- `Finsupp.mapDomain_le_mapDomain_iff_le` idx 7: necessary (f : Bool → Unit, single true 1 vs single false 1)
theorem c1_133 : ¬ drop0% Finsupp.mapDomain_le_mapDomain_iff_le 7 := fun h => by
  have := (@h Bool Unit ℕ _ _ _ (fun _ => ()) (single true 1) (single false 1)).1
    (by rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single])
  simpa using Finsupp.le_def.1 this true

-- `Finsupp.mapDomain_lt_mapDomain_iff_lt` idx 6: necessary (f : Bool → Unit, single true 1 vs single false 2)
theorem c1_134 : ¬ drop0% Finsupp.mapDomain_lt_mapDomain_iff_lt 6 := fun h => by
  have := (@h Bool Unit ℕ _ _ (fun _ => ()) (single true 1) (single false 2)).1
    (by rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
        exact lt_of_le_of_ne (Finsupp.le_def.2 fun i => by simp) (fun e => by simpa using DFunLike.congr_fun e ()))
  simpa using Finsupp.le_def.1 this.le true

-- `Finsupp.wellQuasiOrderedLE` idx 4: necessary (alpha = int, sigma = Unit: single (-n) is a bad sequence)
theorem c1_135 : ¬ drop0% Finsupp.wellQuasiOrderedLE 4 := fun h => by
  have := @h ℤ Unit _ _ _
  obtain ⟨m, n, hmn, hle⟩ := wellQuasiOrdered_le (fun n : ℕ => (single () (-(n : ℤ)) : Unit →₀ ℤ))
  have := Finsupp.le_def.1 hle (); simp at this; omega

-- `Finsupp.wellQuasiOrderedLE` idx 5: necessary (sigma = nat, alpha = nat: single n 1 is an antichain)
theorem c1_136 : ¬ drop0% Finsupp.wellQuasiOrderedLE 5 := fun h => by
  have := @h ℕ ℕ _ _ _
  obtain ⟨m, n, hmn, hle⟩ := wellQuasiOrdered_le (fun n : ℕ => (single n 1 : ℕ →₀ ℕ))
  have := Finsupp.le_def.1 hle m; simp [Finsupp.single_apply, show n ≠ m by omega] at this

-- `Quot.liftFinsupp_mk` idx 5: necessary (r = all pairs, f = single true 1)
theorem c1_137 : ¬ indep0% Quot.liftFinsupp_mk 5 := fun h => by
  have := @h Bool ℕ (fun _ _ => True) _ (single true 1) true true false trivial
  simp at this

namespace W1c1
def topSetoid (X : Type) : Setoid X := ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩
end W1c1

-- `Quotient.liftFinsupp_mk` idx 5: necessary (s = all pairs, f = single true 1)
theorem c1_138 : ¬ indep0% Quotient.liftFinsupp_mk 5 := fun h => by
  have := @h Bool ℕ (topSetoid Bool) _ (single true 1) true true false trivial
  simp at this

-- `Setoid.liftFinsuppEquiv_apply_mk` idx 4: necessary (alpha = nat, s = all pairs: classes are infinite)
theorem c1_139 : ¬ indep0% Setoid.liftFinsuppEquiv_apply_mk 4 := fun h => by
  have := @h ℕ ℕ (topSetoid ℕ) _ ⟨0, fun _ _ _ => rfl⟩ 0 0
  exact Set.infinite_univ (α := ℕ) this

-- `Setoid.liftFinsuppEquiv_symm_apply` idx 4: necessary (alpha = nat, s = all pairs)
theorem c1_140 : ¬ indep0% Setoid.liftFinsuppEquiv_symm_apply 4 := fun h => by
  have := @h ℕ ℕ (topSetoid ℕ) _ 0 0 0
  exact Set.infinite_univ (α := ℕ) this

-- `IsSMulRegular.finsupp` idx 6: necessary (k = 0)
theorem c1_141 : ¬ drop0% IsSMulRegular.finsupp 6 := fun h => by
  have := @h Unit ℕ ℕ _ _ 0 (a₁ := single () 1) (a₂ := 0) (by simp)
  simp at this

-- `Finsupp.faithfulSMul` idx 3: necessary (alpha empty: 0 and 1 act equally on the trivial module)
theorem c1_142 : ¬ drop0% Finsupp.faithfulSMul 3 := fun h => by
  have := @FaithfulSMul.eq_of_smul_eq_smul ℕ (Empty →₀ ℕ) _ (@h Empty ℕ ℕ _ _ _) 0 1
    (fun m => Subsingleton.elim _ _)
  simp at this

-- `Finsupp.faithfulSMul` idx 6: necessary (M = Unit)
theorem c1_143 : ¬ drop0% Finsupp.faithfulSMul 6 := fun h => by
  have := @FaithfulSMul.eq_of_smul_eq_smul ℕ (Unit →₀ Unit) _ (@h Unit Unit ℕ _ _ _) 0 1
    (fun m => Finsupp.ext fun _ => Subsingleton.elim _ _)
  simp at this

-- `Finsupp.support_smul_eq` idx 4: necessary (R = M = ZMod 4, b = 2, g = single 2)
theorem c1_144 : ¬ drop0% Finsupp.support_smul_eq 4 := fun h => by
  have := @h Unit (ZMod 4) (ZMod 4) _ _ _ _ 2 (by decide) (single () 2)
  rw [Finsupp.smul_single, show (2 : ZMod 4) • (2 : ZMod 4) = 0 by decide, Finsupp.single_zero,
    Finsupp.support_zero, Finsupp.support_single_ne_zero _ (show (2 : ZMod 4) ≠ 0 by decide)] at this
  simp at this

-- `Finsupp.support_smul_eq` idx 7: necessary (R = nat, M = ZMod 2, b = 2)
theorem c1_145 : ¬ drop0% Finsupp.support_smul_eq 7 := fun h => by
  have := @h Unit (ZMod 2) ℕ _ _ _ _ 2 (by decide) (single () 1)
  rw [Finsupp.smul_single, show (2 : ℕ) • (1 : ZMod 2) = 0 by decide] at this
  simp at this

-- `Finsupp.support_smul_eq` idx 9: necessary (b = 0)
theorem c1_146 : ¬ drop0% Finsupp.support_smul_eq 9 := fun h => by
  have := @h Unit ℕ ℕ _ _ _ _ _ 0 (single () 1)
  simp at this

-- `Finsupp.comapDomain_smul` idx 9: necessary (f : Bool → Unit constant, v = single () 1)
theorem c1_147 : ¬ indep0% Finsupp.comapDomain_smul 9 := fun h => by
  have := @h Bool Unit ℕ ℕ _ _ (fun _ => ()) 0 (single () 1)
  exact Bool.noConfusion (this (show true ∈ _ by simp) (show false ∈ _ by simp) rfl)

-- `Finsupp.comapDomain_smul` idx 10: removable (the support of r • v is contained in that of v, so hfv implies hfrv)
theorem c1_148 : indep% Finsupp.comapDomain_smul 10 := by
  intro α β M R _ _ f r v hfv
  exact hfv.mono (Set.preimage_mono (Finset.coe_subset.2 Finsupp.support_smul))

-- `Finsupp.comapDomain_smul_of_injective` idx 7: necessary (f : Bool → Unit)
theorem c1_149 : ¬ indep0% Finsupp.comapDomain_smul_of_injective 7 := fun h => by
  exact Bool.noConfusion (@h Bool Unit ℕ ℕ _ _ (fun _ => ()) 0 0 (a₁ := true) (a₂ := false) rfl)

-- `Finsupp.sum_smul_index` idx 8: necessary (b = 0, h = const 1, g = single 1)
theorem c1_150 : ¬ drop0% Finsupp.sum_smul_index 8 := fun h => by
  have := @h Unit ℕ ℕ _ _ (single () 1) 0 (fun _ _ => 1)
  simp [Finsupp.sum] at this

-- `Finsupp.sum_smul_index'` idx 10: necessary (b = 0, h = const 1, g = single 1)
theorem c1_151 : ¬ drop0% Finsupp.sum_smul_index' 10 := fun h => by
  have := @h Unit ℕ ℕ ℕ _ _ _ (single () 1) 0 (fun _ _ => 1)
  simp [Finsupp.sum] at this

-- `Finsupp.moduleIsTorsionFree` idx 6: necessary (R = nat, M = ZMod 2: 2 • single 1 = 0)
theorem c1_152 : ¬ drop0% Finsupp.moduleIsTorsionFree 6 := fun h => by
  have := (@h (ZMod 2) ℕ _ _ _ Unit).isSMulRegular (r := 2) (IsRegular.of_ne_zero two_ne_zero)
    (a₁ := single () 1) (a₂ := 0)
    (by simp only [smul_zero]; rw [Finsupp.smul_single, show (2 : ℕ) • (1 : ZMod 2) = 0 by decide]; simp)
  simpa using DFunLike.congr_fun this ()

namespace W1c1
/-- evaluation at () as an equivariant hom -/
def evalU : (Unit →₀ ℕ) →+[ℕ] ℕ :=
  { toFun := fun v => v (), map_smul' := fun m v => by simp, map_zero' := by simp,
    map_add' := fun v w => by simp }
end W1c1

-- `Finsupp.distribMulActionHom_ext` idx 11: necessary (id and 0 on Unit →₀ ℕ)
theorem c1_153 : ¬ drop0% Finsupp.distribMulActionHom_ext 11 := fun h => by
  have := DFunLike.congr_fun (@h Unit ℕ ℕ ℕ _ _ _ _ _ evalU 0) (single () 1)
  change (single () (1:ℕ)) () = (0 : ℕ) at this
  simp at this

-- `Finsupp.distribMulActionHom_ext'` idx 11: necessary (id and 0 on Unit →₀ ℕ)
theorem c1_154 : ¬ drop0% Finsupp.distribMulActionHom_ext' 11 := fun h => by
  have := DFunLike.congr_fun (@h Unit ℕ ℕ ℕ _ _ _ _ _ evalU 0) (single () 1)
  change (single () (1:ℕ)) () = (0 : ℕ) at this
  simp at this

-- `Finsupp.isScalarTower` idx 8: necessary (R = S = M = nat with the zero action of R on S)
theorem c1_155 : ¬ drop0% Finsupp.isScalarTower 8 := fun h => by
  have := (@h Unit ℕ ℕ ℕ _ _ _ ⟨fun _ _ => 0⟩).smul_assoc 1 1 (single () 1)
  have := DFunLike.congr_fun this ()
  change (0 : ℕ) • (single () 1 : Unit →₀ ℕ) () = 1 • (1 • (single () 1 : Unit →₀ ℕ)) () at this
  simp at this

namespace W1c1
/-- nat acting on nat by s • m = m * m * s -/
def sqAct : SMulZeroClass ℕ ℕ := { smul := fun s m => m * m * s, smul_zero := fun s => by show 0 * 0 * s = 0; simp }
end W1c1

-- `Finsupp.smulCommClass` idx 7: necessary (R = nat acting by multiplication, S = nat acting by s • m = m * m * s)
theorem c1_156 : ¬ drop0% Finsupp.smulCommClass 7 := fun h => by
  have := DFunLike.congr_fun ((@h Unit ℕ ℕ ℕ _ _ sqAct).smul_comm (2 : ℕ) (1 : ℕ) (single () (1 : ℕ))) ()
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same] at this
  exact absurd this (by decide)

namespace W1c1
/-- the zero action of natᵐᵒᵖ on nat -/
def zeroOpAct : SMulZeroClass ℕᵐᵒᵖ ℕ := { smul := fun _ _ => 0, smul_zero := fun _ => rfl }
end W1c1

-- `Finsupp.isCentralScalar` idx 6: necessary (the opposite action is zero)
theorem c1_157 : ¬ drop0% Finsupp.isCentralScalar 6 := fun h => by
  have := DFunLike.congr_fun ((@h Unit ℕ ℕ _ _ zeroOpAct).op_smul_eq_smul 1 (single () (1 : ℕ))) ()
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same] at this
  exact absurd this (by decide)

-- `Finsupp.mapRange_smul'` idx 10: necessary (f = const 1, c = d = 1)
theorem c1_158 : ¬ indep0% Finsupp.mapRange_smul' 10 := fun h => by
  have := @h Unit ℕ ℕ ℕ ℕ _ _ _ _ (fun _ => 1) 1 1 0 (fun x => by simp)
  simp at this

-- `Finsupp.mapRange_smul'` idx 14: necessary (f = id, c = 1, d = 0)
theorem c1_159 : ¬ drop0% Finsupp.mapRange_smul' 14 := fun h => by
  have := DFunLike.congr_fun (@h Unit ℕ ℕ ℕ ℕ _ _ _ _ id rfl 1 0 (single () 1)) ()
  simp at this

-- `Finsupp.mapRange_smul` idx 9: necessary (f = const 1, c = 1)
theorem c1_160 : ¬ indep0% Finsupp.mapRange_smul 9 := fun h => by
  have := @h Unit ℕ ℕ ℕ _ _ _ _ (fun _ => 1) 1 0 (fun x => by simp)
  simp at this

-- `Finsupp.mapRange_smul` idx 12: necessary (f m = m * m, c = 2)
theorem c1_161 : ¬ drop0% Finsupp.mapRange_smul 12 := fun h => by
  have := DFunLike.congr_fun (@h Unit ℕ ℕ ℕ _ _ _ _ (fun m => m * m) (by simp) 2 (single () 1)) ()
  simp at this


-- `Finsupp.sum_option_index` idx 8: removable (with b o 0 = 0 both sides are sums over a common finite superset of the support, split at none; additivity is not used)
theorem c1_162 : drop% Finsupp.sum_option_index 8 := by
  intro α M N _ _ f b h0
  classical
  have hs : f.support ⊆ insert none (f.some.support.map Function.Embedding.some) := by
    intro x hx
    cases x with
    | none => simp
    | some a => simpa [Finsupp.mem_support_iff] using hx
  rw [Finsupp.sum_of_support_subset f hs b (fun x _ => h0 x), Finset.sum_insert (by simp), Finset.sum_map]
  simp [Finsupp.sum]

-- `Finsupp.prod_option_index` idx 8: removable (with b o 0 = 1 both sides are products over a common finite superset of the support; multiplicativity is not used)
theorem c1_163 : drop% Finsupp.prod_option_index 8 := by
  intro α M N _ _ f b h0
  classical
  have hs : f.support ⊆ insert none (f.some.support.map Function.Embedding.some) := by
    intro x hx
    cases x with
    | none => simp
    | some a => simpa [Finsupp.mem_support_iff] using hx
  rw [Finsupp.prod_of_support_subset f hs b (fun x _ => h0 x), Finset.prod_insert (by simp), Finset.prod_map]
  simp [Finsupp.prod]

-- `Finsupp.nonTorsionWeight_of` idx 7: necessary (R = M = ZMod 4, w = 2: 2 • 2 = 0)
theorem c1_164 : ¬ drop0% Finsupp.nonTorsionWeight_of 7 := fun h => by
  have := (@h Unit (ZMod 4) (ZMod 4) _ (fun _ => 2) _ _ _ (fun _ => by decide)).eq_zero_of_smul_eq_zero
    (r := 2) (s := ()) (by decide)
  exact absurd this (by decide)

-- `Finsupp.NonTorsionWeight.ne_zero` idx 7: necessary (R = M = Unit)
theorem c1_165 : ¬ drop0% Finsupp.NonTorsionWeight.ne_zero 7 := fun h =>
  @h Unit Unit Unit _ (fun _ => ()) _ _ ⟨fun {_ _} _ => Subsingleton.elim _ _⟩ () (Subsingleton.elim _ _)

-- `Finsupp.le_weight` idx 3: necessary (w = 0, f = single 1)
theorem c1_166 : ¬ drop0% Finsupp.le_weight 3 := fun h => by
  have := @h Unit 0 () (single () 1)
  rw [Finsupp.weight_single] at this; simp at this

-- `Finsupp.le_weight_of_ne_zero` idx 4: necessary (M = W, w = w2 ≥ 0, f = single 2: w2 ≰ 2 • w2 = w1)
theorem c1_167 : ¬ drop0% Finsupp.le_weight_of_ne_zero 4 := fun h => by
  have := @h Unit W _ _ (fun _ => w2) (fun _ => w0_le_w2) () (single () 2) (by simp)
  rw [Finsupp.weight_single, two_smul_w2] at this; exact not_w2_le_w1 this

-- `Finsupp.le_weight_of_ne_zero` idx 6: necessary (int, w = -1, f = single 2)
theorem c1_168 : ¬ drop0% Finsupp.le_weight_of_ne_zero 6 := fun h => by
  have := @h Unit ℤ _ _ _ (fun _ => -1) () (single () 2) (by simp)
  rw [Finsupp.weight_single] at this; simp at this

-- `Finsupp.le_weight_of_ne_zero'` idx 5: necessary (int, w = -1, f = single 2)
theorem c1_169 : ¬ drop0% Finsupp.le_weight_of_ne_zero' 5 := fun h => by
  have := @h Unit ℤ _ _ _ (fun _ => -1) () (single () 2) (by simp)
  rw [Finsupp.weight_single] at this; simp at this

-- `Finsupp.le_weight_of_ne_zero'` idx 4: removable (canonical order: w s ≤ n • w s + w s ≤ weight w f; monotonicity of addition is not needed)
theorem c1_170 : drop% Finsupp.le_weight_of_ne_zero' 4 := by
  intro σ M _ _ _ w s f hs
  classical
  rw [Finsupp.weight_apply, Finsupp.sum, ← Finset.add_sum_erase _ _ (Finsupp.mem_support_iff.2 hs)]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hs
  rw [hn, succ_nsmul]
  exact le_add_self.trans le_self_add

-- `Finsupp.weight_eq_zero_iff_eq_zero` idx 4: removable (canonical order: each term f s • w s is below the weight, so it vanishes, and NonTorsionWeight gives f s = 0)
theorem c1_171 : drop% Finsupp.weight_eq_zero_iff_eq_zero 4 := by
  intro σ M _ _ _ w _ f
  classical
  constructor
  · intro h
    ext s
    by_contra hs
    have h1 : f s • w s ≤ Finsupp.weight w f := by
      rw [Finsupp.weight_apply, Finsupp.sum, ← Finset.add_sum_erase _ _ (Finsupp.mem_support_iff.2 hs)]
      exact le_self_add
    rw [h] at h1
    exact hs (Finsupp.NonTorsionWeight.eq_zero_of_smul_eq_zero (le_antisymm h1 zero_le))
  · rintro rfl; simp

namespace W1c1
theorem ntwInt : Finsupp.NonTorsionWeight ℕ (fun b : Bool => if b then (1 : ℤ) else -1) :=
  ⟨fun {r s} h => by cases s <;> simpa using h⟩
end W1c1

-- `Finsupp.weight_eq_zero_iff_eq_zero` idx 5: necessary (int, w = (1, -1) on Bool, f = (1, 1) has weight 0)
theorem c1_172 : ¬ drop0% Finsupp.weight_eq_zero_iff_eq_zero 5 := fun h => by
  have := (@h Bool ℤ _ _ _ (fun b => if b then 1 else -1) ntwInt (single true 1 + single false 1)).1
    (by rw [Finsupp.weight_apply, p2_sum _ _ one_ne_zero one_ne_zero]; simp)
  simpa using DFunLike.congr_fun this true

-- `Finsupp.weight_eq_zero_iff_eq_zero` idx 7: necessary (w = 0, f = single 1)
theorem c1_173 : ¬ drop0% Finsupp.weight_eq_zero_iff_eq_zero 7 := fun h => by
  have := (@h Unit ℕ _ _ _ _ 0 (single () 1)).1 (by rw [Finsupp.weight_single]; simp)
  simpa using DFunLike.congr_fun this ()

namespace W1c1
theorem singles_inj : Function.Injective (fun n : ℕ => (single n 1 : ℕ →₀ ℕ)) :=
  Finsupp.single_left_injective one_ne_zero
theorem singleU_inj : Function.Injective (fun n : ℕ => (single () n : Unit →₀ ℕ)) :=
  Finsupp.single_injective ()
end W1c1

-- `Finsupp.finite_of_nat_weight_le` idx 1: necessary (sigma = nat, w = 1: all single n 1 have weight 1)
theorem c1_174 : ¬ drop0% Finsupp.finite_of_nat_weight_le 1 := fun h =>
  Set.infinite_of_injective_forall_mem singles_inj (fun n => by simp [Finsupp.weight_single])
    (@h ℕ (fun _ => 1) (fun _ => one_ne_zero) 1)

-- `Finsupp.finite_of_nat_weight_le` idx 3: necessary (sigma = Unit, w = 0)
theorem c1_175 : ¬ drop0% Finsupp.finite_of_nat_weight_le 3 := fun h =>
  Set.infinite_of_injective_forall_mem singleU_inj (fun n => by simp [Finsupp.weight_single])
    (@h Unit _ 0 0)

-- `Finsupp.finite_of_nat_weight_lt` idx 1: necessary (sigma = nat, w = 1, n = 2)
theorem c1_176 : ¬ drop0% Finsupp.finite_of_nat_weight_lt 1 := fun h =>
  Set.infinite_of_injective_forall_mem singles_inj (fun n => by simp [Finsupp.weight_single])
    (@h ℕ (fun _ => 1) (fun _ => one_ne_zero) 2)

-- `Finsupp.finite_of_nat_weight_lt` idx 3: necessary (sigma = Unit, w = 0, n = 1)
theorem c1_177 : ¬ drop0% Finsupp.finite_of_nat_weight_lt 3 := fun h =>
  Set.infinite_of_injective_forall_mem singleU_inj (fun n => by simp [Finsupp.weight_single])
    (@h Unit _ 0 1)

-- `Finsupp.finite_of_nat_weight_eq` idx 1: necessary (sigma = nat, w = 1, n = 1)
theorem c1_178 : ¬ drop0% Finsupp.finite_of_nat_weight_eq 1 := fun h =>
  Set.infinite_of_injective_forall_mem singles_inj (fun n => by simp [Finsupp.weight_single])
    (@h ℕ (fun _ => 1) (fun _ => one_ne_zero) 1)

-- `Finsupp.finite_of_nat_weight_eq` idx 3: necessary (sigma = Unit, w = 0, n = 0)
theorem c1_179 : ¬ drop0% Finsupp.finite_of_nat_weight_eq 3 := fun h =>
  Set.infinite_of_injective_forall_mem singleU_inj (fun n => by simp [Finsupp.weight_single])
    (@h Unit _ 0 0)

-- `Finsupp.finite_of_degree_le` idx 1: necessary (sigma = nat: all single n 1 have degree 1)
theorem c1_180 : ¬ drop0% Finsupp.finite_of_degree_le 1 := fun h =>
  Set.infinite_of_injective_forall_mem singles_inj (fun n => by simp [Finsupp.degree_single]) (@h ℕ 1)

-- `Finsupp.finite_of_degree_lt` idx 1: necessary (sigma = nat, n = 2)
theorem c1_181 : ¬ drop0% Finsupp.finite_of_degree_lt 1 := fun h =>
  Set.infinite_of_injective_forall_mem singles_inj (fun n => by simp [Finsupp.degree_single]) (@h ℕ 2)

-- `Finsupp.finite_of_degree_eq` idx 1: necessary (sigma = nat, n = 1)
theorem c1_182 : ¬ drop0% Finsupp.finite_of_degree_eq 1 := fun h =>
  Set.infinite_of_injective_forall_mem singles_inj (fun n => by simp [Finsupp.degree_single]) (@h ℕ 1)

namespace W1c1
theorem degree_p2 {R : Type} [AddCommMonoid R] (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    Finsupp.degree (single true a + single false b) = a + b := by
  show (single true a + single false b).sum (fun _ v => v) = a + b
  rw [p2_sum _ _ ha hb]
end W1c1

-- `Finsupp.degree_eq_zero_iff` idx 4: necessary (int, d = (1, -1))
theorem c1_183 : ¬ drop0% Finsupp.degree_eq_zero_iff 4 := fun h => by
  have := (@h Bool ℤ _ _ (single true 1 + single false (-1))).1
    (by rw [degree_p2 _ _ one_ne_zero (by norm_num)]; simp)
  simpa using DFunLike.congr_fun this true

-- `Finsupp.le_degree` idx 4: necessary (int, f = (1, -1), s = true)
theorem c1_184 : ¬ drop0% Finsupp.le_degree 4 := fun h => by
  have := @h Bool ℤ _ _ true (single true 1 + single false (-1))
  rw [degree_p2 _ _ one_ne_zero (by norm_num)] at this; simp at this

-- `Finsupp.degree_comapDomain_le_of_canonicallyOrderedAdd` idx 6: necessary (int, x = (1, -1), f : Unit → Bool picks true)
theorem c1_185 : ¬ drop0% Finsupp.degree_comapDomain_le_of_canonicallyOrderedAdd 6 := fun h => by
  have := @h Unit ℤ Bool (fun _ => true) _ _ (single true 1 + single false (-1))
    (by intro a _ b _ _; exact Subsingleton.elim a b)
  rw [degree_p2 _ _ one_ne_zero (by norm_num), Finsupp.degree_eq_sum, Fintype.sum_unique] at this
  simp [Finsupp.comapDomain_apply] at this

-- `Finsupp.degree_comapDomain_le_of_canonicallyOrderedAdd` idx 8: necessary (f : Bool → Unit constant, x = single () 1)
theorem c1_186 : ¬ indep0% Finsupp.degree_comapDomain_le_of_canonicallyOrderedAdd 8 := fun h => by
  have := @h Bool ℕ Unit (fun _ => ()) _ _ _ (single () 1)
  exact Bool.noConfusion (this (show true ∈ _ by simp) (show false ∈ _ by simp) rfl)

-- `Finsupp.degree_mono` idx 4: necessary (R = Fin 2: single true 1 ≤ (1, 1) but degrees 1 vs 0)
theorem c1_187 : ¬ drop0% Finsupp.degree_mono 4 := fun h => by
  have := @h Bool (Fin 2) _ _ (single true 1) (single true 1 + single false 1)
    (Finsupp.le_def.2 fun i => by cases i <;> simp)
  rw [degree_p2 _ _ (by decide) (by decide), Finsupp.degree_single] at this
  exact absurd this (by decide)

-- `Finsupp.degree_strictMono` idx 5: necessary (R = ENat: single true top < (top, 1), degrees top = top)
theorem c1_188 : ¬ drop0% Finsupp.degree_strictMono 5 := fun h => by
  have := @h Bool ℕ∞ _ _ _ (single true ⊤) (single true ⊤ + single false 1)
    (lt_of_le_of_ne (Finsupp.le_def.2 fun i => by cases i <;> simp)
      (fun e => by simpa using DFunLike.congr_fun e false))
  rw [degree_p2 _ _ (by simp) one_ne_zero, Finsupp.degree_single] at this
  simp at this

-- `Finsupp.degree_strictMono` idx 4: removable (sum over the union of supports; Finset.sum_lt_sum needs only IsOrderedCancelAddMonoid)
theorem c1_189 : drop% Finsupp.degree_strictMono 4 := by
  intro σ R _ _ _ f g hfg
  classical
  have hle : ∀ i, f i ≤ g i := Finsupp.le_def.1 hfg.le
  obtain ⟨j, hj⟩ : ∃ j, f j < g j := by
    by_contra hc
    exact hfg.ne (Finsupp.ext fun i => (hle i).eq_of_not_lt (fun hlt => hc ⟨i, hlt⟩))
  have hf : Finsupp.degree f = ∑ i ∈ f.support ∪ g.support, f i :=
    Finset.sum_subset Finset.subset_union_left (fun i _ hi => by simpa using hi)
  have hg : Finsupp.degree g = ∑ i ∈ f.support ∪ g.support, g i :=
    Finset.sum_subset Finset.subset_union_right (fun i _ hi => by simpa using hi)
  rw [hf, hg]
  refine Finset.sum_lt_sum (fun i _ => hle i) ⟨j, ?_, hj⟩
  by_contra hn
  simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hn
  rw [hn.1, hn.2] at hj; exact lt_irrefl _ hj

open scoped Pointwise

-- `Finsupp.degree_preimage_nsmul` idx 3: removable (for n = 0 both sides are the set 0 = {0}: 0 • s = 0 for the iterated pointwise addition, and degree f = 0 iff f = 0)
theorem c1_190 : drop% Finsupp.degree_preimage_nsmul 3 := by
  intro σ s n
  rcases n with _ | n
  · rw [zero_nsmul, zero_nsmul]; ext f; simp [Finsupp.degree_eq_zero_iff]
  · exact Finsupp.degree_preimage_nsmul s (n + 1) (Nat.succ_ne_zero n)
