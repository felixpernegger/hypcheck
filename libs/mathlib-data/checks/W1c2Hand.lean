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

namespace W1c2
def RQ := ℚ
instance : Field RQ := inferInstanceAs (Field ℚ)
instance : LinearOrder RQ := inferInstanceAs (LinearOrder ℚᵒᵈ)
def RZ := ℤ
instance : CommRing RZ := inferInstanceAs (CommRing ℤ)
instance : LinearOrder RZ := inferInstanceAs (LinearOrder ℤᵒᵈ)
instance : AddLeftMono RZ := inferInstanceAs (AddLeftMono ℤᵒᵈ)
instance : NeZero (1:RZ) := ⟨one_ne_zero (α := ℤ)⟩
instance : IsOrderedRing Unit where
  add_le_add_left := by intros; exact le_rfl
  zero_le_one := le_rfl
  mul_le_mul_of_nonneg_left := by intros; exact le_rfl
  mul_le_mul_of_nonneg_right := by intros; exact le_rfl
def F2 := ZMod 2
instance : DecidableEq F2 := inferInstanceAs (DecidableEq (ZMod 2))
instance : LinearOrder F2 := inferInstanceAs (LinearOrder (Fin 2))
noncomputable instance : Field F2 := IsField.toField (R := ZMod 2) ⟨⟨0, 1, by decide⟩, mul_comm,
  by intro a h; exact ⟨a, by revert a; decide⟩⟩
theorem F2_two : ((2:ℕ):F2) = 0 := by decide
theorem F2_fact2 : ((Nat.factorial 2 : ℕ) : F2) = 0 := by decide
end W1c2
open W1c2

namespace W1c2
def bad : ℕ → ℕ := fun n => if n = 2 then 3 else 1
theorem bad_not : ¬ IsDvdSequence bad := fun h => absurd (h 2 4 (by decide)) (by decide)
theorem one_dvdseq : IsDvdSequence (fun _ : ℕ => (1:ℕ)) := fun _ _ _ => dvd_refl _
abbrev M := FreeMonoid Bool
def mf : M := FreeMonoid.ofList [false]
def mft : M := FreeMonoid.ofList [false, true]
def gM : ℕ → M := fun n => if n = 1 then mf else mft
theorem mf_dvd : mf ∣ mft := ⟨FreeMonoid.ofList [true], rfl⟩
theorem gM_dvdseq : IsDvdSequence gM := by
  intro a b hab
  by_cases ha : a = 1
  · subst ha; by_cases hb : b = 1
    · simp [gM, hb]
    · simp [gM, hb, mf_dvd]
  · have hb : b ≠ 1 := fun hb => ha (Nat.dvd_one.1 (hb ▸ hab))
    simp [gM, ha, hb]
theorem not_dvd1 : ¬ (mf * mf ∣ mft * mf) := by
  rintro ⟨c, hc⟩; have := congrArg FreeMonoid.toList hc; simp [mf, mft] at this
def B := ℕ
instance : Monoid B := inferInstanceAs (Monoid ℕ)
def uB : B → ℕ := fun b : ℕ => if b = 2 then 2 else 1
instance : SMul B ℕ := ⟨fun b x => uB b * x⟩
instance : IsScalarTower B ℕ ℕ := ⟨fun b x y => by
  show uB b * x * y = uB b * (x * y); ring⟩
instance : SMulCommClass B ℕ ℕ := ⟨fun b x y => by
  show uB b * (x * y) = x * (uB b * y); ring⟩
def fB : ℕ → B := fun n => if n = 1 then (2:ℕ) else (4:ℕ)
theorem fB_dvdseq : IsDvdSequence fB := by
  intro a b hab
  by_cases ha : a = 1
  · subst ha; by_cases hb : b = 1
    · simp only [fB, hb]; exact dvd_refl _
    · simp only [fB, hb]; exact (⟨(2:ℕ), rfl⟩ : ((2:ℕ):B) ∣ ((4:ℕ):B))
  · have hb : b ≠ 1 := fun hb => ha (Nat.dvd_one.1 (hb ▸ hab))
    simp only [fB, ha, hb]; exact dvd_refl _
end W1c2

namespace W1c2
theorem zeros {b : ℕ} {L : List ℕ} (h : ∀ l ∈ L, l < b) (hb : b ≤ 1) :
    L = List.replicate L.length 0 :=
  List.eq_replicate_iff.2 ⟨rfl, fun x hx => by have := h x hx; omega⟩
theorem ofDigits_rep0 (b n : ℕ) : Nat.ofDigits b (List.replicate n 0) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, Nat.ofDigits_cons, ih]
end W1c2

namespace W1c2
def N1 := ℕ
instance : CommSemiring N1 := inferInstanceAs (CommSemiring ℕ)
instance : PartialOrder N1 := inferInstanceAs (PartialOrder ℕ)
instance : CanonicallyOrderedAdd N1 := inferInstanceAs (CanonicallyOrderedAdd ℕ)
instance : AddLeftReflectLE N1 := inferInstanceAs (AddLeftReflectLE ℕ)
instance : DecidableEq N1 := inferInstanceAs (DecidableEq ℕ)
instance : Sub N1 := ⟨fun _ _ => (0 : ℕ)⟩
end W1c2

namespace W1c2
def BS := Bool
instance : DecidableEq BS := inferInstanceAs (DecidableEq Bool)
instance : Zero BS := ⟨false⟩
instance : One BS := ⟨true⟩
instance : Add BS := ⟨or⟩
instance : Mul BS := ⟨and⟩
instance : NatCast BS := ⟨fun n => decide (n ≠ 0)⟩
instance : CommSemiring BS where
  natCast_zero := rfl
  natCast_succ := by intro n; cases n <;> rfl
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul := by intro a; cases a <;> rfl
  mul_one := by intro a; cases a <;> rfl
  zero_mul := by intro a; cases a <;> rfl
  mul_zero := by intro a; cases a <;> rfl
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  right_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  mul_comm := by intro a b; cases a <;> cases b <;> rfl
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  npow := npowRec
  npow_zero := fun _ => rfl
  npow_succ := fun _ _ => rfl
instance : Fintype BS := inferInstanceAs (Fintype Bool)
instance : PartialOrder BS := inferInstanceAs (PartialOrder Bool)
instance : DecidableRel (α := BS) (· ≤ ·) := inferInstanceAs (DecidableRel (α := Bool) (· ≤ ·))
instance : Sub BS := ⟨fun a b => (a && !b : Bool)⟩
instance : CanonicallyOrderedAdd BS where
  exists_add_of_le := by
    intro a b h; revert a b; decide
  le_add_self := by decide
  le_self_add := by decide
instance : OrderedSub BS := ⟨by decide⟩
end W1c2

-- `Nat.cast_inv_le_one` idx 3: necessary
theorem c2_1 : ¬ drop0% Nat.cast_inv_le_one 3 := fun h => by
  have := @h RQ _ _ 2; change (1:ℚ) ≤ ((2:ℕ):ℚ)⁻¹ at this; norm_num at this
-- `Nat.cast_div_le` idx 3: necessary
theorem c2_2 : ¬ drop0% Nat.cast_div_le 3 := fun h => by
  have := @h RQ _ _ 1 2; change ((1:ℕ):ℚ) / ((2:ℕ):ℚ) ≤ (((1/2 : ℕ)) : ℚ) at this; norm_num at this
-- `Nat.inv_pos_of_nat` idx 3: necessary
theorem c2_3 : ¬ drop0% Nat.inv_pos_of_nat 3 := fun h => by
  have := @h RQ _ _ 0; change (((0:ℕ):ℚ) + 1)⁻¹ < 0 at this; norm_num at this
-- `Nat.one_div_pos_of_nat` idx 3: necessary
theorem c2_4 : ¬ drop0% Nat.one_div_pos_of_nat 3 := fun h => by
  have := @h RQ _ _ 0; change 1 / (((0:ℕ):ℚ) + 1) < 0 at this; norm_num at this
-- `Nat.one_div_le_one_div` idx 3: necessary
theorem c2_5 : ¬ drop0% Nat.one_div_le_one_div 3 := fun h => by
  have := @h RQ _ _ 0 1 (by decide); change 1 / (((0:ℕ):ℚ) + 1) ≤ 1 / (((1:ℕ):ℚ) + 1) at this
  norm_num at this
-- `Nat.one_div_lt_one_div` idx 3: necessary
theorem c2_6 : ¬ drop0% Nat.one_div_lt_one_div 3 := fun h => by
  have := @h RQ _ _ 0 1 (by decide); change 1 / (((0:ℕ):ℚ) + 1) < 1 / (((1:ℕ):ℚ) + 1) at this
  norm_num at this
-- `Nat.one_div_cast_pos` idx 3: necessary
theorem c2_7 : ¬ drop0% Nat.one_div_cast_pos 3 := fun h => by
  have := @h RQ _ _ 1 (by decide); change 1 / ((1:ℕ):ℚ) < 0 at this; norm_num at this
-- `Nat.one_div_cast_nonneg` idx 3: necessary
theorem c2_8 : ¬ drop0% Nat.one_div_cast_nonneg 3 := fun h => by
  have := @h RQ _ _ 1; change 1 / ((1:ℕ):ℚ) ≤ 0 at this; norm_num at this
-- `Nat.one_div_cast_ne_zero` idx 3: necessary
theorem c2_9 : ¬ drop0% Nat.one_div_cast_ne_zero 3 := fun h => by
  have := @h F2 _ _ 2 (by decide); exact this (by rw [F2_two, div_zero])
-- `Nat.one_sub_one_div_cast_nonneg` idx 3: necessary
theorem c2_10 : ¬ drop0% Nat.one_sub_one_div_cast_nonneg 3 := fun h => by
  have := @h RQ _ _ 2; change 1 - 1 / ((2:ℕ):ℚ) ≤ 0 at this; norm_num at this
-- `Nat.one_sub_one_div_cast_le_one` idx 3: necessary
theorem c2_11 : ¬ drop0% Nat.one_sub_one_div_cast_le_one 3 := fun h => by
  have := @h RQ _ _ 2; change (1:ℚ) ≤ 1 - 1 / ((2:ℕ):ℚ) at this; norm_num at this
-- `Nat.cast_nonneg` idx 3: necessary
theorem c2_12 : ¬ drop0% Nat.cast_nonneg 3 := fun h => by
  have := @h RQ _ _ 1; change ((1:ℕ):ℚ) ≤ 0 at this; norm_num at this
-- `Nat.ofNat_nonneg` idx 3: necessary
theorem c2_13 : ¬ drop0% Nat.ofNat_nonneg 3 := fun h => by
  have := @h RQ _ _ 2 _; change ((2:ℕ):ℚ) ≤ 0 at this; norm_num at this
-- `Nat.cast_pos` idx 4: necessary
theorem c2_14 : ¬ drop0% Nat.cast_pos 4 := fun h => by
  have := (@h Unit _ _ _ 1).mpr one_pos; exact lt_irrefl _ this
-- `Nat.ofNat_pos'` idx 4: necessary
theorem c2_15 : ¬ drop0% Nat.ofNat_pos' 4 := fun h => by
  have := @h RZ _ _ _ _ 2 _; change ((2:ℕ):ℤ) < 0 at this; norm_num at this
-- `Nat.ofNat_pos'` idx 5: necessary
theorem c2_16 : ¬ drop0% Nat.ofNat_pos' 5 := fun h => by
  have := @h Unit _ _ _ _ 2 _; exact lt_irrefl _ this
-- `Nat.ofNat_pos` idx 4: necessary
theorem c2_17 : ¬ drop0% Nat.ofNat_pos 4 := fun h => by
  have := @h Unit _ _ _ 2 _; exact lt_irrefl _ this
-- `Nat.cast_tsub` idx 3: necessary
theorem c2_18 : ¬ drop0% Nat.cast_tsub 3 := fun h => by
  have := @h ℤ _ _ _ _ _ 1 2; norm_num at this
-- `Nat.abs_cast` idx 3: necessary
theorem c2_19 : ¬ drop0% Nat.abs_cast 3 := fun h => by
  have := @h RZ _ _ 1; revert this; decide
-- `Nat.abs_ofNat` idx 3: necessary
theorem c2_20 : ¬ drop0% Nat.abs_ofNat 3 := fun h => by
  have := @h RZ _ _ 2 _; revert this; decide
-- `Nat.modEq_list_prod_iff` idx 3: necessary
theorem c2_21 : ¬ drop0% Nat.modEq_list_prod_iff 3 := fun h => by
  have := @h 0 2 [2,2]; revert this; decide
-- `Nat.modEq_list_map_prod_iff` idx 5: necessary
theorem c2_22 : ¬ drop0% Nat.modEq_list_map_prod_iff 5 := fun h => by
  have := @h ℕ 0 2 id [2,2]; revert this; decide
-- `Nat.chineseRemainderOfList_perm` idx 7: necessary
theorem c2_23 : ¬ indep0% Nat.chineseRemainderOfList_perm 7 := fun h => by
  have := @h ℕ (fun _ => 0) id [2,2] [2,2] (List.Perm.refl _) (by decide); revert this; decide
-- `Nat.choose_le_pow_div` idx 3: necessary
theorem c2_24 : ¬ drop0% Nat.choose_le_pow_div 3 := fun h => by
  have := @h RQ _ _ 2 2
  norm_num [Nat.factorial] at this; revert this; decide +kernel
-- `Nat.choose_lt_pow_div` idx 3: necessary
theorem c2_25 : ¬ drop0% Nat.choose_lt_pow_div 3 := fun h => by
  have := @h RQ _ _ 2 2 (by decide) le_rfl
  norm_num [Nat.factorial] at this; revert this; decide +kernel
-- `Nat.pow_le_choose` idx 3: necessary
theorem c2_26 : ¬ drop0% Nat.pow_le_choose 3 := fun h => by
  have := @h RQ _ _ 2 2
  norm_num [Nat.factorial] at this; revert this; decide +kernel
-- `Nat.cast_choose` idx 2: necessary
theorem c2_27 : ¬ drop0% Nat.cast_choose 2 := fun h => by
  have := @h F2 _ 0 2 (by decide)
  rw [F2_fact2, zero_div] at this; simp at this
-- `Nat.cast_add_choose` idx 2: necessary
theorem c2_28 : ¬ drop0% Nat.cast_add_choose 2 := fun h => by
  have := @h F2 _ 0 2
  rw [show (0 + 2 : ℕ) = 2 from rfl, F2_fact2, zero_div] at this; simp at this
-- `Nat.cast_choose_two` idx 2: necessary
theorem c2_29 : ¬ drop0% Nat.cast_choose_two 2 := fun h => by
  have := @h F2 _ 2
  rw [show ((2:ℕ):F2) = 0 from F2_two] at this; simp at this

instance W1c2.fact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
instance W1c2.fact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

-- `Nat.chineseRemainderOfMultiset_lt_prod` idx 6: necessary
theorem c2_30 : ¬ indep0% Nat.chineseRemainderOfMultiset_lt_prod 6 := fun h => by
  have := h (ι := ℕ) (a := fun _ => 0) (s := fun _ => 2) (m := {0, 1}) (by decide) (by decide)
  have := this (x := 0) (by simp) (y := 1) (by simp) (by decide)
  revert this; decide
-- `Choose.choose_modEq_prod_range_choose` idx 3: necessary
theorem c2_31 : ¬ drop0% Choose.choose_modEq_prod_range_choose 3 := fun h => by
  have := @h 6 2 4 2 (by decide) (by decide); revert this; decide +kernel
-- `Choose.choose_modEq_prod_range_choose_nat` idx 3: necessary
theorem c2_32 : ¬ drop0% Choose.choose_modEq_prod_range_choose_nat 3 := fun h => by
  have := @h 6 2 4 2 (by decide) (by decide); revert this; decide +kernel
-- `Choose.lucas_theorem` idx 3: necessary
theorem c2_33 : ¬ drop0% Choose.lucas_theorem 3 := fun h => by
  have := @h 6 2 4 2 (by decide) (by decide); revert this; decide +kernel
-- `Choose.lucas_theorem_nat` idx 3: necessary
theorem c2_34 : ¬ drop0% Choose.lucas_theorem_nat 3 := fun h => by
  have := @h 6 2 4 2 (by decide) (by decide); revert this; decide +kernel
-- `Choose.eq_pow_multiplicity_of_choose_modEq_zero` idx 3: necessary
theorem c2_35 : ¬ drop0% Choose.eq_pow_multiplicity_of_choose_modEq_zero 3 := fun h => by
  have := @h 0 2 _ (by intro i hi; simp at hi)
  exact absurd this.symm (pow_ne_zero _ two_ne_zero)
-- `Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat` idx 3: necessary
theorem c2_36 : ¬ drop0% Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat 3 := fun h => by
  have := @h 0 2 _ (by intro i hi; simp at hi)
  exact absurd this.symm (pow_ne_zero _ two_ne_zero)
-- `Choose.eq_pow_multiplicity_of_choose_modEq_zero` idx 4: necessary
theorem c2_37 : ¬ drop0% Choose.eq_pow_multiplicity_of_choose_modEq_zero 4 := fun h => by
  have := @h 2 3 _ (by decide)
  generalize multiplicity 3 2 = k at this
  rcases k with _ | k
  · simp at this
  · have := Nat.le_self_pow (Nat.succ_ne_zero k) 3; omega
-- `Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat` idx 4: necessary
theorem c2_38 : ¬ drop0% Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat 4 := fun h => by
  have := @h 2 3 _ (by decide)
  generalize multiplicity 3 2 = k at this
  rcases k with _ | k
  · simp at this
  · have := Nat.le_self_pow (Nat.succ_ne_zero k) 3; omega
-- `Nat.multinomial_congr_of_eq_on_inter` idx 6: necessary
theorem c2_39 : ¬ drop0% Nat.multinomial_congr_of_eq_on_inter 6 := fun h => by
  have := @h (Fin 2) _ (fun _ => 1) (fun _ => 1) Finset.univ ∅ (by decide) (by decide)
  revert this; decide +kernel
-- `Nat.multinomial_congr_of_eq_on_inter` idx 7: necessary
theorem c2_40 : ¬ drop0% Nat.multinomial_congr_of_eq_on_inter 7 := fun h => by
  have := @h (Fin 2) _ (fun _ => 1) (fun _ => 1) ∅ Finset.univ (by decide) (by decide)
  revert this; decide +kernel
-- `Nat.multinomial_congr_of_eq_on_inter` idx 8: necessary
theorem c2_41 : ¬ drop0% Nat.multinomial_congr_of_eq_on_inter 8 := fun h => by
  have := @h (Fin 2) _ (fun _ => 1) (fun i => if i = 0 then 1 else 0) Finset.univ Finset.univ
    (by decide) (by decide)
  revert this; decide +kernel
-- `Nat.multinomial_congr_of_sdiff` idx 6: necessary
theorem c2_42 : ¬ drop0% Nat.multinomial_congr_of_sdiff 6 := fun h => by
  have := @h (Fin 2) _ (fun _ => 1) (fun _ => 1) Finset.univ ∅ (by decide) (by decide)
  revert this; decide +kernel
-- `Nat.multinomial_congr_of_sdiff` idx 7: necessary
theorem c2_43 : ¬ drop0% Nat.multinomial_congr_of_sdiff 7 := fun h => by
  have := @h (Fin 2) _ (fun _ => 1) (fun _ => 1) ∅ Finset.univ (by decide) (by decide)
  revert this; decide +kernel
-- `Nat.multinomial_congr_of_sdiff` idx 8: necessary
theorem c2_44 : ¬ drop0% Nat.multinomial_congr_of_sdiff 8 := fun h => by
  have := @h (Fin 2) _ (fun _ => 1) (fun i => if i = 0 then 1 else 0) Finset.univ Finset.univ
    (by decide) (by decide)
  revert this; decide +kernel
-- `Finsupp.multinomial_eq_of_support_subset` idx 3: necessary
theorem c2_45 : ¬ drop0% Finsupp.multinomial_eq_of_support_subset 3 := fun h => by
  let d : Bool →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)
  have := @h Bool d ∅
  rw [Finsupp.multinomial_eq_of_support_subset (s := Finset.univ) (Finset.subset_univ _)] at this
  have hs := Nat.multinomial_spec (Finset.univ : Finset Bool) d
  rw [this, Nat.multinomial_empty] at hs
  simp [d] at hs
-- `Finset.sum_pow_of_commute` idx 6: necessary
theorem c2_46 : ¬ indep0% Finset.sum_pow_of_commute 6 := fun h => by
  let f : Bool → Matrix (Fin 2) (Fin 2) ℕ := fun b => if b then !![1, 0; 0, 0] else !![0, 1; 0, 0]
  have := @h Bool (Matrix (Fin 2) (Fin 2) ℕ) _ _ f Finset.univ
  have hc : Commute (f true) (f false) :=
    this 0 (Finset.mem_coe.2 (Finset.mem_univ true)) (Finset.mem_coe.2 (Finset.mem_univ false)) (by decide)
  have := congrFun (congrFun hc.eq 0) 1
  simp [f, Matrix.mul_apply, Fin.sum_univ_two] at this
-- `Commute.add_pow` idx 4: necessary
theorem c2_47 : ¬ drop0% Commute.add_pow 4 := fun h => by
  have := congrFun (congrFun (@h (Matrix (Fin 2) (Fin 2) ℕ) _ !![1, 0; 0, 0] !![0, 1; 0, 0] 2) 0) 1
  simp [Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_two, pow_two] at this; revert this; decide
-- `Commute.add_pow'` idx 4: necessary
theorem c2_48 : ¬ drop0% Commute.add_pow' 4 := fun h => by
  have := congrFun (congrFun (@h (Matrix (Fin 2) (Fin 2) ℕ) _ !![1, 0; 0, 0] !![0, 1; 0, 0] 2) 0) 1
  simp [Finset.Nat.antidiagonal_succ, Matrix.mul_apply, Fin.sum_univ_two, pow_two] at this; revert this; decide
-- `Nat.count_le_card` idx 2: necessary
theorem c2_49 : ¬ indep0% Nat.count_le_card 2 := fun h =>
  Set.infinite_univ (α := ℕ) (by simpa [Set.ofPred] using @h (fun _ => True) _)
-- `Nat.count_lt_card` idx 3: necessary
theorem c2_50 : ¬ indep0% Nat.count_lt_card 3 := fun h =>
  Set.infinite_univ (α := ℕ) (by simpa [Set.ofPred] using @h (fun _ => True) _ 0 trivial)

-- `Nat.factorization_prod_apply` idx 4: necessary
theorem c2_51 : ¬ drop0% Nat.factorization_prod_apply 4 := fun h => by
  have := @h ℕ 2 {0, 1} (fun x => 2 * x)
  simp [Nat.prime_two.factorization_self] at this
-- `Nat.factorization_prod` idx 3: necessary
theorem c2_52 : ¬ drop0% Nat.factorization_prod 3 := fun h => by
  have := DFunLike.congr_fun (@h ℕ {0, 1} (fun x => 2 * x)) 2
  simp [Nat.prime_two.factorization_self] at this
-- `Nat.factorization_prime_le_iff_dvd` idx 3: necessary
theorem c2_53 : ¬ drop0% Nat.factorization_prime_le_iff_dvd 3 := fun h => by
  have := (h (d := 2) (n := 0) (by decide)).mpr (dvd_zero 2) 2 Nat.prime_two
  simp [Nat.prime_two.factorization_self] at this
-- `Nat.factorization_div` idx 2: necessary
theorem c2_54 : ¬ drop0% Nat.factorization_div 2 := fun h => by
  have := DFunLike.congr_fun (h (d := 2) (n := 3)) 3
  simp [Nat.prime_two.factorization, Nat.prime_three.factorization] at this
-- `Nat.dvd_ordProj_of_dvd` idx 3: necessary
theorem c2_55 : ¬ drop0% Nat.dvd_ordProj_of_dvd 3 := fun h => by
  have := h (n := 4) (p := 4) (by decide) (dvd_refl 4)
  simp [Nat.factorization_eq_zero_of_not_prime _ (by decide : ¬ Nat.Prime 4)] at this
-- `Nat.ordCompl_div_pow_of_dvd` idx 3: necessary
theorem c2_56 : ¬ drop0% Nat.ordCompl_div_pow_of_dvd 3 := fun h => by
  have := h 1 (x := 4) (p := 4) (by decide)
  simp [Nat.factorization_eq_zero_of_not_prime _ (by decide : ¬ Nat.Prime 4)] at this
-- `Nat.ordCompl_div_of_dvd` idx 2: necessary
theorem c2_57 : ¬ drop0% Nat.ordCompl_div_of_dvd 2 := fun h => by
  have := h (x := 4) (p := 4) (dvd_refl 4)
  simp [Nat.factorization_eq_zero_of_not_prime _ (by decide : ¬ Nat.Prime 4)] at this
-- `Nat.dvd_ordCompl_of_dvd_not_dvd` idx 4: necessary
theorem c2_58 : ¬ drop0% Nat.dvd_ordCompl_of_dvd_not_dvd 4 := fun h => by
  have := h (p := 2) (d := 2) (n := 2) (dvd_refl 2)
  simp [Nat.prime_two.factorization_self] at this
-- `Nat.dvd_iff_div_factorization_eq_tsub` idx 3: necessary
theorem c2_59 : ¬ drop0% Nat.dvd_iff_div_factorization_eq_tsub 3 := fun h => by
  have := (h (d := 2) (n := 1) (by decide)).mpr (by simp)
  revert this; decide
-- `Nat.factorization_lcm` idx 2: necessary
theorem c2_60 : ¬ drop0% Nat.factorization_lcm 2 := fun h => by
  have := DFunLike.congr_fun (h (a := 0) (b := 2) (by decide)) 2
  simp [Nat.prime_two.factorization_self] at this
-- `Nat.factorization_lcm` idx 3: necessary
theorem c2_61 : ¬ drop0% Nat.factorization_lcm 3 := fun h => by
  have := DFunLike.congr_fun (h (a := 2) (b := 0) (by decide)) 2
  simp [Nat.prime_two.factorization_self] at this
-- `Nat.setOfPred_pow_dvd_eq_Icc_factorization` idx 2: necessary
theorem c2_62 : ¬ drop0% Nat.setOfPred_pow_dvd_eq_Icc_factorization 2 := fun h => by
  have h1 : (1:ℕ) ∈ {i : ℕ | i ≠ 0 ∧ 4 ^ i ∣ 4} := ⟨one_ne_zero, by norm_num⟩
  rw [h (n := 4) (p := 4) (by decide)] at h1
  simp [Nat.factorization_eq_zero_of_not_prime _ (by decide : ¬ Nat.Prime 4)] at h1
-- `Nat.setOfPred_pow_dvd_eq_Icc_factorization` idx 3: necessary
theorem c2_63 : ¬ drop0% Nat.setOfPred_pow_dvd_eq_Icc_factorization 3 := fun h => by
  have h1 : (1:ℕ) ∈ {i : ℕ | i ≠ 0 ∧ 2 ^ i ∣ 0} := ⟨one_ne_zero, dvd_zero _⟩
  rw [h (n := 0) (p := 2) Nat.prime_two] at h1
  simp at h1
-- `Nat.setOf_pow_dvd_eq_Icc_factorization` idx 2: necessary
theorem c2_64 : ¬ drop0% Nat.setOf_pow_dvd_eq_Icc_factorization 2 := fun h => by
  have h1 : (1:ℕ) ∈ {i : ℕ | i ≠ 0 ∧ 4 ^ i ∣ 4} := ⟨one_ne_zero, by norm_num⟩
  rw [h (n := 4) (p := 4) (by decide)] at h1
  simp [Nat.factorization_eq_zero_of_not_prime _ (by decide : ¬ Nat.Prime 4)] at h1
-- `Nat.setOf_pow_dvd_eq_Icc_factorization` idx 3: necessary
theorem c2_65 : ¬ drop0% Nat.setOf_pow_dvd_eq_Icc_factorization 3 := fun h => by
  have h1 : (1:ℕ) ∈ {i : ℕ | i ≠ 0 ∧ 2 ^ i ∣ 0} := ⟨one_ne_zero, dvd_zero _⟩
  rw [h (n := 0) (p := 2) Nat.prime_two] at h1
  simp at h1
-- `Nat.eq_iff_prime_multiplicity_eq` idx 2: necessary
theorem c2_66 : ¬ drop0% Nat.eq_iff_prime_multiplicity_eq 2 := fun h => by
  have := (h 0 1 (by decide)).mpr (fun p _ => by simp)
  exact absurd this (by decide)
-- `Nat.eq_iff_prime_multiplicity_eq` idx 3: necessary
theorem c2_67 : ¬ drop0% Nat.eq_iff_prime_multiplicity_eq 3 := fun h => by
  have := (h 1 0 (by decide)).mpr (fun p _ => by simp)
  exact absurd this (by decide)
-- `Nat.eq_iff_prime_padicValNat_eq` idx 2: necessary
theorem c2_68 : ¬ drop0% Nat.eq_iff_prime_padicValNat_eq 2 := fun h => by
  have := (h 0 1 (by decide)).mpr (fun p _ => by simp)
  exact absurd this (by decide)
-- `Nat.eq_iff_prime_padicValNat_eq` idx 3: necessary
theorem c2_69 : ¬ drop0% Nat.eq_iff_prime_padicValNat_eq 3 := fun h => by
  have := (h 1 0 (by decide)).mpr (fun p _ => by simp)
  exact absurd this (by decide)
-- `Nat.exists_dvd_pow_iff` idx 3: necessary
theorem c2_70 : ¬ drop0% Nat.exists_dvd_pow_iff 3 := fun h => by
  have := (h (n := 2) (k := 0) (by decide)).mp ⟨1, by simp⟩
  simp [Nat.prime_two.primeFactors] at this
-- `Nat.factorization_prod_pow_eq_self` idx 1: necessary
theorem c2_71 : ¬ drop0% Nat.factorization_prod_pow_eq_self 1 := fun h => by
  have := DFunLike.congr_fun (h (f := Finsupp.single 4 1)) 4
  simp [Nat.factorization_eq_zero_of_not_prime _ (by decide : ¬ Nat.Prime 4)] at this
-- `Nat.prod_pow_factorization_eq_self` idx 1: necessary
theorem c2_72 : ¬ drop0% Nat.prod_pow_factorization_eq_self 1 := fun h => by
  have := DFunLike.congr_fun (h (f := Finsupp.single 4 1)) 4
  simp [Nat.factorization_eq_zero_of_not_prime _ (by decide : ¬ Nat.Prime 4)] at this
-- `Nat.eq_factorization_iff` idx 3: necessary
theorem c2_73 : ¬ drop0% Nat.eq_factorization_iff 3 := fun h => by
  have := DFunLike.congr_fun ((h (n := 4) (f := Finsupp.single 4 1) (by decide)).mpr (by simp)) 4
  simp [Nat.factorization_eq_zero_of_not_prime _ (by decide : ¬ Nat.Prime 4)] at this
-- `Nat.factorization_prod_pow_eq_self_of_le_factorization` idx 2: necessary
theorem c2_74 : ¬ drop0% Nat.factorization_prod_pow_eq_self_of_le_factorization 2 := fun h => by
  have := DFunLike.congr_fun (h (n := 0) (f := Finsupp.single 4 1)) 4
  simp [Nat.factorization_eq_zero_of_not_prime _ (by decide : ¬ Nat.Prime 4)] at this
-- `Nat.prod_pow_dvd_of_le_factorization` idx 2: necessary
theorem c2_75 : ¬ drop0% Nat.prod_pow_dvd_of_le_factorization 2 := fun h => by
  have := h (n := 1) (f := Finsupp.single 2 1)
  simp at this
-- `Nat.factorization_mul_of_coprime` idx 2: necessary
theorem c2_76 : ¬ drop0% Nat.factorization_mul_of_coprime 2 := fun h => by
  have := DFunLike.congr_fun (h (a := 0) (b := 2)) 2
  simp [Nat.prime_two.factorization_self] at this
-- `Nat.ordProj_dvd_ordProj_iff_dvd` idx 3: necessary
theorem c2_77 : ¬ drop0% Nat.ordProj_dvd_ordProj_iff_dvd 3 := fun h => by
  have := (h (a := 2) (b := 0) (by decide)).mpr (dvd_zero 2) 2
  simp [Nat.prime_two.factorization_self] at this

-- `smul_dvd_smul` idx 5: necessary
theorem c2_78 : ¬ drop0% smul_dvd_smul 5 := fun h => by
  have := h (α := Mᵐᵒᵖ) (β := M) (a := MulOpposite.op mf) (b := MulOpposite.op mf) (c := mf) (d := mft)
    (dvd_refl _) mf_dvd
  exact not_dvd1 this
-- `smul_dvd_smul` idx 6: necessary
theorem c2_79 : ¬ drop0% smul_dvd_smul 6 := fun h => by
  have := h (α := B) (β := ℕ) (a := ((2:ℕ):B)) (b := ((4:ℕ):B)) (c := 1) (d := 1)
    ⟨(2:ℕ), rfl⟩ (dvd_refl _)
  revert this; decide +kernel
-- `smul_dvd_smul` idx 7: necessary
theorem c2_80 : ¬ drop0% smul_dvd_smul 7 := fun h => by
  have := h (α := M) (β := M) (a := mf) (b := mft) (c := mf) (d := mf) mf_dvd (dvd_refl _)
  exact not_dvd1 this
-- `IsDvdSequence.smul'` idx 9: necessary
theorem c2_81 : ¬ drop0% IsDvdSequence.smul' 9 := fun h => by
  have := h (α := ℕ) (β := Mᵐᵒᵖ) (γ := M) (f := fun _ => MulOpposite.op mf) (g := gM)
    (fun _ _ _ => dvd_refl _) gM_dvdseq 1 2 (by decide)
  exact not_dvd1 this
-- `IsDvdSequence.smul'` idx 10: necessary
theorem c2_82 : ¬ drop0% IsDvdSequence.smul' 10 := fun h => by
  have := h (α := ℕ) (β := B) (γ := ℕ) (f := fB) (g := fun _ => 1) fB_dvdseq one_dvdseq 1 2 (by decide)
  revert this; decide +kernel
-- `IsDvdSequence.smul'` idx 11: necessary
theorem c2_83 : ¬ drop0% IsDvdSequence.smul' 11 := fun h => by
  have := h (α := ℕ) (β := M) (γ := M) (f := gM) (g := fun _ => mf) gM_dvdseq
    (fun _ _ _ => dvd_refl _) 1 2 (by decide)
  exact not_dvd1 this
-- `IsDvdSequence.smul'` idx 12: necessary
theorem c2_84 : ¬ drop0% IsDvdSequence.smul' 12 := fun h => by
  have := h (α := ℕ) (β := ℕ) (γ := ℕ) (f := bad) (g := fun _ => 1) one_dvdseq 2 4 (by decide)
  revert this; decide
-- `IsDvdSequence.smul'` idx 13: necessary
theorem c2_85 : ¬ drop0% IsDvdSequence.smul' 13 := fun h => by
  have := h (α := ℕ) (β := ℕ) (γ := ℕ) (f := fun _ => 1) (g := bad) one_dvdseq 2 4 (by decide)
  revert this; decide
-- `IsDvdSequence.mul` idx 6: necessary
theorem c2_86 : ¬ drop0% IsDvdSequence.mul 6 := fun h => by
  have := h (α := ℕ) (β := ℕ) (f := bad) (g := fun _ => 1) one_dvdseq 2 4 (by decide)
  revert this; decide
-- `IsDvdSequence.mul` idx 7: necessary
theorem c2_87 : ¬ drop0% IsDvdSequence.mul 7 := fun h => by
  have := h (α := ℕ) (β := ℕ) (f := fun _ => 1) (g := bad) one_dvdseq 2 4 (by decide)
  revert this; decide
-- `IsDvdSequence.smul` idx 8: necessary
theorem c2_88 : ¬ drop0% IsDvdSequence.smul 8 := fun h => by
  have := h (α := ℕ) (β := Mᵐᵒᵖ) (γ := M) (f := gM) (MulOpposite.op mf) gM_dvdseq 1 2 (by decide)
  exact not_dvd1 this
-- `IsDvdSequence.smul` idx 12: necessary
theorem c2_89 : ¬ drop0% IsDvdSequence.smul 12 := fun h => by
  have := h (α := ℕ) (β := ℕ) (γ := ℕ) (f := bad) 1 2 4 (by decide)
  revert this; decide
-- `IsDivSequence.smul` idx 8: necessary
theorem c2_90 : ¬ drop0% IsDivSequence.smul 8 := fun h => by
  have := h (α := ℕ) (β := Mᵐᵒᵖ) (γ := M) (f := gM) (MulOpposite.op mf) gM_dvdseq 1 2 (by decide)
  exact not_dvd1 this
-- `IsDivSequence.smul` idx 12: necessary
theorem c2_91 : ¬ drop0% IsDivSequence.smul 12 := fun h => by
  have := h (α := ℕ) (β := ℕ) (γ := ℕ) (f := bad) 1 2 4 (by decide)
  revert this; decide
-- `IsDvdSequence.comp` idx 8: necessary
theorem c2_92 : ¬ drop0% IsDvdSequence.comp 8 := fun h =>
  bad_not (h (α := ℕ) (β := ℕ) (γ := ℕ) (f := bad) (g := id) (fun _ _ h => h))
-- `IsDvdSequence.comp` idx 9: necessary
theorem c2_93 : ¬ drop0% IsDvdSequence.comp 9 := fun h =>
  bad_not (h (α := ℕ) (β := ℕ) (γ := ℕ) (f := id) (g := bad) (fun _ _ h => h))
-- `Nat.IsStrongDvdSequence.isDvdSequence` idx 1: necessary
theorem c2_94 : ¬ drop0% Nat.IsStrongDvdSequence.isDvdSequence 1 := fun h => bad_not (h (f := bad))

-- `Nat.leRec_succ` idx 5: necessary
theorem c2_95 : ¬ indep0% Nat.leRec_succ 5 := fun h =>
  absurd (@h 0 1 (fun _ _ => True) trivial (fun _ _ _ => trivial) (by omega)) (by omega)
-- `Nat.leRec_trans` idx 6: necessary
theorem c2_96 : ¬ indep0% Nat.leRec_trans 6 := fun h =>
  absurd (@h 1 0 0 (fun _ _ => True) trivial (fun _ _ _ => trivial) le_rfl) (by omega)
-- `Nat.leRec_trans` idx 7: necessary
theorem c2_97 : ¬ indep0% Nat.leRec_trans 7 := fun h =>
  absurd (@h 0 1 0 (fun _ _ => True) trivial (fun _ _ _ => trivial) (by omega)) (by omega)
-- `Nat.leRec_succ_left` idx 6: necessary
theorem c2_98 : ¬ indep0% Nat.leRec_succ_left 6 := fun h =>
  absurd (@h 0 (fun _ _ => True) trivial (fun _ _ _ => trivial) 0 le_rfl) (by omega)
-- `Nat.leRecOn_succ` idx 3: necessary
theorem c2_99 : ¬ indep0% Nat.leRecOn_succ 3 := fun h =>
  absurd (@h (fun _ => True) 1 0 (fun _ => trivial) trivial) (by omega)
-- `Nat.leRecOn_trans` idx 4: necessary
theorem c2_100 : ¬ indep0% Nat.leRecOn_trans 4 := fun h =>
  absurd (@h (fun _ => True) 1 0 0 le_rfl (fun _ => trivial) trivial) (by omega)
-- `Nat.leRecOn_trans` idx 5: necessary
theorem c2_101 : ¬ indep0% Nat.leRecOn_trans 5 := fun h =>
  absurd (@h (fun _ => True) 0 1 0 (by omega) (fun _ => trivial) trivial) (by omega)
-- `Nat.leRecOn_succ_left` idx 5: necessary
theorem c2_102 : ¬ indep0% Nat.leRecOn_succ_left 5 := fun h =>
  absurd (@h (fun _ => True) 0 0 (fun _ => trivial) trivial) (by omega)
-- `Nat.le_induction` idx 5: necessary
theorem c2_103 : ¬ indep0% Nat.le_induction 5 := fun h =>
  absurd (@h 1 (fun _ _ => True) trivial (fun _ _ _ => trivial) 0) (by omega)
-- `Nat.decreasingInduction_succ` idx 5: necessary
theorem c2_104 : ¬ indep0% Nat.decreasingInduction_succ 5 := fun h =>
  absurd (@h 1 0 (fun _ _ => True) (fun _ _ _ => trivial) trivial le_rfl) (by omega)
-- `Nat.decreasingInduction_trans` idx 4: necessary
theorem c2_105 : ¬ indep0% Nat.decreasingInduction_trans 4 := fun h =>
  absurd (@h 1 0 1 (fun _ _ => True) (by omega) (fun _ _ _ => trivial) trivial) (by omega)
-- `Nat.decreasingInduction_trans` idx 5: necessary
theorem c2_106 : ¬ indep0% Nat.decreasingInduction_trans 5 := fun h =>
  absurd (@h 0 1 0 (fun _ _ => True) (by omega) (fun _ _ _ => trivial) trivial) (by omega)
-- `Nat.decreasingInduction_succ_left` idx 5: necessary
theorem c2_107 : ¬ indep0% Nat.decreasingInduction_succ_left 5 := fun h =>
  absurd (@h 0 0 (fun _ _ => True) (fun _ _ _ => trivial) trivial le_rfl) (by omega)
-- `List.consFixedLengthDigits_head` idx 5: necessary
theorem c2_108 : ¬ indep0% List.consFixedLengthDigits_head 5 := fun h =>
  List.ne_empty_of_mem_consFixedLengthDigits (by decide : 1 < 2)
    (@h 2 (by decide) 0 0 []) rfl
-- `Nat.evenOddRec_even` idx 4: necessary
theorem c2_109 : ¬ drop1% Nat.evenOddRec_even 4 := fun h => by
  have := @h (fun _ => ℕ) 0 (fun _ x => x + 1) (fun _ x => x) 0
  simp at this
-- `_private.Mathlib.Data.Nat.Find.0.Nat.wf_lbp` idx 1: necessary
theorem c2_110 : ¬ drop0% _private.Mathlib.Data.Nat.Find.«0».Nat.wf_lbp 1 := fun h => by
  obtain ⟨n, hn⟩ := (@h (fun _ => False)).not_rel_apply_succ id
  exact hn ⟨rfl, fun _ _ h => h⟩
-- `Nat.le_induction` idx 2: necessary
theorem c2_111 : ¬ drop0% Nat.le_induction 2 := fun h =>
  @h 0 (fun _ _ => False) (fun _ _ h => h) 0 le_rfl
-- `Nat.le_induction` idx 3: necessary
theorem c2_112 : ¬ drop0% Nat.le_induction 3 := fun h =>
  absurd (@h 0 (fun n _ => n = 0) rfl 1 (by omega)) (by omega)
-- `Nat.case_strong_induction_on` idx 2: necessary
theorem c2_113 : ¬ drop0% Nat.case_strong_induction_on 2 := fun h =>
  @h (fun _ => False) 0 (fun _ ih => ih 0 (Nat.zero_le _))
-- `Nat.diag_induction` idx 1: necessary
theorem c2_114 : ¬ drop0% Nat.diag_induction 1 := fun h =>
  absurd (h (fun a _ => a = 0) (fun _ => rfl) (fun _ _ _ h _ => absurd h (by omega)) 1 2 (by omega))
    (by omega)
-- `Nat.diag_induction` idx 3: necessary
theorem c2_115 : ¬ drop0% Nat.diag_induction 3 := fun h =>
  absurd (h (fun a b => a = 0 ∨ a = b) (fun _ => Or.inr rfl) (fun _ => Or.inl rfl) 1 2 (by omega))
    (by omega)
-- `induction_on_primes` idx 1: necessary
theorem c2_116 : ¬ drop0% induction_on_primes 1 := fun h =>
  absurd (@h (fun n => n ≠ 0) one_ne_zero
    (fun p a hp ha => Nat.mul_ne_zero hp.ne_zero ha) 0) (by simp)
-- `induction_on_primes` idx 3: necessary
theorem c2_117 : ¬ drop0% induction_on_primes 3 := fun h =>
  absurd (@h (fun n => n ≤ 1) (Nat.zero_le _) le_rfl 2) (by omega)
-- `Nat.prime_composite_induction` idx 1: necessary
theorem c2_118 : ¬ drop0% Nat.prime_composite_induction 1 := fun h =>
  absurd (@h (fun n => n ≠ 0) one_ne_zero (fun p hp => hp.ne_zero)
    (fun a _ ha b _ hb => Nat.mul_ne_zero ha hb) 0) (by simp)
-- `Nat.prime_composite_induction` idx 2: necessary
theorem c2_119 : ¬ drop0% Nat.prime_composite_induction 2 := fun h =>
  absurd (@h (fun n => n ≠ 1) zero_ne_one (fun p hp => hp.ne_one)
    (fun a ha _ b hb _ => by show a * b ≠ 1; nlinarith) 1) (by simp)
-- `Nat.prime_composite_induction` idx 3: necessary
theorem c2_120 : ¬ drop0% Nat.prime_composite_induction 3 := fun h =>
  absurd (@h (fun n => n ≤ 1) (Nat.zero_le _) le_rfl
    (fun a ha ha' _ _ _ => absurd ha' (by show ¬ a ≤ 1; omega)) 2) (by omega)
-- `Nat.prime_composite_induction` idx 4: necessary
theorem c2_121 : ¬ drop0% Nat.prime_composite_induction 4 := fun h =>
  absurd (@h (fun n => n ≤ 1 ∨ n.Prime) (Or.inl (Nat.zero_le _)) (Or.inl le_rfl)
    (fun p hp => Or.inr hp) 4) (by decide)
-- `Nat.multiplicative_factorization` idx 3: necessary
theorem c2_122 : ¬ drop0% Nat.multiplicative_factorization 3 := fun h => by
  have := @h ℕ _ (fun n => if n = 6 then 0 else 1) rfl 6 (by decide)
  rw [show (6:ℕ) = 2 * 3 from rfl, Nat.factorization_mul (by decide) (by decide),
    Nat.prime_two.factorization, Nat.prime_three.factorization,
    Finsupp.prod_add_index_of_disjoint (by simp)] at this
  simp at this
-- `Nat.multiplicative_factorization'` idx 4: necessary
theorem c2_123 : ¬ drop0% Nat.multiplicative_factorization' 4 := fun h => by
  have := @h 6 ℕ _ (fun n => if n = 6 then 0 else 1) rfl rfl
  rw [show (6:ℕ) = 2 * 3 from rfl, Nat.factorization_mul (by decide) (by decide),
    Nat.prime_two.factorization, Nat.prime_three.factorization,
    Finsupp.prod_add_index_of_disjoint (by simp)] at this
  simp at this
-- `Nat.find_mono` idx 4: necessary
theorem c2_124 : ¬ drop0% Nat.find_mono 4 := fun h => by
  have := h (p := (· = 1)) (q := (· = 0)) (hp := ⟨1, rfl⟩) (hq := ⟨0, rfl⟩)
  have h1 := Nat.find_spec (⟨1, rfl⟩ : ∃ n : ℕ, n = 1)
  have h2 := Nat.find_min' (⟨0, rfl⟩ : ∃ n : ℕ, n = 0) rfl
  omega
-- `Nat.find_congr'` idx 6: necessary
theorem c2_125 : ¬ drop0% Nat.find_congr' 6 := fun h => by
  have := h (p := (· = 1)) (q := (· = 0)) (hp := ⟨1, rfl⟩) (hq := ⟨0, rfl⟩)
  have h1 := Nat.find_spec (⟨1, rfl⟩ : ∃ n : ℕ, n = 1)
  have h2 := Nat.find_min' (⟨0, rfl⟩ : ∃ n : ℕ, n = 0) rfl
  omega
-- `Nat.Prime.not_dvd_lcm` idx 3: necessary
theorem c2_126 : ¬ drop0% Nat.Prime.not_dvd_lcm 3 := fun h =>
  h (p := 6) (a := 2) (b := 3) (by decide) (by decide) (by decide)
-- `exists_ordCompl_eq_one_iff_isPrimePow` idx 1: necessary
theorem c2_127 : ¬ drop0% exists_ordCompl_eq_one_iff_isPrimePow 1 := fun h =>
  not_isPrimePow_one ((h (n := 1)).mpr ⟨2, Nat.prime_two, by simp⟩)
-- `Nat.exists_base_eq_prime_pow_of_prime_pow_eq_base_pow` idx 4: necessary
theorem c2_128 : ¬ drop0% Nat.exists_base_eq_prime_pow_of_prime_pow_eq_base_pow 4 := fun h => by
  obtain ⟨k, hk⟩ := h (p := 4) (a := 2) (m := 1) (n := 2) (by decide) (by decide)
  rcases k with _ | k
  · simp at hk
  · have := Nat.le_self_pow (Nat.succ_ne_zero k) 4; omega
-- `Nat.exists_base_eq_prime_pow_of_prime_pow_eq_base_pow` idx 5: necessary
theorem c2_129 : ¬ drop0% Nat.exists_base_eq_prime_pow_of_prime_pow_eq_base_pow 5 := fun h => by
  obtain ⟨k, hk⟩ := h (p := 3) (a := 2) (m := 0) (n := 0) Nat.prime_three (by simp)
  rcases k with _ | k
  · simp at hk
  · have := Nat.le_self_pow (Nat.succ_ne_zero k) 3; omega
-- `Nat.exists_base_eq_prime_pow_of_prime_pow_eq_base_pow` idx 6: necessary
theorem c2_130 : ¬ drop0% Nat.exists_base_eq_prime_pow_of_prime_pow_eq_base_pow 6 := fun h => by
  obtain ⟨k, hk⟩ := h (p := 2) (a := 3) (m := 0) (n := 1) Nat.prime_two (by decide)
  rcases k with _ | _ | k
  · simp at hk
  · simp at hk
  · have := Nat.one_le_two_pow (n := k); rw [pow_succ, pow_succ] at hk; omega
-- `IsUnit.natCast_factorial_of_algebra` idx 4: necessary
theorem c2_131 : ¬ drop0% IsUnit.natCast_factorial_of_algebra 4 := fun h => by
  have := @h F2 _ F2 _ _ 2
  rw [F2_fact2] at this; exact not_isUnit_zero this
-- `IsUnit.natCast_factorial_of_isNilpotent` idx 5: necessary
theorem c2_132 : ¬ drop0% IsUnit.natCast_factorial_of_isNilpotent 5 := fun h => by
  have := h (A := ZMod 4) (n := 3) (p := 4) ⟨1, by decide⟩ (by decide)
  obtain ⟨b, hb⟩ := this.exists_right_inv
  revert b; decide
-- `IsUnit.natCast_factorial_of_isNilpotent` idx 6: necessary
theorem c2_133 : ¬ drop0% IsUnit.natCast_factorial_of_isNilpotent 6 := fun h => by
  have := h (A := ZMod 2) (n := 2) (p := 2) ⟨1, by decide⟩
  obtain ⟨b, hb⟩ := this.exists_right_inv
  revert b; decide
-- `Nat.clog_mono` idx 5: necessary
theorem c2_134 : ¬ drop0% Nat.clog_mono 5 := fun h => by
  have := h (b := 2) (c := 3) (m := 8) (n := 8) (by decide) le_rfl
  revert this; decide +kernel
-- `Nat.ofDigits_inj_of_len_eq` idx 5: necessary
theorem c2_135 : ¬ drop0% Nat.ofDigits_inj_of_len_eq 5 := fun h => by
  have := h (b := 2) (L1 := [2, 0]) (L2 := [0, 1]) (by decide) rfl (by decide) (by decide)
  simp at this
-- `Nat.ofDigits_inj_of_len_eq` idx 6: necessary
theorem c2_136 : ¬ drop0% Nat.ofDigits_inj_of_len_eq 6 := fun h => by
  have := h (b := 2) (L1 := [0, 1]) (L2 := [2, 0]) (by decide) rfl (by decide) (by decide)
  simp at this

-- `_private.Mathlib.Data.Nat.Choose.Basic.0.Nat.choose_le_middle_of_le_half_left` idx 2: removable
theorem c2_137 : drop% _private.Mathlib.Data.Nat.Choose.Basic.«0».Nat.choose_le_middle_of_le_half_left 2 := by
  intro n r; exact Nat.choose_le_middle r n
-- `Nat.factorization_choose` idx 5: removable
theorem c2_138 : drop% Nat.factorization_choose 5 := by
  intro p n k b hp hnb
  by_cases hkn : k ≤ n
  · exact Nat.factorization_choose hp hkn hnb
  · push Not at hkn
    rw [Nat.choose_eq_zero_of_lt hkn, Nat.sub_eq_zero_of_le hkn.le]
    simp only [Nat.factorization_zero, Finsupp.coe_zero, Pi.zero_apply, Nat.zero_mod, add_zero]
    symm; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _; exact not_le.2 (Nat.mod_lt _ (pow_pos hp.pos _))
-- `Choose.choose_modEq_prod_range_choose` idx 5: removable
theorem c2_139 : drop% Choose.choose_modEq_prod_range_choose 5 := by
  intro n k p _ a ha₂
  have hp := (Fact.out : p.Prime)
  have hle : ∀ i, p ^ a ≤ p ^ (a + i) := fun i => Nat.pow_le_pow_right hp.pos (by omega)
  have h1 : n < p ^ (a + n) := lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
    (Nat.pow_le_pow_right hp.pos (by omega))
  have := Choose.choose_modEq_prod_range_choose h1 (lt_of_lt_of_le ha₂ (hle n))
  rw [Finset.prod_range_add] at this
  have h3 : ∏ x ∈ Finset.range n, (((n / p ^ (a + x) % p).choose (k / p ^ (a + x) % p) : ℕ) : ℤ) = 1 :=
    Finset.prod_eq_one fun i _ => by rw [Nat.div_eq_of_lt (lt_of_lt_of_le ha₂ (hle i))]; simp
  rw [h3, mul_one] at this
  exact this
-- `Choose.choose_modEq_prod_range_choose_nat` idx 5: removable
theorem c2_140 : drop% Choose.choose_modEq_prod_range_choose_nat 5 := by
  intro n k p _ a ha₂
  have hp := (Fact.out : p.Prime)
  have hle : ∀ i, p ^ a ≤ p ^ (a + i) := fun i => Nat.pow_le_pow_right hp.pos (by omega)
  have h1 : n < p ^ (a + n) := lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt)
    (Nat.pow_le_pow_right hp.pos (by omega))
  have := Choose.choose_modEq_prod_range_choose_nat h1 (lt_of_lt_of_le ha₂ (hle n))
  rw [Finset.prod_range_add] at this
  have h3 : ∏ x ∈ Finset.range n, ((n / p ^ (a + x) % p).choose (k / p ^ (a + x) % p) : ℕ) = 1 :=
    Finset.prod_eq_one fun i _ => by rw [Nat.div_eq_of_lt (lt_of_lt_of_le ha₂ (hle i))]; simp
  rw [h3, mul_one] at this
  exact this
-- `Choose.lucas_theorem` idx 5: removable
theorem c2_141 : drop% Choose.lucas_theorem 5 := c2_139
-- `Choose.lucas_theorem_nat` idx 5: removable
theorem c2_142 : drop% Choose.lucas_theorem_nat 5 := c2_140
-- `Nat.digits_ofDigits` idx 1: removable
theorem c2_143 : drop% Nat.digits_ofDigits 1 := by
  intro b L w1 w2
  rcases lt_or_ge 1 b with hb | hb
  · exact Nat.digits_ofDigits b hb L w1 w2
  · by_cases hL : L = []
    · subst hL; simp
    · have h1 := w2 hL; have h2 := w1 _ (List.getLast_mem hL); omega
-- `Nat.digits_getLast` idx 2: removable
theorem c2_144 : drop% Nat.digits_getLast 2 := by
  intro b m p q
  rcases lt_or_ge 1 b with hb | hb
  · exact Nat.digits_getLast m hb p q
  · interval_cases b
    · simp at q
    · simp only [Nat.div_one]
-- `Nat.digits_getLast` idx 3: removable
theorem c2_145 : indep% Nat.digits_getLast 3 := by
  intro b m hb q hm
  apply q; rw [Nat.digits_eq_nil_iff_eq_zero] at hm ⊢; simp [hm]
-- `Nat.ofDigits_inj_of_len_eq` idx 1: removable
theorem c2_146 : drop% Nat.ofDigits_inj_of_len_eq 1 := by
  intro b L1 L2 len w1 w2 h
  rcases lt_or_ge 1 b with hb | hb
  · exact Nat.ofDigits_inj_of_len_eq hb len w1 w2 h
  · rw [zeros w1 hb, zeros w2 hb, len]
-- `Nat.ofDigits_lt_base_pow_length` idx 2: removable
theorem c2_147 : drop% Nat.ofDigits_lt_base_pow_length 2 := by
  intro b l hl
  rcases lt_or_ge 1 b with hb | hb
  · exact Nat.ofDigits_lt_base_pow_length hb hl
  · interval_cases b
    · have : l = [] := List.eq_nil_iff_forall_not_mem.2 fun x hx => by have := hl x hx; omega
      subst this; simp
    · rw [zeros hl le_rfl, ofDigits_rep0]; simp
-- `Nat.ofDigits_div_eq_ofDigits_tail` idx 1: removable
theorem c2_148 : drop% Nat.ofDigits_div_eq_ofDigits_tail 1 := by
  intro p digits w
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have : digits = [] := List.eq_nil_iff_forall_not_mem.2 fun x hx => by have := w x hx; omega
    subst this; simp
  · exact Nat.ofDigits_div_eq_ofDigits_tail hp digits w
-- `Nat.ofDigits_div_pow_eq_ofDigits_drop` idx 2: removable
theorem c2_149 : drop% Nat.ofDigits_div_pow_eq_ofDigits_drop 2 := by
  intro p i digits w
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have : digits = [] := List.eq_nil_iff_forall_not_mem.2 fun x hx => by have := w x hx; omega
    subst this; simp
  · exact Nat.ofDigits_div_pow_eq_ofDigits_drop i hp digits w
-- `Nat.ofDigits_mod_pow_eq_ofDigits_take` idx 2: removable
theorem c2_150 : drop% Nat.ofDigits_mod_pow_eq_ofDigits_take 2 := by
  intro p i digits w
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have : digits = [] := List.eq_nil_iff_forall_not_mem.2 fun x hx => by have := w x hx; omega
    subst this; simp
  · exact Nat.ofDigits_mod_pow_eq_ofDigits_take i hp digits w
-- `Nat.base_pow_length_digits_le` idx 2: removable
theorem c2_151 : drop% Nat.base_pow_length_digits_le 2 := by
  intro b m hm
  rcases lt_or_ge 1 b with hb | hb
  · exact Nat.base_pow_length_digits_le b m hb hm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    interval_cases b
    · simp
    · simp [Nat.digits_one]
-- `Nat.mapsTo_ofDigits` idx 1: removable
theorem c2_152 : drop% Nat.mapsTo_ofDigits 1 := by
  intro b l L hL
  obtain ⟨hlen, hL⟩ := hL
  change Nat.ofDigits b L < b ^ l
  rw [← hlen]; exact c2_147 hL
-- `Nat.mapsTo_digitsAppend` idx 1: removable
theorem c2_153 : drop% Nat.mapsTo_digitsAppend 1 := by
  intro b l n hn
  rcases lt_or_ge 1 b with hb | hb
  · exact Nat.mapsTo_digitsAppend hb l hn
  · simp only [Set.mem_setOf_eq] at hn
    interval_cases b
    · rcases l with _ | l
      · simp at hn; subst hn; simp [Nat.digitsAppend]
      · simp at hn
    · simp at hn; subst hn; simp [Nat.digitsAppend]
-- `Nat.injOn_ofDigits` idx 1: removable
theorem c2_154 : drop% Nat.injOn_ofDigits 1 := by
  intro b l L1 h1 L2 h2 heq
  exact c2_146 (h1.1.trans h2.1.symm) h1.2 h2.2 heq
-- `Nat.setInvOn_digitsAppend_ofDigits` idx 1: removable
theorem c2_155 : drop% Nat.setInvOn_digitsAppend_ofDigits 1 := by
  intro b l
  rcases lt_or_ge 1 b with hb | hb
  · exact Nat.setInvOn_digitsAppend_ofDigits hb l
  · constructor
    · rintro L ⟨hlen, hL⟩
      have hz := zeros hL hb
      rw [hlen] at hz; subst hz
      simp [Nat.digitsAppend, ofDigits_rep0]
    · intro n hn
      simp only [Set.mem_setOf_eq] at hn
      interval_cases b
      · rcases l with _ | l
        · simp at hn; subst hn; simp [Nat.digitsAppend]
        · simp at hn
      · simp at hn; subst hn; simp [Nat.digitsAppend, ofDigits_rep0]
-- `Nat.bijOn_ofDigits` idx 1: removable
theorem c2_156 : drop% Nat.bijOn_ofDigits 1 := by
  intro b l; exact (c2_155 (b := b) (l := l)).bijOn (c2_152 l) (c2_153 l)
-- `Nat.bijOn_digitsAppend` idx 1: removable
theorem c2_157 : drop% Nat.bijOn_digitsAppend 1 := by
  intro b l; exact (c2_155 (b := b) (l := l)).symm.bijOn (c2_153 l) (c2_152 l)
-- `Nat.sum_digits_ofDigits_eq_sum` idx 1: removable
theorem c2_158 : drop% Nat.sum_digits_ofDigits_eq_sum 1 := by
  intro b l L hL
  rcases lt_or_ge 1 b with hb | hb
  · exact Nat.sum_digits_ofDigits_eq_sum hb hL
  · have hz := zeros hL.2 hb
    rw [hz]; simp [ofDigits_rep0]
-- `Nat.sum_sum_digits_eq` idx 1: removable
theorem c2_159 : drop% Nat.sum_sum_digits_eq 1 := by
  intro b l
  rcases lt_or_ge 1 b with hb | hb
  · exact Nat.sum_sum_digits_eq hb l
  · interval_cases b
    · rcases l with _ | l <;> simp
    · simp

-- `Nat.cast_tsub` idx 5: necessary
theorem c2_160 : ¬ drop0% Nat.cast_tsub 5 := fun h => by
  have := @h N1 _ _ _ _ _ 2 1; revert this; decide
-- `IsDvdSequence.smul` idx 9: removable
theorem c2_161 : drop% IsDvdSequence.smul 9 := by
  intro α β γ _ _ _ f _ _ _ b hg m n hmn
  obtain ⟨c, hc⟩ := hg m n hmn
  exact ⟨c, by simp only [Pi.smul_apply, hc, smul_mul_assoc]⟩
-- `IsDvdSequence.smul` idx 10: removable
theorem c2_162 : drop% IsDvdSequence.smul 10 := by
  intro α β γ _ _ _ f _ _ _ b hg m n hmn
  obtain ⟨c, hc⟩ := hg m n hmn
  exact ⟨c, by simp only [Pi.smul_apply, hc, smul_mul_assoc]⟩
-- `IsDivSequence.smul` idx 9: removable
theorem c2_163 : drop% IsDivSequence.smul 9 := c2_161
-- `IsDivSequence.smul` idx 10: removable
theorem c2_164 : drop% IsDivSequence.smul 10 := c2_162
-- `Nat.evenOddRec_odd` idx 4: removable
theorem c2_165 : drop% Nat.evenOddRec_odd 4 := by
  intro P h0 h_even h_odd n
  apply Nat.binaryRec_eq true n
  simp
-- `Nat.multiplicative_factorization'` idx 6: removable
theorem c2_166 : drop% Nat.multiplicative_factorization' 6 := by
  intro n β _ f h_mult hf0
  apply Nat.multiplicative_factorization' f h_mult hf0
  have := h_mult 0 1 (Nat.coprime_one_right 0)
  simp only [zero_mul, hf0, one_mul] at this
  exact this.symm
-- `Nat.Ico_pow_dvd_eq_Ico_of_lt` idx 3: removable
theorem c2_167 : drop% Nat.Ico_pow_dvd_eq_Ico_of_lt 3 := by
  intro n p b hn hb
  have hp : 2 ≤ p := by
    rcases p with _ | _ | p
    · rcases b with _ | b <;> simp at hb <;> omega
    · simp at hb; omega
    · omega
  ext i
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h3
    exact (Nat.pow_lt_pow_iff_right (by omega)).1 (lt_of_le_of_lt this hb)
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h3
    have h4 := Nat.lt_two_pow_self (n := i)
    have h5 := Nat.pow_le_pow_left hp i
    omega
-- `Nat.dvd_iff_exists_le_factorization` idx 2: removable
theorem c2_168 : drop% Nat.dvd_iff_exists_le_factorization 2 := by
  intro n d hn
  rcases eq_or_ne d 0 with rfl | hd
  · constructor
    · intro h; exact absurd (zero_dvd_iff.1 h) hn
    · rintro ⟨f, hf, h0⟩
      exfalso
      have : (f.prod fun x1 x2 => x1 ^ x2) ≠ 0 := by
        rw [Finsupp.prod_ne_zero_iff]
        intro p hp
        apply pow_ne_zero
        rintro rfl
        have := hf 0
        simp only [Nat.factorization_zero_right, nonpos_iff_eq_zero] at this
        exact (Finsupp.mem_support_iff.1 hp) this
      exact this h0.symm
  · exact Nat.dvd_iff_exists_le_factorization hd hn
-- `Nat.eq_prime_pow_of_unique_prime_dvd` idx 2: removable
theorem c2_169 : drop% Nat.eq_prime_pow_of_unique_prime_dvd 2 := by
  intro n p h
  rcases eq_or_ne n 0 with rfl | hn
  · have h2 := h Nat.prime_two (dvd_zero 2); have h3 := h Nat.prime_three (dvd_zero 3); omega
  · exact Nat.eq_prime_pow_of_unique_prime_dvd hn h
-- `Nat.greatestFib_sub_fib_greatestFib_le_greatestFib` idx 1: removable
theorem c2_170 : drop% Nat.greatestFib_sub_fib_greatestFib_le_greatestFib 1 := by
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.greatestFib_eq_zero.2 rfl]; simp
  · exact Nat.greatestFib_sub_fib_greatestFib_le_greatestFib hn
-- `Nat.find_comp_succ` idx 3: removable
theorem c2_171 : indep% Nat.find_comp_succ 3 := by
  intro p _ h h0
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => exact absurd hn h0
  | succ n => exact ⟨n, hn⟩
-- `Nat.find_add` idx 3: removable
theorem c2_172 : indep% Nat.find_add 3 := by
  intro n p _ hₙ hn
  exact ⟨Nat.find hₙ - n, by rw [Nat.sub_add_cancel hn]; exact Nat.find_spec hₙ⟩
-- `Nat.log.go_spec` idx 3: removable
theorem c2_173 : drop% Nat.log.go_spec 3 := by
  intro b n fuel hn hfuel
  have hb : 1 < b := by
    by_contra hb; push Not at hb
    interval_cases b
    · rcases fuel with _ | f <;> simp at hfuel; omega
    · simp at hfuel; omega
  exact Nat.log.go_spec hb hn hfuel
-- `Nat.clog.go_spec` idx 4: removable
theorem c2_174 : drop% Nat.clog.go_spec 4 := by
  intro n b fuel hn hfuel
  have hb : 1 < b := by
    by_contra hb; push Not at hb
    interval_cases b
    · rcases fuel with _ | f <;> simp at hfuel; omega
    · simp at hfuel; omega
  exact Nat.clog.go_spec hn hb hfuel
-- `Nat.log_lt_log_succ_iff` idx 2: removable
theorem c2_175 : drop% Nat.log_lt_log_succ_iff 2 := by
  intro b n hn
  rcases lt_or_ge 1 b with hb | hb
  · exact Nat.log_lt_log_succ_iff hb hn
  · simp only [Nat.log_of_left_le_one hb, lt_self_iff_false, pow_zero, false_iff]; omega
-- `Nat.log_eq_log_succ_iff` idx 2: removable
theorem c2_176 : drop% Nat.log_eq_log_succ_iff 2 := by
  intro b n hn
  rcases lt_or_ge 1 b with hb | hb
  · exact Nat.log_eq_log_succ_iff hb hn
  · simp only [Nat.log_of_left_le_one hb, pow_zero, true_iff]; omega
-- `Nat.pow_pred_clog_lt_self` idx 1: removable
theorem c2_177 : drop% Nat.pow_pred_clog_lt_self 1 := by
  intro b x hx
  rcases lt_or_ge 1 b with hb | hb
  · exact Nat.pow_pred_clog_lt_self hb hx
  · rw [Nat.clog_of_left_le_one hb]; simpa

-- `Nat.cast_tsub` idx 6: necessary
theorem c2_178 : ¬ drop0% Nat.cast_tsub 6 := fun h => by
  have := @h BS _ _ _ _ _ 2 1; revert this; decide
-- `Sym.countPerms_coe_fill_of_notMem` idx 6: necessary
theorem c2_179 : ¬ drop0% Sym.countPerms_coe_fill_of_notMem 6 := fun h => by
  have := @h 2 ℕ _ 1 (Sym.replicate _ 0) 0
  rw [Sym.coe_fill, Multiset.countPerms_filter_ne 0] at this
  simp only [Sym.coe_replicate] at this
  rw [Multiset.countPerms_filter_ne 0 (Multiset.replicate (2 - ((1 : Fin 3) : ℕ)) 0)] at this
  simp [Multiset.countPerms_zero, Multiset.filter_singleton] at this

-- `Nat.sub_one_mul_sum_div_pow_eq_sub_sum_digits` idx 3: removable
theorem c2_180 : drop% Nat.sub_one_mul_sum_div_pow_eq_sub_sum_digits 3 := by
  intro p L
  induction L using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton L' x ih =>
    intro hne hlt
    by_cases hx : x = 0
    · subst hx
      rcases eq_or_ne L' [] with rfl | hL'
      · simp
      · have hlt' : ∀ l ∈ L', l < p := fun l hl => hlt l (by simp [hl])
        have key := ih (h_nonempty := hL') hlt'
        have hN := c2_147 hlt'
        have hp : 0 < p := by
          obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil L' hL'
          have := hlt' y hy; omega
        have h0 : Nat.ofDigits p (L' ++ [0]) = Nat.ofDigits p L' := by
          rw [Nat.ofDigits_append]; simp [Nat.ofDigits]
        rw [h0, List.length_append, List.length_singleton, Finset.sum_range_succ,
          Nat.div_eq_of_lt (lt_of_lt_of_le hN (Nat.pow_le_pow_right hp (by omega))), add_zero, key]
        simp
    · exact Nat.sub_one_mul_sum_div_pow_eq_sub_sum_digits (L' ++ [x]) (h_nonempty := hne) (by simpa using hx) hlt
