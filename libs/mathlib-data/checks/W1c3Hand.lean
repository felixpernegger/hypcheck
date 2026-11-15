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

namespace W1c3

-- helper: the reals are uncountable
theorem nCR : ¬ (Set.univ : Set ℝ).Countable := Cardinal.not_countable_real
theorem nCtR : ¬ Countable ℝ := fun h => nCR Set.countable_univ
-- helper: ℕ is infinite as a set
theorem iN : (Set.univ : Set ℕ).Infinite := Set.infinite_univ

end W1c3

open W1c3

-- `Set.Finite.nonempty_fintype` idx 2: necessary
theorem c3_96 : ¬ drop0% Set.Finite.nonempty_fintype 2 := fun h => by
  obtain ⟨i⟩ := h (α := ℕ) (s := Set.univ)
  exact iN (Set.toFinite _)

-- `Set.Finite.ofFinset` idx 3: necessary
theorem c3_97 : ¬ drop0% Set.Finite.ofFinset 3 := fun h => iN (h (p := Set.univ) ∅)

-- `Set.Finite.toFinset_eq_toFinset` idx 3: removable (the Fintype instance gives finiteness)
theorem c3_98 : indep% Set.Finite.toFinset_eq_toFinset 3 := by
  intro α s _; exact Set.toFinite s

-- `Set.Finite.exists_finset` idx 2: necessary
theorem c3_99 : ¬ drop0% Set.Finite.exists_finset 2 := fun h => by
  obtain ⟨s', hs'⟩ := h (s := (Set.univ : Set ℕ))
  exact iN ((s'.finite_toSet).subset (fun x _ => (hs' x).2 trivial))

-- `Set.Finite.exists_finset_coe` idx 2: necessary
theorem c3_100 : ¬ drop0% Set.Finite.exists_finset_coe 2 := fun h => by
  obtain ⟨s', hs'⟩ := h (s := (Set.univ : Set ℕ))
  exact iN (hs' ▸ s'.finite_toSet)

-- `Set.Finite.mem_toFinset` idx 3: necessary
theorem c3_101 : ¬ indep0% Set.Finite.mem_toFinset 3 := fun h => iN (h (s := Set.univ) (a := 0))

-- `Set.Finite.coe_toFinset` idx 2: necessary
theorem c3_102 : ¬ indep0% Set.Finite.coe_toFinset 2 := fun h => iN (h (s := Set.univ))

-- `Set.Finite.toFinset_nonempty` idx 2: necessary
theorem c3_103 : ¬ indep0% Set.Finite.toFinset_nonempty 2 := fun h => iN (h (s := Set.univ))

-- `Set.Finite.coeSort_toFinset` idx 2: necessary
theorem c3_104 : ¬ indep0% Set.Finite.coeSort_toFinset 2 := fun h => iN (h (s := Set.univ))

-- `Set.Finite.subtypeEquivToFinset_apply_coe` idx 2: necessary
theorem c3_105 : ¬ indep0% Set.Finite.subtypeEquivToFinset_apply_coe 2 := fun h =>
  iN (h (s := Set.univ) ⟨0, trivial⟩)

-- `Set.Finite.subtypeEquivToFinset_symm_apply_coe` idx 2: necessary
theorem c3_106 : ¬ indep0% Set.Finite.subtypeEquivToFinset_symm_apply_coe 2 := fun h => iN (h (s := Set.univ))

-- `Set.Finite.toFinset_inj` idx 3: necessary
theorem c3_107 : ¬ indep0% Set.Finite.toFinset_inj 3 := fun h =>
  iN (h (s := Set.univ) (t := ∅) (ht := Set.finite_empty))

-- `Set.Finite.toFinset_inj` idx 4: necessary
theorem c3_108 : ¬ indep0% Set.Finite.toFinset_inj 4 := fun h =>
  iN (h (t := Set.univ) (s := ∅) (hs := Set.finite_empty))

-- `Set.Finite.toFinset_subset` idx 2: necessary
theorem c3_109 : ¬ indep0% Set.Finite.toFinset_subset 2 := fun h => iN (h (s := Set.univ) (t := ∅))

-- `Set.Finite.toFinset_ssubset` idx 2: necessary
theorem c3_110 : ¬ indep0% Set.Finite.toFinset_ssubset 2 := fun h => iN (h (s := Set.univ) (t := ∅))

-- `Set.Finite.subset_toFinset` idx 2: necessary
theorem c3_111 : ¬ indep0% Set.Finite.subset_toFinset 2 := fun h => iN (h (t := Set.univ) (s := ∅))

-- `Set.Finite.ssubset_toFinset` idx 2: necessary
theorem c3_112 : ¬ indep0% Set.Finite.ssubset_toFinset 2 := fun h => iN (h (t := Set.univ) (s := ∅))

-- `Set.Finite.toFinset_subset_toFinset` idx 3: necessary
theorem c3_113 : ¬ indep0% Set.Finite.toFinset_subset_toFinset 3 := fun h =>
  iN (h (s := Set.univ) (t := ∅) (ht := Set.finite_empty))

-- `Set.Finite.toFinset_subset_toFinset` idx 4: necessary
theorem c3_114 : ¬ indep0% Set.Finite.toFinset_subset_toFinset 4 := fun h =>
  iN (h (t := Set.univ) (s := ∅) (hs := Set.finite_empty))

-- `Set.Finite.toFinset_ssubset_toFinset` idx 3: necessary
theorem c3_115 : ¬ indep0% Set.Finite.toFinset_ssubset_toFinset 3 := fun h =>
  iN (h (s := Set.univ) (t := ∅) (ht := Set.finite_empty))

-- `Set.Finite.toFinset_ssubset_toFinset` idx 4: necessary
theorem c3_116 : ¬ indep0% Set.Finite.toFinset_ssubset_toFinset 4 := fun h =>
  iN (h (t := Set.univ) (s := ∅) (hs := Set.finite_empty))

-- `Set.Finite.toFinset_mono` idx 3: removable (s ⊆ t and t finite give s finite)
theorem c3_117 : indep% Set.Finite.toFinset_mono 3 := by
  intro α s t ht hst; exact ht.subset hst

-- `Set.Finite.toFinset_mono` idx 4: necessary
theorem c3_118 : ¬ indep0% Set.Finite.toFinset_mono 4 := fun h =>
  iN (h (t := Set.univ) (s := ∅) (hs := Set.finite_empty) (Set.empty_subset _))

-- `Set.Finite.toFinset_strictMono` idx 3: removable (s ⊂ t and t finite give s finite)
theorem c3_119 : indep% Set.Finite.toFinset_strictMono 3 := by
  intro α s t ht hst; exact ht.subset hst.subset

-- `Set.Finite.toFinset_strictMono` idx 4: necessary
theorem c3_120 : ¬ indep0% Set.Finite.toFinset_strictMono 4 := fun h =>
  iN (h (t := Set.univ) (s := ∅) (hs := Set.finite_empty) ⟨Set.empty_subset _, fun h' => h' (Set.mem_univ 0)⟩)

-- `Set.Finite.toFinset_ofPred` idx 4: removable (the type is a Fintype)
theorem c3_121 : indep% Set.Finite.toFinset_ofPred 4 := by
  intro α _ p _; exact Set.toFinite _

-- `Set.Finite.toFinset_setOf` idx 4: removable (the type is a Fintype)
theorem c3_122 : indep% Set.Finite.toFinset_setOf 4 := by
  intro α _ p _; exact Set.toFinite _

-- `Set.Finite.disjoint_toFinset` idx 3: necessary
theorem c3_123 : ¬ indep0% Set.Finite.disjoint_toFinset 3 := fun h =>
  iN (h (s := Set.univ) (t := ∅) (ht := Set.finite_empty))

-- `Set.Finite.disjoint_toFinset` idx 4: necessary
theorem c3_124 : ¬ indep0% Set.Finite.disjoint_toFinset 4 := fun h =>
  iN (h (t := Set.univ) (s := ∅) (hs := Set.finite_empty))

-- `Set.Finite.toFinset_inter` idx 4: necessary
theorem c3_125 : ¬ indep0% Set.Finite.toFinset_inter 4 := fun h =>
  iN (h (s := Set.univ) (t := ∅) Set.finite_empty (by simp))

-- `Set.Finite.toFinset_inter` idx 5: necessary
theorem c3_126 : ¬ indep0% Set.Finite.toFinset_inter 5 := fun h =>
  iN (h (t := Set.univ) (s := ∅) Set.finite_empty (by simp))

-- `Set.Finite.toFinset_inter` idx 6: removable (an intersection of finite sets is finite)
theorem c3_127 : indep% Set.Finite.toFinset_inter 6 := by
  intro α s t _ hs ht; exact hs.inter_of_left t

-- `Set.Finite.toFinset_sdiff` idx 4: removable (s ⊆ (s \ t) ∪ t)
theorem c3_128 : indep% Set.Finite.toFinset_sdiff 4 := by
  intro α s t _ ht hd; exact hd.of_diff ht

-- `Set.Finite.toFinset_sdiff` idx 5: necessary
theorem c3_129 : ¬ indep0% Set.Finite.toFinset_sdiff 5 := fun h =>
  iN (h (t := Set.univ) (s := ∅) Set.finite_empty (by simp))

-- `Set.Finite.toFinset_symmDiff` idx 4: removable (s ⊆ (s ∆ t) ∪ t)
theorem c3_130 : indep% Set.Finite.toFinset_symmDiff 4 := by
  intro α s t _ ht hd
  exact (hd.union ht).subset (fun x hx => by by_cases hxt : x ∈ t <;> simp_all)

-- `Set.Finite.toFinset_symmDiff` idx 5: removable (t ⊆ (s ∆ t) ∪ s)
theorem c3_131 : indep% Set.Finite.toFinset_symmDiff 5 := by
  intro α s t _ hs hd
  exact (hd.union hs).subset (fun x hx => by by_cases hxs : x ∈ s <;> simp_all)

-- `Set.Finite.toFinset_compl` idx 4: removable (the type is a Fintype)
theorem c3_132 : indep% Set.Finite.toFinset_compl 4 := by
  intro α s _ _ _; exact Set.toFinite s

-- `Set.Finite.toFinset_compl` idx 5: removable (the type is a Fintype)
theorem c3_133 : indep% Set.Finite.toFinset_compl 5 := by
  intro α s _ _ _; exact Set.toFinite _

-- `Set.Finite.toFinset_eq_empty` idx 2: necessary
theorem c3_134 : ¬ indep0% Set.Finite.toFinset_eq_empty 2 := fun h => iN (h (s := Set.univ))

-- `Set.Finite.toFinset_eq_univ` idx 3: removable (the type is a Fintype)
theorem c3_135 : indep% Set.Finite.toFinset_eq_univ 3 := by
  intro α s _; exact Set.toFinite s

-- `Set.Finite.toFinset_image` idx 5: necessary
theorem c3_136 : ¬ indep0% Set.Finite.toFinset_image 5 := fun h =>
  iN (h (s := Set.univ) (fun _ : ℕ => (0 : ℕ)) (Set.toFinite _ |>.subset (by
    rintro _ ⟨x, _, rfl⟩; exact Set.mem_singleton 0) : ((fun _ : ℕ => (0 : ℕ)) '' Set.univ).Finite))

-- `Set.Finite.toFinset_image` idx 6: removable (images of finite sets are finite)
theorem c3_137 : indep% Set.Finite.toFinset_image 6 := by
  intro α β s _ f hs; exact hs.image f

-- `Set.Finite.toFinset_range` idx 5: removable (the domain is a Fintype)
theorem c3_138 : indep% Set.Finite.toFinset_range 5 := by
  intro α β _ _ f; exact Set.finite_range f

-- `Set.Finite.toFinset_nontrivial` idx 2: necessary
theorem c3_139 : ¬ indep0% Set.Finite.toFinset_nontrivial 2 := fun h => iN (h (s := Set.univ))

-- `Finite.Set.finite_union` idx 3: necessary
theorem c3_140 : ¬ drop0% Finite.Set.finite_union 3 := fun h => by
  have := h (Set.univ : Set ℕ) ∅
  exact iN (by simpa using Set.toFinite (Set.univ ∪ (∅ : Set ℕ)))

-- `Finite.Set.finite_union` idx 4: necessary
theorem c3_141 : ¬ drop0% Finite.Set.finite_union 4 := fun h => by
  have := h ∅ (Set.univ : Set ℕ)
  exact iN (by simpa using Set.toFinite ((∅ : Set ℕ) ∪ Set.univ))

-- `Finite.Set.finite_sep` idx 3: necessary
theorem c3_142 : ¬ drop0% Finite.Set.finite_sep 3 := fun h => by
  have := h (Set.univ : Set ℕ) (fun _ => True)
  exact iN (by simpa using Set.toFinite {a | a ∈ (Set.univ : Set ℕ) ∧ True})

-- `Finite.Set.subset` idx 3: necessary
theorem c3_143 : ¬ drop0% Finite.Set.subset 3 := fun h => by
  have := h (Set.univ : Set ℕ) (t := Set.univ) subset_rfl
  exact iN (Set.toFinite _)

-- `Finite.Set.subset` idx 4: necessary
theorem c3_144 : ¬ drop0% Finite.Set.subset 4 := fun h => by
  have := @h ℕ ∅ Set.univ Set.finite_empty.to_subtype
  exact iN (Set.toFinite _)

-- `Finite.Set.finite_inter_of_right` idx 3: necessary
theorem c3_145 : ¬ drop0% Finite.Set.finite_inter_of_right 3 := fun h => by
  have := h (Set.univ : Set ℕ) Set.univ
  exact iN (by simpa using Set.toFinite ((Set.univ : Set ℕ) ∩ Set.univ))

-- `Finite.Set.finite_inter_of_left` idx 3: necessary
theorem c3_146 : ¬ drop0% Finite.Set.finite_inter_of_left 3 := fun h => by
  have := h (Set.univ : Set ℕ) Set.univ
  exact iN (by simpa using Set.toFinite ((Set.univ : Set ℕ) ∩ Set.univ))

-- `Finite.Set.finite_diff` idx 3: necessary
theorem c3_147 : ¬ drop0% Finite.Set.finite_diff 3 := fun h => by
  have := h (Set.univ : Set ℕ) ∅
  exact iN (by simpa using Set.toFinite ((Set.univ : Set ℕ) \ ∅))

-- `Finite.Set.finite_insert` idx 3: necessary
theorem c3_148 : ¬ drop0% Finite.Set.finite_insert 3 := fun h => by
  have := h 0 (Set.univ : Set ℕ)
  exact iN (by simpa using Set.toFinite (insert 0 (Set.univ : Set ℕ)))

-- `Finite.Set.finite_image` idx 4: necessary
theorem c3_149 : ¬ drop0% Finite.Set.finite_image 4 := fun h => by
  have := h (Set.univ : Set ℕ) id
  exact iN (by simpa using Set.toFinite (id '' (Set.univ : Set ℕ)))

-- `Set.Finite.of_subsingleton` idx 1: necessary
theorem c3_150 : ¬ drop0% Set.Finite.of_subsingleton 1 := fun h => iN (h Set.univ)

-- `Finite.of_finite_univ` idx 1: necessary
theorem c3_151 : ¬ drop0% Finite.of_finite_univ 1 := fun h => by
  have := h (α := ℕ)
  exact iN (Set.toFinite _)

-- `Set.Finite.subset` idx 4: necessary
theorem c3_152 : ¬ drop0% Set.Finite.subset 4 := fun h => iN (h (s := ∅) Set.finite_empty (t := Set.univ))

-- `Set.Finite.finite_of_compl` idx 2: necessary
theorem c3_153 : ¬ drop0% Set.Finite.finite_of_compl 2 := fun h => by
  have := h (s := (Set.univ : Set ℕ)) (by simp)
  exact iN (Set.toFinite _)

-- `Set.Finite.finite_of_compl` idx 3: necessary
theorem c3_154 : ¬ drop0% Set.Finite.finite_of_compl 3 := fun h => by
  have := h (s := (∅ : Set ℕ)) Set.finite_empty
  exact iN (Set.toFinite _)

-- `Set.Finite.sep` idx 2: necessary
theorem c3_155 : ¬ drop0% Set.Finite.sep 2 := fun h => iN (by simpa using h (s := (Set.univ : Set ℕ)) (fun _ => True))

-- `Set.Finite.inter_of_left` idx 2: necessary
theorem c3_156 : ¬ drop0% Set.Finite.inter_of_left 2 := fun h => iN (by simpa using h (s := (Set.univ : Set ℕ)) Set.univ)

-- `Set.Finite.inter_of_right` idx 2: necessary
theorem c3_157 : ¬ drop0% Set.Finite.inter_of_right 2 := fun h => iN (by simpa using h (s := (Set.univ : Set ℕ)) Set.univ)

-- `Set.Finite.inf_of_left` idx 2: necessary
theorem c3_158 : ¬ drop0% Set.Finite.inf_of_left 2 := fun h => iN (by simpa using h (s := (Set.univ : Set ℕ)) Set.univ)

-- `Set.Finite.inf_of_right` idx 2: necessary
theorem c3_159 : ¬ drop0% Set.Finite.inf_of_right 2 := fun h => iN (by simpa using h (s := (Set.univ : Set ℕ)) Set.univ)

-- `Set.Infinite.mono` idx 3: necessary
theorem c3_160 : ¬ drop0% Set.Infinite.mono 3 := fun h => h (s := (Set.univ : Set ℕ)) (t := ∅) iN Set.finite_empty

-- `Set.Finite.sdiff` idx 3: necessary
theorem c3_161 : ¬ drop0% Set.Finite.sdiff 3 := fun h => iN (by simpa using h (s := (Set.univ : Set ℕ)) (t := ∅))

-- `Set.Finite.diff` idx 3: necessary
theorem c3_162 : ¬ drop0% Set.Finite.diff 3 := fun h => iN (by simpa using h (s := (Set.univ : Set ℕ)) (t := ∅))

-- `Set.Finite.of_sdiff` idx 3: necessary
theorem c3_163 : ¬ drop0% Set.Finite.of_sdiff 3 := fun h => iN (h (s := (Set.univ : Set ℕ)) (t := ∅) Set.finite_empty)

-- `Set.Finite.of_diff` idx 3: necessary
theorem c3_164 : ¬ drop0% Set.Finite.of_diff 3 := fun h => iN (h (s := (Set.univ : Set ℕ)) (t := ∅) Set.finite_empty)

-- `Set.Finite.symmDiff` idx 3: necessary
theorem c3_165 : ¬ drop0% Set.Finite.symmDiff 3 := fun h =>
  iN ((h (s := (Set.univ : Set ℕ)) (t := ∅) Set.finite_empty).subset (fun x _ => by simp [Set.mem_symmDiff]))

-- `Set.Finite.symmDiff` idx 4: necessary
theorem c3_166 : ¬ drop0% Set.Finite.symmDiff 4 := fun h =>
  iN ((h (t := (Set.univ : Set ℕ)) (s := ∅) Set.finite_empty).subset (fun x _ => by simp [Set.mem_symmDiff]))

-- `Set.Finite.symmDiff_congr` idx 4: necessary
theorem c3_167 : ¬ drop0% Set.Finite.symmDiff_congr 4 := fun h =>
  iN (((h (s := (Set.univ : Set ℕ)) (t := ∅) (u := ∅)).2 (by simp)).subset (fun x _ => by simp [Set.mem_symmDiff]))

-- `Set.Finite.insert` idx 3: necessary
theorem c3_168 : ¬ drop0% Set.Finite.insert 3 := fun h => iN (by simpa using h 0 (s := (Set.univ : Set ℕ)))

-- `Set.Finite.image` idx 4: necessary
theorem c3_169 : ¬ drop0% Set.Finite.image 4 := fun h => iN (by simpa using h (s := (Set.univ : Set ℕ)) id)

-- `Set.Finite.of_surjOn` idx 5: necessary
theorem c3_170 : ¬ drop0% Set.Finite.of_surjOn 5 := fun h =>
  iN (h (s := (∅ : Set ℕ)) (t := (Set.univ : Set ℕ)) id Set.finite_empty)

-- `Set.Finite.of_surjOn` idx 6: necessary
theorem c3_171 : ¬ drop0% Set.Finite.of_surjOn 6 := fun h =>
  iN (h (s := (Set.univ : Set ℕ)) (t := (Set.univ : Set ℕ)) id (fun x _ => ⟨x, trivial, rfl⟩))

-- `Set.Finite.map` idx 4: necessary
theorem c3_172 : ¬ drop0% Set.Finite.map 4 := fun h =>
  iN (by simpa [Set.fmap_eq_image] using h (s := (Set.univ : Set ℕ)) id)

-- `Set.Finite.of_finite_image` idx 4: necessary
theorem c3_173 : ¬ drop0% Set.Finite.of_finite_image 4 := fun h =>
  iN (h (s := (Set.univ : Set ℕ)) (f := id) Function.injective_id.injOn)

-- `Set.Finite.of_finite_image` idx 5: necessary
theorem c3_174 : ¬ drop0% Set.Finite.of_finite_image 5 := fun h =>
  iN (h (s := (Set.univ : Set ℕ)) (f := fun _ => ()) (Set.toFinite _))

-- `Set.Finite.of_injOn` idx 5: necessary
theorem c3_175 : ¬ drop0% Set.Finite.of_injOn 5 := fun h =>
  iN (h (s := (Set.univ : Set ℕ)) (t := (∅ : Set ℕ)) (f := id) Function.injective_id.injOn Set.finite_empty)

-- `Set.Finite.of_injOn` idx 6: necessary
theorem c3_176 : ¬ drop0% Set.Finite.of_injOn 6 := fun h =>
  iN (h (s := (Set.univ : Set ℕ)) (t := (Set.univ : Set Unit)) (f := fun _ => ()) (fun _ _ => trivial) (Set.toFinite _))

-- `Set.Finite.of_injOn` idx 7: necessary
theorem c3_177 : ¬ drop0% Set.Finite.of_injOn 7 := fun h =>
  iN (h (s := (Set.univ : Set ℕ)) (t := (Set.univ : Set ℕ)) (f := id) (fun _ _ => trivial) Function.injective_id.injOn)

-- `Set.BijOn.finite_iff_finite` idx 5: necessary
theorem c3_178 : ¬ drop0% Set.BijOn.finite_iff_finite 5 := fun h =>
  iN ((h (s := (Set.univ : Set ℕ)) (t := (∅ : Set ℕ)) (f := id)).2 Set.finite_empty)

-- `Set.finite_of_finite_preimage` idx 4: necessary
theorem c3_179 : ¬ drop0% Set.finite_of_finite_preimage 4 := fun h =>
  iN (h (s := (Set.univ : Set ℕ)) (f := id) (fun x _ => ⟨x, rfl⟩))

-- `Set.finite_of_finite_preimage` idx 5: necessary
theorem c3_180 : ¬ drop0% Set.finite_of_finite_preimage 5 := fun h =>
  iN (h (s := (Set.univ : Set ℕ)) (f := fun _ : Unit => 0) (Set.toFinite _))

-- `Set.Finite.of_preimage` idx 4: necessary
theorem c3_181 : ¬ drop0% Set.Finite.of_preimage 4 := fun h =>
  iN (h (s := (Set.univ : Set ℕ)) (f := id) Function.surjective_id)

-- `Set.Finite.of_preimage` idx 5: necessary
theorem c3_182 : ¬ drop0% Set.Finite.of_preimage 5 := fun h =>
  iN (h (s := (Set.univ : Set ℕ)) (f := fun _ : Unit => 0) (Set.toFinite _))

-- `Set.Finite.preimage` idx 4: necessary
theorem c3_183 : ¬ drop0% Set.Finite.preimage 4 := fun h =>
  iN (by simpa using h (s := (Set.univ : Set Unit)) (f := fun _ : ℕ => ()) (Set.toFinite _))

-- `Set.Finite.preimage` idx 5: necessary
theorem c3_184 : ¬ drop0% Set.Finite.preimage 5 := fun h =>
  iN (by simpa using h (s := (Set.univ : Set ℕ)) (f := id) Function.injective_id.injOn)

-- `Set.Infinite.preimage` idx 5: necessary
theorem c3_185 : ¬ drop0% Set.Infinite.preimage 5 := fun h =>
  h (s := (Set.univ : Set ℕ)) (f := fun _ : Unit => 0) iN (Set.toFinite _)

-- `Set.Finite.preimage_embedding` idx 4: necessary
theorem c3_186 : ¬ drop0% Set.Finite.preimage_embedding 4 := fun h =>
  iN (by simpa using h (s := (Set.univ : Set ℕ)) (Function.Embedding.refl ℕ))

-- `Set.Finite.surjOn_iff_bijOn_of_mapsTo` idx 3: necessary
theorem c3_187 : ¬ drop0% Set.Finite.surjOn_iff_bijOn_of_mapsTo 3 := fun h => by
  have := ((h (s := (Set.univ : Set ℕ)) (f := Nat.pred) (fun _ _ => trivial)).1
    (fun x _ => ⟨x + 1, trivial, rfl⟩)).2.1
  exact absurd (this (Set.mem_univ 0) (Set.mem_univ 1) rfl) (by decide)

-- `Set.Finite.surjOn_iff_bijOn_of_mapsTo` idx 4: removable (s finite and s ⊆ f '' s force f '' s = s, so f maps s to s)
theorem c3_188 : drop% Set.Finite.surjOn_iff_bijOn_of_mapsTo 4 := by
  intro α s f hs
  refine ⟨fun h => ?_, Set.BijOn.surjOn⟩
  have he : s = f '' s := Set.eq_of_subset_of_ncard_le h (Set.ncard_image_le hs) (hs.image f)
  have hm : Set.MapsTo f s s := fun x hx => he ▸ Set.mem_image_of_mem f hx
  exact (Set.Finite.surjOn_iff_bijOn_of_mapsTo hs hm).1 h

-- `Set.Finite.injOn_iff_bijOn_of_mapsTo` idx 3: necessary
theorem c3_189 : ¬ drop0% Set.Finite.injOn_iff_bijOn_of_mapsTo 3 := fun h => by
  have := ((h (s := (Set.univ : Set ℕ)) (f := Nat.succ) (fun _ _ => trivial)).1
    (Nat.succ_injective.injOn)).2.2
  obtain ⟨x, _, hx⟩ := this (Set.mem_univ 0)
  exact Nat.succ_ne_zero x hx

-- `Set.Subsingleton.finite` idx 2: necessary
theorem c3_190 : ¬ drop0% Set.Subsingleton.finite 2 := fun h => iN (h (s := Set.univ))

-- `Set.finite_range_ite` idx 6: necessary
theorem c3_191 : ¬ drop0% Set.finite_range_ite 6 := fun h =>
  iN (by simpa using h (p := fun _ : ℕ => True) (f := id) (g := fun _ => (0 : ℕ)) (by simp))

-- `Set.finite_range_ite` idx 7: necessary
theorem c3_192 : ¬ drop0% Set.finite_range_ite 7 := fun h =>
  iN (by simpa using h (p := fun _ : ℕ => False) (g := id) (f := fun _ => (0 : ℕ)) (by simp))

-- `Set.finite_image_iff` idx 4: necessary
theorem c3_193 : ¬ drop0% Set.finite_image_iff 4 := fun h =>
  iN ((h (s := (Set.univ : Set ℕ)) (f := fun _ => ())).1 (Set.toFinite _))

-- `Set.finite_range_iff` idx 3: necessary
theorem c3_194 : ¬ drop0% Set.finite_range_iff 3 := fun h => by
  have := (h (f := fun _ : ℕ => ())).1 (Set.toFinite _)
  exact iN (Set.toFinite _)

-- `Set.Finite.toFinset_insert` idx 4: necessary
theorem c3_195 : ¬ indep0% Set.Finite.toFinset_insert 4 := fun h =>
  iN (by simpa using h (s := (Set.univ : Set ℕ)) (a := 0))

-- `Set.Finite.toFinset_insert'` idx 4: necessary
theorem c3_196 : ¬ indep0% Set.Finite.toFinset_insert' 4 := fun h => iN (h (s := Set.univ) (a := 0))

-- `Set.Finite.induction_on` idx 3: necessary
theorem c3_197 : ¬ indep0% Set.Finite.induction_on 3 := fun h =>
  iN (h (motive := fun _ _ => True) Set.univ trivial (fun _ _ _ => trivial))

-- `Set.Finite.induction_on` idx 4: necessary
theorem c3_198 : ¬ drop0% Set.Finite.induction_on 4 := fun h =>
  h (motive := fun _ _ => False) (∅ : Set ℕ) Set.finite_empty (fun _ _ h => h)

-- `Set.Finite.induction_on` idx 5: necessary
theorem c3_199 : ¬ drop0% Set.Finite.induction_on 5 := fun h => by
  have := h (motive := fun s _ => s = ∅) {0} (Set.finite_singleton 0) rfl
  simp at this

-- `Set.Finite.induction_on_subset` idx 3: necessary
theorem c3_200 : ¬ indep0% Set.Finite.induction_on_subset 3 := fun h =>
  iN (h (motive := fun _ _ => True) Set.univ trivial)

-- `Set.Finite.induction_on_subset` idx 4: necessary
theorem c3_201 : ¬ drop0% Set.Finite.induction_on_subset 4 := fun h =>
  h (motive := fun _ _ => False) (∅ : Set ℕ) Set.finite_empty (fun _ _ _ h => h)

-- `Set.Finite.induction_on_subset` idx 5: necessary
theorem c3_202 : ¬ drop0% Set.Finite.induction_on_subset 5 := fun h => by
  have := h (motive := fun s _ => s = ∅) {0} (Set.finite_singleton 0) rfl
  simp at this

-- `Set.seq_of_forall_finite_exists` idx 2: necessary
theorem c3_203 : ¬ drop0% Set.seq_of_forall_finite_exists 2 := fun h => by
  obtain ⟨u, hu⟩ := h (γ := ℕ) (P := fun _ _ => False)
  exact hu 0

-- `Set.Finite.card_toFinset` idx 3: removable (the Fintype instance gives finiteness)
theorem c3_204 : indep% Set.Finite.card_toFinset 3 := by
  intro α s _; exact Set.toFinite s

-- `Set.Infinite.to_type` idx 2: necessary
theorem c3_205 : ¬ drop0% Set.Infinite.to_type 2 := fun h => by
  have := h (α := Unit) (s := Set.univ)
  exact not_finite Unit

-- `Set.Infinite.exists_notMem_finite` idx 4: necessary
theorem c3_206 : ¬ drop0% Set.Infinite.exists_notMem_finite 4 := fun h => by
  obtain ⟨a, _, ha⟩ := h (s := (Set.univ : Set ℕ)) (t := Set.univ) iN
  exact ha trivial

-- `Set.infinite_image_iff` idx 4: necessary
theorem c3_207 : ¬ drop0% Set.infinite_image_iff 4 := fun h =>
  (h (s := (Set.univ : Set ℕ)) (f := fun _ => ())).2 iN (Set.toFinite _)

-- `Set.infinite_range_iff` idx 3: necessary
theorem c3_208 : ¬ drop0% Set.infinite_range_iff 3 := fun h =>
  (h (f := fun _ : ℕ => ())).2 inferInstance (Set.toFinite _)

-- `Set.Infinite.image` idx 4: necessary
theorem c3_209 : ¬ drop0% Set.Infinite.image 4 := fun h =>
  h (s := (Set.univ : Set ℕ)) (f := fun _ => ()) iN (Set.toFinite _)

-- `Set.infinite_of_injOn_mapsTo` idx 5: necessary
theorem c3_210 : ¬ drop0% Set.infinite_of_injOn_mapsTo 5 := fun h =>
  h (s := (Set.univ : Set ℕ)) (t := (Set.univ : Set Unit)) (f := fun _ => ()) (fun _ _ => trivial) iN (Set.toFinite _)

-- `Set.infinite_of_injOn_mapsTo` idx 6: necessary
theorem c3_211 : ¬ drop0% Set.infinite_of_injOn_mapsTo 6 := fun h =>
  h (s := (Set.univ : Set ℕ)) (t := (∅ : Set ℕ)) (f := id) Function.injective_id.injOn iN Set.finite_empty

-- `Set.Infinite.exists_ne_map_eq_of_mapsTo` idx 6: necessary
theorem c3_212 : ¬ drop0% Set.Infinite.exists_ne_map_eq_of_mapsTo 6 := fun h => by
  obtain ⟨x, _, y, _, hxy, he⟩ := h (s := (Set.univ : Set ℕ)) (t := (∅ : Set ℕ)) (f := id) iN Set.finite_empty
  exact hxy he

-- `Set.Infinite.exists_ne_map_eq_of_mapsTo` idx 7: necessary
theorem c3_213 : ¬ drop0% Set.Infinite.exists_ne_map_eq_of_mapsTo 7 := fun h => by
  obtain ⟨x, _, y, _, hxy, he⟩ := h (s := (Set.univ : Set ℕ)) (t := (Set.univ : Set ℕ)) (f := id) iN (fun _ _ => trivial)
  exact hxy he

-- `Set.infinite_of_injective_forall_mem` idx 2: necessary
theorem c3_214 : ¬ drop0% Set.infinite_of_injective_forall_mem 2 := fun h =>
  h (α := Empty) (s := (∅ : Set ℕ)) (f := Empty.elim) (fun x => x.elim) (fun x => x.elim) Set.finite_empty

-- `Set.infinite_of_injective_forall_mem` idx 6: necessary
theorem c3_215 : ¬ drop0% Set.infinite_of_injective_forall_mem 6 := fun h =>
  h (α := ℕ) (s := (∅ : Set ℕ)) (f := id) Function.injective_id Set.finite_empty

-- `Set.not_injOn_infinite_finite_image` idx 5: necessary
theorem c3_216 : ¬ drop0% Set.not_injOn_infinite_finite_image 5 := fun h =>
  h (s := (Set.univ : Set ℕ)) (f := id) iN Function.injective_id.injOn

-- `Finset.exists_subset_injOn_image_eq_of_surjOn` idx 6: necessary
theorem c3_217 : ¬ drop0% Finset.exists_subset_injOn_image_eq_of_surjOn 6 := fun h => by
  obtain ⟨u, hu, _, he⟩ := h (f := (id : ℕ → ℕ)) ∅ {0}
  have : u = ∅ := Finset.coe_eq_empty.1 (Set.subset_empty_iff.1 hu)
  subst this; simp at he

-- `Finite.of_forall_not_lt_lt` idx 2: necessary
theorem c3_218 : ¬ drop0% Finite.of_forall_not_lt_lt 2 := fun h => by
  have := h (α := ℕ)
  exact iN (Set.toFinite _)

-- `Set.finite_of_forall_not_lt_lt` idx 3: necessary
theorem c3_219 : ¬ drop0% Set.finite_of_forall_not_lt_lt 3 := fun h => iN (h (α := ℕ) (s := Set.univ))

namespace W1c3
-- helper: the reals lifted to Type 1 are uncountable
theorem nCU : ¬ (Set.univ : Set (ULift.{1} ℝ)).Countable := fun h =>
  by
  haveI := Set.countable_univ_iff.1 h
  exact nCtR (Function.Injective.countable (f := ULift.up.{1}) ULift.up_injective)
theorem rU : Set.range (ULift.up.{1} : ℝ → ULift ℝ) = Set.univ := by ext ⟨y⟩; simp
theorem uS : (⋃ x : ℝ, ({x} : Set ℝ)) = Set.univ := by ext; simp
theorem uSU : (⋃ x : ℝ, ({ULift.up x} : Set (ULift.{1} ℝ))) = Set.univ := by
  ext ⟨y⟩; simp
end W1c3

-- `Set.to_countable` idx 2: necessary
theorem c3_28 : ¬ drop0% Set.to_countable 2 := fun h => nCR (h Set.univ)

-- `Countable.to_set` idx 2: necessary
theorem c3_29 : ¬ drop0% Countable.to_set 2 := fun h => nCR (h (s := Set.univ))

-- `Set.subset_range_enumerate` idx 2: necessary
theorem c3_30 : ¬ indep0% Set.subset_range_enumerate 2 := fun h => nCR (h (s := Set.univ) 0)

-- `Set.range_enumerateCountable_subset` idx 2: necessary
theorem c3_31 : ¬ indep0% Set.range_enumerateCountable_subset 2 := fun h => nCR (h (s := Set.univ) 0)

-- `Set.range_enumerateCountable_of_mem` idx 2: necessary
theorem c3_32 : ¬ indep0% Set.range_enumerateCountable_of_mem 2 := fun h =>
  nCR (h (s := Set.univ) (default := 0) trivial)

-- `Set.enumerateCountable_mem` idx 2: necessary
theorem c3_33 : ¬ indep0% Set.enumerateCountable_mem 2 := fun h =>
  nCR (h (s := Set.univ) (default := 0) trivial 0)

-- `Set.Countable.mono` idx 3: necessary
theorem c3_34 : ¬ drop0% Set.Countable.mono 3 := fun h =>
  nCR (h (s₁ := Set.univ) (s₂ := ∅) Set.countable_empty)

-- `Set.Countable.mono` idx 4: necessary
theorem c3_35 : ¬ drop0% Set.Countable.mono 4 := fun h =>
  nCR (h (s₁ := Set.univ) (s₂ := Set.univ) subset_rfl)

-- `Set.countable_range` idx 2: necessary
theorem c3_36 : ¬ drop1% Set.countable_range 2 := fun h =>
  nCU (by simpa [rU] using h (ULift.up.{1} : ℝ → ULift ℝ))

-- `Set.Countable.exists_surjective` idx 3: necessary
theorem c3_37 : ¬ drop0% Set.Countable.exists_surjective 3 := fun h => by
  obtain ⟨f, hf⟩ := h (s := (Set.univ : Set ℝ)) ⟨0, trivial⟩
  have : Countable (Set.univ : Set ℝ) := hf.countable
  exact nCR (Set.countable_coe_iff.1 this)

-- `Set.countable_univ` idx 1: necessary
theorem c3_38 : ¬ drop0% Set.countable_univ 1 := fun h => nCR (h (α := ℝ))

-- `Set.Countable.exists_eq_range` idx 2: necessary
theorem c3_39 : ¬ drop0% Set.Countable.exists_eq_range 2 := fun h => by
  obtain ⟨f, hf⟩ := h (s := (Set.univ : Set ℝ)) ⟨0, trivial⟩
  exact nCR (hf ▸ Set.countable_range f)

-- `Set.Countable.exists_eq_range` idx 3: necessary
theorem c3_40 : ¬ drop0% Set.Countable.exists_eq_range 3 := fun h => by
  obtain ⟨f, hf⟩ := h (s := (∅ : Set ℕ)) Set.countable_empty
  exact (Set.range_nonempty f).ne_empty hf.symm

-- `Set.MapsTo.countable_of_injOn` idx 5: necessary
theorem c3_41 : ¬ drop0% Set.MapsTo.countable_of_injOn 5 := fun h =>
  nCR (h (s := Set.univ) (t := (∅ : Set ℝ)) (f := id) Function.injective_id.injOn Set.countable_empty)

-- `Set.MapsTo.countable_of_injOn` idx 6: necessary
theorem c3_42 : ¬ drop0% Set.MapsTo.countable_of_injOn 6 := fun h =>
  nCR (h (s := Set.univ) (t := (Set.univ : Set Unit)) (f := fun _ => ()) (fun _ _ => trivial) (Set.to_countable _))

-- `Set.MapsTo.countable_of_injOn` idx 7: necessary
theorem c3_43 : ¬ drop0% Set.MapsTo.countable_of_injOn 7 := fun h =>
  nCR (h (s := Set.univ) (t := (Set.univ : Set ℝ)) (f := id) (fun _ _ => trivial) Function.injective_id.injOn)

-- `Set.Countable.preimage_of_injOn` idx 3: necessary
theorem c3_44 : ¬ drop0% Set.Countable.preimage_of_injOn 3 := fun h =>
  nCR (h (s := (Set.univ : Set ℝ)) (f := id) Function.injective_id.injOn)

-- `Set.Countable.preimage_of_injOn` idx 5: necessary
theorem c3_45 : ¬ drop0% Set.Countable.preimage_of_injOn 5 := fun h =>
  nCR (h (s := (Set.univ : Set Unit)) (Set.to_countable _) (f := fun _ : ℝ => ()))

-- `Set.Countable.preimage` idx 3: necessary
theorem c3_46 : ¬ drop0% Set.Countable.preimage 3 := fun h =>
  nCR (h (s := (Set.univ : Set ℝ)) (f := id) Function.injective_id)

-- `Set.Countable.preimage` idx 5: necessary
theorem c3_47 : ¬ drop0% Set.Countable.preimage 5 := fun h =>
  nCR (h (s := (Set.univ : Set Unit)) (Set.to_countable _) (f := fun _ : ℝ => ()))

-- `Set.exists_seq_iSup_eq_top_iff_countable` idx 3: necessary
theorem c3_48 : ¬ drop0% Set.exists_seq_iSup_eq_top_iff_countable 3 := fun h => by
  obtain ⟨s, hs, _⟩ := (h (α := Unit) (p := fun _ => False)).2
    ⟨∅, Set.countable_empty, fun _ h => h.elim, Subsingleton.elim _ _⟩
  exact hs 0

-- `Set.exists_seq_cover_iff_countable` idx 2: necessary
theorem c3_49 : ¬ drop0% Set.exists_seq_cover_iff_countable 2 := fun h => by
  obtain ⟨s, hs, _⟩ := (h (α := Empty) (p := fun _ => False)).2
    ⟨∅, Set.countable_empty, fun _ h => h.elim, Subsingleton.elim _ _⟩
  exact hs 0

-- `Set.countable_of_injective_of_countable_image` idx 4: necessary
theorem c3_50 : ¬ drop0% Set.countable_of_injective_of_countable_image 4 := fun h =>
  nCR (h (s := Set.univ) (f := fun _ : ℝ => ()) (Set.to_countable _))

-- `Set.countable_of_injective_of_countable_image` idx 5: necessary
theorem c3_51 : ¬ drop0% Set.countable_of_injective_of_countable_image 5 := fun h =>
  nCR (h (s := Set.univ) (f := (id : ℝ → ℝ)) Function.injective_id.injOn)

-- `Set.countable_iUnion` idx 3: necessary
theorem c3_52 : ¬ drop1% Set.countable_iUnion 3 := fun h => by
  have := h (t := fun x : ℝ => ({ULift.up x} : Set (ULift.{1} ℝ))) (fun _ => Set.countable_singleton _)
  exact nCU (by simpa [uSU, rU] using this)

-- `Set.countable_iUnion` idx 4: necessary
theorem c3_53 : ¬ drop1% Set.countable_iUnion 4 := fun h => by
  have := h (t := fun _ : Unit => (Set.univ : Set (ULift.{1} ℝ)))
  exact nCU (by simpa using this)

-- `Set.countable_iUnion_iff` idx 2: necessary
theorem c3_54 : ¬ drop1% Set.countable_iUnion_iff 2 := fun h => by
  have := (h (t := fun x : ℝ => ({ULift.up x} : Set (ULift.{1} ℝ)))).2 (fun _ => Set.countable_singleton _)
  exact nCU (by simpa [uSU, rU] using this)

-- `Set.Countable.biUnion_iff` idx 4: necessary
theorem c3_55 : ¬ drop0% Set.Countable.biUnion_iff 4 := fun h => by
  have := (h (s := (Set.univ : Set ℝ)) (t := fun x _ => ({x} : Set ℝ))).2 (fun _ _ => Set.countable_singleton _)
  exact nCR (by simpa [uS] using this)

-- `Set.Countable.sUnion_iff` idx 2: necessary
theorem c3_56 : ¬ drop0% Set.Countable.sUnion_iff 2 := fun h => by
  have := (h (s := Set.range (fun x : ℝ => ({x} : Set ℝ)))).2
    (by rintro _ ⟨x, rfl⟩; exact Set.countable_singleton _)
  exact nCR (by simpa [Set.sUnion_range, uS] using this)

-- `Set.Countable.biUnion` idx 4: necessary
theorem c3_57 : ¬ drop0% Set.Countable.biUnion 4 := fun h => by
  have := h (s := (Set.univ : Set ℝ)) (t := fun x _ => ({x} : Set ℝ)) (fun _ _ => Set.countable_singleton _)
  exact nCR (by simpa [uS] using this)

-- `Set.Countable.biUnion` idx 5: necessary
theorem c3_58 : ¬ drop0% Set.Countable.biUnion 5 := fun h => by
  have := h (s := (Set.univ : Set Unit)) (t := fun _ _ => (Set.univ : Set ℝ)) (Set.to_countable _)
  exact nCR (by simpa using this)

-- `Set.Countable.sUnion` idx 2: necessary
theorem c3_59 : ¬ drop0% Set.Countable.sUnion 2 := fun h => by
  have := h (s := Set.range (fun x : ℝ => ({x} : Set ℝ)))
    (by rintro _ ⟨x, rfl⟩; exact Set.countable_singleton _)
  exact nCR (by simpa [Set.sUnion_range, uS] using this)

-- `Set.Countable.sUnion` idx 3: necessary
theorem c3_60 : ¬ drop0% Set.Countable.sUnion 3 := fun h => by
  have := h (s := {(Set.univ : Set ℝ)}) (Set.countable_singleton _)
  exact nCR (by simpa using this)

-- `Set.Countable.union` idx 3: necessary
theorem c3_61 : ¬ drop0% Set.Countable.union 3 := fun h =>
  nCR (by simpa using h (s := (Set.univ : Set ℝ)) (t := ∅) Set.countable_empty)

-- `Set.Countable.union` idx 4: necessary
theorem c3_62 : ¬ drop0% Set.Countable.union 4 := fun h =>
  nCR (by simpa using h (t := (Set.univ : Set ℝ)) (s := ∅) Set.countable_empty)

-- `Set.Countable.of_sdiff` idx 3: necessary
theorem c3_63 : ¬ drop0% Set.Countable.of_sdiff 3 := fun h =>
  nCR (h (s := (Set.univ : Set ℝ)) (t := ∅) Set.countable_empty)

-- `Set.Countable.of_sdiff` idx 4: necessary
theorem c3_64 : ¬ drop0% Set.Countable.of_sdiff 4 := fun h =>
  nCR (h (s := (Set.univ : Set ℝ)) (t := Set.univ) (by simp))

-- `Set.Countable.of_diff` idx 3: necessary
theorem c3_65 : ¬ drop0% Set.Countable.of_diff 3 := fun h =>
  nCR (h (s := (Set.univ : Set ℝ)) (t := ∅) Set.countable_empty)

-- `Set.Countable.of_diff` idx 4: necessary
theorem c3_66 : ¬ drop0% Set.Countable.of_diff 4 := fun h =>
  nCR (h (s := (Set.univ : Set ℝ)) (t := Set.univ) (by simp))

-- `Set.Finite.countable` idx 2: necessary
theorem c3_67 : ¬ drop0% Set.Finite.countable 2 := fun h => nCR (h (s := Set.univ))

-- `Set.Countable.of_subsingleton` idx 1: necessary
theorem c3_68 : ¬ drop0% Set.Countable.of_subsingleton 1 := fun h => nCR (h Set.univ)

-- `Set.Subsingleton.countable` idx 2: necessary
theorem c3_69 : ¬ drop0% Set.Subsingleton.countable 2 := fun h => nCR (h (s := Set.univ))

-- `Set.Countable.ofPred_finite` idx 1: necessary
theorem c3_70 : ¬ drop0% Set.Countable.ofPred_finite 1 := fun h => by
  have := (h (α := ℝ)).preimage (f := fun x : ℝ => ({x} : Set ℝ)) Set.singleton_injective
  exact nCR (by simpa using this)

-- `Set.Countable.setOf_finite` idx 1: necessary
theorem c3_71 : ¬ drop0% Set.Countable.setOf_finite 1 := fun h => by
  have := (h (α := ℝ)).preimage (f := fun x : ℝ => ({x} : Set ℝ)) Set.singleton_injective
  exact nCR (by simpa using this)

-- `Set.Countable.of_preimage_singleton` idx 3: necessary
theorem c3_72 : ¬ drop0% Set.Countable.of_preimage_singleton 3 := fun h =>
  nCtR (h (f := (id : ℝ → ℝ)) (fun b => by simp))

-- `Set.Countable.of_preimage_singleton` idx 4: necessary
theorem c3_73 : ¬ drop0% Set.Countable.of_preimage_singleton 4 := fun h =>
  nCtR (@h ℝ Unit (fun _ => ()) (@Finite.to_countable Unit Finite.of_subsingleton))

-- `Set.countable_univ_pi` idx 2: necessary
theorem c3_74 : ¬ drop0% Set.countable_univ_pi 2 := fun h => by
  have := h (α := ℕ) (π := fun _ => Prop) (s := fun _ => Set.univ) (fun _ => Set.to_countable _)
  rw [Set.pi_univ, Set.countable_univ_iff] at this
  obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Prop)
  exact Function.cantor_surjective (fun n => {m | f n m}) (fun s => by
    obtain ⟨n, hn⟩ := hf (fun m => m ∈ s); exact ⟨n, by ext m; simp [hn]⟩)

-- `Set.countable_univ_pi` idx 4: necessary
theorem c3_75 : ¬ drop0% Set.countable_univ_pi 4 := fun h => by
  have := h (α := Unit) (π := fun _ => ℝ) (s := fun _ => Set.univ)
  rw [Set.pi_univ, Set.countable_univ_iff] at this
  exact nCtR (show Function.Injective (fun (x : ℝ) (_ : Unit) => x) from fun a b hab => congrFun hab ()).countable

-- `Set.countable_pi` idx 2: necessary
theorem c3_76 : ¬ drop0% Set.countable_pi 2 := fun h => by
  have := h (α := ℕ) (π := fun _ => Prop) (s := fun _ => Set.univ) (fun _ => Set.to_countable _)
  simp only [Set.mem_univ, implies_true, Set.ofPred_true, Set.countable_univ_iff] at this
  obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Prop)
  exact Function.cantor_surjective (fun n => {m | f n m}) (fun s => by
    obtain ⟨n, hn⟩ := hf (fun m => m ∈ s); exact ⟨n, by ext m; simp [hn]⟩)

-- `Set.countable_pi` idx 4: necessary
theorem c3_77 : ¬ drop0% Set.countable_pi 4 := fun h => by
  have := h (α := Unit) (π := fun _ => ℝ) (s := fun _ => Set.univ)
  simp only [Set.mem_univ, implies_true, Set.ofPred_true, Set.countable_univ_iff] at this
  exact nCtR (show Function.Injective (fun (x : ℝ) (_ : Unit) => x) from fun a b hab => congrFun hab ()).countable

-- `Set.Countable.prod` idx 4: necessary
theorem c3_78 : ¬ drop0% Set.Countable.prod 4 := fun h => by
  have := (h (s := (Set.univ : Set ℝ)) (t := (Set.univ : Set Unit)) (Set.to_countable _)).preimage
    (f := fun x : ℝ => (x, ())) (fun a b hab => congrArg Prod.fst hab)
  exact nCR (by simpa using this)

-- `Set.Countable.prod` idx 5: necessary
theorem c3_79 : ¬ drop0% Set.Countable.prod 5 := fun h => by
  have := (h (t := (Set.univ : Set ℝ)) (s := (Set.univ : Set Unit)) (Set.to_countable _)).preimage
    (f := fun x : ℝ => ((), x)) (fun a b hab => congrArg Prod.snd hab)
  exact nCR (by simpa using this)

-- `Set.Countable.image2` idx 5: necessary
theorem c3_80 : ¬ drop0% Set.Countable.image2 5 := fun h => by
  have := h (s := (Set.univ : Set ℝ)) (t := (Set.univ : Set Unit)) (Set.to_countable _) (fun a _ => a)
  exact nCR (this.mono (fun x _ => Set.mem_image2_of_mem (f := fun a (_ : Unit) => a) (Set.mem_univ x) (Set.mem_univ ())))

-- `Set.Countable.image2` idx 6: necessary
theorem c3_81 : ¬ drop0% Set.Countable.image2 6 := fun h => by
  have := h (t := (Set.univ : Set ℝ)) (s := (Set.univ : Set Unit)) (Set.to_countable _) (fun _ b => b)
  exact nCR (this.mono (fun x _ => Set.mem_image2_of_mem (f := fun (_ : Unit) b => b) (Set.mem_univ ()) (Set.mem_univ x)))

-- `Set.countable_ofPred_nonempty_of_disjoint` idx 3: necessary
theorem c3_82 : ¬ drop0% Set.countable_ofPred_nonempty_of_disjoint 3 := fun h => by
  have := h (f := fun _ : ℝ => (Set.univ : Set Unit)) (s := Set.univ) (fun _ => subset_rfl) (Set.to_countable _)
  exact nCR (by simpa using this)

-- `Set.countable_ofPred_nonempty_of_disjoint` idx 5: necessary
theorem c3_83 : ¬ drop0% Set.countable_ofPred_nonempty_of_disjoint 5 := fun h => by
  have := h (f := fun x : ℝ => ({x} : Set ℝ))
    (fun a b hab => Set.disjoint_singleton.2 hab) (s := ∅) Set.countable_empty
  exact nCR (by simpa using this)

-- `Set.countable_ofPred_nonempty_of_disjoint` idx 6: necessary
theorem c3_84 : ¬ drop0% Set.countable_ofPred_nonempty_of_disjoint 6 := fun h => by
  have := h (f := fun x : ℝ => ({x} : Set ℝ))
    (fun a b hab => Set.disjoint_singleton.2 hab) (s := Set.univ) (fun _ => Set.subset_univ _)
  exact nCR (by simpa using this)

-- `Set.countable_setOf_nonempty_of_disjoint` idx 3: necessary
theorem c3_85 : ¬ drop0% Set.countable_setOf_nonempty_of_disjoint 3 := fun h => by
  have := h (f := fun _ : ℝ => (Set.univ : Set Unit)) (s := Set.univ) (fun _ => subset_rfl) (Set.to_countable _)
  exact nCR (by simpa using this)

-- `Set.countable_setOf_nonempty_of_disjoint` idx 5: necessary
theorem c3_86 : ¬ drop0% Set.countable_setOf_nonempty_of_disjoint 5 := fun h => by
  have := h (f := fun x : ℝ => ({x} : Set ℝ))
    (fun a b hab => Set.disjoint_singleton.2 hab) (s := ∅) Set.countable_empty
  exact nCR (by simpa using this)

-- `Set.countable_setOf_nonempty_of_disjoint` idx 6: necessary
theorem c3_87 : ¬ drop0% Set.countable_setOf_nonempty_of_disjoint 6 := fun h => by
  have := h (f := fun x : ℝ => ({x} : Set ℝ))
    (fun a b hab => Set.disjoint_singleton.2 hab) (s := Set.univ) (fun _ => Set.subset_univ _)
  exact nCR (by simpa using this)

namespace W1c3

-- helper: no split of the one-point set into two disjoint parts of equal cardinality
theorem cardCex : ¬ ∃ t u : Set Unit, t ∪ u = Set.univ ∧ Disjoint t u ∧ Cardinal.mk t = Cardinal.mk u := by
  rintro ⟨t, u, hu, hd, hc⟩
  obtain ⟨e⟩ := Cardinal.eq.1 hc
  have h0 : () ∈ t ∪ u := hu ▸ Set.mem_univ ()
  rcases h0 with h0 | h0
  · exact Set.disjoint_left.1 hd h0 (e ⟨(), h0⟩).2
  · exact Set.disjoint_left.1 hd (e.symm ⟨(), h0⟩).2 h0

-- helper: same with ncard
theorem ncardCex : ¬ ∃ t u : Set Unit, t ∪ u = Set.univ ∧ Disjoint t u ∧ t.ncard = u.ncard := by
  rintro ⟨t, u, hu, hd, hc⟩
  have := Set.ncard_union_eq hd (Set.toFinite t) (Set.toFinite u)
  rw [hu, Set.ncard_univ, Nat.card_unique] at this; omega

-- helper: a finite piece and an infinite piece of ℕ, indexed by Bool
def sp : Bool → Set ℕ := fun b => if b then {0} else {0}ᶜ
theorem sp_disj : Pairwise (Function.onFun Disjoint sp) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [sp, Function.onFun, disjoint_compl_left, disjoint_compl_right]
theorem sp_fin : (sp true).Finite := by simp [sp]
theorem sp_union : (⋃ b, sp b) = Set.univ := by
  ext n; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases hn : n = 0
  · exact ⟨true, by simp [sp, hn]⟩
  · exact ⟨false, by simp [sp, hn]⟩
theorem sp_sum : ∑ᶠ b, (sp b).ncard = 1 := by
  rw [finsum_eq_sum_of_fintype, Fintype.sum_bool]
  simp [sp, (Set.finite_singleton (0 : ℕ)).infinite_compl.ncard]

-- helper: the families of a discrete ordered copy of ℕ
def DN := ℕ
instance : Semiring DN := inferInstanceAs (Semiring ℕ)
instance : PartialOrder DN where
  le a b := a = b
  le_refl a := rfl
  le_trans a b c h1 h2 := h1.trans h2
  le_antisymm a b h _ := h
theorem DN_not : ¬ ((0 : DN) ≤ 0 + 1) := by
  show ¬ ((0 : ℕ) = 0 + 1); decide

open Classical in
-- helper: a selection function on sets of Bool
noncomputable def selB (s : Set Bool) : Option Bool := if true ∈ s then some true else none
theorem selB_ok : ∀ (s : Set Bool) (a : Bool), selB s = some a → a ∈ s := by
  intro s a h; unfold selB at h; split_ifs at h with h1
  · cases h; exact h1
theorem selB_0 : Set.enumerate selB {true} 0 = some true := by simp [Set.enumerate, selB]
theorem selB_1 : Set.enumerate selB {true} 1 = none := by simp [Set.enumerate, selB]

-- helper: the family containing only univ is closed under finite intersections
theorem fiU : FiniteInter ({Set.univ} : Set (Set Bool)) :=
  ⟨rfl, fun s hs t ht => by simp_all⟩
theorem tf_ne : ¬ (({true} : Set Bool) ∩ {false} = {true} ∨ ({true} : Set Bool) ∩ {false} = {false}) := by
  rintro (h | h)
  · have := h ▸ Set.mem_singleton true; simp at this
  · have := h ▸ Set.mem_singleton false; simp at this

end W1c3

-- `Set.Infinite.exists_union_disjoint_cardinal_eq_of_infinite` idx 2: necessary
theorem c3_0 : ¬ drop0% Set.Infinite.exists_union_disjoint_cardinal_eq_of_infinite 2 := fun h =>
  cardCex (h (s := Set.univ))

-- `Set.exists_union_disjoint_cardinal_eq_of_even` idx 2: necessary
theorem c3_1 : ¬ drop0% Set.exists_union_disjoint_cardinal_eq_of_even 2 := fun h =>
  cardCex (h (s := Set.univ))

-- `Set.exists_union_disjoint_ncard_eq_of_even` idx 2: necessary
theorem c3_2 : ¬ drop0% Set.exists_union_disjoint_ncard_eq_of_even 2 := fun h =>
  ncardCex (h (s := Set.univ))

-- `Set.Finite.ncard_biUnion` idx 3: removable (if infinitely many s i with i ∈ t are nonempty, the disjoint union is infinite and both sides are 0)
theorem c3_3 : drop% Set.Finite.ncard_biUnion 3 := by
  intro α ι t s hs h
  have key : t ∩ Function.support (fun i => (s i).ncard) = {i ∈ t | (s i).Nonempty} := by
    ext i; simp only [Set.mem_inter_iff, Set.mem_sep_iff, Function.mem_support, ne_eq]
    constructor
    · rintro ⟨hi, h0⟩; exact ⟨hi, Set.nonempty_of_ncard_ne_zero h0⟩
    · rintro ⟨hi, hn⟩; exact ⟨hi, ((Set.ncard_pos (hs i hi)).2 hn).ne'⟩
  by_cases hT : {i ∈ t | (s i).Nonempty}.Finite
  · have e1 : (⋃ i ∈ t, s i) = ⋃ i ∈ {i ∈ t | (s i).Nonempty}, s i := by
      ext x; simp only [Set.mem_iUnion, Set.mem_sep_iff]
      exact ⟨fun ⟨i, hi, hx⟩ => ⟨i, ⟨hi, x, hx⟩, hx⟩, fun ⟨i, ⟨hi, _⟩, hx⟩ => ⟨i, hi, hx⟩⟩
    rw [e1, Set.Finite.ncard_biUnion hT (fun i hi => hs i hi.1) (h.subset (fun i hi => hi.1)), ← key,
      finsum_mem_inter_support]
  · have hU : (⋃ i ∈ t, s i).Infinite := fun hf => hT ((h.finite_biUnion_iff.1 hf).2)
    rw [hU.ncard, finsum_mem_eq_zero_of_infinite (by rw [key]; exact hT)]

-- `Set.Finite.ncard_biUnion` idx 5: necessary
theorem c3_4 : ¬ drop0% Set.Finite.ncard_biUnion 5 := fun h => by
  have := h (t := Set.univ) Set.finite_univ (s := sp) (fun a _ b _ hab => sp_disj hab)
  simp only [Set.mem_univ, Set.iUnion_true, finsum_true, sp_union, sp_sum, Set.ncard_univ,
    Nat.card_eq_zero_of_infinite] at this
  exact absurd this (by decide)

-- `Set.Finite.ncard_biUnion` idx 6: necessary
theorem c3_5 : ¬ drop0% Set.Finite.ncard_biUnion 6 := fun h => by
  have := h (t := Set.univ) Set.finite_univ (s := fun _ : Bool => ({0} : Set ℕ)) (fun _ _ => Set.finite_singleton 0)
  simp [finsum_eq_sum_of_fintype] at this

-- `Set.ncard_iUnion_of_finite` idx 2: removable (if infinitely many s i are nonempty, the disjoint union is infinite and both sides are 0)
theorem c3_6 : drop% Set.ncard_iUnion_of_finite 2 := by
  intro α ι s hs h
  have := c3_3 (t := Set.univ) (s := s) (fun i _ => hs i) (fun a _ b _ hab => h hab)
  simpa only [Set.mem_univ, Set.iUnion_true, finsum_true] using this

-- `Set.ncard_iUnion_of_finite` idx 4: necessary
theorem c3_7 : ¬ drop0% Set.ncard_iUnion_of_finite 4 := fun h => by
  have := h (s := sp) sp_disj
  simp only [sp_union, sp_sum, Set.ncard_univ, Nat.card_eq_zero_of_infinite] at this
  exact absurd this (by decide)

-- `Set.ncard_iUnion_of_finite` idx 5: necessary
theorem c3_8 : ¬ drop0% Set.ncard_iUnion_of_finite 5 := fun h => by
  have := h (s := fun _ : Bool => ({0} : Set ℕ)) (fun _ => Set.finite_singleton 0)
  simp [finsum_eq_sum_of_fintype] at this

-- `Set.Finite.encard_biUnion` idx 3: necessary
theorem c3_9 : ¬ drop0% Set.Finite.encard_biUnion 3 := fun h => by
  have := h (t := (Set.univ : Set ℕ)) (s := fun i : ℕ => ({i} : Set ℕ))
    (fun a _ b _ hab => Set.disjoint_singleton.2 hab)
  simp only [Set.mem_univ, Set.iUnion_true, finsum_true, Set.encard_singleton] at this
  rw [finsum_of_infinite_support (by simp [Function.support_const, Set.infinite_univ])] at this
  rw [show (⋃ i : ℕ, ({i} : Set ℕ)) = Set.univ by ext; simp,
    Set.encard_eq_top_iff.2 Set.infinite_univ] at this
  exact absurd this (by simp)

-- `Set.Finite.encard_biUnion` idx 5: necessary
theorem c3_10 : ¬ drop0% Set.Finite.encard_biUnion 5 := fun h => by
  have := h (t := Set.univ) Set.finite_univ (s := fun _ : Bool => ({0} : Set ℕ))
  simp [finsum_eq_sum_of_fintype] at this

-- `Set.encard_iUnion_of_finite` idx 4: necessary
theorem c3_11 : ¬ drop0% Set.encard_iUnion_of_finite 4 := fun h => by
  have := h (s := fun _ : Bool => ({0} : Set ℕ))
  simp [finsum_eq_sum_of_fintype] at this

-- `Set.Finite.ncard_biUnion_le` idx 3: necessary
theorem c3_12 : ¬ drop0% Set.Finite.ncard_biUnion_le 3 := fun h => by
  have := h (t := (Set.univ : Set ℕ)) (fun _ => ({0} : Set ℕ))
  simp only [Set.mem_univ, Set.iUnion_true, finsum_true, Set.ncard_singleton, Set.iUnion_const] at this
  rw [finsum_of_infinite_support (by simp [Function.support_const, Set.infinite_univ])] at this
  exact absurd this (by decide)

-- `Set.Finite.encard_biUnion_le` idx 3: necessary
theorem c3_13 : ¬ drop0% Set.Finite.encard_biUnion_le 3 := fun h => by
  have := h (t := (Set.univ : Set ℕ)) (fun _ => ({0} : Set ℕ))
  simp only [Set.mem_univ, Set.iUnion_true, finsum_true, Set.encard_singleton, Set.iUnion_const] at this
  rw [finsum_of_infinite_support (by simp [Function.support_const, Set.infinite_univ])] at this
  exact absurd this (by simp)

-- `Set.ncard_iUnion_le_of_finite` idx 2: necessary
theorem c3_14 : ¬ drop0% Set.ncard_iUnion_le_of_finite 2 := fun h => by
  have := h (fun _ : ℕ => ({0} : Set ℕ))
  simp only [Set.ncard_singleton, Set.iUnion_const] at this
  rw [finsum_of_infinite_support (by simp [Function.support_const, Set.infinite_univ])] at this
  exact absurd this (by decide)

-- `Set.encard_iUnion_le_of_finite` idx 2: necessary
theorem c3_15 : ¬ drop0% Set.encard_iUnion_le_of_finite 2 := fun h => by
  have := h (fun _ : ℕ => ({0} : Set ℕ))
  simp only [Set.encard_singleton, Set.iUnion_const] at this
  rw [finsum_of_infinite_support (by simp [Function.support_const, Set.infinite_univ])] at this
  exact absurd this (by simp)

-- `FiniteInter.inter_mem` idx 2: necessary
theorem c3_16 : ¬ drop0% FiniteInter.inter_mem 2 := fun h => by
  have := h (S := ({{true}, {false}} : Set (Set Bool))) (s := {true}) (by simp) (t := {false}) (by simp)
  exact tf_ne (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this)

-- `FiniteInter.inter_mem` idx 4: necessary
theorem c3_17 : ¬ drop0% FiniteInter.inter_mem 4 := fun h => by
  have := h fiU (s := ∅) (t := Set.univ) rfl
  simp [Set.ext_iff] at this

-- `FiniteInter.inter_mem` idx 6: necessary
theorem c3_18 : ¬ drop0% FiniteInter.inter_mem 6 := fun h => by
  have := h fiU (s := Set.univ) rfl (t := ∅)
  simp [Set.ext_iff] at this

-- `FiniteInter.finiteInterClosure_induction` idx 3: necessary
theorem c3_19 : ¬ drop0% FiniteInter.finiteInterClosure_induction 3 := fun h => by
  have := h (S := ({∅} : Set (Set Bool))) (motive := fun s _ => s = Set.univ) rfl
    (fun s t _ _ hs ht => by rw [hs, ht]; simp) (s := ∅) (FiniteInter.subset_finiteInterClosure _ rfl)
  simp [Set.ext_iff] at this

-- `FiniteInter.finiteInterClosure_induction` idx 4: necessary
theorem c3_20 : ¬ drop0% FiniteInter.finiteInterClosure_induction 4 := fun h => by
  have := h (S := (∅ : Set (Set Bool))) (motive := fun s _ => s ∈ (∅ : Set (Set Bool))) (fun _ hs => hs)
    (fun s t _ _ hs _ => hs.elim) (s := Set.univ) (FiniteInter.finiteInterClosure_finiteInter _).univ_mem
  exact this

-- `FiniteInter.finiteInterClosure_induction` idx 5: necessary
theorem c3_21 : ¬ drop0% FiniteInter.finiteInterClosure_induction 5 := fun h => by
  have := h (S := ({{true}, {false}} : Set (Set Bool)))
    (motive := fun s _ => s ∈ ({{true}, {false}} : Set (Set Bool)) ∨ s = Set.univ) (fun _ hs => Or.inl hs)
    (Or.inr rfl) (s := {true} ∩ {false})
    ((FiniteInter.finiteInterClosure_finiteInter _).inter_mem
      (FiniteInter.subset_finiteInterClosure _ (by simp)) (FiniteInter.subset_finiteInterClosure _ (by simp)))
  rcases this with h1 | h1
  · exact tf_ne (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h1)
  · have := h1 ▸ Set.mem_univ true; simp at this

-- `FiniteInter.finiteInterClosure_induction` idx 7: necessary
theorem c3_22 : ¬ indep0% FiniteInter.finiteInterClosure_induction 7 := fun h => by
  have := h (S := (∅ : Set (Set Bool))) (motive := fun _ _ => True) (fun _ _ => trivial) trivial
    (fun _ _ _ _ _ _ => trivial) (s := ∅)
  have := FiniteInter.finiteInterClosure_min (Set.empty_subset _) fiU this
  have := this ▸ Set.mem_univ true; simp at this

-- `FiniteInter.finiteInterClosure_min` idx 3: necessary
theorem c3_23 : ¬ drop0% FiniteInter.finiteInterClosure_min 3 := fun h => by
  have := h (S := ({∅} : Set (Set Bool))) fiU (FiniteInter.subset_finiteInterClosure _ rfl)
  have := (show (∅ : Set Bool) = Set.univ from this) ▸ Set.mem_univ true; simp at this

-- `FiniteInter.finiteInterClosure_min` idx 4: necessary
theorem c3_24 : ¬ drop0% FiniteInter.finiteInterClosure_min 4 := fun h =>
  h (S := (∅ : Set (Set Bool))) (T := ∅) subset_rfl (FiniteInter.finiteInterClosure_finiteInter _).univ_mem

-- `FiniteInter.finiteInter_mem` idx 4: necessary
theorem c3_25 : ¬ drop0% FiniteInter.finiteInter_mem 4 := fun h => by
  have := h fiU {∅}
  simp only [Finset.coe_singleton, Set.sInter_singleton, Set.mem_singleton_iff] at this
  have := this ▸ Set.mem_univ true; simp at this

-- `FiniteInter.finiteInterClosure_insert` idx 5: necessary
theorem c3_26 : ¬ drop0% FiniteInter.finiteInterClosure_insert 5 := fun h => by
  have := h (A := Set.univ) fiU ∅
  simp only [Set.mem_singleton_iff, exists_eq_left, Set.univ_inter, or_self] at this
  have := this ▸ Set.mem_univ true; simp at this

-- `FiniteInter.mk₂` idx 2: necessary
theorem c3_27 : ¬ drop0% FiniteInter.mk₂ 2 := fun h => by
  have := (h (S := ({{true}, {false}} : Set (Set Bool)))).inter_mem (s := {true}) (t := {false})
    (by simp) (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  rcases this with h1 | h1
  · have := h1 ▸ Set.mem_univ true; simp at this
  · exact tf_ne h1

-- `Set.enumerate_eq_none` idx 6: necessary
theorem c3_88 : ¬ drop0% Set.enumerate_eq_none 6 := fun h => by
  have := h selB (s := {true}) (n₁ := 1) (n₂ := 0) selB_1
  rw [selB_0] at this; cases this

-- `Set.enumerate_inj` idx 7: necessary
theorem c3_89 : ¬ drop0% Set.enumerate_inj 7 := fun h => by
  have := h selB (n₁ := 1) (n₂ := 0) (a := true) (s := {true}) selB_ok selB_0
  cases this

-- `Set.enumerate_inj` idx 8: necessary
theorem c3_90 : ¬ drop0% Set.enumerate_inj 8 := fun h => by
  have := h selB (n₁ := 0) (n₂ := 1) (a := true) (s := {true}) selB_ok selB_0
  cases this

-- `Set.Subsingleton.equitableOn` idx 4: necessary
theorem c3_91 : ¬ drop0% Set.Subsingleton.equitableOn 4 := fun h =>
  DN_not (h (β := DN) (s := ({()} : Set Unit)) Set.subsingleton_singleton (fun _ => 0) rfl rfl)

-- `Set.Subsingleton.equitableOn` idx 6: necessary
theorem c3_92 : ¬ drop0% Set.Subsingleton.equitableOn 6 := fun h => by
  have := h (β := ℕ) (s := (Set.univ : Set Bool)) (fun b => if b then 2 else 0) (a₁ := true) (a₂ := false) trivial trivial
  simp at this

-- `Set.equitableOn_singleton` idx 4: necessary
theorem c3_93 : ¬ drop0% Set.equitableOn_singleton 4 := fun h =>
  DN_not (h (β := DN) () (fun _ => 0) rfl rfl)

-- `Finset.EquitableOn.le` idx 5: necessary
theorem c3_94 : ¬ drop0% Finset.EquitableOn.le 5 := fun h => by
  have := h (s := {0}) (f := fun n => if n = 0 then 1 else 0) (a := 1)
    (Set.Subsingleton.equitableOn (by simp) _)
  simp at this

-- `Finset.EquitableOn.le_add_one` idx 4: necessary
theorem c3_95 : ¬ drop0% Finset.EquitableOn.le_add_one 4 := fun h => by
  have := h (s := {0, 1}) (f := fun n => if n = 0 then 3 else 0) (a := 0) (by simp)
  simp at this
