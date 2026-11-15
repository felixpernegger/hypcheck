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

namespace W1c4

def TN := ℕ
instance : SMul ℕ TN := ⟨fun _ b => b⟩
instance : SMulZeroClass TN ℕ where
  smul b c := (show ℕ from b) * c
  smul_zero b := Nat.mul_zero _
def TZ := ℕ
instance : Zero TZ := ⟨(0:ℕ)⟩
instance : SMulZeroClass ℕ TZ where
  smul b c := show ℕ from b * (show ℕ from c)
  smul_zero b := Nat.mul_zero b
instance : SMulZeroClass ℕᵐᵒᵖ TZ where
  smul _ c := c
  smul_zero _ := rfl
def NS := ℕ
instance : AddCommMonoid NS := inferInstanceAs (AddCommMonoid ℕ)
instance : PartialOrder NS := inferInstanceAs (PartialOrder ℕ)
instance : CanonicallyOrderedAdd NS := inferInstanceAs (CanonicallyOrderedAdd ℕ)
instance : Sub NS := ⟨fun _ _ => (0:ℕ)⟩
instance : DecidableEq NS := inferInstanceAs (DecidableEq ℕ)
theorem ns_not_orderedSub : ¬ OrderedSub NS := fun h => by
  have := (h.tsub_le_iff_right (show NS from (1:ℕ)) (show NS from (0:ℕ)) (show NS from (0:ℕ))).1 (le_refl _)
  exact absurd (show (1:ℕ) ≤ 0 + 0 from this) (by decide)
theorem notWF {β : Type*} {r : β → β → Prop} (f : ℕ → β) (hf : ∀ n, r (f (n+1)) (f n)) :
    ¬ WellFounded r := by
  intro h
  obtain ⟨m, ⟨n, rfl⟩, hm⟩ := h.has_min (Set.range f) ⟨f 0, 0, rfl⟩
  exact hm _ ⟨n+1, rfl⟩ (hf n)
theorem notAcc {β : Type*} {R : β → β → Prop} (f : ℕ → β) (hf : ∀ n, R (f (n+1)) (f n)) : ¬ Acc R (f 0) := by
  intro h
  have : ∀ y, Acc R y → ∀ n, y = f n → False := fun y hy => by
    induction hy with
    | intro z _ ih => intro n hz; subst hz; exact ih _ (hf n) (n+1) rfl
  exact this _ h 0 rfl
theorem notAccSelf {β : Type*} {R : β → β → Prop} {x : β} (hx : R x x) : ¬ Acc R x :=
  notAcc (fun _ => x) (fun _ => hx)
/-- relation on ℕ with the single step 1 below 0: well-founded, but 0 is not minimal -/
theorem wf10 : WellFounded (fun a b : ℕ => a = 1 ∧ b = 0) :=
  ⟨fun b => Acc.intro b (fun a hab => Acc.intro a (fun c hca => absurd (hab.1.symm.trans hca.2) one_ne_zero))⟩
theorem wfLtGt : WellFounded ((fun a b : ℕ => a > b)ᶜ ⊓ fun x1 x2 => x1 ≠ x2) :=
  Subrelation.wf (fun {a b} h => by simp only [Pi.inf_apply, Pi.compl_apply, compl_iff_not, inf_Prop_eq] at h; omega) wellFounded_lt
theorem wfUnit (r : Unit → Unit → Prop) : WellFounded (rᶜ ⊓ fun x1 x2 => x1 ≠ x2) :=
  ⟨fun a => ⟨a, fun b h => absurd (Subsingleton.elim b a) (by simp only [Pi.inf_apply, inf_Prop_eq] at h; exact h.2)⟩⟩
/-- Bool with the empty strict order -/
def B2 := Bool
instance : LT B2 := ⟨fun _ _ => False⟩
instance : DecidableEq B2 := inferInstanceAs (DecidableEq Bool)
instance : WellFoundedGT B2 := ⟨fun a => Acc.intro a (fun _ h => False.elim h)⟩
instance : WellFoundedLT B2 := ⟨fun a => Acc.intro a (fun _ h => False.elim h)⟩
def b2 (b : Bool) : B2 := b
/-- ℕ whose zero is 1, so the raw 0 lies below zero; still well-founded -/
def N1 := ℕ
instance : Zero N1 := ⟨(1:ℕ)⟩
instance : LinearOrder N1 := inferInstanceAs (LinearOrder ℕ)
instance : WellFoundedLT N1 := inferInstanceAs (WellFoundedLT ℕ)
instance : DecidableEq N1 := inferInstanceAs (DecidableEq ℕ)
def n0 : N1 := (0:ℕ)
theorem n0_lt : n0 < (0 : N1) := Nat.zero_lt_one
theorem n0_le : n0 ≤ (0 : N1) := Nat.zero_le 1
/-- raw 0 on indices 0..n, zero elsewhere -/
def m1 (n : ℕ) : Π₀ _ : ℕ, N1 := DFinsupp.mk (Finset.range (n+1)) (fun _ => n0)
theorem m1_lt (n : ℕ) : m1 (n+1) < m1 n := by
  rw [DFinsupp.lt_def]
  refine ⟨fun k => ?_, n+1, ?_⟩
  · simp only [m1, DFinsupp.mk_apply, Finset.mem_range]
    split_ifs <;> first | exact le_rfl | exact n0_le | omega
  · simp only [m1, DFinsupp.mk_apply, Finset.mem_range]
    split_ifs <;> first | exact n0_lt | omega
def q (n : ℕ) : ℚ≥0 := 1 / ((n:ℚ≥0) + 1)
theorem q_lt (n : ℕ) : q (n+1) < q n := by
  unfold q; gcongr; push_cast; linarith
theorem sumBool {γ : Type} [AddCommMonoid γ] (F : Bool → ℤ → γ) (hF : ∀ i, F i 0 = 0) :
    (DFinsupp.single true 1 + DFinsupp.single false 1 : Π₀ _ : Bool, ℤ).sum F = F true 1 + F false 1 := by
  rw [DFinsupp.sum_eq_sum_fintype _ hF]; simp [Fintype.sum_bool]
theorem prodBool {γ : Type} [CommMonoid γ] (F : Bool → ℤ → γ) (hF : ∀ i, F i 0 = 1) :
    (DFinsupp.single true 1 + DFinsupp.single false 1 : Π₀ _ : Bool, ℤ).prod F = F true 1 * F false 1 := by
  rw [DFinsupp.prod_eq_prod_fintype _ hF]; simp [Fintype.prod_bool]

end W1c4
open W1c4

-- `Ctop.inter_mem` idx 6: necessary
theorem w1c4_0 : ¬ indep0% Ctop.inter_mem 6 := fun h => by
  have := h (default : Ctop Unit (Set Unit)) ∅ ∅ ()
  simp [default] at this

-- `Ctop.inter_sub` idx 6: necessary
theorem w1c4_1 : ¬ indep0% Ctop.inter_sub 6 := fun h => by
  have := h (default : Ctop Unit (Set Unit)) ∅ ∅ ()
  simp [default] at this

-- `Ctop.coe_mk` idx 4: necessary
theorem w1c4_2 : ¬ indep0% Ctop.coe_mk 4 := fun h => by
  have := h (α := Unit) (σ := Unit) (fun _ => ∅) (fun _ => ()) (fun _ _ _ _ => ())
    (fun _ _ _ hx => by simp at hx) (fun _ _ _ hx => by simp at hx) () ()
  simp at this

-- `Ctop.coe_mk` idx 6: necessary
theorem w1c4_3 : ¬ indep0% Ctop.coe_mk 6 := fun h => by
  have := h (α := Unit) (σ := Bool) (fun b => if b then Set.univ else ∅) (fun _ => true) (fun _ => by simp)
    (fun _ _ _ _ => false) (fun _ _ _ _ => by simp) true true true () (by simp)
  simp at this

-- `Ctop.coe_mk` idx 7: necessary
theorem w1c4_4 : ¬ indep0% Ctop.coe_mk 7 := fun h => by
  have := h (α := Bool) (σ := Set Bool) id (fun _ => Set.univ) (fun _ => trivial)
    (fun _ _ _ _ => Set.univ) (fun _ _ _ _ => trivial) {true} {true} {true} true (by simp)
  have := this (Set.mem_univ false)
  simp at this

-- `Ctop.Realizer.ext'` idx 4: necessary
theorem w1c4_5 : ¬ drop0% Ctop.Realizer.ext' 4 := fun h => by
  have e := h (α := Bool) (T := ⊥) (F := ⟨fun _ : Unit => Set.univ, fun _ => (), fun _ => trivial,
    fun _ _ _ _ => (), fun _ _ _ _ => trivial, fun _ _ _ _ => by simp⟩)
  have : ({true} : Set Bool) ∈ @nhds Bool (Ctop.toTopsp ⟨fun _ : Unit => Set.univ, fun _ => (), fun _ => trivial,
    fun _ _ _ _ => (), fun _ _ _ _ => trivial, fun _ _ _ _ => by simp⟩) true := by
    rw [e]
    letI : TopologicalSpace Bool := ⊥
    haveI : DiscreteTopology Bool := ⟨rfl⟩
    exact IsOpen.mem_nhds (isOpen_discrete _) rfl
  rw [Ctop.mem_nhds_toTopsp] at this
  obtain ⟨b, -, hb⟩ := this
  exact absurd (hb (Set.mem_univ false)) (by simp)

-- `Ctop.Realizer.ext` idx 4: necessary
theorem w1c4_6 : ¬ drop0% Ctop.Realizer.ext 4 := fun h => by
  have e := h (α := Bool) (T := ⊤) (F := (default : Ctop Bool (Set Bool)))
    (fun a s hs => ⟨s, @mem_of_mem_nhds Bool ⊤ _ _ hs, subset_rfl⟩)
  have : ({true} : Set Bool) ∈ @nhds Bool (Ctop.toTopsp (default : Ctop Bool (Set Bool))) true := by
    rw [Ctop.mem_nhds_toTopsp]; exact ⟨{true}, rfl, subset_rfl⟩
  rw [e, nhds_top, Filter.mem_top] at this
  exact absurd (this ▸ Set.mem_univ false : false ∈ ({true} : Set Bool)) (by simp)

-- `Ctop.Realizer.ext` idx 5: necessary
theorem w1c4_7 : ¬ drop0% Ctop.Realizer.ext 5 := fun h => by
  have e := h (α := Bool) (T := ⊥) (F := ⟨fun _ : Unit => Set.univ, fun _ => (), fun _ => trivial,
    fun _ _ _ _ => (), fun _ _ _ _ => trivial, fun _ _ _ _ => by simp⟩) (fun _ => @isOpen_univ Bool ⊥)
  have : ({true} : Set Bool) ∈ @nhds Bool (Ctop.toTopsp ⟨fun _ : Unit => Set.univ, fun _ => (), fun _ => trivial,
    fun _ _ _ _ => (), fun _ _ _ _ => trivial, fun _ _ _ _ => by simp⟩) true := by
    rw [e]
    letI : TopologicalSpace Bool := ⊥
    haveI : DiscreteTopology Bool := ⟨rfl⟩
    exact IsOpen.mem_nhds (isOpen_discrete _) rfl
  rw [Ctop.mem_nhds_toTopsp] at this
  obtain ⟨b, -, hb⟩ := this
  exact absurd (hb (Set.mem_univ false)) (by simp)

-- `instNonemptyRealizerOfFinite` idx 3: necessary
theorem w1c4_8 : ¬ drop0% instNonemptyRealizerOfFinite 3 := fun h => by
  let _ : TopologicalSpace Unit := ⊥
  obtain ⟨R⟩ := h (α := Unit) (β := ℕ) (Ctop.Realizer.id) (fun _ => Set.univ)
  have hl := (locallyFinite_iff_exists_realizer Ctop.Realizer.id).2 ⟨R⟩
  obtain ⟨t, ht, hfin⟩ := hl ()
  have : {i : ℕ | ((fun _ : ℕ => (Set.univ : Set Unit)) i ∩ t).Nonempty} = Set.univ :=
    Set.eq_univ_of_forall fun i => ⟨(), trivial, mem_of_mem_nhds ht⟩
  rw [this] at hfin
  exact Set.infinite_univ hfin

-- `List.IsChain.count_true_le_count_false_add_one` idx 1: necessary
theorem w1c4_9 : ¬ drop0% List.IsChain.count_true_le_count_false_add_one 1 := fun h => by
  have := h (l := [true, true, true])
  revert this; decide

-- `Bundle.TotalSpace.ext` idx 5: necessary
theorem w1c4_10 : ¬ drop0% Bundle.TotalSpace.ext 5 := fun h => by
  have := h (B := Bool) (F := Unit) (E := fun _ => Unit) (x := ⟨true, ()⟩) (y := ⟨false, ()⟩) HEq.rfl
  have := congrArg Bundle.TotalSpace.proj this
  simp at this

-- `Bundle.TotalSpace.ext` idx 6: necessary
theorem w1c4_11 : ¬ drop0% Bundle.TotalSpace.ext 6 := fun h => by
  have := h (B := Unit) (F := Unit) (E := fun _ => Bool) (x := ⟨(), true⟩) (y := ⟨(), false⟩) rfl
  have := congrArg Bundle.TotalSpace.snd this
  simp at this

-- `Bundle.instNonemptyPullback` idx 5: necessary
theorem w1c4_12 : ¬ drop0% Bundle.instNonemptyPullback 5 := fun h => by
  obtain ⟨e⟩ := h (B := Unit) (E := fun _ => Empty) (B' := Unit) (f := id) (x := ())
  exact e.elim

-- `DFinsupp.sum_of_support_subset` idx 10: necessary
theorem w1c4_13 : ¬ drop0% DFinsupp.sum_of_support_subset 10 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (f := DFinsupp.single () 1) (g := fun _ b => b) (s := ∅) (by simp)
  simp [DFinsupp.sum] at this

-- `DFinsupp.sum_of_support_subset` idx 11: necessary
theorem w1c4_14 : ¬ drop0% DFinsupp.sum_of_support_subset 11 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (f := 0) (g := fun _ _ => 1) (s := {()}) (by simp)
  simp [DFinsupp.sum] at this

-- `DFinsupp.prod_of_support_subset` idx 10: necessary
theorem w1c4_15 : ¬ drop0% DFinsupp.prod_of_support_subset 10 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (f := DFinsupp.single () 2) (g := fun _ b => b) (s := ∅) (by simp)
  simp [DFinsupp.prod] at this

-- `DFinsupp.prod_of_support_subset` idx 11: necessary
theorem w1c4_16 : ¬ drop0% DFinsupp.prod_of_support_subset 11 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (f := 0) (g := fun _ _ => 2) (s := {()}) (by simp)
  simp [DFinsupp.prod] at this

-- `DFinsupp.sum_congr_of_eq_on_union` idx 11: necessary
theorem w1c4_17 : ¬ drop0% DFinsupp.sum_congr_of_eq_on_union 11 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (f1 := DFinsupp.single () 1) (f2 := DFinsupp.single () 1)
    (g1 := fun _ b => b) (g2 := fun _ b => 2 * b) (by simp) (by simp)
  simp [DFinsupp.sum] at this

-- `DFinsupp.sum_congr_of_eq_on_union` idx 12: necessary
theorem w1c4_18 : ¬ drop0% DFinsupp.sum_congr_of_eq_on_union 12 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (f1 := 0) (f2 := DFinsupp.single () 1)
    (g1 := fun _ _ => 1) (g2 := fun _ b => b) (by simp) (by simp)
  simp [DFinsupp.sum] at this

-- `DFinsupp.sum_congr_of_eq_on_union` idx 13: necessary
theorem w1c4_19 : ¬ drop0% DFinsupp.sum_congr_of_eq_on_union 13 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (f1 := DFinsupp.single () 1) (f2 := 0)
    (g1 := fun _ b => b) (g2 := fun _ _ => 1) (by simp) (by simp)
  simp [DFinsupp.sum] at this

-- `DFinsupp.prod_congr_of_eq_on_union` idx 11: necessary
theorem w1c4_20 : ¬ drop0% DFinsupp.prod_congr_of_eq_on_union 11 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (f1 := DFinsupp.single () 1) (f2 := DFinsupp.single () 1)
    (g1 := fun _ b => 1 + b) (g2 := fun _ b => 1 + 2 * b) (by simp) (by simp)
  simp [DFinsupp.prod] at this

-- `DFinsupp.prod_congr_of_eq_on_union` idx 12: necessary
theorem w1c4_21 : ¬ drop0% DFinsupp.prod_congr_of_eq_on_union 12 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (f1 := 0) (f2 := DFinsupp.single () 1)
    (g1 := fun _ _ => 2) (g2 := fun _ b => b + 1) (by simp) (by simp)
  simp [DFinsupp.prod] at this

-- `DFinsupp.prod_congr_of_eq_on_union` idx 13: necessary
theorem w1c4_22 : ¬ drop0% DFinsupp.prod_congr_of_eq_on_union 13 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (f1 := DFinsupp.single () 1) (f2 := 0)
    (g1 := fun _ b => b + 1) (g2 := fun _ _ => 2) (by simp) (by simp)
  simp [DFinsupp.prod] at this

-- `map_dfinsuppSum` idx 11: necessary
theorem w1c4_23 : ¬ drop0% map_dfinsuppSum 11 := fun h => by
  let _ : FunLike (ℤ → ℤ) ℤ ℤ := ⟨id, fun _ _ h => h⟩
  have := h (ι := Unit) (β := fun _ => ℤ) (R := ℤ) (S := ℤ) (H := ℤ → ℤ) (fun x => x + 1) 0 (fun _ b => b)
  simp [DFinsupp.sum, ← DFinsupp.single_add] at this
  exact absurd this (by decide)

-- `map_dfinsuppProd` idx 11: necessary
theorem w1c4_24 : ¬ drop0% map_dfinsuppProd 11 := fun h => by
  let _ : FunLike (ℤ → ℤ) ℤ ℤ := ⟨id, fun _ _ h => h⟩
  have := h (ι := Unit) (β := fun _ => ℤ) (R := ℤ) (S := ℤ) (H := ℤ → ℤ) (fun x => x + 1) 0 (fun _ b => b)
  simp [DFinsupp.prod, ← DFinsupp.single_add] at this
  exact absurd this (by decide)

-- `DFinsupp.sum_mapRange_index` idx 11: necessary
theorem w1c4_25 : ¬ indep0% DFinsupp.sum_mapRange_index 11 := fun h => by
  have := h (ι := Unit) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (γ := ℤ) (f := fun _ _ => 1) (g := 0) (h := fun _ _ => (0:ℤ)) (fun _ => rfl) ()
  simp at this

-- `DFinsupp.sum_mapRange_index` idx 14: necessary
theorem w1c4_26 : ¬ drop0% DFinsupp.sum_mapRange_index 14 := fun h => by
  have := h (ι := Unit) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (γ := ℤ) (f := fun _ _ => 0) (hf := fun _ => rfl)
    (g := DFinsupp.single () 1) (h := fun _ _ => 1)
  simp [DFinsupp.sum] at this

-- `DFinsupp.prod_mapRange_index` idx 11: necessary
theorem w1c4_27 : ¬ indep0% DFinsupp.prod_mapRange_index 11 := fun h => by
  have := h (ι := Unit) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (γ := ℤ) (f := fun _ _ => 1) (g := 0) (h := fun _ _ => (1:ℤ)) (fun _ => rfl) ()
  simp at this

-- `DFinsupp.prod_mapRange_index` idx 14: necessary
theorem w1c4_28 : ¬ drop0% DFinsupp.prod_mapRange_index 14 := fun h => by
  have := h (ι := Unit) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (γ := ℤ) (f := fun _ _ => 0) (hf := fun _ => rfl)
    (g := DFinsupp.single () 1) (h := fun _ _ => 2)
  simp [DFinsupp.prod] at this

-- `DFinsupp.sum_single_index` idx 10: necessary
theorem w1c4_29 : ¬ drop0% DFinsupp.sum_single_index 10 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (i := ()) (b := 0) (h := fun _ _ => 1)
  simp [DFinsupp.sum] at this

-- `DFinsupp.prod_single_index` idx 10: necessary
theorem w1c4_30 : ¬ drop0% DFinsupp.prod_single_index 10 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (i := ()) (b := 0) (h := fun _ _ => 2)
  simp [DFinsupp.prod] at this

-- `DFinsupp.sum_neg_index` idx 9: removable
theorem w1c4_31 : drop% DFinsupp.sum_neg_index 9 := by
  intro ι γ β _ _ _ _ g h
  simp only [DFinsupp.sum, DFinsupp.support_neg, DFinsupp.neg_apply]

-- `DFinsupp.prod_neg_index` idx 9: removable
theorem w1c4_32 : drop% DFinsupp.prod_neg_index 9 := by
  intro ι γ β _ _ _ _ g h
  simp only [DFinsupp.prod, DFinsupp.support_neg, DFinsupp.neg_apply]

-- `DFinsupp.sum_eq_zero` idx 9: necessary
theorem w1c4_33 : ¬ drop0% DFinsupp.sum_eq_zero 9 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (f := DFinsupp.single () 1) (h := fun _ b => b)
  simp [DFinsupp.sum] at this

-- `DFinsupp.prod_eq_one` idx 9: necessary
theorem w1c4_34 : ¬ drop0% DFinsupp.prod_eq_one 9 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (f := DFinsupp.single () 2) (h := fun _ b => b)
  simp [DFinsupp.prod] at this

-- `DFinsupp.sum_add_index` idx 10: necessary
theorem w1c4_35 : ¬ drop0% DFinsupp.sum_add_index 10 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℕ∞) (f := DFinsupp.single () 1) (g := DFinsupp.single () (-1))
    (h := fun _ _ => ⊤) (by simp)
  simp [DFinsupp.sum, ← DFinsupp.single_add] at this

-- `DFinsupp.sum_add_index` idx 11: necessary
theorem w1c4_36 : ¬ drop0% DFinsupp.sum_add_index 11 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (f := DFinsupp.single () 1) (g := DFinsupp.single () 1)
    (h := fun _ b => b * b) (by simp)
  simp [DFinsupp.sum, ← DFinsupp.single_add] at this

-- `DFinsupp.prod_add_index` idx 10: necessary
theorem w1c4_37 : ¬ drop0% DFinsupp.prod_add_index 10 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℕ) (f := DFinsupp.single () 1) (g := DFinsupp.single () (-1))
    (h := fun _ _ => 0) (by simp)
  have e : (DFinsupp.single () (1:ℤ) + DFinsupp.single () (-1) : Π₀ _ : Unit, ℤ) = 0 := by ext; simp
  rw [e, DFinsupp.prod_zero_index] at this
  simp [DFinsupp.prod] at this

-- `DFinsupp.prod_add_index` idx 11: necessary
theorem w1c4_38 : ¬ drop0% DFinsupp.prod_add_index 11 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℕ) (γ := ℕ) (f := DFinsupp.single () 1) (g := DFinsupp.single () 1)
    (h := fun _ b => if b = 0 then 1 else 2) (by simp)
  simp [DFinsupp.prod, ← DFinsupp.single_add] at this

-- `DFinsupp.sum_eq_sum_fintype` idx 10: necessary
theorem w1c4_39 : ¬ drop0% DFinsupp.sum_eq_sum_fintype 10 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) 0 (f := fun _ _ => 1)
  simp [DFinsupp.sum, ← DFinsupp.single_add] at this

-- `DFinsupp.prod_eq_prod_fintype` idx 10: necessary
theorem w1c4_40 : ¬ drop0% DFinsupp.prod_eq_prod_fintype 10 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) 0 (f := fun _ _ => 2)
  simp [DFinsupp.prod, ← DFinsupp.single_add] at this

-- `DFinsupp.prod_eq_zero_iff` idx 6: necessary
theorem w1c4_41 : ¬ drop0% DFinsupp.prod_eq_zero_iff 6 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := Unit) (f := 0) (g := fun _ _ => ())
  simp at this

-- `DFinsupp.prod_eq_zero_iff` idx 7: necessary
theorem w1c4_42 : ¬ drop0% DFinsupp.prod_eq_zero_iff 7 := fun h => by
  have : Fact (1 < 4) := ⟨by decide⟩
  have := h (ι := Bool) (β := fun _ => ℤ) (γ := ZMod 4) (f := DFinsupp.single true 1 + DFinsupp.single false 1)
    (g := fun _ b => if b = 0 then 1 else 2)
  rw [DFinsupp.prod_eq_prod_fintype _ (by simp)] at this
  simp [Fintype.prod_bool] at this
  revert this; decide

-- `DFinsupp.prod_ne_zero_iff` idx 6: necessary
theorem w1c4_43 : ¬ drop0% DFinsupp.prod_ne_zero_iff 6 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := Unit) (f := 0) (g := fun _ _ => ())
  simp at this

-- `DFinsupp.prod_ne_zero_iff` idx 7: necessary
theorem w1c4_44 : ¬ drop0% DFinsupp.prod_ne_zero_iff 7 := fun h => by
  have : Fact (1 < 4) := ⟨by decide⟩
  have := h (ι := Bool) (β := fun _ => ℤ) (γ := ZMod 4) (f := DFinsupp.single true 1 + DFinsupp.single false 1)
    (g := fun _ b => if b = 0 then 1 else 2)
  rw [DFinsupp.prod_eq_prod_fintype _ (by simp)] at this
  simp [Fintype.prod_bool] at this
  revert this; decide

-- `DFinsupp.sum_sub_index` idx 10: necessary
theorem w1c4_45 : ¬ drop0% DFinsupp.sum_sub_index 10 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (f := 0) (g := DFinsupp.single () 1)
    (h := fun _ b => b * b)
  simp [DFinsupp.sum, ← DFinsupp.single_add] at this

-- `DFinsupp.sum_finsetSum_index` idx 11: necessary
theorem w1c4_46 : ¬ drop0% DFinsupp.sum_finsetSum_index 11 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℕ∞) (α := Bool) (s := Finset.univ)
    (g := fun b => if b then DFinsupp.single () 1 else DFinsupp.single () (-1)) (h := fun _ _ => ⊤) (by simp)
  simp [DFinsupp.sum, ← DFinsupp.single_add] at this

-- `DFinsupp.sum_finsetSum_index` idx 12: necessary
theorem w1c4_47 : ¬ drop0% DFinsupp.sum_finsetSum_index 12 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (α := Bool) (s := Finset.univ)
    (g := fun b => if b then DFinsupp.single () 1 else DFinsupp.single () 2) (h := fun _ b => b * b) (by simp)
  simp [DFinsupp.sum, Fintype.sum_bool, ← DFinsupp.single_add] at this

-- `DFinsupp.prod_finsetSum_index` idx 11: necessary
theorem w1c4_48 : ¬ drop0% DFinsupp.prod_finsetSum_index 11 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℕ) (α := Bool) (s := Finset.univ)
    (g := fun b => if b then DFinsupp.single () 1 else DFinsupp.single () (-1)) (h := fun _ _ => 0) (by simp)
  simp [DFinsupp.prod, ← DFinsupp.single_add] at this

-- `DFinsupp.prod_finsetSum_index` idx 12: necessary
theorem w1c4_49 : ¬ drop0% DFinsupp.prod_finsetSum_index 12 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℕ) (γ := ℕ) (α := Bool) (s := Finset.univ)
    (g := fun b => if b then DFinsupp.single () 1 else DFinsupp.single () 2)
    (h := fun _ b => if b = 0 then 1 else 2) (by simp)
  simp [DFinsupp.prod, Fintype.prod_bool, Fintype.sum_bool, ← DFinsupp.single_add] at this

-- `DFinsupp.sum_sum_index` idx 15: necessary
theorem w1c4_50 : ¬ drop0% DFinsupp.sum_sum_index 15 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℕ∞) (ι₁ := Bool) (β₁ := fun _ => ℤ)
    (f := DFinsupp.single true 1 + DFinsupp.single false 1)
    (g := fun i b => DFinsupp.single () (if i then b else -b)) (h := fun _ _ => ⊤) (by simp)
  rw [sumBool _ (fun i => by cases i <;> simp), sumBool _ (fun i => by cases i <;> simp [DFinsupp.sum_zero_index])] at this
  simp [← DFinsupp.single_add, DFinsupp.sum] at this

-- `DFinsupp.sum_sum_index` idx 16: necessary
theorem w1c4_51 : ¬ drop0% DFinsupp.sum_sum_index 16 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℕ) (γ := ℕ) (ι₁ := Bool) (β₁ := fun _ => ℕ)
    (f := DFinsupp.single true 1 + DFinsupp.single false 1)
    (g := fun i b => DFinsupp.single () b) (h := fun _ b => if b = 0 then 0 else 1) (by simp)
  simp [DFinsupp.sum_eq_sum_fintype, Fintype.sum_bool, ← DFinsupp.single_add] at this

-- `DFinsupp.prod_sum_index` idx 15: necessary
theorem w1c4_52 : ¬ drop0% DFinsupp.prod_sum_index 15 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℕ) (ι₁ := Bool) (β₁ := fun _ => ℤ)
    (f := DFinsupp.single true 1 + DFinsupp.single false 1)
    (g := fun i b => DFinsupp.single () (if i then b else -b)) (h := fun _ _ => 0) (by simp)
  rw [sumBool _ (fun i => by cases i <;> simp), prodBool _ (fun i => by cases i <;> simp [DFinsupp.prod_zero_index])] at this
  simp [← DFinsupp.single_add, DFinsupp.prod] at this

-- `DFinsupp.prod_sum_index` idx 16: necessary
theorem w1c4_53 : ¬ drop0% DFinsupp.prod_sum_index 16 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℕ) (γ := ℕ) (ι₁ := Bool) (β₁ := fun _ => ℕ)
    (f := DFinsupp.single true 1 + DFinsupp.single false 1)
    (g := fun i b => DFinsupp.single () b) (h := fun _ b => if b = 0 then 1 else 2) (by simp)
  simp [DFinsupp.sum_eq_sum_fintype, DFinsupp.prod_eq_prod_fintype, Fintype.sum_bool, Fintype.prod_bool, ← DFinsupp.single_add] at this

-- `DFinsupp.sum_subtypeDomain_index` idx 11: necessary
theorem w1c4_54 : ¬ drop0% DFinsupp.sum_subtypeDomain_index 11 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (v := DFinsupp.single () 1) (p := fun _ => False) (h := fun _ b => b)
  simp [DFinsupp.sum, Finset.eq_empty_of_isEmpty] at this

-- `DFinsupp.prod_subtypeDomain_index` idx 11: necessary
theorem w1c4_55 : ¬ drop0% DFinsupp.prod_subtypeDomain_index 11 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (v := DFinsupp.single () 2) (p := fun _ => False) (h := fun _ b => b)
  simp [DFinsupp.prod, Finset.eq_empty_of_isEmpty] at this

-- `DFinsupp.ext` idx 5: necessary
theorem w1c4_56 : ¬ drop0% DFinsupp.ext 5 := fun h => by
  have := congrArg (fun f => f ()) (h (ι := Unit) (β := fun _ => ℤ) (f := 0) (g := DFinsupp.single () 1))
  simp at this

-- `DFinsupp.mapRange_apply` idx 6: necessary
theorem w1c4_57 : ¬ indep0% DFinsupp.mapRange_apply 6 := fun h => by
  have := h (ι := Unit) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (fun _ _ => 1) 0 () ()
  simp at this

-- `DFinsupp.mapRange_comp` idx 10: necessary
theorem w1c4_58 : ¬ indep0% DFinsupp.mapRange_comp 10 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (fun _ _ => 0) (fun _ _ => 1)
    (fun _ => rfl) (fun _ => rfl) 0 ()
  simp at this

-- `DFinsupp.mapRange_zero` idx 6: necessary
theorem w1c4_59 : ¬ indep0% DFinsupp.mapRange_zero 6 := fun h => by
  have := h (ι := Unit) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (fun _ _ => 1) ()
  simp at this

-- `DFinsupp.zipWith_apply` idx 8: necessary
theorem w1c4_60 : ¬ indep0% DFinsupp.zipWith_apply 8 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (fun _ _ _ => 1) 0 0 () ()
  simp at this

-- `DFinsupp.instIsLeftCancelAdd` idx 3: necessary
theorem w1c4_61 : ¬ drop0% DFinsupp.instIsLeftCancelAdd 3 := fun h => by
  have := @h Unit (fun _ => ℕ∞) _
  have := add_left_cancel (a := DFinsupp.single (β := fun _ : Unit => ℕ∞) () ⊤) (b := 0) (c := DFinsupp.single () 1)
    (DFinsupp.ext fun i => by simp)
  have := DFunLike.congr_fun this ()
  simp at this

-- `DFinsupp.instIsRightCancelAdd` idx 3: necessary
theorem w1c4_62 : ¬ drop0% DFinsupp.instIsRightCancelAdd 3 := fun h => by
  have := @h Unit (fun _ => ℕ∞) _
  have := add_right_cancel (b := DFinsupp.single (β := fun _ : Unit => ℕ∞) () ⊤) (a := 0) (c := DFinsupp.single () 1)
    (DFinsupp.ext fun i => by simp)
  have := DFunLike.congr_fun this ()
  simp at this

-- `DFinsupp.filter_apply_pos` idx 7: necessary
theorem w1c4_63 : ¬ drop0% DFinsupp.filter_apply_pos 7 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (p := fun _ => False) (DFinsupp.single () 1) (i := ())
  simp at this

-- `DFinsupp.filter_apply_neg` idx 7: necessary
theorem w1c4_64 : ¬ drop0% DFinsupp.filter_apply_neg 7 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (p := fun _ => True) (DFinsupp.single () 1) (i := ())
  simp at this

-- `DFinsupp.mk_of_mem` idx 7: necessary
theorem w1c4_65 : ¬ indep0% DFinsupp.mk_of_mem 7 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (s := ∅) (x := fun _ => 0) (i := ())
  simp at this

-- `DFinsupp.mk_of_notMem` idx 7: necessary
theorem w1c4_66 : ¬ drop0% DFinsupp.mk_of_notMem 7 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (s := {()}) (x := fun _ => 1) (i := ())
  simp at this

-- `DFinsupp.single_left_injective` idx 5: necessary
theorem w1c4_67 : ¬ drop0% DFinsupp.single_left_injective 5 := fun h => by
  have hi := h (ι := Bool) (β := fun _ => ℤ) (b := fun _ => 0)
  have := @hi true false (by simp)
  simp at this

-- `DFinsupp.zipWith_single_single` idx 9: necessary
theorem w1c4_68 : ¬ indep0% DFinsupp.zipWith_single_single 9 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (fun _ _ _ => 1) (i := ()) 0 0 ()
  simp at this

-- `DFinsupp.erase_ne` idx 7: necessary
theorem w1c4_69 : ¬ drop0% DFinsupp.erase_ne 7 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (i := ()) (i' := ()) (f := DFinsupp.single () 1)
  simp at this

-- `DFinsupp.induction` idx 6: necessary
theorem w1c4_70 : ¬ drop0% DFinsupp.induction 6 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (p := fun _ => False) 0 (by simp)
  exact this

-- `DFinsupp.induction` idx 7: necessary
theorem w1c4_71 : ¬ drop0% DFinsupp.induction 7 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (p := fun f => f = 0) (DFinsupp.single () 1) rfl
  simp at this

-- `DFinsupp.induction₂` idx 6: necessary
theorem w1c4_72 : ¬ drop0% DFinsupp.induction₂ 6 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (p := fun _ => False) 0 (by simp)
  exact this

-- `DFinsupp.induction₂` idx 7: necessary
theorem w1c4_73 : ¬ drop0% DFinsupp.induction₂ 7 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (p := fun f => f = 0) (DFinsupp.single () 1) rfl
  simp at this

-- `DFinsupp.support_mk'_subset` idx 7: necessary
theorem w1c4_74 : ¬ indep0% DFinsupp.support_mk'_subset 7 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (f := fun _ => 1) (s := 0) ()
  simp at this

-- `DFinsupp.mapRange_def` idx 8: necessary
theorem w1c4_75 : ¬ indep0% DFinsupp.mapRange_def 8 := fun h => by
  have := h (ι := Unit) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (f := fun _ _ => 1) (g := 0) ()
  simp at this

-- `DFinsupp.mapRange_single` idx 7: necessary
theorem w1c4_76 : ¬ indep0% DFinsupp.mapRange_single 7 := fun h => by
  have := h (ι := Unit) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (f := fun _ _ => 1) (i := ()) (b := 0) ()
  simp at this

-- `DFinsupp.mapRange_injective` idx 6: necessary
theorem w1c4_77 : ¬ indep0% DFinsupp.mapRange_injective 6 := fun h => by
  have := h (ι := Unit) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (fun _ _ => 1) ()
  simp at this

-- `DFinsupp.mapRange_surjective` idx 6: necessary
theorem w1c4_78 : ¬ indep0% DFinsupp.mapRange_surjective 6 := fun h => by
  have := h (ι := Unit) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (fun _ _ => 1) ()
  simp at this

-- `DFinsupp.support_mapRange` idx 9: necessary
theorem w1c4_79 : ¬ indep0% DFinsupp.support_mapRange 9 := fun h => by
  have := h (ι := Unit) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (f := fun _ _ => 1) (g := 0) ()
  simp at this

-- `DFinsupp.zipWith_def` idx 11: necessary
theorem w1c4_80 : ¬ indep0% DFinsupp.zipWith_def 11 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (f := fun _ _ _ => 1) (g₁ := 0) (g₂ := 0) ()
  simp at this

-- `DFinsupp.support_zipWith` idx 12: necessary
theorem w1c4_81 : ¬ indep0% DFinsupp.support_zipWith 12 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (f := fun _ _ _ => 1) (g₁ := 0) (g₂ := 0) ()
  simp at this

-- `DFinsupp.mapRange_add` idx 6: necessary
theorem w1c4_82 : ¬ indep0% DFinsupp.mapRange_add 6 := fun h => by
  have := h (ι := Unit) (β₁ := fun _ => ℕ∞) (β₂ := fun _ => ℕ∞) (fun _ _ => ⊤) (fun _ _ _ => by simp) 0 0 ()
  simp at this

-- `DFinsupp.mapRange_add` idx 7: necessary
theorem w1c4_83 : ¬ drop0% DFinsupp.mapRange_add 7 := fun h => by
  have := congrArg (fun f => f ()) (h (ι := Unit) (β₁ := fun _ => ℤ) (β₂ := fun _ => ℤ) (f := fun _ b => b * b)
    (fun _ => rfl) (DFinsupp.single () 1) (DFinsupp.single () 1))
  simp at this

-- `instCountableDFinsupp` idx 3: necessary
theorem w1c4_84 : ¬ drop0% instCountableDFinsupp 3 := fun h => by
  have := h (ι := ℝ) (α := fun _ => ℕ)
  have hc : Countable ℝ := Function.Injective.countable (f := fun r : ℝ => DFinsupp.single r (1:ℕ))
    (fun a b e => DFinsupp.single_left_injective (β := fun _ : ℝ => ℕ) (b := fun _ => 1) (by simp) e)
  exact Cardinal.not_countable_real Set.countable_univ

-- `instCountableDFinsupp` idx 4: necessary
theorem w1c4_85 : ¬ drop0% instCountableDFinsupp 4 := fun h => by
  have := h (ι := Unit) (α := fun _ => ℝ)
  have hc : Countable ℝ := Function.Injective.countable (f := fun r : ℝ => (DFinsupp.single () r : Π₀ _ : Unit, ℝ))
    (fun a b e => by simpa using DFunLike.congr_fun e ())
  exact Cardinal.not_countable_real Set.countable_univ

-- `DFinsupp.addHom_ext` idx 8: necessary
theorem w1c4_86 : ¬ drop0% DFinsupp.addHom_ext 8 := fun h => by
  have := congrArg (fun F => F (DFinsupp.single () 1) ()) (h (ι := Unit) (β := fun _ => ℤ) (γ := Π₀ _ : Unit, ℤ)
    (f := AddMonoidHom.id _) (g := 0))
  simp at this

-- `DFinsupp.addHom_ext'` idx 8: necessary
theorem w1c4_87 : ¬ drop0% DFinsupp.addHom_ext' 8 := fun h => by
  have := congrArg (fun F => F (DFinsupp.single () 1) ()) (@h Unit (fun _ => ℤ) _ _ (Π₀ _ : Unit, ℤ) _
    (AddMonoidHom.id _) 0)
  simp at this

-- `DFinsupp.infinite_of_left` idx 2: necessary
theorem w1c4_88 : ¬ drop0% DFinsupp.infinite_of_left 2 := fun h => by
  have := h (ι := ℕ) (π := fun _ => Unit)
  exact (not_finite_iff_infinite.2 this) inferInstance

-- `DFinsupp.infinite_of_left` idx 4: necessary
theorem w1c4_89 : ¬ drop0% DFinsupp.infinite_of_left 4 := fun h => by
  have := h (ι := Unit) (π := fun _ => Fin 2)
  exact (not_finite_iff_infinite.2 this) (Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm)

-- `DFinsupp.infinite_of_exists_right` idx 3: necessary
theorem w1c4_90 : ¬ drop0% DFinsupp.infinite_of_exists_right 3 := fun h => by
  have := h (ι := Unit) (π := fun _ => Fin 2) ()
  exact (not_finite_iff_infinite.2 this) (Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm)

-- `DFinsupp.infinite_of_right` idx 2: necessary
theorem w1c4_91 : ¬ drop0% DFinsupp.infinite_of_right 2 := fun h => by
  have := h (ι := Unit) (π := fun _ => Fin 2)
  exact (not_finite_iff_infinite.2 this) (Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm)

-- `DFinsupp.infinite_of_right` idx 4: necessary
theorem w1c4_92 : ¬ drop0% DFinsupp.infinite_of_right 4 := fun h => by
  have := h (ι := Empty) (π := fun _ => ℕ)
  exact (not_finite_iff_infinite.2 this) inferInstance

-- `DFinsupp.card_Iic` idx 6: necessary
theorem w1c4_93 : ¬ indep0% DFinsupp.card_Iic 6 := fun h => by
  have := (h (ι := Unit) (α := fun _ => WithBot ℕ) 0 ()).isBot_zero ⊥
  simp at this

-- `DFinsupp.card_Iio` idx 6: necessary
theorem w1c4_94 : ¬ indep0% DFinsupp.card_Iio 6 := fun h => by
  have := (h (ι := Unit) (α := fun _ => WithBot ℕ) 0 ()).isBot_zero ⊥
  simp at this

-- `DFinsupp.lex_lt_of_lt_of_preorder` idx 5: necessary
theorem w1c4_95 : ¬ drop0% DFinsupp.lex_lt_of_lt_of_preorder 5 := fun h => by
  obtain ⟨i, h1, h2⟩ := h (ι := Unit) (α := fun _ => ℕ) (fun _ _ => True) (x := 0) (y := DFinsupp.single () 1)
    (by rw [DFinsupp.lt_def]; refine ⟨fun _ => by simp, (), by simp⟩)
  exact absurd (h1 i trivial).2 (not_le.2 h2)

-- `DFinsupp.lex_lt_of_lt` idx 5: necessary
theorem w1c4_96 : ¬ drop0% DFinsupp.lex_lt_of_lt 5 := fun h => by
  obtain ⟨i, h1, h2⟩ := h (ι := Unit) (α := fun _ => ℕ) (fun _ _ => True) (x := 0) (y := DFinsupp.single () 1)
    (by rw [DFinsupp.lt_def]; refine ⟨fun _ => by simp, (), by simp⟩)
  exact absurd (h1 i trivial) (ne_of_lt h2)

-- `DFinsupp.lex_iff_of_unique` idx 6: necessary
theorem w1c4_97 : ¬ drop0% DFinsupp.lex_iff_of_unique 6 := fun h => by
  have := (h (ι := Unit) (α := fun _ => ℕ) (r := fun _ _ => True) (x := 0) (y := DFinsupp.single () 1)).2 (by simp)
  obtain ⟨i, h1, h2⟩ := this
  exact absurd (h1 i trivial) (ne_of_lt h2)

-- `DFinsupp.Lex.addLeftStrictMono` idx 5: necessary
theorem w1c4_98 : ¬ drop0% DFinsupp.Lex.addLeftStrictMono 5 := fun h => by
  have := h (ι := Unit) (α := fun _ => Fin 3)
  have h12 : toLex (DFinsupp.single (β := fun _ : Unit => Fin 3) () 1) < toLex (DFinsupp.single () 2) := by
    rw [DFinsupp.Lex.lt_iff_of_unique]; simp
  have := add_lt_add_left h12 (toLex (DFinsupp.single () (1 : Fin 3)))
  rw [DFinsupp.Lex.lt_iff_of_unique] at this
  revert this; simp

-- `DFinsupp.Colex.addLeftStrictMono` idx 5: necessary
theorem w1c4_99 : ¬ drop0% DFinsupp.Colex.addLeftStrictMono 5 := fun h => by
  have := h (ι := Unit) (α := fun _ => Fin 3)
  have h12 : toColex (DFinsupp.single (β := fun _ : Unit => Fin 3) () 1) < toColex (DFinsupp.single () 2) := by
    rw [DFinsupp.colex_lt_iff_of_unique]; simp
  have := add_lt_add_left h12 (toColex (DFinsupp.single () (1 : Fin 3)))
  rw [DFinsupp.colex_lt_iff_of_unique] at this
  revert this; simp

-- `DFinsupp.Lex.addLeftMono` idx 5: necessary
theorem w1c4_100 : ¬ drop0% DFinsupp.Lex.addLeftMono 5 := fun h => by
  have := h (ι := Unit) (α := fun _ => Fin 3)
  have h12 : toLex (DFinsupp.single (β := fun _ : Unit => Fin 3) () 1) ≤ toLex (DFinsupp.single () 2) := by
    rw [DFinsupp.Lex.le_iff_of_unique]; simp
  have := add_le_add_left h12 (toLex (DFinsupp.single () (1 : Fin 3)))
  rw [DFinsupp.Lex.le_iff_of_unique] at this
  revert this; simp

-- `DFinsupp.Colex.addLeftMono` idx 5: necessary
theorem w1c4_101 : ¬ drop0% DFinsupp.Colex.addLeftMono 5 := fun h => by
  have := h (ι := Unit) (α := fun _ => Fin 3)
  have h12 : toColex (DFinsupp.single (β := fun _ : Unit => Fin 3) () 1) ≤ toColex (DFinsupp.single () 2) := by
    rw [DFinsupp.Colex.le_iff_of_unique]; simp
  have := add_le_add_left h12 (toColex (DFinsupp.single () (1 : Fin 3)))
  rw [DFinsupp.Colex.le_iff_of_unique] at this
  revert this; simp

-- `DFinsupp.Lex.addRightStrictMono` idx 5: necessary
theorem w1c4_102 : ¬ drop0% DFinsupp.Lex.addRightStrictMono 5 := fun h => by
  have := h (ι := Unit) (α := fun _ => Fin 3)
  have h12 : toLex (DFinsupp.single (β := fun _ : Unit => Fin 3) () 1) < toLex (DFinsupp.single () 2) := by
    rw [DFinsupp.Lex.lt_iff_of_unique]; simp
  have := this.elim (toLex (DFinsupp.single () (1 : Fin 3))) h12
  simp only [Function.swap] at this
  rw [DFinsupp.Lex.lt_iff_of_unique] at this
  revert this; simp

-- `DFinsupp.Colex.addRightStrictMono` idx 5: necessary
theorem w1c4_103 : ¬ drop0% DFinsupp.Colex.addRightStrictMono 5 := fun h => by
  have := h (ι := Unit) (α := fun _ => Fin 3)
  have h12 : toColex (DFinsupp.single (β := fun _ : Unit => Fin 3) () 1) < toColex (DFinsupp.single () 2) := by
    rw [DFinsupp.colex_lt_iff_of_unique]; simp
  have := this.elim (toColex (DFinsupp.single () (1 : Fin 3))) h12
  simp only [Function.swap] at this
  rw [DFinsupp.colex_lt_iff_of_unique] at this
  revert this; simp

-- `DFinsupp.Lex.addRightMono` idx 5: necessary
theorem w1c4_104 : ¬ drop0% DFinsupp.Lex.addRightMono 5 := fun h => by
  have := h (ι := Unit) (α := fun _ => Fin 3)
  have h12 : toLex (DFinsupp.single (β := fun _ : Unit => Fin 3) () 1) ≤ toLex (DFinsupp.single () 2) := by
    rw [DFinsupp.Lex.le_iff_of_unique]; simp
  have := this.elim (toLex (DFinsupp.single () (1 : Fin 3))) h12
  simp only [Function.swap] at this
  rw [DFinsupp.Lex.le_iff_of_unique] at this
  revert this; simp

-- `DFinsupp.Colex.addRightMono` idx 5: necessary
theorem w1c4_105 : ¬ drop0% DFinsupp.Colex.addRightMono 5 := fun h => by
  have := h (ι := Unit) (α := fun _ => Fin 3)
  have h12 : toColex (DFinsupp.single (β := fun _ : Unit => Fin 3) () 1) ≤ toColex (DFinsupp.single () 2) := by
    rw [DFinsupp.Colex.le_iff_of_unique]; simp
  have := this.elim (toColex (DFinsupp.single () (1 : Fin 3))) h12
  simp only [Function.swap] at this
  rw [DFinsupp.Colex.le_iff_of_unique] at this
  revert this; simp

-- `DFinsupp.Lex.isBotZeroClass` idx 5: necessary
theorem w1c4_106 : ¬ drop0% DFinsupp.Lex.isBotZeroClass 5 := fun h => by
  have := h (ι := Unit) (α := fun _ => ℤ)
  have h1 : toLex (DFinsupp.single (β := fun _ : Unit => ℤ) () (-1)) < 0 := by
    rw [DFinsupp.Lex.lt_iff_of_unique]; simp
  exact lt_irrefl _ (lt_of_lt_of_le h1 (this.isBot_zero _))

-- `DFinsupp.Colex.isOrderedCancelAddMonoid` idx 5: necessary
theorem w1c4_107 : ¬ drop0% DFinsupp.Colex.isOrderedCancelAddMonoid 5 := fun h => by
  have := h (ι := Unit) (α := fun _ => Fin 3)
  have h12 : toColex (DFinsupp.single (β := fun _ : Unit => Fin 3) () 1) ≤ toColex (DFinsupp.single () 2) := by
    rw [DFinsupp.Colex.le_iff_of_unique]; simp
  have := add_le_add_left h12 (toColex (DFinsupp.single () (1 : Fin 3)))
  rw [DFinsupp.Colex.le_iff_of_unique] at this
  revert this; simp

-- `DFinsupp.Lex.isOrderedAddMonoid` idx 5: necessary
theorem w1c4_108 : ¬ drop0% DFinsupp.Lex.isOrderedAddMonoid 5 := fun h => by
  have := h (ι := Unit) (α := fun _ => Fin 3)
  have h12 : toLex (DFinsupp.single (β := fun _ : Unit => Fin 3) () 1) ≤ toLex (DFinsupp.single () 2) := by
    rw [DFinsupp.Lex.le_iff_of_unique]; simp
  have := add_le_add_left h12 (toLex (DFinsupp.single () (1 : Fin 3)))
  rw [DFinsupp.Lex.le_iff_of_unique] at this
  revert this; simp

-- `DFinsupp.Colex.isOrderedAddMonoid` idx 5: necessary
theorem w1c4_109 : ¬ drop0% DFinsupp.Colex.isOrderedAddMonoid 5 := fun h => by
  have := h (ι := Unit) (α := fun _ => Fin 3)
  have h12 : toColex (DFinsupp.single (β := fun _ : Unit => Fin 3) () 1) ≤ toColex (DFinsupp.single () 2) := by
    rw [DFinsupp.Colex.le_iff_of_unique]; simp
  have := add_le_add_left h12 (toColex (DFinsupp.single () (1 : Fin 3)))
  rw [DFinsupp.Colex.le_iff_of_unique] at this
  revert this; simp

-- `DFinsupp.smulCommClass` idx 7: necessary
theorem w1c4_110 : ¬ drop0% DFinsupp.smulCommClass 7 := fun h => by
  have := h (ι := Unit) (β := fun _ => Matrix (Fin 2) (Fin 2) ℕ) (γ := Matrix (Fin 2) (Fin 2) ℕ)
    (δ := Matrix (Fin 2) (Fin 2) ℕ)
  have e := congrArg (fun f => f () 0 0) (smul_comm (!![1,1;0,1] : Matrix (Fin 2) (Fin 2) ℕ) !![1,0;1,1]
    (DFinsupp.single (β := fun _ : Unit => Matrix (Fin 2) (Fin 2) ℕ) () 1))
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e

-- `DFinsupp.isScalarTower` idx 8: necessary
theorem w1c4_111 : ¬ drop0% DFinsupp.isScalarTower 8 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℕ) (γ := ℕ) (δ := TN)
  have e := congrArg (fun f => f ()) (smul_assoc (2:ℕ) (show TN from (1:ℕ)) (DFinsupp.single (β := fun _ : Unit => ℕ) () 1))
  simp only [DFinsupp.smul_apply, DFinsupp.single_eq_same] at e
  change (1:ℕ) * 1 = 2 * (1 * 1) at e
  omega

-- `DFinsupp.isCentralScalar` idx 6: necessary
theorem w1c4_112 : ¬ drop0% DFinsupp.isCentralScalar 6 := fun h => by
  have := h (ι := Unit) (β := fun _ => TZ) (γ := ℕ)
  have e := congrArg (fun f => f ()) (op_smul_eq_smul (2:ℕ) (DFinsupp.single (β := fun _ : Unit => TZ) () (show TZ from (1:ℕ))))
  simp only [DFinsupp.smul_apply] at e
  change (1:ℕ) = 2 * 1 at e
  omega

-- `DFinsupp.subset_mapRange_neLocus` idx 11: necessary
theorem w1c4_113 : ¬ indep0% DFinsupp.subset_mapRange_neLocus 11 := fun h => by
  have := h (α := Unit) (N := fun _ => ℤ) (M := fun _ => ℤ) 0 0 (F := fun _ _ => 1) ()
  simp at this

-- `DFinsupp.zipWith_neLocus_eq_left` idx 11: necessary
theorem w1c4_114 : ¬ indep0% DFinsupp.zipWith_neLocus_eq_left 11 := fun h => by
  have := h (α := Unit) (N := fun _ => ℤ) (M := fun _ => ℤ) (P := fun _ => ℤ) (F := fun _ _ g => g + 1) 0 0 0
    (fun _ _ a b e => by simpa using e) ()
  simp at this

-- `DFinsupp.zipWith_neLocus_eq_left` idx 15: necessary
theorem w1c4_115 : ¬ drop0% DFinsupp.zipWith_neLocus_eq_left 15 := fun h => by
  have := h (α := Unit) (N := fun _ => ℤ) (M := fun _ => ℤ) (P := fun _ => ℤ) (F := fun _ _ _ => 0) (fun _ => rfl)
    0 0 (DFinsupp.single () 1)
  have := congrArg (fun s => () ∈ s) this
  simp at this

-- `DFinsupp.zipWith_neLocus_eq_right` idx 11: necessary
theorem w1c4_116 : ¬ indep0% DFinsupp.zipWith_neLocus_eq_right 11 := fun h => by
  have := h (α := Unit) (N := fun _ => ℤ) (M := fun _ => ℤ) (P := fun _ => ℤ) (F := fun _ f _ => f + 1) 0 0 0
    (fun _ _ a b e => by simpa using e) ()
  simp at this

-- `DFinsupp.zipWith_neLocus_eq_right` idx 15: necessary
theorem w1c4_117 : ¬ drop0% DFinsupp.zipWith_neLocus_eq_right 15 := fun h => by
  have := h (α := Unit) (N := fun _ => ℤ) (M := fun _ => ℤ) (P := fun _ => ℤ) (F := fun _ _ _ => 0) (fun _ => rfl)
    0 (DFinsupp.single () 1) 0
  have := congrArg (fun s => () ∈ s) this
  simp at this

-- `DFinsupp.mapRange_neLocus_eq` idx 11: necessary
theorem w1c4_118 : ¬ indep0% DFinsupp.mapRange_neLocus_eq 11 := fun h => by
  have := h (α := Unit) (N := fun _ => ℤ) (M := fun _ => ℤ) 0 0 (F := fun _ g => g + 1)
    (fun _ a b e => by simpa using e) ()
  simp at this

-- `DFinsupp.mapRange_neLocus_eq` idx 12: necessary
theorem w1c4_119 : ¬ drop0% DFinsupp.mapRange_neLocus_eq 12 := fun h => by
  have := h (α := Unit) (N := fun _ => ℤ) (M := fun _ => ℤ) 0 (DFinsupp.single () 1) (F := fun _ _ => 0) (fun _ => rfl)
  have := congrArg (fun s => () ∈ s) this
  simp at this

-- `DFinsupp.instIsOrderedAddMonoid` idx 4: necessary
theorem w1c4_120 : ¬ drop0% DFinsupp.instIsOrderedAddMonoid 4 := fun h => by
  have := h (ι := Unit) (fun _ => Fin 3)
  have h12 : DFinsupp.single (β := fun _ : Unit => Fin 3) () 1 ≤ DFinsupp.single () 2 := fun _ => by simp
  have := add_le_add_left h12 (DFinsupp.single () (1 : Fin 3)) ()
  revert this; simp

-- `DFinsupp.instIsOrderedCancelAddMonoid` idx 4: necessary
theorem w1c4_121 : ¬ drop0% DFinsupp.instIsOrderedCancelAddMonoid 4 := fun h => by
  have := h (ι := Unit) (fun _ => Fin 3)
  have h12 : DFinsupp.single (β := fun _ : Unit => Fin 3) () 1 ≤ DFinsupp.single () 2 := fun _ => by simp
  have := add_le_add_left h12 (DFinsupp.single () (1 : Fin 3)) ()
  revert this; simp

-- `DFinsupp.instAddLeftReflectLE` idx 4: necessary
theorem w1c4_122 : ¬ drop0% DFinsupp.instAddLeftReflectLE 4 := fun h => by
  have := h (ι := Unit) (α := fun _ => Fin 3)
  have h12 : DFinsupp.single (β := fun _ : Unit => Fin 3) () 1 + DFinsupp.single () 2 ≤
      DFinsupp.single () 1 + DFinsupp.single () 0 := fun _ => by simp
  have := le_of_add_le_add_left h12 ()
  revert this; simp

-- `DFinsupp.instPosSMulMono` idx 8: necessary
theorem w1c4_123 : ¬ drop0% DFinsupp.instPosSMulMono 8 := fun h => by
  have := h (ι := Unit) (α := ℕ) (β := fun _ => Fin 3)
  have := smul_le_smul_of_nonneg_left (a := (2:ℕ)) (show DFinsupp.single (β := fun _ : Unit => Fin 3) () 1 ≤ DFinsupp.single () 2 from fun _ => by simp) (by simp) ()
  revert this; first | (simp; done) | (simp; decide) | decide

-- `DFinsupp.instSMulPosMono` idx 8: necessary
theorem w1c4_124 : ¬ drop0% DFinsupp.instSMulPosMono 8 := fun h => by
  have := h (ι := Unit) (α := ℕ) (β := fun _ => Fin 3)
  have := smul_le_smul_of_nonneg_right (b := DFinsupp.single (β := fun _ : Unit => Fin 3) () 2) (show (1:ℕ) ≤ 2 by decide) (fun _ => by simp) ()
  revert this; first | (simp; done) | (simp; decide) | decide

-- `DFinsupp.instPosSMulReflectLE` idx 8: necessary
theorem w1c4_125 : ¬ drop0% DFinsupp.instPosSMulReflectLE 8 := fun h => by
  have := h (ι := Unit) (α := ℕ) (β := fun _ => Fin 3)
  have := le_of_smul_le_smul_left (a := (2:ℕ)) (b₁ := DFinsupp.single (β := fun _ : Unit => Fin 3) () 2) (b₂ := DFinsupp.single () 1)
    (fun i => by cases i; simp; decide) (by decide) ()
  revert this; first | (simp; done) | (simp; decide) | decide

-- `DFinsupp.instSMulPosReflectLE` idx 8: necessary
theorem w1c4_126 : ¬ drop0% DFinsupp.instSMulPosReflectLE 8 := fun h => by
  have := h (ι := Unit) (α := ℕ) (β := fun _ => Fin 3)
  have := le_of_smul_le_smul_right (a₁ := (3:ℕ)) (a₂ := 0) (b := DFinsupp.single (β := fun _ : Unit => Fin 3) () 1)
    (fun i => by cases i; simp; decide) (by rw [DFinsupp.lt_def]; exact ⟨fun _ => by simp, (), by simp⟩)
  revert this; decide

-- `DFinsupp.instPosSMulStrictMono` idx 8: necessary
theorem w1c4_127 : ¬ drop0% DFinsupp.instPosSMulStrictMono 8 := fun h => by
  have := h (ι := Unit) (α := ℕ) (β := fun _ => Fin 3)
  have := smul_lt_smul_of_pos_left (a := (2:ℕ)) (show DFinsupp.single (β := fun _ : Unit => Fin 3) () 1 < DFinsupp.single () 2 by
    rw [DFinsupp.lt_def]; exact ⟨fun _ => by simp, (), by simp⟩) (by decide)
  rw [DFinsupp.lt_def] at this
  have := this.1 ()
  revert this; first | (simp; done) | (simp; decide) | decide

-- `DFinsupp.instSMulPosStrictMono` idx 8: necessary
theorem w1c4_128 : ¬ drop0% DFinsupp.instSMulPosStrictMono 8 := fun h => by
  have := h (ι := Unit) (α := ℕ) (β := fun _ => Fin 3)
  have := smul_lt_smul_of_pos_right (a₁ := (0:ℕ)) (a₂ := 3) (b := DFinsupp.single (β := fun _ : Unit => Fin 3) () 1) (by decide)
    (by rw [DFinsupp.lt_def]; exact ⟨fun _ => by simp, (), by simp⟩)
  rw [DFinsupp.lt_def] at this
  obtain ⟨_, i, hi⟩ := this
  revert hi; simp; decide

-- `DFinsupp.instSMulPosReflectLT` idx 8: necessary
theorem w1c4_129 : ¬ drop0% DFinsupp.instSMulPosReflectLT 8 := fun h => by
  have := h (ι := Unit) (α := ℕ) (β := fun _ => Fin 3)
  have := lt_of_smul_lt_smul_right (a₁ := (3:ℕ)) (a₂ := 1) (b := DFinsupp.single (β := fun _ : Unit => Fin 3) () 1)
    (by rw [DFinsupp.lt_def]; exact ⟨fun i => by cases i; simp; decide, (), by simp; decide⟩) (fun _ => by simp)
  revert this; decide

-- `DFinsupp.instIsBotZeroClass` idx 4: necessary
theorem w1c4_130 : ¬ drop0% DFinsupp.instIsBotZeroClass 4 := fun h => by
  have := (h (ι := Unit) (fun _ => ℤ)).isBot_zero (DFinsupp.single () (-1)) ()
  revert this; simp

-- `DFinsupp.bot_eq_zero` idx 4: necessary
theorem w1c4_131 : ¬ indep0% DFinsupp.bot_eq_zero 4 := fun h => by
  have := (h (ι := Unit) (α := fun _ => ℤ) ()).isBot_zero (-1)
  revert this; simp

-- `DFinsupp.add_eq_zero_iff` idx 4: necessary
theorem w1c4_132 : ¬ drop0% DFinsupp.add_eq_zero_iff 4 := fun h => by
  have := ((h (ι := Unit) (α := fun _ => ℤ) (DFinsupp.single () 1) (DFinsupp.single () (-1))).1
    (by ext; simp)).1
  have := congrArg (fun f => f ()) this
  simp at this

-- `DFinsupp.le_iff'` idx 4: necessary
theorem w1c4_133 : ¬ drop0% DFinsupp.le_iff' 4 := fun h => by
  have := (h (ι := Unit) (α := fun _ => ℤ) (f := 0) (g := DFinsupp.single () (-1)) (s := ∅) (by simp)).2 (by simp) ()
  revert this; simp

-- `DFinsupp.le_iff'` idx 10: necessary
theorem w1c4_134 : ¬ drop0% DFinsupp.le_iff' 10 := fun h => by
  have := (h (ι := Unit) (α := fun _ => ℕ) (f := DFinsupp.single () 1) (g := 0) (s := ∅)).2 (by simp) ()
  revert this; simp

-- `DFinsupp.le_iff` idx 4: necessary
theorem w1c4_135 : ¬ drop0% DFinsupp.le_iff 4 := fun h => by
  have := (h (ι := Unit) (α := fun _ => ℤ) (f := 0) (g := DFinsupp.single () (-1))).2 (by simp) ()
  revert this; simp

-- `DFinsupp.support_monotone` idx 4: necessary
theorem w1c4_136 : ¬ drop0% DFinsupp.support_monotone 4 := fun h => by
  have := h (ι := Unit) (α := fun _ => ℤ) (a := DFinsupp.single () (-1)) (b := 0) (fun _ => by simp)
  simp at this

-- `DFinsupp.support_mono` idx 4: necessary
theorem w1c4_137 : ¬ drop0% DFinsupp.support_mono 4 := fun h => by
  have := h (ι := Unit) (α := fun _ => ℤ) (f := DFinsupp.single () (-1)) (g := 0) (fun _ => by simp)
  simp at this

-- `DFinsupp.support_mono` idx 9: necessary
theorem w1c4_138 : ¬ drop0% DFinsupp.support_mono 9 := fun h => by
  have := h (ι := Unit) (α := fun _ => ℕ) (f := DFinsupp.single () 1) (g := 0)
  simp at this

-- `DFinsupp.single_le_iff` idx 4: necessary
theorem w1c4_139 : ¬ drop0% DFinsupp.single_le_iff 4 := fun h => by
  have := (h (ι := Bool) (α := fun _ => ℤ) (f := DFinsupp.single false (-1)) (i := true) (a := 0)).2 (by simp) false
  revert this; simp

-- `DFinsupp.tsub_apply` idx 4: necessary
theorem w1c4_140 : ¬ indep0% DFinsupp.tsub_apply 4 := fun h => by
  have := (h (ι := Unit) (α := fun _ => ℤ) 0 0 () ()).le_self_add 0 (-1)
  revert this; simp

-- `DFinsupp.tsub_apply` idx 6: necessary
theorem w1c4_141 : ¬ indep0% DFinsupp.tsub_apply 6 := fun h => ns_not_orderedSub (h (ι := Unit) (α := fun _ => NS) 0 0 () ())

-- `DFinsupp.coe_tsub` idx 4: necessary
theorem w1c4_142 : ¬ indep0% DFinsupp.coe_tsub 4 := fun h => by
  have := (h (ι := Unit) (α := fun _ => ℤ) 0 0 ()).le_self_add 0 (-1)
  revert this; simp

-- `DFinsupp.coe_tsub` idx 6: necessary
theorem w1c4_143 : ¬ indep0% DFinsupp.coe_tsub 6 := fun h => ns_not_orderedSub (h (ι := Unit) (α := fun _ => NS) 0 0 ())

-- `DFinsupp.instOrderedSub` idx 4: necessary
theorem w1c4_144 : ¬ indep0% DFinsupp.instOrderedSub 4 := fun h => by
  have := (h (ι := Unit) (fun _ => ℤ) ()).le_self_add 0 (-1)
  revert this; simp

-- `DFinsupp.instOrderedSub` idx 6: necessary
theorem w1c4_145 : ¬ indep0% DFinsupp.instOrderedSub 6 := fun h => ns_not_orderedSub (h (ι := Unit) (fun _ => NS) ())

-- `DFinsupp.instCanonicallyOrderedAddOfAddLeftMono` idx 4: necessary
theorem w1c4_146 : ¬ drop0% DFinsupp.instCanonicallyOrderedAddOfAddLeftMono 4 := fun h => by
  have := (h (ι := Unit) (fun _ => ℤ)).le_self_add 0 (DFinsupp.single () (-1)) ()
  revert this; simp

-- `DFinsupp.instCanonicallyOrderedAddOfAddLeftMono` idx 6: removable
theorem w1c4_147 : drop% DFinsupp.instCanonicallyOrderedAddOfAddLeftMono 6 := by
  intro ι α _ _ _ _ _
  classical
  exact {
    exists_add_of_le := by
      intro f g hfg
      choose c hc using fun i => exists_add_of_le (hfg i)
      refine ⟨DFinsupp.mk g.support (fun i => c i), ?_⟩
      ext i
      by_cases hi : i ∈ g.support
      · rw [DFinsupp.add_apply, DFinsupp.mk_of_mem hi]; exact hc i
      · rw [DFinsupp.add_apply, DFinsupp.mk_of_notMem hi, add_zero]
        have h0 : g i = 0 := DFinsupp.notMem_support_iff.1 hi
        rw [h0]; exact (le_antisymm (h0 ▸ hfg i) zero_le).symm
    le_add_self := fun _ _ _ => le_add_self
    le_self_add := fun _ _ _ => le_self_add }

-- `DFinsupp.single_tsub` idx 4: necessary
theorem w1c4_148 : ¬ indep0% DFinsupp.single_tsub 4 := fun h => by
  have := (h (ι := Unit) (α := fun _ => ℤ) (i := ()) (a := 0) (b := 0) ()).le_self_add 0 (-1)
  revert this; simp

-- `DFinsupp.single_tsub` idx 6: necessary
theorem w1c4_149 : ¬ indep0% DFinsupp.single_tsub 6 := fun h => ns_not_orderedSub (h (ι := Unit) (α := fun _ => NS) (i := ()) (a := 0) (b := 0) ())

-- `DFinsupp.support_tsub` idx 4: necessary
theorem w1c4_150 : ¬ indep0% DFinsupp.support_tsub 4 := fun h => by
  have := (h (ι := Unit) (α := fun _ => ℤ) (f := 0) (g := 0) ()).le_self_add 0 (-1)
  revert this; simp

-- `DFinsupp.support_tsub` idx 6: necessary
theorem w1c4_151 : ¬ indep0% DFinsupp.support_tsub 6 := fun h => ns_not_orderedSub (h (ι := Unit) (α := fun _ => NS) (f := 0) (g := 0) ())

-- `DFinsupp.subset_support_tsub` idx 4: necessary
theorem w1c4_152 : ¬ indep0% DFinsupp.subset_support_tsub 4 := fun h => by
  have := (h (ι := Unit) (α := fun _ => ℤ) (f := 0) (g := 0) ()).le_self_add 0 (-1)
  revert this; simp

-- `DFinsupp.subset_support_tsub` idx 6: necessary
theorem w1c4_153 : ¬ indep0% DFinsupp.subset_support_tsub 6 := fun h => ns_not_orderedSub (h (ι := Unit) (α := fun _ => NS) (f := 0) (g := 0) ())

-- `DFinsupp.support_inf` idx 4: necessary
theorem w1c4_154 : ¬ drop0% DFinsupp.support_inf 4 := fun h => by
  have := congrArg (fun s => () ∈ s) (h (ι := Unit) (α := fun _ => ℤ) (f := DFinsupp.single () (-1)) (g := 0))
  simp at this

-- `DFinsupp.support_sup` idx 4: necessary
theorem w1c4_155 : ¬ drop0% DFinsupp.support_sup 4 := fun h => by
  have := congrArg (fun s => () ∈ s) (h (ι := Unit) (α := fun _ => ℤ) (f := DFinsupp.single () (-1)) (g := 0))
  simp at this

-- `DFinsupp.disjoint_iff` idx 4: necessary
theorem w1c4_156 : ¬ indep0% DFinsupp.disjoint_iff 4 := fun h => by
  have := (h (ι := Unit) (α := fun _ => ℤ) (f := 0) (g := 0) ()).isBot_zero (-1)
  revert this; simp

-- `DFinsupp.small` idx 3: necessary
theorem w1c4_157 : ¬ ∀ {ι : Type 1} {π : ι → Type} [inst : (i : ι) → Zero (π i)] [∀ (i : ι), Small.{0, 0} (π i)],
    Small.{0, 1} (DFinsupp π) := fun h => by
  classical
  have := h (ι := Type) (π := fun _ => ℕ)
  have : Small.{0} Type := small_of_injective (f := fun T : Type => (DFinsupp.single T (1:ℕ) : Π₀ _ : Type, ℕ))
    (fun a b e => DFinsupp.single_left_injective (β := fun _ : Type => ℕ) (b := fun _ => 1) (by simp) e)
  exact not_small_type this

-- `DFinsupp.small` idx 4: necessary
theorem w1c4_158 : ¬ ∀ {ι : Type} {π : ι → Type 1} [inst : (i : ι) → Zero (π i)] [Small.{0, 0} ι],
    Small.{0, 1} (DFinsupp π) := fun h => by
  have := h (ι := Unit) (π := fun _ => WithZero Type)
  have : Small.{0} Type := small_of_injective (f := fun T : Type => (DFinsupp.single () (T : WithZero Type) : Π₀ _ : Unit, WithZero Type))
    (fun a b e => by simpa using DFunLike.congr_fun e ())
  exact not_small_type this

-- `Finsupp.small` idx 3: necessary
theorem w1c4_159 : ¬ ∀ {σ : Type} {R : Type 1} [inst : Zero R] [Small.{0, 0} σ], Small.{0, 1} (Finsupp σ R) := fun h => by
  have := h (σ := Unit) (R := WithZero Type)
  have : Small.{0} Type := small_of_injective (f := fun T : Type => Finsupp.single () (T : WithZero Type))
    (fun a b e => by simpa using DFunLike.congr_fun e ())
  exact not_small_type this

-- `Finsupp.small` idx 4: necessary
theorem w1c4_160 : ¬ ∀ {σ : Type 1} {R : Type} [inst : Zero R] [Small.{0, 0} R], Small.{0, 1} (Finsupp σ R) := fun h => by
  classical
  have := h (σ := Type) (R := ℕ)
  have : Small.{0} Type := small_of_injective (f := fun T : Type => Finsupp.single T (1:ℕ))
    (Finsupp.single_left_injective one_ne_zero)
  exact not_small_type this

-- `dfinsuppSum_mem` idx 9: necessary
theorem w1c4_161 : ¬ drop0% dfinsuppSum_mem 9 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (S := Submonoid ℤ) (Submonoid.powers 2) 0 (fun _ b => b) (by simp)
  simp [Submonoid.mem_powers_iff] at this

-- `dfinsuppSum_mem` idx 13: necessary
theorem w1c4_162 : ¬ drop0% dfinsuppSum_mem 13 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (S := AddSubmonoid ℤ) ⊥ (DFinsupp.single () 1) (fun _ b => b)
  simp [DFinsupp.sum] at this

-- `dfinsuppProd_mem` idx 9: necessary
theorem w1c4_163 : ¬ drop0% dfinsuppProd_mem 9 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (S := AddSubmonoid ℤ) ⊥ 0 (fun _ b => b) (by simp)
  simp at this

-- `dfinsuppProd_mem` idx 13: necessary
theorem w1c4_164 : ¬ drop0% dfinsuppProd_mem 13 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (S := Submonoid ℤ) ⊥ (DFinsupp.single () 2) (fun _ b => b)
  simp [DFinsupp.prod] at this

-- `dfinsuppSumAddHom_mem` idx 8: necessary
theorem w1c4_165 : ¬ drop0% dfinsuppSumAddHom_mem 8 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (S := Submonoid ℤ) (Submonoid.powers 2) 0 (fun _ => AddMonoidHom.id ℤ) (by simp)
  simp [Submonoid.mem_powers_iff] at this

-- `dfinsuppSumAddHom_mem` idx 12: necessary
theorem w1c4_166 : ¬ drop0% dfinsuppSumAddHom_mem 12 := fun h => by
  have := h (ι := Unit) (β := fun _ => ℤ) (γ := ℤ) (S := AddSubmonoid ℤ) ⊥ (DFinsupp.single () 1) (fun _ => AddMonoidHom.id ℤ)
  simp at this

-- `DFinsupp.Lex.acc_of_single_erase` idx 8: necessary
theorem w1c4_167 : ¬ drop0% DFinsupp.Lex.acc_of_single_erase 8 := fun h => by
  have := h (ι := Unit) (α := fun _ => ℕ) (r := fun _ _ => False) (s := fun _ a b => 0 < a ∧ 0 < b)
    (x := DFinsupp.single () 1) () (Acc.intro _ (fun y hy => by
      rw [DFinsupp.lex_def] at hy; obtain ⟨j, -, hj⟩ := hy; simp at hj))
  exact notAccSelf (x := DFinsupp.single () 1) ⟨(), fun _ h => h.elim, by simp⟩ this

-- `DFinsupp.Lex.acc_of_single_erase` idx 9: necessary
theorem w1c4_168 : ¬ drop0% DFinsupp.Lex.acc_of_single_erase 9 := fun h => by
  have := h (ι := Bool) (α := fun _ => ℕ) (r := fun _ _ => False) (s := fun i a b => i = false ∧ 0 < a ∧ 0 < b)
    (x := DFinsupp.single true 1 + DFinsupp.single false 1) true (Acc.intro _ (fun y hy => by
      rw [DFinsupp.lex_def] at hy; obtain ⟨j, -, hj⟩ := hy; cases j <;> simp at hj))
  exact notAccSelf ⟨false, fun _ h => h.elim, by simp⟩ this

-- `DFinsupp.Lex.acc_zero` idx 5: necessary
theorem w1c4_169 : ¬ drop0% DFinsupp.Lex.acc_zero 5 := fun h => by
  have := h (ι := Unit) (α := fun _ => ℕ) (r := fun _ _ => False) (s := fun _ _ _ => True)
  exact notAccSelf ⟨(), fun _ h => h.elim, trivial⟩ this

-- `DFinsupp.Lex.acc_of_single` idx 5: necessary
theorem w1c4_170 : ¬ drop0% DFinsupp.Lex.acc_of_single 5 := fun h => by
  have := h (ι := Unit) (α := fun _ => ℕ) (r := fun _ _ => False) (s := fun _ _ _ => True) 0 (by simp)
  exact notAccSelf ⟨(), fun _ h => h.elim, trivial⟩ this

-- `DFinsupp.Lex.acc_of_single` idx 9: necessary
theorem w1c4_171 : ¬ drop0% DFinsupp.Lex.acc_of_single 9 := fun h => by
  have := h (ι := Unit) (α := fun _ => ℕ) (r := fun _ _ => False) (s := fun _ a b => 0 < a ∧ 0 < b)
    (fun _ _ h => (lt_irrefl _ h.2)) (DFinsupp.single () 1)
  exact notAccSelf ⟨(), fun _ h => h.elim, by simp⟩ this

-- `DFinsupp.Lex.acc_single` idx 5: necessary
theorem w1c4_172 : ¬ drop0% DFinsupp.Lex.acc_single 5 := fun h => by
  have := h (ι := ℕ) (α := fun _ => ℕ) (r := fun a b => a > b) (s := fun _ a b => a = 1 ∧ b = 0) (hs := fun _ => wf10)
    (i := 0) (wfLtGt.apply 0) 1
  exact notAcc (fun n => (DFinsupp.single n 1 : Π₀ _ : ℕ, ℕ))
    (fun n => ⟨n+1, fun d hd => by simp [DFinsupp.single_apply]; split_ifs <;> omega, by simp⟩) this

-- `DFinsupp.Lex.acc_single` idx 6: necessary
theorem w1c4_173 : ¬ drop0% DFinsupp.Lex.acc_single 6 := fun h => by
  have := h (ι := Unit) (α := fun _ => ℕ) (r := fun _ _ => False) (s := fun _ a b => 0 < b ∧ b < a)
    (fun _ _ h => lt_irrefl _ h.1) (i := ()) ((wfUnit _).apply ()) 1
  exact notAcc (fun n => (DFinsupp.single () (n+1) : Π₀ _ : Unit, ℕ))
    (fun n => ⟨(), fun _ h => h.elim, by simp⟩) this

-- `DFinsupp.Lex.acc_single` idx 9: necessary
theorem w1c4_174 : ¬ drop0% DFinsupp.Lex.acc_single 9 := fun h => by
  have := h (ι := ℕ) (α := fun _ => ℕ) (r := fun a b => a < b) (s := fun _ a b => a < b)
    (fun _ _ h => Nat.not_lt_zero _ h) (hs := fun _ => wellFounded_lt) (i := 0) 1
  exact notAcc (fun n => (DFinsupp.single n 1 : Π₀ _ : ℕ, ℕ))
    (fun n => ⟨n, fun d hd => by simp [DFinsupp.single_apply]; split_ifs <;> omega, by simp⟩) this

-- `DFinsupp.Lex.acc` idx 5: necessary
theorem w1c4_175 : ¬ drop0% DFinsupp.Lex.acc 5 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ (fun a b => a > b) (fun _ a b => a = 1 ∧ b = 0) (fun _ => wf10) _ _
    (DFinsupp.single 0 1) (fun i hi => by
      have : i = 0 := by simpa using DFinsupp.support_single_subset hi
      subst this; exact wfLtGt.apply 0)
  exact notAcc (fun n => (DFinsupp.single n 1 : Π₀ _ : ℕ, ℕ))
    (fun n => ⟨n+1, fun d hd => by simp [DFinsupp.single_apply]; split_ifs <;> omega, by simp⟩) this

-- `DFinsupp.Lex.acc` idx 6: necessary
theorem w1c4_176 : ¬ drop0% DFinsupp.Lex.acc 6 := fun h => by
  have := h (ι := Unit) (α := fun _ => ℕ) (r := fun _ _ => False) (s := fun _ a b => 0 < b ∧ b < a)
    (fun _ _ h => lt_irrefl _ h.1) (DFinsupp.single () 1) (fun i _ => (wfUnit _).apply i)
  exact notAcc (fun n => (DFinsupp.single () (n+1) : Π₀ _ : Unit, ℕ))
    (fun n => ⟨(), fun _ h => h.elim, by simp⟩) this

-- `DFinsupp.Lex.acc` idx 10: necessary
theorem w1c4_177 : ¬ drop0% DFinsupp.Lex.acc 10 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ (fun a b => a < b) (fun _ a b => a < b)
    (fun _ _ h => Nat.not_lt_zero _ h) (fun _ => wellFounded_lt) _ _ (DFinsupp.single 0 1)
  exact notAcc (fun n => (DFinsupp.single n 1 : Π₀ _ : ℕ, ℕ))
    (fun n => ⟨n, fun d hd => by simp [DFinsupp.single_apply]; split_ifs <;> omega, by simp⟩) this

-- `DFinsupp.Lex.wellFounded` idx 5: necessary
theorem w1c4_178 : ¬ drop0% DFinsupp.Lex.wellFounded 5 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ (fun a b => a > b) (fun _ a b => a = 1 ∧ b = 0) (fun _ => wf10) wfLtGt
  exact notWF (fun n => (DFinsupp.single n 1 : Π₀ _ : ℕ, ℕ))
    (fun n => ⟨n+1, fun d hd => by simp [DFinsupp.single_apply]; split_ifs <;> omega, by simp⟩) this

-- `DFinsupp.Lex.wellFounded` idx 6: necessary
theorem w1c4_179 : ¬ drop0% DFinsupp.Lex.wellFounded 6 := fun h => by
  have := h (ι := Unit) (α := fun _ => ℕ) (r := fun _ _ => False) (s := fun _ a b => 0 < b ∧ b < a)
    (fun _ _ h => lt_irrefl _ h.1) (wfUnit _)
  exact notWF (fun n => (DFinsupp.single () (n+1) : Π₀ _ : Unit, ℕ))
    (fun n => ⟨(), fun _ h => h.elim, by simp⟩) this

-- `DFinsupp.Lex.wellFounded'` idx 5: necessary
theorem w1c4_180 : ¬ drop0% DFinsupp.Lex.wellFounded' 5 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ (fun a b => a > b) (fun _ a b => a = 1 ∧ b = 0) (fun _ => wf10) _
    (wellFounded_lt)
  exact notWF (fun n => (DFinsupp.single n 1 : Π₀ _ : ℕ, ℕ))
    (fun n => ⟨n+1, fun d hd => by simp [DFinsupp.single_apply]; split_ifs <;> omega, by simp⟩) this

-- `DFinsupp.Lex.wellFounded'` idx 6: necessary
theorem w1c4_181 : ¬ drop0% DFinsupp.Lex.wellFounded' 6 := fun h => by
  have := h (ι := Unit) (α := fun _ => ℕ) (r := fun _ _ => False) (s := fun _ a b => 0 < b ∧ b < a)
    (fun _ _ h => lt_irrefl _ h.1) ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩
  exact notWF (fun n => (DFinsupp.single () (n+1) : Π₀ _ : Unit, ℕ))
    (fun n => ⟨(), fun _ h => h.elim, by simp⟩) this

-- `DFinsupp.Lex.wellFounded'` idx 7: necessary
theorem w1c4_182 : ¬ drop0% DFinsupp.Lex.wellFounded' 7 := fun h => by
  have := @h Bool (fun _ => ℕ) _ (fun _ _ => False) (fun _ a b => a < b)
    (fun _ _ h => Nat.not_lt_zero _ h) (fun _ => wellFounded_lt) ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩
  have h1 : DFinsupp.Lex (fun _ _ => False) (fun _ a b => a < b) (DFinsupp.single true 1 : Π₀ _ : Bool, ℕ)
      (DFinsupp.single false 1) := ⟨false, fun _ h => h.elim, by simp⟩
  have h2 : DFinsupp.Lex (fun _ _ => False) (fun _ a b => a < b) (DFinsupp.single false 1 : Π₀ _ : Bool, ℕ)
      (DFinsupp.single true 1) := ⟨true, fun _ h => h.elim, by simp⟩
  exact this.asymmetric _ _ h1 h2

-- `DFinsupp.Lex.wellFounded'` idx 8: necessary
theorem w1c4_183 : ¬ drop0% DFinsupp.Lex.wellFounded' 8 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ (fun a b => a < b) (fun _ a b => a < b)
    (fun _ _ h => Nat.not_lt_zero _ h) (fun _ => wellFounded_lt) _
  exact notWF (fun n => (DFinsupp.single n 1 : Π₀ _ : ℕ, ℕ))
    (fun n => ⟨n, fun d hd => by simp [DFinsupp.single_apply]; split_ifs <;> omega, by simp⟩) this

-- `DFinsupp.Lex.wellFoundedLT` idx 3: necessary
theorem w1c4_184 : ¬ drop0% DFinsupp.Lex.wellFoundedLT 3 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := B2) (α := fun _ => ℕ))
  have h1 : toLex (DFinsupp.single (b2 true) 1 : Π₀ _ : B2, ℕ) < toLex (DFinsupp.single (b2 false) 1) :=
    ⟨b2 false, fun _ h => h.elim, by
      show (DFinsupp.single (b2 true) 1 : Π₀ _ : B2, ℕ) (b2 false) < (DFinsupp.single (b2 false) 1 : Π₀ _ : B2, ℕ) (b2 false)
      rw [DFinsupp.single_eq_of_ne (by decide), DFinsupp.single_eq_same]; decide⟩
  have h2 : toLex (DFinsupp.single (b2 false) 1 : Π₀ _ : B2, ℕ) < toLex (DFinsupp.single (b2 true) 1) :=
    ⟨b2 true, fun _ h => h.elim, by
      show (DFinsupp.single (b2 false) 1 : Π₀ _ : B2, ℕ) (b2 true) < (DFinsupp.single (b2 true) 1 : Π₀ _ : B2, ℕ) (b2 true)
      rw [DFinsupp.single_eq_of_ne (by decide), DFinsupp.single_eq_same]; decide⟩
  exact this.asymmetric _ _ h1 h2

-- `DFinsupp.Lex.wellFoundedLT` idx 4: necessary
theorem w1c4_185 : ¬ drop0% DFinsupp.Lex.wellFoundedLT 4 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := ℕ) (α := fun _ => ℕ))
  exact notWF (fun n => toLex (DFinsupp.single n 1 : Π₀ _ : ℕ, ℕ))
    (fun n => ⟨n, fun d hd => by simp [DFinsupp.single_apply]; split_ifs <;> omega, by simp⟩) this

-- `DFinsupp.Lex.wellFoundedLT` idx 7: necessary
theorem w1c4_186 : ¬ drop0% DFinsupp.Lex.wellFoundedLT 7 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := ℕᵒᵈ) (α := fun _ => N1))
  refine notWF (fun n => toLex (DFinsupp.single (OrderDual.toDual n) n0 : Π₀ _ : ℕᵒᵈ, N1)) (fun n => ?_) this
  refine ⟨OrderDual.toDual (n+1), fun j hj => ?_, ?_⟩
  · have hj' : n + 1 < OrderDual.ofDual j := hj
    show (DFinsupp.single (OrderDual.toDual (n+1)) n0 : Π₀ _ : ℕᵒᵈ, N1) j = (DFinsupp.single (OrderDual.toDual n) n0 : Π₀ _ : ℕᵒᵈ, N1) j
    rw [DFinsupp.single_eq_of_ne, DFinsupp.single_eq_of_ne] <;>
      (intro e; rw [e] at hj'; simp only [OrderDual.ofDual_toDual] at hj'; omega)
  · show (DFinsupp.single (OrderDual.toDual (n+1)) n0 : Π₀ _ : ℕᵒᵈ, N1) (OrderDual.toDual (n+1)) <
      (DFinsupp.single (OrderDual.toDual n) n0 : Π₀ _ : ℕᵒᵈ, N1) (OrderDual.toDual (n+1))
    rw [DFinsupp.single_eq_same, DFinsupp.single_eq_of_ne (by simp)]
    exact n0_lt

-- `DFinsupp.Lex.wellFoundedLT` idx 8: necessary
theorem w1c4_187 : ¬ drop0% DFinsupp.Lex.wellFoundedLT 8 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := Unit) (α := fun _ => ℚ≥0))
  refine notWF (fun n => toLex (DFinsupp.single () (q n) : Π₀ _ : Unit, ℚ≥0)) (fun n => ?_) this
  rw [DFinsupp.Lex.lt_iff_of_unique]
  simpa using q_lt n

-- `DFinsupp.Colex.wellFoundedLT` idx 3: necessary
theorem w1c4_188 : ¬ drop0% DFinsupp.Colex.wellFoundedLT 3 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := B2) (α := fun _ => ℕ))
  have h1 : toColex (DFinsupp.single (b2 true) 1 : Π₀ _ : B2, ℕ) < toColex (DFinsupp.single (b2 false) 1) :=
    ⟨b2 false, fun _ h => h.elim, by
      show (DFinsupp.single (b2 true) 1 : Π₀ _ : B2, ℕ) (b2 false) < (DFinsupp.single (b2 false) 1 : Π₀ _ : B2, ℕ) (b2 false)
      rw [DFinsupp.single_eq_of_ne (by decide), DFinsupp.single_eq_same]; decide⟩
  have h2 : toColex (DFinsupp.single (b2 false) 1 : Π₀ _ : B2, ℕ) < toColex (DFinsupp.single (b2 true) 1) :=
    ⟨b2 true, fun _ h => h.elim, by
      show (DFinsupp.single (b2 false) 1 : Π₀ _ : B2, ℕ) (b2 true) < (DFinsupp.single (b2 true) 1 : Π₀ _ : B2, ℕ) (b2 true)
      rw [DFinsupp.single_eq_of_ne (by decide), DFinsupp.single_eq_same]; decide⟩
  exact this.asymmetric _ _ h1 h2

-- `DFinsupp.Colex.wellFoundedLT` idx 4: necessary
theorem w1c4_189 : ¬ drop0% DFinsupp.Colex.wellFoundedLT 4 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := ℤ) (α := fun _ => ℕ))
  exact notWF (fun n => toColex (DFinsupp.single (-(n:ℤ)) 1 : Π₀ _ : ℤ, ℕ))
    (fun n => ⟨-(n:ℤ), fun d hd => by simp [DFinsupp.single_apply]; split_ifs <;> omega, by simp⟩) this

-- `DFinsupp.Colex.wellFoundedLT` idx 7: necessary
theorem w1c4_190 : ¬ drop0% DFinsupp.Colex.wellFoundedLT 7 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := ℕ) (α := fun _ => N1))
  refine notWF (fun n => toColex (DFinsupp.single n n0 : Π₀ _ : ℕ, N1)) (fun n => ?_) this
  refine ⟨n+1, fun j hj => ?_, ?_⟩
  · show (DFinsupp.single (n+1) n0 : Π₀ _ : ℕ, N1) j = (DFinsupp.single n n0 : Π₀ _ : ℕ, N1) j
    rw [DFinsupp.single_eq_of_ne (by omega), DFinsupp.single_eq_of_ne (by omega)]
  · show (DFinsupp.single (n+1) n0 : Π₀ _ : ℕ, N1) (n+1) < (DFinsupp.single n n0 : Π₀ _ : ℕ, N1) (n+1)
    rw [DFinsupp.single_eq_same, DFinsupp.single_eq_of_ne (by omega)]
    exact n0_lt

-- `DFinsupp.Colex.wellFoundedLT` idx 8: necessary
theorem w1c4_191 : ¬ drop0% DFinsupp.Colex.wellFoundedLT 8 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := Unit) (α := fun _ => ℚ≥0))
  refine notWF (fun n => toColex (DFinsupp.single () (q n) : Π₀ _ : Unit, ℚ≥0)) (fun n => ?_) this
  rw [DFinsupp.colex_lt_iff_of_unique]
  simpa using q_lt n

-- `Pi.Lex.wellFounded` idx 4: necessary
theorem w1c4_192 : ¬ drop0% Pi.Lex.wellFounded 4 := fun h => by
  have := h (ι := Bool) (α := fun _ => ℕ) (fun _ _ => False) (s := fun _ a b => a < b) (hs := fun _ => wellFounded_lt)
  have h1 : Pi.Lex (fun _ _ => False) (fun {_} a b => a < b) (fun b : Bool => if b then 1 else 0 : Bool → ℕ)
      (fun b => if b then 0 else 1) := ⟨false, fun _ h => h.elim, by simp⟩
  have h2 : Pi.Lex (fun _ _ => False) (fun {_} a b => a < b) (fun b : Bool => if b then 0 else 1 : Bool → ℕ)
      (fun b => if b then 1 else 0) := ⟨true, fun _ h => h.elim, by simp⟩
  exact this.asymmetric _ _ h1 h2

-- `Pi.Lex.wellFounded` idx 5: necessary
theorem w1c4_193 : ¬ drop0% Pi.Lex.wellFounded 5 := fun h => by
  have := h (ι := ℕ) (α := fun _ => ℕ) (fun a b => a < b) (s := fun _ a b => a < b) (hs := fun _ => wellFounded_lt)
  exact notWF (fun n k => if k = n then 1 else 0)
    (fun n => ⟨n, fun d hd => by simp only; split_ifs <;> omega, by simp⟩) this

-- `Pi.Lex.wellFoundedLT` idx 3: necessary
theorem w1c4_194 : ¬ drop0% Pi.Lex.wellFoundedLT 3 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := ℕ) (α := fun _ => ℕ))
  exact notWF (fun n => toLex (fun k : ℕ => if k = n then 1 else 0 : ℕ → ℕ))
    (fun n => ⟨n, fun d hd => by change (if d = n + 1 then 1 else 0 : ℕ) = if d = n then 1 else 0; split_ifs <;> omega, by simp⟩) this

-- `Pi.Colex.wellFoundedLT` idx 3: necessary
theorem w1c4_195 : ¬ drop0% Pi.Colex.wellFoundedLT 3 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := ℕ) (α := fun _ => ℕ))
  exact notWF (fun n => toColex (fun k : ℕ => if k < n then 0 else 1 : ℕ → ℕ))
    (fun n => ⟨n, fun d hd => by change (if d < n + 1 then 0 else 1 : ℕ) = if d < n then 0 else 1; split_ifs <;> omega, by simp⟩) this

-- `Function.Lex.wellFoundedLT` idx 3: necessary
theorem w1c4_196 : ¬ drop0% Function.Lex.wellFoundedLT 3 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := ℕ) (α := ℕ))
  exact notWF (fun n => toLex (fun k : ℕ => if k = n then 1 else 0 : ℕ → ℕ))
    (fun n => ⟨n, fun d hd => by change (if d = n + 1 then 1 else 0 : ℕ) = if d = n then 1 else 0; split_ifs <;> omega, by simp⟩) this

-- `Function.Lex.wellFoundedLT` idx 5: necessary
theorem w1c4_197 : ¬ drop0% Function.Lex.wellFoundedLT 5 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := Unit) (α := ℤ))
  refine notWF (fun n => toLex (fun _ : Unit => -(n:ℤ))) (fun n => ?_) this
  rw [Pi.Lex.lt_iff_of_unique]; simp

-- `DFinsupp.Lex.wellFounded_of_finite` idx 4: necessary
theorem w1c4_198 : ¬ drop0% DFinsupp.Lex.wellFounded_of_finite 4 := fun h => by
  have := @h Bool (fun _ => ℕ) (fun _ _ => False) (fun _ a b => a < b) _ _ (fun _ => wellFounded_lt)
  have h1 : DFinsupp.Lex (fun _ _ => False) (fun _ a b => a < b) (DFinsupp.single true 1 : Π₀ _ : Bool, ℕ)
      (DFinsupp.single false 1) := ⟨false, fun _ h => h.elim, by simp⟩
  have h2 : DFinsupp.Lex (fun _ _ => False) (fun _ a b => a < b) (DFinsupp.single false 1 : Π₀ _ : Bool, ℕ)
      (DFinsupp.single true 1) := ⟨true, fun _ h => h.elim, by simp⟩
  exact this.asymmetric _ _ h1 h2

-- `DFinsupp.Lex.wellFounded_of_finite` idx 5: necessary
theorem w1c4_199 : ¬ drop0% DFinsupp.Lex.wellFounded_of_finite 5 := fun h => by
  have := @h ℕ (fun _ => ℕ) (fun a b => a < b) (fun _ a b => a < b) _ _ (fun _ => wellFounded_lt)
  exact notWF (fun n => (DFinsupp.single n 1 : Π₀ _ : ℕ, ℕ))
    (fun n => ⟨n, fun d hd => by simp [DFinsupp.single_apply]; split_ifs <;> omega, by simp⟩) this

-- `DFinsupp.Lex.wellFounded_of_finite` idx 7: necessary
theorem w1c4_200 : ¬ drop0% DFinsupp.Lex.wellFounded_of_finite 7 := fun h => by
  have := @h Unit (fun _ => ℕ) (fun a b => a < b) (fun _ a b => b < a) _ _ _
  exact notWF (fun n => (DFinsupp.single () n : Π₀ _ : Unit, ℕ))
    (fun n => ⟨(), fun d hd => absurd hd (lt_irrefl _), by simp⟩) this

-- `DFinsupp.Lex.wellFoundedLT_of_finite` idx 3: necessary
theorem w1c4_201 : ¬ drop0% DFinsupp.Lex.wellFoundedLT_of_finite 3 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := ℕ) (α := fun _ => ℕ))
  exact notWF (fun n => toLex (DFinsupp.single n 1 : Π₀ _ : ℕ, ℕ))
    (fun n => ⟨n, fun d hd => by simp [DFinsupp.single_apply]; split_ifs <;> omega, by simp⟩) this

-- `DFinsupp.Lex.wellFoundedLT_of_finite` idx 6: necessary
theorem w1c4_202 : ¬ drop0% DFinsupp.Lex.wellFoundedLT_of_finite 6 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := Unit) (α := fun _ => ℤ))
  refine notWF (fun n => toLex (DFinsupp.single () (-(n:ℤ)) : Π₀ _ : Unit, ℤ)) (fun n => ?_) this
  rw [DFinsupp.Lex.lt_iff_of_unique]; simp

-- `DFinsupp.Colex.wellFoundedLT_of_finite` idx 3: necessary
theorem w1c4_203 : ¬ drop0% DFinsupp.Colex.wellFoundedLT_of_finite 3 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := ℤ) (α := fun _ => ℕ))
  exact notWF (fun n => toColex (DFinsupp.single (-(n:ℤ)) 1 : Π₀ _ : ℤ, ℕ))
    (fun n => ⟨-(n:ℤ), fun d hd => by simp [DFinsupp.single_apply]; split_ifs <;> omega, by simp⟩) this

-- `DFinsupp.Colex.wellFoundedLT_of_finite` idx 6: necessary
theorem w1c4_204 : ¬ drop0% DFinsupp.Colex.wellFoundedLT_of_finite 6 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := Unit) (α := fun _ => ℤ))
  refine notWF (fun n => toColex (DFinsupp.single () (-(n:ℤ)) : Π₀ _ : Unit, ℤ)) (fun n => ?_) this
  rw [DFinsupp.colex_lt_iff_of_unique]; simp

-- `DFinsupp.wellFoundedLT` idx 4: necessary
theorem w1c4_205 : ¬ drop0% DFinsupp.wellFoundedLT 4 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := Unit) (α := fun _ => ℚ≥0) (fun _ a h => by simp at h))
  refine notWF (fun n => (DFinsupp.single () (q n) : Π₀ _ : Unit, ℚ≥0)) (fun n => ?_) this
  rw [DFinsupp.lt_def]; exact ⟨fun _ => by simpa using (q_lt n).le, (), by simpa using q_lt n⟩

-- `DFinsupp.wellFoundedLT` idx 5: necessary
theorem w1c4_206 : ¬ drop0% DFinsupp.wellFoundedLT 5 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := ℕ) (α := fun _ => N1))
  exact notWF m1 m1_lt this

-- `DFinsupp.wellFoundedLT'` idx 4: necessary
theorem w1c4_207 : ¬ drop0% DFinsupp.wellFoundedLT' 4 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := ℕ) (α := fun _ => N1))
  exact notWF m1 m1_lt this

-- `DFinsupp.wellFoundedLT'` idx 5: necessary
theorem w1c4_208 : ¬ drop0% DFinsupp.wellFoundedLT' 5 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := Unit) (α := fun _ => ℚ≥0))
  refine notWF (fun n => (DFinsupp.single () (q n) : Π₀ _ : Unit, ℚ≥0)) (fun n => ?_) this
  rw [DFinsupp.lt_def]; exact ⟨fun _ => by simpa using (q_lt n).le, (), by simpa using q_lt n⟩

-- `Pi.wellFoundedLT` idx 4: necessary
theorem w1c4_209 : ¬ drop0% Pi.wellFoundedLT 4 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := Unit) (α := fun _ => ℤ))
  refine notWF (fun n => (fun _ => -(n:ℤ) : Unit → ℤ)) (fun n => ?_) this
  rw [Pi.lt_def]; exact ⟨fun _ => by simp, (), by simp⟩

-- `Function.wellFoundedLT` idx 4: necessary
theorem w1c4_210 : ¬ drop0% Function.wellFoundedLT 4 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := Unit) (α := ℤ))
  refine notWF (fun n => (fun _ => -(n:ℤ) : Unit → ℤ)) (fun n => ?_) this
  rw [Pi.lt_def]; exact ⟨fun _ => by simp, (), by simp⟩

-- `DFinsupp.wellFoundedLT_of_finite` idx 2: necessary
theorem w1c4_211 : ¬ drop0% DFinsupp.wellFoundedLT_of_finite 2 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := ℕ) (α := fun _ => N1))
  exact notWF m1 m1_lt this

-- `DFinsupp.wellFoundedLT_of_finite` idx 5: necessary
theorem w1c4_212 : ¬ drop0% DFinsupp.wellFoundedLT_of_finite 5 := fun h => by
  have := @wellFounded_lt _ _ (h (ι := Unit) (α := fun _ => ℤ))
  refine notWF (fun n => (DFinsupp.single () (-(n:ℤ)) : Π₀ _ : Unit, ℤ)) (fun n => ?_) this
  rw [DFinsupp.lt_def]; exact ⟨fun _ => by simp, (), by simp⟩

