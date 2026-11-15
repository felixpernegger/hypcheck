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
-- `ENat.recTopCoe_ofNat` idx 4: necessary (x = 0: Nat.AtLeastTwo 0 fails)
theorem c5_1 : ¬ indep0% ENat.recTopCoe_ofNat 4 := fun h => by
  have := @h (fun _ => True) trivial (fun _ => trivial) 0
  obtain ⟨h2⟩ := this
  omega
-- `ENat.add_lt_add_of_le_of_lt` idx 4: necessary (a = b = top, c = 0, d = 1: top + 0 < top + 1 fails)
theorem c5_2 : ¬ drop0% ENat.add_lt_add_of_le_of_lt 4 := fun h => by
  have := @h ⊤ ⊤ 0 1 le_rfl (by decide)
  simp at this
-- `ENat.add_lt_add_of_lt_of_le` idx 4: necessary (a = 0, b = 1, c = d = top)
theorem c5_3 : ¬ drop0% ENat.add_lt_add_of_lt_of_le 4 := fun h => by
  have := @h 0 1 ⊤ ⊤ (by decide) le_rfl
  simp at this
-- `ENat.nat_induction` idx 2: necessary (motive a := a != 0, a = 0)
theorem c5_4 : ¬ drop0% ENat.nat_induction 2 := fun h => by
  have := @h (fun a => a ≠ 0) 0 (fun n _ => by simp) (fun _ => by simp)
  simp at this
-- `ENat.nat_induction` idx 3: necessary (motive a := a = 0, a = 1 (top case vacuous since motive 1 fails))
theorem c5_5 : ¬ drop0% ENat.nat_induction 3 := fun h => by
  have := @h (fun a => a = 0) 1 rfl (fun H => by simpa using H 1)
  simp at this
-- `ENat.prod_ne_top` idx 3: necessary (s = univ on Unit, f = top)
theorem c5_9 : ¬ drop0% ENat.prod_ne_top 3 := fun h => by
  have := @h Unit Finset.univ (fun _ => ⊤)
  simp at this
-- `ENat.prod_lt_top` idx 3: necessary (s = univ on Unit, f = top)
theorem c5_10 : ¬ drop0% ENat.prod_lt_top 3 := fun h => by
  have := @h Unit Finset.univ (fun _ => ⊤)
  simp at this
-- `ENat.lt_top_of_sum_ne_top` idx 3: necessary (s = univ on Unit, f = top)
theorem c5_11 : ¬ drop0% ENat.lt_top_of_sum_ne_top 3 := fun h => by
  have := @h Unit Finset.univ (fun _ => ⊤) () (by simp)
  simp at this
-- `ENat.lt_top_of_sum_ne_top` idx 5: necessary (s = empty, f = top: sum 0 != top but f a = top)
theorem c5_12 : ¬ drop0% ENat.lt_top_of_sum_ne_top 5 := fun h => by
  have := @h Unit ∅ (fun _ => ⊤) (by simp) ()
  simp at this
-- `ENat.toNat_sum` idx 3: necessary (f = (top, 1) on Bool: toNat sum = 0, sum of toNat = 1)
theorem c5_13 : ¬ drop0% ENat.toNat_sum 3 := fun h => by
  have := @h Bool Finset.univ (fun b => if b then ⊤ else 1)
  simp at this
-- `ENat.sum_lt_sum_of_nonempty` idx 5: necessary (f = g = 0 on Unit)
theorem c5_14 : ¬ drop0% ENat.sum_lt_sum_of_nonempty 5 := fun h => by
  have := @h Unit Finset.univ (by simp) 0 0
  simp at this
-- `ENat.exists_le_of_sum_le` idx 5: necessary (f = 1, g = 0 on Unit)
theorem c5_15 : ¬ drop0% ENat.exists_le_of_sum_le 5 := fun h => by
  have := @h Unit Finset.univ (by simp) 1 0
  simp at this

-- `ENat.iInf_sum` idx 4: necessary (iota = Empty, s = empty: iInf = top, sum = 0)
theorem c5_7 : ¬ drop0% ENat.iInf_sum 4 := fun h => by
  have := @h Empty Unit (fun _ _ => 0) ∅ (fun _ i => i.elim)
  simp at this
-- `ENat.iInf_sum` idx 5: necessary (iota = alpha = Bool, f i a = if i = a then 0 else 1: LHS 1, RHS 0)
theorem c5_8 : ¬ drop0% ENat.iInf_sum 5 := fun h => by
  have := @h Bool Bool (fun i a => if i = a then 0 else 1) Finset.univ
  simp [iInf_bool_eq] at this
-- `ENat.sum_iSup` idx 4: necessary (alpha = iota = Bool, f a i = if a = i then 1 else 0: LHS 2, RHS 1)
theorem c5_16 : ¬ drop0% ENat.sum_iSup 4 := fun h => by
  have := @h Bool Bool Finset.univ (fun a i => if a = i then 1 else 0)
  simp [iSup_bool_eq] at this
-- `ENat.natCast_sSup` idx 1: necessary (s = univ: sSup univ = 0 in N (junk), RHS = top)
theorem c5_19 : ¬ drop0% ENat.natCast_sSup 1 := fun h => by
  have := @h Set.univ
  simp [ENat.iSup_natCast] at this
-- `ENat.natCast_iInf` idx 2: necessary (iota = False: iInf in N = 0, in N-infinity = top)
theorem c5_21 : ¬ drop0% ENat.natCast_iInf 2 := fun h => by
  have := @h False (fun _ => 0)
  simp at this
-- `ENat.finite_of_sSup_lt_top` idx 1: necessary (s = range of the cast N -> N-infinity: sSup = top, s infinite)
theorem c5_23 : ¬ drop0% ENat.finite_of_sSup_lt_top 1 := fun h => by
  exact Set.infinite_range_of_injective Nat.cast_injective (@h (Set.range ((↑) : ℕ → ℕ∞)))
-- `ENat.exists_eq_iSup_of_lt_top` idx 2: necessary (iota = False: iSup = 0 < top, no index)
theorem c5_25 : ¬ drop0% ENat.exists_eq_iSup_of_lt_top 2 := fun h => by
  have := @h False (fun _ => 0) (by simp)
  simp at this
-- `ENat.exists_eq_iSup_of_lt_top` idx 3: necessary (iota = N (universe 1), f = cast: iSup = top is not attained)
theorem c5_26 : ¬ drop1% ENat.exists_eq_iSup_of_lt_top 3 := fun h => by
  obtain ⟨i, hi⟩ := @h ℕ (fun n => n) inferInstance
  simp [ENat.iSup_natCast] at hi
-- `ENat.exists_eq_iInf` idx 1: necessary (iota = False: no index)
theorem c5_27 : ¬ drop0% ENat.exists_eq_iInf 1 := fun h => by
  have := @h False (fun _ => 0)
  simp at this

namespace W1c5
universe u
/-- Two incomparable points: a preorder that is not directed. -/
abbrev U2 := Unit ⊕ Unit
theorem u2_mono (f : U2 → ℕ∞) : Monotone f := by
  rintro (⟨⟩|⟨⟩) (⟨⟩|⟨⟩) h <;> simp_all
/-- Smul on ℕ∞ by a one-point type that sends 0 to 1 and everything else to 0. -/
structure R1 : Type u where
instance : SMul R1.{u} ℕ∞ := ⟨fun _ x => if x = 0 then 1 else 0⟩
theorem r1_smul (c : R1.{u}) (x : ℕ∞) : c • x = if x = 0 then 1 else 0 := rfl
end W1c5
open W1c5
-- `ENat.sum_iSup_of_monotone` idx 3: necessary (iota = Unit + Unit (sum order, not directed), f a = indicator of one summand: LHS 2, RHS 1)
theorem c5_17 : ¬ drop0% ENat.sum_iSup_of_monotone 3 := fun h => by
  have := @h Bool U2 _ Finset.univ (fun a => Sum.elim (fun _ => if a then 1 else 0) (fun _ => if a then 0 else 1))
    (fun a => u2_mono _)
  simp [iSup_sum] at this
-- `ENat.sum_iSup_of_monotone` idx 6: necessary (iota = Bool, f a i = if a = i then 1 else 0 (not monotone): LHS 2, RHS 1)
theorem c5_18 : ¬ drop0% ENat.sum_iSup_of_monotone 6 := fun h => by
  have := @h Bool Bool _ inferInstance Finset.univ (fun a i => if a = i then 1 else 0)
  simp [iSup_bool_eq] at this
-- `ENat.coe_sSup` idx 1: necessary (s = univ: sSup univ = 0 in N (junk), RHS = top)
theorem c5_20 : ¬ drop0% ENat.coe_sSup 1 := fun h => by
  have := @h Set.univ
  simp [ENat.iSup_natCast] at this
-- `ENat.coe_iInf` idx 2: necessary (iota = False: iInf in N = 0, in N-infinity = top)
theorem c5_22 : ¬ drop0% ENat.coe_iInf 2 := fun h => by
  have := @h False (fun _ => 0)
  simp at this
-- `ENat.sSup_mem_of_nonempty_of_lt_top` idx 2: necessary (s = range of the cast: sSup = top is not in s)
theorem c5_24 : ¬ drop0% ENat.sSup_mem_of_nonempty_of_lt_top 2 := fun h => by
  have := @h (Set.range ((↑) : ℕ → ℕ∞)) ⟨⟨0, 0, rfl⟩⟩
  simp [sSup_range, ENat.iSup_natCast] at this
-- `ENat.exists_eq_iSup₂_of_lt_top` idx 3: necessary (iota1 = Empty)
theorem c5_28 : ¬ drop0% ENat.exists_eq_iSup₂_of_lt_top 3 := fun h => by
  have := @h Empty Unit (fun _ _ => 0) inferInstance (by simp)
  simp at this
-- `ENat.exists_eq_iSup₂_of_lt_top` idx 4: necessary (iota2 = Empty)
theorem c5_29 : ¬ drop0% ENat.exists_eq_iSup₂_of_lt_top 4 := fun h => by
  have := @h Unit Empty (fun _ _ => 0) inferInstance (by simp)
  simp at this
-- `ENat.exists_eq_iSup₂_of_lt_top` idx 5: necessary (iota2 = N, f i j = j: iSup = top is not attained)
theorem c5_30 : ¬ drop0% ENat.exists_eq_iSup₂_of_lt_top 5 := fun h => by
  obtain ⟨i, j, hj⟩ := @h Unit ℕ (fun _ j => j) inferInstance inferInstance
  simp [ENat.iSup_natCast] at hj
-- `ENat.mul_iInf` idx 3: necessary (iota = False, a = 0: 0 * top = 0, empty iInf = top)
theorem c5_31 : ¬ drop0% ENat.mul_iInf 3 := fun h => by
  have := @h False (fun _ => 0) 0
  simp at this
-- `ENat.iInf_mul` idx 3: necessary (iota = False, a = 0: top * 0 = 0, empty iInf = top)
theorem c5_32 : ¬ drop0% ENat.iInf_mul 3 := fun h => by
  have := @h False (fun _ => 0) 0
  simp at this
-- `ENat.mul_iInf'` idx 3: necessary (iota = False, a = 0)
theorem c5_33 : ¬ drop0% ENat.mul_iInf' 3 := fun h => by
  have := @h False (fun _ => 0) 0
  simp at this
-- `ENat.iInf_mul'` idx 3: necessary (iota = False, a = 0)
theorem c5_34 : ¬ drop0% ENat.iInf_mul' 3 := fun h => by
  have := @h False (fun _ => 0) 0
  simp at this
-- `ENat.mul_iInf_of_ne` idx 3: necessary (iota = False, a = 0)
theorem c5_35 : ¬ drop0% ENat.mul_iInf_of_ne 3 := fun h => by
  have := @h False (fun _ => 0) 0
  simp at this
-- `ENat.iInf_mul_of_ne` idx 3: necessary (iota = False, a = 0)
theorem c5_36 : ¬ drop0% ENat.iInf_mul_of_ne 3 := fun h => by
  have := @h False (fun _ => 0) 0
  simp at this
-- `ENat.add_iSup` idx 2: necessary (iota = False, a = 1: 1 + 0 = 1, empty iSup = 0)
theorem c5_37 : ¬ drop0% ENat.add_iSup 2 := fun h => by
  have := @h False 1 (fun _ => 0)
  simp at this
-- `ENat.iSup_add` idx 2: necessary (iota = False, a = 1)
theorem c5_38 : ¬ drop0% ENat.iSup_add 2 := fun h => by
  have := @h False 1 (fun _ => 0)
  simp at this
-- `ENat.iSup_add_iSup_le` idx 4: necessary (iota = False, kappa = True, g = 1, a = 0: hypothesis vacuous, 0 + 1 <= 0 fails)
theorem c5_39 : ¬ drop0% ENat.iSup_add_iSup_le 4 := fun h => by
  have := @h False True (fun _ => 1) 0 inferInstance (fun _ => 1) (fun i => i.elim)
  simp at this
-- `ENat.iSup_add_iSup_le` idx 5: necessary (iota = True, kappa = False, f = 1, a = 0)
theorem c5_40 : ¬ drop0% ENat.iSup_add_iSup_le 5 := fun h => by
  have := @h True False (fun _ => 1) 0 inferInstance (fun _ => 1) (fun _ j => j.elim)
  simp at this
-- `ENat.biSup_add_biSup_le'` idx 6: necessary (p = False, q = True, g = 1, a = 0)
theorem c5_41 : ¬ drop0% ENat.biSup_add_biSup_le' 6 := fun h => by
  have := @h True True (fun _ => 1) 0 (fun _ => False) (fun _ => True) ⟨trivial, trivial⟩ (fun _ => 1)
    (fun _ hp => hp.elim)
  simp at this
-- `ENat.biSup_add_biSup_le'` idx 7: necessary (p = True, q = False, f = 1, a = 0)
theorem c5_42 : ¬ drop0% ENat.biSup_add_biSup_le' 7 := fun h => by
  have := @h True True (fun _ => 1) 0 (fun _ => True) (fun _ => False) ⟨trivial, trivial⟩ (fun _ => 1)
    (fun _ _ _ hq => hq.elim)
  simp at this
-- `ENat.biSup_add_biSup_le` idx 4: necessary (s = empty, t = univ on Unit, g = 1, a = 0)
theorem c5_43 : ¬ drop0% ENat.biSup_add_biSup_le 4 := fun h => by
  have := @h Unit Unit ∅ Set.univ (by simp) (fun _ => 1) (fun _ => 1) 0 (by simp)
  simp at this
-- `ENat.biSup_add_biSup_le` idx 5: necessary (s = univ, t = empty on Unit, f = 1, a = 0)
theorem c5_44 : ¬ drop0% ENat.biSup_add_biSup_le 5 := fun h => by
  have := @h Unit Unit Set.univ ∅ (by simp) (fun _ => 1) (fun _ => 1) 0 (by simp)
  simp at this
-- `ENat.biSup_add_biSup_le` idx 9: necessary (f = g = 1, a = 0 on Unit)
theorem c5_45 : ¬ drop0% ENat.biSup_add_biSup_le 9 := fun h => by
  have := @h Unit Unit Set.univ Set.univ (by simp) (by simp) (fun _ => 1) (fun _ => 1) 0
  simp at this
-- `ENat.iSup_add_iSup` idx 3: necessary (iota = Bool, f = (1 at true), g = (1 at false): LHS 2, RHS 1)
theorem c5_46 : ¬ drop1% ENat.iSup_add_iSup 3 := fun h => by
  have := @h Bool (fun i => if i then 1 else 0) (fun i => if i then 0 else 1)
  simp [iSup_bool_eq] at this
-- `ENat.iSup_add_iSup_of_monotone` idx 2: necessary (iota = Unit + Unit (not directed), f, g indicators of the two summands (monotone): LHS 2, RHS 1)
theorem c5_47 : ¬ drop0% ENat.iSup_add_iSup_of_monotone 2 := fun h => by
  have := @h U2 _ (Sum.elim (fun _ => 1) (fun _ => 0)) (Sum.elim (fun _ => 0) (fun _ => 1))
    (u2_mono _) (u2_mono _)
  simp [iSup_sum] at this
-- `ENat.iSup_add_iSup_of_monotone` idx 5: necessary (iota = Bool, f antitone (1 at false), g monotone (1 at true): LHS 2, RHS 1)
theorem c5_48 : ¬ drop0% ENat.iSup_add_iSup_of_monotone 5 := fun h => by
  have := @h Bool _ inferInstance (fun i => if i then 0 else 1) (fun i => if i then 1 else 0)
    (by intro a b hab; cases a <;> cases b <;> first | exact absurd hab (by decide) | simp)
  simp [iSup_bool_eq] at this
-- `ENat.iSup_add_iSup_of_monotone` idx 6: necessary (iota = Bool, f monotone, g antitone)
theorem c5_49 : ¬ drop0% ENat.iSup_add_iSup_of_monotone 6 := fun h => by
  have := @h Bool _ inferInstance (fun i => if i then 1 else 0) (fun i => if i then 0 else 1)
    (by intro a b hab; cases a <;> cases b <;> first | exact absurd hab (by decide) | simp)
  simp [iSup_bool_eq] at this
-- `ENat.smul_iSup` idx 3: necessary (R a one-point type with c . x = if x = 0 then 1 else 0, f = (0, 1) on Bool: c . 1 = 0, iSup = 1)
theorem c5_50 : ¬ drop1% ENat.smul_iSup 3 := fun h => by
  have := @h Bool R1 _ (fun i => if i then 1 else 0) ⟨⟩
  simp [iSup_bool_eq, r1_smul] at this
-- `ENat.smul_sSup` idx 2: necessary (same smul, s = {0, 1}: c . sSup s = 0, RHS = 1)
theorem c5_51 : ¬ drop0% ENat.smul_sSup 2 := fun h => by
  have := @h R1 _ {0, 1} ⟨⟩
  simp only [iSup_insert, iSup_singleton, sSup_insert, sSup_singleton, r1_smul] at this
  simp at this
-- `ENat.sub_iSup` idx 3: necessary (iota = False, a = 0: 0 - 0 = 0, empty iInf = top)
theorem c5_52 : ¬ drop0% ENat.sub_iSup 3 := fun h => by
  have := @h False (fun _ => 0) 0 (by simp)
  simp at this
-- `ENat.sub_iSup` idx 4: necessary (a = top, iota = N, f = cast: top - top = 0, iInf of top - n = top)
theorem c5_53 : ¬ drop1% ENat.sub_iSup 4 := fun h => by
  have := @h ℕ (fun n => n) ⊤ inferInstance
  simp [ENat.iSup_natCast] at this
-- `ENat.iInf_add_iInf` idx 3: necessary (iota = Bool, f = (0 at true), g = (0 at false): LHS 0, RHS 1)
theorem c5_54 : ¬ drop1% ENat.iInf_add_iInf 3 := fun h => by
  have := @h Bool (fun i => if i then 0 else 1) (fun i => if i then 1 else 0)
  simp [iInf_bool_eq] at this
-- `ENat.iInf_add_iInf_of_monotone` idx 2: necessary (iota = Unit + Unit (not codirected), f, g indicators of the summands: LHS 0, RHS 1)
theorem c5_55 : ¬ drop0% ENat.iInf_add_iInf_of_monotone 2 := fun h => by
  have := @h U2 _ (Sum.elim (fun _ => 1) (fun _ => 0)) (Sum.elim (fun _ => 0) (fun _ => 1))
    (u2_mono _) (u2_mono _)
  simp [iInf_sum] at this
-- `ENat.iInf_add_iInf_of_monotone` idx 5: necessary (iota = Bool, f antitone, g monotone: LHS 0, RHS 1)
theorem c5_56 : ¬ drop0% ENat.iInf_add_iInf_of_monotone 5 := fun h => by
  have := @h Bool _ inferInstance (fun i => if i then 0 else 1) (fun i => if i then 1 else 0)
    (by intro a b hab; cases a <;> cases b <;> first | exact absurd hab (by decide) | simp)
  simp [iInf_bool_eq] at this
-- `ENat.iInf_add_iInf_of_monotone` idx 6: necessary (iota = Bool, f monotone, g antitone)
theorem c5_57 : ¬ drop0% ENat.iInf_add_iInf_of_monotone 6 := fun h => by
  have := @h Bool _ inferInstance (fun i => if i then 1 else 0) (fun i => if i then 0 else 1)
    (by intro a b hab; cases a <;> cases b <;> first | exact absurd hab (by decide) | simp)
  simp [iInf_bool_eq] at this
-- `ENat.le_iInf₂_add_iInf₂` idx 7: necessary (all index types True, f = g = 0, a = 1)
theorem c5_58 : ¬ drop0% ENat.le_iInf₂_add_iInf₂ 7 := fun h => by
  have := @h True 1 True (fun _ => True) (fun _ => True) (fun _ _ => 0) (fun _ _ => 0)
  simp at this
-- `ENat.le_sub_of_add_le_left` idx 3: necessary (a = c = top, b = 1: 1 <= top - top = 0 fails)
theorem c5_59 : ¬ drop0% ENat.le_sub_of_add_le_left 3 := fun h => by
  have := @h ⊤ 1 ⊤ (by simp)
  simp at this
-- `ENat.le_sub_of_add_le_right` idx 3: necessary (b = c = top, a = 1)
theorem c5_60 : ¬ drop0% ENat.le_sub_of_add_le_right 3 := fun h => by
  have := @h 1 ⊤ ⊤ (by simp)
  simp at this
-- `ENat.mul_le_mul_of_le_right` idx 5: removable (x * a <= y * a holds for all a in a canonically ordered semiring (mul_le_mul_left), a != top not needed)
theorem c5_61 : drop% ENat.mul_le_mul_of_le_right 5 := fun h _ => mul_le_mul_left h _

namespace W1c5
/-- ℤ with the reversed order: AddLeftMono and CharZero, but 1 < 0. -/
def Zd := ℤ
def Zd.val : Zd → ℤ := id
instance : AddCommMonoidWithOne Zd := inferInstanceAs (AddCommMonoidWithOne ℤ)
instance : CharZero Zd := inferInstanceAs (CharZero ℤ)
instance : PartialOrder Zd where
  le a b := b.val ≤ a.val
  le_refl a := le_refl a.val
  le_trans a b c := by intro h1 h2; change _ ≤ _ at h1 h2 ⊢; omega
  le_antisymm a b := by intro h1 h2; change _ ≤ _ at h1 h2; change a.val = b.val; omega
theorem zd_le (a b : Zd) : a ≤ b ↔ b.val ≤ a.val := Iff.rfl
instance : AddLeftMono Zd := ⟨fun c a b h => by
  change b.val ≤ a.val at h; change c.val + b.val ≤ c.val + a.val; omega⟩
theorem zd_not_nonneg_one : ¬ (0 : Zd) ≤ 1 := by
  rw [zd_le]; change ¬ (1 : ℤ) ≤ 0; omega
/-- ℤ ordered by equality plus 0 ≤ 1 only: ZeroLEOneClass and CharZero, not AddLeftMono. -/
def Z1 := ℤ
def Z1.val : Z1 → ℤ := id
instance : AddCommMonoidWithOne Z1 := inferInstanceAs (AddCommMonoidWithOne ℤ)
instance : CharZero Z1 := inferInstanceAs (CharZero ℤ)
instance : PartialOrder Z1 where
  le a b := a.val = b.val ∨ (a.val = 0 ∧ b.val = 1)
  le_refl a := Or.inl rfl
  le_trans a b c := by intro h1 h2; change _ ∨ _ at h1 h2 ⊢; omega
  le_antisymm a b := by intro h1 h2; change _ ∨ _ at h1 h2; change a.val = b.val; omega
theorem z1_le (a b : Z1) : a ≤ b ↔ a.val = b.val ∨ (a.val = 0 ∧ b.val = 1) := Iff.rfl
instance : ZeroLEOneClass Z1 := ⟨Or.inr ⟨rfl, rfl⟩⟩
/-- A FunLike type of maps ℕ → ℕ with no additivity. -/
structure FN where
  toFun : ℕ → ℕ
instance : FunLike FN ℕ ℕ where
  coe := FN.toFun
  coe_injective := by rintro ⟨f⟩ ⟨g⟩ h; cases h; rfl
instance : AddLeftMono PUnit := ⟨fun _ _ _ _ => le_of_eq (Subsingleton.elim _ _)⟩
theorem setU_nontrivial : Nontrivial (SetSemiring Unit) :=
  nontrivial_of_ne 0 1 (fun e => by have := congrArg SetSemiring.toSet e; simp at this; exact Set.empty_ne_univ (this.trans (Set.eq_univ_of_forall fun _ => rfl)))
end W1c5
open W1c5
-- `ENat.map_natCast_nonneg` idx 4: necessary (alpha = Z ordered by equality plus 0 <= 1 (ZeroLEOneClass, not AddLeftMono), n = 2: 0 <= 2 fails)
theorem c5_62 : ¬ drop0% ENat.map_natCast_nonneg 4 := fun h => by
  have := @h ((2 : ℕ) : ℕ∞) Z1 _ _ _
  simp only [ENat.map_natCast] at this
  rw [WithTop.coe_nonneg] at this
  rw [z1_le] at this
  change (0 : ℤ) = 2 ∨ ((0 : ℤ) = 0 ∧ (2 : ℤ) = 1) at this
  omega
-- `ENat.map_natCast_nonneg` idx 5: necessary (alpha = Z with the reversed order (AddLeftMono, not ZeroLEOneClass), n = 1)
theorem c5_63 : ¬ drop0% ENat.map_natCast_nonneg 5 := fun h => by
  have := @h ((1 : ℕ) : ℕ∞) Zd _ _ _
  simp only [ENat.map_natCast] at this
  rw [WithTop.coe_nonneg, Nat.cast_one] at this
  exact zd_not_nonneg_one this
-- `ENat.map_natCast_strictMono` idx 3: necessary (alpha = Z ordered by equality plus 0 <= 1, cast not strictly monotone at 1 < 2)
theorem c5_64 : ¬ drop0% ENat.map_natCast_strictMono 3 := fun h => by
  have := @h Z1 _ _ _ _ ((1 : ℕ) : ℕ∞) ((2 : ℕ) : ℕ∞) (by decide)
  simp only [ENat.map_natCast] at this
  rw [WithTop.coe_lt_coe, lt_iff_le_and_ne, z1_le] at this
  change ((1 : ℤ) = 2 ∨ ((1 : ℤ) = 0 ∧ (2 : ℤ) = 1)) ∧ _ at this
  omega
-- `ENat.map_natCast_strictMono` idx 4: necessary (alpha = Z with the reversed order: cast 0 < cast 1 fails)
theorem c5_65 : ¬ drop0% ENat.map_natCast_strictMono 4 := fun h => by
  have := @h Zd _ _ _ _ ((0 : ℕ) : ℕ∞) ((1 : ℕ) : ℕ∞) (by decide)
  simp only [ENat.map_natCast] at this
  rw [WithTop.coe_lt_coe, Nat.cast_one, Nat.cast_zero] at this
  exact zd_not_nonneg_one this.le
-- `ENat.map_natCast_strictMono` idx 5: necessary (alpha = PUnit (not CharZero): cast 0 = cast 1)
theorem c5_66 : ¬ drop0% ENat.map_natCast_strictMono 5 := fun h => by
  have := @h PUnit _ _ _ _ ((0 : ℕ) : ℕ∞) ((1 : ℕ) : ℕ∞) (by decide)
  simp only [ENat.map_natCast] at this
  rw [WithTop.coe_lt_coe] at this
  exact lt_irrefl _ this
universe u_1
-- `ENat.map_natCast_injective` idx 3: removable (injectivity of WithTop.map Nat.cast only needs CharZero (Nat.cast_injective))
theorem c5_67 : drop% ENat.map_natCast_injective 3 := fun {α} _ _ _ _ => WithTop.map_injective Nat.cast_injective
-- `ENat.map_natCast_injective` idx 4: removable (injectivity of WithTop.map Nat.cast only needs CharZero (Nat.cast_injective))
theorem c5_68 : drop% ENat.map_natCast_injective 4 := fun {α} _ _ _ _ => WithTop.map_injective Nat.cast_injective
-- `ENat.map_natCast_injective` idx 5: necessary (alpha = PUnit (not CharZero): map cast 0 = map cast 1)
theorem c5_69 : ¬ drop0% ENat.map_natCast_injective 5 := fun h => by
  have := @h PUnit _ _ _ _ (a₁ := 0) (a₂ := 1) rfl
  exact absurd this (by decide)
-- `ENat.map_natCast_inj` idx 5: removable (follows from injectivity of WithTop.map Nat.cast, which only needs CharZero)
theorem c5_70 : drop% ENat.map_natCast_inj 5 := fun {m n α} _ _ _ _ => (WithTop.map_injective Nat.cast_injective).eq_iff
-- `ENat.map_natCast_inj` idx 6: removable (follows from injectivity of WithTop.map Nat.cast, which only needs CharZero)
theorem c5_71 : drop% ENat.map_natCast_inj 6 := fun {m n α} _ _ _ _ => (WithTop.map_injective Nat.cast_injective).eq_iff
-- `ENat.map_natCast_inj` idx 7: necessary (alpha = PUnit, m = 0, n = 1)
theorem c5_72 : ¬ drop0% ENat.map_natCast_inj 7 := fun h => by
  have := (@h 0 1 PUnit _ _ _ _).1 rfl
  exact absurd this (by decide)
-- `ENat.map_natCast_eq_zero` idx 4: removable (0 = map cast 0 and injectivity of WithTop.map Nat.cast (CharZero only))
theorem c5_73 : drop% ENat.map_natCast_eq_zero 4 := fun {n α} _ _ _ _ => by
  rw [show (0 : WithTop α) = ENat.map Nat.cast 0 by simp]
  exact (WithTop.map_injective Nat.cast_injective).eq_iff
-- `ENat.map_natCast_eq_zero` idx 5: removable (0 = map cast 0 and injectivity of WithTop.map Nat.cast (CharZero only))
theorem c5_74 : drop% ENat.map_natCast_eq_zero 5 := fun {n α} _ _ _ _ => by
  rw [show (0 : WithTop α) = ENat.map Nat.cast 0 by simp]
  exact (WithTop.map_injective Nat.cast_injective).eq_iff
-- `ENat.map_natCast_eq_zero` idx 6: necessary (alpha = PUnit, n = 1)
theorem c5_75 : ¬ drop0% ENat.map_natCast_eq_zero 6 := fun h => by
  have := (@h 1 PUnit _ _ _ _).1 rfl
  exact absurd this (by decide)
-- `ENat.map_add` idx 4: necessary (F a FunLike type of maps N -> N, f = const 1: map f (0 + 0) = 1, map f 0 + map f 0 = 2)
theorem c5_6 : ¬ drop0% ENat.map_add 4 := fun h => by
  have := @h ℕ FN _ _ ⟨fun _ => 1⟩ 0 0
  simp only [add_zero, ENat.map_zero] at this
  change ((1 : ℕ) : WithTop ℕ) = (1 : ℕ) + (1 : ℕ) at this
  norm_cast at this
-- `MonoidWithZeroHom.ENatMap_apply` idx 3: removable (derivable: hf (injective f : N -> S) gives f 0 != f 1, so S is nontrivial)
theorem c5_76 : indep% MonoidWithZeroHom.ENatMap_apply 3 := fun {S} _ _ f hf =>
  ⟨⟨f 0, f 1, fun e => absurd (hf e) (by decide)⟩⟩
-- `MonoidWithZeroHom.ENatMap_apply` idx 5: necessary (S = ZMod 2, f = Nat.castRingHom: f 0 = f 2)
theorem c5_77 : ¬ indep0% MonoidWithZeroHom.ENatMap_apply 5 := fun h => by
  have := @h (ZMod 2) _ _ _ (Nat.castRingHom (ZMod 2) : ℕ →*₀ ZMod 2) (a₁ := 0) (a₂ := 2) rfl
  exact absurd this (by decide)
-- `RingHom.ENatMap_apply` idx 3: necessary (S = Z (f = Nat.castRingHom Z injective) is not canonically ordered: 0 <= 0 + -1 fails)
theorem c5_78 : ¬ indep0% RingHom.ENatMap_apply 3 := fun h => by
  have := @h ℤ _ _ _ _ (Nat.castRingHom ℤ) Nat.cast_injective
  exact absurd (le_self_add (a := (0 : ℤ)) (b := -1)) (by omega)
-- `RingHom.ENatMap_apply` idx 5: removable (derivable: hf (injective f : N -> S) gives f 0 != f 1, so S is nontrivial)
theorem c5_79 : indep% RingHom.ENatMap_apply 5 := fun {S} _ _ _ _ f hf =>
  ⟨⟨f 0, f 1, fun e => absurd (hf e) (by decide)⟩⟩
-- `RingHom.ENatMap_apply` idx 7: necessary (S = SetSemiring Unit (idempotent, canonically ordered, nontrivial), f = Nat.castRingHom: f 1 = 1 + 1 = f 2)
theorem c5_80 : ¬ indep0% RingHom.ENatMap_apply 7 := fun h => by
  have := @h (SetSemiring Unit) _ _ _ (Classical.decEq _) setU_nontrivial (Nat.castRingHom _) (a₁ := 1) (a₂ := 2)
    (by simp only [map_one, map_ofNat]; rw [← one_add_one_eq_two, SetSemiring.add_def]; simp)
  exact absurd this (by decide)

namespace W1c5
/-- Disequalities between the EReal points used in the induction rows. -/
theorem er_ne : ((⊤ : EReal) = 1 ↔ False) ∧ ((⊥ : EReal) = 1 ↔ False) ∧ ((1 : EReal) = ⊤ ↔ False) ∧
    ((1 : EReal) = ⊥ ↔ False) ∧ ((⊤ : EReal) = -1 ↔ False) ∧ ((⊥ : EReal) = -1 ↔ False) ∧
    ((-1 : EReal) = ⊤ ↔ False) ∧ ((-1 : EReal) = ⊥ ↔ False) ∧ (∀ x : ℝ, (x : EReal) = -1 ↔ x = -1) ∧ ((0 : EReal) = -1 ↔ False) ∧ ((-1 : EReal) = 0 ↔ False) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x => ?_, ?_, ?_⟩
  · exact iff_false_intro (EReal.top_ne_coe 1)
  · exact iff_false_intro (EReal.bot_ne_coe 1)
  · exact iff_false_intro (EReal.coe_ne_top 1)
  · exact iff_false_intro (EReal.coe_ne_bot 1)
  · exact iff_false_intro (EReal.top_ne_coe (-1))
  · exact iff_false_intro (EReal.bot_ne_coe (-1))
  · exact iff_false_intro (EReal.coe_ne_top (-1))
  · exact iff_false_intro (EReal.coe_ne_bot (-1))
  · rw [← EReal.coe_one, ← EReal.coe_neg, EReal.coe_eq_coe_iff]
  · exact iff_false_intro (by rw [← EReal.coe_zero, ← EReal.coe_one, ← EReal.coe_neg, EReal.coe_eq_coe_iff]; norm_num)
  · exact iff_false_intro (by rw [← EReal.coe_zero, ← EReal.coe_one, ← EReal.coe_neg, EReal.coe_eq_coe_iff]; norm_num)
end W1c5
open W1c5
-- `EReal.induction₂` idx 1: necessary (P a b := not (a = ⊤ and b = ⊤); only case 1 covers that point)
theorem c5_101 : ¬ drop0% EReal.induction₂ 1 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (⊤ : EReal) ∧ b = (⊤ : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊤ : EReal) (⊤ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 2: necessary (P a b := not (a = ⊤ and b = 1); only case 2 covers that point)
theorem c5_102 : ¬ drop0% EReal.induction₂ 2 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (⊤ : EReal) ∧ b = (1 : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊤ : EReal) (1 : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 3: necessary (P a b := not (a = ⊤ and b = 0); only case 3 covers that point)
theorem c5_103 : ¬ drop0% EReal.induction₂ 3 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (⊤ : EReal) ∧ b = (0 : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊤ : EReal) (0 : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 4: necessary (P a b := not (a = ⊤ and b = -1); only case 4 covers that point)
theorem c5_104 : ¬ drop0% EReal.induction₂ 4 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (⊤ : EReal) ∧ b = (-1 : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊤ : EReal) (-1 : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 6: necessary (P a b := not (a = 1 and b = ⊤); only case 6 covers that point)
theorem c5_105 : ¬ drop0% EReal.induction₂ 6 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (1 : EReal) ∧ b = (⊤ : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (1 : EReal) (⊤ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 7: necessary (P a b := not (a = 1 and b = ⊥); only case 7 covers that point)
theorem c5_106 : ¬ drop0% EReal.induction₂ 7 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (1 : EReal) ∧ b = (⊥ : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (1 : EReal) (⊥ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 8: necessary (P a b := not (a = 0 and b = ⊤); only case 8 covers that point)
theorem c5_107 : ¬ drop0% EReal.induction₂ 8 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (0 : EReal) ∧ b = (⊤ : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (0 : EReal) (⊤ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 9: necessary (P a b := not (a = 1 and b = 1); only case 9 covers that point)
theorem c5_108 : ¬ drop0% EReal.induction₂ 9 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (1 : EReal) ∧ b = (1 : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (1 : EReal) (1 : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 10: necessary (P a b := not (a = 0 and b = ⊥); only case 10 covers that point)
theorem c5_109 : ¬ drop0% EReal.induction₂ 10 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (0 : EReal) ∧ b = (⊥ : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (0 : EReal) (⊥ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 11: necessary (P a b := not (a = -1 and b = ⊤); only case 11 covers that point)
theorem c5_110 : ¬ drop0% EReal.induction₂ 11 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (-1 : EReal) ∧ b = (⊤ : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (-1 : EReal) (⊤ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 12: necessary (P a b := not (a = -1 and b = ⊥); only case 12 covers that point)
theorem c5_111 : ¬ drop0% EReal.induction₂ 12 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (-1 : EReal) ∧ b = (⊥ : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (-1 : EReal) (⊥ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 13: necessary (P a b := not (a = ⊥ and b = ⊤); only case 13 covers that point)
theorem c5_112 : ¬ drop0% EReal.induction₂ 13 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (⊥ : EReal) ∧ b = (⊤ : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊥ : EReal) (⊤ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 14: necessary (P a b := not (a = ⊥ and b = 1); only case 14 covers that point)
theorem c5_113 : ¬ drop0% EReal.induction₂ 14 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (⊥ : EReal) ∧ b = (1 : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊥ : EReal) (1 : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 15: necessary (P a b := not (a = ⊥ and b = 0); only case 15 covers that point)
theorem c5_114 : ¬ drop0% EReal.induction₂ 15 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (⊥ : EReal) ∧ b = (0 : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊥ : EReal) (0 : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 16: necessary (P a b := not (a = ⊥ and b = -1); only case 16 covers that point)
theorem c5_115 : ¬ drop0% EReal.induction₂ 16 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (⊥ : EReal) ∧ b = (-1 : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊥ : EReal) (-1 : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂` idx 17: necessary (P a b := not (a = ⊥ and b = ⊥); only case 17 covers that point)
theorem c5_116 : ¬ drop0% EReal.induction₂ 17 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (⊥ : EReal) ∧ b = (⊥ : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊥ : EReal) (⊥ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂_symm` idx 1: necessary (P a b := not (a = bot and b = top): all listed cases hold, P bot top fails)
theorem c5_131 : ¬ drop0% EReal.induction₂_symm 1 := fun h => by
  refine absurd (@h (fun a b => ¬(a = (⊥ : EReal) ∧ b = (⊤ : EReal))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊥ : EReal) (⊤ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂_symm` idx 2: necessary (symmetric P a b := not ((a, b) = (⊤, ⊤) or (b, a) = (⊤, ⊤)))
theorem c5_132 : ¬ drop0% EReal.induction₂_symm 2 := fun h => by
  refine absurd (@h (fun a b => ¬((a = (⊤ : EReal) ∧ b = (⊤ : EReal)) ∨ (a = (⊤ : EReal) ∧ b = (⊤ : EReal)))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊤ : EReal) (⊤ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂_symm` idx 3: necessary (symmetric P a b := not ((a, b) = (⊤, 1) or (b, a) = (⊤, 1)))
theorem c5_133 : ¬ drop0% EReal.induction₂_symm 3 := fun h => by
  refine absurd (@h (fun a b => ¬((a = (⊤ : EReal) ∧ b = (1 : EReal)) ∨ (a = (1 : EReal) ∧ b = (⊤ : EReal)))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊤ : EReal) (1 : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂_symm` idx 4: necessary (symmetric P a b := not ((a, b) = (⊤, 0) or (b, a) = (⊤, 0)))
theorem c5_134 : ¬ drop0% EReal.induction₂_symm 4 := fun h => by
  refine absurd (@h (fun a b => ¬((a = (⊤ : EReal) ∧ b = (0 : EReal)) ∨ (a = (0 : EReal) ∧ b = (⊤ : EReal)))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊤ : EReal) (0 : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂_symm` idx 5: necessary (symmetric P a b := not ((a, b) = (⊤, -1) or (b, a) = (⊤, -1)))
theorem c5_135 : ¬ drop0% EReal.induction₂_symm 5 := fun h => by
  refine absurd (@h (fun a b => ¬((a = (⊤ : EReal) ∧ b = (-1 : EReal)) ∨ (a = (-1 : EReal) ∧ b = (⊤ : EReal)))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊤ : EReal) (-1 : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂_symm` idx 6: necessary (symmetric P a b := not ((a, b) = (⊤, ⊥) or (b, a) = (⊤, ⊥)))
theorem c5_136 : ¬ drop0% EReal.induction₂_symm 6 := fun h => by
  refine absurd (@h (fun a b => ¬((a = (⊤ : EReal) ∧ b = (⊥ : EReal)) ∨ (a = (⊥ : EReal) ∧ b = (⊤ : EReal)))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊤ : EReal) (⊥ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂_symm` idx 7: necessary (symmetric P a b := not ((a, b) = (1, ⊥) or (b, a) = (1, ⊥)))
theorem c5_137 : ¬ drop0% EReal.induction₂_symm 7 := fun h => by
  refine absurd (@h (fun a b => ¬((a = (1 : EReal) ∧ b = (⊥ : EReal)) ∨ (a = (⊥ : EReal) ∧ b = (1 : EReal)))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (1 : EReal) (⊥ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂_symm` idx 9: necessary (symmetric P a b := not ((a, b) = (0, ⊥) or (b, a) = (0, ⊥)))
theorem c5_138 : ¬ drop0% EReal.induction₂_symm 9 := fun h => by
  refine absurd (@h (fun a b => ¬((a = (0 : EReal) ∧ b = (⊥ : EReal)) ∨ (a = (⊥ : EReal) ∧ b = (0 : EReal)))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (0 : EReal) (⊥ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂_symm` idx 10: necessary (symmetric P a b := not ((a, b) = (-1, ⊥) or (b, a) = (-1, ⊥)))
theorem c5_139 : ¬ drop0% EReal.induction₂_symm 10 := fun h => by
  refine absurd (@h (fun a b => ¬((a = (-1 : EReal) ∧ b = (⊥ : EReal)) ∨ (a = (⊥ : EReal) ∧ b = (-1 : EReal)))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (-1 : EReal) (⊥ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)
-- `EReal.induction₂_symm` idx 11: necessary (symmetric P a b := not ((a, b) = (⊥, ⊥) or (b, a) = (⊥, ⊥)))
theorem c5_140 : ¬ drop0% EReal.induction₂_symm 11 := fun h => by
  refine absurd (@h (fun a b => ¬((a = (⊥ : EReal) ∧ b = (⊥ : EReal)) ∨ (a = (⊥ : EReal) ∧ b = (⊥ : EReal)))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (⊥ : EReal) (⊥ : EReal)) (by simp)
  all_goals first | (intros; simp_all [er_ne]; done) | (intros; simp_all [er_ne]; linarith) | (intro x y hp hq; apply hp; tauto)

open Lean Meta Elab Term
namespace W1c5
theorem em1 : (-1 : EReal) = ((-1 : ℝ) : EReal) := by simp
/-- Numeral facts in EReal that norm_num does not decide (EReal is not an ordered semiring). -/
theorem ex : ((1 : EReal) ≤ 0 ↔ False) ∧ ((1 : EReal) < 0 ↔ False) ∧ ((0 : EReal) ≤ -1 ↔ False) ∧
    (-1 : EReal)⁻¹ = -1 ∧ (1 : EReal) + -1 = 0 ∧ (-1 : EReal) / -1 = 1 ∧
    (⊥ : EReal) / -1 = ⊤ ∧ (⊤ : EReal) / -1 = ⊥ := by
  have hi : (-1 : EReal)⁻¹ = -1 := by
    rw [em1, ← EReal.coe_inv]; norm_num
  refine ⟨?_, ?_, ?_, hi, ?_, ?_, ?_, ?_⟩
  · exact iff_false_intro (not_le.2 zero_lt_one)
  · exact iff_false_intro (not_lt.2 zero_le_one)
  · rw [em1, ← EReal.coe_zero, EReal.coe_le_coe_iff]; norm_num
  · rw [em1, ← EReal.coe_one, ← EReal.coe_add]; norm_num
  · rw [div_eq_mul_inv, hi, em1, ← EReal.coe_mul]; norm_num
  · rw [div_eq_mul_inv, hi]; exact EReal.bot_mul_of_neg (by rw [em1]; exact_mod_cast (by norm_num : (-1:ℝ) < 0))
  · rw [div_eq_mul_inv, hi]; exact EReal.top_mul_of_neg (by rw [em1]; exact_mod_cast (by norm_num : (-1:ℝ) < 0))
end W1c5
open W1c5
open Lean Meta Elab Term
-- `EReal.coe_le_coe` idx 2: necessary (x = 1, y = 0)
theorem c5_81 : ¬ drop0% EReal.coe_le_coe 2 := fun h => by
  have := @h 1 0; norm_num [ex] at this
-- `EReal.toReal_nonneg` idx 1: necessary (x = -1)
theorem c5_82 : ¬ drop0% EReal.toReal_nonneg 1 := fun h => by
  have := @h (-1); norm_num [ex] at this
-- `EReal.toReal_le_toReal` idx 3: necessary (x = bot, y = -1: toReal bot = 0 > -1)
theorem c5_83 : ¬ drop0% EReal.toReal_le_toReal 3 := fun h => by
  have := @h ⊥ (-1) bot_le (by decide); norm_num [ex] at this
-- `EReal.toReal_toENNReal` idx 1: necessary (x = -1: toENNReal (-1) = 0)
theorem c5_84 : ¬ drop0% EReal.toReal_toENNReal 1 := fun h => by
  have := @h (-1); norm_num [ex] at this
-- `EReal.toENNReal_lt_toENNReal` idx 2: necessary (x = -2, y = -1: both toENNReal are 0)
theorem c5_85 : ¬ drop0% EReal.toENNReal_lt_toENNReal 2 := fun h => by
  have := @h (-2) (-1) (by norm_num); norm_num [ex] at this
-- `EReal.sum_mul_of_nonneg` idx 4: necessary (f = (1, -1) on Bool, a = top: (1 + -1) * top = 0, top + bot = bot)
theorem c5_86 : ¬ drop0% EReal.sum_mul_of_nonneg 4 := fun h => by
  have := @h Bool Finset.univ (fun b => if b then 1 else -1) ⊤
  norm_num [ex] at this
-- `EReal.mul_sum_of_nonneg` idx 4: necessary (f = (1, -1) on Bool, a = top)
theorem c5_87 : ¬ drop0% EReal.mul_sum_of_nonneg 4 := fun h => by
  have := @h Bool Finset.univ (fun b => if b then 1 else -1) ⊤
  norm_num [ex] at this
-- `EReal.mul_sum_of_nonneg_of_ne_top` idx 4: necessary (a = -1, f = (top, bot): -1 * (top + bot) = top, bot + top = bot)
theorem c5_88 : ¬ drop0% EReal.mul_sum_of_nonneg_of_ne_top 4 := fun h => by
  have := @h Bool Finset.univ (fun b => if b then ⊤ else ⊥) (-1) (by decide)
  norm_num [ex] at this
-- `EReal.mul_sum_of_nonneg_of_ne_top` idx 5: necessary (a = top, f = (1, -1): top * 0 = 0, top + bot = bot)
theorem c5_89 : ¬ drop0% EReal.mul_sum_of_nonneg_of_ne_top 5 := fun h => by
  have := @h Bool Finset.univ (fun b => if b then 1 else -1) ⊤ le_top
  norm_num [ex] at this
-- `EReal.sum_mul_of_nonneg_of_ne_top` idx 4: necessary (a = -1, f = (top, bot))
theorem c5_90 : ¬ drop0% EReal.sum_mul_of_nonneg_of_ne_top 4 := fun h => by
  have := @h Bool Finset.univ (fun b => if b then ⊤ else ⊥) (-1) (by decide)
  norm_num [ex] at this
-- `EReal.sum_mul_of_nonneg_of_ne_top` idx 5: necessary (a = top, f = (1, -1))
theorem c5_91 : ¬ drop0% EReal.sum_mul_of_nonneg_of_ne_top 5 := fun h => by
  have := @h Bool Finset.univ (fun b => if b then 1 else -1) ⊤ le_top
  norm_num [ex] at this
-- `EReal.mul_le_mul_of_nonpos_right` idx 3: necessary (a = 0, b = 1, c = -1)
theorem c5_92 : ¬ drop0% EReal.mul_le_mul_of_nonpos_right 3 := fun h => by
  have := @h 0 1 (-1) (by norm_num); norm_num [ex] at this
-- `EReal.exists_nat_ge_mul` idx 1: necessary (a = top, n = 1: top * 1 = top is not below any natural)
theorem c5_93 : ¬ drop0% EReal.exists_nat_ge_mul 1 := fun h => by
  obtain ⟨m, hm⟩ := @h ⊤ 1; norm_num [ex] at hm
-- `EReal.inv_nonneg_of_nonneg` idx 1: necessary (a = -1: inverse -1)
theorem c5_94 : ¬ drop0% EReal.inv_nonneg_of_nonneg 1 := fun h => by
  have := @h (-1); norm_num [ex] at this
-- `EReal.div_mul_div_cancel` idx 3: necessary (a = c = 1, b = bot: 1 / bot = 0)
theorem c5_95 : ¬ drop0% EReal.div_mul_div_cancel 3 := fun h => by
  have := @h 1 ⊥ 1 (by decide) (by decide); norm_num [ex] at this
-- `EReal.div_mul_div_cancel` idx 4: necessary (a = c = 1, b = top: 1 / top = 0)
theorem c5_96 : ¬ drop0% EReal.div_mul_div_cancel 4 := fun h => by
  have := @h 1 ⊤ 1 (by decide) (by decide); norm_num [ex] at this
-- `EReal.mul_div_mul_cancel` idx 3: necessary (a = b = 1, c = bot: bot / bot = 0)
theorem c5_97 : ¬ drop0% EReal.mul_div_mul_cancel 3 := fun h => by
  have := @h 1 1 ⊥ (by decide) (by decide); norm_num [ex] at this
-- `EReal.mul_div_mul_cancel` idx 4: necessary (a = b = 1, c = top: top / top = 0)
theorem c5_98 : ¬ drop0% EReal.mul_div_mul_cancel 4 := fun h => by
  have := @h 1 1 ⊤ (by decide) (by decide); norm_num [ex] at this
-- `EReal.mul_div_mul_cancel` idx 5: necessary (a = b = 1, c = 0: 0 / 0 = 0)
theorem c5_99 : ¬ drop0% EReal.mul_div_mul_cancel 5 := fun h => by
  have := @h 1 1 0 (by decide) (by decide); norm_num [ex] at this
-- `EReal.monotone_div_right_of_nonneg` idx 1: necessary (b = -1: 0 <= 1 but 0 / -1 > 1 / -1)
theorem c5_160 : ¬ drop0% EReal.monotone_div_right_of_nonneg 1 := fun h => by
  have := @h (-1) 0 1 (by norm_num); norm_num [ex] at this
-- `EReal.div_le_div_right_of_nonneg` idx 3: necessary (c = -1, a = 0, b = 1)
theorem c5_161 : ¬ drop0% EReal.div_le_div_right_of_nonneg 3 := fun h => by
  have := @h 0 1 (-1) (by norm_num); norm_num [ex] at this
-- `EReal.strictMono_div_right_of_pos` idx 2: necessary (b = top: x / top = 0 for all x)
theorem c5_162 : ¬ drop0% EReal.strictMono_div_right_of_pos 2 := fun h => by
  have := @h ⊤ (by decide) 0 1 (by norm_num); norm_num [ex] at this
-- `EReal.div_lt_div_right_of_pos` idx 4: necessary (c = top, a = 0, b = 1: both quotients 0)
theorem c5_163 : ¬ drop0% EReal.div_lt_div_right_of_pos 4 := fun h => by
  have := @h 0 1 ⊤ (by decide) (by norm_num); norm_num [ex] at this
-- `EReal.div_le_div_right_of_nonpos` idx 4: necessary (c = -1, a = 1, b = 0)
theorem c5_164 : ¬ drop0% EReal.div_le_div_right_of_nonpos 4 := fun h => by
  have := @h 1 0 (-1) (by norm_num); norm_num [ex] at this
-- `EReal.strictAnti_div_right_of_neg` idx 2: necessary (b = bot: x / bot = 0 for all x)
theorem c5_165 : ¬ drop0% EReal.strictAnti_div_right_of_neg 2 := fun h => by
  have := @h ⊥ (by decide) 0 1 (by norm_num); norm_num [ex] at this
-- `EReal.div_lt_div_right_of_neg` idx 4: necessary (c = bot, a = 0, b = 1: both quotients 0)
theorem c5_166 : ¬ drop0% EReal.div_lt_div_right_of_neg 4 := fun h => by
  have := @h 0 1 ⊥ (by decide) (by norm_num); norm_num [ex] at this
-- `EReal.div_lt_div_right_of_neg` idx 5: necessary (a = b = 0, c = -1)
theorem c5_167 : ¬ drop0% EReal.div_lt_div_right_of_neg 5 := fun h => by
  have := @h 0 0 (-1) (by norm_num) (by decide); norm_num [ex] at this
-- `EReal.le_div_iff_mul_le` idx 4: necessary (b = top, a = 1, c = top: 1 <= top / top = 0 fails, 1 * top <= top holds)
theorem c5_168 : ¬ drop0% EReal.le_div_iff_mul_le 4 := fun h => by
  have := @h 1 ⊤ ⊤ (by decide); norm_num [ex] at this
-- `EReal.div_le_iff_le_mul` idx 4: necessary (b = top, a = top, c = 0: top / top = 0 <= 0 holds, top <= top * 0 = 0 fails)
theorem c5_169 : ¬ drop0% EReal.div_le_iff_le_mul 4 := fun h => by
  have := @h ⊤ ⊤ 0 (by decide); norm_num [ex] at this
-- `EReal.lt_div_iff` idx 4: necessary (b = top, a = -1, c = bot: -1 < bot / top = 0 holds, -1 * top = bot < bot fails)
theorem c5_170 : ¬ drop0% EReal.lt_div_iff 4 := fun h => by
  have := @h (-1) ⊤ ⊥ (by decide); norm_num [ex] at this
-- `EReal.div_lt_iff` idx 4: necessary (c = top, b = top, a = 1: top / top = 0 < 1 holds, top < 1 * top fails)
theorem c5_171 : ¬ drop0% EReal.div_lt_iff 4 := fun h => by
  have := @h 1 ⊤ ⊤ (by decide); norm_num [ex] at this
-- `EReal.div_nonneg` idx 3: necessary (a = 1, b = -1)
theorem c5_172 : ¬ drop0% EReal.div_nonneg 3 := fun h => by
  have := @h 1 (-1) (by norm_num); norm_num [ex] at this
-- `EReal.div_pos` idx 4: necessary (a = 1, b = top: 1 / top = 0)
theorem c5_173 : ¬ drop0% EReal.div_pos 4 := fun h => by
  have := @h 1 ⊤ (by norm_num) (by decide); norm_num [ex] at this
-- `EReal.div_nonpos_of_nonpos_of_nonneg` idx 3: necessary (a = b = -1: quotient 1)
theorem c5_174 : ¬ drop0% EReal.div_nonpos_of_nonpos_of_nonneg 3 := fun h => by
  have := @h (-1) (-1) (by norm_num); norm_num [ex] at this
-- `EReal.div_nonpos_of_nonneg_of_nonpos` idx 2: necessary (a = b = -1: quotient 1)
theorem c5_175 : ¬ drop0% EReal.div_nonpos_of_nonneg_of_nonpos 2 := fun h => by
  have := @h (-1) (-1) (by norm_num); norm_num [ex] at this
-- `EReal.div_nonneg_of_nonpos_of_nonpos` idx 2: necessary (a = 1, b = -1)
theorem c5_176 : ¬ drop0% EReal.div_nonneg_of_nonpos_of_nonpos 2 := fun h => by
  have := @h 1 (-1) (by norm_num); norm_num [ex] at this
-- `_private.Mathlib.Data.EReal.Inv.0.EReal.exists_lt_mul_left_of_nonneg` idx 3: necessary (a = -1, b = bot, c = 0: a * b = top > 0 but Ioo 0 (-1) is empty)
theorem c5_177 : ¬ drop0% _private.Mathlib.Data.EReal.Inv.«0».EReal.exists_lt_mul_left_of_nonneg 3 := fun h => by
  obtain ⟨a', ha', _⟩ := @h (-1) ⊥ 0 le_rfl (by norm_num)
  have := ha'.1.trans ha'.2; norm_num [ex] at this
-- `_private.Mathlib.Data.EReal.Inv.0.EReal.exists_lt_mul_left_of_nonneg` idx 4: necessary (a = b = 0, c = -1: c < 0 = a * b but Ioo 0 0 is empty)
theorem c5_178 : ¬ drop0% _private.Mathlib.Data.EReal.Inv.«0».EReal.exists_lt_mul_left_of_nonneg 4 := fun h => by
  obtain ⟨a', ha', _⟩ := @h 0 0 (-1) le_rfl (by norm_num)
  have := ha'.1.trans ha'.2; norm_num [ex] at this
-- `_private.Mathlib.Data.EReal.Inv.0.EReal.exists_lt_mul_right_of_nonneg` idx 4: necessary (a = 1, b = 0, c = -1: Ioo 0 0 is empty)
theorem c5_179 : ¬ drop0% _private.Mathlib.Data.EReal.Inv.«0».EReal.exists_lt_mul_right_of_nonneg 4 := fun h => by
  obtain ⟨b', hb', _⟩ := @h 1 0 (-1) (by norm_num) (by norm_num)
  have := hb'.1.trans hb'.2; norm_num [ex] at this
-- `_private.Mathlib.Data.EReal.Inv.0.EReal.exists_mul_left_lt` idx 3: necessary (a = 0, b = top, c = 1: a * b = 0 < 1, but a' > 0 gives a' * top = top)
theorem c5_180 : ¬ drop0% _private.Mathlib.Data.EReal.Inv.«0».EReal.exists_mul_left_lt 3 := fun h => by
  obtain ⟨a', ha', hl⟩ := @h 0 ⊤ 1 (by decide) (by norm_num)
  rw [EReal.mul_top_of_pos ha'.1] at hl; norm_num [ex] at hl
-- `_private.Mathlib.Data.EReal.Inv.0.EReal.exists_mul_left_lt` idx 4: necessary (a = top, b = 0, c = 1: Ioo top top is empty)
theorem c5_181 : ¬ drop0% _private.Mathlib.Data.EReal.Inv.«0».EReal.exists_mul_left_lt 4 := fun h => by
  obtain ⟨a', ha', _⟩ := @h ⊤ 0 1 (by decide) (by norm_num)
  have := ha'.1.trans ha'.2; norm_num [ex] at this
-- `_private.Mathlib.Data.EReal.Inv.0.EReal.exists_mul_right_lt` idx 3: necessary (a = 0, b = top, c = 1: Ioo top top is empty)
theorem c5_182 : ¬ drop0% _private.Mathlib.Data.EReal.Inv.«0».EReal.exists_mul_right_lt 3 := fun h => by
  obtain ⟨b', hb', _⟩ := @h 0 ⊤ 1 (by decide) (by norm_num)
  have := hb'.1.trans hb'.2; norm_num [ex] at this
-- `_private.Mathlib.Data.EReal.Inv.0.EReal.exists_mul_right_lt` idx 4: necessary (a = top, b = 0, c = 1: b' > 0 gives top * b' = top)
theorem c5_183 : ¬ drop0% _private.Mathlib.Data.EReal.Inv.«0».EReal.exists_mul_right_lt 4 := fun h => by
  obtain ⟨b', hb', hl⟩ := @h ⊤ 0 1 (by decide) (by norm_num)
  rw [EReal.top_mul_of_pos hb'.1] at hl; norm_num [ex] at hl
-- `EReal.le_mul_of_forall_lt` idx 3: necessary (a = 0, b = top, c = 1: no b' > top, so the bound is vacuous; 1 <= 0 * top = 0 fails)
theorem c5_184 : ¬ drop0% EReal.le_mul_of_forall_lt 3 := fun h => by
  have := @h 0 ⊤ 1 (by decide) (fun a' _ b' hb => absurd hb (not_lt.2 le_top)); norm_num [ex] at this
-- `EReal.le_mul_of_forall_lt` idx 4: necessary (a = top, b = 0, c = 1: no a' > top; 1 <= top * 0 = 0 fails)
theorem c5_185 : ¬ drop0% EReal.le_mul_of_forall_lt 4 := fun h => by
  have := @h ⊤ 0 1 (by decide) (fun a' ha => absurd ha (not_lt.2 le_top)); norm_num [ex] at this
-- `EReal.mul_le_of_forall_lt_of_nonneg` idx 3: necessary (a = -1, b = bot, c = 0: Ioo 0 (-1) is empty; -1 * bot = top <= 0 fails)
theorem c5_186 : ¬ drop0% EReal.mul_le_of_forall_lt_of_nonneg 3 := fun h => by
  have := @h (-1) ⊥ 0 le_rfl (fun a' ha => by have := ha.1.trans ha.2; norm_num [ex] at this); norm_num [ex] at this
-- `EReal.div_right_distrib_of_nonneg` idx 3: necessary (a = bot, b = top, c = -1: (bot + top) / -1 = top, bot / -1 + top / -1 = top + bot = bot)
theorem c5_187 : ¬ drop0% EReal.div_right_distrib_of_nonneg 3 := fun h => by
  have := @h ⊥ ⊤ (-1) le_top; norm_num [ex] at this
-- `EReal.div_right_distrib_of_nonneg` idx 4: necessary (a = top, b = bot, c = -1)
theorem c5_188 : ¬ drop0% EReal.div_right_distrib_of_nonneg 4 := fun h => by
  have := @h ⊤ ⊥ (-1) le_top; norm_num [ex] at this
-- `EReal.add_div_of_nonneg_right` idx 3: necessary (a = bot, b = top, c = -1)
theorem c5_189 : ¬ drop0% EReal.add_div_of_nonneg_right 3 := fun h => by
  have := @h ⊥ ⊤ (-1); norm_num [ex] at this
