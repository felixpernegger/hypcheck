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
namespace W1c6
open EReal
-- small EReal facts at the values 1 and -1 (simp cannot see them through the numerals)
theorem one_ne_top' : (1:EReal) ≠ ⊤ := EReal.coe_ne_top 1
theorem one_ne_bot' : (1:EReal) ≠ ⊥ := EReal.coe_ne_bot 1
theorem neg_one_ne_top' : (-1:EReal) ≠ ⊤ := EReal.coe_ne_top (-1)
theorem neg_one_ne_bot' : (-1:EReal) ≠ ⊥ := EReal.coe_ne_bot (-1)
theorem one_sub_one' : (1:EReal) - 1 = 0 := by
  rw [← EReal.coe_one, ← EReal.coe_sub]; simp
theorem one_add_neg_one' : (1:EReal) + -1 = 0 := by
  rw [← EReal.coe_one, ← EReal.coe_neg, ← EReal.coe_add]; simp
theorem neg_one_sub_neg_one' : (-1:EReal) - -1 = 0 := by
  rw [← EReal.coe_one, ← EReal.coe_neg, ← EReal.coe_sub]; simp
theorem neg_one_add_one' : (-1:EReal) + 1 = 0 := by
  rw [← EReal.coe_one, ← EReal.coe_neg, ← EReal.coe_add]; simp
theorem top_mul_neg_one' : (⊤:EReal) * -1 = ⊥ := by
  rw [← EReal.coe_one, ← EReal.coe_neg]; exact EReal.top_mul_coe_of_neg (by norm_num)
theorem neg_one_mul_top' : (-1:EReal) * ⊤ = ⊥ := by
  rw [← EReal.coe_one, ← EReal.coe_neg]; exact EReal.coe_mul_top_of_neg (by norm_num)
theorem neg_one_mul_bot' : (-1:EReal) * ⊥ = ⊤ := by
  rw [← EReal.coe_one, ← EReal.coe_neg]; exact EReal.coe_mul_bot_of_neg (by norm_num)
theorem bot_mul_neg_one' : (⊥:EReal) * -1 = ⊤ := by
  rw [← EReal.coe_one, ← EReal.coe_neg]; exact EReal.bot_mul_coe_of_neg (by norm_num)
attribute [simp] one_ne_top' one_ne_bot' neg_one_ne_top' neg_one_ne_bot' one_sub_one' one_add_neg_one'
  neg_one_sub_neg_one' neg_one_add_one' top_mul_neg_one' neg_one_mul_top' neg_one_mul_bot' bot_mul_neg_one'
theorem top_ne_one' : (⊤:EReal) ≠ 1 := one_ne_top'.symm
theorem bot_ne_one' : (⊥:EReal) ≠ 1 := one_ne_bot'.symm
theorem top_ne_neg_one' : (⊤:EReal) ≠ -1 := neg_one_ne_top'.symm
theorem bot_ne_neg_one' : (⊥:EReal) ≠ -1 := neg_one_ne_bot'.symm
theorem zero_ne_neg_one' : (0:EReal) ≠ -1 := by
  rw [← EReal.coe_one, ← EReal.coe_neg, ← EReal.coe_zero, Ne, EReal.coe_eq_coe_iff]; norm_num
theorem coe_eq_neg_one' (x : ℝ) : (x:EReal) = -1 ↔ x = -1 := by
  rw [← EReal.coe_one, ← EReal.coe_neg, EReal.coe_eq_coe_iff]
theorem coe_eq_one' (x : ℝ) : (x:EReal) = 1 ↔ x = 1 := by
  rw [← EReal.coe_one, EReal.coe_eq_coe_iff]
attribute [simp] top_ne_one' bot_ne_one' top_ne_neg_one' bot_ne_neg_one' zero_ne_neg_one' coe_eq_neg_one' coe_eq_one'
end W1c6

-- `EReal.add_pos_of_pos_of_nonneg` idx 3: necessary (a = 1, b = ⊥)
theorem w6_1 : ¬ drop0% EReal.add_pos_of_pos_of_nonneg 3 := fun h => absurd (@h 1 ⊥ (by simp)) (by simp)
-- `EReal.toReal_add` idx 2: necessary (x = ⊤, y = 1)
theorem w6_2 : ¬ drop0% EReal.toReal_add 2 := fun h => absurd (@h ⊤ 1 (by simp) (by simp) (by simp)) (by simp)
-- `EReal.toReal_add` idx 4: necessary (x = 1, y = ⊤)
theorem w6_3 : ¬ drop0% EReal.toReal_add 4 := fun h => absurd (@h 1 ⊤ (by simp) (by simp) (by simp)) (by simp)
-- `EReal.add_lt_add` idx 4: necessary (x = y = ⊤, z = 0, t = 1)
theorem w6_4 : ¬ drop0% EReal.add_lt_add 4 := fun h => absurd (@h ⊤ ⊤ 0 1 (by simp)) (by simp)
-- `EReal.add_lt_add` idx 5: necessary (x = 0, y = 1, z = t = ⊤)
theorem w6_5 : ¬ drop0% EReal.add_lt_add 5 := fun h => absurd (@h 0 1 ⊤ ⊤ (by simp)) (by simp)
-- `EReal.add_lt_add_of_lt_of_le'` idx 5: necessary (x = 0, y = 1, z = 1, t = 0)
theorem w6_6 : ¬ drop0% EReal.add_lt_add_of_lt_of_le' 5 := fun h => absurd (@h 0 1 1 0 (by simp) (by simp) (by simp)) (by norm_num)
-- `EReal.add_lt_add_of_lt_of_le'` idx 6: necessary (x = 0, y = 1, z = t = ⊥)
theorem w6_7 : ¬ drop0% EReal.add_lt_add_of_lt_of_le' 6 := fun h => absurd (@h 0 1 ⊥ ⊥ (by simp) (by simp) (by simp)) (by simp)
-- `EReal.add_lt_add_of_lt_of_le'` idx 7: necessary (x = 0, y = 1, z = t = ⊤)
theorem w6_8 : ¬ drop0% EReal.add_lt_add_of_lt_of_le' 7 := fun h => absurd (@h 0 1 ⊤ ⊤ (by simp) (by simp) (by simp)) (by simp)
-- `EReal.add_lt_add_of_lt_of_le` idx 5: necessary (x = 0, y = 1, z = 1, t = 0)
theorem w6_9 : ¬ drop0% EReal.add_lt_add_of_lt_of_le 5 := fun h => absurd (@h 0 1 1 0 (by simp) (by simp) (by simp)) (by norm_num)
-- `EReal.add_lt_add_of_lt_of_le` idx 6: necessary (x = 0, y = 1, z = t = ⊥)
theorem w6_10 : ¬ drop0% EReal.add_lt_add_of_lt_of_le 6 := fun h => absurd (@h 0 1 ⊥ ⊥ (by simp) (by simp) (by simp)) (by simp)
-- `EReal.add_lt_add_of_lt_of_le` idx 7: necessary (x = 0, y = 1, z = t = ⊤)
theorem w6_11 : ¬ drop0% EReal.add_lt_add_of_lt_of_le 7 := fun h => absurd (@h 0 1 ⊤ ⊤ (by simp) (by simp) (by simp)) (by simp)
-- `EReal.recENNReal_neg_coe_ennreal` idx 4: necessary (x = 0)
theorem w6_12 : ¬ indep0% EReal.recENNReal_neg_coe_ennreal 4 := fun h => absurd (@h (fun _ => True) (fun _ => trivial) (fun _ _ => trivial) 0) (by simp)
-- `EReal.sub_lt_sub_of_lt_of_le` idx 5: necessary (x = 0, y = 1, z = 1, t = 0)
theorem w6_13 : ¬ drop0% EReal.sub_lt_sub_of_lt_of_le 5 := fun h => absurd (@h 0 1 1 0 (by simp) (by simp) (by simp)) (by norm_num)
-- `EReal.sub_lt_sub_of_lt_of_le` idx 6: necessary (x = 0, y = 1, z = t = ⊥)
theorem w6_14 : ¬ drop0% EReal.sub_lt_sub_of_lt_of_le 6 := fun h => absurd (@h 0 1 ⊥ ⊥ (by simp) (by simp) (by simp)) (by simp)
-- `EReal.sub_lt_sub_of_lt_of_le` idx 7: necessary (x = 0, y = 1, z = t = ⊤)
theorem w6_15 : ¬ drop0% EReal.sub_lt_sub_of_lt_of_le 7 := fun h => absurd (@h 0 1 ⊤ ⊤ (by simp) (by simp) (by simp)) (by simp)
-- `EReal.toReal_sub` idx 2: necessary (x = ⊤, y = 1)
theorem w6_16 : ¬ drop0% EReal.toReal_sub 2 := fun h => absurd (@h ⊤ 1 (by simp) (by simp) (by simp)) (by simp)
-- `EReal.toReal_sub` idx 5: necessary (x = 1, y = ⊥)
theorem w6_17 : ¬ drop0% EReal.toReal_sub 5 := fun h => absurd (@h 1 ⊥ (by simp) (by simp) (by simp)) (by simp)
-- `EReal.add_sub_add_comm` idx 4: necessary (a = b = 0, c = ⊥, d = ⊤)
theorem w6_18 : ¬ drop0% EReal.add_sub_add_comm 4 := fun h => absurd (@h 0 0 ⊥ ⊤ (by simp)) (by simp)
-- `EReal.add_sub_add_comm` idx 5: necessary (a = b = 0, c = ⊤, d = ⊥)
theorem w6_19 : ¬ drop0% EReal.add_sub_add_comm 5 := fun h => absurd (@h 0 0 ⊤ ⊥ (by simp)) (by simp)
-- `EReal.le_sub_iff_add_le` idx 4: necessary (a = 0, b = c = ⊤)
theorem w6_20 : ¬ drop0% EReal.le_sub_iff_add_le 4 := fun h => absurd (@h 0 ⊤ ⊤ (by simp)) (by simp)
-- `EReal.sub_le_iff_le_add` idx 3: necessary (a = 0, b = ⊥, c = ⊤)
theorem w6_21 : ¬ drop0% EReal.sub_le_iff_le_add 3 := fun h => absurd (@h 0 ⊥ ⊤ (by simp)) (by simp)
-- `EReal.sub_le_iff_le_add` idx 4: necessary (a = 0, b = ⊤, c = ⊥)
theorem w6_22 : ¬ drop0% EReal.sub_le_iff_le_add 4 := fun h => absurd (@h 0 ⊤ ⊥ (by simp)) (by simp)
-- `EReal.lt_sub_iff_add_lt` idx 3: necessary (a = 0, b = ⊥, c = ⊤)
theorem w6_23 : ¬ drop0% EReal.lt_sub_iff_add_lt 3 := fun h => absurd (@h 0 ⊥ ⊤ (by simp)) (by simp)
-- `EReal.lt_sub_iff_add_lt` idx 4: necessary (a = 0, b = ⊤, c = ⊥)
theorem w6_24 : ¬ drop0% EReal.lt_sub_iff_add_lt 4 := fun h => absurd (@h 0 ⊤ ⊥ (by simp)) (by simp)
-- `EReal.sub_lt_iff` idx 3: necessary (a = 0, b = c = ⊥)
theorem w6_25 : ¬ drop0% EReal.sub_lt_iff 3 := fun h => absurd (@h 0 ⊥ ⊥ (by simp)) (by simp)
-- `EReal.sub_lt_iff` idx 4: necessary (a = 0, b = c = ⊤)
theorem w6_26 : ¬ drop0% EReal.sub_lt_iff 4 := fun h => absurd (@h 0 ⊤ ⊤ (by simp)) (by simp)
-- `EReal.sub_lt_sub_of_le_of_gt` idx 4: necessary (x = 1, y = 0, z = 0, t = 1)
theorem w6_27 : ¬ drop0% EReal.sub_lt_sub_of_le_of_gt 4 := fun h => absurd (@h 1 0 0 1 (by simp) (by simp) (by simp)) (by norm_num)
-- `EReal.sub_lt_sub_of_le_of_gt` idx 6: necessary (x = y = ⊤, z = 0, t = 1)
theorem w6_28 : ¬ drop0% EReal.sub_lt_sub_of_le_of_gt 6 := fun h => absurd (@h ⊤ ⊤ 0 1 (by simp) (by simp) (by simp)) (by simp)
-- `EReal.sub_lt_sub_of_le_of_gt` idx 7: necessary (x = y = ⊥, z = 0, t = 1)
theorem w6_29 : ¬ drop0% EReal.sub_lt_sub_of_le_of_gt 7 := fun h => absurd (@h ⊥ ⊥ 0 1 (by simp) (by simp) (by simp)) (by simp)
-- `_private.Mathlib.Data.EReal.Operations.0.EReal.exists_lt_add_right` idx 3: necessary (b = ⊥)
theorem w6_30 : ¬ drop0% _private.Mathlib.Data.EReal.Operations.«0».EReal.exists_lt_add_right 3 := fun h => by
  obtain ⟨b', hb, -⟩ := @h ⊥ ⊥ ⊥
  exact not_lt_bot hb
-- `EReal.le_add_of_forall_gt` idx 3: necessary (a = ⊥, b = ⊤, c = 0)
theorem w6_31 : ¬ drop0% EReal.le_add_of_forall_gt 3 := fun h => absurd (@h ⊥ ⊤ 0 (by simp) (fun _ _ b' hb' => absurd hb' (not_lt_of_ge le_top))) (by simp)
-- `EReal.le_add_of_forall_gt` idx 4: necessary (a = ⊤, b = ⊥, c = 0)
theorem w6_32 : ¬ drop0% EReal.le_add_of_forall_gt 4 := fun h => absurd (@h ⊤ ⊥ 0 (by simp) (fun a' ha' _ _ => absurd ha' (not_lt_of_ge le_top))) (by simp)
-- `ENNReal.toEReal_sub` idx 3: necessary (x = 0, y = 1)
theorem w6_33 : ¬ drop0% ENNReal.toEReal_sub 3 := fun h => by
  have := congrArg EReal.toReal (@h 0 1 (by simp)); norm_num at this
-- `EReal.coe_mul_top_of_pos` idx 1: necessary (x = 0)
theorem w6_34 : ¬ drop0% EReal.coe_mul_top_of_pos 1 := fun h => absurd (@h 0) (by simp)
-- `EReal.coe_mul_top_of_neg` idx 1: necessary (x = 0)
theorem w6_35 : ¬ drop0% EReal.coe_mul_top_of_neg 1 := fun h => absurd (@h 0) (by simp)
-- `EReal.top_mul_coe_of_pos` idx 1: necessary (x = 0)
theorem w6_36 : ¬ drop0% EReal.top_mul_coe_of_pos 1 := fun h => absurd (@h 0) (by simp)
-- `EReal.top_mul_coe_of_neg` idx 1: necessary (x = 0)
theorem w6_37 : ¬ drop0% EReal.top_mul_coe_of_neg 1 := fun h => absurd (@h 0) (by simp)
-- `EReal.coe_mul_bot_of_pos` idx 1: necessary (x = 0)
theorem w6_38 : ¬ drop0% EReal.coe_mul_bot_of_pos 1 := fun h => absurd (@h 0) (by simp)
-- `EReal.coe_mul_bot_of_neg` idx 1: necessary (x = 0)
theorem w6_39 : ¬ drop0% EReal.coe_mul_bot_of_neg 1 := fun h => absurd (@h 0) (by simp)
-- `EReal.bot_mul_coe_of_pos` idx 1: necessary (x = 0)
theorem w6_40 : ¬ drop0% EReal.bot_mul_coe_of_pos 1 := fun h => absurd (@h 0) (by simp)
-- `EReal.bot_mul_coe_of_neg` idx 1: necessary (x = 0)
theorem w6_41 : ¬ drop0% EReal.bot_mul_coe_of_neg 1 := fun h => absurd (@h 0) (by simp)
-- `EReal.toENNReal_mul` idx 2: necessary (x = y = -1)
theorem w6_42 : ¬ drop0% EReal.toENNReal_mul 2 := fun h => absurd (@h (-1) (-1)) (by norm_num [ENNReal.ofReal_of_nonpos])
-- `EReal.toENNReal_mul'` idx 2: necessary (x = y = -1)
theorem w6_43 : ¬ drop0% EReal.toENNReal_mul' 2 := fun h => absurd (@h (-1) (-1)) (by norm_num [ENNReal.ofReal_of_nonpos])
-- `EReal.right_distrib_of_nonneg` idx 3: necessary (a = -1, b = 1, c = ⊤)
theorem w6_44 : ¬ drop0% EReal.right_distrib_of_nonneg 3 := fun h => absurd (@h (-1) 1 ⊤ (by simp)) (by norm_num)
-- `EReal.right_distrib_of_nonneg` idx 4: necessary (a = 1, b = -1, c = ⊤)
theorem w6_45 : ¬ drop0% EReal.right_distrib_of_nonneg 4 := fun h => absurd (@h 1 (-1) ⊤ (by simp)) (by norm_num)
-- `EReal.left_distrib_of_nonneg` idx 3: necessary (a = -1, b = 1, c = ⊤)
theorem w6_46 : ¬ drop0% EReal.left_distrib_of_nonneg 3 := fun h => absurd (@h (-1) 1 ⊤ (by simp)) (by norm_num)
-- `EReal.left_distrib_of_nonneg` idx 4: necessary (a = 1, b = -1, c = ⊤)
theorem w6_47 : ¬ drop0% EReal.left_distrib_of_nonneg 4 := fun h => absurd (@h 1 (-1) ⊤ (by simp)) (by norm_num)
-- `EReal.mul_sub_of_nonneg_of_nonpos` idx 3: necessary (a = ⊤, b = c = -1)
theorem w6_48 : ¬ drop0% EReal.mul_sub_of_nonneg_of_nonpos 3 := fun h => absurd (@h ⊤ (-1) (-1) (by norm_num)) (by norm_num)
-- `EReal.mul_sub_of_nonneg_of_nonpos` idx 4: necessary (a = ⊤, b = c = 1)
theorem w6_49 : ¬ drop0% EReal.mul_sub_of_nonneg_of_nonpos 4 := fun h => absurd (@h ⊤ 1 1 (by norm_num)) (by norm_num)
-- `EReal.left_distrib_of_nonneg_of_ne_top` idx 1: necessary (x = -1, y = ⊤, z = ⊥)
theorem w6_50 : ¬ drop0% EReal.left_distrib_of_nonneg_of_ne_top 1 := fun h => absurd (@h (-1) (by simp) ⊤ ⊥) (by norm_num)
-- `EReal.left_distrib_of_nonneg_of_ne_top` idx 2: necessary (x = ⊤, y = 1, z = -1)
theorem w6_51 : ¬ drop0% EReal.left_distrib_of_nonneg_of_ne_top 2 := fun h => absurd (@h ⊤ (by simp) 1 (-1)) (by norm_num)
-- `EReal.right_distrib_of_nonneg_of_ne_top` idx 1: necessary (x = -1, y = ⊤, z = ⊥)
theorem w6_52 : ¬ drop0% EReal.right_distrib_of_nonneg_of_ne_top 1 := fun h => absurd (@h (-1) (by simp) ⊤ ⊥) (by norm_num)
-- `EReal.right_distrib_of_nonneg_of_ne_top` idx 2: necessary (x = ⊤, y = 1, z = -1)
theorem w6_53 : ¬ drop0% EReal.right_distrib_of_nonneg_of_ne_top 2 := fun h => absurd (@h ⊤ (by simp) 1 (-1)) (by norm_num)
-- `EReal.mul_sub_of_nonneg_of_ne_top` idx 3: necessary (a = -1, b = c = ⊤)
theorem w6_54 : ¬ drop0% EReal.mul_sub_of_nonneg_of_ne_top 3 := fun h => absurd (@h (-1) ⊤ ⊤ (by simp)) (by norm_num)
-- `EReal.mul_sub_of_nonneg_of_ne_top` idx 4: necessary (a = ⊤, b = c = 1)
theorem w6_55 : ¬ drop0% EReal.mul_sub_of_nonneg_of_ne_top 4 := fun h => absurd (@h ⊤ 1 1 (by simp)) (by norm_num)
-- `EReal.sub_mul_of_nonneg_of_ne_top` idx 3: necessary (a = -1, b = c = ⊤)
theorem w6_56 : ¬ drop0% EReal.sub_mul_of_nonneg_of_ne_top 3 := fun h => absurd (@h (-1) ⊤ ⊤ (by simp)) (by norm_num)
-- `EReal.sub_mul_of_nonneg_of_ne_top` idx 4: necessary (a = ⊤, b = c = 1)
theorem w6_57 : ¬ drop0% EReal.sub_mul_of_nonneg_of_ne_top 4 := fun h => absurd (@h ⊤ 1 1 (by simp)) (by norm_num)
namespace W1c6
-- discharger for the hypotheses of the EReal two-variable induction principles at a test predicate
macro "w6_ind" : tactic => `(tactic| first
  | (intro x y hp; (try simp only [neg_eq_iff_eq_neg, neg_neg, EReal.neg_top, EReal.neg_bot] at hp ⊢); tauto)
  | (intros; simp_all; done)
  | (intros; simp_all; intro hh; linarith))
end W1c6

-- `EReal.induction₂_neg_left` idx 1: necessary (P x y := x ≠ ⊥)
theorem w6_58 : ¬ drop0% EReal.induction₂_neg_left 1 := fun h => by
  refine absurd (@h (fun x _ => x ≠ ⊥) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fun H => H ⊥ 0 rfl) <;> w6_ind
-- `EReal.induction₂_neg_left` idx 3: necessary (P x y := ¬((x = ±⊤) ∧ y = 1))
theorem w6_59 : ¬ drop0% EReal.induction₂_neg_left 3 := fun h => by
  refine absurd (@h (fun x y => ¬((x = ⊤ ∨ x = -⊤) ∧ y = 1)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fun H => H ⊤ 1 ⟨Or.inl rfl, rfl⟩) <;> w6_ind
-- `EReal.induction₂_neg_left` idx 4: necessary (P x y := ¬((x = ±⊤) ∧ y = 0))
theorem w6_60 : ¬ drop0% EReal.induction₂_neg_left 4 := fun h => by
  refine absurd (@h (fun x y => ¬((x = ⊤ ∨ x = -⊤) ∧ y = 0)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fun H => H ⊤ 0 ⟨Or.inl rfl, rfl⟩) <;> w6_ind
-- `EReal.induction₂_neg_left` idx 5: necessary (P x y := ¬((x = ±⊤) ∧ y = -1))
theorem w6_61 : ¬ drop0% EReal.induction₂_neg_left 5 := fun h => by
  refine absurd (@h (fun x y => ¬((x = ⊤ ∨ x = -⊤) ∧ y = -1)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fun H => H ⊤ (-1) ⟨Or.inl rfl, rfl⟩) <;> w6_ind
-- `EReal.induction₂_neg_left` idx 6: necessary (P x y := ¬((x = ±⊤) ∧ y = ⊥))
theorem w6_62 : ¬ drop0% EReal.induction₂_neg_left 6 := fun h => by
  refine absurd (@h (fun x y => ¬((x = ⊤ ∨ x = -⊤) ∧ y = ⊥)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fun H => H ⊤ ⊥ ⟨Or.inl rfl, rfl⟩) <;> w6_ind
-- `EReal.induction₂_neg_left` idx 7: necessary (P x y := ¬((x = ±0) ∧ y = ⊤))
theorem w6_63 : ¬ drop0% EReal.induction₂_neg_left 7 := fun h => by
  refine absurd (@h (fun x y => ¬((x = 0 ∨ x = -0) ∧ y = ⊤)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fun H => H 0 ⊤ ⟨Or.inl rfl, rfl⟩) <;> w6_ind
-- `EReal.induction₂_neg_left` idx 8: necessary (P x y := ¬((x = ±0) ∧ y = ⊥))
theorem w6_64 : ¬ drop0% EReal.induction₂_neg_left 8 := fun h => by
  refine absurd (@h (fun x y => ¬((x = 0 ∨ x = -0) ∧ y = ⊥)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fun H => H 0 ⊥ ⟨Or.inl rfl, rfl⟩) <;> w6_ind
-- `EReal.induction₂_neg_left` idx 9: necessary (P x y := ¬((x = ±1) ∧ y = ⊤))
theorem w6_65 : ¬ drop0% EReal.induction₂_neg_left 9 := fun h => by
  refine absurd (@h (fun x y => ¬((x = 1 ∨ x = -1) ∧ y = ⊤)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fun H => H 1 ⊤ ⟨Or.inl rfl, rfl⟩) <;> w6_ind
-- `EReal.induction₂_neg_left` idx 10: necessary (P x y := ¬((x = ±1) ∧ y = ⊥))
theorem w6_66 : ¬ drop0% EReal.induction₂_neg_left 10 := fun h => by
  refine absurd (@h (fun x y => ¬((x = 1 ∨ x = -1) ∧ y = ⊥)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fun H => H 1 ⊥ ⟨Or.inl rfl, rfl⟩) <;> w6_ind
-- `EReal.induction₂_neg_left` idx 11: necessary (P x y := ¬((x = ±0) ∧ y = 0))
theorem w6_67 : ¬ drop0% EReal.induction₂_neg_left 11 := fun h => by
  refine absurd (@h (fun x y => ¬((x = 0 ∨ x = -0) ∧ y = 0)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fun H => H 0 0 ⟨Or.inl rfl, rfl⟩) <;> w6_ind
-- `EReal.induction₂_symm_neg` idx 1: necessary (P x y := y ≠ ⊥)
theorem w6_68 : ¬ drop0% EReal.induction₂_symm_neg 1 := fun h => by
  refine absurd (@h (fun _ y => y ≠ ⊥) ?_ ?_ ?_ ?_ ?_) (fun H => H 0 ⊥ rfl) <;> w6_ind
-- `EReal.induction₂_symm_neg` idx 2: necessary (P x y := x ≠ ⊥ ∧ y ≠ ⊥)
theorem w6_69 : ¬ drop0% EReal.induction₂_symm_neg 2 := fun h => by
  refine absurd (@h (fun x y => x ≠ ⊥ ∧ y ≠ ⊥) ?_ ?_ ?_ ?_ ?_) (fun H => (H ⊥ ⊥).1 rfl) <;> w6_ind
-- `EReal.induction₂_symm_neg` idx 3: necessary (symmetric P excluding (±⊤, ±⊤))
theorem w6_70 : ¬ drop0% EReal.induction₂_symm_neg 3 := fun h => by
  refine absurd (@h (fun x y => ¬((x = ⊤ ∨ x = -⊤) ∧ (y = ⊤ ∨ y = -⊤)) ∧ ¬((y = ⊤ ∨ y = -⊤) ∧ (x = ⊤ ∨ x = -⊤))) ?_ ?_ ?_ ?_ ?_) (fun H => (H ⊤ ⊤).1 ⟨Or.inl rfl, Or.inl rfl⟩) <;> w6_ind
-- `EReal.induction₂_symm_neg` idx 4: necessary (symmetric P excluding (±⊤, ±1))
theorem w6_71 : ¬ drop0% EReal.induction₂_symm_neg 4 := fun h => by
  refine absurd (@h (fun x y => ¬((x = ⊤ ∨ x = -⊤) ∧ (y = 1 ∨ y = -1)) ∧ ¬((y = ⊤ ∨ y = -⊤) ∧ (x = 1 ∨ x = -1))) ?_ ?_ ?_ ?_ ?_) (fun H => (H ⊤ 1).1 ⟨Or.inl rfl, Or.inl rfl⟩) <;> w6_ind
-- `EReal.induction₂_symm_neg` idx 5: necessary (symmetric P excluding (±⊤, ±0))
theorem w6_72 : ¬ drop0% EReal.induction₂_symm_neg 5 := fun h => by
  refine absurd (@h (fun x y => ¬((x = ⊤ ∨ x = -⊤) ∧ (y = 0 ∨ y = -0)) ∧ ¬((y = ⊤ ∨ y = -⊤) ∧ (x = 0 ∨ x = -0))) ?_ ?_ ?_ ?_ ?_) (fun H => (H ⊤ 0).1 ⟨Or.inl rfl, Or.inl rfl⟩) <;> w6_ind
-- `EReal.induction₂_symm_neg` idx 6: necessary (symmetric P excluding (±0, ±0))
theorem w6_73 : ¬ drop0% EReal.induction₂_symm_neg 6 := fun h => by
  refine absurd (@h (fun x y => ¬((x = 0 ∨ x = -0) ∧ (y = 0 ∨ y = -0)) ∧ ¬((y = 0 ∨ y = -0) ∧ (x = 0 ∨ x = -0))) ?_ ?_ ?_ ?_ ?_) (fun H => (H 0 0).1 ⟨Or.inl rfl, Or.inl rfl⟩) <;> w6_ind
namespace W1c6
-- NeZero n from an element of Fin n, or from a nonzero / non-last element of Fin (n+1)
theorem nz_of_fin {n : ℕ} (k : Fin n) : NeZero n := ⟨Nat.pos_iff_ne_zero.mp k.pos⟩
theorem nz_of_ne_zero {n : ℕ} {a : Fin (n+1)} (h : a ≠ 0) : NeZero n :=
  ⟨by rintro rfl; exact h (Fin.ext (by have := a.isLt; simp; try omega))⟩
theorem nz_of_ne_last {n : ℕ} {a : Fin (n+1)} (h : a ≠ Fin.last n) : NeZero n :=
  ⟨by rintro rfl; exact h (Fin.ext (by have := a.isLt; simp; try omega))⟩
-- parity facts in Fin 2 and Fin 3
theorem even_one2 : ¬ Even (1 : Fin 2) := by rintro ⟨r, hr⟩; revert hr; fin_cases r <;> decide
open Fin.CommRing in
theorem odd_zero2 : ¬ Odd (0 : Fin 2) := by rintro ⟨r, hr⟩; revert hr; fin_cases r <;> decide
theorem even_one3 : Even (1 : Fin 3) := ⟨2, by decide⟩
theorem even_zero3 : Even (0 : Fin 3) := ⟨0, by decide⟩
open Fin.CommRing in
theorem odd_zero3 : Odd (0 : Fin 3) := ⟨1, by decide⟩
-- in a linear order, a set missing some point is not a maximal chain (the whole type is a chain)
theorem not_maxChain {α : Type} [LinearOrder α] (s : Set α) (b : α) (hb : b ∉ s) :
    ¬ IsMaxChain (· ≤ ·) s := fun hm =>
  hb ((hm.2 (t := Set.univ) (fun a _ c _ _ => le_total a c) (Set.subset_univ _)) ▸ Set.mem_univ b)
end W1c6

-- `Fin.val_pos_iff` idx 1: removable (derivable: a : Fin n forces n ≠ 0)
theorem w6_80 : indep% Fin.val_pos_iff 1 := fun {n} {a} => W1c6.nz_of_fin a
-- `Fin.pos_iff_ne_zero'` idx 1: removable (derivable from a : Fin n)
theorem w6_81 : indep% Fin.pos_iff_ne_zero' 1 := fun a => W1c6.nz_of_fin a
-- `Fin.val_cast_of_lt` idx 1: removable (derivable: a < n forces n ≠ 0)
theorem w6_82 : indep% Fin.val_cast_of_lt 1 := fun {n a} h => ⟨by omega⟩
-- `Fin.xor_self` idx 1: removable (derivable from a : Fin k)
theorem w6_83 : indep% Fin.xor_self 1 := fun a => W1c6.nz_of_fin a
-- `Fin.xor_zero` idx 1: removable (derivable from a : Fin k)
theorem w6_84 : indep% Fin.xor_zero 1 := fun a => W1c6.nz_of_fin a
-- `Fin.odd_of_val` idx 2: removable (derivable from k : Fin n)
theorem w6_85 : indep% Fin.odd_of_val 2 := fun {n k} _ => W1c6.nz_of_fin k
-- `Fin.odd_of_odd` idx 1: removable (derivable from k : Fin n)
theorem w6_86 : indep% Fin.odd_of_odd 1 := fun _ k => W1c6.nz_of_fin k
-- `Fin.odd_iff_of_even` idx 2: removable (derivable from k : Fin n)
theorem w6_87 : indep% Fin.odd_iff_of_even 2 := fun {n k} _ => W1c6.nz_of_fin k
-- `Fin.odd_iff` idx 2: removable (derivable from k : Fin n)
theorem w6_88 : indep% Fin.odd_iff 2 := fun {n k} => W1c6.nz_of_fin k
-- `Fin.odd_iff_imp` idx 2: removable (derivable from k : Fin n)
theorem w6_89 : indep% Fin.odd_iff_imp 2 := fun {n k} => W1c6.nz_of_fin k
-- `Fin.odd_iff_mod_of_even` idx 2: removable (derivable from k : Fin n)
theorem w6_90 : indep% Fin.odd_iff_mod_of_even 2 := fun {n k} _ => W1c6.nz_of_fin k
-- `Fin.not_odd_iff_even_of_even` idx 2: removable (derivable from k : Fin n)
theorem w6_91 : indep% Fin.not_odd_iff_even_of_even 2 := fun {n k} _ => W1c6.nz_of_fin k
-- `Fin.not_even_iff_odd_of_even` idx 2: removable (derivable from k : Fin n)
theorem w6_92 : indep% Fin.not_even_iff_odd_of_even 2 := fun {n k} _ => W1c6.nz_of_fin k
-- `Fin.odd_add_one_iff_even` idx 2: removable (derivable from k : Fin n)
theorem w6_93 : indep% Fin.odd_add_one_iff_even 2 := fun {n k} => W1c6.nz_of_fin k
-- `Fin.even_add_one_iff_odd` idx 2: removable (derivable from k : Fin n)
theorem w6_94 : indep% Fin.even_add_one_iff_odd 2 := fun {n k} => W1c6.nz_of_fin k
-- `Fin.rev_pred` idx 3: removable (optParam, derivable from h by its default value)
theorem w6_95 : indep% Fin.rev_pred 3 := fun {n} {i} h => Fin.rev_ne_iff.mpr ((Fin.rev_last _).symm ▸ h)
-- `Fin.rev_castPred` idx 3: removable (optParam, derivable from h by its default value)
theorem w6_96 : indep% Fin.rev_castPred 3 := fun {n} {i} h => Fin.rev_ne_iff.mpr ((Fin.rev_zero _).symm ▸ h)
-- `Fin.le_zero_iff'` idx 1: removable (derivable from k : Fin n)
theorem w6_97 : indep% Fin.le_zero_iff' 1 := fun {n k} => W1c6.nz_of_fin k
-- `Fin.castSucc_pos_iff` idx 1: removable (derivable from i : Fin n)
theorem w6_98 : indep% Fin.castSucc_pos_iff 1 := fun {n i} => W1c6.nz_of_fin i
-- `Fin.castSucc_pos'` idx 1: removable (derivable from i : Fin n)
theorem w6_99 : indep% Fin.castSucc_pos' 1 := fun {n i} => W1c6.nz_of_fin i
-- `Fin.castPred_eq_zero` idx 1: removable (derivable: i ≠ last n forces n ≠ 0)
theorem w6_100 : indep% Fin.castPred_eq_zero 1 := fun h => W1c6.nz_of_ne_last h
-- `Fin.castPred_ne_zero` idx 1: removable (derivable: i ≠ last n forces n ≠ 0)
theorem w6_101 : indep% Fin.castPred_ne_zero 1 := fun h _ => W1c6.nz_of_ne_last h
-- `Fin.succAbove_ne_zero_zero` idx 1: removable (derivable: a ≠ 0 in Fin (n+1) forces n ≠ 0)
theorem w6_102 : indep% Fin.succAbove_ne_zero_zero 1 := fun h => W1c6.nz_of_ne_zero h
-- `Fin.succAbove_eq_zero_iff` idx 1: removable (derivable from b : Fin n)
theorem w6_103 : indep% Fin.succAbove_eq_zero_iff 1 := fun {n a b} _ => W1c6.nz_of_fin b
-- `Fin.succAbove_ne_zero` idx 1: removable (derivable from b : Fin n)
theorem w6_104 : indep% Fin.succAbove_ne_zero 1 := fun {n a b} _ => W1c6.nz_of_fin b
-- `Fin.succAbove_pos` idx 1: removable (derivable from i : Fin n)
theorem w6_105 : indep% Fin.succAbove_pos 1 := fun _ i => W1c6.nz_of_fin i
-- `Fin.castPred_succAbove` idx 4: removable (optParam, derivable from h by its default value)
theorem w6_106 : indep% Fin.castPred_succAbove 4 := fun x y h =>
  Fin.ne_last_of_lt <| (Fin.succAbove_lt_iff_castSucc_lt ..).2 h
-- `Fin.pred_succAbove` idx 4: removable (optParam, derivable from h by its default value)
theorem w6_107 : indep% Fin.pred_succAbove 4 := fun x y h =>
  Fin.ne_zero_of_lt <| (Fin.lt_succAbove_iff_le_castSucc ..).2 h
-- `Fin.succ_succAbove_zero` idx 1: removable (derivable from i : Fin n)
theorem w6_108 : indep% Fin.succ_succAbove_zero 1 := fun i => W1c6.nz_of_fin i
-- `Fin.pred_succAbove_pred` idx 5: removable (optParam, derivable from ha hb by its default value)
theorem w6_109 : indep% Fin.pred_succAbove_pred 5 := fun ha hb => Fin.succAbove_ne_zero ha hb
-- `Fin.castPred_succAbove_castPred` idx 5: removable (optParam, derivable from ha hb by its default value)
theorem w6_110 : indep% Fin.castPred_succAbove_castPred 5 := fun ha hb => Fin.succAbove_ne_last ha hb
-- `Fin.predAbove_right_zero` idx 1: removable (derivable from i : Fin n)
theorem w6_111 : indep% Fin.predAbove_right_zero 1 := fun {n i} => W1c6.nz_of_fin i
-- `Fin.predAbove_zero_succ` idx 1: removable (derivable from i : Fin n)
theorem w6_112 : indep% Fin.predAbove_zero_succ 1 := fun {n i} => W1c6.nz_of_fin i
-- `Fin.predAbove_zero_of_ne_zero` idx 1: removable (derivable: i ≠ 0 in Fin (n+1) forces n ≠ 0)
theorem w6_113 : indep% Fin.predAbove_zero_of_ne_zero 1 := fun h => W1c6.nz_of_ne_zero h
-- `Fin.succ_predAbove_zero` idx 1: removable (derivable: j ≠ 0 in Fin (n+1) forces n ≠ 0)
theorem w6_114 : indep% Fin.succ_predAbove_zero 1 := fun h => W1c6.nz_of_ne_zero h

-- `Fin.heq_ext_iff` idx 2: necessary (k = 1, l = 2, i = j = 0)
theorem w6_115 : ¬ drop0% Fin.heq_ext_iff 2 := fun h => by
  have e := (@h 1 2 0 0).mpr rfl
  exact absurd (Fin.equiv_iff_eq.mp ⟨Equiv.cast (type_eq_of_heq e)⟩) (by decide)
-- `Fin.strong_induction_on` idx 2: necessary (motive = False, n = 1)
theorem w6_116 : ¬ drop0% Fin.strong_induction_on 2 := fun h => @h 1 (fun _ => False) 0
-- `Fin.liftFun_iff_succ` idx 3: necessary (r a b := b = a + 1 on ℕ, f = val on Fin 3)
theorem w6_117 : ¬ drop0% Fin.liftFun_iff_succ 3 := fun h => by
  have e := (@h 2 ℕ (fun a b => b = a + 1) (fun i => i.val)).mpr (fun i => by simp [Fin.val_succ])
  have := e (show (0 : Fin 3) < 2 by decide)
  simp at this
-- `Fin.instNeZeroHAddNatOfNat_mathlib` idx 3: necessary (n = 1, m = 0)
theorem w6_118 : ¬ indep0% Fin.instNeZeroHAddNatOfNat_mathlib 3 := fun h => (@h 1 0 ⟨Nat.one_ne_zero⟩).out rfl
-- `IsMaxChain.range_fin_of_covBy` idx 5: necessary (Bool, n = 0, f = true: false is missing)
theorem w6_119 : ¬ drop0% IsMaxChain.range_fin_of_covBy 5 := fun h =>
  W1c6.not_maxChain _ false (by rintro ⟨k, hk⟩; exact Bool.noConfusion hk)
    (@h Bool _ _ 0 (fun _ => true) rfl (fun k => k.elim0))
-- `IsMaxChain.range_fin_of_covBy` idx 6: necessary (Bool, n = 0, f = false: true is missing)
theorem w6_120 : ¬ drop0% IsMaxChain.range_fin_of_covBy 6 := fun h =>
  W1c6.not_maxChain _ true (by rintro ⟨k, hk⟩; exact Bool.noConfusion hk)
    (@h Bool _ _ 0 (fun _ => false) rfl (fun k => k.elim0))
-- `IsMaxChain.range_fin_of_covBy` idx 7: necessary (Fin 3, n = 1, f = ![0, 2]: 1 is missing)
theorem w6_121 : ¬ drop0% IsMaxChain.range_fin_of_covBy 7 := fun h =>
  W1c6.not_maxChain _ (1 : Fin 3) (by rintro ⟨k, hk⟩; revert hk; fin_cases k <;> decide)
    (@h (Fin 3) _ _ 1 ![0, 2] (by decide) (by decide))
-- `Flag.rangeFin_carrier` idx 7: necessary (Fin 3, n = 1, f = ![0, 2], k = 0: 0 does not cover 2)
theorem w6_122 : ¬ indep0% Flag.rangeFin_carrier 7 := fun h =>
  (@h (Fin 3) _ _ 1 ![0, 2] (by decide) (by decide) 0).2 (c := 1) (by decide) (by decide)
-- `Flag.mem_rangeFin` idx 8: necessary (Fin 3, n = 1, f = ![0, 2], k = 0: 0 does not cover 2)
theorem w6_123 : ¬ indep0% Flag.mem_rangeFin 8 := fun h =>
  (@h (Fin 3) _ _ 1 ![0, 2] 0 (by decide) (by decide) 0).2 (c := 1) (by decide) (by decide)
-- `Fin.even_of_val` idx 2: necessary (n = 2, k = 1)
theorem w6_124 : ¬ drop0% Fin.even_of_val 2 := fun h => W1c6.even_one2 (@h 2 1)
-- `Fin.odd_of_val` idx 3: necessary (n = 2, k = 0)
theorem w6_125 : ¬ drop0% Fin.odd_of_val 3 := fun h => W1c6.odd_zero2 (@h 2 0 _)
-- `Fin.even_of_odd` idx 1: necessary (n = 2, k = 1)
theorem w6_126 : ¬ drop0% Fin.even_of_odd 1 := fun h => W1c6.even_one2 (@h 2 1)
-- `Fin.odd_of_odd` idx 2: necessary (n = 2, k = 0)
theorem w6_127 : ¬ drop0% Fin.odd_of_odd 2 := fun h => W1c6.odd_zero2 (@h 2 _ 0)
-- `Fin.even_iff_of_even` idx 2: necessary (n = 3, k = 1: 1 = 2 + 2 in Fin 3)
theorem w6_128 : ¬ drop0% Fin.even_iff_of_even 2 := fun h => absurd ((@h 3 1).mp W1c6.even_one3) (by decide)
-- `Fin.odd_iff_of_even` idx 3: necessary (n = 3, k = 0: 0 = 2 * 1 + 1 in Fin 3)
theorem w6_129 : ¬ drop0% Fin.odd_iff_of_even 3 := fun h => absurd ((@h 3 0 _).mp W1c6.odd_zero3) (by decide)
-- `Fin.even_iff_mod_of_even` idx 2: necessary (n = 3, k = 1)
theorem w6_130 : ¬ drop0% Fin.even_iff_mod_of_even 2 := fun h => absurd ((@h 3 1).mp W1c6.even_one3) (by decide)
-- `Fin.odd_iff_mod_of_even` idx 3: necessary (n = 3, k = 0)
theorem w6_131 : ¬ drop0% Fin.odd_iff_mod_of_even 3 := fun h => absurd ((@h 3 0 _).mp W1c6.odd_zero3) (by decide)
-- `Fin.not_odd_iff_even_of_even` idx 3: necessary (n = 3, k = 0 is even and odd)
theorem w6_132 : ¬ drop0% Fin.not_odd_iff_even_of_even 3 := fun h => (@h 3 0 _).mpr W1c6.even_zero3 W1c6.odd_zero3
-- `Fin.not_even_iff_odd_of_even` idx 3: necessary (n = 3, k = 0 is even and odd)
theorem w6_133 : ¬ drop0% Fin.not_even_iff_odd_of_even 3 := fun h => (@h 3 0 _).mpr W1c6.odd_zero3 W1c6.even_zero3
-- `Fin.snoc_apply_zero` idx 4: necessary (n = 0)
theorem w6_134 : ¬ indep0% Fin.snoc_apply_zero 4 := fun h => (@h 0 (fun _ => True) trivial (fun _ => trivial)).out rfl
-- `Fin.insertNth_apply_below` idx 4: necessary (n = 0, i = j = 0)
theorem w6_135 : ¬ indep0% Fin.insertNth_apply_below 4 := fun h =>
  absurd (@h 0 (fun _ => True) 0 0 trivial (fun _ => trivial)) (lt_irrefl _)
-- `Fin.insertNth_apply_above` idx 4: necessary (n = 0, i = j = 0)
theorem w6_136 : ¬ indep0% Fin.insertNth_apply_above 4 := fun h =>
  absurd (@h 0 (fun _ => True) 0 0 trivial (fun _ => trivial)) (lt_irrefl _)
-- `Fin.find_spec` idx 3: necessary (p = False, n = 1)
theorem w6_140 : ¬ indep0% Fin.find_spec 3 := fun h => by
  obtain ⟨k, hk⟩ := @h 1 (fun _ => False) (fun _ => inferInstance); exact hk
-- `Fin.find_min` idx 3: necessary (p = False, n = 1)
theorem w6_141 : ¬ indep0% Fin.find_min 3 := fun h => by
  obtain ⟨k, hk⟩ := @h 1 (fun _ => False) (fun _ => inferInstance) 0; exact hk
-- `Fin.find_min` idx 5: necessary (p = True, n = 1, j = 0)
theorem w6_142 : ¬ drop0% Fin.find_min 5 := fun h =>
  @h 1 (fun _ => True) (fun _ => inferInstance) ⟨0, trivial⟩ 0 trivial
-- `Fin.find_le_of_pos` idx 5: necessary (p = (· = 1) on Fin 2, j = 0)
theorem w6_143 : ¬ drop0% Fin.find_le_of_pos 5 := fun h => by
  have e := @h 2 (· = 1) (fun _ => inferInstance) ⟨1, rfl⟩ 0
  obtain ⟨m, hm, hm1⟩ := (Fin.find_le_iff _ 0).mp e
  subst hm1; exact absurd hm (by decide)
-- `Fin.find_eq_iff` idx 4: necessary (p = False, n = 1)
theorem w6_144 : ¬ indep0% Fin.find_eq_iff 4 := fun h => by
  obtain ⟨k, hk⟩ := @h 1 (fun _ => False) (fun _ => inferInstance) 0; exact hk
-- `Fin.val_find` idx 3: necessary (p = False, n = 1)
theorem w6_145 : ¬ indep0% Fin.val_find 3 := fun h => by
  obtain ⟨k, hk⟩ := @h 1 (fun _ => False) (fun _ => inferInstance); exact hk
-- `Fin.find_lt_iff` idx 3: necessary (p = False, n = 1)
theorem w6_146 : ¬ indep0% Fin.find_lt_iff 3 := fun h => by
  obtain ⟨k, hk⟩ := @h 1 (fun _ => False) (fun _ => inferInstance) 0; exact hk
-- `Fin.find_le_iff` idx 3: necessary (p = False, n = 1)
theorem w6_147 : ¬ indep0% Fin.find_le_iff 3 := fun h => by
  obtain ⟨k, hk⟩ := @h 1 (fun _ => False) (fun _ => inferInstance) 0; exact hk
-- `Fin.lt_find_iff` idx 3: necessary (p = False, n = 1)
theorem w6_148 : ¬ indep0% Fin.lt_find_iff 3 := fun h => by
  obtain ⟨k, hk⟩ := @h 1 (fun _ => False) (fun _ => inferInstance) 0; exact hk
-- `Fin.le_find_iff` idx 3: necessary (p = False, n = 1)
theorem w6_149 : ¬ indep0% Fin.le_find_iff 3 := fun h => by
  obtain ⟨k, hk⟩ := @h 1 (fun _ => False) (fun _ => inferInstance) 0; exact hk
-- `Fin.find_eq_zero` idx 3: necessary (p = False, n = 0)
theorem w6_150 : ¬ indep0% Fin.find_eq_zero 3 := fun h => by
  obtain ⟨k, hk⟩ := @h 0 (fun _ => False) (fun _ => inferInstance); exact hk
-- `Fin.find_of_not_zero` idx 3: necessary (p = False, n = 0)
theorem w6_151 : ¬ indep0% Fin.find_of_not_zero 3 := fun h => by
  obtain ⟨k, hk⟩ := @h 0 (fun _ => False) (fun _ => inferInstance) id; exact hk
-- `Fin.find_of_not_zero` idx 4: necessary (p = True, n = 0)
theorem w6_152 : ¬ indep0% Fin.find_of_not_zero 4 := fun h =>
  @h 0 (fun _ => True) (fun _ => inferInstance) ⟨0, trivial⟩ trivial
-- `Fin.find_eq_dite` idx 3: necessary (p = False, n = 0)
theorem w6_153 : ¬ indep0% Fin.find_eq_dite 3 := fun h => by
  obtain ⟨k, hk⟩ := @h 0 (fun _ => False) (fun _ => inferInstance); exact hk
-- `Fin.find_mono_of_le` idx 6: necessary (q = False, p = True, n = 1, i = 0)
theorem w6_154 : ¬ indep0% Fin.find_mono_of_le 6 := fun h =>
  @h 1 (fun _ => True) (fun _ => False) (fun _ => inferInstance) (fun _ => inferInstance) 0 (fun _ _ _ => trivial)
-- `Fin.find_mono_of_le` idx 7: necessary (q = True, p = False, n = 1, i = 0)
theorem w6_155 : ¬ indep0% Fin.find_mono_of_le 7 := fun h =>
  @h 1 (fun _ => False) (fun _ => True) (fun _ => inferInstance) (fun _ => inferInstance) 0 trivial 0 le_rfl trivial
-- `Fin.find_mono` idx 5: necessary (p = (· = 1), q = (· = 0) on Fin 2)
theorem w6_156 : ¬ drop0% Fin.find_mono 5 := fun h => by
  have e := @h 2 (· = 1) (· = 0) (fun _ => inferInstance) (fun _ => inferInstance) ⟨1, rfl⟩ ⟨0, rfl⟩
  rw [(Fin.find_eq_zero (n := 1) (p := fun x : Fin 2 => x = 0) ⟨0, rfl⟩).mpr rfl] at e
  obtain ⟨m, hm, hm1⟩ := (Fin.find_le_iff _ 0).mp e
  subst hm1; exact absurd hm (by decide)
-- `Fin.find_mono` idx 7: necessary (q = False, p = True, n = 1)
theorem w6_157 : ¬ indep0% Fin.find_mono 7 := fun h => by
  obtain ⟨k, hk⟩ := @h 1 (fun _ => True) (fun _ => False) (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ hq => hq.elim) ⟨0, trivial⟩
  exact hk
-- `Fin.find_congr` idx 6: necessary (p = q = False, n = 1, i = 0)
theorem w6_158 : ¬ indep0% Fin.find_congr 6 := fun h =>
  @h 1 (fun _ => False) (fun _ => False) (fun _ => inferInstance) (fun _ => inferInstance) 0 (fun _ _ => Iff.rfl)
-- `Fin.find_congr` idx 7: necessary (p = True, q = False, n = 1, i = 0)
theorem w6_159 : ¬ indep0% Fin.find_congr 7 := fun h =>
  (@h 1 (fun _ => True) (fun _ => False) (fun _ => inferInstance) (fun _ => inferInstance) 0 trivial 0 le_rfl).mp trivial
-- `Fin.find_congr'` idx 7: necessary (p = (· = 1), q = (· = 0) on Fin 2)
theorem w6_160 : ¬ drop0% Fin.find_congr' 7 := fun h => by
  have e := @h 2 (· = 1) (· = 0) (fun _ => inferInstance) (fun _ => inferInstance) ⟨1, rfl⟩ ⟨0, rfl⟩
  rw [(Fin.find_eq_zero (n := 1) (p := fun x : Fin 2 => x = 0) ⟨0, rfl⟩).mpr rfl] at e
  exact absurd ((Fin.find_eq_zero _).mp e) (by decide)
-- `Fin.find_le` idx 4: necessary (p = False, n = 1, i = 0)
theorem w6_161 : ¬ indep0% Fin.find_le 4 := fun h => @h 1 (fun _ => False) (fun _ => inferInstance) 0
-- `Fin.find_pos` idx 3: necessary (p = False, n = 0)
theorem w6_162 : ¬ indep0% Fin.find_pos 3 := fun h => by
  obtain ⟨k, hk⟩ := @h 0 (fun _ => False) (fun _ => inferInstance); exact hk
-- `Fin.find_of_find_le` idx 4: necessary (p = False, m = 0, n = 1)
theorem w6_163 : ¬ indep0% Fin.find_of_find_le 4 := fun h => by
  obtain ⟨k, hk⟩ := @h 0 1 (fun _ => False) (fun _ => inferInstance); exact hk
-- `Fin.find_of_find_le` idx 5: necessary (p = True, m = 1, n = 0)
theorem w6_164 : ¬ indep0% Fin.find_of_find_le 5 := fun h => by
  have h1 := @h 1 0 (fun _ => True) (fun _ => inferInstance) ⟨0, trivial⟩
  have h2 := (Fin.find (fun _ : Fin (1 + 0) => True) ⟨0, trivial⟩).isLt
  omega
-- `Fin.find?_decide_get_eq_find` idx 3: necessary (p = False, n = 1)
theorem w6_165 : ¬ indep0% Fin.find?_decide_get_eq_find 3 := fun h => by
  obtain ⟨k, hk⟩ := @h 1 (fun _ => False) (fun _ => inferInstance); exact hk
-- `Fin.find_mem_find?_decide` idx 3: necessary (p = False, n = 1)
theorem w6_166 : ¬ indep0% Fin.find_mem_find?_decide 3 := fun h => by
  obtain ⟨k, hk⟩ := @h 1 (fun _ => False) (fun _ => inferInstance); exact hk
-- `Tuple.bubble_sort_induction'` idx 5: necessary (P = False, n = 0)
theorem w6_167 : ¬ drop0% Tuple.bubble_sort_induction' 5 := fun h =>
  @h 0 ℕ _ Fin.elim0 (fun _ => False) (fun _ _ _ _ _ hp => hp)
-- `Tuple.bubble_sort_induction` idx 5: necessary (P = False, n = 0)
theorem w6_168 : ¬ drop0% Tuple.bubble_sort_induction 5 := fun h =>
  @h 0 ℕ _ Fin.elim0 (fun _ => False) (fun _ _ _ _ _ hp => hp)
-- `Tuple.bubble_sort_induction'` idx 6: necessary (P g := g = f, f = ![1, 0] not monotone)
theorem w6_169 : ¬ drop0% Tuple.bubble_sort_induction' 6 := fun h => by
  have e := @h 2 ℕ _ ![1, 0] (fun g => g = ![1, 0]) rfl
  have hm := Tuple.monotone_sort (![1, 0] : Fin 2 → ℕ)
  rw [e] at hm
  exact absurd (hm (show (0 : Fin 2) ≤ 1 by decide)) (by decide)
-- `Tuple.bubble_sort_induction` idx 6: necessary (P g := g = f, f = ![1, 0] not monotone)
theorem w6_170 : ¬ drop0% Tuple.bubble_sort_induction 6 := fun h => by
  have e := @h 2 ℕ _ ![1, 0] (fun g => g = ![1, 0]) rfl
  have hm := Tuple.monotone_sort (![1, 0] : Fin 2 → ℕ)
  rw [e] at hm
  exact absurd (hm (show (0 : Fin 2) ≤ 1 by decide)) (by decide)
-- `Tuple.unique_monotone` idx 6: necessary (f = id on Fin 2, σ = swap 0 1, τ = 1)
theorem w6_171 : ¬ drop0% Tuple.unique_monotone 6 := fun h =>
  absurd (congrFun (@h 2 (Fin 2) _ id (Equiv.swap 0 1) 1 (fun _ _ hab => hab)) 0) (by decide)
-- `Tuple.unique_monotone` idx 7: necessary (f = id on Fin 2, σ = 1, τ = swap 0 1)
theorem w6_172 : ¬ drop0% Tuple.unique_monotone 7 := fun h =>
  absurd (congrFun (@h 2 (Fin 2) _ id 1 (Equiv.swap 0 1) (fun _ _ hab => hab)) 0) (by decide)
-- `Tuple.unique_antitone` idx 6: necessary (f = id on Fin 2, σ = 1, τ = swap 0 1)
theorem w6_173 : ¬ drop0% Tuple.unique_antitone 6 := fun h =>
  absurd (congrFun (@h 2 (Fin 2) _ id 1 (Equiv.swap 0 1)
    (by intro a b hab; revert hab; fin_cases a <;> fin_cases b <;> decide)) 0) (by decide)
-- `Tuple.unique_antitone` idx 7: necessary (f = id on Fin 2, σ = swap 0 1, τ = 1)
theorem w6_174 : ¬ drop0% Tuple.unique_antitone 7 := fun h =>
  absurd (congrFun (@h 2 (Fin 2) _ id (Equiv.swap 0 1) 1
    (by intro a b hab; revert hab; fin_cases a <;> fin_cases b <;> decide)) 0) (by decide)
-- `Tuple.sort_comp_rev_eq_sortDesc_of_injective` idx 4: necessary (constant f on Fin 2: both sorts are the identity)
theorem w6_175 : ¬ drop0% Tuple.sort_comp_rev_eq_sortDesc_of_injective 4 := fun h => by
  have e := @h 2 ℕ _ (fun _ => 0)
  have h1 : Tuple.sort (fun _ : Fin 2 => (0:ℕ)) = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.mpr monotone_const
  have h2 : Tuple.sortDesc (fun _ : Fin 2 => (0:ℕ)) = Equiv.refl _ := by
    unfold Tuple.sortDesc; exact Tuple.sort_eq_refl_iff_monotone.mpr monotone_const
  rw [h1, h2] at e
  exact absurd (congrFun e 0) (by decide)
-- `Tuple.sortDesc_comp_rev_eq_sort_of_injective` idx 4: necessary (constant f on Fin 2: both sorts are the identity)
theorem w6_176 : ¬ drop0% Tuple.sortDesc_comp_rev_eq_sort_of_injective 4 := fun h => by
  have e := @h 2 ℕ _ (fun _ => 0)
  have h1 : Tuple.sort (fun _ : Fin 2 => (0:ℕ)) = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.mpr monotone_const
  have h2 : Tuple.sortDesc (fun _ : Fin 2 => (0:ℕ)) = Equiv.refl _ := by
    unfold Tuple.sortDesc; exact Tuple.sort_eq_refl_iff_monotone.mpr monotone_const
  rw [h1, h2] at e
  exact absurd (congrFun e 0) (by decide)
-- `Tuple.antitone_pair_of_not_sorted'` idx 5: necessary (n = 0)
theorem w6_177 : ¬ drop0% Tuple.antitone_pair_of_not_sorted' 5 := fun h => by
  obtain ⟨i, -⟩ := @h 0 ℕ _ Fin.elim0 1; exact i.elim0
-- `Fin.take_apply` idx 3: necessary (n = 0, m = 1)
theorem w6_178 : ¬ indep0% Fin.take_apply 3 := fun h =>
  absurd (@h 0 (fun _ => True) 1 (fun i => i.elim0) 0) (by decide)
-- `Fin.take_take` idx 4: necessary (n = n' = 0, m = 1)
theorem w6_179 : ¬ indep0% Fin.take_take 4 := fun h =>
  absurd (@h 0 (fun _ => True) 1 0 le_rfl (fun i => i.elim0)) (by decide)
-- `Fin.take_take` idx 5: necessary (n = m = 0, n' = 1)
theorem w6_180 : ¬ indep0% Fin.take_take 5 := fun h =>
  absurd (@h 0 (fun _ => True) 0 1 (Nat.zero_le _) (fun i => i.elim0)) (by decide)
-- `Fin.take_init` idx 3: necessary (n = 0, m = 1)
theorem w6_181 : ¬ indep0% Fin.take_init 3 := fun h =>
  absurd (@h 0 (fun _ => True) 1 (fun _ => trivial)) (by decide)
-- `Fin.take_succ_eq_snoc` idx 3: necessary (n = m = 0)
theorem w6_182 : ¬ indep0% Fin.take_succ_eq_snoc 3 := fun h =>
  absurd (@h 0 (fun _ => True) 0 (fun i => i.elim0)) (by decide)
-- `Fin.take_update_of_lt` idx 3: necessary (n = 0, m = 1)
theorem w6_183 : ¬ indep0% Fin.take_update_of_lt 3 := fun h =>
  absurd (@h 0 (fun _ => True) 1 (fun i => i.elim0) 0) (by decide)
-- `Fin.take_update_of_ge` idx 6: necessary (universe 1: n = m = 1, α = Bool, v = false, i = 0, x = true)
theorem w6_184 : ¬ drop1% Fin.take_update_of_ge 6 := fun h =>
  absurd (congrFun (@h 1 (fun _ => Bool) 1 le_rfl (fun _ => false) 0 true) 0) (by decide)
-- `Fin.take_addCases_left` idx 4: necessary (n = n' = 0, m = 1)
theorem w6_185 : ¬ indep0% Fin.take_addCases_left 4 := fun h =>
  absurd (@h 0 0 (fun _ => True) 1 (fun i => i.elim0) (fun i => i.elim0)) (by decide)
-- `Fin.take_addCases_right` idx 4: necessary (n = n' = 0, m = 1)
theorem w6_186 : ¬ indep0% Fin.take_addCases_right 4 := fun h =>
  absurd (@h 0 0 (fun _ => True) 1 (fun i => i.elim0) (fun i => i.elim0)) (by decide)
-- `FinEnum.card_pos` idx 2: necessary (α = PEmpty)
theorem w6_187 : ¬ drop0% FinEnum.card_pos 2 := fun h => absurd (@h PEmpty FinEnum.pempty) (by simp)
-- `FinEnum.card_ne_zero` idx 2: necessary (α = PEmpty)
theorem w6_188 : ¬ drop0% FinEnum.card_ne_zero 2 := fun h => (@h PEmpty FinEnum.pempty) FinEnum.card_pempty
-- `FinEnum.recEmptyOption_of_card_eq_zero` idx 7: necessary (α = Unit, P = True)
theorem w6_189 : ¬ indep0% FinEnum.recEmptyOption_of_card_eq_zero 7 := fun h =>
  absurd (@h (fun _ => True) (fun _ => 0) (fun _ _ _ hp => hp) trivial (fun _ hp => hp) Unit inferInstance FinEnum.pempty)
    (Nat.pos_iff_ne_zero.mp (FinEnum.card_pos_iff.mpr ⟨()⟩))
-- `FinEnum.recEmptyOption_of_card_pos` idx 7: necessary (α = PEmpty, P = True)
theorem w6_190 : ¬ indep0% FinEnum.recEmptyOption_of_card_pos 7 := fun h =>
  absurd (@h (fun _ => True) (fun _ => 0) (fun _ _ _ hp => hp) trivial (fun _ hp => hp) PEmpty FinEnum.pempty) (by simp)
