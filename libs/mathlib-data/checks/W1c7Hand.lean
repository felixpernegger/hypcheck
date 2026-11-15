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

namespace W1c7

theorem notWF {β : Type*} {r : β → β → Prop} (f : ℕ → β) (hf : ∀ n, r (f (n+1)) (f n)) :
    ¬ WellFounded r := by
  intro h
  obtain ⟨m, ⟨n, rfl⟩, hm⟩ := h.has_min (Set.range f) ⟨f 0, 0, rfl⟩
  exact hm _ ⟨n+1, rfl⟩ (hf n)

/-- The integers are not well-founded: univ is not WF. -/
theorem int_univ_not_wf : ¬ (Set.univ : Set ℤ).IsWF := by
  rw [Set.isWF_univ_iff]; intro h
  exact notWF (r := (· < ·)) (fun n : ℕ => -(n:ℤ)) (fun n => by push_cast; omega) (@wellFounded_lt ℤ _ h)

theorem int_univ_not_pwo : ¬ (Set.univ : Set ℤ).IsPWO := fun h => int_univ_not_wf h.isWF

theorem mint_univ_not_wf : ¬ (Set.univ : Set (Multiplicative ℤ)).IsWF := by
  rw [Set.isWF_univ_iff]; intro h
  exact notWF (r := (· < ·)) (fun n : ℕ => Multiplicative.ofAdd (-(n:ℤ)))
    (fun n => Multiplicative.ofAdd_lt.2 (by push_cast; omega)) (@wellFounded_lt (Multiplicative ℤ) _ h)

theorem mint_univ_not_pwo : ¬ (Set.univ : Set (Multiplicative ℤ)).IsPWO := fun h => mint_univ_not_wf h.isWF

/-- Equiv Bool Bool given by negation (not an inf/sup hom). -/
def bnot : Bool ≃ Bool := ⟨not, not, Bool.not_not, Bool.not_not⟩

@[simp] theorem bnot_apply (b : Bool) : bnot b = !b := rfl

/-- The singleton of the max of t lies below every Ici over t. -/
theorem ici_inf (t : Finset ℕ) : ({t.sup id} : Set ℕ) ≤ t.inf (fun n => Set.Ici n) :=
  Finset.le_inf fun b hb => Set.singleton_subset_iff.2 (Set.mem_Ici.2 (Finset.le_sup (f := id) hb))

/-- The sup of Iic over t lies in Iic of the max of t. -/
theorem iic_sup (t : Finset ℕ) : t.sup (fun n => Set.Iic n) ≤ Set.Iic (t.sup id) :=
  Finset.sup_le fun b hb => Set.Iic_subset_Iic.2 (Finset.le_sup (f := id) hb)

end W1c7
namespace W1c7
open scoped Pointwise

/-- phi: identity on even integers, negation on odd ones (an involution of the integers). -/
def phi (x : ℤ) : ℤ := if Even x then x else -x

theorem phi_phi (x : ℤ) : phi (phi x) = x := by
  unfold phi; by_cases hx : Even x <;> simp [hx, even_neg]

theorem phi_inj : Function.Injective phi := Function.LeftInverse.injective phi_phi

theorem phi_even (n : ℕ) : phi (2 * n) = 2 * n := by simp [phi]

theorem phi_odd (n : ℕ) : phi (2 * n + 1) = -(2 * n + 1) := by
  simp [phi, Int.even_add_one]

/-- The integers with their addition, ordered through phi: a linear order not compatible with addition. -/
def W := ℤ
instance : AddCommMonoid W := inferInstanceAs (AddCommMonoid ℤ)
instance : LinearOrder W := LinearOrder.lift' (fun x : W => phi (x : ℤ)) phi_inj
def w (z : ℤ) : W := z
theorem W_lt (a b : ℤ) : w a < w b ↔ phi a < phi b := Iff.rfl

/-- even naturals (well-founded in W: phi is the identity there) -/
def SW : Set W := {x | ∃ n : ℕ, x = w (2 * n)}

theorem SW_wf : SW.IsWF := by
  rw [Set.isWF_iff_no_descending_seq]
  intro f hf hmem
  choose k hk using hmem
  apply notWF (r := (· < ·)) (fun n => k n) _ (@wellFounded_lt ℕ _ _)
  intro n
  have h1 := hf (Nat.lt_succ_self n)
  rw [hk n, hk (n+1), W_lt, phi_even, phi_even] at h1
  omega

/-- odd naturals 2n+1 = 2n + 1 form a descending sequence in W -/
theorem SW_add_not_wf : ¬ (SW + {w 1}).IsWF := by
  rw [Set.isWF_iff_no_descending_seq]; push_neg
  refine ⟨fun n => w (2 * n + 1), strictAnti_nat_of_succ_lt fun n => ?_, fun n => ?_⟩
  · show phi (2 * ((n+1 : ℕ) : ℤ) + 1) < phi (2 * (n : ℤ) + 1)
    rw [phi_odd, phi_odd]; push_cast; omega
  · exact Set.mem_add.2 ⟨w (2 * n), ⟨n, rfl⟩, w 1, rfl, rfl⟩

/-- Multiplicative copy: the integers with addition written as multiplication, ordered through phi. -/
def MW := ℤ
instance : CommMonoid MW := inferInstanceAs (CommMonoid (Multiplicative ℤ))
instance : LinearOrder MW := LinearOrder.lift' (fun x : MW => phi (x : ℤ)) phi_inj
def mw (z : ℤ) : MW := z
theorem MW_lt (a b : ℤ) : mw a < mw b ↔ phi a < phi b := Iff.rfl

def SM : Set MW := {x | ∃ n : ℕ, x = mw (2 * n)}

theorem SM_wf : SM.IsWF := by
  rw [Set.isWF_iff_no_descending_seq]
  intro f hf hmem
  choose k hk using hmem
  apply notWF (r := (· < ·)) (fun n => k n) _ (@wellFounded_lt ℕ _ _)
  intro n
  have h1 := hf (Nat.lt_succ_self n)
  rw [hk n, hk (n+1), MW_lt, phi_even, phi_even] at h1
  omega

theorem SM_mul_not_wf : ¬ (SM * {mw 1}).IsWF := by
  rw [Set.isWF_iff_no_descending_seq]; push_neg
  refine ⟨fun n => mw (2 * n + 1), strictAnti_nat_of_succ_lt fun n => ?_, fun n => ?_⟩
  · show phi (2 * ((n+1 : ℕ) : ℤ) + 1) < phi (2 * (n : ℤ) + 1)
    rw [phi_odd, phi_odd]; push_cast; omega
  · exact Set.mem_mul.2 ⟨mw (2 * n), ⟨n, rfl⟩, mw 1, rfl, rfl⟩

end W1c7


-- `Finset.instNontrivial` idx 1: necessary (alpha = Empty: Finset Empty is a subsingleton)
theorem w7_0 : ¬ drop0% Finset.instNontrivial 1 := by
  intro h
  obtain ⟨x, y, hxy⟩ := (@h Empty).exists_pair_ne; exact hxy (by ext a; exact a.elim)

-- `Finset.forall_of_forall_cons` idx 5: necessary (s = {0}, a = 1, p = False)
theorem w7_1 : ¬ drop0% Finset.forall_of_forall_cons 5 := by
  intro h
  exact @h ℕ {0} 1 (fun _ => False) (by simp) 0 (by simp)

-- `Finset.consPiProd_snd` idx 7: necessary (s = empty, i = 0)
theorem w7_2 : ¬ indep0% Finset.consPiProd_snd 7 := by
  intro h
  simpa using @h ℕ ∅ 0 (fun _ => Unit) (by simp) (fun _ _ => ()) 0

-- `Finset.insert_subset` idx 6: necessary (s = {1}, t = {0}, a = 0)
theorem w7_3 : ¬ drop0% Finset.insert_subset 6 := by
  intro h
  have := @h ℕ _ {1} {0} 0 (by simp); revert this; decide

-- `Finset.cons_induction` idx 3: necessary (motive s := s = empty)
theorem w7_4 : ¬ drop0% Finset.cons_induction 3 := by
  intro h
  simpa using @h ℕ (fun s => s = ∅) rfl {0}

-- `Finset.cons_induction_on` idx 4: necessary (motive s := s = empty)
theorem w7_5 : ¬ drop0% Finset.cons_induction_on 4 := by
  intro h
  simpa using @h ℕ (fun s => s = ∅) {0} rfl

-- `Finset.induction` idx 3: necessary (motive := Nonempty)
theorem w7_6 : ¬ drop0% Finset.induction 3 := by
  intro h
  simpa using @h ℕ (fun s => s.Nonempty) _ (fun a s _ _ => Finset.insert_nonempty a s) ∅

-- `Finset.induction` idx 4: necessary (motive s := s = empty)
theorem w7_7 : ¬ drop0% Finset.induction 4 := by
  intro h
  simpa using @h ℕ (fun s => s = ∅) _ rfl {0}

-- `Finset.induction_on` idx 4: necessary (motive := Nonempty)
theorem w7_8 : ¬ drop0% Finset.induction_on 4 := by
  intro h
  simpa using @h ℕ (fun s => s.Nonempty) _ ∅ (fun a s _ _ => Finset.insert_nonempty a s)

-- `Finset.induction_on` idx 5: necessary (motive s := s = empty)
theorem w7_9 : ¬ drop0% Finset.induction_on 5 := by
  intro h
  simpa using @h ℕ (fun s => s = ∅) _ {0} rfl

-- `Finset.induction_on'` idx 4: necessary (motive := Nonempty, S = empty)
theorem w7_10 : ¬ drop0% Finset.induction_on' 4 := by
  intro h
  simpa using @h ℕ (fun s => s.Nonempty) _ ∅ (fun a s _ _ _ _ => Finset.insert_nonempty a s)

-- `Finset.induction_on'` idx 5: necessary (motive s := s = empty)
theorem w7_11 : ¬ drop0% Finset.induction_on' 5 := by
  intro h
  simpa using @h ℕ (fun s => s = ∅) _ {0} rfl

-- `Finset.Nonempty.cons_induction` idx 2: necessary (motive := False (step vacuous))
theorem w7_12 : ¬ drop0% Finset.Nonempty.cons_induction 2 := by
  intro h
  exact @h ℕ (fun _ _ => False) (fun _ _ _ _ hm => hm) {0} (by simp)

-- `Finset.Nonempty.cons_induction` idx 3: necessary (motive s := card s = 1, s = {0,1})
theorem w7_13 : ¬ drop0% Finset.Nonempty.cons_induction 3 := by
  intro h
  have := @h ℕ (fun s _ => s.card = 1) (fun a => Finset.card_singleton a) {0,1} (by simp); revert this; decide

-- `Finset.Nonempty.cons_induction` idx 5: necessary (motive := True, s = empty)
theorem w7_14 : ¬ indep0% Finset.Nonempty.cons_induction 5 := by
  intro h
  simpa using @h ℕ (fun _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ => trivial) ∅

-- `Finset.insertPiProd_snd` idx 7: necessary (s = empty, i = 0)
theorem w7_15 : ¬ indep0% Finset.insertPiProd_snd 7 := by
  intro h
  simpa using @h ℕ _ ∅ 0 (fun _ => Unit) (fun _ _ => ()) 0

-- `Finset.toList_insert` idx 4: necessary (a = 0 in s = {0}: lengths 1 and 2)
theorem w7_16 : ¬ drop0% Finset.toList_insert 4 := by
  intro h
  have := (@h ℕ _ 0 {0}).length_eq; simp at this

-- `Finset.card_Ico_finset` idx 4: necessary (s = {0}, t = {1,2}: interval empty but formula positive)
theorem w7_17 : ¬ drop0% Finset.card_Ico_finset 4 := by
  intro h
  have := @h ℕ _ {0} {1,2}; rw [Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun u hu => by have hu' := Finset.mem_Ico.1 hu; have := hu'.1.trans hu'.2.le; revert this; decide)] at this; revert this; decide

-- `Finset.card_Ioc_finset` idx 4: necessary (s = {0}, t = {1,2}: interval empty but formula positive)
theorem w7_18 : ¬ drop0% Finset.card_Ioc_finset 4 := by
  intro h
  have := @h ℕ _ {0} {1,2}; rw [Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun u hu => by have hu' := Finset.mem_Ioc.1 hu; have := le_trans hu'.1.le hu'.2; revert this; decide)] at this; revert this; decide

-- `Finset.card_Ioo_finset` idx 4: necessary (s = {0}, t = {1,2,3}: interval empty but formula positive)
theorem w7_19 : ¬ drop0% Finset.card_Ioo_finset 4 := by
  intro h
  have := @h ℕ _ {0} {1,2,3}; rw [Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun u hu => by have hu' := Finset.mem_Ioo.1 hu; have := le_trans hu'.1.le hu'.2.le; revert this; decide)] at this; revert this; decide

-- `Finset.subset_inter` idx 6: necessary (s1 = s2 = {0}, u = empty)
theorem w7_20 : ¬ drop0% Finset.subset_inter 6 := by
  intro h
  have := @h ℕ _ {0} {0} ∅ (subset_refl _); revert this; decide

-- `Finset.inter_subset_inter` idx 6: necessary (s = t = v = {0}, u = empty)
theorem w7_21 : ¬ drop0% Finset.inter_subset_inter 6 := by
  intro h
  have := @h ℕ _ {0} {0} ∅ {0} (subset_refl _); revert this; decide

-- `Finset.inter_subset_inter` idx 7: necessary (s = t = u = {0}, v = empty)
theorem w7_22 : ¬ drop0% Finset.inter_subset_inter 7 := by
  intro h
  have := @h ℕ _ {0} {0} {0} ∅ (subset_refl _); revert this; decide

-- `Finset.inf_cons` idx 7: necessary (s = {0}, b = 0)
theorem w7_23 : ¬ indep0% Finset.inf_cons 7 := by
  intro h
  simpa using @h Bool ℕ _ _ {0} (fun _ => true) 0

-- `map_finset_inf` idx 9: necessary (F = Bool equiv Bool, f = not, s = empty)
theorem w7_24 : ¬ drop0% map_finset_inf 9 := by
  intro h
  have := @h (Bool ≃ Bool) Bool Bool ℕ _ _ _ _ _ W1c7.bnot ∅ (fun _ => true); simp [W1c7.bnot_apply] at this

-- `map_finset_sup` idx 9: necessary (F = Bool equiv Bool, f = not, s = empty)
theorem w7_25 : ¬ drop0% map_finset_sup 9 := by
  intro h
  have := @h (Bool ≃ Bool) Bool Bool ℕ _ _ _ _ _ W1c7.bnot ∅ (fun _ => true); simp [W1c7.bnot_apply] at this

-- `BddBelow.range_finsetInf` idx 5: necessary (alpha = Nat order dual, f = toDual)
theorem w7_26 : ¬ drop0% BddBelow.range_finsetInf 5 := by
  intro h
  obtain ⟨b, hb⟩ := @h ℕᵒᵈ ℕ _ _ OrderDual.toDual; have := hb ⟨{OrderDual.ofDual b + 1}, rfl⟩; simp only [Finset.inf_singleton] at this; rw [OrderDual.le_toDual] at this; omega

-- `BddAbove.range_finsetSup` idx 5: necessary (alpha = Nat, f = id)
theorem w7_27 : ¬ drop0% BddAbove.range_finsetSup 5 := by
  intro h
  obtain ⟨b, hb⟩ := @h ℕ ℕ _ _ id; have := hb ⟨{b + 1}, rfl⟩; simp at this

-- `Finset.inf_le_of_le` idx 9: necessary (Bool, s = {0}, f = true, a = false)
theorem w7_28 : ¬ drop0% Finset.inf_le_of_le 9 := by
  intro h
  have := @h Bool ℕ _ _ {0} (fun _ => true) false 0 (by simp); revert this; decide

-- `Finset.le_sup_of_le` idx 9: necessary (Bool, s = {0}, f = false, a = true)
theorem w7_29 : ¬ drop0% Finset.le_sup_of_le 9 := by
  intro h
  have := @h Bool ℕ _ _ {0} (fun _ => false) true 0 (by simp); revert this; decide

-- `Finset.apply_inf_eq_inf_comp` idx 10: necessary (Fin 3, g = ![1,0,2] fixes top but not inf, s = {0,1}, f = 0,1)
theorem w7_30 : ¬ drop0% Finset.apply_inf_eq_inf_comp 10 := by
  intro h
  have := @h (Fin 3) ℕ (Fin 3) _ _ _ _ {0,1} (fun n => if n = 0 then (0 : Fin 3) else 1) ![1, 0, 2] rfl; revert this; decide

-- `Finset.apply_sup_eq_sup_comp` idx 10: necessary (Fin 3, g = ![0,2,1] fixes bot but not sup, s = {0,1}, f = 1,2)
theorem w7_31 : ¬ drop0% Finset.apply_sup_eq_sup_comp 10 := by
  intro h
  have := @h (Fin 3) ℕ (Fin 3) _ _ _ _ {0,1} (fun n => if n = 0 then (1 : Fin 3) else 2) ![0, 2, 1] rfl; revert this; decide

-- `Finset.comp_sup_eq_sup_comp` idx 10: necessary (Fin 3, g = ![0,2,1] fixes bot but not sup, s = {0,1}, f = 1,2)
theorem w7_32 : ¬ drop0% Finset.comp_sup_eq_sup_comp 10 := by
  intro h
  have := @h (Fin 3) ℕ (Fin 3) _ _ _ _ {0,1} (fun n => if n = 0 then (1 : Fin 3) else 2) ![0, 2, 1] rfl; revert this; decide

-- `Finset.comp_inf_eq_inf_comp` idx 10: necessary (Fin 3, g = ![1,0,2] fixes top but not inf, s = {0,1}, f = 0,1)
theorem w7_33 : ¬ drop0% Finset.comp_inf_eq_inf_comp 10 := by
  intro h
  have := @h (Fin 3) ℕ (Fin 3) _ _ _ _ {0,1} (fun n => if n = 0 then (0 : Fin 3) else 1) ![1, 0, 2] rfl; revert this; decide

-- `Finset.inf_coe` idx 6: necessary (Bool x Bool, P x := x != (false,false))
theorem w7_34 : ¬ indep0% Finset.inf_coe 6 := by
  intro h
  exact @h (Bool × Bool) ℕ _ _ (fun x => x ≠ (false, false)) (by decide) ∅ (fun _ => ⟨⊤, by decide⟩) (true, false) (false, true) (by decide) (by decide) rfl

-- `Finset.sup_coe` idx 6: necessary (Bool x Bool, P x := x != (true,true))
theorem w7_35 : ¬ indep0% Finset.sup_coe 6 := by
  intro h
  exact @h (Bool × Bool) ℕ _ _ (fun x => x ≠ (true, true)) (by decide) ∅ (fun _ => ⟨⊥, by decide⟩) (true, false) (false, true) (by decide) (by decide) rfl

-- `Finset.inf_induction` idx 8: necessary (Bool x Bool, p x := x != (false,false), f = (t,f),(f,t))
theorem w7_36 : ¬ drop0% Finset.inf_induction 8 := by
  intro h
  have := @h (Bool × Bool) ℕ _ _ {0,1} (fun n => if n = 0 then (true, false) else (false, true)) (fun x => x ≠ (false, false)) (by decide) (by decide); revert this; decide

-- `Finset.sup_induction` idx 8: necessary (Bool x Bool, p x := x != (true,true), f = (t,f),(f,t))
theorem w7_37 : ¬ drop0% Finset.sup_induction 8 := by
  intro h
  have := @h (Bool × Bool) ℕ _ _ {0,1} (fun n => if n = 0 then (true, false) else (false, true)) (fun x => x ≠ (true, true)) (by decide) (by decide); revert this; decide

-- `Finset.le_inf_of_directed_le` idx 4: necessary (s = empty)
theorem w7_38 : ¬ drop0% Finset.le_inf_of_directed_le 4 := by
  intro h
  simpa using @h Bool _ _ ∅ (by simp [DirectedOn]) ∅ (by simp)

-- `Finset.le_inf_of_directed_le` idx 5: necessary (Bool x Bool, s = t = {(t,f),(f,t)}: not directed, inf = bot)
theorem w7_39 : ¬ drop0% Finset.le_inf_of_directed_le 5 := by
  intro h
  obtain ⟨x, hx, hle⟩ := @h (Bool × Bool) _ _ {(true, false), (false, true)} ⟨_, Or.inl rfl⟩ {(true, false), (false, true)} (fun x hx => ⟨x, by simpa using hx, le_rfl⟩); rcases hx with rfl | rfl <;> revert hle <;> decide

-- `Finset.le_inf_of_directed_le` idx 7: necessary (Bool, s = {true}, t = {false})
theorem w7_40 : ¬ drop0% Finset.le_inf_of_directed_le 7 := by
  intro h
  obtain ⟨x, hx, hle⟩ := @h Bool _ _ {true} ⟨true, rfl⟩ (by simp [DirectedOn]) {false}; rcases hx with rfl; revert hle; decide

-- `Finset.sup_le_of_le_directed` idx 5: necessary (Bool x Bool, s = t = {(t,f),(f,t)}: not directed, sup = top)
theorem w7_41 : ¬ drop0% Finset.sup_le_of_le_directed 5 := by
  intro h
  obtain ⟨x, hx, hle⟩ := @h (Bool × Bool) _ _ {(true, false), (false, true)} ⟨_, Or.inl rfl⟩ {(true, false), (false, true)} (fun x hx => ⟨x, by simpa using hx, le_rfl⟩); rcases hx with rfl | rfl <;> revert hle <;> decide

-- `Finset.inf_mem` idx 5: necessary (Bool x Bool, s = complement of bot)
theorem w7_42 : ¬ drop0% Finset.inf_mem 5 := by
  intro h
  have := @h (Bool × Bool) _ _ {x | x ≠ (false, false)} (by decide) ℕ {0,1} (fun n => if n = 0 then (true, false) else (false, true)) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> decide); revert this; decide

-- `Finset.sup_mem` idx 5: necessary (Bool x Bool, s = complement of top)
theorem w7_43 : ¬ drop0% Finset.sup_mem 5 := by
  intro h
  have := @h (Bool × Bool) _ _ {x | x ≠ (true, true)} (by decide) ℕ {0,1} (fun n => if n = 0 then (true, false) else (false, true)) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> decide); revert this; decide

-- `Finset.sup_eq_zero` idx 7: necessary (WithBot Nat with zero = coe 0 != bot, s = empty)
theorem w7_44 : ¬ drop0% Finset.sup_eq_zero 7 := by
  intro h
  have := @h (WithBot ℕ) ℕ _ _ ∅ (fun _ => 0) _; simp at this

-- `Finset.inf_dite_pos_le` idx 10: necessary (Bool, s = empty, f = false)
theorem w7_45 : ¬ drop0% Finset.inf_dite_pos_le 10 := by
  intro h
  have := @h Bool ℕ _ _ ∅ (fun _ => True) _ (fun _ _ => false) (fun _ _ => true) 0 trivial; simp at this; revert this; decide

-- `Finset.inf_dite_pos_le` idx 11: necessary (p = False, s = {0}, b = 0)
theorem w7_46 : ¬ indep0% Finset.inf_dite_pos_le 11 := by
  intro h
  exact @h Bool ℕ _ _ {0} (fun _ => False) _ (fun _ _ => true) (fun _ _ => true) 0 (by simp)

-- `Finset.le_sup_dite_pos` idx 10: necessary (Bool, s = empty, f = true)
theorem w7_47 : ¬ drop0% Finset.le_sup_dite_pos 10 := by
  intro h
  have := @h Bool ℕ _ _ ∅ (fun _ => True) _ (fun _ _ => true) (fun _ _ => false) 0 trivial; simp at this; revert this; decide

-- `Finset.le_sup_dite_pos` idx 11: necessary (p = False, s = {0}, b = 0)
theorem w7_48 : ¬ indep0% Finset.le_sup_dite_pos 11 := by
  intro h
  exact @h Bool ℕ _ _ {0} (fun _ => False) _ (fun _ _ => true) (fun _ _ => true) 0 (by simp)

-- `Finset.inf_dite_neg_le` idx 10: necessary (Bool, s = empty, g = false)
theorem w7_49 : ¬ drop0% Finset.inf_dite_neg_le 10 := by
  intro h
  have := @h Bool ℕ _ _ ∅ (fun _ => False) _ (fun _ _ => true) (fun _ _ => false) 0 id; simp at this; revert this; decide

-- `Finset.inf_dite_neg_le` idx 11: necessary (p = True, s = {0}, b = 0)
theorem w7_50 : ¬ indep0% Finset.inf_dite_neg_le 11 := by
  intro h
  exact @h Bool ℕ _ _ {0} (fun _ => True) _ (fun _ _ => true) (fun _ _ => true) 0 (by simp) trivial

-- `Finset.le_sup_dite_neg` idx 10: necessary (Bool, s = empty, g = true)
theorem w7_51 : ¬ drop0% Finset.le_sup_dite_neg 10 := by
  intro h
  have := @h Bool ℕ _ _ ∅ (fun _ => False) _ (fun _ _ => true) (fun _ _ => true) 0 id; simp at this; revert this; decide

-- `Finset.le_sup_dite_neg` idx 11: necessary (p = True, s = {0}, b = 0)
theorem w7_52 : ¬ indep0% Finset.le_sup_dite_neg 11 := by
  intro h
  exact @h Bool ℕ _ _ {0} (fun _ => True) _ (fun _ _ => true) (fun _ _ => true) 0 (by simp) trivial

-- `Finset.exists_inf_le` idx 4: necessary (beta = Set Nat, f n = Ici n)
theorem w7_53 : ¬ drop0% Finset.exists_inf_le 4 := by
  intro h
  obtain ⟨t, ht⟩ := @h ℕ (Set ℕ) _ _ (fun n => Set.Ici n); have := (W1c7.ici_inf t).trans (ht (t.sup id + 1)); simp at this; obtain ⟨b, hb, hlt⟩ := this; exact absurd (Finset.le_sup (f := id) hb) (not_le.2 hlt)

-- `Finset.exists_sup_ge` idx 4: necessary (beta = Set Nat, f n = Iic n)
theorem w7_54 : ¬ drop0% Finset.exists_sup_ge 4 := by
  intro h
  obtain ⟨t, ht⟩ := @h ℕ (Set ℕ) _ _ (fun n => Set.Iic n); have := (ht (t.sup id + 1)).trans (W1c7.iic_sup t); simp at this; obtain ⟨b, hb, hlt⟩ := this; exact absurd (Finset.le_sup (f := id) hb) (not_le.2 hlt)

-- `Finset.exists_inf_eq_iInf` idx 3: necessary (beta = Set Nat, f n = Ici n)
theorem w7_55 : ¬ drop0% Finset.exists_inf_eq_iInf 3 := by
  intro h
  obtain ⟨t, ht⟩ := @h ℕ (Set ℕ) _ (fun n => Set.Ici n); have := ((W1c7.ici_inf t).trans ht.le).trans (iInf_le _ (t.sup id + 1)); simp at this; obtain ⟨b, hb, hlt⟩ := this; exact absurd (Finset.le_sup (f := id) hb) (not_le.2 hlt)

-- `Finset.exists_sup_eq_iSup` idx 3: necessary (beta = Set Nat, f n = Iic n)
theorem w7_56 : ¬ drop0% Finset.exists_sup_eq_iSup 3 := by
  intro h
  obtain ⟨t, ht⟩ := @h ℕ (Set ℕ) _ (fun n => Set.Iic n); have := ((le_iSup (fun n => Set.Iic n) (t.sup id + 1)).trans ht.ge).trans (W1c7.iic_sup t); simp at this; obtain ⟨b, hb, hlt⟩ := this; exact absurd (Finset.le_sup (f := id) hb) (not_le.2 hlt)

-- `Finset.apply_inf_eq_inf_comp_of_linearOrder` idx 10: necessary (Fin 3, non-monotone g = ![1,0,2] fixing top, s = {0,1})
theorem w7_57 : ¬ drop0% Finset.apply_inf_eq_inf_comp_of_linearOrder 10 := by
  intro h
  have := @h (Fin 3) (Fin 3) ℕ _ _ {0,1} (fun n => if n = 0 then (0 : Fin 3) else 1) _ _ ![1, 0, 2] rfl; revert this; decide

-- `Finset.apply_sup_eq_sup_comp_of_linearOrder` idx 10: necessary (Fin 3, non-monotone g = ![0,2,1] fixing bot, s = {0,1})
theorem w7_58 : ¬ drop0% Finset.apply_sup_eq_sup_comp_of_linearOrder 10 := by
  intro h
  have := @h (Fin 3) (Fin 3) ℕ _ _ {0,1} (fun n => if n = 0 then (1 : Fin 3) else 2) _ _ ![0, 2, 1] rfl; revert this; decide

-- `Finset.comp_sup_eq_sup_comp_of_is_total` idx 10: necessary (Fin 3, non-monotone g = ![0,2,1] fixing bot, s = {0,1})
theorem w7_59 : ¬ drop0% Finset.comp_sup_eq_sup_comp_of_is_total 10 := by
  intro h
  have := @h (Fin 3) (Fin 3) ℕ _ _ {0,1} (fun n => if n = 0 then (1 : Fin 3) else 2) _ _ ![0, 2, 1] rfl; revert this; decide

-- `Finset.comp_inf_eq_inf_comp_of_is_total` idx 10: necessary (Fin 3, non-monotone g = ![1,0,2] fixing top, s = {0,1})
theorem w7_60 : ¬ drop0% Finset.comp_inf_eq_inf_comp_of_is_total 10 := by
  intro h
  have := @h (Fin 3) (Fin 3) ℕ _ _ {0,1} (fun n => if n = 0 then (0 : Fin 3) else 1) _ _ ![1, 0, 2] rfl; revert this; decide

-- `Finset.inf_eq_bot_iff` idx 4: necessary (alpha = Unit, s = empty)
theorem w7_61 : ¬ drop0% Finset.inf_eq_bot_iff 4 := by
  intro h
  have := @h ℕ Unit _ _ ∅ (fun _ => ()); exact absurd (this.1 (Subsingleton.elim _ _)) (by simp)

-- `Finset.sup_eq_top_iff` idx 4: necessary (alpha = Unit, s = empty)
theorem w7_62 : ¬ drop0% Finset.sup_eq_top_iff 4 := by
  intro h
  have := @h ℕ Unit _ _ ∅ (fun _ => ()); exact absurd (this.1 (Subsingleton.elim _ _)) (by simp)

-- `Finset.Nonempty.inf_eq_bot_iff` idx 6: necessary (alpha = Unit, s = empty)
theorem w7_63 : ¬ drop0% Finset.Nonempty.inf_eq_bot_iff 6 := by
  intro h
  have := @h ℕ Unit _ _ ∅ (fun _ => ()); exact absurd (this.1 (Subsingleton.elim _ _)) (by simp)

-- `Finset.Nonempty.sup_eq_top_iff` idx 6: necessary (alpha = Unit, s = empty)
theorem w7_64 : ¬ drop0% Finset.Nonempty.sup_eq_top_iff 6 := by
  intro h
  have := @h ℕ Unit _ _ ∅ (fun _ => ()); exact absurd (this.1 (Subsingleton.elim _ _)) (by simp)

-- `Finset.inf'_union` idx 6: necessary (s1 = empty)
theorem w7_65 : ¬ indep0% Finset.inf'_union 6 := by
  intro h
  simpa using @h ℕ ℕ _ _ ∅ {0} ⟨0, by simp⟩ (fun _ => 0)

-- `Finset.inf'_union` idx 7: necessary (s2 = empty)
theorem w7_66 : ¬ indep0% Finset.inf'_union 7 := by
  intro h
  simpa using @h ℕ ℕ _ _ {0} ∅ ⟨0, by simp⟩ (fun _ => 0)

-- `Finset.sup'_union` idx 6: necessary (s1 = empty)
theorem w7_67 : ¬ indep0% Finset.sup'_union 6 := by
  intro h
  simpa using @h ℕ ℕ _ _ ∅ {0} ⟨0, by simp⟩ (fun _ => 0)

-- `Finset.sup'_union` idx 7: necessary (s2 = empty)
theorem w7_68 : ¬ indep0% Finset.sup'_union 7 := by
  intro h
  simpa using @h ℕ ℕ _ _ {0} ∅ ⟨0, by simp⟩ (fun _ => 0)

-- `Finset.inf'_comm` idx 6: necessary (s = empty)
theorem w7_69 : ¬ indep0% Finset.inf'_comm 6 := by
  intro h
  simpa using @h ℕ ℕ ℕ _ ∅ {0} ⟨0, by simp⟩ (fun _ _ => 0)

-- `Finset.inf'_comm` idx 7: necessary (t = empty)
theorem w7_70 : ¬ indep0% Finset.inf'_comm 7 := by
  intro h
  simpa using @h ℕ ℕ ℕ _ {0} ∅ ⟨0, by simp⟩ (fun _ _ => 0)

-- `Finset.sup'_comm` idx 6: necessary (s = empty)
theorem w7_71 : ¬ indep0% Finset.sup'_comm 6 := by
  intro h
  simpa using @h ℕ ℕ ℕ _ ∅ {0} ⟨0, by simp⟩ (fun _ _ => 0)

-- `Finset.sup'_comm` idx 7: necessary (t = empty)
theorem w7_72 : ¬ indep0% Finset.sup'_comm 7 := by
  intro h
  simpa using @h ℕ ℕ ℕ _ {0} ∅ ⟨0, by simp⟩ (fun _ _ => 0)

-- `Finset.inf'_induction` idx 4: necessary (s = empty)
theorem w7_73 : ¬ indep0% Finset.inf'_induction 4 := by
  intro h
  simpa using @h ℕ ℕ _ ∅ id (fun _ => True) (fun _ _ _ _ => trivial) (by simp)

-- `Finset.inf'_induction` idx 7: necessary (Bool x Bool, p x := x != bot)
theorem w7_74 : ¬ drop0% Finset.inf'_induction 7 := by
  intro h
  have := @h (Bool × Bool) ℕ _ {0,1} ⟨0, by simp⟩ (fun n => if n = 0 then (true, false) else (false, true)) (fun x => x ≠ (false, false)) (by decide); revert this; decide

-- `Finset.inf'_induction` idx 8: necessary (p = False, s = {0})
theorem w7_75 : ¬ drop0% Finset.inf'_induction 8 := by
  intro h
  exact @h ℕ ℕ _ {0} ⟨0, by simp⟩ id (fun _ => False) (fun _ h _ _ => h)

-- `Finset.sup'_induction` idx 4: necessary (s = empty)
theorem w7_76 : ¬ indep0% Finset.sup'_induction 4 := by
  intro h
  simpa using @h ℕ ℕ _ ∅ id (fun _ => True) (fun _ _ _ _ => trivial) (by simp)

-- `Finset.sup'_induction` idx 7: necessary (Bool x Bool, p x := x != top)
theorem w7_77 : ¬ drop0% Finset.sup'_induction 7 := by
  intro h
  have := @h (Bool × Bool) ℕ _ {0,1} ⟨0, by simp⟩ (fun n => if n = 0 then (true, false) else (false, true)) (fun x => x ≠ (true, true)) (by decide); revert this; decide

-- `Finset.sup'_induction` idx 8: necessary (p = False, s = {0})
theorem w7_78 : ¬ drop0% Finset.sup'_induction 8 := by
  intro h
  exact @h ℕ ℕ _ {0} ⟨0, by simp⟩ id (fun _ => False) (fun _ h _ _ => h)

-- `Finset.inf'_mem` idx 3: necessary (Bool x Bool, s = complement of bot)
theorem w7_79 : ¬ drop0% Finset.inf'_mem 3 := by
  intro h
  have := @h (Bool × Bool) _ {x | x ≠ (false, false)} ℕ {0,1} ⟨0, by simp⟩ (fun n => if n = 0 then (true, false) else (false, true)) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> decide); revert this; decide

-- `Finset.inf'_mem` idx 8: necessary (s = empty, t = {0})
theorem w7_80 : ¬ drop0% Finset.inf'_mem 8 := by
  intro h
  simpa using @h ℕ _ ∅ (by simp) ℕ {0} ⟨0, by simp⟩ id

-- `Finset.sup'_mem` idx 3: necessary (Bool x Bool, s = complement of top)
theorem w7_81 : ¬ drop0% Finset.sup'_mem 3 := by
  intro h
  have := @h (Bool × Bool) _ {x | x ≠ (true, true)} ℕ {0,1} ⟨0, by simp⟩ (fun n => if n = 0 then (true, false) else (false, true)) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> decide); revert this; decide

-- `Finset.sup'_mem` idx 8: necessary (s = empty, t = {0})
theorem w7_82 : ¬ drop0% Finset.sup'_mem 8 := by
  intro h
  simpa using @h ℕ _ ∅ (by simp) ℕ {0} ⟨0, by simp⟩ id

-- `map_finset_inf'` idx 7: necessary (F = Bool equiv Bool, f = not, g = true,false)
theorem w7_83 : ¬ drop0% map_finset_inf' 7 := by
  intro h
  have := @h (Bool ≃ Bool) Bool Bool ℕ _ _ _ W1c7.bnot {0,1} ⟨0, by simp⟩ (fun n => if n = 0 then true else false); simp [W1c7.bnot_apply] at this

-- `map_finset_inf'` idx 10: necessary (s = empty)
theorem w7_84 : ¬ indep0% map_finset_inf' 10 := by
  intro h
  simpa using @h (InfHom Bool Bool) Bool Bool ℕ _ _ _ _ (InfHom.id Bool) ∅ (fun _ => true)

-- `map_finset_sup'` idx 7: necessary (F = Bool equiv Bool, f = not, g = true,false)
theorem w7_85 : ¬ drop0% map_finset_sup' 7 := by
  intro h
  have := @h (Bool ≃ Bool) Bool Bool ℕ _ _ _ W1c7.bnot {0,1} ⟨0, by simp⟩ (fun n => if n = 0 then true else false); simp [W1c7.bnot_apply] at this

-- `map_finset_sup'` idx 10: necessary (s = empty)
theorem w7_86 : ¬ indep0% map_finset_sup' 10 := by
  intro h
  simpa using @h (SupHom Bool Bool) Bool Bool ℕ _ _ _ _ (SupHom.id Bool) ∅ (fun _ => true)

-- `Finset.inf'_eq_inf` idx 5: necessary (s = empty)
theorem w7_87 : ¬ indep0% Finset.inf'_eq_inf 5 := by
  intro h
  simpa using @h Bool ℕ _ _ ∅ (fun _ => true)

-- `Finset.sup'_eq_zero` idx 7: necessary (WithBot Nat, zero = coe 0, f = bot,0: sup is 0 but f 0 = bot)
theorem w7_88 : ¬ drop0% Finset.sup'_eq_zero 7 := by
  intro h
  have := @h (WithBot ℕ) ℕ _ _ {0,1} (fun n => if n = 0 then ⊥ else 0) _ ⟨0, by simp⟩; simp at this

-- `Finset.sup'_eq_one` idx 8: necessary (alpha = Unit, s = empty)
theorem w7_89 : ¬ indep0% Finset.sup'_eq_one 8 := by
  intro h
  simpa using @h Unit ℕ _ _ ∅ (fun _ => ()) _ ⟨fun _ => le_rfl⟩

-- `Finset.ofDual_inf'` idx 4: necessary (s = empty)
theorem w7_90 : ¬ indep0% Finset.ofDual_inf' 4 := by
  intro h
  simpa using @h ℕ ℕ _ ∅ (fun _ => OrderDual.toDual 0)

-- `Finset.ofDual_sup'` idx 4: necessary (s = empty)
theorem w7_91 : ¬ indep0% Finset.ofDual_sup' 4 := by
  intro h
  simpa using @h ℕ ℕ _ ∅ (fun _ => OrderDual.toDual 0)

-- `Finset.apply_inf_eq_inf_comp_of_nonempty` idx 10: necessary (Fin 3, non-monotone g = ![1,0,2], s = {0,1})
theorem w7_92 : ¬ drop0% Finset.apply_inf_eq_inf_comp_of_nonempty 10 := by
  intro h
  have := @h (Fin 3) (Fin 3) ℕ _ {0,1} (fun n => if n = 0 then (0 : Fin 3) else 1) _ _ _ ![1, 0, 2] ⟨0, by simp⟩; revert this; decide

-- `Finset.apply_sup_eq_sup_comp_of_nonempty` idx 10: necessary (Fin 3, non-monotone g = ![0,2,1], s = {0,1})
theorem w7_93 : ¬ drop0% Finset.apply_sup_eq_sup_comp_of_nonempty 10 := by
  intro h
  have := @h (Fin 3) (Fin 3) ℕ _ {0,1} (fun n => if n = 0 then (1 : Fin 3) else 2) _ _ _ ![0, 2, 1] ⟨0, by simp⟩; revert this; decide

-- `Multiset.map_finset_sup` idx 8: necessary (g = const 0, s = {0,1}, f n = {n})
theorem w7_94 : ¬ drop0% Multiset.map_finset_sup 8 := by
  intro h
  have := @h ℕ ℕ ℕ _ _ {0,1} (fun n => {n}) (fun _ => 0); revert this; decide

-- `Finset.induction_on_union` idx 3: necessary (P a b := card b <= 1)
theorem w7_95 : ¬ drop0% Finset.induction_on_union 3 := by
  intro h
  have := @h ℕ _ (fun _ b => b.card ≤ 1) (by simp) (by simp) (fun h1 _ => h1) ∅ {0,1}; revert this; decide

-- `Finset.induction_on_union` idx 4: necessary (P a b := a, b nonempty)
theorem w7_96 : ¬ drop0% Finset.induction_on_union 4 := by
  intro h
  have := @h ℕ _ (fun a b => a.Nonempty ∧ b.Nonempty) (fun h => ⟨h.2, h.1⟩) (⟨by simp, by simp⟩) (fun h1 _ => ⟨h1.1.mono Finset.subset_union_left, h1.2⟩) ∅ ∅; simp at this

-- `Finset.induction_on_union` idx 5: necessary (P a b := a = empty or b = empty)
theorem w7_97 : ¬ drop0% Finset.induction_on_union 5 := by
  intro h
  have := @h ℕ _ (fun a b => a = ∅ ∨ b = ∅) (fun h => h.symm) (Or.inr rfl) (fun h1 h2 => by rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all) {0} {0}; simp at this

-- `Finset.induction_on_union` idx 6: necessary (P a b := a or b empty, or both singletons)
theorem w7_98 : ¬ drop0% Finset.induction_on_union 6 := by
  intro h
  have := @h ℕ _ (fun a b => a = ∅ ∨ b = ∅ ∨ (a.card = 1 ∧ b.card = 1)) (fun h => by rcases h with h | h | h; exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h.symm)]) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr ⟨by simp, by simp⟩)) {0,1} {0,1}; revert this; decide

-- `Finset.sup_prodMap` idx 10: necessary (Bool, s = empty, t = {0}, g = true)
theorem w7_99 : ¬ drop0% Finset.sup_prodMap 10 := by
  intro h
  have := @h ℕ ℕ Bool Bool _ _ _ _ ∅ {0} ⟨0, by simp⟩ (fun _ => true) (fun _ => true); simp at this; revert this; decide

-- `Finset.sup_prodMap` idx 11: necessary (Bool, s = {0}, t = empty, f = true)
theorem w7_100 : ¬ drop0% Finset.sup_prodMap 11 := by
  intro h
  have := @h ℕ ℕ Bool Bool _ _ _ _ {0} ∅ ⟨0, by simp⟩ (fun _ => true) (fun _ => true); simp at this; revert this; decide

-- `Finset.prodMk_inf'_inf'` idx 8: necessary (s = empty)
theorem w7_101 : ¬ indep0% Finset.prodMk_inf'_inf' 8 := by
  intro h
  simpa using @h ℕ ℕ ℕ ℕ _ _ ∅ {0} ⟨0, by simp⟩ id id

-- `Finset.prodMk_inf'_inf'` idx 9: necessary (t = empty)
theorem w7_102 : ¬ indep0% Finset.prodMk_inf'_inf' 9 := by
  intro h
  simpa using @h ℕ ℕ ℕ ℕ _ _ {0} ∅ ⟨0, by simp⟩ id id

-- `Finset.prodMk_sup'_sup'` idx 8: necessary (s = empty)
theorem w7_103 : ¬ indep0% Finset.prodMk_sup'_sup' 8 := by
  intro h
  simpa using @h ℕ ℕ ℕ ℕ _ _ ∅ {0} ⟨0, by simp⟩ id id

-- `Finset.prodMk_sup'_sup'` idx 9: necessary (t = empty)
theorem w7_104 : ¬ indep0% Finset.prodMk_sup'_sup' 9 := by
  intro h
  simpa using @h ℕ ℕ ℕ ℕ _ _ {0} ∅ ⟨0, by simp⟩ id id

-- `Finset.inf'_sup_inf'` idx 6: necessary (s = empty)
theorem w7_105 : ¬ indep0% Finset.inf'_sup_inf' 6 := by
  intro h
  simpa using @h ℕ ℕ ℕ _ ∅ {0} ⟨0, by simp⟩ id id

-- `Finset.inf'_sup_inf'` idx 7: necessary (t = empty)
theorem w7_106 : ¬ indep0% Finset.inf'_sup_inf' 7 := by
  intro h
  simpa using @h ℕ ℕ ℕ _ {0} ∅ ⟨0, by simp⟩ id id

-- `Finset.sup'_inf_sup'` idx 6: necessary (s = empty)
theorem w7_107 : ¬ indep0% Finset.sup'_inf_sup' 6 := by
  intro h
  simpa using @h ℕ ℕ ℕ _ ∅ {0} ⟨0, by simp⟩ id id

-- `Finset.sup'_inf_sup'` idx 7: necessary (t = empty)
theorem w7_108 : ¬ indep0% Finset.sup'_inf_sup' 7 := by
  intro h
  simpa using @h ℕ ℕ ℕ _ {0} ∅ ⟨0, by simp⟩ id id

-- `Finset.sup'_biUnion` idx 7: necessary (s = empty)
theorem w7_109 : ¬ indep0% Finset.sup'_biUnion 7 := by
  intro h
  simpa using @h ℕ ℕ ℕ _ id _ ∅ (fun _ => {0}) (fun _ => ⟨0, by simp⟩)

-- `Finset.sup'_biUnion` idx 9: necessary (t = fun _ => empty)
theorem w7_110 : ¬ indep0% Finset.sup'_biUnion 9 := by
  intro h
  simpa using @h ℕ ℕ ℕ _ id _ {0} ⟨0, by simp⟩ (fun _ => ∅) 0

-- `Finset.inf'_biUnion` idx 7: necessary (s = empty)
theorem w7_111 : ¬ indep0% Finset.inf'_biUnion 7 := by
  intro h
  simpa using @h ℕ ℕ ℕ _ id _ ∅ (fun _ => {0}) (fun _ => ⟨0, by simp⟩)

-- `Finset.inf'_biUnion` idx 9: necessary (t = fun _ => empty)
theorem w7_112 : ¬ indep0% Finset.inf'_biUnion 9 := by
  intro h
  simpa using @h ℕ ℕ ℕ _ id _ {0} ⟨0, by simp⟩ (fun _ => ∅) 0

-- `Finset.min'_lt_max'` idx 5: necessary (s = {0}, j = 0, i = 1)
theorem w7_113 : ¬ indep0% Finset.min'_lt_max' 5 := by
  intro h
  simpa using @h ℕ _ {0} 1 0 (by simp) (by decide)

-- `Finset.min'_union` idx 4: necessary (s1 = empty)
theorem w7_114 : ¬ indep0% Finset.min'_union 4 := by
  intro h
  simpa using @h ℕ _ ∅ {0} ⟨0, by simp⟩

-- `Finset.min'_union` idx 5: necessary (s2 = empty)
theorem w7_115 : ¬ indep0% Finset.min'_union 5 := by
  intro h
  simpa using @h ℕ _ {0} ∅ ⟨0, by simp⟩

-- `Finset.max'_union` idx 4: necessary (s1 = empty)
theorem w7_116 : ¬ indep0% Finset.max'_union 4 := by
  intro h
  simpa using @h ℕ _ ∅ {0} ⟨0, by simp⟩

-- `Finset.max'_union` idx 5: necessary (s2 = empty)
theorem w7_117 : ¬ indep0% Finset.max'_union 5 := by
  intro h
  simpa using @h ℕ _ {0} ∅ ⟨0, by simp⟩

-- `Finset.induction_on_min` idx 5: necessary (motive := Nonempty)
theorem w7_118 : ¬ drop0% Finset.induction_on_min 5 := by
  intro h
  simpa using @h ℕ _ _ (fun s => s.Nonempty) ∅ (fun a s _ _ => Finset.insert_nonempty a s)

-- `Finset.induction_on_min` idx 6: necessary (motive s := s = empty)
theorem w7_119 : ¬ drop0% Finset.induction_on_min 6 := by
  intro h
  simpa using @h ℕ _ _ (fun s => s = ∅) {0} rfl

-- `Finset.induction_on_max` idx 5: necessary (motive := Nonempty)
theorem w7_120 : ¬ drop0% Finset.induction_on_max 5 := by
  intro h
  simpa using @h ℕ _ _ (fun s => s.Nonempty) ∅ (fun a s _ _ => Finset.insert_nonempty a s)

-- `Finset.induction_on_max` idx 6: necessary (motive s := s = empty)
theorem w7_121 : ¬ drop0% Finset.induction_on_max 6 := by
  intro h
  simpa using @h ℕ _ _ (fun s => s = ∅) {0} rfl

-- `Finset.induction_on_min_value` idx 7: necessary (motive := Nonempty)
theorem w7_122 : ¬ drop0% Finset.induction_on_min_value 7 := by
  intro h
  simpa using @h ℕ ℕ _ _ id (fun s => s.Nonempty) ∅ (fun a s _ _ _ => Finset.insert_nonempty a s)

-- `Finset.induction_on_min_value` idx 8: necessary (motive s := s = empty)
theorem w7_123 : ¬ drop0% Finset.induction_on_min_value 8 := by
  intro h
  simpa using @h ℕ ℕ _ _ id (fun s => s = ∅) {0} rfl

-- `Finset.induction_on_max_value` idx 7: necessary (motive := Nonempty)
theorem w7_124 : ¬ drop0% Finset.induction_on_max_value 7 := by
  intro h
  simpa using @h ℕ ℕ _ _ id (fun s => s.Nonempty) ∅ (fun a s _ _ _ => Finset.insert_nonempty a s)

-- `Finset.induction_on_max_value` idx 8: necessary (motive s := s = empty)
theorem w7_125 : ¬ drop0% Finset.induction_on_max_value 8 := by
  intro h
  simpa using @h ℕ ℕ _ _ id (fun s => s = ∅) {0} rfl

-- `Finset.isGLB_iff_isLeast` idx 4: necessary (Bool, s = empty, i = true (top is the GLB of empty))
theorem w7_126 : ¬ drop0% Finset.isGLB_iff_isLeast 4 := by
  intro h
  have h2 := (@h Bool _ true ∅).1 (by rw [Finset.coe_empty, isGLB_empty_iff]; exact fun b => le_top); simpa using h2.1

-- `Finset.isLUB_mem` idx 4: necessary (s = {0}, i = 1)
theorem w7_127 : ¬ drop0% Finset.isLUB_mem 4 := by
  intro h
  simpa using @h ℕ _ 1 {0} ⟨0, by simp⟩

-- `Finset.isGLB_mem` idx 4: necessary (s = {0}, i = 1)
theorem w7_128 : ¬ drop0% Finset.isGLB_mem 4 := by
  intro h
  simpa using @h ℕ _ 1 {0} ⟨0, by simp⟩

-- `Finset.isGLB_mem` idx 5: necessary (Bool, s = empty, i = true)
theorem w7_129 : ¬ drop0% Finset.isGLB_mem 5 := by
  intro h
  simpa using @h Bool _ true ∅ (by rw [Finset.coe_empty, isGLB_empty_iff]; exact fun b => le_top)

-- `Set.IsPWO.add` idx 5: necessary (W = Int with addition ordered by phi (id on evens, negation on odds); s = even naturals (WF), t = {1}, s + t = odd naturals descending)
theorem w7_130 : ¬ drop0% Set.IsPWO.add 5 := by
  intro h
  exact W1c7.SW_add_not_wf (@h W1c7.W W1c7.SW {W1c7.w 1} _ _ W1c7.SW_wf.isPWO (Set.isPWO_singleton _)).isWF

-- `Set.IsPWO.add` idx 6: necessary (Int, s = univ, t = {0})
theorem w7_131 : ¬ drop0% Set.IsPWO.add 6 := by
  intro h
  exact W1c7.int_univ_not_pwo (by simpa [Set.add_singleton] using @h ℤ Set.univ {0} _ _ _ (Set.isPWO_singleton 0))

-- `Set.IsPWO.add` idx 7: necessary (Int, s = {0}, t = univ)
theorem w7_132 : ¬ drop0% Set.IsPWO.add 7 := by
  intro h
  exact W1c7.int_univ_not_pwo (by simpa [Set.singleton_add] using @h ℤ {0} Set.univ _ _ _ (Set.isPWO_singleton 0))

-- `Set.IsPWO.mul` idx 5: necessary (multiplicative copy of W (Int ordered by phi); s = even naturals, t = {1})
theorem w7_133 : ¬ drop0% Set.IsPWO.mul 5 := by
  intro h
  exact W1c7.SM_mul_not_wf (@h W1c7.MW W1c7.SM {W1c7.mw 1} _ _ W1c7.SM_wf.isPWO (Set.isPWO_singleton _)).isWF

-- `Set.IsPWO.mul` idx 6: necessary (Multiplicative Int, s = univ, t = {1})
theorem w7_134 : ¬ drop0% Set.IsPWO.mul 6 := by
  intro h
  exact W1c7.mint_univ_not_pwo (by simpa [Set.mul_singleton] using @h (Multiplicative ℤ) Set.univ {1} _ _ _ (Set.isPWO_singleton 1))

-- `Set.IsPWO.mul` idx 7: necessary (Multiplicative Int, s = {1}, t = univ)
theorem w7_135 : ¬ drop0% Set.IsPWO.mul 7 := by
  intro h
  exact W1c7.mint_univ_not_pwo (by simpa [Set.singleton_mul] using @h (Multiplicative ℤ) {1} Set.univ _ _ _ (Set.isPWO_singleton 1))

-- `Set.IsWF.add` idx 5: necessary (W = Int with addition ordered by phi (id on evens, negation on odds); s = even naturals (WF), t = {1}, s + t = odd naturals descending)
theorem w7_136 : ¬ drop0% Set.IsWF.add 5 := by
  intro h
  exact W1c7.SW_add_not_wf (@h W1c7.W W1c7.SW {W1c7.w 1} _ _ W1c7.SW_wf Set.isWF_singleton)

-- `Set.IsWF.add` idx 6: necessary (Int, s = univ, t = {0})
theorem w7_137 : ¬ drop0% Set.IsWF.add 6 := by
  intro h
  exact W1c7.int_univ_not_wf (by simpa [Set.add_singleton] using @h ℤ Set.univ {0} _ _ _ Set.isWF_singleton)

-- `Set.IsWF.mul` idx 5: necessary (multiplicative copy of W (Int ordered by phi); s = even naturals, t = {1})
theorem w7_138 : ¬ drop0% Set.IsWF.mul 5 := by
  intro h
  exact W1c7.SM_mul_not_wf (@h W1c7.MW W1c7.SM {W1c7.mw 1} _ _ W1c7.SM_wf Set.isWF_singleton)

-- `Set.IsWF.mul` idx 6: necessary (Multiplicative Int, s = univ, t = {1})
theorem w7_139 : ¬ drop0% Set.IsWF.mul 6 := by
  intro h
  exact W1c7.mint_univ_not_wf (by simpa [Set.mul_singleton] using @h (Multiplicative ℤ) Set.univ {1} _ _ _ Set.isWF_singleton)

-- `Set.IsWF.mul` idx 7: necessary (Multiplicative Int, s = {1}, t = univ)
theorem w7_140 : ¬ drop0% Set.IsWF.mul 7 := by
  intro h
  exact W1c7.mint_univ_not_wf (by simpa [Set.singleton_mul] using @h (Multiplicative ℤ) {1} Set.univ _ _ _ Set.isWF_singleton)

-- `Set.IsWF.min_add` idx 6: necessary (Int, s = univ, t = {0})
theorem w7_141 : ¬ indep0% Set.IsWF.min_add 6 := by
  intro h
  exact W1c7.int_univ_not_wf (@h ℤ Set.univ {0} _ _ _ Set.isWF_singleton Set.univ_nonempty (Set.singleton_nonempty 0))

-- `Set.IsWF.min_add` idx 7: necessary (Int, s = {0}, t = univ)
theorem w7_142 : ¬ indep0% Set.IsWF.min_add 7 := by
  intro h
  exact W1c7.int_univ_not_wf (@h ℤ {0} Set.univ _ _ _ Set.isWF_singleton (Set.singleton_nonempty 0) Set.univ_nonempty)

-- `Set.IsWF.min_mul` idx 6: necessary (Multiplicative Int, s = univ, t = {1})
theorem w7_143 : ¬ indep0% Set.IsWF.min_mul 6 := by
  intro h
  exact W1c7.mint_univ_not_wf (@h (Multiplicative ℤ) Set.univ {1} _ _ _ Set.isWF_singleton Set.univ_nonempty (Set.singleton_nonempty 1))

-- `Set.IsWF.min_mul` idx 7: necessary (Multiplicative Int, s = {1}, t = univ)
theorem w7_144 : ¬ indep0% Set.IsWF.min_mul 7 := by
  intro h
  exact W1c7.mint_univ_not_wf (@h (Multiplicative ℤ) {1} Set.univ _ _ _ Set.isWF_singleton (Set.singleton_nonempty 1) Set.univ_nonempty)

-- `Set.IsWF.min_mul` idx 8: necessary (s = empty)
theorem w7_145 : ¬ indep0% Set.IsWF.min_mul 8 := by
  intro h
  exact Set.not_nonempty_empty (@h (Multiplicative ℤ) ∅ {1} _ _ _ Set.finite_empty.isWF Set.isWF_singleton (Set.singleton_nonempty 1))

-- `Set.IsWF.min_mul` idx 9: necessary (t = empty)
theorem w7_146 : ¬ indep0% Set.IsWF.min_mul 9 := by
  intro h
  exact Set.not_nonempty_empty (@h (Multiplicative ℤ) {1} ∅ _ _ _ Set.isWF_singleton Set.finite_empty.isWF (Set.singleton_nonempty 1))

-- `Finset.mem_antidiagonal` idx 6: necessary (Int, s = univ)
theorem w7_147 : ¬ indep0% Finset.mem_antidiagonal 6 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ Set.univ ∅ Set.isPWO_empty 0 (0, 0))

-- `Finset.mem_antidiagonal` idx 7: necessary (Int, t = univ)
theorem w7_148 : ¬ indep0% Finset.mem_antidiagonal 7 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ ∅ Set.univ Set.isPWO_empty 0 (0, 0))

-- `Finset.mem_mulAntidiagonal` idx 6: necessary (Multiplicative Int, s = univ)
theorem w7_149 : ¬ indep0% Finset.mem_mulAntidiagonal 6 := by
  intro h
  exact W1c7.mint_univ_not_pwo (@h (Multiplicative ℤ) _ _ _ Set.univ ∅ Set.isPWO_empty 1 (1, 1))

-- `Finset.mem_mulAntidiagonal` idx 7: necessary (Multiplicative Int, t = univ)
theorem w7_150 : ¬ indep0% Finset.mem_mulAntidiagonal 7 := by
  intro h
  exact W1c7.mint_univ_not_pwo (@h (Multiplicative ℤ) _ _ _ ∅ Set.univ Set.isPWO_empty 1 (1, 1))

-- `Finset.antidiagonal_mono_left` idx 6: necessary (Int, s = univ, u = empty)
theorem w7_151 : ¬ indep0% Finset.antidiagonal_mono_left 6 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ Set.univ ∅ Set.isPWO_empty 0 ∅ Set.isPWO_empty (Set.empty_subset _))

-- `Finset.antidiagonal_mono_left` idx 7: necessary (Int, t = univ, u = empty)
theorem w7_152 : ¬ indep0% Finset.antidiagonal_mono_left 7 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ ∅ Set.univ Set.isPWO_empty 0 ∅ Set.isPWO_empty (Set.empty_subset _))

-- `Finset.antidiagonal_mono_left` idx 10: removable (derivable: u is a subset of s and s.IsPWO, so u.IsPWO by IsPWO.mono)
theorem w7_153 : indep% Finset.antidiagonal_mono_left 10 := by
  intro α _ _ _ s t hs ht a u hu; exact hs.mono hu

-- `Finset.antidiagonal_mono_left` idx 11: necessary (ℕ, u = {0} not a subset of the empty set: (z,z) in the left antidiagonal only)
theorem w7_154 : ¬ drop0% Finset.antidiagonal_mono_left 11 := by
  intro h
  have hm : ((0 : ℕ), (0 : ℕ)) ∈ Finset.antidiagonal (Set.isPWO_singleton (0 : ℕ)) (Set.isPWO_singleton (0 : ℕ)) 0 := by simp [Finset.mem_antidiagonal]
  have := @h ℕ _ _ _ ∅ {0} (Set.isPWO_empty (α := ℕ)) (Set.isPWO_singleton (0 : ℕ)) 0 {0} (Set.isPWO_singleton (0 : ℕ)) (0, 0) hm; simp [Finset.mem_antidiagonal] at this

-- `Finset.mulAntidiagonal_mono_left` idx 6: necessary (Multiplicative Int, s = univ, u = empty)
theorem w7_155 : ¬ indep0% Finset.mulAntidiagonal_mono_left 6 := by
  intro h
  exact W1c7.mint_univ_not_pwo (@h (Multiplicative ℤ) _ _ _ Set.univ ∅ Set.isPWO_empty 1 ∅ Set.isPWO_empty (Set.empty_subset _))

-- `Finset.mulAntidiagonal_mono_left` idx 7: necessary (Multiplicative Int, t = univ, u = empty)
theorem w7_156 : ¬ indep0% Finset.mulAntidiagonal_mono_left 7 := by
  intro h
  exact W1c7.mint_univ_not_pwo (@h (Multiplicative ℤ) _ _ _ ∅ Set.univ Set.isPWO_empty 1 ∅ Set.isPWO_empty (Set.empty_subset _))

-- `Finset.mulAntidiagonal_mono_left` idx 10: removable (derivable: u is a subset of s and s.IsPWO, so u.IsPWO by IsPWO.mono)
theorem w7_157 : indep% Finset.mulAntidiagonal_mono_left 10 := by
  intro α _ _ _ s t hs ht a u hu; exact hs.mono hu

-- `Finset.mulAntidiagonal_mono_left` idx 11: necessary ((Multiplicative ℕ), u = {1} not a subset of the empty set: (z,z) in the left antidiagonal only)
theorem w7_158 : ¬ drop0% Finset.mulAntidiagonal_mono_left 11 := by
  intro h
  have hm : ((1 : (Multiplicative ℕ)), (1 : (Multiplicative ℕ))) ∈ Finset.mulAntidiagonal (Set.isPWO_singleton (1 : (Multiplicative ℕ))) (Set.isPWO_singleton (1 : (Multiplicative ℕ))) 1 := by simp [Finset.mem_mulAntidiagonal]
  have := @h (Multiplicative ℕ) _ _ _ ∅ {1} (Set.isPWO_empty (α := (Multiplicative ℕ))) (Set.isPWO_singleton (1 : (Multiplicative ℕ))) 1 {1} (Set.isPWO_singleton (1 : (Multiplicative ℕ))) (1, 1) hm; simp [Finset.mem_mulAntidiagonal] at this

-- `Finset.antidiagonal_mono_right` idx 6: necessary (Int, s = univ, u = empty)
theorem w7_159 : ¬ indep0% Finset.antidiagonal_mono_right 6 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ Set.univ ∅ Set.isPWO_empty 0 ∅ Set.isPWO_empty (Set.empty_subset _))

-- `Finset.antidiagonal_mono_right` idx 7: necessary (Int, t = univ, u = empty)
theorem w7_160 : ¬ indep0% Finset.antidiagonal_mono_right 7 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ ∅ Set.univ Set.isPWO_empty 0 ∅ Set.isPWO_empty (Set.empty_subset _))

-- `Finset.antidiagonal_mono_right` idx 10: removable (derivable: u is a subset of t and t.IsPWO, so u.IsPWO by IsPWO.mono)
theorem w7_161 : indep% Finset.antidiagonal_mono_right 10 := by
  intro α _ _ _ s t hs ht a u hu; exact ht.mono hu

-- `Finset.antidiagonal_mono_right` idx 11: necessary (ℕ, u = {0} not a subset of the empty set: (z,z) in the left antidiagonal only)
theorem w7_162 : ¬ drop0% Finset.antidiagonal_mono_right 11 := by
  intro h
  have hm : ((0 : ℕ), (0 : ℕ)) ∈ Finset.antidiagonal (Set.isPWO_singleton (0 : ℕ)) (Set.isPWO_singleton (0 : ℕ)) 0 := by simp [Finset.mem_antidiagonal]
  have := @h ℕ _ _ _ {0} ∅ (Set.isPWO_singleton (0 : ℕ)) (Set.isPWO_empty (α := ℕ)) 0 {0} (Set.isPWO_singleton (0 : ℕ)) (0, 0) hm; simp [Finset.mem_antidiagonal] at this

-- `Finset.mulAntidiagonal_mono_right` idx 6: necessary (Multiplicative Int, s = univ, u = empty)
theorem w7_163 : ¬ indep0% Finset.mulAntidiagonal_mono_right 6 := by
  intro h
  exact W1c7.mint_univ_not_pwo (@h (Multiplicative ℤ) _ _ _ Set.univ ∅ Set.isPWO_empty 1 ∅ Set.isPWO_empty (Set.empty_subset _))

-- `Finset.mulAntidiagonal_mono_right` idx 7: necessary (Multiplicative Int, t = univ, u = empty)
theorem w7_164 : ¬ indep0% Finset.mulAntidiagonal_mono_right 7 := by
  intro h
  exact W1c7.mint_univ_not_pwo (@h (Multiplicative ℤ) _ _ _ ∅ Set.univ Set.isPWO_empty 1 ∅ Set.isPWO_empty (Set.empty_subset _))

-- `Finset.mulAntidiagonal_mono_right` idx 10: removable (derivable: u is a subset of t and t.IsPWO, so u.IsPWO by IsPWO.mono)
theorem w7_165 : indep% Finset.mulAntidiagonal_mono_right 10 := by
  intro α _ _ _ s t hs ht a u hu; exact ht.mono hu

-- `Finset.mulAntidiagonal_mono_right` idx 11: necessary ((Multiplicative ℕ), u = {1} not a subset of the empty set: (z,z) in the left antidiagonal only)
theorem w7_166 : ¬ drop0% Finset.mulAntidiagonal_mono_right 11 := by
  intro h
  have hm : ((1 : (Multiplicative ℕ)), (1 : (Multiplicative ℕ))) ∈ Finset.mulAntidiagonal (Set.isPWO_singleton (1 : (Multiplicative ℕ))) (Set.isPWO_singleton (1 : (Multiplicative ℕ))) 1 := by simp [Finset.mem_mulAntidiagonal]
  have := @h (Multiplicative ℕ) _ _ _ {1} ∅ (Set.isPWO_singleton (1 : (Multiplicative ℕ))) (Set.isPWO_empty (α := (Multiplicative ℕ))) 1 {1} (Set.isPWO_singleton (1 : (Multiplicative ℕ))) (1, 1) hm; simp [Finset.mem_mulAntidiagonal] at this

-- `Finset.swap_mem_antidiagonal` idx 6: necessary (Int, s = univ)
theorem w7_167 : ¬ indep0% Finset.swap_mem_antidiagonal 6 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ Set.univ ∅ Set.isPWO_empty 0 (0, 0))

-- `Finset.swap_mem_antidiagonal` idx 7: necessary (Int, t = univ)
theorem w7_168 : ¬ indep0% Finset.swap_mem_antidiagonal 7 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ ∅ Set.univ Set.isPWO_empty 0 (0, 0))

-- `Finset.swap_mem_mulAntidiagonal` idx 6: necessary (Multiplicative Int, s = univ)
theorem w7_169 : ¬ indep0% Finset.swap_mem_mulAntidiagonal 6 := by
  intro h
  exact W1c7.mint_univ_not_pwo (@h (Multiplicative ℤ) _ _ _ Set.univ ∅ Set.isPWO_empty 1 (1, 1))

-- `Finset.swap_mem_mulAntidiagonal` idx 7: necessary (Multiplicative Int, t = univ)
theorem w7_170 : ¬ indep0% Finset.swap_mem_mulAntidiagonal 7 := by
  intro h
  exact W1c7.mint_univ_not_pwo (@h (Multiplicative ℤ) _ _ _ ∅ Set.univ Set.isPWO_empty 1 (1, 1))

-- `Finset.support_antidiagonal_subset_add` idx 6: necessary (Int, s = univ)
theorem w7_171 : ¬ indep0% Finset.support_antidiagonal_subset_add 6 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ Set.univ ∅ Set.isPWO_empty)

-- `Finset.support_antidiagonal_subset_add` idx 7: necessary (Int, t = univ)
theorem w7_172 : ¬ indep0% Finset.support_antidiagonal_subset_add 7 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ ∅ Set.univ Set.isPWO_empty)

-- `Finset.support_mulAntidiagonal_subset_mul` idx 6: necessary (Multiplicative Int, s = univ)
theorem w7_173 : ¬ indep0% Finset.support_mulAntidiagonal_subset_mul 6 := by
  intro h
  exact W1c7.mint_univ_not_pwo (@h (Multiplicative ℤ) _ _ _ Set.univ ∅ Set.isPWO_empty)

-- `Finset.support_mulAntidiagonal_subset_mul` idx 7: necessary (Multiplicative Int, t = univ)
theorem w7_174 : ¬ indep0% Finset.support_mulAntidiagonal_subset_mul 7 := by
  intro h
  exact W1c7.mint_univ_not_pwo (@h (Multiplicative ℤ) _ _ _ ∅ Set.univ Set.isPWO_empty)

-- `Finset.isPWO_support_antidiagonal` idx 6: necessary (Int, s = univ)
theorem w7_175 : ¬ indep0% Finset.isPWO_support_antidiagonal 6 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ Set.univ ∅ Set.isPWO_empty)

-- `Finset.isPWO_support_antidiagonal` idx 7: necessary (Int, t = univ)
theorem w7_176 : ¬ indep0% Finset.isPWO_support_antidiagonal 7 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ ∅ Set.univ Set.isPWO_empty)

-- `Finset.isPWO_support_mulAntidiagonal` idx 6: necessary (Multiplicative Int, s = univ)
theorem w7_177 : ¬ indep0% Finset.isPWO_support_mulAntidiagonal 6 := by
  intro h
  exact W1c7.mint_univ_not_pwo (@h (Multiplicative ℤ) _ _ _ Set.univ ∅ Set.isPWO_empty)

-- `Finset.isPWO_support_mulAntidiagonal` idx 7: necessary (Multiplicative Int, t = univ)
theorem w7_178 : ¬ indep0% Finset.isPWO_support_mulAntidiagonal 7 := by
  intro h
  exact W1c7.mint_univ_not_pwo (@h (Multiplicative ℤ) _ _ _ ∅ Set.univ Set.isPWO_empty)

-- `Finset.antidiagonal_min_add_min` idx 6: necessary (Int, s = univ, t = {0})
theorem w7_179 : ¬ indep0% Finset.antidiagonal_min_add_min 6 := by
  intro h
  exact W1c7.int_univ_not_wf (@h ℤ _ _ _ Set.univ {0} Set.isWF_singleton Set.univ_nonempty (Set.singleton_nonempty 0))

-- `Finset.antidiagonal_min_add_min` idx 7: necessary (Int, s = {0}, t = univ)
theorem w7_180 : ¬ indep0% Finset.antidiagonal_min_add_min 7 := by
  intro h
  exact W1c7.int_univ_not_wf (@h ℤ _ _ _ {0} Set.univ Set.isWF_singleton (Set.singleton_nonempty 0) Set.univ_nonempty)

-- `Finset.mulAntidiagonal_min_mul_min` idx 6: necessary (Multiplicative Int, s = univ, t = {1})
theorem w7_181 : ¬ indep0% Finset.mulAntidiagonal_min_mul_min 6 := by
  intro h
  exact W1c7.mint_univ_not_wf (@h (Multiplicative ℤ) _ _ _ Set.univ {1} Set.isWF_singleton Set.univ_nonempty (Set.singleton_nonempty 1))

-- `Finset.mulAntidiagonal_min_mul_min` idx 7: necessary (Multiplicative Int, s = {1}, t = univ)
theorem w7_182 : ¬ indep0% Finset.mulAntidiagonal_min_mul_min 7 := by
  intro h
  exact W1c7.mint_univ_not_wf (@h (Multiplicative ℤ) _ _ _ {1} Set.univ Set.isWF_singleton (Set.singleton_nonempty 1) Set.univ_nonempty)

-- `Finset.mulAntidiagonal_min_mul_min` idx 8: necessary (s = empty)
theorem w7_183 : ¬ indep0% Finset.mulAntidiagonal_min_mul_min 8 := by
  intro h
  exact Set.not_nonempty_empty (@h (Multiplicative ℤ) _ _ _ ∅ {1} Set.finite_empty.isWF Set.isWF_singleton (Set.singleton_nonempty 1))

-- `Finset.mulAntidiagonal_min_mul_min` idx 9: necessary (t = empty)
theorem w7_184 : ¬ indep0% Finset.mulAntidiagonal_min_mul_min 9 := by
  intro h
  exact Set.not_nonempty_empty (@h (Multiplicative ℤ) _ _ _ {1} ∅ Set.isWF_singleton Set.finite_empty.isWF (Set.singleton_nonempty 1))

-- `Finset.mem_addAntidiagonal` idx 6: necessary (Int, s = univ)
theorem w7_185 : ¬ indep0% Finset.mem_addAntidiagonal 6 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ Set.univ ∅ Set.isPWO_empty 0 (0, 0))

-- `Finset.mem_addAntidiagonal` idx 7: necessary (Int, t = univ)
theorem w7_186 : ¬ indep0% Finset.mem_addAntidiagonal 7 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ ∅ Set.univ Set.isPWO_empty 0 (0, 0))

-- `Finset.addAntidiagonal_mono_left` idx 6: necessary (Int, s = univ, u = empty)
theorem w7_187 : ¬ indep0% Finset.addAntidiagonal_mono_left 6 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ Set.univ ∅ Set.isPWO_empty 0 ∅ Set.isPWO_empty (Set.empty_subset _))

-- `Finset.addAntidiagonal_mono_left` idx 7: necessary (Int, t = univ, u = empty)
theorem w7_188 : ¬ indep0% Finset.addAntidiagonal_mono_left 7 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ ∅ Set.univ Set.isPWO_empty 0 ∅ Set.isPWO_empty (Set.empty_subset _))

-- `Finset.addAntidiagonal_mono_left` idx 10: removable (derivable: u is a subset of s and s.IsPWO, so u.IsPWO by IsPWO.mono)
theorem w7_189 : indep% Finset.addAntidiagonal_mono_left 10 := by
  intro α _ _ _ s t hs ht a u hu; exact hs.mono hu

-- `Finset.addAntidiagonal_mono_left` idx 11: necessary (ℕ, u = {0} not a subset of the empty set: (z,z) in the left antidiagonal only)
theorem w7_190 : ¬ drop0% Finset.addAntidiagonal_mono_left 11 := by
  intro h
  have hm : ((0 : ℕ), (0 : ℕ)) ∈ Finset.antidiagonal (Set.isPWO_singleton (0 : ℕ)) (Set.isPWO_singleton (0 : ℕ)) 0 := by simp [Finset.mem_antidiagonal]
  have := @h ℕ _ _ _ ∅ {0} (Set.isPWO_empty (α := ℕ)) (Set.isPWO_singleton (0 : ℕ)) 0 {0} (Set.isPWO_singleton (0 : ℕ)) (0, 0) hm; simp [Finset.mem_antidiagonal] at this

-- `Finset.addAntidiagonal_mono_right` idx 6: necessary (Int, s = univ, u = empty)
theorem w7_191 : ¬ indep0% Finset.addAntidiagonal_mono_right 6 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ Set.univ ∅ Set.isPWO_empty 0 ∅ Set.isPWO_empty (Set.empty_subset _))

-- `Finset.addAntidiagonal_mono_right` idx 7: necessary (Int, t = univ, u = empty)
theorem w7_192 : ¬ indep0% Finset.addAntidiagonal_mono_right 7 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ ∅ Set.univ Set.isPWO_empty 0 ∅ Set.isPWO_empty (Set.empty_subset _))

-- `Finset.addAntidiagonal_mono_right` idx 10: removable (derivable: u is a subset of t and t.IsPWO, so u.IsPWO by IsPWO.mono)
theorem w7_193 : indep% Finset.addAntidiagonal_mono_right 10 := by
  intro α _ _ _ s t hs ht a u hu; exact ht.mono hu

-- `Finset.addAntidiagonal_mono_right` idx 11: necessary (ℕ, u = {0} not a subset of the empty set: (z,z) in the left antidiagonal only)
theorem w7_194 : ¬ drop0% Finset.addAntidiagonal_mono_right 11 := by
  intro h
  have hm : ((0 : ℕ), (0 : ℕ)) ∈ Finset.antidiagonal (Set.isPWO_singleton (0 : ℕ)) (Set.isPWO_singleton (0 : ℕ)) 0 := by simp [Finset.mem_antidiagonal]
  have := @h ℕ _ _ _ {0} ∅ (Set.isPWO_singleton (0 : ℕ)) (Set.isPWO_empty (α := ℕ)) 0 {0} (Set.isPWO_singleton (0 : ℕ)) (0, 0) hm; simp [Finset.mem_antidiagonal] at this

-- `Finset.swap_mem_addAntidiagonal` idx 6: necessary (Int, s = univ)
theorem w7_195 : ¬ indep0% Finset.swap_mem_addAntidiagonal 6 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ Set.univ ∅ Set.isPWO_empty 0 (0, 0))

-- `Finset.swap_mem_addAntidiagonal` idx 7: necessary (Int, t = univ)
theorem w7_196 : ¬ indep0% Finset.swap_mem_addAntidiagonal 7 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ ∅ Set.univ Set.isPWO_empty 0 (0, 0))

-- `Finset.support_addAntidiagonal_subset_add` idx 6: necessary (Int, s = univ)
theorem w7_197 : ¬ indep0% Finset.support_addAntidiagonal_subset_add 6 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ Set.univ ∅ Set.isPWO_empty)

-- `Finset.support_addAntidiagonal_subset_add` idx 7: necessary (Int, t = univ)
theorem w7_198 : ¬ indep0% Finset.support_addAntidiagonal_subset_add 7 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ ∅ Set.univ Set.isPWO_empty)

-- `Finset.isPWO_support_addAntidiagonal` idx 6: necessary (Int, s = univ)
theorem w7_199 : ¬ indep0% Finset.isPWO_support_addAntidiagonal 6 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ Set.univ ∅ Set.isPWO_empty)

-- `Finset.isPWO_support_addAntidiagonal` idx 7: necessary (Int, t = univ)
theorem w7_200 : ¬ indep0% Finset.isPWO_support_addAntidiagonal 7 := by
  intro h
  exact W1c7.int_univ_not_pwo (@h ℤ _ _ _ ∅ Set.univ Set.isPWO_empty)

-- `Finset.addAntidiagonal_min_mul_min` idx 6: necessary (Int, s = univ, t = {0})
theorem w7_201 : ¬ indep0% Finset.addAntidiagonal_min_mul_min 6 := by
  intro h
  exact W1c7.int_univ_not_wf (@h ℤ _ _ _ Set.univ {0} Set.isWF_singleton Set.univ_nonempty (Set.singleton_nonempty 0))

-- `Finset.addAntidiagonal_min_mul_min` idx 7: necessary (Int, s = {0}, t = univ)
theorem w7_202 : ¬ indep0% Finset.addAntidiagonal_min_mul_min 7 := by
  intro h
  exact W1c7.int_univ_not_wf (@h ℤ _ _ _ {0} Set.univ Set.isWF_singleton (Set.singleton_nonempty 0) Set.univ_nonempty)
