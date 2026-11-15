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

namespace W2c0

abbrev P3 := Equiv.Perm (Fin 3)
/-- two non-commuting permutations of Fin 3 -/
def σ : P3 := Equiv.swap 0 1
def τ : P3 := Equiv.swap 1 2
abbrev A3 := Additive P3
def σ' : A3 := Additive.ofMul σ
def τ' : A3 := Additive.ofMul τ

theorem nc : ¬ Commute σ τ := by unfold Commute SemiconjBy; decide
theorem nc' : ¬ Commute τ σ := fun h => nc h.symm
theorem anc : ¬ AddCommute σ' τ' := by unfold AddCommute AddSemiconjBy; decide
theorem anc' : ¬ AddCommute τ' σ' := fun h => anc h.symm
theorem st : σ ≠ τ := by decide
theorem st' : σ' ≠ τ' := by decide

/-- 0 ↦ σ, else τ -/
def fp (n : ℕ) : P3 := if n = 0 then σ else τ
def fa (n : ℕ) : A3 := if n = 0 then σ' else τ'
/-- 0 ↦ σ, else 1 ; and 0 ↦ 1, else τ -/
def f1 (n : ℕ) : P3 := if n = 0 then σ else 1
def g1 (n : ℕ) : P3 := if n = 0 then 1 else τ
def f1a (n : ℕ) : A3 := if n = 0 then σ' else 0
def g1a (n : ℕ) : A3 := if n = 0 then 0 else τ'

/-- a set with two distinct elements not related is not pairwise related -/
theorem np {α : Type*} {S : Set α} {r : α → α → Prop} {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y)
    (hr : ¬ r x y) : ¬ S.Pairwise r := fun h => hr (h hx hy hne)

/-- pairwise on the pair {0,1} of naturals -/
theorem pw2 {r : ℕ → ℕ → Prop} (h01 : r 0 1) (h10 : r 1 0) : (↑({0, 1} : Finset ℕ) : Set ℕ).Pairwise r := by
  intro x hx y hy hxy
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | exact absurd rfl hxy | assumption

/-- pairwise on a singleton multiset -/
theorem pwm1 {α : Type*} (a : α) (r : α → α → Prop) : {x | x ∈ ({a} : Multiset α)}.Pairwise r := by
  intro x hx y hy hxy
  exact absurd ((Multiset.mem_singleton.1 hx).trans (Multiset.mem_singleton.1 hy).symm) hxy

theorem pwm0 {α : Type*} (r : α → α → Prop) : {x | x ∈ (0 : Multiset α)}.Pairwise r := by
  intro x hx; exact absurd hx (Multiset.notMem_zero x)

/-- a bare function type: FunLike with arbitrary (non-hom) maps -/
structure FW (α β : Type) where
  toFun : α → β

instance (α β : Type) : FunLike (FW α β) α β where
  coe := FW.toFun
  coe_injective := by intro f g h; cases f; cases g; cases h; rfl

end W2c0

namespace W2c0

/-- finitely supported functions from the naturals to the integers (range of the coercion from finsupps) -/
noncomputable def FS : AddSubgroup (ℕ → ℤ) := (Finsupp.coeFnAddHom : (ℕ →₀ ℤ) →+ ℕ → ℤ).range

theorem single_mem (i : ℕ) (x : ℤ) : Pi.single i x ∈ FS :=
  ⟨Finsupp.single i x, Finsupp.single_eq_pi_single i x⟩

theorem one_notMem : (fun _ => (1 : ℤ)) ∉ FS := by
  rintro ⟨g, hg⟩
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset g.support
  have h1 : g n = 1 := congrFun hg n
  rw [Finsupp.notMem_support_iff] at hn
  omega

end W2c0

-- `Finset.card_image₂` idx 5: necessary (f = const 0, s = t = {0,1})
theorem w0_0 : ¬ drop0% Finset.card_image₂ 5 := fun h =>
  absurd (h (f := fun (_ _ : ℕ) => (0 : ℕ)) ({0, 1} : Finset ℕ) ({0, 1} : Finset ℕ)) (by decide)
-- `Finset.mem_image₂_of_mem` idx 9: necessary (s = ∅, t = {0})
theorem w0_1 : ¬ drop0% Finset.mem_image₂_of_mem 9 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (s := (∅ : Finset ℕ)) (t := ({0} : Finset ℕ)) (a := 0) (b := 0) (by decide)) (by decide)
-- `Finset.mem_image₂_of_mem` idx 10: necessary (s = {0}, t = ∅)
theorem w0_2 : ¬ drop0% Finset.mem_image₂_of_mem 10 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (s := ({0} : Finset ℕ)) (t := (∅ : Finset ℕ)) (a := 0) (b := 0) (by decide)) (by decide)
-- `Finset.mem_image₂_iff` idx 9: necessary (f = const 0, s = t = {0}, a = b = 1)
theorem w0_3 : ¬ drop0% Finset.mem_image₂_iff 9 := fun h =>
  absurd (h (f := fun (_ _ : ℕ) => (0 : ℕ)) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ)) (a := 1) (b := 1)) (by decide)
-- `Finset.image₂_subset` idx 9: necessary (s = {0}, s' = ∅)
theorem w0_4 : ¬ drop0% Finset.image₂_subset 9 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (s := ({0} : Finset ℕ)) (s' := ∅) (t := ({0} : Finset ℕ)) (t' := {0}) (by decide)) (by decide)
-- `Finset.image₂_subset` idx 10: necessary (t = {0}, t' = ∅)
theorem w0_5 : ¬ drop0% Finset.image₂_subset 10 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (s := ({0} : Finset ℕ)) (s' := {0}) (t := ({0} : Finset ℕ)) (t' := ∅) (by decide)) (by decide)
-- `Finset.image₂_subset_left` idx 8: necessary (t = {0}, t' = ∅)
theorem w0_6 : ¬ drop0% Finset.image₂_subset_left 8 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ)) (t' := ∅)) (by decide)
-- `Finset.image₂_subset_right` idx 8: necessary (s = {0}, s' = ∅)
theorem w0_7 : ¬ drop0% Finset.image₂_subset_right 8 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (s := ({0} : Finset ℕ)) (s' := ∅) (t := ({0} : Finset ℕ))) (by decide)
-- `Finset.image_subset_image₂_left` idx 8: necessary (s = {0}, t = ∅)
theorem w0_8 : ¬ drop0% Finset.image_subset_image₂_left 8 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (s := ({0} : Finset ℕ)) (t := (∅ : Finset ℕ)) (b := 0)) (by decide)
-- `Finset.image_subset_image₂_right` idx 8: necessary (s = ∅, t = {0})
theorem w0_9 : ¬ drop0% Finset.image_subset_image₂_right 8 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (s := (∅ : Finset ℕ)) (t := ({0} : Finset ℕ)) (a := 0)) (by decide)
-- `Finset.Nonempty.image₂` idx 7: necessary (s = ∅, t = {0})
theorem w0_10 : ¬ drop0% Finset.Nonempty.image₂ 7 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (s := (∅ : Finset ℕ)) (t := ({0} : Finset ℕ)) (Finset.singleton_nonempty 0)) (by simp)
-- `Finset.Nonempty.image₂` idx 8: necessary (s = {0}, t = ∅)
theorem w0_11 : ¬ drop0% Finset.Nonempty.image₂ 8 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (s := ({0} : Finset ℕ)) (t := (∅ : Finset ℕ)) (Finset.singleton_nonempty 0)) (by simp)
-- `Finset.image₂_inter_left` idx 9: necessary (f = const 0, s = {0}, s' = {1}, t = {0})
theorem w0_12 : ¬ drop0% Finset.image₂_inter_left 9 := fun h =>
  absurd (h (f := fun (_ _ : ℕ) => (0 : ℕ)) (s := ({0} : Finset ℕ)) (s' := {1}) (t := ({0} : Finset ℕ))) (by decide)
-- `Finset.image₂_inter_right` idx 9: necessary (f = const 0, t = {0}, t' = {1}, s = {0})
theorem w0_13 : ¬ drop0% Finset.image₂_inter_right 9 := fun h =>
  absurd (h (f := fun (_ _ : ℕ) => (0 : ℕ)) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ)) (t' := {1})) (by decide)
-- `Finset.image₂_congr` idx 8: necessary (f = add, f' = const 5)
theorem w0_14 : ¬ drop0% Finset.image₂_congr 8 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (f' := fun _ _ => 5) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ))) (by decide)
-- `Finset.image₂_congr'` idx 8: necessary (f = add, f' = const 5)
theorem w0_15 : ¬ drop0% Finset.image₂_congr' 8 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (f' := fun _ _ => 5) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ))) (by decide)
-- `Finset.image₂_singleton_inter` idx 9: necessary (f = const 0, t₁ = {0}, t₂ = {1})
theorem w0_16 : ¬ drop0% Finset.image₂_singleton_inter 9 := fun h =>
  absurd (h (f := fun (_ _ : ℕ) => (0 : ℕ)) (a := 0) ({0} : Finset ℕ) {1}) (by decide)
-- `Finset.image₂_inter_singleton` idx 9: necessary (f = const 0, s₁ = {0}, s₂ = {1})
theorem w0_17 : ¬ drop0% Finset.image₂_inter_singleton 9 := fun h =>
  absurd (h (f := fun (_ _ : ℕ) => (0 : ℕ)) (b := 0) ({0} : Finset ℕ) {1}) (by decide)
-- `Finset.card_le_card_image₂_left` idx 8: necessary (s = ∅, t = {0}, f = add)
theorem w0_18 : ¬ drop0% Finset.card_le_card_image₂_left 8 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (s := (∅ : Finset ℕ)) (t := ({0} : Finset ℕ)) (a := 0) (add_right_injective 0)) (by decide)
-- `Finset.card_le_card_image₂_left` idx 9: necessary (f = const 0, s = {0}, t = {0,1})
theorem w0_19 : ¬ drop0% Finset.card_le_card_image₂_left 9 := fun h =>
  absurd (h (f := fun (_ _ : ℕ) => (0 : ℕ)) (s := ({0} : Finset ℕ)) (t := ({0, 1} : Finset ℕ)) (a := 0) (by decide)) (by decide)
-- `Finset.card_le_card_image₂_right` idx 8: necessary (t = ∅, s = {0}, f = add)
theorem w0_20 : ¬ drop0% Finset.card_le_card_image₂_right 8 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (s := ({0} : Finset ℕ)) (t := (∅ : Finset ℕ)) (b := 0) (add_left_injective 0)) (by decide)
-- `Finset.card_le_card_image₂_right` idx 9: necessary (f = const 0, s = {0,1}, t = {0})
theorem w0_21 : ¬ drop0% Finset.card_le_card_image₂_right 9 := fun h =>
  absurd (h (f := fun (_ _ : ℕ) => (0 : ℕ)) (s := ({0, 1} : Finset ℕ)) (t := ({0} : Finset ℕ)) (b := 0) (by decide)) (by decide)
-- `Finset.image₂_assoc` idx 16: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_22 : ¬ drop0% Finset.image₂_assoc 16 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (g := fun (a b : ℕ) => a + b) (g' := fun (a b : ℕ) => a + b) (f' := fun (_ _ : ℕ) => (1 : ℕ)) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ)) (u := ({0} : Finset ℕ))) (by decide)

-- `Finset.image₂_comm` idx 8: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_23 : ¬ drop0% Finset.image₂_comm 8 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (g := fun (_ _ : ℕ) => (1 : ℕ)) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ))) (by decide)

-- `Finset.image₂_left_comm` idx 16: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_24 : ¬ drop0% Finset.image₂_left_comm 16 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (g := fun (a b : ℕ) => a + b) (f' := fun (a b : ℕ) => a + b) (g' := fun (_ _ : ℕ) => (1 : ℕ)) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ)) (u := ({0} : Finset ℕ))) (by decide)

-- `Finset.image₂_right_comm` idx 16: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_25 : ¬ drop0% Finset.image₂_right_comm 16 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (g := fun (a b : ℕ) => a + b) (f' := fun (a b : ℕ) => a + b) (g' := fun (_ _ : ℕ) => (1 : ℕ)) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ)) (u := ({0} : Finset ℕ))) (by decide)

-- `Finset.image_image₂_distrib` idx 17: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_26 : ¬ drop0% Finset.image_image₂_distrib 17 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (f' := fun (_ _ : ℕ) => (1 : ℕ)) (g := fun (a : ℕ) => a) (g₁ := fun (a : ℕ) => a) (g₂ := fun (a : ℕ) => a) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ))) (by decide)

-- `Finset.image_image₂_distrib_left` idx 14: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_27 : ¬ drop0% Finset.image_image₂_distrib_left 14 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (f' := fun (_ _ : ℕ) => (1 : ℕ)) (g := fun (a : ℕ) => a) (g' := fun (a : ℕ) => a) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ))) (by decide)

-- `Finset.image_image₂_distrib_right` idx 14: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_28 : ¬ drop0% Finset.image_image₂_distrib_right 14 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (f' := fun (_ _ : ℕ) => (1 : ℕ)) (g := fun (a : ℕ) => a) (g' := fun (a : ℕ) => a) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ))) (by decide)

-- `Finset.image₂_image_left_comm` idx 14: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_29 : ¬ drop0% Finset.image₂_image_left_comm 14 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (f' := fun (a b : ℕ) => a + b) (g := fun (a : ℕ) => a) (g' := fun (_ : ℕ) => (1 : ℕ)) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ))) (by decide)

-- `Finset.image_image₂_right_comm` idx 14: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_30 : ¬ drop0% Finset.image_image₂_right_comm 14 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (f' := fun (a b : ℕ) => a + b) (g := fun (a : ℕ) => a) (g' := fun (_ : ℕ) => (1 : ℕ)) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ))) (by decide)

-- `Finset.image₂_distrib_subset_left` idx 19: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_31 : ¬ drop0% Finset.image₂_distrib_subset_left 19 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (g := fun (a b : ℕ) => a + b) (f₁ := fun (a b : ℕ) => a + b) (f₂ := fun (a b : ℕ) => a + b) (g' := fun (_ _ : ℕ) => (1 : ℕ)) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ)) (u := ({0} : Finset ℕ))) (by decide)

-- `Finset.image₂_distrib_subset_right` idx 19: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_32 : ¬ drop0% Finset.image₂_distrib_subset_right 19 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (g := fun (a b : ℕ) => a + b) (f₁ := fun (a b : ℕ) => a + b) (f₂ := fun (a b : ℕ) => a + b) (g' := fun (_ _ : ℕ) => (1 : ℕ)) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ)) (u := ({0} : Finset ℕ))) (by decide)

-- `Finset.image_image₂_antidistrib` idx 17: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_33 : ¬ drop0% Finset.image_image₂_antidistrib 17 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (f' := fun (_ _ : ℕ) => (1 : ℕ)) (g := fun (a : ℕ) => a) (g₁ := fun (a : ℕ) => a) (g₂ := fun (a : ℕ) => a) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ))) (by decide)

-- `Finset.image_image₂_antidistrib_left` idx 14: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_34 : ¬ drop0% Finset.image_image₂_antidistrib_left 14 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (f' := fun (_ _ : ℕ) => (1 : ℕ)) (g := fun (a : ℕ) => a) (g' := fun (a : ℕ) => a) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ))) (by decide)

-- `Finset.image_image₂_antidistrib_right` idx 14: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_35 : ¬ drop0% Finset.image_image₂_antidistrib_right 14 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (f' := fun (_ _ : ℕ) => (1 : ℕ)) (g := fun (a : ℕ) => a) (g' := fun (a : ℕ) => a) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ))) (by decide)

-- `Finset.image₂_image_left_anticomm` idx 14: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_36 : ¬ drop0% Finset.image₂_image_left_anticomm 14 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (f' := fun (a b : ℕ) => a + b) (g := fun (a : ℕ) => a) (g' := fun (_ : ℕ) => (1 : ℕ)) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ))) (by decide)

-- `Finset.image_image₂_right_anticomm` idx 14: necessary (all sets {0}, the outermost function of the right side constant 1, others add/id)
theorem w0_37 : ¬ drop0% Finset.image_image₂_right_anticomm 14 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (f' := fun (a b : ℕ) => a + b) (g := fun (a : ℕ) => a) (g' := fun (_ : ℕ) => (1 : ℕ)) (s := ({0} : Finset ℕ)) (t := ({0} : Finset ℕ))) (by decide)
-- `Finset.card_dvd_card_image₂_right` idx 7: necessary (f = const 0, s = {0}, t = {0,1})
theorem w0_38 : ¬ drop0% Finset.card_dvd_card_image₂_right 7 := fun h =>
  absurd (h (f := fun (_ _ : ℕ) => (0 : ℕ)) (s := ({0} : Finset ℕ)) (t := ({0, 1} : Finset ℕ))
    (by simp)) (by decide)
-- `Finset.card_dvd_card_image₂_right` idx 8: necessary (f = add, s = t = {0,1}: 2 does not divide 3)
theorem w0_39 : ¬ drop0% Finset.card_dvd_card_image₂_right 8 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (s := ({0, 1} : Finset ℕ)) (t := ({0, 1} : Finset ℕ))
    (fun a _ => add_right_injective a)) (by decide)
-- `Finset.card_dvd_card_image₂_left` idx 7: necessary (f = const 0, t = {0}, s = {0,1})
theorem w0_40 : ¬ drop0% Finset.card_dvd_card_image₂_left 7 := fun h =>
  absurd (h (f := fun (_ _ : ℕ) => (0 : ℕ)) (s := ({0, 1} : Finset ℕ)) (t := ({0} : Finset ℕ))
    (by simp)) (by decide)
-- `Finset.card_dvd_card_image₂_left` idx 8: necessary (f = add, s = t = {0,1})
theorem w0_41 : ¬ drop0% Finset.card_dvd_card_image₂_left 8 := fun h =>
  absurd (h (f := fun (a b : ℕ) => a + b) (s := ({0, 1} : Finset ℕ)) (t := ({0, 1} : Finset ℕ))
    (fun b _ => add_left_injective b)) (by decide)
-- `Finset.subset_set_image₂` idx 8: necessary (s = t = ∅, u = {0})
theorem w0_42 : ¬ drop0% Finset.subset_set_image₂ 8 := fun h => by
  obtain ⟨s', t', hs, ht, hu⟩ := h (f := fun (a b : ℕ) => a + b) (u := ({0} : Finset ℕ)) (s := (∅ : Set ℕ)) (t := (∅ : Set ℕ))
  have : s' = ∅ := Finset.coe_eq_empty.1 (Set.subset_empty_iff.1 hs)
  subst this; simp at hu
-- `Finset.image₂_inter_union_subset` idx 7: necessary (f a b = b, s = {0,1}, t = {1})
theorem w0_43 : ¬ drop0% Finset.image₂_inter_union_subset 7 := fun h =>
  absurd (h (f := fun (_ b : ℕ) => b) (s := ({0, 1} : Finset ℕ)) (t := {1})) (by decide)
-- `Finset.image₂_union_inter_subset` idx 7: necessary (f a b = a, s = {1}, t = {0,1})
theorem w0_44 : ¬ drop0% Finset.image₂_union_inter_subset 7 := fun h =>
  absurd (h (f := fun (a _ : ℕ) => a) (s := ({1} : Finset ℕ)) (t := {0, 1})) (by decide)
-- `Set.Finite.toFinset_image2` idx 7: necessary (s = univ of ℕ, t = ∅)
theorem w0_45 : ¬ indep0% Set.Finite.toFinset_image2 7 := fun h =>
  Set.infinite_univ (h (s := (Set.univ : Set ℕ)) (t := (∅ : Set ℕ)) (fun (a b : ℕ) => a + b) Set.finite_empty)
-- `Set.Finite.toFinset_image2` idx 8: necessary (s = ∅, t = univ of ℕ)
theorem w0_46 : ¬ indep0% Set.Finite.toFinset_image2 8 := fun h =>
  Set.infinite_univ (h (s := (∅ : Set ℕ)) (t := (Set.univ : Set ℕ)) (fun (a b : ℕ) => a + b) Set.finite_empty)
-- `Set.Finite.toFinset_image2` idx 9: removable (optParam, derivable from hs and ht: Set.Finite.image2)
theorem w0_47 : indep% Set.Finite.toFinset_image2 9 := fun f hs ht => hs.image2 f ht

-- `Multiset.noncommFoldr_cons` idx 5: necessary (f = multiplication in Perm (Fin 3), s = {τ}, a = σ)
theorem w0_48 : ¬ indep0% Multiset.noncommFoldr_cons 5 := fun h =>
  W2c0.np (x := W2c0.σ) (y := W2c0.τ) (by simp) (by simp) W2c0.st (fun hh => absurd (hh 1) (by decide))
    (h (fun (x y : W2c0.P3) => x * y) {W2c0.τ} W2c0.σ (W2c0.pwm1 _ _) 1)
-- `Multiset.noncommFoldr_cons` idx 6: removable (derivable from h: s is a sub-multiset of a ::ₘ s)
theorem w0_49 : indep% Multiset.noncommFoldr_cons 6 := fun f s a h b =>
  Set.Pairwise.mono (fun x hx => Multiset.mem_cons_of_mem hx) h
-- `Multiset.noncommFold_coe` idx 4: necessary (op = multiplication in Perm (Fin 3), l = [σ, τ])
theorem w0_50 : ¬ indep0% Multiset.noncommFold_coe 4 := fun h =>
  W2c0.np (x := W2c0.σ) (y := W2c0.τ) (by simp) (by simp) W2c0.st (by show ¬ W2c0.σ * W2c0.τ = W2c0.τ * W2c0.σ; decide)
    (h (fun (x y : W2c0.P3) => x * y) [W2c0.σ, W2c0.τ] 1)
-- `Multiset.noncommFold_cons` idx 5: necessary (op = multiplication in Perm (Fin 3), s = {τ}, a = σ)
theorem w0_51 : ¬ indep0% Multiset.noncommFold_cons 5 := fun h =>
  W2c0.np (x := W2c0.σ) (y := W2c0.τ) (by simp) (by simp) W2c0.st (by show ¬ W2c0.σ * W2c0.τ = W2c0.τ * W2c0.σ; decide)
    (h (fun (x y : W2c0.P3) => x * y) {W2c0.τ} W2c0.σ (W2c0.pwm1 _ _) 1)
-- `Multiset.noncommFold_cons` idx 6: removable (derivable from h: s is a sub-multiset of a ::ₘ s)
theorem w0_52 : indep% Multiset.noncommFold_cons 6 := by
  intro α op _ s a h x
  exact Set.Pairwise.mono (fun y hy => Multiset.mem_cons_of_mem hy) h
-- `Multiset.noncommSum_coe` idx 3: necessary (l = [σ, τ] in Additive (Perm (Fin 3)))
theorem w0_53 : ¬ indep0% Multiset.noncommSum_coe 3 := fun h =>
  W2c0.np (x := W2c0.σ') (y := W2c0.τ') (by simp) (by simp) W2c0.st' W2c0.anc (h (l := [W2c0.σ', W2c0.τ']))
-- `Multiset.noncommProd_coe` idx 3: necessary (l = [σ, τ] in Perm (Fin 3))
theorem w0_54 : ¬ indep0% Multiset.noncommProd_coe 3 := fun h =>
  W2c0.np (x := W2c0.σ) (y := W2c0.τ) (by simp) (by simp) W2c0.st W2c0.nc (h (l := [W2c0.σ, W2c0.τ]))
-- `Multiset.noncommSum_cons` idx 4: necessary (s = {τ}, a = σ, additive)
theorem w0_55 : ¬ indep0% Multiset.noncommSum_cons 4 := fun h =>
  W2c0.np (x := W2c0.σ') (y := W2c0.τ') (by simp) (by simp) W2c0.st' W2c0.anc (h {W2c0.τ'} W2c0.σ')
-- `Multiset.noncommProd_cons` idx 4: necessary (s = {τ}, a = σ)
theorem w0_56 : ¬ indep0% Multiset.noncommProd_cons 4 := fun h =>
  W2c0.np (x := W2c0.σ) (y := W2c0.τ) (by simp) (by simp) W2c0.st W2c0.nc (h {W2c0.τ} W2c0.σ)
-- `Multiset.noncommSum_cons'` idx 4: necessary (s = {τ}, a = σ, additive)
theorem w0_57 : ¬ indep0% Multiset.noncommSum_cons' 4 := fun h =>
  W2c0.np (x := W2c0.σ') (y := W2c0.τ') (by simp) (by simp) W2c0.st' W2c0.anc (h {W2c0.τ'} W2c0.σ')
-- `Multiset.noncommProd_cons'` idx 4: necessary (s = {τ}, a = σ)
theorem w0_58 : ¬ indep0% Multiset.noncommProd_cons' 4 := fun h =>
  W2c0.np (x := W2c0.σ) (y := W2c0.τ) (by simp) (by simp) W2c0.st W2c0.nc (h {W2c0.τ} W2c0.σ)
-- `Multiset.noncommSum_add` idx 4: necessary (s = {σ}, t = {τ}, additive)
theorem w0_59 : ¬ indep0% Multiset.noncommSum_add 4 := fun h =>
  W2c0.np (x := W2c0.σ') (y := W2c0.τ') (by simp) (by simp) W2c0.st' W2c0.anc (h {W2c0.σ'} {W2c0.τ'})
-- `Multiset.noncommProd_add` idx 4: necessary (s = {σ}, t = {τ})
theorem w0_60 : ¬ indep0% Multiset.noncommProd_add 4 := fun h =>
  W2c0.np (x := W2c0.σ) (y := W2c0.τ) (by simp) (by simp) W2c0.st W2c0.nc (h {W2c0.σ} {W2c0.τ})
-- `Multiset.noncommSum_induction` idx 3: necessary (s = [σ, τ] additive, p = True)
theorem w0_61 : ¬ indep0% Multiset.noncommSum_induction 3 := fun h =>
  W2c0.np (x := W2c0.σ') (y := W2c0.τ') (by simp) (by simp) W2c0.st' W2c0.anc
    (h (↑[W2c0.σ', W2c0.τ'] : Multiset W2c0.A3) (fun _ => True) (fun _ _ _ _ => trivial) trivial (fun _ _ => trivial))
-- `Multiset.noncommSum_induction` idx 5: necessary (ℕ, s = [1,1], p n = n ≠ 2)
theorem w0_62 : ¬ drop0% Multiset.noncommSum_induction 5 := fun h => by
  have := h (↑[1, 1] : Multiset ℕ) (fun _ _ _ _ _ => AddCommute.all _ _) (fun n => n ≠ 2) (by decide) (by simp)
  simp [Multiset.noncommSum_eq_sum] at this
-- `Multiset.noncommSum_induction` idx 7: necessary (ℕ, s = [1], p n = n = 0)
theorem w0_63 : ¬ drop0% Multiset.noncommSum_induction 7 := fun h => by
  have := h (↑[1] : Multiset ℕ) (fun _ _ _ _ _ => AddCommute.all _ _) (fun n => n = 0)
    (fun a b (ha : a = 0) (hb : b = 0) => by subst ha; subst hb; rfl) rfl
  simp [Multiset.noncommSum_eq_sum] at this
-- `Multiset.noncommProd_induction` idx 3: necessary (s = [σ, τ], p = True)
theorem w0_64 : ¬ indep0% Multiset.noncommProd_induction 3 := fun h =>
  W2c0.np (x := W2c0.σ) (y := W2c0.τ) (by simp) (by simp) W2c0.st W2c0.nc
    (h (↑[W2c0.σ, W2c0.τ] : Multiset W2c0.P3) (fun _ => True) (fun _ _ _ _ => trivial) trivial (fun _ _ => trivial))
-- `Multiset.noncommProd_induction` idx 5: necessary (ℕ, s = [2,2], p n = n ≠ 4)
theorem w0_65 : ¬ drop0% Multiset.noncommProd_induction 5 := fun h => by
  have := h (↑[2, 2] : Multiset ℕ) (fun _ _ _ _ _ => Commute.all _ _) (fun n => n ≠ 4) (by decide) (by simp)
  simp [Multiset.noncommProd_eq_prod] at this
-- `Multiset.noncommProd_induction` idx 7: necessary (ℕ, s = [2], p n = n = 1)
theorem w0_66 : ¬ drop0% Multiset.noncommProd_induction 7 := fun h => by
  have := h (↑[2] : Multiset ℕ) (fun _ _ _ _ _ => Commute.all _ _) (fun n => n = 1)
    (fun a b (ha : a = 1) (hb : b = 1) => by subst ha; subst hb; rfl) rfl
  simp [Multiset.noncommProd_eq_prod] at this
-- `Multiset.map_noncommSum_aux` idx 6: necessary (non-additive map ℕ → Additive (Perm (Fin 3)), 0 ↦ σ, 1 ↦ τ)
theorem w0_67 : ¬ drop0% Multiset.map_noncommSum_aux 6 := fun h =>
  W2c0.np (x := (⟨W2c0.fa⟩ : W2c0.FW ℕ W2c0.A3) 0) (y := (⟨W2c0.fa⟩ : W2c0.FW ℕ W2c0.A3) 1) (Multiset.mem_map_of_mem _ (by simp : (0 : ℕ) ∈ (↑[0, 1] : Multiset ℕ)))
    (Multiset.mem_map_of_mem _ (by simp : (1 : ℕ) ∈ (↑[0, 1] : Multiset ℕ))) (by decide) W2c0.anc
    (h (F := W2c0.FW ℕ W2c0.A3) (α := ℕ) (β := W2c0.A3) (↑[0, 1] : Multiset ℕ) (fun _ _ _ _ _ => AddCommute.all _ _) ⟨W2c0.fa⟩)
-- `Multiset.map_noncommSum_aux` idx 8: necessary (f = identity hom, s = [σ, τ] additive)
theorem w0_68 : ¬ drop0% Multiset.map_noncommSum_aux 8 := fun h =>
  W2c0.np (Multiset.mem_map_of_mem _ (by simp : W2c0.σ' ∈ (↑[W2c0.σ', W2c0.τ'] : Multiset W2c0.A3)))
    (Multiset.mem_map_of_mem _ (by simp : W2c0.τ' ∈ (↑[W2c0.σ', W2c0.τ'] : Multiset W2c0.A3)))
    (by simpa using W2c0.st') (by simpa using W2c0.anc)
    (h (F := W2c0.A3 →+ W2c0.A3) (↑[W2c0.σ', W2c0.τ'] : Multiset W2c0.A3) (AddMonoidHom.id W2c0.A3))
-- `Multiset.map_noncommProd_aux` idx 6: necessary (non-multiplicative map ℕ → Perm (Fin 3), 0 ↦ σ, 1 ↦ τ)
theorem w0_69 : ¬ drop0% Multiset.map_noncommProd_aux 6 := fun h =>
  W2c0.np (x := (⟨W2c0.fp⟩ : W2c0.FW ℕ W2c0.P3) 0) (y := (⟨W2c0.fp⟩ : W2c0.FW ℕ W2c0.P3) 1) (Multiset.mem_map_of_mem _ (by simp : (0 : ℕ) ∈ (↑[0, 1] : Multiset ℕ)))
    (Multiset.mem_map_of_mem _ (by simp : (1 : ℕ) ∈ (↑[0, 1] : Multiset ℕ))) (by decide) W2c0.nc
    (h (F := W2c0.FW ℕ W2c0.P3) (α := ℕ) (β := W2c0.P3) (↑[0, 1] : Multiset ℕ) (fun _ _ _ _ _ => Commute.all _ _) ⟨W2c0.fp⟩)
-- `Multiset.map_noncommProd_aux` idx 8: necessary (f = identity hom, s = [σ, τ])
theorem w0_70 : ¬ drop0% Multiset.map_noncommProd_aux 8 := fun h =>
  W2c0.np (Multiset.mem_map_of_mem _ (by simp : W2c0.σ ∈ (↑[W2c0.σ, W2c0.τ] : Multiset W2c0.P3)))
    (Multiset.mem_map_of_mem _ (by simp : W2c0.τ ∈ (↑[W2c0.σ, W2c0.τ] : Multiset W2c0.P3)))
    (by simpa using W2c0.st) (by simpa using W2c0.nc)
    (h (F := W2c0.P3 →* W2c0.P3) (↑[W2c0.σ, W2c0.τ] : Multiset W2c0.P3) (MonoidHom.id W2c0.P3))
-- `Multiset.map_noncommSum` idx 6: necessary (F = all maps ℕ → ℕ, constant map 1 does not preserve 0)
theorem w0_71 : ¬ indep0% Multiset.map_noncommSum 6 := fun h => by
  have inst := h (F := W2c0.FW ℕ ℕ) (α := ℕ) (β := ℕ) 0 (W2c0.pwm0 _) ⟨fun _ => 1⟩
  exact absurd (map_zero (⟨fun _ => 1⟩ : W2c0.FW ℕ ℕ)) (by decide)
-- `Multiset.map_noncommSum` idx 8: necessary (f = identity hom, s = [σ, τ] additive)
theorem w0_72 : ¬ indep0% Multiset.map_noncommSum 8 := fun h =>
  W2c0.np (x := W2c0.σ') (y := W2c0.τ') (by simp) (by simp) W2c0.st' W2c0.anc
    (h (F := W2c0.A3 →+ W2c0.A3) (↑[W2c0.σ', W2c0.τ'] : Multiset W2c0.A3) (AddMonoidHom.id W2c0.A3))
-- `Multiset.map_noncommProd` idx 6: necessary (F = all maps ℕ → ℕ, constant map 2 does not preserve 1)
theorem w0_73 : ¬ indep0% Multiset.map_noncommProd 6 := fun h => by
  have inst := h (F := W2c0.FW ℕ ℕ) (α := ℕ) (β := ℕ) 0 (W2c0.pwm0 _) ⟨fun _ => 2⟩
  exact absurd (map_one (⟨fun _ => 2⟩ : W2c0.FW ℕ ℕ)) (by decide)
-- `Multiset.map_noncommProd` idx 8: necessary (f = identity hom, s = [σ, τ])
theorem w0_74 : ¬ indep0% Multiset.map_noncommProd 8 := fun h =>
  W2c0.np (x := W2c0.σ) (y := W2c0.τ) (by simp) (by simp) W2c0.st W2c0.nc
    (h (F := W2c0.P3 →* W2c0.P3) (↑[W2c0.σ, W2c0.τ] : Multiset W2c0.P3) (MonoidHom.id W2c0.P3))
-- `Multiset.noncommSum_eq_card_nsmul` idx 3: removable (derivable from h: all elements equal m, so no two distinct ones)
theorem w0_75 : indep% Multiset.noncommSum_eq_card_nsmul 3 := fun s m h x hx y hy hxy =>
  absurd ((h x hx).trans (h y hy).symm) hxy
-- `Multiset.noncommProd_eq_pow_card` idx 3: removable (derivable from h: all elements equal m, so no two distinct ones)
theorem w0_76 : indep% Multiset.noncommProd_eq_pow_card 3 := fun s m h x hx y hy hxy =>
  absurd ((h x hx).trans (h y hy).symm) hxy
-- `Multiset.noncommSum_addCommute` idx 3: necessary (s = [σ, τ] additive, y = 0)
theorem w0_77 : ¬ indep0% Multiset.noncommSum_addCommute 3 := fun h =>
  W2c0.np (x := W2c0.σ') (y := W2c0.τ') (by simp) (by simp) W2c0.st' W2c0.anc
    (h (↑[W2c0.σ', W2c0.τ'] : Multiset W2c0.A3) 0 (fun x _ => AddCommute.zero_left x))
-- `Multiset.noncommSum_addCommute` idx 5: necessary (s = {σ}, y = τ additive)
theorem w0_78 : ¬ drop0% Multiset.noncommSum_addCommute 5 := fun h => by
  have := h ({W2c0.σ'} : Multiset W2c0.A3) (W2c0.pwm1 _ _) W2c0.τ'
  exact W2c0.anc' this
-- `Multiset.noncommProd_commute` idx 3: necessary (s = [σ, τ], y = 1)
theorem w0_79 : ¬ indep0% Multiset.noncommProd_commute 3 := fun h =>
  W2c0.np (x := W2c0.σ) (y := W2c0.τ) (by simp) (by simp) W2c0.st W2c0.nc
    (h (↑[W2c0.σ, W2c0.τ] : Multiset W2c0.P3) 1 (fun x _ => Commute.one_left x))
-- `Multiset.noncommProd_commute` idx 5: necessary (s = {σ}, y = τ)
theorem w0_80 : ¬ drop0% Multiset.noncommProd_commute 5 := fun h => by
  have := h ({W2c0.σ} : Multiset W2c0.P3) (W2c0.pwm1 _ _) W2c0.τ
  exact W2c0.nc' this
-- `Multiset.mul_noncommProd_erase` idx 6: necessary (s = [σ, τ], a = σ)
theorem w0_81 : ¬ indep0% Multiset.mul_noncommProd_erase 6 := fun h =>
  W2c0.np (x := W2c0.σ) (y := W2c0.τ) (by simp) (by simp) W2c0.st W2c0.nc
    (h (↑[W2c0.σ, W2c0.τ] : Multiset W2c0.P3) (a := W2c0.σ) (by simp))
-- `Multiset.mul_noncommProd_erase` idx 7: removable (optParam, derivable from comm by its default value)
theorem w0_82 : indep% Multiset.mul_noncommProd_erase 7 := fun s a h comm x hx y hy hxy =>
  comm (Multiset.mem_of_mem_erase hx) (Multiset.mem_of_mem_erase hy) hxy
-- `Multiset.noncommProd_erase_mul` idx 6: necessary (s = [σ, τ], a = σ)
theorem w0_83 : ¬ indep0% Multiset.noncommProd_erase_mul 6 := fun h =>
  W2c0.np (x := W2c0.σ) (y := W2c0.τ) (by simp) (by simp) W2c0.st W2c0.nc
    (h (↑[W2c0.σ, W2c0.τ] : Multiset W2c0.P3) (a := W2c0.σ) (by simp))
-- `Multiset.noncommProd_erase_mul` idx 7: removable (optParam, derivable from comm by its default value)
theorem w0_84 : indep% Multiset.noncommProd_erase_mul 7 := fun s a h comm x hx y hy hxy =>
  comm (Multiset.mem_of_mem_erase hx) (Multiset.mem_of_mem_erase hy) hxy
-- `Finset.noncommSum_lemma` idx 5: necessary (s = {0,1}, f 0 = σ, f 1 = τ additive)
theorem w0_85 : ¬ drop0% Finset.noncommSum_lemma 5 := fun h =>
  W2c0.np (x := W2c0.σ') (y := W2c0.τ') (by decide) (by decide) W2c0.st' W2c0.anc (h (s := {0, 1}) (f := W2c0.fa))
-- `Finset.noncommProd_lemma` idx 5: necessary (s = {0,1}, f 0 = σ, f 1 = τ)
theorem w0_86 : ¬ drop0% Finset.noncommProd_lemma 5 := fun h =>
  W2c0.np (x := W2c0.σ) (y := W2c0.τ) (by decide) (by decide) W2c0.st W2c0.nc (h (s := {0, 1}) (f := W2c0.fp))
-- `Finset.noncommSum_induction` idx 7: necessary (ℕ, s = {0,1}, f = 1, p n = n ≠ 2)
theorem w0_87 : ¬ drop0% Finset.noncommSum_induction 7 := fun h => by
  have := h ({0, 1} : Finset ℕ) (fun _ => (1 : ℕ)) (fun _ _ _ _ _ => AddCommute.all _ _) (fun n => n ≠ 2) (by decide) (by simp)
  simp [Finset.noncommSum_eq_sum] at this
-- `Finset.noncommSum_induction` idx 9: necessary (ℕ, s = {0}, f = 1, p n = n = 0)
theorem w0_88 : ¬ drop0% Finset.noncommSum_induction 9 := fun h => by
  have := h ({0} : Finset ℕ) (fun _ => (1 : ℕ)) (fun _ _ _ _ _ => AddCommute.all _ _) (fun n => n = 0)
    (fun a b (ha : a = 0) (hb : b = 0) => by subst ha; subst hb; rfl) rfl
  simp [Finset.noncommSum_eq_sum] at this
-- `Finset.noncommProd_induction` idx 5: necessary (s = {0,1}, f 0 = σ, f 1 = τ, p = True)
theorem w0_89 : ¬ indep0% Finset.noncommProd_induction 5 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.nc
    (h ({0, 1} : Finset ℕ) W2c0.fp (fun _ => True) (fun _ _ _ _ => trivial) trivial (fun _ _ => trivial))
-- `Finset.noncommProd_induction` idx 7: necessary (ℕ, s = {0,1}, f = 2, p n = n ≠ 4)
theorem w0_90 : ¬ drop0% Finset.noncommProd_induction 7 := fun h => by
  have := h ({0, 1} : Finset ℕ) (fun _ => (2 : ℕ)) (fun _ _ _ _ _ => Commute.all _ _) (fun n => n ≠ 4) (by decide) (by simp)
  simp [Finset.noncommProd_eq_prod] at this
-- `Finset.noncommProd_induction` idx 9: necessary (ℕ, s = {0}, f = 2, p n = n = 1)
theorem w0_91 : ¬ drop0% Finset.noncommProd_induction 9 := fun h => by
  have := h ({0} : Finset ℕ) (fun _ => (2 : ℕ)) (fun _ _ _ _ _ => Commute.all _ _) (fun n => n = 1)
    (fun a b (ha : a = 1) (hb : b = 1) => by subst ha; subst hb; rfl) rfl
  simp [Finset.noncommProd_eq_prod] at this
-- `Finset.noncommSum_congr` idx 8: necessary (ℕ, s₁ = s₂ = {0}, f = 0, g = 1)
theorem w0_92 : ¬ indep0% Finset.noncommSum_congr 8 := fun h =>
  absurd (h (s₁ := ({0} : Finset ℕ)) (s₂ := {0}) (f := fun _ => (0 : ℕ)) (g := fun _ => 1) rfl
    (fun _ _ _ _ _ => AddCommute.all _ _) 0 (by simp)) (by decide)
-- `Finset.noncommSum_congr` idx 9: necessary (s₁ = s₂ = {0,1}, f = g with f 0 = σ, f 1 = τ additive)
theorem w0_93 : ¬ indep0% Finset.noncommSum_congr 9 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.anc
    (h (s₁ := ({0, 1} : Finset ℕ)) (s₂ := {0, 1}) (f := W2c0.fa) (g := W2c0.fa) rfl (fun _ _ => rfl))
-- `Finset.noncommProd_congr` idx 8: necessary (ℕ, s₁ = s₂ = {0}, f = 0, g = 1)
theorem w0_94 : ¬ indep0% Finset.noncommProd_congr 8 := fun h =>
  absurd (h (s₁ := ({0} : Finset ℕ)) (s₂ := {0}) (f := fun _ => (0 : ℕ)) (g := fun _ => 1) rfl
    (fun _ _ _ _ _ => Commute.all _ _) 0 (by simp)) (by decide)
-- `Finset.noncommProd_congr` idx 9: necessary (s₁ = s₂ = {0,1}, f = g with f 0 = σ, f 1 = τ)
theorem w0_95 : ¬ indep0% Finset.noncommProd_congr 9 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.nc
    (h (s₁ := ({0, 1} : Finset ℕ)) (s₂ := {0, 1}) (f := W2c0.fp) (g := W2c0.fp) rfl (fun _ _ => rfl))
-- `Finset.noncommSum_toFinset` idx 6: necessary (l = [0,1], f 0 = σ, f 1 = τ additive)
theorem w0_96 : ¬ indep0% Finset.noncommSum_toFinset 6 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.anc (h [0, 1] W2c0.fa (by decide))
-- `Finset.noncommSum_toFinset` idx 7: necessary (ℕ, l = [0,0], f = 1)
theorem w0_97 : ¬ drop0% Finset.noncommSum_toFinset 7 := fun h => by
  have := h [0, 0] (fun _ => (1 : ℕ)) (fun _ _ _ _ _ => AddCommute.all _ _)
  simp [Finset.noncommSum_eq_sum] at this
-- `Finset.noncommProd_toFinset` idx 6: necessary (l = [0,1], f 0 = σ, f 1 = τ)
theorem w0_98 : ¬ indep0% Finset.noncommProd_toFinset 6 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.nc (h [0, 1] W2c0.fp (by decide))
-- `Finset.noncommProd_toFinset` idx 7: necessary (ℕ, l = [0,0], f = 2)
theorem w0_99 : ¬ drop0% Finset.noncommProd_toFinset 7 := fun h => by
  have := h [0, 0] (fun _ => (2 : ℕ)) (fun _ _ _ _ _ => Commute.all _ _)
  simp [Finset.noncommProd_eq_prod] at this
-- `Finset.noncommSum_cons` idx 7: necessary (s = {1}, a = 0, f 0 = σ, f 1 = τ additive)
theorem w0_100 : ¬ indep0% Finset.noncommSum_cons 7 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.anc (h {1} 0 W2c0.fa (by decide))
-- `Finset.noncommProd_cons` idx 7: necessary (s = {1}, a = 0, f 0 = σ, f 1 = τ)
theorem w0_101 : ¬ indep0% Finset.noncommProd_cons 7 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.nc (h {1} 0 W2c0.fp (by decide))
-- `Finset.noncommSum_cons'` idx 7: necessary (s = {1}, a = 0, f 0 = σ, f 1 = τ additive)
theorem w0_102 : ¬ indep0% Finset.noncommSum_cons' 7 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.anc (h {1} 0 W2c0.fa (by decide))
-- `Finset.noncommProd_cons'` idx 7: necessary (s = {1}, a = 0, f 0 = σ, f 1 = τ)
theorem w0_103 : ¬ indep0% Finset.noncommProd_cons' 7 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.nc (h {1} 0 W2c0.fp (by decide))
-- `Finset.noncommSum_insert_of_notMem` idx 7: necessary (s = {1}, a = 0, f 0 = σ, f 1 = τ additive)
theorem w0_104 : ¬ indep0% Finset.noncommSum_insert_of_notMem 7 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.anc (h {1} 0 W2c0.fa (by decide))
-- `Finset.noncommSum_insert_of_notMem` idx 8: necessary (ℕ, s = {0}, a = 0, f = 1)
theorem w0_105 : ¬ drop0% Finset.noncommSum_insert_of_notMem 8 := fun h => by
  have := h {0} 0 (fun _ => (1 : ℕ)) (fun _ _ _ _ _ => AddCommute.all _ _)
  simp [Finset.noncommSum_eq_sum] at this
-- `Finset.noncommProd_insert_of_notMem` idx 7: necessary (s = {1}, a = 0, f 0 = σ, f 1 = τ)
theorem w0_106 : ¬ indep0% Finset.noncommProd_insert_of_notMem 7 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.nc (h {1} 0 W2c0.fp (by decide))
-- `Finset.noncommProd_insert_of_notMem` idx 8: necessary (ℕ, s = {0}, a = 0, f = 2)
theorem w0_107 : ¬ drop0% Finset.noncommProd_insert_of_notMem 8 := fun h => by
  have := h {0} 0 (fun _ => (2 : ℕ)) (fun _ _ _ _ _ => Commute.all _ _)
  simp [Finset.noncommProd_eq_prod] at this
-- `Finset.noncommSum_insert_of_notMem'` idx 7: necessary (s = {1}, a = 0, f 0 = σ, f 1 = τ additive)
theorem w0_108 : ¬ indep0% Finset.noncommSum_insert_of_notMem' 7 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.anc (h {1} 0 W2c0.fa (by decide))
-- `Finset.noncommSum_insert_of_notMem'` idx 8: necessary (ℕ, s = {0}, a = 0, f = 1)
theorem w0_109 : ¬ drop0% Finset.noncommSum_insert_of_notMem' 8 := fun h => by
  have := h {0} 0 (fun _ => (1 : ℕ)) (fun _ _ _ _ _ => AddCommute.all _ _)
  simp [Finset.noncommSum_eq_sum] at this
-- `Finset.noncommProd_insert_of_notMem'` idx 7: necessary (s = {1}, a = 0, f 0 = σ, f 1 = τ)
theorem w0_110 : ¬ indep0% Finset.noncommProd_insert_of_notMem' 7 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.nc (h {1} 0 W2c0.fp (by decide))
-- `Finset.noncommProd_insert_of_notMem'` idx 8: necessary (ℕ, s = {0}, a = 0, f = 2)
theorem w0_111 : ¬ drop0% Finset.noncommProd_insert_of_notMem' 8 := fun h => by
  have := h {0} 0 (fun _ => (2 : ℕ)) (fun _ _ _ _ _ => Commute.all _ _)
  simp [Finset.noncommProd_eq_prod] at this
-- `Finset.map_noncommSum` idx 7: necessary (F = all maps ℕ → ℕ, constant map 1 does not preserve 0)
theorem w0_112 : ¬ indep0% Finset.map_noncommSum 7 := fun h => by
  have inst := h (F := W2c0.FW ℕ ℕ) (α := ℕ) (β := ℕ) (γ := ℕ) ∅ id (by simp) ⟨fun _ => 1⟩
  exact absurd (map_zero (⟨fun _ => 1⟩ : W2c0.FW ℕ ℕ)) (by decide)
-- `Finset.map_noncommSum` idx 10: necessary (g = identity hom, s = {0,1}, f 0 = σ, f 1 = τ additive)
theorem w0_113 : ¬ indep0% Finset.map_noncommSum 10 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.anc
    (h (F := W2c0.A3 →+ W2c0.A3) ({0, 1} : Finset ℕ) W2c0.fa (AddMonoidHom.id W2c0.A3))
-- `Finset.map_noncommProd` idx 7: necessary (F = all maps ℕ → ℕ, constant map 2 does not preserve 1)
theorem w0_114 : ¬ indep0% Finset.map_noncommProd 7 := fun h => by
  have inst := h (F := W2c0.FW ℕ ℕ) (α := ℕ) (β := ℕ) (γ := ℕ) ∅ id (by simp) ⟨fun _ => 2⟩
  exact absurd (map_one (⟨fun _ => 2⟩ : W2c0.FW ℕ ℕ)) (by decide)
-- `Finset.map_noncommProd` idx 10: necessary (g = identity hom, s = {0,1}, f 0 = σ, f 1 = τ)
theorem w0_115 : ¬ indep0% Finset.map_noncommProd 10 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.nc
    (h (F := W2c0.P3 →* W2c0.P3) ({0, 1} : Finset ℕ) W2c0.fp (MonoidHom.id W2c0.P3))
-- `Finset.noncommSum_eq_card_nsmul` idx 5: removable (derivable from h: f is constant m on s, and m commutes with itself)
theorem w0_116 : indep% Finset.noncommSum_eq_card_nsmul 5 := fun s f m h x hx y hy hxy => by
  show AddCommute (f x) (f y); rw [h x hx, h y hy]
-- `Finset.noncommSum_eq_card_nsmul` idx 7: necessary (ℕ, s = {0}, f = 1, m = 0)
theorem w0_117 : ¬ drop0% Finset.noncommSum_eq_card_nsmul 7 := fun h => by
  have := h {0} (fun _ => (1 : ℕ)) (fun _ _ _ _ _ => AddCommute.all _ _) 0
  simp [Finset.noncommSum_eq_sum] at this
-- `Finset.noncommProd_eq_pow_card` idx 5: removable (derivable from h: f is constant m on s, and m commutes with itself)
theorem w0_118 : indep% Finset.noncommProd_eq_pow_card 5 := fun s f m h x hx y hy hxy => by
  show Commute (f x) (f y); rw [h x hx, h y hy]
-- `Finset.noncommProd_eq_pow_card` idx 7: necessary (ℕ, s = {0}, f = 2, m = 1)
theorem w0_119 : ¬ drop0% Finset.noncommProd_eq_pow_card 7 := fun h => by
  have := h {0} (fun _ => (2 : ℕ)) (fun _ _ _ _ _ => Commute.all _ _) 1
  simp [Finset.noncommProd_eq_prod] at this
-- `Finset.noncommSum_addCommute` idx 5: necessary (s = {0,1}, f 0 = σ, f 1 = τ additive, y = 0)
theorem w0_120 : ¬ indep0% Finset.noncommSum_addCommute 5 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.anc
    (h ({0, 1} : Finset ℕ) W2c0.fa 0 (fun x _ => AddCommute.zero_left _))
-- `Finset.noncommProd_commute` idx 5: necessary (s = {0,1}, f 0 = σ, f 1 = τ, y = 1)
theorem w0_121 : ¬ indep0% Finset.noncommProd_commute 5 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.nc
    (h ({0, 1} : Finset ℕ) W2c0.fp 1 (fun x _ => Commute.one_left _))
-- `Finset.noncommProd_commute` idx 7: necessary (s = {0}, f = σ, y = τ)
theorem w0_122 : ¬ drop0% Finset.noncommProd_commute 7 := fun h => by
  have := h ({0} : Finset ℕ) (fun _ => W2c0.σ) (by simp) W2c0.τ
  simp only [Finset.noncommProd_singleton] at this
  exact W2c0.nc' this
-- `Finset.mul_noncommProd_erase` idx 8: necessary (s = {0,1}, a = 0, f 0 = σ, f 1 = τ)
theorem w0_123 : ¬ indep0% Finset.mul_noncommProd_erase 8 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.nc (h ({0, 1} : Finset ℕ) (a := 0) (by decide) W2c0.fp)
-- `Finset.mul_noncommProd_erase` idx 9: removable (optParam, derivable from comm by its default value)
theorem w0_124 : indep% Finset.mul_noncommProd_erase 9 := fun s a h f comm x hx y hy hxy =>
  comm (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) hxy
-- `Finset.noncommProd_erase_mul` idx 8: necessary (s = {0,1}, a = 0, f 0 = σ, f 1 = τ)
theorem w0_125 : ¬ indep0% Finset.noncommProd_erase_mul 8 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.nc (h ({0, 1} : Finset ℕ) (a := 0) (by decide) W2c0.fp)
-- `Finset.noncommProd_erase_mul` idx 9: removable (optParam, derivable from comm by its default value)
theorem w0_126 : indep% Finset.noncommProd_erase_mul 9 := fun s a h f comm x hx y hy hxy =>
  comm (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) hxy
-- `Finset.noncommSum_union_of_disjoint` idx 6: necessary (ℕ, s = t = {0}, f = 1)
theorem w0_127 : ¬ drop0% Finset.noncommSum_union_of_disjoint 6 := fun h => by
  have := h (s := ({0} : Finset ℕ)) (t := {0}) (fun _ => (1 : ℕ)) (fun _ _ _ _ _ => AddCommute.all _ _)
  simp [Finset.noncommSum_eq_sum] at this
-- `Finset.noncommSum_union_of_disjoint` idx 8: necessary (s = {0}, t = {1}, f 0 = σ, f 1 = τ additive)
theorem w0_128 : ¬ indep0% Finset.noncommSum_union_of_disjoint 8 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.anc (h (s := ({0} : Finset ℕ)) (t := {1}) (by decide) W2c0.fa)
-- `Finset.noncommProd_union_of_disjoint` idx 6: necessary (ℕ, s = t = {0}, f = 2)
theorem w0_129 : ¬ drop0% Finset.noncommProd_union_of_disjoint 6 := fun h => by
  have := h (s := ({0} : Finset ℕ)) (t := {0}) (fun _ => (2 : ℕ)) (fun _ _ _ _ _ => Commute.all _ _)
  simp [Finset.noncommProd_eq_prod] at this
-- `Finset.noncommProd_union_of_disjoint` idx 8: necessary (s = {0}, t = {1}, f 0 = σ, f 1 = τ)
theorem w0_130 : ¬ indep0% Finset.noncommProd_union_of_disjoint 8 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.nc (h (s := ({0} : Finset ℕ)) (t := {1}) (by decide) W2c0.fp)

-- `Finset.noncommSum_add_distrib_aux` idx 6: necessary (s = {0,1}, f 0 = σ, f 1 = τ additive, g = 0)
theorem w0_131 : ¬ drop0% Finset.noncommSum_add_distrib_aux 6 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide)
    (by simp only [Pi.add_apply, Pi.zero_apply, add_zero]; exact W2c0.anc)
    (h (s := ({0, 1} : Finset ℕ)) (f := W2c0.fa) (g := 0) (fun _ _ _ _ _ => AddCommute.zero_left _)
      (fun _ _ _ _ _ => AddCommute.zero_left _))
-- `Finset.noncommSum_add_distrib_aux` idx 7: necessary (s = {0,1}, f = 0, g 0 = σ, g 1 = τ additive)
theorem w0_132 : ¬ drop0% Finset.noncommSum_add_distrib_aux 7 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide)
    (by simp only [Pi.add_apply, Pi.zero_apply, zero_add]; exact W2c0.anc)
    (h (s := ({0, 1} : Finset ℕ)) (f := 0) (g := W2c0.fa) (fun _ _ _ _ _ => AddCommute.zero_left _)
      (fun _ _ _ _ _ => AddCommute.zero_right _))
-- `Finset.noncommSum_add_distrib_aux` idx 8: necessary (s = {0,1}, f = (σ, 0), g = (0, τ) additive)
theorem w0_133 : ¬ drop0% Finset.noncommSum_add_distrib_aux 8 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) (by simp only [Pi.add_apply, AddCommute, AddSemiconjBy]; decide)
   (h (s := {0,1}) (f := W2c0.f1a) (g := W2c0.g1a) (W2c0.pw2 (by unfold Function.onFun AddCommute AddSemiconjBy; decide) (by unfold Function.onFun AddCommute AddSemiconjBy; decide)) (W2c0.pw2 (by unfold Function.onFun AddCommute AddSemiconjBy; decide) (by unfold Function.onFun AddCommute AddSemiconjBy; decide)))
-- `Finset.noncommProd_mul_distrib_aux` idx 6: necessary (s = {0,1}, f 0 = σ, f 1 = τ, g = 1)
theorem w0_134 : ¬ drop0% Finset.noncommProd_mul_distrib_aux 6 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide)
    (by simp only [Pi.mul_apply, Pi.one_apply, mul_one]; exact W2c0.nc)
    (h (s := ({0, 1} : Finset ℕ)) (f := W2c0.fp) (g := 1) (fun _ _ _ _ _ => Commute.one_left _)
      (fun _ _ _ _ _ => Commute.one_left _))
-- `Finset.noncommProd_mul_distrib_aux` idx 7: necessary (s = {0,1}, f = 1, g 0 = σ, g 1 = τ)
theorem w0_135 : ¬ drop0% Finset.noncommProd_mul_distrib_aux 7 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide)
    (by simp only [Pi.mul_apply, Pi.one_apply, one_mul]; exact W2c0.nc)
    (h (s := ({0, 1} : Finset ℕ)) (f := 1) (g := W2c0.fp) (fun _ _ _ _ _ => Commute.one_left _)
      (fun _ _ _ _ _ => Commute.one_right _))
-- `Finset.noncommProd_mul_distrib_aux` idx 8: necessary (s = {0,1}, f = (σ, 1), g = (1, τ))
theorem w0_136 : ¬ drop0% Finset.noncommProd_mul_distrib_aux 8 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) (by simp only [Pi.mul_apply, Commute, SemiconjBy]; decide)
   (h (s := {0,1}) (f := W2c0.f1) (g := W2c0.g1) (W2c0.pw2 (by unfold Function.onFun Commute SemiconjBy; decide) (by unfold Function.onFun Commute SemiconjBy; decide)) (W2c0.pw2 (by unfold Function.onFun Commute SemiconjBy; decide) (by unfold Function.onFun Commute SemiconjBy; decide)))
-- `Finset.noncommSum_add_distrib` idx 6: necessary (s = {0,1}, f 0 = σ, f 1 = τ additive, g = 0)
theorem w0_137 : ¬ indep0% Finset.noncommSum_add_distrib 6 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.anc
    (h (s := ({0, 1} : Finset ℕ)) W2c0.fa 0 (fun _ _ _ _ _ => AddCommute.zero_left _)
      (fun _ _ _ _ _ => AddCommute.zero_left _))
-- `Finset.noncommSum_add_distrib` idx 7: necessary (s = {0,1}, f = 0, g 0 = σ, g 1 = τ additive)
theorem w0_138 : ¬ indep0% Finset.noncommSum_add_distrib 7 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.anc
    (h (s := ({0, 1} : Finset ℕ)) 0 W2c0.fa (fun _ _ _ _ _ => AddCommute.zero_left _)
      (fun _ _ _ _ _ => AddCommute.zero_right _))
-- `Finset.noncommSum_add_distrib` idx 8: necessary (s = {0,1}, f = (σ, 0), g = (0, τ) additive)
theorem w0_139 : ¬ indep0% Finset.noncommSum_add_distrib 8 := fun h =>
  W2c0.np (x := 1) (y := 0) (by simp) (by simp) (by decide) W2c0.anc'
   (h (s := {0,1}) W2c0.f1a W2c0.g1a (W2c0.pw2 (by unfold Function.onFun AddCommute AddSemiconjBy; decide) (by unfold Function.onFun AddCommute AddSemiconjBy; decide)) (W2c0.pw2 (by unfold Function.onFun AddCommute AddSemiconjBy; decide) (by unfold Function.onFun AddCommute AddSemiconjBy; decide)))
-- `Finset.noncommProd_mul_distrib` idx 6: necessary (s = {0,1}, f 0 = σ, f 1 = τ, g = 1)
theorem w0_140 : ¬ indep0% Finset.noncommProd_mul_distrib 6 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.nc
    (h (s := ({0, 1} : Finset ℕ)) W2c0.fp 1 (fun _ _ _ _ _ => Commute.one_left _)
      (fun _ _ _ _ _ => Commute.one_left _))
-- `Finset.noncommProd_mul_distrib` idx 7: necessary (s = {0,1}, f = 1, g 0 = σ, g 1 = τ)
theorem w0_141 : ¬ indep0% Finset.noncommProd_mul_distrib 7 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W2c0.nc
    (h (s := ({0, 1} : Finset ℕ)) 1 W2c0.fp (fun _ _ _ _ _ => Commute.one_left _)
      (fun _ _ _ _ _ => Commute.one_right _))
-- `Finset.noncommProd_mul_distrib` idx 8: necessary (s = {0,1}, f = (σ, 1), g = (1, τ))
theorem w0_142 : ¬ indep0% Finset.noncommProd_mul_distrib 8 := fun h =>
  W2c0.np (x := 1) (y := 0) (by simp) (by simp) (by decide) W2c0.nc'
   (h (s := {0,1}) W2c0.f1 W2c0.g1 (W2c0.pw2 (by unfold Function.onFun Commute SemiconjBy; decide) (by unfold Function.onFun Commute SemiconjBy; decide)) (W2c0.pw2 (by unfold Function.onFun Commute SemiconjBy; decide) (by unfold Function.onFun Commute SemiconjBy; decide)))
-- `AddMonoidHom.pi_ext` idx 9: necessary (ι = Unit, M = ℕ, f = id, g = 0)
theorem w0_144 : ¬ drop0% AddMonoidHom.pi_ext 9 := fun h =>
  absurd (congrArg (fun φ : (Unit → ℕ) →+ (Unit → ℕ) => φ (fun _ => 1) ())
    (h (ι := Unit) (M := fun _ => ℕ) (f := AddMonoidHom.id _) (g := 0))) (by simp)
-- `MonoidHom.pi_ext` idx 9: necessary (ι = Unit, M = ℕ, f = id, g = 1)
theorem w0_146 : ¬ drop0% MonoidHom.pi_ext 9 := fun h =>
  absurd (congrArg (fun φ : (Unit → ℕ) →* (Unit → ℕ) => φ (fun _ => 0) ())
    (h (ι := Unit) (M := fun _ => ℕ) (f := MonoidHom.id _) (g := 1))) (by simp)
-- `Finset.card_eraseNone_of_mem` idx 2: necessary (s = {some 0})
theorem w0_147 : ¬ drop0% Finset.card_eraseNone_of_mem 2 := fun h =>
  absurd (h (s := ({some 0} : Finset (Option ℕ)))) (by decide)
-- `Finset.card_eraseNone_of_notMem` idx 2: necessary (s = {none})
theorem w0_148 : ¬ drop0% Finset.card_eraseNone_of_notMem 2 := fun h =>
  absurd (h (s := ({none} : Finset (Option ℕ)))) (by decide)
-- `Finset.card_eraseNone_of_not_mem` idx 2: necessary (s = {none})
theorem w0_149 : ¬ drop0% Finset.card_eraseNone_of_not_mem 2 := fun h =>
  absurd (h (s := ({none} : Finset (Option ℕ)))) (by decide)
-- `Directed.finset_le` idx 2: necessary (r = ≠ on Fin 3, f = id, s = univ: directed but not transitive)
theorem w0_150 : ¬ drop0% Directed.finset_le 2 := fun h =>
  absurd (h (α := Fin 3) (r := fun a b => a ≠ b) (ι := Fin 3) (f := id) (by unfold Directed; decide) Finset.univ)
    (by decide)
-- `Directed.finset_le` idx 4: necessary (ι = Empty, s = ∅)
theorem w0_151 : ¬ drop0% Directed.finset_le 4 := fun h => by
  obtain ⟨z, _⟩ := h (α := ℕ) (r := (· ≤ ·)) (ι := Empty) (f := fun e => e.elim) (fun x => x.elim) ∅
  exact z.elim
-- `Finset.exists_ge` idx 1: necessary (α = Empty, s = ∅)
theorem w0_152 : ¬ drop0% Finset.exists_ge 1 := fun h => by
  obtain ⟨M, _⟩ := @h Empty (Preorder.lift (fun e : Empty => (e.elim : ℕ))) ⟨fun a => a.elim⟩ ∅
  exact M.elim
-- `Finset.exists_ge` idx 3: necessary (α = Unit ⊕ Unit with the sum order, s = univ)
theorem w0_153 : ¬ drop0% Finset.exists_ge 3 := fun h => by
  obtain ⟨M, hM⟩ := h (α := Unit ⊕ Unit) Finset.univ
  have h1 := hM (Sum.inl ()) (Finset.mem_univ _)
  have h2 := hM (Sum.inr ()) (Finset.mem_univ _)
  cases M <;> simp_all
-- `Finset.exists_le` idx 1: necessary (α = Empty, s = ∅)
theorem w0_154 : ¬ drop0% Finset.exists_le 1 := fun h => by
  obtain ⟨M, _⟩ := @h Empty (Preorder.lift (fun e : Empty => (e.elim : ℕ))) ⟨fun a => a.elim⟩ ∅
  exact M.elim
-- `Finset.exists_le` idx 3: necessary (α = Unit ⊕ Unit with the sum order, s = univ)
theorem w0_155 : ¬ drop0% Finset.exists_le 3 := fun h => by
  obtain ⟨M, hM⟩ := h (α := Unit ⊕ Unit) Finset.univ
  have h1 := hM (Sum.inl ()) (Finset.mem_univ _)
  have h2 := hM (Sum.inr ()) (Finset.mem_univ _)
  cases M <;> simp_all

-- `Finset.pimage_congr` idx 9: necessary (s = ∅, t = {0}, f = g = Part.some)
theorem w0_156 : ¬ drop0% Finset.pimage_congr 9 := fun h => by
  have := h (f := fun x : ℕ => Part.some x) (g := fun x : ℕ => Part.some x) (s := ∅) (t := {0}) (fun _ _ => rfl)
  have m : (0 : ℕ) ∈ Finset.pimage (fun x : ℕ => Part.some x) {0} := Finset.mem_pimage.2 ⟨0, by simp, Part.mem_some 0⟩
  rw [← this] at m
  obtain ⟨a, ha, _⟩ := Finset.mem_pimage.1 m
  simp at ha
-- `Finset.pimage_congr` idx 10: necessary (s = t = {0}, f = Part.some, g = Part.some ∘ succ)
theorem w0_157 : ¬ drop0% Finset.pimage_congr 10 := fun h => by
  have := h (f := fun x : ℕ => Part.some x) (g := fun x : ℕ => Part.some (x + 1)) (s := {0}) (t := {0}) rfl
  have m : (0 : ℕ) ∈ Finset.pimage (fun x : ℕ => Part.some x) {0} := Finset.mem_pimage.2 ⟨0, by simp, Part.mem_some 0⟩
  rw [this] at m
  obtain ⟨a, ha, hm⟩ := Finset.mem_pimage.1 m
  simp at ha hm
-- `Finset.pimage_mono` idx 7: necessary (s = {0}, t = ∅, f = Part.some)
theorem w0_158 : ¬ drop0% Finset.pimage_mono 7 := fun h => by
  have := h (f := fun x : ℕ => Part.some x) (s := {0}) (t := ∅)
  have m : (0 : ℕ) ∈ Finset.pimage (fun x : ℕ => Part.some x) {0} := Finset.mem_pimage.2 ⟨0, by simp, Part.mem_some 0⟩
  obtain ⟨a, ha, _⟩ := Finset.mem_pimage.1 (this m)
  simp at ha
-- `Set.PairwiseDisjoint.elim_finset` idx 4: necessary (s = univ, f = const {0}, i = 0, j = 1)
theorem w0_159 : ¬ drop0% Set.PairwiseDisjoint.elim_finset 4 := fun h =>
  absurd (h (s := (Set.univ : Set ℕ)) (f := fun _ => ({0} : Finset ℕ)) (i := 0) (j := 1) trivial trivial 0
    (by decide) (by decide)) (by decide)
-- `Set.PairwiseDisjoint.elim_finset` idx 7: necessary (s = {1}, f = const {0}, i = 0, j = 1)
theorem w0_160 : ¬ drop0% Set.PairwiseDisjoint.elim_finset 7 := fun h =>
  absurd (h (s := ({1} : Set ℕ)) (f := fun _ => ({0} : Finset ℕ)) (i := 0) (j := 1)
    (Set.pairwiseDisjoint_singleton _ _) (Set.mem_singleton 1) 0 (by decide) (by decide)) (by decide)
-- `Set.PairwiseDisjoint.elim_finset` idx 8: necessary (s = {0}, f = const {0}, i = 0, j = 1)
theorem w0_161 : ¬ drop0% Set.PairwiseDisjoint.elim_finset 8 := fun h =>
  absurd (h (s := ({0} : Set ℕ)) (f := fun _ => ({0} : Finset ℕ)) (i := 0) (j := 1)
    (Set.pairwiseDisjoint_singleton _ _) (Set.mem_singleton 0) 0 (by decide) (by decide)) (by decide)
-- `Set.PairwiseDisjoint.elim_finset` idx 10: necessary (s = univ, f 1 = {0}, f i = ∅ otherwise, i = 0, j = 1)
theorem w0_162 : ¬ drop0% Set.PairwiseDisjoint.elim_finset 10 := fun h =>
  absurd (h (s := (Set.univ : Set ℕ)) (f := fun i => if i = 1 then ({0} : Finset ℕ) else ∅) (i := 0) (j := 1)
    (fun x _ y _ hxy => by simp only [Function.onFun]; split_ifs <;> simp_all) trivial trivial 0 (by decide)) (by decide)
-- `Set.PairwiseDisjoint.elim_finset` idx 11: necessary (s = univ, f 1 = {0}, f i = ∅ otherwise, i = 1, j = 0)
theorem w0_163 : ¬ drop0% Set.PairwiseDisjoint.elim_finset 11 := fun h =>
  absurd (h (s := (Set.univ : Set ℕ)) (f := fun i => if i = 1 then ({0} : Finset ℕ) else ∅) (i := 1) (j := 0)
    (fun x _ y _ hxy => by simp only [Function.onFun]; split_ifs <;> simp_all) trivial trivial 0 (by decide)) (by decide)
-- `Set.PairwiseDisjoint.image_finset_of_le` idx 7: necessary (s = {0,1}, f = const {0}, g = id)
theorem w0_164 : ¬ drop0% Set.PairwiseDisjoint.image_finset_of_le 7 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) (by unfold Function.onFun; decide)
    (h (s := ({0, 1} : Finset ℕ)) (f := fun _ => ({0} : Finset ℕ)) (g := id) (fun _ => le_refl _))
-- `Set.PairwiseDisjoint.image_finset_of_le` idx 9: necessary (s = {0,1}, f i = ∅ for i ≤ 1 else {0}, g = (· + 2))
theorem w0_165 : ¬ drop0% Set.PairwiseDisjoint.image_finset_of_le 9 := fun h =>
  W2c0.np (x := 2) (y := 3) (by simp) (by simp) (by decide) (by unfold Function.onFun; decide)
    (h (s := ({0, 1} : Finset ℕ)) (f := fun i => if i ≤ 1 then ∅ else ({0} : Finset ℕ))
      (W2c0.pw2 (by unfold Function.onFun; decide) (by unfold Function.onFun; decide)) (g := fun i => i + 2))
-- `Set.PairwiseDisjoint.attach` idx 6: necessary (s = {0,1}, f = const {0})
theorem w0_166 : ¬ drop0% Set.PairwiseDisjoint.attach 6 := fun h =>
  W2c0.np (x := (⟨0, by decide⟩ : {x // x ∈ ({0, 1} : Finset ℕ)})) (y := (⟨1, by decide⟩ : {x // x ∈ ({0, 1} : Finset ℕ)})) (Finset.mem_coe.2 (Finset.mem_attach _ _))
    (Finset.mem_coe.2 (Finset.mem_attach _ _)) (fun e => absurd (congrArg Subtype.val e) (by decide))
    (by unfold Function.onFun; decide) (h (s := ({0, 1} : Finset ℕ)) (f := fun _ => ({0} : Finset ℕ)))
-- `Set.PairwiseDisjoint.biUnion_finset` idx 8: necessary (s = univ, g i = {i}, f = const {0})
theorem w0_167 : ¬ drop0% Set.PairwiseDisjoint.biUnion_finset 8 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) (by unfold Function.onFun; decide)
    (h (s := (Set.univ : Set ℕ)) (g := fun i => ({i} : Finset ℕ)) (f := fun _ => ({0} : Finset ℕ)) (fun i _ => by simp))
-- `Set.PairwiseDisjoint.biUnion_finset` idx 9: necessary (s = {()}, g () = {0,1}, f = const {0})
theorem w0_168 : ¬ drop0% Set.PairwiseDisjoint.biUnion_finset 9 := fun h =>
  W2c0.np (x := 0) (y := 1) (by simp) (by simp) (by decide) (by unfold Function.onFun; decide)
    (h (s := ({()} : Set Unit)) (g := fun _ => ({0, 1} : Finset ℕ)) (f := fun _ => ({0} : Finset ℕ))
      (Set.pairwiseDisjoint_singleton _ _))
-- `List.pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint` idx 7: necessary (l = [0,1], f = const {0})
theorem w0_169 : ¬ drop0% List.pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint 7 := fun h =>
  absurd (h (l := [0, 1]) (f := fun _ => ({0} : Finset ℕ)) (by decide)) (by unfold Function.onFun; decide)
-- `List.pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint` idx 8: necessary (l = [0,0], f = const {0})
theorem w0_170 : ¬ drop0% List.pairwise_disjoint_of_coe_toFinset_pairwiseDisjoint 8 := fun h =>
  absurd (h (l := [0, 0]) (f := fun _ => ({0} : Finset ℕ)) (by simp)) (by unfold Function.onFun; decide)
-- `List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint` idx 7: necessary (l = [0,0], f = const {0})
theorem w0_171 : ¬ drop0% List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint 7 := fun h =>
  absurd ((h (l := [0, 0]) (f := fun _ => ({0} : Finset ℕ))).1 (by simp)) (by unfold Function.onFun; decide)
-- `Finset.Pi.cons_ne` idx 8: necessary (s = ∅, a = 0, a' = 1)
theorem w0_172 : ¬ indep0% Finset.Pi.cons_ne 8 := fun h =>
  absurd (h (δ := fun _ : ℕ => True) (s := ∅) (a := 0) (a' := 1) (b := trivial) (f := fun _ _ => trivial) (by decide))
    (by decide)
-- `Finset.Pi.cons_ne` idx 9: necessary (s = ∅, a = a' = 0)
theorem w0_173 : ¬ indep0% Finset.Pi.cons_ne 9 := fun h =>
  absurd (h (δ := fun _ : ℕ => True) (s := ∅) (a := 0) (a' := 0) (b := trivial) (f := fun _ _ => trivial)
    (h := by decide)) (by decide)
-- `Finset.Pi.cons_injective` idx 6: necessary (at δ : α → Type: s = {0}, a = 0, two different functions on s)
theorem w0_174 : ¬ ∀ {α : Type} {δ : α → Type} [DecidableEq α] {a : α} {b : δ a} {s : Finset α},
    Function.Injective (Finset.Pi.cons s a b) := fun h => by
  have H := @h ℕ (fun _ => ℕ) _ 0 5 {0} (fun _ _ => 0) (fun _ _ => 1) (by
    funext x hx
    have : x = 0 := by simpa using hx
    subst this
    simp [Finset.Pi.cons_same])
  exact absurd (congrFun (congrFun H 0) (by simp)) (by decide)
-- `Finset.pi_nonempty_of_forall_nonempty` idx 5: necessary (s = {0}, t = const ∅)
theorem w0_175 : ¬ drop0% Finset.pi_nonempty_of_forall_nonempty 5 := fun h =>
  absurd (h (β := fun _ => ℕ) (s := ({0} : Finset ℕ)) (t := fun _ => ∅)) (by simp)
-- `Finset.pi_insert` idx 7: removable (if a ∈ s both sides equal s.pi t: every g equals Pi.cons s a (g a) g)
theorem w0_176 : drop% Finset.pi_insert 7 := by
  intro α β _ _ s t a
  ext g
  simp only [Finset.mem_pi, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · intro hg
    refine ⟨g a (Finset.mem_insert_self a s), hg _ _, fun x hx => g x (Finset.mem_insert_of_mem hx),
      fun x hx => hg _ _, ?_⟩
    funext x hx
    by_cases hax : a = x
    · subst hax; simp [Finset.Pi.cons_same]
    · rw [Finset.Pi.cons_ne hax]
  · rintro ⟨b, hb, e, he, rfl⟩ x hx
    by_cases hax : a = x
    · subst hax; rw [Finset.Pi.cons_same]; exact hb
    · rw [Finset.Pi.cons_ne hax]; exact he _ _
-- `Finset.pi_subset` idx 6: necessary (s = {0}, t₁ = const {0}, t₂ = const ∅)
theorem w0_177 : ¬ drop0% Finset.pi_subset 6 := fun h => by
  have H := h (β := fun _ => ℕ) (s := ({0} : Finset ℕ)) (fun _ => {0}) (fun _ => ∅)
  have h1 : (({0} : Finset ℕ).pi fun _ => ({0} : Finset ℕ)).Nonempty := by simp
  have h2 : (({0} : Finset ℕ).pi fun _ => (∅ : Finset ℕ)) = ∅ := by simp
  exact (h1.mono H).ne_empty h2
-- `Finset.pi_disjoint_of_disjoint` idx 7: necessary (s = ∅: both pi sets are the singleton of the empty function)
theorem w0_178 : ¬ drop0% Finset.pi_disjoint_of_disjoint 7 := fun h => by
  have := h (δ := fun _ => ℕ) (s := (∅ : Finset ℕ)) (fun _ => {0}) (fun _ => ∅) (a := 0) (by simp)
  simp [Finset.pi_empty] at this
-- `Finset.pi_disjoint_of_disjoint` idx 8: necessary (s = {0}, t₁ = t₂ = const {0})
theorem w0_179 : ¬ drop0% Finset.pi_disjoint_of_disjoint 8 := fun h => by
  have := h (δ := fun _ => ℕ) (s := ({0} : Finset ℕ)) (fun _ => {0}) (fun _ => {0}) (a := 0) (by simp)
  simp at this
-- `Finset.card_piDiag` idx 4: necessary (ι = Empty, s = {0,1}: only one function Empty → ℕ)
theorem w0_180 : ¬ drop0% Finset.card_piDiag 4 := fun h => by
  have H := h ({0, 1} : Finset ℕ) Empty
  have h1 := Finset.card_le_one_of_subsingleton (({0, 1} : Finset ℕ).piDiag Empty)
  rw [H] at h1
  exact absurd h1 (by decide)
-- `Finset.restrict₂_preimage` idx 5: necessary (s = {0}, t = ∅)
theorem w0_181 : ¬ indep0% Finset.restrict₂_preimage 5 := fun h =>
  absurd (h (ι := ℕ) (π := fun _ => ℕ) (s := {0}) (t := ∅) (fun _ => Set.univ)) (by decide)

-- `AddMonoidHom.pi_ext` idx 5: necessary (ι = ℕ, M = ℤ, f = quotient map by the finitely supported functions, g = 0)
theorem w0_143 : ¬ drop0% AddMonoidHom.pi_ext 5 := fun h => by
  have H := h (ι := ℕ) (M := fun _ => ℤ) (γ := (ℕ → ℤ) ⧸ W2c0.FS) (f := QuotientAddGroup.mk' W2c0.FS) (g := 0)
    (fun i x => by simp [QuotientAddGroup.eq_zero_iff, W2c0.single_mem])
  have := congrArg (fun φ : (ℕ → ℤ) →+ (ℕ → ℤ) ⧸ W2c0.FS => φ (fun _ => (1 : ℤ))) H
  simp [QuotientAddGroup.eq_zero_iff] at this
  exact W2c0.one_notMem this
-- `MonoidHom.pi_ext` idx 5: necessary (multiplicative copy: ι = ℕ, M = Multiplicative ℤ, f = quotient map by the finitely supported functions, g = 1)
theorem w0_145 : ¬ drop0% MonoidHom.pi_ext 5 := fun h => by
  have H := h (ι := ℕ) (M := fun _ => Multiplicative ℤ) (γ := Multiplicative ((ℕ → ℤ) ⧸ W2c0.FS))
    (f := AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' W2c0.FS)) (g := 1)
    (fun i x => by
      show Multiplicative.ofAdd (QuotientAddGroup.mk' W2c0.FS (Pi.single i (Multiplicative.toAdd x))) = Multiplicative.ofAdd 0
      simp [QuotientAddGroup.eq_zero_iff, W2c0.single_mem])
  have := congrArg (fun φ : (ℕ → Multiplicative ℤ) →* Multiplicative ((ℕ → ℤ) ⧸ W2c0.FS) =>
    Multiplicative.toAdd (φ (fun _ => Multiplicative.ofAdd (1 : ℤ)))) H
  change QuotientAddGroup.mk' W2c0.FS (fun _ => (1 : ℤ)) = 0 at this
  simp [QuotientAddGroup.eq_zero_iff] at this
  exact W2c0.one_notMem this
