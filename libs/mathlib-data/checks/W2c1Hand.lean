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

namespace W2c1
open scoped Pointwise

theorem notWF {β : Type*} {r : β → β → Prop} (f : ℕ → β) (hf : ∀ n, r (f (n+1)) (f n)) :
    ¬ WellFounded r := by
  intro h
  obtain ⟨m, ⟨n, rfl⟩, hm⟩ := h.has_min (Set.range f) ⟨f 0, 0, rfl⟩
  exact hm _ ⟨n+1, rfl⟩ (hf n)

theorem int_univ_not_wf : ¬ (Set.univ : Set ℤ).IsWF := by
  rw [Set.isWF_univ_iff]; intro h
  exact notWF (r := (· < ·)) (fun n : ℕ => -(n:ℤ)) (fun n => by push_cast; omega) (@wellFounded_lt ℤ _ h)

theorem int_univ_not_pwo : ¬ (Set.univ : Set ℤ).IsPWO := fun h => int_univ_not_wf h.isWF

theorem mint_univ_not_wf : ¬ (Set.univ : Set (Multiplicative ℤ)).IsWF := by
  rw [Set.isWF_univ_iff]; intro h
  exact notWF (r := (· < ·)) (fun n : ℕ => Multiplicative.ofAdd (-(n:ℤ)))
    (fun n => Multiplicative.ofAdd_lt.2 (by push_cast; omega)) (@wellFounded_lt (Multiplicative ℤ) _ h)

theorem mint_univ_not_pwo : ¬ (Set.univ : Set (Multiplicative ℤ)).IsPWO := fun h => mint_univ_not_wf h.isWF

/-- phi: identity on even integers, negation on odd ones. -/
def phi (x : ℤ) : ℤ := if Even x then x else -x
theorem phi_phi (x : ℤ) : phi (phi x) = x := by
  unfold phi; by_cases hx : Even x <;> simp [hx, even_neg]
theorem phi_inj : Function.Injective phi := Function.LeftInverse.injective phi_phi
theorem phi_even (n : ℕ) : phi (2 * n) = 2 * n := by simp [phi]
theorem phi_odd (n : ℕ) : phi (2 * n + 1) = -(2 * n + 1) := by
  simp [phi, Int.even_add_one]

/-- The integers with addition, ordered through phi (order incompatible with addition). -/
def W := ℤ
instance : AddCommMonoid W := inferInstanceAs (AddCommMonoid ℤ)
instance : LinearOrder W := LinearOrder.lift' (fun x : W => phi (x : ℤ)) phi_inj
def w (z : ℤ) : W := z
theorem W_lt (a b : ℤ) : w a < w b ↔ phi a < phi b := Iff.rfl
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
/-- SW +ᵥ {1} (vector addition = addition) is not well-founded. -/
theorem SW_vadd_not_wf : ¬ (SW +ᵥ ({w 1} : Set W)).IsWF := by
  rw [Set.isWF_iff_no_descending_seq]; push_neg
  refine ⟨fun n => w (2 * n + 1), strictAnti_nat_of_succ_lt fun n => ?_, fun n => ?_⟩
  · show phi (2 * ((n+1 : ℕ) : ℤ) + 1) < phi (2 * (n : ℤ) + 1)
    rw [phi_odd, phi_odd]; push_cast; omega
  · exact Set.mem_vadd.2 ⟨w (2 * n), ⟨n, rfl⟩, w 1, rfl, rfl⟩

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
theorem SM_smul_not_wf : ¬ (SM • ({mw 1} : Set MW)).IsWF := by
  rw [Set.isWF_iff_no_descending_seq]; push_neg
  refine ⟨fun n => mw (2 * n + 1), strictAnti_nat_of_succ_lt fun n => ?_, fun n => ?_⟩
  · show phi (2 * ((n+1 : ℕ) : ℤ) + 1) < phi (2 * (n : ℤ) + 1)
    rw [phi_odd, phi_odd]; push_cast; omega
  · exact Set.mem_smul.2 ⟨mw (2 * n), ⟨n, rfl⟩, mw 1, rfl, rfl⟩

/-- In ℤ (addition), the antidiagonal of univ, univ at 0 is infinite. -/
theorem vanti_inf : ¬ ((Set.univ : Set ℤ).vaddAntidiagonal (Set.univ : Set ℤ) 0).Finite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℤ => (n, -n))
    (fun a b hab => congrArg Prod.fst hab) (fun n => by simp [vadd_eq_add])

/-- In ℤ (multiplication as SMul), the antidiagonal of univ, univ at 0 is infinite. -/
theorem santi_inf : ¬ ((Set.univ : Set ℤ).smulAntidiagonal (Set.univ : Set ℤ) 0).Finite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℤ => (0, n))
    (fun a b hab => congrArg Prod.snd hab) (fun n => by simp)

theorem vanti_empty {G P : Type} [VAdd G P] (t : Set P) (a : P) :
    ((∅ : Set G).vaddAntidiagonal t a).Finite := Set.finite_empty.subset fun x hx => hx.1
theorem vanti_empty' {G P : Type} [VAdd G P] (s : Set G) (a : P) :
    (s.vaddAntidiagonal (∅ : Set P) a).Finite := Set.finite_empty.subset fun x hx => hx.2.1
theorem santi_empty {G P : Type} [SMul G P] (t : Set P) (a : P) :
    ((∅ : Set G).smulAntidiagonal t a).Finite := Set.finite_empty.subset fun x hx => hx.1
theorem santi_empty' {G P : Type} [SMul G P] (s : Set G) (a : P) :
    (s.smulAntidiagonal (∅ : Set P) a).Finite := Set.finite_empty.subset fun x hx => hx.2.1

/-- The constant map Bool → Unit is not injective on the preimage of a finset containing (). -/
theorem ni (s : Finset Unit) (hs : () ∈ s) :
    ¬ Set.InjOn (fun _ : Bool => ()) ((fun _ : Bool => ()) ⁻¹' ↑s) := by
  intro h
  exact absurd (@h true (show () ∈ s from hs) false (show () ∈ s from hs) rfl) (by decide)

/-- Finitely supported families stay finitely supported under update. -/
theorem fin_upd {ι : Type} {α : ι → Type} [DecidableEq ι] (g : ∀ i, Finset (α i)) (i : ι)
    (t : Finset (α i)) (hg : {j | (g j).Nonempty}.Finite) :
    {j | (Function.update g i t j).Nonempty}.Finite := by
  apply (hg.insert i).subset
  intro j hj
  by_cases hji : j = i
  · exact Or.inl hji
  · right; simpa [Function.update_of_ne hji] using hj

theorem fin_univ : ¬ {j : ℕ | ({()} : Finset Unit).Nonempty}.Finite := by
  simpa using Set.infinite_univ (α := ℕ)

/-- rock-paper-scissors on Fin 3: total, antisymmetric, not transitive. -/
def rps (a b : Fin 3) : Prop := a = b ∨ b = a + 1
instance rpsDec : DecidableRel rps := fun a b => by unfold rps; infer_instance
instance rpsAnti : Std.Antisymm rps := ⟨by decide⟩
instance rpsTot : Std.Total rps := ⟨by decide⟩
theorem rps_nt : ¬ IsTrans (Fin 3) rps := fun h =>
  absurd (@IsTrans.trans _ rps h 0 1 2 (by decide) (by decide)) (by decide)

/-- the empty relation on Unit: transitive, antisymmetric, not total -/
def fr (_ _ : Unit) : Prop := False
instance frDec : DecidableRel fr := fun _ _ => instDecidableFalse
instance frTrans : IsTrans Unit fr := ⟨fun _ _ _ h => h.elim⟩
instance frAnti : Std.Antisymm fr := ⟨fun _ _ h => h.elim⟩
theorem fr_nt : ¬ Std.Total fr := fun h => (h.total () ()).elim id id

/-- the full relation on Unit: transitive, antisymmetric, total -/
def tr (_ _ : Unit) : Prop := True
instance trDec : DecidableRel tr := fun _ _ => instDecidableTrue
instance trTrans : IsTrans Unit tr := ⟨fun _ _ _ _ _ => trivial⟩
instance trAnti : Std.Antisymm tr := ⟨fun _ _ _ _ => rfl⟩
instance trTot : Std.Total tr := ⟨fun _ _ => Or.inl trivial⟩

/-- the full relation on Bool: transitive, total, not antisymmetric -/
def trB (_ _ : Bool) : Prop := True
instance trBDec : DecidableRel trB := fun _ _ => instDecidableTrue
instance trBTrans : IsTrans Bool trB := ⟨fun _ _ _ _ _ => trivial⟩
instance trBTot : Std.Total trB := ⟨fun _ _ => Or.inl trivial⟩
theorem trB_na : ¬ Std.Antisymm trB := fun h => absurd (h.antisymm true false trivial trivial) (by decide)

/-- reverse order on Bool -/
def geB (a b : Bool) : Prop := b ≤ a
instance : DecidableRel geB := fun a b => by unfold geB; infer_instance
instance : IsTrans Bool geB := ⟨by decide⟩
instance : Std.Antisymm geB := ⟨by decide⟩
instance : Std.Total geB := ⟨by decide⟩

/-- the usual order on ℕ as a plain relation with named instances -/
def leN (a b : ℕ) : Prop := a ≤ b
instance leNDec : DecidableRel leN := fun a b => Nat.decLe a b
instance leNTrans : IsTrans ℕ leN := ⟨fun _ _ _ => Nat.le_trans⟩
instance leNAnti : Std.Antisymm leN := ⟨fun _ _ => Nat.le_antisymm⟩
instance leNTot : Std.Total leN := ⟨Nat.le_total⟩

theorem s_ft : (Finset.univ : Finset Bool).sort (fun a b : Bool => a ≤ b) = [false, true] := by
  rw [show (Finset.univ : Finset Bool) = insert false {true} by decide,
    Finset.sort_insert (s := {true}) (a := false) (fun a b : Bool => a ≤ b) (by decide) (by decide),
    Finset.sort_singleton]
theorem s_tf : (Finset.univ : Finset Bool).sort geB = [true, false] := by
  rw [show (Finset.univ : Finset Bool) = insert true {false} by decide,
    Finset.sort_insert (s := {false}) (a := true) geB (by decide) (by decide),
    Finset.sort_singleton]

def bnotE : Bool ↪ Bool := ⟨not, by decide⟩
def u0 : Unit ↪ Fin 3 := ⟨fun _ => 0, fun _ _ _ => rfl⟩
def uB : Unit ↪ Bool := ⟨fun _ => true, fun _ _ _ => rfl⟩

theorem sm1 (f : Fin 1 → ℕ) : StrictMono f := fun a b hab => by
  rw [Subsingleton.elim a b] at hab; exact absurd hab (lt_irrefl b)

end W2c1

-- `Finset.induction_on_pi_of_choice` idx 2: necessary (iota = Nat, alpha = Unit, f = fun _ => {()}, r = True, p g = finitely many nonempty g i)
theorem c1_0 : ¬ drop0% Finset.induction_on_pi_of_choice 2 := by
  intro hc
  exact W2c1.fin_univ (hc (ι := ℕ) (α := fun _ => Unit) (fun _ _ _ => True)
    (fun i s hs => ⟨hs.choose, hs.choose_spec, trivial⟩) (p := fun g => {i | (g i).Nonempty}.Finite)
    (fun _ => {()}) (by simp) (fun g i x _ hg => W2c1.fin_upd g i _ hg))

-- `Finset.induction_on_pi_of_choice` idx 6: necessary (iota = alpha = Unit, r = False, p g = (g = empty), f = {()})
theorem c1_1 : ¬ drop0% Finset.induction_on_pi_of_choice 6 := by
  intro hc
  have := hc (ι := Unit) (α := fun _ => Unit) (fun _ _ _ => False) (p := fun g => g = fun _ => ∅)
    (fun _ => {()}) rfl (fun _ _ _ hr => hr.elim)
  exact absurd (congrFun this ()) (by decide)

-- `Finset.induction_on_pi_of_choice` idx 9: necessary (p = False, r = True on Unit)
theorem c1_2 : ¬ drop0% Finset.induction_on_pi_of_choice 9 := by
  intro hc
  exact hc (ι := Unit) (α := fun _ => Unit) (fun _ _ _ => True)
    (fun i s hs => ⟨hs.choose, hs.choose_spec, trivial⟩) (p := fun _ => False) (fun _ => ∅)
    (fun _ _ _ _ hg => hg)

-- `Finset.induction_on_pi_of_choice` idx 10: necessary (p g = (g = empty), f = {()}, r = True on Unit)
theorem c1_3 : ¬ drop0% Finset.induction_on_pi_of_choice 10 := by
  intro hc
  have := hc (ι := Unit) (α := fun _ => Unit) (fun _ _ _ => True)
    (fun i s hs => ⟨hs.choose, hs.choose_spec, trivial⟩) (p := fun g => g = fun _ => ∅) (fun _ => {()}) rfl
  exact absurd (congrFun this ()) (by decide)

-- `Finset.induction_on_pi` idx 2: necessary (iota = Nat, alpha = Unit, f = fun _ => {()}, p g = finitely many nonempty g i)
theorem c1_4 : ¬ drop0% Finset.induction_on_pi 2 := by
  intro hc
  exact W2c1.fin_univ (hc (ι := ℕ) (α := fun _ => Unit) (p := fun g => {i | (g i).Nonempty}.Finite)
    (fun _ => {()}) (by simp) (fun g i x _ hg => W2c1.fin_upd g i _ hg))

-- `Finset.induction_on_pi` idx 7: necessary (p = False on Unit)
theorem c1_5 : ¬ drop0% Finset.induction_on_pi 7 := by
  intro hc
  exact hc (ι := Unit) (α := fun _ => Unit) (p := fun _ => False) (fun _ => ∅) (fun _ _ _ _ hg => hg)

-- `Finset.induction_on_pi` idx 8: necessary (p g = (g = empty), f = {()} on Unit)
theorem c1_6 : ¬ drop0% Finset.induction_on_pi 8 := by
  intro hc
  have := hc (ι := Unit) (α := fun _ => Unit) (p := fun g => g = fun _ => ∅) (fun _ => {()}) rfl
  exact absurd (congrFun this ()) (by decide)

-- `Finset.induction_on_pi_max` idx 2: necessary (iota = Nat, alpha = Unit, f = fun _ => {()}, p g = finitely many nonempty g i)
theorem c1_7 : ¬ drop0% Finset.induction_on_pi_max 2 := by
  intro hc
  exact W2c1.fin_univ (hc (ι := ℕ) (α := fun _ => Unit) (p := fun g => {i | (g i).Nonempty}.Finite)
    (fun _ => {()}) (by simp) (fun g i x _ hg => W2c1.fin_upd g i _ hg))

-- `Finset.induction_on_pi_max` idx 8: necessary (p = False on Unit)
theorem c1_8 : ¬ drop0% Finset.induction_on_pi_max 8 := by
  intro hc
  exact hc (ι := Unit) (α := fun _ => Unit) (p := fun _ => False) (fun _ => ∅) (fun _ _ _ _ hg => hg)

-- `Finset.induction_on_pi_max` idx 9: necessary (p g = (g = empty), f = {()} on Unit)
theorem c1_9 : ¬ drop0% Finset.induction_on_pi_max 9 := by
  intro hc
  have := hc (ι := Unit) (α := fun _ => Unit) (p := fun g => g = fun _ => ∅) (fun _ => {()}) rfl
  exact absurd (congrFun this ()) (by decide)

-- `Finset.induction_on_pi_min` idx 2: necessary (iota = Nat, alpha = Unit, f = fun _ => {()}, p g = finitely many nonempty g i)
theorem c1_10 : ¬ drop0% Finset.induction_on_pi_min 2 := by
  intro hc
  exact W2c1.fin_univ (hc (ι := ℕ) (α := fun _ => Unit) (p := fun g => {i | (g i).Nonempty}.Finite)
    (fun _ => {()}) (by simp) (fun g i x _ hg => W2c1.fin_upd g i _ hg))

-- `Finset.induction_on_pi_min` idx 8: necessary (p = False on Unit)
theorem c1_11 : ¬ drop0% Finset.induction_on_pi_min 8 := by
  intro hc
  exact hc (ι := Unit) (α := fun _ => Unit) (p := fun _ => False) (fun _ => ∅) (fun _ _ _ _ hg => hg)

-- `Finset.induction_on_pi_min` idx 9: necessary (p g = (g = empty), f = {()} on Unit)
theorem c1_12 : ¬ drop0% Finset.induction_on_pi_min 9 := by
  intro hc
  have := hc (ι := Unit) (α := fun _ => Unit) (p := fun g => g = fun _ => ∅) (fun _ => {()}) rfl
  exact absurd (congrFun this ()) (by decide)

-- `Finset.piecewise_eq_of_mem` idx 7: necessary (universe 1: iota = PUnit, pi = Bool, s = empty, f = true, g = false)
theorem c1_13 : ¬ drop1% Finset.piecewise_eq_of_mem 7 := by
  intro hc
  have := hc (ι := PUnit.{2}) (π := fun _ => Bool) ∅ (fun _ => true) (fun _ => false) (i := PUnit.unit)
  simp at this

-- `Finset.piecewise_eq_of_notMem` idx 7: necessary (universe 1: iota = PUnit, pi = Bool, s = univ, f = true, g = false)
theorem c1_14 : ¬ drop1% Finset.piecewise_eq_of_notMem 7 := by
  intro hc
  have := hc (ι := PUnit.{2}) (π := fun _ => Bool) Finset.univ (fun _ => true) (fun _ => false) (i := PUnit.unit)
  simp at this

-- `Finset.piecewise_congr` idx 8: necessary (universe 1: s = univ, f = true, f' = false, g = g')
theorem c1_15 : ¬ drop1% Finset.piecewise_congr 8 := by
  intro hc
  have := hc (ι := PUnit.{2}) (π := fun _ => Bool) Finset.univ (f := fun _ => true) (f' := fun _ => false)
    (g := fun _ => true) (g' := fun _ => true) (fun _ _ => rfl)
  have := congrFun this PUnit.unit
  simp at this

-- `Finset.piecewise_congr` idx 9: necessary (universe 1: s = empty, g = true, g' = false, f = f')
theorem c1_16 : ¬ drop1% Finset.piecewise_congr 9 := by
  intro hc
  have := hc (ι := PUnit.{2}) (π := fun _ => Bool) ∅ (f := fun _ => true) (f' := fun _ => true)
    (g := fun _ => true) (g' := fun _ => false) (fun _ _ => rfl)
  have := congrFun this PUnit.unit
  simp at this

-- `Finset.piecewise_insert_of_ne` idx 10: necessary (universe 1: i = j, s = empty, f = true, g = false)
theorem c1_17 : ¬ drop1% Finset.piecewise_insert_of_ne 10 := by
  intro hc
  have := hc (ι := PUnit.{2}) (π := fun _ => Bool) ∅ (fun _ => true) (fun _ => false) (i := PUnit.unit)
    (j := PUnit.unit)
  simp at this

-- `Finset.piecewise_cases` idx 8: necessary (universe 1: s = univ, f = true, g = false, p = (· = false))
theorem c1_18 : ¬ drop1% Finset.piecewise_cases 8 := by
  intro hc
  have := hc (ι := PUnit.{2}) (π := fun _ => Bool) Finset.univ (fun _ => true) (fun _ => false)
    (i := PUnit.unit) (fun b => b = false) rfl
  simp at this

-- `Finset.piecewise_cases` idx 9: necessary (universe 1: s = empty, f = true, g = false, p = (· = true))
theorem c1_19 : ¬ drop1% Finset.piecewise_cases 9 := by
  intro hc
  have := hc (ι := PUnit.{2}) (π := fun _ => Bool) ∅ (fun _ => true) (fun _ => false)
    (i := PUnit.unit) (fun b => b = true) rfl
  simp at this

-- `Finset.piecewise_piecewise_of_subset_left` idx 6: necessary (universe 1: s = univ, t = empty, f1 = true, f2 = false)
theorem c1_20 : ¬ drop1% Finset.piecewise_piecewise_of_subset_left 6 := by
  intro hc
  have := hc (ι := PUnit.{2}) (π := fun _ => Bool) (s := Finset.univ) (t := ∅) (fun _ => true) (fun _ => false)
    (fun _ => false)
  have := congrFun this PUnit.unit
  simp at this

-- `Finset.piecewise_piecewise_of_subset_right` idx 6: necessary (universe 1: s = empty, t = univ, g1 = true, g2 = false)
theorem c1_21 : ¬ drop1% Finset.piecewise_piecewise_of_subset_right 6 := by
  intro hc
  have := hc (ι := PUnit.{2}) (π := fun _ => Bool) (s := ∅) (t := Finset.univ) (fun _ => false) (fun _ => true)
    (fun _ => false)
  have := congrFun this PUnit.unit
  simp at this

-- `Finset.update_piecewise_of_mem` idx 8: necessary (universe 1: s = empty, g = false, v = true)
theorem c1_22 : ¬ drop1% Finset.update_piecewise_of_mem 8 := by
  intro hc
  have := hc (ι := PUnit.{2}) (π := fun _ => Bool) ∅ (fun _ => false) (fun _ => false) (i := PUnit.unit) true
  have := congrFun this PUnit.unit
  simp at this

-- `Finset.update_piecewise_of_notMem` idx 8: necessary (universe 1: s = univ, f = false, v = true)
theorem c1_23 : ¬ drop1% Finset.update_piecewise_of_notMem 8 := by
  intro hc
  have := hc (ι := PUnit.{2}) (π := fun _ => Bool) Finset.univ (fun _ => false) (fun _ => false)
    (i := PUnit.unit) true
  have := congrFun this PUnit.unit
  simp at this

-- `Finset.piecewise_mem_set_pi` idx 8: necessary (Unit, s = univ, t' = {0}, f = 1, g = 0)
theorem c1_24 : ¬ drop0% Finset.piecewise_mem_set_pi 8 := by
  intro hc
  have := hc (ι := Unit) Finset.univ (π := fun _ => ℕ) (t := Set.univ) (t' := fun _ => {0})
    (f := fun _ => 1) (g := fun _ => 0) (by simp)
  simp at this

-- `Finset.piecewise_mem_set_pi` idx 9: necessary (Unit, s = empty, t' = {0}, f = 0, g = 1)
theorem c1_25 : ¬ drop0% Finset.piecewise_mem_set_pi 9 := by
  intro hc
  have := hc (ι := Unit) ∅ (π := fun _ => ℕ) (t := Set.univ) (t' := fun _ => {0})
    (f := fun _ => 0) (g := fun _ => 1) (by simp)
  simp at this

-- `Finset.piecewise_le_of_le_of_le` idx 8: necessary (Unit, s = univ, f = 1, g = h = 0)
theorem c1_26 : ¬ drop0% Finset.piecewise_le_of_le_of_le 8 := by
  intro hc
  have := hc (ι := Unit) Finset.univ (π := fun _ => ℕ) (f := fun _ => 1) (g := fun _ => 0) (h := fun _ => 0) le_rfl
  have := this ()
  simp at this

-- `Finset.piecewise_le_of_le_of_le` idx 9: necessary (Unit, s = empty, g = 1, f = h = 0)
theorem c1_27 : ¬ drop0% Finset.piecewise_le_of_le_of_le 9 := by
  intro hc
  have := hc (ι := Unit) ∅ (π := fun _ => ℕ) (f := fun _ => 0) (g := fun _ => 1) (h := fun _ => 0) le_rfl
  have := this ()
  simp at this

-- `Finset.le_piecewise_of_le_of_le` idx 8: necessary (Unit, s = univ, h = g = 1, f = 0)
theorem c1_28 : ¬ drop0% Finset.le_piecewise_of_le_of_le 8 := by
  intro hc
  have := hc (ι := Unit) Finset.univ (π := fun _ => ℕ) (f := fun _ => 0) (g := fun _ => 1) (h := fun _ => 1) le_rfl
  have := this ()
  simp at this

-- `Finset.le_piecewise_of_le_of_le` idx 9: necessary (Unit, s = empty, h = f = 1, g = 0)
theorem c1_29 : ¬ drop0% Finset.le_piecewise_of_le_of_le 9 := by
  intro hc
  have := hc (ι := Unit) ∅ (π := fun _ => ℕ) (f := fun _ => 1) (g := fun _ => 0) (h := fun _ => 1) le_rfl
  have := this ()
  simp at this

-- `Finset.piecewise_le_piecewise'` idx 9: necessary (Unit, s = univ, f = 1, f' = g = g' = 0)
theorem c1_30 : ¬ drop0% Finset.piecewise_le_piecewise' 9 := by
  intro hc
  have := hc (ι := Unit) Finset.univ (π := fun _ => ℕ) (f := fun _ => 1) (f' := fun _ => 0) (g := fun _ => 0)
    (g' := fun _ => 0) (fun _ _ => le_rfl)
  have := this ()
  simp at this

-- `Finset.piecewise_le_piecewise'` idx 10: necessary (Unit, s = empty, g = 1, g' = f = f' = 0)
theorem c1_31 : ¬ drop0% Finset.piecewise_le_piecewise' 10 := by
  intro hc
  have := hc (ι := Unit) ∅ (π := fun _ => ℕ) (f := fun _ => 0) (f' := fun _ => 0) (g := fun _ => 1)
    (g' := fun _ => 0) (fun _ _ => le_rfl)
  have := this ()
  simp at this

-- `Finset.piecewise_le_piecewise` idx 9: necessary (Unit, s = univ, f = 1, f' = g = g' = 0)
theorem c1_32 : ¬ drop0% Finset.piecewise_le_piecewise 9 := by
  intro hc
  have := hc (ι := Unit) Finset.univ (π := fun _ => ℕ) (f := fun _ => 1) (f' := fun _ => 0) (g := fun _ => 0)
    (g' := fun _ => 0) le_rfl
  have := this ()
  simp at this

-- `Finset.piecewise_le_piecewise` idx 10: necessary (Unit, s = empty, g = 1, g' = f = f' = 0)
theorem c1_33 : ¬ drop0% Finset.piecewise_le_piecewise 10 := by
  intro hc
  have := hc (ι := Unit) ∅ (π := fun _ => ℕ) (f := fun _ => 0) (f' := fun _ => 0) (g := fun _ => 1)
    (g' := fun _ => 0) le_rfl
  have := this ()
  simp at this

-- `Finset.piecewise_mem_Icc_of_mem_of_mem` idx 10: necessary (Unit, s = empty, g = 1, f = f' = g' = 0)
theorem c1_34 : ¬ drop0% Finset.piecewise_mem_Icc_of_mem_of_mem 10 := by
  intro hc
  have := hc (ι := Unit) ∅ (π := fun _ => ℕ) (f := fun _ => 0) (g := fun _ => 1) (f' := fun _ => 0)
    (g' := fun _ => 0) ⟨le_rfl, le_rfl⟩
  have := this.2 ()
  simp at this

-- `Finset.piecewise_mem_Icc` idx 7: necessary (Unit, s = empty, f = 1, g = 0)
theorem c1_35 : ¬ drop0% Finset.piecewise_mem_Icc 7 := by
  intro hc
  have := hc (ι := Unit) ∅ (π := fun _ => ℕ) (f := fun _ => 1) (g := fun _ => 0)
  have := this.1 ()
  simp at this

-- `Finset.piecewise_mem_Icc'` idx 7: necessary (Unit, s = empty, g = 1, f = 0)
theorem c1_36 : ¬ drop0% Finset.piecewise_mem_Icc' 7 := by
  intro hc
  have := hc (ι := Unit) ∅ (π := fun _ => ℕ) (f := fun _ => 0) (g := fun _ => 1)
  have := this.2 ()
  simp at this

-- `Finset.injOn_image_of_biUnion_injOn` idx 6: necessary (S = {{0},{1}}, f constant into Unit)
theorem c1_37 : ¬ drop0% Finset.injOn_image_of_biUnion_injOn 6 := by
  intro hc
  have := @hc ℕ Unit _ _ {{0}, {1}} (fun _ => ()) {0} (by simp) {1} (by simp) (by simp)
  exact absurd this (by decide)

-- `Finset.pairwiseDisjoint_pair_insert` idx 4: necessary (s = {0}, a = 0: images of empty and {0} share {0})
theorem c1_38 : ¬ drop0% Finset.pairwiseDisjoint_pair_insert 4 := by
  intro hc
  have := @hc ℕ {0} _ 0 ∅ (by simp) {0} (by simp) (by decide)
  simp [Function.onFun] at this

-- `Finset.filter_powersetCard_subset` idx 6: necessary (s = t = {0}, n = 0)
theorem c1_39 : ¬ drop0% Finset.filter_powersetCard_subset 6 := by
  intro hc
  have := hc (α := ℕ) {0} {0} 0 (by decide)
  revert this; decide

-- `Finset.card_filter_powersetCard_subset` idx 6: necessary (s = t = {0}, n = 0: 0 = 1)
theorem c1_40 : ¬ drop0% Finset.card_filter_powersetCard_subset 6 := by
  intro hc
  have := hc (α := ℕ) {0} {0} 0 (by decide)
  revert this; decide

-- `Disjoint.powersetCard_powersetCard_finset` idx 4: necessary (s = t = {0}, n = m = 1)
theorem c1_41 : ¬ drop0% Disjoint.powersetCard_powersetCard_finset 4 := by
  intro hc
  have := hc (α := ℕ) (n := 1) (s := {0}) (t := {0}) (m := 1) (Or.inl one_ne_zero)
  revert this; decide

-- `Finset.eq_of_powersetCard_eq` idx 4: removable (derivable: powersetCard r a nonempty (1 <= r <= #a) forces r <= #b, then both biUnions give a = b)
theorem c1_42 : drop% Finset.eq_of_powersetCard_eq 4 := by
  intro α a b r hr₀ hra h
  classical
  have hb : r ≤ b.card := by
    by_contra hb; push_neg at hb
    rw [Finset.powersetCard_eq_empty.2 hb, Finset.powersetCard_eq_empty] at h; omega
  simpa [Finset.powersetCard_biUnion hr₀ hra, Finset.powersetCard_biUnion hr₀ hb] using congr(($h).biUnion id)

-- `Finset.eq_of_powersetCard_eq` idx 5: necessary (r = 0, a = {0}, b = {1})
theorem c1_43 : ¬ drop0% Finset.eq_of_powersetCard_eq 5 := by
  intro hc
  have := hc (a := ({0} : Finset ℕ)) (b := {1}) (r := 0) rfl (by simp) (by simp)
  exact absurd this (by decide)

-- `Finset.eq_of_powersetCard_eq` idx 6: necessary (r = 2, a = {0}, b = {1}: both powersetCards empty)
theorem c1_44 : ¬ drop0% Finset.eq_of_powersetCard_eq 6 := by
  intro hc
  have := hc (a := ({0} : Finset ℕ)) (b := {1}) (r := 2) rfl (by simp) (by decide)
  exact absurd this (by decide)

-- `Finset.eq_of_powersetCard_eq` idx 7: necessary (r = 1, a = {0}, b = {1})
theorem c1_45 : ¬ drop0% Finset.eq_of_powersetCard_eq 7 := by
  intro hc
  have := hc (a := ({0} : Finset ℕ)) (b := {1}) (r := 1) rfl (by simp) (by simp)
  exact absurd this (by decide)

-- `Finset.powersetCard_injOn` idx 3: necessary (q = 1, r = 0: {0} and {1} both give {empty})
theorem c1_46 : ¬ drop0% Finset.powersetCard_injOn 3 := by
  intro hc
  have := @hc ℕ 1 0 (by simp) {0} (by simp) {1} (by simp) (by simp)
  exact absurd this (by decide)

-- `Finset.powersetCard_injOn` idx 4: necessary (q = 1, r = 2: everything maps to empty)
theorem c1_47 : ¬ drop0% Finset.powersetCard_injOn 4 := by
  intro hc
  have := @hc ℕ 1 2 (by simp) {0} (by simp) {1} (by simp) (by decide)
  exact absurd this (by decide)

-- `Finset.mem_preimage` idx 4: necessary (f : Bool -> Unit constant, s = {()})
theorem c1_48 : ¬ indep0% Finset.mem_preimage 4 := fun hc => W2c1.ni {()} (by simp) (@hc Bool Unit (fun _ => ()) {()} true)

-- `Finset.coe_preimage` idx 4: necessary (f : Bool -> Unit constant, s = {()})
theorem c1_49 : ¬ indep0% Finset.coe_preimage 4 := fun hc => W2c1.ni {()} (by simp) (@hc Bool Unit (fun _ => ()) {()})

-- `Finset.disjoint_preimage` idx 5: necessary (f : Bool -> Unit constant, s = {()}, t = empty)
theorem c1_50 : ¬ indep0% Finset.disjoint_preimage 5 := fun hc =>
  W2c1.ni {()} (by simp) (@hc Bool Unit (fun _ => ()) {()} ∅ (by simp) (by simp))

-- `Finset.disjoint_preimage` idx 6: necessary (f : Bool -> Unit constant, s = empty, t = {()})
theorem c1_51 : ¬ indep0% Finset.disjoint_preimage 6 := fun hc =>
  W2c1.ni {()} (by simp) (@hc Bool Unit (fun _ => ()) ∅ {()} (by simp) (by simp))

-- `Finset.disjoint_preimage` idx 7: necessary (f = id on Unit, s = t = {()})
theorem c1_52 : ¬ drop0% Finset.disjoint_preimage 7 := by
  intro hc
  have := @hc Unit Unit id {()} {()} Function.injective_id.injOn Function.injective_id.injOn
  have h2 := Finset.disjoint_left.1 this
  exact @h2 () (by simp) (by simp)

-- `Finset.preimage_inter` idx 7: necessary (f : Bool -> Unit constant, s = {()}, t = empty)
theorem c1_53 : ¬ indep0% Finset.preimage_inter 7 := fun hc =>
  W2c1.ni {()} (by simp) (@hc Bool Unit _ _ (fun _ => ()) {()} ∅ (by simp))

-- `Finset.preimage_inter` idx 8: necessary (f : Bool -> Unit constant, s = empty, t = {()})
theorem c1_54 : ¬ indep0% Finset.preimage_inter 8 := fun hc =>
  W2c1.ni {()} (by simp) (@hc Bool Unit _ _ (fun _ => ()) ∅ {()} (by simp))

-- `Finset.preimage_union` idx 7: necessary (f : Bool -> Unit constant, s = t = {()})
theorem c1_55 : ¬ indep0% Finset.preimage_union 7 := fun hc =>
  W2c1.ni ({()} ∪ {()}) (by simp) (@hc Bool Unit _ _ (fun _ => ()) {()} {()})

-- `Finset.preimage_compl'` idx 9: necessary (f : Bool -> Unit constant, s = univ (complement empty))
theorem c1_56 : ¬ indep0% Finset.preimage_compl' 9 := fun hc =>
  W2c1.ni Finset.univ (by simp) (@hc Bool Unit _ _ _ _ (fun _ => ()) Finset.univ
    (by rw [Finset.compl_univ, Finset.coe_empty, Set.preimage_empty]; exact Set.injOn_empty _))

-- `Finset.image_subset_iff_subset_preimage` idx 6: necessary (f : Bool -> Unit constant, t = {()})
theorem c1_57 : ¬ indep0% Finset.image_subset_iff_subset_preimage 6 := fun hc =>
  W2c1.ni {()} (by simp) (@hc Bool Unit _ (fun _ => ()) ∅ {()})

-- `Finset.image_eq_preimage_of_leftInvOn_injOn` idx 6: necessary (f = succ, g = id on Nat, s = {0}: image {1}, preimage {0})
theorem c1_58 : ¬ drop0% Finset.image_eq_preimage_of_leftInvOn_injOn 6 := by
  intro hc
  have := @hc ℕ ℕ _ Nat.succ id {0} Function.injective_id.injOn
  have h1 : (1 : ℕ) ∈ Finset.image Nat.succ {0} := by simp
  rw [this, Finset.mem_preimage] at h1
  simp at h1

-- `Finset.image_eq_preimage_of_leftInvOn_injOn` idx 7: necessary (f : Unit -> Bool, g : Bool -> Unit constant, s = {()})
theorem c1_59 : ¬ indep0% Finset.image_eq_preimage_of_leftInvOn_injOn 7 := fun hc =>
  W2c1.ni {()} (by simp) (@hc Unit Bool _ (fun _ => true) (fun _ => ()) {()} (fun x _ => rfl))

-- `Finset.image_preimage_of_bij` idx 5: necessary (f : Bool -> Unit constant, s = {()})
theorem c1_60 : ¬ indep0% Finset.image_preimage_of_bij 5 := fun hc =>
  W2c1.ni {()} (by simp) (@hc Bool Unit _ (fun _ => ()) {()}).2.1

-- `Finset.preimage_subset_of_subset_image` idx 6: necessary (f = id on Nat, s = {0}, t = empty)
theorem c1_61 : ¬ drop0% Finset.preimage_subset_of_subset_image 6 := by
  intro hc
  have := @hc ℕ ℕ _ id {0} ∅ Function.injective_id.injOn
  have := @this 0 (by simp)
  simp at this

-- `Finset.preimage_subset_of_subset_image` idx 7: necessary (f : Bool -> Unit constant, s = {()}, t = univ)
theorem c1_62 : ¬ indep0% Finset.preimage_subset_of_subset_image 7 := fun hc =>
  W2c1.ni {()} (by simp) (@hc Bool Unit _ (fun _ => ()) {()} Finset.univ (by decide))

-- `Finset.preimage_subset` idx 5: necessary (f = id embedding on Nat, s = {0}, t = empty)
theorem c1_63 : ¬ drop0% Finset.preimage_subset 5 := by
  intro hc
  have := @hc ℕ ℕ (Function.Embedding.refl ℕ) {0} ∅
  have := @this 0 (by simp)
  simp at this

-- `Finset.sup_preimage_self` idx 2: removable (unused: the sup over the preimage equals the sup over its image, which is s by image_preimage_of_bij (no Nonempty needed))
theorem c1_64 : drop% Finset.sup_preimage_self 2 := by
  intro α β _ _ s f hf
  classical
  calc (s.preimage f hf.2.1).sup f = (s.preimage f hf.2.1).sup (id ∘ f) := rfl
    _ = ((s.preimage f hf.2.1).image f).sup id := (Finset.sup_image _ _ _).symm
    _ = s.sup id := by rw [Finset.image_preimage_of_bij f s hf]

-- `Finset.sup_preimage_self` idx 7: necessary (f : Bool -> Bool constant false, s = {false})
theorem c1_65 : ¬ indep0% Finset.sup_preimage_self 7 := by
  intro hc
  have := (@hc Bool Bool _ _ _ {false} (fun _ => false)).2.1
  exact absurd (@this true (by simp) false (by simp) rfl) (by decide)

-- `Finset.sup_preimage_val_id` idx 4: necessary (Bool x Bool, P x = (x != (true, true)), t = empty)
theorem c1_66 : ¬ indep0% Finset.sup_preimage_val_id 4 := by
  intro hc
  have := @hc (Bool × Bool) _ _ (fun x => x ≠ (true, true)) (by decide) ∅ (by simp) (true, false) (false, true)
    (by decide) (by decide)
  revert this; decide

-- `Finset.sigma_preimage_mk_of_subset` idx 5: necessary (s = {(0,0)}, t = empty)
theorem c1_67 : ¬ drop0% Finset.sigma_preimage_mk_of_subset 5 := by
  intro hc
  have := hc (α := ℕ) (β := fun _ => ℕ) {⟨0, 0⟩} (t := ∅)
  have h := congrArg (fun u => (⟨0, 0⟩ : (_ : ℕ) × ℕ) ∈ u) this
  simp at h

-- `Finset.mk_mem_product` idx 6: necessary (s = empty, t = {0}, a = b = 0)
theorem c1_68 : ¬ drop0% Finset.mk_mem_product 6 := by
  intro hc
  have := @hc ℕ ℕ ∅ {0} 0 0 (by simp)
  simp at this

-- `Finset.mk_mem_product` idx 7: necessary (s = {0}, t = empty, a = b = 0)
theorem c1_69 : ¬ drop0% Finset.mk_mem_product 7 := by
  intro hc
  have := @hc ℕ ℕ {0} ∅ 0 0 (by simp)
  simp at this

-- `Finset.product_subset_product` idx 7: necessary (s = s' = t = {0}, t' = empty)
theorem c1_70 : ¬ drop0% Finset.product_subset_product 7 := by
  intro hc
  have := @hc ℕ ℕ {0} {0} {0} ∅ subset_rfl (0, 0) (by simp)
  simp at this

-- `Finset.product_subset_product_right` idx 5: necessary (s = t = {0}, t' = empty)
theorem c1_71 : ¬ drop0% Finset.product_subset_product_right 5 := by
  intro hc
  have := @hc ℕ ℕ {0} {0} ∅ (0, 0) (by simp)
  simp at this

-- `Finset.Nonempty.product` idx 4: necessary (s = empty, t = {0})
theorem c1_72 : ¬ drop0% Finset.Nonempty.product 4 := by
  intro hc
  have := @hc ℕ ℕ ∅ {0} (by simp)
  simp at this

-- `Finset.Nonempty.product` idx 5: necessary (s = {0}, t = empty)
theorem c1_73 : ¬ drop0% Finset.Nonempty.product 5 := by
  intro hc
  have := @hc ℕ ℕ {0} ∅ (by simp)
  simp at this

-- `Finset.sdiff_subset_sdiff` idx 7: necessary (s = t = v = {0}, u = empty)
theorem c1_74 : ¬ drop0% Finset.sdiff_subset_sdiff 7 := by
  intro hc
  have := @hc ℕ _ {0} {0} ∅ {0} subset_rfl 0 (by simp)
  simp at this

-- `Finset.sdiff_subset_sdiff_iff_subset` idx 5: removable (derivable: if r \ s ⊆ r \ t and x ∈ t ⊆ r, x ∉ s would put x in r \ t; s ⊆ r is never used)
theorem c1_75 : drop% Finset.sdiff_subset_sdiff_iff_subset 5 := by
  intro α _ s t r ht
  constructor
  · intro h x hx
    by_contra hxs
    exact (Finset.mem_sdiff.1 (h (Finset.mem_sdiff.2 ⟨ht hx, hxs⟩))).2 hx
  · intro h
    exact Finset.sdiff_subset_sdiff subset_rfl h

-- `Finset.sdiff_ssubset` idx 4: necessary (s = empty, t = {0})
theorem c1_76 : ¬ drop0% Finset.sdiff_ssubset 4 := by
  intro hc
  have := @hc ℕ _ ∅ {0} (by simp)
  simp at this

-- `Finset.sdiff_union_sdiff_cancel` idx 6: necessary (s = {0}, t = empty, u = {0})
theorem c1_77 : ¬ drop0% Finset.sdiff_union_sdiff_cancel 6 := by
  intro hc
  have := @hc ℕ _ {0} ∅ {0} (by simp)
  revert this; decide

-- `Set.IsPWO.vadd` idx 5: necessary (W (Int ordered through phi, incompatible with +): SW + {1} not PWO)
theorem c1_78 : ¬ drop0% Set.IsPWO.vadd 5 := fun hc =>
  W2c1.SW_vadd_not_wf (hc (G := W2c1.W) (P := W2c1.W) W2c1.SW_wf.isPWO (Set.isPWO_singleton _)).isWF

-- `Set.IsPWO.vadd` idx 8: necessary (Int, s = univ, t = {0})
theorem c1_79 : ¬ drop0% Set.IsPWO.vadd 8 := by
  intro hc
  have := hc (G := ℤ) (P := ℤ) (s := Set.univ) (t := {0}) (Set.isPWO_singleton _)
  exact W2c1.int_univ_not_pwo (this.mono fun x _ => Set.mem_vadd.2 ⟨x, trivial, 0, rfl, by simp⟩)

-- `Set.IsPWO.vadd` idx 9: necessary (Int, s = {0}, t = univ)
theorem c1_80 : ¬ drop0% Set.IsPWO.vadd 9 := by
  intro hc
  have := hc (G := ℤ) (P := ℤ) (s := {0}) (t := Set.univ) (Set.isPWO_singleton _)
  exact W2c1.int_univ_not_pwo (this.mono fun x _ => Set.mem_vadd.2 ⟨0, rfl, x, trivial, by simp⟩)

-- `Set.IsPWO.smul` idx 5: necessary (MW (Multiplicative Int ordered through phi): SM * {1} not PWO)
theorem c1_81 : ¬ drop0% Set.IsPWO.smul 5 := fun hc =>
  W2c1.SM_smul_not_wf (hc (G := W2c1.MW) (P := W2c1.MW) W2c1.SM_wf.isPWO (Set.isPWO_singleton _)).isWF

-- `Set.IsPWO.smul` idx 8: necessary (Multiplicative Int, s = univ, t = {1})
theorem c1_82 : ¬ drop0% Set.IsPWO.smul 8 := by
  intro hc
  have := hc (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := Set.univ) (t := {1}) (Set.isPWO_singleton _)
  exact W2c1.mint_univ_not_pwo (this.mono fun x _ => Set.mem_smul.2 ⟨x, trivial, 1, rfl, by simp⟩)

-- `Set.IsPWO.smul` idx 9: necessary (Multiplicative Int, s = {1}, t = univ)
theorem c1_83 : ¬ drop0% Set.IsPWO.smul 9 := by
  intro hc
  have := hc (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := {1}) (t := Set.univ) (Set.isPWO_singleton _)
  exact W2c1.mint_univ_not_pwo (this.mono fun x _ => Set.mem_smul.2 ⟨1, rfl, x, trivial, by simp⟩)

-- `Set.IsWF.vadd` idx 5: necessary (W (Int ordered through phi, incompatible with +): SW + {1} not WF)
theorem c1_84 : ¬ drop0% Set.IsWF.vadd 5 := fun hc =>
  W2c1.SW_vadd_not_wf (hc (G := W2c1.W) (P := W2c1.W) W2c1.SW_wf Set.isWF_singleton)

-- `Set.IsWF.vadd` idx 8: necessary (Int, s = univ, t = {0})
theorem c1_85 : ¬ drop0% Set.IsWF.vadd 8 := by
  intro hc
  have := hc (G := ℤ) (P := ℤ) (s := Set.univ) (t := {0}) Set.isWF_singleton
  exact W2c1.int_univ_not_wf (this.mono fun x _ => Set.mem_vadd.2 ⟨x, trivial, 0, rfl, by simp⟩)

-- `Set.IsWF.vadd` idx 9: necessary (Int, s = {0}, t = univ)
theorem c1_86 : ¬ drop0% Set.IsWF.vadd 9 := by
  intro hc
  have := hc (G := ℤ) (P := ℤ) (s := {0}) (t := Set.univ) Set.isWF_singleton
  exact W2c1.int_univ_not_wf (this.mono fun x _ => Set.mem_vadd.2 ⟨0, rfl, x, trivial, by simp⟩)

-- `Set.IsWF.smul` idx 5: necessary (MW (Multiplicative Int ordered through phi): SM * {1} not WF)
theorem c1_87 : ¬ drop0% Set.IsWF.smul 5 := fun hc =>
  W2c1.SM_smul_not_wf (hc (G := W2c1.MW) (P := W2c1.MW) W2c1.SM_wf Set.isWF_singleton)

-- `Set.IsWF.smul` idx 8: necessary (Multiplicative Int, s = univ, t = {1})
theorem c1_88 : ¬ drop0% Set.IsWF.smul 8 := by
  intro hc
  have := hc (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := Set.univ) (t := {1}) Set.isWF_singleton
  exact W2c1.mint_univ_not_wf (this.mono fun x _ => Set.mem_smul.2 ⟨x, trivial, 1, rfl, by simp⟩)

-- `Set.IsWF.smul` idx 9: necessary (Multiplicative Int, s = {1}, t = univ)
theorem c1_89 : ¬ drop0% Set.IsWF.smul 9 := by
  intro hc
  have := hc (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := {1}) (t := Set.univ) Set.isWF_singleton
  exact W2c1.mint_univ_not_wf (this.mono fun x _ => Set.mem_smul.2 ⟨1, rfl, x, trivial, by simp⟩)

-- `Set.IsWF.min_vadd` idx 8: necessary (Int, s = univ, t = {0})
theorem c1_90 : ¬ indep0% Set.IsWF.min_vadd 8 := fun hc =>
  W2c1.int_univ_not_wf (hc (G := ℤ) (P := ℤ) (s := Set.univ) (t := {0}) Set.isWF_singleton ⟨0, trivial⟩ ⟨0, rfl⟩)

-- `Set.IsWF.min_vadd` idx 9: necessary (Int, s = {0}, t = univ)
theorem c1_91 : ¬ indep0% Set.IsWF.min_vadd 9 := fun hc =>
  W2c1.int_univ_not_wf (hc (G := ℤ) (P := ℤ) (s := {0}) (t := Set.univ) Set.isWF_singleton ⟨0, rfl⟩ ⟨0, trivial⟩)

-- `Set.IsWF.min_smul` idx 8: necessary (Multiplicative Int, s = univ, t = {1})
theorem c1_92 : ¬ indep0% Set.IsWF.min_smul 8 := fun hc =>
  W2c1.mint_univ_not_wf (hc (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := Set.univ) (t := {1})
    Set.isWF_singleton ⟨1, trivial⟩ ⟨1, rfl⟩)

-- `Set.IsWF.min_smul` idx 9: necessary (Multiplicative Int, s = {1}, t = univ)
theorem c1_93 : ¬ indep0% Set.IsWF.min_smul 9 := fun hc =>
  W2c1.mint_univ_not_wf (hc (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := {1}) (t := Set.univ)
    Set.isWF_singleton ⟨1, rfl⟩ ⟨1, trivial⟩)

-- `Finset.mem_vaddAntidiagonal` idx 6: necessary (Int with addition, s = t = univ, a = 0: antidiagonal infinite)
theorem c1_94 : ¬ indep0% Finset.mem_vaddAntidiagonal 6 := fun hc => W2c1.vanti_inf (@hc ℤ ℤ _ Set.univ Set.univ 0 (0, 0))

-- `Finset.mem_smulAntidiagonal` idx 6: necessary (Int acting on Int by multiplication, s = t = univ, a = 0: antidiagonal infinite)
theorem c1_95 : ¬ indep0% Finset.mem_smulAntidiagonal 6 := fun hc => W2c1.santi_inf (@hc ℤ ℤ _ Set.univ Set.univ 0 (0, 0))

-- `Finset.vaddAntidiagonal_mono_left` idx 7: necessary (Unit, s = empty, u = t = univ)
theorem c1_96 : ¬ drop0% Finset.vaddAntidiagonal_mono_left 7 := by
  intro hc
  have := @hc Unit Unit _ ∅ Set.univ Set.univ () (Set.toFinite _) (Set.toFinite _)
  have := @this ((), ()) (by simp)
  simp at this

-- `Finset.vaddAntidiagonal_mono_left` idx 8: necessary (Int with addition, u = empty, s = t = univ, a = 0)
theorem c1_97 : ¬ indep0% Finset.vaddAntidiagonal_mono_left 8 := fun hc =>
  W2c1.vanti_inf (@hc ℤ ℤ _ Set.univ ∅ Set.univ 0 (Set.empty_subset _) (W2c1.vanti_empty _ _))

-- `Finset.vaddAntidiagonal_mono_left` idx 9: removable (derivable: u ⊆ s, so the u-antidiagonal is a subset of the finite s-antidiagonal)
theorem c1_98 : indep% Finset.vaddAntidiagonal_mono_left 9 := by
  intro G P _ s u t a hus hst
  exact hst.subset (Set.vaddAntidiagonal_mono_left hus)

-- `Finset.smulAntidiagonal_mono_left` idx 7: necessary (Unit, s = empty, u = t = univ)
theorem c1_99 : ¬ drop0% Finset.smulAntidiagonal_mono_left 7 := by
  intro hc
  have := @hc Unit Unit _ ∅ Set.univ Set.univ () (Set.toFinite _) (Set.toFinite _)
  have := @this ((), ()) (by simp)
  simp at this

-- `Finset.smulAntidiagonal_mono_left` idx 8: necessary (Int acting on Int by multiplication, u = empty, s = t = univ, a = 0)
theorem c1_100 : ¬ indep0% Finset.smulAntidiagonal_mono_left 8 := fun hc =>
  W2c1.santi_inf (@hc ℤ ℤ _ Set.univ ∅ Set.univ 0 (Set.empty_subset _) (W2c1.santi_empty _ _))

-- `Finset.smulAntidiagonal_mono_left` idx 9: removable (derivable: u ⊆ s, so the u-antidiagonal is a subset of the finite s-antidiagonal)
theorem c1_101 : indep% Finset.smulAntidiagonal_mono_left 9 := by
  intro G P _ s u t a hus hst
  exact hst.subset (Set.smulAntidiagonal_mono_left hus)

-- `Finset.vaddAntidiagonal_mono_right` idx 7: necessary (Int with addition, v = empty, s = t = univ, a = 0)
theorem c1_102 : ¬ indep0% Finset.vaddAntidiagonal_mono_right 7 := fun hc =>
  W2c1.vanti_inf (@hc ℤ ℤ _ Set.univ Set.univ ∅ 0 (W2c1.vanti_empty' _ _) (Set.empty_subset _))

-- `Finset.vaddAntidiagonal_mono_right` idx 8: removable (derivable: v ⊆ t, so the v-antidiagonal is a subset of the finite t-antidiagonal)
theorem c1_103 : indep% Finset.vaddAntidiagonal_mono_right 8 := by
  intro G P _ s t v a hst hvt
  exact hst.subset (Set.vaddAntidiagonal_mono_right hvt)

-- `Finset.vaddAntidiagonal_mono_right` idx 9: necessary (Unit, t = empty, s = v = univ)
theorem c1_104 : ¬ drop0% Finset.vaddAntidiagonal_mono_right 9 := by
  intro hc
  have := @hc Unit Unit _ Set.univ ∅ Set.univ () (Set.toFinite _) (Set.toFinite _)
  have := @this ((), ()) (by simp)
  simp at this

-- `Finset.smulAntidiagonal_mono_right` idx 7: necessary (Int acting on Int by multiplication, v = empty, s = t = univ, a = 0)
theorem c1_105 : ¬ indep0% Finset.smulAntidiagonal_mono_right 7 := fun hc =>
  W2c1.santi_inf (@hc ℤ ℤ _ Set.univ Set.univ ∅ 0 (W2c1.santi_empty' _ _) (Set.empty_subset _))

-- `Finset.smulAntidiagonal_mono_right` idx 8: removable (derivable: v ⊆ t, so the v-antidiagonal is a subset of the finite t-antidiagonal)
theorem c1_106 : indep% Finset.smulAntidiagonal_mono_right 8 := by
  intro G P _ s t v a hst hvt
  exact hst.subset (Set.smulAntidiagonal_mono_right hvt)

-- `Finset.smulAntidiagonal_mono_right` idx 9: necessary (Unit, t = empty, s = v = univ)
theorem c1_107 : ¬ drop0% Finset.smulAntidiagonal_mono_right 9 := by
  intro hc
  have := @hc Unit Unit _ Set.univ ∅ Set.univ () (Set.toFinite _) (Set.toFinite _)
  have := @this ((), ()) (by simp)
  simp at this

-- `Finset.support_vaddAntidiagonal_subset_vadd` idx 5: necessary (Int with addition, s = t = univ, a = 0)
theorem c1_108 : ¬ indep0% Finset.support_vaddAntidiagonal_subset_vadd 5 := fun hc => W2c1.vanti_inf (@hc ℤ ℤ _ Set.univ Set.univ 0)

-- `Finset.support_smulAntidiagonal_subset_smul` idx 5: necessary (Int acting on Int by multiplication, s = t = univ, a = 0)
theorem c1_109 : ¬ indep0% Finset.support_smulAntidiagonal_subset_smul 5 := fun hc => W2c1.santi_inf (@hc ℤ ℤ _ Set.univ Set.univ 0)

-- `Finset.isPWO_support_vaddAntidiagonal` idx 8: necessary (Int, s = univ, t = {0})
theorem c1_110 : ¬ indep0% Finset.isPWO_support_vaddAntidiagonal 8 := fun hc =>
  W2c1.int_univ_not_pwo (hc (G := ℤ) (P := ℤ) (s := Set.univ) (t := {0}) (Set.isPWO_singleton _))

-- `Finset.isPWO_support_vaddAntidiagonal` idx 9: necessary (Int, s = {0}, t = univ)
theorem c1_111 : ¬ indep0% Finset.isPWO_support_vaddAntidiagonal 9 := fun hc =>
  W2c1.int_univ_not_pwo (hc (G := ℤ) (P := ℤ) (s := {0}) (t := Set.univ) (Set.isPWO_singleton _))

-- `Finset.isPWO_support_smulAntidiagonal` idx 8: necessary (Multiplicative Int, s = univ, t = {1})
theorem c1_112 : ¬ indep0% Finset.isPWO_support_smulAntidiagonal 8 := fun hc =>
  W2c1.mint_univ_not_pwo (hc (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := Set.univ) (t := {1})
    (Set.isPWO_singleton _))

-- `Finset.isPWO_support_smulAntidiagonal` idx 9: necessary (Multiplicative Int, s = {1}, t = univ)
theorem c1_113 : ¬ indep0% Finset.isPWO_support_smulAntidiagonal 9 := fun hc =>
  W2c1.mint_univ_not_pwo (hc (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := {1}) (t := Set.univ)
    (Set.isPWO_singleton _))

-- `Finset.vaddAntidiagonal_min_vadd_min` idx 8: necessary (Int, s = univ, t = {0})
theorem c1_114 : ¬ indep0% Finset.vaddAntidiagonal_min_vadd_min 8 := fun hc =>
  W2c1.int_univ_not_wf (hc (G := ℤ) (P := ℤ) (s := Set.univ) (t := {0}) Set.isWF_singleton ⟨0, trivial⟩ ⟨0, rfl⟩)

-- `Finset.vaddAntidiagonal_min_vadd_min` idx 9: necessary (Int, s = {0}, t = univ)
theorem c1_115 : ¬ indep0% Finset.vaddAntidiagonal_min_vadd_min 9 := fun hc =>
  W2c1.int_univ_not_wf (hc (G := ℤ) (P := ℤ) (s := {0}) (t := Set.univ) Set.isWF_singleton ⟨0, rfl⟩ ⟨0, trivial⟩)

-- `Finset.smulAntidiagonal_min_smul_min` idx 8: necessary (Multiplicative Int, s = univ, t = {1})
theorem c1_116 : ¬ indep0% Finset.smulAntidiagonal_min_smul_min 8 := fun hc =>
  W2c1.mint_univ_not_wf (hc (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := Set.univ) (t := {1})
    Set.isWF_singleton ⟨1, trivial⟩ ⟨1, rfl⟩)

-- `Finset.smulAntidiagonal_min_smul_min` idx 9: necessary (Multiplicative Int, s = {1}, t = univ)
theorem c1_117 : ¬ indep0% Finset.smulAntidiagonal_min_smul_min 9 := fun hc =>
  W2c1.mint_univ_not_wf (hc (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := {1}) (t := Set.univ)
    Set.isWF_singleton ⟨1, rfl⟩ ⟨1, trivial⟩)

-- `Finset.smulAntidiagonal_min_smul_min` idx 10: necessary (Multiplicative Int, s = empty, t = {1})
theorem c1_118 : ¬ indep0% Finset.smulAntidiagonal_min_smul_min 10 := fun hc =>
  Set.not_nonempty_empty (hc (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := ∅) (t := {1})
    Set.isWF_empty Set.isWF_singleton ⟨1, rfl⟩)

-- `Finset.smulAntidiagonal_min_smul_min` idx 11: necessary (Multiplicative Int, s = {1}, t = empty)
theorem c1_119 : ¬ indep0% Finset.smulAntidiagonal_min_smul_min 11 := fun hc =>
  Set.not_nonempty_empty (hc (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := {1}) (t := ∅)
    Set.isWF_singleton Set.isWF_empty ⟨1, rfl⟩)

-- `Finset.Aesop.sigma_nonempty_of_exists_nonempty` idx 4: necessary (s = empty)
theorem c1_120 : ¬ drop0% Finset.Aesop.sigma_nonempty_of_exists_nonempty 4 := by
  intro hc
  have := @hc ℕ (fun _ => ℕ) ∅ (fun _ => {0})
  simp at this

-- `Finset.sigma_mono` idx 6: necessary (s1 = {0}, s2 = empty, t1 = t2 = {0})
theorem c1_121 : ¬ drop0% Finset.sigma_mono 6 := by
  intro hc
  have := @hc ℕ (fun _ => ℕ) {0} ∅ (fun _ => {0}) (fun _ => {0}) (fun _ => subset_rfl) ⟨0, 0⟩ (by simp)
  simp at this

-- `Finset.sigma_mono` idx 7: necessary (s1 = s2 = {0}, t1 = {0}, t2 = empty)
theorem c1_122 : ¬ drop0% Finset.sigma_mono 7 := by
  intro hc
  have := @hc ℕ (fun _ => ℕ) {0} {0} (fun _ => {0}) (fun _ => ∅) subset_rfl ⟨0, 0⟩ (by simp)
  simp at this

-- `Finset.notMem_sigmaLift_of_ne_left` idx 9: necessary (all Unit, f = {()})
theorem c1_123 : ¬ drop0% Finset.notMem_sigmaLift_of_ne_left 9 := by
  intro hc
  have := @hc Unit (fun _ => Unit) (fun _ => Unit) (fun _ => Unit) _ (fun _ _ _ => {()}) ⟨(), ()⟩ ⟨(), ()⟩ ⟨(), ()⟩
  simp [Finset.mem_sigmaLift] at this

-- `Finset.notMem_sigmaLift_of_ne_right` idx 9: necessary (all Unit, f = {()})
theorem c1_124 : ¬ drop0% Finset.notMem_sigmaLift_of_ne_right 9 := by
  intro hc
  have := @hc Unit (fun _ => Unit) (fun _ => Unit) (fun _ => Unit) _ (fun _ _ _ => {()}) ⟨(), ()⟩ ⟨(), ()⟩ ⟨(), ()⟩
  simp [Finset.mem_sigmaLift] at this

-- `Finset.sigmaLift_mono` idx 7: necessary (all Unit, f = {()}, g = empty)
theorem c1_125 : ¬ drop0% Finset.sigmaLift_mono 7 := by
  intro hc
  have := @hc Unit (fun _ => Unit) (fun _ => Unit) (fun _ => Unit) _ (fun _ _ _ => {()}) (fun _ _ _ => ∅)
    ⟨(), ()⟩ ⟨(), ()⟩ ⟨(), ()⟩ (by simp [Finset.mem_sigmaLift])
  simp [Finset.mem_sigmaLift] at this

-- `Set.Sized.mono` idx 4: necessary (A = {{0}}, B = empty, r = 0)
theorem c1_126 : ¬ drop0% Set.Sized.mono 4 := by
  intro hc
  have := @hc ℕ {{0}} ∅ 0 (fun x hx => absurd hx (Set.notMem_empty x))
  exact absurd (@this {0} rfl) (by decide)

-- `Set.Sized.mono` idx 5: necessary (A = B = {{0}}, r = 0)
theorem c1_127 : ¬ drop0% Set.Sized.mono 5 := by
  intro hc
  have := @hc ℕ {{0}} {{0}} 0 subset_rfl
  exact absurd (@this {0} rfl) (by decide)

-- `Set.sized.union` idx 4: necessary (A = {{0}}, B = empty, r = 0)
theorem c1_128 : ¬ drop0% Set.sized.union 4 := by
  intro hc
  have := @hc ℕ {{0}} ∅ 0
  exact absurd (@this {0} (Or.inl rfl)) (by decide)

-- `Set.Sized.subsingleton` idx 2: necessary (A = {empty, {0}})
theorem c1_129 : ¬ drop0% Set.Sized.subsingleton 2 := by
  intro hc
  have := @hc ℕ {∅, {0}} ∅ (by simp) {0} (by simp)
  exact absurd this (by decide)

-- `Set.Sized.subsingleton'` idx 3: necessary (alpha = Bool, A = {empty, {true}})
theorem c1_130 : ¬ drop0% Set.Sized.subsingleton' 3 := by
  intro hc
  have := @hc Bool {∅, {true}} _ ∅ (by simp) {true} (by simp)
  exact absurd this (by decide)

-- `Set.Sized.univ_mem_iff` idx 4: necessary (alpha = Unit, A = {univ, empty})
theorem c1_131 : ¬ drop0% Set.Sized.univ_mem_iff 4 := by
  intro hc
  have := (@hc Unit {Finset.univ, ∅} 0 _).1 (Or.inl rfl)
  have h2 : (∅ : Finset Unit) ∈ ({Finset.univ, ∅} : Set (Finset Unit)) := Or.inr rfl
  rw [this] at h2
  exact absurd h2 (by decide)

-- `Set.Sized.subset_powersetCard_univ` idx 4: necessary (alpha = Unit, family = {empty}, r = 1)
theorem c1_132 : ¬ drop0% Set.Sized.subset_powersetCard_univ 4 := by
  intro hc
  have := @hc Unit _ {∅} 1 ∅ (by simp)
  simp at this

-- `Finset.eq_of_mem_slice` idx 5: necessary (family = {empty}, A = empty, r1 = 1, r2 = 0)
theorem c1_133 : ¬ drop0% Finset.eq_of_mem_slice 5 := by
  intro hc
  have := @hc ℕ {∅} ∅ 1 0 (by simp [Finset.mem_slice])
  simp at this

-- `Finset.eq_of_mem_slice` idx 6: necessary (family = {empty}, A = empty, r1 = 0, r2 = 1)
theorem c1_134 : ¬ drop0% Finset.eq_of_mem_slice 6 := by
  intro hc
  have := @hc ℕ {∅} ∅ 0 1 (by simp [Finset.mem_slice])
  simp at this

-- `Finset.ne_of_mem_slice` idx 6: necessary (family = {empty}, A1 = A2 = empty, r1 = 1, r2 = 0)
theorem c1_135 : ¬ drop0% Finset.ne_of_mem_slice 6 := by
  intro hc
  exact @hc ℕ {∅} ∅ ∅ 1 0 (by simp [Finset.mem_slice]) (by simp) rfl

-- `Finset.ne_of_mem_slice` idx 7: necessary (family = {empty}, A1 = A2 = empty, r1 = 0, r2 = 1)
theorem c1_136 : ¬ drop0% Finset.ne_of_mem_slice 7 := by
  intro hc
  exact @hc ℕ {∅} ∅ ∅ 0 1 (by simp [Finset.mem_slice]) (by simp) rfl

-- `Finset.ne_of_mem_slice` idx 8: necessary (family = {empty}, A1 = A2 = empty, r1 = r2 = 0)
theorem c1_137 : ¬ drop0% Finset.ne_of_mem_slice 8 := by
  intro hc
  exact @hc ℕ {∅} ∅ ∅ 0 0 (by simp [Finset.mem_slice]) (by simp [Finset.mem_slice]) rfl

-- `Finset.sort_val` idx 4: necessary (rock-paper-scissors on Fin 3: total, antisymmetric, not transitive)
theorem c1_138 : ¬ indep0% Finset.sort_val 4 := fun hc => W2c1.rps_nt (hc (α := Fin 3) ∅ W2c1.rps)

-- `Finset.pairwise_sort` idx 4: necessary (rock-paper-scissors on Fin 3: total, antisymmetric, not transitive)
theorem c1_139 : ¬ indep0% Finset.pairwise_sort 4 := fun hc => W2c1.rps_nt (hc (α := Fin 3) ∅ W2c1.rps)

-- `Finset.sort_eq` idx 4: necessary (rock-paper-scissors on Fin 3: total, antisymmetric, not transitive)
theorem c1_140 : ¬ indep0% Finset.sort_eq 4 := fun hc => W2c1.rps_nt (hc (α := Fin 3) ∅ W2c1.rps)

-- `Finset.sort_nodup` idx 4: necessary (rock-paper-scissors on Fin 3: total, antisymmetric, not transitive)
theorem c1_141 : ¬ indep0% Finset.sort_nodup 4 := fun hc => W2c1.rps_nt (hc (α := Fin 3) ∅ W2c1.rps)

-- `Finset.sort_toFinset` idx 4: necessary (rock-paper-scissors on Fin 3: total, antisymmetric, not transitive)
theorem c1_142 : ¬ indep0% Finset.sort_toFinset 4 := fun hc => W2c1.rps_nt (hc (α := Fin 3) ∅ W2c1.rps)

-- `Finset.sort_empty` idx 3: necessary (rock-paper-scissors on Fin 3: total, antisymmetric, not transitive)
theorem c1_143 : ¬ indep0% Finset.sort_empty 3 := fun hc => W2c1.rps_nt (hc (α := Fin 3) W2c1.rps)

-- `Finset.sort_singleton` idx 3: necessary (rock-paper-scissors on Fin 3: total, antisymmetric, not transitive)
theorem c1_144 : ¬ indep0% Finset.sort_singleton 3 := fun hc => W2c1.rps_nt (hc (α := Fin 3) W2c1.rps 0)

-- `Finset.map_sort` idx 6: necessary (rock-paper-scissors on Fin 3, s = empty, target (Nat, <=))
theorem c1_145 : ¬ indep0% Finset.map_sort 6 := fun hc =>
  W2c1.rps_nt (@hc (Fin 3) ℕ Fin.valEmbedding ∅ W2c1.rps W2c1.rpsDec W2c1.rpsAnti W2c1.rpsTot
    W2c1.leN W2c1.leNDec W2c1.leNTrans W2c1.leNAnti W2c1.leNTot (by simp))

-- `Finset.map_sort` idx 8: necessary (empty relation on Unit: transitive, antisymmetric, not total; s = empty)
theorem c1_146 : ¬ indep0% Finset.map_sort 8 := fun hc =>
  W2c1.fr_nt (@hc Unit Unit (Function.Embedding.refl Unit) ∅ W2c1.fr W2c1.frDec W2c1.frTrans W2c1.frAnti
    W2c1.tr W2c1.trDec W2c1.trTrans W2c1.trAnti W2c1.trTot (by simp))

-- `Finset.map_sort` idx 11: necessary (target rock-paper-scissors on Fin 3, source full relation on Unit, s = empty)
theorem c1_147 : ¬ indep0% Finset.map_sort 11 := fun hc =>
  W2c1.rps_nt (@hc Unit (Fin 3) W2c1.u0 ∅ W2c1.tr W2c1.trDec W2c1.trTrans W2c1.trAnti W2c1.trTot
    W2c1.rps W2c1.rpsDec W2c1.rpsAnti W2c1.rpsTot (by simp))

-- `Finset.map_sort` idx 12: necessary (target full relation on Bool (not antisymmetric), s = empty)
theorem c1_148 : ¬ indep0% Finset.map_sort 12 := fun hc =>
  W2c1.trB_na (@hc Unit Bool W2c1.uB ∅ W2c1.tr W2c1.trDec W2c1.trTrans W2c1.trAnti W2c1.trTot
    W2c1.trB W2c1.trBDec W2c1.trBTrans W2c1.trBTot (by simp))

-- `Finset.map_sort` idx 13: necessary (target empty relation on Unit (not total), s = empty)
theorem c1_149 : ¬ indep0% Finset.map_sort 13 := fun hc =>
  W2c1.fr_nt (@hc Unit Unit (Function.Embedding.refl Unit) ∅ W2c1.tr W2c1.trDec W2c1.trTrans W2c1.trAnti
    W2c1.trTot W2c1.fr W2c1.frDec W2c1.frTrans W2c1.frAnti (by simp))

-- `Finset.map_sort` idx 14: necessary (Bool, f = id, r = (<=), r' = (>=), s = univ: [false, true] vs [true, false])
theorem c1_150 : ¬ drop0% Finset.map_sort 14 := by
  intro hc
  have := hc (Function.Embedding.refl Bool) Finset.univ (fun a b : Bool => a ≤ b) W2c1.geB
  rw [Finset.map_refl, W2c1.s_ft, W2c1.s_tf] at this
  simp at this

-- `StrictMonoOn.map_finsetSort` idx 6: necessary (Bool, f = not, s = univ)
theorem c1_151 : ¬ drop0% StrictMonoOn.map_finsetSort 6 := by
  intro hc
  have := hc W2c1.bnotE Finset.univ
  rw [show Finset.map W2c1.bnotE Finset.univ = Finset.univ by decide, W2c1.s_ft] at this
  simp [W2c1.bnotE] at this

-- `Finset.sort_perm_toList` idx 4: necessary (rock-paper-scissors on Fin 3: total, antisymmetric, not transitive)
theorem c1_152 : ¬ indep0% Finset.sort_perm_toList 4 := fun hc => W2c1.rps_nt (hc (α := Fin 3) ∅ W2c1.rps)

-- `List.toFinset_sort` idx 3: necessary (rock-paper-scissors on Fin 3, l = [])
theorem c1_153 : ¬ indep0% List.toFinset_sort 3 := fun hc => W2c1.rps_nt (hc (α := Fin 3) W2c1.rps (l := []) List.nodup_nil)

-- `List.toFinset_sort` idx 8: necessary (Bool, r = (<=), l = [false, false])
theorem c1_154 : ¬ drop0% List.toFinset_sort 8 := by
  intro hc
  have := hc (fun a b : Bool => a ≤ b) (l := [false, false])
  rw [show [false, false].toFinset = {false} by decide, Finset.sort_singleton] at this
  simp at this

-- `Finset.sort_mk` idx 4: necessary (rock-paper-scissors on Fin 3, m = 0)
theorem c1_155 : ¬ indep0% Finset.sort_mk 4 := fun hc => W2c1.rps_nt (hc (m := (0 : Multiset (Fin 3))) W2c1.rps Multiset.nodup_zero)

-- `Finset.mem_sort` idx 4: necessary (rock-paper-scissors on Fin 3, s = empty)
theorem c1_156 : ¬ indep0% Finset.mem_sort 4 := fun hc => W2c1.rps_nt (hc (s := (∅ : Finset (Fin 3))) W2c1.rps (a := 0))

-- `Finset.length_sort` idx 4: necessary (rock-paper-scissors on Fin 3, s = empty)
theorem c1_157 : ¬ indep0% Finset.length_sort 4 := fun hc => W2c1.rps_nt (hc (s := (∅ : Finset (Fin 3))) W2c1.rps)

-- `Finset.sort_cons` idx 4: necessary (rock-paper-scissors on Fin 3, s = empty, a = 0)
theorem c1_158 : ¬ indep0% Finset.sort_cons 4 := fun hc =>
  W2c1.rps_nt (hc (s := (∅ : Finset (Fin 3))) W2c1.rps (a := 0) (by simp) (by simp))

-- `Finset.sort_cons` idx 8: necessary (Bool, r = (<=), s = {false}, a = true)
theorem c1_159 : ¬ drop0% Finset.sort_cons 8 := by
  intro hc
  have := hc (s := {false}) (fun a b : Bool => a ≤ b) (a := true) (by decide)
  rw [show Finset.cons true {false} (by decide) = insert false {true} by decide,
    Finset.sort_insert (s := {true}) (a := false) (fun a b : Bool => a ≤ b) (by decide) (by decide),
    Finset.sort_singleton, Finset.sort_singleton] at this
  simp at this

-- `Finset.sort_insert` idx 4: necessary (rock-paper-scissors on Fin 3, s = empty, a = 0)
theorem c1_160 : ¬ indep0% Finset.sort_insert 4 := fun hc =>
  W2c1.rps_nt (hc (s := (∅ : Finset (Fin 3))) W2c1.rps (a := 0) (by simp) (by simp))

-- `Finset.sort_insert` idx 9: necessary (Bool, r = (<=), s = {false}, a = true)
theorem c1_161 : ¬ drop0% Finset.sort_insert 9 := by
  intro hc
  have := hc (s := {false}) (fun a b : Bool => a ≤ b) (a := true) (by decide)
  rw [show (insert true {false} : Finset Bool) = insert false {true} by decide,
    Finset.sort_insert (s := {true}) (a := false) (fun a b : Bool => a ≤ b) (by decide) (by decide),
    Finset.sort_singleton, Finset.sort_singleton] at this
  simp at this

-- `Finset.sort_insert` idx 10: necessary (Bool, r = (<=), s = {false}, a = false)
theorem c1_162 : ¬ drop0% Finset.sort_insert 10 := by
  intro hc
  have := hc (s := {false}) (fun a b : Bool => a ≤ b) (a := false) (by decide)
  rw [show (insert false {false} : Finset Bool) = {false} by decide, Finset.sort_singleton] at this
  simp at this

-- `Finset.coe_orderIsoOfFin_apply` idx 4: necessary (s = empty, k = 1)
theorem c1_163 : ¬ indep0% Finset.coe_orderIsoOfFin_apply 4 := fun hc => absurd (hc (α := ℕ) ∅ (k := 1) 0) (by simp)

-- `Finset.orderIsoOfFin_symm_apply` idx 4: necessary (s = {0}, k = 0)
theorem c1_164 : ¬ indep0% Finset.orderIsoOfFin_symm_apply 4 := fun hc => absurd (hc (α := ℕ) {0} (k := 0) ⟨0, by simp⟩) (by simp)

-- `Finset.orderEmbOfFin_apply` idx 4: necessary (s = empty, k = 1)
theorem c1_165 : ¬ indep0% Finset.orderEmbOfFin_apply 4 := fun hc => absurd (hc (α := ℕ) ∅ (k := 1) 0) (by simp)

-- `Finset.orderEmbOfFin_mem` idx 4: necessary (s = empty, k = 1)
theorem c1_166 : ¬ indep0% Finset.orderEmbOfFin_mem 4 := fun hc => absurd (hc (α := ℕ) ∅ (k := 1) 0) (by simp)

-- `Finset.orderEmbOfFin_unique` idx 4: necessary (s = {0}, k = 0, f = Fin.elim0)
theorem c1_167 : ¬ indep0% Finset.orderEmbOfFin_unique 4 := fun hc =>
  absurd (hc (α := ℕ) (s := {0}) (k := 0) (f := Fin.elim0) (fun x => x.elim0) (fun x => x.elim0)) (by simp)

-- `Finset.orderEmbOfFin_unique` idx 6: necessary (s = {0}, k = 1, f = fun _ => 1)
theorem c1_168 : ¬ drop0% Finset.orderEmbOfFin_unique 6 := by
  intro hc
  have := congrFun (hc (α := ℕ) (s := {0}) (k := 1) (Finset.card_singleton 0) (f := fun _ => 1) (W2c1.sm1 _)) 0
  have hm := Finset.orderEmbOfFin_mem ({0} : Finset ℕ) (Finset.card_singleton 0) 0
  rw [← this] at hm
  simp at hm

-- `Finset.orderEmbOfFin_unique` idx 7: necessary (s = {0, 1}, k = 2, f = fun _ => 0)
theorem c1_169 : ¬ drop0% Finset.orderEmbOfFin_unique 7 := by
  intro hc
  have := hc (α := ℕ) (s := {0, 1}) (k := 2) (by decide) (f := fun _ => 0) (fun _ => by simp)
  have h01 := (congrFun this 0).symm.trans (congrFun this 1)
  exact absurd ((Finset.orderEmbOfFin _ _).injective h01) (by decide)

-- `Finset.orderEmbOfFin_unique'` idx 4: necessary (s = {0}, k = 0, f = Fin.valOrderEmb 0)
theorem c1_170 : ¬ indep0% Finset.orderEmbOfFin_unique' 4 := fun hc =>
  absurd (hc (α := ℕ) (s := {0}) (k := 0) (f := Fin.valOrderEmb 0) (fun x => x.elim0)) (by simp)

-- `Finset.orderEmbOfFin_unique'` idx 6: necessary (s = {0}, k = 1, f 0 = 1)
theorem c1_171 : ¬ drop0% Finset.orderEmbOfFin_unique' 6 := by
  intro hc
  have := hc (α := ℕ) (s := {0}) (k := 1) (Finset.card_singleton 0)
    (f := OrderEmbedding.ofStrictMono (fun _ => 1) (W2c1.sm1 _))
  have h0 := DFunLike.congr_fun this 0
  have hm := Finset.orderEmbOfFin_mem ({0} : Finset ℕ) (Finset.card_singleton 0) 0
  rw [← h0] at hm
  simp at hm

-- `Finset.orderEmbOfFin_eq_orderEmbOfFin_iff` idx 7: necessary (s = {0}, k = 2, l = 1)
theorem c1_172 : ¬ indep0% Finset.orderEmbOfFin_eq_orderEmbOfFin_iff 7 := fun hc =>
  absurd (hc (α := ℕ) (k := 2) (l := 1) (s := {0}) (i := 0) (j := 0) (h' := Finset.card_singleton 0)) (by simp)

-- `Finset.orderEmbOfFin_eq_orderEmbOfFin_iff` idx 8: necessary (s = {0}, k = 1, l = 2)
theorem c1_173 : ¬ indep0% Finset.orderEmbOfFin_eq_orderEmbOfFin_iff 8 := fun hc =>
  absurd (hc (α := ℕ) (k := 1) (l := 2) (s := {0}) (i := 0) (j := 0) (h := Finset.card_singleton 0)) (by simp)

-- `Finset.orderEmbOfCardLe_mem` idx 4: necessary (s = empty, k = 1)
theorem c1_174 : ¬ indep0% Finset.orderEmbOfCardLe_mem 4 := fun hc => absurd (hc (α := ℕ) ∅ (k := 1) 0) (by simp)

-- `nonempty_orderEmbedding_of_finite_infinite` idx 2: necessary (alpha = Int, beta = Nat: no order embedding of Int into Nat)
theorem c1_175 : ¬ drop0% nonempty_orderEmbedding_of_finite_infinite 2 := by
  intro hc
  obtain ⟨f⟩ := hc ℤ ℕ
  exact W2c1.notWF (r := (· < ·)) (fun n : ℕ => -(n:ℤ)) (fun n => by push_cast; omega)
    (@wellFounded_lt ℤ _ f.wellFoundedLT)

-- `nonempty_orderEmbedding_of_finite_infinite` idx 5: necessary (alpha = Bool, beta = Unit)
theorem c1_176 : ¬ drop0% nonempty_orderEmbedding_of_finite_infinite 5 := by
  intro hc
  obtain ⟨f⟩ := hc Bool Unit
  exact absurd (f.injective (Subsingleton.elim (f true) (f false))) (by decide)

-- `Finset.disjSum_mono` idx 6: necessary (s1 = {0}, s2 = t1 = t2 = empty)
theorem c1_177 : ¬ drop0% Finset.disjSum_mono 6 := by
  intro hc
  have := @hc ℕ ℕ {0} ∅ ∅ ∅ subset_rfl (Sum.inl 0) (by simp)
  simp at this

-- `Finset.disjSum_mono` idx 7: necessary (t1 = {0}, t2 = s1 = s2 = empty)
theorem c1_178 : ¬ drop0% Finset.disjSum_mono 7 := by
  intro hc
  have := @hc ℕ ℕ ∅ ∅ {0} ∅ subset_rfl (Sum.inr 0) (by simp)
  simp at this

-- `Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset` idx 7: necessary (s1 = empty, s2 = {0}, t1 = {0}, t2 = empty)
theorem c1_179 : ¬ drop0% Finset.disjSum_ssubset_disjSum_of_ssubset_of_subset 7 := by
  intro hc
  have h := (@hc ℕ ℕ ∅ {0} {0} ∅ (by simp)).1
  have := @h (Sum.inr 0) (by simp)
  simp at this

-- `Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset` idx 6: necessary (s1 = {0}, s2 = empty, t1 = empty, t2 = {0})
theorem c1_180 : ¬ drop0% Finset.disjSum_ssubset_disjSum_of_subset_of_ssubset 6 := by
  intro hc
  have h := (@hc ℕ ℕ {0} ∅ ∅ {0} (by simp)).1
  have := @h (Sum.inl 0) (by simp)
  simp at this

-- `Finset.toLeft_subset_toLeft` idx 4: necessary (u = {inl 0}, v = empty)
theorem c1_181 : ¬ drop0% Finset.toLeft_subset_toLeft 4 := by
  intro hc
  have := @hc ℕ ℕ {Sum.inl 0} ∅ 0 (by simp)
  simp at this

-- `Finset.toRight_subset_toRight` idx 4: necessary (u = {inr 0}, v = empty)
theorem c1_182 : ¬ drop0% Finset.toRight_subset_toRight 4 := by
  intro hc
  have := @hc ℕ ℕ {Sum.inr 0} ∅ 0 (by simp)
  simp at this

-- `Finset.toLeft_cons_inl` idx 4: necessary (u = {inl 0}, a = 0)
theorem c1_183 : ¬ indep0% Finset.toLeft_cons_inl 4 := fun hc => @hc ℕ ℕ {Sum.inl 0} 0 (by simp)

-- `Finset.toLeft_cons_inr` idx 4: necessary (u = {inr 0}, b = 0)
theorem c1_184 : ¬ indep0% Finset.toLeft_cons_inr 4 := fun hc => @hc ℕ ℕ {Sum.inr 0} 0 (by simp)

-- `Finset.toRight_cons_inl` idx 4: necessary (u = {inl 0}, a = 0)
theorem c1_185 : ¬ indep0% Finset.toRight_cons_inl 4 := fun hc => @hc ℕ ℕ {Sum.inl 0} 0 (by simp)

-- `Finset.toRight_cons_inr` idx 4: necessary (u = {inr 0}, b = 0)
theorem c1_186 : ¬ indep0% Finset.toRight_cons_inr 4 := fun hc => @hc ℕ ℕ {Sum.inr 0} 0 (by simp)

