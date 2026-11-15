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

namespace W2c2

/-- A family with two distinct indices sharing an element is not pairwise disjoint. -/
theorem npd {α β : Type*} {s : Set α} {f : α → Finset β} {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (x : β) (hxa : x ∈ f a) (hxb : x ∈ f b) : ¬ s.PairwiseDisjoint f :=
  fun h => Finset.disjoint_left.1 (h ha hb hab) hxa hxb

end W2c2
open W2c2

namespace W2c2

/-- A family on the pair 0, 1 is pairwise disjoint if its two members are disjoint. -/
theorem pd2 {β : Type*} (f : ℕ → Finset β) (h : Disjoint (f 0) (f 1)) :
    (↑({0, 1} : Finset ℕ) : Set ℕ).PairwiseDisjoint f := by
  rw [Finset.coe_pair]; exact Set.pairwise_pair.2 fun _ => ⟨h, h.symm⟩

/-- A relation holding both ways between 0 and 1 holds pairwise on the pair. -/
theorem pp2 (r : ℕ → ℕ → Prop) (h01 : r 0 1) (h10 : r 1 0) :
    (↑({0, 1} : Finset ℕ) : Set ℕ).Pairwise r := by
  rw [Finset.coe_pair]; exact Set.pairwise_pair.2 fun _ => ⟨h01, h10⟩

end W2c2
open W2c2

namespace W2c2

/-- Squaring on Nat as a zero-preserving map is not additive. -/
def sq0 : ZeroHom ℕ ℕ := ⟨fun n => n * n, rfl⟩

theorem not_amhc : ¬ AddMonoidHomClass (ZeroHom ℕ ℕ) ℕ ℕ := by
  intro hc
  have := map_add sq0 1 1
  simp [sq0] at this

/-- The Nat-valued finsupp with value 1 at 0 and at 1. -/
noncomputable abbrev v11 : ℕ →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1

theorem v11_supp : v11.support ⊆ {0, 1} := by
  intro x hx; rw [Finsupp.mem_support_iff] at hx
  simp only [v11, Finsupp.add_apply, Finsupp.single_apply] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton]; split_ifs at hx <;> omega

theorem md_v11 : Finsupp.mapDomain (fun _ : ℕ => (0 : ℕ)) v11 = Finsupp.single 0 2 := by
  simp [v11, Finsupp.mapDomain_add, Finsupp.mapDomain_single, ← Finsupp.single_add]

/-- The Int-valued finsupp with value 1 at 0 and -1 at 1. -/
noncomputable abbrev vpm : ℕ →₀ ℤ := Finsupp.single 0 1 + Finsupp.single 1 (-1)

theorem md_vpm : Finsupp.mapDomain (fun _ : ℕ => (0 : ℕ)) vpm = 0 := by
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, ← Finsupp.single_add]
  simp

theorem vpm0 : (0 : ℕ) ∈ vpm.support := by simp [vpm]

theorem vpm_ne : vpm ≠ 0 := fun h => by simpa [h] using vpm0

open Classical in
/-- Splitting off the summand at i from a finsupp sum. -/
theorem sum_split {ι α β : Type*} [Zero α] [AddCommMonoid β] (X : ι →₀ α) (i : ι) (g : ι → α → β) :
    X.sum g = (X.erase i).sum g + (if X i = 0 then 0 else g i (X i)) := by
  by_cases hX : X i = 0
  · rw [Finsupp.erase_of_notMem_support (by simpa using hX)]; simp [hX]
  · rw [← Finsupp.add_sum_erase X i g (by simpa using hX)]; simp [hX, add_comm]

open Classical in
/-- sum_update_add holds whenever g i 0 is absorbed by every g i x. -/
theorem sum_update_add_of {ι α β : Type*} [AddZeroClass α] [AddCommMonoid β] (f : ι →₀ α) (i : ι)
    (a : α) (g : ι → α → β) (habs : ∀ x, g i x + g i 0 = g i x) :
    (f.update i a).sum g + g i (f i) = f.sum g + g i a := by
  rw [sum_split (f.update i a) i, sum_split f i, Finsupp.erase_update_eq_erase, Finsupp.update_apply,
    if_pos rfl]
  have key : ∀ x y : α, (if x = 0 then 0 else g i x) + g i y = (if y = 0 then 0 else g i y) + g i x := by
    intro x y
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    · subst hx; subst hy; rfl
    · subst hx; simp [hy, habs]
    · subst hy; simp [hx, habs]
    · simp [hx, hy, add_comm]
  rw [add_assoc, add_assoc, key]

end W2c2
open W2c2

universe u_1 u_2 u_3 u_4 u_5

-- `Finset.sup_mem_sups` idx 8: necessary (Bool, s = {true}, t = empty, a = true, b = false)
theorem w22_1 : ¬ drop0% Finset.sup_mem_sups 8 := fun h =>
  absurd (@h Bool _ _ {true} ∅ true false (by simp)) (by decide)

-- `Finset.sups_subset` idx 7: necessary (Bool, s1 = {true}, s2 = empty, t1 = t2 = {true})
theorem w22_2 : ¬ drop0% Finset.sups_subset 7 := fun h =>
  absurd (@h Bool _ _ {true} ∅ {true} {true} (by simp)) (by decide)

-- `Finset.sups_subset` idx 8: necessary (Bool, s1 = s2 = {true}, t1 = {true}, t2 = empty)
theorem w22_3 : ¬ drop0% Finset.sups_subset 8 := fun h =>
  absurd (@h Bool _ _ {true} {true} {true} ∅ (by simp)) (by decide)

-- `Finset.Nonempty.sups` idx 5: necessary (s = empty)
theorem w22_4 : ¬ drop0% Finset.Nonempty.sups 5 := fun h =>
  absurd (@h Bool _ _ ∅ {true} (by simp)) (by decide)

-- `Finset.Nonempty.sups` idx 6: necessary (t = empty)
theorem w22_5 : ¬ drop0% Finset.Nonempty.sups 6 := fun h =>
  absurd (@h Bool _ _ {true} ∅ (by simp)) (by decide)

-- `Finset.subset_sups` idx 6: necessary (u = {true}, s = t = empty)
theorem w22_6 : ¬ drop0% Finset.subset_sups 6 := fun h => by
  obtain ⟨s', t', hs, ht, hu⟩ := @h Bool _ _ {true} ∅ ∅
  simp at hs; subst hs; simp at hu

-- `Finset.image_sups` idx 8: necessary (negation on Bool is no sup hom)
theorem w22_7 : ¬ drop0% Finset.image_sups 8 := fun h =>
  absurd (@h (Bool ≃ Bool) Bool Bool _ _ _ _ _ ⟨not, not, Bool.not_not, Bool.not_not⟩ {true} {false})
    (by decide)

-- `Finset.map_sups` idx 8: necessary (negation on Bool is no sup hom)
theorem w22_8 : ¬ drop0% Finset.map_sups 8 := fun h => by
  have := @h (Bool ≃ Bool) Bool Bool _ _ _ _ _ ⟨not, not, Bool.not_not, Bool.not_not⟩
    (Equiv.injective _) {true} {false}
  revert this; decide

-- `Finset.map_sups` idx 10: necessary (constant sup hom to true is not injective)
theorem w22_9 : ¬ indep0% Finset.map_sups 10 := fun h => by
  have := @h (SupHom Bool Bool) Bool Bool _ _ _ _ _ _ ⟨fun _ => true, fun _ _ => rfl⟩
  exact absurd (@this ∅ ∅ true false rfl) (by decide)

-- `Finset.inf_mem_infs` idx 8: necessary (Bool, s = {true}, t = empty)
theorem w22_10 : ¬ drop0% Finset.inf_mem_infs 8 := fun h =>
  absurd (@h Bool _ _ {true} ∅ true false (by simp)) (by decide)

-- `Finset.infs_subset` idx 7: necessary (s1 = {true}, s2 = empty)
theorem w22_11 : ¬ drop0% Finset.infs_subset 7 := fun h =>
  absurd (@h Bool _ _ {true} ∅ {true} {true} (by simp)) (by decide)

-- `Finset.infs_subset` idx 8: necessary (t1 = {true}, t2 = empty)
theorem w22_12 : ¬ drop0% Finset.infs_subset 8 := fun h =>
  absurd (@h Bool _ _ {true} {true} {true} ∅ (by simp)) (by decide)

-- `Finset.Nonempty.infs` idx 5: necessary (s = empty)
theorem w22_13 : ¬ drop0% Finset.Nonempty.infs 5 := fun h =>
  absurd (@h Bool _ _ ∅ {true} (by simp)) (by decide)

-- `Finset.Nonempty.infs` idx 6: necessary (t = empty)
theorem w22_14 : ¬ drop0% Finset.Nonempty.infs 6 := fun h =>
  absurd (@h Bool _ _ {true} ∅ (by simp)) (by decide)

-- `Finset.subset_infs` idx 6: necessary (u = {true}, s = t = empty)
theorem w22_15 : ¬ drop0% Finset.subset_infs 6 := fun h => by
  obtain ⟨s', t', hs, ht, hu⟩ := @h Bool _ _ {true} ∅ ∅
  simp at hs; subst hs; simp at hu

-- `Finset.image_infs` idx 8: necessary (negation on Bool is no inf hom)
theorem w22_16 : ¬ drop0% Finset.image_infs 8 := fun h =>
  absurd (@h (Bool ≃ Bool) Bool Bool _ _ _ _ _ ⟨not, not, Bool.not_not, Bool.not_not⟩ {true} {false})
    (by decide)

-- `Finset.map_infs` idx 8: necessary (negation on Bool is no inf hom)
theorem w22_17 : ¬ drop0% Finset.map_infs 8 := fun h => by
  have := @h (Bool ≃ Bool) Bool Bool _ _ _ _ _ ⟨not, not, Bool.not_not, Bool.not_not⟩
    (Equiv.injective _) {true} {false}
  revert this; decide

-- `Finset.map_infs` idx 10: necessary (constant inf hom to true is not injective)
theorem w22_18 : ¬ indep0% Finset.map_infs 10 := fun h => by
  have := @h (InfHom Bool Bool) Bool Bool _ _ _ _ _ _ ⟨fun _ => true, fun _ _ => rfl⟩
  exact absurd (@this ∅ ∅ true false rfl) (by decide)

-- `Finset.union_mem_sups` idx 6: necessary (A = empty, B = {empty})
theorem w22_19 : ¬ drop0% Finset.union_mem_sups 6 := fun h =>
  absurd (@h Bool _ ∅ {∅} ∅ ∅ (by simp)) (by decide)

-- `Finset.union_mem_sups` idx 7: necessary (A = {empty}, B = empty)
theorem w22_20 : ¬ drop0% Finset.union_mem_sups 7 := fun h =>
  absurd (@h Bool _ {∅} ∅ ∅ ∅ (by simp)) (by decide)

-- `Finset.inter_mem_infs` idx 6: necessary (A = empty, B = {empty})
theorem w22_21 : ¬ drop0% Finset.inter_mem_infs 6 := fun h =>
  absurd (@h Bool _ ∅ {∅} ∅ ∅ (by simp)) (by decide)

-- `Finset.inter_mem_infs` idx 7: necessary (A = {empty}, B = empty)
theorem w22_22 : ¬ drop0% Finset.inter_mem_infs 7 := fun h =>
  absurd (@h Bool _ {∅} ∅ ∅ ∅ (by simp)) (by decide)

-- `Finset.disjSups_subset` idx 9: necessary (in Finset Nat: s1 = {empty}, s2 = empty, t = {empty})
theorem w22_23 : ¬ drop0% Finset.disjSups_subset 9 := fun h =>
  absurd (@h (Finset ℕ) _ _ _ _ {∅} ∅ {∅} {∅} (by simp)) (by decide)

-- `Finset.disjSups_subset` idx 10: necessary (s = {empty}, t1 = {empty}, t2 = empty)
theorem w22_24 : ¬ drop0% Finset.disjSups_subset 10 := fun h =>
  absurd (@h (Finset ℕ) _ _ _ _ {∅} {∅} {∅} ∅ (by simp)) (by decide)

-- `Finset.disjSups_subset_left` idx 8: necessary (s = {empty}, t1 = {empty}, t2 = empty)
theorem w22_25 : ¬ drop0% Finset.disjSups_subset_left 8 := fun h =>
  absurd (@h (Finset ℕ) _ _ _ _ {∅} {∅} ∅) (by decide)

-- `Finset.disjSups_subset_right` idx 8: necessary (s1 = {empty}, s2 = empty, t = {empty})
theorem w22_26 : ¬ drop0% Finset.disjSups_subset_right 8 := fun h =>
  absurd (@h (Finset ℕ) _ _ _ _ {∅} ∅ {∅}) (by decide)

-- `Finset.Nonempty.of_disjSups_left` idx 7: necessary (s = empty)
theorem w22_27 : ¬ drop0% Finset.Nonempty.of_disjSups_left 7 := fun h =>
  absurd (@h (Finset ℕ) _ _ _ _ ∅ ∅) (by decide)

-- `Finset.Nonempty.of_disjSups_right` idx 7: necessary (t = empty)
theorem w22_28 : ¬ drop0% Finset.Nonempty.of_disjSups_right 7 := fun h =>
  absurd (@h (Finset ℕ) _ _ _ _ ∅ ∅) (by decide)

-- `Finset.sdiff_mem_diffs` idx 7: necessary (Bool, s = empty, t = {false})
theorem w22_29 : ¬ drop0% Finset.sdiff_mem_diffs 7 := fun h =>
  absurd (@h Bool _ _ ∅ {false} true false (by simp)) (by decide)

-- `Finset.sdiff_mem_diffs` idx 8: necessary (Bool, s = {true}, t = empty)
theorem w22_30 : ¬ drop0% Finset.sdiff_mem_diffs 8 := fun h =>
  absurd (@h Bool _ _ {true} ∅ true false (by simp)) (by decide)

-- `Finset.diffs_subset` idx 7: necessary (s1 = {true}, s2 = empty, t = {false})
theorem w22_31 : ¬ drop0% Finset.diffs_subset 7 := fun h =>
  absurd (@h Bool _ _ {true} ∅ {false} {false} (by simp)) (by decide)

-- `Finset.diffs_subset` idx 8: necessary (s = {true}, t1 = {false}, t2 = empty)
theorem w22_32 : ¬ drop0% Finset.diffs_subset 8 := fun h =>
  absurd (@h Bool _ _ {true} {true} {false} ∅ (by simp)) (by decide)

-- `Finset.Nonempty.diffs` idx 6: necessary (t = empty)
theorem w22_33 : ¬ drop0% Finset.Nonempty.diffs 6 := fun h =>
  absurd (@h Bool _ _ {true} ∅ (by simp)) (by decide)

-- `Finset.subset_diffs` idx 6: necessary (u = {true}, s = t = empty)
theorem w22_34 : ¬ drop0% Finset.subset_diffs 6 := fun h => by
  obtain ⟨s', t', hs, ht, hu⟩ := @h Bool _ _ {true} ∅ ∅
  simp at hs; subst hs; simp at hu

-- `Set.Sized.compls` idx 5: necessary (Bool, A = {empty, univ}, n = 0)
theorem w22_35 : ¬ drop0% Set.Sized.compls 5 := fun h => by
  have := @h Bool _ _ {∅, Finset.univ} 0 (∅ : Finset Bool)
    (by rw [Finset.mem_coe, Finset.mem_compls]; simp)
  revert this; decide

-- `Finset.sized_compls` idx 5: necessary (Bool, A = {empty}, n = 3 > card)
theorem w22_36 : ¬ drop0% Finset.sized_compls 5 := fun h => by
  have hs := (@h Bool _ _ {∅} 3).2 (by intro x hx; simp at hx; simp [hx])
  have := @hs (Finset.univ : Finset Bool) (by rw [Finset.mem_coe, Finset.mem_compls]; decide)
  revert this; decide

-- `Finset.sym_fill_mem` idx 7: necessary (s = empty, n = 1, i = 0, m = {1}, a = 0)
theorem w22_37 : ¬ drop0% Finset.sym_fill_mem 7 := fun h => by
  have := @h ℕ ∅ _ 1 0 0 (Sym.replicate _ 1)
  rw [Finset.mem_sym_iff] at this
  have h1 := this 1 (by rw [Sym.mem_fill_iff]; simp [Sym.mem_replicate])
  simp at h1

-- `Finset.sym_filterNe_mem` idx 6: necessary (s = empty, n = 1, m = {1}, a = 0)
theorem w22_38 : ¬ drop0% Finset.sym_filterNe_mem 6 := fun h => by
  have := @h ℕ ∅ _ 1 (Sym.mk {1} rfl) 0
  rw [Finset.mem_sym_iff] at this
  have h1 := this 1 (by decide)
  simp at h1

-- `Finset.symInsertEquiv_apply_fst` idx 5: necessary (s = {0}, a = 0, n = 0)
theorem w22_39 : ¬ indep0% Finset.symInsertEquiv_apply_fst 5 := fun h =>
  @h ℕ {0} 0 _ 0 ⟨Sym.nil, by simp; rfl⟩ (by simp)

-- `Finset.symInsertEquiv_apply_snd_coe` idx 5: necessary (s = {0}, a = 0, n = 0)
theorem w22_40 : ¬ indep0% Finset.symInsertEquiv_apply_snd_coe 5 := fun h =>
  @h ℕ {0} 0 _ 0 ⟨Sym.nil, by simp; rfl⟩ (by simp)

-- `Finset.val_sum_eq_sum_count_nsmul` idx 6: necessary (s = empty, k = {1})
theorem w22_41 : ¬ drop0% Finset.val_sum_eq_sum_count_nsmul 6 := fun h => by
  have := @h ℕ _ _ 1 (Sym.mk {1} rfl) ∅
  simp at this

-- `Finset.val_prod_eq_prod_count_pow` idx 6: necessary (s = empty, k = {2})
theorem w22_42 : ¬ drop0% Finset.val_prod_eq_prod_count_pow 6 := fun h => by
  have := @h ℕ _ _ 1 (Sym.mk {2} rfl) ∅
  simp at this

-- `Finset.image_symmDiff` idx 7: necessary (f constant, s = {0}, t = {1})
theorem w22_43 : ¬ drop0% Finset.image_symmDiff 7 := fun h =>
  absurd (@h ℕ ℕ _ _ (fun _ => 0) {0} {1}) (by decide)

-- `Finset.disjiUnion_val` idx 4: necessary (s = {0, 1}, t constant {0})
theorem w22_44 : ¬ indep0% Finset.disjiUnion_val 4 := fun h => by
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) (@h ℕ ℕ {0, 1} (fun _ => {0}))

-- `Finset.mem_disjiUnion` idx 5: necessary (s = {0, 1}, t constant {0})
theorem w22_45 : ¬ indep0% Finset.mem_disjiUnion 5 := fun h => by
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) (@h ℕ ℕ {0, 1} (fun _ => {0}) 0)

-- `Finset.coe_disjiUnion` idx 4: necessary (s = {0, 1}, t constant {0})
theorem w22_46 : ¬ indep0% Finset.coe_disjiUnion 4 := fun h => by
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) (@h ℕ ℕ {0, 1} (fun _ => {0}))

-- `Finset.disjiUnion_cons` idx 6: necessary (cons 0 {1}, f constant {0})
theorem w22_47 : ¬ indep0% Finset.disjiUnion_cons 6 := fun h => by
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) (@h ℕ ℕ 0 {1} (by simp) (fun _ => {0}))

-- `Finset.disjiUnion_disjiUnion` idx 6: necessary (s = {0, 1}, f constant {0})
theorem w22_48 : ¬ indep0% Finset.disjiUnion_disjiUnion 6 := fun h => by
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) (@h ℕ ℕ ℕ {0, 1} (fun _ => {0}) (fun _ => {0}))

-- `Finset.disjiUnion_disjiUnion` idx 7: necessary (s = {0}, f 0 = {0, 1}, g constant {0})
theorem w22_49 : ¬ indep0% Finset.disjiUnion_disjiUnion 7 := fun h => by
  have := @h ℕ ℕ ℕ {0} (fun _ => {0, 1}) (fun _ => {0}) (by simp)
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) this

-- `Finset.sUnion_disjiUnion` idx 4: necessary (I = {0, 1}, f constant {univ})
theorem w22_50 : ¬ indep0% Finset.sUnion_disjiUnion 4 := fun h => by
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) Set.univ (by simp) (by simp) (@h ℕ ℕ (fun _ => {Set.univ}) {0, 1})

-- `Finset.disjiUnion_filter_eq_of_maps_to` idx 6: necessary (s = {0}, t = empty, f = id)
theorem w22_51 : ¬ drop0% Finset.disjiUnion_filter_eq_of_maps_to 6 := fun h => by
  have := @h ℕ ℕ _ {0} ∅ id
  simp at this

-- `Finset.map_disjiUnion` idx 6: necessary (s = {0, 1}, f = id, t constant {0})
theorem w22_52 : ¬ indep0% Finset.map_disjiUnion 6 := fun h => by
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) (@h ℕ ℕ ℕ (Function.Embedding.refl ℕ) {0, 1} (fun _ => {0}))

-- `Finset.disjiUnion_map` idx 6: necessary (s = {0, 1}, t constant {0})
theorem w22_53 : ¬ indep0% Finset.disjiUnion_map 6 := fun h => by
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) (@h ℕ ℕ ℕ {0, 1} (fun _ => {0}) (Function.Embedding.refl ℕ))

-- `Finset.fold_disjiUnion` idx 11: necessary (s = {0, 1}, t constant {0})
theorem w22_54 : ¬ indep0% Finset.fold_disjiUnion 11 := fun h => by
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) (@h ℕ ℕ id (· + ·) _ _ ℕ {0, 1} (fun _ => {0}) (fun _ => 0) 0)

-- `Finset.pairwiseDisjoint_filter` idx 4: necessary (s = {0, 1}, f constant {0}, p = True)
theorem w22_55 : ¬ drop0% Finset.pairwiseDisjoint_filter 4 := fun h => by
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp)
    (@h ℕ ℕ {0, 1} (fun _ => {0}) (fun _ => True) _)

-- `Finset.filter_disjiUnion` idx 4: necessary (s = {0, 1}, f constant {0})
theorem w22_56 : ¬ indep0% Finset.filter_disjiUnion 4 := fun h => by
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) (@h ℕ ℕ {0, 1} (fun _ => {0}) (fun _ => True) _)

-- `Finset.disjoint_disjiUnion_left` idx 4: necessary (s = {0, 1}, f constant {0})
theorem w22_57 : ¬ indep0% Finset.disjoint_disjiUnion_left 4 := fun h => by
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) (@h ℕ ℕ {0, 1} (fun _ => {0}) ∅)

-- `Finset.disjoint_disjiUnion_right` idx 5: necessary (t = {0, 1}, f constant {0})
theorem w22_58 : ¬ indep0% Finset.disjoint_disjiUnion_right 5 := fun h => by
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) (@h ℕ ℕ ∅ {0, 1} (fun _ => {0}))

-- `Finset.pairwiseDisjoint_disjUnion` idx 5: necessary (s = empty, f = g constant {0})
theorem w22_59 : ¬ indep0% Finset.pairwiseDisjoint_disjUnion 5 := fun h => by
  have := @h ℕ ℕ ∅ (fun _ => {0}) (fun _ => {0}) (by simp) (by simp) (by simp) 0
  simp at this

-- `Finset.pairwiseDisjoint_disjUnion` idx 6: necessary (s = {0, 1}, f = ({0}, {1}), g = ({2}, {0}))
theorem w22_60 : ¬ drop0% Finset.pairwiseDisjoint_disjUnion 6 := fun h => by
  have := @h ℕ ℕ {0, 1} (fun a => if a = 0 then {0} else {1}) (fun a => if a = 0 then {2} else {0})
    (fun a => by split_ifs <;> decide) (pd2 _ (by decide)) (pd2 _ (by decide))
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) this

-- `Finset.pairwiseDisjoint_disjUnion` idx 7: necessary (s = {0, 1}, f constant {0}, g constant empty)
theorem w22_61 : ¬ drop0% Finset.pairwiseDisjoint_disjUnion 7 := fun h => by
  have := @h ℕ ℕ {0, 1} (fun _ => {0}) (fun _ => ∅) (fun a => by simp)
    (pp2 _ (by simp) (by simp)) (pd2 _ (by simp))
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) this

-- `Finset.disjiUnion_disjUnion` idx 5: necessary (s = empty, f = g constant {0})
theorem w22_62 : ¬ indep0% Finset.disjiUnion_disjUnion 5 := fun h => by
  have := @h ℕ ℕ ∅ (fun _ => {0}) (fun _ => {0}) (by simp) (by simp) (by simp) 0
  simp at this

-- `Finset.disjiUnion_disjUnion` idx 6: necessary (s = {0, 1}, f = ({0}, empty), g = (empty, {0}))
theorem w22_63 : ¬ indep0% Finset.disjiUnion_disjUnion 6 := fun h => by
  have := @h ℕ ℕ {0, 1} (fun a => if a = 0 then {0} else ∅) (fun a => if a = 0 then ∅ else {0})
    (fun a => by split_ifs <;> simp) (pd2 _ (by simp)) (pd2 _ (by simp))
  have h2 := this (by simp : (0 : ℕ) ∈ (↑({0, 1} : Finset ℕ) : Set ℕ)) (by simp : (1 : ℕ) ∈ _) (by decide)
  simp at h2

-- `Finset.disjiUnion_disjUnion` idx 7: necessary (s = {0, 1}, f constant {0}, g constant empty)
theorem w22_64 : ¬ indep0% Finset.disjiUnion_disjUnion 7 := fun h => by
  have := @h ℕ ℕ {0, 1} (fun _ => {0}) (fun _ => ∅) (fun a => by simp)
    (pp2 _ (by simp) (by simp)) (pd2 _ (by simp))
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) this

-- `Finset.disjiUnion_disjUnion` idx 8: necessary (s = {0, 1}, f constant empty, g constant {0})
theorem w22_65 : ¬ indep0% Finset.disjiUnion_disjUnion 8 := fun h => by
  have := @h ℕ ℕ {0, 1} (fun _ => ∅) (fun _ => {0}) (fun a => by simp)
    (pp2 _ (by simp) (by simp)) (pd2 _ (by simp))
  exact npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) this

-- `Finset.biUnion_congr` idx 7: necessary (s1 = {0}, s2 = empty, t constant {0})
theorem w22_66 : ¬ drop0% Finset.biUnion_congr 7 := fun h =>
  absurd (@h ℕ ℕ {0} ∅ (fun _ => {0}) (fun _ => {0}) _ (by simp)) (by decide)

-- `Finset.biUnion_congr` idx 8: necessary (s = {0}, t1 constant {0}, t2 constant empty)
theorem w22_67 : ¬ drop0% Finset.biUnion_congr 8 := fun h =>
  absurd (@h ℕ ℕ {0} {0} (fun _ => {0}) (fun _ => ∅) _ rfl) (by decide)

-- `Finset.disjiUnion_eq_biUnion` idx 5: necessary (s = {0, 1}, f constant {0})
theorem w22_68 : ¬ indep0% Finset.disjiUnion_eq_biUnion 5 := fun h =>
  npd (a := 0) (b := 1) (by simp) (by simp) (by simp) 0 (by simp) (by simp) (@h ℕ ℕ _ {0, 1} (fun _ => {0}))

-- `Finset.biUnion_mono` idx 6: necessary (s = {0}, t1 constant {0}, t2 constant empty)
theorem w22_69 : ¬ drop0% Finset.biUnion_mono 6 := fun h =>
  absurd (@h ℕ ℕ {0} (fun _ => {0}) (fun _ => ∅) _) (by decide)

-- `Finset.biUnion_subset_biUnion_of_subset_left` idx 6: necessary (s1 = {0}, s2 = empty)
theorem w22_70 : ¬ drop0% Finset.biUnion_subset_biUnion_of_subset_left 6 := fun h =>
  absurd (@h ℕ ℕ {0} ∅ _ (fun _ => {0})) (by decide)

-- `Finset.subset_biUnion_of_mem` idx 6: necessary (s = empty, u constant {0})
theorem w22_71 : ¬ drop0% Finset.subset_biUnion_of_mem 6 := fun h =>
  absurd (@h ℕ ℕ ∅ _ (fun _ => {0}) 0) (by decide)

-- `Finset.Nonempty.biUnion` idx 6: necessary (s = {0}, t constant empty)
theorem w22_72 : ¬ drop0% Finset.Nonempty.biUnion 6 := fun h =>
  absurd (@h ℕ ℕ {0} (fun _ => ∅) _ (by simp)) (by decide)

-- `DependsOn.updateFinset` idx 6: necessary (f x = x 0, s = t = empty)
theorem w22_73 : ¬ drop0% DependsOn.updateFinset 6 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ ℕ (fun x => x 0) ∅ ∅ (fun _ => 0) (fun _ => 0) (fun _ => 1) (by simp)
  simp [Function.updateFinset] at this

-- `DependsOn.update` idx 6: necessary (f x = x 0, s = empty, i = 1)
theorem w22_74 : ¬ drop0% DependsOn.update 6 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ ℕ (fun x => x 0) ∅ 1 0 (fun _ => 0) (fun _ => 1) (by simp)
  simp [Function.update] at this

-- `Function.updateFinset_updateFinset` idx 8: necessary (s = t = {0})
theorem w22_75 : ¬ indep0% Function.updateFinset_updateFinset 8 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) (fun _ => 0) _ {0} {0} (fun _ => 0) (fun _ => 0)) (by decide)

-- `Function.updateFinset_updateFinset_of_subset` idx 5: necessary (s = {0}, t = empty, x = 0, y = 1)
theorem w22_76 : ¬ ∀ {ι : Type} {π : ι → Type} [DecidableEq ι] {s t : Finset ι} (x : ∀ i, π i)
    (y : ∀ i : s, π i) (z : ∀ i : t, π i),
    Function.updateFinset (Function.updateFinset x s y) t z = Function.updateFinset x t z := fun h => by
  have := congrFun (@h ℕ (fun _ => ℕ) _ {0} ∅ (fun _ => 0) (fun _ => 1) (fun _ => 2)) 0
  simp [Function.updateFinset] at this

-- `Function.restrict_updateFinset_of_subset` idx 5: necessary (s = {0}, t = empty)
theorem w22_77 : ¬ indep0% Function.restrict_updateFinset_of_subset 5 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ {0} ∅ (fun _ => 0) (fun _ => 0)) (by decide)

-- `Function.update_updateFinset` idx 8: necessary (s = {0}, i = 0)
theorem w22_78 : ¬ indep0% Function.update_updateFinset 8 := fun h =>
  @h ℕ (fun _ => ℕ) (fun _ => 0) _ {0} (fun _ => 0) 0 0 (by simp)

-- `Function.updateFinset_congr` idx 8: necessary (s = {0}, t = empty)
theorem w22_79 : ¬ indep0% Function.updateFinset_congr 8 := fun h =>
  absurd (@h ℕ (fun _ => True) (fun _ => trivial) _ {0} ∅ (fun _ => trivial) (fun _ => trivial)) (by decide)

-- `Finsupp.apply_eq_of_mem_graph` idx 6: necessary (f = 0, a = 0, m = 1)
theorem w22_80 : ¬ drop0% Finsupp.apply_eq_of_mem_graph 6 := fun h => by
  have := @h ℕ ℕ _ 0 1 0
  simp at this

-- `Finsupp.mapRange_multiset_sum` idx 7: necessary (F = zero homs, squaring is no additive hom)
theorem w22_81 : ¬ indep0% Finsupp.mapRange_multiset_sum 7 := fun h =>
  not_amhc (@h ℕ ℕ ℕ _ _ (ZeroHom ℕ ℕ) _ sq0 0)

-- `Finsupp.mapRange_finsetSum` idx 8: necessary (F = zero homs, squaring is no additive hom)
theorem w22_82 : ¬ indep0% Finsupp.mapRange_finsetSum 8 := fun h =>
  not_amhc (@h ℕ ℕ ℕ ℕ _ _ (ZeroHom ℕ ℕ) _ sq0 ∅ (fun _ => 0))

-- `Finsupp.mapDomain_apply_of_injective` idx 5: necessary (f constant 0, x = single 0 1, a = 1)
theorem w22_85 : ¬ drop0% Finsupp.mapDomain_apply_of_injective 5 := fun h => by
  have := @h ℕ ℕ ℕ _ (fun _ => 0) (Finsupp.single 0 1) 1
  simp [Finsupp.mapDomain_single] at this

-- `Finsupp.mapDomain_of_notMem_image_support` idx 7: necessary (f = id, x = single 0 1, b = 0)
theorem w22_86 : ¬ drop0% Finsupp.mapDomain_of_notMem_image_support 7 := fun h => by
  have := @h ℕ ℕ ℕ _ id (Finsupp.single 0 1) 0
  simp at this

-- `Finsupp.mapDomain_of_not_mem_image_support` idx 7: necessary (f = id, x = single 0 1, b = 0)
theorem w22_87 : ¬ drop0% Finsupp.mapDomain_of_not_mem_image_support 7 := fun h => by
  have := @h ℕ ℕ ℕ _ id (Finsupp.single 0 1) 0
  simp at this

-- `Finsupp.mapDomain_of_notMem_range` idx 7: necessary (f = id, x = single 0 1, a = 0)
theorem w22_88 : ¬ drop0% Finsupp.mapDomain_of_notMem_range 7 := fun h => by
  have := @h ℕ ℕ ℕ _ id (Finsupp.single 0 1) 0
  simp at this

-- `Finsupp.mapDomain_notin_range` idx 7: necessary (f = id, x = single 0 1, a = 0)
theorem w22_89 : ¬ drop0% Finsupp.mapDomain_notin_range 7 := fun h => by
  have := @h ℕ ℕ ℕ _ id (Finsupp.single 0 1) 0
  simp at this

-- `Finsupp.mapDomain_congr` idx 7: necessary (v = single 0 1, f = id, g = succ)
theorem w22_90 : ¬ drop0% Finsupp.mapDomain_congr 7 := fun h => by
  have := congrArg (· 0) (@h ℕ ℕ ℕ _ (Finsupp.single 0 1) id Nat.succ)
  simp [Finsupp.mapDomain_single] at this

-- `Finsupp.mapDomain_apply'` idx 7: necessary (S = {0}, f constant 0, x = single 0 1 + single 1 1, a = 0)
theorem w22_91 : ¬ drop0% Finsupp.mapDomain_apply' 7 := fun h => by
  have := @h ℕ ℕ ℕ _ {0} (fun _ => 0) v11 (Set.injOn_singleton _ _) 0 rfl
  rw [md_v11] at this; simp at this

-- `Finsupp.mapDomain_apply'` idx 8: necessary (S = univ, f constant 0, x = single 0 1 + single 1 1)
theorem w22_92 : ¬ drop0% Finsupp.mapDomain_apply' 8 := fun h => by
  have := @h ℕ ℕ ℕ _ Set.univ (fun _ => 0) v11 (Set.subset_univ _) 0 trivial
  rw [md_v11] at this; simp at this

-- `Finsupp.mapDomain_apply'` idx 10: necessary (S = {0}, f constant 0, x = single 0 1, a = 1)
theorem w22_93 : ¬ drop0% Finsupp.mapDomain_apply' 10 := fun h => by
  have := @h ℕ ℕ ℕ _ {0} (fun _ => 0) (Finsupp.single 0 1)
    (by simpa using Finsupp.support_single_subset) (Set.injOn_singleton _ _) 1
  simp [Finsupp.mapDomain_single] at this

-- `Finsupp.mapDomain_support_of_injOn` idx 7: necessary (Int values, f constant 0, s = single 0 1 + single 1 (-1))
theorem w22_94 : ¬ drop0% Finsupp.mapDomain_support_of_injOn 7 := fun h => by
  have := @h ℕ ℕ ℤ _ _ (fun _ => 0) vpm
  rw [md_vpm] at this
  have h0 := Finset.mem_image_of_mem (fun _ : ℕ => (0 : ℕ)) vpm0
  rw [← this] at h0; simp at h0

-- `Finsupp.mapDomain_support_of_injective` idx 6: necessary (Int values, f constant 0)
theorem w22_95 : ¬ drop0% Finsupp.mapDomain_support_of_injective 6 := fun h => by
  have := @h ℕ ℕ ℤ _ _ (fun _ => 0) vpm
  rw [md_vpm] at this
  have h0 := Finset.mem_image_of_mem (fun _ : ℕ => (0 : ℕ)) vpm0
  rw [← this] at h0; simp at h0

-- `Finsupp.sum_mapDomain_index` idx 9: necessary (Int values cancelling under f constant 0, h constant top in ENat)
theorem w22_96 : ¬ drop0% Finsupp.sum_mapDomain_index 9 := fun h => by
  have := @h ℕ ℕ ℤ ℕ∞ _ _ (fun _ => 0) vpm (fun _ _ => ⊤) (fun _ _ _ => by simp)
  rw [md_vpm, Finsupp.sum_zero_index] at this
  have h2 := (Finset.sum_eq_zero_iff.1 this.symm) 0 vpm0
  simp at h2

-- `Finsupp.prod_mapDomain_index` idx 9: necessary (Int values cancelling under f constant 0, h constant 0 in Nat)
theorem w22_97 : ¬ drop0% Finsupp.prod_mapDomain_index 9 := fun h => by
  have := @h ℕ ℕ ℤ ℕ _ _ (fun _ => 0) vpm (fun _ _ => 0) (fun _ _ _ => by simp)
  rw [md_vpm, Finsupp.prod_zero_index] at this
  have h2 : vpm.prod (fun _ _ => (0 : ℕ)) = 0 := Finset.prod_eq_zero vpm0 rfl
  rw [h2] at this; exact one_ne_zero this

-- `Finsupp.sum_mapDomain_index` idx 10: necessary (f constant 0, s = single 0 1 + single 1 1, h b m = [m != 0])
theorem w22_98 : ¬ drop0% Finsupp.sum_mapDomain_index 10 := fun h => by
  have := @h ℕ ℕ ℕ ℕ _ _ (fun _ => 0) v11 (fun _ m => if m = 0 then 0 else 1) (fun _ => rfl)
  rw [md_v11, Finsupp.sum_single_index rfl, Finsupp.sum_of_support_subset _ v11_supp _ (by simp)] at this
  simp at this

-- `Finsupp.prod_mapDomain_index` idx 10: necessary (f constant 0, s = single 0 1 + single 1 1, h b m = 2 ^ [m != 0])
theorem w22_99 : ¬ drop0% Finsupp.prod_mapDomain_index 10 := fun h => by
  have := @h ℕ ℕ ℕ ℕ _ _ (fun _ => 0) v11 (fun _ m => if m = 0 then 1 else 2) (fun _ => rfl)
  rw [md_v11, Finsupp.prod_single_index rfl, Finsupp.prod_of_support_subset _ v11_supp _ (by simp)] at this
  simp at this

-- `Finsupp.sum_mapDomain_index_inj` idx 9: necessary (f constant 0, s = single 0 1 + single 1 1, h b m = [m != 0])
theorem w22_100 : ¬ drop0% Finsupp.sum_mapDomain_index_inj 9 := fun h => by
  have := @h ℕ ℕ ℕ ℕ _ _ (fun _ => 0) v11 (fun _ m => if m = 0 then 0 else 1)
  rw [md_v11, Finsupp.sum_single_index rfl, Finsupp.sum_of_support_subset _ v11_supp _ (by simp)] at this
  simp at this

-- `Finsupp.prod_mapDomain_index_inj` idx 9: necessary (f constant 0, h b m = 2 ^ [m != 0])
theorem w22_101 : ¬ drop0% Finsupp.prod_mapDomain_index_inj 9 := fun h => by
  have := @h ℕ ℕ ℕ ℕ _ _ (fun _ => 0) v11 (fun _ m => if m = 0 then 1 else 2)
  rw [md_v11, Finsupp.prod_single_index rfl, Finsupp.prod_of_support_subset _ v11_supp _ (by simp)] at this
  simp at this

-- `Finsupp.mapDomain_injective` idx 5: necessary (f constant 0 identifies single 0 1 and single 1 1)
theorem w22_102 : ¬ drop0% Finsupp.mapDomain_injective 5 := fun h => by
  have := congrArg (· 0) (@h ℕ ℕ ℕ _ (fun _ => 0) (Finsupp.single 0 1) (Finsupp.single 1 1)
    (by simp [Finsupp.mapDomain_single]))
  simp at this

-- `Finsupp.mapDomain_surjective` idx 5: necessary (f constant 0 misses single 1 1)
theorem w22_103 : ¬ drop0% Finsupp.mapDomain_surjective 5 := fun h => by
  obtain ⟨v, hv⟩ := @h ℕ ℕ ℕ _ (fun _ => 0) (Finsupp.single 1 1)
  have := congrArg (· 1) hv
  simp only [Finsupp.mapDomain_of_notMem_range (f := fun _ : ℕ => (0 : ℕ)) v 1 (by simp)] at this
  simp at this

-- `Finsupp.mapDomain_mapRange` idx 9: necessary (g constant top in ENat is additive with g 0 != 0)
theorem w22_104 : ¬ indep0% Finsupp.mapDomain_mapRange 9 := fun h => by
  have := @h ℕ ℕ ℕ ℕ∞ _ _ id 0 (fun _ => ⊤) (fun _ _ => by simp)
  simp at this

-- `Finsupp.sum_update_add` idx 9: removable (additivity gives g i x + g i 0 = g i x, which suffices)
theorem w22_105 : drop% Finsupp.sum_update_add 9 := by
  intro α β ι _ _ f i a g hgg
  exact sum_update_add_of f i a g fun x => by rw [← hgg, add_zero]

-- `Finsupp.sum_update_add` idx 10: removable (g i 0 = 0 alone suffices)
theorem w22_106 : drop% Finsupp.sum_update_add 10 := by
  intro α β ι _ _ f i a g hg
  exact sum_update_add_of f i a g fun x => by rw [hg, add_zero]

-- `Finsupp.mapDomain_mapRange` idx 10: necessary (f constant 0, v = single 0 1 + single 1 1, g x = [x != 0])
theorem w22_107 : ¬ drop0% Finsupp.mapDomain_mapRange 10 := fun h => by
  have h0 : (fun x : ℕ => if x = 0 then (0 : ℕ) else 1) 0 = 0 := rfl
  have := congrArg (· 0) (@h ℕ ℕ ℕ ℕ _ _ (fun _ => 0) v11 (fun x : ℕ => if x = 0 then (0 : ℕ) else 1) h0)
  have hv : Finsupp.mapRange (fun x : ℕ => if x = 0 then (0 : ℕ) else 1) h0 v11 = v11 := by
    ext a; simp only [Finsupp.mapRange_apply, v11, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  simp only [hv, md_v11] at this
  simp at this

-- `Finsupp.mapDomain_injOn` idx 6: necessary (S = univ, f constant 0)
theorem w22_108 : ¬ drop0% Finsupp.mapDomain_injOn 6 := fun h => by
  have := congrArg (· 0) (@h ℕ ℕ ℕ _ Set.univ (fun _ => 0) (Finsupp.single 0 1) (by simp)
    (Finsupp.single 1 1) (by simp) (by simp [Finsupp.mapDomain_single]))
  simp at this

-- `Finsupp.comapDomain_support` idx 6: necessary (f constant 0, l = single 0 1)
theorem w22_109 : ¬ indep0% Finsupp.comapDomain_support 6 := fun h => by
  have := @h ℕ ℕ ℕ _ (fun _ => 0) (Finsupp.single 0 1)
  exact absurd (this (show (0 : ℕ) ∈ _ by simp) (show (1 : ℕ) ∈ _ by simp) rfl) (by decide)

-- `Finsupp.comapDomain_apply` idx 6: necessary (f constant 0, l = single 0 1)
theorem w22_110 : ¬ indep0% Finsupp.comapDomain_apply 6 := fun h => by
  have := @h ℕ ℕ ℕ _ (fun _ => 0) (Finsupp.single 0 1) 0
  exact absurd (this (show (0 : ℕ) ∈ _ by simp) (show (1 : ℕ) ∈ _ by simp) rfl) (by decide)

-- `Finsupp.sum_comapDomain` idx 9: necessary (f constant 0, l = single 0 1)
theorem w22_111 : ¬ indep0% Finsupp.sum_comapDomain 9 := fun h => by
  have := (@h ℕ ℕ ℕ ℕ _ _ (fun _ => 0) (Finsupp.single 0 1) (fun _ _ => 0)).injOn
  exact absurd (this (show (0 : ℕ) ∈ _ by simp) (show (1 : ℕ) ∈ _ by simp) rfl) (by decide)

-- `Finsupp.prod_comapDomain` idx 9: necessary (f constant 0, l = single 0 1)
theorem w22_112 : ¬ indep0% Finsupp.prod_comapDomain 9 := fun h => by
  have := (@h ℕ ℕ ℕ ℕ _ _ (fun _ => 0) (Finsupp.single 0 1) (fun _ _ => 0)).injOn
  exact absurd (this (show (0 : ℕ) ∈ _ by simp) (show (1 : ℕ) ∈ _ by simp) rfl) (by decide)

-- `Finsupp.eq_zero_of_comapDomain_eq_zero` idx 6: necessary (f constant 0, l = single 0 1)
theorem w22_113 : ¬ indep0% Finsupp.eq_zero_of_comapDomain_eq_zero 6 := fun h => by
  have := (@h ℕ ℕ ℕ _ (fun _ => 0) (Finsupp.single 0 1)).injOn
  exact absurd (this (show (0 : ℕ) ∈ _ by simp) (show (1 : ℕ) ∈ _ by simp) rfl) (by decide)

-- `Finsupp.eq_zero_of_comapDomain_eq_zero` idx 7: necessary (f = id, l = single 0 1)
theorem w22_114 : ¬ drop0% Finsupp.eq_zero_of_comapDomain_eq_zero 7 := fun h => by
  have := @h ℕ ℕ ℕ _ id (Finsupp.single 0 1) (by simpa using Set.bijOn_id _)
  simp at this

-- `Finsupp.comapDomain_single_of_notMem_range` idx 8: removable (derivable: the preimage of the support is empty since b is not in the range)
theorem w22_115 : indep% Finsupp.comapDomain_single_of_notMem_range 8 := by
  intro α β M _ f b hb m a₁ h₁ a₂ h₂ _
  exact absurd ⟨a₁, Finset.mem_singleton.1 (Finsupp.support_single_subset h₁)⟩ hb

-- `Finsupp.comapDomain_single_of_not_mem_range` idx 8: removable (derivable: the preimage of the support is empty since b is not in the range)
theorem w22_116 : indep% Finsupp.comapDomain_single_of_not_mem_range 8 := by
  intro α β M _ f b hb m a₁ h₁ a₂ h₂ _
  exact absurd ⟨a₁, Finset.mem_singleton.1 (Finsupp.support_single_subset h₁)⟩ hb

-- `Finsupp.embDomain_comapDomain` idx 6: necessary (f = succ, g = single 0 1)
theorem w22_117 : ¬ drop0% Finsupp.embDomain_comapDomain 6 := fun h => by
  have := congrArg (· 0) (@h ℕ ℕ ℕ _ ⟨Nat.succ, Nat.succ_injective⟩ (Finsupp.single 0 1))
  simp only [Finsupp.embDomain_of_notMem_range (⟨Nat.succ, Nat.succ_injective⟩ : ℕ ↪ ℕ) _ 0 (by simp)] at this
  simp at this

-- `Finsupp.comapDomain_add` idx 7: removable (derivable: f is injective on the preimage of supp v2 and of supp (v1 + v2), which cover supp v1, and preimage membership only depends on the value of f)
theorem w22_118 : indep% Finsupp.comapDomain_add 7 := by
  intro α β M _ f v₁ v₂ h₂ h₁₂ a₁ ha₁ a₂ ha₂ he
  simp only [Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff] at ha₁ ha₂
  by_cases hv : v₂ (f a₁) = 0
  · exact h₁₂ (by simp [hv, ha₁]) (by simp [← he, hv, ha₁]) he
  · exact h₂ (by simpa using hv) (by simpa [← he] using hv) he

-- `Finsupp.comapDomain_add` idx 8: removable (derivable: supp v2 is covered by supp v1 and supp (v1 + v2))
theorem w22_119 : indep% Finsupp.comapDomain_add 8 := by
  intro α β M _ f v₁ v₂ h₁ h₁₂ a₁ ha₁ a₂ ha₂ he
  simp only [Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff] at ha₁ ha₂
  by_cases hv : v₁ (f a₁) = 0
  · exact h₁₂ (by simp [hv, ha₁]) (by simp [← he, hv, ha₁]) he
  · exact h₁ (by simpa using hv) (by simpa [← he] using hv) he

-- `Finsupp.comapDomain_add` idx 9: removable (derivable: supp (v1 + v2) is covered by supp v1 and supp v2)
theorem w22_120 : indep% Finsupp.comapDomain_add 9 := by
  intro α β M _ f v₁ v₂ h₁ h₂ a₁ ha₁ a₂ ha₂ he
  simp only [Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.add_apply] at ha₁ ha₂
  by_cases hv : v₁ (f a₁) = 0
  · exact h₂ (by simp_all) (by simp_all [← he]) he
  · exact h₁ (by simpa using hv) (by simpa [← he] using hv) he

-- `Finsupp.comapDomain_add_of_injective` idx 5: necessary (f constant 0)
theorem w22_121 : ¬ indep0% Finsupp.comapDomain_add_of_injective 5 := fun h => by
  have := @h ℕ ℕ ℕ _ (fun _ => 0) 0 0 (a₁ := 0) (a₂ := 1) rfl
  simp at this

-- `Finsupp.mapDomain_comapDomain` idx 5: necessary (f constant 0, l = 0)
theorem w22_122 : ¬ indep0% Finsupp.mapDomain_comapDomain 5 := fun h => by
  have := @h ℕ ℕ ℕ _ (fun _ => 0) 0 (by simp) (a₁ := 0) (a₂ := 1) rfl
  simp at this

-- `Finsupp.mapDomain_comapDomain` idx 7: necessary (f = succ, l = single 0 1)
theorem w22_123 : ¬ drop0% Finsupp.mapDomain_comapDomain 7 := fun h => by
  have := congrArg (· 0) (@h ℕ ℕ ℕ _ Nat.succ Nat.succ_injective (Finsupp.single 0 1))
  simp only [Finsupp.mapDomain_of_notMem_range (f := Nat.succ) _ 0 (by simp)] at this
  simp at this

-- `Finsupp.mem_range_mapDomain_iff` idx 5: removable (a section of f on its range gives a preimage; empty domain separately)
theorem w22_124 : drop% Finsupp.mem_range_mapDomain_iff 5 := by
  intro α β M _ f x
  constructor
  · rintro ⟨v, rfl⟩ b hb; exact Finsupp.mapDomain_of_notMem_range v b hb
  · intro hx
    rcases isEmpty_or_nonempty α with hα | hα
    · refine ⟨0, ?_⟩
      ext b; rw [Finsupp.mapDomain_zero, hx b (by rintro ⟨a, -⟩; exact isEmptyElim a)]; rfl
    · refine ⟨Finsupp.mapDomain (Function.invFun f) x, ?_⟩
      rw [← Finsupp.mapDomain_comp]
      conv_rhs => rw [← Finsupp.mapDomain_id (v := x)]
      apply Finsupp.mapDomain_congr
      intro b hb
      have : b ∈ Set.range f := by
        by_contra hn; exact (Finsupp.mem_support_iff.1 hb) (hx b hn)
      exact Function.invFun_eq this

-- `Finsupp.filter_apply_pos` idx 7: necessary (p = False, f = single 0 1, a = 0)
theorem w22_125 : ¬ drop0% Finsupp.filter_apply_pos 7 := fun h => by
  have := @h ℕ ℕ _ (fun _ => False) _ (Finsupp.single 0 1) 0
  simp at this

-- `Finsupp.filter_apply_neg` idx 7: necessary (p = True, f = single 0 1, a = 0)
theorem w22_126 : ¬ drop0% Finsupp.filter_apply_neg 7 := fun h => by
  have := @h ℕ ℕ _ (fun _ => True) _ (Finsupp.single 0 1) 0
  simp at this

-- `Finsupp.filter_single_of_pos` idx 7: necessary (p = False, a = 0, b = 1)
theorem w22_127 : ¬ drop0% Finsupp.filter_single_of_pos 7 := fun h => by
  have := congrArg (· 0) (@h ℕ ℕ _ (fun _ => False) _ 0 1)
  simp at this

-- `Finsupp.subtypeDomain_eq_iff` idx 6: necessary (p = False, f = single 0 1, g = 0)
theorem w22_128 : ¬ drop0% Finsupp.subtypeDomain_eq_iff 6 := fun h => by
  have := (@h ℕ ℕ _ (fun _ => False) (Finsupp.single 0 1) 0 (by simp)).1 (by ext a; exact a.2.elim)
  simp at this

-- `Finsupp.subtypeDomain_eq_iff` idx 7: necessary (p = False, f = 0, g = single 0 1)
theorem w22_129 : ¬ drop0% Finsupp.subtypeDomain_eq_iff 7 := fun h => by
  have := congrArg (· 0) ((@h ℕ ℕ _ (fun _ => False) 0 (Finsupp.single 0 1) (by simp)).1
    (by ext a; exact a.2.elim))
  simp at this

-- `Finsupp.subtypeDomain_eq_zero_iff` idx 5: necessary (p = False, f = single 0 1)
theorem w22_130 : ¬ drop0% Finsupp.subtypeDomain_eq_zero_iff 5 := fun h => by
  have := (@h ℕ ℕ _ (fun _ => False) (Finsupp.single 0 1)).1 (by ext a; exact a.2.elim)
  simp at this

-- `Finsupp.sum_subtypeDomain_index` idx 8: necessary (p = False, v = single 0 1, h = 1)
theorem w22_131 : ¬ drop0% Finsupp.sum_subtypeDomain_index 8 := fun h => by
  have := @h ℕ ℕ ℕ _ (fun _ => False) _ (Finsupp.single 0 1) (fun _ _ => 1)
  rw [show Finsupp.subtypeDomain (fun _ : ℕ => False) (Finsupp.single 0 1 : ℕ →₀ ℕ) = 0 by
    ext a; exact a.2.elim] at this
  simp [Finsupp.sum, Finsupp.prod, Finsupp.support_single_ne_zero] at this

-- `Finsupp.prod_subtypeDomain_index` idx 8: necessary (p = False, v = single 0 1, h = 2)
theorem w22_132 : ¬ drop0% Finsupp.prod_subtypeDomain_index 8 := fun h => by
  have := @h ℕ ℕ ℕ _ (fun _ => False) _ (Finsupp.single 0 1) (fun _ _ => 2)
  rw [show Finsupp.subtypeDomain (fun _ : ℕ => False) (Finsupp.single 0 1 : ℕ →₀ ℕ) = 0 by
    ext a; exact a.2.elim] at this
  simp [Finsupp.sum, Finsupp.prod, Finsupp.support_single_ne_zero] at this

-- `Finsupp.mem_support_finsetSum` idx 7: necessary (s = empty)
theorem w22_133 : ¬ drop0% Finsupp.mem_support_finsetSum 7 := fun h => by
  have := @h ℕ ℕ ℕ _ ∅ (fun _ => 0) 0
  simp at this

-- `Finsupp.extendDomain_subtypeDomain` idx 6: necessary (P = False, f = single 0 1)
theorem w22_134 : ¬ drop0% Finsupp.extendDomain_subtypeDomain 6 := fun h => by
  have := congrArg (· 0) (@h ℕ ℕ _ (fun _ => False) _ (Finsupp.single 0 1))
  simp at this

-- `Finsupp.mapDomain_support_of_subsingletonAddUnits` idx 6: necessary (Int values, f constant 0)
theorem w22_135 : ¬ drop0% Finsupp.mapDomain_support_of_subsingletonAddUnits 6 := fun h => by
  have := @h ℕ ℕ ℤ _ _ (fun _ => 0) vpm
  rw [md_vpm] at this
  have h0 := Finset.mem_image_of_mem (fun _ : ℕ => (0 : ℕ)) vpm0
  rw [← this] at h0; simp at h0

-- `Finsupp.mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits` idx 5: necessary (Int values, f constant 0)
theorem w22_136 : ¬ drop0% Finsupp.mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits 5 := fun h =>
  vpm_ne ((@h ℕ ℕ ℤ _ (fun _ => 0) vpm).1 md_vpm)

-- `List.support_sum_eq` idx 5: necessary (l = [single 0 1, single 0 (-1)] in Int)
theorem w22_137 : ¬ drop0% List.support_sum_eq 5 := fun h => by
  have := @h ℕ ℤ _ _ [Finsupp.single 0 1, Finsupp.single 0 (-1)]
  simp [← Finsupp.single_add] at this

-- `Multiset.support_sum_eq` idx 5: necessary (s = {single 0 1, single 0 (-1)} in Int)
theorem w22_138 : ¬ drop0% Multiset.support_sum_eq 5 := fun h => by
  have := @h ℕ ℤ _ _ ↑[Finsupp.single 0 1, Finsupp.single 0 (-1)]
  simp [← Finsupp.single_add] at this

-- `Finset.support_sum_eq` idx 5: necessary (s = {single 0 1, single 0 (-1)} in Int)
theorem w22_139 : ¬ drop0% Finset.support_sum_eq 5 := fun h => by
  have hne : (Finsupp.single 0 1 : ℕ →₀ ℤ) ≠ Finsupp.single 0 (-1) := by
    intro he; have := congrArg (· 0) he; simp at this
  have := @h ℕ ℤ _ _ {Finsupp.single 0 1, Finsupp.single 0 (-1)}
  rw [Finset.sum_pair hne, Finset.sup_insert, Finset.sup_singleton] at this
  simp [← Finsupp.single_add] at this

-- `Finsupp.ext` idx 5: necessary (f = 0, g = single 0 1)
theorem w22_140 : ¬ drop0% Finsupp.ext 5 := fun h => by
  have := congrArg (· 0) (@h ℕ ℕ _ 0 (Finsupp.single 0 1))
  simp at this

-- `Finsupp.instSubsingleton` idx 3: necessary (alpha = Unit, M = Nat)
theorem w22_141 : ¬ drop0% Finsupp.instSubsingleton 3 := fun h => by
  have := congrArg (· ()) ((@h Unit ℕ _).elim (Finsupp.single () 1) 0)
  simp at this

-- `Finsupp.instSubsingleton'` idx 3: necessary (alpha = Unit, M = Nat)
theorem w22_142 : ¬ drop0% Finsupp.instSubsingleton' 3 := fun h => by
  have := congrArg (· ()) ((@h Unit ℕ _).elim (Finsupp.single () 1) 0)
  simp at this

-- `Finsupp.nontrivial_of_nontrivial` idx 3: necessary (M = Unit)
theorem w22_143 : ¬ drop0% Finsupp.nontrivial_of_nontrivial 3 := fun h =>
  not_nontrivial Unit (@h ℕ Unit _)

-- `Finsupp.equivFunOnFinite_symm_apply_apply` idx 3: necessary (alpha = Nat)
theorem w22_144 : ¬ indep0% Finsupp.equivFunOnFinite_symm_apply_apply 3 := fun h =>
  @not_finite ℕ _ (@h ℕ ℕ _ 0 0)

-- `Finsupp.equivFunOnFinite_apply` idx 3: necessary (alpha = Nat)
theorem w22_145 : ¬ indep0% Finsupp.equivFunOnFinite_apply 3 := fun h =>
  @not_finite ℕ _ (@h ℕ ℕ _ 0 0)

-- `Finsupp.equivFunOnFinite_symm_apply_support` idx 3: necessary (alpha = Nat)
theorem w22_146 : ¬ indep0% Finsupp.equivFunOnFinite_symm_apply_support 3 := fun h =>
  @not_finite ℕ _ (@h ℕ ℕ _ 0)

-- `Finsupp.equivFunOnFinite_symm_coe` idx 3: necessary (alpha = Nat)
theorem w22_147 : ¬ indep0% Finsupp.equivFunOnFinite_symm_coe 3 := fun h =>
  @not_finite ℕ _ (@h ℕ _ ℕ 0)

-- `Finsupp.coe_equivFunOnFinite_symm` idx 3: necessary (alpha = Nat)
theorem w22_148 : ¬ indep0% Finsupp.coe_equivFunOnFinite_symm 3 := fun h =>
  @not_finite ℕ _ (@h ℕ _ ℕ 0)

-- `Finsupp.unique_ext` idx 6: necessary (alpha = Unit, f = single () 1, g = 0)
theorem w22_149 : ¬ drop0% Finsupp.unique_ext 6 := fun h => by
  have := congrArg (· ()) (@h Unit ℕ _ _ (Finsupp.single () 1) 0)
  simp at this

-- `Finsupp.ofSupportFinite_coe` idx 4: necessary (f constant 1 on Nat)
theorem w22_150 : ¬ indep0% Finsupp.ofSupportFinite_coe 4 := fun h => by
  have := @h ℕ ℕ _ (fun _ => 1)
  simp [Function.support_const] at this
  exact Set.infinite_univ this

-- `Finsupp.ofSupportFinite_support` idx 4: necessary (f constant 1 on Nat)
theorem w22_151 : ¬ indep0% Finsupp.ofSupportFinite_support 4 := fun h => by
  have := @h ℕ ℕ _ (fun _ => 1)
  simp [Function.support_const] at this
  exact Set.infinite_univ this

-- `Finsupp.mapRange_eq_zero` idx 7: necessary (f constant 0, a = single 0 1)
theorem w22_152 : ¬ drop0% Finsupp.mapRange_eq_zero 7 := fun h => by
  have := congrArg (· 0) ((@h ℕ ℕ ℕ _ _ (Finsupp.single 0 1) (fun _ => 0) rfl).1 (by ext; simp))
  simp at this

-- `Finsupp.mapRange_eq_zero` idx 8: necessary (f = succ)
theorem w22_153 : ¬ indep0% Finsupp.mapRange_eq_zero 8 := fun h => by
  have := @h ℕ ℕ ℕ _ _ 0 Nat.succ Nat.succ_injective
  simp at this

-- `Finsupp.support_mapRange_of_injective` idx 8: necessary (e constant 0, f = single 0 1)
theorem w22_154 : ¬ drop0% Finsupp.support_mapRange_of_injective 8 := fun h => by
  have := @h ℕ ℕ ℕ _ _ (fun _ => 0) rfl (Finsupp.single 0 1)
  rw [show Finsupp.mapRange (fun _ : ℕ => (0 : ℕ)) rfl (Finsupp.single 0 1 : ℕ →₀ ℕ) = 0 by
    ext; simp] at this
  simp at this

-- `Finsupp.support_mapRange_eq` idx 8: necessary (f constant 0, g = single 0 1)
theorem w22_155 : ¬ drop0% Finsupp.support_mapRange_eq 8 := fun h => by
  have := @h ℕ ℕ ℕ _ _ (fun _ => 0) rfl (Finsupp.single 0 1)
  rw [show Finsupp.mapRange (fun _ : ℕ => (0 : ℕ)) rfl (Finsupp.single 0 1 : ℕ →₀ ℕ) = 0 by
    ext; simp] at this
  simp at this

-- `Finsupp.mapRange_injective` idx 7: necessary (e constant 0)
theorem w22_156 : ¬ drop0% Finsupp.mapRange_injective 7 := fun h => by
  have := congrArg (· 0) (@h ℕ ℕ ℕ _ _ (fun _ => 0) rfl (Finsupp.single 0 1) 0 (by ext; simp))
  simp at this

-- `Finsupp.mapRange_surjective` idx 7: necessary (e constant 0, alpha = Unit)
theorem w22_157 : ¬ drop0% Finsupp.mapRange_surjective 7 := fun h => by
  obtain ⟨v, hv⟩ := @h Unit ℕ ℕ _ _ (fun _ => 0) rfl (Finsupp.single () 1)
  have := congrArg (· ()) hv
  simp at this

-- `Finsupp.mapRange_bijective` idx 7: necessary (e constant 0, alpha = Unit)
theorem w22_158 : ¬ drop0% Finsupp.mapRange_bijective 7 := fun h => by
  obtain ⟨v, hv⟩ := (@h Unit ℕ ℕ _ _ (fun _ => 0) rfl).2 (Finsupp.single () 1)
  have := congrArg (· ()) hv
  simp at this

-- `Finsupp.mapRange.equiv_apply` idx 6: necessary (e = swap 0 1)
theorem w22_159 : ¬ indep0% Finsupp.mapRange.equiv_apply 6 := fun h => by
  have := @h ℕ ℕ ℕ _ _ (Equiv.swap 0 1) 0
  simp [Equiv.swap_apply_left] at this

-- `Finsupp.mapRange.equiv_trans` idx 8: necessary (e = swap 0 1, f2 = refl)
theorem w22_160 : ¬ indep0% Finsupp.mapRange.equiv_trans 8 := fun h => by
  have := @h ℕ ℕ ℕ ℕ _ _ _ (Equiv.swap 0 1) (Equiv.refl ℕ) rfl
  simp [Equiv.swap_apply_left] at this

-- `Finsupp.mapRange.equiv_trans` idx 10: necessary (e = refl, f2 = swap 0 1)
theorem w22_161 : ¬ indep0% Finsupp.mapRange.equiv_trans 10 := fun h => by
  have := @h ℕ ℕ ℕ ℕ _ _ _ (Equiv.refl ℕ) rfl (Equiv.swap 0 1)
  simp [Equiv.swap_apply_left] at this

-- `Finsupp.mapRange.equiv_symm` idx 6: necessary (e = swap 0 1)
theorem w22_162 : ¬ indep0% Finsupp.mapRange.equiv_symm 6 := fun h => by
  have := @h ℕ ℕ ℕ _ _ (Equiv.swap 0 1)
  simp [Equiv.swap_apply_left] at this

-- `Finsupp.embDomain_of_notMem_range` idx 7: necessary (f = refl, v = single 0 1, a = 0)
theorem w22_163 : ¬ drop0% Finsupp.embDomain_of_notMem_range 7 := fun h => by
  have h1 := @h ℕ ℕ ℕ _ (Function.Embedding.refl ℕ) (Finsupp.single 0 1) 0
  have h2 := Finsupp.embDomain_apply (Function.Embedding.refl ℕ) (Finsupp.single 0 1 : ℕ →₀ ℕ) 0
  have h3 : (0 : ℕ) = 1 := h1.symm.trans (h2.trans (by simp))
  simp at h3

-- `Finsupp.embDomain_notin_range` idx 7: necessary (f = refl, v = single 0 1, a = 0)
theorem w22_164 : ¬ drop0% Finsupp.embDomain_notin_range 7 := fun h => by
  have h1 := @h ℕ ℕ ℕ _ (Function.Embedding.refl ℕ) (Finsupp.single 0 1) 0
  have h2 := Finsupp.embDomain_apply (Function.Embedding.refl ℕ) (Finsupp.single 0 1 : ℕ →₀ ℕ) 0
  have h3 : (0 : ℕ) = 1 := h1.symm.trans (h2.trans (by simp))
  simp at h3

-- `Finsupp.embDomain_mapRange` idx 9: necessary (g = succ)
theorem w22_165 : ¬ indep0% Finsupp.embDomain_mapRange 9 := fun h => by
  have := @h ℕ ℕ ℕ ℕ _ _ (Function.Embedding.refl ℕ) Nat.succ 0
  simp at this

-- `Finsupp.zipWith_apply` idx 8: necessary (f constant 1)
theorem w22_166 : ¬ indep0% Finsupp.zipWith_apply 8 := fun h => by
  have := @h ℕ ℕ ℕ ℕ _ _ _ (fun _ _ => 1) 0 0 0
  simp at this

-- `Finsupp.support_zipWith` idx 9: necessary (f constant 1)
theorem w22_167 : ¬ indep0% Finsupp.support_zipWith 9 := fun h => by
  have := @h ℕ ℕ ℕ ℕ _ _ _ _ (fun _ _ => 1) 0 0
  simp at this

-- `instCountableFinsupp` idx 2: necessary (alpha = Real embeds into Real to Nat finsupps via single)
theorem w22_168 : ¬ drop0% instCountableFinsupp 2 := fun h =>
  Cardinal.not_countable_real (Set.countable_univ_iff.2
    (@Function.Injective.countable _ _ (@h ℝ ℕ _ _) _ (Finsupp.single_left_injective one_ne_zero)))

-- `instCountableFinsupp` idx 3: necessary (beta = Real embeds into Unit to Real finsupps via single)
theorem w22_169 : ¬ drop0% instCountableFinsupp 3 := fun h =>
  Cardinal.not_countable_real (Set.countable_univ_iff.2
    (@Function.Injective.countable _ _ (@h Unit ℝ _ _) _ (Finsupp.single_injective ())))

-- `Finsupp.addHom_ext` idx 7: necessary (f = 0, g = evaluation at 0)
theorem w22_170 : ¬ drop0% Finsupp.addHom_ext 7 := fun h => by
  have := congrArg (· (Finsupp.single 0 1)) (@h ℕ ℕ ℕ _ _ 0 (Finsupp.applyAddHom 0))
  simp at this

-- `Finsupp.addHom_ext'` idx 7: necessary (f = 0, g = evaluation at 0)
theorem w22_171 : ¬ drop0% Finsupp.addHom_ext' 7 := fun h => by
  have := congrArg (· (Finsupp.single 0 1)) (@h ℕ ℕ ℕ _ _ 0 (Finsupp.applyAddHom 0))
  simp at this

-- `Finsupp.mulHom_ext` idx 7: necessary (f = 1, g = evaluation at 0, multiplicatively)
theorem w22_172 : ¬ drop0% Finsupp.mulHom_ext 7 := fun h => by
  have := congrArg (· (Multiplicative.ofAdd (Finsupp.single 0 1)))
    (@h ℕ ℕ (Multiplicative ℕ) _ _ 1 (Finsupp.applyAddHom 0).toMultiplicative)
  simp at this
  exact absurd (ofAdd_eq_one.1 this.symm) one_ne_zero

-- `Finsupp.mulHom_ext'` idx 7: necessary (f = 1, g = evaluation at 0, multiplicatively)
theorem w22_173 : ¬ drop0% Finsupp.mulHom_ext' 7 := fun h => by
  have := congrArg (· (Multiplicative.ofAdd (Finsupp.single 0 1)))
    (@h ℕ ℕ (Multiplicative ℕ) _ _ 1 (Finsupp.applyAddHom 0).toMultiplicative)
  simp at this
  exact absurd (ofAdd_eq_one.1 this.symm) one_ne_zero

-- `Finsupp.cons_ne_zero_of_left` idx 5: necessary (y = 0, s = 0)
theorem w22_174 : ¬ drop0% Finsupp.cons_ne_zero_of_left 5 := fun h =>
  @h 0 ℕ _ 0 0 Finsupp.cons_zero_zero

-- `Finsupp.cons_ne_zero_of_right` idx 5: necessary (y = 0, s = 0)
theorem w22_175 : ¬ drop0% Finsupp.cons_ne_zero_of_right 5 := fun h =>
  @h 0 ℕ _ 0 0 Finsupp.cons_zero_zero

-- `Finsupp.infinite_of_left` idx 3: necessary (alpha = Unit: Nat to Unit finsupps form a subsingleton)
theorem w22_176 : ¬ drop0% Finsupp.infinite_of_left 3 := fun h =>
  @not_finite (ℕ →₀ Unit) (@h ℕ Unit _ _) inferInstance

-- `Finsupp.infinite_of_left` idx 4: necessary (iota = Unit, alpha = Fin 2)
theorem w22_177 : ¬ drop0% Finsupp.infinite_of_left 4 := fun h =>
  @not_finite (Unit →₀ Fin 2) (@h Unit (Fin 2) _ _) (Finite.of_equiv _ Finsupp.equivFunOnFinite.symm)

-- `Finsupp.infinite_of_right` idx 3: necessary (iota = Unit, alpha = Fin 2)
theorem w22_178 : ¬ drop0% Finsupp.infinite_of_right 3 := fun h =>
  @not_finite (Unit →₀ Fin 2) (@h Unit (Fin 2) _ _) (Finite.of_equiv _ Finsupp.equivFunOnFinite.symm)

-- `Finsupp.infinite_of_right` idx 4: necessary (iota = Empty: a subsingleton)
theorem w22_179 : ¬ drop0% Finsupp.infinite_of_right 4 := fun h =>
  @not_finite (Empty →₀ ℕ) (@h Empty ℕ _ _) inferInstance

-- `Finsupp.indicator_of_mem` idx 5: necessary (s = empty)
theorem w22_180 : ¬ indep0% Finsupp.indicator_of_mem 5 := fun h => by
  have := @h ℕ ℕ _ ∅ 0 (fun _ _ => 0)
  simp at this

-- `Finsupp.indicator_of_notMem` idx 5: necessary (s = {0}, i = 0, f = 1)
theorem w22_181 : ¬ drop0% Finsupp.indicator_of_notMem 5 := fun h => by
  have := @h ℕ ℕ _ {0} 0 (fun _ _ => 1)
  rw [Finsupp.indicator_of_mem (by simp)] at this
  simp at this

section
namespace W2c2

theorem isField2 : IsField (ZMod 2) :=
  ⟨⟨0, 1, by decide⟩, fun {a b} => mul_comm a b, fun {a} ha => ⟨a, by revert a; decide⟩⟩

/-- ZMod 2 as a field (the library instance lives outside Mathlib.Data). -/
noncomputable def F2 : Field (ZMod 2) := isField2.toField

end W2c2
attribute [local instance] W2c2.F2

theorem W2c2.half2 : (((1 / 2 : ℚ)) : ZMod 2) = 0 := by
  rw [one_div, show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, Rat.cast_inv_nat,
    show ((2 : ℕ) : ZMod 2) = 0 from by decide, inv_zero]

-- `Rat.cast_finsupp_sum` idx 6: necessary (R = ZMod 2, f = single 0 1 + single 1 1, g a b = 1/2 for b != 0)
theorem w22_83 : ¬ drop0% Rat.cast_finsupp_sum 6 := fun h => by
  have := @h ℕ ℕ (ZMod 2) _ v11 _
    (fun _ b => if b = 0 then 0 else ((2 : ℕ) : ℚ)⁻¹)
  rw [Finsupp.sum_of_support_subset _ v11_supp _ (by simp),
    Finsupp.sum_of_support_subset _ v11_supp _ (by simp)] at this
  simp only [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)] at this
  simp only [v11, Finsupp.add_apply, Finsupp.single_apply] at this
  norm_num at this
  rw [W2c2.half2] at this
  revert this; decide

-- `Rat.cast_finsuppProd` idx 6: necessary (R = ZMod 2, factors 1/2 and 2)
theorem w22_84 : ¬ drop0% Rat.cast_finsuppProd 6 := fun h => by
  have := @h ℕ ℕ (ZMod 2) _ v11 _
    (fun a b => if b = 0 then 1 else if a = 0 then ((2 : ℕ) : ℚ)⁻¹ else 2)
  rw [Finsupp.prod_of_support_subset _ v11_supp _ (by simp),
    Finsupp.prod_of_support_subset _ v11_supp _ (by simp)] at this
  simp only [Finset.prod_pair (by decide : (0 : ℕ) ≠ 1)] at this
  simp only [v11, Finsupp.add_apply, Finsupp.single_apply] at this
  norm_num at this
  rw [W2c2.half2] at this
  revert this; decide

end

