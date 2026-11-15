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

namespace W2c3

/-- In ℤ, the supremum of a sequence above the identity is the junk value 0. -/
theorem zsup_unb (f : ℕ → ℤ) (hf : ∀ n : ℕ, (n : ℤ) ≤ f n) : ⨆ n, f n = 0 :=
  Int.csSup_of_not_bddAbove (by
    rintro ⟨b, hb⟩
    have h1 : f (b.toNat + 1) ≤ b := hb ⟨b.toNat + 1, rfl⟩
    have h2 := hf (b.toNat + 1)
    omega)

/-- In ℤ, the infimum of a sequence below minus the identity is the junk value 0. -/
theorem zinf_unb (f : ℕ → ℤ) (hf : ∀ n : ℕ, f n ≤ -(n : ℤ)) : ⨅ n, f n = 0 :=
  Int.csInf_of_not_bddBelow (by
    rintro ⟨b, hb⟩
    have h1 : b ≤ f (b.natAbs + 1) := hb ⟨b.natAbs + 1, rfl⟩
    have h2 := hf (b.natAbs + 1)
    omega)

theorem zsup_empty (f : Empty → ℤ) : ⨆ i, f i = 0 := by
  show sSup (Set.range f) = 0
  rw [Set.range_eq_empty]; exact Int.csSup_empty

theorem zinf_empty (f : Empty → ℤ) : ⨅ i, f i = 0 := by
  show sInf (Set.range f) = 0
  rw [Set.range_eq_empty]; exact Int.csInf_empty

theorem zsupB (g : Bool → ℤ) : ⨆ b, g b = max (g true) (g false) :=
  le_antisymm (ciSup_le fun b => by cases b <;> simp)
    (max_le (le_ciSup (Set.finite_range g).bddAbove true) (le_ciSup (Set.finite_range g).bddAbove false))

theorem zinfB (g : Bool → ℤ) : ⨅ b, g b = min (g true) (g false) :=
  le_antisymm (le_min (ciInf_le (Set.finite_range g).bddBelow true) (ciInf_le (Set.finite_range g).bddBelow false))
    (le_ciInf fun b => by cases b <;> simp)

/-- Unit ⊕ Unit with the disjoint sum order is not directed. -/
theorem uu_nd : ¬ ∃ M : Unit ⊕ Unit, Sum.inl () ≤ M ∧ Sum.inr () ≤ M := by
  rintro ⟨M | M, h1, h2⟩ <;> simp at h1 h2

theorem uu_ncd : ¬ ∃ M : Unit ⊕ Unit, M ≤ Sum.inl () ∧ M ≤ Sum.inr () := by
  rintro ⟨M | M, h1, h2⟩ <;> simp at h1 h2

/-- On Fin 3, ≠ is directed (any two points have a third point different from both). -/
theorem ne3_dir : Directed (fun a b : Fin 3 => a ≠ b) id := by
  unfold Directed; decide

theorem iio_dir : Directed (fun x1 x2 : Set ℕ => x1 ≤ x2) (fun n => Set.Iio n) :=
  Monotone.directed_le (fun _ _ h => Set.Iio_subset_Iio h)

/-! J: copy of Probe1.J (checks/Probe1Hand.lean), ℕ with a set-dependent junk sSup. -/
def J := ℕ

def toJ (n : ℕ) : J := n
def ofJ (a : J) : ℕ := a

instance : Lattice J := inferInstanceAs (Lattice ℕ)

open Classical in
noncomputable instance : ConditionallyCompleteLattice J :=
  { (inferInstance : Lattice J) with
    sSup := fun s : Set J => if s.Nonempty ∧ BddAbove s then toJ (sSup (α := ℕ) s) else
      if toJ 7 ∈ s then toJ 1 else toJ 0
    sInf := fun s : Set J => toJ (sInf (α := ℕ) s)
    isLUB_csSup := fun s hn hb => by
      show IsLUB s (if s.Nonempty ∧ BddAbove s then toJ (sSup (α := ℕ) s) else
        if toJ 7 ∈ s then toJ 1 else toJ 0)
      rw [if_pos ⟨hn, hb⟩]; exact isLUB_csSup (α := ℕ) hn hb
    isGLB_csInf := fun s hn hb => isGLB_csInf (α := ℕ) hn hb }

open Classical in
theorem sSupJ (s : Set J) (hs : ¬ BddAbove s) : sSup s = if toJ 7 ∈ s then toJ 1 else toJ 0 := by
  classical
  show (if _ then _ else _) = _
  rw [if_neg (fun h => hs h.2)]

theorem leJ {a b : J} : a ≤ b ↔ ofJ a ≤ ofJ b := Iff.rfl
@[simp] theorem ofJ_toJ (n : ℕ) : ofJ (toJ n) = n := rfl
theorem toJ_inj {a b : ℕ} : toJ a = toJ b ↔ a = b := Iff.rfl

/-- Copy of Probe1 p1_44: junk sSup of J refutes the ciSup product formula when the first index type is infinite. -/
theorem jprod : ¬ ∀ {α ι ι' : Type} [Finite ι'] [inst : ConditionallyCompleteLattice α] (f : ι × ι' → α),
    ⨆ a, f a = ⨆ i, ⨆ i', f (i, i') := fun h => by
  let f : ℕ × Bool → J := fun p => if p.2 then toJ (p.1 + 8) else if p.1 = 0 then toJ 7 else toJ 0
  have e := @h J ℕ Bool _ _ f
  have hg : ∀ i, (⨆ b, f (i, b)) = toJ (i + 8) := fun i =>
    le_antisymm (ciSup_le fun b => by
        rw [leJ]
        cases b
        · by_cases hi : i = 0 <;> simp [f, hi]
        · simp [f])
      (le_ciSup_of_le (Set.finite_range _).bddAbove true (by simp [f]))
  simp only [hg] at e
  have hL : ¬ BddAbove (Set.range f) := by
    rintro ⟨b, hb⟩
    have := leJ.1 (hb ⟨(ofJ b, true), rfl⟩)
    simp [f] at this
  have hR : ¬ BddAbove (Set.range fun i => toJ (i + 8)) := by
    rintro ⟨b, hb⟩
    have := leJ.1 (hb ⟨ofJ b, rfl⟩)
    simp at this
  rw [iSup, iSup, sSupJ _ hL, sSupJ _ hR, if_pos ⟨((0 : ℕ), false), rfl⟩, if_neg] at e
  · exact absurd (toJ_inj.1 e) (by decide)
  · rintro ⟨i, hi⟩
    exact absurd (toJ_inj.1 hi) (by omega)

theorem finU : Finite Unit := inferInstance
theorem infN : Infinite ℕ := inferInstance
def fintU : Fintype Unit := inferInstance

/-- Copy of Probe1.notWF: a descending sequence refutes well-foundedness. -/
theorem notWF {β : Type*} {r : β → β → Prop} (f : ℕ → β) (hf : ∀ n, r (f (n+1)) (f n)) :
    ¬ WellFounded r := by
  intro h
  obtain ⟨m, ⟨n, rfl⟩, hm⟩ := h.has_min (Set.range f) ⟨f 0, 0, rfl⟩
  exact hm _ ⟨n+1, rfl⟩ (hf n)

/-- A descending sequence from f 0 refutes accessibility of f 0. -/
theorem notAcc {β : Type*} {r : β → β → Prop} (f : ℕ → β) (hf : ∀ n, r (f (n+1)) (f n)) :
    ¬ Acc r (f 0) := by
  suffices ∀ a, Acc r a → ∀ n, f n ≠ a from fun h => this _ h 0 rfl
  intro a ha
  induction ha with
  | intro x _ ih => intro n hn; exact ih _ (hn ▸ hf n) (n + 1) rfl

/-- The relation "1 is below 0" on ℕ: well-founded, but has an element below 0. -/
theorem wf10 : WellFounded (fun a b : ℕ => b = 0 ∧ a = 1) :=
  ⟨fun b => ⟨b, fun a hab => ⟨a, fun c hca => by omega⟩⟩⟩

/-- Strict > restricted to positive elements: no element below 0, not well-founded. -/
theorem nwfPos : ¬ WellFounded (fun a b : ℕ => 0 < b ∧ b < a) :=
  notWF (fun n => n + 1) (fun n => by omega)

/-- On ℕ, the complement of > intersected with ≠ is well-founded. -/
theorem wfGtC : WellFounded ((fun a b : ℕ => a > b)ᶜ ⊓ (· ≠ ·)) :=
  Subrelation.wf (fun {a b} h => lt_of_le_of_ne (not_lt.1 h.1) h.2) wellFounded_lt

/-- On ℕ, the complement of < intersected with ≠ is >, not well-founded. -/
theorem nwfLtC : ¬ WellFounded ((fun a b : ℕ => a < b)ᶜ ⊓ (· ≠ ·)) :=
  notWF (fun n => n) (fun n => ⟨by simp, by simp⟩)

/-- Finsupp single n 1 descends in the Lex order with r = (>) and s = "1 below 0". -/
theorem lexGt10 (n : ℕ) : Finsupp.Lex (· > ·) (fun a b : ℕ => b = 0 ∧ a = 1)
    (Finsupp.single (n + 1) 1) (Finsupp.single n 1) := by
  rw [Finsupp.lex_def]
  refine ⟨n + 1, fun d hd => ?_, by simp⟩
  rw [Finsupp.single_eq_of_ne (by omega), Finsupp.single_eq_of_ne (by omega)]

/-- Finsupp single n 1 descends in the Lex order with r = s = (<). -/
theorem lexLt (n : ℕ) : Finsupp.Lex (· < ·) (· < ·)
    (Finsupp.single (n + 1) 1 : ℕ →₀ ℕ) (Finsupp.single n 1) := by
  rw [Finsupp.lex_def]
  refine ⟨n, fun d hd => ?_, by simp⟩
  rw [Finsupp.single_eq_of_ne (by omega), Finsupp.single_eq_of_ne (by omega)]

/-- Finsupp single () (n+1) descends for s = nwfPos relation over Unit, when r () () fails. -/
theorem lexPos (r : Unit → Unit → Prop) (hr : ∀ d, ¬ r d ()) (n : ℕ) :
    Finsupp.Lex r (fun a b : ℕ => 0 < b ∧ b < a)
    (Finsupp.single () (n + 2)) (Finsupp.single () (n + 1)) := by
  rw [Finsupp.lex_def]
  exact ⟨(), fun d hd => (hr d hd).elim, by simp⟩

end W2c3

open W2c3


namespace W2c3

/-- The element 1 of (Fin 2)ᵒᵈ, which lies below the zero (= toDual 0, the top). -/
def tD : (Fin 2)ᵒᵈ := OrderDual.toDual 1

theorem tD_lt : tD < 0 := by decide

/-- Indicator of range n with value tD: a pointwise descending chain in ℕ →₀ (Fin 2)ᵒᵈ. -/
noncomputable def dch (n : ℕ) : ℕ →₀ (Fin 2)ᵒᵈ := Finsupp.indicator (Finset.range n) (fun _ _ => tD)

theorem dch_apply (n k : ℕ) : dch n k = if k < n then tD else 0 := by
  simp [dch, Finsupp.indicator_apply]

theorem dch_lt (n : ℕ) : dch (n + 1) < dch n := by
  refine lt_of_le_not_ge (Finsupp.le_def.2 fun k => ?_) (fun hh => ?_)
  · rw [dch_apply, dch_apply]; split_ifs <;> first | exact le_rfl | exact tD_lt.le | omega
  · have := Finsupp.le_def.1 hh n
    rw [dch_apply, dch_apply, if_neg (lt_irrefl n), if_pos (Nat.lt_succ_self n)] at this
    exact absurd this (not_le.2 tD_lt)

/-- single () (-n) descends pointwise in Unit →₀ ℤ. -/
theorem zch_lt (n : ℕ) : Finsupp.single () (-((n + 1 : ℕ) : ℤ)) < Finsupp.single () (-(n : ℤ)) := by
  have key : -((n + 1 : ℕ) : ℤ) < -(n : ℤ) := by omega
  exact lt_of_le_not_ge (Finsupp.single_le_single.2 key.le) (fun hh => absurd (Finsupp.single_le_single.1 hh) (not_le.2 key))

/-- single () (1/(n+1)) descends pointwise in Unit →₀ ℚ≥0. -/
theorem qch_lt (n : ℕ) : Finsupp.single () (1 / (((n + 1 : ℕ) : ℚ≥0) + 1)) < Finsupp.single () (1 / ((n : ℚ≥0) + 1)) := by
  have key : 1 / (((n + 1 : ℕ) : ℚ≥0) + 1) < 1 / ((n : ℚ≥0) + 1) := by
    gcongr
    push_cast; linarith
  exact lt_of_le_not_ge (Finsupp.single_le_single.2 key.le) (fun hh => absurd (Finsupp.single_le_single.1 hh) (not_le.2 key))

/-- toLex (single (toDual n) tD) descends in Lex (ℕᵒᵈ →₀ (Fin 2)ᵒᵈ). -/
theorem lexD_lt (n : ℕ) : toLex (Finsupp.single (OrderDual.toDual (n + 1)) tD) <
    toLex (Finsupp.single (OrderDual.toDual n) tD) := by
  rw [Finsupp.Lex.lt_iff]
  refine ⟨OrderDual.toDual (n + 1), fun j hj => ?_, ?_⟩
  · have hj' : n + 1 < OrderDual.ofDual j := hj
    simp only [ofLex_toLex]
    rw [Finsupp.single_eq_of_ne, Finsupp.single_eq_of_ne] <;>
      · intro e; have := congrArg OrderDual.ofDual e; (try simp only [OrderDual.ofDual_toDual] at this); omega
  · simp only [ofLex_toLex]
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by simp)]
    exact tD_lt

/-- toColex (single n tD) descends in Colex (ℕ →₀ (Fin 2)ᵒᵈ). -/
theorem colexD_lt (n : ℕ) : toColex (Finsupp.single (n + 1) tD) < toColex (Finsupp.single n tD) := by
  rw [Finsupp.Colex.lt_iff]
  refine ⟨n + 1, fun j hj => ?_, ?_⟩
  · simp only [ofColex_toColex]
    rw [Finsupp.single_eq_of_ne (by omega), Finsupp.single_eq_of_ne (by omega)]
  · simp only [ofColex_toColex]
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by omega)]
    exact tD_lt

end W2c3


namespace W2c3

/-! Support for the two gave-up rows (induction_empty_option idx 1, a type-identity question):
without the equivalence hypothesis, the Fintype induction principle is equivalent to
"every Fintype type is literally an iterated Option of PEmpty". -/

universe u

/-- Iterated Option of PEmpty. -/
def OptN : ℕ → Type u
  | 0 => PEmpty
  | n + 1 => Option (OptN n)

instance optNFintype : (n : ℕ) → Fintype (OptN.{u} n)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | n + 1 => @instFintypeOption _ (optNFintype n)

/-- The weakened induction principle forces every Fintype type to be some OptN n. -/
theorem indOpt_to_ident
    (H : ∀ {P : (α : Type u) → [Fintype α] → Prop}, P PEmpty →
      (∀ (α : Type u) [Fintype α], P α → P (Option α)) → ∀ (α : Type u) [Fintype α], P α)
    (α : Type u) [Fintype α] : ∃ n, α = OptN.{u} n :=
  @H (fun α _ => ∃ n, α = OptN.{u} n) ⟨0, rfl⟩ (fun _ _ ⟨n, e⟩ => ⟨n + 1, by subst e; rfl⟩) α _

/-- Conversely, if every Fintype type is some OptN n, the weakened principle holds. -/
theorem ident_to_indOpt (I : ∀ (α : Type u) [Fintype α], ∃ n, α = OptN.{u} n)
    {P : (α : Type u) → [Fintype α] → Prop} (h0 : P PEmpty)
    (hs : ∀ (α : Type u) [Fintype α], P α → P (Option α)) (α : Type u) [inst : Fintype α] : P α := by
  obtain ⟨n, rfl⟩ := I α
  have key : ∀ n, @P (OptN.{u} n) (optNFintype n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact @hs (OptN n) (optNFintype n) ih
  rw [Subsingleton.elim inst (optNFintype n)]
  exact key n

end W2c3

-- `Directed.finite_set_le` idx 2: necessary (alpha = Fin 3 with r = (≠): directed, not transitive, no common bound of univ)
theorem c3_1 : ¬ drop0% Directed.finite_set_le 2 := fun h => by
  obtain ⟨z, hz⟩ := @h (Fin 3) (fun a b => a ≠ b) (Fin 3) _ id ne3_dir Set.univ Set.finite_univ
  exact hz z trivial rfl

-- `Directed.finite_set_le` idx 4: necessary (gamma empty)
theorem c3_2 : ¬ drop0% Directed.finite_set_le 4 := fun h => by
  obtain ⟨z, _⟩ := @h ℕ (· ≤ ·) _ Empty Empty.elim (fun x => x.elim) ∅ Set.finite_empty
  exact z.elim

-- `Directed.finite_set_le` idx 8: necessary (s = univ in ℕ)
theorem c3_3 : ¬ drop0% Directed.finite_set_le 8 := fun h => by
  obtain ⟨z, hz⟩ := @h ℕ (· ≤ ·) _ ℕ _ id directed_id Set.univ
  have := hz (z + 1) trivial
  simp at this

-- `Directed.finite_le` idx 2: necessary (iota = kappa = Fin 3, r = (≠); stated at Sort 1, at Sort 0 it holds)
theorem c3_4 : ¬ ∀ {α : Type} {r : α → α → Prop} {ι κ : Type} [Nonempty ι] [Finite κ] {f : ι → α},
    Directed r f → ∀ (g : κ → ι), ∃ z, ∀ i, r (f (g i)) (f z) := fun h => by
  obtain ⟨z, hz⟩ := @h (Fin 3) (fun a b => a ≠ b) (Fin 3) (Fin 3) _ _ id ne3_dir id
  exact hz z rfl

-- `Directed.finite_le` idx 5: necessary (iota = kappa = False)
theorem c3_5 : ¬ drop0% Directed.finite_le 5 := fun h => by
  obtain ⟨z, _⟩ := @h ℕ (· ≤ ·) _ False False _ False.elim (fun x => x.elim) id
  exact z.elim

-- `Finite.exists_le` idx 3: necessary (iota = False, alpha = Empty)
theorem c3_6 : ¬ drop0% Finite.exists_le 3 := fun h => by
  obtain ⟨M, _⟩ := @h False Empty _ _ ⟨fun a => a.elim⟩ False.elim
  exact M.elim

-- `Finite.exists_le` idx 5: necessary (iota = Bool, alpha = Unit ⊕ Unit; stated at Sort 1)
theorem c3_7 : ¬ ∀ {ι : Type} {α : Type} [Finite ι] [Nonempty α] [inst : Preorder α] (f : ι → α),
    ∃ M, ∀ i, f i ≤ M := fun h => by
  obtain ⟨M, hM⟩ := @h Bool (Unit ⊕ Unit) _ _ _ (fun b => if b then Sum.inl () else Sum.inr ())
  exact uu_nd ⟨M, hM true, hM false⟩

-- `Finite.exists_ge` idx 2: necessary (iota = ℕ, alpha = ℤ, f n = -n; stated at Sort 1)
theorem c3_8 : ¬ ∀ {ι : Type} {α : Type} [Nonempty α] [inst : Preorder α] [IsCodirectedOrder α] (f : ι → α),
    ∃ M, ∀ i, M ≤ f i := fun h => by
  obtain ⟨M, hM⟩ := @h ℕ ℤ _ _ _ (fun n => -(n : ℤ))
  have : M ≤ -((M.natAbs + 1 : ℕ) : ℤ) := hM _
  omega

-- `Finite.exists_ge` idx 3: necessary (iota = False, alpha = Empty)
theorem c3_9 : ¬ drop0% Finite.exists_ge 3 := fun h => by
  obtain ⟨M, _⟩ := @h False Empty _ _ ⟨fun a => a.elim⟩ False.elim
  exact M.elim

-- `Finite.exists_ge` idx 5: necessary (iota = Bool, alpha = Unit ⊕ Unit; stated at Sort 1)
theorem c3_10 : ¬ ∀ {ι : Type} {α : Type} [Finite ι] [Nonempty α] [inst : Preorder α] (f : ι → α),
    ∃ M, ∀ i, M ≤ f i := fun h => by
  obtain ⟨M, hM⟩ := @h Bool (Unit ⊕ Unit) _ _ _ (fun b => if b then Sum.inl () else Sum.inr ())
  exact uu_ncd ⟨M, hM true, hM false⟩

-- `Set.Finite.exists_le` idx 1: necessary (alpha = Empty)
theorem c3_11 : ¬ drop0% Set.Finite.exists_le 1 := fun h => by
  obtain ⟨M, _⟩ := @h Empty _ ⟨fun a => a.elim⟩ ∅ Set.finite_empty
  exact M.elim

-- `Set.Finite.exists_le` idx 3: necessary (alpha = Unit ⊕ Unit, s = univ)
theorem c3_12 : ¬ drop0% Set.Finite.exists_le 3 := fun h => by
  obtain ⟨M, hM⟩ := @h (Unit ⊕ Unit) _ _ Set.univ Set.finite_univ
  exact uu_nd ⟨M, hM _ trivial, hM _ trivial⟩

-- `Set.Finite.exists_le` idx 5: necessary (alpha = ℕ, s = univ)
theorem c3_13 : ¬ drop0% Set.Finite.exists_le 5 := fun h => by
  obtain ⟨M, hM⟩ := @h ℕ _ _ _ Set.univ
  have := hM (M + 1) trivial
  simp at this

-- `Set.Finite.exists_ge` idx 1: necessary (alpha = Empty)
theorem c3_14 : ¬ drop0% Set.Finite.exists_ge 1 := fun h => by
  obtain ⟨M, _⟩ := @h Empty _ ⟨fun a => a.elim⟩ ∅ Set.finite_empty
  exact M.elim

-- `Set.Finite.exists_ge` idx 5: necessary (alpha = ℤ, s = univ)
theorem c3_15 : ¬ drop0% Set.Finite.exists_ge 5 := fun h => by
  obtain ⟨M, hM⟩ := @h ℤ _ _ _ Set.univ
  have := hM (M - 1) trivial
  omega

-- `Finite.bddAbove_range` idx 3: necessary (iota = False, alpha = Empty)
theorem c3_16 : ¬ drop0% Finite.bddAbove_range 3 := fun h => by
  obtain ⟨M, _⟩ := @h False Empty _ _ ⟨fun a => a.elim⟩ False.elim
  exact M.elim

-- `Finite.bddAbove_range` idx 5: necessary (iota = Bool, alpha = Unit ⊕ Unit; stated at Sort 1)
theorem c3_17 : ¬ ∀ {ι : Type} {α : Type} [Finite ι] [Nonempty α] [inst : Preorder α] (f : ι → α),
    BddAbove (Set.range f) := fun h => by
  obtain ⟨M, hM⟩ := @h Bool (Unit ⊕ Unit) _ _ _ (fun b => if b then Sum.inl () else Sum.inr ())
  exact uu_nd ⟨M, hM ⟨true, rfl⟩, hM ⟨false, rfl⟩⟩

-- `Finite.bddBelow_range` idx 2: necessary (iota = ℕ, alpha = ℤ, f n = -n; stated at Sort 1)
theorem c3_18 : ¬ ∀ {ι : Type} {α : Type} [Nonempty α] [inst : Preorder α] [IsCodirectedOrder α] (f : ι → α),
    BddBelow (Set.range f) := fun h => by
  obtain ⟨M, hM⟩ := @h ℕ ℤ _ _ _ (fun n => -(n : ℤ))
  have : M ≤ -((M.natAbs + 1 : ℕ) : ℤ) := hM ⟨_, rfl⟩
  omega

-- `Finite.bddBelow_range` idx 3: necessary (iota = False, alpha = Empty)
theorem c3_19 : ¬ drop0% Finite.bddBelow_range 3 := fun h => by
  obtain ⟨M, _⟩ := @h False Empty _ _ ⟨fun a => a.elim⟩ False.elim
  exact M.elim

-- `Finite.bddBelow_range` idx 5: necessary (iota = Bool, alpha = Unit ⊕ Unit; stated at Sort 1)
theorem c3_20 : ¬ ∀ {ι : Type} {α : Type} [Finite ι] [Nonempty α] [inst : Preorder α] (f : ι → α),
    BddBelow (Set.range f) := fun h => by
  obtain ⟨M, hM⟩ := @h Bool (Unit ⊕ Unit) _ _ _ (fun b => if b then Sum.inl () else Sum.inr ())
  exact uu_ncd ⟨M, hM ⟨true, rfl⟩, hM ⟨false, rfl⟩⟩

-- `le_iSup_iff_of_directed` idx 5: necessary (iota = False, alpha = Prop, a = bottom)
theorem c3_21 : ¬ drop0% le_iSup_iff_of_directed 5 := fun h => by
  have := (@h False Prop _ ⊥ False.elim _ (fun x => x.elim)).1 bot_le
  obtain ⟨i, _⟩ := this
  exact i

-- `le_iSup_iff_of_directed` idx 6: necessary (iota = ℕ, alpha = Set ℕ, f n = Iio n, a = univ; stated at Sort 1)
theorem c3_22 : ¬ ∀ {ι : Type} {α : Type} [inst : CompleteLattice α] {a : α} {f : ι → α} [Nonempty ι],
    Directed (fun (x1 x2 : α) => x1 ≤ x2) f → (a ≤ ⨆ (i : ι), f i ↔ ∃ (i : ι), a ≤ f i) := fun h => by
  obtain ⟨i, hi⟩ := (@h ℕ (Set ℕ) _ Set.univ (fun n => Set.Iio n) _ iio_dir).1 (by
    intro x _; simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_Iio]; exact ⟨x + 1, by omega⟩)
  have := hi (Set.mem_univ i)
  simp at this

-- `le_iSup_iff_of_directed` idx 7: necessary (iota = Bool, alpha = Set Bool, f b = {b}, a = univ; stated at Sort 1)
theorem c3_23 : ¬ ∀ {ι : Type} {α : Type} [inst : CompleteLattice α] {a : α} {f : ι → α} [Nonempty ι] [Finite ι],
    a ≤ ⨆ (i : ι), f i ↔ ∃ (i : ι), a ≤ f i := fun h => by
  obtain ⟨i, hi⟩ := (@h Bool (Set Bool) _ Set.univ (fun b => {b}) _ _).1 (by
    intro x _; simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_singleton_iff]; exact ⟨x, rfl⟩)
  have := hi (Set.mem_univ (!i))
  cases i <;> simp at this

-- `le_sSup_iff_of_directedOn` idx 5: necessary (s = range Iio in Set ℕ, a = univ)
theorem c3_24 : ¬ drop0% le_sSup_iff_of_directedOn 5 := fun h => by
  obtain ⟨b, ⟨i, rfl⟩, hi⟩ := (@h (Set ℕ) _ (Set.range fun n => Set.Iio n) Set.univ
    ⟨_, ⟨0, rfl⟩⟩ (directedOn_range.mpr iio_dir)).1 (by
      intro x _; simp only [Set.sSup_eq_sUnion, Set.mem_sUnion, Set.mem_range]
      exact ⟨_, ⟨x + 1, rfl⟩, by simp⟩)
  have := hi (Set.mem_univ i)
  simp at this

-- `le_sSup_iff_of_directedOn` idx 6: necessary (s = {{true}, {false}} in Set Bool, a = univ)
theorem c3_25 : ¬ drop0% le_sSup_iff_of_directedOn 6 := fun h => by
  obtain ⟨b, hb, hi⟩ := (@h (Set Bool) _ {{true}, {false}} Set.univ
    ⟨_, Or.inl rfl⟩ (by simp)).1 (by
      intro x _; simp only [Set.sSup_eq_sUnion, Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff]
      cases x
      · exact ⟨_, Or.inr rfl, rfl⟩
      · exact ⟨_, Or.inl rfl, rfl⟩)
  rcases hb with rfl | rfl
  · exact absurd (hi (Set.mem_univ false)) (by simp)
  · exact absurd (hi (Set.mem_univ true)) (by simp)

-- `Set.subset_iUnion_iff_of_directed` idx 4: necessary (iota = False, s = ∅ in Set Unit)
theorem c3_26 : ¬ drop0% Set.subset_iUnion_iff_of_directed 4 := fun h => by
  have := (@h False Unit ∅ False.elim _ (fun x => x.elim)).1 (Set.empty_subset _)
  obtain ⟨i, _⟩ := this
  exact i

-- `Set.subset_iUnion_iff_of_directed` idx 5: necessary (iota = ℕ, f n = Iio n, s = univ; stated at Sort 1)
theorem c3_27 : ¬ ∀ {ι : Type} {α : Type} {s : Set α} {f : ι → Set α} [Nonempty ι],
    Directed (fun (x1 x2 : Set α) => x1 ⊆ x2) f → (s ⊆ ⋃ (i : ι), f i ↔ ∃ (i : ι), s ⊆ f i) := fun h => by
  obtain ⟨i, hi⟩ := (@h ℕ ℕ Set.univ (fun n => Set.Iio n) _ iio_dir).1 (by
    intro x _; simp only [Set.mem_iUnion, Set.mem_Iio]; exact ⟨x + 1, by omega⟩)
  have := hi (Set.mem_univ i)
  simp at this

-- `Set.subset_iUnion_iff_of_directed` idx 6: necessary (iota = Bool, f b = {b}, s = univ; stated at Sort 1)
theorem c3_28 : ¬ ∀ {ι : Type} {α : Type} {s : Set α} {f : ι → Set α} [Nonempty ι] [Finite ι],
    s ⊆ ⋃ (i : ι), f i ↔ ∃ (i : ι), s ⊆ f i := fun h => by
  obtain ⟨i, hi⟩ := (@h Bool Bool Set.univ (fun b => {b}) _ _).1 (by
    intro x _; simp only [Set.mem_iUnion, Set.mem_singleton_iff]; exact ⟨x, rfl⟩)
  have := hi (Set.mem_univ (!i))
  cases i <;> simp at this

-- `Set.subset_sUnion_iff_of_directed` idx 3: necessary (S = ∅, s = ∅)
theorem c3_29 : ¬ drop0% Set.subset_sUnion_iff_of_directed 3 := fun h => by
  obtain ⟨t, ht, _⟩ := (@h Unit ∅ ∅ Set.finite_empty (fun x hx => hx.elim)).1 (Set.empty_subset _)
  exact ht

-- `Set.subset_sUnion_iff_of_directed` idx 4: necessary (S = range Iio in Set ℕ, s = univ)
theorem c3_30 : ¬ drop0% Set.subset_sUnion_iff_of_directed 4 := fun h => by
  obtain ⟨b, ⟨i, rfl⟩, hi⟩ := (@h ℕ (Set.range fun n => Set.Iio n) Set.univ
    ⟨_, ⟨0, rfl⟩⟩ (directedOn_range.mpr iio_dir)).1 (by
      intro x _; simp only [Set.sSup_eq_sUnion, Set.mem_sUnion, Set.mem_range]
      exact ⟨_, ⟨x + 1, rfl⟩, by simp⟩)
  have := hi (Set.mem_univ i)
  simp at this

-- `Set.subset_sUnion_iff_of_directed` idx 5: necessary (S = {{true}, {false}}, s = univ)
theorem c3_31 : ¬ drop0% Set.subset_sUnion_iff_of_directed 5 := fun h => by
  obtain ⟨b, hb, hi⟩ := (@h Bool {{true}, {false}} Set.univ
    ⟨_, Or.inl rfl⟩ (by simp)).1 (by
      intro x _; simp only [Set.sSup_eq_sUnion, Set.mem_sUnion, Set.mem_insert_iff, Set.mem_singleton_iff]
      cases x
      · exact ⟨_, Or.inr rfl, rfl⟩
      · exact ⟨_, Or.inl rfl, rfl⟩)
  rcases hb with rfl | rfl
  · exact absurd (hi (Set.mem_univ false)) (by simp)
  · exact absurd (hi (Set.mem_univ true)) (by simp)

-- `Finite.ciInf_le_of_le` idx 2: necessary (ℤ, f n = -n: junk iInf 0 > f 1)
theorem c3_32 : ¬ drop0% Finite.ciInf_le_of_le 2 := fun h => by
  have := @h ℤ ℕ _ (-1) (fun n => -(n : ℤ)) 1 (by simp)
  rw [zinf_unb _ (fun n => le_refl _)] at this
  omega

-- `Finite.ciSup_mono` idx 2: necessary (ℤ, f = 1, g n = n + 1: junk iSup g = 0)
theorem c3_33 : ¬ drop0% Finite.ciSup_mono 2 := fun h => by
  have := @h ℤ ℕ _ (fun _ => 1) (fun n => (n : ℤ) + 1) (fun x => show (1 : ℤ) ≤ x + 1 by omega)
  rw [zsup_unb _ (fun n => show (n : ℤ) ≤ n + 1 by omega), ciSup_const] at this
  omega

-- `Finite.ciInf_mono` idx 2: necessary (ℤ, f n = -n - 1, g = -1: junk iInf f = 0)
theorem c3_34 : ¬ drop0% Finite.ciInf_mono 2 := fun h => by
  have := @h ℤ ℕ _ (fun n => -(n : ℤ) - 1) (fun _ => -1) (fun x => show -(x : ℤ) - 1 ≤ -1 by omega)
  rw [zinf_unb _ (fun n => show -(n : ℤ) - 1 ≤ -n by omega), ciInf_const] at this
  omega

-- `Finite.ciInf_le` idx 2: necessary (ℤ, f n = -n, i = 1)
theorem c3_35 : ¬ drop0% Finite.ciInf_le 2 := fun h => by
  have := @h ℤ ℕ _ (fun n => -(n : ℤ)) 1
  rw [zinf_unb _ (fun n => le_refl _)] at this
  simp at this

-- `Finite.ciSup_sup` idx 2: necessary (ℤ, f n = n, a = 1)
theorem c3_36 : ¬ drop0% Finite.ciSup_sup 2 := fun h => by
  have := @h ℤ ℕ _ _ (fun n => (n : ℤ)) 1
  rw [zsup_unb _ (fun n => le_refl _), zsup_unb _ (fun n => le_sup_left)] at this
  simp at this

-- `Finite.ciSup_sup` idx 4: necessary (iota = Empty, ℤ, a = 1)
theorem c3_37 : ¬ drop0% Finite.ciSup_sup 4 := fun h => by
  have := @h ℤ Empty _ _ Empty.elim 1
  rw [zsup_empty, zsup_empty] at this
  simp at this

-- `Finite.ciInf_inf` idx 2: necessary (ℤ, f n = -n, a = -1)
theorem c3_38 : ¬ drop0% Finite.ciInf_inf 2 := fun h => by
  have := @h ℤ ℕ _ _ (fun n => -(n : ℤ)) (-1)
  rw [zinf_unb _ (fun n => le_refl _), zinf_unb _ (fun n => inf_le_left)] at this
  simp at this

-- `Finite.ciInf_inf` idx 4: necessary (iota = Empty, ℤ, a = -1)
theorem c3_39 : ¬ drop0% Finite.ciInf_inf 4 := fun h => by
  have := @h ℤ Empty _ _ Empty.elim (-1)
  rw [zinf_empty, zinf_empty] at this
  simp at this

-- `Finite.ciSup_prod` idx 4: necessary (ℤ, iota = Bool, iota' = ℕ, f (b, n) = if b then n else 1)
theorem c3_40 : ¬ drop0% Finite.ciSup_prod 4 := fun h => by
  have e := @h ℤ Bool ℕ _ _ (fun p => if p.1 then (p.2 : ℤ) else 1)
  have hL : ⨆ a : Bool × ℕ, (if a.1 then (a.2 : ℤ) else 1) = 0 :=
    Int.csSup_of_not_bddAbove (by
      rintro ⟨b, hb⟩
      have : ((b.toNat + 1 : ℕ) : ℤ) ≤ b := hb ⟨(true, b.toNat + 1), by simp⟩
      omega)
  rw [hL, zsupB] at e
  simp only [Bool.false_eq_true, ite_false, ciSup_const, ite_true] at e
  omega

-- `Finite.ciInf_prod` idx 3: necessary (alpha = J order dual, junk sSup of J as in Probe1 p1_44)
theorem c3_41 : ¬ drop0% Finite.ciInf_prod 3 := fun h =>
  jprod (fun {α ι ι'} _ _ f => @h αᵒᵈ ι ι' _ _ f)

-- `Finite.ciInf_prod` idx 4: necessary (ℤ, iota = Bool, iota' = ℕ, f (b, n) = if b then -n else -1)
theorem c3_42 : ¬ drop0% Finite.ciInf_prod 4 := fun h => by
  have e := @h ℤ Bool ℕ _ _ (fun p => if p.1 then -(p.2 : ℤ) else -1)
  have hL : ⨅ a : Bool × ℕ, (if a.1 then -(a.2 : ℤ) else -1) = 0 :=
    Int.csInf_of_not_bddBelow (by
      rintro ⟨b, hb⟩
      have : b ≤ -((b.natAbs + 1 : ℕ) : ℤ) := hb ⟨(true, b.natAbs + 1), by simp⟩
      omega)
  rw [hL, zinfB] at e
  simp only [Bool.false_eq_true, ite_false, ciInf_const, ite_true] at e
  omega

-- `Finite.map_iSup_of_monotoneOn` idx 5: necessary (ℤ, iota = ℕ, f unbounded, g = (fun x : ℤ => x + 1): junk values differ)
theorem c3_43 : ¬ drop0% Finite.map_iSup_of_monotoneOn 5 := fun h => by
  have := @h ℤ ℤ ℕ _ _ _ Set.univ (fun n : ℕ => (n : ℤ)) (fun x : ℤ => x + 1) (fun a _ b _ hab => by first | omega | (simp only; omega)) (fun _ => trivial)
  beta_reduce at this
  rw [zsup_unb _ (fun n => le_refl _), zsup_unb _ (fun n => by first | omega | (simp only; omega))] at this
  simp at this

-- `Finite.map_iSup_of_monotoneOn` idx 6: necessary (iota = Empty, ℤ, g = (fun x : ℤ => x + 1))
theorem c3_44 : ¬ drop0% Finite.map_iSup_of_monotoneOn 6 := fun h => by
  have := @h ℤ ℤ Empty _ _ _ Set.univ Empty.elim (fun x : ℤ => x + 1) (fun a _ b _ hab => by first | omega | (simp only; omega)) (fun _ => trivial)
  rw [zsup_empty, zsup_empty] at this
  simp at this

-- `Finite.map_iSup_of_monotoneOn` idx 10: necessary (iota = Bool, f = 1/0, g = (fun x : ℤ => -x) of the wrong monotonicity)
theorem c3_45 : ¬ drop0% Finite.map_iSup_of_monotoneOn 10 := fun h => by
  have := @h ℤ ℤ Bool _ _ _ _ Set.univ (fun b : Bool => if b then (1 : ℤ) else 0) (fun x : ℤ => -x) (fun _ => trivial)
  rw [zsupB, zsupB] at this
  simp at this

-- `Finite.map_iSup_of_monotoneOn` idx 11: necessary (s = ∅, iota = Bool, f = 1/0, g = (fun x : ℤ => -x))
theorem c3_46 : ¬ drop0% Finite.map_iSup_of_monotoneOn 11 := fun h => by
  have := @h ℤ ℤ Bool _ _ _ _ ∅ (fun b : Bool => if b then (1 : ℤ) else 0) (fun x : ℤ => -x) (fun a ha => ha.elim)
  rw [zsupB, zsupB] at this
  simp at this

-- `Finite.map_iSup_of_monotone` idx 5: necessary (ℤ, iota = ℕ, f unbounded, g = (fun x : ℤ => x + 1): junk values differ)
theorem c3_47 : ¬ drop0% Finite.map_iSup_of_monotone 5 := fun h => by
  have := @h ℤ ℤ ℕ _ _ _ (fun n : ℕ => (n : ℤ)) (fun x : ℤ => x + 1) (fun a b hab => by first | omega | (simp only; omega))
  beta_reduce at this
  rw [zsup_unb _ (fun n => le_refl _), zsup_unb _ (fun n => by first | omega | (simp only; omega))] at this
  simp at this

-- `Finite.map_iSup_of_monotone` idx 6: necessary (iota = Empty, ℤ, g = (fun x : ℤ => x + 1))
theorem c3_48 : ¬ drop0% Finite.map_iSup_of_monotone 6 := fun h => by
  have := @h ℤ ℤ Empty _ _ _ Empty.elim (fun x : ℤ => x + 1) (fun a b hab => by first | omega | (simp only; omega))
  rw [zsup_empty, zsup_empty] at this
  simp at this

-- `Finite.map_iSup_of_monotone` idx 9: necessary (iota = Bool, f = 1/0, g = (fun x : ℤ => -x) of the wrong monotonicity)
theorem c3_49 : ¬ drop0% Finite.map_iSup_of_monotone 9 := fun h => by
  have := @h ℤ ℤ Bool _ _ _ _ (fun b : Bool => if b then (1 : ℤ) else 0) (fun x : ℤ => -x)
  rw [zsupB, zsupB] at this
  simp at this

-- `Finite.map_iSup_of_antitoneOn` idx 5: necessary (ℤ, iota = ℕ, f unbounded, g = (fun x : ℤ => -x - 1): junk values differ)
theorem c3_50 : ¬ drop0% Finite.map_iSup_of_antitoneOn 5 := fun h => by
  have := @h ℤ ℤ ℕ _ _ _ Set.univ (fun n : ℕ => (n : ℤ)) (fun x : ℤ => -x - 1) (fun a _ b _ hab => by first | omega | (simp only; omega)) (fun _ => trivial)
  beta_reduce at this
  rw [zsup_unb _ (fun n => le_refl _), zinf_unb _ (fun n => by first | omega | (simp only; omega))] at this
  simp at this

-- `Finite.map_iSup_of_antitoneOn` idx 6: necessary (iota = Empty, ℤ, g = (fun x : ℤ => -x + 1))
theorem c3_51 : ¬ drop0% Finite.map_iSup_of_antitoneOn 6 := fun h => by
  have := @h ℤ ℤ Empty _ _ _ Set.univ Empty.elim (fun x : ℤ => -x + 1) (fun a _ b _ hab => by first | omega | (simp only; omega)) (fun _ => trivial)
  rw [zsup_empty, zinf_empty] at this
  simp at this

-- `Finite.map_iSup_of_antitoneOn` idx 10: necessary (iota = Bool, f = 1/0, g = (fun x : ℤ => x) of the wrong monotonicity)
theorem c3_52 : ¬ drop0% Finite.map_iSup_of_antitoneOn 10 := fun h => by
  have := @h ℤ ℤ Bool _ _ _ _ Set.univ (fun b : Bool => if b then (1 : ℤ) else 0) (fun x : ℤ => x) (fun _ => trivial)
  rw [zsupB, zinfB] at this
  simp at this

-- `Finite.map_iSup_of_antitoneOn` idx 11: necessary (s = ∅, iota = Bool, f = 1/0, g = (fun x : ℤ => x))
theorem c3_53 : ¬ drop0% Finite.map_iSup_of_antitoneOn 11 := fun h => by
  have := @h ℤ ℤ Bool _ _ _ _ ∅ (fun b : Bool => if b then (1 : ℤ) else 0) (fun x : ℤ => x) (fun a ha => ha.elim)
  rw [zsupB, zinfB] at this
  simp at this

-- `Finite.map_iSup_of_antitone` idx 5: necessary (ℤ, iota = ℕ, f unbounded, g = (fun x : ℤ => -x - 1): junk values differ)
theorem c3_54 : ¬ drop0% Finite.map_iSup_of_antitone 5 := fun h => by
  have := @h ℤ ℤ ℕ _ _ _ (fun n : ℕ => (n : ℤ)) (fun x : ℤ => -x - 1) (fun a b hab => by first | omega | (simp only; omega))
  beta_reduce at this
  rw [zsup_unb _ (fun n => le_refl _), zinf_unb _ (fun n => by first | omega | (simp only; omega))] at this
  simp at this

-- `Finite.map_iSup_of_antitone` idx 6: necessary (iota = Empty, ℤ, g = (fun x : ℤ => -x + 1))
theorem c3_55 : ¬ drop0% Finite.map_iSup_of_antitone 6 := fun h => by
  have := @h ℤ ℤ Empty _ _ _ Empty.elim (fun x : ℤ => -x + 1) (fun a b hab => by first | omega | (simp only; omega))
  rw [zsup_empty, zinf_empty] at this
  simp at this

-- `Finite.map_iSup_of_antitone` idx 9: necessary (iota = Bool, f = 1/0, g = (fun x : ℤ => x) of the wrong monotonicity)
theorem c3_56 : ¬ drop0% Finite.map_iSup_of_antitone 9 := fun h => by
  have := @h ℤ ℤ Bool _ _ _ _ (fun b : Bool => if b then (1 : ℤ) else 0) (fun x : ℤ => x)
  rw [zsupB, zinfB] at this
  simp at this

-- `Finite.map_iInf_of_monotoneOn` idx 5: necessary (ℤ, iota = ℕ, f unbounded, g = (fun x : ℤ => x - 1): junk values differ)
theorem c3_57 : ¬ drop0% Finite.map_iInf_of_monotoneOn 5 := fun h => by
  have := @h ℤ ℤ ℕ _ _ _ Set.univ (fun n : ℕ => -(n : ℤ)) (fun x : ℤ => x - 1) (fun a _ b _ hab => by first | omega | (simp only; omega)) (fun _ => trivial)
  beta_reduce at this
  rw [zinf_unb _ (fun n => le_refl _), zinf_unb _ (fun n => by first | omega | (simp only; omega))] at this
  simp at this

-- `Finite.map_iInf_of_monotoneOn` idx 6: necessary (iota = Empty, ℤ, g = (fun x : ℤ => x + 1))
theorem c3_58 : ¬ drop0% Finite.map_iInf_of_monotoneOn 6 := fun h => by
  have := @h ℤ ℤ Empty _ _ _ Set.univ Empty.elim (fun x : ℤ => x + 1) (fun a _ b _ hab => by first | omega | (simp only; omega)) (fun _ => trivial)
  rw [zinf_empty, zinf_empty] at this
  simp at this

-- `Finite.map_iInf_of_monotoneOn` idx 10: necessary (iota = Bool, f = 1/0, g = (fun x : ℤ => -x) of the wrong monotonicity)
theorem c3_59 : ¬ drop0% Finite.map_iInf_of_monotoneOn 10 := fun h => by
  have := @h ℤ ℤ Bool _ _ _ _ Set.univ (fun b : Bool => if b then (1 : ℤ) else 0) (fun x : ℤ => -x) (fun _ => trivial)
  rw [zinfB, zinfB] at this
  simp at this

-- `Finite.map_iInf_of_monotoneOn` idx 11: necessary (s = ∅, iota = Bool, f = 1/0, g = (fun x : ℤ => -x))
theorem c3_60 : ¬ drop0% Finite.map_iInf_of_monotoneOn 11 := fun h => by
  have := @h ℤ ℤ Bool _ _ _ _ ∅ (fun b : Bool => if b then (1 : ℤ) else 0) (fun x : ℤ => -x) (fun a ha => ha.elim)
  rw [zinfB, zinfB] at this
  simp at this

-- `Finite.map_iInf_of_monotone` idx 5: necessary (ℤ, iota = ℕ, f unbounded, g = (fun x : ℤ => x - 1): junk values differ)
theorem c3_61 : ¬ drop0% Finite.map_iInf_of_monotone 5 := fun h => by
  have := @h ℤ ℤ ℕ _ _ _ (fun n : ℕ => -(n : ℤ)) (fun x : ℤ => x - 1) (fun a b hab => by first | omega | (simp only; omega))
  beta_reduce at this
  rw [zinf_unb _ (fun n => le_refl _), zinf_unb _ (fun n => by first | omega | (simp only; omega))] at this
  simp at this

-- `Finite.map_iInf_of_monotone` idx 6: necessary (iota = Empty, ℤ, g = (fun x : ℤ => x + 1))
theorem c3_62 : ¬ drop0% Finite.map_iInf_of_monotone 6 := fun h => by
  have := @h ℤ ℤ Empty _ _ _ Empty.elim (fun x : ℤ => x + 1) (fun a b hab => by first | omega | (simp only; omega))
  rw [zinf_empty, zinf_empty] at this
  simp at this

-- `Finite.map_iInf_of_monotone` idx 9: necessary (iota = Bool, f = 1/0, g = (fun x : ℤ => -x) of the wrong monotonicity)
theorem c3_63 : ¬ drop0% Finite.map_iInf_of_monotone 9 := fun h => by
  have := @h ℤ ℤ Bool _ _ _ _ (fun b : Bool => if b then (1 : ℤ) else 0) (fun x : ℤ => -x)
  rw [zinfB, zinfB] at this
  simp at this

-- `Finite.map_iInf_of_antitoneOn` idx 5: necessary (ℤ, iota = ℕ, f unbounded, g = (fun x : ℤ => -x + 1): junk values differ)
theorem c3_64 : ¬ drop0% Finite.map_iInf_of_antitoneOn 5 := fun h => by
  have := @h ℤ ℤ ℕ _ _ _ Set.univ (fun n : ℕ => -(n : ℤ)) (fun x : ℤ => -x + 1) (fun a _ b _ hab => by first | omega | (simp only; omega)) (fun _ => trivial)
  beta_reduce at this
  rw [zinf_unb _ (fun n => le_refl _), zsup_unb _ (fun n => by first | omega | (simp only; omega))] at this
  simp at this

-- `Finite.map_iInf_of_antitoneOn` idx 6: necessary (iota = Empty, ℤ, g = (fun x : ℤ => -x + 1))
theorem c3_65 : ¬ drop0% Finite.map_iInf_of_antitoneOn 6 := fun h => by
  have := @h ℤ ℤ Empty _ _ _ Set.univ Empty.elim (fun x : ℤ => -x + 1) (fun a _ b _ hab => by first | omega | (simp only; omega)) (fun _ => trivial)
  rw [zinf_empty, zsup_empty] at this
  simp at this

-- `Finite.map_iInf_of_antitoneOn` idx 10: necessary (iota = Bool, f = 1/0, g = (fun x : ℤ => x) of the wrong monotonicity)
theorem c3_66 : ¬ drop0% Finite.map_iInf_of_antitoneOn 10 := fun h => by
  have := @h ℤ ℤ Bool _ _ _ _ Set.univ (fun b : Bool => if b then (1 : ℤ) else 0) (fun x : ℤ => x) (fun _ => trivial)
  rw [zinfB, zsupB] at this
  simp at this

-- `Finite.map_iInf_of_antitoneOn` idx 11: necessary (s = ∅, iota = Bool, f = 1/0, g = (fun x : ℤ => x))
theorem c3_67 : ¬ drop0% Finite.map_iInf_of_antitoneOn 11 := fun h => by
  have := @h ℤ ℤ Bool _ _ _ _ ∅ (fun b : Bool => if b then (1 : ℤ) else 0) (fun x : ℤ => x) (fun a ha => ha.elim)
  rw [zinfB, zsupB] at this
  simp at this

-- `Finite.map_iInf_of_antitone` idx 5: necessary (ℤ, iota = ℕ, f unbounded, g = (fun x : ℤ => -x + 1): junk values differ)
theorem c3_68 : ¬ drop0% Finite.map_iInf_of_antitone 5 := fun h => by
  have := @h ℤ ℤ ℕ _ _ _ (fun n : ℕ => -(n : ℤ)) (fun x : ℤ => -x + 1) (fun a b hab => by first | omega | (simp only; omega))
  beta_reduce at this
  rw [zinf_unb _ (fun n => le_refl _), zsup_unb _ (fun n => by first | omega | (simp only; omega))] at this
  simp at this

-- `Finite.map_iInf_of_antitone` idx 6: necessary (iota = Empty, ℤ, g = (fun x : ℤ => -x + 1))
theorem c3_69 : ¬ drop0% Finite.map_iInf_of_antitone 6 := fun h => by
  have := @h ℤ ℤ Empty _ _ _ Empty.elim (fun x : ℤ => -x + 1) (fun a b hab => by first | omega | (simp only; omega))
  rw [zinf_empty, zsup_empty] at this
  simp at this

-- `Finite.map_iInf_of_antitone` idx 9: necessary (iota = Bool, f = 1/0, g = (fun x : ℤ => x) of the wrong monotonicity)
theorem c3_70 : ¬ drop0% Finite.map_iInf_of_antitone 9 := fun h => by
  have := @h ℤ ℤ Bool _ _ _ _ (fun b : Bool => if b then (1 : ℤ) else 0) (fun x : ℤ => x)
  rw [zinfB, zsupB] at this
  simp at this

-- `exists_seq_of_forall_finset_exists'` idx 3: necessary (alpha = ℕ, P = True, r = (<): no sequence with r both ways)
theorem c3_71 : ¬ drop0% exists_seq_of_forall_finset_exists' 3 := fun h => by
  obtain ⟨f, -, hf⟩ := @h ℕ (fun _ => True) (· < ·) (fun s _ => ⟨s.sup id + 1, trivial, fun x hx => by
    have := Finset.le_sup (f := id) hx; simp only [id] at this; omega⟩)
  have h1 := hf (show (0 : ℕ) ≠ 1 by decide)
  have h2 := hf (show (1 : ℕ) ≠ 0 by decide)
  simp only [Function.onFun] at h1 h2
  omega

-- `Fintype.eq_of_subsingleton_of_sum_eq` idx 3: necessary (iota = Bool, f = 1/0, b = 1)
theorem c3_72 : ¬ drop0% Fintype.eq_of_subsingleton_of_sum_eq 3 := fun h => by
  have := @h ℕ _ Bool Finset.univ (fun b => if b then 1 else 0) 1 (by decide) false (Finset.mem_univ _)
  simp at this

-- `Fintype.eq_of_subsingleton_of_sum_eq` idx 7: necessary (iota = Unit, f = 0, b = 1)
theorem c3_73 : ¬ drop0% Fintype.eq_of_subsingleton_of_sum_eq 7 := fun h => by
  have := @h ℕ _ Unit _ Finset.univ (fun _ => 0) 1 () (Finset.mem_univ _)
  simp at this

-- `Fintype.eq_of_subsingleton_of_prod_eq` idx 3: necessary (iota = Bool, f = 2/1, b = 2)
theorem c3_74 : ¬ drop0% Fintype.eq_of_subsingleton_of_prod_eq 3 := fun h => by
  have := @h ℕ _ Bool Finset.univ (fun b => if b then 2 else 1) 2 (by decide) false (Finset.mem_univ _)
  simp at this

-- `Fintype.eq_of_subsingleton_of_prod_eq` idx 7: necessary (iota = Unit, f = 1, b = 2)
theorem c3_75 : ¬ drop0% Fintype.eq_of_subsingleton_of_prod_eq 7 := fun h => by
  have := @h ℕ _ Unit _ Finset.univ (fun _ => 1) 2 () (Finset.mem_univ _)
  simp at this

-- `Finset.compl_eq_of_disjoint_of_card_add_eq` idx 5: necessary (Fin 2, S1 = S2 = {0})
theorem c3_76 : ¬ drop0% Finset.compl_eq_of_disjoint_of_card_add_eq 5 := fun h => by
  have := @h (Fin 2) _ _ {0} {0} (by decide)
  revert this; decide

-- `Finite.exists_univ_list` idx 1: necessary (alpha = ℕ)
theorem c3_77 : ¬ drop0% Finite.exists_univ_list 1 := fun h => by
  obtain ⟨l, -, hl⟩ := h ℕ
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset l.toFinset
  exact hx (List.mem_toFinset.2 (hl x))

-- `Fintype.existsUnique_notMem_image_of_injective_of_card_eq_add_one` idx 6: necessary (Bool → Fin 3 constant 0)
theorem c3_78 : ¬ drop0% Fintype.existsUnique_notMem_image_of_injective_of_card_eq_add_one 6 := fun h => by
  obtain ⟨x, -, hu⟩ := @h Bool (Fin 3) _ _ _ (fun _ => 0) (by decide)
  have h1 := hu 1 (by decide)
  have h2 := hu 2 (by decide)
  exact absurd (h1.trans h2.symm) (by decide)

-- `Fintype.card_range` idx 4: necessary (constant monotone map Bool → Unit)
theorem c3_79 : ¬ drop0% Fintype.card_range 4 := fun h => by
  have := @h Bool Unit (Bool →o Unit) _ ⟨fun _ => (), fun _ _ _ => le_rfl⟩ _ _
  have h1 : Fintype.card (Set.range (⇑(⟨fun _ => (), fun _ _ _ => le_rfl⟩ : Bool →o Unit))) ≤ 1 :=
    Fintype.card_le_one_iff.2 (fun a b => Subtype.ext (Subsingleton.elim _ _))
  rw [this] at h1
  simp at h1

-- `Fintype.card_pos` idx 2: necessary (alpha = Empty)
theorem c3_80 : ¬ drop0% Fintype.card_pos 2 := fun h => by
  have := @h Empty _
  simp at this

-- `Fintype.card_ne_zero` idx 2: necessary (alpha = Empty)
theorem c3_81 : ¬ drop0% Fintype.card_ne_zero 2 := fun h => by
  have := @h Empty _
  simp at this

-- `Fintype.instNeZeroNatCardOfNonempty` idx 2: necessary (alpha = Empty)
theorem c3_82 : ¬ drop0% Fintype.instNeZeroNatCardOfNonempty 2 := fun h => by
  have := (@h Empty _).out
  simp at this

-- `Finite.surjective_of_injective` idx 1: necessary (succ on ℕ)
theorem c3_83 : ¬ drop0% Finite.surjective_of_injective 1 := fun h => by
  obtain ⟨n, hn⟩ := @h ℕ Nat.succ Nat.succ_injective 0
  omega

-- `Finite.injective_iff_surjective` idx 1: necessary (succ on ℕ)
theorem c3_84 : ¬ drop0% Finite.injective_iff_surjective 1 := fun h => by
  obtain ⟨n, hn⟩ := (@h ℕ Nat.succ).1 Nat.succ_injective 0
  omega

-- `Finite.injective_iff_bijective` idx 1: necessary (succ on ℕ)
theorem c3_85 : ¬ drop0% Finite.injective_iff_bijective 1 := fun h => by
  obtain ⟨n, hn⟩ := ((@h ℕ Nat.succ).1 Nat.succ_injective).2 0
  omega

-- `Finite.surjective_iff_bijective` idx 1: necessary (pred on ℕ)
theorem c3_86 : ¬ drop0% Finite.surjective_iff_bijective 1 := fun h => by
  have hi := ((@h ℕ Nat.pred).1 (fun n => ⟨n + 1, rfl⟩)).1
  have := @hi 0 1 rfl
  omega

-- `Finite.injective_iff_surjective_of_equiv` idx 2: necessary (succ on ℕ, e = refl)
theorem c3_87 : ¬ drop0% Finite.injective_iff_surjective_of_equiv 2 := fun h => by
  obtain ⟨n, hn⟩ := (@h ℕ ℕ Nat.succ (Equiv.refl ℕ)).1 Nat.succ_injective 0
  omega

-- `Function.Injective.bijective_of_finite` idx 1: necessary (succ on ℕ)
theorem c3_88 : ¬ drop0% Function.Injective.bijective_of_finite 1 := fun h => by
  obtain ⟨n, hn⟩ := (@h ℕ Nat.succ Nat.succ_injective).2 0
  omega

-- `Function.Surjective.bijective_of_finite` idx 1: necessary (pred on ℕ)
theorem c3_89 : ¬ drop0% Function.Surjective.bijective_of_finite 1 := fun h => by
  have hi := (@h ℕ Nat.pred (fun n => ⟨n + 1, rfl⟩)).1
  have := @hi 0 1 rfl
  omega

-- `Function.Injective.surjective_of_finite` idx 2: necessary (succ on ℕ, e = refl)
theorem c3_90 : ¬ drop0% Function.Injective.surjective_of_finite 2 := fun h => by
  obtain ⟨n, hn⟩ := @h ℕ ℕ Nat.succ (Equiv.refl ℕ) Nat.succ_injective 0
  omega

-- `Function.Surjective.injective_of_finite` idx 2: necessary (pred on ℕ, e = refl)
theorem c3_91 : ¬ drop0% Function.Surjective.injective_of_finite 2 := fun h => by
  have hi := @h ℕ ℕ Nat.pred (Equiv.refl ℕ) (fun n => ⟨n + 1, rfl⟩)
  have := @hi 0 1 rfl
  omega

-- `Fintype.card_compl_eq_card_compl` idx 1: removable (Finite alpha follows from the Fintype instances of {x // p x} and {x // ¬p x}, alpha ≃ their sum)
theorem c3_92 : drop% Fintype.card_compl_eq_card_compl 1 := by
  intro α p q _ _ _ _ h
  classical
  have : Finite α := Finite.of_equiv _ (Equiv.sumCompl p)
  exact Fintype.card_compl_eq_card_compl p q h

-- `Finite.wellFounded_of_trans_of_irrefl` idx 1: necessary (ℕ with >)
theorem c3_93 : ¬ drop0% Finite.wellFounded_of_trans_of_irrefl 1 := fun h => by
  obtain ⟨n, -, hn⟩ := (@h ℕ (· > ·) _ _).has_min Set.univ ⟨0, trivial⟩
  exact hn (n + 1) trivial (Nat.lt_succ_self n)

-- `Finite.wellFounded_of_trans_of_irrefl` idx 3: necessary (Bool with ≠: irreflexive, not transitive, cyclic)
theorem c3_94 : ¬ drop0% Finite.wellFounded_of_trans_of_irrefl 3 := fun h => by
  obtain ⟨a, -, ha⟩ := (@h Bool _ (· ≠ ·) ⟨fun a h => h rfl⟩).has_min Set.univ ⟨true, trivial⟩
  exact ha (!a) trivial (by cases a <;> decide)

-- `Finite.wellFounded_of_trans_of_irrefl` idx 4: necessary (Unit with the total relation)
theorem c3_95 : ¬ drop0% Finite.wellFounded_of_trans_of_irrefl 4 := fun h => by
  obtain ⟨a, -, ha⟩ := (@h Unit _ (fun _ _ => True) ⟨fun _ _ _ _ _ => trivial⟩).has_min Set.univ ⟨(), trivial⟩
  exact ha a trivial trivial

-- `Finite.to_wellFoundedGT` idx 1: necessary (ℕ)
theorem c3_96 : ¬ drop0% Finite.to_wellFoundedGT 1 := fun h => by
  obtain ⟨n, -, hn⟩ := (@wellFounded_gt ℕ _ (@h ℕ _)).has_min Set.univ ⟨0, trivial⟩
  exact hn (n + 1) trivial (Nat.lt_succ_self n)

-- `Finite.to_wellFoundedLT` idx 1: necessary (ℤ)
theorem c3_97 : ¬ drop0% Finite.to_wellFoundedLT 1 := fun h => by
  obtain ⟨n, -, hn⟩ := (@wellFounded_lt ℤ _ (@h ℤ _)).has_min Set.univ ⟨0, trivial⟩
  exact hn (n - 1) trivial (by omega)

-- `Fintype.induction_subsingleton_or_nontrivial` idx 3: necessary (P = False; the step holds via a smaller Unit)
theorem c3_98 : ¬ drop0% Fintype.induction_subsingleton_or_nontrivial 3 := fun h =>
  @h (fun _ _ => False) Unit _ (fun α _ _ ih => ih Unit (by
    have := @Fintype.one_lt_card α _ _
    simpa using this))

-- `Fintype.induction_subsingleton_or_nontrivial` idx 4: necessary (P = Subsingleton, alpha = Bool)
theorem c3_99 : ¬ drop0% Fintype.induction_subsingleton_or_nontrivial 4 := fun h => by
  have := @h (fun α _ => Subsingleton α) Bool _ (fun α _ hs => hs)
  exact absurd (this.elim true false) (by decide)

-- `Fin.cast_eq_cast'` idx 2: necessary (Fin 0 ≠ Fin 1)
theorem c3_100 : ¬ indep0% Fin.cast_eq_cast' 2 := fun h =>
  (cast (@h 1 0) (0 : Fin 1)).elim0

-- `Fintype.card_embedding_eq_of_infinite` idx 2: necessary (alpha = beta = Unit)
theorem c3_101 : ¬ drop0% Fintype.card_embedding_eq_of_infinite 2 := fun h => by
  have := @h Unit Unit _ _
  have h1 : 0 < Fintype.card (Unit ↪ Unit) := Fintype.card_pos_iff.2 ⟨Function.Embedding.refl _⟩
  omega

-- `Fintype.card_embedding_eq_of_infinite` idx 3: removable (an embedding e of an infinite alpha gives infinitely many embeddings σ.trans e for σ : Perm alpha, so a Fintype instance forces α ↪ β to be empty)
theorem c3_102 : drop% Fintype.card_embedding_eq_of_infinite 3 := by
  intro α β _ _
  rcases isEmpty_or_nonempty (α ↪ β) with hE | hN
  · exact Fintype.card_eq_zero
  · exfalso
    obtain ⟨e⟩ := hN
    have hinj : Function.Injective (fun σ : Equiv.Perm α => σ.toEmbedding.trans e) := by
      intro σ τ hστ
      ext x
      have := congrArg (fun g : α ↪ β => g x) hστ
      exact e.injective this
    have : Finite (Equiv.Perm α) := Finite.of_injective _ hinj
    exact not_finite (Equiv.Perm α)

-- `Finite.of_injective` idx 4: necessary (ℕ → Unit constant; stated at Sort 1, every Prop is finite)
theorem c3_103 : ¬ ∀ {α β : Type} [Finite β] (f : α → β), Finite α := fun h =>
  @not_finite ℕ infN (@h ℕ Unit finU (fun _ => ()))

-- `Finite.of_surjective` idx 2: necessary (id on ℕ; stated at Sort 1)
theorem c3_104 : ¬ ∀ {α β : Type} (f : α → β), Function.Surjective f → Finite β := fun h =>
  @not_finite ℕ _ (@h ℕ ℕ id Function.surjective_id)

-- `Finite.of_surjective` idx 4: necessary (Unit → ℕ constant; stated at Sort 1)
theorem c3_105 : ¬ ∀ {α β : Type} [Finite α] (f : α → β), Finite β := fun h =>
  @not_finite ℕ infN (@h Unit ℕ finU (fun _ => 0))

-- `Quot.finite` idx 1: necessary (alpha = ℕ, empty relation; stated at Sort 1)
theorem c3_106 : ¬ ∀ {α : Type} (r : α → α → Prop), Finite (Quot r) := fun h => by
  have := @h ℕ (fun _ _ => False)
  have : Finite ℕ := Finite.of_surjective (Quot.lift (r := fun _ _ : ℕ => False) id (fun _ _ (h : False) => h.elim)) (fun n => ⟨Quot.mk _ n, rfl⟩)
  exact not_finite ℕ

-- `Quotient.finite` idx 1: necessary (alpha = ℕ, equality setoid; stated at Sort 1)
theorem c3_107 : ¬ ∀ {α : Type} (s : Setoid α), Finite (Quotient s) := fun h => by
  have := @h ℕ ⟨Eq, eq_equivalence⟩
  have : Finite ℕ := Finite.of_surjective (Quotient.lift (s := ⟨Eq, eq_equivalence⟩) id (fun _ _ h => h))
    (fun n => ⟨Quotient.mk _ n, rfl⟩)
  exact not_finite ℕ

-- `Function.Embedding.toEmbedding_equivOfFiniteSelfEmbedding` idx 1: necessary (alpha = ℕ)
theorem c3_108 : ¬ indep0% Function.Embedding.toEmbedding_equivOfFiniteSelfEmbedding 1 := fun h =>
  @not_finite ℕ _ (@h ℕ (Function.Embedding.refl ℕ))

-- `Equiv.embeddingEquivOfFinite_apply` idx 1: necessary (alpha = ℕ)
theorem c3_109 : ¬ indep0% Equiv.embeddingEquivOfFinite_apply 1 := fun h =>
  @not_finite ℕ _ (h ℕ (Function.Embedding.refl ℕ))

-- `Equiv.embeddingEquivOfFinite_symm_apply_apply` idx 1: necessary (alpha = ℕ)
theorem c3_110 : ¬ indep0% Equiv.embeddingEquivOfFinite_symm_apply_apply 1 := fun h =>
  @not_finite ℕ _ (h ℕ (Equiv.refl ℕ) 0)

-- `Function.Embedding.nonempty_of_card_le` idx 4: necessary (Unit into Empty)
theorem c3_111 : ¬ drop0% Function.Embedding.nonempty_of_card_le 4 := fun h => by
  obtain ⟨e⟩ := @h Unit Empty _ _
  exact (e ()).elim

-- `Function.Embedding.exists_of_card_le_finset` idx 4: necessary (Unit into s = ∅)
theorem c3_112 : ¬ drop0% Function.Embedding.exists_of_card_le_finset 4 := fun h => by
  obtain ⟨f, hf⟩ := @h Unit ℕ _ ∅
  exact absurd (hf ⟨(), rfl⟩) (by simp)

-- `Function.Embedding.exists_of_card_eq_finset` idx 4: necessary (Unit into s = ∅)
theorem c3_113 : ¬ drop0% Function.Embedding.exists_of_card_eq_finset 4 := fun h => by
  obtain ⟨f, hf⟩ := @h Unit ℕ _ ∅
  simp at hf

-- `Infinite.of_not_fintype` idx 1: necessary (alpha = Unit)
theorem c3_114 : ¬ drop0% Infinite.of_not_fintype 1 := fun h =>
  @Fintype.false Unit (@h Unit) inferInstance

-- `Infinite.of_injective_to_set` idx 2: necessary (alpha = Unit, s = univ)
theorem c3_115 : ¬ drop0% Infinite.of_injective_to_set 2 := fun h =>
  @Fintype.false Unit (@h Unit Set.univ (fun _ => ⟨(), trivial⟩) (fun _ _ _ => rfl)) inferInstance

-- `Infinite.of_injective_to_set` idx 4: necessary (alpha = Bool, s = {true}, f constant)
theorem c3_116 : ¬ drop0% Infinite.of_injective_to_set 4 := fun h =>
  @Fintype.false Bool (@h Bool {true} (fun e => by have : false ∈ ({true} : Set Bool) := e ▸ Set.mem_univ false; simp at this) (fun _ => ⟨true, rfl⟩)) inferInstance

-- `Infinite.of_surjective_from_set` idx 2: necessary (alpha = Unit, s = univ, f = val)
theorem c3_117 : ¬ drop0% Infinite.of_surjective_from_set 2 := fun h =>
  @Fintype.false Unit (@h Unit Set.univ Subtype.val (fun x => ⟨⟨x, trivial⟩, rfl⟩)) inferInstance

-- `Infinite.of_surjective_from_set` idx 4: necessary (alpha = Bool, s = ∅)
theorem c3_118 : ¬ drop0% Infinite.of_surjective_from_set 4 := fun h =>
  @Fintype.false Bool (@h Bool ∅ (fun e => by have : false ∈ (∅ : Set Bool) := e ▸ Set.mem_univ false; exact this) (fun x => x.2.elim)) inferInstance

-- `Infinite.instNontrivial` idx 1: necessary (alpha = Unit)
theorem c3_119 : ¬ drop0% Infinite.instNontrivial 1 := fun h => by
  obtain ⟨x, y, hxy⟩ := (h Unit).exists_pair_ne
  exact hxy rfl

-- `Infinite.nonempty` idx 1: necessary (alpha = Empty)
theorem c3_120 : ¬ drop0% Infinite.nonempty 1 := fun h => by
  obtain ⟨x⟩ := h Empty
  exact x.elim

-- `Infinite.of_injective` idx 2: necessary (alpha = beta = True)
theorem c3_121 : ¬ drop0% Infinite.of_injective 2 := fun h =>
  (@h True True id Function.injective_id).not_finite inferInstance

-- `Infinite.of_injective` idx 4: necessary (ℕ → Unit; stated at Sort 1, no Prop is infinite)
theorem c3_122 : ¬ ∀ {α β : Type} [Infinite β] (f : β → α), Infinite α := fun h =>
  @Fintype.false Unit (@h Unit ℕ infN (fun _ => ())) fintU

-- `Infinite.of_surjective` idx 4: necessary (Unit → ℕ; stated at Sort 1, no Prop is infinite)
theorem c3_123 : ¬ ∀ {α β : Type} [Infinite β] (f : α → β), Infinite α := fun h =>
  @Fintype.false Unit (@h Unit ℕ infN (fun _ => 0)) fintU

-- `Infinite.instSigmaOfNonempty` idx 2: necessary (alpha = Unit, beta = Unit)
theorem c3_124 : ¬ drop0% Infinite.instSigmaOfNonempty 2 := fun h =>
  (@h Unit (fun _ => Unit) _).not_finite inferInstance

-- `Infinite.instSigmaOfNonempty` idx 3: necessary (alpha = ℕ, beta = Empty)
theorem c3_125 : ¬ drop0% Infinite.instSigmaOfNonempty 3 := fun h =>
  (@h ℕ (fun _ => Empty) _).not_finite (Finite.of_injective (β := Empty) (fun x => x.2) (fun x _ _ => x.2.elim))

-- `Infinite.sigma_of_right` idx 3: necessary (alpha = Unit, beta = Unit)
theorem c3_126 : ¬ drop0% Infinite.sigma_of_right 3 := fun h =>
  (@h Unit (fun _ => Unit) ()).not_finite inferInstance

-- `Infinite.instSigmaOfNonempty_1` idx 2: necessary (alpha = Empty, beta = ℕ)
theorem c3_127 : ¬ drop0% Infinite.instSigmaOfNonempty_1 2 := fun h =>
  (@h Empty (fun _ => ℕ) _).not_finite (Finite.of_injective (β := Empty) (fun x => x.1) (fun x _ _ => x.1.elim))

-- `Infinite.instSigmaOfNonempty_1` idx 3: necessary (alpha = Unit, beta = Unit)
theorem c3_128 : ¬ drop0% Infinite.instSigmaOfNonempty_1 3 := fun h =>
  (@h Unit (fun _ => Unit) _).not_finite inferInstance

-- `instInfiniteMultisetOfNonempty` idx 1: necessary (Multiset Empty = {0})
theorem c3_129 : ¬ drop0% instInfiniteMultisetOfNonempty 1 := fun h =>
  (@h Empty).not_finite (@Finite.of_subsingleton _ ⟨fun s t => by
    rw [Multiset.eq_zero_of_forall_notMem (s := s) (fun x => x.elim),
      Multiset.eq_zero_of_forall_notMem (s := t) (fun x => x.elim)]⟩)

-- `instInfiniteListOfNonempty` idx 1: necessary (List Empty = {[]})
theorem c3_130 : ¬ drop0% instInfiniteListOfNonempty 1 := fun h =>
  (@h Empty).not_finite (@Finite.of_subsingleton _ ⟨fun s t => by
    cases s with
    | nil => cases t with
      | nil => rfl
      | cons a _ => exact a.elim
    | cons a _ => exact a.elim⟩)

-- `Infinite.set` idx 1: necessary (Set Unit)
theorem c3_131 : ¬ drop0% Infinite.set 1 := fun h =>
  (@h Unit).not_finite inferInstance

-- `instInfiniteFinset` idx 1: necessary (Finset Unit)
theorem c3_132 : ¬ drop0% instInfiniteFinset 1 := fun h =>
  (@h Unit).not_finite inferInstance

-- `instInfiniteOption` idx 1: necessary (Option Unit)
theorem c3_133 : ¬ drop0% instInfiniteOption 1 := fun h =>
  (@h Unit).not_finite inferInstance

-- `Sum.infinite_of_left` idx 2: necessary (Unit ⊕ Unit)
theorem c3_134 : ¬ drop0% Sum.infinite_of_left 2 := fun h =>
  (@h Unit Unit).not_finite inferInstance

-- `Sum.infinite_of_right` idx 2: necessary (Unit ⊕ Unit)
theorem c3_135 : ¬ drop0% Sum.infinite_of_right 2 := fun h =>
  (@h Unit Unit).not_finite inferInstance

-- `Prod.infinite_of_right` idx 2: necessary (Empty × ℕ)
theorem c3_136 : ¬ drop0% Prod.infinite_of_right 2 := fun h =>
  (@h Empty ℕ _).not_finite (Finite.of_injective (β := Empty) (fun x => x.1) (fun x _ _ => x.1.elim))

-- `Prod.infinite_of_right` idx 3: necessary (Unit × Unit)
theorem c3_137 : ¬ drop0% Prod.infinite_of_right 3 := fun h =>
  (@h Unit Unit _).not_finite inferInstance

-- `Prod.infinite_of_left` idx 2: necessary (Unit × Unit)
theorem c3_138 : ¬ drop0% Prod.infinite_of_left 2 := fun h =>
  (@h Unit Unit _).not_finite inferInstance

-- `Prod.infinite_of_left` idx 3: necessary (ℕ × Empty)
theorem c3_139 : ¬ drop0% Prod.infinite_of_left 3 := fun h =>
  (@h ℕ Empty _).not_finite (Finite.of_injective (β := Empty) (fun x => x.2) (fun x _ _ => x.2.elim))

-- `instInfinitePerm` idx 1: necessary (Perm Unit)
theorem c3_140 : ¬ drop0% instInfinitePerm 1 := fun h =>
  (@h Unit).not_finite inferInstance

-- `_private.Mathlib.Data.Fintype.EquivFin.0.Infinite.natEmbeddingAux_injective` idx 1: necessary (alpha = Unit)
theorem c3_141 : ¬ indep0% _private.Mathlib.Data.Fintype.EquivFin.«0».Infinite.natEmbeddingAux_injective 1 := fun h =>
  (h Unit).not_finite inferInstance

-- `Function.Embedding.is_empty` idx 3: necessary (ℕ ↪ ℕ; stated at Sort 1, no Prop is infinite)
theorem c3_142 : ¬ ∀ {α β : Type} [Infinite α], IsEmpty (α ↪ β) := fun h =>
  (@h ℕ ℕ infN).false (Function.Embedding.refl ℕ)

-- `not_surjective_finite_infinite` idx 2: necessary (id on ℕ; stated at Sort 1)
theorem c3_143 : ¬ ∀ {α β : Type} [Infinite β] (f : α → β), ¬Function.Surjective f := fun h =>
  @h ℕ ℕ infN id Function.surjective_id

-- `Fin.lt_card_filter_univ_iff_apply_of_imp` idx 4: necessary (n = 2, p = (· = 1), j = 1)
theorem c3_144 : ¬ drop0% Fin.lt_card_filter_univ_iff_apply_of_imp 4 := fun h => by
  have := @h 2 1 (· = 1) _
  revert this; decide

-- `Function.Injective.invFun_restrict` idx 6: necessary (alpha = Empty)
theorem c3_145 : ¬ indep0% Function.Injective.invFun_restrict 6 := fun h => by
  obtain ⟨x⟩ := @h Empty Unit _ _ Empty.elim (fun x => x.elim)
  exact x.elim

-- `Function.Embedding.invFun_restrict` idx 5: necessary (alpha = Empty)
theorem c3_146 : ¬ indep0% Function.Embedding.invFun_restrict 5 := fun h => by
  obtain ⟨x⟩ := @h Empty Unit _ _ ⟨Empty.elim, fun x => x.elim⟩
  exact x.elim

-- `Fintype.choose_subtype_eq` idx 5: removable (optParam, derivable: the default value proves it)
theorem c3_147 : indep% Fintype.choose_subtype_eq 5 := fun p _ _ x =>
  ⟨x, rfl, fun y hy => Subtype.ext hy⟩

-- `Finite.exists_max` idx 2: necessary (id on ℕ)
theorem c3_148 : ¬ drop0% Finite.exists_max 2 := fun h => by
  obtain ⟨x, hx⟩ := @h ℕ ℕ _ _ id
  have := hx (x + 1)
  simp at this

-- `Finite.exists_max` idx 3: necessary (alpha = Empty)
theorem c3_149 : ¬ drop0% Finite.exists_max 3 := fun h => by
  obtain ⟨x, _⟩ := @h Empty ℕ _ _ Empty.elim
  exact x.elim

-- `Finite.exists_min` idx 2: necessary (negation on ℤ)
theorem c3_150 : ¬ drop0% Finite.exists_min 2 := fun h => by
  obtain ⟨x, hx⟩ := @h ℤ ℤ _ _ id
  have := hx (x - 1)
  simp at this

-- `Finite.exists_min` idx 3: necessary (alpha = Empty)
theorem c3_151 : ¬ drop0% Finite.exists_min 3 := fun h => by
  obtain ⟨x, _⟩ := @h Empty ℕ _ _ Empty.elim
  exact x.elim

-- `instFiniteOption` idx 1: necessary (Option ℕ)
theorem c3_152 : ¬ drop0% instFiniteOption 1 := fun h =>
  @not_finite ℕ infN (@Finite.of_injective _ _ (@h ℕ) _ (Option.some_injective ℕ))

-- `Fintype.induction_empty_option` idx 2: necessary (P = False)
theorem c3_153 : ¬ drop0% Fintype.induction_empty_option 2 := fun h =>
  @h (fun _ _ => False) (fun _ _ _ _ x => x) (fun _ _ x => x) PEmpty _

-- `Fintype.induction_empty_option` idx 3: necessary (P = IsEmpty, alpha = Unit)
theorem c3_154 : ¬ drop0% Fintype.induction_empty_option 3 := fun h =>
  (@h (fun α _ => IsEmpty α) (fun _ _ _ e hα => e.symm.isEmpty) inferInstance Unit _).false ()

-- `Finite.induction_empty_option` idx 2: necessary (P = False)
theorem c3_155 : ¬ drop0% Finite.induction_empty_option 2 := fun h =>
  @h (fun _ => False) (fun _ x => x) (fun x => x) PEmpty _

-- `Finite.induction_empty_option` idx 3: necessary (P = IsEmpty, alpha = Unit)
theorem c3_156 : ¬ drop0% Finite.induction_empty_option 3 := fun h =>
  (@h (fun α => IsEmpty α) (fun e hα => e.symm.isEmpty) inferInstance Unit _).false ()

-- `Finite.induction_empty_option` idx 5: necessary (P = Finite, alpha = ℕ)
theorem c3_157 : ¬ drop0% Finite.induction_empty_option 5 := fun h =>
  @not_finite ℕ _ (@h (fun α => Finite α) (fun e hα => Finite.of_equiv _ e) inferInstance
    (fun _ => inferInstance) ℕ)

-- `Finsupp.Lex.acc` idx 5: necessary (r = (>) on ℕ, s = "1 below 0", x = single 0 1)
theorem c3_158 : ¬ drop0% Finsupp.Lex.acc 5 := fun h =>
  notAcc (fun n => Finsupp.single n 1) lexGt10
    (@h ℕ ℕ _ (· > ·) (fun a b => b = 0 ∧ a = 1) wf10 (Finsupp.single 0 1) (fun a _ => wfGtC.apply a))

-- `Finsupp.Lex.acc` idx 6: necessary (alpha = Unit, s = (>) on positive naturals, x = single () 1)
theorem c3_159 : ¬ drop0% Finsupp.Lex.acc 6 := fun h =>
  notAcc (fun n => Finsupp.single () (n + 1)) (lexPos _ (fun _ h => h))
    (@h Unit ℕ _ (fun _ _ => False) (fun a b => 0 < b ∧ b < a) (fun n hn => by omega) (Finsupp.single () 1)
      (fun a _ => ⟨a, fun b hb => (hb.2 (Subsingleton.elim _ _)).elim⟩))

-- `Finsupp.Lex.acc` idx 8: necessary (r = s = (<) on ℕ, x = single 0 1)
theorem c3_160 : ¬ drop0% Finsupp.Lex.acc 8 := fun h =>
  notAcc (fun n => Finsupp.single n 1) lexLt
    (@h ℕ ℕ _ (· < ·) (· < ·) (fun n hn => Nat.not_lt_zero _ hn) wellFounded_lt (Finsupp.single 0 1))

-- `Finsupp.Lex.wellFounded` idx 5: necessary (r = (>) on ℕ, s = "1 below 0")
theorem c3_161 : ¬ drop0% Finsupp.Lex.wellFounded 5 := fun h =>
  notWF (fun n => Finsupp.single n 1) lexGt10 (@h ℕ ℕ _ (· > ·) (fun a b => b = 0 ∧ a = 1) wf10 wfGtC)

-- `Finsupp.Lex.wellFounded` idx 6: necessary (alpha = Unit, s = (>) on positive naturals)
theorem c3_162 : ¬ drop0% Finsupp.Lex.wellFounded 6 := fun h =>
  notWF (fun n => Finsupp.single () (n + 1)) (lexPos _ (fun _ h => h))
    (@h Unit ℕ _ (fun _ _ => False) (fun a b => 0 < b ∧ b < a) (fun n hn => by omega)
      ⟨fun a => ⟨a, fun b hb => (hb.2 (Subsingleton.elim _ _)).elim⟩⟩)

-- `Finsupp.Lex.wellFounded` idx 7: necessary (r = s = (<) on ℕ)
theorem c3_163 : ¬ drop0% Finsupp.Lex.wellFounded 7 := fun h =>
  notWF (fun n => Finsupp.single n 1) lexLt
    (@h ℕ ℕ _ (· < ·) (· < ·) (fun n hn => Nat.not_lt_zero _ hn) wellFounded_lt)

-- `Finsupp.Lex.wellFounded'` idx 5: necessary (r = (>) on ℕ, s = "1 below 0")
theorem c3_164 : ¬ drop0% Finsupp.Lex.wellFounded' 5 := fun h =>
  notWF (fun n => Finsupp.single n 1) lexGt10
    (@h ℕ ℕ _ (· > ·) (fun a b => b = 0 ∧ a = 1) wf10 ⟨fun a b h1 h2 => by omega⟩ wellFounded_lt)

-- `Finsupp.Lex.wellFounded'` idx 7: necessary (alpha = Bool, r empty, s = (<): two singles below each other)
theorem c3_165 : ¬ drop0% Finsupp.Lex.wellFounded' 7 := fun h => by
  have := @h Bool ℕ _ (fun _ _ => False) (· < ·) (fun n hn => Nat.not_lt_zero _ hn) wellFounded_lt
    ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩
  have h1 : Finsupp.Lex (fun _ _ => False) (· < ·) (Finsupp.single true 1 : Bool →₀ ℕ) (Finsupp.single false 1) :=
    Finsupp.lex_def.2 ⟨false, fun _ h => h.elim, by simp⟩
  have h2 : Finsupp.Lex (fun _ _ => False) (· < ·) (Finsupp.single false 1 : Bool →₀ ℕ) (Finsupp.single true 1) :=
    Finsupp.lex_def.2 ⟨true, fun _ h => h.elim, by simp⟩
  exact @WellFounded.asymmetric _ _ this _ _ h1 h2

-- `Finsupp.Lex.wellFounded'` idx 8: necessary (r = s = (<) on ℕ)
theorem c3_166 : ¬ drop0% Finsupp.Lex.wellFounded' 8 := fun h =>
  notWF (fun n => Finsupp.single n 1) lexLt
    (@h ℕ ℕ _ (· < ·) (· < ·) (fun n hn => Nat.not_lt_zero _ hn) wellFounded_lt ⟨fun a b h1 h2 => by omega⟩)

-- `Finsupp.Lex.wellFoundedLT` idx 3: necessary (alpha = Unit ⊕ Unit, no two indices comparable: 2-cycle of singles)
theorem c3_167 : ¬ drop0% Finsupp.Lex.wellFoundedLT 3 := fun h => by
  have := @wellFounded_lt _ _ (h (α := Unit ⊕ Unit) (N := ℕ))
  have h1 : toLex (Finsupp.single (Sum.inl ()) 1 : Unit ⊕ Unit →₀ ℕ) < toLex (Finsupp.single (Sum.inr ()) 1) :=
    Finsupp.Lex.lt_iff.2 ⟨Sum.inr (), fun j hj => by cases j <;> simp at hj, by simp⟩
  have h2 : toLex (Finsupp.single (Sum.inr ()) 1 : Unit ⊕ Unit →₀ ℕ) < toLex (Finsupp.single (Sum.inl ()) 1) :=
    Finsupp.Lex.lt_iff.2 ⟨Sum.inl (), fun j hj => by cases j <;> simp at hj, by simp⟩
  exact @WellFounded.asymmetric _ _ this _ _ h1 h2

-- `Finsupp.Lex.wellFoundedLT` idx 4: necessary (alpha = N = ℕ, toLex (single n 1) descends)
theorem c3_168 : ¬ drop0% Finsupp.Lex.wellFoundedLT 4 := fun h =>
  notWF (fun n => toLex (Finsupp.single n 1)) (fun n => Finsupp.Lex.single_strictAnti (Nat.lt_succ_self n))
    (@wellFounded_lt _ _ (h (α := ℕ) (N := ℕ)))

-- `Finsupp.Lex.wellFoundedLT` idx 7: necessary (alpha = ℕᵒᵈ, N = (Fin 2)ᵒᵈ whose zero is the top)
theorem c3_169 : ¬ drop0% Finsupp.Lex.wellFoundedLT 7 := fun h =>
  notWF _ lexD_lt (@wellFounded_lt _ _ (h (α := ℕᵒᵈ) (N := (Fin 2)ᵒᵈ)))

-- `Finsupp.Colex.wellFoundedLT` idx 3: necessary (alpha = Unit ⊕ Unit: 2-cycle of singles)
theorem c3_170 : ¬ drop0% Finsupp.Colex.wellFoundedLT 3 := fun h => by
  have := @wellFounded_lt _ _ (h (α := Unit ⊕ Unit) (N := ℕ))
  have h1 : toColex (Finsupp.single (Sum.inl ()) 1 : Unit ⊕ Unit →₀ ℕ) < toColex (Finsupp.single (Sum.inr ()) 1) :=
    Finsupp.Colex.lt_iff.2 ⟨Sum.inr (), fun j hj => by cases j <;> simp at hj, by simp⟩
  have h2 : toColex (Finsupp.single (Sum.inr ()) 1 : Unit ⊕ Unit →₀ ℕ) < toColex (Finsupp.single (Sum.inl ()) 1) :=
    Finsupp.Colex.lt_iff.2 ⟨Sum.inl (), fun j hj => by cases j <;> simp at hj, by simp⟩
  exact @WellFounded.asymmetric _ _ this _ _ h1 h2

-- `Finsupp.Colex.wellFoundedLT` idx 4: necessary (alpha = ℤ, toColex (single (-n) 1) descends)
theorem c3_171 : ¬ drop0% Finsupp.Colex.wellFoundedLT 4 := fun h =>
  notWF (fun n => toColex (Finsupp.single (-(n:ℤ)) 1)) (fun n => Finsupp.Colex.single_strictMono (by omega))
    (@wellFounded_lt _ _ (h (α := ℤ) (N := ℕ)))

-- `Finsupp.Colex.wellFoundedLT` idx 7: necessary (alpha = ℕ, N = (Fin 2)ᵒᵈ whose zero is the top)
theorem c3_172 : ¬ drop0% Finsupp.Colex.wellFoundedLT 7 := fun h =>
  notWF _ colexD_lt (@wellFounded_lt _ _ (h (α := ℕ) (N := (Fin 2)ᵒᵈ)))

-- `Finsupp.Lex.wellFounded_of_finite` idx 5: necessary (alpha = Bool, r empty: 2-cycle of singles)
theorem c3_173 : ¬ drop0% Finsupp.Lex.wellFounded_of_finite 5 := fun h => by
  have := @h Bool ℕ _ (fun _ _ => False) (· < ·) _ wellFounded_lt
  have h1 : Finsupp.Lex (fun _ _ => False) (· < ·) (Finsupp.single true 1 : Bool →₀ ℕ) (Finsupp.single false 1) :=
    Finsupp.lex_def.2 ⟨false, fun _ h => h.elim, by simp⟩
  have h2 : Finsupp.Lex (fun _ _ => False) (· < ·) (Finsupp.single false 1 : Bool →₀ ℕ) (Finsupp.single true 1) :=
    Finsupp.lex_def.2 ⟨true, fun _ h => h.elim, by simp⟩
  exact @WellFounded.asymmetric _ _ this _ _ h1 h2

-- `Finsupp.Lex.wellFounded_of_finite` idx 6: necessary (alpha = ℕ, r = s = (<))
theorem c3_174 : ¬ drop0% Finsupp.Lex.wellFounded_of_finite 6 := fun h =>
  notWF (fun n => Finsupp.single n 1) lexLt (@h ℕ ℕ _ (· < ·) (· < ·) _ wellFounded_lt)

-- `Finsupp.Lex.wellFounded_of_finite` idx 7: necessary (alpha = Unit, s = (>) on positive naturals)
theorem c3_175 : ¬ drop0% Finsupp.Lex.wellFounded_of_finite 7 := fun h =>
  notWF (fun n => Finsupp.single () (n + 1)) (lexPos _ (fun d => by cases d; exact lt_irrefl _))
    (@h Unit ℕ _ (· < ·) (fun a b => 0 < b ∧ b < a) _ _)

-- `Finsupp.Lex.wellFoundedLT_of_finite` idx 4: necessary (alpha = N = ℕ)
theorem c3_176 : ¬ drop0% Finsupp.Lex.wellFoundedLT_of_finite 4 := fun h =>
  notWF (fun n => toLex (Finsupp.single n 1)) (fun n => Finsupp.Lex.single_strictAnti (Nat.lt_succ_self n))
    (@wellFounded_lt _ _ (h (α := ℕ) (N := ℕ)))

-- `Finsupp.Lex.wellFoundedLT_of_finite` idx 6: necessary (alpha = Unit, N = ℤ)
theorem c3_177 : ¬ drop0% Finsupp.Lex.wellFoundedLT_of_finite 6 := fun h =>
  notWF (fun n => toLex (Finsupp.single () (-(n:ℤ)))) (fun n => by
      rw [Finsupp.Lex.lt_iff_of_unique]; simp)
    (@wellFounded_lt _ _ (h (α := Unit) (N := ℤ)))

-- `Finsupp.Colex.wellFoundedLT_of_finite` idx 6: necessary (alpha = Unit, N = ℤ)
theorem c3_178 : ¬ drop0% Finsupp.Colex.wellFoundedLT_of_finite 6 := fun h =>
  notWF (fun n => toColex (Finsupp.single () (-(n:ℤ)))) (fun n => by
      rw [Finsupp.Colex.lt_iff_of_unique]; simp)
    (@wellFounded_lt _ _ (h (α := Unit) (N := ℤ)))

-- `Finsupp.wellFoundedLT` idx 4: necessary (alpha = Unit, N = ℚ≥0)
theorem c3_179 : ¬ drop0% Finsupp.wellFoundedLT 4 := fun h =>
  notWF _ qch_lt (@wellFounded_lt _ _ (@h Unit ℚ≥0 _ _ (fun n => not_lt_zero)))

-- `Finsupp.wellFoundedLT` idx 5: necessary (alpha = ℕ, N = (Fin 2)ᵒᵈ whose zero is the top)
theorem c3_180 : ¬ drop0% Finsupp.wellFoundedLT 5 := fun h =>
  notWF dch dch_lt (@wellFounded_lt _ _ (@h ℕ (Fin 2)ᵒᵈ _ _ _))

-- `Finsupp.wellFoundedLT'` idx 4: necessary (alpha = ℕ, N = (Fin 2)ᵒᵈ whose zero is the top)
theorem c3_181 : ¬ drop0% Finsupp.wellFoundedLT' 4 := fun h =>
  notWF dch dch_lt (@wellFounded_lt _ _ (h (α := ℕ) (N := (Fin 2)ᵒᵈ)))

-- `Finsupp.wellFoundedLT'` idx 5: necessary (alpha = Unit, N = ℚ≥0)
theorem c3_182 : ¬ drop0% Finsupp.wellFoundedLT' 5 := fun h =>
  notWF _ qch_lt (@wellFounded_lt _ _ (h (α := Unit) (N := ℚ≥0)))

-- `Finsupp.wellFoundedLT_of_finite` idx 3: necessary (alpha = ℕ, N = (Fin 2)ᵒᵈ)
theorem c3_183 : ¬ drop0% Finsupp.wellFoundedLT_of_finite 3 := fun h =>
  notWF dch dch_lt (@wellFounded_lt _ _ (h (α := ℕ) (N := (Fin 2)ᵒᵈ)))

-- `Finsupp.wellFoundedLT_of_finite` idx 5: necessary (alpha = Unit, N = ℤ)
theorem c3_184 : ¬ drop0% Finsupp.wellFoundedLT_of_finite 5 := fun h =>
  notWF _ zch_lt (@wellFounded_lt _ _ (h (α := Unit) (N := ℤ)))

-- `Finite.le_ciSup_iff` idx 3: necessary (ℤ, f n = n, a = 1: junk iSup 0)
theorem c3_185 : ¬ drop0% Finite.le_ciSup_iff 3 := fun h => by
  have := (@h ℤ ℕ _ _ 1 (fun n => (n : ℤ))).2 ⟨1, by simp⟩
  rw [zsup_unb _ (fun n => le_refl _)] at this
  omega

-- `Finite.le_ciSup_iff` idx 4: necessary (iota = Empty, ℤ, a = 0)
theorem c3_186 : ¬ drop0% Finite.le_ciSup_iff 4 := fun h => by
  obtain ⟨x, _⟩ := (@h ℤ Empty _ _ 0 Empty.elim).1 (by rw [zsup_empty])
  exact x.elim

-- `Finite.ciInf_le_iff` idx 3: necessary (ℤ, f n = -n, a = -1: junk iInf 0)
theorem c3_187 : ¬ drop0% Finite.ciInf_le_iff 3 := fun h => by
  have := (@h ℤ ℕ _ _ (-1) (fun n => -(n : ℤ))).2 ⟨1, by simp⟩
  rw [zinf_unb _ (fun n => le_refl _)] at this
  omega

-- `Finite.ciInf_le_iff` idx 4: necessary (iota = Empty, ℤ, a = 0)
theorem c3_188 : ¬ drop0% Finite.ciInf_le_iff 4 := fun h => by
  obtain ⟨x, _⟩ := (@h ℤ Empty _ _ 0 Empty.elim).1 (by rw [zinf_empty])
  exact x.elim

-- `Finite.lt_ciInf_iff` idx 3: necessary (ℤ, f n = -n, a = -1: junk iInf 0)
theorem c3_189 : ¬ drop0% Finite.lt_ciInf_iff 3 := fun h => by
  have := (@h ℤ ℕ _ _ (-1) (fun n => -(n : ℤ))).1 (by rw [zinf_unb _ (fun n => le_refl _)]; omega) 1
  simp at this

-- `Finite.lt_ciInf_iff` idx 4: necessary (iota = Empty, ℤ, a = 0)
theorem c3_190 : ¬ drop0% Finite.lt_ciInf_iff 4 := fun h => by
  have := (@h ℤ Empty _ _ 0 Empty.elim).2 (fun x => x.elim)
  rw [zinf_empty] at this
  exact lt_irrefl _ this

-- `Finite.ciSup_lt_iff` idx 3: necessary (ℤ, f n = n, a = 1: junk iSup 0)
theorem c3_191 : ¬ drop0% Finite.ciSup_lt_iff 3 := fun h => by
  have := (@h ℤ ℕ _ _ 1 (fun n => (n : ℤ))).1 (by rw [zsup_unb _ (fun n => le_refl _)]; omega) 1
  simp at this

-- `Finite.ciSup_lt_iff` idx 4: necessary (iota = Empty, ℤ, a = 0)
theorem c3_192 : ¬ drop0% Finite.ciSup_lt_iff 4 := fun h => by
  have := (@h ℤ Empty _ _ 0 Empty.elim).2 (fun x => x.elim)
  rw [zsup_empty] at this
  exact lt_irrefl _ this
