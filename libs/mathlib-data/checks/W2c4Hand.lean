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

namespace W2c4
/-- involution of ℚ fixing ℕ, swapping -1/2 ↔ 5/2, 1/2 ↔ 1/4, 3/2 ↔ 1/3 -/
def φ (x : ℚ) : ℚ := if x = -1/2 then 5/2 else if x = 5/2 then -1/2 else if x = 1/2 then 1/4
  else if x = 1/4 then 1/2 else if x = 3/2 then 1/3 else if x = 1/3 then 3/2 else x
theorem φφ (x : ℚ) : φ (φ x) = x := by
  by_cases h1 : x = -1/2; · subst h1; norm_num [φ]
  by_cases h2 : x = 5/2; · subst h2; norm_num [φ]
  by_cases h3 : x = 1/2; · subst h3; norm_num [φ]
  by_cases h4 : x = 1/4; · subst h4; norm_num [φ]
  by_cases h5 : x = 3/2; · subst h5; norm_num [φ]
  by_cases h6 : x = 1/3; · subst h6; norm_num [φ]
  have : φ x = x := by simp only [φ, h1, h2, h3, h4, h5, h6, ite_false]
  rw [this, this]
theorem φ_inj : Function.Injective φ := fun a b h => by rw [← φφ a, h, φφ]
theorem φ_nat (n : ℕ) : φ (n : ℚ) = n := by
  unfold φ
  have : (0:ℚ) ≤ n := Nat.cast_nonneg n
  split_ifs with h1 h2 h3 h4 h5 h6
  · linarith
  · have := congrArg (· * 2) h2; norm_num at this; norm_cast at this; omega
  · have := congrArg (· * 2) h3; norm_num at this; norm_cast at this; omega
  · have := congrArg (· * 4) h4; norm_num at this; norm_cast at this; omega
  · have := congrArg (· * 2) h5; norm_num at this; norm_cast at this; omega
  · have := congrArg (· * 3) h6; norm_num at this; norm_cast at this; omega
  · rfl
/-- ℚ with the field structure of ℚ but the order pulled back along φ: a linear order with a
lawful `FloorSemiring` (ℕ is fixed by φ) that is not a strict ordered ring -/
def Q := ℚ
instance : Field Q := inferInstanceAs (Field ℚ)
instance : LinearOrder Q := LinearOrder.lift' (fun x : Q => φ x) φ_inj
instance : FloorSemiring Q where
  floor x := ⌊φ x⌋₊
  ceil x := ⌈φ x⌉₊
  floor_of_neg {a} h := by
    change φ a < φ (0:ℚ) at h; rw [show φ (0:ℚ) = 0 by simpa using φ_nat 0] at h
    exact Nat.floor_of_nonpos h.le
  gc_floor {a n} h := by
    change φ (0:ℚ) ≤ φ a at h; rw [show φ (0:ℚ) = 0 by simpa using φ_nat 0] at h
    show n ≤ ⌊φ a⌋₊ ↔ φ (n : ℚ) ≤ φ a
    rw [φ_nat, Nat.le_floor_iff h]
  gc_ceil a n := by
    show ⌈φ a⌉₊ ≤ n ↔ φ a ≤ φ (n : ℚ)
    rw [φ_nat, Nat.ceil_le]
instance : DecidableLE Q := fun a b => inferInstanceAs (Decidable (φ a ≤ φ b))
instance : DecidableLT Q := fun a b => inferInstanceAs (Decidable (φ a < φ b))
/-- Bool with left projection as xor, zero false -/
def LP := Bool
instance : XorOp LP := ⟨fun a _ => a⟩
instance : Zero LP := ⟨(false : Bool)⟩
instance : DecidableEq LP := inferInstanceAs (DecidableEq Bool)
instance : Fintype LP := inferInstanceAs (Fintype Bool)
/-- Bool with constant-false xor, zero false -/
def CF := Bool
instance : XorOp CF := ⟨fun _ _ => (false : Bool)⟩
instance : Zero CF := ⟨(false : Bool)⟩
instance : DecidableEq CF := inferInstanceAs (DecidableEq Bool)
instance : Fintype CF := inferInstanceAs (Fintype Bool)
/-- Bool with NOR as xor (not associative), zero false -/
def NR := Bool
instance : XorOp NR := ⟨fun a b => (!(a || b) : Bool)⟩
instance : Zero NR := ⟨(false : Bool)⟩
instance : DecidableEq NR := inferInstanceAs (DecidableEq Bool)
instance : Fintype NR := inferInstanceAs (Fintype Bool)
end W2c4
namespace W2c4
/-- `ZMod 2` as a field (the library instance lives outside Mathlib.Data) -/
abbrev Z2 := ZMod 2
noncomputable instance z2F : Field Z2 := Field.ofIsUnitOrEqZero (by decide)
/-- a non-additive `FunLike` ℤ → ℤ, x ↦ x * x (sends 1 to 1) -/
def FZ := Unit
instance : FunLike FZ ℤ ℤ where
  coe _ := fun x => x * x
  coe_injective a b _ := rfl
/-- two `FunLike` maps ℤ → ℤ that differ only at 0 -/
instance : FunLike Bool ℤ ℤ where
  coe b := fun x => if x = 0 then (if b then 1 else 0) else 1
  coe_injective a b h := by
    have := congrFun h 0; cases a <;> cases b <;> simp_all
/-- `n ↦ |n|` as a monoid-with-zero hom ℤ → ℤ -/
def absZ : ℤ →*₀ ℤ := (Nat.castRingHom ℤ : ℕ →*₀ ℤ).comp Int.natAbsHom
/-- `n ↦ sign n` as a monoid-with-zero hom ℤ → ℤ -/
def sgnZ : ℤ →*₀ ℤ where
  toFun := Int.sign
  map_zero' := rfl
  map_one' := rfl
  map_mul' := Int.sign_mul
/-- function type with the identity as `DFunLike` -/
def PF (α β : Type) := α → β
instance (α β : Type) : FunLike (PF α β) α β where
  coe f := f
  coe_injective _ _ h := h
end W2c4
namespace W2c4
/-- floor division by a negative number, without divisibility -/
theorem H1 {a b c : ℤ} (hb : b < 0) : a / b ≤ c ↔ b * c ≤ a := by
  rw [show a / b = -(a / -b) by rw [Int.ediv_neg, Int.neg_neg], neg_le, Int.le_ediv_iff_mul_le (by omega)]
  constructor <;> intro h <;> linarith
/-- strict version for a negative divisor -/
theorem H4 {a b c : ℤ} (hc : c < 0) : a < b / c ↔ b < c * a := by
  rw [show b / c = -(b / -c) by rw [Int.ediv_neg, Int.neg_neg], lt_neg, Int.ediv_lt_iff_lt_mul (by omega)]
  constructor <;> intro h <;> linarith
end W2c4
namespace W2c4
/-- ℕ with zero multiplication -/
def NZ := ℕ
instance : Mul NZ := ⟨fun _ _ => (0:ℕ)⟩
instance : AddMonoid NZ := inferInstanceAs (AddMonoid ℕ)
/-- every CP-rank-one holor of non-empty shape over NZ vanishes -/
theorem cp1 {ds : List ℕ} {x : Holor NZ ds} (h : x.CPRankMax1) : ∀ t, ds ≠ [] → x t = (0:ℕ) := by
  induction h with
  | nil x => intro t h; exact absurd rfl h
  | cons x y _ _ => intro t _; rfl
/-- a holor of CP rank at most 0 is 0 -/
theorem cp0 {α : Type} {ds : List ℕ} [Mul α] [AddMonoid α] {x : Holor α ds} (h : Holor.CPRankMax 0 x) : x = 0 := by
  cases h; rfl
end W2c4
namespace W2c4
/-- for a prime p, p^(k+l+1) ∣ m n forces p^(k+1) ∣ m or p^(l+1) ∣ n (no lower divisibility needed) -/
theorem prime_pow_split {p : ℤ} (hp : Prime p) : ∀ (k l : ℕ) {m n : ℤ}, p ^ (k + l + 1) ∣ m * n → p ^ (k + 1) ∣ m ∨ p ^ (l + 1) ∣ n := by
  intro k l
  induction k with
  | zero =>
    intro m n h
    by_cases hm : p ∣ m
    · left; simpa using hm
    · right; exact hp.pow_dvd_of_dvd_mul_left _ hm (by simpa using h)
  | succ k ih =>
    intro m n h
    by_cases hm : p ∣ m
    · obtain ⟨m', rfl⟩ := hm
      have h' : p ^ (k + l + 1) ∣ m' * n := by
        rw [show k + 1 + l + 1 = (k + l + 1) + 1 by omega, pow_succ', mul_assoc] at h
        exact (mul_dvd_mul_iff_left hp.ne_zero).mp h
      rcases ih h' with h1 | h1
      · left; rw [pow_succ']; exact mul_dvd_mul_left p h1
      · right; exact h1
    · right
      exact (pow_dvd_pow p (by omega)).trans (hp.pow_dvd_of_dvd_mul_left _ hm h)
end W2c4

-- `Fintype.piFinset_subset` idx 6: necessary (α = Unit, t₁ = {true}, t₂ = ∅)
theorem c4_1 : ¬ drop0% Fintype.piFinset_subset 6 := fun h => absurd (@h Unit _ _ (fun _ => Bool) (fun _ => {true}) (fun _ => ∅)) (by decide)

-- `Fintype.piFinset_empty` idx 4: necessary (α = Empty: piFinset is {the empty function})
theorem c4_2 : ¬ drop0% Fintype.piFinset_empty 4 := fun h => absurd (@h Empty _ _ (fun _ => Unit)) (by decide)

-- `Fintype.Aesop.piFinset_nonempty_of_forall_nonempty` idx 5: necessary (α = Unit, s = ∅)
theorem c4_3 : ¬ drop0% Fintype.Aesop.piFinset_nonempty_of_forall_nonempty 5 := fun h => absurd (@h Unit _ _ (fun _ => Bool) (fun _ => ∅)) (by simp)

-- `Fintype.piFinset_of_isEmpty` idx 4: necessary (dependent: α = Unit is not empty)
theorem c4_4 : ¬ indep0% Fintype.piFinset_of_isEmpty 4 := fun h => (@h Unit _ _ (fun _ => Unit) (fun _ => ∅)).false ()

-- `Fintype.piFinset_subsingleton` idx 5: necessary (α = Unit, f = univ : Finset Bool)
theorem c4_5 : ¬ drop0% Fintype.piFinset_subsingleton 5 := fun h => by
  have := @h Unit _ _ (fun _ => Bool) (fun _ => Finset.univ)
  exact absurd (@this (fun _ => true) (by simp) (fun _ => false) (by simp)) (by decide)

-- `Fintype.piFinset_disjoint_of_disjoint` idx 7: necessary (α = Unit, t₁ = t₂ = {true})
theorem c4_6 : ¬ drop0% Fintype.piFinset_disjoint_of_disjoint 7 := fun h => absurd (@h Unit _ _ (fun _ => Bool) (fun _ => {true}) (fun _ => {true}) ()) (by decide)

-- `Fintype.eval_image_piFinset` idx 7: necessary (α = Bool, t false = ∅, t true = {true}, a = true)
theorem c4_7 : ¬ drop0% Fintype.eval_image_piFinset 7 := fun h => absurd (@h Bool _ _ (fun _ => Bool) (fun b => if b then {true} else ∅) true _) (by decide)

-- `Fintype.filter_piFinset_of_notMem` idx 8: necessary (α = Unit, t = {true}, x = true)
theorem c4_8 : ¬ drop0% Fintype.filter_piFinset_of_notMem 8 := fun h => absurd (@h Unit _ _ (fun _ => Bool) _ (fun _ => {true}) () true) (by decide)

-- `Fintype.piFinset_update_singleton_eq_filter_piFinset_eq` idx 8: necessary (α = Unit, s = ∅, a = true)
theorem c4_9 : ¬ drop0% Fintype.piFinset_update_singleton_eq_filter_piFinset_eq 8 := fun h => absurd (@h Unit _ _ (fun _ => Bool) _ (fun _ => ∅) () true) (by decide)

-- `Set.Finite.pi` idx 1: necessary (ι = ℕ, t i = univ : Set Bool)
theorem c4_10 : ¬ drop0% Set.Finite.pi 1 := fun h => Set.infinite_univ (α := ℕ → Bool) (by have := @h ℕ (fun _ => Bool) (fun _ => Set.univ) (fun _ => Set.finite_univ); rwa [Set.pi_univ] at this)

-- `Set.Finite.pi` idx 4: necessary (ι = Unit, t = univ : Set ℕ)
theorem c4_11 : ¬ drop0% Set.Finite.pi 4 := fun h => Set.infinite_univ (α := Unit → ℕ) (by simpa using @h Unit _ (fun _ => ℕ) (fun _ => Set.univ))

-- `Set.Finite.pi'` idx 1: necessary (ι = ℕ, t i = univ : Set Bool)
theorem c4_12 : ¬ drop0% Set.Finite.pi' 1 := fun h => Set.infinite_univ (α := ℕ → Bool) (by have := @h ℕ (fun _ => Bool) (fun _ => Set.univ) (fun _ => Set.finite_univ); simp only [Set.mem_univ, implies_true, Set.setOf_true] at this; exact this)

-- `Set.Finite.pi'` idx 4: necessary (ι = Unit, t = univ : Set ℕ)
theorem c4_13 : ¬ drop0% Set.Finite.pi' 4 := fun h => Set.infinite_univ (α := Unit → ℕ) (by simpa using @h Unit _ (fun _ => ℕ) (fun _ => Set.univ))

-- `Set.forall_finite_image_eval_iff` idx 1: necessary (δ = ℕ, κ = Bool, s = univ)
theorem c4_14 : ¬ drop0% Set.forall_finite_image_eval_iff 1 := fun h => Set.infinite_univ (α := ℕ → Bool) ((@h ℕ (fun _ => Bool) Set.univ).mp (fun d => (Set.finite_univ (α := Bool)).subset (Set.subset_univ _)))

-- `Finite.exists_infinite_fiber` idx 2: necessary (α = β = Unit)
theorem c4_15 : ¬ drop0% Finite.exists_infinite_fiber 2 := fun h => by obtain ⟨y, hy⟩ := @h Unit Unit _ id; exact not_finite (id ⁻¹' {y} : Set Unit)

-- `Finite.exists_infinite_fiber` idx 3: necessary (α = β = ℕ, f = id)
theorem c4_16 : ¬ drop0% Finite.exists_infinite_fiber 3 := fun h => by obtain ⟨y, hy⟩ := @h ℕ ℕ _ id; exact Set.infinite_coe_iff.mp hy (by simp)

-- `Set.instFinite` idx 1: necessary (α = ℕ)
theorem c4_17 : ¬ drop0% Set.instFinite 1 := fun h => @not_finite (Set ℕ) _ (@h ℕ)

-- `Finset.product_eq_univ` idx 6: necessary (α = Empty, β = Unit, t = ∅)
theorem c4_18 : ¬ drop0% Finset.product_eq_univ 6 := fun h => absurd (@h Empty Unit _ _ ∅ ∅ _) (by decide)

-- `Finset.product_eq_univ` idx 7: necessary (α = Unit, β = Empty, s = ∅)
theorem c4_19 : ¬ drop0% Finset.product_eq_univ 7 := fun h => absurd (@h Unit Empty _ _ ∅ ∅ _) (by decide)

-- `Pi.infinite_of_left` idx 2: necessary (universe 1: ι = ℕ, π = PUnit)
theorem c4_20 : ¬ drop1% Pi.infinite_of_left 2 := fun h => @not_finite _ (@h ℕ (fun _ => PUnit) _) _

-- `Pi.infinite_of_left` idx 3: necessary (universe 1: ι = Unit, π = ULift Bool)
theorem c4_21 : ¬ drop1% Pi.infinite_of_left 3 := fun h => @not_finite _ (@h Unit (fun _ => ULift Bool) _) _

-- `Pi.infinite_of_exists_right` idx 3: necessary (universe 1: ι = Unit, π = PUnit)
theorem c4_22 : ¬ drop1% Pi.infinite_of_exists_right 3 := fun h => @not_finite _ (@h Unit (fun _ => PUnit) () _) _

-- `Pi.infinite_of_exists_right` idx 4: necessary (universe 1: ι = Bool, π true = ℕ, π false = Empty)
theorem c4_23 : ¬ drop1% Pi.infinite_of_exists_right 4 := fun h => by
  have : IsEmpty (∀ b : Bool, cond b ℕ Empty) := ⟨fun f => (f false).elim⟩
  exact @not_finite _ (@h Bool (fun b => cond b ℕ Empty) true (inferInstanceAs (Infinite ℕ))) inferInstance

-- `Pi.infinite_of_right` idx 2: necessary (universe 1: ι = Unit, π = PUnit)
theorem c4_24 : ¬ drop1% Pi.infinite_of_right 2 := fun h => @not_finite _ (@h Unit (fun _ => PUnit) _) _

-- `Pi.infinite_of_right` idx 3: necessary (universe 1: ι = Empty)
theorem c4_25 : ¬ drop1% Pi.infinite_of_right 3 := fun h => @not_finite _ (@h Empty (fun _ => ULift ℕ) _) _

-- `Function.infinite_of_left` idx 2: necessary (universe 1: ι = ℕ, π = PUnit)
theorem c4_26 : ¬ drop1% Function.infinite_of_left 2 := fun h => @not_finite _ (@h ℕ PUnit _) _

-- `Function.infinite_of_left` idx 3: necessary (universe 1: ι = Unit, π = ULift Bool)
theorem c4_27 : ¬ drop1% Function.infinite_of_left 3 := fun h => @not_finite _ (@h Unit (ULift Bool) _) _

-- `Function.infinite_of_right` idx 2: necessary (universe 1: ι = Unit, π = PUnit)
theorem c4_28 : ¬ drop1% Function.infinite_of_right 2 := fun h => @not_finite _ (@h Unit PUnit _) _

-- `Function.infinite_of_right` idx 3: necessary (universe 1: ι = Empty, π = ULift ℕ)
theorem c4_29 : ¬ drop1% Function.infinite_of_right 3 := fun h => @not_finite _ (@h Empty (ULift ℕ) _) _

-- `Quotient.list_ind` idx 6: necessary (C := False, l = [])
theorem c4_30 : ¬ drop0% Quotient.list_ind 6 := fun h => @h Unit _ (fun _ => True) (fun _ => ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩) [] (fun _ => False) (fun i hi => nomatch hi)

-- `Quotient.ind_fintype_pi` idx 6: necessary (C := False, ι = Unit)
theorem c4_31 : ¬ drop0% Quotient.ind_fintype_pi 6 := fun h => @h Unit _ _ (fun _ => True) (fun _ => ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩) (fun _ => False) (fun _ => Quotient.mk _ trivial)

-- `Quotient.induction_on_fintype_pi` idx 7: necessary (C := False, ι = Unit)
theorem c4_32 : ¬ drop0% Quotient.induction_on_fintype_pi 7 := fun h => @h Unit _ _ (fun _ => True) (fun _ => ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩) (fun _ => False) (fun _ => Quotient.mk _ trivial)

-- `Quotient.finLiftOn_empty` idx 6: necessary (dependent: ι = Unit)
theorem c4_33 : ¬ indep0% Quotient.finLiftOn_empty 6 := fun h => (@h Unit _ _ (fun _ => True) (fun _ => ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩) True (fun _ => Quotient.mk _ trivial)).false ()

-- `Trunc.finLiftOn_empty` idx 5: necessary (dependent: ι = Unit)
theorem c4_34 : ¬ indep0% Trunc.finLiftOn_empty 5 := fun h => (@h Unit _ _ (fun _ => True) True (fun _ => Trunc.mk trivial)).false ()

-- `Shrink.instFinite` idx 1: necessary (dependent: α = ℕ)
theorem c4_35 : ¬ indep0% Shrink.instFinite 1 := fun h => @not_finite ℕ _ (@h ℕ)

-- `finSumEquivOfFinset_inl` idx 7: necessary (dependent: α = Bool, s = ∅, m = 1, n = 2)
theorem c4_36 : ¬ indep0% finSumEquivOfFinset_inl 7 := fun h => absurd (@h Bool _ _ _ 1 2 ∅ (by decide) 0) (by decide)

-- `finSumEquivOfFinset_inl` idx 8: necessary (dependent: s = {true}, m = 1, n = 0)
theorem c4_37 : ¬ indep0% finSumEquivOfFinset_inl 8 := fun h => absurd (@h Bool _ _ _ 1 0 {true} (by decide) 0) (by decide)

-- `finSumEquivOfFinset_inr` idx 7: necessary (dependent: s = ∅, m = 1, n = 2)
theorem c4_38 : ¬ indep0% finSumEquivOfFinset_inr 7 := fun h => absurd (@h Bool _ _ _ 1 2 ∅ (by decide) 0) (by decide)

-- `finSumEquivOfFinset_inr` idx 8: necessary (dependent: s = {true}, m = 1, n = 2)
theorem c4_39 : ¬ indep0% finSumEquivOfFinset_inr 8 := fun h => absurd (@h Bool _ _ _ 1 2 {true} (by decide) 0) (by decide)

-- `Finset.exists_equiv_extend_of_card_eq` idx 8: necessary (α = Unit, t = {true}, f = const false)
theorem c4_40 : ¬ drop0% Finset.exists_equiv_extend_of_card_eq 8 := fun h => by
  obtain ⟨g, hg⟩ := @h Unit Bool _ _ {true} (by decide) Finset.univ (fun _ => false) (by simp [Set.InjOn])
  have := (g ()).2; rw [hg () (by simp)] at this; simp at this

-- `Finset.exists_equiv_extend_of_card_eq` idx 9: necessary (α = β = Bool, t = univ, f = const true)
theorem c4_41 : ¬ drop0% Finset.exists_equiv_extend_of_card_eq 9 := fun h => by
  obtain ⟨g, hg⟩ := @h Bool Bool _ _ Finset.univ (by simp) Finset.univ (fun _ => true) (by simp)
  have := g.injective (Subtype.ext ((hg true (by simp)).trans (hg false (by simp)).symm)); simp at this

-- `Set.MapsTo.exists_equiv_extend_of_card_eq` idx 7: necessary (α = Unit, t = {true}, f = const false)
theorem c4_42 : ¬ drop0% Set.MapsTo.exists_equiv_extend_of_card_eq 7 := fun h => by
  obtain ⟨g, hg⟩ := @h Unit Bool _ {true} (by decide) Set.univ (fun _ => false) (by simp [Set.InjOn])
  have := (g ()).2; rw [hg () (by simp)] at this; simp at this

-- `Set.MapsTo.exists_equiv_extend_of_card_eq` idx 8: necessary (α = β = Bool, t = univ, f = const true)
theorem c4_43 : ¬ drop0% Set.MapsTo.exists_equiv_extend_of_card_eq 8 := fun h => by
  obtain ⟨g, hg⟩ := @h Bool Bool _ Finset.univ (by simp) Set.univ (fun _ => true) (by simp [Set.MapsTo])
  have := g.injective (Subtype.ext ((hg true (by simp)).trans (hg false (by simp)).symm)); simp at this

-- `List.Vector.instFinite` idx 1: necessary (α = ℕ, n = 1)
theorem c4_44 : ¬ drop0% List.Vector.instFinite 1 := fun h => @not_finite (List.Vector ℕ 1) (Infinite.of_injective (fun k : ℕ => (⟨[k], rfl⟩ : List.Vector ℕ 1)) (fun a b hab => by simpa using congrArg Subtype.val hab)) (@h ℕ 1)

-- `Sym.instFinite` idx 1: necessary (α = ℕ, n = 1)
theorem c4_45 : ¬ drop0% Sym.instFinite 1 := fun h => @not_finite (Sym ℕ 1) (Infinite.of_injective _ Sym.oneEquiv.injective) (@h ℕ 1)

-- `Sym.Sym'.instFinite` idx 1: necessary (α = ℕ, n = 1)
theorem c4_46 : ¬ drop0% Sym.Sym'.instFinite 1 := fun h => @not_finite (Sym.Sym' ℕ 1) (Infinite.of_injective (fun k => Sym.symEquivSym' (Sym.oneEquiv k)) (Sym.symEquivSym'.injective.comp Sym.oneEquiv.injective)) (@h ℕ 1)

-- `instFiniteWithBot` idx 1: necessary (α = ℕ)
theorem c4_47 : ¬ drop0% instFiniteWithBot 1 := fun h => @not_finite (WithBot ℕ) (Infinite.of_injective _ WithBot.coe_injective) (@h ℕ)

-- `instFiniteWithTop` idx 1: necessary (α = ℕ)
theorem c4_48 : ¬ drop0% instFiniteWithTop 1 := fun h => @not_finite (WithTop ℕ) (Infinite.of_injective _ WithTop.coe_injective) (@h ℕ)

-- `DFunLike.finite` idx 4: necessary (universe 1: F = ℕ → Bool)
theorem c4_49 : ¬ drop1% DFunLike.finite 4 := fun h => @not_finite (W2c4.PF ℕ Bool) (inferInstanceAs (Infinite (ℕ → Bool))) (@h (W2c4.PF ℕ Bool) ℕ (fun _ => Bool) _ _)

-- `DFunLike.finite` idx 5: necessary (universe 1: F = Unit → ℕ)
theorem c4_50 : ¬ drop1% DFunLike.finite 5 := fun h => @not_finite (W2c4.PF Unit ℕ) (inferInstanceAs (Infinite (Unit → ℕ))) (@h (W2c4.PF Unit ℕ) Unit (fun _ => ℕ) _ _)

-- `FunLike.finite` idx 4: necessary (universe 1: G = ℕ → Bool)
theorem c4_51 : ¬ drop1% FunLike.finite 4 := fun h => @not_finite (W2c4.PF ℕ Bool) (inferInstanceAs (Infinite (ℕ → Bool))) (@h (W2c4.PF ℕ Bool) ℕ Bool _ _)

-- `FunLike.finite` idx 5: necessary (universe 1: G = Unit → ℕ)
theorem c4_52 : ¬ drop1% FunLike.finite 5 := fun h => @not_finite (W2c4.PF Unit ℕ) (inferInstanceAs (Infinite (Unit → ℕ))) (@h (W2c4.PF Unit ℕ) Unit ℕ _ _)

-- `Holor.cast_type` idx 3: necessary (dependent: ds₁ = [], ds₂ = [0])
theorem c4_53 : ¬ indep0% Holor.cast_type 3 := fun h => absurd (@h ℕ [] [0] (fun _ => 0)) (by decide)

-- `Holor.holor_index_cons_decomp` idx 4: necessary (p := False, t = [0] in shape [1])
theorem c4_54 : ¬ drop0% Holor.holor_index_cons_decomp 4 := fun h => @h 1 [] (fun _ => False) ⟨[0], .cons (by decide) .nil⟩

-- `Holor.slice_eq` idx 5: necessary (shape [1], x = 0, y = 1)
theorem c4_55 : ¬ drop0% Holor.slice_eq 5 := fun h => absurd (congrFun (@h ℕ 1 [] (fun _ => 0) (fun _ => 1)) ⟨[0], .cons (by decide) .nil⟩) (by decide)

-- `Holor.slice_unitVec_mul` idx 6: necessary (dependent: d = 0, i = 0)
theorem c4_56 : ¬ indep0% Holor.slice_unitVec_mul 6 := fun h => absurd (@h ℕ 0 [] _ 0 0 (fun _ => 0)) (by decide)

-- `Holor.slice_add` idx 5: necessary (dependent: d = 0, i = 0)
theorem c4_57 : ¬ indep0% Holor.slice_add 5 := fun h => absurd (@h ℕ 0 [] _ 0 (fun _ => 0) (fun _ => 0)) (by decide)

-- `Holor.slice_sum` idx 6: necessary (dependent: d = 0, i = 0)
theorem c4_58 : ¬ indep0% Holor.slice_sum 6 := fun h => absurd (@h ℕ 0 [] _ Unit 0 ∅ (fun _ _ => 0)) (by decide)

-- `Holor.cprankMax_add` idx 8: necessary (m = n = 0, x = 1, y = 0)
theorem c4_59 : ¬ drop0% Holor.cprankMax_add 8 := fun h => absurd (congrFun (W2c4.cp0 (@h ℕ [] _ _ 0 0 (fun _ => 1) 0 .zero)) ⟨[], .nil⟩) (by decide)

-- `Holor.cprankMax_add` idx 9: necessary (m = n = 0, x = 0, y = 1)
theorem c4_60 : ¬ drop0% Holor.cprankMax_add 9 := fun h => absurd (congrFun (W2c4.cp0 (@h ℕ [] _ _ 0 0 0 (fun _ => 1) .zero)) ⟨[], .nil⟩) (by decide)

-- `Holor.cprankMax_mul` idx 7: necessary (n = 0, x = y = 1 (shape [1] ⊗ []): x ⊗ y ≠ 0)
theorem c4_61 : ¬ drop0% Holor.cprankMax_mul 7 := fun h => absurd (congrFun (W2c4.cp0 (@h ℕ 1 [] _ 0 (fun _ => 1) (fun _ => 1))) ⟨[0], .cons (by decide) .nil⟩) (by simp [Holor.mul])

-- `Holor.cprankMax_1` idx 5: necessary (α = ℕ with zero multiplication: rank-one holors of shape [1] vanish, 1 is not of rank ≤ 1)
theorem c4_62 : ¬ drop0% Holor.cprankMax_1 5 := fun h => by
  have := @h W2c4.NZ [1] _ _ (fun _ => (1:ℕ))
  generalize hx : (fun _ => (1:ℕ) : Holor W2c4.NZ [1]) = x at this
  rcases this with _ | ⟨_, x1, y1, h1, h0⟩
  have e := congrFun hx ⟨[0], .cons (by decide) .nil⟩
  rw [W2c4.cp0 h0] at e
  have := W2c4.cp1 h1 ⟨[0], .cons (by decide) .nil⟩ (by simp)
  change (1:ℕ) = _ + (0:ℕ) at e
  rw [this] at e; exact absurd e (by decide)

-- `_private.Mathlib.Data.Int.GCD.0.Nat.xgcdAux_P` idx 8: necessary (x = y = 0, (r,s,t) = (1,0,0), (r',s',t') = 0: result (1,0,0))
theorem c4_63 : ¬ drop0% _private.Mathlib.Data.Int.GCD.«0».Nat.xgcdAux_P 8 := fun h => by
  have hP := @h 0 0 1 0 0 0 0 0 (by show ((0:ℕ):ℤ) = ((0:ℕ):ℤ) * 0 + ((0:ℕ):ℤ) * 0; decide)
  rw [Nat.xgcdAux_rec (by decide)] at hP; simp only [Nat.zero_mod, Nat.xgcd_zero_left] at hP
  change ((1:ℕ):ℤ) = _ at hP; simp at hP

-- `_private.Mathlib.Data.Int.GCD.0.Nat.xgcdAux_P` idx 9: necessary (x = y = 0, r = 0, r' = 1: result (1,0,0))
theorem c4_64 : ¬ drop0% _private.Mathlib.Data.Int.GCD.«0».Nat.xgcdAux_P 9 := fun h => by
  have hP := @h 0 0 0 1 0 0 0 0 (by show ((0:ℕ):ℤ) = ((0:ℕ):ℤ) * 0 + ((0:ℕ):ℤ) * 0; decide)
  rw [Nat.xgcd_zero_left] at hP
  change ((1:ℕ):ℤ) = _ at hP; simp at hP

-- `WithZeroMulInt.toNNReal_eq_one_iff` idx 3: necessary (e = 1, m = ofAdd 1: e ^ 1 = 1 but m ≠ 1)
theorem c4_65 : ¬ drop0% WithZeroMulInt.toNNReal_eq_one_iff 3 := fun h => absurd ((@h 1 (WithZero.coe (Multiplicative.ofAdd 1)) one_ne_zero).mp (by rw [WithZeroMulInt.toNNReal_neg_apply _ (by simp)]; simp)) (by decide)

-- `Int.strongRec_of_ge` idx 5: necessary (m = 1, n = 0)
theorem c4_66 : ¬ indep0% Int.strongRec_of_ge 5 := fun h => absurd (@h 1 0 (fun _ => True) (fun _ _ => trivial) (fun _ _ _ => trivial)) (by decide)

-- `Int.strongRec_of_lt` idx 5: necessary (m = n = 0)
theorem c4_67 : ¬ indep0% Int.strongRec_of_lt 5 := fun h => absurd (@h 0 0 (fun _ => True) (fun _ _ => trivial) (fun _ _ _ => trivial)) (by decide)

-- `Int.inductionOn'_add_one` idx 6: necessary (z = 0, b = 1)
theorem c4_68 : ¬ indep0% Int.inductionOn'_add_one 6 := fun h => absurd (@h (fun _ => True) 0 1 trivial (fun _ _ _ => trivial) (fun _ _ _ => trivial)) (by decide)

-- `Int.inductionOn'_sub_one` idx 6: necessary (z = 1, b = 0)
theorem c4_69 : ¬ indep0% Int.inductionOn'_sub_one 6 := fun h => absurd (@h (fun _ => True) 1 0 trivial (fun _ _ _ => trivial) (fun _ _ _ => trivial)) (by decide)

-- `Int.leInduction_add_one` idx 5: necessary (m = 1, n = 0)
theorem c4_70 : ¬ indep0% Int.leInduction_add_one 5 := fun h => absurd (@h 1 (fun _ _ => True) trivial (fun _ _ _ => trivial) 0) (by decide)

-- `Int.leInductionDown_sub_one` idx 5: necessary (m = 0, n = 1)
theorem c4_71 : ¬ indep0% Int.leInductionDown_sub_one 5 := fun h => absurd (@h 0 (fun _ _ => True) trivial (fun _ _ _ => trivial) 1) (by decide)

-- `Int.induction_on` idx 2: necessary (motive := False, i = 0)
theorem c4_72 : ¬ drop0% Int.induction_on 2 := fun h => @h (fun _ => False) 0 (fun _ h => h) (fun _ h => h)

-- `Int.induction_on` idx 3: necessary (motive i := i ≤ 0, i = 1)
theorem c4_73 : ¬ drop0% Int.induction_on 3 := fun h => absurd (@h (fun i => i ≤ 0) 1 (by decide) (fun i hi => by omega)) (by decide)

-- `Int.induction_on` idx 4: necessary (motive i := 0 ≤ i, i = -1)
theorem c4_74 : ¬ drop0% Int.induction_on 4 := fun h => absurd (@h (fun i => 0 ≤ i) (-1) (by decide) (fun i hi => by omega)) (by decide)

-- `Int.ediv_of_neg_of_pos` idx 2: removable (for 0 < b the identity a / b = -((-a-1)/b + 1) holds for every a (floor division))
theorem c4_75 : drop% Int.ediv_of_neg_of_pos 2 := by
  intro a b hb
  have e1 := Int.emod_def a b
  have e2 := Int.emod_nonneg a (by omega : b ≠ 0)
  have e3 := Int.emod_lt_of_pos a hb
  have := (Int.ediv_emod_unique hb).mpr (show b - 1 - a % b + b * (-(a/b) - 1) = -a-1 ∧ 0 ≤ b - 1 - a % b ∧ b - 1 - a % b < b from ⟨by linarith, by omega, by omega⟩)
  show a / b = _
  rw [this.1]; ring

-- `Int.div_le_iff_of_dvd_of_neg` idx 4: removable (for b < 0, a / b ≤ c ↔ b * c ≤ a holds without b ∣ a (ediv rounds toward the correct side))
theorem c4_76 : drop% Int.div_le_iff_of_dvd_of_neg 4 := by intro a b c hb; exact W2c4.H1 hb

-- `Int.div_lt_iff_of_dvd_of_pos` idx 4: removable (for 0 < b, a / b < c ↔ a < b * c holds without b ∣ a (Int.ediv_lt_iff_lt_mul))
theorem c4_77 : drop% Int.div_lt_iff_of_dvd_of_pos 4 := by intro a b c hb; rw [Int.ediv_lt_iff_lt_mul hb, mul_comm]

-- `Int.le_div_iff_of_dvd_of_pos` idx 4: removable (for 0 < c, a ≤ b / c ↔ c * a ≤ b holds without c ∣ b (Int.le_ediv_iff_mul_le))
theorem c4_78 : drop% Int.le_div_iff_of_dvd_of_pos 4 := by intro a b c hc; rw [Int.le_ediv_iff_mul_le hc, mul_comm]

-- `Int.lt_div_iff_of_dvd_of_neg` idx 4: removable (for c < 0, a < b / c ↔ b < c * a holds without c ∣ b)
theorem c4_79 : drop% Int.lt_div_iff_of_dvd_of_neg 4 := by intro a b c hc; exact W2c4.H4 hc

-- `Int.div_le_div_iff_of_dvd_of_pos_of_pos` idx 7: removable (with b ∣ a and b, d > 0, d ∣ c is not needed: a/b = k, k ≤ c/d ↔ d k ≤ c)
theorem c4_80 : drop% Int.div_le_div_iff_of_dvd_of_pos_of_pos 7 := by
  intro a b c d hb hd hba; obtain ⟨k, rfl⟩ := hba; rw [Int.mul_ediv_cancel_left _ (by omega), Int.le_ediv_iff_mul_le hd]
  constructor <;> intro h <;> nlinarith

-- `Int.div_le_div_iff_of_dvd_of_neg_of_pos` idx 6: removable (d ∣ c suffices: c/d exact, then the one-division iff for b < 0)
theorem c4_81 : drop% Int.div_le_div_iff_of_dvd_of_neg_of_pos 6 := by
  intro a b c d hb hd hdc; obtain ⟨m, rfl⟩ := hdc; rw [Int.mul_ediv_cancel_left _ (by omega), W2c4.H1 hb]
  constructor <;> intro h <;> nlinarith

-- `Int.div_le_div_iff_of_dvd_of_neg_of_pos` idx 7: removable (b ∣ a suffices: a/b exact, then Int.le_ediv_iff_mul_le for d > 0)
theorem c4_82 : drop% Int.div_le_div_iff_of_dvd_of_neg_of_pos 7 := by
  intro a b c d hb hd hba; obtain ⟨k, rfl⟩ := hba; rw [Int.mul_ediv_cancel_left _ (by omega), Int.le_ediv_iff_mul_le hd]
  constructor <;> intro h <;> nlinarith

-- `Int.div_le_div_iff_of_dvd_of_neg_of_neg` idx 6: removable (d ∣ c suffices: c/d exact, then the one-division iff for b < 0)
theorem c4_83 : drop% Int.div_le_div_iff_of_dvd_of_neg_of_neg 6 := by
  intro a b c d hb hd hdc; obtain ⟨m, rfl⟩ := hdc; rw [Int.mul_ediv_cancel_left _ (by omega), W2c4.H1 hb]
  constructor <;> intro h <;> nlinarith

-- `Int.div_lt_div_iff_of_dvd_of_pos` idx 6: removable (d ∣ c suffices: c/d exact, then Int.ediv_lt_iff_lt_mul)
theorem c4_84 : drop% Int.div_lt_div_iff_of_dvd_of_pos 6 := by
  intro a b c d hb hd hdc; obtain ⟨m, rfl⟩ := hdc; rw [Int.mul_ediv_cancel_left _ (by omega), Int.ediv_lt_iff_lt_mul hb]
  constructor <;> intro h <;> nlinarith

-- `Int.div_lt_div_iff_of_dvd_of_pos_of_neg` idx 6: removable (d ∣ c suffices: c/d exact, then Int.ediv_lt_iff_lt_mul for b > 0)
theorem c4_85 : drop% Int.div_lt_div_iff_of_dvd_of_pos_of_neg 6 := by
  intro a b c d hb hd hdc; obtain ⟨m, rfl⟩ := hdc; rw [Int.mul_ediv_cancel_left _ (by omega), Int.ediv_lt_iff_lt_mul hb]
  constructor <;> intro h <;> nlinarith

-- `Int.div_lt_div_iff_of_dvd_of_pos_of_neg` idx 7: removable (b ∣ a suffices: a/b exact, then the one-division iff for d < 0)
theorem c4_86 : drop% Int.div_lt_div_iff_of_dvd_of_pos_of_neg 7 := by
  intro a b c d hb hd hba; obtain ⟨k, rfl⟩ := hba; rw [Int.mul_ediv_cancel_left _ (by omega), W2c4.H4 hd]
  constructor <;> intro h <;> nlinarith

-- `Int.div_lt_div_iff_of_dvd_of_neg_of_neg` idx 7: removable (b ∣ a suffices: a/b exact, then the one-division iff for d < 0)
theorem c4_87 : drop% Int.div_lt_div_iff_of_dvd_of_neg_of_neg 7 := by
  intro a b c d hb hd hba; obtain ⟨k, rfl⟩ := hba; rw [Int.mul_ediv_cancel_left _ (by omega), W2c4.H4 hd]
  constructor <;> intro h <;> nlinarith

-- `Int.dvd_mul_of_div_dvd` idx 3: necessary (a = 3, b = 2, c = 1: 3/2 = 1 ∣ 1 but 3 ∤ 2)
theorem c4_88 : ¬ drop0% Int.dvd_mul_of_div_dvd 3 := fun h => absurd (@h 3 2 1 (by decide)) (by decide)

-- `Int.eq_mul_div_of_mul_eq_mul_of_dvd_left` idx 5: necessary (a = 1, b = 2, c = 1, d = 2)
theorem c4_89 : ¬ drop0% Int.eq_mul_div_of_mul_eq_mul_of_dvd_left 5 := fun h => absurd (@h 1 2 1 2 (by decide) (by decide)) (by decide)

-- `Int.fdiv_fdiv_eq_fdiv_mul` idx 3: removable (0 ≤ n not needed: for n < 0 rewrite with Int.neg_fdiv_neg and apply the theorem to -m, -n)
theorem c4_90 : drop% Int.fdiv_fdiv_eq_fdiv_mul 3 := by
  intro m n k hk; rcases le_or_gt 0 n with hn | hn
  · exact Int.fdiv_fdiv_eq_fdiv_mul m hn hk
  · rw [← Int.neg_fdiv_neg m n, Int.fdiv_fdiv_eq_fdiv_mul (-m) (by omega) hk, ← Int.neg_fdiv_neg m (n*k)]; congr 1; ring

-- `Nat.count_modEq_card` idx 2: removable (r = 0: ≡ [MOD 0] is equality, count = [v < b] = b/0 + [v%0 < b%0])
theorem c4_91 : drop% Nat.count_modEq_card 2 := by
  intro b r v
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [Nat.ModEq, Nat.count_eq_card_filter_range, Finset.filter_eq']; split_ifs <;> simp
  · exact @Nat.count_modEq_card b r hr v

-- `Int.exists_gcd_one` idx 2: removable (m = n = 0 (gcd 0): m' = 1, n' = 0 works)
theorem c4_92 : drop% Int.exists_gcd_one 2 := by
  intro m n
  rcases Nat.eq_zero_or_pos (m.gcd n) with h | h
  · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp h
    exact ⟨1, 0, by decide, by simp, by simp⟩
  · exact Int.exists_gcd_one h

-- `Int.exists_gcd_one'` idx 2: necessary (m = n = 0: g > 0 forces m' = n' = 0, gcd 0 0 ≠ 1)
theorem c4_93 : ¬ drop0% Int.exists_gcd_one' 2 := fun h => by
  obtain ⟨g, m', n', hg, h1, h2, h3⟩ := @h 0 0
  have : m' = 0 := by rcases mul_eq_zero.mp h2.symm with h | h; exact h; omega
  have : n' = 0 := by rcases mul_eq_zero.mp h3.symm with h | h; exact h; omega
  subst_vars; simp at h1

-- `Int.ModEq.of_div` idx 7: necessary (m = 3, a = 0, b = 2, c = 2: m/c = 1)
theorem c4_94 : ¬ drop0% Int.ModEq.of_div 7 := fun h => absurd (@h 3 0 2 2 (by decide) (by decide) (by decide)) (by decide)

-- `Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul` idx 1: necessary (p = 4, m = n = 2, k = l = 0)
theorem c4_95 : ¬ drop0% Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul 1 := fun h => absurd (@h 4 2 2 0 0 (by decide) (by decide) (by decide)) (by decide)

-- `Int.Prime.dvd_natAbs_of_coe_dvd_sq` idx 1: necessary (p = 4, k = 2)
theorem c4_96 : ¬ drop0% Int.Prime.dvd_natAbs_of_coe_dvd_sq 1 := fun h => absurd (@h 4 2 (by decide)) (by decide)

-- `AddCommGroup.ModEq.intCast` idx 2: removable (ModEq.map along Int.castAddHom; CharZero only needed for the converse)
theorem c4_97 : drop% AddCommGroup.ModEq.intCast 2 := by intro G _ a b z h; simpa using h.map (Int.castAddHom G)

-- `SemiconjBy.intCast_mul_intCast_mul` idx 5: necessary (ℤ, a = 1, x = 0, y = 1, m = n = 1)
theorem c4_98 : ¬ drop0% SemiconjBy.intCast_mul_intCast_mul 5 := fun h => absurd (@h ℤ _ 1 0 1 1 1) (by unfold SemiconjBy; decide)

-- `Commute.intCast_mul_right` idx 4: necessary (2×2 integer matrix units E11, E12, m = 1)
theorem c4_99 : ¬ drop0% Commute.intCast_mul_right 4 := fun h => absurd (@h (Matrix (Fin 2) (Fin 2) ℤ) _ !![1,0;0,0] !![0,1;0,0] 1) (by unfold Commute SemiconjBy; decide)

-- `Commute.pow_eq_pow_iff_of_coprime` idx 6: necessary (WithZero (Perm (Fin 3)), a = swap 0 1, b = 3-cycle, m = 2, n = 3: a^2 = b^3 = 1 but no c)
theorem c4_100 : ¬ drop0% Commute.pow_eq_pow_iff_of_coprime 6 := fun h => by
  have := (@h (WithZero (Equiv.Perm (Fin 3))) _ (↑(Equiv.swap (0:Fin 3) 1)) (↑(finRotate 3)) 2 3 (by decide)).mp
    (by rw [← WithZero.coe_pow, ← WithZero.coe_pow]; congr 1; decide)
  obtain ⟨c, h1, h2⟩ := this
  induction c using WithZero.recZeroCoe with
  | zero => simp at h1
  | coe g => rw [← WithZero.coe_pow, WithZero.coe_inj] at h1 h2; revert h1 h2; revert g; decide

-- `Int.cast_div` idx 5: necessary (α = ZMod 2 (field), m = n = 2: ↑1 = 1 ≠ 0 = 0/0)
theorem c4_101 : ¬ drop0% Int.cast_div 5 := fun h => absurd (@h W2c4.Z2 _ 2 2 (by decide)) (by rw [show ((2:ℤ):W2c4.Z2) = 0 by decide, div_zero]; decide)

-- `Int.cast_div_charZero` idx 2: necessary (k = ZMod 2, m = n = 2)
theorem c4_102 : ¬ drop0% Int.cast_div_charZero 2 := fun h => absurd (@h W2c4.Z2 _ 2 2 (by decide)) (by rw [show ((2:ℤ):W2c4.Z2) = 0 by decide, div_zero]; decide)

-- `Int.cast_div_ofNat_charZero` idx 2: necessary (k = ZMod 2, m = n = 2)
theorem c4_103 : ¬ drop0% Int.cast_div_ofNat_charZero 2 := fun h => absurd (@h W2c4.Z2 _ 2 2 (by decide)) (by rw [show ((2:ℕ):W2c4.Z2) = 0 by decide, div_zero]; decide)

-- `RingHom.injective_int` idx 3: necessary (α = ZMod 2, 0 and 2 have the same image)
theorem c4_104 : ¬ drop0% RingHom.injective_int 3 := fun h => absurd (@h W2c4.Z2 _ (Int.castRingHom _) 0 2 (by decide)) (by decide)

-- `Function.support_intCast` idx 3: necessary (β = ZMod 2, n = 2, α = Unit)
theorem c4_105 : ¬ drop0% Function.support_intCast 3 := fun h => absurd (congrArg (() ∈ ·) (@h Unit W2c4.Z2 _ 2 (by decide))) (by simp; decide)

-- `Function.support_intCast` idx 5: necessary (n = 0, α = Unit, β = ℤ)
theorem c4_106 : ¬ drop0% Function.support_intCast 5 := fun h => absurd (congrArg (() ∈ ·) (@h Unit ℤ _ _ 0)) (by simp)

-- `Function.mulSupport_intCast` idx 3: necessary (β = ZMod 2, n = 3 (↑3 = 1))
theorem c4_107 : ¬ drop0% Function.mulSupport_intCast 3 := fun h => absurd (congrArg (() ∈ ·) (@h Unit W2c4.Z2 _ 3 (by decide))) (by simp; decide)

-- `Function.mulSupport_intCast` idx 5: necessary (n = 1, β = ℤ)
theorem c4_108 : ¬ drop0% Function.mulSupport_intCast 5 := fun h => absurd (congrArg (() ∈ ·) (@h Unit ℤ _ _ 1)) (by simp)

-- `Commute.intCast_mul_left` idx 4: necessary (2×2 integer matrix units E11, E12, m = 1)
theorem c4_109 : ¬ drop0% Commute.intCast_mul_left 4 := fun h => absurd (@h (Matrix (Fin 2) (Fin 2) ℤ) _ !![1,0;0,0] !![0,1;0,0] 1) (by unfold Commute SemiconjBy; decide)

-- `Commute.intCast_mul_intCast_mul` idx 4: necessary (2×2 integer matrix units E11, E12, m = n = 1)
theorem c4_110 : ¬ drop0% Commute.intCast_mul_intCast_mul 4 := fun h => absurd (@h (Matrix (Fin 2) (Fin 2) ℤ) _ !![1,0;0,0] !![0,1;0,0] 1 1) (by unfold Commute SemiconjBy; decide)

-- `AddMonoidHom.ext_int` idx 4: necessary (f = 0, g = id on ℤ)
theorem c4_111 : ¬ drop0% AddMonoidHom.ext_int 4 := fun h => absurd (congrArg (· 1) (@h ℤ _ 0 (AddMonoidHom.id ℤ))) (by simp)

-- `AddMonoidHom.eq_intCastAddHom` idx 3: necessary (f = 0)
theorem c4_112 : ¬ drop0% AddMonoidHom.eq_intCastAddHom 3 := fun h => absurd (congrArg (· 1) (@h ℤ _ 0)) (by simp)

-- `AddEquiv.ext_int` idx 4: necessary (refl vs neg on ℤ)
theorem c4_113 : ¬ drop0% AddEquiv.ext_int 4 := fun h => absurd (congrArg (· 1) (@h ℤ _ (AddEquiv.refl ℤ) (AddEquiv.neg ℤ))) (by simp)

-- `eq_intCast'` idx 4: necessary (FunLike ℤ → ℤ, x ↦ x² (f 1 = 1, f 2 = 4))
theorem c4_114 : ¬ drop0% eq_intCast' 4 := fun h => absurd (@h W2c4.FZ ℤ _ _ () rfl 2) (by decide)

-- `eq_intCast'` idx 6: necessary (f = 0 : ℤ →+ ℤ)
theorem c4_115 : ¬ drop0% eq_intCast' 6 := fun h => absurd (@h (ℤ →+ ℤ) ℤ _ _ _ 0 1) (by simp)

-- `map_intCast'` idx 6: necessary (FunLike ℤ → ℤ, x ↦ x²)
theorem c4_116 : ¬ drop0% map_intCast' 6 := fun h => absurd (@h W2c4.FZ ℤ ℤ _ _ _ () rfl 2) (by decide)

-- `map_intCast'` idx 8: necessary (f = 0 : ℤ →+ ℤ)
theorem c4_117 : ¬ drop0% map_intCast' 8 := fun h => absurd (@h (ℤ →+ ℤ) ℤ ℤ _ _ _ _ 0 1) (by simp)

-- `MonoidHom.ext_mint` idx 4: necessary (trivial hom vs id on Multiplicative ℤ)
theorem c4_118 : ¬ drop0% MonoidHom.ext_mint 4 := fun h => absurd (congrArg (· (Multiplicative.ofAdd 1)) (@h (Multiplicative ℤ) _ 1 (MonoidHom.id _))) (by decide)

-- `MonoidHom.ext_int` idx 4: necessary (id vs |·| on (ℤ, *): agree on ℕ, differ at -1)
theorem c4_119 : ¬ drop0% MonoidHom.ext_int 4 := fun h => absurd (congrArg (· (-1)) (@h ℤ _ (MonoidHom.id ℤ) W2c4.absZ.toMonoidHom (by ext n; simp [W2c4.absZ]))) (by simp [W2c4.absZ])

-- `MonoidHom.ext_int` idx 5: necessary (id vs sign: agree at -1, differ at 2)
theorem c4_120 : ¬ drop0% MonoidHom.ext_int 5 := fun h => absurd (congrArg (· 2) (@h ℤ _ (MonoidHom.id ℤ) W2c4.sgnZ.toMonoidHom (by decide))) (by decide)

-- `MonoidWithZeroHom.ext_int` idx 4: necessary (id vs |·|)
theorem c4_121 : ¬ drop0% MonoidWithZeroHom.ext_int 4 := fun h => absurd (congrArg (· (-1)) (@h ℤ _ (MonoidWithZeroHom.id ℤ) W2c4.absZ (by ext n; simp [W2c4.absZ]))) (by simp [W2c4.absZ])

-- `MonoidWithZeroHom.ext_int` idx 5: necessary (id vs sign)
theorem c4_122 : ¬ drop0% MonoidWithZeroHom.ext_int 5 := fun h => absurd (congrArg (· 2) (@h ℤ _ (MonoidWithZeroHom.id ℤ) W2c4.sgnZ (by decide))) (by decide)

-- `ext_int'` idx 4: necessary (two FunLike maps ℤ → ℤ differing only at 0)
theorem c4_123 : ¬ drop0% ext_int' 4 := fun h => absurd (@h Bool ℤ _ _ true false (by decide) (fun n hn => by show (if _ then _ else _) = (if _ then _ else _); simp; omega)) (by decide)

-- `ext_int'` idx 7: necessary (id vs |·|)
theorem c4_124 : ¬ drop0% ext_int' 7 := fun h => absurd (congrArg (· (-1)) (@h (ℤ →*₀ ℤ) ℤ _ _ _ (MonoidWithZeroHom.id ℤ) W2c4.absZ (fun n hn => by simp [W2c4.absZ]))) (by simp [W2c4.absZ])

-- `ext_int'` idx 8: necessary (id vs sign)
theorem c4_125 : ¬ drop0% ext_int' 8 := fun h => absurd (congrArg (· 2) (@h (ℤ →*₀ ℤ) ℤ _ _ _ (MonoidWithZeroHom.id ℤ) W2c4.sgnZ (by decide))) (by decide)

-- `zmultiplesHom_injective` idx 2: necessary (β = ZMod 2, x = 1: 0 and 2 map to 0)
theorem c4_126 : ¬ drop0% zmultiplesHom_injective 2 := fun h => absurd (@h W2c4.Z2 _ 1 (by decide) 0 2 (by simp; decide)) (by decide)

-- `zmultiplesHom_injective` idx 4: necessary (x = 0 in ℤ)
theorem c4_127 : ¬ drop0% zmultiplesHom_injective 4 := fun h => absurd (@h ℤ _ _ 0 1 2 (by simp)) (by decide)

-- `eq_intCast` idx 4: necessary (FunLike ℤ → ℤ, x ↦ x², at 2)
theorem c4_128 : ¬ drop0% eq_intCast 4 := fun h => absurd (@h W2c4.FZ ℤ _ _ () 2) (by decide)

-- `map_intCast` idx 6: necessary (FunLike ℤ → ℤ, x ↦ x², at 2)
theorem c4_129 : ¬ drop0% map_intCast 6 := fun h => absurd (@h W2c4.FZ ℤ ℤ _ _ _ () 2) (by decide)

-- `Int.log_of_right_le_zero` idx 4: necessary (R = Q, b = 2, r = -2: φ(-1/2) = 5/2 gives log = -2)
theorem c4_130 : ¬ drop0% Int.log_of_right_le_zero 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 (-2) (by decide +kernel)) (by decide +kernel)

-- `Int.zpow_log_le_self` idx 4: necessary (R = Q, b = 2, r = 3/2 (φ r = 1/3): 2^0 ≤ r fails)
theorem c4_131 : ¬ drop0% Int.zpow_log_le_self 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 (3/2) (by decide) (by decide +kernel)) (by decide +kernel)

-- `Int.lt_zpow_succ_log_self` idx 4: necessary (R = Q, b = 2, r = 1/4: log = -2 but 1/4 < 1/2 fails in Q)
theorem c4_132 : ¬ drop0% Int.lt_zpow_succ_log_self 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 (by decide) (1/4)) (by decide +kernel)

-- `Int.log_zpow` idx 4: necessary (R = Q, b = 3, z = -1: 3^-1 = 1/3 ≥ 1 in Q, log = 0)
theorem c4_133 : ¬ drop0% Int.log_zpow 4 := fun h => absurd (@h W2c4.Q _ _ _ 3 (by decide) (-1)) (by decide +kernel)

-- `Int.log_mono_right` idx 4: necessary (R = Q, 1/2 ≤ 1/4 in Q, logs -1, -2)
theorem c4_134 : ¬ drop0% Int.log_mono_right 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 (1/2) (1/4) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Int.lt_zpow_iff_log_lt` idx 4: necessary (R = Q, b = 2, x = -1, r = 1/4)
theorem c4_135 : ¬ drop0% Int.lt_zpow_iff_log_lt 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 (by decide) (-1) (1/4) (by decide +kernel)) (by decide +kernel)

-- `Int.zpow_le_iff_le_log` idx 4: necessary (R = Q, b = 2, x = -1, r = 1/4)
theorem c4_136 : ¬ drop0% Int.zpow_le_iff_le_log 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 (by decide) (-1) (1/4) (by decide +kernel)) (by decide +kernel)

-- `Int.clog_of_right_le_zero` idx 4: necessary (R = Q, b = 2, r = -2: clog = -1)
theorem c4_137 : ¬ drop0% Int.clog_of_right_le_zero 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 (-2) (by decide +kernel)) (by decide +kernel)

-- `Int.clog_inv` idx 4: necessary (R = Q, b = 2, r = 3: 1/3 ≥ 1 in Q, clog 2 (1/3) = 1 ≠ -1)
theorem c4_138 : ¬ drop0% Int.clog_inv 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 3) (by decide +kernel)

-- `Int.log_inv` idx 4: necessary (R = Q, b = 2, r = 1/3)
theorem c4_139 : ¬ drop0% Int.log_inv 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 (1/3)) (by decide +kernel)

-- `Int.neg_log_inv_eq_clog` idx 4: necessary (R = Q, b = 2, r = 1/3)
theorem c4_140 : ¬ drop0% Int.neg_log_inv_eq_clog 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 (1/3)) (by decide +kernel)

-- `Int.neg_clog_inv_eq_log` idx 4: necessary (R = Q, b = 2, r = 3)
theorem c4_141 : ¬ drop0% Int.neg_clog_inv_eq_log 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 3) (by decide +kernel)

-- `Int.self_le_zpow_clog` idx 4: necessary (R = Q, b = 2, r = 3/8: clog = -1, 3/8 ≤ 1/2 fails in Q)
theorem c4_142 : ¬ drop0% Int.self_le_zpow_clog 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 (by decide) (3/8)) (by decide +kernel)

-- `Int.zpow_pred_clog_lt_self` idx 4: necessary (R = Q, b = 2, r = 3/8)
theorem c4_143 : ¬ drop0% Int.zpow_pred_clog_lt_self 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 (3/8) (by decide) (by decide +kernel)) (by decide +kernel)

-- `Int.clog_zpow` idx 4: necessary (R = Q, b = 3, z = -1: clog = 1)
theorem c4_144 : ¬ drop0% Int.clog_zpow 4 := fun h => absurd (@h W2c4.Q _ _ _ 3 (by decide) (-1)) (by decide +kernel)

-- `Int.clog_mono_right` idx 4: necessary (R = Q, 1/2 ≤ 1/4 in Q, clogs -1, -2)
theorem c4_145 : ¬ drop0% Int.clog_mono_right 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 (1/2) (1/4) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Int.zpow_lt_iff_lt_clog` idx 4: necessary (R = Q, b = 2, x = -1, r = 1/4)
theorem c4_146 : ¬ drop0% Int.zpow_lt_iff_lt_clog 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 (by decide) (-1) (1/4) (by decide +kernel)) (by decide +kernel)

-- `Int.le_zpow_iff_clog_le` idx 4: necessary (R = Q, b = 2, x = -1, r = 1/4)
theorem c4_147 : ¬ drop0% Int.le_zpow_iff_clog_le 4 := fun h => absurd (@h W2c4.Q _ _ _ 2 (by decide) (-1) (1/4) (by decide +kernel)) (by decide +kernel)

-- `Int.zpow_log_le_self` idx 7: necessary (R = ℚ, b = 0, r = 1/2: 0^0 = 1 > 1/2)
theorem c4_148 : ¬ drop0% Int.zpow_log_le_self 7 := fun h => absurd (@h ℚ _ _ _ _ 0 (1/2) (by norm_num)) (by decide +kernel)

-- `Int.log_mono_right` idx 8: necessary (R = ℚ, b = 2, r₁ = -1, r₂ = 1/2: 0 ≤ -1 fails)
theorem c4_149 : ¬ drop0% Int.log_mono_right 8 := fun h => absurd (@h ℚ _ _ _ _ 2 (-1) (1/2) (by norm_num)) (by decide +kernel)

-- `Int.log_mono_right` idx 9: necessary (R = ℚ, b = 2, r₁ = 2, r₂ = 1)
theorem c4_150 : ¬ drop0% Int.log_mono_right 9 := fun h => absurd (@h ℚ _ _ _ _ 2 2 1 (by norm_num)) (by decide +kernel)

-- `Int.lt_zpow_iff_log_lt` idx 6: necessary (R = ℚ, b = 1, x = 1, r = 2)
theorem c4_151 : ¬ drop0% Int.lt_zpow_iff_log_lt 6 := fun h => absurd (@h ℚ _ _ _ _ 1 1 2 (by norm_num)) (by decide +kernel)

-- `Int.zpow_le_iff_le_log` idx 6: necessary (R = ℚ, b = 1, x = 1, r = 2)
theorem c4_152 : ¬ drop0% Int.zpow_le_iff_le_log 6 := fun h => absurd (@h ℚ _ _ _ _ 1 1 2 (by norm_num)) (by decide +kernel)

-- `Int.clog_mono_right` idx 8: necessary (R = ℚ, b = 2, r₁ = -1, r₂ = 1/2)
theorem c4_153 : ¬ drop0% Int.clog_mono_right 8 := fun h => absurd (@h ℚ _ _ _ _ 2 (-1) (1/2) (by norm_num)) (by decide +kernel)

-- `Int.clog_mono_right` idx 9: necessary (R = ℚ, b = 2, r₁ = 2, r₂ = 1)
theorem c4_154 : ¬ drop0% Int.clog_mono_right 9 := fun h => absurd (@h ℚ _ _ _ _ 2 2 1 (by norm_num)) (by decide +kernel)

-- `Int.log_zero_right` idx 4: removable (log b 0 = 0 holds by Nat.floor_zero/Nat.ceil_zero, which need only a linear order)
theorem c4_155 : drop% Int.log_zero_right 4 := by intro R _ _ _ b; simp [Int.log, Nat.floor_zero, Nat.ceil_zero]

-- `Int.clog_zero_right` idx 4: removable (clog b 0 = 0 holds by Nat.floor_zero/Nat.ceil_zero, which need only a linear order)
theorem c4_156 : drop% Int.clog_zero_right 4 := by intro R _ _ _ b; simp [Int.clog, Nat.floor_zero, Nat.ceil_zero]

-- `Int.clog_of_left_le_one` idx 4: removable (for b ≤ 1 both branches of clog are 0 (Nat.clog_of_left_le_one, Nat.log_of_left_le_one))
theorem c4_157 : drop% Int.clog_of_left_le_one 4 := by intro R _ _ _ b hb r; unfold Int.clog; split_ifs <;> simp [Nat.clog_of_left_le_one hb, Nat.log_of_left_le_one hb]

-- `Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul` idx 6: removable (for prime p, p^(k+l+1) ∣ m n alone forces p^(k+1) ∣ m ∨ p^(l+1) ∣ n (valuations would add to ≤ k+l); neither p^k ∣ m nor p^l ∣ n is needed)
theorem c4_158 : drop% Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul 6 := by
  intro p hp m n k l _ h
  push_cast at h ⊢
  exact W2c4.prime_pow_split (Nat.prime_iff_prime_int.mp hp) k l h

-- `Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul` idx 7: removable (for prime p, p^(k+l+1) ∣ m n alone forces p^(k+1) ∣ m ∨ p^(l+1) ∣ n (valuations would add to ≤ k+l); neither p^k ∣ m nor p^l ∣ n is needed)
theorem c4_159 : drop% Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul 7 := by
  intro p hp m n k l _ h
  push_cast at h ⊢
  exact W2c4.prime_pow_split (Nat.prime_iff_prime_int.mp hp) k l h

-- `LawfulXor.xor_assoc` idx 3: necessary (α = Bool with xor := NOR (not associative))
theorem c4_160 : ¬ drop0% LawfulXor.xor_assoc 3 := fun h => by have := @h W2c4.NR inferInstance inferInstance; revert this; decide

-- `LawfulXor.xor_self` idx 3: necessary (α = Bool with xor := left projection: true ^^^ true = true)
theorem c4_161 : ¬ drop0% LawfulXor.xor_self 3 := fun h => by have := @h W2c4.LP inferInstance inferInstance; revert this; decide

-- `LawfulXor.xor_zero` idx 3: necessary (α = Bool with constant-false xor: true ^^^ 0 = false)
theorem c4_162 : ¬ drop0% LawfulXor.xor_zero 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide

-- `LawfulXor.xor_comm` idx 3: necessary (left projection is not commutative)
theorem c4_163 : ¬ drop0% LawfulXor.xor_comm 3 := fun h => by have := @h W2c4.LP inferInstance inferInstance; revert this; decide

-- `zero_xor` idx 3: necessary (constant-false xor)
theorem c4_164 : ¬ drop0% zero_xor 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide

-- `instCommutativeXor_mathlib` idx 3: necessary (left projection is not commutative)
theorem c4_165 : ¬ drop0% instCommutativeXor_mathlib 3 := fun h => absurd ((@h W2c4.LP inferInstance inferInstance).comm (show W2c4.LP from true) (show W2c4.LP from false)) (by decide)

-- `instAssociativeXor_mathlib` idx 3: necessary (NOR is not associative)
theorem c4_166 : ¬ drop0% instAssociativeXor_mathlib 3 := fun h => absurd ((@h W2c4.NR inferInstance inferInstance).assoc (show W2c4.NR from true) (show W2c4.NR from false) (show W2c4.NR from false)) (by decide)

-- `instLawfulCommIdentityXorOfNat_mathlib` idx 3: necessary (dependent: left-projection xor on Bool is not LawfulXor (xor_self fails))
theorem c4_167 : ¬ indep0% instLawfulCommIdentityXorOfNat_mathlib 3 := fun h => absurd ((@h W2c4.LP inferInstance inferInstance).xor_self (show W2c4.LP from true)) (by decide)

-- `xor_cancel_left` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_168 : ¬ drop0% xor_cancel_left 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide

-- `xor_cancel_right` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_169 : ¬ drop0% xor_cancel_right 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide

-- `xor_right_eq` idx 3: necessary (α = Bool with xor := LP, zero := false)
theorem c4_170 : ¬ drop0% xor_right_eq 3 := fun h => by have := @h W2c4.LP inferInstance inferInstance; revert this; decide

-- `xor_left_involutive` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_171 : ¬ drop0% xor_left_involutive 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; unfold Function.Involutive; decide

-- `xor_right_involutive` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_172 : ¬ drop0% xor_right_involutive 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; unfold Function.Involutive; decide

-- `xor_eq_iff_left_eq` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_173 : ¬ drop0% xor_eq_iff_left_eq 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide

-- `xor_eq_iff_right_eq` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_174 : ¬ drop0% xor_eq_iff_right_eq 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide

-- `xor_eq_zero_iff` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_175 : ¬ drop0% xor_eq_zero_iff 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide

-- `xor_xor_cancel_comm` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_176 : ¬ drop0% xor_xor_cancel_comm 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide

-- `xor_xor_cancel_comm_assoc` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_177 : ¬ drop0% xor_xor_cancel_comm_assoc 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide

-- `xor_left_eq_self_iff` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_178 : ¬ drop0% xor_left_eq_self_iff 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide

-- `xor_right_eq_self_iff` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_179 : ¬ drop0% xor_right_eq_self_iff 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide

-- `xor_left_eq_id_iff` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_180 : ¬ drop0% xor_left_eq_id_iff 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide

-- `xor_right_eq_id_iff` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_181 : ¬ drop0% xor_right_eq_id_iff 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide

-- `isFixedPt_xor_left_iff` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_182 : ¬ drop0% isFixedPt_xor_left_iff 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide

-- `isFixedPt_xor_right_iff` idx 3: necessary (α = Bool with xor := CF, zero := false)
theorem c4_183 : ¬ drop0% isFixedPt_xor_right_iff 3 := fun h => by have := @h W2c4.CF inferInstance inferInstance; revert this; decide
