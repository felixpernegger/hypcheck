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
namespace W2c5

def XB := Bool
instance : XorOp XB := ⟨fun a b => show Bool from (a && b : Bool)⟩
instance : Zero XB := ⟨show Bool from false⟩
instance : DecidableEq XB := inferInstanceAs (DecidableEq Bool)
theorem xb_not : ¬ LawfulXor XB := fun h => absurd (h.xor_self (show XB from true)) (by decide)

abbrev BN := fun _ : ℕ => ℕ
def sA : AList BN := AList.singleton 0 0
def sB : AList BN := AList.singleton 0 1

/-- A BEq on ℕ-copy that is always false. -/
def NB := ℕ
instance : BEq NB := ⟨fun _ _ => false⟩
instance : DecidableEq NB := inferInstanceAs (DecidableEq ℕ)
instance (n : ℕ) : OfNat NB n := ⟨show ℕ from n⟩
def nbN : NB → ℕ := fun x => show ℕ from x
def nNB : ℕ → NB := fun x => x
theorem nbN_inj : Function.Injective nbN := fun _ _ h => h
theorem nNB_inj : Function.Injective nNB := fun _ _ h => h

/-- Monad on ℕ × α whose bind keeps the first component of its first argument. -/
def KM (α : Type) := ℕ × α
instance : DecidableEq (KM ℕ) := inferInstanceAs (DecidableEq (ℕ × ℕ))
instance : Monad KM where
  pure x := (0, x)
  bind x f := (x.1, (f x.2).2)

end W2c5
open W2c5

namespace W2c5
/-- successor relation on ℕ: not transitive. -/
def sr (a b : ℕ) : Prop := b = a + 1
instance : DecidableRel sr := fun a b => inferInstanceAs (Decidable (b = a + 1))
end W2c5
open W2c5

namespace W2c5
theorem acc_irr {α : Type} {r : α → α → Prop} {x : α} (h : Acc r x) : ¬ r x x := by
  induction h with
  | intro x _ ih => exact fun hx => ih x hx hx
def r3 (a b : Fin 3) : Prop := b = a + 1
instance : DecidableRel r3 := fun a b => inferInstanceAs (Decidable (b = a + 1))
instance : Std.Antisymm r3 := ⟨by decide⟩
instance : Std.Trichotomous r3 := ⟨by decide⟩
instance : Std.Irrefl r3 := ⟨by decide⟩
def fo (a b : ℕ) : ℕ := (a + b) * 2
instance : Std.Commutative fo := ⟨fun a b => by simp [fo, Nat.add_comm]⟩
theorem foldr_const (l : List Unit) : l.foldr (fun _ a => a) (0:ℕ) = 0 := by induction l <;> simp_all
theorem foldl_const (l : List Unit) : l.foldl (fun a _ => a) (0:ℕ) = 0 := by induction l <;> simp_all
end W2c5
open W2c5

namespace W2c5
instance neEquiv : IsEquiv ℕ (fun a b : ℕ => a ≠ b)ᶜ where
  refl a := by simp
  trans a b c h1 h2 := by simp_all
  symm a b h := by simp_all
theorem lu_eq : Relator.LeftUnique (@Eq ℕ) := fun _ _ _ h1 h2 => h1.trans h2.symm
theorem ru_eq : Relator.RightUnique (@Eq ℕ) := fun _ _ _ h1 h2 => h1.symm.trans h2
end W2c5
open W2c5

-- `Equiv.xor_apply` idx 3: necessary (counterexample: @h XB _ _ (show XB from true) (show XB from true)))
theorem c5_1 : ¬ indep0% Equiv.xor_apply 3 := fun h => xb_not (@h XB _ _ (show XB from true) (show XB from true))

-- `Equiv.xor_symm` idx 3: necessary (counterexample: @h XB _ _ (show XB from true)))
theorem c5_2 : ¬ indep0% Equiv.xor_symm 3 := fun h => xb_not (@h XB _ _ (show XB from true))

-- `Equiv.xor_involutive` idx 3: necessary (counterexample: @h XB _ _ (show XB from true)))
theorem c5_3 : ¬ indep0% Equiv.xor_involutive 3 := fun h => xb_not (@h XB _ _ (show XB from true))

-- `Equiv.xor_zero` idx 3: necessary (counterexample: @h XB _ _))
theorem c5_4 : ¬ indep0% Equiv.xor_zero 3 := fun h => xb_not (@h XB _ _)

-- `Equiv.xor_eq_one_iff` idx 3: necessary (counterexample: @h XB _ _ (show XB from true)))
theorem c5_5 : ¬ indep0% Equiv.xor_eq_one_iff 3 := fun h => xb_not (@h XB _ _ (show XB from true))

-- `Equiv.isFixedPt_xor` idx 3: necessary (counterexample: @h XB _ _ (show XB from true) (show XB from true)))
theorem c5_6 : ¬ indep0% Equiv.isFixedPt_xor 3 := fun h => xb_not (@h XB _ _ (show XB from true) (show XB from true))

-- `Equiv.xor_trans_xor` idx 3: necessary (counterexample: @h XB _ _ (show XB from true) (show XB from true)))
theorem c5_7 : ¬ indep0% Equiv.xor_trans_xor 3 := fun h => xb_not (@h XB _ _ (show XB from true) (show XB from true))

-- `AList.ext` idx 4: necessary (counterexample: @h ℕ BN ∅ sA)) (by decide))
theorem c5_8 : ¬ drop0% AList.ext 4 := fun h => absurd (congrArg AList.entries (@h ℕ BN ∅ sA)) (by decide)

-- `AList.mem_of_perm` idx 5: necessary (counterexample: @h ℕ BN 0 ∅ sA) (by decide))
theorem c5_9 : ¬ drop0% AList.mem_of_perm 5 := fun h => absurd (@h ℕ BN 0 ∅ sA) (by decide)

-- `AList.perm_lookup` idx 6: necessary (counterexample: @h ℕ BN _ 0 ∅ sA) (by decide))
theorem c5_10 : ¬ drop0% AList.perm_lookup 6 := fun h => absurd (@h ℕ BN _ 0 ∅ sA) (by decide)

-- `AList.keys_subset_keys_of_entries_subset_entries` idx 4: necessary (counterexample: @h ℕ BN sA ∅) (by decide))
theorem c5_11 : ¬ drop0% AList.keys_subset_keys_of_entries_subset_entries 4 := fun h => absurd (@h ℕ BN sA ∅) (by decide)

-- `AList.perm_replace` idx 7: necessary (counterexample: @h ℕ BN _ 1 0 ∅ sA).length_eq (by decide))
theorem c5_12 : ¬ drop0% AList.perm_replace 7 := fun h => absurd (@h ℕ BN _ 1 0 ∅ sA).length_eq (by decide)

-- `AList.perm_erase` idx 6: necessary (counterexample: @h ℕ BN _ 1 ∅ sA).length_eq (by decide))
theorem c5_13 : ¬ drop0% AList.perm_erase 6 := fun h => absurd (@h ℕ BN _ 1 ∅ sA).length_eq (by decide)

-- `AList.entries_insert_of_notMem` idx 6: necessary (counterexample: @h ℕ BN _ 0 1 sA) (by decide))
theorem c5_14 : ¬ drop0% AList.entries_insert_of_notMem 6 := fun h => absurd (@h ℕ BN _ 0 1 sA) (by decide)

-- `AList.insert_of_notMem` idx 6: necessary (counterexample: @h ℕ BN _ 0 1 sA) (by decide))
theorem c5_15 : ¬ indep0% AList.insert_of_notMem 6 := fun h => absurd (@h ℕ BN _ 0 1 sA) (by decide)

-- `AList.perm_insert` idx 7: necessary (counterexample: @h ℕ BN _ 1 0 ∅ sA).length_eq (by decide))
theorem c5_16 : ¬ drop0% AList.perm_insert 7 := fun h => absurd (@h ℕ BN _ 1 0 ∅ sA).length_eq (by decide)

-- `AList.insertRec_insert` idx 8: necessary (counterexample: @h ℕ BN _ (fun _ => True) trivial (fun _ _ _ _ _ => trivial) ⟨0, 0⟩ sA) (by decide))
theorem c5_17 : ¬ indep0% AList.insertRec_insert 8 := fun h => absurd (@h ℕ BN _ (fun _ => True) trivial (fun _ _ _ _ _ => trivial) ⟨0, 0⟩ sA) (by decide)

-- `AList.insertRec_insert_mk` idx 9: necessary (counterexample: @h ℕ BN _ (fun _ => True) trivial (fun _ _ _ _ _ => trivial) 0 0 sA) (by decide))
theorem c5_18 : ¬ indep0% AList.insertRec_insert_mk 9 := fun h => absurd (@h ℕ BN _ (fun _ => True) trivial (fun _ _ _ _ _ => trivial) 0 0 sA) (by decide)

-- `AList.perm_union` idx 7: necessary (counterexample: @h ℕ BN _ ∅ sA ∅ ∅ (List.Perm.refl _)).length_eq (by decide))
theorem c5_19 : ¬ drop0% AList.perm_union 7 := fun h => absurd (@h ℕ BN _ ∅ sA ∅ ∅ (List.Perm.refl _)).length_eq (by decide)

-- `AList.perm_union` idx 8: necessary (counterexample: @h ℕ BN _ ∅ ∅ ∅ sA (List.Perm.refl _)).length_eq (by decide))
theorem c5_20 : ¬ drop0% AList.perm_union 8 := fun h => absurd (@h ℕ BN _ ∅ ∅ ∅ sA (List.Perm.refl _)).length_eq (by decide)

-- `AList.lookup_union_left` idx 6: necessary (counterexample: @h ℕ BN _ 0 ∅ sA) (by decide))
theorem c5_21 : ¬ drop0% AList.lookup_union_left 6 := fun h => absurd (@h ℕ BN _ 0 ∅ sA) (by decide)

-- `AList.lookup_union_right` idx 6: necessary (counterexample: @h ℕ BN _ 0 sA ∅) (by decide))
theorem c5_22 : ¬ drop0% AList.lookup_union_right 6 := fun h => absurd (@h ℕ BN _ 0 sA ∅) (by decide)

-- `AList.mem_lookup_union_middle` idx 9: necessary (counterexample: @h ℕ BN _ 0 0 ∅ sB sA (by decide)) (by decide))
theorem c5_23 : ¬ drop0% AList.mem_lookup_union_middle 9 := fun h => absurd (@h ℕ BN _ 0 0 ∅ sB sA (by decide)) (by decide)

-- `AList.union_comm_of_disjoint` idx 5: necessary (counterexample: @h ℕ BN _ sA sB) (by decide))
theorem c5_24 : ¬ drop0% AList.union_comm_of_disjoint 5 := fun h => absurd (@h ℕ BN _ sA sB) (by decide)

-- `List.length_injective` idx 1: necessary (counterexample: @h Bool [true] [false] rfl) (by decide))
theorem c5_25 : ¬ drop0% List.length_injective 1 := fun h => absurd (@h Bool [true] [false] rfl) (by decide)

-- `List.IsPrefix.idxOf_le` idx 4: removable (findIdx on a prefix is at most findIdx on the whole list for any predicate (List.IsPrefix.findIdx_le); lawfulness of BEq unused)
theorem c5_26 : drop% List.IsPrefix.idxOf_le 4 := by
  intro α l₁ l₂ _ h a
  exact List.IsPrefix.findIdx_le h

-- `List.IsPrefix.idxOf_eq_of_mem` idx 4: necessary (counterexample: @h NB [0] [0, 0] _ ⟨[0], rfl⟩ 0 (by)
theorem c5_27 : ¬ drop0% List.IsPrefix.idxOf_eq_of_mem 4 := fun h => absurd (@h NB [0] [0, 0] _ ⟨[0], rfl⟩ 0 (by simp)) (by decide)

-- `List.IsSuffix.idxOf_le` idx 4: removable (findIdx_append holds for any predicate, so idxOf in l2 = t ++ l1 is at most t.length + idxOf in l1; BEq lawfulness unused)
theorem c5_28 : drop% List.IsSuffix.idxOf_le 4 := by
  intro α l₁ l₂ _ h a
  obtain ⟨t, rfl⟩ := h
  have h1 := List.findIdx_le_length (p := (· == a)) (xs := t)
  have h2 := List.findIdx_le_length (p := (· == a)) (xs := l₁)
  simp only [List.idxOf, List.findIdx_append, List.length_append]
  split <;> omega

-- `List.IsSuffix.idxOf_add_length_le` idx 4: removable (same as IsSuffix.idxOf_le: findIdx_append for any predicate; BEq lawfulness unused)
theorem c5_29 : drop% List.IsSuffix.idxOf_add_length_le 4 := by
  intro α l₁ l₂ _ h a
  obtain ⟨t, rfl⟩ := h
  have h1 := List.findIdx_le_length (p := (· == a)) (xs := t)
  have h2 := List.findIdx_le_length (p := (· == a)) (xs := l₁)
  simp only [List.idxOf, List.findIdx_append, List.length_append]
  split <;> omega

-- `List.mem_dropLast_iff_idxOf_lt` idx 5: removable (if a is not in l both sides are false: a not in dropLast, and idxOf a l = length (idxOf_eq_length_iff))
theorem c5_30 : drop% List.mem_dropLast_iff_idxOf_lt 5 := by
  intro α _ _ l a
  by_cases ha : a ∈ l
  · exact List.mem_dropLast_iff_idxOf_lt ha
  · have h1 : a ∉ l.dropLast := fun h => ha (List.dropLast_subset l h)
    have h2 : l.idxOf a = l.length := List.idxOf_eq_length_iff.2 ha
    simp only [h1, false_iff, h2]; omega

-- `List.succ_idxOf_lt_length_of_mem_dropLast` idx 2: necessary (counterexample: @h NB _ [0, 0] 0 (by)
theorem c5_31 : ¬ drop0% List.succ_idxOf_lt_length_of_mem_dropLast 2 := fun h => absurd (@h NB _ [0, 0] 0 (by simp)) (by decide)

-- `Function.Involutive.list_map` idx 2: necessary (counterexample: @h ℕ Nat.succ [0]) (by decide))
theorem c5_32 : ¬ drop0% Function.Involutive.list_map 2 := fun h => absurd (@h ℕ Nat.succ [0]) (by decide)

-- `List.foldrM_eq_foldr` idx 4: necessary (counterexample: @h rem c5_33 : ¬ drop0% List.foldrM_eq_foldr 4 := fun h => absurd (@h ℕ ℕ KM _ (fun a b => ((1 : ℕ), b)) 0 [0]) (by decide))
theorem c5_33 : ¬ drop0% List.foldrM_eq_foldr 4 := fun h => absurd (@h ℕ ℕ KM _ (fun a b => ((1 : ℕ), b)) 0 [0]) (by decide)

-- `List.foldlM_eq_foldl` idx 4: necessary (counterexample: @h rem c5_34 : ¬ drop0% List.foldlM_eq_foldl 4 := fun h => absurd (@h ℕ ℕ KM _ (fun a b => ((1 : ℕ), b)) 0 [0]) (by decide))
theorem c5_34 : ¬ drop0% List.foldlM_eq_foldl 4 := fun h => absurd (@h ℕ ℕ KM _ (fun a b => ((1 : ℕ), b)) 0 [0]) (by decide)

-- `List.map_erase` idx 3: necessary (counterexample: @h NB ℕ _ _ _ _ nbN_inj 0 [0]) (by decide))
theorem c5_35 : ¬ drop0% List.map_erase 3 := fun h => absurd (@h NB ℕ _ _ _ _ nbN_inj 0 [0]) (by decide)

-- `List.map_erase` idx 5: necessary (counterexample: @h ℕ NB _ _ _ _ nNB_inj 0 [0]) (by decide))
theorem c5_36 : ¬ drop0% List.map_erase 5 := fun h => absurd (@h ℕ NB _ _ _ _ nNB_inj 0 [0]) (by decide)

-- `List.map_foldl_erase` idx 3: necessary (counterexample: @h NB ℕ _ _ _ _ nbN_inj [0] [0]) (by decide))
theorem c5_37 : ¬ drop0% List.map_foldl_erase 3 := fun h => absurd (@h NB ℕ _ _ _ _ nbN_inj [0] [0]) (by decide)

-- `List.map_foldl_erase` idx 5: necessary (counterexample: @h ℕ NB _ _ _ _ nNB_inj [0] [0]) (by decide))
theorem c5_38 : ¬ drop0% List.map_foldl_erase 5 := fun h => absurd (@h ℕ NB _ _ _ _ nNB_inj [0] [0]) (by decide)

-- `List.map_diff` idx 3: necessary (counterexample: @h NB ℕ _ _ _ _ nbN_inj [0] [0]) (by decide))
theorem c5_39 : ¬ drop0% List.map_diff 3 := fun h => absurd (@h NB ℕ _ _ _ _ nbN_inj [0] [0]) (by decide)

-- `List.map_diff` idx 5: necessary (counterexample: @h ℕ NB _ _ _ _ nNB_inj [0] [0]) (by decide))
theorem c5_40 : ¬ drop0% List.map_diff 5 := fun h => absurd (@h ℕ NB _ _ _ _ nNB_inj [0] [0]) (by decide)

-- `List.disjoint_pmap` idx 6: necessary (counterexample: @h ℕ ℕ (fun _ => False) (fun a h => h.elim) [0] [] (by)
theorem c5_41 : ¬ indep0% List.disjoint_pmap 6 := fun h => by
  have := @h ℕ ℕ (fun _ => False) (fun a h => h.elim) [0] [] (by simp)
  simp at this

-- `List.disjoint_pmap` idx 7: necessary (counterexample: @h ℕ ℕ (fun _ => False) (fun a h => h.elim) [] [0] (by)
theorem c5_42 : ¬ indep0% List.disjoint_pmap 7 := fun h => by
  have := @h ℕ ℕ (fun _ => False) (fun a h => h.elim) [] [0] (by simp)
  simp at this

-- `List.disjoint_pmap` idx 8: necessary (counterexample: @h ℕ ℕ (fun _ => True) (fun _ _ => 0) [0] [1] (by)
theorem c5_43 : ¬ drop0% List.disjoint_pmap 8 := fun h => by
  have := @h ℕ ℕ (fun _ => True) (fun _ _ => 0) [0] [1] (by simp) (by simp) (by simp)
  simp at this

-- `List.disjoint_map` idx 5: necessary (counterexample: @h ℕ ℕ (fun _ => 0) [0] [1] (by)
theorem c5_44 : ¬ drop0% List.disjoint_map 5 := fun h => by
  have := @h ℕ ℕ (fun _ => 0) [0] [1] (by simp); simp at this

-- `List.Disjoint.map` idx 5: necessary (counterexample: @h ℕ ℕ (fun _ => 0) [0] [1] (by)
theorem c5_45 : ¬ drop0% List.Disjoint.map 5 := fun h => by
  have := @h ℕ ℕ (fun _ => 0) [0] [1] (by simp); simp at this

-- `List.Disjoint.map_iff` idx 5: necessary (counterexample: @h ℕ ℕ (fun _ => 0) [0] [1])
theorem c5_46 : ¬ drop0% List.Disjoint.map_iff 5 := fun h => by
  have := @h ℕ ℕ (fun _ => 0) [0] [1]; simp at this

-- `List.isChain_pmap` idx 6: necessary (counterexample: @h ℕ ℕ (fun _ _ => True) (fun _ => False) (fun a h => h.elim) [0])
theorem c5_47 : ¬ indep0% List.isChain_pmap 6 := fun h => by
  have := @h ℕ ℕ (fun _ _ => True) (fun _ => False) (fun a h => h.elim) [0]; simp at this

-- `List.isChain_pmap_of_isChain` idx 6: necessary (counterexample: @h ℕ ℕ (fun _ _ => True) (fun _ _ => False) (fun _ => True) (fun a _ => a) [0, 0] (by)
theorem c5_48 : ¬ drop0% List.isChain_pmap_of_isChain 6 := fun h => by
  have := @h ℕ ℕ (fun _ _ => True) (fun _ _ => False) (fun _ => True) (fun a _ => a) [0, 0] (by simp) (by simp)
  simp at this

-- `List.isChain_pmap_of_isChain` idx 8: necessary (counterexample: @h ℕ ℕ (fun _ _ => False) (fun _ _ => False) (fun _ => True) (fun a _ => a) (by)
theorem c5_49 : ¬ drop0% List.isChain_pmap_of_isChain 8 := fun h => by
  have := @h ℕ ℕ (fun _ _ => False) (fun _ _ => False) (fun _ => True) (fun a _ => a) (by simp) [0, 0] (by simp)
  simp at this

-- `List.isChain_pmap_of_isChain` idx 9: necessary (counterexample: @h ℕ ℕ (fun _ _ => True) (fun _ _ => True) (fun _ => False) (fun a h => h.elim) (by)
theorem c5_50 : ¬ indep0% List.isChain_pmap_of_isChain 9 := fun h => by
  have := @h ℕ ℕ (fun _ _ => True) (fun _ _ => True) (fun _ => False) (fun a h => h.elim) (by simp) [0] (by simp)
  simp at this

-- `List.isChain_of_isChain_pmap` idx 7: necessary (counterexample: @h ℕ ℕ (fun _ _ => True) (fun _ _ => True) (fun _ => False) (fun a h => h.elim) [0] (by)
theorem c5_51 : ¬ indep0% List.isChain_of_isChain_pmap 7 := fun h => by
  have := @h ℕ ℕ (fun _ _ => True) (fun _ _ => True) (fun _ => False) (fun a h => h.elim) [0] (by simp)
  simp at this

-- `List.isChain_of_isChain_pmap` idx 8: necessary (counterexample: @h ℕ ℕ (fun _ _ => False) (fun _ _ => False) (fun _ => True) (fun a _ => a) [0, 0] (by)
theorem c5_52 : ¬ drop0% List.isChain_of_isChain_pmap 8 := fun h => by
  have := @h ℕ ℕ (fun _ _ => False) (fun _ _ => False) (fun _ => True) (fun a _ => a) [0, 0] (by simp) (by simp)
  simp at this

-- `List.isChain_of_isChain_pmap` idx 9: necessary (counterexample: @h ℕ ℕ (fun _ _ => False) (fun _ _ => True) (fun _ => True) (fun a _ => a) [0, 0] (by)
theorem c5_53 : ¬ drop0% List.isChain_of_isChain_pmap 9 := fun h => by
  have := @h ℕ ℕ (fun _ _ => False) (fun _ _ => True) (fun _ => True) (fun a _ => a) [0, 0] (by simp) (by simp)
  simp at this

-- `List.isChain_cons_pmap` idx 6: necessary (counterexample: @h ℕ ℕ (fun _ _ => True) (fun x => x = 1) (fun a _ => a) [0] 1 rfl)
theorem c5_54 : ¬ indep0% List.isChain_cons_pmap 6 := fun h => by
  have := @h ℕ ℕ (fun _ _ => True) (fun x => x = 1) (fun a _ => a) [0] 1 rfl; simp at this

-- `List.isChain_cons_pmap` idx 8: necessary (counterexample: @h ℕ ℕ (fun _ _ => True) (fun x => x = 1) (fun a _ => a) [] (by)
theorem c5_55 : ¬ indep0% List.isChain_cons_pmap 8 := fun h => by
  have := @h ℕ ℕ (fun _ _ => True) (fun x => x = 1) (fun a _ => a) [] (by simp) 0; simp at this

-- `List.isChain_cons_pmap_of_isChain_cons` idx 6: necessary (counterexample: @h ℕ ℕ (fun _ _ => True) (fun _ _ => False) (fun _ => True) (fun a _ => a) [0] 0 trivial (by)
theorem c5_56 : ¬ drop0% List.isChain_cons_pmap_of_isChain_cons 6 := fun h => by
  have := @h ℕ ℕ (fun _ _ => True) (fun _ _ => False) (fun _ => True) (fun a _ => a) [0] 0 trivial (by simp) (by simp)
  simp at this

-- `List.isChain_cons_pmap_of_isChain_cons` idx 9: necessary (counterexample: @h ℕ ℕ (fun _ _ => True) (fun _ _ => True) (fun x => x = 1) (fun a _ => a) (by)
theorem c5_57 : ¬ indep0% List.isChain_cons_pmap_of_isChain_cons 9 := fun h => by
  have := @h ℕ ℕ (fun _ _ => True) (fun _ _ => True) (fun x => x = 1) (fun a _ => a) (by simp) [] 0 (by simp) (by simp)
  simp at this

-- `List.isChain_cons_pmap_of_isChain_cons` idx 10: necessary (counterexample: @h ℕ ℕ (fun _ _ => False) (fun _ _ => False) (fun _ => True) (fun a _ => a) (by)
theorem c5_58 : ¬ drop0% List.isChain_cons_pmap_of_isChain_cons 10 := fun h => by
  have := @h ℕ ℕ (fun _ _ => False) (fun _ _ => False) (fun _ => True) (fun a _ => a) (by simp) [0] 0 trivial (by simp)
  simp at this

-- `List.isChain_cons_pmap_of_isChain_cons` idx 11: necessary (counterexample: @h ℕ ℕ (fun _ _ => True) (fun _ _ => True) (fun x => x = 0) (fun a _ => a) (by)
theorem c5_59 : ¬ indep0% List.isChain_cons_pmap_of_isChain_cons 11 := fun h => by
  have := @h ℕ ℕ (fun _ _ => True) (fun _ _ => True) (fun x => x = 0) (fun a _ => a) (by simp) [1] 0 rfl (by simp)
  simp at this

-- `List.isChain_cons_of_isChain_cons_pmap` idx 7: necessary (counterexample: @h ℕ ℕ (fun _ _ => True) (fun _ _ => False) (fun x => x = 1) (fun a _ => a) [0] 1 rfl (by)
theorem c5_60 : ¬ indep0% List.isChain_cons_of_isChain_cons_pmap 7 := fun h => by
  have := @h ℕ ℕ (fun _ _ => True) (fun _ _ => False) (fun x => x = 1) (fun a _ => a) [0] 1 rfl (by simp)
  simp at this

-- `List.isChain_cons_of_isChain_cons_pmap` idx 9: necessary (counterexample: @h ℕ ℕ (fun _ _ => True) (fun _ _ => False) (fun x => x = 1) (fun a _ => a) [] (by)
theorem c5_61 : ¬ indep0% List.isChain_cons_of_isChain_cons_pmap 9 := fun h => by
  have := @h ℕ ℕ (fun _ _ => True) (fun _ _ => False) (fun x => x = 1) (fun a _ => a) [] (by simp) 0 (by simp)
  simp at this

-- `List.isChain_cons_of_isChain_cons_pmap` idx 10: necessary (counterexample: @h ℕ ℕ (fun _ _ => False) (fun _ _ => False) (fun _ => True) (fun a _ => a) [0] (by)
theorem c5_62 : ¬ drop0% List.isChain_cons_of_isChain_cons_pmap 10 := fun h => by
  have := @h ℕ ℕ (fun _ _ => False) (fun _ _ => False) (fun _ => True) (fun a _ => a) [0] (by simp) 0 trivial (by simp)
  simp at this

-- `List.isChain_cons_of_isChain_cons_pmap` idx 11: necessary (counterexample: @h ℕ ℕ (fun _ _ => False) (fun _ _ => True) (fun _ => True) (fun a _ => a) [0] (by)
theorem c5_63 : ¬ drop0% List.isChain_cons_of_isChain_cons_pmap 11 := fun h => by
  have := @h ℕ ℕ (fun _ _ => False) (fun _ _ => True) (fun _ => True) (fun a _ => a) [0] (by simp) 0 trivial (by simp)
  simp at this

-- `List.IsChain.sublist` idx 4: necessary (counterexample: @h ℕ sr [0, 2] [0, 1, 2] (by decide) (by decide))
theorem c5_64 : ¬ drop0% List.IsChain.sublist 4 := fun h => by
  have := @h ℕ sr [0, 2] [0, 1, 2] (by decide) (by decide); revert this; decide

-- `List.IsChain.sublist` idx 5: necessary (counterexample: @h ℕ (· < ·) [1, 0] [1, 0] _ (List.Sublist.refl _))
theorem c5_65 : ¬ drop0% List.IsChain.sublist 5 := fun h => by
  have := @h ℕ (· < ·) [1, 0] [1, 0] _ (List.Sublist.refl _); revert this; decide

-- `List.IsChain.rel_cons` idx 5: necessary (counterexample: @h ℕ sr [1, 2] 0 2 (by decide) (by decide))
theorem c5_66 : ¬ drop0% List.IsChain.rel_cons 5 := fun h => by
  have := @h ℕ sr [1, 2] 0 2 (by decide) (by decide); revert this; decide

-- `List.isChain_flatten` idx 3: necessary (counterexample: @h ℕ (fun _ _ => False) [[0], [], [0]])
theorem c5_67 : ¬ drop0% List.isChain_flatten 3 := fun h => by
  have := @h ℕ (fun _ _ => False) [[0], [], [0]]; simp at this

-- `List.isChain_attachWith` idx 3: necessary (counterexample: @h ℕ [0] (fun _ => False))
theorem c5_68 : ¬ indep0% List.isChain_attachWith 3 := fun h => by
  have := @h ℕ [0] (fun _ => False); simp at this

-- `List.exists_isChain_cons_of_relationReflTransGen` idx 4: necessary (counterexample: @h ℕ (fun _ _ => False) 0 1 cases l with | nil =>)
theorem c5_69 : ¬ drop0% List.exists_isChain_cons_of_relationReflTransGen 4 := fun h => by
  obtain ⟨l, hl, he⟩ := @h ℕ (fun _ _ => False) 0 1
  cases l with
  | nil => simp at he
  | cons x l => simp at hl

-- `List.exists_isChain_ne_nil_of_relationReflTransGen` idx 4: necessary (counterexample: @h ℕ (fun _ _ => False) 0 1 match l, hne, hl, h1, h2 with | [x], _, _, h1, h2 =>)
theorem c5_70 : ¬ drop0% List.exists_isChain_ne_nil_of_relationReflTransGen 4 := fun h => by
  obtain ⟨l, hne, hl, h1, h2⟩ := @h ℕ (fun _ _ => False) 0 1
  match l, hne, hl, h1, h2 with
  | [x], _, _, h1, h2 => simp at h1 h2; omega
  | x :: y :: l, _, hl, _, _ => simp at hl

-- `List.IsChain.induction` idx 4: necessary (counterexample: @h ℕ (fun _ _ => False) (fun x => x = 0) [0, 1] (by)
theorem c5_71 : ¬ drop0% List.IsChain.induction 4 := fun h => by
  have := @h ℕ (fun _ _ => False) (fun x => x = 0) [0, 1] (by simp) (by simp) 1 (by simp); simp at this

-- `List.IsChain.cons_induction` idx 5: necessary (counterexample: @h ℕ (fun _ _ => False) 0 (fun x => x = 0) [1] (by)
theorem c5_72 : ¬ drop0% List.IsChain.cons_induction 5 := fun h => by
  have := @h ℕ (fun _ _ => False) 0 (fun x => x = 0) [1] (by simp) rfl 1 (by simp); simp at this

-- `List.IsChain.cons_induction` idx 7: necessary (counterexample: @h ℕ (fun _ _ => True) 0 (fun _ => False) [0] (by)
theorem c5_73 : ¬ drop0% List.IsChain.cons_induction 7 := fun h => by
  have := @h ℕ (fun _ _ => True) 0 (fun _ => False) [0] (by simp) (by simp) 0 (by simp); simp at this

-- `List.IsChain.concat_induction` idx 6: necessary (counterexample: @h ℕ (fun _ _ => False) 0 1 (fun x => x = 0) [0] rfl (by)
theorem c5_74 : ¬ drop0% List.IsChain.concat_induction 6 := fun h => by
  have := @h ℕ (fun _ _ => False) 0 1 (fun x => x = 0) [0] rfl (by simp) rfl 1 (by simp); simp at this

-- `List.IsChain.concat_induction_head` idx 6: necessary (counterexample: @h ℕ (fun _ _ => False) 0 1 (fun x => x = 0) [0] rfl (by)
theorem c5_75 : ¬ drop0% List.IsChain.concat_induction_head 6 := fun h => by
  have := @h ℕ (fun _ _ => False) 0 1 (fun x => x = 0) [0] rfl (by simp) rfl; simp at this

-- `List.IsChain.backwards_concat_induction` idx 7: necessary (counterexample: @h ℕ (fun _ _ => True) 1 (fun _ => False) [0] (by)
theorem c5_76 : ¬ drop0% List.IsChain.backwards_concat_induction 7 := fun h => by
  have := @h ℕ (fun _ _ => True) 1 (fun _ => False) [0] (by simp) (by simp) 0 (by simp); simp at this

-- `List.relationReflTransGen_of_exists_isChain` idx 3: necessary (counterexample: @h ℕ (fun _ _ => False) [0, 1] (by)
theorem c5_77 : ¬ drop0% List.relationReflTransGen_of_exists_isChain 3 := fun h => by
  have := @h ℕ (fun _ _ => False) [0, 1] (by simp)
  simp at this
  exact absurd (Relation.ReflTransGen.cases_tail this) (by
    rintro (h | ⟨c, _, hc⟩) <;> simp_all)

-- `List.IsChain.cons_of_le` idx 6: necessary (counterexample: @h ℕ _ 2 [1] [0, 5] (by)
theorem c5_78 : ¬ drop0% List.IsChain.cons_of_le 6 := fun h => by
  have := @h ℕ _ 2 [1] [0, 5] (by simp) (by decide); revert this; decide

-- `WellFoundedRelation.asymmetricₙ` idx 4: necessary (counterexample: @h ℕ ⟨(· < ·), wellFounded_lt⟩ [1, 0] (by)
theorem c5_79 : ¬ drop0% WellFoundedRelation.asymmetricₙ 4 := fun h =>
  (@h ℕ ⟨(· < ·), wellFounded_lt⟩ [1, 0] (by simp)) (show (0:ℕ) < 1 by decide)

-- `WellFounded.asymmetricₙ` idx 4: necessary (counterexample: @h ℕ (· < ·) [] wellFounded_lt (by)
theorem c5_80 : ¬ indep0% WellFounded.asymmetricₙ 4 := fun h => (@h ℕ (· < ·) [] wellFounded_lt (by simp)) rfl

-- `WellFounded.asymmetricₙ` idx 5: necessary (counterexample: @h ℕ (· < ·) [1, 0] wellFounded_lt (by)
theorem c5_81 : ¬ drop0% WellFounded.asymmetricₙ 5 := fun h =>
  (@h ℕ (· < ·) [1, 0] wellFounded_lt (by simp)) (show (0:ℕ) < 1 by decide)

-- `WellFounded.listPairwise_reverse_compl` idx 4: necessary (counterexample: @h ℕ (· < ·) [1, 0] wellFounded_lt)
theorem c5_82 : ¬ drop0% WellFounded.listPairwise_reverse_compl 4 := fun h => by
  have := @h ℕ (· < ·) [1, 0] wellFounded_lt; simp at this

-- `Acc.list_chain'` idx 3: necessary (counterexample: @h Unit (fun _ _ => True) ⟨[()], by)
theorem c5_83 : ¬ drop0% Acc.list_chain' 3 := fun h =>
  acc_irr (@h Unit (fun _ _ => True) ⟨[()], by simp⟩) (List.Lex.rel trivial)

-- `WellFounded.list_chain'` idx 2: necessary (counterexample: @h Unit (fun _ _ => True)).apply ⟨[()], by)
theorem c5_84 : ¬ drop0% WellFounded.list_chain' 2 := fun h =>
  acc_irr ((@h Unit (fun _ _ => True)).apply ⟨[()], by simp⟩) (List.Lex.rel trivial)

-- `List.count_map_of_injective` idx 3: necessary (counterexample: @h NB ℕ _ _ _ [0] nbN nbN_inj 0) (by decide))
theorem c5_85 : ¬ drop0% List.count_map_of_injective 3 := fun h => absurd (@h NB ℕ _ _ _ [0] nbN nbN_inj 0) (by decide)

-- `List.count_map_of_injective` idx 5: necessary (counterexample: @h ℕ NB _ _ _ [0] nNB nNB_inj 0) (by decide))
theorem c5_86 : ¬ drop0% List.count_map_of_injective 5 := fun h => absurd (@h ℕ NB _ _ _ [0] nNB nNB_inj 0) (by decide)

-- `List.next_getLast_eq_head_of_notMem_dropLast` idx 4: necessary (counterexample: @h ℕ _ [0, 1, 0] (by)
theorem c5_87 : ¬ drop0% List.next_getLast_eq_head_of_notMem_dropLast 4 := fun h => by
  have := @h ℕ _ [0, 1, 0] (by simp); revert this; decide

-- `List.next_getElem` idx 3: necessary (counterexample: @h ℕ _ [0, 1, 0] 2 (by decide))
theorem c5_88 : ¬ drop0% List.next_getElem 3 := fun h => by
  have := @h ℕ _ [0, 1, 0] 2 (by decide); revert this; decide

-- `List.prev_getElem` idx 3: necessary (counterexample: @h ℕ _ [0, 1, 0] 2 (by decide))
theorem c5_89 : ¬ drop0% List.prev_getElem 3 := fun h => by
  have := @h ℕ _ [0, 1, 0] 2 (by decide); revert this; decide

-- `List.next_getLast_eq_head` idx 4: necessary (counterexample: @h ℕ _ [0, 1, 0] (by)
theorem c5_90 : ¬ drop0% List.next_getLast_eq_head 4 := fun h => by
  have := @h ℕ _ [0, 1, 0] (by simp); revert this; decide

-- `List.pmap_next_eq_rotate_one` idx 3: necessary (counterexample: @h ℕ _ [0, 0, 1])
theorem c5_91 : ¬ drop0% List.pmap_next_eq_rotate_one 3 := fun h => by
  have := @h ℕ _ [0, 0, 1]; revert this; decide

-- `List.pmap_prev_eq_rotate_length_sub_one` idx 3: necessary (counterexample: @h ℕ _ [0, 0, 1])
theorem c5_92 : ¬ drop0% List.pmap_prev_eq_rotate_length_sub_one 3 := fun h => by
  have := @h ℕ _ [0, 0, 1]; revert this; decide

-- `List.next_prev` idx 3: necessary (counterexample: @h ℕ _ [0, 1, 0] 0 (by)
theorem c5_93 : ¬ drop0% List.next_prev 3 := fun h => by
  have := @h ℕ _ [0, 1, 0] 0 (by simp); revert this; decide

-- `List.prev_reverse_eq_next` idx 3: necessary (counterexample: @h ℕ _ [0, 1, 0] 0 (by)
theorem c5_94 : ¬ drop0% List.prev_reverse_eq_next 3 := fun h => by
  have := @h ℕ _ [0, 1, 0] 0 (by simp); revert this; decide

-- `List.next_reverse_eq_prev` idx 3: necessary (counterexample: @h ℕ _ [0, 1, 0] 0 (by)
theorem c5_95 : ¬ drop0% List.next_reverse_eq_prev 3 := fun h => by
  have := @h ℕ _ [0, 1, 0] 0 (by simp); revert this; decide

-- `List.isRotated_next_eq` idx 5: necessary (counterexample: @h ℕ _ [0, 1, 0] [1, 0, 0] ⟨1, rfl⟩ 0 (by)
theorem c5_96 : ¬ drop0% List.isRotated_next_eq 5 := fun h => by
  have := @h ℕ _ [0, 1, 0] [1, 0, 0] ⟨1, rfl⟩ 0 (by simp); revert this; decide

-- `List.isRotated_prev_eq` idx 5: necessary (counterexample: @h ℕ _ [0, 1, 0] [1, 0, 0] ⟨1, rfl⟩ 0 (by)
theorem c5_97 : ¬ drop0% List.isRotated_prev_eq 5 := fun h => by
  have := @h ℕ _ [0, 1, 0] [1, 0, 0] ⟨1, rfl⟩ 0 (by simp); revert this; decide

-- `Cycle.induction_on` idx 3: necessary (counterexample: @h ℕ (fun s => s ≠ Cycle.nil) Cycle.nil (fun a l _ => by)
theorem c5_98 : ¬ drop0% Cycle.induction_on 3 := fun h =>
  (@h ℕ (fun s => s ≠ Cycle.nil) Cycle.nil (fun a l _ => by simp)) rfl

-- `Cycle.induction_on` idx 4: necessary (counterexample: @h ℕ (fun s => s = Cycle.nil) ↑[0] rfl)
theorem c5_99 : ¬ drop0% Cycle.induction_on 4 := fun h => by
  have := @h ℕ (fun s => s = Cycle.nil) ↑[0] rfl; simp at this

-- `Cycle.nontrivial_coe_nodup_iff` idx 2: necessary (counterexample: @h ℕ [0, 0])
theorem c5_100 : ¬ drop0% Cycle.nontrivial_coe_nodup_iff 2 := fun h => by
  have := @h ℕ [0, 0]; simp [Cycle.Nontrivial] at this

-- `Cycle.Subsingleton.nodup` idx 2: necessary (counterexample: @h ℕ ↑[0, 0])
theorem c5_101 : ¬ drop0% Cycle.Subsingleton.nodup 2 := fun h => by
  have := @h ℕ ↑[0, 0]; simp at this

-- `Cycle.Nodup.nontrivial_iff` idx 2: necessary (counterexample: @h ℕ ↑[0, 0])
theorem c5_102 : ¬ drop0% Cycle.Nodup.nontrivial_iff 2 := fun h => by
  have := @h ℕ ↑[0, 0]; simp [Cycle.Nontrivial, Cycle.Subsingleton] at this

-- `Cycle.prev_reverse_eq_next` idx 3: necessary (counterexample: @h ℕ _ ↑[0, 0] 0 (by)
theorem c5_103 : ¬ indep0% Cycle.prev_reverse_eq_next 3 := fun h => by
  have := @h ℕ _ ↑[0, 0] 0 (by simp); simp at this

-- `Cycle.prev_reverse_eq_next'` idx 3: necessary (counterexample: @h ℕ _ ↑[0, 0] 0 (by)
theorem c5_104 : ¬ indep0% Cycle.prev_reverse_eq_next' 3 := fun h => by
  have := @h ℕ _ ↑[0, 0] 0 (by simp); simp at this

-- `Cycle.next_reverse_eq_prev` idx 3: necessary (counterexample: @h ℕ _ ↑[0, 0] 0 (by)
theorem c5_105 : ¬ indep0% Cycle.next_reverse_eq_prev 3 := fun h => by
  have := @h ℕ _ ↑[0, 0] 0 (by simp); simp at this

-- `Cycle.next_reverse_eq_prev'` idx 3: necessary (counterexample: @h ℕ _ ↑[0, 0] 0 (by)
theorem c5_106 : ¬ indep0% Cycle.next_reverse_eq_prev' 3 := fun h => by
  have := @h ℕ _ ↑[0, 0] 0 (by simp); simp at this

-- `Cycle.next_mem` idx 3: necessary (counterexample: @h ℕ _ ↑[0, 0] 0 (by)
theorem c5_107 : ¬ indep0% Cycle.next_mem 3 := fun h => by
  have := @h ℕ _ ↑[0, 0] 0 (by simp); simp at this

-- `Cycle.prev_mem` idx 3: necessary (counterexample: @h ℕ _ ↑[0, 0] 0 (by)
theorem c5_108 : ¬ indep0% Cycle.prev_mem 3 := fun h => by
  have := @h ℕ _ ↑[0, 0] 0 (by simp); simp at this

-- `Cycle.prev_next` idx 3: necessary (counterexample: @h ℕ _ ↑[0, 0] 0 (by)
theorem c5_109 : ¬ indep0% Cycle.prev_next 3 := fun h => by
  have := @h ℕ _ ↑[0, 0] 0 (by simp); simp at this

-- `Cycle.next_prev` idx 3: necessary (counterexample: @h ℕ _ ↑[0, 0] 0 (by)
theorem c5_110 : ¬ indep0% Cycle.next_prev 3 := fun h => by
  have := @h ℕ _ ↑[0, 0] 0 (by simp); simp at this

-- `Cycle.forall_eq_of_chain` idx 3: necessary (counterexample: @h @h (Fin 3) r3 (([0, 1, 2] : List (Fin 3)) : Cycle (Fin 3)) _ (by simp [r3]) 0 1 (by simp) (by simp); revert this; decide)
theorem c5_111 : ¬ drop0% Cycle.forall_eq_of_chain 3 := fun h => by
  have := @h (Fin 3) r3 (([0, 1, 2] : List (Fin 3)) : Cycle (Fin 3)) _ (by simp [r3]) 0 1 (by simp) (by simp); revert this; decide

-- `Cycle.forall_eq_of_chain` idx 4: necessary (counterexample: @h Bool (fun _ _ => True) ↑[false, true] ⟨fun _ _ _ _ _ => trivial⟩ (by)
theorem c5_112 : ¬ drop0% Cycle.forall_eq_of_chain 4 := fun h => by
  have := @h Bool (fun _ _ => True) ↑[false, true] ⟨fun _ _ _ _ _ => trivial⟩ (by simp) false true (by simp) (by simp)
  simp at this

-- `List.length_destutter'_congr` idx 7: necessary (counterexample: @h ℕ [0] (fun a b => a ≠ b) _ 0 1 _)
theorem c5_113 : ¬ drop0% List.length_destutter'_congr 7 := fun h => by
  have := @h ℕ [0] (fun a b => a ≠ b) _ 0 1 _; revert this; decide

-- `List.IsChain.length_le_length_destutter` idx 3: necessary (counterexample: @h ℕ (· < ·) _ [0, 1, 2] [0, 5, 1, 2] (by decide) (by decide))
theorem c5_114 : ¬ drop0% List.IsChain.length_le_length_destutter 3 := fun h => by
  have := @h ℕ (· < ·) _ [0, 1, 2] [0, 5, 1, 2] (by decide) (by decide); revert this; decide

-- `List.IsChain.length_le_length_destutter` idx 7: necessary (counterexample: @h ℕ (fun a b => a ≠ b) _ _ [0, 0] [0, 0] (List.Sublist.refl _))
theorem c5_115 : ¬ drop0% List.IsChain.length_le_length_destutter 7 := fun h => by
  have := @h ℕ (fun a b => a ≠ b) _ _ [0, 0] [0, 0] (List.Sublist.refl _); revert this; decide

-- `List.IsChain.length_le_length_destutter_ne` idx 5: necessary (counterexample: @h ℕ [0, 0] [0, 0] _ (List.Sublist.refl _))
theorem c5_116 : ¬ drop0% List.IsChain.length_le_length_destutter_ne 5 := fun h => by
  have := @h ℕ [0, 0] [0, 0] _ (List.Sublist.refl _); revert this; decide

-- `List.Pairwise.destutter_eq_dedup` idx 3: necessary (counterexample: @h ℕ _ (fun _ _ => True) [0, 1, 0] (by)
theorem c5_117 : ¬ drop0% List.Pairwise.destutter_eq_dedup 3 := fun h => by
  have := @h ℕ _ (fun _ _ => True) [0, 1, 0] (by simp); revert this; decide

-- `List.Pairwise.destutter_eq_dedup` idx 5: necessary (counterexample: @h ℕ _ (fun _ _ => False) ⟨fun _ _ h _ => h.elim⟩ [0, 1, 0])
theorem c5_118 : ¬ drop0% List.Pairwise.destutter_eq_dedup 5 := fun h => by
  have := @h ℕ _ (fun _ _ => False) ⟨fun _ _ h _ => h.elim⟩ [0, 1, 0]; revert this; decide

-- `List.Duplicate.mono_sublist` idx 5: necessary (counterexample: @h ℕ [0, 0] 0 [] (by)
theorem c5_119 : ¬ drop0% List.Duplicate.mono_sublist 5 := fun h => by
  have := @h ℕ [0, 0] 0 [] (by simp [List.duplicate_iff_two_le_count]); simp at this

-- `List.find?_eq_find?_of_perm` idx 5: necessary (counterexample: @h ℕ (fun _ => true) [0, 1] [1, 0] (by decide))
theorem c5_120 : ¬ drop0% List.find?_eq_find?_of_perm 5 := fun h => by
  have := @h ℕ (fun _ => true) [0, 1] [1, 0] (by decide); revert this; decide

-- `List.foldl_eq_foldr` idx 5: necessary (counterexample: @h ℕ [0, 1] 0 fo _)
theorem c5_121 : ¬ drop0% List.foldl_eq_foldr 5 := fun h => by
  have := @h ℕ [0, 1] 0 fo _; revert this; decide

-- `List.Forall₂.mp` idx 5: necessary (counterexample: @h ℕ ℕ (fun _ _ => True) (fun _ _ => False) (fun _ _ => True) [0] [0] (by)
theorem c5_122 : ¬ drop0% List.Forall₂.mp 5 := fun h => by
  have := @h ℕ ℕ (fun _ _ => True) (fun _ _ => False) (fun _ _ => True) [0] [0] (by simp) (by simp); simp at this

-- `List.left_unique_forall₂'` idx 3: necessary (counterexample: @h ℕ ℕ (fun _ _ => True) [0] [1] [0] (by)
theorem c5_123 : ¬ drop0% List.left_unique_forall₂' 3 := fun h => by
  have := @h ℕ ℕ (fun _ _ => True) [0] [1] [0] (by simp) (by simp); simp at this

-- `List.left_unique_forall₂'` idx 7: necessary (counterexample: @h ℕ ℕ Eq lu_eq [0] [1] [1] (by)
theorem c5_124 : ¬ drop0% List.left_unique_forall₂' 7 := fun h => by
  have := @h ℕ ℕ Eq lu_eq [0] [1] [1] (by simp); simp at this

-- `List.left_unique_forall₂'` idx 8: necessary (counterexample: @h ℕ ℕ Eq lu_eq [0] [1] [0] (by)
theorem c5_125 : ¬ drop0% List.left_unique_forall₂' 8 := fun h => by
  have := @h ℕ ℕ Eq lu_eq [0] [1] [0] (by simp); simp at this

-- `Relator.LeftUnique.forall₂` idx 3: necessary (counterexample: @h ℕ ℕ (fun _ _ => True))
theorem c5_126 : ¬ drop0% Relator.LeftUnique.forall₂ 3 := fun h => by
  have h' := @h ℕ ℕ (fun _ _ => True)
  have := @h' [0] [1] [0] (by simp) (by simp); simp at this

-- `List.right_unique_forall₂'` idx 3: necessary (counterexample: @h ℕ ℕ (fun _ _ => True) [0] [0] [1] (by)
theorem c5_127 : ¬ drop0% List.right_unique_forall₂' 3 := fun h => by
  have := @h ℕ ℕ (fun _ _ => True) [0] [0] [1] (by simp) (by simp); simp at this

-- `List.right_unique_forall₂'` idx 7: necessary (counterexample: @h ℕ ℕ Eq ru_eq [0] [1] [0] (by)
theorem c5_128 : ¬ drop0% List.right_unique_forall₂' 7 := fun h => by
  have := @h ℕ ℕ Eq ru_eq [0] [1] [0] (by simp); simp at this

-- `List.right_unique_forall₂'` idx 8: necessary (counterexample: @h ℕ ℕ Eq ru_eq [0] [0] [1] (by)
theorem c5_129 : ¬ drop0% List.right_unique_forall₂' 8 := fun h => by
  have := @h ℕ ℕ Eq ru_eq [0] [0] [1] (by simp); simp at this

-- `Relator.RightUnique.forall₂` idx 3: necessary (counterexample: @h ℕ ℕ (fun _ _ => True))
theorem c5_130 : ¬ drop0% Relator.RightUnique.forall₂ 3 := fun h => by
  have h' := @h ℕ ℕ (fun _ _ => True)
  have := @h' [0] [0] [1] (by simp) (by simp); simp at this

-- `Relator.BiUnique.forall₂` idx 3: necessary (counterexample: @h ℕ ℕ (fun _ _ => True)).1)
theorem c5_131 : ¬ drop0% Relator.BiUnique.forall₂ 3 := fun h => by
  have h' := (@h ℕ ℕ (fun _ _ => True)).1
  have := @h' [0] [1] [0] (by simp) (by simp); simp at this

-- `List.Forall₂.get` idx 7: removable (derivable: Forall2 R x y gives x.length = y.length, so hy implies hx)
theorem c5_132 : indep% List.Forall₂.get 7 := by
  intro α β R x y h i hy
  rw [h.length_eq]; exact hy

-- `List.rel_mem` idx 3: necessary (counterexample: @h ℕ ℕ (fun _ _ => True))
theorem c5_133 : ¬ drop0% List.rel_mem 3 := fun h => by
  have h' := @h ℕ ℕ (fun _ _ => True)
  have := @h' 0 0 trivial [1] [0] (by simp); simp at this

-- `List.rel_filter` idx 5: necessary (counterexample: @h ℕ ℕ Eq (fun _ => true) (fun _ => false))
theorem c5_134 : ¬ drop0% List.rel_filter 5 := fun h => by
  have h' := @h ℕ ℕ Eq (fun _ => true) (fun _ => false)
  have := @h' [0] [0] (by simp); simp at this

-- `List.SublistForall₂.is_refl` idx 2: necessary (counterexample: @h ℕ (fun _ _ => False)).refl [0])
theorem c5_135 : ¬ drop0% List.SublistForall₂.is_refl 2 := fun h => by
  have := (@h ℕ (fun _ _ => False)).refl [0]
  rw [List.sublistForall₂_iff] at this
  obtain ⟨l, h1, -⟩ := this
  cases h1; assumption

-- `List.SublistForall₂.is_trans` idx 2: necessary (counterexample: @h ℕ sr).trans [0] [1] [2] (List.sublistForall₂_iff.2 ⟨[1], by)
theorem c5_136 : ¬ drop0% List.SublistForall₂.is_trans 2 := fun h => by
  have := (@h ℕ sr).trans [0] [1] [2] (List.sublistForall₂_iff.2 ⟨[1], by simp [sr], List.Sublist.refl _⟩)
    (List.sublistForall₂_iff.2 ⟨[2], by simp [sr], List.Sublist.refl _⟩)
  rw [List.sublistForall₂_iff] at this
  obtain ⟨l, h1, h2⟩ := this
  cases h1 with
  | cons h3 h4 => cases h4; simp [sr] at h3; subst h3; simp at h2

-- `List.getD_surjective` idx 2: necessary (counterexample: @h ℕ [] 0 1)
theorem c5_137 : ¬ drop0% List.getD_surjective 2 := fun h => by
  obtain ⟨n, hn⟩ := @h ℕ [] 0 1; simp at hn

-- `List.recNeNil_cons` idx 4: necessary (counterexample: @h ℕ (fun _ _ => True) 0 [] (fun _ => trivial) (fun _ _ _ _ => trivial)) rfl)
theorem c5_138 : ¬ indep0% List.recNeNil_cons 4 := fun h =>
  (@h ℕ (fun _ _ => True) 0 [] (fun _ => trivial) (fun _ _ _ _ => trivial)) rfl

-- `List.IsInfix.nodup` idx 4: necessary (counterexample: @h ℕ [0, 0] [0, 0] (List.infix_refl _))
theorem c5_139 : ¬ drop0% List.IsInfix.nodup 4 := fun h => by
  have := @h ℕ [0, 0] [0, 0] (List.infix_refl _); revert this; decide

-- `List.insertIdx_pmap` idx 7: necessary (counterexample: @h ℕ ℕ (fun x => x = 1) (fun a _ => a) [0] 1 0 rfl)
theorem c5_140 : ¬ indep0% List.insertIdx_pmap 7 := fun h => by
  have := @h ℕ ℕ (fun x => x = 1) (fun a _ => a) [0] 1 0 rfl; simp at this

-- `List.insertIdx_pmap` idx 8: necessary (counterexample: @h ℕ ℕ (fun x => x = 1) (fun a _ => a) [] 0 0 (by)
theorem c5_141 : ¬ indep0% List.insertIdx_pmap 8 := fun h => by
  have := @h ℕ ℕ (fun x => x = 1) (fun a _ => a) [] 0 0 (by simp); simp at this

-- `List.eraseIdx_pmap` idx 5: necessary (counterexample: @h ℕ ℕ (fun _ => False) (fun a h => h.elim) [0])
theorem c5_142 : ¬ indep0% List.eraseIdx_pmap 5 := fun h => by
  have := @h ℕ ℕ (fun _ => False) (fun a h => h.elim) [0]; simp at this

-- `List.Interleaves.pairwise_left` idx 4: necessary (counterexample: @h ℕ sr [1, 3] [0, 2, 4] (by)
theorem c5_143 : ¬ drop0% List.Interleaves.pairwise_left 4 := fun h => by
  have := @h ℕ sr [1, 3] [0, 2, 4] (by simp [sr]); simp [sr] at this

-- `List.Interleaves.pairwise_right` idx 4: necessary (counterexample: @h ℕ sr [1, 3] [0, 2, 4] (by)
theorem c5_144 : ¬ drop0% List.Interleaves.pairwise_right 4 := fun h => by
  have := @h ℕ sr [1, 3] [0, 2, 4] (by simp [sr]); simp [sr] at this

-- `List.injOn_insertIdx_index_of_notMem` idx 3: necessary (counterexample: @h ℕ [0] 0)
theorem c5_145 : ¬ drop0% List.injOn_insertIdx_index_of_notMem 3 := fun h => by
  have h' := @h ℕ [0] 0
  have := @h' 0 (by simp) 1 (by simp) (by decide); simp at this

-- `List.foldr_range_subset_of_range_subset` idx 5: necessary (counterexample: @h ℕ Unit Unit (fun _ a => a + 1) (fun _ a => a) 0 _ ⟨[()], rfl⟩)
theorem c5_146 : ¬ drop0% List.foldr_range_subset_of_range_subset 5 := fun h => by
  obtain ⟨l, hl⟩ := @h ℕ Unit Unit (fun _ a => a + 1) (fun _ a => a) 0 _ ⟨[()], rfl⟩
  rw [foldr_const] at hl; simp at hl

-- `List.foldl_range_subset_of_range_subset` idx 5: necessary (counterexample: @h ℕ Unit Unit (fun a _ => a + 1) (fun a _ => a) 0 _ ⟨[()], rfl⟩)
theorem c5_147 : ¬ drop0% List.foldl_range_subset_of_range_subset 5 := fun h => by
  obtain ⟨l, hl⟩ := @h ℕ Unit Unit (fun a _ => a + 1) (fun a _ => a) 0 _ ⟨[()], rfl⟩
  rw [foldl_const] at hl; simp at hl

-- `List.foldr_range_eq_of_range_eq` idx 5: necessary (counterexample: @h ℕ Unit Unit (fun _ a => a + 1) (fun _ a => a) 0)
theorem c5_148 : ¬ drop0% List.foldr_range_eq_of_range_eq 5 := fun h => by
  have := @h ℕ Unit Unit (fun _ a => a + 1) (fun _ a => a) 0
  obtain ⟨l, hl⟩ := (Set.ext_iff.1 this _).1 ⟨[()], rfl⟩
  rw [foldr_const] at hl; simp at hl

-- `List.Lex.isOrderConnected` idx 2: necessary (counterexample: @h (Fin 3) r3 _).conn [0] [2] [1] (List.Lex.rel (by decide)))
theorem c5_149 : ¬ drop0% List.Lex.isOrderConnected 2 := fun h => by
  have := (@h (Fin 3) r3 _).conn [0] [2] [1] (List.Lex.rel (by decide))
  simp at this; revert this; decide

-- `_private.Mathlib.Data.List.Lex.0.List.Lex.isOrderConnected.aux` idx 2: necessary (counterexample: @h (Fin 3) r3 _ [0] [2] [1] (List.Lex.rel (by decide)))
theorem c5_150 : ¬ drop0% _private.Mathlib.Data.List.Lex.«0».List.Lex.isOrderConnected.aux 2 := fun h => by
  have := @h (Fin 3) r3 _ [0] [2] [1] (List.Lex.rel (by decide))
  simp at this; revert this; decide

-- `_private.Mathlib.Data.List.Lex.0.List.Lex.isOrderConnected.aux` idx 3: necessary (counterexample: @h ℕ (fun _ _ => False) ⟨fun _ _ _ h => h.elim⟩ [0] [1] [0, 0] (List.Lex.cons List.Lex.nil) rcases this with h1 | h1 <)
theorem c5_151 : ¬ drop0% _private.Mathlib.Data.List.Lex.«0».List.Lex.isOrderConnected.aux 3 := fun h => by
  have := @h ℕ (fun _ _ => False) ⟨fun _ _ _ h => h.elim⟩ [0] [1] [0, 0] (List.Lex.cons List.Lex.nil)
  rcases this with h1 | h1 <;> cases h1 <;> simp_all

-- `List.head!_le_of_lt` idx 6: necessary (counterexample: @h ℕ _ ⟨5⟩ [0] [] (by decide))
theorem c5_152 : ¬ drop0% List.head!_le_of_lt 6 := fun h => by
  have := @h ℕ _ ⟨5⟩ [0] [] (by decide); revert this; decide

-- `List.perm_lookmap` idx 4: necessary (counterexample: @h ℕ (fun a => some (a + 1)) [0, 1] [1, 0] (by decide))
theorem c5_153 : ¬ drop0% List.perm_lookmap 4 := fun h => by
  have := @h ℕ (fun a => some (a + 1)) [0, 1] [1, 0] (by decide)
  rw [List.lookmap_cons_some (f := fun a : ℕ => some (a + 1)) (b := 1) _ rfl,
    List.lookmap_cons_some (f := fun a : ℕ => some (a + 1)) (b := 2) _ rfl] at this; revert this; decide

-- `List.argAux_self` idx 3: removable (argAux r (some a) a is if r a a then some a else some a, equal to some a whatever r is)
theorem c5_154 : drop% List.argAux_self 3 := by
  intro α r _ a
  simp [List.argAux]

-- `List.not_of_mem_foldl_argAux` idx 5: necessary (counterexample: @h (Fin 3) r3 _ [0, 1, 2] ⟨by decide⟩ 1 2 none (by decide) (by decide))
theorem c5_155 : ¬ drop0% List.not_of_mem_foldl_argAux 5 := fun h => by
  have := @h (Fin 3) r3 _ [0, 1, 2] ⟨by decide⟩ 1 2 none (by decide) (by decide); revert this; decide

-- `List.rel_nodup` idx 3: necessary (counterexample: @h ℕ ℕ (fun _ _ => True))
theorem c5_156 : ¬ drop0% List.rel_nodup 3 := fun h => by
  have h' := @h ℕ ℕ (fun _ _ => True)
  have := @h' [0, 0] [0, 1] (by simp); revert this; decide

-- `List.nodup_iff_count_le_one` idx 2: necessary (counterexample: @h y have := (@h NB _ [0, 0]).2 (fun a => (show List.count a [(0:NB), 0] = 0 from rfl) ▸ Nat.zero_le 1) revert this; decide)
theorem c5_157 : ¬ drop0% List.nodup_iff_count_le_one 2 := fun h => by
  have := (@h NB _ [0, 0]).2 (fun a => (show List.count a [(0:NB), 0] = 0 from rfl) ▸ Nat.zero_le 1)
  revert this; decide

-- `List.count_eq_one_of_mem` idx 5: necessary (counterexample: @h ℕ _ _ 0 [0, 0] (by)
theorem c5_158 : ¬ drop0% List.count_eq_one_of_mem 5 := fun h => by
  have := @h ℕ _ _ 0 [0, 0] (by simp); revert this; decide

-- `List.inj_on_of_nodup_map` idx 4: necessary (counterexample: @h ℕ ℕ (fun _ => 0) [0, 1] 0 (by)
theorem c5_159 : ¬ drop0% List.inj_on_of_nodup_map 4 := fun h => by
  have := @h ℕ ℕ (fun _ => 0) [0, 1] 0 (by simp) 1 (by simp) rfl; simp at this

-- `List.Nodup.pmap` idx 5: necessary (counterexample: @h ℕ ℕ (fun _ => False) (fun a h => h.elim) [0] (fun a ha => ha.elim) (by)
theorem c5_160 : ¬ indep0% List.Nodup.pmap 5 := fun h => by
  have := @h ℕ ℕ (fun _ => False) (fun a h => h.elim) [0] (fun a ha => ha.elim) (by simp); simp at this

-- `List.Nodup.pmap` idx 6: necessary (counterexample: @h ℕ ℕ (fun _ => True) (fun _ _ => 0) [0, 1] (by)
theorem c5_161 : ¬ drop0% List.Nodup.pmap 6 := fun h => by
  have := @h ℕ ℕ (fun _ => True) (fun _ _ => 0) [0, 1] (by simp) (by simp); simp at this

-- `List.Nodup.pmap` idx 7: necessary (counterexample: @h ℕ ℕ (fun _ => True) (fun a _ => a) [0, 0] (by)
theorem c5_162 : ¬ drop0% List.Nodup.pmap 7 := fun h => by
  have := @h ℕ ℕ (fun _ => True) (fun a _ => a) [0, 0] (by simp) (fun a _ b _ h => h); simp at this

-- `List.Nodup.tail` idx 2: necessary (counterexample: @h ℕ [0, 1, 1])
theorem c5_163 : ¬ drop0% List.Nodup.tail 2 := fun h => by
  have := @h ℕ [0, 1, 1]; revert this; decide

-- `List.nodup_tail_reverse` idx 2: necessary (counterexample: @h ℕ [0, 1, 1])
theorem c5_164 : ¬ drop0% List.nodup_tail_reverse 2 := fun h => by
  have := @h ℕ [0, 1, 1]; revert this; decide

-- `List.Nodup.prefix_of_head_mem_of_infix` idx 5: necessary (counterexample: @h ℕ [1] [0, 1] (by decide) (by)
theorem c5_165 : ¬ drop0% List.Nodup.prefix_of_head_mem_of_infix 5 := fun h => by
  have := @h ℕ [1] [0, 1] (by decide) (by simp) (by decide); revert this; decide

-- `List.Nodup.prefix_of_head_mem_of_infix` idx 6: necessary (counterexample: @h ℕ [1, 0] [0, 1, 0] (by decide) (by)
theorem c5_166 : ¬ drop0% List.Nodup.prefix_of_head_mem_of_infix 6 := fun h => by
  have := @h ℕ [1, 0] [0, 1, 0] (by decide) (by simp) (by simp); revert this; decide

-- `List.Nodup.suffix_of_getLast_mem_of_infix` idx 6: necessary (counterexample: @h ℕ [0, 1] [0, 1, 0] (by decide) (by)
theorem c5_167 : ¬ drop0% List.Nodup.suffix_of_getLast_mem_of_infix 6 := fun h => by
  have := @h ℕ [0, 1] [0, 1, 0] (by decide) (by simp) (by simp); revert this; decide

-- `List.Nodup.erase_getElem` idx 4: necessary (counterexample: @h ℕ _ _ [0, 1, 0] 2 (by decide))
theorem c5_168 : ¬ drop0% List.Nodup.erase_getElem 4 := fun h => by
  have := @h ℕ _ _ [0, 1, 0] 2 (by decide); revert this; decide

-- `List.Nodup.erase_get` idx 4: necessary (counterexample: @h ℕ _ _ [0, 1, 0] ⟨2, by decide⟩)
theorem c5_169 : ¬ drop0% List.Nodup.erase_get 4 := fun h => by
  have := @h ℕ _ _ [0, 1, 0] ⟨2, by decide⟩; revert this; decide

-- `List.Nodup.diff` idx 4: removable (l1.diff l2 is a sublist of l1 for any BEq (erase is a sublist), so it stays nodup)
theorem c5_170 : drop% List.Nodup.diff 4 := by
  intro α l₁ l₂ _ h
  induction l₂ generalizing l₁ with
  | nil => simpa [List.diff] using h
  | cons b t ih =>
    simp only [List.diff]
    split
    · exact ih (h.sublist (List.erase_sublist ..))
    · exact ih h

-- `List.Nodup.diff` idx 5: necessary (counterexample: @h ℕ [0, 0] [] _ _)
theorem c5_171 : ¬ drop0% List.Nodup.diff 5 := fun h => by
  have := @h ℕ [0, 0] [] _ _; revert this; decide

-- `List.Nodup.sigma` idx 4: necessary (counterexample: @h ℕ [0, 0] (fun _ => ℕ) (fun _ => [0]) (by)
theorem c5_172 : ¬ drop0% List.Nodup.sigma 4 := fun h => by
  have := @h ℕ [0, 0] (fun _ => ℕ) (fun _ => [0]) (by simp); revert this; decide

-- `List.Nodup.sigma` idx 5: necessary (counterexample: @h ℕ [0] (fun _ => ℕ) (fun _ => [0, 0]) (by)
theorem c5_173 : ¬ drop0% List.Nodup.sigma 5 := fun h => by
  have := @h ℕ [0] (fun _ => ℕ) (fun _ => [0, 0]) (by simp); revert this; decide

-- `List.Nodup.sdiff_eq_filter` idx 5: necessary (counterexample: @h ℕ _ _ [0, 0] [0])
theorem c5_174 : ¬ drop0% List.Nodup.sdiff_eq_filter 5 := fun h => by
  have := @h ℕ _ _ [0, 0] [0]; revert this; decide

-- `List.Nodup.diff_eq_filter` idx 5: necessary (counterexample: @h ℕ _ _ [0, 0] [0])
theorem c5_175 : ¬ drop0% List.Nodup.diff_eq_filter 5 := fun h => by
  have := @h ℕ _ _ [0, 0] [0]; revert this; decide

-- `List.Nodup.mem_sdiff_iff` idx 6: necessary (counterexample: @h ℕ [0, 0] [0] 0 _ _)
theorem c5_176 : ¬ drop0% List.Nodup.mem_sdiff_iff 6 := fun h => by
  have := @h ℕ [0, 0] [0] 0 _ _; revert this; decide

-- `List.Nodup.mem_diff_iff` idx 6: necessary (counterexample: @h ℕ [0, 0] [0] 0 _ _)
theorem c5_177 : ¬ drop0% List.Nodup.mem_diff_iff 6 := fun h => by
  have := @h ℕ [0, 0] [0] 0 _ _; revert this; decide

-- `List.Nodup.take_eq_filter_mem` idx 5: necessary (counterexample: @h ℕ _ _ [0, 0] 1)
theorem c5_178 : ¬ drop0% List.Nodup.take_eq_filter_mem 5 := fun h => by
  have := @h ℕ _ _ [0, 0] 1; revert this; decide

-- `List.Nodup.getBijectionOfForallMemList_coe` idx 2: necessary (counterexample: @h Unit [(), ()] (fun x => by)
theorem c5_179 : ¬ indep0% List.Nodup.getBijectionOfForallMemList_coe 2 := fun h => by
  have := @h Unit [(), ()] (fun x => by simp); revert this; decide

-- `List.Nodup.getEquiv_symm_apply_val` idx 3: necessary (counterexample: @h ℕ _ [0, 0])
theorem c5_180 : ¬ indep0% List.Nodup.getEquiv_symm_apply_val 3 := fun h => by
  have := @h ℕ _ [0, 0]; revert this; decide

-- `List.Nodup.getEquivOfForallMemList_symm_apply_val` idx 3: necessary (counterexample: @h Unit _ [(), ()] (fun x => by)
theorem c5_181 : ¬ indep0% List.Nodup.getEquivOfForallMemList_symm_apply_val 3 := fun h => by
  have := @h Unit _ [(), ()] (fun x => by simp); revert this; decide

-- `List.Nodup.getEquivOfForallMemList_apply` idx 3: necessary (counterexample: @h Unit _ [(), ()] (fun x => by)
theorem c5_182 : ¬ indep0% List.Nodup.getEquivOfForallMemList_apply 3 := fun h => by
  have := @h Unit _ [(), ()] (fun x => by simp); revert this; decide

-- `List.SortedLT.coe_getIso_symm_apply` idx 4: necessary (counterexample: @h ℕ _ [1, 0] _ ⟨1, by)
theorem c5_183 : ¬ indep0% List.SortedLT.coe_getIso_symm_apply 4 := fun h => by
  have h' : List.SortedLT [1, 0] := @h ℕ _ [1, 0] _ ⟨1, by simp⟩
  unfold List.SortedLT StrictMono at h'
  have := @h' ⟨0, by simp⟩ ⟨1, by simp⟩ (by decide); simp at this
