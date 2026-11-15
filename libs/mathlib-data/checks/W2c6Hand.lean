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

namespace W2c6

/-- Relations on Fin 3 encoded by a 9-bit code: bit 3i+j says r i j. -/
def RC (c : ℕ) (i j : Fin 3) : Prop := c.testBit (3 * i.val + j.val) = true
instance (c : ℕ) : DecidableRel (RC c) := fun _ _ => inferInstanceAs (Decidable (_ = true))
/-- 371: reflexive rock-paper-scissors (total, antisymmetric, not transitive). -/
instance tot371 : Std.Total (RC 371) := ⟨by decide⟩
instance ant371 : Std.Antisymm (RC 371) := ⟨by decide⟩
/-- 319: total preorder with 0 and 1 equivalent (not antisymmetric). -/
instance tot319 : Std.Total (RC 319) := ⟨by decide⟩
instance trn319 : IsTrans (Fin 3) (RC 319) := ⟨by decide⟩
/-- 1: only r 0 0 (transitive, antisymmetric, not total). -/
instance trn1 : IsTrans (Fin 3) (RC 1) := ⟨by decide⟩
instance ant1 : Std.Antisymm (RC 1) := ⟨by decide⟩

theorem symmEq : Std.Symm (fun a b : ℕ => a = b) := ⟨fun _ _ h => h.symm⟩
theorem symmNe : Std.Symm (fun a b : ℕ => a ≠ b) := ⟨fun _ _ h => Ne.symm h⟩
theorem irrNe : Std.Irrefl (fun a b : ℕ => a ≠ b) := ⟨fun _ h => h rfl⟩
theorem antLe : Std.Antisymm (fun a b : ℕ => a ≤ b) := ⟨fun _ _ => Nat.le_antisymm⟩
theorem antLt : Std.Antisymm (fun a b : ℕ => a < b) := ⟨fun _ _ h1 h2 => absurd (h1.trans h2) (lt_irrefl _)⟩
theorem antTrue : Std.Total (fun _ _ : ℕ => True) := ⟨fun _ _ => Or.inl trivial⟩
theorem trnTrue : IsTrans ℕ (fun _ _ : ℕ => True) := ⟨fun _ _ _ _ _ => trivial⟩

/-- Sigma lists with a duplicated key. -/
abbrev SL := List (Σ _ : ℕ, ℕ)
def dl : SL := [⟨0, 0⟩, ⟨0, 1⟩]
theorem dl_not : ¬ dl.NodupKeys := by simp [dl, List.NodupKeys, List.keys]
theorem nk_nil : ([] : SL).NodupKeys := by simp [List.NodupKeys, List.keys]
theorem dl_perm : dl.Perm dl.reverse := by decide

/-- The accessible part: an element below itself is not accessible. -/
theorem acc_self {α : Type} {r : α → α → Prop} {a : α} (h : r a a) : ¬ Acc r a := fun hacc =>
  Acc.rec (motive := fun x _ => ¬ r x x) (fun x _ ih hxx => ih x hxx hxx) hacc h

/-- Two non-commuting 2x2 integer matrices. -/
def MA : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]
def MB : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]
theorem MAB_ne : MA * MB ≠ MB * MA := by
  intro h; have := congrFun (congrFun h 0) 0
  simp [MA, MB, Matrix.mul_apply, Fin.sum_univ_two] at this

/-- Swap ring hom on ℤ × ℤ. -/
def swZ : ℤ × ℤ →+* ℤ × ℤ := (RingEquiv.prodComm : ℤ × ℤ ≃+* ℤ × ℤ).toRingHom
theorem swZ_ne : swZ ≠ RingHom.id _ := by
  intro h; have := congrArg (fun f => f (1, 0)) h; simp [swZ] at this

/-- Shift operators on ℕ → ℕ: L * R = 1 but R * L ≠ 1, so the semiring is not Dedekind-finite. -/
abbrev E := AddMonoid.End (ℕ → ℤ)
def shL : E := AddMonoidHom.mk' (fun f n => f (n + 1)) (fun _ _ => rfl)
def shR : E := AddMonoidHom.mk' (fun f n => if n = 0 then 0 else f (n - 1))
  (fun f g => by funext n; split_ifs <;> simp [*])
theorem shLR : shL * shR = 1 := by
  ext f n; change (if n + 1 = 0 then (0:ℤ) else f (n + 1 - 1)) = f n; simp
theorem shRL : shR * shL ≠ 1 := by
  intro h; have := congrFun (DFunLike.congr_fun h (fun _ => 1)) 0
  change (if (0:ℕ) = 0 then (0:ℤ) else 1) = 1 at this; simp at this
theorem E_not_df : ¬ IsDedekindFiniteMonoid E := fun h => shRL (h.mul_eq_one_symm shLR)

theorem totLe : Std.Total (fun a b : ℕ => a ≤ b) := ⟨Nat.le_total⟩
theorem trnLe : IsTrans ℕ (fun a b : ℕ => a ≤ b) := ⟨fun _ _ _ => Nat.le_trans⟩
theorem irrLt : Std.Irrefl (fun a b : ℕ => a < b) := ⟨fun a => lt_irrefl a⟩

/-- MaxN (copied from Probe1): ℕ∞ with max as multiplication, one = 0, zero = ⊤. -/
def MaxN := ℕ∞
def toM (n : ℕ∞) : MaxN := n
def ofM (a : MaxN) : ℕ∞ := a
noncomputable instance : CommMonoidWithZero MaxN where
  mul a b := toM (max (ofM a) (ofM b))
  one := toM 0
  zero := toM ⊤
  mul_assoc a b c := max_assoc (ofM a) (ofM b) (ofM c)
  one_mul a := max_eq_right (by simp : (0:ℕ∞) ≤ ofM a)
  mul_one a := max_eq_left (by simp : (0:ℕ∞) ≤ ofM a)
  zero_mul a := max_eq_left (le_top : ofM a ≤ ⊤)
  mul_zero a := max_eq_right (le_top : ofM a ≤ ⊤)
  mul_comm a b := max_comm (ofM a) (ofM b)
@[simp] theorem ofM_toM (n : ℕ∞) : ofM (toM n) = n := rfl
@[simp] theorem ofM_zero : ofM 0 = ⊤ := rfl
@[simp] theorem ofM_one : ofM 1 = 0 := rfl
@[simp] theorem ofM_mul (a b : MaxN) : ofM (a * b) = max (ofM a) (ofM b) := rfl
theorem ofM_inj {a b : MaxN} : ofM a = ofM b ↔ a = b := Iff.rfl
theorem maxN_dvd (a b : MaxN) : a ∣ b ↔ ofM a ≤ ofM b := by
  constructor
  · rintro ⟨c, rfl⟩; simp
  · intro h; exact ⟨b, ofM_inj.1 (by simp [h])⟩
instance : Subsingleton MaxNˣ := ⟨fun u v => by
  have key : ∀ w : MaxNˣ, w = 1 := fun w => by
    apply Units.ext
    have h1 := congrArg ofM w.val_inv
    simp only [ofM_mul, ofM_one] at h1
    have h2 : ofM (w : MaxN) ≤ 0 := h1 ▸ le_max_left _ _
    exact ofM_inj.1 (by simpa using h2)
  rw [key u, key v]⟩
theorem maxN_prime (n : ℕ∞) (h0 : n ≠ 0) (ht : n ≠ ⊤) : Prime (toM n) := by
  refine ⟨fun e => ht (by simpa using congrArg ofM e), fun hu => h0 ?_, fun a b hab => ?_⟩
  · simpa using congrArg ofM (isUnit_iff_eq_one.1 hu)
  · rw [maxN_dvd] at hab; rw [maxN_dvd, maxN_dvd]
    simpa using hab

/-- Shortlex: the empty list is always accessible. -/
theorem acc_nil {α : Type} (r : α → α → Prop) : Acc (List.Shortlex r) [] := Acc.intro _ fun y hy => by
  rcases List.shortlex_def.mp hy with h | ⟨h1, h2⟩
  · simp at h
  · exact absurd h2 (List.not_lex_nil)
theorem accB : Acc (fun x y : Bool => x = false ∧ y = false) true :=
  Acc.intro _ fun y hy => absurd hy.2 (by decide)
theorem accT : Acc (List.Shortlex (fun x y : Bool => x = false ∧ y = false)) [true] := Acc.intro _ fun y hy => by
  rcases List.shortlex_def.mp hy with h | ⟨h1, h2⟩
  · simp at h; subst h; exact acc_nil _
  · obtain ⟨c, rfl⟩ : ∃ c, y = [c] := by
      match y, h1 with
      | [c], _ => exact ⟨c, rfl⟩
    cases h2 with
    | rel hr => exact absurd hr.2 (by decide)
    | cons h3 => exact absurd h3 (List.not_lex_nil)
theorem nacc : ¬ Acc (List.Shortlex (fun x y : Bool => x = false ∧ y = false)) [true, true] := fun ha =>
  acc_self (List.shortlex_def.mpr (Or.inr ⟨rfl, List.Lex.rel ⟨rfl, rfl⟩⟩))
    (ha.inv (List.shortlex_def.mpr (Or.inl (by simp))) : Acc (List.Shortlex _) [false])

/-- In a chain whose relation forces the right element to be nonempty, a nonempty head makes all entries nonempty. -/
theorem chain_ne {α : Type*} {R : List α → List α → Prop} (hR : ∀ b a, R b a → a ≠ []) :
    ∀ (x : List α) (rest : List (List α)), (x :: rest).IsChain R → x ≠ [] → [] ∉ x :: rest
  | x, [], _, hx => by simpa [eq_comm] using hx
  | x, y :: rest, hc, hx => by
      rw [List.isChain_cons_cons] at hc
      have := chain_ne hR y rest hc.2 (hR _ _ hc.1)
      simp only [List.mem_cons, not_or] at this ⊢
      exact ⟨fun h => hx h.symm, this.1, this.2⟩

theorem tw_true : List.Triplewise (fun _ _ _ : ℕ => True) [0, 1, 2] :=
  .cons (by simp) (.cons (by simp) (.cons (by simp) .nil))
theorem tw_false (h : List.Triplewise (fun _ _ _ : ℕ => False) [0, 1, 2]) : False := by
  cases h with | cons h1 _ => exact (List.pairwise_cons.mp h1).1 2 (by simp)

/-- Diagonal ring hom ℤ → ℤ × ℤ: fst ∘ diag = id, diag ∘ fst ≠ id. -/
def dgZ : ℤ →+* ℤ × ℤ := RingHom.prod (RingHom.id ℤ) (RingHom.id ℤ)

theorem ms3 {α : Type*} (le : α → α → Bool) (a b c : α) :
    [a, b, c].mergeSort le = List.merge ([a, b].mergeSort le) [c] le := by
  rw [show [a, b, c] = [a, b] ++ [c] from rfl, List.mergeSort_append _ _ (by simp) (by simp),
    List.mergeSort_singleton]

theorem oi_append {α : Type*} (r : α → α → Prop) [DecidableRel r] (a : α) :
    ∀ (l₁ l₂ : List α), (∀ b ∈ l₁, ¬ r a b) →
      (l₁ ++ l₂).orderedInsert r a = l₁ ++ l₂.orderedInsert r a
  | [], l₂, _ => by simp
  | b :: l₁, l₂, h => by
      have hb : ¬ r a b := h b (by simp)
      have ih := oi_append r a l₁ l₂ (fun c hc => h c (by simp [hc]))
      simp [List.orderedInsert, hb, ih]

/-- Without totality, insertion sort still never puts v before u when r u v and u ≠ v. -/
theorem oi_inv {α : Type*} (r : α → α → Prop) [DecidableRel r] [Std.Antisymm r] [IsTrans α r] (a : α) :
    ∀ L : List α, L.Pairwise (fun u v => r v u → v = u) →
      (L.orderedInsert r a).Pairwise (fun u v => r v u → v = u)
  | [], _ => by simp
  | y :: L, hL => by
      rw [List.pairwise_cons] at hL
      by_cases hay : r a y
      · rw [List.orderedInsert_cons_of_le _ _ hay]
        refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr hL⟩
        intro u hu hua
        rcases List.mem_cons.mp hu with rfl | hu
        · exact Std.Antisymm.antisymm _ _ hua hay
        · have := hL.1 u hu (_root_.trans hua hay)
          subst this; exact Std.Antisymm.antisymm _ _ hua hay
      · rw [List.orderedInsert_cons, if_neg hay]
        refine List.pairwise_cons.mpr ⟨?_, oi_inv r a L hL.2⟩
        intro u hu huy
        rcases (List.mem_orderedInsert r).mp hu with rfl | hu
        · exact absurd huy hay
        · exact hL.1 u hu huy

theorem is_inv {α : Type*} (r : α → α → Prop) [DecidableRel r] [Std.Antisymm r] [IsTrans α r] :
    ∀ l : List α, (l.insertionSort r).Pairwise (fun u v => r v u → v = u)
  | [] => by simp
  | a :: l => by rw [List.insertionSort_cons]; exact oi_inv r a _ (is_inv r l)
/-- Insertion into a sublist, with the weak insertion-sort invariant instead of sortedness of bs. -/
theorem oi_sub {α : Type*} (r : α → α → Prop) [DecidableRel r] [Std.Antisymm r] [IsTrans α r] (x : α) :
    ∀ {xs ys : List α}, xs.Sublist ys → ys.Pairwise (fun u v => r v u → v = u) → (∀ y ∈ xs, r x y ∨ r y x) →
      (xs.orderedInsert r x).Sublist (ys.orderedInsert r x)
  | [], bs, _, _, _ => by simpa using (List.mem_orderedInsert r).mpr (Or.inl rfl)
  | a' :: as', [], hs, _, _ => absurd hs (by simp)
  | a' :: as', b :: bs', hs, hb, hc => by
    rw [List.pairwise_cons] at hb
    by_cases hxb : r x b
    · cases hs with
      | cons _ h =>
        by_cases hxa : r x a'
        · simp only [List.orderedInsert, hxb, hxa, ↓reduceIte]
          exact (h.cons b).cons_cons x
        · have hax : r a' x := (hc a' (by simp)).resolve_left hxa
          have hab : a' = b := hb.1 a' (h.subset (by simp)) (_root_.trans hax hxb)
          exact absurd (hab ▸ hxb) hxa
      | cons_cons _ h =>
        simp only [List.orderedInsert, hxb, ↓reduceIte]
        exact (h.cons_cons _).cons_cons x
    · cases hs with
      | cons _ h =>
        simp only [List.orderedInsert, hxb, ↓reduceIte]
        exact (oi_sub r x h hb.2 hc).cons b
      | cons_cons _ h =>
        simp only [List.orderedInsert, hxb, ↓reduceIte]
        exact (oi_sub r x h hb.2 (fun y hy => hc y (by simp [hy]))).cons_cons _

end W2c6

open W2c6

-- `List.Pairwise.forall_of_forall` idx 3: necessary (R = ≤ on ℕ, l = [0,1], x = 1, y = 0)
theorem x26_1 : ¬ drop0% List.Pairwise.forall_of_forall 3 := fun h =>
  absurd (@h ℕ (· ≤ ·) [0, 1] (by decide) (by decide) 1 (by decide) 0 (by decide)) (by decide)
-- `List.Pairwise.forall_of_forall` idx 5: necessary (R = Eq, l = [0,1])
theorem x26_2 : ¬ drop0% List.Pairwise.forall_of_forall 5 := fun h =>
  absurd (@h ℕ (fun a b => a = b) [0, 1] symmEq (by decide) 0 (by decide) 1 (by decide)) (by decide)
-- `List.Pairwise.forall_of_forall` idx 7: necessary (R = Eq, l = [0], x = 1)
theorem x26_3 : ¬ drop0% List.Pairwise.forall_of_forall 7 := fun h =>
  absurd (@h ℕ (fun a b => a = b) [0] symmEq (by decide) (by decide) 1 0 (by decide)) (by decide)
-- `List.Pairwise.forall` idx 4: necessary (R = Eq, l = [0,1])
theorem x26_4 : ¬ drop0% List.Pairwise.forall 4 := fun h =>
  absurd (@h ℕ (fun a b => a = b) [0, 1] symmEq 0 (by decide) 1 (by decide) (by decide)) (by decide)
-- `List.Pairwise.set_pairwise` idx 3: necessary (R = Eq, l = [0,1])
theorem x26_5 : ¬ drop0% List.Pairwise.set_pairwise 3 := fun h =>
  absurd ((@h ℕ (fun a b => a = b) [0, 1] symmEq) (show (0:ℕ) ∈ {x | x ∈ [0, 1]} by simp)
    (show (1:ℕ) ∈ {x | x ∈ [0, 1]} by simp) (by decide)) (by decide)
-- `List.Pairwise.set_pairwise` idx 4: necessary (R = <, l = [0,1])
theorem x26_6 : ¬ drop0% List.Pairwise.set_pairwise 4 := fun h =>
  absurd ((@h ℕ (· < ·) [0, 1] (by decide)) (show (1:ℕ) ∈ {x | x ∈ [0, 1]} by simp)
    (show (0:ℕ) ∈ {x | x ∈ [0, 1]} by simp) (by decide)) (by decide)
-- `List.pairwise_append_of_mem` idx 7: necessary (R = ≠, l₁ = [0], l₂ = [1,0], a = 0, b = 1)
theorem x26_7 : ¬ drop0% List.pairwise_append_of_mem 7 := fun h =>
  absurd (@h ℕ (fun a b => a ≠ b) [0] [1, 0] 0 1 symmNe (by decide) (by decide)) (by decide)
-- `List.pairwise_cons_of_mem` idx 6: necessary (R = ≠, l = [1,0], a = 0, b = 1)
theorem x26_8 : ¬ drop0% List.pairwise_cons_of_mem 6 := fun h =>
  absurd (@h ℕ (fun a b => a ≠ b) [1, 0] 0 1 symmNe (by decide)) (by decide)
-- `List.Pairwise.cons_cons_of_trans` idx 2: necessary (R = ≠, a = 0, b = 1, l = [0])
theorem x26_9 : ¬ drop0% List.Pairwise.cons_cons_of_trans 2 := fun h =>
  absurd (@h ℕ (fun a b => a ≠ b) [0] 0 1 (by decide) (by decide)) (by decide)
-- `List.tfae_cons_of_mem` idx 2: necessary (a = False, l = [True])
theorem x26_10 : ¬ drop0% List.tfae_cons_of_mem 2 := fun h =>
  absurd (@h False [True]) (by simp [List.tfae_cons_cons])
-- `List.tfae_concat_of_mem` idx 2: necessary (a = False, l = [True])
theorem x26_11 : ¬ drop0% List.tfae_concat_of_mem 2 := fun h =>
  absurd (@h False [True]) (by simp [List.tfae_cons_cons])
-- `List.tfae_of_cycle` idx 3: necessary (a = True, b = False, l = [])
theorem x26_12 : ¬ drop0% List.tfae_of_cycle 3 := fun h =>
  absurd (@h True False [] (fun _ => trivial)) (by simp [List.tfae_cons_cons])
-- `List.tfae_of_cycle` idx 4: necessary (a = False, b = True, l = [])
theorem x26_13 : ¬ drop0% List.tfae_of_cycle 4 := fun h =>
  absurd (@h False True [] (by simp)) (by simp [List.tfae_cons_cons])
-- `List.TFAE.subset` idx 2: necessary (l₁ = l₂ = [True, False])
theorem x26_14 : ¬ drop0% List.TFAE.subset 2 := fun h =>
  absurd (@h [True, False] [True, False] (List.Subset.refl _)) (by simp [List.tfae_cons_cons])
-- `List.TFAE.subset` idx 3: necessary (l₁ = [True, False], l₂ = [True])
theorem x26_15 : ¬ drop0% List.TFAE.subset 3 := fun h =>
  absurd (@h [True, False] [True] (by simp [List.tfae_cons_cons])) (by simp [List.tfae_cons_cons])
-- `List.tfae_congr` idx 2: necessary (l₁ = [True, False], l₂ = [True])
theorem x26_16 : ¬ drop0% List.tfae_congr 2 := fun h =>
  absurd (@h [True, False] [True] (by simp)) (by simp [List.tfae_cons_cons])
-- `List.tfae_congr` idx 3: necessary (l₁ = [True], l₂ = [True, False])
theorem x26_17 : ¬ drop0% List.tfae_congr 3 := fun h =>
  absurd (@h [True] [True, False] (by simp)) (by simp [List.tfae_cons_cons])
-- `List.Perm.tfae_iff` idx 2: necessary (l₁ = [True, False], l₂ = [True])
theorem x26_18 : ¬ drop0% List.Perm.tfae_iff 2 := fun h =>
  absurd (@h [True, False] [True]) (by simp [List.tfae_cons_cons])
-- `List.tfae_of_forall` idx 2: necessary (b = True, l = [True, False])
theorem x26_19 : ¬ drop0% List.tfae_of_forall 2 := fun h =>
  absurd (@h True [True, False]) (by simp [List.tfae_cons_cons])
-- `List.TFAE.out` idx 1: necessary (l = [True, False], i = 1, j = 2)
theorem x26_20 : ¬ drop0% List.TFAE.out 1 := fun h =>
  (@h [True, False] 1 2 True False rfl rfl (by decide) (by decide)).mp trivial
-- `List.forall_tfae` idx 2: necessary (α = ℕ, l = [fun _ => True, fun a => a = 0])
theorem x26_21 : ¬ drop0% List.forall_tfae 2 := fun h => by
  have := @h ℕ [fun _ => True, fun a => a = 0]
  simp [List.tfae_cons_cons] at this; have := this 1; simp at this
-- `List.exists_tfae` idx 2: necessary (α = ℕ, l = [fun _ => True, fun _ => False])
theorem x26_22 : ¬ drop0% List.exists_tfae 2 := fun h =>
  absurd (@h ℕ [fun _ => True, fun _ => False]) (by simp [List.tfae_cons_cons])
-- `List.TFAE.not` idx 1: necessary (l = [True, False])
theorem x26_23 : ¬ drop0% List.TFAE.not 1 := fun h =>
  absurd (@h [True, False]) (by simp [List.tfae_cons_cons])
-- `List.HasPeriod.infix` idx 4: necessary (u = w = [0,1], p = 1)
theorem x26_24 : ¬ drop0% List.HasPeriod.infix 4 := fun h =>
  absurd (@h ℕ [0, 1] [0, 1] 1 (List.infix_refl _)) (by unfold List.HasPeriod; decide)
-- `List.HasPeriod.infix` idx 5: necessary (u = [0,1], w = [0,0], p = 1)
theorem x26_25 : ¬ drop0% List.HasPeriod.infix 5 := fun h =>
  absurd (@h ℕ [0, 1] [0, 0] 1 (by unfold List.HasPeriod; decide)) (by unfold List.HasPeriod; decide)
-- `List.HasPeriod.take_append` idx 4: necessary (p = 2, n = 1, w = [0,1,0,1])
theorem x26_26 : ¬ drop0% List.HasPeriod.take_append 4 := fun h =>
  absurd (@h ℕ 2 1 [0, 1, 0, 1] (by decide) (by unfold List.HasPeriod; decide)) (by unfold List.HasPeriod; decide)
-- `List.HasPeriod.take_append` idx 5: necessary (p = 2, n = 4, w = [0,1,0])
theorem x26_27 : ¬ drop0% List.HasPeriod.take_append 5 := fun h =>
  absurd (@h ℕ 2 4 [0, 1, 0] (by decide) (by unfold List.HasPeriod; decide)) (by unfold List.HasPeriod; decide)
-- `List.HasPeriod.drop_of_hasPeriod_add` idx 4: necessary (q = k = 1, w = [0,1,0])
theorem x26_28 : ¬ drop0% List.HasPeriod.drop_of_hasPeriod_add 4 := fun h =>
  absurd (@h ℕ 1 1 [0, 1, 0] (by unfold List.HasPeriod; decide)) (by unfold List.HasPeriod; decide)
-- `List.HasPeriod.gcd` idx 4: necessary (w = [0,0,1,0,0,1], p = 2, q = 3)
theorem x26_29 : ¬ drop0% List.HasPeriod.gcd 4 := fun h => by
  have := @h ℕ [0, 0, 1, 0, 0, 1] 2 3 (by unfold List.HasPeriod; decide) (by norm_num)
  rw [show Nat.gcd 2 3 = 1 by norm_num] at this; revert this; unfold List.HasPeriod; decide
-- `List.HasPeriod.gcd` idx 5: necessary (w = [0,0,1,0,0,1], p = 3, q = 2)
theorem x26_30 : ¬ drop0% List.HasPeriod.gcd 5 := fun h => by
  have := @h ℕ [0, 0, 1, 0, 0, 1] 3 2 (by unfold List.HasPeriod; decide) (by norm_num)
  rw [show Nat.gcd 3 2 = 1 by norm_num] at this; revert this; unfold List.HasPeriod; decide
-- `List.HasPeriod.gcd` idx 6: necessary (w = [0,1,0], p = 2, q = 3)
theorem x26_31 : ¬ drop0% List.HasPeriod.gcd 6 := fun h => by
  have := @h ℕ [0, 1, 0] 2 3 (by unfold List.HasPeriod; decide) (by unfold List.HasPeriod; decide)
  rw [show Nat.gcd 2 3 = 1 by norm_num] at this; revert this; unfold List.HasPeriod; decide
-- `List.Perm.eraseIdx_of_getElem?_eq` idx 5: necessary (l₁ = l₂ = [0,1], m = 0, n = 1)
theorem x26_32 : ¬ drop0% List.Perm.eraseIdx_of_getElem?_eq 5 := fun h =>
  absurd (@h ℕ [0, 1] [0, 1] 0 1 (List.Perm.refl _)) (by decide)
-- `List.perm_comp_forall₂` idx 6: necessary (r = Eq, l = [0], u = v = [])
theorem x26_33 : ¬ drop0% List.perm_comp_forall₂ 6 := fun h => by
  obtain ⟨b, h1, h2⟩ := @h ℕ ℕ (fun a b => a = b) [0] [] [] .nil
  rw [List.perm_nil] at h2; subst h2; cases h1
-- `List.perm_comp_forall₂` idx 7: necessary (r = Eq, l = u = [], v = [0])
theorem x26_34 : ¬ drop0% List.perm_comp_forall₂ 7 := fun h => by
  obtain ⟨b, h1, h2⟩ := @h ℕ ℕ (fun a b => a = b) [] [] [0] (List.Perm.refl _)
  cases h1; exact absurd h2.length_eq (by simp)
-- `List.rel_perm_imp` idx 3: necessary (r = full relation, [0] ~ [0] but not [0] ~ [1])
theorem x26_35 : ¬ drop0% List.rel_perm_imp 3 := fun h =>
  absurd ((@h ℕ ℕ (fun _ _ => True)) (List.Forall₂.cons trivial .nil : List.Forall₂ (fun (_:ℕ) (_:ℕ) => True) [0] [0])
    (List.Forall₂.cons trivial .nil : List.Forall₂ (fun (_:ℕ) (_:ℕ) => True) [0] [1]) (List.Perm.refl _)) (by decide)
-- `List.rel_perm` idx 3: necessary (r = full relation)
theorem x26_36 : ¬ drop0% List.rel_perm 3 := fun h =>
  absurd (((@h ℕ ℕ (fun _ _ => True)) (List.Forall₂.cons trivial .nil : List.Forall₂ (fun (_:ℕ) (_:ℕ) => True) [0] [0])
    (List.Forall₂.cons trivial .nil : List.Forall₂ (fun (_:ℕ) (_:ℕ) => True) [0] [1])).mp (List.Perm.refl _)) (by decide)
-- `List.Perm.foldl_eq` idx 5: necessary (f b a = a, [0,1] vs [1,0])
theorem x26_37 : ¬ drop0% List.Perm.foldl_eq 5 := fun h =>
  absurd (@h ℕ ℕ (fun _ a => a) [0, 1] [1, 0] (by decide) 0) (by decide)
-- `List.Perm.foldr_eq` idx 5: necessary (f a b = a, [0,1] vs [1,0])
theorem x26_38 : ¬ drop0% List.Perm.foldr_eq 5 := fun h =>
  absurd (@h ℕ ℕ (fun a _ => a) [0, 1] [1, 0] (by decide) 0) (by decide)
-- `List.Perm.foldl_op_eq` idx 2: necessary (op a b = a*b+1, commutative, not associative)
theorem x26_39 : ¬ drop0% List.Perm.foldl_op_eq 2 := fun h =>
  absurd (@h ℕ (fun a b => a * b + 1) ⟨fun a b => by rw [Nat.mul_comm]⟩ [0, 1] [1, 0] 0 (by decide)) (by decide)
-- `List.Perm.foldl_op_eq` idx 3: necessary (op a b = b, associative, not commutative)
theorem x26_40 : ¬ drop0% List.Perm.foldl_op_eq 3 := fun h =>
  absurd (@h ℕ (fun _ b => b) ⟨fun _ _ _ => rfl⟩ [0, 1] [1, 0] 0 (by decide)) (by decide)
-- `List.Perm.foldl_op_eq` idx 7: necessary (op = +, [0] vs [1])
theorem x26_41 : ¬ drop0% List.Perm.foldl_op_eq 7 := fun h =>
  absurd (@h ℕ (· + ·) ⟨Nat.add_assoc⟩ ⟨Nat.add_comm⟩ [0] [1] 0) (by decide)
-- `List.Perm.foldr_op_eq` idx 2: necessary (op a b = a*b+1)
theorem x26_42 : ¬ drop0% List.Perm.foldr_op_eq 2 := fun h =>
  absurd (@h ℕ (fun a b => a * b + 1) ⟨fun a b => by rw [Nat.mul_comm]⟩ [0, 1] [1, 0] 0 (by decide)) (by decide)
-- `List.Perm.foldr_op_eq` idx 3: necessary (op a b = a)
theorem x26_43 : ¬ drop0% List.Perm.foldr_op_eq 3 := fun h =>
  absurd (@h ℕ (fun a _ => a) ⟨fun _ _ _ => rfl⟩ [0, 1] [1, 0] 0 (by decide)) (by decide)
-- `List.Perm.foldr_op_eq` idx 7: necessary (op = +, [0] vs [1])
theorem x26_44 : ¬ drop0% List.Perm.foldr_op_eq 7 := fun h =>
  absurd (@h ℕ (· + ·) ⟨Nat.add_assoc⟩ ⟨Nat.add_comm⟩ [0] [1] 0) (by decide)
-- `List.Perm.flatMap` idx 7: necessary (l = [0], f = [0], g = [])
theorem x26_45 : ¬ drop0% List.Perm.flatMap 7 := fun h =>
  absurd (@h ℕ ℕ [0] [0] (fun _ => [0]) (fun _ => []) (List.Perm.refl _)) (by decide)
-- `List.Perm.product` idx 6: necessary (l₁ = [0], l₂ = [1], t = [0])
theorem x26_46 : ¬ drop0% List.Perm.product 6 := fun h =>
  absurd (@h ℕ ℕ [0] [1] [0] [0] (List.Perm.refl _)) (by decide)
-- `List.Perm.product` idx 7: necessary (l = [0], t₁ = [0], t₂ = [1])
theorem x26_47 : ¬ drop0% List.Perm.product 7 := fun h =>
  absurd (@h ℕ ℕ [0] [0] [0] [1] (List.Perm.refl _)) (by decide)
-- `List.Perm.bagInter` idx 6: necessary (l₁ = [0], l₂ = [1], t = [0])
theorem x26_48 : ¬ drop0% List.Perm.bagInter 6 := fun h =>
  absurd (@h ℕ _ [0] [1] [0] [0] (List.Perm.refl _)) (by decide)
-- `List.Perm.bagInter` idx 7: necessary (l = [0], t₁ = [0], t₂ = [1])
theorem x26_49 : ¬ drop0% List.Perm.bagInter 7 := fun h =>
  absurd (@h ℕ _ [0] [0] [0] [1] (List.Perm.refl _)) (by decide)
-- `List.Perm.take_inter` idx 6: necessary (xs = ys = [0,0], n = 1)
theorem x26_50 : ¬ drop0% List.Perm.take_inter 6 := fun h =>
  absurd (@h ℕ _ [0, 0] [0, 0] 1 (List.Perm.refl _)) (by decide)
-- `List.Perm.drop_inter` idx 6: necessary (xs = ys = [0,0], n = 1)
theorem x26_51 : ¬ drop0% List.Perm.drop_inter 6 := fun h =>
  absurd (@h ℕ _ [0, 0] [0, 0] 1 (List.Perm.refl _)) (by decide)
-- `List.Perm.dropSlice_inter` idx 7: necessary (xs = ys = [0,0], n = 0, m = 1)
theorem x26_52 : ¬ drop0% List.Perm.dropSlice_inter 7 := fun h =>
  absurd (@h ℕ _ [0, 0] [0, 0] 0 1 (List.Perm.refl _)) (by decide)
-- `List.Subperm.map` idx 5: removable (map preserves both the permutation and the sublist witnessing a subperm, for any f)
theorem x26_53 : drop% List.Subperm.map 5 := by
  intro α β l₁ l₂ f h
  obtain ⟨l, p, s⟩ := h
  exact ⟨_, p.map f, s.map f⟩
-- `List.Pi.forall_rel_cons_ext` idx 10: necessary (r = False, l = [], j = i)
theorem x26_54 : ¬ drop0% List.Pi.forall_rel_cons_ext 10 := fun h =>
  @h ℕ _ (fun _ => True) 0 [] (fun _ _ _ => False) trivial trivial (fun _ h => (List.not_mem_nil h).elim)
    (fun _ h => (List.not_mem_nil h).elim) (fun _ h => (List.not_mem_nil h).elim) 0 (by simp)
-- `List.Pi.forall_rel_cons_ext` idx 11: necessary (r holds only at index 0, i = 0, l = [1], j = 1)
theorem x26_55 : ¬ drop0% List.Pi.forall_rel_cons_ext 11 := fun h => by
  have := @h ℕ _ (fun _ => True) 0 [1] (fun i _ _ => i = 0) trivial trivial (fun _ _ => trivial)
    (fun _ _ => trivial) rfl 1 (by simp)
  simp at this
-- `List.Pi.forall_rel_cons_ext` idx 13: necessary (dependent; j = 1 ∉ [0])
theorem x26_56 : ¬ indep0% List.Pi.forall_rel_cons_ext 13 := fun h => by
  have := @h ℕ _ (fun _ => True) 0 [] (fun _ _ _ => True) trivial trivial (fun _ _ => trivial)
    (fun _ _ => trivial) trivial (fun _ _ => trivial) 1
  simp at this
-- `mem_list_primes_of_dvd_prod` idx 3: necessary (M = ℤ, p = -2, L = [2])
theorem x26_57 : ¬ drop0% mem_list_primes_of_dvd_prod 3 := fun h =>
  absurd (@h ℤ _ _ (-2) (Int.prime_iff_natAbs_prime.mpr (by simpa using Nat.prime_two)) [2] (by simpa using Int.prime_two) (by decide)) (by decide)
-- `perm_of_prod_eq_prod` idx 3: necessary (M = ℤ, l₁ = [2,2], l₂ = [-2,-2])
theorem x26_58 : ¬ drop0% perm_of_prod_eq_prod 3 := fun h =>
  absurd (@h ℤ _ _ [2, 2] [-2, -2] (by decide) (by simpa using Int.prime_two) (by simpa using (Int.prime_iff_natAbs_prime.mpr (by simpa using Nat.prime_two)))) (by decide)
-- `perm_of_prod_eq_prod` idx 6: necessary (M = ℕ, [2] vs [3])
theorem x26_59 : ¬ drop0% perm_of_prod_eq_prod 6 := fun h =>
  absurd (@h ℕ _ _ _ [2] [3] (by simpa using Nat.prime_two.prime) (by simpa using Nat.prime_three.prime)) (by decide)
-- `List.rotate_eq_self_iff_eq_replicate` idx 1: necessary (α = Empty, l = [])
theorem x26_60 : ¬ drop0% List.rotate_eq_self_iff_eq_replicate 1 := fun h => by
  obtain ⟨a, -⟩ := (@h Empty []).mp (fun _ => rfl); exact a.elim
-- `List.rotate_one_eq_self_iff_eq_replicate` idx 1: necessary (α = Empty, l = [])
theorem x26_61 : ¬ drop0% List.rotate_one_eq_self_iff_eq_replicate 1 := fun h => by
  obtain ⟨a, -⟩ := (@h Empty []).mp rfl; exact a.elim
-- `List.Shortlex.of_lex` idx 4: necessary (r = <, s = [0,0], t = [1])
theorem x26_62 : ¬ drop0% List.Shortlex.of_lex 4 := fun h => by
  have := @h ℕ (· < ·) [0, 0] [1] (List.Lex.rel (by decide))
  rw [List.shortlex_def] at this; simp at this
-- `List.shortlex_iff_lex` idx 4: necessary (r = <, s = [0,0], t = [1])
theorem x26_63 : ¬ drop0% List.shortlex_iff_lex 4 := fun h => by
  have := (@h ℕ (· < ·) [0, 0] [1]).mpr (List.Lex.rel (by decide))
  rw [List.shortlex_def] at this; simp at this
-- `List.Shortlex.cons` idx 2: removable (equal lengths stay equal and List.Lex.cons needs no irreflexivity)
theorem x26_64 : drop% List.Shortlex.cons 2 := by
  intro α r a s t h
  rw [List.shortlex_def] at *
  rcases h with h | ⟨h1, h2⟩
  · left; simpa using h
  · right; exact ⟨by simp [h1], List.Lex.cons h2⟩
-- `List.Shortlex.trichotomous` idx 2: necessary (empty relation on Bool: [true], [false] incomparable)
theorem x26_65 : ¬ drop0% List.Shortlex.trichotomous 2 := fun h => by
  have := (@h Bool (fun _ _ => False)).trichotomous [true] [false]
  simp [List.shortlex_def] at this
-- `List.Shortlex.asymm` idx 2: necessary (full relation on Unit: [()] below itself)
theorem x26_66 : ¬ drop0% List.Shortlex.asymm 2 := fun h => by
  have hs : List.Shortlex (fun _ _ : Unit => True) [()] [()] :=
    List.shortlex_def.mpr (Or.inr ⟨rfl, List.Lex.rel trivial⟩)
  exact (@h Unit (fun _ _ => True)).asymm _ _ hs hs
-- `List.Shortlex.wf` idx 2: necessary (full relation on Unit: [()] below itself)
theorem x26_67 : ¬ drop0% List.Shortlex.wf 2 := fun h => by
  have hs : List.Shortlex (fun _ _ : Unit => True) [()] [()] :=
    List.shortlex_def.mpr (Or.inr ⟨rfl, List.Lex.rel trivial⟩)
  exact acc_self hs ((@h Unit (fun _ _ => True)).apply _)
-- `List.NodupKeys.eq_of_fst_eq` idx 3: necessary (l = [⟨0,0⟩, ⟨0,1⟩])
theorem x26_68 : ¬ drop0% List.NodupKeys.eq_of_fst_eq 3 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) dl ⟨0, 0⟩ ⟨0, 1⟩ (by decide) (by decide) rfl) (by decide)
-- `List.NodupKeys.eq_of_fst_eq` idx 8: necessary (l = [⟨0,0⟩, ⟨1,0⟩])
theorem x26_69 : ¬ drop0% List.NodupKeys.eq_of_fst_eq 8 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) [⟨0, 0⟩, ⟨1, 0⟩] (by simp [List.NodupKeys, List.keys]) ⟨0, 0⟩ ⟨1, 0⟩ (by decide) (by decide)) (by decide)
-- `List.NodupKeys.eq_of_mk_mem` idx 6: necessary (l = [⟨0,0⟩, ⟨0,1⟩])
theorem x26_70 : ¬ drop0% List.NodupKeys.eq_of_mk_mem 6 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) 0 0 1 dl (by decide) (by decide)) (by decide)
-- `List.NodupKeys.sublist` idx 4: necessary (l₁ = [⟨0,0⟩, ⟨0,1⟩], l₂ = [])
theorem x26_71 : ¬ drop0% List.NodupKeys.sublist 4 := fun h => dl_not (@h ℕ (fun _ => ℕ) dl [] nk_nil)
-- `List.NodupKeys.sublist` idx 5: necessary (l₁ = l₂ = [⟨0,0⟩, ⟨0,1⟩])
theorem x26_72 : ¬ drop0% List.NodupKeys.sublist 5 := fun h => dl_not (@h ℕ (fun _ => ℕ) dl dl (List.Sublist.refl _))
-- `List.perm_nodupKeys` idx 4: necessary (l₁ = [⟨0,0⟩, ⟨0,1⟩], l₂ = [])
theorem x26_73 : ¬ drop0% List.perm_nodupKeys 4 := fun h => dl_not ((@h ℕ (fun _ => ℕ) dl []).mpr nk_nil)
-- `List.mem_ext` idx 4: necessary (l₀ = [x, x], l₁ = [x])
theorem x26_74 : ¬ drop0% List.mem_ext 4 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) [⟨0, 0⟩, ⟨0, 0⟩] [⟨0, 0⟩] (by decide) (by simp)) (by decide)
-- `List.mem_ext` idx 5: necessary (l₀ = [x], l₁ = [x, x])
theorem x26_75 : ¬ drop0% List.mem_ext 5 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) [⟨0, 0⟩] [⟨0, 0⟩, ⟨0, 0⟩] (by decide) (by simp)) (by decide)
-- `List.mem_dlookup` idx 6: necessary (l = [⟨0,0⟩, ⟨0,1⟩], a = 0, b = 1)
theorem x26_76 : ¬ drop0% List.mem_dlookup 6 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ 0 1 dl (by decide)) (by decide)
-- `List.mem_dlookup_iff` idx 6: necessary (l = [⟨0,0⟩, ⟨0,1⟩], a = 0, b = 1)
theorem x26_77 : ¬ drop0% List.mem_dlookup_iff 6 := fun h =>
  absurd ((@h ℕ (fun _ => ℕ) _ 0 1 dl).mpr (by decide)) (by decide)
-- `List.perm_dlookup` idx 6: necessary (l₁ = [⟨0,0⟩, ⟨0,1⟩], l₂ its reverse, a = 0)
theorem x26_78 : ¬ drop0% List.perm_dlookup 6 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ 0 dl dl.reverse dl_perm) (by decide)
-- `List.lookup_ext` idx 5: necessary (l₀ = [x, x], l₁ = [x])
theorem x26_79 : ¬ drop0% List.lookup_ext 5 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ [⟨0, 0⟩, ⟨0, 0⟩] [⟨0, 0⟩] (by simp [List.NodupKeys, List.keys])
    (by intro x y; by_cases hx : 0 = x <;> simp [List.dlookup, hx])) (by decide)
-- `List.lookup_ext` idx 6: necessary (l₀ = [x], l₁ = [x, x])
theorem x26_80 : ¬ drop0% List.lookup_ext 6 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ [⟨0, 0⟩] [⟨0, 0⟩, ⟨0, 0⟩] (by simp [List.NodupKeys, List.keys])
    (by intro x y; by_cases hx : 0 = x <;> simp [List.dlookup, hx])) (by decide)
-- `List.dlookup_map` idx 8: necessary (f = const 0, l = [⟨0,0⟩, ⟨1,1⟩], a = 1)
theorem x26_81 : ¬ drop0% List.dlookup_map 8 := fun h =>
  absurd (@h ℕ ℕ (fun _ => ℕ) (fun _ => ℕ) _ _ [⟨0, 0⟩, ⟨1, 1⟩] (fun _ => 0) (fun _ x => x) 1) (by decide)
-- `List.NodupKeys.map₁` idx 6: necessary (f = id, l = [⟨0,0⟩, ⟨0,1⟩])
theorem x26_82 : ¬ drop0% List.NodupKeys.map₁ 6 := fun h => by
  have := @h ℕ ℕ ℕ id Function.injective_id dl
  simp [dl, List.NodupKeys, List.keys, Sigma.map] at this
-- `List.NodupKeys.map₂` idx 5: necessary (f = id, l = [⟨0,0⟩, ⟨0,1⟩])
theorem x26_83 : ¬ drop0% List.NodupKeys.map₂ 5 := fun h => by
  have := @h ℕ (fun _ => ℕ) (fun _ => ℕ) (fun _ x => x) dl
  simp [dl, List.NodupKeys, List.keys, Sigma.map] at this
-- `List.sublist_dlookup` idx 7: necessary (l₁ = [⟨0,1⟩], l₂ = [⟨0,0⟩, ⟨0,1⟩])
theorem x26_84 : ¬ drop0% List.sublist_dlookup 7 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ [⟨0, 1⟩] dl 0 1 (by decide) (by decide)) (by decide)
-- `List.perm_lookupAll` idx 6: necessary (l₁ = [⟨0,0⟩, ⟨0,1⟩], l₂ its reverse)
theorem x26_85 : ¬ drop0% List.perm_lookupAll 6 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ 0 dl dl.reverse dl_perm) (by decide)
-- `List.kreplace_self` idx 6: necessary (l = [⟨0,0⟩, ⟨0,1⟩], a = 0, b = 1)
theorem x26_86 : ¬ drop0% List.kreplace_self 6 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ 0 1 dl (by decide)) (by simp [dl, List.kreplace])
-- `List.Perm.kreplace` idx 7: necessary (l₁ = [⟨0,0⟩, ⟨0,1⟩], l₂ its reverse, a = 0, b = 2)
theorem x26_87 : ¬ drop0% List.Perm.kreplace 7 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ 0 2 dl dl.reverse dl_perm) (by simp [dl, List.kreplace])
-- `List.NodupKeys.kerase` idx 5: necessary (l = [⟨0,0⟩, ⟨0,1⟩], a = 1)
theorem x26_88 : ¬ drop0% List.NodupKeys.kerase 5 := fun h => by
  have := @h ℕ (fun _ => ℕ) dl _ 1
  simp [dl, List.NodupKeys, List.keys, Sigma.map] at this
-- `List.Perm.kerase` idx 6: necessary (l₁ = [⟨0,0⟩, ⟨0,1⟩], l₂ its reverse, a = 0)
theorem x26_89 : ¬ drop0% List.Perm.kerase 6 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ 0 dl dl.reverse dl_perm) (by decide)
-- `List.kinsert_nodupKeys` idx 6: necessary (l = [⟨1,0⟩, ⟨1,1⟩], a = 0)
theorem x26_90 : ¬ drop0% List.kinsert_nodupKeys 6 := fun h => by
  have := @h ℕ (fun _ => ℕ) _ 0 0 [⟨1, 0⟩, ⟨1, 1⟩]
  simp [List.kinsert, List.NodupKeys, List.keys] at this
-- `List.Perm.kinsert` idx 7: necessary (l₁ = [⟨0,0⟩, ⟨0,1⟩], l₂ its reverse, a = 0, b = 2)
theorem x26_91 : ¬ drop0% List.Perm.kinsert 7 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ 0 2 dl dl.reverse dl_perm) (by decide)
-- `List.NodupKeys.kunion` idx 5: necessary (l₁ = [⟨0,0⟩, ⟨0,1⟩], l₂ = [])
theorem x26_92 : ¬ drop0% List.NodupKeys.kunion 5 := fun h => by
  have := @h ℕ (fun _ => ℕ) dl [] _ nk_nil
  simp [dl, List.kunion, List.NodupKeys, List.keys] at this
-- `List.NodupKeys.kunion` idx 6: necessary (l₁ = [], l₂ = [⟨0,0⟩, ⟨0,1⟩])
theorem x26_93 : ¬ drop0% List.NodupKeys.kunion 6 := fun h => by
  have := @h ℕ (fun _ => ℕ) [] dl _ nk_nil
  simp [dl, List.kunion, List.NodupKeys, List.keys] at this
-- `List.Perm.kunion_left` idx 6: necessary (l = [⟨0,5⟩], l₁ = [⟨0,0⟩, ⟨0,1⟩], l₂ its reverse)
theorem x26_94 : ¬ drop0% List.Perm.kunion_left 6 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ [⟨0, 5⟩] dl dl.reverse dl_perm) (by decide)
-- `List.Perm.kunion` idx 7: necessary (l₁ = l₂ = [⟨0,5⟩], l₃ = [⟨0,0⟩, ⟨0,1⟩], l₄ its reverse)
theorem x26_95 : ¬ drop0% List.Perm.kunion 7 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ [⟨0, 5⟩] [⟨0, 5⟩] dl dl.reverse (List.Perm.refl _) dl_perm) (by decide)
-- `List.Perm.kunion` idx 8: necessary (l₁ = [⟨0,0⟩], l₂ = l₃ = l₄ = [])
theorem x26_96 : ¬ drop0% List.Perm.kunion 8 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ [⟨0, 0⟩] [] [] [] nk_nil (List.Perm.refl _)) (by decide)
-- `List.mem_dlookup_kunion_middle` idx 9: necessary (l₁ = [], l₂ = [⟨0,1⟩], l₃ = [⟨0,0⟩], a = b = 0)
theorem x26_97 : ¬ drop0% List.mem_dlookup_kunion_middle 9 := fun h =>
  absurd (@h ℕ (fun _ => ℕ) _ 0 0 [] [⟨0, 1⟩] [⟨0, 0⟩] (by decide)) (by decide)
-- `List.signVariations_congr` idx 8: necessary (l₁ = [1,-1], l₂ = [1,1] in ℤ)
theorem x26_98 : ¬ drop0% List.signVariations_congr 8 := fun h =>
  absurd (@h ℤ _ _ ℤ _ _ [1, -1] [1, 1]) (by decide)
-- `List.signVariations_map` idx 7: necessary (f = 0, l = [1,-1])
theorem x26_99 : ¬ drop0% List.signVariations_map 7 := fun h =>
  absurd (@h ℤ _ _ ℤ _ _ (fun _ => 0) [1, -1]) (by decide)
-- `List.signVariations_map_of_sign_eq_neg` idx 7: necessary (f = 0, l = [1,-1])
theorem x26_100 : ¬ drop0% List.signVariations_map_of_sign_eq_neg 7 := fun h =>
  absurd (@h ℤ _ _ ℤ _ _ (fun _ => 0) [1, -1]) (by decide)
-- `perm_of_prod_eq_prod` idx 2: necessary (MaxN: max-multiplication monoid, [1,2] and [2] both have product 2)
theorem x26_101 : ¬ drop0% perm_of_prod_eq_prod 2 := fun h => by
  have := @h MaxN _ _ [toM 1, toM 2] [toM 2] (ofM_inj.1 (by simp [List.prod_cons]))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p (rfl | rfl) <;> exact maxN_prime _ (by decide) (by decide))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro p rfl; exact maxN_prime _ (by decide) (by decide))
  exact absurd this.length_eq (by simp)
-- `List.orderedInsert_erase` idx 4: necessary (full relation, x = 0, xs = [1,0])
theorem x26_102 : ¬ drop0% List.orderedInsert_erase 4 := fun h =>
  absurd (@h ℕ (fun _ _ => True) (fun _ _ => instDecidableTrue) _ 0 [1, 0] (by decide) (by decide)) (by decide)
-- `List.Sublist.orderedInsert_sublist` idx 3: necessary (Fin 3, r = {(0,2),(1,0)}, as = [2], bs = [0,2], x = 1)
theorem x26_103 : ¬ drop0% List.Sublist.orderedInsert_sublist 3 := fun h =>
  absurd (@h (Fin 3) (RC 12) _ [2] [0, 2] 1 (by decide) (by decide)) (by decide)
-- `List.Sublist.orderedInsert_sublist` idx 8: necessary (Fin 3, r = {(0,0)}, as = [1], bs = [0,1], x = 0)
theorem x26_104 : ¬ drop0% List.Sublist.orderedInsert_sublist 8 := fun h =>
  absurd (@h (Fin 3) (RC 1) _ trn1 [1] [0, 1] 0 (by decide)) (by decide)
-- `List.Pairwise.orderedInsert` idx 4: necessary (Fin 3, reflexive rock-paper-scissors, a = 1, l = [2,0])
theorem x26_105 : ¬ drop0% List.Pairwise.orderedInsert 4 := fun h =>
  absurd (@h (Fin 3) (RC 371) _ tot371 1 [2, 0] (by decide)) (by decide)
-- `List.pairwise_insertionSort` idx 4: necessary (Fin 3, rock-paper-scissors, l = [2,1,0])
theorem x26_106 : ¬ drop0% List.pairwise_insertionSort 4 := fun h =>
  absurd (@h (Fin 3) (RC 371) _ tot371 [2, 1, 0]) (by decide)
-- `List.sublist_insertionSort` idx 5: necessary (r = ≤, l = c = [1,0])
theorem x26_107 : ¬ drop0% List.sublist_insertionSort 5 := fun h =>
  absurd (@h ℕ (· ≤ ·) _ [1, 0] [1, 0] (List.Sublist.refl _)) (by decide)
-- `List.pair_sublist_insertionSort` idx 6: necessary (r = ≤, a = 1, b = 0, l = [1,0])
theorem x26_108 : ¬ drop0% List.pair_sublist_insertionSort 6 := fun h =>
  absurd (@h ℕ (· ≤ ·) _ 1 0 [1, 0] (List.Sublist.refl _)) (by decide)
-- `List.sublist_insertionSort'` idx 3: necessary (Fin 3, total preorder with 0 ~ 1, l = [0,1], c = [1,0])
theorem x26_109 : ¬ drop0% List.sublist_insertionSort' 3 := fun h =>
  absurd (@h (Fin 3) (RC 319) _ tot319 trn319 [0, 1] [1, 0] (by decide) (by decide)) (by decide)
-- `List.sublist_insertionSort'` idx 5: necessary (Fin 3, rock-paper-scissors, l = [0,2,1], c = [2,0])
theorem x26_110 : ¬ drop0% List.sublist_insertionSort' 5 := fun h =>
  absurd (@h (Fin 3) (RC 371) _ ant371 tot371 [0, 2, 1] [2, 0] (by decide) (by decide)) (by decide)
-- `List.sublist_insertionSort'` idx 8: necessary (r = ≤, l = c = [1,0])
theorem x26_111 : ¬ drop0% List.sublist_insertionSort' 8 := fun h =>
  absurd (@h ℕ (· ≤ ·) _ antLe totLe trnLe [1, 0] [1, 0] (List.Subperm.refl _)) (by decide)
-- `List.pair_sublist_insertionSort'` idx 3: necessary (Fin 3, total preorder with 0 ~ 1, a = 1, b = 0, l = [0,1])
theorem x26_112 : ¬ drop0% List.pair_sublist_insertionSort' 3 := fun h =>
  absurd (@h (Fin 3) (RC 319) _ tot319 trn319 1 0 [0, 1] (by decide) (by decide)) (by decide)
-- `List.pair_sublist_insertionSort'` idx 5: necessary (Fin 3, rock-paper-scissors, a = 2, b = 0, l = [0,2,1])
theorem x26_113 : ¬ drop0% List.pair_sublist_insertionSort' 5 := fun h =>
  absurd (@h (Fin 3) (RC 371) _ ant371 tot371 2 0 [0, 2, 1] (by decide) (by decide)) (by decide)
-- `List.pair_sublist_insertionSort'` idx 9: necessary (r = ≤, a = 1, b = 0, l = [1,0])
theorem x26_114 : ¬ drop0% List.pair_sublist_insertionSort' 9 := fun h =>
  absurd (@h ℕ (· ≤ ·) _ antLe totLe trnLe 1 0 [1, 0] (List.Subperm.refl _)) (by decide)
-- `List.Perm.eq_of_pairwise'` idx 2: necessary (full relation, [0,1] vs [1,0])
theorem x26_115 : ¬ drop0% List.Perm.eq_of_pairwise' 2 := fun h =>
  absurd (@h ℕ (fun _ _ => True) [0, 1] [1, 0] (by decide) (by decide) (by decide)) (by decide)
-- `List.Perm.eq_of_pairwise'` idx 5: necessary (r = ≤, l₁ = [1,0], l₂ = [0,1])
theorem x26_116 : ¬ drop0% List.Perm.eq_of_pairwise' 5 := fun h =>
  absurd (@h ℕ (· ≤ ·) antLe [1, 0] [0, 1] (by decide) (by decide)) (by decide)
-- `List.sublist_of_subperm_of_pairwise` idx 2: necessary (full relation, [1,0] and [0,1])
theorem x26_117 : ¬ drop0% List.sublist_of_subperm_of_pairwise 2 := fun h =>
  absurd (@h ℕ (fun _ _ => True) [1, 0] [0, 1] (by decide) (by decide) (by decide)) (by decide)
-- `List.sublist_of_subperm_of_pairwise` idx 6: necessary (r = ≤, l₁ = [1,0], l₂ = [0,1])
theorem x26_118 : ¬ drop0% List.sublist_of_subperm_of_pairwise 6 := fun h =>
  absurd (@h ℕ (· ≤ ·) antLe [1, 0] [0, 1] (by decide) (by decide)) (by decide)
-- `List.sublist_of_subperm_of_pairwise` idx 7: necessary (r = ≤, l₁ = [0,1], l₂ = [1,0])
theorem x26_119 : ¬ drop0% List.sublist_of_subperm_of_pairwise 7 := fun h =>
  absurd (@h ℕ (· ≤ ·) antLe [0, 1] [1, 0] (by decide) (by decide)) (by decide)
-- `List.Subset.antisymm_of_pairwise` idx 2: necessary (r = ≠, [0,1] and [1,0])
theorem x26_120 : ¬ drop0% List.Subset.antisymm_of_pairwise 2 := fun h =>
  absurd (@h ℕ (fun a b => a ≠ b) irrNe [0, 1] [1, 0] (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `List.Subset.antisymm_of_pairwise` idx 3: necessary (r = ≤, [0,0] and [0])
theorem x26_121 : ¬ drop0% List.Subset.antisymm_of_pairwise 3 := fun h =>
  absurd (@h ℕ (· ≤ ·) antLe [0, 0] [0] (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `List.Subset.antisymm_of_pairwise` idx 6: necessary (r = <, l₁ = [1,0], l₂ = [0,1])
theorem x26_122 : ¬ drop0% List.Subset.antisymm_of_pairwise 6 := fun h =>
  absurd (@h ℕ (· < ·) antLt irrLt [1, 0] [0, 1] (by decide) (by decide) (by decide)) (by decide)
-- `List.Subset.antisymm_of_pairwise` idx 7: necessary (r = <, l₁ = [0,1], l₂ = [1,0])
theorem x26_123 : ¬ drop0% List.Subset.antisymm_of_pairwise 7 := fun h =>
  absurd (@h ℕ (· < ·) antLt irrLt [0, 1] [1, 0] (by decide) (by decide) (by decide)) (by decide)
-- `List.Pairwise.eq_of_mem_iff` idx 2: necessary (r = ≠, [0,1] and [1,0])
theorem x26_124 : ¬ drop0% List.Pairwise.eq_of_mem_iff 2 := fun h =>
  absurd (@h ℕ (fun a b => a ≠ b) irrNe [0, 1] [1, 0] (by decide) (by decide) (by intro a; simp; tauto)) (by decide)
-- `List.Pairwise.eq_of_mem_iff` idx 3: necessary (r = ≤, [0,0] and [0])
theorem x26_125 : ¬ drop0% List.Pairwise.eq_of_mem_iff 3 := fun h =>
  absurd (@h ℕ (· ≤ ·) antLe [0, 0] [0] (by decide) (by decide) (by intro a; simp)) (by decide)
-- `List.Pairwise.eq_of_mem_iff` idx 6: necessary (r = <, l₁ = [1,0], l₂ = [0,1])
theorem x26_126 : ¬ drop0% List.Pairwise.eq_of_mem_iff 6 := fun h =>
  absurd (@h ℕ (· < ·) antLt irrLt [1, 0] [0, 1] (by decide) (by intro a; simp; tauto)) (by decide)
-- `List.Pairwise.eq_of_mem_iff` idx 7: necessary (r = <, l₁ = [0,1], l₂ = [1,0])
theorem x26_127 : ¬ drop0% List.Pairwise.eq_of_mem_iff 7 := fun h =>
  absurd (@h ℕ (· < ·) antLt irrLt [0, 1] [1, 0] (by decide) (by intro a; simp; tauto)) (by decide)
-- `List.Pairwise.merge` idx 4: necessary (Fin 3, rock-paper-scissors, l = [0], l' = [1,2])
theorem x26_128 : ¬ drop0% List.Pairwise.merge 4 := fun h =>
  absurd (@h (Fin 3) (RC 371) _ tot371 [0] [1, 2] (by decide) (by decide)) (by simp (config := {decide := true}) only [ms3, List.mergeSort_pair, List.cons_merge_cons, List.merge_right, List.nil_merge, ite_true, ite_false]; try decide)
-- `List.Pairwise.merge` idx 7: necessary (r = ≤, l = [1,0], l' = [])
theorem x26_129 : ¬ drop0% List.Pairwise.merge 7 := fun h =>
  absurd (@h ℕ (· ≤ ·) _ totLe trnLe [1, 0] [] (by decide)) (by simp (config := {decide := true}) only [ms3, List.mergeSort_pair, List.cons_merge_cons, List.merge_right, List.nil_merge, ite_true, ite_false]; try decide)
-- `List.Pairwise.merge` idx 8: necessary (r = ≤, l = [], l' = [1,0])
theorem x26_130 : ¬ drop0% List.Pairwise.merge 8 := fun h =>
  absurd (@h ℕ (· ≤ ·) _ totLe trnLe [] [1, 0] (by decide)) (by simp (config := {decide := true}) only [ms3, List.mergeSort_pair, List.cons_merge_cons, List.merge_right, List.nil_merge, ite_true, ite_false]; try decide)
-- `List.pairwise_mergeSort'` idx 4: necessary (Fin 3, rock-paper-scissors, l = [2,1,0])
theorem x26_131 : ¬ drop0% List.pairwise_mergeSort' 4 := fun h =>
  absurd (@h (Fin 3) (RC 371) _ tot371 [2, 1, 0]) (by simp (config := {decide := true}) only [ms3, List.mergeSort_pair, List.cons_merge_cons, List.merge_right, List.nil_merge, ite_true, ite_false]; try decide)
-- `List.mergeSort_eq_self` idx 3: removable (List.mergeSort_of_pairwise needs no hypotheses on the relation)
theorem x26_132 : drop% List.mergeSort_eq_self 3 := by
  intro α r _ _ _ l h; exact List.mergeSort_of_pairwise (by simpa using h)
-- `List.mergeSort_eq_self` idx 4: removable (List.mergeSort_of_pairwise needs no hypotheses on the relation)
theorem x26_133 : drop% List.mergeSort_eq_self 4 := by
  intro α r _ _ _ l h; exact List.mergeSort_of_pairwise (by simpa using h)
-- `List.mergeSort_eq_self` idx 5: removable (List.mergeSort_of_pairwise needs no hypotheses on the relation)
theorem x26_134 : drop% List.mergeSort_eq_self 5 := by
  intro α r _ _ _ l h; exact List.mergeSort_of_pairwise (by simpa using h)
-- `List.mergeSort_eq_insertionSort` idx 3: necessary (Fin 3, r = {(0,0)}, l = [0,1,0])
theorem x26_135 : ¬ drop0% List.mergeSort_eq_insertionSort 3 := fun h =>
  absurd (@h (Fin 3) (RC 1) _ trn1 ant1 [0, 1, 0]) (by simp (config := {decide := true}) only [ms3, List.mergeSort_pair, List.cons_merge_cons, List.merge_right, List.nil_merge, ite_true, ite_false]; try decide)
-- `List.mergeSort_eq_insertionSort` idx 4: necessary (Fin 3, rock-paper-scissors, l = [2,1,0])
theorem x26_136 : ¬ drop0% List.mergeSort_eq_insertionSort 4 := fun h =>
  absurd (@h (Fin 3) (RC 371) _ tot371 ant371 [2, 1, 0]) (by simp (config := {decide := true}) only [ms3, List.mergeSort_pair, List.cons_merge_cons, List.merge_right, List.nil_merge, ite_true, ite_false]; try decide)
-- `List.SortedLE.map_ofDual` idx 3: necessary (α = ℕ, l a two-element list in ℕᵒᵈ for which the conclusion l.SortedGE fails)
theorem x26_137 : ¬ drop0% List.SortedLE.map_ofDual 3 := fun h => by
  first
  | exact absurd (@h ℕ _ [OrderDual.toDual 1, OrderDual.toDual 0]) (by decide)
  | exact absurd (@h ℕ _ [OrderDual.toDual 0, OrderDual.toDual 1]) (by decide)
-- `List.SortedGE.of_map_ofDual` idx 3: necessary (α = ℕ, l a two-element list in ℕᵒᵈ for which the conclusion (map ofDual l).SortedLE fails)
theorem x26_138 : ¬ drop0% List.SortedGE.of_map_ofDual 3 := fun h => by
  first
  | exact absurd (@h ℕ _ [OrderDual.toDual 1, OrderDual.toDual 0]) (by decide)
  | exact absurd (@h ℕ _ [OrderDual.toDual 0, OrderDual.toDual 1]) (by decide)
-- `List.SortedLE.of_map_ofDual` idx 3: necessary (α = ℕ, l a two-element list in ℕᵒᵈ for which the conclusion (map ofDual l).SortedGE fails)
theorem x26_139 : ¬ drop0% List.SortedLE.of_map_ofDual 3 := fun h => by
  first
  | exact absurd (@h ℕ _ [OrderDual.toDual 1, OrderDual.toDual 0]) (by decide)
  | exact absurd (@h ℕ _ [OrderDual.toDual 0, OrderDual.toDual 1]) (by decide)
-- `List.SortedGT.of_map_ofDual` idx 3: necessary (α = ℕ, l a two-element list in ℕᵒᵈ for which the conclusion (map ofDual l).SortedLT fails)
theorem x26_140 : ¬ drop0% List.SortedGT.of_map_ofDual 3 := fun h => by
  first
  | exact absurd (@h ℕ _ [OrderDual.toDual 1, OrderDual.toDual 0]) (by decide)
  | exact absurd (@h ℕ _ [OrderDual.toDual 0, OrderDual.toDual 1]) (by decide)
-- `List.SortedLT.map_ofDual` idx 3: necessary (α = ℕ, l a two-element list in ℕᵒᵈ for which the conclusion l.SortedGT fails)
theorem x26_141 : ¬ drop0% List.SortedLT.map_ofDual 3 := fun h => by
  first
  | exact absurd (@h ℕ _ [OrderDual.toDual 1, OrderDual.toDual 0]) (by decide)
  | exact absurd (@h ℕ _ [OrderDual.toDual 0, OrderDual.toDual 1]) (by decide)
-- `List.SortedGT.map_ofDual` idx 3: necessary (α = ℕ, l a two-element list in ℕᵒᵈ for which the conclusion l.SortedLT fails)
theorem x26_142 : ¬ drop0% List.SortedGT.map_ofDual 3 := fun h => by
  first
  | exact absurd (@h ℕ _ [OrderDual.toDual 1, OrderDual.toDual 0]) (by decide)
  | exact absurd (@h ℕ _ [OrderDual.toDual 0, OrderDual.toDual 1]) (by decide)
-- `List.SortedLT.of_map_ofDual` idx 3: necessary (α = ℕ, l a two-element list in ℕᵒᵈ for which the conclusion (map ofDual l).SortedGT fails)
theorem x26_143 : ¬ drop0% List.SortedLT.of_map_ofDual 3 := fun h => by
  first
  | exact absurd (@h ℕ _ [OrderDual.toDual 1, OrderDual.toDual 0]) (by decide)
  | exact absurd (@h ℕ _ [OrderDual.toDual 0, OrderDual.toDual 1]) (by decide)
-- `List.SortedLT.of_map_toDual` idx 3: necessary (α = ℕ, l a two-element list in ℕᵒᵈ for which the conclusion (map toDual l).SortedGT fails)
theorem x26_144 : ¬ drop0% List.SortedLT.of_map_toDual 3 := fun h => by
  first
  | exact absurd (@h ℕ _ [OrderDual.toDual 1, OrderDual.toDual 0]) (by decide)
  | exact absurd (@h ℕ _ [OrderDual.toDual 0, OrderDual.toDual 1]) (by decide)
-- `List.SortedGT.map_toDual` idx 3: necessary (α = ℕ, l a two-element list in ℕᵒᵈ for which the conclusion l.SortedLT fails)
theorem x26_145 : ¬ drop0% List.SortedGT.map_toDual 3 := fun h => by
  first
  | exact absurd (@h ℕ _ [OrderDual.toDual 1, OrderDual.toDual 0]) (by decide)
  | exact absurd (@h ℕ _ [OrderDual.toDual 0, OrderDual.toDual 1]) (by decide)
-- `List.Perm.eq_of_sortedLE` idx 4: necessary (ℕ, l₁ = [1, 0], l₂ = [0, 1])
theorem x26_146 : ¬ drop0% List.Perm.eq_of_sortedLE 4 := fun h =>
  absurd (@h ℕ _ [1, 0] [0, 1] (by decide) (by decide)) (by decide)
-- `List.Perm.eq_of_sortedLE` idx 5: necessary (ℕ, l₁ = [0, 1], l₂ = [1, 0])
theorem x26_147 : ¬ drop0% List.Perm.eq_of_sortedLE 5 := fun h =>
  absurd (@h ℕ _ [0, 1] [1, 0] (by decide) (by decide)) (by decide)
-- `List.Perm.eq_of_sortedGE` idx 4: necessary (ℕ, l₁ = [0, 1], l₂ = [1, 0])
theorem x26_148 : ¬ drop0% List.Perm.eq_of_sortedGE 4 := fun h =>
  absurd (@h ℕ _ [0, 1] [1, 0] (by decide) (by decide)) (by decide)
-- `List.Perm.eq_of_sortedGE` idx 5: necessary (ℕ, l₁ = [1, 0], l₂ = [0, 1])
theorem x26_149 : ¬ drop0% List.Perm.eq_of_sortedGE 5 := fun h =>
  absurd (@h ℕ _ [1, 0] [0, 1] (by decide) (by decide)) (by decide)
-- `List.Perm.eq_reverse_of_sortedLE_of_sortedGE` idx 5: necessary (ℕ, l₁ = [1, 0], l₂ = [1, 0])
theorem x26_150 : ¬ drop0% List.Perm.eq_reverse_of_sortedLE_of_sortedGE 5 := fun h =>
  absurd (@h ℕ _ [1, 0] [1, 0] (List.Perm.refl _) (by decide)) (by decide)
-- `List.Perm.eq_reverse_of_sortedLE_of_sortedGE` idx 6: necessary (ℕ, l₁ = [0, 1], l₂ = [0, 1])
theorem x26_151 : ¬ drop0% List.Perm.eq_reverse_of_sortedLE_of_sortedGE 6 := fun h =>
  absurd (@h ℕ _ [0, 1] [0, 1] (List.Perm.refl _) (by decide)) (by decide)
-- `List.SortedGT.eq_reverse_of_mem_iff_of_sortedLT` idx 5: necessary (ℕ, l₁ = [0, 1], l₂ = [0, 1])
theorem x26_152 : ¬ drop0% List.SortedGT.eq_reverse_of_mem_iff_of_sortedLT 5 := fun h =>
  absurd (@h ℕ _ [0, 1] [0, 1] (fun _ => Iff.rfl) (by decide)) (by decide)
-- `List.SortedGT.eq_reverse_of_mem_iff_of_sortedLT` idx 6: necessary (ℕ, l₁ = [1, 0], l₂ = [1, 0])
theorem x26_153 : ¬ drop0% List.SortedGT.eq_reverse_of_mem_iff_of_sortedLT 6 := fun h =>
  absurd (@h ℕ _ [1, 0] [1, 0] (fun _ => Iff.rfl) (by decide)) (by decide)
-- `List.sublist_of_subperm_of_sortedLE` idx 5: necessary (ℕ, l₁ = [1, 0], l₂ = [0, 1])
theorem x26_154 : ¬ drop0% List.sublist_of_subperm_of_sortedLE 5 := fun h =>
  absurd (@h ℕ _ [1, 0] [0, 1] (by decide) (by decide)) (by decide)
-- `List.sublist_of_subperm_of_sortedLE` idx 6: necessary (ℕ, l₁ = [0, 1], l₂ = [1, 0])
theorem x26_155 : ¬ drop0% List.sublist_of_subperm_of_sortedLE 6 := fun h =>
  absurd (@h ℕ _ [0, 1] [1, 0] (by decide) (by decide)) (by decide)
-- `List.sublist_of_subperm_of_sortedGE` idx 5: necessary (ℕ, l₁ = [0, 1], l₂ = [1, 0])
theorem x26_156 : ¬ drop0% List.sublist_of_subperm_of_sortedGE 5 := fun h =>
  absurd (@h ℕ _ [0, 1] [1, 0] (by decide) (by decide)) (by decide)
-- `List.sublist_of_subperm_of_sortedGE` idx 6: necessary (ℕ, l₁ = [1, 0], l₂ = [0, 1])
theorem x26_157 : ¬ drop0% List.sublist_of_subperm_of_sortedGE 6 := fun h =>
  absurd (@h ℕ _ [1, 0] [0, 1] (by decide) (by decide)) (by decide)
-- `_private.Mathlib.Data.List.SplitBy.0.List.isChain_of_mem_splitByLoop` idx 7: necessary (r = <, l = [], a = 2, g = [0,1], m = [1,0,2])
theorem x26_158 : ¬ drop0% _private.Mathlib.Data.List.SplitBy.«0».List.isChain_of_mem_splitByLoop 7 := fun h =>
  absurd (@h ℕ [1, 0, 2] (fun x y => decide (x < y)) [] 2 [0, 1] (by decide) (by decide)) (by decide)
-- `_private.Mathlib.Data.List.SplitBy.0.List.isChain_getLast_head_splitByLoop` idx 6: removable (derivable: hga makes the head of gs nonempty and the chain hgs makes every later entry nonempty, so the empty list is not in gs)
theorem x26_159 : drop% _private.Mathlib.Data.List.SplitBy.«0».List.isChain_getLast_head_splitByLoop 6 := by
  intro α r l a g gs hgs hga
  refine (priv% _private.Mathlib.Data.List.SplitBy.«0».List.isChain_getLast_head_splitByLoop) l ?_ hgs hga
  cases gs with
  | nil => simp
  | cons x rest =>
    obtain ⟨hx, -⟩ := hga x (by simp)
    exact chain_ne (fun _ _ h => h.1) x rest hgs hx
-- `_private.Mathlib.Data.List.SplitBy.0.List.isChain_getLast_head_splitByLoop` idx 7: necessary (r = (==), l = [], a = 1, g = [], gs = [[0],[0]])
theorem x26_160 : ¬ drop0% _private.Mathlib.Data.List.SplitBy.«0».List.isChain_getLast_head_splitByLoop 7 := fun h =>
  absurd (@h ℕ (fun x y => x == y) [] 1 [] [[0], [0]] (by simp) (by simp)) (by simp [List.splitBy.loop])
-- `List.splitBy_flatten` idx 4: necessary (r = false, l = [[0,1]])
theorem x26_161 : ¬ drop0% List.splitBy_flatten 4 := fun h =>
  absurd (@h ℕ (fun _ _ => false) [[0, 1]] (by simp) (by simp)) (by decide)
-- `List.Sublist.sym` idx 4: necessary (n = 1, xs = [0], ys = [])
theorem x26_162 : ¬ drop0% List.Sublist.sym 4 := fun h =>
  absurd (@h ℕ 1 [0] []) (by simp [List.sym])
-- `List.mem_of_mem_of_mem_sym` idx 5: necessary (n = 0, xs = [], z = nil, a = 0)
theorem x26_163 : ¬ drop0% List.mem_of_mem_of_mem_sym 5 := fun h =>
  absurd (@h ℕ 0 [] 0 Sym.nil (by simp [List.sym])) (by simp)
-- `List.mem_of_mem_of_mem_sym` idx 6: necessary (n = 1, xs = [], z = {0}, a = 0)
theorem x26_164 : ¬ drop0% List.mem_of_mem_of_mem_sym 6 := fun h =>
  absurd (@h ℕ 1 [] 0 (0 ::ₛ Sym.nil) (by simp)) (by simp)
-- `List.first_mem_of_cons_mem_sym` idx 5: necessary (xs = [], n = 0, a = 0)
theorem x26_165 : ¬ drop0% List.first_mem_of_cons_mem_sym 5 := fun h =>
  absurd (@h ℕ [] 0 0 Sym.nil) (by simp)
-- `List.Nodup.sym` idx 3: necessary (n = 1, xs = [0,0])
theorem x26_166 : ¬ drop0% List.Nodup.sym 3 := fun h =>
  absurd (@h ℕ 1 [0, 0]) (by simp [List.sym])
-- `List.Triplewise.imp` idx 4: necessary (p = True, q = False, l = [0,1,2])
theorem x26_167 : ¬ drop0% List.Triplewise.imp 4 := fun h =>
  tw_false (@h ℕ [0, 1, 2] (fun _ _ _ => True) (fun _ _ _ => False) tw_true)
-- `List.Triplewise.imp` idx 5: necessary (p = q = False, l = [0,1,2])
theorem x26_168 : ¬ drop0% List.Triplewise.imp 5 := fun h =>
  tw_false (@h ℕ [0, 1, 2] (fun _ _ _ => False) (fun _ _ _ => False) (fun h => h))
-- `List.Triplewise.of_map` idx 6: necessary (f = id, p' = True, p = False)
theorem x26_169 : ¬ drop0% List.Triplewise.of_map 6 := fun h =>
  tw_false (@h ℕ ℕ [0, 1, 2] (fun _ _ _ => False) id (fun _ _ _ => True) (by simpa using tw_true))
-- `List.Triplewise.of_map` idx 7: necessary (f = id, p' = p = False)
theorem x26_170 : ¬ drop0% List.Triplewise.of_map 7 := fun h =>
  tw_false (@h ℕ ℕ [0, 1, 2] (fun _ _ _ => False) id (fun _ _ _ => False) (fun h => h))
-- `List.Triplewise.map` idx 6: necessary (f = id, p = True, p' = False)
theorem x26_171 : ¬ drop0% List.Triplewise.map 6 := fun h =>
  tw_false (by simpa using @h ℕ ℕ [0, 1, 2] (fun _ _ _ => True) id (fun _ _ _ => False) tw_true)
-- `List.Triplewise.map` idx 7: necessary (f = id, p = p' = False)
theorem x26_172 : ¬ drop0% List.Triplewise.map 7 := fun h =>
  tw_false (by simpa using @h ℕ ℕ [0, 1, 2] (fun _ _ _ => False) id (fun _ _ _ => False) (fun h => h))
-- `_private.Mathlib.Data.List.Shortlex.0.Acc.shortlex` idx 4: necessary (full relation on Unit, a = (), b = []: [()] lies below itself)
theorem x26_173 : ¬ drop0% _private.Mathlib.Data.List.Shortlex.«0».Acc.shortlex 4 := fun h =>
  acc_self (List.shortlex_def.mpr (Or.inr ⟨rfl, List.Lex.rel trivial⟩))
    (@h Unit (fun _ _ => True) () [] (acc_nil _) (fun s hs => by simp at hs; subst hs; exact acc_nil _))
-- `_private.Mathlib.Data.List.Shortlex.0.Acc.shortlex` idx 6: necessary (Bool, r = both false, a = true, b = [true]: the shorter list [false] is not accessible)
theorem x26_174 : ¬ drop0% _private.Mathlib.Data.List.Shortlex.«0».Acc.shortlex 6 := fun h =>
  nacc (@h Bool (fun x y => x = false ∧ y = false) true [true] accB accT)
-- `Matrix.instFinite` idx 2: necessary (m = ℕ, n = Unit, α = Bool)
theorem x26_175 : ¬ drop0% Matrix.instFinite 2 := fun h =>
  @not_finite (ℕ → Unit → Bool) inferInstance (@h Unit ℕ _ Bool _)
-- `Matrix.instFinite` idx 3: necessary (m = Unit, n = ℕ, α = Bool)
theorem x26_176 : ¬ drop0% Matrix.instFinite 3 := fun h =>
  @not_finite (Unit → ℕ → Bool) inferInstance (@h ℕ Unit _ Bool _)
-- `Matrix.instFinite` idx 5: necessary (m = n = Unit, α = ℕ)
theorem x26_177 : ¬ drop0% Matrix.instFinite 5 := fun h =>
  @not_finite (Unit → Unit → ℕ) inferInstance (@h Unit Unit _ _ ℕ)
-- `Matrix.instIsStablyFiniteRingOfFinite` idx 2: necessary (AddMonoid.End (ℕ → ℤ) with the shift operators is not Dedekind-finite)
theorem x26_178 : ¬ drop0% Matrix.instIsStablyFiniteRingOfFinite 2 := fun h =>
  E_not_df (by haveI := @h E _; infer_instance)
-- `instIsStablyFiniteRingMulOpposite` idx 3: necessary (the opposite of the shift-operator semiring is not Dedekind-finite)
theorem x26_179 : ¬ drop0% instIsStablyFiniteRingMulOpposite 3 := fun h => by
  haveI := @h E _ _
  have : IsDedekindFiniteMonoid Eᵐᵒᵖ := inferInstance
  apply shRL
  have e : MulOpposite.op shR * MulOpposite.op shL = (1 : Eᵐᵒᵖ) := by
    rw [← MulOpposite.op_mul, shLR, MulOpposite.op_one]
  have := congrArg MulOpposite.unop (this.mul_eq_one_symm e)
  simpa using this
-- `Matrix.zero_le_one_elem` idx 6: necessary (α = ℤᵒᵈ, n = Unit)
theorem x26_180 : ¬ drop0% Matrix.zero_le_one_elem 6 := fun h => by
  have := @h Unit ℤᵒᵈ _ _ _ _ () ()
  simp only [Matrix.one_apply_eq] at this
  exact absurd this (by decide)
-- `Matrix.zero_le_one_row` idx 6: necessary (α = ℤᵒᵈ, n = Unit)
theorem x26_181 : ¬ drop0% Matrix.zero_le_one_row 6 := fun h => by
  have := (@h Unit ℤᵒᵈ _ _ _ _ ()) ()
  simp only [Pi.zero_apply, Matrix.one_apply_eq] at this
  exact absurd this (by decide)
-- `Matrix.scalar_inj` idx 5: necessary (n = Empty, r = 0, s = 1 in ℕ)
theorem x26_182 : ¬ drop0% Matrix.scalar_inj 5 := fun h =>
  absurd ((@h Empty ℕ _ _ _ 0 1).mp (Matrix.ext fun i => i.elim)) (by decide)
-- `Matrix.scalar_comm` idx 9: necessary (α = 2x2 integer matrices, m = n = Unit, r = MA, M = MB)
theorem x26_183 : ¬ drop0% Matrix.scalar_comm 9 := fun h => by
  have := congrFun (congrFun (@h Unit Unit (Matrix (Fin 2) (Fin 2) ℤ) _ _ _ _ _ MA (Matrix.of fun _ _ => MB)) ()) ()
  simp [Matrix.mul_apply] at this
  exact MAB_ne this
-- `Matrix.scalar_commute` idx 6: necessary (α = 2x2 integer matrices, n = Unit, r = MA, M = MB)
theorem x26_184 : ¬ drop0% Matrix.scalar_commute 6 := fun h => by
  have := congrFun (congrFun (@h Unit (Matrix (Fin 2) (Fin 2) ℤ) _ _ _ MA (Matrix.of fun _ _ => MB)).eq ()) ()
  simp [Matrix.mul_apply] at this
  exact MAB_ne this
-- `Matrix.map_algebraMap` idx 13: necessary (n = Fin 2, R = α = β = ℕ, r = 1, f = const 1: off-diagonal entry 1 ≠ 0)
theorem x26_185 : ¬ drop0% Matrix.map_algebraMap 13 := fun h => by
  have := congrFun (congrFun (@h (Fin 2) ℕ ℕ ℕ _ _ _ _ _ _ _ 1 (fun _ => 1) (by simp)) 0) 1
  simp [Matrix.algebraMap_matrix_apply] at this
-- `LinearMap.mapMatrix_comp` idx 14: necessary (dependent; R = S = T = ℤ × ℤ, σᵣₛ = σₛₜ = id, σᵣₜ = swap)
theorem x26_186 : ¬ indep0% LinearMap.mapMatrix_comp 14 := fun h =>
  swZ_ne ((@h Unit Unit (ℤ × ℤ) (ℤ × ℤ) (ℤ × ℤ) (ℤ × ℤ) (ℤ × ℤ) (ℤ × ℤ) _ _ _ (RingHom.id _) (RingHom.id _) swZ
    _ _ _ _ _ _ 0 0).comp_eq.symm.trans (RingHom.id_comp _))
-- `LinearMap.mapMatrix_smul` idx 16: necessary (dependent; S = A = β = 2x2 integer matrices acting by left multiplication)
theorem x26_187 : ¬ indep0% LinearMap.mapMatrix_smul 16 := fun h => by
  have := (@h Unit Unit (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ)
    (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ) _ _ (RingHom.id _) _ _ _ _ _ _ 1 0).smul_comm MA MB 1
  simp only [smul_eq_mul, mul_one] at this
  exact MAB_ne this
-- `LinearMap.mapMatrixLinear_apply` idx 16: necessary (dependent; S = A = β = 2x2 integer matrices acting by left multiplication)
theorem x26_188 : ¬ indep0% LinearMap.mapMatrixLinear_apply 16 := fun h => by
  have := (@h Unit Unit (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ)
    (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ) _ _ (RingHom.id _) _ _ _ _ _ _ 0).smul_comm MA MB 1
  simp only [smul_eq_mul, mul_one] at this
  exact MAB_ne this
-- `LinearEquiv.mapMatrix_apply` idx 14: removable (dependent, derivable: RingHomInvPair is symmetric and the reverse pair is among the other hypotheses)
theorem x26_189 : indep% LinearEquiv.mapMatrix_apply 14 := by
  intros; exact RingHomInvPair.symm _ _
-- `LinearEquiv.mapMatrix_apply` idx 15: removable (dependent, derivable: RingHomInvPair is symmetric and the reverse pair is among the other hypotheses)
theorem x26_190 : indep% LinearEquiv.mapMatrix_apply 15 := by
  intros; exact RingHomInvPair.symm _ _
-- `LinearEquiv.mapMatrix_symm` idx 14: removable (dependent, derivable: RingHomInvPair is symmetric and the reverse pair is among the other hypotheses)
theorem x26_191 : indep% LinearEquiv.mapMatrix_symm 14 := by
  intros; exact RingHomInvPair.symm _ _
-- `LinearEquiv.mapMatrix_symm` idx 15: removable (dependent, derivable: RingHomInvPair is symmetric and the reverse pair is among the other hypotheses)
theorem x26_192 : indep% LinearEquiv.mapMatrix_symm 15 := by
  intros; exact RingHomInvPair.symm _ _
-- `LinearEquiv.mapMatrix_trans` idx 25: removable (dependent, derivable: RingHomInvPair is symmetric and the reverse pair is among the other hypotheses)
theorem x26_193 : indep% LinearEquiv.mapMatrix_trans 25 := by
  intros; exact RingHomInvPair.symm _ _
-- `LinearEquiv.mapMatrix_trans` idx 26: removable (dependent, derivable: RingHomInvPair is symmetric and the reverse pair is among the other hypotheses)
theorem x26_194 : indep% LinearEquiv.mapMatrix_trans 26 := by
  intros; exact RingHomInvPair.symm _ _
-- `LinearEquiv.mapMatrix_trans` idx 27: removable (dependent, derivable: RingHomInvPair is symmetric and the reverse pair is among the other hypotheses)
theorem x26_195 : indep% LinearEquiv.mapMatrix_trans 27 := by
  intros; exact RingHomInvPair.symm _ _
-- `LinearEquiv.mapMatrix_trans` idx 28: removable (dependent, derivable: RingHomInvPair is symmetric and the reverse pair is among the other hypotheses)
theorem x26_196 : indep% LinearEquiv.mapMatrix_trans 28 := by
  intros; exact RingHomInvPair.symm _ _
-- `LinearEquiv.mapMatrix_trans` idx 29: removable (dependent, derivable: RingHomInvPair is symmetric and the reverse pair is among the other hypotheses)
theorem x26_197 : indep% LinearEquiv.mapMatrix_trans 29 := by
  intros; exact RingHomInvPair.symm _ _
-- `LinearEquiv.mapMatrix_trans` idx 30: removable (dependent, derivable: RingHomInvPair is symmetric and the reverse pair is among the other hypotheses)
theorem x26_198 : indep% LinearEquiv.mapMatrix_trans 30 := by
  intros; exact RingHomInvPair.symm _ _
-- `LinearEquiv.mapMatrix_toLinearMap` idx 14: removable (dependent, derivable: RingHomInvPair is symmetric and the reverse pair is among the other hypotheses)
theorem x26_199 : indep% LinearEquiv.mapMatrix_toLinearMap 14 := by
  intros; exact RingHomInvPair.symm _ _
-- `LinearEquiv.mapMatrix_toLinearMap` idx 15: removable (dependent, derivable: RingHomInvPair is symmetric and the reverse pair is among the other hypotheses)
theorem x26_200 : indep% LinearEquiv.mapMatrix_toLinearMap 15 := by
  intros; exact RingHomInvPair.symm _ _
-- `LinearEquiv.entryLinearMap_comp_mapMatrix` idx 14: removable (dependent, derivable: RingHomInvPair is symmetric and the reverse pair is among the other hypotheses)
theorem x26_201 : indep% LinearEquiv.entryLinearMap_comp_mapMatrix 14 := by
  intros; exact RingHomInvPair.symm _ _
-- `LinearEquiv.entryLinearMap_comp_mapMatrix` idx 15: removable (dependent, derivable: RingHomInvPair is symmetric and the reverse pair is among the other hypotheses)
theorem x26_202 : indep% LinearEquiv.entryLinearMap_comp_mapMatrix 15 := by
  intros; exact RingHomInvPair.symm _ _
-- `LinearEquiv.mapMatrix_trans` idx 20: removable (dependent, derivable from the reverse composition triple and the inverse pairs)
theorem x26_203 : indep% LinearEquiv.mapMatrix_trans 20 := by
  intro m n R S T α β γ _ _ _ _ _ _ _ _ _ σᵣₛ σₛₜ σᵣₜ σₛᵣ σₜₛ σₜᵣ _ _ _ _ _ _ _ f g
  refine ⟨RingHom.ext fun x => ?_⟩
  rw [RingHom.comp_apply]
  have h1 : σₜᵣ (σₛₜ (σᵣₛ x)) = x := by
    rw [← RingHomCompTriple.comp_apply (σ₁₂ := σₜₛ) (σ₂₃ := σₛᵣ), RingHomInvPair.comp_apply_eq (σ := σₛₜ),
      RingHomInvPair.comp_apply_eq (σ := σᵣₛ)]
  calc σₛₜ (σᵣₛ x) = σᵣₜ (σₜᵣ (σₛₜ (σᵣₛ x))) := (RingHomInvPair.comp_apply_eq₂ (σ := σᵣₜ) (σ' := σₜᵣ)).symm
    _ = σᵣₜ x := by rw [h1]
-- `LinearEquiv.mapMatrix_trans` idx 24: removable (dependent, derivable from the forward composition triple and the inverse pairs)
theorem x26_204 : indep% LinearEquiv.mapMatrix_trans 24 := by
  intro m n R S T α β γ _ _ _ _ _ _ _ _ _ σᵣₛ σₛₜ σᵣₜ _ σₛᵣ σₜₛ σₜᵣ _ _ _ _ _ _ f g
  refine ⟨RingHom.ext fun y => ?_⟩
  rw [RingHom.comp_apply]
  have h1 : σᵣₜ (σₛᵣ (σₜₛ y)) = y := by
    rw [← RingHomCompTriple.comp_apply (σ₁₂ := σᵣₛ) (σ₂₃ := σₛₜ), RingHomInvPair.comp_apply_eq₂ (σ := σᵣₛ),
      RingHomInvPair.comp_apply_eq₂ (σ := σₛₜ)]
  calc σₛᵣ (σₜₛ y) = σₜᵣ (σᵣₜ (σₛᵣ (σₜₛ y))) := (RingHomInvPair.comp_apply_eq (σ := σᵣₜ) (σ' := σₜᵣ)).symm
    _ = σₜᵣ y := by rw [h1]

-- `List.mergeSort_eq_insertionSort` idx 5: removable (by induction: List.mergeSort_cons inserts the head after the elements it is not related to, exactly like orderedInsert; both sorts are stable, so antisymmetry is not needed)
theorem x26_205 : drop% List.mergeSort_eq_insertionSort 5 := by
  intro α r _ _ _ l
  have trans : ∀ a b c : α, decide (r a b) = true → decide (r b c) = true → decide (r a c) = true := by
    intro a b c h1 h2; simp only [decide_eq_true_eq] at *; exact _root_.trans h1 h2
  have total : ∀ a b : α, (decide (r a b) || decide (r b a)) = true := by
    intro a b; simpa using Std.Total.total a b
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨l₁, l₂, h1, h2, h3⟩ := List.mergeSort_cons trans total a l
    have hp := List.pairwise_mergeSort trans total (a :: l)
    rw [h1] at hp ⊢
    rw [List.insertionSort_cons, ← ih, h2, oi_append r a l₁ l₂ (fun b hb => by simpa using h3 b hb)]
    congr 1
    have hl₂ : ∀ b ∈ l₂, r a b := by
      intro b hb
      have := (List.pairwise_append.mp hp).2.1
      simpa using (List.pairwise_cons.mp this).1 b hb
    cases l₂ with
    | nil => simp
    | cons c l₂ => simp [List.orderedInsert, hl₂ c (by simp)]
-- `List.pair_sublist_insertionSort'` idx 4: removable (without totality insertionSort still keeps the invariant that v never precedes u when r u v and u ≠ v; with r a b this puts some a before some b, and the count handles a = b)
theorem x26_206 : drop% List.pair_sublist_insertionSort' 4 := by
  intro α r _ _ _ a b l hab h
  classical
  have hp := List.perm_insertionSort r l
  have hinv := is_inv r l
  by_cases hab' : a = b
  · subst hab'
    have h2 : 2 ≤ (l.insertionSort r).count a := by
      rw [hp.count_eq]
      simpa using h.count_le a
    simpa using (List.replicate_sublist_iff (n := 2)).mpr h2
  · have ha : a ∈ l.insertionSort r := hp.mem_iff.mpr (h.subset (by simp))
    have hb : b ∈ l.insertionSort r := hp.mem_iff.mpr (h.subset (by simp))
    obtain ⟨p, q, hpq⟩ := List.append_of_mem ha
    rw [hpq] at hb hinv ⊢
    rcases List.mem_append.mp hb with hb | hb
    · exact absurd ((List.pairwise_append.mp hinv).2.2 b hb a (by simp) hab) hab'
    · rcases List.mem_cons.mp hb with hb | hb
      · exact absurd hb.symm hab'
      · exact ((List.singleton_sublist.mpr hb).cons_cons a).trans (List.sublist_append_right p _)
-- `List.sublist_insertionSort'` idx 4: removable (the library induction goes through with the weak insertion-sort invariant in place of sortedness, since c pairwise r makes every element comparable with the inserted one)
theorem x26_207 : drop% List.sublist_insertionSort' 4 := by
  intro α r _ _ _ l c hs hc
  classical
  obtain ⟨d, hc, hd⟩ := hc
  induction l generalizing c d with
  | nil => rw [List.sublist_nil] at hd; subst hd; rw [List.nil_perm] at hc; subst hc; simp
  | cons a l' ih =>
    cases hd with
    | cons _ h => exact (ih hs _ hc h).trans (List.sublist_orderedInsert ..)
    | cons_cons _ h =>
      specialize ih (hs.erase _) _ (List.erase_cons_head a _ ▸ hc.erase a) h
      have hm := hc.mem_iff.mp (List.mem_cons_self ..)
      have he := List.orderedInsert_erase _ _ hm hs
      have ht : c.Pairwise (fun u v => r u v ∨ r v u) := hs.imp Or.inl
      have ht' := ((List.perm_cons_erase hm).pairwise_iff Or.symm).mp ht
      have key := oi_sub r a ih (is_inv r l') (fun y hy => (List.pairwise_cons.mp ht').1 y hy)
      rw [he] at key
      rw [List.insertionSort_cons]; exact key
