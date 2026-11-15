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

namespace W2c7
open Matrix

/-- non-commuting 2x2 matrices over ℕ -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℕ
def eA : M2 := !![1,0;0,0]
def eB : M2 := !![0,1;0,0]
theorem eAB : eA * eB ≠ eB * eA := by decide

/-- ¬ SMulCommClass M2 M2 M2 (left multiplication) -/
theorem nSC : ¬ SMulCommClass M2 M2 M2 := fun h => eAB (by
  have := h.smul_comm eA eB 1; simpa [smul_eq_mul] using this)

/-- a bare function type: FunLike with arbitrary (non-hom) maps -/
structure FW (α β : Type) where
  toFun : α → β

instance (α β : Type) : FunLike (FW α β) α β where
  coe := FW.toFun
  coe_injective := by intro f g h; cases f; cases g; cases h; rfl

/-- ℕ with the discrete order (≤ is =) -/
def DN := ℕ
instance : CommSemiring DN := inferInstanceAs (CommSemiring ℕ)
instance : PartialOrder DN where
  le a b := a = b
  le_refl a := rfl
  le_trans a b c h1 h2 := h1.trans h2
  le_antisymm a b h _ := h

/-- a non-Dedekind-finite semiring: shifts on ℕ → ℕ -/
abbrev E := Module.End ℕ (ℕ → ℕ)
def sa : E := { toFun := fun f n => f (n+1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
def sb : E where
  toFun f n := if n = 0 then 0 else f (n-1)
  map_add' f g := by funext n; by_cases h : n = 0 <;> simp [h]
  map_smul' c f := by funext n; by_cases h : n = 0 <;> simp [h]
theorem hab : sa * sb = 1 := LinearMap.ext fun f => funext fun n => by simp [sa, sb]
theorem hba : sb * sa ≠ 1 := fun h => by
  have := congrFun (LinearMap.congr_fun h (fun _ => 1)) 0; simp [sb, sa] at this
theorem E_nDF : ¬ IsDedekindFiniteMonoid E := fun h => hba (h.mul_eq_one_symm hab)
theorem E_nSF : ¬ IsStablyFiniteRing E := fun h => E_nDF inferInstance
def mA : Matrix Unit Unit E := Matrix.of fun _ _ => sa
def mB : Matrix Unit Unit E := Matrix.of fun _ _ => sb
theorem mAB : mA * mB = 1 := by ext i j; simp [Matrix.mul_apply, mA, mB, hab]
theorem mBA : mB * mA ≠ 1 := fun h => hba (by have := congrFun (congrFun h ()) (); simpa [Matrix.mul_apply, mA, mB] using this)
theorem mU_nDF : ¬ IsDedekindFiniteMonoid (Matrix Unit Unit E) := fun h => mBA (h.mul_eq_one_symm mAB)
def fA : Matrix (Fin 1) (Fin 1) E := Matrix.of fun _ _ => sa
def fB : Matrix (Fin 1) (Fin 1) E := Matrix.of fun _ _ => sb
theorem fAB : fA * fB = 1 := by ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply, fA, fB, hab]
theorem fBA : fB * fA ≠ 1 := fun h => hba (by have := congrFun (congrFun h 0) 0; simpa [Matrix.mul_apply, fA, fB] using this)

/-- the trivial semiring is stably finite -/
theorem pSF : IsStablyFiniteRing PUnit.{1} := ⟨fun n => ⟨fun _ => Subsingleton.elim _ _⟩⟩

/-- E → PUnit ring hom -/
def toP : E →+* PUnit := { toFun := fun _ => (), map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }

/-- commutative, idempotent, non-associative op on ℕ -/
def cop (a b : ℕ) : ℕ := if a = b then a else a + b + 1
instance : Std.Commutative cop := ⟨fun a b => by unfold cop; split_ifs <;> omega⟩
instance : Std.IdempotentOp cop := ⟨fun a => by simp [cop]⟩
theorem cop_nA : ¬ Std.Associative cop := fun h => absurd (h.assoc 0 1 1) (by decide)
/-- left projection: associative, not commutative -/
def lp (a _ : ℕ) : ℕ := a
instance : Std.Associative lp := ⟨fun _ _ _ => rfl⟩
theorem lp_nC : ¬ Std.Commutative lp := fun h => absurd (h.comm 0 1) (by decide)

/-- ℕ with constant multiplication 1 -/
def N1 := ℕ
instance : AddCommMonoid N1 := inferInstanceAs (AddCommMonoid ℕ)
instance : Mul N1 := ⟨fun _ _ => (1 : ℕ)⟩
instance : DecidableEq N1 := inferInstanceAs (DecidableEq ℕ)

end W2c7
open W2c7

namespace W2c7

/-- StateM ℕ is not a commutative applicative -/
theorem nCA (c : CommApplicative (StateM ℕ)) : False := by
  have := congrArg (fun x => (x.run 0).1) (c.commutative_prod (get : StateM ℕ ℕ) (set 1 : StateM ℕ PUnit))
  revert this; decide

/-- well-founded relations are irreflexive -/
theorem irr {α : Type} {r : α → α → Prop} (wf : WellFounded r) (a : α) : ¬ r a a := by
  have := wf.apply a
  induction this with | intro x _ ih => exact fun h => ih x h h

/-- a descending sequence gives non-well-foundedness / non-accessibility -/
theorem notWF {β : Type} {r : β → β → Prop} (f : ℕ → β) (h : ∀ n, r (f (n+1)) (f n)) : ¬ WellFounded r := by
  intro wf
  obtain ⟨a, ⟨n, rfl⟩, ha⟩ := wf.has_min (Set.range f) ⟨f 0, 0, rfl⟩
  exact ha (f (n+1)) ⟨n+1, rfl⟩ (h n)
theorem notAcc {β : Type} {r : β → β → Prop} (f : ℕ → β) (h : ∀ n, r (f (n+1)) (f n)) : ¬ Acc r (f 0) := by
  suffices ∀ x, Acc r x → ∀ n, x ≠ f n from fun hA => this _ hA 0 rfl
  intro x hA; induction hA with | intro x _ ih => intro n hx; subst hx; exact ih _ (h n) (n+1) rfl

theorem dm01 : Multiset.IsDershowitzMannaLT ({0} : Multiset ℕ) {1} :=
  ⟨0, {0}, {1}, by simp, by simp, by simp, by simp⟩
theorem dm_irr (M : Multiset ℕ) : ¬ M.IsDershowitzMannaLT M := irr Multiset.wellFounded_isDershowitzMannaLT M

/-- descending OneStep / Dershowitz–Manna chain {-n} in Multiset ℤ -/
def zc (n : ℕ) : Multiset ℤ := {-(n : ℤ)}
theorem zc_os (n : ℕ) : (priv% _private.Mathlib.Data.Multiset.DershowitzManna.«0».Multiset.OneStep) (zc (n+1)) (zc n) :=
  ⟨0, {-((n+1 : ℕ) : ℤ)}, -(n : ℤ), by simp [zc], by simp [zc], by simp⟩
theorem zc_dm (n : ℕ) : Multiset.IsDershowitzMannaLT (zc (n+1)) (zc n) :=
  ⟨0, {-((n+1 : ℕ) : ℤ)}, {-(n : ℤ)}, by simp, by simp [zc], by simp [zc], by simp⟩

/-- Id is a commutative applicative -/
def idCA : CommApplicative Id := { (inferInstance : LawfulApplicative Id) with commutative_prod := fun _ _ => rfl }

end W2c7

namespace W2c7

/-- finitely supported functions ℕ → ℤ (copied from W2c0) -/
noncomputable def FS : AddSubgroup (ℕ → ℤ) := (Finsupp.coeFnAddHom : (ℕ →₀ ℤ) →+ ℕ → ℤ).range
theorem single_mem (i : ℕ) (x : ℤ) : Pi.single i x ∈ FS :=
  ⟨Finsupp.single i x, Finsupp.single_eq_pi_single i x⟩
theorem one_notMem : (fun _ => (1 : ℤ)) ∉ FS := by
  rintro ⟨g, hg⟩
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset g.support
  have h1 : g n = 1 := congrFun hg n
  rw [Finsupp.notMem_support_iff] at hn
  omega

abbrev Q := (ℕ → ℤ) ⧸ FS
def colH : Matrix ℕ Unit ℤ →+ (ℕ → ℤ) where
  toFun M i := M i ()
  map_zero' := rfl
  map_add' _ _ := rfl
def rowH : Matrix Unit ℕ ℤ →+ (ℕ → ℤ) where
  toFun M j := M () j
  map_zero' := rfl
  map_add' _ _ := rfl
/-- column (row) quotient maps: kill every single-entry matrix but not the all-ones matrix -/
noncomputable def φc : Matrix ℕ Unit ℤ →+ Q := (QuotientAddGroup.mk' FS).comp colH
noncomputable def φr : Matrix Unit ℕ ℤ →+ Q := (QuotientAddGroup.mk' FS).comp rowH
theorem colH_single (i : ℕ) (j : Unit) (x : ℤ) : colH (Matrix.single i j x) = Pi.single i x := by
  funext k; show Matrix.single i j x k () = _; by_cases hk : k = i
  · subst hk; simp [Matrix.single]
  · simp [Matrix.single, Pi.single_apply, hk, Ne.symm hk]
theorem φc_single (i : ℕ) (j : Unit) (x : ℤ) : φc (Matrix.single i j x) = 0 := by
  show QuotientAddGroup.mk' FS (colH (Matrix.single i j x)) = 0
  rw [colH_single]; exact (QuotientAddGroup.eq_zero_iff _).2 (single_mem i x)
theorem rowH_single (i : Unit) (j : ℕ) (x : ℤ) : rowH (Matrix.single i j x) = Pi.single j x := by
  funext k; show Matrix.single i j x () k = _; by_cases hk : k = j
  · subst hk; simp [Matrix.single]
  · simp [Matrix.single, Pi.single_apply, hk, Ne.symm hk]
theorem φr_single (i : Unit) (j : ℕ) (x : ℤ) : φr (Matrix.single i j x) = 0 := by
  show QuotientAddGroup.mk' FS (rowH (Matrix.single i j x)) = 0
  rw [rowH_single]; exact (QuotientAddGroup.eq_zero_iff _).2 (single_mem j x)
theorem φc_ne : φc ≠ 0 := fun e => by
  have := DFunLike.congr_fun e (Matrix.of fun _ _ => 1)
  change QuotientAddGroup.mk' FS (fun _ => (1:ℤ)) = 0 at this
  exact one_notMem ((QuotientAddGroup.eq_zero_iff _).1 this)
theorem φr_ne : φr ≠ 0 := fun e => by
  have := DFunLike.congr_fun e (Matrix.of fun _ _ => 1)
  change QuotientAddGroup.mk' FS (fun _ => (1:ℤ)) = 0 at this
  exact one_notMem ((QuotientAddGroup.eq_zero_iff _).1 this)
theorem φc_comp (i : ℕ) (j : Unit) : φc.comp (Matrix.singleAddMonoidHom i j) = 0 :=
  AddMonoidHom.ext fun x => φc_single i j x
theorem φr_comp (i : Unit) (j : ℕ) : φr.comp (Matrix.singleAddMonoidHom i j) = 0 :=
  AddMonoidHom.ext fun x => φr_single i j x
theorem φc_lcomp (i : ℕ) (j : Unit) : φc.toIntLinearMap ∘ₗ Matrix.singleLinearMap ℤ i j = 0 :=
  LinearMap.ext fun x => φc_single i j x
theorem φr_lcomp (i : Unit) (j : ℕ) : φr.toIntLinearMap ∘ₗ Matrix.singleLinearMap ℤ i j = 0 :=
  LinearMap.ext fun x => φr_single i j x
theorem φc_lne : φc.toIntLinearMap ≠ 0 := fun e => φc_ne (AddMonoidHom.ext fun x => LinearMap.congr_fun e x)
theorem φr_lne : φr.toIntLinearMap ≠ 0 := fun e => φr_ne (AddMonoidHom.ext fun x => LinearMap.congr_fun e x)

/-- ℤ ⊕ Unit (sum order): inr () is accessible, but {inr (), inl (-n)} descends in OneStep -/
abbrev ZU := ℤ ⊕ Unit
theorem accInr : Acc (· < ·) (Sum.inr () : ZU) := Acc.intro _ fun y hy => by cases y <;> simp at hy
def zu (n : ℕ) : Multiset ZU := Sum.inr () ::ₘ {Sum.inl (-(n : ℤ))}
theorem zu_os (n : ℕ) : (priv% _private.Mathlib.Data.Multiset.DershowitzManna.«0».Multiset.OneStep) (zu (n+1)) (zu n) :=
  ⟨{Sum.inr ()}, {Sum.inl (-((n+1 : ℕ) : ℤ))}, Sum.inl (-(n : ℤ)), by simp [zu], by simp [zu], by simp⟩

/-- pointwise ZMod 2-valued functions form a stably finite ring -/
theorem piSF (ι : Type) : IsStablyFiniteRing (ι → ZMod 2) := ⟨fun n => by
  let f : Matrix (Fin n) (Fin n) (ι → ZMod 2) →* (ι → Matrix (Fin n) (Fin n) (ZMod 2)) :=
    { toFun := fun M i => M.map (fun x => x i)
      map_one' := by funext i; ext a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
      map_mul' := fun M N => by funext i; ext a b; simp [Matrix.mul_apply, Finset.sum_apply] }
  refine IsDedekindFiniteMonoid.of_injective f (fun M N hMN => ?_)
  ext a b i; exact congrFun (congrFun (congrFun hMN i) a) b⟩

def cCA : CommApplicative (Functor.Const PUnit.{1}) :=
  { (inferInstance : LawfulApplicative (Functor.Const PUnit.{1})) with commutative_prod := fun _ _ => rfl }

end W2c7

-- `Matrix.map_single` idx 13: necessary (f = const 1 on ℕ, Fin 2 indices, entry (0,1))
theorem c7_1 : ¬ drop0% Matrix.map_single 13 := fun h => by
  have := congrFun (congrFun (@h (Fin 2) (Fin 2) ℕ _ _ _ 0 0 0 ℕ _ (FW ℕ ℕ) _ ⟨fun _ => 1⟩) 0) 1
  revert this; decide

-- `Matrix.single_mem_matrix` idx 7: necessary (S = {1}, a = 1, Fin 2 indices)
theorem c7_2 : ¬ drop0% Matrix.single_mem_matrix 7 := fun h => by
  have := Set.mem_matrix.1 ((@h (Fin 2) (Fin 2) ℕ _ _ _ {1} 0 0 1).2 rfl) 0 1
  simp [Matrix.single] at this

-- `Matrix.induction_on'` idx 6: necessary (m = ℕ, P = finitely many nonzero rows, all-ones matrix)
theorem c7_3 : ¬ drop0% Matrix.induction_on' 6 := fun h => by
  have := @h ℕ Unit ℕ _ _ _ _ (fun M => {i | M i () ≠ 0}.Finite) (fun _ _ => 1) (by simp)
    (fun p q hp hq => (hp.union hq).subset (fun i hi => by
      by_contra hc; simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc hi; simp [hc.1, hc.2] at hi))
    (fun i j x => (Set.finite_singleton i).subset (fun k hk => by
      by_contra hc; simp only [Set.mem_singleton_iff, Set.mem_setOf_eq] at hc hk; simp [Matrix.single, Ne.symm hc] at hk))
  simp at this; exact Set.infinite_univ this

-- `Matrix.induction_on'` idx 7: necessary (n = ℕ, P = finitely many nonzero columns, all-ones matrix)
theorem c7_4 : ¬ drop0% Matrix.induction_on' 7 := fun h => by
  have := @h Unit ℕ ℕ _ _ _ _ (fun M => {j | M () j ≠ 0}.Finite) (fun _ _ => 1) (by simp)
    (fun p q hp hq => (hp.union hq).subset (fun i hi => by
      by_contra hc; simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc hi; simp [hc.1, hc.2] at hi))
    (fun i j x => (Set.finite_singleton j).subset (fun k hk => by
      by_contra hc; simp only [Set.mem_singleton_iff, Set.mem_setOf_eq] at hc hk; simp [Matrix.single, Ne.symm hc] at hk))
  simp at this; exact Set.infinite_univ this

-- `Matrix.induction_on'` idx 10: necessary (m = Empty, P = False)
theorem c7_5 : ¬ drop0% Matrix.induction_on' 10 := fun h =>
  @h Empty Unit ℕ _ _ _ _ _ (fun _ => False) (fun e => e.elim) (fun _ _ hp _ => hp) (fun i => i.elim)

-- `Matrix.induction_on'` idx 11: necessary (P = some entry of column 0 is zero, Fin 2 × Unit, all-ones)
theorem c7_6 : ¬ drop0% Matrix.induction_on' 11 := fun h => by
  have := @h (Fin 2) Unit ℕ _ _ _ _ _ (fun M => M 0 () = 0 ∨ M 1 () = 0) (fun _ _ => 1) (by simp)
    (fun i j x => by fin_cases i <;> simp [Matrix.single])
  simp at this

-- `Matrix.induction_on'` idx 12: necessary (P = (· = 0), all-ones 1×1 matrix)
theorem c7_7 : ¬ drop0% Matrix.induction_on' 12 := fun h => by
  have := @h Unit Unit ℕ _ _ _ _ _ (fun M => M = 0) (fun _ _ => 1) rfl (fun p q hp hq => by simp [hp, hq])
  exact absurd (congrFun (congrFun this ()) ()) (by decide)

-- `Matrix.induction_on` idx 6: necessary (m = ℕ, P = finitely many nonzero rows, all-ones matrix)
theorem c7_8 : ¬ drop0% Matrix.induction_on 6 := fun h => by
  have := @h ℕ Unit ℕ _ _ _ _ _ _ (fun M => {i | M i () ≠ 0}.Finite) (fun _ _ => 1)
    (fun p q hp hq => (hp.union hq).subset (fun i hi => by
      by_contra hc; simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc hi; simp [hc.1, hc.2] at hi))
    (fun i j x => (Set.finite_singleton i).subset (fun k hk => by
      by_contra hc; simp only [Set.mem_singleton_iff, Set.mem_setOf_eq] at hc hk; simp [Matrix.single, Ne.symm hc] at hk))
  simp at this; exact Set.infinite_univ this

-- `Matrix.induction_on` idx 7: necessary (n = ℕ, P = finitely many nonzero columns, all-ones matrix)
theorem c7_9 : ¬ drop0% Matrix.induction_on 7 := fun h => by
  have := @h Unit ℕ ℕ _ _ _ _ _ _ (fun M => {j | M () j ≠ 0}.Finite) (fun _ _ => 1)
    (fun p q hp hq => (hp.union hq).subset (fun i hi => by
      by_contra hc; simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc hi; simp [hc.1, hc.2] at hi))
    (fun i j x => (Set.finite_singleton j).subset (fun k hk => by
      by_contra hc; simp only [Set.mem_singleton_iff, Set.mem_setOf_eq] at hc hk; simp [Matrix.single, Ne.symm hc] at hk))
  simp at this; exact Set.infinite_univ this

-- `Matrix.induction_on` idx 8: necessary (m = Empty, P = False)
theorem c7_10 : ¬ drop0% Matrix.induction_on 8 := fun h =>
  @h Empty Unit ℕ _ _ _ _ _ _ (fun _ => False) (fun e => e.elim) (fun _ _ hp _ => hp) (fun i => i.elim)

-- `Matrix.induction_on` idx 9: necessary (n = Empty, P = False)
theorem c7_11 : ¬ drop0% Matrix.induction_on 9 := fun h =>
  @h Unit Empty ℕ _ _ _ _ _ _ (fun _ => False) (fun _ e => e.elim) (fun _ _ hp _ => hp) (fun _ j => j.elim)

-- `Matrix.induction_on` idx 12: necessary (P = some entry of column 0 is zero, all-ones)
theorem c7_12 : ¬ drop0% Matrix.induction_on 12 := fun h => by
  have := @h (Fin 2) Unit ℕ _ _ _ _ _ _ _ (fun M => M 0 () = 0 ∨ M 1 () = 0) (fun _ _ => 1)
    (fun i j x => by fin_cases i <;> simp [Matrix.single])
  simp at this

-- `Matrix.induction_on` idx 13: necessary (P = (· = 0), all-ones 1×1 matrix)
theorem c7_13 : ¬ drop0% Matrix.induction_on 13 := fun h => by
  have := @h Unit Unit ℕ _ _ _ _ _ _ _ (fun M => M = 0) (fun _ _ => 1) (fun p q hp hq => by simp [hp, hq])
  exact absurd (congrFun (congrFun this ()) ()) (by decide)

-- `Matrix.ext_addMonoidHom` idx 12: necessary (f = id, g = 0)
theorem c7_14 : ¬ drop0% Matrix.ext_addMonoidHom 12 := fun h => by
  have := @h Unit Unit ℕ (Matrix Unit Unit ℕ) _ _ _ _ _ _ (AddMonoidHom.id _) 0
  have := DFunLike.congr_fun this 1; simp at this

-- `Matrix.ext_linearMap` idx 16: necessary (f = id, g = 0)
theorem c7_15 : ¬ drop0% Matrix.ext_linearMap 16 := fun h => by
  have := @h Unit Unit ℕ ℕ (Matrix Unit Unit ℕ) _ _ _ _ _ _ _ _ _ LinearMap.id 0
  have := LinearMap.congr_fun this 1; simp at this

-- `Matrix.liftLinear_apply` idx 17: necessary (R = S = β = M2 acting on itself on the left)
theorem c7_16 : ¬ indep0% Matrix.liftLinear_apply 17 := fun h =>
  nSC (@h Unit Unit M2 M2 M2 M2 _ _ _ _ _ _ _ _ _ _ _ (fun _ _ => 0) 0)

-- `Matrix.liftLinear_single` idx 17: necessary (R = S = β = M2 acting on itself on the left)
theorem c7_17 : ¬ indep0% Matrix.liftLinear_single 17 := fun h =>
  nSC (@h Unit Unit M2 M2 M2 M2 _ _ _ _ _ _ _ _ _ _ _ (fun _ _ => 0) () () 0)

-- `Matrix.liftLinear_comp_singleLinearMap` idx 17: necessary (R = S = β = M2 acting on itself on the left)
theorem c7_18 : ¬ indep0% Matrix.liftLinear_comp_singleLinearMap 17 := fun h =>
  nSC (@h Unit Unit M2 M2 M2 M2 _ _ _ _ _ _ _ _ _ _ _ (fun _ _ => 0) () ())

-- `Matrix.liftLinear_singleLinearMap` idx 14: necessary (R = S = α = M2 acting on itself on the left)
theorem c7_19 : ¬ indep0% Matrix.liftLinear_singleLinearMap 14 := fun h =>
  nSC (@h Unit Unit M2 M2 M2 _ _ _ _ _ _ _ _ _)

-- `Matrix.single_mul_apply_of_ne` idx 13: necessary (a = i, c = 1, M = 1)
theorem c7_20 : ¬ drop0% Matrix.single_mul_apply_of_ne 13 := fun h =>
  absurd (@h Unit Unit Unit ℕ _ _ _ _ 1 () () () () 1) (by decide)

-- `Matrix.mul_single_apply_of_ne` idx 13: necessary (b = j, c = 1, M = 1)
theorem c7_21 : ¬ drop0% Matrix.mul_single_apply_of_ne 13 := fun h =>
  absurd (@h Unit Unit Unit ℕ _ _ _ _ 1 () () () () 1) (by decide)

-- `Matrix.single_mul_single_of_ne` idx 14: necessary (j = k, c = d = 1)
theorem c7_22 : ¬ drop0% Matrix.single_mul_single_of_ne 14 := fun h =>
  absurd (@h Unit Unit Unit ℕ _ _ _ _ _ 1 () () () () 1) (by decide)

-- `Matrix.row_eq_zero_of_commute_single` idx 9: necessary (all-ones 2×2, i = j = 0, k = 1)
theorem c7_23 : ¬ drop0% Matrix.row_eq_zero_of_commute_single 9 := fun h =>
  absurd (@h (Fin 2) ℕ _ _ _ 0 0 1 (fun _ _ => 1) (by decide)) (by decide)

-- `Matrix.row_eq_zero_of_commute_single` idx 10: necessary (M = 1, k = j)
theorem c7_24 : ¬ drop0% Matrix.row_eq_zero_of_commute_single 10 := fun h =>
  absurd (@h Unit ℕ _ _ _ () () () 1 (Commute.one_right _)) (by decide)

-- `Matrix.col_eq_zero_of_commute_single` idx 9: necessary (all-ones 2×2, i = j = 0, k = 1)
theorem c7_25 : ¬ drop0% Matrix.col_eq_zero_of_commute_single 9 := fun h =>
  absurd (@h (Fin 2) ℕ _ _ _ 0 0 1 (fun _ _ => 1) (by decide)) (by decide)

-- `Matrix.col_eq_zero_of_commute_single` idx 10: necessary (M = 1, k = i)
theorem c7_26 : ¬ drop0% Matrix.col_eq_zero_of_commute_single 10 := fun h =>
  absurd (@h Unit ℕ _ _ _ () () () 1 (Commute.one_right _)) (by decide)

-- `Matrix.diag_eq_of_commute_single` idx 8: necessary (M = diagonal ![1,0], i = 0, j = 1)
theorem c7_27 : ¬ drop0% Matrix.diag_eq_of_commute_single 8 := fun h =>
  absurd (@h (Fin 2) ℕ _ _ _ 0 1 (Matrix.diagonal ![1,0])) (by decide)

-- `Matrix.mem_range_scalar_of_commute_single` idx 6: necessary (M = diagonal ![1,0])
theorem c7_28 : ¬ drop0% Matrix.mem_range_scalar_of_commute_single 6 := fun h => by
  obtain ⟨a, ha⟩ := @h (Fin 2) ℕ _ _ _ (Matrix.diagonal ![1,0])
  rw [Matrix.scalar_apply, Matrix.diagonal_eq_diagonal_iff] at ha
  exact absurd ((ha 0).symm.trans (ha 1)) (by decide)

-- `Matrix.blockDiagonal_apply_ne` idx 11: necessary (k = k', blocks of ones)
theorem c7_29 : ¬ drop0% Matrix.blockDiagonal_apply_ne 11 := fun h =>
  absurd (@h Unit Unit Unit ℕ _ _ (fun _ _ _ => 1) () () () ()) (by decide)

-- `Matrix.blockDiagonal_map` idx 10: necessary (f = const 1, two blocks, off-block entry)
theorem c7_30 : ¬ drop0% Matrix.blockDiagonal_map 10 := fun h => by
  have := congrFun (congrFun (@h Unit Unit (Fin 2) ℕ ℕ _ _ _ (fun _ _ _ => 0) (fun _ => 1)) ((), 0)) ((), 1)
  simp [Matrix.blockDiagonal_apply] at this

-- `Matrix.blockDiagonal'_apply_ne` idx 11: necessary (k = k', blocks of ones)
theorem c7_31 : ¬ drop0% Matrix.blockDiagonal'_apply_ne 11 := fun h =>
  absurd (@h Unit (fun _ => Unit) (fun _ => Unit) ℕ _ _ (fun _ _ _ => 1) () () () ()) (by decide)

-- `Matrix.blockDiagonal'_map` idx 10: necessary (f = const 1, two blocks, off-block entry)
theorem c7_32 : ¬ drop0% Matrix.blockDiagonal'_map 10 := fun h => by
  have := congrFun (congrFun (@h (Fin 2) (fun _ => Unit) (fun _ => Unit) ℕ ℕ _ _ _ (fun _ _ _ => 0) (fun _ => 1)) ⟨0, ()⟩) ⟨1, ()⟩
  simp [Matrix.blockDiagonal'_apply] at this

-- `DMatrix.ext` idx 5: necessary (M = 0, N = 1)
theorem c7_33 : ¬ drop0% DMatrix.ext 5 := fun h =>
  absurd (congrFun (congrFun (@h Unit Unit (fun _ _ => ℕ) (fun _ _ => 0) (fun _ _ => 1)) ()) ()) (by decide)

-- `DMatrix.instSubsingleton` idx 3: necessary (entries in ℕ)
theorem c7_34 : ¬ drop0% DMatrix.instSubsingleton 3 := fun h =>
  absurd (congrFun (congrFun ((@h Unit Unit (fun _ _ => ℕ)).elim (fun _ _ => 0) (fun _ _ => 1)) ()) ()) (by decide)

-- `DMatrix.map_zero` idx 7: necessary (f = const 1)
theorem c7_35 : ¬ drop0% DMatrix.map_zero 7 := fun h =>
  absurd (congrFun (congrFun (@h Unit Unit (fun _ _ => ℕ) _ (fun _ _ => ℕ) _ (fun _ _ _ => 1)) ()) ()) (by decide)

-- `DMatrix.subsingleton_of_empty_left` idx 3: necessary (m = n = Unit, entries in ℕ)
theorem c7_36 : ¬ drop0% DMatrix.subsingleton_of_empty_left 3 := fun h =>
  absurd (congrFun (congrFun ((@h Unit Unit (fun _ _ => ℕ)).elim (fun _ _ => 0) (fun _ _ => 1)) ()) ()) (by decide)

-- `DMatrix.subsingleton_of_empty_right` idx 3: necessary (m = n = Unit, entries in ℕ)
theorem c7_37 : ¬ drop0% DMatrix.subsingleton_of_empty_right 3 := fun h =>
  absurd (congrFun (congrFun ((@h Unit Unit (fun _ _ => ℕ)).elim (fun _ _ => 0) (fun _ _ => 1)) ()) ()) (by decide)

-- `Matrix.diagonal_mem_matrix_iff` idx 5: necessary (S = {1}, d = 1, Fin 2)
theorem c7_38 : ¬ drop0% Matrix.diagonal_mem_matrix_iff 5 := fun h => by
  have := Set.mem_matrix.1 ((@h (Fin 2) ℕ _ _ {1} (fun _ => 1)).2 (fun _ => rfl)) 0 1
  simp at this

-- `Matrix.map_ofNat` idx 7: necessary (f = const 1, d = 2, entry (0,1))
theorem c7_39 : ¬ drop0% Matrix.map_ofNat 7 := fun h => by
  have := congrFun (congrFun (@h (Fin 2) ℕ ℕ _ _ _ (fun _ => 1) 2 _) 0) 1
  revert this; decide

-- `Matrix.submatrix_ofNat` idx 8: necessary (e : Fin 2 → Unit constant, k = 2, entry (0,1))
theorem c7_40 : ¬ drop0% Matrix.submatrix_ofNat 8 := fun h => by
  have := congrFun (congrFun (@h (Fin 2) Unit ℕ _ _ _ _ (fun _ => ()) 2 _) 0) 1
  revert this; decide

-- `Matrix.transpose_eq_ofNat` idx 6: necessary (d = 0 is not AtLeastTwo)
theorem c7_41 : ¬ indep0% Matrix.transpose_eq_ofNat 6 := fun h =>
  absurd (@h Unit ℕ _ _ 0 0).prop (by decide)

-- `Matrix.submatrix_ofNat_embedding` idx 9: necessary (k = 0 is not AtLeastTwo)
theorem c7_42 : ¬ indep0% Matrix.submatrix_ofNat_embedding 9 := fun h =>
  absurd (@h Unit Unit ℕ _ _ _ _ (Function.Embedding.refl _) 0).prop (by decide)

-- `Matrix.submatrix_equiv_eq_ofNat_iff` idx 10: necessary (k = 0 is not AtLeastTwo)
theorem c7_43 : ¬ indep0% Matrix.submatrix_equiv_eq_ofNat_iff 10 := fun h =>
  absurd (@h Unit Unit ℕ _ _ _ _ 0 (Equiv.refl _) 0).prop (by decide)

-- `dotProduct_smul` idx 7: necessary (R = α = M2, left multiplication; v = eA, x = eB, w = 1)
theorem c7_44 : ¬ drop0% dotProduct_smul 7 := fun h =>
  absurd (@h Unit M2 M2 _ _ _ _ eB (fun _ => eA) (fun _ => 1)) (by decide)

-- `Matrix.mul_smul` idx 10: necessary (R = α = M2, left multiplication)
theorem c7_45 : ¬ drop0% Matrix.mul_smul 10 := fun h =>
  absurd (@h Unit Unit Unit M2 M2 _ _ _ _ _ (fun _ _ => eA) eB (fun _ _ => 1)) (by decide)

-- `Matrix.Semiring.isScalarTower` idx 7: necessary (R = M2ᵐᵒᵖ acting by right multiplication on M2)
theorem c7_46 : ¬ drop0% Matrix.Semiring.isScalarTower 7 := fun h => by
  have := (@h Unit M2ᵐᵒᵖ M2 _ _ _ _).smul_assoc (MulOpposite.op eB) (fun _ _ => 1) (fun _ _ => eA)
  revert this; decide

-- `Matrix.Semiring.smulCommClass` idx 7: necessary (R = M2 acting by left multiplication on M2)
theorem c7_47 : ¬ drop0% Matrix.Semiring.smulCommClass 7 := fun h => by
  have := (@h Unit M2 M2 _ _ _ _).smul_comm eB (fun _ _ => eA) (fun _ _ => 1)
  revert this; decide

-- `Matrix.map_mul` idx 12: necessary (f = succ, L = M = 1×1 ones)
theorem c7_48 : ¬ drop0% Matrix.map_mul 12 := fun h =>
  absurd (@h Unit Unit Unit ℕ ℕ _ _ (fun _ _ => 1) (fun _ _ => 1) _ (FW ℕ ℕ) _ ⟨Nat.succ⟩) (by decide)

-- `Matrix.pow_apply_nonneg` idx 6: necessary (ℕ with the discrete order, A = 0, k = 0)
theorem c7_49 : ¬ drop0% Matrix.pow_apply_nonneg 6 := fun h => by
  have := @h Unit DN _ _ _ _ 0 (fun _ _ => rfl) 0 () ()
  have h2 : ((0 : Matrix Unit Unit DN) ^ 0) () () = 1 := by simp
  rw [h2] at this; exact absurd (show (0:ℕ) = 1 from this) (by decide)

-- `Matrix.pow_apply_nonneg` idx 8: necessary (A = [-1] over ℤ, k = 1)
theorem c7_50 : ¬ drop0% Matrix.pow_apply_nonneg 8 := fun h =>
  absurd (@h Unit ℤ _ _ _ _ _ (fun _ _ => -1) 1 () ()) (by decide)

-- `IsStablyFiniteRing.isDedekindFiniteMonoid` idx 3: necessary (shift operators on ℕ → ℕ, n = 1)
theorem c7_51 : ¬ drop0% IsStablyFiniteRing.isDedekindFiniteMonoid 3 := fun h =>
  fBA ((@h E _ _ 1).mul_eq_one_symm fAB)

-- `instIsDedekindFiniteMonoidOfIsStablyFiniteRing` idx 2: necessary (shift operators on ℕ → ℕ)
theorem c7_52 : ¬ drop0% instIsDedekindFiniteMonoidOfIsStablyFiniteRing 2 := fun h => E_nDF (h E)

-- `Matrix.instIsDedekindFiniteMonoidOfIsStablyFiniteRing` idx 6: necessary (1×1 matrices of shift operators)
theorem c7_53 : ¬ drop0% Matrix.instIsDedekindFiniteMonoidOfIsStablyFiniteRing 6 := fun h =>
  mU_nDF (h Unit E)

-- `Matrix.instIsStablyFiniteRing` idx 6: necessary (I = Unit, R = shift operators)
theorem c7_54 : ¬ drop0% Matrix.instIsStablyFiniteRing 6 := fun h =>
  mU_nDF (@instIsDedekindFiniteMonoidOfIsStablyFiniteRing _ _ (h Unit E))

-- `Matrix.mul_eq_one_comm_of_equiv` idx 9: necessary (1×1 matrices of shift operators)
theorem c7_55 : ¬ drop0% Matrix.mul_eq_one_comm_of_equiv 9 := fun h =>
  mBA ((@h Unit Unit E _ _ _ _ _ _ mA mB (Equiv.refl _)).1 mAB)

-- `Matrix.mul_eq_one_comm_of_card_eq` idx 9: necessary (1×1 matrices of shift operators)
theorem c7_56 : ¬ drop0% Matrix.mul_eq_one_comm_of_card_eq 9 := fun h =>
  mBA ((@h Unit Unit E _ _ _ _ _ _ mA mB rfl).1 mAB)

-- `Matrix.mul_eq_one_comm_of_card_eq` idx 12: necessary (m = Unit, n = Empty over ZMod 2: B * A = 1 but A * B = 0)
theorem c7_57 : ¬ drop0% Matrix.mul_eq_one_comm_of_card_eq 12 := fun h => by
  have := (@h Unit Empty (ZMod 2) _ _ _ _ _ _ _ 0 0).2 (Subsingleton.elim _ _)
  revert this; decide

-- `IsStablyFiniteRing.of_injective` idx 8: necessary (shift operators → PUnit)
theorem c7_58 : ¬ drop0% IsStablyFiniteRing.of_injective 8 := fun h =>
  E_nSF (@h E PUnit (E →+* PUnit) _ _ _ _ toP pSF)

-- `IsStablyFiniteRing.of_injective` idx 9: necessary (R = S = shift operators, f = id)
theorem c7_59 : ¬ drop0% IsStablyFiniteRing.of_injective 9 := fun h =>
  E_nSF (@h E E (E →+* E) _ _ _ _ (RingHom.id E) Function.injective_id)

-- `instIsStablyFiniteRingSubtypeMem` idx 6: necessary (R = shift operators, S = ⊤)
theorem c7_60 : ¬ drop0% instIsStablyFiniteRingSubtypeMem 6 := fun h => by
  have hS := @h E (Subsemiring E) _ _ _ ⊤
  have hD : IsDedekindFiniteMonoid (⊤ : Subsemiring E) := inferInstance
  have := hD.mul_eq_one_symm (a := ⟨sa, trivial⟩) (b := ⟨sb, trivial⟩) (Subtype.ext hab)
  exact hba (congrArg Subtype.val this)

-- `instIsStablyFiniteRingSubtypeMem` idx 4: necessary (F = Set PUnit: ∅ does not contain 1)
theorem c7_61 : ¬ indep0% instIsStablyFiniteRingSubtypeMem 4 := fun h => by
  have := (@h PUnit (Subsemigroup PUnit) _ _ ⊥ pSF).one_mem ⊥
  rw [← SetLike.mem_coe, Subsemigroup.coe_bot] at this; exact this

-- `Matrix.vecMulVec_ne_zero` idx 5: necessary (ZMod 4, a = b = 2)
theorem c7_62 : ¬ drop0% Matrix.vecMulVec_ne_zero 5 := fun h =>
  (@h Unit Unit (ZMod 4) _ _ (fun _ => 2) (fun _ => 2) (by decide) (by decide)) (by decide)

-- `Matrix.vecMulVec_ne_zero` idx 8: necessary (a = 0)
theorem c7_63 : ¬ drop0% Matrix.vecMulVec_ne_zero 8 := fun h =>
  (@h Unit Unit ℕ _ _ _ 0 (fun _ => 1) (by decide)) (by decide)

-- `Matrix.vecMulVec_ne_zero` idx 9: necessary (b = 0)
theorem c7_64 : ¬ drop0% Matrix.vecMulVec_ne_zero 9 := fun h =>
  (@h Unit Unit ℕ _ _ _ (fun _ => 1) 0 (by decide)) (by decide)

-- `Matrix.vecMulVec_eq_zero` idx 4: necessary (ZMod 4, a = b = 2)
theorem c7_65 : ¬ drop0% Matrix.vecMulVec_eq_zero 4 := fun h =>
  absurd ((@h Unit Unit (ZMod 4) _ (fun _ => 2) (fun _ => 2)).1 (by decide)) (by decide)

-- `Matrix.add_vecMulVec` idx 5: necessary (ℕ with constant multiplication 1)
theorem c7_66 : ¬ drop0% Matrix.add_vecMulVec 5 := fun h =>
  absurd (@h Unit Unit N1 _ _ (fun _ => (1 : ℕ)) (fun _ => (1 : ℕ)) (fun _ => (1 : ℕ))) (by decide)

-- `Matrix.vecMulVec_add` idx 5: necessary (ℕ with constant multiplication 1)
theorem c7_67 : ¬ drop0% Matrix.vecMulVec_add 5 := fun h =>
  absurd (@h Unit Unit N1 _ _ (fun _ => (1 : ℕ)) (fun _ => (1 : ℕ)) (fun _ => (1 : ℕ))) (by decide)

-- `Matrix.smul_vecMulVec` idx 6: necessary (R = M2ᵐᵒᵖ acting by right multiplication)
theorem c7_68 : ¬ drop0% Matrix.smul_vecMulVec 6 := fun h =>
  absurd (@h Unit Unit M2ᵐᵒᵖ M2 _ _ (MulOpposite.op eA) (fun _ => 1) (fun _ => eB)) (by decide)

-- `Matrix.vecMulVec_smul` idx 6: necessary (R = M2 acting by left multiplication)
theorem c7_69 : ¬ drop0% Matrix.vecMulVec_smul 6 := fun h =>
  absurd (@h Unit Unit M2 M2 _ _ eB (fun _ => eA) (fun _ => 1)) (by decide)

-- `Matrix.mulVec_smul` idx 7: necessary (R = M2 acting by left multiplication)
theorem c7_70 : ¬ drop0% Matrix.mulVec_smul 7 := fun h =>
  absurd (@h Unit Unit M2 M2 _ _ _ (fun _ _ => eA) eB (fun _ => 1)) (by decide)

-- `Matrix.smul_mulVec` idx 7: necessary (R = M2ᵐᵒᵖ acting by right multiplication)
theorem c7_71 : ¬ drop0% Matrix.smul_mulVec 7 := fun h =>
  absurd (@h Unit Unit M2ᵐᵒᵖ M2 _ _ _ (MulOpposite.op eA) (fun _ _ => 1) (fun _ => eB)) (by decide)

-- `Matrix.smul_vecMul` idx 7: necessary (R = M2ᵐᵒᵖ acting by right multiplication)
theorem c7_72 : ¬ drop0% Matrix.smul_vecMul 7 := fun h =>
  absurd (@h Unit Unit M2ᵐᵒᵖ M2 _ _ _ (MulOpposite.op eA) (fun _ => 1) (fun _ _ => eB)) (by decide)

-- `Matrix.vecMul_smul` idx 7: necessary (R = M2 acting by left multiplication)
theorem c7_73 : ¬ drop0% Matrix.vecMul_smul 7 := fun h =>
  absurd (@h Unit Unit M2 M2 _ _ _ (fun _ => eA) eB (fun _ _ => 1)) (by decide)

-- `Matrix.mul_right_injective_iff_mulVec_injective` idx 6: necessary (n = Empty, A = 0)
theorem c7_74 : ¬ drop0% Matrix.mul_right_injective_iff_mulVec_injective 6 := fun h => by
  have := (@h Unit Unit Empty ℕ _ _ 0).1 (fun B C _ => funext fun _ => funext fun e => e.elim)
  exact absurd (@this (fun _ => 0) (fun _ => 1) (by decide)) (by decide)

-- `Matrix.mul_left_injective_iff_vecMul_injective` idx 5: necessary (l = Empty, A = 0)
theorem c7_75 : ¬ drop0% Matrix.mul_left_injective_iff_vecMul_injective 5 := fun h => by
  have := (@h Empty Unit Unit ℕ _ _ 0).1 (fun B C _ => funext fun e => e.elim)
  exact absurd (@this (fun _ => 0) (fun _ => 1) (by decide)) (by decide)

-- `Matrix.ext_of_mulVec_single` idx 8: necessary (M = 0, N = 1)
theorem c7_76 : ¬ drop0% Matrix.ext_of_mulVec_single 8 := fun h =>
  absurd (@h Unit Unit ℕ _ _ _ 0 1) (by decide)

-- `Matrix.ext_of_single_vecMul` idx 8: necessary (M = 0, N = 1)
theorem c7_77 : ¬ drop0% Matrix.ext_of_single_vecMul 8 := fun h =>
  absurd (@h Unit Unit ℕ _ _ _ 0 1) (by decide)

-- `Matrix.mulVec_injective_of_isUnit` idx 6: necessary (A = 0)
theorem c7_78 : ¬ drop0% Matrix.mulVec_injective_of_isUnit 6 := fun h =>
  absurd ((@h Unit ℕ _ _ _ 0) (a₁ := fun _ => 0) (a₂ := fun _ => 1) (by decide)) (by decide)

-- `Matrix.vecMul_injective_of_isUnit` idx 6: necessary (A = 0)
theorem c7_79 : ¬ drop0% Matrix.vecMul_injective_of_isUnit 6 := fun h =>
  absurd ((@h Unit ℕ _ _ _ 0) (a₁ := fun _ => 0) (a₂ := fun _ => 1) (by decide)) (by decide)

-- `Matrix.pow_row_eq_zero_of_le` idx 9: necessary (M = 1, k = l = 0)
theorem c7_80 : ¬ drop0% Matrix.pow_row_eq_zero_of_le 9 := fun h =>
  absurd (@h Unit ℕ _ _ _ 1 0 0 () le_rfl) (by decide)

-- `Matrix.pow_row_eq_zero_of_le` idx 10: necessary (M = 0, k = 1, l = 0)
theorem c7_81 : ¬ drop0% Matrix.pow_row_eq_zero_of_le 10 := fun h =>
  absurd (@h Unit ℕ _ _ _ 0 1 0 () (by decide)) (by decide)

-- `Matrix.pow_col_eq_zero_of_le` idx 9: necessary (M = 1, k = l = 0)
theorem c7_82 : ¬ drop0% Matrix.pow_col_eq_zero_of_le 9 := fun h =>
  absurd (@h Unit ℕ _ _ _ 1 0 0 () le_rfl) (by decide)

-- `Matrix.pow_col_eq_zero_of_le` idx 10: necessary (M = 0, k = 1, l = 0)
theorem c7_83 : ¬ drop0% Matrix.pow_col_eq_zero_of_le 10 := fun h =>
  absurd (@h Unit ℕ _ _ _ 0 1 0 () (by decide)) (by decide)

-- `Matrix.submatrix_mul` idx 16: necessary (o = Empty: empty sum on the right)
theorem c7_84 : ¬ drop0% Matrix.submatrix_mul 16 := fun h =>
  absurd (@h Unit Unit Unit Empty ℕ _ _ _ _ Unit Unit (fun _ _ => 1) (fun _ _ => 1) id (fun e => e.elim) id) (by decide)

-- `Matrix.mul_submatrix_one` idx 6: removable (Finite o follows from e₁ : n ≃ o with n a Fintype)
theorem c7_85 : drop% Matrix.mul_submatrix_one 6 := by
  intro l m n o α _ _ _ e₁ e₂ M
  have : Finite o := Finite.of_equiv n e₁
  exact Matrix.mul_submatrix_one e₁ e₂ M

-- `Matrix.one_submatrix_mul` idx 6: removable (Finite o follows from e₂ : m ≃ o with m a Fintype)
theorem c7_86 : drop% Matrix.one_submatrix_mul 6 := by
  intro l m n o α _ _ _ e₁ e₂ M
  have : Finite o := Finite.of_equiv m e₂
  exact Matrix.one_submatrix_mul e₁ e₂ M

-- `PEquiv.toMatrix_injective` idx 5: necessary (α = Unit: refl and ⊥ give the same matrix)
theorem c7_87 : ¬ drop0% PEquiv.toMatrix_injective 5 := fun h => by
  have := congrArg (fun f => f ()) (@h Unit Unit Unit _ _ (PEquiv.refl Unit) ⊥ (Subsingleton.elim _ _))
  simp at this

-- `Multiset.Rel.add` idx 7: necessary (r = Eq, s = {0}, t = u = v = 0)
theorem c7_101 : ¬ drop0% Multiset.Rel.add 7 := fun h =>
  absurd (Multiset.card_eq_card_of_rel (@h ℕ ℕ Eq {0} 0 0 0 Multiset.Rel.zero)) (by simp)

-- `Multiset.Rel.add` idx 8: necessary (r = Eq, u = {0}, s = t = v = 0)
theorem c7_102 : ¬ drop0% Multiset.Rel.add 8 := fun h =>
  absurd (Multiset.card_eq_card_of_rel (@h ℕ ℕ Eq 0 0 {0} 0 Multiset.Rel.zero)) (by simp)

-- `Multiset.case_strongInductionOn` idx 3: necessary (p = (· ≠ 0), s = 0)
theorem c7_103 : ¬ drop0% Multiset.case_strongInductionOn 3 := fun h =>
  @h ℕ (fun s => s ≠ 0) 0 (fun a s _ => Multiset.cons_ne_zero) rfl

-- `Multiset.case_strongInductionOn` idx 4: necessary (p = (· = 0), s = {0})
theorem c7_104 : ¬ drop0% Multiset.case_strongInductionOn 4 := fun h =>
  absurd (@h ℕ (fun s => s = 0) {0} rfl) (by simp)

-- `Multiset.rel_join` idx 5: necessary (r = Eq, s = {{0}}, t = 0)
theorem c7_105 : ¬ drop0% Multiset.rel_join 5 := fun h =>
  absurd (Multiset.card_eq_card_of_rel (@h ℕ ℕ Eq {{0}} 0)) (by simp)

-- `Multiset.bind_congr` idx 5: necessary (m = {0}, f = const {0}, g = const 0)
theorem c7_106 : ¬ drop0% Multiset.bind_congr 5 := fun h =>
  absurd (@h ℕ ℕ (fun _ => {0}) (fun _ => 0) {0}) (by simp)

-- `Multiset.bind_hcongr` idx 6: necessary (m = 0, β = ℕ, β' = ℝ: Multiset ℕ ≠ Multiset ℝ by countability)
theorem c7_107 : ¬ drop0% Multiset.bind_hcongr 6 := fun h => by
  have e := type_eq_of_heq (@h ℕ ℕ ℝ 0 (fun _ => 0) (fun _ => 0) (fun a ha => absurd ha (Multiset.notMem_zero a)))
  have hc : Countable (Multiset ℝ) := e ▸ inferInstance
  exact Cardinal.not_countable_real (Set.countable_univ_iff.2
    (Function.Injective.countable (f := fun x : ℝ => ({x} : Multiset ℝ)) (fun x y hxy => by simpa using hxy)))

-- `Multiset.bind_hcongr` idx 7: necessary (β = β' = ℕ, m = {0}, f = const {0}, f' = const 0)
theorem c7_108 : ¬ drop0% Multiset.bind_hcongr 7 := fun h =>
  absurd (eq_of_heq (@h ℕ ℕ ℕ {0} (fun _ => {0}) (fun _ => 0) rfl)) (by simp)

-- `Multiset.map_hcongr` idx 6: necessary (m = 0, β = ℕ, β' = ℝ: Multiset ℕ ≠ Multiset ℝ by countability)
theorem c7_109 : ¬ drop0% Multiset.map_hcongr 6 := fun h => by
  have e := type_eq_of_heq (@h ℕ ℕ ℝ 0 (fun _ => 0) (fun _ => 0) (fun a ha => absurd ha (Multiset.notMem_zero a)))
  have hc : Countable (Multiset ℝ) := e ▸ inferInstance
  exact Cardinal.not_countable_real (Set.countable_univ_iff.2
    (Function.Injective.countable (f := fun x : ℝ => ({x} : Multiset ℝ)) (fun x y hxy => by simpa using hxy)))

-- `Multiset.map_hcongr` idx 7: necessary (β = β' = ℕ, m = {0}, f = id, f' = succ)
theorem c7_110 : ¬ drop0% Multiset.map_hcongr 7 := fun h =>
  absurd (eq_of_heq (@h ℕ ℕ ℕ {0} id Nat.succ rfl)) (by simp)

-- `Multiset.rel_bind` idx 10: necessary (r = p = Eq, s = t = {0}, f = const {0}, g = const 0)
theorem c7_111 : ¬ drop0% Multiset.rel_bind 10 := fun h =>
  absurd (Multiset.card_eq_card_of_rel (@h ℕ ℕ ℕ ℕ Eq Eq {0} {0} (fun _ => {0}) (fun _ => 0) (Multiset.rel_eq.2 rfl))) (by simp)

-- `Multiset.rel_bind` idx 11: necessary (r = p = Eq, s = {0}, t = 0, f = g = const {0})
theorem c7_112 : ¬ drop0% Multiset.rel_bind 11 := fun h =>
  absurd (Multiset.card_eq_card_of_rel (@h ℕ ℕ ℕ ℕ Eq Eq {0} 0 (fun _ => {0}) (fun _ => {0})
    (fun _ _ _ => Multiset.rel_eq.2 rfl))) (by simp)

-- `Multiset.le_bind` idx 5: necessary (S = 0, f = const {0})
theorem c7_113 : ¬ drop0% Multiset.le_bind 5 := fun h =>
  absurd (@h ℕ ℕ (fun _ => {0}) 0 0) (by simp)

-- `Multiset.Nodup.sigma` idx 4: necessary (s = {0,0}, t = const {0})
theorem c7_114 : ¬ drop0% Multiset.Nodup.sigma 4 := fun h =>
  absurd (@h ℕ {0, 0} (fun _ => ℕ) (fun _ => {0}) (fun _ => by simp)) (by decide)

-- `Multiset.Nodup.sigma` idx 5: necessary (s = {0}, t = const {0,0})
theorem c7_115 : ¬ drop0% Multiset.Nodup.sigma 5 := fun h =>
  absurd (@h ℕ {0} (fun _ => ℕ) (fun _ => {0, 0}) (by simp)) (by decide)

-- `Multiset.countP_pos_of_mem` idx 6: necessary (p = False, s = {0})
theorem c7_116 : ¬ drop0% Multiset.countP_pos_of_mem 6 := fun h =>
  absurd (@h ℕ (fun _ => False) _ {0} 0 (by simp)) (by simp)

-- `Multiset.Rel.countP_eq` idx 2: necessary (r = (≠) on Bool, s = {true}, t = {false}, x = true)
theorem c7_117 : ¬ drop0% Multiset.Rel.countP_eq 2 := fun h =>
  absurd (@h Bool (· ≠ ·) ⟨fun _ _ h => h.symm⟩ {true} {false} true _
    (Multiset.Rel.cons (by decide) Multiset.Rel.zero)) (by decide)

-- `Multiset.Rel.countP_eq` idx 3: necessary (r = (≤) on ℕ, s = {0}, t = {1}, x = 1)
theorem c7_118 : ¬ drop0% Multiset.Rel.countP_eq 3 := fun h =>
  absurd (@h ℕ (· ≤ ·) ⟨fun _ _ _ => le_trans⟩ {0} {1} 1 _
    (Multiset.Rel.cons (by decide) Multiset.Rel.zero)) (by decide)

-- `Multiset.lift_coe` idx 4: necessary (f = id on lists, [0,1] ~ [1,0])
theorem c7_119 : ¬ indep0% Multiset.lift_coe 4 := fun h =>
  absurd (@h ℕ (List ℕ) [] id [0, 1] [1, 0] (List.Perm.swap 1 0 [])) (by decide)

-- `Multiset.Subset.trans` idx 4: necessary (s = {0}, t = u = 0)
theorem c7_120 : ¬ drop0% Multiset.Subset.trans 4 := fun h =>
  absurd (@h ℕ {0} 0 0 (Multiset.Subset.refl _)) (by simp)

-- `Multiset.Subset.trans` idx 5: necessary (s = t = {0}, u = 0)
theorem c7_121 : ¬ drop0% Multiset.Subset.trans 5 := fun h =>
  absurd (@h ℕ {0} {0} 0 (Multiset.Subset.refl _)) (by simp)

-- `Multiset.leInductionOn` idx 5: necessary (C = False)
theorem c7_122 : ¬ drop0% Multiset.leInductionOn 5 := fun h =>
  @h ℕ (fun _ _ => False) 0 0 le_rfl

-- `Multiset.coe_pmap` idx 5: necessary (p = False, l = [0])
theorem c7_123 : ¬ indep0% Multiset.coe_pmap 5 := fun h =>
  @h ℕ ℕ (fun _ => False) (fun _ h => h.elim) [0] 0 (by simp)

-- `Multiset.pmap_congr` idx 7: necessary (p = False, s = {0})
theorem c7_124 : ¬ indep0% Multiset.pmap_congr 7 := fun h =>
  @h ℕ ℕ (fun _ => False) (fun _ => True) (fun _ h => h.elim) (fun _ _ => 0) {0} (fun _ _ => trivial)
    (fun _ _ h => h.elim) 0 (Multiset.mem_singleton_self 0)

-- `Multiset.pmap_congr` idx 8: necessary (q = False, s = {0})
theorem c7_125 : ¬ indep0% Multiset.pmap_congr 8 := fun h =>
  @h ℕ ℕ (fun _ => True) (fun _ => False) (fun _ _ => 0) (fun _ h => h.elim) {0} (fun _ _ => trivial)
    (fun _ _ _ h => h.elim) 0 (Multiset.mem_singleton_self 0)

-- `Multiset.pmap_congr` idx 9: necessary (p = q = True, s = {0}, f = 0, g = 1)
theorem c7_126 : ¬ drop0% Multiset.pmap_congr 9 := fun h =>
  absurd (@h ℕ ℕ (fun _ => True) (fun _ => True) (fun _ _ => 0) (fun _ _ => 1) {0}
    (fun _ _ => trivial) (fun _ _ => trivial))
    (by intro e; have := congrArg (fun s => (0:ℕ) ∈ s) e; simp [Multiset.mem_pmap] at this)

-- `Multiset.mem_pmap` idx 5: necessary (p = False, s = {0})
theorem c7_127 : ¬ indep0% Multiset.mem_pmap 5 := fun h =>
  @h ℕ ℕ (fun _ => False) (fun _ h => h.elim) {0} 0 0 (Multiset.mem_singleton_self 0)

-- `Multiset.card_pmap` idx 5: necessary (p = False, s = {0})
theorem c7_128 : ¬ indep0% Multiset.card_pmap 5 := fun h =>
  @h ℕ ℕ (fun _ => False) (fun _ h => h.elim) {0} 0 (Multiset.mem_singleton_self 0)

-- `Multiset.pairwise_coe_iff_pairwise` idx 2: necessary (r = (<), l = [1,0])
theorem c7_129 : ¬ drop0% Multiset.pairwise_coe_iff_pairwise 2 := fun h =>
  absurd ((@h ℕ (· < ·) [1, 0]).1 ⟨[0, 1], Quot.sound (List.Perm.swap 0 1 []), by decide⟩) (by decide)

-- `Multiset.Nodup.ext` idx 3: necessary (s = {0,0}, t = {0})
theorem c7_130 : ¬ drop0% Multiset.Nodup.ext 3 := fun h =>
  absurd ((@h ℕ {0, 0} {0} (by simp)).2 (fun a => by simp)) (by decide)

-- `Multiset.Nodup.ext` idx 4: necessary (s = {0}, t = {0,0})
theorem c7_131 : ¬ drop0% Multiset.Nodup.ext 4 := fun h =>
  absurd ((@h ℕ {0} {0, 0} (by simp)).2 (fun a => by simp)) (by decide)

-- `Multiset.nodup_of_le` idx 4: necessary (s = t = {0,0})
theorem c7_132 : ¬ drop0% Multiset.nodup_of_le 4 := fun h =>
  absurd (@h ℕ {0, 0} {0, 0} le_rfl) (by decide)

-- `Multiset.mem_filter_of_mem` idx 6: necessary (p = False, l = {0})
theorem c7_133 : ¬ drop0% Multiset.mem_filter_of_mem 6 := fun h =>
  absurd (@h ℕ (fun _ => False) _ 0 {0} (by simp)) (by simp)

-- `Multiset.map_filter` idx 5: necessary (f = const 0, p = (· = 0), s = {0,1})
theorem c7_134 : ¬ drop0% Multiset.map_filter 5 := fun h =>
  absurd (@h ℕ ℕ (· = 0) _ (fun _ => 0) {0, 1}
    (fun b => decidable_of_iff (b = 0) ⟨fun hb => ⟨0, rfl, hb.symm⟩, fun ⟨_, _, h⟩ => h.symm⟩)) (by decide)

-- `Multiset.map_filter'` idx 5: necessary (f = const 0, p = (· = 0), s = {0,1})
theorem c7_135 : ¬ drop0% Multiset.map_filter' 5 := fun h =>
  absurd (@h ℕ ℕ (· = 0) _ (fun _ => 0) {0, 1}
    (fun b => decidable_of_iff (b = 0) ⟨fun hb => ⟨0, rfl, hb.symm⟩, fun ⟨_, _, h⟩ => h.symm⟩)) (by decide)

-- `Multiset.find?_cons` idx 5: necessary (p = True, a = 0, s = {1})
theorem c7_136 : ¬ indep0% Multiset.find?_cons 5 := fun h =>
  absurd (@h ℕ (fun _ => True) _ 0 {1} (x := 0) (by simp) (y := 1) (by simp)) (by decide)

-- `Multiset.find?_singleton` idx 4: removable (the set of matches inside a singleton is a subsingleton)
theorem c7_137 : indep% Multiset.find?_singleton 4 := by
  intro α p _ a x hx y hy
  simp only [Set.mem_ofPred_eq, Multiset.mem_singleton] at hx hy
  rw [hx.1, hy.1]

-- `Multiset.find?_add` idx 5: necessary (p = True, s = {0}, t = {1})
theorem c7_138 : ¬ indep0% Multiset.find?_add 5 := fun h =>
  absurd (@h ℕ (fun _ => True) _ {0} {1} (x := 0) (by simp) (y := 1) (by simp)) (by decide)

-- `Multiset.find?_congr` idx 6: necessary (p₁ = True, s = {0,1})
theorem c7_139 : ¬ indep0% Multiset.find?_congr 6 := fun h =>
  absurd (@h ℕ (fun _ => True) (fun _ => True) _ _ {0, 1} (x := 0) (by simp) (y := 1) (by simp)) (by decide)

-- `Multiset.fold_hom` idx 3: necessary (op = left projection on ℕ, β = Unit)
theorem c7_141 : ¬ indep0% Multiset.fold_hom 3 := fun h =>
  lp_nC (@h ℕ Unit lp _ (fun _ _ => ()) ⟨fun _ _ => rfl⟩ ⟨fun _ _ _ => rfl⟩ (fun _ => ()) (fun _ _ => rfl) 0 0)

-- `Multiset.fold_hom` idx 4: necessary (op = commutative idempotent non-associative cop on ℕ, β = Unit)
theorem c7_142 : ¬ indep0% Multiset.fold_hom 4 := fun h =>
  cop_nA (@h ℕ Unit cop _ (fun _ _ => ()) ⟨fun _ _ => rfl⟩ ⟨fun _ _ _ => rfl⟩ (fun _ => ()) (fun _ _ => rfl) 0 0)

-- `Multiset.fold_hom` idx 6: necessary (α = Unit, op' = left projection on ℕ, m = const 0)
theorem c7_143 : ¬ indep0% Multiset.fold_hom 6 := fun h =>
  lp_nC (@h Unit ℕ (fun _ _ => ()) ⟨fun _ _ => rfl⟩ ⟨fun _ _ _ => rfl⟩ lp _ (fun _ => 0) (fun _ _ => rfl) () 0)

-- `Multiset.fold_hom` idx 7: necessary (α = Unit, op' = cop on ℕ, m = const 0)
theorem c7_144 : ¬ indep0% Multiset.fold_hom 7 := fun h =>
  cop_nA (@h Unit ℕ (fun _ _ => ()) ⟨fun _ _ => rfl⟩ ⟨fun _ _ _ => rfl⟩ cop _ (fun _ => 0) (fun _ _ => by simp [cop]) () 0)

-- `Multiset.fold_dedup_idem` idx 3: necessary (op = cop: commutative, idempotent, not associative)
theorem c7_145 : ¬ indep0% Multiset.fold_dedup_idem 3 := fun h =>
  cop_nA (@h ℕ cop _ _ _ 0 0)

-- `Multiset.fold_dedup_idem` idx 5: necessary (op = +, s = {1,1}, b = 0)
theorem c7_146 : ¬ drop0% Multiset.fold_dedup_idem 5 := fun h =>
  absurd (@h ℕ (· + ·) _ _ _ {1, 1} 0) (by decide)

-- `Multiset.comp_traverse` idx 4: necessary (G = StateM ℕ, H = Id)
theorem c7_147 : ¬ indep0% Multiset.comp_traverse 4 := fun h =>
  nCA (@h (StateM ℕ) Id _ _ idCA ℕ ℕ ℕ (fun _ => pure 0) (fun _ => pure 0) 0)

-- `Multiset.comp_traverse` idx 5: necessary (G = Id, H = StateM ℕ)
theorem c7_148 : ¬ indep0% Multiset.comp_traverse 5 := fun h =>
  nCA (@h Id (StateM ℕ) _ _ idCA ℕ ℕ ℕ (fun _ => pure 0) (fun _ => pure 0) 0)

-- `Multiset.map_traverse` idx 2: necessary (G = StateM ℕ)
theorem c7_149 : ¬ indep0% Multiset.map_traverse 2 := fun h =>
  nCA (@h (StateM ℕ) _ ℕ ℕ ℕ (fun _ => pure 0) id 0)

-- `Multiset.traverse_map` idx 2: necessary (G = StateM ℕ)
theorem c7_150 : ¬ indep0% Multiset.traverse_map 2 := fun h =>
  nCA (@h (StateM ℕ) _ ℕ ℕ ℕ id (fun _ => pure 0) 0)

-- `Multiset.naturality` idx 5: necessary (G = Id, H = StateM ℕ, eta = pure)
theorem c7_151 : ¬ indep0% Multiset.naturality 5 := fun h =>
  nCA (@h Id (StateM ℕ) _ _ idCA (ApplicativeTransformation.mk (fun _ x => pure x) (fun _ => rfl) (fun _ _ => rfl))
    ℕ ℕ (fun _ => pure 0) 0)

-- `Multiset.foldr_induction'` idx 3: necessary (f a b = a, p = q = True)
theorem c7_152 : ¬ indep0% Multiset.foldr_induction' 3 := fun h =>
  absurd ((@h ℕ ℕ (fun a _ => a) 0 (fun _ => True) (fun _ => True) 0 (fun _ _ _ _ => trivial) trivial
    (fun _ _ => trivial)).left_comm 0 1 0) (by decide)

-- `Multiset.foldr_induction` idx 2: necessary (f a b = a, p = True)
theorem c7_153 : ¬ indep0% Multiset.foldr_induction 2 := fun h =>
  absurd ((@h ℕ (fun a _ => a) 0 (fun _ => True) 0 (fun _ _ _ _ => trivial) trivial
    (fun _ _ => trivial)).left_comm 0 1 0) (by decide)

-- `Multiset.foldr_induction'` idx 8: necessary (f a b = b + 1, p = (· = 0), x = 0, s = {0})
theorem c7_154 : ¬ drop0% Multiset.foldr_induction' 8 := fun h =>
  absurd (@h ℕ ℕ (fun _ b => b + 1) ⟨fun _ _ _ => rfl⟩ 0 (fun _ => True) (· = 0) {0} rfl (fun _ _ => trivial)) (by decide)

-- `Multiset.foldr_induction'` idx 10: necessary (q = False, f a b = b + 1, p = (· = 0), s = {0})
theorem c7_155 : ¬ drop0% Multiset.foldr_induction' 10 := fun h =>
  absurd (@h ℕ ℕ (fun _ b => b + 1) ⟨fun _ _ _ => rfl⟩ 0 (fun _ => False) (· = 0) {0} (fun _ _ hq _ => hq.elim) rfl) (by decide)

-- `Multiset.foldr_induction` idx 6: necessary (f a b = b + 1, p = (· = 0), s = {0})
theorem c7_156 : ¬ drop0% Multiset.foldr_induction 6 := fun h =>
  absurd (@h ℕ (fun _ b => b + 1) ⟨fun _ _ _ => rfl⟩ 0 (· = 0) {0} rfl (by simp)) (by decide)

-- `Multiset.foldr_induction` idx 8: necessary (f = +, p = (· = 0), x = 0, s = {1})
theorem c7_157 : ¬ drop0% Multiset.foldr_induction 8 := fun h =>
  absurd (@h ℕ (· + ·) ⟨fun a b c => by omega⟩ 0 (· = 0) {1} (fun a b ha hb => by simp [ha, hb]) rfl) (by decide)

-- `Multiset.foldl_induction'` idx 8: necessary (f b a = b + 1, p = (· = 0), x = 0, s = {0})
theorem c7_158 : ¬ drop0% Multiset.foldl_induction' 8 := fun h =>
  absurd (@h ℕ ℕ (fun b _ => b + 1) ⟨fun _ _ _ => rfl⟩ 0 (fun _ => True) (· = 0) {0} rfl (fun _ _ => trivial)) (by decide)

-- `Multiset.foldl_induction'` idx 9: necessary (f b a = b, p = (· = 0), x = 1, s = 0)
theorem c7_159 : ¬ drop0% Multiset.foldl_induction' 9 := fun h =>
  absurd (@h ℕ ℕ (fun b _ => b) ⟨fun _ _ _ => rfl⟩ 1 (fun _ => True) (· = 0) 0 (fun _ _ _ hb => hb) (fun _ _ => trivial)) (by decide)

-- `Multiset.foldl_induction'` idx 10: necessary (q = False, f b a = b + 1, p = (· = 0), s = {0})
theorem c7_160 : ¬ drop0% Multiset.foldl_induction' 10 := fun h =>
  absurd (@h ℕ ℕ (fun b _ => b + 1) ⟨fun _ _ _ => rfl⟩ 0 (fun _ => False) (· = 0) {0} (fun _ _ hq _ => hq.elim) rfl) (by decide)

-- `Multiset.foldl_induction` idx 6: necessary (f b a = b + 1, p = (· = 0), s = {0})
theorem c7_161 : ¬ drop0% Multiset.foldl_induction 6 := fun h =>
  absurd (@h ℕ (fun b _ => b + 1) ⟨fun _ _ _ => rfl⟩ 0 (· = 0) {0} rfl (by simp)) (by decide)

-- `Multiset.foldl_induction` idx 7: necessary (f = +, p = (· = 0), x = 1, s = 0)
theorem c7_162 : ¬ drop0% Multiset.foldl_induction 7 := fun h =>
  absurd (@h ℕ (· + ·) ⟨fun a b c => by omega⟩ 1 (· = 0) 0 (fun a b ha hb => by simp [ha, hb]) (by simp)) (by decide)

-- `Multiset.foldl_induction` idx 8: necessary (f = +, p = (· = 0), x = 0, s = {1})
theorem c7_163 : ¬ drop0% Multiset.foldl_induction 8 := fun h =>
  absurd (@h ℕ (· + ·) ⟨fun a b c => by omega⟩ 0 (· = 0) {1} (fun a b ha hb => by simp [ha, hb]) rfl) (by decide)

-- `Multiset.map_pmap` idx 7: necessary (p = False, s = {0})
theorem c7_164 : ¬ indep0% Multiset.map_pmap 7 := fun h =>
  @h ℕ ℕ ℕ (fun _ => False) id (fun _ h => h.elim) {0} 0 (Multiset.mem_singleton_self 0)

-- `Multiset.pmap_eq_map_attach` idx 5: necessary (p = False, s = {0})
theorem c7_165 : ¬ indep0% Multiset.pmap_eq_map_attach 5 := fun h =>
  @h ℕ ℕ (fun _ => False) (fun _ h => h.elim) {0} 0 (Multiset.mem_singleton_self 0)

-- `Multiset.Nodup.pmap` idx 5: necessary (p = False, s = {0})
theorem c7_166 : ¬ indep0% Multiset.Nodup.pmap 5 := fun h =>
  @h ℕ ℕ (fun _ => False) (fun _ h => h.elim) {0} (fun _ h => h.elim) (Multiset.nodup_singleton 0) 0
    (Multiset.mem_singleton_self 0)

-- `Multiset.Nodup.pmap` idx 6: necessary (f = const 0, p = True, s = {0,1})
theorem c7_167 : ¬ drop0% Multiset.Nodup.pmap 6 := fun h =>
  absurd (@h ℕ ℕ (fun _ => True) (fun _ _ => 0) {0, 1} (fun _ _ => trivial) (by decide)) (by decide)

-- `Multiset.Nodup.pmap` idx 7: necessary (f = id, p = True, s = {0,0})
theorem c7_168 : ¬ drop0% Multiset.Nodup.pmap 7 := fun h =>
  absurd (@h ℕ ℕ (fun _ => True) (fun a _ => a) {0, 0} (fun _ _ => trivial) (fun _ _ _ _ h => h)) (by decide)

-- `Multiset.canLift` idx 4: necessary (β = Empty: {0} has no preimage)
theorem c7_169 : ¬ drop0% Multiset.canLift 4 := fun h => by
  obtain ⟨y, hy⟩ := (@h ℕ Empty (fun e => e.elim) (fun _ => True)).prf {0} (fun _ _ => trivial)
  have : y = 0 := Multiset.eq_zero_of_forall_notMem (fun e => e.elim)
  subst this; simp at hy

-- `Multiset.map_surjective_of_surjective` idx 3: necessary (f = const 0 : Unit → ℕ, {1} not hit)
theorem c7_170 : ¬ drop0% Multiset.map_surjective_of_surjective 3 := fun h => by
  obtain ⟨y, hy⟩ := @h Unit ℕ (fun _ => 0) {1}
  have : 1 ∈ Multiset.map (fun _ : Unit => 0) y := hy ▸ Multiset.mem_singleton_self 1
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 this; exact absurd ha (by decide)

-- `Multiset.inj_on_of_nodup_map` idx 4: necessary (f = const 0, s = {0,1}, x = 0, y = 1)
theorem c7_171 : ¬ drop0% Multiset.inj_on_of_nodup_map 4 := fun h =>
  absurd (@h ℕ ℕ (fun _ => 0) {0, 1} 0 (by simp) 1 (by simp) rfl) (by decide)

-- `Multiset.inj_on_of_nodup_map` idx 6: necessary (f = min · 1, s = {1}, x = 2 ∉ s, y = 1)
theorem c7_172 : ¬ drop0% Multiset.inj_on_of_nodup_map 6 := fun h =>
  absurd (@h ℕ ℕ (fun n => min n 1) {1} (by decide) 2 1 (by simp) rfl) (by decide)

-- `Multiset.inj_on_of_nodup_map` idx 8: necessary (f = min · 1, s = {1}, x = 1, y = 2 ∉ s)
theorem c7_173 : ¬ drop0% Multiset.inj_on_of_nodup_map 8 := fun h =>
  absurd (@h ℕ ℕ (fun n => min n 1) {1} (by decide) 1 (by simp) 2 rfl) (by decide)

-- `Multiset.inj_on_of_nodup_map` idx 9: necessary (f = id, s = {0,1}, x = 0, y = 1)
theorem c7_174 : ¬ drop0% Multiset.inj_on_of_nodup_map 9 := fun h =>
  absurd (@h ℕ ℕ id {0, 1} (by decide) 0 (by simp) 1 (by simp)) (by decide)

-- `Multiset.map_eq_map_of_bij_of_nodup` idx 7: necessary (s = {0,0}, t = {0}, i = id, f = g = id)
theorem c7_175 : ¬ drop0% Multiset.map_eq_map_of_bij_of_nodup 7 := fun h =>
  absurd (@h ℕ ℕ ℕ id id {0, 0} {0} (by decide) (fun a _ => a) (fun a ha => by simp_all)
    (fun _ _ _ _ h => h) (fun b hb => ⟨0, by simp, by simp_all⟩) (fun _ _ => rfl)) (by decide)

-- `Multiset.map_eq_map_of_bij_of_nodup` idx 8: necessary (s = {0}, t = {0,0}, i = id, f = g = id)
theorem c7_176 : ¬ drop0% Multiset.map_eq_map_of_bij_of_nodup 8 := fun h =>
  absurd (@h ℕ ℕ ℕ id id {0} {0, 0} (by decide) (fun a _ => a) (fun a ha => by simp_all)
    (fun _ _ _ _ h => h) (fun b hb => ⟨0, by simp, by simp_all⟩) (fun _ _ => rfl)) (by decide)

-- `Multiset.map_eq_map_of_bij_of_nodup` idx 10: necessary (s = {0}, t = 0, i = id)
theorem c7_177 : ¬ drop0% Multiset.map_eq_map_of_bij_of_nodup 10 := fun h =>
  absurd (@h ℕ ℕ ℕ id id {0} 0 (by decide) (by decide) (fun a _ => a)
    (fun _ _ _ _ h => h) (fun b hb => by simp at hb) (fun _ _ => rfl)) (by decide)

-- `Multiset.map_eq_map_of_bij_of_nodup` idx 11: necessary (s = {0,1}, t = {0}, i = const 0, f = g = const 0)
theorem c7_178 : ¬ drop0% Multiset.map_eq_map_of_bij_of_nodup 11 := fun h =>
  absurd (@h ℕ ℕ ℕ (fun _ => 0) (fun _ => 0) {0, 1} {0} (by decide) (by decide) (fun _ _ => 0) (fun _ _ => by simp)
    (fun b hb => ⟨0, by simp, by simp_all⟩) (fun _ _ => rfl)) (by decide)

-- `Multiset.map_eq_map_of_bij_of_nodup` idx 12: necessary (s = {0}, t = {0,1}, i = id)
theorem c7_179 : ¬ drop0% Multiset.map_eq_map_of_bij_of_nodup 12 := fun h =>
  absurd (@h ℕ ℕ ℕ id id {0} {0, 1} (by decide) (by decide) (fun a _ => a) (fun a ha => by simp_all)
    (fun _ _ _ _ h => h) (fun _ _ => rfl)) (by decide)

-- `Multiset.map_eq_map_of_bij_of_nodup` idx 13: necessary (s = t = {0}, f = const 1, g = id)
theorem c7_180 : ¬ drop0% Multiset.map_eq_map_of_bij_of_nodup 13 := fun h =>
  absurd (@h ℕ ℕ ℕ (fun _ => 1) id {0} {0} (by decide) (by decide) (fun a _ => a) (fun a ha => ha)
    (fun _ _ _ _ h => h) (fun b hb => ⟨b, hb, rfl⟩)) (by decide)

-- `Multiset.map_fst_le_of_subset_toEnumFinset` idx 4: necessary (m = {0}, s = {(0,0),(0,1)})
theorem c7_181 : ¬ drop0% Multiset.map_fst_le_of_subset_toEnumFinset 4 := fun h =>
  absurd (@h ℕ _ {0} {(0,0), (0,1)}) (by decide)

-- `Multiset.cast_symm_apply_snd` idx 4: necessary (s = 0, t = {0})
theorem c7_182 : ¬ indep0% Multiset.cast_symm_apply_snd 4 := fun h =>
  absurd (@h ℕ _ 0 {0} (Sigma.mk 0 ⟨0, by simp⟩)) (by simp)

-- `Multiset.cast_apply_fst` idx 4: necessary (s = {0}, t = 0)
theorem c7_183 : ¬ indep0% Multiset.cast_apply_fst 4 := fun h =>
  absurd (@h ℕ _ {0} 0 (Sigma.mk 0 ⟨0, by simp⟩)) (by simp)

-- `Multiset.cast_symm_apply_fst` idx 4: necessary (s = 0, t = {0})
theorem c7_184 : ¬ indep0% Multiset.cast_symm_apply_fst 4 := fun h =>
  absurd (@h ℕ _ 0 {0} (Sigma.mk 0 ⟨0, by simp⟩)) (by simp)

-- `Multiset.cast_apply_snd` idx 4: necessary (s = {0}, t = 0)
theorem c7_185 : ¬ indep0% Multiset.cast_apply_snd 4 := fun h =>
  absurd (@h ℕ _ {0} 0 (Sigma.mk 0 ⟨0, by simp⟩)) (by simp)

-- `Multiset.coe_consEquiv_of_ne` idx 5: necessary (x = ⟨v, 0⟩)
theorem c7_186 : ¬ indep0% Multiset.coe_consEquiv_of_ne 5 := fun h =>
  @h ℕ _ 0 0 (Sigma.mk 0 ⟨0, by simp⟩) rfl

-- `Multiset.coe_consEquiv_of_eq_of_eq` idx 5: necessary (m = {1}, v = 0, x = ⟨1, 0⟩: consEquiv x = some _)
theorem c7_187 : ¬ drop0% Multiset.coe_consEquiv_of_eq_of_eq 5 := fun h => by
  have := @h ℕ _ {1} 0 (Sigma.mk 1 ⟨0, by simp⟩) (by simp)
  exact (Option.some_ne_none _).symm (this.symm.trans (Multiset.coe_consEquiv_of_ne _ (by decide)))

-- `Multiset.coe_consEquiv_of_eq_of_eq` idx 6: necessary (m = {0}, v = 0, x = ⟨0, 0⟩: consEquiv x = some _)
theorem c7_188 : ¬ drop0% Multiset.coe_consEquiv_of_eq_of_eq 6 := fun h => by
  have := @h ℕ _ {0} 0 (Sigma.mk 0 ⟨0, by simp⟩) rfl
  exact (Option.some_ne_none _).symm (this.symm.trans (Multiset.coe_consEquiv_of_eq_of_lt _ rfl (by simp)))

-- `Multiset.coe_consEquiv_of_eq_of_lt` idx 5: necessary (m = {0,1}, v = 0, x = ⟨1, 0⟩)
theorem c7_189 : ¬ indep0% Multiset.coe_consEquiv_of_eq_of_lt 5 := fun h =>
  absurd (@h ℕ _ {0, 1} 0 (Sigma.mk 1 ⟨0, by simp⟩) (by simp)) (by decide)

-- `Multiset.coe_consEquiv_of_eq_of_lt` idx 6: necessary (m = 0, v = 0, x = ⟨0, 0⟩)
theorem c7_190 : ¬ indep0% Multiset.coe_consEquiv_of_eq_of_lt 6 := fun h =>
  absurd (@h ℕ _ 0 0 (Sigma.mk 0 ⟨0, by simp⟩) rfl) (by simp)

-- `Multiset.IsDershowitzMannaLT.trans` idx 5: necessary (M = P = {1}, N = {0} in ℕ)
theorem c7_191 : ¬ drop0% Multiset.IsDershowitzMannaLT.trans 5 := fun h =>
  dm_irr {1} (@h ℕ _ {1} {0} {1} dm01)

-- `Multiset.IsDershowitzMannaLT.trans` idx 6: necessary (M = P = {0}, N = {1} in ℕ)
theorem c7_192 : ¬ drop0% Multiset.IsDershowitzMannaLT.trans 6 := fun h =>
  dm_irr {0} (@h ℕ _ {0} {1} {0} dm01)

-- `Multiset.wellFounded_isDershowitzMannaLT` idx 2: necessary (α = ℤ, chain {-n})
theorem c7_193 : ¬ drop0% Multiset.wellFounded_isDershowitzMannaLT 2 := fun h =>
  notWF zc zc_dm (@h ℤ _)

-- `_private.Mathlib.Data.Multiset.DershowitzManna.0.Multiset.isDershowitzMannaLT_of_oneStep` idx 4: necessary (M = N = 0 in ℕ)
theorem c7_194 : ¬ drop0% _private.Mathlib.Data.Multiset.DershowitzManna.«0».Multiset.isDershowitzMannaLT_of_oneStep 4 :=
  fun h => dm_irr 0 (@h ℕ _ 0 0)

-- `_private.Mathlib.Data.Multiset.DershowitzManna.0.Multiset.isDershowitzMannaLT_of_transGen_oneStep` idx 4: necessary (M = N = 0 in ℕ)
theorem c7_195 : ¬ drop0% _private.Mathlib.Data.Multiset.DershowitzManna.«0».Multiset.isDershowitzMannaLT_of_transGen_oneStep 4 :=
  fun h => dm_irr 0 (@h ℕ _ 0 0)

-- `_private.Mathlib.Data.Multiset.DershowitzManna.0.Multiset.isDershowitzMannaLT_singleton_insert` idx 5: necessary (M = {0}, N = 0, a = 0)
theorem c7_196 : ¬ drop0% _private.Mathlib.Data.Multiset.DershowitzManna.«0».Multiset.isDershowitzMannaLT_singleton_insert 5 :=
  fun h => by
    obtain ⟨M', h1 | h2⟩ := @h ℕ _ {0} 0 0
    · exact absurd h1.1 (by simp)
    · exact absurd h2.1 (by simp)

-- `_private.Mathlib.Data.Multiset.DershowitzManna.0.Multiset.acc_oneStep_cons_of_acc_lt` idx 3: necessary (α = ℤ, a = 0, M = 0)
theorem c7_197 : ¬ drop0% _private.Mathlib.Data.Multiset.DershowitzManna.«0».Multiset.acc_oneStep_cons_of_acc_lt 3 :=
  fun h => notAcc zc zc_os (@h ℤ _ (-((0 : ℕ) : ℤ)) 0
    ⟨_, fun y hy => by obtain ⟨X, Y, a, -, h2, -⟩ := hy; exact absurd (congrArg Multiset.card h2) (by simp)⟩)

-- `_private.Mathlib.Data.Multiset.DershowitzManna.0.Multiset.acc_oneStep_of_acc_lt` idx 3: necessary (α = ℤ, M = {0})
theorem c7_198 : ¬ drop0% _private.Mathlib.Data.Multiset.DershowitzManna.«0».Multiset.acc_oneStep_of_acc_lt 3 :=
  fun h => notAcc zc zc_os (@h ℤ _ (zc 0))

-- `_private.Mathlib.Data.Multiset.DershowitzManna.0.Multiset.isDershowitzMannaLT_singleton_wf` idx 2: necessary (α = ℤ, chain {-n})
theorem c7_199 : ¬ drop0% _private.Mathlib.Data.Multiset.DershowitzManna.«0».Multiset.isDershowitzMannaLT_singleton_wf 2 :=
  fun h => notWF zc zc_os (@h ℤ _)

-- `_private.Mathlib.Data.Multiset.DershowitzManna.0.Multiset.transGen_oneStep_of_isDershowitzMannaLT` idx 4: necessary (M = N = 0 in ℕ)
theorem c7_200 : ¬ drop0% _private.Mathlib.Data.Multiset.DershowitzManna.«0».Multiset.transGen_oneStep_of_isDershowitzMannaLT 4 :=
  fun h => by
    have := @h ℕ _ 0 0
    cases this with
    | single hs => obtain ⟨X, Y, a, -, h2, -⟩ := hs; exact absurd (congrArg Multiset.card h2) (by simp)
    | tail _ hs => obtain ⟨X, Y, a, -, h2, -⟩ := hs; exact absurd (congrArg Multiset.card h2) (by simp)

-- `Matrix.ext_addMonoidHom_iff` idx 6: necessary (m = ℕ, n = Unit over ℤ: quotient by finitely supported columns)
theorem c7_201 : ¬ drop0% Matrix.ext_addMonoidHom_iff 6 := fun h =>
  φc_ne ((@h ℕ Unit ℤ Q _ _ _ _ _ φc 0).2 φc_comp)

-- `Matrix.ext_addMonoidHom_iff` idx 7: necessary (m = Unit, n = ℕ over ℤ: quotient by finitely supported rows)
theorem c7_202 : ¬ drop0% Matrix.ext_addMonoidHom_iff 7 := fun h =>
  φr_ne ((@h Unit ℕ ℤ Q _ _ _ _ _ φr 0).2 φr_comp)

-- `Matrix.ext_addMonoidHom` idx 6: necessary (m = ℕ, n = Unit over ℤ: quotient by finitely supported columns)
theorem c7_203 : ¬ drop0% Matrix.ext_addMonoidHom 6 := fun h =>
  φc_ne (@h ℕ Unit ℤ Q _ _ _ _ _ φc 0 φc_comp)

-- `Matrix.ext_addMonoidHom` idx 7: necessary (m = Unit, n = ℕ over ℤ: quotient by finitely supported rows)
theorem c7_204 : ¬ drop0% Matrix.ext_addMonoidHom 7 := fun h =>
  φr_ne (@h Unit ℕ ℤ Q _ _ _ _ _ φr 0 φr_comp)

-- `Matrix.ext_linearMap_iff` idx 7: necessary (m = ℕ, n = Unit, R = ℤ: quotient by finitely supported columns)
theorem c7_205 : ¬ drop0% Matrix.ext_linearMap_iff 7 := fun h =>
  φc_lne ((@h ℕ Unit ℤ ℤ Q _ _ _ _ _ _ _ _ φc.toIntLinearMap 0).2 φc_lcomp)

-- `Matrix.ext_linearMap_iff` idx 8: necessary (m = Unit, n = ℕ, R = ℤ: quotient by finitely supported rows)
theorem c7_206 : ¬ drop0% Matrix.ext_linearMap_iff 8 := fun h =>
  φr_lne ((@h Unit ℕ ℤ ℤ Q _ _ _ _ _ _ _ _ φr.toIntLinearMap 0).2 φr_lcomp)

-- `Matrix.ext_linearMap` idx 7: necessary (m = ℕ, n = Unit, R = ℤ: quotient by finitely supported columns)
theorem c7_207 : ¬ drop0% Matrix.ext_linearMap 7 := fun h =>
  φc_lne (@h ℕ Unit ℤ ℤ Q _ _ _ _ _ _ _ _ φc.toIntLinearMap 0 φc_lcomp)

-- `Matrix.ext_linearMap` idx 8: necessary (m = Unit, n = ℕ, R = ℤ: quotient by finitely supported rows)
theorem c7_208 : ¬ drop0% Matrix.ext_linearMap 8 := fun h =>
  φr_lne (@h Unit ℕ ℤ ℤ Q _ _ _ _ _ _ _ _ φr.toIntLinearMap 0 φr_lcomp)

-- `IsStablyFiniteRing.of_injective` idx 6: necessary (shift operators E inject into the stably finite E → ZMod 2 by indicators)
theorem c7_209 : ¬ drop0% IsStablyFiniteRing.of_injective 6 := fun h => by
  classical
  refine E_nSF (@h E (E → ZMod 2) (FW E (E → ZMod 2)) _ _ _ ⟨fun e e' => if e = e' then 1 else 0⟩ ?_ (piSF E))
  intro e e' hee
  have := congrFun hee e'
  change (if e = e' then (1 : ZMod 2) else 0) = if e' = e' then 1 else 0 at this
  by_contra hne; simp [hne] at this

-- `_private.Mathlib.Data.Multiset.DershowitzManna.0.Multiset.acc_oneStep_cons_of_acc_lt` idx 5: necessary (α = ℤ ⊕ Unit, a = inr (), M = {inl 0})
theorem c7_210 : ¬ drop0% _private.Mathlib.Data.Multiset.DershowitzManna.«0».Multiset.acc_oneStep_cons_of_acc_lt 5 :=
  fun h => notAcc zu zu_os (@h ZU _ (Sum.inr ()) accInr {Sum.inl (-((0 : ℕ) : ℤ))})

-- `Multiset.naturality` idx 4: necessary (G = StateM ℕ, H = Const PUnit, eta = const)
theorem c7_211 : ¬ indep0% Multiset.naturality 4 := fun h =>
  nCA (@h (StateM ℕ) (Functor.Const PUnit) _ _ cCA
    (ApplicativeTransformation.mk (fun _ _ => PUnit.unit) (fun _ => rfl) (fun _ _ => rfl)) ℕ ℕ (fun _ => pure 0) 0)

namespace W2c7

/-- ZMod 2 × (ℕ → ZMod 2) as a unitization of the bilinear product x * y = (x 0 * y 1) • cB:
    a non-associative semiring with (1, e₀) * (1, e₁) = 1 but (1, e₁) * (1, e₀) ≠ 1 -/
def SP := ZMod 2 × (ℕ → ZMod 2)
def cB : ℕ → ZMod 2 := fun n => if n ≤ 1 then 1 else 0
def spMul (p q : ZMod 2 × (ℕ → ZMod 2)) : ZMod 2 × (ℕ → ZMod 2) :=
  (p.1 * q.1, fun n => p.1 * q.2 n + q.1 * p.2 n + p.2 0 * q.2 1 * cB n)
abbrev P2 := ZMod 2 × (ℕ → ZMod 2)
theorem sp_ld (p q r : P2) : spMul p (q + r) = spMul p q + spMul p r :=
  Prod.ext (by simp [spMul]; ring) (funext fun n => by simp [spMul]; ring)
theorem sp_rd (p q r : P2) : spMul (p + q) r = spMul p r + spMul q r :=
  Prod.ext (by simp [spMul]; ring) (funext fun n => by simp [spMul]; ring)
theorem sp_zm (p : P2) : spMul 0 p = 0 := Prod.ext (by simp [spMul]) (funext fun n => by simp [spMul])
theorem sp_mz (p : P2) : spMul p 0 = 0 := Prod.ext (by simp [spMul]) (funext fun n => by simp [spMul])
theorem sp_om (p : P2) : spMul ((1 : ZMod 2), (0 : ℕ → ZMod 2)) p = p :=
  Prod.ext (by simp [spMul]) (funext fun n => by simp [spMul])
theorem sp_mo (p : P2) : spMul p ((1 : ZMod 2), (0 : ℕ → ZMod 2)) = p :=
  Prod.ext (by simp [spMul]) (funext fun n => by simp [spMul])
instance : NonAssocSemiring SP :=
  { (inferInstance : AddCommMonoid P2) with
    mul := spMul
    one := ((1 : ZMod 2), (0 : ℕ → ZMod 2))
    natCast := fun n => ((n : ZMod 2), (0 : ℕ → ZMod 2))
    natCast_zero := Prod.ext Nat.cast_zero rfl
    natCast_succ := fun n => Prod.ext (Nat.cast_succ n) (funext fun _ => (add_zero (0 : ZMod 2)).symm)
    left_distrib := sp_ld
    right_distrib := sp_rd
    zero_mul := sp_zm
    mul_zero := sp_mz
    one_mul := sp_om
    mul_one := sp_mo }

def sp0 : SP := ((1 : ZMod 2), fun n => if n = 0 then 1 else 0)
def sp1 : SP := ((1 : ZMod 2), fun n => if n = 1 then 1 else 0)
theorem sp01 : sp0 * sp1 = 1 := by
  show spMul sp0 sp1 = ((1 : ZMod 2), (0 : ℕ → ZMod 2))
  refine Prod.ext (by simp [spMul, sp0, sp1]) (funext fun n => ?_)
  rcases n with _ | _ | n <;> simp [spMul, cB, sp0, sp1] <;> decide
theorem sp10 : sp1 * sp0 ≠ 1 := fun h => by
  have : spMul sp1 sp0 = ((1 : ZMod 2), (0 : ℕ → ZMod 2)) := h
  have := congrFun (congrArg Prod.snd this) 0
  revert this; simp [spMul, cB, sp0, sp1]
theorem SP_nSF : ¬ IsStablyFiniteRing SP := fun h => sp10 (mul_eq_one_symm sp01)

/-- head/tail bijection ℕ → ZMod 2 ≃ SP -/
def eSP : (ℕ → ZMod 2) ≃ SP where
  toFun v := (v 0, fun n => v (n+1))
  invFun p n := Nat.casesOn n (Prod.fst p) (fun m => Prod.snd p m)
  left_inv v := funext fun n => by cases n <;> rfl
  right_inv p := rfl

end W2c7

-- `RingEquiv.isStablyFiniteRing_iff` idx 6: necessary (pointwise ℕ → ZMod 2 is stably finite; head/tail bijection to a non-Dedekind-finite unitization SP)
theorem c7_212 : ¬ drop0% RingEquiv.isStablyFiniteRing_iff 6 := fun h =>
  SP_nSF ((@h (ℕ → ZMod 2) SP ((ℕ → ZMod 2) ≃ SP) _ _ _ eSP).1 (piSF ℕ))
