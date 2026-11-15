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
namespace W3c0
/-- ℤ with the partial order 2 < 0 < 1 (other integers isolated): ZeroLEOneClass, CharZero, not AddLeftMono. -/
def Z2 := ℤ
def Z2.val : Z2 → ℤ := id
instance : AddCommMonoidWithOne Z2 := inferInstanceAs (AddCommMonoidWithOne ℤ)
instance : CharZero Z2 := inferInstanceAs (CharZero ℤ)
def Z2.R (a b : ℤ) : Prop := a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 2 ∧ (b = 0 ∨ b = 1))
instance : PartialOrder Z2 where
  le a b := Z2.R a.val b.val
  le_refl a := Or.inl rfl
  le_trans a b c := by intro h1 h2; unfold Z2.R at *; omega
  le_antisymm a b := by intro h1 h2; unfold Z2.R at *; change a.val = b.val; omega
instance (a b : ℤ) : Decidable (Z2.R a b) := by unfold Z2.R; infer_instance
instance : DecidableRel (α := Z2) (· ≤ ·) := fun a b => inferInstanceAs (Decidable (Z2.R a.val b.val))
instance : DecidableRel (α := Z2) (· < ·) := fun a b => inferInstanceAs (Decidable (a ≤ b ∧ ¬ b ≤ a))
instance : ZeroLEOneClass Z2 := ⟨Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
theorem z2_not_mono : ¬ AddLeftMono Z2 := fun h => by
  have := @CovariantClass.elim Z2 Z2 (· + ·) (· ≤ ·) h 1 0 1 zero_le_one
  revert this; decide +kernel
/-- ℤ with the reversed order: AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass. -/
def RZ := ℤ
instance : CommRing RZ := inferInstanceAs (CommRing ℤ)
instance : LinearOrder RZ := inferInstanceAs (LinearOrder ℤᵒᵈ)
instance : AddLeftMono RZ := inferInstanceAs (AddLeftMono ℤᵒᵈ)
instance : CharZero RZ := inferInstanceAs (CharZero ℤ)
instance : NeZero (1:RZ) := ⟨one_ne_zero (α := ℤ)⟩
theorem rz_not_zlo : ¬ ZeroLEOneClass RZ := fun h => by
  have := @zero_le_one RZ _ _ _ h
  revert this; decide +kernel
instance : AddLeftMono Unit := ⟨fun _ _ _ _ => le_rfl⟩
instance : ZeroLEOneClass Unit := ⟨le_rfl⟩
theorem unit_not_cz : ¬ CharZero Unit := fun h => by
  have := @Nat.cast_injective Unit _ h 0 1 (Subsingleton.elim _ _)
  omega
theorem pw1 {α : Type*} (r : α → α → Prop) (a : α) : Multiset.Pairwise r ({a} : Multiset α) := ⟨[a], rfl, by simp⟩
/-- no pair-list of x, y is r-pairwise when r fails on all four pairs -/
theorem np2 {α : Type*} {r : α → α → Prop} {x y : α} (h1 : ¬ r x y) (h2 : ¬ r y x) (h3 : ¬ r x x) (h4 : ¬ r y y) :
    ¬ Multiset.Pairwise r ({x, y} : Multiset α) := by
  rintro ⟨l, hl, hp⟩
  have hperm : List.Perm [x, y] l := Multiset.coe_eq_coe.1 hl
  have hlen := hperm.length_eq
  match l, hperm, hp, hlen with
  | [a, b], hperm, hp, _ =>
    have ha : a ∈ [x, y] := hperm.symm.subset (by simp)
    have hb : b ∈ [x, y] := hperm.symm.subset (by simp)
    have hab : r a b := by simpa using hp
    simp at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> contradiction
/-- rock-paper-scissors on Fin 3 plus reflexivity: total, antisymmetric, not transitive -/
def rps (a b : Fin 3) : Prop := a = b ∨ b = a + 1
instance : DecidableRel rps := fun a b => by unfold rps; infer_instance
instance : Std.Antisymm rps := ⟨by decide⟩
instance : Std.Total rps := ⟨by decide⟩
theorem rps_not_trans : ¬ IsTrans (Fin 3) rps := fun h => absurd (h.trans 0 1 2 (by decide) (by decide)) (by decide)
def topB (_ _ : Bool) : Prop := True
instance : DecidableRel topB := fun _ _ => instDecidableTrue
instance : IsTrans Bool topB := ⟨fun _ _ _ _ _ => trivial⟩
instance : Std.Total topB := ⟨fun _ _ => Or.inl trivial⟩
theorem topB_not_antisymm : ¬ Std.Antisymm topB := fun h => absurd (h.antisymm true false trivial trivial) (by decide)
def eqB (a b : Bool) : Prop := a = b
instance : DecidableRel eqB := fun a b => by unfold eqB; infer_instance
instance : IsTrans Bool eqB := ⟨fun _ _ _ h1 h2 => h1.trans h2⟩
instance : Std.Antisymm eqB := ⟨fun _ _ h _ => h⟩
theorem eqB_not_total : ¬ Std.Total eqB := fun h => by have := h.total true false; revert this; decide
def leN (a b : ℕ) : Prop := a ≤ b
instance : DecidableRel leN := fun a b => Nat.decLe a b
instance leN_trans : IsTrans ℕ leN := ⟨fun _ _ _ h1 h2 => Nat.le_trans h1 h2⟩
instance leN_anti : Std.Antisymm leN := ⟨fun _ _ h1 h2 => Nat.le_antisymm h1 h2⟩
instance leN_total : Std.Total leN := ⟨fun a b => Nat.le_total a b⟩
def geN (a b : ℕ) : Prop := b ≤ a
instance : DecidableRel geN := fun a b => Nat.decLe b a
instance geN_trans : IsTrans ℕ geN := ⟨fun _ _ _ h1 h2 => Nat.le_trans h2 h1⟩
instance geN_anti : Std.Antisymm geN := ⟨fun _ _ h1 h2 => Nat.le_antisymm h2 h1⟩
instance geN_total : Std.Total geN := ⟨fun a b => Nat.le_total b a⟩
def topN (_ _ : ℕ) : Prop := True
instance : IsTrans ℕ topN := ⟨fun _ _ _ _ _ => trivial⟩
theorem rel_ss {α β : Type*} {r : α → β → Prop} {a : α} {b : β} : Multiset.Rel r {a} {b} ↔ r a b := by
  constructor
  · intro h
    rw [show ({a} : Multiset α) = a ::ₘ 0 from rfl, Multiset.rel_cons_left] at h
    obtain ⟨b', bs', hr, h0, he⟩ := h
    rw [Multiset.rel_zero_left] at h0; subst h0
    rw [show ({b} : Multiset β) = b ::ₘ 0 from rfl, Multiset.cons_inj_left] at he
    exact he ▸ hr
  · intro h; exact Multiset.Rel.cons h Multiset.Rel.zero
/-- bare FunLike wrapper (no hom structure) -/
structure FW (α β : Type) where
  toFun : α → β
instance (α β : Type) : FunLike (FW α β) α β where
  coe := FW.toFun
  coe_injective := by intro f g h; cases f; cases g; cases h; rfl
def F2 := ZMod 2
instance : DecidableEq F2 := inferInstanceAs (DecidableEq (ZMod 2))
noncomputable instance : Field F2 := IsField.toField (R := ZMod 2) ⟨⟨0, 1, by decide⟩, mul_comm,
  by intro a h; exact ⟨a, by revert a; decide⟩⟩
theorem F2_two : ((2:ℕ):F2) = 0 := by decide
def mA : Matrix (Fin 2) (Fin 2) ℕ := !![1, 0; 0, 0]
def mB : Matrix (Fin 2) (Fin 2) ℕ := !![0, 1; 0, 0]
theorem ncAB : ¬ Commute mA mB := fun hc => by
  have := congrFun (congrFun hc 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, mA, mB] at this
/-- n ↦ (0 if n = 0 else 1) as a monoid-with-zero hom on ℕ -/
def sgnHom : ℕ →*₀ ℕ where
  toFun n := if n = 0 then 0 else 1
  map_zero' := rfl
  map_one' := rfl
  map_mul' a b := by by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]
/-- Pi.cons over {0} at 0 forgets its tail: every point of 0 ::ₘ {0} is 0 -/
theorem cons_const (b : Bool) (f g : ∀ a ∈ ({0} : Multiset ℕ), (fun _ => Bool) a) :
    Multiset.Pi.cons {0} 0 b f = Multiset.Pi.cons {0} 0 b g := by
  funext a' ha'
  have : a' = 0 := by simpa using ha'
  subst this; simp [Multiset.Pi.cons_same]
theorem half_num : (1/2 : ℚ≥0).num = 1 := by decide +kernel
theorem half_den : (1/2 : ℚ≥0).den = 2 := by decide +kernel
theorem half0 : ((1/2 : ℚ≥0) : F2) = 0 := by
  rw [NNRat.cast_def, half_num, half_den, F2_two, div_zero]
/-- ℚ with the order pulled back along the swap 1/2 ↔ 11/2 (fixes every integer): a field with a
linear order and floor/ceil (FloorSemiring and FloorRing) that is not an ordered ring; ⌊1/2⌋ = 5. -/
def sw1 (x : ℚ) : ℚ := if x = 1/2 then 11/2 else if x = 11/2 then 1/2 else x
theorem sw1_sw1 (x : ℚ) : sw1 (sw1 x) = x := by
  unfold sw1; split_ifs <;> first | rfl | (subst_vars; norm_num at *)
theorem sw1_int (z : ℤ) : sw1 z = z := by
  have h1 : (z : ℚ) ≠ 1/2 := by
    intro h; have h2 : (2 * z : ℚ) = 1 := by rw [h]; norm_num
    norm_cast at h2; omega
  have h3 : (z : ℚ) ≠ 11/2 := by
    intro h; have h2 : (2 * z : ℚ) = 11 := by rw [h]; norm_num
    norm_cast at h2; omega
  unfold sw1; simp only [h1, h3, ↓reduceIte]
theorem sw1_nat (n : ℕ) : sw1 n = n := by exact_mod_cast sw1_int n
def K1 := ℚ
def K1.val : K1 → ℚ := id
instance : Field K1 := inferInstanceAs (Field ℚ)
instance : LinearOrder K1 := LinearOrder.lift' (fun x : K1 => sw1 x.val) (fun a b h => by
  have := congrArg sw1 h; simp only [sw1_sw1] at this; exact this)
theorem k1_le (a b : K1) : a ≤ b ↔ sw1 a.val ≤ sw1 b.val := Iff.rfl
theorem k1_lt (a b : K1) : a < b ↔ sw1 a.val < sw1 b.val := Iff.rfl
theorem k1_natCast (n : ℕ) : (n : K1).val = n := rfl
theorem k1_intCast (z : ℤ) : (z : K1).val = z := rfl
theorem k1_zero : (0 : K1).val = ((0 : ℕ) : ℚ) := rfl
instance : FloorSemiring K1 where
  floor x := ⌊sw1 x.val⌋₊
  ceil x := ⌈sw1 x.val⌉₊
  floor_of_neg {x} hx := by
    rw [k1_lt, k1_zero, sw1_nat] at hx; exact Nat.floor_of_nonpos (by exact_mod_cast hx.le)
  gc_floor {x n} hx := by
    rw [k1_le, k1_zero, sw1_nat] at hx
    show n ≤ ⌊sw1 x.val⌋₊ ↔ sw1 (n : K1).val ≤ sw1 x.val
    rw [k1_natCast, sw1_nat, Nat.le_floor_iff (by exact_mod_cast hx)]
  gc_ceil x n := by
    show ⌈sw1 x.val⌉₊ ≤ n ↔ sw1 x.val ≤ sw1 (n : K1).val
    rw [k1_natCast, sw1_nat, Nat.ceil_le]
instance : FloorRing K1 where
  floor x := ⌊sw1 x.val⌋
  ceil x := ⌈sw1 x.val⌉
  gc_coe_floor z x := by
    show sw1 (z : K1).val ≤ sw1 x.val ↔ z ≤ ⌊sw1 x.val⌋
    rw [k1_intCast, sw1_int, Int.le_floor]
  gc_ceil_coe x z := by
    show ⌈sw1 x.val⌉ ≤ z ↔ sw1 x.val ≤ sw1 (z : K1).val
    rw [k1_intCast, sw1_int, Int.ceil_le]
/-- ℚ with the order pulled back along the swap -1 ↔ 11/2 (fixes every natural number): a field
with a linear order and a FloorSemiring that is not an ordered ring; ⌈-1⌉₊ = 6. -/
def sw2 (x : ℚ) : ℚ := if x = -1 then 11/2 else if x = 11/2 then -1 else x
theorem sw2_sw2 (x : ℚ) : sw2 (sw2 x) = x := by
  unfold sw2; split_ifs <;> first | rfl | (subst_vars; norm_num at *)
theorem sw2_nat (n : ℕ) : sw2 n = n := by
  have h1 : (n : ℚ) ≠ -1 := by
    intro h; have : (0:ℚ) ≤ n := Nat.cast_nonneg n; linarith
  have h3 : (n : ℚ) ≠ 11/2 := by
    intro h; have h2 : (2 * n : ℚ) = 11 := by rw [h]; norm_num
    norm_cast at h2; omega
  unfold sw2; simp only [h1, h3, ↓reduceIte]
def K2 := ℚ
def K2.val : K2 → ℚ := id
instance : Field K2 := inferInstanceAs (Field ℚ)
instance : LinearOrder K2 := LinearOrder.lift' (fun x : K2 => sw2 x.val) (fun a b h => by
  have := congrArg sw2 h; simp only [sw2_sw2] at this; exact this)
theorem k2_le (a b : K2) : a ≤ b ↔ sw2 a.val ≤ sw2 b.val := Iff.rfl
theorem k2_lt (a b : K2) : a < b ↔ sw2 a.val < sw2 b.val := Iff.rfl
theorem k2_natCast (n : ℕ) : (n : K2).val = n := rfl
theorem k2_zero : (0 : K2).val = ((0 : ℕ) : ℚ) := rfl
instance : FloorSemiring K2 where
  floor x := ⌊sw2 x.val⌋₊
  ceil x := ⌈sw2 x.val⌉₊
  floor_of_neg {x} hx := by
    rw [k2_lt, k2_zero, sw2_nat] at hx; exact Nat.floor_of_nonpos (by exact_mod_cast hx.le)
  gc_floor {x n} hx := by
    rw [k2_le, k2_zero, sw2_nat] at hx
    show n ≤ ⌊sw2 x.val⌋₊ ↔ sw2 (n : K2).val ≤ sw2 x.val
    rw [k2_natCast, sw2_nat, Nat.le_floor_iff (by exact_mod_cast hx)]
  gc_ceil x n := by
    show ⌈sw2 x.val⌉₊ ≤ n ↔ sw2 x.val ≤ sw2 (n : K2).val
    rw [k2_natCast, sw2_nat, Nat.ceil_le]
theorem sortA : ({0,1} : Multiset ℕ).sort leN = [0,1] := by
  rw [show ({0,1} : Multiset ℕ) = 0 ::ₘ {1} from rfl, Multiset.sort_cons 0 {1} leN (by simp [leN]), Multiset.sort_singleton]
theorem sortB : ({0,1} : Multiset ℕ).sort geN = [1,0] := by
  rw [show ({0,1} : Multiset ℕ) = 1 ::ₘ {0} from Multiset.cons_swap 0 1 0, Multiset.sort_cons 1 {0} geN (by simp [geN]), Multiset.sort_singleton]
theorem sortC : (1 ::ₘ {0} : Multiset ℕ).sort leN = [0,1] := by
  rw [show (1 ::ₘ {0} : Multiset ℕ) = {0,1} from Multiset.cons_swap 1 0 0]; exact sortA
end W3c0
open W3c0

-- `Nat.cast_nonneg'` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (n = 2))
theorem c0_1 : ¬ drop0% Nat.cast_nonneg' 3 := fun h => absurd (h (α := Z2) (n := 2)) (by decide +kernel)

-- `Nat.cast_nonneg'` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (n = 1))
theorem c0_2 : ¬ drop0% Nat.cast_nonneg' 4 := fun h => absurd (h (α := RZ) (n := 1)) (by decide +kernel)

-- `Nat.ofNat_nonneg'` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (n = 2))
theorem c0_3 : ¬ drop0% Nat.ofNat_nonneg' 3 := fun h => absurd (h (α := Z2) (n := 2)) (by decide +kernel)

-- `Nat.ofNat_nonneg'` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (n = 2))
theorem c0_4 : ¬ drop0% Nat.ofNat_nonneg' 4 := fun h => absurd (h (α := RZ) (n := 2)) (by decide +kernel)

-- `Nat.cast_add_one_pos` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (n = 0))
theorem c0_5 : ¬ drop0% Nat.cast_add_one_pos 4 := fun h => absurd (h (α := RZ) (n := 0)) (by decide +kernel)

-- `Nat.cast_add_one_pos` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (n = 0))
theorem c0_6 : ¬ drop0% Nat.cast_add_one_pos 5 := fun h => absurd (h (α := Unit) (n := 0)) (by decide +kernel)

-- `Nat.castOrderEmbedding_apply` idx 3: necessary (alpha = Z2 has ZeroLEOneClass, CharZero but not AddLeftMono)
theorem c0_7 : ¬ indep0% Nat.castOrderEmbedding_apply 3 := fun h => z2_not_mono (h (α := Z2))

-- `Nat.castOrderEmbedding_apply` idx 4: necessary (alpha = RZ has AddLeftMono, CharZero but not ZeroLEOneClass)
theorem c0_8 : ¬ indep0% Nat.castOrderEmbedding_apply 4 := fun h => rz_not_zlo (h (α := RZ))

-- `Nat.castOrderEmbedding_apply` idx 5: necessary (alpha = Unit has AddLeftMono, ZeroLEOneClass but not CharZero)
theorem c0_9 : ¬ indep0% Nat.castOrderEmbedding_apply 5 := fun h => unit_not_cz (h (α := Unit))

-- `Nat.cast_le` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (m = 2) (n = 1))
theorem c0_10 : ¬ drop0% Nat.cast_le 3 := fun h => absurd (h (α := Z2) (m := 2) (n := 1)) (by decide +kernel)

-- `Nat.cast_le` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (m = 0) (n = 1))
theorem c0_11 : ¬ drop0% Nat.cast_le 4 := fun h => absurd (h (α := RZ) (m := 0) (n := 1)) (by decide +kernel)

-- `Nat.cast_le` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (m = 1) (n = 0))
theorem c0_12 : ¬ drop0% Nat.cast_le 5 := fun h => absurd (h (α := Unit) (m := 1) (n := 0)) (by decide +kernel)

-- `Nat.cast_lt` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (m = 2) (n = 1))
theorem c0_13 : ¬ drop0% Nat.cast_lt 3 := fun h => absurd (h (α := Z2) (m := 2) (n := 1)) (by decide +kernel)

-- `Nat.cast_lt` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (m = 0) (n = 1))
theorem c0_14 : ¬ drop0% Nat.cast_lt 4 := fun h => absurd (h (α := RZ) (m := 0) (n := 1)) (by decide +kernel)

-- `Nat.cast_lt` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (m = 0) (n = 1))
theorem c0_15 : ¬ drop0% Nat.cast_lt 5 := fun h => absurd (h (α := Unit) (m := 0) (n := 1)) (by decide +kernel)

-- `Nat.one_lt_cast` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (n = 2))
theorem c0_16 : ¬ drop0% Nat.one_lt_cast 3 := fun h => absurd (h (α := Z2) (n := 2)) (by decide +kernel)

-- `Nat.one_lt_cast` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (n = 2))
theorem c0_17 : ¬ drop0% Nat.one_lt_cast 4 := fun h => absurd (h (α := RZ) (n := 2)) (by decide +kernel)

-- `Nat.one_lt_cast` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (n = 2))
theorem c0_18 : ¬ drop0% Nat.one_lt_cast 5 := fun h => absurd (h (α := Unit) (n := 2)) (by decide +kernel)

-- `Nat.one_le_cast` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (n = 2))
theorem c0_19 : ¬ drop0% Nat.one_le_cast 3 := fun h => absurd (h (α := Z2) (n := 2)) (by decide +kernel)

-- `Nat.one_le_cast` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (n = 2))
theorem c0_20 : ¬ drop0% Nat.one_le_cast 4 := fun h => absurd (h (α := RZ) (n := 2)) (by decide +kernel)

-- `Nat.one_le_cast` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (n = 0))
theorem c0_21 : ¬ drop0% Nat.one_le_cast 5 := fun h => absurd (h (α := Unit) (n := 0)) (by decide +kernel)

-- `Nat.one_le_cast_iff_ne_zero` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (n = 2))
theorem c0_22 : ¬ drop0% Nat.one_le_cast_iff_ne_zero 3 := fun h => absurd (h (α := Z2) (n := 2)) (by decide +kernel)

-- `Nat.one_le_cast_iff_ne_zero` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (n = 2))
theorem c0_23 : ¬ drop0% Nat.one_le_cast_iff_ne_zero 4 := fun h => absurd (h (α := RZ) (n := 2)) (by decide +kernel)

-- `Nat.one_le_cast_iff_ne_zero` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (n = 0))
theorem c0_24 : ¬ drop0% Nat.one_le_cast_iff_ne_zero 5 := fun h => absurd (h (α := Unit) (n := 0)) (by decide +kernel)

-- `Nat.cast_lt_one` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (n = 2))
theorem c0_25 : ¬ drop0% Nat.cast_lt_one 3 := fun h => absurd (h (α := Z2) (n := 2)) (by decide +kernel)

-- `Nat.cast_lt_one` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (n = 0))
theorem c0_26 : ¬ drop0% Nat.cast_lt_one 4 := fun h => absurd (h (α := RZ) (n := 0)) (by decide +kernel)

-- `Nat.cast_lt_one` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (n = 0))
theorem c0_27 : ¬ drop0% Nat.cast_lt_one 5 := fun h => absurd (h (α := Unit) (n := 0)) (by decide +kernel)

-- `Nat.cast_le_one` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (n = 2))
theorem c0_28 : ¬ drop0% Nat.cast_le_one 3 := fun h => absurd (h (α := Z2) (n := 2)) (by decide +kernel)

-- `Nat.cast_le_one` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (n = 2))
theorem c0_29 : ¬ drop0% Nat.cast_le_one 4 := fun h => absurd (h (α := RZ) (n := 2)) (by decide +kernel)

-- `Nat.cast_le_one` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (n = 2))
theorem c0_30 : ¬ drop0% Nat.cast_le_one 5 := fun h => absurd (h (α := Unit) (n := 2)) (by decide +kernel)

-- `Nat.cast_nonpos` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (n = 2))
theorem c0_31 : ¬ drop0% Nat.cast_nonpos 3 := fun h => absurd (h (α := Z2) (n := 2)) (by decide +kernel)

-- `Nat.cast_nonpos` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (n = 1))
theorem c0_32 : ¬ drop0% Nat.cast_nonpos 4 := fun h => absurd (h (α := RZ) (n := 1)) (by decide +kernel)

-- `Nat.cast_nonpos` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (n = 1))
theorem c0_33 : ¬ drop0% Nat.cast_nonpos 5 := fun h => absurd (h (α := Unit) (n := 1)) (by decide +kernel)

-- `Nat.ofNat_le_cast` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (m = 2) (n = 1))
theorem c0_34 : ¬ drop0% Nat.ofNat_le_cast 3 := fun h => absurd (h (α := Z2) (m := 2) (n := 1)) (by decide +kernel)

-- `Nat.ofNat_le_cast` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (m = 2) (n = 3))
theorem c0_35 : ¬ drop0% Nat.ofNat_le_cast 4 := fun h => absurd (h (α := RZ) (m := 2) (n := 3)) (by decide +kernel)

-- `Nat.ofNat_le_cast` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (m = 2) (n = 0))
theorem c0_36 : ¬ drop0% Nat.ofNat_le_cast 5 := fun h => absurd (h (α := Unit) (m := 2) (n := 0)) (by decide +kernel)

-- `Nat.ofNat_lt_cast` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (m = 2) (n = 1))
theorem c0_37 : ¬ drop0% Nat.ofNat_lt_cast 3 := fun h => absurd (h (α := Z2) (m := 2) (n := 1)) (by decide +kernel)

-- `Nat.ofNat_lt_cast` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (m = 2) (n = 3))
theorem c0_38 : ¬ drop0% Nat.ofNat_lt_cast 4 := fun h => absurd (h (α := RZ) (m := 2) (n := 3)) (by decide +kernel)

-- `Nat.ofNat_lt_cast` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (m = 2) (n = 3))
theorem c0_39 : ¬ drop0% Nat.ofNat_lt_cast 5 := fun h => absurd (h (α := Unit) (m := 2) (n := 3)) (by decide +kernel)

-- `Nat.cast_le_ofNat` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (m = 0) (n = 2))
theorem c0_40 : ¬ drop0% Nat.cast_le_ofNat 3 := fun h => absurd (h (α := Z2) (m := 0) (n := 2)) (by decide +kernel)

-- `Nat.cast_le_ofNat` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (m = 0) (n = 2))
theorem c0_41 : ¬ drop0% Nat.cast_le_ofNat 4 := fun h => absurd (h (α := RZ) (m := 0) (n := 2)) (by decide +kernel)

-- `Nat.cast_le_ofNat` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (m = 3) (n = 2))
theorem c0_42 : ¬ drop0% Nat.cast_le_ofNat 5 := fun h => absurd (h (α := Unit) (m := 3) (n := 2)) (by decide +kernel)

-- `Nat.cast_lt_ofNat` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (m = 0) (n = 2))
theorem c0_43 : ¬ drop0% Nat.cast_lt_ofNat 3 := fun h => absurd (h (α := Z2) (m := 0) (n := 2)) (by decide +kernel)

-- `Nat.cast_lt_ofNat` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (m = 0) (n = 2))
theorem c0_44 : ¬ drop0% Nat.cast_lt_ofNat 4 := fun h => absurd (h (α := RZ) (m := 0) (n := 2)) (by decide +kernel)

-- `Nat.cast_lt_ofNat` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (m = 0) (n = 2))
theorem c0_45 : ¬ drop0% Nat.cast_lt_ofNat 5 := fun h => absurd (h (α := Unit) (m := 0) (n := 2)) (by decide +kernel)

-- `Nat.one_lt_ofNat` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (n = 2))
theorem c0_46 : ¬ drop0% Nat.one_lt_ofNat 3 := fun h => absurd (h (α := Z2) (n := 2)) (by decide +kernel)

-- `Nat.one_lt_ofNat` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (n = 2))
theorem c0_47 : ¬ drop0% Nat.one_lt_ofNat 4 := fun h => absurd (h (α := RZ) (n := 2)) (by decide +kernel)

-- `Nat.one_lt_ofNat` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (n = 2))
theorem c0_48 : ¬ drop0% Nat.one_lt_ofNat 5 := fun h => absurd (h (α := Unit) (n := 2)) (by decide +kernel)

-- `Nat.one_le_ofNat` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (n = 2))
theorem c0_49 : ¬ drop0% Nat.one_le_ofNat 3 := fun h => absurd (h (α := Z2) (n := 2)) (by decide +kernel)

-- `Nat.one_le_ofNat` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (n = 2))
theorem c0_50 : ¬ drop0% Nat.one_le_ofNat 4 := fun h => absurd (h (α := RZ) (n := 2)) (by decide +kernel)

-- `Nat.one_le_ofNat` idx 5: removable (1 <= ofNat n follows from Nat.mono_cast (needs only AddLeftMono, ZeroLEOneClass); CharZero unused)
theorem c0_51 : drop% Nat.one_le_ofNat 5 := by
  intro α _ _ _ _ n _
  have := Nat.mono_cast (α := α) (show 1 ≤ n by have := ‹n.AtLeastTwo›.prop; omega)
  rw [Nat.cast_one] at this; exact this

-- `Nat.not_ofNat_le_one` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (n = 2))
theorem c0_52 : ¬ drop0% Nat.not_ofNat_le_one 3 := fun h => absurd (h (α := Z2) (n := 2)) (by decide +kernel)

-- `Nat.not_ofNat_le_one` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (n = 2))
theorem c0_53 : ¬ drop0% Nat.not_ofNat_le_one 4 := fun h => absurd (h (α := RZ) (n := 2)) (by decide +kernel)

-- `Nat.not_ofNat_le_one` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (n = 2))
theorem c0_54 : ¬ drop0% Nat.not_ofNat_le_one 5 := fun h => absurd (h (α := Unit) (n := 2)) (by decide +kernel)

-- `Nat.not_ofNat_lt_one` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (n = 2))
theorem c0_55 : ¬ drop0% Nat.not_ofNat_lt_one 3 := fun h => absurd (h (α := Z2) (n := 2)) (by decide +kernel)

-- `Nat.not_ofNat_lt_one` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (n = 2))
theorem c0_56 : ¬ drop0% Nat.not_ofNat_lt_one 4 := fun h => absurd (h (α := RZ) (n := 2)) (by decide +kernel)

-- `Nat.not_ofNat_lt_one` idx 5: removable (1 <= ofNat n by Nat.mono_cast, so ofNat n < 1 is impossible; CharZero unused)
theorem c0_57 : drop% Nat.not_ofNat_lt_one 5 := by
  intro α _ _ _ _ n _ hlt
  have := Nat.mono_cast (α := α) (show 1 ≤ n by have := ‹n.AtLeastTwo›.prop; omega)
  rw [Nat.cast_one] at this; exact absurd (lt_of_le_of_lt this hlt) (lt_irrefl _)

-- `Nat.ofNat_le` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (m = 2) (n = 3))
theorem c0_58 : ¬ drop0% Nat.ofNat_le 3 := fun h => absurd (h (α := Z2) (m := 2) (n := 3)) (by decide +kernel)

-- `Nat.ofNat_le` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (m = 2) (n = 3))
theorem c0_59 : ¬ drop0% Nat.ofNat_le 4 := fun h => absurd (h (α := RZ) (m := 2) (n := 3)) (by decide +kernel)

-- `Nat.ofNat_le` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (m = 3) (n = 2))
theorem c0_60 : ¬ drop0% Nat.ofNat_le 5 := fun h => absurd (h (α := Unit) (m := 3) (n := 2)) (by decide +kernel)

-- `Nat.ofNat_le` idx 8: necessary (alpha = N, m = 2, n = 0: 0 is not AtLeastTwo)
theorem c0_61 : ¬ indep0% Nat.ofNat_le 8 := fun h => absurd (@h ℕ _ _ _ _ _ 2 0 ⟨le_refl 2⟩) (fun h => by have := h.prop; omega)

-- `Nat.ofNat_le` idx 9: necessary (alpha = N, m = 0, n = 2: 0 is not AtLeastTwo)
theorem c0_62 : ¬ indep0% Nat.ofNat_le 9 := fun h => absurd (@h ℕ _ _ _ _ _ 0 2 ⟨le_refl 2⟩) (fun h => by have := h.prop; omega)

-- `Nat.ofNat_lt` idx 3: necessary (Z2 = Z with partial order 2 < 0 < 1 (ZeroLEOneClass, CharZero, not AddLeftMono), (m = 2) (n = 3))
theorem c0_63 : ¬ drop0% Nat.ofNat_lt 3 := fun h => absurd (h (α := Z2) (m := 2) (n := 3)) (by decide +kernel)

-- `Nat.ofNat_lt` idx 4: necessary (RZ = Z with reversed order (AddLeftMono, CharZero, NeZero 1, not ZeroLEOneClass), (m = 2) (n = 3))
theorem c0_64 : ¬ drop0% Nat.ofNat_lt 4 := fun h => absurd (h (α := RZ) (m := 2) (n := 3)) (by decide +kernel)

-- `Nat.ofNat_lt` idx 5: necessary (alpha = Unit (AddLeftMono, ZeroLEOneClass, not CharZero), (m = 2) (n = 3))
theorem c0_65 : ¬ drop0% Nat.ofNat_lt 5 := fun h => absurd (h (α := Unit) (m := 2) (n := 3)) (by decide +kernel)

-- `Nat.ofNat_lt` idx 8: necessary (alpha = N, m = 2, n = 0: 0 is not AtLeastTwo)
theorem c0_66 : ¬ indep0% Nat.ofNat_lt 8 := fun h => absurd (@h ℕ _ _ _ _ _ 2 0 ⟨le_refl 2⟩) (fun h => by have := h.prop; omega)

-- `Nat.ofNat_lt` idx 9: necessary (alpha = N, m = 0, n = 2: 0 is not AtLeastTwo)
theorem c0_67 : ¬ indep0% Nat.ofNat_lt 9 := fun h => absurd (@h ℕ _ _ _ _ _ 0 2 ⟨le_refl 2⟩) (fun h => by have := h.prop; omega)

-- `instNontrivialOfCharZero` idx 2: necessary (alpha = Unit is a trivial AddMonoidWithOne)
theorem c0_68 : ¬ drop0% instNontrivialOfCharZero 2 := fun h => not_nontrivial Unit (h (α := Unit))

-- `Multiset.Pairwise.forall` idx 3: necessary (r = (<) on N, s = {0,1} (pairwise as [0,1]), a = 1, b = 0)
theorem c0_69 : ¬ drop0% Multiset.Pairwise.forall 3 := fun h => absurd
  (h (r := (· < ·)) (s := ({0, 1} : Multiset ℕ)) (by rw [show ({0, 1} : Multiset ℕ) = ↑[0, 1] from rfl, Multiset.pairwise_coe_iff]; exact ⟨[0,1], List.Perm.refl _, by decide⟩) (a := 1) (by simp) (b := 0) (by simp) (by decide)) (by decide)

-- `Multiset.Pairwise.forall` idx 4: necessary (r = empty relation, s = {0,1}, a = 1, b = 0)
theorem c0_70 : ¬ drop0% Multiset.Pairwise.forall 4 := fun h => absurd
  (h (r := fun (_ _ : ℕ) => False) (s := ({0, 1} : Multiset ℕ)) (a := 1) (by simp) (b := 0) (by simp) (by decide)) id

-- `Multiset.Pairwise.forall` idx 6: necessary (r = empty relation, s = {0}, a = 1 not in s, b = 0)
theorem c0_71 : ¬ drop0% Multiset.Pairwise.forall 6 := fun h => absurd
  (h (r := fun (_ _ : ℕ) => False) (s := ({0} : Multiset ℕ)) (pw1 _ _) (a := 1) (b := 0) (by simp) (by decide)) id

-- `Multiset.Pairwise.forall` idx 8: necessary (r = empty relation, s = {0}, a = 0, b = 1 not in s)
theorem c0_72 : ¬ drop0% Multiset.Pairwise.forall 8 := fun h => absurd
  (h (r := fun (_ _ : ℕ) => False) (s := ({0} : Multiset ℕ)) (pw1 _ _) (a := 0) (by simp) (b := 1) (by decide)) id

-- `Multiset.Pairwise.forall` idx 9: necessary (r = (!=), s = {0}, a = b = 0)
theorem c0_73 : ¬ drop0% Multiset.Pairwise.forall 9 := fun h => absurd
  (h (r := fun (a b : ℕ) => a ≠ b) (s := ({0} : Multiset ℕ)) (pw1 _ _) (a := 0) (by simp) (b := 0) (by simp)) (by simp)

-- `Multiset.Pi.cons_ne` idx 8: necessary (m = 0, a = 0, a' = 1: 1 is not in 0 ::m 0)
theorem c0_74 : ¬ indep0% Multiset.Pi.cons_ne 8 := fun h => absurd
  (h (δ := fun _ : ℕ => True) (m := 0) (a := 0) (a' := 1) (b := trivial) (f := fun _ h => trivial) (by decide)) (by simp)

-- `Multiset.Pi.cons_ne` idx 9: necessary (a = a' = 0)
theorem c0_75 : ¬ indep0% Multiset.Pi.cons_ne 9 := fun h => absurd
  (h (δ := fun _ : ℕ => True) (m := 0) (a := 0) (a' := 0) (b := trivial) (f := fun _ h => trivial) (by simp)) (by simp)

-- `Multiset.Pi.forall_rel_cons_ext` idx 13: necessary (m = 0, a = 0: 1 is not in a ::m m)
theorem c0_76 : ¬ indep0% Multiset.Pi.forall_rel_cons_ext 13 := fun h => absurd
  (h (δ := fun _ : ℕ => True) (m := 0) (a := 0) (r := fun _ _ _ => True) (b₁ := trivial) (b₂ := trivial) (f₁ := fun _ _ => trivial) (f₂ := fun _ _ => trivial) trivial (by simp) 1) (by simp)

-- `Multiset.Pi.forall_rel_cons_ext` idx 10: necessary (m = 0, r = False: the conclusion at a gives r b1 b2)
theorem c0_77 : ¬ drop0% Multiset.Pi.forall_rel_cons_ext 10 := fun h => absurd
  (h (δ := fun _ : ℕ => True) (m := 0) (a := 0) (r := fun _ _ _ => False) (b₁ := trivial) (b₂ := trivial) (f₁ := fun _ _ => trivial) (f₂ := fun _ _ => trivial) (by simp) 0 (by simp)) id

-- `Multiset.Pi.forall_rel_cons_ext` idx 11: necessary (m = {1}, a = 0, r holds only over the point 0: fails at 1)
theorem c0_78 : ¬ drop0% Multiset.Pi.forall_rel_cons_ext 11 := fun h => absurd
  (h (δ := fun _ : ℕ => True) (m := {1}) (a := 0) (r := fun x _ _ => x = 0) (b₁ := trivial) (b₂ := trivial) (f₁ := fun _ _ => trivial) (f₂ := fun _ _ => trivial) rfl 1 (by simp)) (by simp)

-- `Multiset.revzip_powersetAux_lemma` idx 4: necessary (l = [], l' = [{0}]: revzip gives ({0},{0}) but 0 - {0} = 0)
theorem c0_79 : ¬ drop0% Multiset.revzip_powersetAux_lemma 4 := fun h => absurd
  (h (α := ℕ) [] (l' := [{0}])) (by decide)

-- `Disjoint.powersetCard_powersetCard_multiset` idx 3: necessary (s = t = {0}, n = m = 1: both powersetCards contain {0})
theorem c0_80 : ¬ drop0% Disjoint.powersetCard_powersetCard_multiset 3 := fun h => by
  have := h (s := ({0} : Multiset ℕ)) (t := {0}) (n := 1) (m := 1) (Or.inl one_ne_zero)
  rw [Multiset.disjoint_left] at this
  exact this (a := {0}) (by simp [Multiset.mem_powersetCard]) (by simp [Multiset.mem_powersetCard])

-- `Multiset.Nodup.pairwise` idx 3: necessary (r = empty relation, s = {0,1})
theorem c0_81 : ¬ drop0% Multiset.Nodup.pairwise 3 := fun h =>
  np2 id id id id (h (r := fun (_ _ : ℕ) => False) (s := {0, 1}) (by decide))

-- `Multiset.Nodup.pairwise` idx 4: necessary (r = (!=), s = {0,0}: hypothesis vacuous, [0,0] not pairwise)
theorem c0_82 : ¬ drop0% Multiset.Nodup.pairwise 4 := fun h =>
  np2 (x := 0) (y := 0) (by simp) (by simp) (by simp) (by simp) (h (r := fun (a b : ℕ) => a ≠ b) (s := {0, 0}) (by simp))

-- `Multiset.coe_sort` idx 4: necessary (alpha = Fin 3, r = rock-paper-scissors (reflexive, total, antisymmetric, not transitive))
theorem c0_83 : ¬ indep0% Multiset.coe_sort 4 := fun h => rps_not_trans (h (α := Fin 3) [] rps)

-- `Multiset.pairwise_sort` idx 4: necessary (alpha = Fin 3, r = rock-paper-scissors (reflexive, total, antisymmetric, not transitive))
theorem c0_84 : ¬ indep0% Multiset.pairwise_sort 4 := fun h => rps_not_trans (h (α := Fin 3) 0 rps)

-- `Multiset.sort_eq` idx 4: necessary (alpha = Fin 3, r = rock-paper-scissors (reflexive, total, antisymmetric, not transitive))
theorem c0_85 : ¬ indep0% Multiset.sort_eq 4 := fun h => rps_not_trans (h (α := Fin 3) 0 rps)

-- `Multiset.sort_zero` idx 3: necessary (alpha = Fin 3, r = rock-paper-scissors (reflexive, total, antisymmetric, not transitive))
theorem c0_86 : ¬ indep0% Multiset.sort_zero 3 := fun h => rps_not_trans (h (α := Fin 3) rps)

-- `Multiset.sort_singleton` idx 4: necessary (alpha = Fin 3, r = rock-paper-scissors (reflexive, total, antisymmetric, not transitive))
theorem c0_87 : ¬ indep0% Multiset.sort_singleton 4 := fun h => rps_not_trans (h (α := Fin 3) 0 rps)

-- `Multiset.map_sort` idx 6: necessary (alpha = Fin 3, r = rock-paper-scissors, s = 0, r' = (<=) on N)
theorem c0_88 : ¬ indep0% Multiset.map_sort 6 := fun h => rps_not_trans (@h (Fin 3) ℕ (fun _ => 0) 0 rps _ _ _ leN _ leN_trans leN_anti leN_total (by simp))

-- `Multiset.map_sort` idx 7: necessary (r = True on Bool (transitive, total, not antisymmetric), s = 0)
theorem c0_89 : ¬ indep0% Multiset.map_sort 7 := fun h => topB_not_antisymm (@h Bool ℕ (fun _ => 0) 0 topB _ _ _ leN _ leN_trans leN_anti leN_total (by simp))

-- `Multiset.map_sort` idx 11: necessary (r' = rock-paper-scissors on Fin 3, s = 0, r = (<=) on N)
theorem c0_90 : ¬ indep0% Multiset.map_sort 11 := fun h => rps_not_trans (@h ℕ (Fin 3) (fun _ => 0) 0 leN _ leN_trans leN_anti leN_total rps _ _ _ (by simp))

-- `Multiset.map_sort` idx 12: necessary (r' = True on Bool, s = 0)
theorem c0_91 : ¬ indep0% Multiset.map_sort 12 := fun h => topB_not_antisymm (@h ℕ Bool (fun _ => true) 0 leN _ leN_trans leN_anti leN_total topB _ _ _ (by simp))

-- `Multiset.map_sort` idx 13: necessary (r' = (=) on Bool (transitive, antisymmetric, not total), s = 0)
theorem c0_92 : ¬ indep0% Multiset.map_sort 13 := fun h => eqB_not_total (@h ℕ Bool (fun _ => true) 0 leN _ leN_trans leN_anti leN_total eqB _ _ _ (by simp))

-- `Multiset.map_sort` idx 14: necessary (f = id, s = {0,1}, r = (<=), r' = (>=): [0,1] vs [1,0])
theorem c0_93 : ¬ drop0% Multiset.map_sort 14 := fun h => absurd (@h ℕ ℕ id {0, 1} leN _ leN_trans leN_anti leN_total geN _ geN_trans geN_anti geN_total) (by rw [Multiset.map_id, sortA, sortB]; decide)

-- `Multiset.sort_cons` idx 5: necessary (alpha = Fin 3, r = rock-paper-scissors, s = 0)
theorem c0_94 : ¬ indep0% Multiset.sort_cons 5 := fun h => rps_not_trans (h (α := Fin 3) 0 0 rps (by simp))

-- `Multiset.sort_cons` idx 8: necessary (a = 1, s = {0}, r = (<=): sort gives [0,1], not [1,0])
theorem c0_95 : ¬ drop0% Multiset.sort_cons 8 := fun h => absurd (h (α := ℕ) 1 {0} leN) (by rw [sortC, Multiset.sort_singleton]; decide)

-- `Multiset.mem_sort` idx 5: necessary (alpha = Fin 3, r = rock-paper-scissors)
theorem c0_96 : ¬ indep0% Multiset.mem_sort 5 := fun h => rps_not_trans (h (α := Fin 3) (a := 0) (s := 0) rps)

-- `Multiset.length_sort` idx 4: necessary (alpha = Fin 3, r = rock-paper-scissors)
theorem c0_97 : ¬ indep0% Multiset.length_sort 4 := fun h => rps_not_trans (h (α := Fin 3) (s := 0) rps)

-- `Multiset.disjSum_lt_disjSum_of_lt_of_le` idx 7: necessary (s1 = 0 < s2 = {0}, t1 = {0}, t2 = 0: both disjSums have card 1)
theorem c0_98 : ¬ drop0% Multiset.disjSum_lt_disjSum_of_lt_of_le 7 := fun h => absurd
  (Multiset.card_lt_card (h (s₁ := (0 : Multiset ℕ)) (s₂ := {0}) (t₁ := ({0} : Multiset ℕ)) (t₂ := 0) (by simp))) (by simp)

-- `Multiset.disjSum_lt_disjSum_of_le_of_lt` idx 6: necessary (t1 = 0 < t2 = {0}, s1 = {0}, s2 = 0: both disjSums have card 1)
theorem c0_99 : ¬ drop0% Multiset.disjSum_lt_disjSum_of_le_of_lt 6 := fun h => absurd
  (Multiset.card_lt_card (h (s₁ := ({0} : Multiset ℕ)) (s₂ := 0) (t₁ := (0 : Multiset ℕ)) (t₂ := {0}) (by simp))) (by simp)

-- `Multiset.le_inter` idx 5: necessary (s = u = {0}, t = 0)
theorem c0_100 : ¬ drop0% Multiset.le_inter 5 := fun h => absurd (h (s := ({0} : Multiset ℕ)) (t := 0) (u := {0}) (by decide)) (by decide)

-- `Multiset.le_inter` idx 6: necessary (s = t = {0}, u = 0)
theorem c0_101 : ¬ drop0% Multiset.le_inter 6 := fun h => absurd (h (s := ({0} : Multiset ℕ)) (t := {0}) (u := 0) (by decide)) (by decide)

-- `Multiset.disjoint_of_subset_left` idx 4: necessary (s = t = {0}, u = 0)
theorem c0_102 : ¬ drop0% Multiset.disjoint_of_subset_left 4 := fun h => absurd (h (s := ({0} : Multiset ℕ)) (t := {0}) (u := 0) (by simp)) (by simp)

-- `Multiset.disjoint_of_subset_left` idx 5: necessary (s = t = u = {0})
theorem c0_103 : ¬ drop0% Multiset.disjoint_of_subset_left 5 := fun h => absurd (h (s := ({0} : Multiset ℕ)) (t := {0}) (u := {0}) (by simp)) (by simp)

-- `Multiset.disjoint_of_subset_right` idx 4: necessary (s = t = {0}, u = 0)
theorem c0_104 : ¬ drop0% Multiset.disjoint_of_subset_right 4 := fun h => absurd (h (s := ({0} : Multiset ℕ)) (t := {0}) (u := 0) (by simp)) (by simp)

-- `Multiset.disjoint_of_subset_right` idx 5: necessary (s = t = u = {0})
theorem c0_105 : ¬ drop0% Multiset.disjoint_of_subset_right 5 := fun h => absurd (h (s := ({0} : Multiset ℕ)) (t := {0}) (u := {0}) (by simp)) (by simp)

-- `Multiset.add_eq_union_left_of_le` idx 5: necessary (u = t = {0}, s = 0: u + s = u ∪ t but s != t)
theorem c0_106 : ¬ drop0% Multiset.add_eq_union_left_of_le 5 := fun h => absurd (h (s := (0 : Multiset ℕ)) (t := {0}) (u := {0})) (fun hh => absurd (hh.1 (by decide)).2 (by decide))

-- `Multiset.add_eq_union_right_of_le` idx 5: necessary (x = z = {0}, y = 0: x + y = x ∪ z but y != z)
theorem c0_107 : ¬ drop0% Multiset.add_eq_union_right_of_le 5 := fun h => absurd (h (x := ({0} : Multiset ℕ)) (y := 0) (z := {0})) (fun hh => absurd (hh.1 (by decide)).1 (by decide))

-- `Multiset.map_set_pairwise` idx 5: necessary (f = id, m = {0,1}, r = empty relation)
theorem c0_108 : ¬ drop0% Multiset.map_set_pairwise 5 := fun h => absurd
  (h (f := id) (r := fun (_ _ : ℕ) => False) (m := {0, 1}) (x := 0) (by simp) (y := 1) (by simp) (by decide)) id

-- `Multiset.disjoint_of_nodup_add` idx 3: necessary (s = t = {0})
theorem c0_109 : ¬ drop0% Multiset.disjoint_of_nodup_add 3 := fun h => absurd (h (s := ({0} : Multiset ℕ)) (t := {0})) (by simp)

-- `Multiset.Nodup.add_iff` idx 3: necessary (s = {0,0}, t = 0: s + t not nodup but s, t disjoint)
theorem c0_110 : ¬ drop0% Multiset.Nodup.add_iff 3 := fun h => absurd (h (s := ({0, 0} : Multiset ℕ)) (t := 0) (by simp)) (by simp)

-- `Multiset.induction` idx 2: necessary (p = False)
theorem c0_111 : ¬ drop0% Multiset.induction 2 := fun h => h (α := ℕ) (p := fun _ => False) (fun _ _ x => x) 0

-- `Multiset.induction` idx 3: necessary (p s := s = 0, s = {0})
theorem c0_112 : ¬ drop0% Multiset.induction 3 := fun h => absurd (h (α := ℕ) (p := fun s => s = 0) rfl {0}) (by simp)

-- `Multiset.induction_on` idx 3: necessary (p = False)
theorem c0_113 : ¬ drop0% Multiset.induction_on 3 := fun h => h (α := ℕ) (p := fun _ => False) 0 (fun _ _ x => x)

-- `Multiset.induction_on` idx 4: necessary (p s := s = 0, s = {0})
theorem c0_114 : ¬ drop0% Multiset.induction_on 4 := fun h => absurd (h (α := ℕ) (p := fun s => s = 0) {0} rfl) (by simp)

-- `Multiset.induction_on'` idx 3: necessary (p = False)
theorem c0_115 : ¬ drop0% Multiset.induction_on' 3 := fun h => h (α := ℕ) (p := fun _ => False) 0 (fun _ _ x => x)

-- `Multiset.induction_on'` idx 4: necessary (p s := s = 0, S = {0})
theorem c0_116 : ¬ drop0% Multiset.induction_on' 4 := fun h => absurd (h (α := ℕ) (p := fun s => s = 0) {0} rfl) (by simp)

-- `Multiset.ssubset_cons` idx 3: necessary (s = {0}, a = 0: 0 ::m {0} is a subset of {0})
theorem c0_117 : ¬ drop0% Multiset.ssubset_cons 3 := fun h => absurd (h (s := ({0} : Multiset ℕ)) (a := 0)) (by simp [HasSSubset.SSubset, Multiset.cons_subset])

-- `Multiset.cons_subset_cons` idx 4: necessary (a = 0, s = {1}, t = 0)
theorem c0_118 : ¬ drop0% Multiset.cons_subset_cons 4 := fun h => absurd (h (a := 0) (s := ({1} : Multiset ℕ)) (t := 0)) (by simp)

-- `Multiset.pmap_cons` idx 6: necessary (p = False, a = 0)
theorem c0_119 : ¬ indep0% Multiset.pmap_cons 6 := fun h => h (β := ℕ) (p := fun (_ : ℕ) => False) (fun _ h => h.elim) 0 0 0 (by simp)

-- `_private.Mathlib.Data.Multiset.ZeroCons.0.Multiset.rel_flip_aux` idx 5: necessary (r = True, s = {0}, t = 0: cards differ)
theorem c0_120 : ¬ drop0% _private.Mathlib.Data.Multiset.ZeroCons.«0».Multiset.rel_flip_aux 5 := fun h => absurd
  (Multiset.card_eq_card_of_rel (h (r := fun (_ _ : ℕ) => True) (s := {0}) (t := (0 : Multiset ℕ)))) (by simp)

-- `Multiset.rel_refl_of_refl_on` idx 3: necessary (m = {0}, r = False)
theorem c0_121 : ¬ drop0% Multiset.rel_refl_of_refl_on 3 := fun h => absurd (h (m := ({0} : Multiset ℕ)) (r := fun _ _ => False)) (fun hh => (rel_ss.1 hh))

-- `Multiset.Rel.mono` idx 6: necessary (s = {0}, t = 0: cards differ)
theorem c0_122 : ¬ drop0% Multiset.Rel.mono 6 := fun h => absurd
  (Multiset.card_eq_card_of_rel (h (r := fun (_ _ : ℕ) => True) (p := fun _ _ => True) (s := {0}) (t := (0 : Multiset ℕ)) (fun _ _ _ _ _ => trivial))) (by simp)

-- `Multiset.Rel.mono` idx 7: necessary (s = t = {0}, r = True, p = False)
theorem c0_123 : ¬ drop0% Multiset.Rel.mono 7 := fun h => absurd
  (h (r := fun (_ _ : ℕ) => True) (p := fun (_ _ : ℕ) => False) (s := {0}) (t := ({0} : Multiset ℕ)) (rel_ss.2 trivial)) (fun hh => rel_ss.1 hh)

-- `Multiset.exists_mem_of_rel_of_mem` idx 5: necessary (s = {0}, t = 0, a = 0)
theorem c0_124 : ¬ drop0% Multiset.exists_mem_of_rel_of_mem 5 := fun h => absurd
  (h (r := fun (_ _ : ℕ) => True) (s := {0}) (t := (0 : Multiset ℕ)) (a := 0) (by simp)) (by simp)

-- `Multiset.rel_of_forall` idx 4: necessary (m1 = m2 = {0}, r = False)
theorem c0_125 : ¬ drop0% Multiset.rel_of_forall 4 := fun h => absurd
  (h (m1 := ({0} : Multiset ℕ)) (m2 := {0}) (r := fun _ _ => False) rfl) (fun hh => rel_ss.1 hh)

-- `Multiset.Rel.trans` idx 2: necessary (r a b := a + 1 = b, s = {0}, t = {1}, u = {2})
theorem c0_126 : ¬ drop0% Multiset.Rel.trans 2 := fun h => absurd
  (h (fun (a b : ℕ) => a + 1 = b) (s := {0}) (t := {1}) (u := {2}) (rel_ss.2 rfl) (rel_ss.2 rfl)) (fun hh => absurd (rel_ss.1 hh) (by decide))

-- `Multiset.Rel.trans` idx 6: necessary (s = {0}, t = u = 0: cards differ)
theorem c0_127 : ¬ drop0% Multiset.Rel.trans 6 := fun h => absurd
  (Multiset.card_eq_card_of_rel (h topN (s := {0}) (t := 0) (u := 0) Multiset.Rel.zero)) (by simp)

-- `Multiset.Rel.trans` idx 7: necessary (s = t = 0, u = {0}: cards differ)
theorem c0_128 : ¬ drop0% Multiset.Rel.trans 7 := fun h => absurd
  (Multiset.card_eq_card_of_rel (h topN (s := 0) (t := 0) (u := {0}) Multiset.Rel.zero)) (by simp)

-- `eq_natCast'` idx 4: necessary (F = bare FunLike N -> N, f n = if n = 1 then 1 else 0, n = 2)
theorem c0_129 : ¬ drop0% eq_natCast' 4 := fun h => absurd (h (A := ℕ) (F := FW ℕ ℕ) ⟨fun n => if n = 1 then 1 else 0⟩ rfl 2) (by decide)

-- `eq_natCast'` idx 6: necessary (f = 0 : N ->+ N, n = 1)
theorem c0_130 : ¬ drop0% eq_natCast' 6 := fun h => absurd (h (A := ℕ) (F := ℕ →+ ℕ) 0 1) (by simp)

-- `map_natCast'` idx 6: necessary (F = bare FunLike N -> N, f n = if n = 1 then 1 else 0, n = 2)
theorem c0_131 : ¬ drop0% map_natCast' 6 := fun h => absurd (h (B := ℕ) (F := FW ℕ ℕ) (A := ℕ) ⟨fun n => if n = 1 then 1 else 0⟩ rfl 2) (by decide)

-- `map_natCast'` idx 8: necessary (f = 0 : N ->+ N, n = 1)
theorem c0_132 : ¬ drop0% map_natCast' 8 := fun h => absurd (h (B := ℕ) (F := ℕ →+ ℕ) (A := ℕ) 0 1) (by simp)

-- `map_ofNat'` idx 6: necessary (F = bare FunLike N -> N, f n = if n = 1 then 1 else 0, n = 2)
theorem c0_133 : ¬ drop0% map_ofNat' 6 := fun h => absurd (h (B := ℕ) (F := FW ℕ ℕ) (A := ℕ) ⟨fun n => if n = 1 then 1 else 0⟩ rfl 2) (by decide)

-- `map_ofNat'` idx 8: necessary (f = 0 : N ->+ N, n = 2)
theorem c0_134 : ¬ drop0% map_ofNat' 8 := fun h => absurd (h (B := ℕ) (F := ℕ →+ ℕ) (A := ℕ) 0 2) (by simp)

-- `map_ofNat'` idx 10: necessary (f = id : N ->+ N, n = 0)
theorem c0_135 : ¬ indep0% map_ofNat' 10 := fun h => absurd (h (B := ℕ) (F := ℕ →+ ℕ) (A := ℕ) (AddMonoidHom.id ℕ) rfl 0) (fun h => by have := h.prop; omega)

-- `ext_nat''` idx 4: necessary (F = bare FunLike N -> N, f = 0, g = indicator of 0)
theorem c0_136 : ¬ drop0% ext_nat'' 4 := fun h => by
  have := h (A := ℕ) (F := FW ℕ ℕ) ⟨fun _ => 0⟩ ⟨fun n => if n = 0 then 1 else 0⟩ (fun {n} hn => by
    show 0 = if n = 0 then 1 else 0; simp [Nat.pos_iff_ne_zero.1 hn])
  exact absurd (congrArg (fun φ : FW ℕ ℕ => φ.toFun 0) this) (by decide)

-- `ext_nat''` idx 7: necessary (F = ZeroHom N N, f = id, g = 0)
theorem c0_137 : ¬ drop0% ext_nat'' 7 := fun h => by
  have := h (A := ℕ) (F := ZeroHom ℕ ℕ) ⟨id, rfl⟩ 0
  exact absurd (congrArg (fun φ : ZeroHom ℕ ℕ => φ 1) this) (by simp)

-- `MonoidWithZeroHom.ext_nat` idx 4: necessary (f = id, g n = (0 if n = 0 else 1) as N ->*0 N)
theorem c0_138 : ¬ drop0% MonoidWithZeroHom.ext_nat 4 := fun h => by
  have := h (A := ℕ) (f := MonoidWithZeroHom.id ℕ) (g := sgnHom)
  exact absurd (congrArg (fun φ : ℕ →*₀ ℕ => φ 2) this) (by simp [sgnHom])

-- `eq_natCast` idx 4: necessary (F = bare FunLike N -> N, f = 0, n = 1)
theorem c0_139 : ¬ drop0% eq_natCast 4 := fun h => absurd (h (R := ℕ) (F := FW ℕ ℕ) ⟨fun _ => 0⟩ 1) (by decide)

-- `map_natCast` idx 6: necessary (F = bare FunLike N -> N, f = 0, n = 1)
theorem c0_140 : ¬ drop0% map_natCast 6 := fun h => absurd (h (R := ℕ) (S := ℕ) (F := FW ℕ ℕ) ⟨fun _ => 0⟩ 1) (by decide)

-- `map_ofNat` idx 6: necessary (F = bare FunLike N -> N, f = 0, n = 2)
theorem c0_141 : ¬ drop0% map_ofNat 6 := fun h => absurd (h (R := ℕ) (S := ℕ) (F := FW ℕ ℕ) ⟨fun _ => 0⟩ 2) (by decide)

-- `map_ofNat` idx 9: necessary (f = RingHom.id N, n = 0)
theorem c0_142 : ¬ indep0% map_ofNat 9 := fun h => absurd (h (R := ℕ) (S := ℕ) (F := ℕ →+* ℕ) (RingHom.id ℕ) 0) (fun h => by have := h.prop; omega)

-- `ext_nat` idx 4: necessary (F = bare FunLike N -> N, f = 0, g = 1)
theorem c0_143 : ¬ drop0% ext_nat 4 := fun h => absurd (congrArg (fun φ : FW ℕ ℕ => φ.toFun 0) (h (R := ℕ) (F := FW ℕ ℕ) ⟨fun _ => 0⟩ ⟨fun _ => 1⟩)) (by decide)

-- `NeZero.nat_of_neZero` idx 6: necessary (R = ZMod 2, S = N, F = bare FunLike, n = 2)
theorem c0_144 : ¬ drop0% NeZero.nat_of_neZero 6 := fun h => (@h (ZMod 2) ℕ _ _ (FW (ZMod 2) ℕ) _ ⟨fun _ => 0⟩ 2 ⟨by decide⟩).out (by decide)

-- `NeZero.nat_of_neZero` idx 9: necessary (f = RingHom.id N, n = 0)
theorem c0_145 : ¬ drop0% NeZero.nat_of_neZero 9 := fun h => (h (R := ℕ) (S := ℕ) (F := ℕ →+* ℕ) (RingHom.id ℕ) (n := 0)).out rfl

-- `NeZero.nat_of_injective` idx 7: necessary (f = RingHom.id N, n = 0)
theorem c0_146 : ¬ drop0% NeZero.nat_of_injective 7 := fun h => (h (R := ℕ) (S := ℕ) (F := ℕ →+* ℕ) (n := 0) (f := RingHom.id ℕ) (fun _ _ e => e)).out rfl

-- `NeZero.nat_of_injective` idx 8: necessary (R = ZMod 3, S = ZMod 4, injective bare map x -> x.val, n = 4)
theorem c0_147 : ¬ drop0% NeZero.nat_of_injective 8 := fun h =>
  (@h (ZMod 3) (ZMod 4) (FW (ZMod 3) (ZMod 4)) _ _ _ 4 ⟨by decide⟩ ⟨fun x => (x.val : ZMod 4)⟩ (by show ∀ a b : Fin 3, ((a.val : ZMod 4)) = (b.val : ZMod 4) → a = b; decide)).out (by decide)

-- `NeZero.nat_of_injective` idx 10: necessary (f = Nat.castRingHom (ZMod 2), n = 2)
theorem c0_148 : ¬ drop0% NeZero.nat_of_injective 10 := fun h =>
  (@h ℕ (ZMod 2) (ℕ →+* ZMod 2) _ _ _ 2 ⟨by decide⟩ _ (Nat.castRingHom (ZMod 2))).out (by decide)

-- `SemiconjBy.natCast_mul_natCast_mul` idx 5: necessary (alpha = N, a = 1, x = 0, y = 1, m = n = 1)
theorem c0_149 : ¬ drop0% SemiconjBy.natCast_mul_natCast_mul 5 := fun h => absurd (h (a := (1:ℕ)) (x := 0) (y := 1) 1 1) (by unfold SemiconjBy; decide)

-- `Commute.natCast_mul_right` idx 4: necessary (2x2 N-matrices E11, E12, n = 1)
theorem c0_150 : ¬ drop0% Commute.natCast_mul_right 4 := fun h => ncAB (by simpa using h (a := mA) (b := mB) 1)

-- `Commute.natCast_mul_left` idx 4: necessary (2x2 N-matrices E11, E12, n = 1)
theorem c0_151 : ¬ drop0% Commute.natCast_mul_left 4 := fun h => ncAB (by simpa using h (a := mA) (b := mB) 1)

-- `Commute.natCast_mul_natCast_mul` idx 4: necessary (2x2 N-matrices E11, E12, m = n = 1)
theorem c0_152 : ¬ drop0% Commute.natCast_mul_natCast_mul 4 := fun h => ncAB (by simpa using h (a := mA) (b := mB) 1 1)

-- `Nat.cast_div` idx 5: necessary (K = ZMod 2 as a field, m = n = 2: 1 vs 0/0 = 0)
theorem c0_153 : ¬ drop0% Nat.cast_div 5 := fun h => absurd (h (K := F2) (m := 2) (n := 2) dvd_rfl) (by rw [F2_two]; simp)

-- `Nat.cast_div_charZero` idx 4: necessary (K = ZMod 2 as a field, m = n = 2: 1 vs 0/0 = 0)
theorem c0_154 : ¬ drop0% Nat.cast_div_charZero 4 := fun h => absurd (h (K := F2) (m := 2) (n := 2) dvd_rfl) (by rw [F2_two]; simp)

-- `Nat.cast_div_div_div_cancel_right` idx 5: necessary (K = ZMod 2 as a field, d = m = n = 2: 1/1 vs 0/0)
theorem c0_155 : ¬ drop0% Nat.cast_div_div_div_cancel_right 5 := fun h => absurd (h (K := F2) (d := 2) (m := 2) (n := 2) dvd_rfl dvd_rfl) (by rw [F2_two]; simp)

-- `Nat.cast_div_div_div_cancel_right` idx 6: necessary (K = Q, d = 2, m = 2, n = 1)
theorem c0_156 : ¬ drop0% Nat.cast_div_div_div_cancel_right 6 := fun h => absurd (h (K := ℚ) (d := 2) (m := 2) (n := 1) dvd_rfl) (by norm_num)

-- `Nat.cast_div_div_div_cancel_right` idx 7: necessary (K = Q, d = 2, m = 1, n = 2)
theorem c0_157 : ¬ drop0% Nat.cast_div_div_div_cancel_right 7 := fun h => absurd (h (K := ℚ) (d := 2) (m := 1) (n := 2) dvd_rfl) (by norm_num)

-- `Nat.leRecOn_injective` idx 3: necessary (C = True, n = 1, m = 0)
theorem c0_158 : ¬ indep0% Nat.leRecOn_injective 3 := fun h => absurd (h (C := fun _ => True) (n := 1) (m := 0) (fun _ => trivial) (fun _ _ _ _ => rfl)) (by decide)

-- `Nat.leRecOn_surjective` idx 3: necessary (C = True, n = 1, m = 0)
theorem c0_159 : ¬ indep0% Nat.leRecOn_surjective 3 := fun h => absurd (h (C := fun _ => True) (n := 1) (m := 0) (fun _ => trivial) (fun _ _ => ⟨trivial, rfl⟩)) (by decide)

-- `Nat.leRecOn_surjective` idx 5: necessary (C k := 1 <= k, n = 0, m = 1: C 0 is empty)
theorem c0_160 : ¬ drop0% Nat.leRecOn_surjective 5 := fun h => by
  obtain ⟨x, _⟩ := h (C := fun k => 1 ≤ k) (n := 0) (m := 1) (Nat.zero_le 1) (fun {k} hk => Nat.le_succ_of_le hk) (le_refl 1)
  exact absurd x (by decide)

-- `Nat.leRecOn_injective` idx 5: necessary (universe 1: C = Bool, n = 0, m = 1, next = const false)
theorem c0_161 : ¬ drop1% Nat.leRecOn_injective 5 := fun h => by
  have := @h (fun _ => Bool) 0 1 (Nat.zero_le 1) (fun _ => false) true false (by
    rw [Nat.leRecOn_succ (le_refl 0), Nat.leRecOn_succ (le_refl 0)])
  exact absurd this (by decide)

-- `Nat.set_induction_bounded` idx 5: necessary (S = {m | 1 <= m}, k = 1, n = 0)
theorem c0_162 : ¬ drop0% Nat.set_induction_bounded 5 := fun h => absurd
  (h (n := 0) (k := 1) (S := {m | 1 ≤ m}) (le_refl 1) (fun k hk => Nat.le_succ_of_le hk)) (by simp)

-- `Nat.binaryRec_eq` idx 5: necessary (universe 1: motive = N, zero = 0, bit adds 1, b = false, n = 0)
theorem c0_163 : ¬ drop1% Nat.binaryRec_eq 5 := fun h => absurd
  (h (motive := fun _ => ℕ) (zero := 0) (bit := fun _ _ x => x + 1) false 0) (by rw [show Nat.bit false 0 = 0 from rfl, Nat.binaryRec_zero]; decide)

-- `Nat.binaryRec'_eq` idx 5: necessary (b = false, n = 0)
theorem c0_164 : ¬ indep0% Nat.binaryRec'_eq 5 := fun h => absurd
  (h (motive := fun _ => True) (zero := trivial) (bit := fun _ _ _ _ => trivial) false 0 rfl) (by decide)

-- `Nat.binaryRecFromOne_eq` idx 6: necessary (n = 0)
theorem c0_165 : ¬ indep0% Nat.binaryRecFromOne_eq 6 := fun h =>
  h (motive := fun _ => True) (zero := trivial) (one := trivial) (bit := fun _ _ _ _ => trivial) false 0 rfl

-- `Nat.binaryRec_of_ne_zero` idx 4: necessary (universe 1: C = N, z = 0, f adds 1, n = 0)
theorem c0_166 : ¬ drop1% Nat.binaryRec_of_ne_zero 4 := fun h => absurd
  (h (C := fun _ => ℕ) 0 (fun _ _ x => x + 1) (n := 0)) (by simp [Nat.binaryRec_zero])

-- `Multiset.Pi.cons_injective` idx 6: necessary (universe 1: delta = Bool, a = 0, s = {0}: cons at 0 forgets the tail)
theorem c0_167 : ¬ (∀ {α : Type} [DecidableEq α] {δ : α → Type} {a : α} {b : δ a} {s : Multiset α},
    Function.Injective (Multiset.Pi.cons s a b)) := fun h => by
  have := h (δ := fun _ : ℕ => Bool) (a := 0) (b := true) (s := {0}) (a₁ := fun _ _ => true) (a₂ := fun _ _ => false) (cons_const _ _ _)
  exact absurd (congrFun (congrFun this 0) (by simp)) (by decide)

-- `Multiset.Pi.cons_swap` idx 9: necessary (universe 1: delta = Bool, a = a' = 0, b = true, b' = false, m = 0)
theorem c0_168 : ¬ (∀ {α : Type} [DecidableEq α] {δ : α → Type} {a a' : α} {b : δ a} {b' : δ a'} {m : Multiset α}
    {f : ∀ a ∈ m, δ a}, Multiset.Pi.cons (a' ::ₘ m) a b (Multiset.Pi.cons m a' b' f) ≍
      Multiset.Pi.cons (a ::ₘ m) a' b' (Multiset.Pi.cons m a b f)) := fun h => by
  have e := eq_of_heq (h (δ := fun _ : ℕ => Bool) (a := 0) (a' := 0) (b := true) (b' := false) (m := 0) (f := fun _ h => absurd h (Multiset.notMem_zero _)))
  have := congrFun (congrFun e 0) (Multiset.mem_cons_self 0 _)
  simp [Multiset.Pi.cons_same] at this

-- `Multiset.Nodup.pi` idx 6: necessary (s = {0}, t a = {0,0}: two equal functions in s.pi t)
theorem c0_169 : ¬ drop0% Multiset.Nodup.pi 6 := fun h => by
  have hn := h (β := fun _ : ℕ => ℕ) (s := {0}) (t := fun _ => {0, 0}) (by simp)
  rw [show ({0} : Multiset ℕ) = 0 ::ₘ 0 from rfl, Multiset.pi_cons, Multiset.nodup_bind] at hn
  have := hn.2
  simp only [Multiset.pi_zero, Multiset.map_singleton] at this
  have hR : ¬ Function.onFun Disjoint (fun b : ℕ => ({Multiset.Pi.cons 0 0 b (Multiset.Pi.empty fun _ => ℕ)} : Multiset _)) 0 0 := by
    simp [Function.onFun]
  exact np2 (x := 0) (y := 0) hR hR hR hR this

-- `Multiset.Nodup.pi` idx 5: necessary (s = {0,0}, t a = {false,true}: cons over {0} at 0 forgets its tail)
theorem c0_170 : ¬ drop0% Multiset.Nodup.pi 5 := fun h => by
  have hn := h (β := fun _ : ℕ => Bool) (s := {0, 0}) (t := fun _ => {false, true}) (fun _ _ => by simp)
  rw [show ({0, 0} : Multiset ℕ) = 0 ::ₘ {0} from rfl, Multiset.pi_cons, Multiset.nodup_bind] at hn
  have h2 := hn.1 false (by simp)
  have := Multiset.inj_on_of_nodup_map h2 (fun _ _ => false) (by simp [Multiset.mem_pi]) (fun _ _ => true) (by simp [Multiset.mem_pi]) (cons_const _ _ _)
  exact absurd (congrFun (congrFun this 0) (by simp)) (by decide)

-- `Multiset.recOn_0` idx 4: necessary (universe 1: C = N, C_cons a _ x = 2x + a, a = 0, a' = 1)
theorem c0_171 : ¬ (∀ {α : Type} {C : Multiset α → Type} {C_0 : C 0} {C_cons : ∀ (a : α) (m : Multiset α), C m → C (a ::ₘ m)}
    (a a' : α) (m : Multiset α) (b : C m), C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_cons a m b)) := fun h => by
  have e : (2 * (2 * 0 + 1) + 0 : ℕ) = 2 * (2 * 0 + 0) + 1 :=
    eq_of_heq (h (α := ℕ) (C := fun _ : Multiset ℕ => ℕ) (C_0 := (0:ℕ)) (C_cons := fun a _ x => 2 * x + a) (0:ℕ) (1:ℕ) (0 : Multiset ℕ) (0:ℕ))
  omega

-- `Multiset.recOn_cons` idx 4: necessary (universe 1: C = N, C_cons a _ x = 2x + a, a = 0, a' = 1)
theorem c0_172 : ¬ (∀ {α : Type} {C : Multiset α → Type} {C_0 : C 0} {C_cons : ∀ (a : α) (m : Multiset α), C m → C (a ::ₘ m)}
    (a : α) (m : Multiset α) (a a' : α) (m : Multiset α) (b : C m), C_cons a (a' ::ₘ m) (C_cons a' m b) ≍ C_cons a' (a ::ₘ m) (C_cons a m b)) := fun h => by
  have e : (2 * (2 * 0 + 1) + 0 : ℕ) = 2 * (2 * 0 + 0) + 1 :=
    eq_of_heq (h (α := ℕ) (C := fun _ : Multiset ℕ => ℕ) (C_0 := (0:ℕ)) (C_cons := fun a _ x => 2 * x + a) (0:ℕ) (0 : Multiset ℕ) (0:ℕ) (1:ℕ) (0 : Multiset ℕ) (0:ℕ))
  omega

-- `NNRat.cast_listSum` idx 2: necessary (K = ZMod 2 as a field, l = [1/2, 1/2] (1/2 casts to 1/0 = 0))
theorem c0_173 : ¬ drop0% NNRat.cast_listSum 2 := fun h => by
  have := h (K := F2) [1/2, 1/2]
  simp only [List.sum_cons, List.sum_nil, List.map_cons, List.map_nil, half0, add_zero] at this
  norm_num at this

-- `NNRat.cast_listProd` idx 2: necessary (K = ZMod 2 as a field, l = [1/2, 2])
theorem c0_174 : ¬ drop0% NNRat.cast_listProd 2 := fun h => by
  have := h (K := F2) [1/2, 2]
  simp only [List.prod_cons, List.prod_nil, List.map_cons, List.map_nil, half0, zero_mul] at this
  norm_num at this

-- `NNRat.cast_multisetSum` idx 2: necessary (K = ZMod 2 as a field, s = {1/2, 1/2})
theorem c0_175 : ¬ drop0% NNRat.cast_multisetSum 2 := fun h => by
  have := h (K := F2) {1/2, 1/2}
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton, Multiset.map_cons, Multiset.map_singleton, half0, add_zero] at this
  norm_num at this

-- `NNRat.cast_sum` idx 3: necessary (K = ZMod 2 as a field, s = univ : Finset Bool, f = 1/2)
theorem c0_176 : ¬ drop0% NNRat.cast_sum 3 := fun h => by
  have := h (K := F2) (Finset.univ : Finset Bool) (fun _ => 1/2)
  simp only [Fintype.sum_bool, half0, add_zero] at this
  norm_num at this

-- `NNRat.cast_multisetProd` idx 2: necessary (K = ZMod 2 as a field, s = {1/2, 2})
theorem c0_177 : ¬ drop0% NNRat.cast_multisetProd 2 := fun h => by
  have := h (K := F2) {1/2, 2}
  simp only [Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton, Multiset.map_cons, Multiset.map_singleton, half0, zero_mul] at this
  norm_num at this

-- `NNRat.cast_prod` idx 3: necessary (K = ZMod 2 as a field, f = ![2, 1/2] over Bool)
theorem c0_178 : ¬ drop0% NNRat.cast_prod 3 := fun h => by
  have := h (K := F2) (Finset.univ : Finset Bool) (fun b => if b then 1/2 else 2)
  simp only [Fintype.prod_bool, ite_true, half0, zero_mul] at this
  norm_num at this

-- `NNRat.toNNRat_sum_of_nonneg` idx 3: necessary (f = ![-1, 1] over Bool: 0 vs 1)
theorem c0_179 : ¬ drop0% NNRat.toNNRat_sum_of_nonneg 3 := fun h => by
  have := h (s := (Finset.univ : Finset Bool)) (f := fun b => if b then 1 else -1)
  simp at this
  rw [show (-1:ℚ).toNNRat = 0 from Rat.toNNRat_eq_zero.2 (by norm_num)] at this; simp at this

-- `NNRat.toNNRat_prod_of_nonneg` idx 3: necessary (f = -1 over Bool: 1 vs 0)
theorem c0_180 : ¬ drop0% NNRat.toNNRat_prod_of_nonneg 3 := fun h => by
  have := h (s := (Finset.univ : Finset Bool)) (f := fun _ => -1)
  simp at this
  rw [show (-1:ℚ).toNNRat = 0 from Rat.toNNRat_eq_zero.2 (by norm_num)] at this; simp at this

-- `NNRat.ext_num_den` idx 3: necessary (p = 1, q = 1/2)
theorem c0_181 : ¬ drop0% NNRat.ext_num_den 3 := fun h => by
  have := h (p := 1) (q := 1/2) (by rw [half_num]; rfl)
  norm_num at this

-- `NNRat.floor_cast` idx 3: necessary (K = Q ordered via the swap 1/2 <-> 11/2 (FloorSemiring, not ordered ring), x = 1/2: 5 vs 0)
theorem c0_182 : ¬ drop0% NNRat.floor_cast 3 := fun h => absurd (h (K := K1) (1/2)) (by decide +kernel)

-- `NNRat.ceil_cast` idx 3: necessary (K = Q ordered via the swap 1/2 <-> 11/2, x = 1/2: 6 vs 1)
theorem c0_183 : ¬ drop0% NNRat.ceil_cast 3 := fun h => absurd (h (K := K1) (1/2)) (by decide +kernel)

-- `NNRat.intFloor_cast` idx 3: necessary (K = Q ordered via the swap 1/2 <-> 11/2 (FloorRing), x = 1/2: 5 vs 0)
theorem c0_184 : ¬ drop0% NNRat.intFloor_cast 3 := fun h => absurd (h (K := K1) (1/2)) (by decide +kernel)

-- `NNRat.intCeil_cast` idx 3: necessary (K = Q ordered via the swap 1/2 <-> 11/2 (FloorRing), x = 1/2: 6 vs 1)
theorem c0_185 : ¬ drop0% NNRat.intCeil_cast 3 := fun h => absurd (h (K := K1) (1/2)) (by decide +kernel)

-- `Mathlib.Meta.NormNum.IsInt.natCeil` idx 3: necessary (R = Q ordered via the swap -1 <-> 11/2, r = -1, m = 1: natCeil 6)
theorem c0_186 : ¬ drop0% Mathlib.Meta.NormNum.IsInt.natCeil 3 := fun h =>
  absurd (h (R := K2) (-1) 1 ⟨by decide +kernel⟩).out (by decide +kernel)

-- `Mathlib.Meta.NormNum.IsNNRat.natCeil` idx 3: necessary (R = Q ordered via the swap 1/2 <-> 11/2, r = 1/2, n = 1, d = 2, res = 1: natCeil 6)
theorem c0_187 : ¬ drop0% Mathlib.Meta.NormNum.IsNNRat.natCeil 3 := fun h =>
  absurd (h (R := K1) _ 1 2 (Mathlib.Meta.NormNum.IsNNRat.of_raw K1 1 2 (by decide +kernel)) 1 (by decide +kernel)).out (by decide +kernel)

-- `Mathlib.Meta.NormNum.IsNNRat.natCeil` idx 8: necessary (R = Q, r = 0, n = d = 1, res = 1)
theorem c0_188 : ¬ drop0% Mathlib.Meta.NormNum.IsNNRat.natCeil 8 := fun h =>
  absurd (h (R := ℚ) 0 1 1 1 (by decide +kernel)).out (by decide +kernel)

-- `Mathlib.Meta.NormNum.IsNNRat.natCeil` idx 10: necessary (R = Q, r = 1/2, n = 1, d = 2, res = 0)
theorem c0_189 : ¬ drop0% Mathlib.Meta.NormNum.IsNNRat.natCeil 10 := fun h =>
  absurd (h (R := ℚ) _ 1 2 (Mathlib.Meta.NormNum.IsNNRat.of_raw ℚ 1 2 (by decide +kernel)) 0).out (by decide +kernel)

-- `Mathlib.Meta.NormNum.IsRat.natCeil` idx 3: necessary (R = Q ordered via the swap -1 <-> 11/2, r = -1, n = d = 1: natCeil 6)
theorem c0_190 : ¬ drop0% Mathlib.Meta.NormNum.IsRat.natCeil 3 := fun h =>
  absurd (h (R := K2) _ 1 1 (Mathlib.Meta.NormNum.IsRat.of_raw K2 (Int.negOfNat 1) 1 (by decide +kernel))).out (by decide +kernel)
