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

namespace W3c1
theorem inf_true : ¬ (Set.ofPred (fun _ : ℕ => True)).Finite := Set.infinite_univ
theorem tf (S : Finset ℕ) (hf : (Set.ofPred (· ∈ S)).Finite) : hf.toFinset = S :=
  Finset.coe_injective (by rw [hf.coe_toFinset]; rfl)
theorem fts (S : Finset ℕ) : (Set.ofPred (· ∈ S)).Finite := S.finite_toSet
theorem nthv (p : ℕ → Prop) [DecidablePred p] {n k : ℕ} (hp : p n) (hc : Nat.count p n = k) :
    Nat.nth p k = n := hc ▸ Nat.nth_count hp
theorem nth_big (S : Finset ℕ) {n : ℕ} (h : S.card ≤ n) : Nat.nth (· ∈ S) n = 0 :=
  Nat.nth_of_card_le S.finite_toSet (by rw [tf]; exact h)
theorem hmU : ((0:ℕ):Unit) ≡ ((1:ℕ):Unit) [PMOD ((0:ℕ):Unit)] := by
  rw [Subsingleton.elim ((1:ℕ):Unit) ((0:ℕ):Unit)]; try exact AddCommGroup.ModEq.refl _
theorem nth_true (n : ℕ) : Nat.nth (fun _ => True) n = n :=
  nthv _ trivial (by simp [Nat.count_eq_card_filter_range])
theorem em_eq (a b n : ℕ) (h1 : a ^ n ∣ b) (h2 : ¬ a ^ (n + 1) ∣ b) : emultiplicity a b = n :=
  emultiplicity_eq_coe.2 ⟨h1, h2⟩
theorem memS (T : Finset ℕ) {n : ℕ} (h : n < T.card) :
    n ∈ {n | ∀ (hf : (Set.ofPred (· ∈ T)).Finite), n < hf.toFinset.card} := fun hf => by rw [tf]; exact h
theorem memI {n : ℕ} : n ∈ {n | ∀ (hf : (Set.ofPred (fun n : ℕ => 1 ≤ n)).Finite), n < hf.toFinset.card} :=
  fun hf => absurd hf (Set.Ici_infinite 1)
theorem nth_empty' (q : ℕ → Prop) [DecidablePred q] (hq : ∀ i, ¬ q i) (n : ℕ) : Nat.nth q n = 0 := by
  have : q = (· ∈ (∅ : Finset ℕ)) := funext fun i => by simp [hq i]
  subst this; exact nth_big _ (by simp)
end W3c1
open W3c1

-- `Nat.isLUB_maxPrimeFac` idx 1: n = 0
theorem c1_3 : ¬ drop0% Nat.isLUB_maxPrimeFac 1 := fun h =>
  absurd ((h (n := 0)).1 ⟨Nat.prime_two, dvd_zero 2⟩) (by simp)
-- `Nat.isGreatest_maxPrimeFac` idx 1: n = 1
theorem c1_2 : ¬ drop0% Nat.isGreatest_maxPrimeFac 1 := fun h =>
  absurd (h (n := 1)).1.1 (by simp [Nat.not_prime_one])
-- `Nat.maxPrimeFac_le_iff` idx 2: n = 1, m = 0
theorem c1_4 : ¬ drop0% Nat.maxPrimeFac_le_iff 2 := fun h =>
  absurd ((h (m := 0) (n := 1)).2 (fun p hp hd => absurd (Nat.dvd_one.1 hd) hp.ne_one)) (by simp)
-- `Nat.maxPrimeFac_eq_sSup` idx 1: n = 1
theorem c1_5 : ¬ drop0% Nat.maxPrimeFac_eq_sSup 1 := fun h => by
  have e : {p | Nat.Prime p ∧ p ∣ 1} = ∅ := by
    ext p; simp only [Nat.dvd_one, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp h1; exact hp.ne_one h1
  have := h (n := 1); rw [e, csSup_empty] at this; simp at this
-- `Nat.le_maxPrimeFac` idx 3: n = p = 4
theorem c1_1 : ¬ drop0% Nat.le_maxPrimeFac 3 := fun h => by
  have h1 := h (n := 4) (p := 4) (by decide) dvd_rfl
  have h2 : Nat.maxPrimeFac 4 ≤ 2 := (Nat.maxPrimeFac_le_iff (by decide)).2
    (fun p hp hd => Nat.le_of_dvd two_pos (hp.dvd_of_dvd_pow (n := 2) (by simpa using hd)))
  omega
-- `AddCommGroup.natCast_modEq_natCast` idx 2: M = Unit, a = 0, b = 1, n = 0
theorem c1_6 : ¬ drop0% AddCommGroup.natCast_modEq_natCast 2 := fun h => by
  have := (h (M := Unit) (a := 0) (b := 1) (n := 0)).1 hmU
  exact absurd this (by decide)
-- `Nat.ModEq.of_natCast` idx 2: M = Unit, a = 0, b = 1, n = 0
theorem c1_7 : ¬ drop0% Nat.ModEq.of_natCast 2 := fun h => by
  have := h (M := Unit) (a := 0) (b := 1) (n := 0) hmU
  exact absurd this (by decide)
-- `Nat.ModEq.of_div` idx 7: m = 3, a = 0, b = 2, c = 2
theorem c1_8 : ¬ drop0% Nat.ModEq.of_div 7 := fun h =>
  absurd (h (m := 3) (a := 0) (b := 2) (c := 2) (by decide) (by decide) (by decide)) (by decide)
-- `Nat.odd_mul_odd_div_two` idx 2: removable, n odd suffices
theorem c1_9 : drop% Nat.odd_mul_odd_div_two 2 := by
  intro m n hn
  have e : n = 2 * (n / 2) + 1 := by omega
  conv_lhs => rw [e]
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm, Nat.mul_add_div two_pos]

-- `Nat.emultiplicity_eq_card_pow_dvd` idx 5: m = n = 2, b = 0
theorem c1_10 : ¬ drop0% Nat.emultiplicity_eq_card_pow_dvd 5 := fun h => by
  have := h (m := 2) (n := 2) (b := 0) (by decide) (by decide)
  rw [em_eq _ _ 1 (by decide) (by decide)] at this; simp at this
-- `Nat.Prime.emultiplicity_mul` idx 3: p = 4, m = n = 2
theorem c1_11 : ¬ drop0% Nat.Prime.emultiplicity_mul 3 := fun h => by
  have := h (p := 4) (m := 2) (n := 2)
  rw [em_eq _ _ 1 (by decide) (by decide),
    em_eq _ _ 0 (by decide) (by decide)] at this; simp at this
-- `Nat.Prime.sub_one_mul_multiplicity_factorial` idx 2: p = 4, n = 8
theorem c1_12 : ¬ drop0% Nat.Prime.sub_one_mul_multiplicity_factorial 2 := fun h => by
  have := h (n := 8) (p := 4)
  rw [multiplicity_eq_of_dvd_of_not_dvd (k := 3) (by decide) (by decide)] at this
  norm_num at this
-- `Nat.Prime.emultiplicity_choose'` idx 5: p = 2, n = k = 1, b = 0
theorem c1_13 : ¬ drop0% Nat.Prime.emultiplicity_choose' 5 := fun h => by
  have := h (p := 2) (n := 1) (k := 1) (b := 0) Nat.prime_two
  rw [em_eq _ _ 1 (by decide) (by decide)] at this; simp at this
-- `Nat.Prime.emultiplicity_choose` idx 5: p = 2, n = 0, k = 1, b = 1
theorem c1_14 : ¬ drop0% Nat.Prime.emultiplicity_choose 5 := fun h => by
  have := h (p := 2) (n := 0) (k := 1) (b := 1) Nat.prime_two (by decide)
  simp at this
-- `Nat.Prime.emultiplicity_choose` idx 6: p = 2, n = 2, k = 1, b = 0
theorem c1_15 : ¬ drop0% Nat.Prime.emultiplicity_choose 6 := fun h => by
  have := h (p := 2) (n := 2) (k := 1) (b := 0) Nat.prime_two (by decide)
  rw [em_eq _ _ 1 (by decide) (by decide)] at this; simp at this
-- `Nat.Prime.emultiplicity_le_emultiplicity_choose_add` idx 1: p = 4, n = 4, k = 2
theorem c1_16 : ¬ drop0% Nat.Prime.emultiplicity_le_emultiplicity_choose_add 1 := fun h => by
  have := h (p := 4) 4 2
  rw [em_eq _ _ 1 (by decide) (by decide),
    em_eq _ _ 0 (by decide) (by decide), em_eq _ _ 0 (by decide) (by decide)] at this; simp at this
-- `Nat.Prime.emultiplicity_choose_prime_pow_add_emultiplicity` idx 4: p = 2, n = 0, k = 2
theorem c1_17 : ¬ drop0% Nat.Prime.emultiplicity_choose_prime_pow_add_emultiplicity 4 := fun h => by
  have := h (p := 2) (n := 0) (k := 2) Nat.prime_two (by decide)
  simp at this
-- `Nat.Prime.emultiplicity_choose_prime_pow` idx 4: p = 2, n = 0, k = 2
theorem c1_18 : ¬ drop0% Nat.Prime.emultiplicity_choose_prime_pow 4 := fun h => by
  have := h (p := 2) (n := 0) (k := 2) Nat.prime_two (by decide)
  simp at this
-- `Nat.Prime.emultiplicity_choose_prime_pow` idx 5: p = 2, n = 1, k = 0
theorem c1_19 : ¬ drop0% Nat.Prime.emultiplicity_choose_prime_pow 5 := fun h => by
  have := h (p := 2) (n := 1) (k := 0) Nat.prime_two (by decide)
  rw [em_eq _ _ 0 (by decide) (by decide)] at this; simp at this
-- `Nat.pow_dvd_iff_le_multiplicity` idx 4: p = 2, k = 1, n = 0
theorem c1_20 : ¬ drop0% Nat.pow_dvd_iff_le_multiplicity 4 := fun h => by
  have := (h (p := 2) (k := 1) (n := 0) (by decide)).1 (dvd_zero _)
  simp at this
-- `Nat.pow_dvd_iff_le_padicValNat` idx 4: p = 2, k = 1, n = 0
theorem c1_21 : ¬ drop0% Nat.pow_dvd_iff_le_padicValNat 4 := fun h => by
  have := (h (p := 2) (k := 1) (n := 0) (by decide)).1 (dvd_zero _)
  simp at this
-- `multiplicity_base_pow_mul` idx 3: p = 2, n = 0, k = 1
theorem c1_22 : ¬ drop0% multiplicity_base_pow_mul 3 := fun h => by
  have := h (p := 2) (n := 0) (by decide) 1
  simp at this
-- `padicValNat_base_pow_mul` idx 3: p = 2, n = 0, k = 1
theorem c1_23 : ¬ drop0% padicValNat_base_pow_mul 3 := fun h => by
  have := h (p := 2) (n := 0) (by decide) 1
  simp at this
-- `multiplicity_base_mul` idx 3: p = 2, n = 0
theorem c1_24 : ¬ drop0% multiplicity_base_mul 3 := fun h => by
  have := h (p := 2) (n := 0) (by decide)
  simp at this
-- `padicValNat_base_mul` idx 3: p = 2, n = 0
theorem c1_25 : ¬ drop0% padicValNat_base_mul 3 := fun h => by
  have := h (p := 2) (n := 0) (by decide)
  simp at this
-- `Nat.exists_dvd_of_not_prime` idx 2: n = 2
theorem c1_26 : ¬ drop0% Nat.exists_dvd_of_not_prime 2 := fun h => by
  obtain ⟨m, hm, h1, h2⟩ := h (n := 2) le_rfl
  have := Nat.le_of_dvd two_pos hm
  interval_cases m <;> simp_all
-- `Nat.forall_prime_of_two_of_odd` idx 3: P = Nat.Prime, p = 0
theorem c1_27 : ¬ drop0% Nat.forall_prime_of_two_of_odd 3 := fun h =>
  Nat.not_prime_zero (h (P := Nat.Prime) ⟨Nat.prime_two, fun _ hp _ => hp⟩ 0)
-- `Nat.Prime.dvd_of_dvd_pow` idx 3: p = 4, m = 2, n = 2
theorem c1_28 : ¬ drop0% Nat.Prime.dvd_of_dvd_pow 3 := fun h =>
  absurd (h (p := 4) (m := 2) (n := 2) (by decide)) (by decide)
-- `Nat.Prime.dvd_mul_of_dvd_ne` idx 4: p1 = 4, p2 = 2, n = 4
theorem c1_29 : ¬ drop0% Nat.Prime.dvd_mul_of_dvd_ne 4 := fun h =>
  absurd (h (p1 := 4) (p2 := 2) (n := 4) (by decide) Nat.prime_two (by decide) (by decide)) (by decide)
-- `Nat.Prime.dvd_mul_of_dvd_ne` idx 5: p1 = 2, p2 = 4, n = 4
theorem c1_30 : ¬ drop0% Nat.Prime.dvd_mul_of_dvd_ne 5 := fun h =>
  absurd (h (p1 := 2) (p2 := 4) (n := 4) (by decide) Nat.prime_two (by decide) (by decide)) (by decide)
-- `Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul` idx 1: p = 4, m = n = 2, k = l = 0
theorem c1_31 : ¬ drop0% Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul 1 := fun h =>
  absurd (h (p := 4) (m := 2) (n := 2) (k := 0) (l := 0) (by decide) (by decide) (by decide)) (by decide)
-- `Nat.Prime.pow_inj` idx 4: p = 4, q = 2, m = 0, n = 1
theorem c1_32 : ¬ drop0% Nat.Prime.pow_inj 4 := fun h =>
  absurd (h (p := 4) (q := 2) (m := 0) (n := 1) Nat.prime_two (by decide)).1 (by decide)
-- `Nat.Prime.pow_inj` idx 5: p = 2, q = 4, m = 1, n = 0
theorem c1_33 : ¬ drop0% Nat.Prime.pow_inj 5 := fun h =>
  absurd (h (p := 2) (q := 4) (m := 1) (n := 0) Nat.prime_two (by decide)).1 (by decide)
-- `Nat.Prime.pow_inj` idx 6: p = 2, q = 3
theorem c1_34 : ¬ drop0% Nat.Prime.pow_inj 6 := fun h =>
  absurd (h (p := 2) (q := 3) (m := 0) (n := 0) Nat.prime_two Nat.prime_three).1 (by decide)
-- `Nat.Prime.pow_inj'` idx 4: p = 4, q = 2, m = 1, n = 2
theorem c1_35 : ¬ drop0% Nat.Prime.pow_inj' 4 := fun h =>
  absurd (h (p := 4) (q := 2) (m := 1) (n := 2) Nat.prime_two (by decide) (by decide) (by decide)).1 (by decide)
-- `Nat.Prime.pow_inj'` idx 5: p = 2, q = 4, m = 2, n = 1
theorem c1_36 : ¬ drop0% Nat.Prime.pow_inj' 5 := fun h =>
  absurd (h (p := 2) (q := 4) (m := 2) (n := 1) Nat.prime_two (by decide) (by decide) (by decide)).1 (by decide)
-- `Nat.Prime.pow_inj'` idx 8: p = 2, q = 3, m = n = 1
theorem c1_37 : ¬ drop0% Nat.Prime.pow_inj' 8 := fun h =>
  absurd (h (p := 2) (q := 3) (m := 1) (n := 1) Nat.prime_two Nat.prime_three (by decide) (by decide)).1 (by decide)
-- `Nat.Prime.pow_inj'` idx 6: removable, p ^ 0 = 1 is no power q ^ n with n ≠ 0
theorem c1_38 : drop% Nat.Prime.pow_inj' 6 := by
  intro p q m n hp hq hn h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact absurd h.symm (by rw [pow_zero]; exact (Nat.one_lt_pow hn hq.one_lt).ne')
  · exact Nat.Prime.pow_inj' hp hq hm.ne' hn h
-- `Nat.Prime.pow_inj'` idx 7: removable, q ^ 0 = 1 is no power p ^ m with m ≠ 0
theorem c1_39 : drop% Nat.Prime.pow_inj' 7 := by
  intro p q m n hp hq hm h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd h (by rw [pow_zero]; exact (Nat.one_lt_pow hm hp.one_lt).ne')
  · exact Nat.Prime.pow_inj' hp hq hm hn.ne' h
-- `Nat.Squarefree.ext_iff` idx 2: n = 4, m = 2
theorem c1_40 : ¬ drop0% Nat.Squarefree.ext_iff 2 := fun h => by
  have := (h (n := 4) (m := 2) Nat.squarefree_two).2 (fun p hp =>
    ⟨fun hd => hp.dvd_of_dvd_pow (n := 2) (by simpa using hd), fun hd => hd.trans (by decide)⟩)
  exact absurd this (by decide)
-- `Nat.Squarefree.ext_iff` idx 3: n = 2, m = 4
theorem c1_41 : ¬ drop0% Nat.Squarefree.ext_iff 3 := fun h => by
  have := (h (n := 2) (m := 4) Nat.squarefree_two).2 (fun p hp =>
    ⟨fun hd => hd.trans (by decide), fun hd => hp.dvd_of_dvd_pow (n := 2) (by simpa using hd)⟩)
  exact absurd this (by decide)

-- `Nat.nth_of_card_le` idx 1: p = True is infinite
theorem c1_42 : ¬ indep0% Nat.nth_of_card_le 1 := fun h => inf_true (h (p := fun _ => True) (n := 0))
-- `Nat.nth_of_card_le` idx 3: p = (· ∈ {1}), n = 0
theorem c1_43 : ¬ drop0% Nat.nth_of_card_le 3 := fun h => by
  have := h (p := (· ∈ ({1} : Finset ℕ))) (fts _) (n := 0)
  rw [show Nat.nth (· ∈ ({1} : Finset ℕ)) 0 = 1 from nthv _ (by decide) (by decide)] at this
  exact absurd this (by decide)
-- `Nat.nth_eq_getD_sort` idx 1: p = True is infinite
theorem c1_44 : ¬ indep0% Nat.nth_eq_getD_sort 1 := fun h => inf_true (h (p := fun _ => True) 0)
-- `Nat.nth_eq_orderEmbOfFin` idx 1: p = True is infinite
theorem c1_45 : ¬ indep0% Nat.nth_eq_orderEmbOfFin 1 := fun h => inf_true (h (p := fun _ => True) (n := 0))
-- `Nat.nth_strictMonoOn` idx 1: p = True is infinite
theorem c1_46 : ¬ indep0% Nat.nth_strictMonoOn 1 := fun h => inf_true (h (p := fun _ => True))
-- `Nat.nth_lt_nth_of_lt_card` idx 1: p = True is infinite
theorem c1_47 : ¬ indep0% Nat.nth_lt_nth_of_lt_card 1 := fun h =>
  inf_true (h (p := fun _ => True) (m := 0) (n := 1) (by decide))
-- `Nat.nth_le_nth_of_lt_card` idx 1: p = True is infinite
theorem c1_48 : ¬ indep0% Nat.nth_le_nth_of_lt_card 1 := fun h =>
  inf_true (h (p := fun _ => True) (m := 0) (n := 0) le_rfl)
-- `Nat.nth_le_nth_of_lt_card` idx 4: p = (· ∈ {1,2}), m = 1, n = 0
theorem c1_49 : ¬ drop0% Nat.nth_le_nth_of_lt_card 4 := fun h => by
  have := h (p := (· ∈ ({1, 2} : Finset ℕ))) (fts _) (m := 1) (n := 0) (by rw [tf]; decide)
  rw [show Nat.nth (· ∈ ({1, 2} : Finset ℕ)) 0 = 1 from nthv _ (by decide) (by decide),
    show Nat.nth (· ∈ ({1, 2} : Finset ℕ)) 1 = 2 from nthv _ (by decide) (by decide)] at this
  exact absurd this (by decide)
-- `Nat.nth_le_nth_of_lt_card` idx 5: p = (· ∈ {1}), m = 0, n = 1
theorem c1_50 : ¬ drop0% Nat.nth_le_nth_of_lt_card 5 := fun h => by
  have := h (p := (· ∈ ({1} : Finset ℕ))) (fts _) (m := 0) (n := 1) (by decide)
  rw [show Nat.nth (· ∈ ({1} : Finset ℕ)) 0 = 1 from nthv _ (by decide) (by decide),
    nth_big _ (by decide)] at this
  exact absurd this (by decide)
-- `Nat.lt_of_nth_lt_nth_of_lt_card` idx 1: p = True is infinite
theorem c1_51 : ¬ indep0% Nat.lt_of_nth_lt_nth_of_lt_card 1 := fun h =>
  inf_true (h (p := fun _ => True) (m := 0) (n := 1) (by rw [nth_true, nth_true]; decide))
-- `Nat.lt_of_nth_lt_nth_of_lt_card` idx 5: p = (· ∈ {1}), m = 1, n = 0
theorem c1_52 : ¬ drop0% Nat.lt_of_nth_lt_nth_of_lt_card 5 := fun h => by
  have := h (p := (· ∈ ({1} : Finset ℕ))) (fts _) (m := 1) (n := 0)
    (by rw [show Nat.nth (· ∈ ({1} : Finset ℕ)) 0 = 1 from nthv _ (by decide) (by decide),
      nth_big _ (by decide)]; decide)
  exact absurd this (by decide)
-- `Nat.le_of_nth_le_nth_of_lt_card` idx 1: p = True is infinite
theorem c1_53 : ¬ indep0% Nat.le_of_nth_le_nth_of_lt_card 1 := fun h =>
  inf_true (h (p := fun _ => True) (m := 0) (n := 0) le_rfl)
-- `Nat.le_of_nth_le_nth_of_lt_card` idx 4: p = (· ∈ {1,2}), m = 1, n = 0
theorem c1_54 : ¬ drop0% Nat.le_of_nth_le_nth_of_lt_card 4 := fun h => by
  have := h (p := (· ∈ ({1, 2} : Finset ℕ))) (fts _) (m := 1) (n := 0) (by rw [tf]; decide)
  exact absurd this (by decide)
-- `Nat.nth_injOn` idx 1: p = True is infinite
theorem c1_55 : ¬ indep0% Nat.nth_injOn 1 := fun h => inf_true (h (p := fun _ => True))
-- `Nat.range_nth_of_finite` idx 1: p = (0 < ·), infinite, 0 not in the range
theorem c1_56 : ¬ drop0% Nat.range_nth_of_finite 1 := fun h => by
  have hi : (Set.ofPred (fun n : ℕ => 0 < n)).Infinite := Set.Ioi_infinite 0
  have h0 : (0 : ℕ) ∈ Set.range (Nat.nth (fun n : ℕ => 0 < n)) := by
    rw [h]; exact Set.mem_insert _ _
  obtain ⟨k, hk⟩ := h0
  have := Nat.nth_mem_of_infinite hi k
  rw [hk] at this; exact absurd this (lt_irrefl 0)
-- `Nat.image_nth_Iio_card` idx 1: p = True is infinite
theorem c1_57 : ¬ indep0% Nat.image_nth_Iio_card 1 := fun h => inf_true (h (p := fun _ => True))
-- `Nat.exists_lt_card_finite_nth_eq` idx 1: p = True is infinite
theorem c1_58 : ¬ indep0% Nat.exists_lt_card_finite_nth_eq 1 := fun h =>
  inf_true (h (p := fun _ => True) (x := 0) trivial)
-- `Nat.nth_injective` idx 1: p = False, nth is constantly 0
theorem c1_59 : ¬ drop0% Nat.nth_injective 1 := fun h => by
  have := @h (· ∈ (∅ : Finset ℕ)) 0 1 (by rw [nth_big _ (by decide), nth_big _ (by decide)])
  exact absurd this (by decide)
-- `Nat.nth_monotone` idx 1: p = (· ∈ {1}), nth 0 = 1, nth 1 = 0
theorem c1_60 : ¬ drop0% Nat.nth_monotone 1 := fun h => by
  have := @h (· ∈ ({1} : Finset ℕ)) 0 1 (by decide)
  rw [show Nat.nth (· ∈ ({1} : Finset ℕ)) 0 = 1 from nthv _ (by decide) (by decide),
    nth_big _ (by decide)] at this
  exact absurd this (by decide)
-- `Nat.nth_le_nth'` idx 4: p = (· ∈ {1}), m = 0, n = 1
theorem c1_61 : ¬ drop0% Nat.nth_le_nth' 4 := fun h => by
  have := h (p := (· ∈ ({1} : Finset ℕ))) (m := 0) (n := 1) (by decide)
  rw [show Nat.nth (· ∈ ({1} : Finset ℕ)) 0 = 1 from nthv _ (by decide) (by decide),
    nth_big _ (by decide)] at this
  exact absurd this (by decide)
-- `Nat.isLeast_nth_of_lt_card` idx 2: p = True is infinite
theorem c1_62 : ¬ indep0% Nat.isLeast_nth_of_lt_card 2 := fun h => inf_true (h (p := fun _ => True) (n := 0))
-- `Nat.nth_zero_of_zero` idx 1: p = (· ∈ {1})
theorem c1_63 : ¬ drop0% Nat.nth_zero_of_zero 1 := fun h => by
  have := h (p := (· ∈ ({1} : Finset ℕ)))
  rw [show Nat.nth (· ∈ ({1} : Finset ℕ)) 0 = 1 from nthv _ (by decide) (by decide)] at this
  exact absurd this (by decide)
-- `Nat.lt_card_toFinset_of_nth_ne_zero` idx 3: p = True is infinite
theorem c1_64 : ¬ indep0% Nat.lt_card_toFinset_of_nth_ne_zero 3 := fun h =>
  inf_true (h (p := fun _ => True) (n := 1) (by rw [nth_true]; decide))
-- `Nat.nth_eq_zero_mono` idx 5: p = (· ∈ {1}), a = b = 0
theorem c1_65 : ¬ drop0% Nat.nth_eq_zero_mono 5 := fun h => by
  have := h (p := (· ∈ ({1} : Finset ℕ))) (by decide) (a := 0) (b := 0) le_rfl
  rw [show Nat.nth (· ∈ ({1} : Finset ℕ)) 0 = 1 from nthv _ (by decide) (by decide)] at this
  exact absurd this (by decide)
-- `Nat.nth_ne_zero_anti` idx 4: p = (· ∈ {1}), a = 1, b = 0
theorem c1_66 : ¬ drop0% Nat.nth_ne_zero_anti 4 := fun h => by
  have := h (p := (· ∈ ({1} : Finset ℕ))) (by decide) (a := 1) (b := 0)
    (by rw [show Nat.nth (· ∈ ({1} : Finset ℕ)) 0 = 1 from nthv _ (by decide) (by decide)]; decide)
  exact this (nth_big _ (by decide))
-- `Nat.le_nth_of_lt_nth_succ` idx 4: p = (· ∈ {0,5}), k = 0, a = 3
theorem c1_67 : ¬ drop0% Nat.le_nth_of_lt_nth_succ 4 := fun h => by
  have e0 : Nat.nth (· ∈ ({0, 5} : Finset ℕ)) 0 = 0 := nthv _ (by decide) (by decide)
  have e1 : Nat.nth (· ∈ ({0, 5} : Finset ℕ)) 1 = 5 := nthv _ (by decide) (by decide)
  have := h (p := (· ∈ ({0, 5} : Finset ℕ))) (k := 0) (a := 3) (by rw [e1]; decide)
  rw [e0] at this; exact absurd this (by decide)
-- `Nat.nth_mem_anti` idx 3: p = (· ∈ {1}), a = 1, b = 0
theorem c1_68 : ¬ drop0% Nat.nth_mem_anti 3 := fun h => by
  have e0 : Nat.nth (· ∈ ({1} : Finset ℕ)) 0 = 1 := nthv _ (by decide) (by decide)
  have := h (p := (· ∈ ({1} : Finset ℕ))) (a := 1) (b := 0) (by rw [e0]; decide)
  rw [nth_big _ (by decide)] at this; exact absurd this (by decide)

-- `Nat.nth_le_of_strictMonoOn_of_mapsTo` idx 2: p = (· ∈ {5}), f = id, n = 0
theorem c1_69 : ¬ drop0% Nat.nth_le_of_strictMonoOn_of_mapsTo 2 := fun h => by
  have := h (p := (· ∈ ({5} : Finset ℕ))) id (strictMono_id.strictMonoOn _) (n := 0)
  rw [show Nat.nth (· ∈ ({5} : Finset ℕ)) 0 = 5 from nthv _ (by decide) (by decide)] at this
  exact absurd this (by decide)
-- `Nat.nth_le_of_strictMonoOn_of_mapsTo` idx 3: p = (· ∈ {1,2}), f = const 1, n = 1
theorem c1_70 : ¬ drop0% Nat.nth_le_of_strictMonoOn_of_mapsTo 3 := fun h => by
  have := h (p := (· ∈ ({1, 2} : Finset ℕ))) (fun _ => 1) (fun _ _ => show (1:ℕ) ∈ ({1, 2} : Finset ℕ) by decide) (n := 1)
  rw [show Nat.nth (· ∈ ({1, 2} : Finset ℕ)) 1 = 2 from nthv _ (by decide) (by decide)] at this
  exact absurd this (by decide)
-- `Nat.le_nth_of_monotoneOn_of_surjOn` idx 3: p = (· ∈ {1,2}), f 0 = 2, f n = 1 otherwise, n = 0
theorem c1_71 : ¬ drop0% Nat.le_nth_of_monotoneOn_of_surjOn 3 := fun h => by
  have := h (p := (· ∈ ({1, 2} : Finset ℕ))) (fun n => if n = 0 then 2 else 1)
    (by
      intro y hy
      have : y = 1 ∨ y = 2 := by simpa using hy
      rcases this with rfl | rfl
      exacts [⟨1, memS _ (by decide), rfl⟩, ⟨0, memS _ (by decide), rfl⟩])
    (n := 0) (memS _ (by decide))
  rw [show Nat.nth (· ∈ ({1, 2} : Finset ℕ)) 0 = 1 from nthv _ (by decide) (by decide)] at this
  exact absurd this (by decide)
-- `Nat.le_nth_of_monotoneOn_of_surjOn` idx 5: p = (· ∈ {1}), f = (· + 1), n = 1
theorem c1_72 : ¬ drop0% Nat.le_nth_of_monotoneOn_of_surjOn 5 := fun h => by
  have := h (p := (· ∈ ({1} : Finset ℕ))) (fun n => n + 1)
    (by
      intro y hy
      have : y = 1 := by simpa using hy
      subst this; exact ⟨0, memS _ (by decide), rfl⟩)
    (fun a _ b _ hab => Nat.succ_le_succ hab) (n := 1)
  rw [nth_big _ (by decide)] at this
  exact absurd this (by decide)
-- `Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn` idx 2: p = (1 ≤ ·), f = (· + 2)
theorem c1_73 : ¬ drop0% Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn 2 := fun h => by
  have := h (p := fun n => 1 ≤ n) (fun n => n + 2) (fun x _ => show 1 ≤ x + 2 by omega)
    (fun a _ b _ hab => show a + 2 < b + 2 by omega) (x := 0) memI
  rw [show Nat.nth (fun n : ℕ => 1 ≤ n) 0 = 1 from nthv _ (by decide) (by decide)] at this
  exact absurd this (by decide)
-- `Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn` idx 3: p = (1 ≤ ·), f = id
theorem c1_74 : ¬ drop0% Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn 3 := fun h => by
  have := h (p := fun n => 1 ≤ n) id (fun y _ => ⟨y, memI, rfl⟩)
    (strictMono_id.strictMonoOn _) (x := 0) memI
  rw [show Nat.nth (fun n : ℕ => 1 ≤ n) 0 = 1 from nthv _ (by decide) (by decide)] at this
  exact absurd this (by decide)
-- `Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn` idx 4: p = (· ∈ {1,2}), f 0 = 2, f n = 1 otherwise
theorem c1_75 : ¬ drop0% Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn 4 := fun h => by
  have := h (p := (· ∈ ({1, 2} : Finset ℕ))) (fun n => if n = 0 then 2 else 1)
    (by
      intro y hy
      have : y = 1 ∨ y = 2 := by simpa using hy
      rcases this with rfl | rfl
      exacts [⟨1, memS _ (by decide), rfl⟩, ⟨0, memS _ (by decide), rfl⟩])
    (fun x _ => by by_cases hx : x = 0 <;> simp [hx]) (x := 0) (memS _ (by decide))
  rw [show Nat.nth (· ∈ ({1, 2} : Finset ℕ)) 0 = 1 from nthv _ (by decide) (by decide)] at this
  exact absurd this (by decide)
-- `Nat.nth_comp_of_strictMono` idx 3: p = (· ∈ {1,2}), f 0 = 2, f i = 1 otherwise, n = 0
theorem c1_76 : ¬ drop0% Nat.nth_comp_of_strictMono 3 := fun h => by
  have := h (p := (· ∈ ({1, 2} : Finset ℕ))) (n := 0) (f := fun n => if n = 0 then 2 else 1)
    (by
      intro y hy
      have : y = 1 ∨ y = 2 := by simpa using hy
      rcases this with rfl | rfl
      exacts [⟨1, rfl⟩, ⟨0, rfl⟩])
    (memS _ (by decide))
  rw [Nat.nth_zero_of_zero (by decide),
    show Nat.nth (· ∈ ({1, 2} : Finset ℕ)) 0 = 1 from nthv _ (by decide) (by decide)] at this
  exact absurd this (by decide)
-- `Nat.nth_comp_of_strictMono` idx 4: p = (· ∈ {0}), f = succ, n = 0
theorem c1_77 : ¬ drop0% Nat.nth_comp_of_strictMono 4 := fun h => by
  have := h (p := (· ∈ ({0} : Finset ℕ))) (n := 0) (f := fun n => n + 1) (strictMono_id.add_const 1)
    (memS _ (by decide))
  rw [nth_empty' _ (fun i => by simp) 0,
    show Nat.nth (· ∈ ({0} : Finset ℕ)) 0 = 0 from nthv _ (by decide) (by decide)] at this
  exact absurd this (by decide)
-- `Nat.nth_comp_of_strictMono` idx 5: p = False, f = succ, n = 0
theorem c1_78 : ¬ drop0% Nat.nth_comp_of_strictMono 5 := fun h => by
  have := h (p := (· ∈ (∅ : Finset ℕ))) (n := 0) (f := fun n => n + 1) (strictMono_id.add_const 1)
    (fun k hk => absurd hk (by simp))
  rw [nth_empty' _ (fun i => by simp) 0, nth_big _ (by decide)] at this
  exact absurd this (by decide)
-- `Nat.nth_add` idx 3: p = (· ∈ {1}), m = 2, n = 0
theorem c1_79 : ¬ drop0% Nat.nth_add 3 := fun h => by
  have e : Nat.nth (· ∈ ({1} : Finset ℕ)) 0 = 1 := nthv _ (by decide) (by decide)
  have := h (p := (· ∈ ({1} : Finset ℕ))) (m := 2) (n := 0) (by rw [e]; decide)
  rw [nth_empty' _ (fun i => by simp) 0, e] at this
  exact absurd this (by decide)
-- `Nat.nth_add_eq_sub` idx 3: p = (· ∈ {1,3}), m = 2, n = 0
theorem c1_80 : ¬ drop0% Nat.nth_add_eq_sub 3 := fun h => by
  have e : Nat.nth (· ∈ ({1, 3} : Finset ℕ)) 0 = 1 := nthv _ (by decide) (by decide)
  have := h (p := (· ∈ ({1, 3} : Finset ℕ))) (m := 2) (n := 0) (by rw [e]; decide)
  rw [e, nthv (fun i => i + 2 ∈ ({1, 3} : Finset ℕ)) (n := 1) (by decide) (by decide)] at this
  exact absurd this (by decide)
-- `Nat.filter_range_nth_eq_insert_of_finite` idx 2: p = True is infinite
theorem c1_81 : ¬ indep0% Nat.filter_range_nth_eq_insert_of_finite 2 := fun h =>
  inf_true (@h (fun _ => True) inferInstance 0)
-- `Nat.count_nth_of_lt_card_finite` idx 3: p = True is infinite
theorem c1_82 : ¬ indep0% Nat.count_nth_of_lt_card_finite 3 := fun h =>
  inf_true (@h (fun _ => True) inferInstance 0)
-- `Nat.surjective_count_of_infinite_setOfPred` idx 2: p = False, count is constantly 0
theorem c1_83 : ¬ drop0% Nat.surjective_count_of_infinite_setOfPred 2 := fun h => by
  obtain ⟨n, hn⟩ := @h (fun _ => False) inferInstance 1
  simp [Nat.count_eq_card_filter_range] at hn
-- `Nat.surjective_count_of_infinite_setOf` idx 2: p = False, count is constantly 0
theorem c1_84 : ¬ drop0% Nat.surjective_count_of_infinite_setOf 2 := fun h => by
  obtain ⟨n, hn⟩ := @h (fun _ => False) inferInstance 1
  simp [Nat.count_eq_card_filter_range] at hn
-- `Nat.nth_add_one_le_iff` idx 1: p = (· ∈ {1}), n = 0, q = 1
theorem c1_85 : ¬ drop0% Nat.nth_add_one_le_iff 1 := fun h => by
  have := (h (p := (· ∈ ({1} : Finset ℕ))) (n := 0) (q := 1) (by decide)).1
    (by rw [nth_big _ (by decide)]; decide)
  rw [show Nat.nth (· ∈ ({1} : Finset ℕ)) 0 = 1 from nthv _ (by decide) (by decide)] at this
  exact absurd this (by decide)
-- `Nat.nth_add_one_le_iff` idx 4: p = (· ≠ 1), n = 0, q = 1
theorem c1_86 : ¬ drop0% Nat.nth_add_one_le_iff 4 := fun h => by
  have hi : (Set.ofPred (fun n : ℕ => n ≠ 1)).Infinite := (Set.finite_singleton 1).infinite_compl
  have := (h (p := fun n : ℕ => n ≠ 1) hi (n := 0) (q := 1)).2
    (by rw [show Nat.nth (fun n : ℕ => n ≠ 1) 0 = 0 from nthv _ (by decide) (by decide)]; decide)
  rw [show Nat.nth (fun n : ℕ => n ≠ 1) (0 + 1) = 2 from nthv _ (by decide) (by decide)] at this
  exact absurd this (by decide)

-- `Option.mem_pmem` idx 6: x = some (), p = False
theorem c1_87 : ¬ indep0% Option.mem_pmem 6 := fun h =>
  h (α := Unit) (β := Unit) (p := fun _ => False) (fun _ h => h.elim) (some ()) (a := ()) rfl () rfl
-- `Option.mem_pmem` idx 7: x = none
theorem c1_88 : ¬ indep0% Option.mem_pmem 7 := fun h => by
  have := h (α := Unit) (β := Unit) (p := fun _ => True) (fun _ _ => ()) none (a := ()) (fun _ _ => trivial)
  simp at this
-- `Option.pmap_bind` idx 7: x = some (), g = some, p = False
theorem c1_89 : ¬ indep0% Option.pmap_bind 7 := fun h =>
  h (α := Unit) (β := Unit) (γ := Unit) (x := some ()) (g := some) (p := fun _ => False)
    (f := fun _ h => h.elim) (fun a b _ => by cases a; cases b; rfl) () rfl
-- `Option.pmap_bind` idx 8: x = none, g = some, p = True
theorem c1_90 : ¬ indep0% Option.pmap_bind 8 := fun h => by
  have := h (α := Unit) (β := Unit) (γ := Unit) (x := none) (g := some) (p := fun _ => True)
    (f := fun _ _ => ()) (fun _ _ => trivial) () () rfl
  simp at this
-- `Option.bind_pmap` idx 7: x = some (), p = False
theorem c1_91 : ¬ indep0% Option.bind_pmap 7 := fun h =>
  h (α := Unit) (β := Unit) (γ := Unit) (p := fun _ => False) (fun _ h => h.elim) (some ()) some () rfl
-- `Option.pbind_eq_none` idx 4: x = some (), f = none
theorem c1_92 : ¬ drop0% Option.pbind_eq_none 4 := fun h => by
  have := (h (α := Unit) (β := Unit) (x := some ()) (f := fun _ _ => none)).1 rfl
  simp at this
-- `Option.join_pmap_eq_pmap_join` idx 5: x = some (some ()), p = False
theorem c1_93 : ¬ indep0% Option.join_pmap_eq_pmap_join 5 := fun h =>
  h (α := Unit) (β := Unit) (p := fun _ => False) (f := fun _ h => h.elim) (x := some (some ()))
    (some ()) rfl () rfl
-- `Option.pmap_bind_id_eq_pmap_join` idx 5: x = some (some ()), p = False
theorem c1_94 : ¬ indep0% Option.pmap_bind_id_eq_pmap_join 5 := fun h =>
  h (α := Unit) (β := Unit) (p := fun _ => False) (f := fun _ h => h.elim) (x := some (some ()))
    (some ()) rfl () rfl
-- `Option.choice_eq_none` idx 1: α = Unit
theorem c1_95 : ¬ drop0% Option.choice_eq_none 1 := fun h =>
  Option.choice_eq_none_iff_not_nonempty.1 (h Unit) ⟨()⟩
-- `Option.map₂_assoc` idx 13: Bool, outer functions constant true / false
theorem c1_96 : ¬ drop0% Option.map₂_assoc 13 := fun h =>
  absurd (h (a := some true) (b := some true) (c := some true) (f := fun (_ : Bool) (_ : Bool) => true)
    (g := fun (_ : Bool) (_ : Bool) => true) (f' := fun (_ : Bool) (_ : Bool) => false)
    (g' := fun (_ : Bool) (_ : Bool) => true)) (by decide)
-- `Option.map₂_left_comm` idx 13: Bool, outer functions constant true / false
theorem c1_97 : ¬ drop0% Option.map₂_left_comm 13 := fun h =>
  absurd (h (a := some true) (b := some true) (c := some true) (f := fun (_ : Bool) (_ : Bool) => true)
    (g := fun (_ : Bool) (_ : Bool) => true) (f' := fun (_ : Bool) (_ : Bool) => true)
    (g' := fun (_ : Bool) (_ : Bool) => false)) (by decide)
-- `Option.map₂_right_comm` idx 13: Bool, outer functions constant true / false
theorem c1_98 : ¬ drop0% Option.map₂_right_comm 13 := fun h =>
  absurd (h (a := some true) (b := some true) (c := some true) (f := fun (_ : Bool) (_ : Bool) => true)
    (g := fun (_ : Bool) (_ : Bool) => true) (f' := fun (_ : Bool) (_ : Bool) => true)
    (g' := fun (_ : Bool) (_ : Bool) => false)) (by decide)
-- `Option.map_map₂_distrib_left` idx 11: Bool, outer functions constant true / false
theorem c1_99 : ¬ drop0% Option.map_map₂_distrib_left 11 := fun h =>
  absurd (h (a := some true) (b := some true) (f := fun (_ : Bool) (_ : Bool) => true)
    (g := fun (_ : Bool) => true) (f' := fun (_ : Bool) (_ : Bool) => false)
    (g' := fun (_ : Bool) => true)) (by decide)
-- `Option.map₂_map_left_comm` idx 11: Bool, outer functions constant true / false
theorem c1_100 : ¬ drop0% Option.map₂_map_left_comm 11 := fun h =>
  absurd (h (a := some true) (b := some true) (f := fun (_ : Bool) (_ : Bool) => true)
    (g := fun (_ : Bool) => true) (f' := fun (_ : Bool) (_ : Bool) => true)
    (g' := fun (_ : Bool) => false)) (by decide)
-- `Option.map_map₂_antidistrib_left` idx 11: Bool, outer functions constant true / false
theorem c1_101 : ¬ drop0% Option.map_map₂_antidistrib_left 11 := fun h =>
  absurd (h (a := some true) (b := some true) (f := fun (_ : Bool) (_ : Bool) => true)
    (g := fun (_ : Bool) => true) (f' := fun (_ : Bool) (_ : Bool) => false)
    (g' := fun (_ : Bool) => true)) (by decide)
-- `Option.map₂_map_left_anticomm` idx 11: Bool, outer functions constant true / false
theorem c1_102 : ¬ drop0% Option.map₂_map_left_anticomm 11 := fun h =>
  absurd (h (a := some true) (b := some true) (f := fun (_ : Bool) (_ : Bool) => true)
    (g := fun (_ : Bool) => true) (f' := fun (_ : Bool) (_ : Bool) => true)
    (g' := fun (_ : Bool) => false)) (by decide)
-- `Nat.minSqFacProp_div` idx 2: n = 8, k = 4, o = none
theorem c1_103 : ¬ drop0% Nat.minSqFacProp_div 2 := fun h => by
  have := h 8 (k := 4) (by decide) (by decide) (o := none) (show Squarefree 2 from Nat.squarefree_two)
  exact absurd (Nat.isUnit_iff.1 ((show Squarefree 8 from this) 2 ⟨2, rfl⟩)) (by decide)
-- `Nat.minSqFacProp_div` idx 3: n = 9, k = 2, o = some 2
theorem c1_104 : ¬ drop0% Nat.minSqFacProp_div 3 := fun h => by
  have := h 9 (k := 2) Nat.prime_two (by decide) (o := some 2)
    (show Nat.Prime 2 ∧ 2 * 2 ∣ 4 ∧ ∀ p, Nat.Prime p → p * p ∣ 4 → 2 ≤ p from
      ⟨Nat.prime_two, by decide, fun p hp _ => hp.two_le⟩)
  exact absurd (show 2 * 2 ∣ 9 from this.2.1) (by decide)
-- `Nat.minSqFacProp_div` idx 4: n = 4, k = 2, o = none
theorem c1_105 : ¬ drop0% Nat.minSqFacProp_div 4 := fun h => by
  have := h 4 (k := 2) Nat.prime_two (by decide) (o := none) (show Squarefree 2 from Nat.squarefree_two)
  exact absurd (Nat.isUnit_iff.1 ((show Squarefree 4 from this) 2 ⟨1, rfl⟩)) (by decide)
-- `Nat.minSqFacProp_div` idx 6: n = 18, k = 2, o = none
theorem c1_106 : ¬ drop0% Nat.minSqFacProp_div 6 := fun h => by
  have := h 18 (k := 2) Nat.prime_two (by decide) (by decide) (o := none)
  exact absurd (Nat.isUnit_iff.1 ((show Squarefree 18 from this) 3 ⟨2, rfl⟩)) (by decide)
-- `Nat.minSqFacAux_has_prop` idx 2: removable, n = 0 contradicts ih at m = 2 since k ≥ 3
theorem c1_107 : drop% Nat.minSqFacAux_has_prop 2 := by
  intro n k i e ih
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd (ih 2 Nat.prime_two (dvd_zero 2)) (by omega)
  · exact Nat.minSqFacAux_has_prop k hn i e ih
-- `Nat.minSqFacAux_has_prop` idx 4: n = 1, k = 1 gives some 1
theorem c1_108 : ¬ drop0% Nat.minSqFacAux_has_prop 4 := fun h => by
  have := h (n := 1) 1 (by decide) 0 (fun m hm _ => hm.one_le)
  have e : Nat.minSqFacAux 1 1 = some 1 := by rw [Nat.minSqFacAux]; simp
  rw [e] at this
  exact Nat.not_prime_one (show Nat.Prime 1 ∧ _ from this).1
-- `Nat.minSqFacAux_has_prop` idx 5: n = 4, k = 3 gives none
theorem c1_109 : ¬ drop0% Nat.minSqFacAux_has_prop 5 := fun h => by
  have := h (n := 4) 3 (by decide) 0 (by decide)
  have e : Nat.minSqFacAux 4 3 = none := by rw [Nat.minSqFacAux]; simp
  rw [e] at this
  exact absurd (Nat.isUnit_iff.1 ((show Squarefree 4 from this) 2 ⟨1, rfl⟩)) (by decide)
-- `Nat.minSqFac_le_of_dvd` idx 5: n = 9, m = 2
theorem c1_110 : ¬ drop0% Nat.minSqFac_le_of_dvd 5 := fun h => by
  have hp := Nat.minSqFac_has_prop 9
  rcases hd : Nat.minSqFac 9 with _ | d
  · rw [hd] at hp
    exact absurd (Nat.isUnit_iff.1 ((show Squarefree 9 from hp) 3 ⟨1, rfl⟩)) (by decide)
  · rw [hd] at hp
    obtain ⟨hpd, hdd, -⟩ := hp
    have h2 := h hd (m := 2) le_rfl
    have h3 := hpd.two_le
    obtain rfl : d = 2 := by omega
    exact absurd hdd (by decide)
-- `Nat.coprime_div_gcd_of_squarefree` idx 3: removable, for n = 0 the quotient is m / m = 1
theorem c1_111 : drop% Nat.coprime_div_gcd_of_squarefree 3 := by
  intro m n hm
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.div_self (Nat.pos_of_ne_zero hm.ne_zero)]
  · exact Nat.coprime_div_gcd_of_squarefree hm hn
-- `Nat.primeFactors_prod` idx 1: s = {4}
theorem c1_112 : ¬ drop0% Nat.primeFactors_prod 1 := fun h => by
  have e := h (s := {4})
  have h4 : 4 ∈ (∏ p ∈ ({4} : Finset ℕ), p).primeFactors := by rw [e]; simp
  exact absurd (Nat.prime_of_mem_primeFactors h4) (by decide)
-- `Nat.prod_primeFactors_sdiff_of_squarefree` idx 3: n = 1, t = {2}
theorem c1_113 : ¬ drop0% Nat.prod_primeFactors_sdiff_of_squarefree 3 := fun h => by
  have := h (n := 1) squarefree_one (t := {2})
  simp at this
-- `ZMod.card_units_eq_totient` idx 1: n = 0
theorem c1_114 : ¬ drop0% ZMod.card_units_eq_totient 1 := fun h => by
  letI : Fintype (ZMod 0)ˣ := inferInstanceAs (Fintype ℤˣ)
  have := h 0
  rw [Nat.totient_zero] at this
  exact (Fintype.card_eq_zero_iff.1 this).elim 1
-- `Nat.Upto.wf` idx 1: p = False, the identity is an increasing sequence
theorem c1_115 : ¬ drop0% Nat.Upto.wf 1 := fun h => by
  obtain ⟨n, hn⟩ := @WellFounded.not_rel_apply_succ _ _ (h (p := fun _ => False))
    (fun n => ⟨n, fun _ _ h => h⟩)
  exact hn (Nat.lt_succ_self n)
-- `Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul` idx 6: removable, the valuation of n is exactly l
theorem c1_116 : drop% Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul 6 := by
  intro p hp m n k l hn hmn
  by_contra hc
  rw [not_or] at hc
  obtain ⟨n', rfl⟩ := hn
  have hn' : ¬ p ∣ n' := fun ⟨c, hc'⟩ => hc.2 ⟨c, by rw [hc', pow_succ]; ring⟩
  have h1 : p ^ (k + 1) ∣ m * n' := by
    have e : p ^ (k + l + 1) = p ^ l * p ^ (k + 1) := by rw [← pow_add]; ring_nf
    rw [e, show m * (p ^ l * n') = p ^ l * (m * n') by ring] at hmn
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos l) hmn
  have hcop : Nat.Coprime (p ^ (k + 1)) n' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hn')
  exact hc.1 (hcop.dvd_of_dvd_mul_right h1)
-- `Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul` idx 7: removable, the valuation of m is exactly k
theorem c1_117 : drop% Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul 7 := by
  intro p hp m n k l hm hmn
  by_contra hc
  rw [not_or] at hc
  obtain ⟨m', rfl⟩ := hm
  have hm' : ¬ p ∣ m' := fun ⟨c, hc'⟩ => hc.1 ⟨c, by rw [hc', pow_succ]; ring⟩
  have h1 : p ^ (l + 1) ∣ m' * n := by
    have e : p ^ (k + l + 1) = p ^ k * p ^ (l + 1) := by rw [← pow_add]; ring_nf
    rw [e, show p ^ k * m' * n = p ^ k * (m' * n) by ring] at hmn
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos k) hmn
  have hcop : Nat.Coprime (p ^ (l + 1)) m' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hm')
  exact hc.2 (hcop.dvd_of_dvd_mul_left h1)

namespace W3c1
open Ordnode
/-- Sizedness check for trees over ℕ. -/
def szd : Ordnode ℕ → Bool
  | .nil => true
  | .node s l _ r => s == l.size + r.size + 1 && szd l && szd r
theorem szd_of {t : Ordnode ℕ} (h : t.Sized) : szd t = true := by
  induction t with
  | nil => rfl
  | node s l x r ihl ihr =>
    obtain ⟨e, hl, hr⟩ := h
    simp [szd, e, ihl hl, ihr hr]
theorem sized_of {t : Ordnode ℕ} (h : szd t = true) : t.Sized := by
  induction t with
  | nil => trivial
  | node s l x r ihl ihr =>
    simp only [szd, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1, ihl h.1.2, ihr h.2⟩
/-- Pre-order encoding of a tree over ℕ (sizes and values). -/
def enc : Ordnode ℕ → List ℕ
  | .nil => [0]
  | .node s l x r => [1, s, x] ++ enc l ++ enc r
/-- A two-element type whose `≤` is equality (not total). -/
def E := Bool
instance : LE E := ⟨fun a b => a = b⟩
instance : DecidableRel (α := E) (· ≤ ·) := fun a b => (inferInstance : DecidableEq Bool) a b
def ea : E := true
def eb : E := false
def encE : Ordnode E → List Bool
  | .nil => [false]
  | .node s l x r => [true, x] ++ encE l ++ encE r
end W3c1
open W3c1

-- `Ordnode.Sized.induction` idx 2: t = node 5 nil 0 nil (not sized), C = Sized
theorem c1_118 : ¬ drop0% Ordnode.Sized.induction 2 := fun h =>
  absurd (szd_of (h (t := Ordnode.node 5 .nil 0 .nil) (C := Ordnode.Sized) trivial
    (fun _ _ _ hl hr => Ordnode.Sized.node' hl hr))) (by decide)
-- `Ordnode.Sized.induction` idx 4: t = nil, C = False
theorem c1_119 : ¬ drop0% Ordnode.Sized.induction 4 := fun h =>
  h (α := ℕ) (t := .nil) trivial (C := fun _ => False) (fun _ _ _ h _ => h)
-- `Ordnode.Sized.induction` idx 5: t = node 1 nil 0 nil, C = (· = nil)
theorem c1_120 : ¬ drop0% Ordnode.Sized.induction 5 := fun h => by
  have := h (t := Ordnode.node 1 .nil 0 .nil) (sized_of (by decide)) (C := fun t => t = .nil) rfl
  simp at this
-- `Ordnode.Balanced.dual` idx 2: an unbalanced chain
theorem c1_121 : ¬ drop0% Ordnode.Balanced.dual 2 := fun h =>
  absurd (h (t := Ordnode.node 3 .nil 0 (.node 2 .nil 1 (.node 1 .nil 2 .nil)))) (by decide)
-- `Ordnode.Sized.rotateR` idx 4: l has an unsized left child
theorem c1_122 : ¬ drop0% Ordnode.Sized.rotateR 4 := fun h =>
  absurd (szd_of (h (l := Ordnode.node 1 (.node 7 .nil 0 .nil) 1 .nil) (x := 2) (r := .nil) trivial))
    (by decide)
-- `Ordnode.size_balance'` idx 4: l with wrong stored size
theorem c1_123 : ¬ drop0% Ordnode.size_balance' 4 := fun h =>
  absurd (h (l := Ordnode.node 9 (.node 1 .nil 0 .nil) 1 .nil) (x := 2) (r := .nil) trivial) (by decide)
-- `Ordnode.size_balance'` idx 5: r with wrong stored size
theorem c1_124 : ¬ drop0% Ordnode.size_balance' 5 := fun h =>
  absurd (h (l := .nil) (x := 0) (r := Ordnode.node 5 .nil 1 (.node 1 .nil 2 .nil)) trivial) (by decide)
-- `Ordnode.dual_insert` idx 2: ≤ is equality on a two-element type
theorem c1_125 : ¬ drop0% Ordnode.dual_insert 2 := fun h =>
  absurd (congrArg encE (h (α := E) ea (Ordnode.node 1 .nil eb .nil))) (by decide)
-- `Ordnode.balance_eq_balance'` idx 4: l = unbalanced right chain, r = nil
theorem c1_126 : ¬ drop0% Ordnode.balance_eq_balance' 4 := fun h =>
  absurd (congrArg enc (h (l := Ordnode.node 3 .nil 0 (.node 2 .nil 1 (.node 1 .nil 2 .nil))) (x := 5)
    (r := .nil) trivial (sized_of (by decide)) trivial)) (by decide)
-- `Ordnode.balance_eq_balance'` idx 5: l = nil, r = unbalanced left chain
theorem c1_127 : ¬ drop0% Ordnode.balance_eq_balance' 5 := fun h =>
  absurd (congrArg enc (h (l := .nil) (x := 5)
    (r := Ordnode.node 3 (.node 2 (.node 1 .nil 0 .nil) 1 .nil) 2 .nil) trivial trivial
    (sized_of (by decide)))) (by decide)
-- `Ordnode.balanceL_eq_balance` idx 4: l = node 0 nil 0 nil (stored size 0), r a singleton
theorem c1_128 : ¬ drop0% Ordnode.balanceL_eq_balance 4 := fun h =>
  absurd (congrArg enc (h (l := Ordnode.node 0 .nil 0 .nil) (x := 1) (r := .node 1 .nil 2 .nil)
    (sized_of (by decide)) (fun _ => by decide) (fun h _ => absurd h (by decide)))) (by decide)
-- `Ordnode.balanceL_eq_balance` idx 6: l = nil, r of size 2
theorem c1_129 : ¬ drop0% Ordnode.balanceL_eq_balance 6 := fun h =>
  absurd (congrArg enc (h (l := .nil) (x := 0) (r := .node 2 .nil 1 (.node 1 .nil 2 .nil))
    trivial (sized_of (by decide)) (fun h _ => absurd h (by decide)))) (by decide)
-- `Ordnode.balanceL_eq_balance` idx 7: l a singleton, r of size 4
theorem c1_130 : ¬ drop0% Ordnode.balanceL_eq_balance 7 := fun h =>
  absurd (congrArg enc (h (l := .node 1 .nil 0 .nil) (x := 1)
    (r := .node 4 (.node 1 .nil 2 .nil) 3 (.node 2 .nil 4 (.node 1 .nil 5 .nil)))
    (sized_of (by decide)) (sized_of (by decide)) (fun h => absurd h (by decide)))) (by decide)
-- `Ordnode.Raised.right` idx 6: r₁ = nil, r₂ of size 2
theorem c1_131 : ¬ drop0% Ordnode.Raised.right 6 := fun h =>
  absurd (h (l := .nil) (x₁ := 0) (x₂ := 0) (r₁ := .nil) (r₂ := .node 2 .nil 0 (.node 1 .nil 1 .nil)))
    (by unfold Ordnode.Raised; decide)
-- `Ordnode.balanceL_eq_balance'` idx 4: l = unbalanced right chain, r = nil
theorem c1_132 : ¬ drop0% Ordnode.balanceL_eq_balance' 4 := fun h =>
  absurd (congrArg enc (h (l := Ordnode.node 3 .nil 0 (.node 2 .nil 1 (.node 1 .nil 2 .nil))) (x := 5)
    (r := .nil) trivial (sized_of (by decide)) trivial (Or.inr ⟨1, Or.inr rfl, by decide⟩))) (by decide)
-- `Ordnode.balanceL_eq_balance'` idx 8: l = nil, r of size 2
theorem c1_133 : ¬ drop0% Ordnode.balanceL_eq_balance' 8 := fun h =>
  absurd (congrArg enc (h (l := .nil) (x := 0) (r := .node 2 .nil 1 (.node 1 .nil 2 .nil))
    trivial (by decide) trivial (sized_of (by decide)))) (by decide)
-- `Ordnode.balance_sz_dual` idx 3: l = nil, r with stored size 5
theorem c1_134 : ¬ drop0% Ordnode.balance_sz_dual 3 := fun h => by
  rcases h (l := (.nil : Ordnode ℕ)) (r := .node 5 .nil 0 .nil) with ⟨l', hr, hb⟩ | ⟨r', hr, hb⟩ <;>
    simp only [Ordnode.dual, Ordnode.size, Ordnode.Raised, Ordnode.BalancedSz, Ordnode.delta] at hr hb <;>
    omega
-- `Ordnode.size_balanceL` idx 4: l = unbalanced right chain, r = nil
theorem c1_135 : ¬ drop0% Ordnode.size_balanceL 4 := fun h =>
  absurd (h (l := Ordnode.node 3 .nil 0 (.node 2 .nil 1 (.node 1 .nil 2 .nil))) (x := 5)
    (r := .nil) trivial (sized_of (by decide)) trivial (Or.inr ⟨1, Or.inr rfl, by decide⟩)) (by decide)
-- `Ordnode.all_balanceL` idx 5: l = unbalanced right chain, P = (· ≠ 2)
theorem c1_136 : ¬ drop0% Ordnode.all_balanceL 5 := fun h =>
  absurd (h (P := (· ≠ 2)) (l := Ordnode.node 3 .nil 0 (.node 2 .nil 1 (.node 1 .nil 2 .nil))) (x := 5)
    (r := .nil) trivial (sized_of (by decide)) trivial (Or.inr ⟨1, Or.inr rfl, by decide⟩)) (by decide)
-- `Ordnode.all_balanceL` idx 7: l balanced with wrong stored size of its right child, P = (· ≠ 5)
theorem c1_137 : ¬ drop0% Ordnode.all_balanceL 7 := fun h =>
  absurd (h (P := (· ≠ 5)) (l := Ordnode.node 2 .nil 0 (.node 1 (.node 1 .nil 5 .nil) 1 .nil)) (x := 7)
    (r := .nil) (by decide) trivial trivial (Or.inr ⟨1, Or.inr rfl, by decide⟩)) (by decide)
-- `Ordnode.balanceR_eq_balance'` idx 5: l = nil, r = unbalanced left chain
theorem c1_138 : ¬ drop0% Ordnode.balanceR_eq_balance' 5 := fun h =>
  absurd (congrArg enc (h (l := .nil) (x := 5)
    (r := Ordnode.node 3 (.node 2 (.node 1 .nil 2 .nil) 1 .nil) 0 .nil) trivial trivial
    (sized_of (by decide)) (Or.inl ⟨1, Or.inr rfl, by decide⟩))) (by decide)
-- `Ordnode.balanceR_eq_balance'` idx 8: l of size 2, r = nil
theorem c1_139 : ¬ drop0% Ordnode.balanceR_eq_balance' 8 := fun h =>
  absurd (congrArg enc (h (l := .node 2 (.node 1 .nil 0 .nil) 1 .nil) (x := 2) (r := .nil)
    (by decide) trivial (sized_of (by decide)) trivial)) (by decide)
-- `Ordnode.size_balanceR` idx 5: l = nil, r = unbalanced left chain
theorem c1_140 : ¬ drop0% Ordnode.size_balanceR 5 := fun h =>
  absurd (h (l := .nil) (x := 5)
    (r := Ordnode.node 3 (.node 2 (.node 1 .nil 2 .nil) 1 .nil) 0 .nil) trivial trivial
    (sized_of (by decide)) (Or.inl ⟨1, Or.inr rfl, by decide⟩)) (by decide)
-- `Ordnode.all_balanceR` idx 6: l = nil, r = unbalanced left chain, P = (· ≠ 2)
theorem c1_141 : ¬ drop0% Ordnode.all_balanceR 6 := fun h =>
  absurd (h (P := (· ≠ 2)) (l := .nil) (x := 5)
    (r := Ordnode.node 3 (.node 2 (.node 1 .nil 2 .nil) 1 .nil) 0 .nil) trivial trivial
    (sized_of (by decide)) (Or.inl ⟨1, Or.inr rfl, by decide⟩)) (by decide)
-- `Ordnode.all_balanceR` idx 8: r balanced with wrong stored size of its left child, P = (· ≠ 5)
theorem c1_142 : ¬ drop0% Ordnode.all_balanceR 8 := fun h =>
  absurd (h (P := (· ≠ 5)) (l := .nil) (x := 7) (r := Ordnode.node 2 (.node 1 .nil 1 (.node 1 .nil 5 .nil)) 0 .nil)
    trivial (by decide) trivial (Or.inl ⟨1, Or.inr rfl, by decide⟩)) (by decide)
-- `Ordnode.Bounded.of_lt` idx 8: t = {5}, x = 0
theorem c1_143 : ¬ drop0% Ordnode.Bounded.of_lt 8 := fun h => by
  have := h (α := ℕ) (t := .node 1 .nil 5 .nil) (o₁ := ⊥) (o₂ := ⊤) (x := 0)
    (by simp [Ordnode.Bounded]) (by simp [Ordnode.Bounded])
  simp [Ordnode.Bounded] at this
-- `Ordnode.Bounded.of_gt` idx 8: t = {0}, x = 5
theorem c1_144 : ¬ drop0% Ordnode.Bounded.of_gt 8 := fun h => by
  have := h (α := ℕ) (t := .node 1 .nil 0 .nil) (o₁ := ⊥) (o₂ := ⊤) (x := 5)
    (by simp [Ordnode.Bounded]) (by simp [Ordnode.Bounded])
  simp [Ordnode.Bounded] at this
-- `Ordnode.Bounded.to_sep` idx 7: t₁ = {5}, t₂ = {1}, x = 0
theorem c1_145 : ¬ drop0% Ordnode.Bounded.to_sep 7 := fun h => by
  have := h (α := ℕ) (t₁ := .node 1 .nil 5 .nil) (t₂ := .node 1 .nil 1 .nil) (o₁ := ⊥) (o₂ := ⊤) (x := 0)
    (by simp [Ordnode.Bounded])
  simp [Ordnode.All] at this

namespace W3c1
open Ordnode
theorem szL {α : Type*} {l : Ordnode α} {x : α} {r : Ordnode α} (hl : Balanced l) (sl : Sized l)
    (sr : Sized r) : size (balanceL l x r) = size l + size r + 1 := by
  rcases r with _ | ⟨rs, rl, rx, rr⟩
  · rcases l with _ | ⟨ls, ll, lx, lr⟩
    · rfl
    · rcases ll with _ | ⟨lls, lll, llx, llr⟩ <;> rcases lr with _ | ⟨lrs, lrl, lrx, lrr⟩
      · have := sl.1; simp only [balanceL, id, size] at this ⊢; omega
      · have h1 := hl.1; have h2 := sl.2.2.pos; have h3 := sl.1
        simp only [balanceL, id, size, BalancedSz] at h3 h1 ⊢; omega
      · have h1 := hl.1; have h2 := sl.2.1.pos; have h3 := sl.1
        simp only [balanceL, id, size, BalancedSz] at h3 h1 ⊢; omega
      · simp only [balanceL, id, size]; split_ifs <;> rfl
  · rcases l with _ | ⟨ls, ll, lx, lr⟩
    · simp only [balanceL, id, size]; omega
    · have hrs := sr.pos
      by_cases hc : ls > delta * rs
      · have h1 := hl.1
        rcases ll with _ | ⟨lls, lll, llx, llr⟩
        · have := sl.1; simp only [size, BalancedSz, delta] at this h1 hc; omega
        rcases lr with _ | ⟨lrs, lrl, lrx, lrr⟩
        · have := sl.1; simp only [size, BalancedSz, delta] at this h1 hc; omega
        simp only [balanceL, id, hc, if_true]; split_ifs <;> simp only [size]
      · simp only [balanceL, id, hc, if_false, size]
theorem allL {α : Type*} {P : α → Prop} {l : Ordnode α} {x : α} {r : Ordnode α} (hl : Balanced l)
    (sl : Sized l) (sr : Sized r) : All P (balanceL l x r) ↔ All P l ∧ P x ∧ All P r := by
  rcases r with _ | ⟨rs, rl, rx, rr⟩
  · rcases l with _ | ⟨ls, ll, lx, lr⟩
    · simp [balanceL, id, All, Ordnode.singleton]
    · rcases ll with _ | ⟨lls, lll, llx, llr⟩ <;> rcases lr with _ | ⟨lrs, lrl, lrx, lrr⟩
      · simp only [balanceL, id]; simp [All]
      · have h1 := hl.1; have h2 := sl.2.2; have h3 := sl.1
        have e : lrs = 1 := by
          have := h2.pos; simp only [size, BalancedSz] at h1 h3 ⊢; omega
        have z1 : lrl = nil := h2.2.1.size_eq_zero.1 (by have := h2.1; omega)
        have z2 : lrr = nil := h2.2.2.size_eq_zero.1 (by have := h2.1; omega)
        subst z1 z2; simp only [balanceL, id]; simp [All, Ordnode.singleton]; tauto
      · simp only [balanceL, id]; simp [All, Ordnode.singleton]; tauto
      · simp only [balanceL, id]; split_ifs <;> simp [All] <;> tauto
  · rcases l with _ | ⟨ls, ll, lx, lr⟩
    · simp only [balanceL, id]; simp [All]
    · have hrs := sr.pos
      by_cases hc : ls > delta * rs
      · have h1 := hl.1
        rcases ll with _ | ⟨lls, lll, llx, llr⟩
        · have := sl.1; simp only [size, BalancedSz, delta] at this h1 hc; omega
        rcases lr with _ | ⟨lrs, lrl, lrx, lrr⟩
        · have := sl.1; simp only [size, BalancedSz, delta] at this h1 hc; omega
        simp only [balanceL, id, hc, if_true]; split_ifs <;> simp [All] <;> tauto
      · simp only [balanceL, id, hc, if_false]; simp [All]
end W3c1

namespace W3c1
open Ordnode
set_option backward.isDefEq.respectTransparency false in
theorem eqL' {α : Type*} {l : Ordnode α} {x : α} {r : Ordnode α} (hl : Balanced l) (sl : Sized l)
    (sr : Sized r)
    (H : (∃ l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    balanceL l x r = balance' l x r := by
  have H1 : size l = 0 → size r ≤ 1 := by
    intro l0; rw [l0] at H
    rcases H with (⟨_, ⟨⟨⟩⟩ | ⟨⟨⟩⟩, H⟩ | ⟨r', e, H⟩)
    · exact balancedSz_zero.1 H.symm
    exact le_trans (raised_iff.1 e).1 (balancedSz_zero.1 H.symm)
  have H2 : 1 ≤ size l → 1 ≤ size r → size r ≤ delta * size l := by
    intro l1 _
    rcases H with (⟨l', e, H | ⟨_, H₂⟩⟩ | ⟨r', e, H | ⟨_, H₂⟩⟩)
    · exact le_trans (le_trans (Nat.le_add_left _ _) H) (mul_pos (by decide) l1 : (0 : ℕ) < _)
    · exact le_trans H₂ (Nat.mul_le_mul_left _ (raised_iff.1 e).1)
    · cases raised_iff.1 e; unfold delta; lia
    · exact le_trans (raised_iff.1 e).1 H₂
  rw [balanceL_eq_balance sl sr H1 H2]
  rcases r with _ | ⟨rs, rl, rx, rr⟩
  · exact balance_eq_balance' hl trivial sl trivial
  rcases l with _ | ⟨ls, ll, lx, lr⟩
  · have h1 := H1 rfl
    have : size rl = 0 ∧ size rr = 0 := by
      rwa [size, sr.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at h1
    cases sr.2.1.size_eq_zero.1 this.1
    cases sr.2.2.size_eq_zero.1 this.2
    obtain rfl : rs = 1 := sr.1
    rfl
  · simp only [balance, id_eq, balance', size_node, gt_iff_lt]
    symm; rw [ite_eq_right]
    · split_ifs with h h_1
      · have := H2 sl.pos sr.pos; simp only [size] at this; omega
      · have ld : delta ≤ size ll + size lr := by
          have := lt_of_le_of_lt (Nat.mul_le_mul_left _ sr.pos) h_1
          rwa [sl.1, Nat.lt_succ_iff] at this
        obtain - | ⟨lls, lll, llx, llr⟩ := ll
        · rw [size, zero_add] at ld
          exact absurd (le_trans ld (balancedSz_zero.1 hl.1.symm)) (by decide)
        obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr
        · exact absurd (le_trans ld (balancedSz_zero.1 hl.1)) (by decide)
        dsimp [rotateR]; split_ifs
        · simp [node3R, node', sl.1]; abel
        · simp [node4R, node', sl.1, sl.2.2.1]; abel
      · simp [node']
    · exact not_le_of_gt (add_le_add (Nat.succ_le_of_lt sl.pos) (Nat.succ_le_of_lt sr.pos))
end W3c1

namespace W3c1
open Ordnode
theorem szR {α : Type*} {l : Ordnode α} {x : α} {r : Ordnode α} (hr : Balanced r) (sl : Sized l)
    (sr : Sized r) : size (balanceR l x r) = size l + size r + 1 := by
  rw [← size_dual, dual_balanceR, szL hr.dual sr.dual sl.dual, size_dual, size_dual]; omega
theorem allR {α : Type*} {P : α → Prop} {l : Ordnode α} {x : α} {r : Ordnode α} (hr : Balanced r)
    (sl : Sized l) (sr : Sized r) : All P (balanceR l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [← all_dual, dual_balanceR, allL hr.dual sr.dual sl.dual, all_dual, all_dual]; tauto
theorem eqR' {α : Type*} {l : Ordnode α} {x : α} {r : Ordnode α} (hr : Balanced r) (sl : Sized l)
    (sr : Sized r)
    (H : (∃ l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    balanceR l x r = balance' l x r := by
  rw [← dual_dual (balanceR l x r), dual_balanceR,
    eqL' hr.dual sr.dual sl.dual (balance_sz_dual H), ← dual_balance', dual_dual]
end W3c1

-- `Ordnode.balanceL_eq_balance'` idx 5: removable (balanceL only inspects r's size; H bounds it)
theorem c1_146 : drop% Ordnode.balanceL_eq_balance' 5 := fun hl sl sr H => eqL' hl sl sr H
-- `Ordnode.size_balanceL` idx 5: removable (size of balanceL needs only l balanced, both sized)
theorem c1_147 : drop% Ordnode.size_balanceL 5 := fun hl sl sr _ => szL hl sl sr
-- `Ordnode.size_balanceL` idx 8: removable (size of balanceL needs only l balanced, both sized)
theorem c1_148 : drop% Ordnode.size_balanceL 8 := fun hl _ sl sr => szL hl sl sr
-- `Ordnode.all_balanceL` idx 6: removable (balanceL keeps all elements when l is balanced, both sized)
theorem c1_149 : drop% Ordnode.all_balanceL 6 := fun hl sl sr _ => allL hl sl sr
-- `Ordnode.all_balanceL` idx 9: removable (balanceL keeps all elements when l is balanced, both sized)
theorem c1_150 : drop% Ordnode.all_balanceL 9 := fun hl _ sl sr => allL hl sl sr
-- `Ordnode.balanceR_eq_balance'` idx 4: removable (mirror of balanceL_eq_balance' idx 5)
theorem c1_151 : drop% Ordnode.balanceR_eq_balance' 4 := fun hr sl sr H => eqR' hr sl sr H
-- `Ordnode.size_balanceR` idx 4: removable (mirror of size_balanceL idx 5)
theorem c1_152 : drop% Ordnode.size_balanceR 4 := fun hr sl sr _ => szR hr sl sr
-- `Ordnode.size_balanceR` idx 8: removable (mirror of size_balanceL idx 8)
theorem c1_153 : drop% Ordnode.size_balanceR 8 := fun _ hr sl sr => szR hr sl sr
-- `Ordnode.all_balanceR` idx 5: removable (mirror of all_balanceL idx 6)
theorem c1_154 : drop% Ordnode.all_balanceR 5 := fun hr sl sr _ => allR hr sl sr
-- `Ordnode.all_balanceR` idx 9: removable (mirror of all_balanceL idx 9)
theorem c1_155 : drop% Ordnode.all_balanceR 9 := fun _ hr sl sr => allR hr sl sr

namespace W3c1
theorem bw0 (m n : ℕ) : Nat.bitwise (fun _ _ => false) m n = 0 :=
  Nat.eq_of_testBit_eq fun i => by rw [Nat.testBit_bitwise rfl]; simp
def p8 : PosNum → PosNum → Num
  | .one, .one => 1
  | .bit0 m, .bit0 n => Num.bit false (p8 m n)
  | .bit0 m, .bit1 n => Num.bit false (p8 m n)
  | .bit1 m, .bit0 n => Num.bit false (p8 m n)
  | .bit1 m, .bit1 n => Num.bit false (p8 m n)
  | _, _ => 0
def p9 : PosNum → PosNum → Num
  | .one, .one => 0
  | .one, _ => 1
  | _, .one => 0
  | .bit0 m, .bit0 n => Num.bit false (p9 m n)
  | .bit0 m, .bit1 n => Num.bit false (p9 m n)
  | .bit1 m, .bit0 n => Num.bit false (p9 m n)
  | .bit1 m, .bit1 n => Num.bit false (p9 m n)
def p10 : PosNum → PosNum → Num
  | .one, .one => 0
  | .one, _ => 0
  | _, .one => 1
  | .bit0 m, .bit0 n => Num.bit false (p10 m n)
  | .bit0 m, .bit1 n => Num.bit false (p10 m n)
  | .bit1 m, .bit0 n => Num.bit false (p10 m n)
  | .bit1 m, .bit1 n => Num.bit false (p10 m n)
def p11 : PosNum → PosNum → Num
  | .one, _ => 0
  | _, .one => 0
  | _, _ => 1
/-- Lift of a `PosNum` operation to `Num`, zero elsewhere. -/
def liftP (p : PosNum → PosNum → Num) : Num → Num → Num
  | .pos a, .pos b => p a b
  | _, _ => 0
end W3c1
open W3c1

-- `_private.Mathlib.Data.Nat.Prime.Defs.0.Nat.minFacAux_has_prop` idx 1: n = 1, k = 3
theorem c1_156 : ¬ drop0% _private.Mathlib.Data.Nat.Prime.Defs.«0».Nat.minFacAux_has_prop 1 := fun h => by
  have := (h (n := 1) 3 0 rfl (fun m hm hd => absurd (Nat.le_of_dvd one_pos hd) (by omega))).1
  rw [Nat.minFacAux] at this; simp at this
-- `_private.Mathlib.Data.Nat.Prime.Defs.0.Nat.minFacAux_has_prop` idx 4: n = 2, k = 1
theorem c1_157 : ¬ drop0% _private.Mathlib.Data.Nat.Prime.Defs.«0».Nat.minFacAux_has_prop 4 := fun h => by
  have := (h (n := 2) (by norm_num) 1 0 (fun m hm _ => by omega)).1
  rw [Nat.minFacAux] at this; simp at this
-- `_private.Mathlib.Data.Nat.Prime.Defs.0.Nat.minFacAux_has_prop` idx 5: n = 4, k = 3
theorem c1_158 : ¬ drop0% _private.Mathlib.Data.Nat.Prime.Defs.«0».Nat.minFacAux_has_prop 5 := fun h => by
  have := (h (n := 4) (by norm_num) 3 0 rfl).2.2 2 le_rfl (by norm_num)
  rw [Nat.minFacAux] at this; simp at this
-- `_private.Mathlib.Data.Nat.Prime.Defs.0.Nat.minFac_has_prop` idx 1: n = 1
theorem c1_159 : ¬ drop0% _private.Mathlib.Data.Nat.Prime.Defs.«0».Nat.minFac_has_prop 1 := fun h => by
  have := (h (n := 1)).1
  simp at this
-- `PosNum.minFacAux_to_nat` idx 3: fuel = 0, n = 9, k = 1
theorem c1_160 : ¬ drop0% PosNum.minFacAux_to_nat 3 := fun h => by
  have := h (fuel := 0) (n := PosNum.bit1 (PosNum.bit0 (PosNum.bit0 1))) (k := 1)
  rw [PosNum.minFacAux, show ((PosNum.bit1 (PosNum.bit0 (PosNum.bit0 1)) : PosNum) : ℕ) = 9 from rfl,
    show ((PosNum.bit1 1 : PosNum) : ℕ) = 3 from rfl, Nat.minFacAux] at this
  simp at this
-- `Num.castNum_eq_bitwise` idx 4: g = false, f = 1 only at (0, 0), p = 0
theorem c1_161 : ¬ drop0% Num.castNum_eq_bitwise 4 := fun h => by
  have := h (f := fun m n => match m, n with | .zero, .zero => 1 | _, _ => 0) (g := fun _ _ => false)
    (fun _ _ => 0) rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) rfl
    (fun b _ => by cases b <;> rfl) (fun a _ => by cases a <;> rfl)
    (fun a b _ _ => by cases a <;> cases b <;> rfl) 0 0
  rw [bw0] at this; exact absurd this (by decide)
-- `Num.castNum_eq_bitwise` idx 5: g = false, f = 1 only at (0, pos _), p = 0
theorem c1_162 : ¬ drop0% Num.castNum_eq_bitwise 5 := fun h => by
  have := h (f := fun m n => match m, n with | .zero, .pos _ => 1 | _, _ => 0) (g := fun _ _ => false)
    (fun _ _ => 0) rfl rfl (fun _ => rfl) (fun _ _ => rfl) rfl
    (fun b _ => by cases b <;> rfl) (fun a _ => by cases a <;> rfl)
    (fun a b _ _ => by cases a <;> cases b <;> rfl) 0 1
  rw [bw0] at this; exact absurd this (by decide)
-- `Num.castNum_eq_bitwise` idx 6: g = false, f = 1 only at (pos _, 0), p = 0
theorem c1_163 : ¬ drop0% Num.castNum_eq_bitwise 6 := fun h => by
  have := h (f := fun m n => match m, n with | .pos _, .zero => 1 | _, _ => 0) (g := fun _ _ => false)
    (fun _ _ => 0) rfl rfl (fun _ => rfl) (fun _ _ => rfl) rfl
    (fun b _ => by cases b <;> rfl) (fun a _ => by cases a <;> rfl)
    (fun a b _ _ => by cases a <;> cases b <;> rfl) 1 0
  rw [bw0] at this; exact absurd this (by decide)
-- `Num.castNum_eq_bitwise` idx 7: g = false, f = 1 at (pos _, pos _), p = 0
theorem c1_164 : ¬ drop0% Num.castNum_eq_bitwise 7 := fun h => by
  have := h (f := fun m n => match m, n with | .pos _, .pos _ => 1 | _, _ => 0) (g := fun _ _ => false)
    (fun _ _ => 0) rfl rfl (fun _ => rfl) (fun _ => rfl) rfl
    (fun b _ => by cases b <;> rfl) (fun a _ => by cases a <;> rfl)
    (fun a b _ _ => by cases a <;> cases b <;> rfl) 1 1
  rw [bw0] at this; exact absurd this (by decide)
-- `Num.castNum_eq_bitwise` idx 8: g = false, p 1 1 = 1 propagated by the bit equations
theorem c1_165 : ¬ drop0% Num.castNum_eq_bitwise 8 := fun h => by
  have := h (f := liftP p8) (g := fun _ _ => false)
    p8 rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun b n => by cases b <;> cases n <;> rfl) (fun a m => by cases a <;> cases m <;> rfl)
    (fun a b _ _ => by cases a <;> cases b <;> rfl) 1 1
  rw [bw0] at this; exact absurd this (by decide)
-- `Num.castNum_eq_bitwise` idx 9: g = false, p 1 (bit b n) = 1
theorem c1_166 : ¬ drop0% Num.castNum_eq_bitwise 9 := fun h => by
  have := h (f := liftP p9) (g := fun _ _ => false)
    p9 rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) rfl
    (fun a m => by cases a <;> cases m <;> rfl)
    (fun a b m n => by cases a <;> cases b <;> cases m <;> cases n <;> rfl) 1 2
  rw [bw0] at this; exact absurd this (by decide)
-- `Num.castNum_eq_bitwise` idx 10: g = false, p (bit a m) 1 = 1
theorem c1_167 : ¬ drop0% Num.castNum_eq_bitwise 10 := fun h => by
  have := h (f := liftP p10) (g := fun _ _ => false)
    p10 rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) rfl
    (fun b n => by cases b <;> cases n <;> rfl)
    (fun a b m n => by cases a <;> cases b <;> cases m <;> cases n <;> rfl) 2 1
  rw [bw0] at this; exact absurd this (by decide)
-- `Num.castNum_eq_bitwise` idx 11: g = false, p = 1 when both arguments are ≥ 2
theorem c1_168 : ¬ drop0% Num.castNum_eq_bitwise 11 := fun h => by
  have := h (f := liftP p11) (g := fun _ _ => false)
    p11 rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) rfl
    (fun b n => by cases b <;> rfl) (fun a m => by cases a <;> rfl) 2 2
  rw [bw0] at this; exact absurd this (by decide)

namespace W3c1
theorem bwb (f : Bool → Bool → Bool) (a b : Bool) (m n : ℕ) (hm : Nat.bit a m ≠ 0)
    (hn : Nat.bit b n ≠ 0) :
    Nat.bitwise f (Nat.bit a m) (Nat.bit b n) = Nat.bit (f a b) (Nat.bitwise f m n) := by
  conv_lhs => unfold Nat.bitwise
  rw [if_neg hm, if_neg hn]
  have h1 : Nat.bit a m / 2 = m := Nat.bit_div_two a m
  have h2 : Nat.bit b n / 2 = n := Nat.bit_div_two b n
  have h3 : (Nat.bit a m % 2 = 1) = (a = true) := by cases a <;> simp [Nat.bit] <;> omega
  have h4 : (Nat.bit b n % 2 = 1) = (b = true) := by cases b <;> simp [Nat.bit] <;> omega
  simp only [h1, h2, h3, h4, decide_eq_true_eq, Bool.decide_eq_true]
  cases f a b <;> simp [Nat.bit] <;> omega
end W3c1

-- `Num.castNum_eq_bitwise` idx 3: removable (bitwise is only ever split at positive arguments,
-- where the bit recursion holds without g false false = false)
theorem c1_169 : drop% Num.castNum_eq_bitwise 3 := by
  intro f g p f00 f0n fn0 fnn p11 p1b pb1 pbb m n
  obtain - | m := m <;> obtain - | n := n <;>
      try simp only [show Num.zero = 0 from rfl, show ((0 : Num) : ℕ) = 0 from rfl]
  · rw [f00, Nat.bitwise_zero]; rfl
  · rw [f0n, Nat.bitwise_zero_left]
    cases g false true <;> rfl
  · rw [fn0, Nat.bitwise_zero_right]
    cases g true false <;> rfl
  · rw [fnn]
    have this b (n : PosNum) : (cond b (↑n) 0 : ℕ) = ↑(cond b (Num.pos n) 0 : Num) := by
      cases b <;> rfl
    have this' b (n : PosNum) : ↑(Num.pos (PosNum.bit b n)) = Nat.bit b ↑n := by
      cases b <;> simp
    have hne : ∀ b (n : PosNum), Nat.bit b (n : ℕ) ≠ 0 := fun b n => by
      have := PosNum.to_nat_pos n; cases b <;> simp [Nat.bit] <;> omega
    have hne1 : Nat.bit true 0 ≠ 0 := by decide
    induction m generalizing n with | one => ?_ | bit1 m IH => ?_ | bit0 m IH => ?_ <;>
    obtain - | n | n := n
    all_goals simp only [show PosNum.one = 1 from rfl, show Num.pos 1 = 1 from rfl,
      show PosNum.bit0 = PosNum.bit false from rfl, show PosNum.bit1 = PosNum.bit true from rfl,
      show ((1 : Num) : ℕ) = Nat.bit true 0 from rfl]
    all_goals
      repeat rw [this']
      rw [W3c1.bwb _ _ _ _ _ (by first | exact hne1 | exact hne _ _) (by first | exact hne1 | exact hne _ _)]
    · rw [Nat.bitwise_zero, p11]; cases g true true <;> rfl
    any_goals rw [Nat.bitwise_zero_left, ← Bool.cond_eq_ite, this, ← Num.bit_to_nat, p1b]
    any_goals rw [Nat.bitwise_zero_right, ← Bool.cond_eq_ite, this, ← Num.bit_to_nat, pb1]
    all_goals
      rw [← show ∀ n : PosNum, ↑(p m n) = Nat.bitwise g ↑m ↑n from IH]
      rw [← Num.bit_to_nat, pbb]
