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

namespace W3c2
def pn : ℕ →. ℕ := fun _ => Part.none
def ps : ℕ →. ℕ := fun n => Part.some n
def ps1 : ℕ →. ℕ := fun n => Part.some (n + 1)
def fn0 : ℕ →. ℕ ⊕ ℕ := fun _ => Part.none
theorem pn_dom (a : ℕ) : a ∉ pn.Dom := fun h => h
theorem notMem_fix_none {b : ℕ} {a : ℕ} {f : ℕ →. ℕ ⊕ ℕ} (hf : ¬ (f a).Dom) : b ∉ f.fix a :=
  fun h => hf (PFun.dom_of_mem_fix h)
/-- 0 ↦ inl 0, else none -/
def fz : ℕ →. ℕ ⊕ ℕ := fun n => if n = 0 then Part.some (Sum.inl 0) else Part.none
/-- 0 ↦ inr 1, 1 ↦ inl 0, else none -/
def fw : ℕ →. ℕ ⊕ ℕ := fun n => if n = 0 then Part.some (Sum.inr 1) else if n = 1 then Part.some (Sum.inl 0) else Part.none
/-- 0 ↦ inr 1, else none -/
def g1 : ℕ →. ℕ ⊕ ℕ := fun n => if n = 0 then Part.some (Sum.inr 1) else Part.none
theorem fz0 : Sum.inl 0 ∈ fz 0 := by simp [fz]
theorem fz1 : ¬ (fz 1).Dom := by simp [fz]
theorem fw0 : Sum.inr 1 ∈ fw 0 := by simp [fw]
theorem fw1 : Sum.inl 0 ∈ fw 1 := by simp [fw]
theorem fwfix : 0 ∈ fw.fix 0 := PFun.mem_fix_iff.2 (Or.inr ⟨1, fw0, PFun.fix_stop fw1⟩)
theorem psne (a b : ℕ) (hab : a ≠ b) : ¬ Part.some a ≤ Part.some b :=
  fun h => hab (Part.mem_some_iff.1 (h a (Part.mem_some a)))

/-- Bool streams -/
abbrev PF2 : PFunctor := ⟨Bool, fun _ => Unit⟩
/-- Bool-labelled binary trees -/
abbrev PF3 : PFunctor := ⟨Bool, fun _ => Bool⟩
noncomputable def gB : Bool → PF2 Bool := fun b => ⟨b, fun _ => b⟩
/-- constant stream -/
noncomputable def cs (b : Bool) : PF2.M := PFunctor.M.corec gB b
theorem cs_mk (b : Bool) : cs b = PFunctor.M.mk ⟨b, fun _ => cs b⟩ := by
  have e : PFunctor.M.dest (cs b) = PF2.map (PFunctor.M.corec gB) (gB b) := PFunctor.M.dest_corec _ _
  conv_lhs => rw [← PFunctor.M.mk_dest (cs b)]
  rw [e]; rfl
theorem cs_head (b : Bool) : (cs b).head = b := by rw [cs_mk, PFunctor.M.head_mk]; rfl
theorem cs_ne : cs true ≠ cs false := fun e => by
  have := congrArg PFunctor.M.head e; rw [cs_head, cs_head] at this; exact Bool.noConfusion this
noncomputable instance : Inhabited PF2.M := ⟨cs false⟩
theorem botBis : PFunctor.M.IsBisimulation (F := PF2) (fun _ _ => False) := ⟨fun h => h.elim, fun h => h.elim⟩
/-- approximations: x 1 has head true, all others head false -/
noncomputable def xs : (n : ℕ) → PFunctor.Approx.CofixA PF2 n
  | 0 => .continue
  | 1 => .intro true fun _ => .continue
  | n + 2 => .intro false fun _ => xs (n + 1)
theorem cs_child (b : Bool) : (cs b).dest.2 () = cs b := by
  conv_lhs => rw [cs_mk]
  rfl
theorem cs_dest (b : Bool) : (cs b).dest = ⟨b, fun _ => cs b⟩ := by
  conv_lhs => rw [cs_mk]
  rfl
/-- relates only the constant true stream to itself: a bisimulation -/
def Rt (a b : PF2.M) : Prop := a = cs true ∧ b = cs true
theorem Rt_bis : PFunctor.M.IsBisimulation Rt := by
  constructor
  · intro a a' f f' ⟨e1, e2⟩
    have h1 := congrArg PFunctor.M.head e1
    have h2 := congrArg PFunctor.M.head e2
    rw [PFunctor.M.head_mk, cs_head] at h1 h2
    exact h1.trans h2.symm
  · intro a f f' ⟨e1, e2⟩ i
    have h1 := congrArg (fun x : PF2.M => x.dest.2 ()) e1
    have h2 := congrArg (fun x : PF2.M => x.dest.2 ()) e2
    simp only [cs_child] at h1 h2
    exact ⟨h1, h2⟩
/-- a two-shape multivariate functor of arity 1 (Bool streams in the last slot) -/
abbrev P0 : MvPFunctor.{0} 1 := ⟨Bool, fun _ _ => Unit⟩
abbrev α0 : TypeVec.{0} 0 := fun _ => Unit
noncomputable def mm (b : Bool) : P0.M α0 := (⟨cs b, fun _ _ => ()⟩ : P0.mp α0)
theorem mm_ne : mm true ≠ mm false := fun e => cs_ne (congrArg Sigma.fst e)

open Ordnode
abbrev T := Ordnode ℕ
instance decSized {α : Type} : DecidablePred (@Sized α)
  | nil => isTrue trivial
  | node s l _ r =>
    have := decSized l; have := decSized r
    inferInstanceAs (Decidable (s = l.size + r.size + 1 ∧ Sized l ∧ Sized r))
instance decBounded {α : Type} [Preorder α] [DecidableLT α] :
    (t : Ordnode α) → (o₁ : WithBot α) → (o₂ : WithTop α) → Decidable (Bounded t o₁ o₂)
  | nil, some a, some b => inferInstanceAs (Decidable (a < b))
  | nil, none, _ => isTrue trivial
  | nil, some _, none => isTrue trivial
  | node _ l x r, o₁, o₂ =>
    have := decBounded l o₁ x; have := decBounded r x o₂
    inferInstanceAs (Decidable (Bounded l o₁ x ∧ Bounded r x o₂))
instance decValid {α : Type} [Preorder α] [DecidableLT α] (lo : WithBot α) (t : Ordnode α) (hi : WithTop α) :
    Decidable (Valid' lo t hi) :=
  decidable_of_iff (Bounded t lo hi ∧ Sized t ∧ Balanced t)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩
instance decValid0 {α : Type} [Preorder α] [DecidableLT α] (t : Ordnode α) : Decidable (Valid t) :=
  decValid ⊥ t ⊤
/-- balanced tree with `n` elements lo, …, lo+n-1 (fuel f) -/
def mk : ℕ → ℕ → ℕ → T
  | 0, _, _ => nil
  | f + 1, lo, n => if n = 0 then nil else node' (mk f lo (n / 2)) (lo + n / 2) (mk f (lo + n / 2 + 1) (n - n / 2 - 1))
def bt (lo n : ℕ) : T := mk n lo n
def sg {α : Type} (x : α) : Ordnode α := node 1 nil x nil
/-- ℕ with the discrete preorder (≤ is =): not total -/
def DN := ℕ
instance : Preorder DN where
  le a b := a = b
  lt _ _ := False
  le_refl _ := rfl
  le_trans _ _ _ h1 h2 := h1.trans h2
  lt_iff_le_not_ge a b := ⟨False.elim, fun ⟨h1, h2⟩ => h2 h1.symm⟩
instance : DecidableLE DN := fun a b => Nat.decEq a b
instance : DecidableLT DN := fun _ _ => isFalse id
def d0 : DN := (0 : ℕ)
def d1 : DN := (1 : ℕ)
end W3c2

open W3c2


-- `PNat.ofNat_le_ofNat`
theorem c2_1 : ¬ indep0% PNat.ofNat_le_ofNat 2 := fun h => (@h 0 1 NeZero.one).out rfl
-- `PNat.ofNat_le_ofNat`
theorem c2_2 : ¬ indep0% PNat.ofNat_le_ofNat 3 := fun h => (@h 1 0 NeZero.one).out rfl
-- `PNat.ofNat_lt_ofNat`
theorem c2_3 : ¬ indep0% PNat.ofNat_lt_ofNat 2 := fun h => (@h 0 1 NeZero.one).out rfl
-- `PNat.ofNat_lt_ofNat`
theorem c2_4 : ¬ indep0% PNat.ofNat_lt_ofNat 3 := fun h => (@h 1 0 NeZero.one).out rfl
-- `PNat.ofNat_inj`
theorem c2_5 : ¬ indep0% PNat.ofNat_inj 2 := fun h => (@h 0 1 NeZero.one).out rfl
-- `PNat.ofNat_inj`
theorem c2_6 : ¬ indep0% PNat.ofNat_inj 3 := fun h => (@h 1 0 NeZero.one).out rfl
-- `PrimeMultiset.mem_ofNatMultiset`
theorem c2_7 : ¬ indep0% PrimeMultiset.mem_ofNatMultiset 2 := fun h =>
  Nat.not_prime_zero (@h 1 {0} 0 (Multiset.mem_singleton_self 0))
-- `PrimeMultiset.to_ofNatMultiset`
theorem c2_8 : ¬ indep0% PrimeMultiset.to_ofNatMultiset 1 := fun h =>
  Nat.not_prime_zero (@h {0} 0 (Multiset.mem_singleton_self 0))
-- `PrimeMultiset.prod_ofNatMultiset`
theorem c2_9 : ¬ indep0% PrimeMultiset.prod_ofNatMultiset 1 := fun h =>
  Nat.not_prime_zero (@h {0} 0 (Multiset.mem_singleton_self 0))
-- `PrimeMultiset.to_ofPNatMultiset`
theorem c2_10 : ¬ indep0% PrimeMultiset.to_ofPNatMultiset 1 := fun h =>
  PNat.not_prime_one (@h {1} 1 (Multiset.mem_singleton_self 1))
-- `PNat.factorMultiset_mono`
theorem c2_11 : ¬ drop0% PNat.factorMultiset_mono 2 := fun h =>
  absurd (PNat.dvd_iff.1 ((PNat.factorMultiset_le_iff).1 (@h 2 1))) (by decide)
-- `PrimeMultiset.prod_dvd_prod`
theorem c2_12 : ¬ drop0% PrimeMultiset.prod_dvd_prod 2 := fun h =>
  by
  have := PNat.dvd_iff.1 (@h (2:ℕ+).factorMultiset 0)
  simp [PNat.prod_factorMultiset] at this
-- `PNat.find_spec`
theorem c2_13 : ¬ indep0% PNat.find_spec 2 := fun h => (@h (fun _ => False) _).elim fun _ hn => hn
-- `PNat.find_min`
theorem c2_14 : ¬ indep0% PNat.find_min 2 := fun h => (@h (fun _ => False) _ 1).elim fun _ hn => hn
-- `PNat.find_min`
theorem c2_15 : ¬ drop0% PNat.find_min 4 := fun h => absurd (@h (fun _ => True) _ ⟨1, trivial⟩ 1) (by simp)
-- `PNat.find_min'`
theorem c2_16 : ¬ drop0% PNat.find_min' 4 := fun h =>
  absurd (@h (· = 2) _ ⟨2, rfl⟩ 1) (by rw [not_le, PNat.one_le_find]; decide)
-- `PNat.find_eq_iff`
theorem c2_17 : ¬ indep0% PNat.find_eq_iff 2 := fun h => (@h (fun _ => False) _ 1).elim fun _ hn => hn
-- `PNat.find_lt_iff`
theorem c2_18 : ¬ indep0% PNat.find_lt_iff 2 := fun h => (@h (fun _ => False) _ 1).elim fun _ hn => hn
-- `PNat.find_le_iff`
theorem c2_19 : ¬ indep0% PNat.find_le_iff 2 := fun h => (@h (fun _ => False) _ 1).elim fun _ hn => hn
-- `PNat.le_find_iff`
theorem c2_20 : ¬ indep0% PNat.le_find_iff 2 := fun h => (@h (fun _ => False) _ 1).elim fun _ hn => hn
-- `PNat.lt_find_iff`
theorem c2_21 : ¬ indep0% PNat.lt_find_iff 2 := fun h => (@h (fun _ => False) _ 1).elim fun _ hn => hn
-- `PNat.find_eq_one`
theorem c2_22 : ¬ indep0% PNat.find_eq_one 2 := fun h => (@h (fun _ => False) _).elim fun _ hn => hn
-- `PNat.one_le_find`
theorem c2_23 : ¬ indep0% PNat.one_le_find 2 := fun h => (@h (fun _ => False) _).elim fun _ hn => hn
-- `PNat.find_mono`
theorem c2_24 : ¬ drop0% PNat.find_mono 4 := fun h =>
  by
  have := @h (· = 2) (· = 1) _ _ ⟨2, rfl⟩ ⟨1, rfl⟩
  have e2 : PNat.find (⟨2, rfl⟩ : ∃ n : ℕ+, n = 2) = 2 := PNat.find_spec (⟨2, rfl⟩ : ∃ n : ℕ+, n = 2)
  have e1 : PNat.find (⟨1, rfl⟩ : ∃ n : ℕ+, n = 1) = 1 := PNat.find_spec (⟨1, rfl⟩ : ∃ n : ℕ+, n = 1)
  rw [e1, e2] at this
  exact absurd this (by decide)
-- `PNat.find_mono`
theorem c2_25 : ¬ indep0% PNat.find_mono 6 := fun h =>
  (@h (fun _ => True) (fun _ => False) _ _ (fun _ hq => trivial) ⟨1, trivial⟩).elim fun _ hn => hn
-- `PNat.find_le`
theorem c2_26 : ¬ drop0% PNat.find_le 4 := fun h =>
  absurd (@h (· = 2) _ 1 ⟨2, rfl⟩) (by rw [not_le, PNat.one_le_find]; decide)
-- `PNat.find_comp_succ`
theorem c2_27 : indep% PNat.find_comp_succ 3 := by
  intro p _ h h1
  obtain ⟨n, hn⟩ := h
  obtain ⟨k, rfl⟩ := PNat.exists_eq_succ_of_ne_one (fun e => h1 (e ▸ hn))
  exact ⟨k, hn⟩
-- `PNat.find_comp_succ`
theorem c2_28 : ¬ drop0% PNat.find_comp_succ 4 := fun h =>
  absurd (@h (fun _ => True) _ ⟨1, trivial⟩ ⟨1, trivial⟩)
    (by rw [(PNat.find_eq_one _).2 trivial]; decide)
-- `PNat.dvd_gcd`
theorem c2_29 : ¬ drop0% PNat.dvd_gcd 3 := fun h => absurd (PNat.dvd_iff.1 (@h 1 2 2 (dvd_refl 2))) (by decide)
-- `PNat.dvd_gcd`
theorem c2_30 : ¬ drop0% PNat.dvd_gcd 4 := fun h => absurd (PNat.dvd_iff.1 (@h 2 1 2 (dvd_refl 2))) (by decide)
-- `PNat.lcm_dvd`
theorem c2_31 : ¬ drop0% PNat.lcm_dvd 3 := fun h => absurd (PNat.dvd_iff.1 (@h 2 1 1 (one_dvd 1))) (by decide)
-- `PNat.lcm_dvd`
theorem c2_32 : ¬ drop0% PNat.lcm_dvd 4 := fun h => absurd (PNat.dvd_iff.1 (@h 1 2 1 (one_dvd 1))) (by decide)
-- `PNat.dvd_prime`
theorem c2_33 : ¬ drop0% PNat.dvd_prime 2 := fun h => by
  have := (@h 4 2).1 (PNat.dvd_iff.2 (by decide))
  revert this; decide
-- `PNat.exists_prime_and_dvd`
theorem c2_34 : ¬ drop0% PNat.exists_prime_and_dvd 1 := fun h => by
  obtain ⟨p, hp, hd⟩ := @h 1
  rw [PNat.dvd_one_iff] at hd
  exact PNat.not_prime_one (hd ▸ hp)
-- `Part.get_eq_of_mem`
theorem c2_35 : indep% Part.get_eq_of_mem 4 := by
  intro α o a h; exact Part.dom_iff_mem.2 ⟨a, h⟩
-- `Part.ext'`
theorem c2_36 : ¬ drop0% Part.ext' 3 := fun h =>
  Part.some_ne_none 0 (@h ℕ Part.none (Part.some 0) (fun h₁ _ => h₁.elim)).symm
-- `Part.ext'`
theorem c2_37 : ¬ drop0% Part.ext' 4 := fun h =>
  absurd (Part.some_injective (@h ℕ (Part.some 0) (Part.some 1) Iff.rfl)) (by decide)
-- `Part.ext`
theorem c2_38 : ¬ drop0% Part.ext 3 := fun h => Part.some_ne_none 0 (@h ℕ (Part.some 0) Part.none)
-- `Part.mem_right_unique`
theorem c2_39 : ¬ drop0% Part.mem_right_unique 4 := fun h =>
  Part.some_ne_none 0 (@h ℕ 0 Part.none (Part.some 0) (Part.mem_some 0)).symm
-- `Part.mem_right_unique`
theorem c2_40 : ¬ drop0% Part.mem_right_unique 5 := fun h =>
  Part.some_ne_none 0 (@h ℕ 0 (Part.some 0) Part.none (Part.mem_some 0))
-- `Part.get_eq_of_mem`
theorem c2_41 : ¬ drop0% Part.get_eq_of_mem 3 := fun h => absurd (@h ℕ (Part.some 0) 1 (Part.some_dom 0)) (by simp)
-- `Part.eq_of_get_eq_get`
theorem c2_42 : ¬ drop0% Part.eq_of_get_eq_get 5 := fun h =>
  absurd (Part.some_injective (@h ℕ (Part.some 0) (Part.some 1) trivial trivial)) (by decide)
-- `Part.eq_of_mem`
theorem c2_43 : ¬ drop0% Part.eq_of_mem 4 := fun h => Part.some_ne_none 0 (@h ℕ (Part.some 0) Part.none trivial)
-- `Part.getOrElse_of_dom`
theorem c2_44 : ¬ indep0% Part.getOrElse_of_dom 2 := fun h => (@h ℕ Part.none _ 0).elim
-- `Part.getOrElse_of_not_dom`
theorem c2_45 : ¬ drop0% Part.getOrElse_of_not_dom 2 := fun h =>
  by
  have := @h ℕ (Part.some 0) _ 1
  rw [Part.getOrElse_of_dom _ (Part.some_dom 0)] at this
  exact absurd this (by decide)
-- `Part.Dom.toOption`
theorem c2_46 : ¬ indep0% Part.Dom.toOption 3 := fun h => (@h ℕ Part.none _).elim
-- `Part.induction_on`
theorem c2_47 : ¬ drop0% Part.induction_on 3 := fun h =>
  @h ℕ (fun o => o ≠ Part.none) Part.none (fun a => Part.some_ne_none a) rfl
-- `Part.induction_on`
theorem c2_48 : ¬ drop0% Part.induction_on 4 := fun h =>
  Part.some_ne_none 0 (@h ℕ (· = Part.none) (Part.some 0) rfl)
-- `Part.le_total_of_le_of_le`
theorem c2_49 : ¬ drop0% Part.le_total_of_le_of_le 4 := fun h =>
  (@h ℕ (Part.some 0) (Part.some 1) (Part.some 1) le_rfl).elim (psne 0 1 (by decide)) (psne 1 0 (by decide))
-- `Part.le_total_of_le_of_le`
theorem c2_50 : ¬ drop0% Part.le_total_of_le_of_le 5 := fun h =>
  (@h ℕ (Part.some 0) (Part.some 1) (Part.some 0) le_rfl).elim (psne 0 1 (by decide)) (psne 1 0 (by decide))
-- `Part.assert_neg`
theorem c2_51 : ¬ drop0% Part.assert_neg 3 := fun h =>
  Part.some_ne_none 0 ((Part.assert_pos trivial).symm.trans (@h ℕ True (fun _ => Part.some 0)))
-- `Part.bind_of_mem`
theorem c2_52 : ¬ drop0% Part.bind_of_mem 4 := fun h =>
  Part.some_ne_none 0 ((@h ℕ ℕ Part.none 0 Part.some).symm.trans (Part.bind_none _))
-- `Part.map_id'`
theorem c2_53 : ¬ drop0% Part.map_id' 2 := fun h =>
  absurd (Part.some_injective ((Part.map_some _ _).symm.trans (@h ℕ Nat.succ (Part.some 0)))) (by decide)
-- `Part.mem_restrict`
theorem c2_54 : ¬ indep0% Part.mem_restrict 3 := fun h => (@h ℕ True Part.none 0 trivial).elim
-- `Part.append_mem_append`
theorem c2_55 : ¬ drop0% Part.append_mem_append 6 := fun h =>
  absurd (Part.mem_unique (@h (List ℕ) _ (Part.some [1]) (Part.some []) [0] [] (Part.mem_some []))
    (Part.append_mem_append _ _ _ _ (Part.mem_some [1]) (Part.mem_some []))) (by decide)
-- `Part.append_mem_append`
theorem c2_56 : ¬ drop0% Part.append_mem_append 7 := fun h =>
  absurd (Part.mem_unique (@h (List ℕ) _ (Part.some []) (Part.some [1]) [] [0] (Part.mem_some []))
    (Part.append_mem_append _ _ _ _ (Part.mem_some []) (Part.mem_some [1]))) (by decide)
-- `PFun.ext'`
theorem c2_57 : ¬ drop0% PFun.ext' 4 := fun h => by
  have := congrFun (@h ℕ ℕ pn ps (fun a p q => p.elim)) 0
  exact Part.some_ne_none 0 this.symm
-- `PFun.ext'`
theorem c2_58 : ¬ drop0% PFun.ext' 5 := fun h => by
  have := congrFun (@h ℕ ℕ ps ps1 (fun a => ⟨fun _ => trivial, fun _ => trivial⟩)) 0
  exact absurd (Part.some_injective this) (by decide)
-- `PFun.asSubtype_eq_of_mem`
theorem c2_59 : ¬ drop0% PFun.asSubtype_eq_of_mem 5 := fun h =>
  absurd (@h ℕ ℕ ps 0 1 trivial) (by simp [PFun.asSubtype, ps, PFun.fn])
-- `PFun.mem_restrict`
theorem c2_60 : ¬ indep0% PFun.mem_restrict 4 := fun h => by
  have := @h ℕ ℕ pn Set.univ 0 0
  exact pn_dom 0 (this (Set.mem_univ 0))
-- `PFun.dom_restrict`
theorem c2_61 : ¬ indep0% PFun.dom_restrict 4 := fun h => pn_dom 0 (@h ℕ ℕ pn Set.univ 0 (Set.mem_univ 0))
-- `PFun.restrict_restrict`
theorem c2_62 : ¬ indep0% PFun.restrict_restrict 5 := fun h => pn_dom 0 (@h ℕ ℕ pn Set.univ ∅ 0 (Set.mem_univ 0))
-- `PFun.restrict_restrict`
theorem c2_63 : ¬ indep0% PFun.restrict_restrict 6 := fun h => by
  have := @h ℕ ℕ ps ∅ Set.univ (Set.empty_subset _) 0 (Set.mem_univ 0)
  rw [PFun.dom_restrict] at this
  exact this
-- `PFun.bind_defined`
theorem c2_64 : ¬ drop0% PFun.bind_defined 6 := fun h => by
  have := @h ℕ ℕ ℕ Set.univ pn (fun _ => ps) (fun _ _ _ => trivial) 0 (Set.mem_univ 0)
  obtain ⟨h1, _⟩ := this; exact h1
-- `PFun.bind_defined`
theorem c2_65 : ¬ drop0% PFun.bind_defined 7 := fun h => by
  have := @h ℕ ℕ ℕ Set.univ ps (fun _ => pn) (fun _ _ => trivial) 0 (Set.mem_univ 0)
  obtain ⟨_, h2⟩ := this; exact h2
-- `PFun.dom_of_mem_fix`
theorem c2_66 : ¬ drop0% PFun.dom_of_mem_fix 5 := fun h => (@h ℕ ℕ fn0 0 0).elim
-- `PFun.fix_stop`
theorem c2_67 : ¬ drop0% PFun.fix_stop 5 := fun h => notMem_fix_none (f := fn0) (a := 0) id (@h ℕ ℕ fn0 0 0)
-- `PFun.fix_fwd_eq`
theorem c2_68 : ¬ drop0% PFun.fix_fwd_eq 5 := fun h => by
  have h0 : (0:ℕ) ∈ fz.fix 0 := PFun.fix_stop fz0
  rw [@h ℕ ℕ fz 0 1] at h0
  exact notMem_fix_none fz1 h0
-- `PFun.fix_fwd`
theorem c2_69 : ¬ drop0% PFun.fix_fwd 6 := fun h =>
  notMem_fix_none (f := g1) (a := 1) (by simp [g1]) (@h ℕ ℕ g1 0 0 1 (by simp [g1]))
-- `PFun.fix_fwd`
theorem c2_70 : ¬ drop0% PFun.fix_fwd 7 := fun h =>
  notMem_fix_none fz1 (@h ℕ ℕ fz 0 0 1 (PFun.fix_stop fz0))
-- `PFun.fixInduction_spec`
theorem c2_71 : ¬ indep0% PFun.fixInduction_spec 6 := fun h =>
  notMem_fix_none (f := fn0) (a := 0) id (@h ℕ ℕ (fun _ => True) fn0 0 0 (fun _ _ _ => trivial))
-- `PFun.fixInduction'_stop`
theorem c2_72 : indep% PFun.fixInduction'_stop 6 := by
  intro α β C f b a fa _ _; exact PFun.fix_stop fa
-- `PFun.fixInduction'_stop`
theorem c2_73 : ¬ indep0% PFun.fixInduction'_stop 7 := fun h => by
  have := @h ℕ ℕ (fun _ => True) fw 0 0 fwfix (fun _ _ => trivial) (fun _ _ _ _ _ => trivial)
  simp [fw] at this
-- `PFun.fixInduction'_fwd`
theorem c2_74 : indep% PFun.fixInduction'_fwd 7 := by
  intro α β C f b a a' h' fa _ _; rw [PFun.fix_fwd_eq fa]; exact h'
-- `PFun.fixInduction'_fwd`
theorem c2_75 : indep% PFun.fixInduction'_fwd 8 := by
  intro α β C f b a a' h fa _ _; exact PFun.fix_fwd h fa
-- `PFun.fixInduction'_fwd`
theorem c2_76 : ¬ indep0% PFun.fixInduction'_fwd 9 := fun h => by
  have := @h ℕ ℕ (fun _ => True) fz 0 0 0 (PFun.fix_stop fz0) (PFun.fix_stop fz0)
    (fun _ _ => trivial) (fun _ _ _ _ _ => trivial)
  simp [fz] at this
-- `PFun.image_mono`
theorem c2_77 : ¬ drop0% PFun.image_mono 5 := fun h => by
  have := @h ℕ ℕ ps Set.univ ∅ 0 (by rw [PFun.image_def]; exact ⟨0, Set.mem_univ 0, Part.mem_some 0⟩)
  rw [PFun.image_def] at this
  obtain ⟨x, hx, _⟩ := this; exact hx
-- `PFun.ran_restrict`
theorem c2_78 : ¬ indep0% PFun.ran_restrict 4 := fun h => pn_dom 0 (@h ℕ ℕ pn Set.univ 0 (Set.mem_univ 0))
-- `PFun.preimage_mono`
theorem c2_79 : ¬ drop0% PFun.preimage_mono 5 := fun h => by
  have := @h ℕ ℕ ps Set.univ ∅ 0 (by rw [PFun.Preimage_def]; exact ⟨0, Set.mem_univ 0, Part.mem_some 0⟩)
  rw [PFun.Preimage_def] at this
  obtain ⟨x, hx, _⟩ := this; exact hx
-- `PFun.disjoint_preimage_of_disjoint`
theorem c2_80 : ¬ drop0% PFun.disjoint_preimage_of_disjoint 5 := fun h => by
  have := @h ℕ ℕ ps Set.univ Set.univ
  rw [disjoint_self, Set.bot_eq_empty, Set.eq_empty_iff_forall_notMem] at this
  exact this 0 (by rw [PFun.Preimage_def]; exact ⟨0, Set.mem_univ 0, Part.mem_some 0⟩)
-- `PFun.preimage_restrict`
theorem c2_81 : ¬ indep0% PFun.preimage_restrict 5 := fun h => pn_dom 0 (@h ℕ ℕ pn Set.univ ∅ 0 (Set.mem_univ 0))
-- `PFun.core_mono`
theorem c2_82 : ¬ drop0% PFun.core_mono 5 := fun h => by
  have := @h ℕ ℕ ps Set.univ ∅ 0 (by rw [PFun.core_def]; exact fun _ _ => Set.mem_univ _)
  rw [PFun.core_def] at this
  exact this 0 (Part.mem_some 0)
-- `PFun.get_prodLift`
theorem c2_83 : ¬ indep0% PFun.get_prodLift 6 := fun h => (@h ℕ ℕ ℕ pn pn 0).1

-- `PFunctor.iget_map`
theorem c2_84 : ¬ drop0% PFunctor.iget_map 9 := fun h =>
  absurd (@h PF2 ℕ ℕ _ _ _ ⟨true, fun _ => 0⟩ Nat.succ ⟨false, ()⟩) (by decide)
-- `PFunctor.Approx.agree_children`
theorem c2_85 : ¬ drop0% PFunctor.Approx.agree_children 6 := fun h => by
  have := @h PF3 1 (.intro true fun b => .intro b fun _ => .continue)
    (.intro true fun b => .intro b fun _ => .intro b fun _ => .continue) true false
    (.intro _ _ fun b => .intro _ _ fun _ => .continu _ _)
  cases this
-- `PFunctor.Approx.agree_children`
theorem c2_86 : ¬ drop0% PFunctor.Approx.agree_children 7 := fun h => by
  have := @h PF2 1 (.intro true fun _ => .intro true fun _ => .continue)
    (.intro true fun _ => .intro false fun _ => .intro false fun _ => .continue) () () HEq.rfl
  cases this
-- `PFunctor.Approx.truncate_eq_of_agree`
theorem c2_87 : ¬ drop0% PFunctor.Approx.truncate_eq_of_agree 4 := fun h => by
  have := @h PF2 1 (.intro true fun _ => .continue) (.intro false fun _ => .intro false fun _ => .continue)
  cases this
-- `PFunctor.Approx.head_succ'`
theorem c2_88 : ¬ drop0% PFunctor.Approx.head_succ' 4 := fun h => absurd (@h PF2 0 1 xs) (by decide)
-- `PFunctor.M.ext'`
theorem c2_89 : ¬ drop0% PFunctor.M.ext' 3 := fun h => cs_ne (h PF2 (cs true) (cs false))
-- `PFunctor.M.mk_inj`
theorem c2_90 : ¬ drop0% PFunctor.M.mk_inj 3 := fun h =>
  Bool.noConfusion (congrArg Sigma.fst (@h PF2 ⟨true, fun _ => cs true⟩ ⟨false, fun _ => cs true⟩))
-- `PFunctor.M.isPath_cons`
theorem c2_91 : ¬ drop0% PFunctor.M.isPath_cons 6 := fun h =>
  Bool.noConfusion (@h PF2 [] true false (fun _ => cs true) ())
-- `PFunctor.M.isPath_cons'`
theorem c2_92 : ¬ drop0% PFunctor.M.isPath_cons' 5 := fun h => by
  have := @h PF2 [⟨false, ()⟩] true (fun _ => cs true) ()
  cases this with
  | cons _ _ g _ e _ =>
    have := congrArg PFunctor.M.head e
    rw [cs_head, PFunctor.M.head_mk] at this
    exact Bool.noConfusion this
-- `PFunctor.M.iselect_eq_default`
theorem c2_93 : ¬ drop0% PFunctor.M.iselect_eq_default 5 := fun h => by
  have := @h PF2 _ ⟨cs false⟩ [] (cs true)
  change (cs true).head = (cs false).head at this
  rw [cs_head, cs_head] at this; exact Bool.noConfusion this
-- `PFunctor.M.ext_aux`
theorem c2_94 : ¬ drop0% PFunctor.M.ext_aux 9 := fun h => by
  have := @h PF2 _ _ 0 (cs true) (cs false) (cs true) (.trivial _ _) (.trivial _ _)
  have := congrArg PFunctor.Approx.head' this
  rw [PFunctor.M.head'_eq_head, PFunctor.M.head'_eq_head, cs_head, cs_head] at this
  exact Bool.noConfusion this
-- `PFunctor.M.ext`
theorem c2_95 : ¬ drop0% PFunctor.M.ext 5 := fun h => cs_ne (@h PF2 _ _ (cs true) (cs false))
-- `PFunctor.M.IsBisimulation.head`
theorem c2_96 : ¬ drop0% PFunctor.M.IsBisimulation.head 2 := fun h =>
  Bool.noConfusion (@h PF2 (fun _ _ => True) true false (fun _ => cs true) (fun _ => cs true) trivial)
-- `PFunctor.M.IsBisimulation.head`
theorem c2_97 : ¬ drop0% PFunctor.M.IsBisimulation.head 7 := fun h =>
  Bool.noConfusion (@h PF2 _ botBis true false (fun _ => cs true) (fun _ => cs true))
-- `PFunctor.M.IsBisimulation.tail`
theorem c2_98 : ¬ drop0% PFunctor.M.IsBisimulation.tail 6 := fun h =>
  @h PF2 _ botBis true (fun _ => cs true) (fun _ => cs true) ()
-- `PFunctor.M.nth_of_bisim`
theorem c2_99 : ¬ drop0% PFunctor.M.nth_of_bisim 4 := fun h => by
  have := (@h PF2 (fun _ _ => True) _ _ (cs true) (cs false) [] trivial (Or.inl (.nil _))).1
  change (cs true).head = (cs false).head at this
  rw [cs_head, cs_head] at this; exact Bool.noConfusion this
-- `PFunctor.M.nth_of_bisim`
theorem c2_100 : ¬ drop0% PFunctor.M.nth_of_bisim 8 := fun h => by
  have := (@h PF2 _ _ _ botBis (cs true) (cs false) [] (Or.inl (.nil _))).1
  change (cs true).head = (cs false).head at this
  rw [cs_head, cs_head] at this; exact Bool.noConfusion this
-- `PFunctor.M.eq_of_bisim`
theorem c2_101 : ¬ drop0% PFunctor.M.eq_of_bisim 3 := fun h =>
  cs_ne (@h PF2 (fun _ _ => True) ⟨cs true⟩ (cs true) (cs false) trivial)
-- `PFunctor.M.eq_of_bisim`
theorem c2_102 : ¬ drop0% PFunctor.M.eq_of_bisim 6 := fun h =>
  cs_ne (@h PF2 _ ⟨cs true⟩ botBis (cs true) (cs false))
-- `PFunctor.M.bisim`
theorem c2_103 : ¬ drop0% PFunctor.M.bisim 2 := fun h => cs_ne (@h PF2 (fun _ _ => True) (cs true) (cs false) trivial)
-- `PFunctor.M.bisim`
theorem c2_104 : ¬ drop0% PFunctor.M.bisim 5 := fun h => cs_ne (@h PF2 (fun _ _ => False) (fun _ _ e => e.elim) (cs true) (cs false))
-- `PFunctor.M.bisim'`
theorem c2_105 : ¬ drop0% PFunctor.M.bisim' 5 := fun h =>
  cs_ne (@h PF2 Unit (fun _ => True) (fun _ => cs true) (fun _ => cs false) () trivial)
-- `PFunctor.M.bisim'`
theorem c2_106 : ¬ drop0% PFunctor.M.bisim' 7 := fun h =>
  cs_ne (@h PF2 Unit (fun _ => False) (fun _ => cs true) (fun _ => cs false) (fun _ e => e.elim) ())
-- `PFunctor.M.bisim_equiv`
theorem c2_107 : ¬ drop0% PFunctor.M.bisim_equiv 2 := fun h =>
  cs_ne (@h PF2 (fun _ _ => True) (cs true) (cs false) trivial)
-- `PFunctor.M.bisim_equiv`
theorem c2_108 : ¬ drop0% PFunctor.M.bisim_equiv 5 := fun h =>
  cs_ne (@h PF2 (fun _ _ => False) (fun _ _ e => e.elim) (cs true) (cs false))
-- `PFunctor.M.corec_unique`
theorem c2_109 : ¬ drop0% PFunctor.M.corec_unique 4 := fun h => by
  have := congrFun (@h PF2 Bool gB (fun _ => cs false)) true
  exact cs_ne this.symm

-- `PFunctor.M.ext_aux`
theorem c2_110 : ¬ drop0% PFunctor.M.ext_aux 7 := fun h => by
  have := @h PF2 ⟨cs true⟩ _ 1 (PFunctor.M.mk ⟨false, fun _ => cs true⟩) (PFunctor.M.mk ⟨true, fun _ => cs true⟩)
    (PFunctor.M.mk ⟨true, fun _ => cs true⟩) (PFunctor.M.agree'_refl _)
    (by
      intro ps hl
      match ps, hl with
      | [], hl => exact absurd hl (by simp)
      | [⟨a, i⟩], _ => cases a <;> rfl
      | _ :: _ :: _, hl => exact absurd hl (by simp))
  have := congrArg PFunctor.Approx.head' this
  rw [PFunctor.M.head'_eq_head, PFunctor.M.head'_eq_head, PFunctor.M.head_mk, PFunctor.M.head_mk] at this
  exact Bool.noConfusion this
-- `PFunctor.M.ext_aux`
theorem c2_111 : ¬ drop0% PFunctor.M.ext_aux 8 := fun h => by
  have := @h PF2 ⟨cs true⟩ _ 1 (PFunctor.M.mk ⟨true, fun _ => cs true⟩) (PFunctor.M.mk ⟨false, fun _ => cs true⟩)
    (PFunctor.M.mk ⟨true, fun _ => cs true⟩) (PFunctor.M.agree'_refl _)
    (by
      intro ps hl
      match ps, hl with
      | [], hl => exact absurd hl (by simp)
      | [⟨a, i⟩], _ => cases a <;> rfl
      | _ :: _ :: _, hl => exact absurd hl (by simp))
  have := congrArg PFunctor.Approx.head' this
  rw [PFunctor.M.head'_eq_head, PFunctor.M.head'_eq_head, PFunctor.M.head_mk, PFunctor.M.head_mk] at this
  exact Bool.noConfusion this
-- `PFunctor.M.nth_of_bisim`
theorem c2_112 : ¬ drop0% PFunctor.M.nth_of_bisim 9 := fun h => by
  obtain ⟨-, a, f, f', e1, e2, hR⟩ :=
    @h PF2 Rt _ _ Rt_bis (cs true) (cs true) [⟨false, ()⟩] ⟨rfl, rfl⟩
  have e0 : PFunctor.M.isubtree [⟨false, ()⟩] (cs true) = cs false := by rw [cs_mk]; rfl
  rw [e0] at e1
  have h1 := congrArg (fun x : PF2.M => x.dest.2 ()) e1
  simp only [cs_child] at h1
  exact cs_ne ((hR ()).1.symm.trans h1.symm)
-- `PNat.XgcdType.reduce_a`
theorem c2_113 : ¬ drop0% PNat.XgcdType.reduce_a 1 := fun h => by
  have := @h ⟨0, 0, 0, 0, 2, 1⟩
  rw [PNat.XgcdType.reduce_b (by decide), PNat.XgcdType.reduce_a (by decide)] at this
  exact absurd (congrArg PNat.XgcdType.wp this) (by decide)
-- `PNat.XgcdType.reduce_b`
theorem c2_114 : ¬ drop0% PNat.XgcdType.reduce_b 1 := fun h => by
  have := @h ⟨0, 0, 0, 0, 0, 0⟩
  rw [PNat.XgcdType.reduce_a (by decide), PNat.XgcdType.reduce_a (by decide)] at this
  exact absurd (congrArg (fun v : PNat.XgcdType => (v.wp, v.x, v.y, v.zp, v.ap, v.bp)) this) (by decide)
-- `PNat.XgcdType.reduce_isSpecial`
theorem c2_115 : ¬ drop0% PNat.XgcdType.reduce_isSpecial 1 := fun h => by
  have := h ⟨0, 0, 0, 1, 0, 0⟩
  rw [PNat.XgcdType.reduce_a (by decide)] at this
  unfold PNat.XgcdType.IsSpecial at this
  revert this; decide
-- `PNat.XgcdType.reduce_isSpecial'`
theorem c2_116 : ¬ drop0% PNat.XgcdType.reduce_isSpecial' 1 := fun h => by
  have := h ⟨0, 0, 0, 1, 0, 0⟩
  rw [PNat.XgcdType.reduce_a (by decide)] at this
  unfold PNat.XgcdType.IsSpecial' at this
  revert this; decide
-- `MvPFunctor.M.dest'_eq_dest'`
theorem c2_117 : ¬ indep0% MvPFunctor.M.dest'_eq_dest' 6 := fun h => by
  have := @h 0 P0 α0 (cs true) false (fun _ => cs true) true (fun _ => cs true) (cs_dest true) (fun _ _ => ())
  exact Bool.noConfusion ((congrArg Sigma.fst this).symm.trans (cs_head true))
-- `MvPFunctor.M.dest'_eq_dest'`
theorem c2_118 : ¬ indep0% MvPFunctor.M.dest'_eq_dest' 9 := fun h => by
  have := @h 0 P0 α0 (cs true) true (fun _ => cs true) (cs_dest true) false (fun _ => cs true) (fun _ _ => ())
  exact Bool.noConfusion ((congrArg Sigma.fst this).symm.trans (cs_head true))
-- `MvPFunctor.M.dest_eq_dest'`
theorem c2_119 : ¬ indep0% MvPFunctor.M.dest_eq_dest' 6 := fun h => by
  have := @h 0 P0 α0 (cs true) false (fun _ => cs true) (fun _ _ => ())
  exact Bool.noConfusion ((congrArg Sigma.fst this).symm.trans (cs_head true))
-- `MvPFunctor.M.bisim_lemma`
theorem c2_120 : ¬ drop0% MvPFunctor.M.bisim_lemma 8 := fun h => by
  obtain ⟨g, e, -⟩ := @h 0 P0 α0 (cs true) (fun _ _ => ()) false (fun _ _ => ()) (fun _ => mm true)
  exact Bool.noConfusion ((congrArg Sigma.fst e).symm.trans (cs_head true))
-- `MvPFunctor.M.bisim`
theorem c2_121 : ¬ drop0% MvPFunctor.M.bisim 4 := fun h => mm_ne (@h 0 P0 α0 (fun _ _ => True) (mm true) (mm false) trivial)
-- `MvPFunctor.M.bisim`
theorem c2_122 : ¬ drop0% MvPFunctor.M.bisim 7 := fun h =>
  mm_ne (@h 0 P0 α0 (fun _ _ => False) (fun _ _ e => e.elim) (mm true) (mm false))
-- `MvPFunctor.M.bisim₀`
theorem c2_123 : ¬ drop0% MvPFunctor.M.bisim₀ 5 := fun h =>
  mm_ne (@h 0 P0 α0 (fun _ _ => True) ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩ (mm true) (mm false) trivial)
-- `MvPFunctor.M.bisim₀`
theorem c2_124 : ¬ drop0% MvPFunctor.M.bisim₀ 8 := fun h =>
  mm_ne (@h 0 P0 α0 Eq ⟨fun _ => rfl, fun e => e.symm, fun e1 e2 => e1.trans e2⟩ (fun x y e => e ▸ rfl) (mm true) (mm false))
-- `MvPFunctor.M.bisim'`
theorem c2_125 : ¬ drop0% MvPFunctor.M.bisim' 4 := fun h => mm_ne (@h 0 P0 α0 (fun _ _ => True) (mm true) (mm false) trivial)
-- `MvPFunctor.M.bisim'`
theorem c2_126 : ¬ drop0% MvPFunctor.M.bisim' 7 := fun h =>
  mm_ne (@h 0 P0 α0 (fun _ _ => False) (fun _ _ e => e.elim) (mm true) (mm false))
-- `MvPFunctor.M.bisim₀`
theorem c2_127 : drop% MvPFunctor.M.bisim₀ 4 := by
  intro n P α R h x y r
  have h' : ∀ x y, Relation.EqvGen R x y →
      MvFunctor.map (TypeVec.appendFun TypeVec.id (Quot.mk R)) (MvPFunctor.M.dest P x) =
        MvFunctor.map (TypeVec.appendFun TypeVec.id (Quot.mk R)) (MvPFunctor.M.dest P y) := by
    intro x y hxy
    induction hxy with
    | rel _ _ hr => exact h _ _ hr
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  apply MvPFunctor.M.bisim P (Relation.EqvGen R) _ _ _ (.rel _ _ r)
  clear r x y
  introv Hr
  specialize h' _ _ Hr
  clear Hr
  revert h'
  rcases MvPFunctor.M.dest P x with ⟨ax, fx⟩
  rcases MvPFunctor.M.dest P y with ⟨ay, fy⟩
  intro h
  rw [MvPFunctor.map_eq, MvPFunctor.map_eq] at h
  injection h with h₀ h₁
  subst ay
  try simp only [heq_eq_eq] at h₁
  have Hdrop : TypeVec.dropFun fx = TypeVec.dropFun fy := by
    replace h₁ := congr(TypeVec.dropFun $h₁)
    simpa using! h₁
  exists ax, TypeVec.dropFun fx, TypeVec.lastFun fx, TypeVec.lastFun fy
  rw [TypeVec.split_dropFun_lastFun, Hdrop, TypeVec.split_dropFun_lastFun]
  refine ⟨rfl, rfl, fun i => ?_⟩
  replace h₁ := congr($h₁ Fin2.fz i)
  simp only [TypeVec.comp, TypeVec.appendFun, TypeVec.splitFun] at h₁
  exact Quot.eqvGen_exact h₁
-- `MvPFunctor.M.map_dest`
theorem c2_128 : ¬ drop0% MvPFunctor.M.map_dest 6 := fun h => by
  have := @h 0 P0 α0 α0 (TypeVec.appendFun TypeVec.id (fun _ => mm false)) (mm true)
  have := congrArg (fun o : P0 (α0 ::: P0.M α0) => ((o.2 Fin2.fz () : P0.M α0).1 : PF2.M).head) this
  dsimp only at this
  change (cs false).head = ((cs true).dest.2 ()).head at this
  rw [cs_child, cs_head, cs_head] at this
  exact Bool.noConfusion this

open Ordnode

-- `Ordnode.Valid'.bal`
theorem c2_129 : ¬ drop0% Ordnode.Valid'.bal 5 := fun h =>
  absurd (@h ℕ _ ⊥ (node 3 nil 0 (node 2 nil 1 (sg 2))) ⊤) (by decide)
-- `Ordnode.Valid'.of_lt`
theorem c2_130 : ¬ drop0% Ordnode.Valid'.of_lt 8 := fun h =>
  absurd (@h ℕ _ (sg 5) 0 ⊥ ⊤ (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.of_gt`
theorem c2_131 : ¬ drop0% Ordnode.Valid'.of_gt 8 := fun h =>
  absurd (@h ℕ _ (sg 0) 5 ⊥ ⊤ (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node`
theorem c2_132 : ¬ drop0% Ordnode.Valid'.node 10 := fun h =>
  absurd (@h ℕ _ 3 nil 0 (node 2 nil 1 (sg 2)) ⊥ ⊤ (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node`
theorem c2_133 : ¬ drop0% Ordnode.Valid'.node 11 := fun h =>
  absurd (@h ℕ _ 5 nil 0 nil ⊥ ⊤ (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node'`
theorem c2_134 : ¬ drop0% Ordnode.Valid'.node' 9 := fun h =>
  absurd (@h ℕ _ nil 0 (node 2 nil 1 (sg 2)) ⊥ ⊤ (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node3L`
theorem c2_135 : ¬ drop0% Ordnode.Valid'.node3L 9 := fun h =>
  absurd (@h ℕ _ (sg 5) 1 nil 2 (sg 3) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node3L`
theorem c2_136 : ¬ drop0% Ordnode.Valid'.node3L 11 := fun h =>
  absurd (@h ℕ _ (sg 0) 1 nil 2 (sg 0) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node3L`
theorem c2_137 : ¬ drop0% Ordnode.Valid'.node3L 12 := fun h =>
  absurd (@h ℕ _ nil 0 (node 2 nil 1 (sg 2)) 3 (sg 4) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide))
    (by decide)
-- `Ordnode.Valid'.node3L`
theorem c2_138 : ¬ drop0% Ordnode.Valid'.node3L 13 := fun h =>
  absurd (@h ℕ _ nil 0 nil 1 (bt 2 4) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node3R`
theorem c2_139 : ¬ drop0% Ordnode.Valid'.node3R 9 := fun h =>
  absurd (@h ℕ _ (sg 5) 1 nil 2 nil ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node3R`
theorem c2_140 : ¬ drop0% Ordnode.Valid'.node3R 11 := fun h =>
  absurd (@h ℕ _ (sg 0) 1 nil 2 (sg 0) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node3R`
theorem c2_141 : ¬ drop0% Ordnode.Valid'.node3R 12 := fun h =>
  absurd (@h ℕ _ nil 0 (sg 1) 2 (sg 3) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node3R`
theorem c2_142 : ¬ drop0% Ordnode.Valid'.node3R 13 := fun h =>
  absurd (@h ℕ _ (bt 0 4) 4 nil 5 (bt 6 4) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node4L_lemma₄`
theorem c2_143 : ¬ drop0% Ordnode.Valid'.node4L_lemma₄ 5 := fun h => absurd (@h 4 9 3 0 (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node4L_lemma₄`
theorem c2_144 : ¬ drop0% Ordnode.Valid'.node4L_lemma₄ 6 := fun h => absurd (@h 4 8 0 3 (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node4L_lemma₅`
theorem c2_145 : ¬ drop0% Ordnode.Valid'.node4L_lemma₅ 4 := fun h => absurd (@h 0 2 6 4 (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node4L_lemma₅`
theorem c2_146 : ¬ drop0% Ordnode.Valid'.node4L_lemma₅ 5 := fun h => absurd (@h 1 0 0 7 (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node4L`
theorem c2_147 : ¬ drop0% Ordnode.Valid'.node4L 9 := fun h =>
  absurd (@h ℕ _ (node 0 nil 0 nil) 1 (sg 2) 3 nil ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node4L`
theorem c2_148 : ¬ drop0% Ordnode.Valid'.node4L 11 := fun h =>
  absurd (@h ℕ _ nil 0 (sg 1) 2 (node 0 nil 3 nil) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.node4L`
theorem c2_149 : drop% Ordnode.Valid'.node4L 12 := by
  intro α _ l x m y r o₁ o₂ hl hm hr H
  refine hl.node4L hm hr ?_ H
  simp only [Ordnode.ratio, Ordnode.delta] at H; omega
-- `Ordnode.Valid'.node4L`
theorem c2_150 : ¬ drop0% Ordnode.Valid'.node4L 13 := fun h =>
  absurd (@h ℕ _ nil 0 (sg 1) 2 (bt 3 3) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.rotateL`
theorem c2_151 : ¬ drop0% Ordnode.Valid'.rotateL 7 := fun h =>
  absurd (@h ℕ _ (node 0 nil 0 nil) 1 (node 2 nil 2 (sg 3)) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide))
    (by decide)
-- `Ordnode.Valid'.rotateL`
theorem c2_152 : ¬ drop0% Ordnode.Valid'.rotateL 8 := fun h =>
  absurd (@h ℕ _ nil 0 (node 2 nil 5 (sg 1)) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.rotateL`
theorem c2_153 : drop% Ordnode.Valid'.rotateL 9 := by
  intro α _ l x r o₁ o₂ hl hr H2 H3
  by_cases H1 : l.size + r.size ≤ 1
  · have hl0 : l.size = 0 := by simp only [Ordnode.delta] at H2; omega
    have hr1 : r.size = 1 := by simp only [Ordnode.delta] at H2; omega
    obtain rfl := hl.2.size_eq_zero.1 hl0
    obtain _ | ⟨rs, rl, y, rr⟩ := r
    · simp at hr1
    · have hs := hr.2.1
      simp only [Ordnode.size_node] at hr1
      have e1 : rl.size = 0 := by omega
      have e2 : rr.size = 0 := by omega
      obtain rfl := hr.2.2.1.size_eq_zero.1 e1
      obtain rfl := hr.2.2.2.size_eq_zero.1 e2
      subst hr1
      have hb := hr.1
      exact (Valid'.node' (Valid'.node' hl (valid'_nil hb.1) (Or.inl (by simp [Ordnode.node'])))
        (valid'_nil hb.2) (Or.inl (by simp [Ordnode.node'])) :)
  · exact hl.rotateL hr H1 H2 H3
-- `Ordnode.Valid'.rotateL`
theorem c2_154 : ¬ drop0% Ordnode.Valid'.rotateL 10 := fun h =>
  absurd (@h ℕ _ (bt 0 3) 3 (node 2 nil 4 (sg 5)) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.rotateL`
theorem c2_155 : ¬ drop0% Ordnode.Valid'.rotateL 11 := fun h =>
  absurd (@h ℕ _ (sg 0) 1 (bt 2 20) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.rotateR`
theorem c2_156 : ¬ drop0% Ordnode.Valid'.rotateR 7 := fun h =>
  absurd (@h ℕ _ (node 2 (sg 5) 1 nil) 9 nil ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.rotateR`
theorem c2_157 : ¬ drop0% Ordnode.Valid'.rotateR 8 := fun h =>
  absurd (@h ℕ _ (node 2 (sg 0) 1 nil) 2 (node 0 nil 3 nil) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide))
    (by decide)
-- `Ordnode.Valid'.rotateR`
theorem c2_158 : drop% Ordnode.Valid'.rotateR 9 := by
  intro α _ l x r o₁ o₂ hl hr H2 H3
  by_cases H1 : l.size + r.size ≤ 1
  · have hr0 : r.size = 0 := by simp only [Ordnode.delta] at H2; omega
    have hl1 : l.size = 1 := by simp only [Ordnode.delta] at H2; omega
    obtain rfl := hr.2.size_eq_zero.1 hr0
    obtain _ | ⟨ls, ll, y, lr⟩ := l
    · simp at hl1
    · have hs := hl.2.1
      simp only [Ordnode.size_node] at hl1
      have e1 : ll.size = 0 := by omega
      have e2 : lr.size = 0 := by omega
      obtain rfl := hl.2.2.1.size_eq_zero.1 e1
      obtain rfl := hl.2.2.2.size_eq_zero.1 e2
      subst hl1
      have hb := hl.1
      exact (Valid'.node' (valid'_nil hb.1) (Valid'.node' (valid'_nil hb.2) hr (Or.inl (by simp [Ordnode.node'])))
        (Or.inl (by simp [Ordnode.node'])) :)
  · exact hl.rotateR hr H1 H2 H3
-- `Ordnode.Valid'.rotateR`
theorem c2_159 : ¬ drop0% Ordnode.Valid'.rotateR 10 := fun h =>
  absurd (@h ℕ _ (node 2 (sg 0) 1 nil) 2 (bt 3 3) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.rotateR`
theorem c2_160 : ¬ drop0% Ordnode.Valid'.rotateR 11 := fun h =>
  absurd (@h ℕ _ (bt 0 20) 20 (sg 21) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.balance'_aux`
theorem c2_161 : ¬ drop0% Ordnode.Valid'.balance'_aux 9 := fun h =>
  absurd (@h ℕ _ (sg 0) 1 (bt 2 20) ⊥ ⊤ (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.balance'_aux`
theorem c2_162 : ¬ drop0% Ordnode.Valid'.balance'_aux 10 := fun h =>
  absurd (@h ℕ _ (bt 0 20) 20 (sg 21) ⊥ ⊤ (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.balance'_lemma`
theorem c2_163 : ¬ drop0% Ordnode.Valid'.balance'_lemma 5 := fun h =>
  absurd (@h ℕ nil 0 (node 10 nil 0 nil) 10 (Or.inl ⟨by decide, rfl⟩)) (by decide)
-- `Ordnode.Valid'.balance'_lemma`
theorem c2_164 : ¬ drop0% Ordnode.Valid'.balance'_lemma 6 := fun h =>
  absurd (@h ℕ nil 0 (node 10 nil 0 nil) 0 (by decide)) (by decide)
-- `Ordnode.Valid'.balance'`
theorem c2_165 : ¬ drop0% Ordnode.Valid'.balance' 7 := fun h =>
  absurd (@h ℕ _ (sg 5) 1 nil ⊥ ⊤ (by decide) ⟨1, 0, by decide, Or.inl ⟨by decide, rfl⟩⟩) (by decide)
-- `Ordnode.Valid'.balance'`
theorem c2_166 : ¬ drop0% Ordnode.Valid'.balance' 8 := fun h =>
  absurd (@h ℕ _ nil 1 (sg 0) ⊥ ⊤ (by decide) ⟨0, 1, by decide, Or.inl ⟨by decide, rfl⟩⟩) (by decide)
-- `Ordnode.Valid'.balance'`
theorem c2_167 : ¬ drop0% Ordnode.Valid'.balance' 9 := fun h =>
  absurd (@h ℕ _ (sg 0) 1 (bt 2 20) ⊥ ⊤ (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.balance`
theorem c2_168 : ¬ drop0% Ordnode.Valid'.balance 7 := fun h =>
  absurd (@h ℕ _ (sg 5) 1 nil ⊥ ⊤ (by decide) ⟨1, 0, by decide, Or.inl ⟨by decide, rfl⟩⟩) (by decide)
-- `Ordnode.Valid'.balance`
theorem c2_169 : ¬ drop0% Ordnode.Valid'.balance 8 := fun h =>
  absurd (@h ℕ _ nil 1 (sg 0) ⊥ ⊤ (by decide) ⟨0, 1, by decide, Or.inl ⟨by decide, rfl⟩⟩) (by decide)
-- `Ordnode.Valid'.balance`
theorem c2_170 : ¬ drop0% Ordnode.Valid'.balance 9 := fun h =>
  absurd (@h ℕ _ (sg 0) 1 (bt 2 20) ⊥ ⊤ (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.balanceL_aux`
theorem c2_171 : ¬ drop0% Ordnode.Valid'.balanceL_aux 9 := fun h =>
  absurd (@h ℕ _ nil 0 (bt 1 3) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.balanceL_aux`
theorem c2_172 : ¬ drop0% Ordnode.Valid'.balanceL_aux 10 := fun h =>
  absurd (@h ℕ _ (sg 0) 1 (bt 2 10) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.balanceL_aux`
theorem c2_173 : ¬ drop0% Ordnode.Valid'.balanceL_aux 11 := fun h =>
  absurd (@h ℕ _ (bt 0 10) 10 nil ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.balanceL`
theorem c2_174 : ¬ drop0% Ordnode.Valid'.balanceL 9 := fun h =>
  absurd (@h ℕ _ nil 0 (bt 1 3) ⊥ ⊤ (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.balanceR_aux`
theorem c2_175 : ¬ drop0% Ordnode.Valid'.balanceR_aux 9 := fun h =>
  absurd (@h ℕ _ (bt 0 3) 3 nil ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.balanceR_aux`
theorem c2_176 : ¬ drop0% Ordnode.Valid'.balanceR_aux 10 := fun h =>
  absurd (@h ℕ _ (bt 0 10) 10 (sg 11) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.balanceR_aux`
theorem c2_177 : ¬ drop0% Ordnode.Valid'.balanceR_aux 11 := fun h =>
  absurd (@h ℕ _ nil 0 (bt 1 10) ⊥ ⊤ (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.balanceR`
theorem c2_178 : ¬ drop0% Ordnode.Valid'.balanceR 9 := fun h =>
  absurd (@h ℕ _ (bt 0 3) 3 nil ⊥ ⊤ (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.glue_aux`
theorem c2_179 : ¬ drop0% Ordnode.Valid'.glue_aux 8 := fun h =>
  absurd (@h ℕ _ (sg 1) (sg 0) ⊥ ⊤ (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.glue_aux`
theorem c2_180 : ¬ drop0% Ordnode.Valid'.glue_aux 9 := fun h =>
  absurd (@h ℕ _ (sg 0) (bt 1 10) ⊥ ⊤ (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.glue`
theorem c2_181 : ¬ drop0% Ordnode.Valid'.glue 9 := fun h =>
  absurd (@h ℕ _ (sg 0) 1 (bt 2 10) ⊥ ⊤ (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.merge_aux₁`
theorem c2_182 : drop% Ordnode.Valid'.merge_aux₁ 13 := by
  intro α _ o₁ o₂ ls ll lx lr rs rl rx rr t hr h v e
  rw [hr.2.1, Ordnode.delta] at h
  have hb := hr.3.1
  unfold BalancedSz at hb
  simp only [Ordnode.delta] at hb
  have H₁ : size t = 0 → size rr ≤ 1 := by omega
  have H₂ : 1 ≤ size t → 1 ≤ size rr → size rr ≤ delta * size t := by simp only [Ordnode.delta]; omega
  have H₃ : 2 * size t ≤ 9 * size rr + 5 ∨ size t ≤ 3 := by omega
  refine ⟨Valid'.balanceL_aux v hr.right H₁ H₂ H₃, ?_⟩
  rw [balanceL_eq_balance v.2 hr.2.2.2 H₁ H₂, balance_eq_balance' v.3 hr.3.2.2 v.2 hr.2.2.2,
    size_balance' v.2 hr.2.2.2, e, hr.2.1]
  omega
-- `Ordnode.Valid'.merge_aux₁`
theorem c2_183 : ¬ drop0% Ordnode.Valid'.merge_aux₁ 14 := fun h =>
  absurd (@h ℕ _ ⊥ ⊤ 1 nil 0 nil 10 nil 5 nil (sg 0) (by decide) (by decide) (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.merge_aux₁`
theorem c2_184 : ¬ drop0% Ordnode.Valid'.merge_aux₁ 15 := fun h =>
  absurd (@h ℕ _ ⊥ ⊤ 10 (bt 0 5) 5 (bt 6 4) 1 nil 100 nil (bt 0 10) (by decide) (by decide) (by decide) (by decide))
    (by decide)
-- `Ordnode.Valid'.merge_aux₁`
theorem c2_185 : ¬ drop0% Ordnode.Valid'.merge_aux₁ 16 := fun h =>
  absurd (@h ℕ _ ⊥ ⊤ 1 nil 0 nil 4 (sg 4) 5 (node 2 nil 6 (sg 7)) (node 2 nil 0 nil) (by decide) (by decide)
    (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.merge_aux₁`
theorem c2_186 : ¬ drop0% Ordnode.Valid'.merge_aux₁ 17 := fun h =>
  absurd (@h ℕ _ ⊥ ⊤ 1 nil 0 nil 4 (sg 4) 5 (node 2 nil 6 (sg 7)) (bt 0 4) (by decide) (by decide)
    (by decide) (by decide)) (by decide)
-- `Ordnode.Valid'.merge_aux`
theorem c2_187 : ¬ drop0% Ordnode.Valid'.merge_aux 8 := fun h =>
  absurd (@h ℕ _ (sg 1) (sg 0) ⊥ ⊤ (by decide) (by decide)) (by decide)
-- `Ordnode.Valid.merge`
theorem c2_188 : ¬ drop0% Ordnode.Valid.merge 6 := fun h =>
  absurd (@h ℕ _ (sg 1) (sg 0) (by decide) (by decide)) (by decide)
-- `Ordnode.insertWith.valid_aux`
theorem c2_189 : ¬ drop0% Ordnode.insertWith.valid_aux 2 := fun h =>
  absurd (@h DN _ _ id d1 (fun y h => h) (sg d0) ⊥ ⊤ (by decide) (by decide) (by decide)).1 (by decide)
-- `Ordnode.insertWith.valid_aux`
theorem c2_190 : ¬ drop0% Ordnode.insertWith.valid_aux 6 := fun h =>
  absurd (@h ℕ _ _ _ (fun _ => 5) 0 (sg 0) ⊥ (1 : ℕ) (by decide) (by decide) (by decide)).1 (by decide)
-- `Ordnode.insertWith.valid_aux`
theorem c2_191 : ¬ drop0% Ordnode.insertWith.valid_aux 11 := fun h =>
  absurd (@h ℕ _ _ _ id 0 (fun y h => h) nil (5 : ℕ) ⊤ (by decide) (by decide)).1 (by decide)
-- `Ordnode.insertWith.valid_aux`
theorem c2_192 : ¬ drop0% Ordnode.insertWith.valid_aux 12 := fun h =>
  absurd (@h ℕ _ _ _ id 5 (fun y h => h) nil ⊥ (0 : ℕ) (by decide) (by decide)).1 (by decide)
-- `Ordnode.insertWith.valid`
theorem c2_193 : ¬ drop0% Ordnode.insertWith.valid 2 := fun h =>
  absurd (@h DN _ _ id d1 (fun y h => h) (sg d0) (by decide)) (by decide)
-- `Ordnode.insertWith.valid`
theorem c2_194 : ¬ drop0% Ordnode.insertWith.valid 6 := fun h =>
  absurd (@h ℕ _ _ _ (fun _ => 5) 0 (node 3 (sg 0) 1 (sg 2)) (by decide)) (by decide)
-- `Ordnode.insert.valid`
theorem c2_195 : ¬ drop0% Ordnode.insert.valid 2 := fun h =>
  absurd (@h DN _ _ d1 (sg d0) (by decide)) (by decide)
-- `Ordnode.insert'.valid`
theorem c2_196 : ¬ drop0% Ordnode.insert'.valid 2 := fun h =>
  absurd (@h DN _ _ d1 (sg d0) (by decide)) (by decide)
-- `Ordnode.map.valid`
theorem c2_197 : ¬ drop0% Ordnode.map.valid 5 := fun h =>
  absurd (@h ℕ _ ℕ _ (fun _ => 0) (node 2 nil 0 (sg 1)) (by decide)) (by decide)
-- `Ordnode.size_erase_of_mem`
theorem c2_198 : ¬ drop0% Ordnode.size_erase_of_mem 8 := fun h =>
  absurd (@h ℕ _ _ 0 (sg 1) ⊥ ⊤ (by decide)) (by decide)
-- `Ordset.pos_size_of_mem`
theorem c2_199 : ¬ drop0% Ordset.pos_size_of_mem 5 := fun h =>
  absurd (@h ℕ _ _ 0 ∅) (by decide)
