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

elab "indep1% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.one
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType (xs.getD (j) default)
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push (xs.getD (j) default)
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

namespace W3c3
universe u

-- Rat.cast commutes with inverse in every division ring
theorem rat_cast_inv {α : Type u} [DivisionRing α] (q : ℚ) : ((q⁻¹ : ℚ) : α) = (q : α)⁻¹ := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  by_cases h : (q.num : α) = 0
  · have h1 : (q : α) = 0 := by rw [Rat.cast_def, h, zero_div]
    have h2 : ((q⁻¹).den : α) = 0 := by
      rw [Rat.den_inv_of_ne_zero hq]
      rcases Int.natAbs_eq q.num with e | e
      · rw [e, Int.cast_natCast] at h; exact h
      · rw [e, Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h; exact h
    rw [h1, inv_zero, Rat.cast_def, h2, div_zero]
  · exact Rat.cast_inv_of_ne_zero h
-- NNRat.cast commutes with inverse in every division semiring
theorem nnrat_cast_inv {α : Type u} [DivisionSemiring α] (q : ℚ≥0) : ((q⁻¹ : ℚ≥0) : α) = (q : α)⁻¹ := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  by_cases h : (q.num : α) = 0
  · have h1 : (q : α) = 0 := by rw [NNRat.cast_def, h, zero_div]
    have h2 : ((q⁻¹).den : α) = 0 := by
      rw [← NNRat.den_coe, NNRat.coe_inv, Rat.den_inv_of_ne_zero (by exact_mod_cast hq)]
      rw [NNRat.natAbs_num_coe]; exact h
    rw [h1, inv_zero, NNRat.cast_def, h2, div_zero]
  · exact NNRat.cast_inv_of_ne_zero h
theorem rat_cast_zpow {α : Type u} [DivisionRing α] (q : ℚ) (n : ℤ) : ((q ^ n : ℚ) : α) = (q : α) ^ n := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simp [Rat.cast_pow]
  · simp only [zpow_neg, zpow_natCast, rat_cast_inv, Rat.cast_pow]
theorem nnrat_cast_zpow {α : Type u} [DivisionSemiring α] (q : ℚ≥0) (n : ℤ) : ((q ^ n : ℚ≥0) : α) = (q : α) ^ n := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simp [NNRat.cast_pow]
  · simp only [zpow_neg, zpow_natCast, nnrat_cast_inv, NNRat.cast_pow]

-- ZMod 2 as a field (characteristic 2), with division and casts made decidable
def F2 := ZMod 2
instance : DecidableEq F2 := inferInstanceAs (DecidableEq (ZMod 2))
noncomputable instance : Field F2 := IsField.toField (R := ZMod 2) ⟨⟨0, 1, by decide⟩, mul_comm,
  by intro a h; exact ⟨a, by revert a; decide⟩⟩
theorem f2_cases (y : F2) : y = 0 ∨ y = 1 := (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) y
theorem f2_div (x y : F2) : x / y = if y = 0 then 0 else x := by
  rcases f2_cases y with rfl | rfl
  · simp
  · rw [div_one]; simp only [one_ne_zero, if_false]
theorem castF2 (q : ℚ) : (q : F2) = if (q.den : F2) = 0 then 0 else (q.num : F2) := by
  rw [Rat.cast_def, f2_div]
theorem ncastF2 (q : ℚ≥0) : (q : F2) = if (q.den : F2) = 0 then 0 else (q.num : F2) := by
  rw [NNRat.cast_def, f2_div]
theorem not_cz : ¬ CharZero F2 := fun h =>
  absurd (h.cast_injective (show ((2:ℕ):F2) = ((0:ℕ):F2) by decide)) (by decide)

-- bare FunLike wrapper (no hom laws)
structure FW (α β : Type) where
  toFun : α → β
instance (α β : Type) : FunLike (FW α β) α β where
  coe := FW.toFun
  coe_injective := fun f g h => by cases f; cases g; cases h; rfl
def intPartN (x : ℚ≥0) : ℚ≥0 := if x.den = 1 then x else 0
theorem intPartN_nat (n : ℕ) : intPartN (n : ℚ≥0) = n := by simp [intPartN]
theorem fwN_ne : (⟨id⟩ : FW ℚ≥0 ℚ≥0) ≠ ⟨intPartN⟩ := fun e =>
  absurd (congrArg (fun f : FW ℚ≥0 ℚ≥0 => f.toFun 2⁻¹) e) (by decide +kernel)
def intPartQ (x : ℚ) : ℚ := if x.den = 1 then x else 0
theorem intPartQ_int (n : ℤ) : intPartQ (n : ℚ) = n := by simp [intPartQ]
theorem fwQ_ne : (⟨id⟩ : FW ℚ ℚ) ≠ ⟨intPartQ⟩ := fun e =>
  absurd (congrArg (fun f : FW ℚ ℚ => f.toFun 2⁻¹) e) (by decide +kernel)
-- the monoid-with-zero hom x ↦ (if x = 0 then 0 else 1)
def nzN : ℚ≥0 →*₀ ℚ≥0 where
  toFun x := if x = 0 then 0 else 1
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
theorem nzN_ne : MonoidWithZeroHom.id ℚ≥0 ≠ nzN := fun e =>
  absurd (DFunLike.congr_fun e 2) (by simp [nzN])
def nzQ : ℚ →*₀ ℚ where
  toFun x := if x = 0 then 0 else 1
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
theorem nzQ_ne : MonoidWithZeroHom.id ℚ ≠ nzQ := fun e =>
  absurd (DFunLike.congr_fun e 2) (by simp [nzQ])
def absQ : ℚ →*₀ ℚ where
  toFun x := |x|
  map_zero' := abs_zero
  map_one' := abs_one
  map_mul' := abs_mul
theorem absQ_nat (n : ℕ) : MonoidWithZeroHom.id ℚ n = absQ n := by simp [absQ]
theorem absQ_ne : MonoidWithZeroHom.id ℚ ≠ absQ := fun e =>
  absurd (DFunLike.congr_fun e (-1)) (by norm_num [absQ])
def sgnQ : ℚ →*₀ ℚ where
  toFun x := x / |x|
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by simp only [abs_mul, mul_div_mul_comm]
theorem sgnQ_neg1 : MonoidWithZeroHom.id ℚ (-1) = sgnQ (-1) := by simp [sgnQ]
theorem sgnQ_ne : MonoidWithZeroHom.id ℚ ≠ sgnQ := fun e =>
  absurd (DFunLike.congr_fun e 2) (by norm_num [sgnQ])
end W3c3
open W3c3

namespace W3c3
-- the total and the discrete setoid
def TopS (α : Type) : Setoid α := ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩
def EqS (α : Type) : Setoid α := ⟨Eq, eq_equivalence⟩
end W3c3

namespace W3c3
noncomputable section
-- constant QPF with value Bool (shape Bool, no children): Fix/Cofix have two distinct points
def CB : PFunctor.{0, 0} := ⟨Bool, fun _ => PEmpty⟩
instance qCB : QPF CB.Obj where
  P := CB
  abs := id
  repr := id
  abs_repr _ := rfl
  abs_map _ _ := rfl
def cbg (b : Bool) : CB.Obj Bool := ⟨b, PEmpty.elim⟩
noncomputable def cc (b : Bool) : QPF.Cofix CB.Obj := QPF.Cofix.corec cbg b
theorem cc_head (b : Bool) : (QPF.Cofix.dest (cc b)).1 = b := by
  rw [cc, QPF.Cofix.dest_corec]; rfl
theorem cc_ne : cc true ≠ cc false := fun e => by
  have := congrArg (fun c => (QPF.Cofix.dest c).1) e
  simp only [cc_head] at this
  exact absurd (show (true : Bool) = false from this) (by decide)
def fx : QPF.Fix CB.Obj := QPF.Fix.mk (⟨true, PEmpty.elim⟩ : CB.Obj _)
def wb (b : Bool) : CB.W := WType.mk b PEmpty.elim
theorem wb_rec (b : Bool) : QPF.recF (F := CB.Obj) (α := Bool) (fun x => x.1) (wb b) = b := rfl
-- shape Bool, one child, with a mapConst that flips the shape: not a lawful functor
def SF (α : Type) : Type := (⟨Bool, fun _ => Unit⟩ : PFunctor.{0, 0}).Obj α
instance : Functor SF where
  map f x := PFunctor.map _ f x
  mapConst a x := ⟨!x.1, fun _ => a⟩
instance qSF : QPF SF where
  P := ⟨Bool, fun _ => Unit⟩
  abs := id
  repr := id
  abs_repr _ := rfl
  abs_map _ _ := rfl
-- non-uniform QPF: F α = PLift (Nonempty α), represented by α (P = identity)
def NE (α : Type) : Type := PLift (Nonempty α)
instance : Functor NE where
  map f x := ⟨x.down.map f⟩
noncomputable instance qNE : QPF NE where
  P := ⟨Unit, fun _ => Unit⟩
  abs x := ⟨⟨x.2 ()⟩⟩
  repr x := ⟨(), fun _ => Classical.choice x.down⟩
  abs_repr _ := rfl
  abs_map _ _ := rfl
theorem ne_supp (b : Bool) (x : NE Bool) : b ∉ Functor.supp x := fun hb => by
  rw [QPF.mem_supp] at hb
  obtain ⟨_, _, hc⟩ := hb () (fun _ => !b) rfl
  cases b <;> simp at hc
def neT : NE Bool := ⟨⟨true⟩⟩
end
end W3c3

namespace W3c3
noncomputable section
-- multivariate constant functor Const 1 Bool over the empty TypeVec
abbrev KB := MvQPF.Const 1 Bool
def tv0 : TypeVec.{0} 0 := Fin2.elim0 (C := fun _ => Type)
def mc (b : Bool) : MvQPF.Cofix KB tv0 := MvQPF.Cofix.mk (MvQPF.Const.mk b)
theorem mc_ne : mc true ≠ mc false := fun e => by
  have := congrArg MvQPF.Cofix.dest e
  rw [mc, mc, MvQPF.Cofix.dest_mk, MvQPF.Cofix.dest_mk] at this
  exact absurd (show (true : Bool) = false from this) (by decide)
def mfx : MvQPF.Fix KB tv0 := MvQPF.Fix.mk (MvQPF.Const.mk true)
def getC (x : KB (tv0 ::: Bool)) : Bool := MvQPF.Const.get x
def mw (b : Bool) : (MvQPF.P KB).W tv0 := (MvQPF.P KB).wMk b (fun i => nomatch i) (fun e => PEmpty.elim e)
theorem mw_rec (b : Bool) : MvQPF.recF getC (mw b) = b := (MvQPF.recF_eq getC b _ _).trans rfl
theorem mwm_rec (b : Bool) : MvQPF.recF getC (MvFunctor.map TypeVec.id (mw b)) = b := by
  rw [mw]; erw [MvPFunctor.w_map_wMk]; exact (MvQPF.recF_eq getC b _ _).trans rfl
theorem mw_ne : ¬ MvQPF.WEquiv (mw true) (mw false) := fun e =>
  absurd ((mw_rec true).symm.trans ((MvQPF.recF_eq_of_wEquiv tv0 getC _ _ e).trans (mw_rec false))) (by decide)
end
end W3c3

namespace W3c3
noncomputable section
-- non-uniform MvQPF in one variable: F α = PLift (Nonempty (α 0)), represented by α 0
def NP : MvPFunctor.{0} 1 := ⟨Unit, fun _ _ => Unit⟩
def MNE (α : TypeVec.{0} 1) : Type := PLift (Nonempty (α Fin2.fz))
instance : MvFunctor MNE where
  map f x := ⟨x.down.map (f Fin2.fz)⟩
def mneRepr {α : TypeVec.{0} 1} (x : MNE α) : NP α :=
  ⟨(), fun i => match i with
    | .fz => fun _ => Classical.choice x.down
    | .fs k => nomatch k⟩
instance qMNE : MvQPF MNE where
  P := NP
  abs x := ⟨⟨x.2 Fin2.fz ()⟩⟩
  repr := mneRepr
  abs_repr _ := rfl
  abs_map _ _ := rfl
abbrev bv : TypeVec.{0} 1 := fun _ => Bool
def mneT : MNE bv := ⟨⟨true⟩⟩
theorem mne_supp (b : Bool) (x : MNE bv) : b ∉ MvFunctor.supp x Fin2.fz := fun hb => by
  obtain ⟨_, _, hc⟩ := (MvQPF.mem_supp x Fin2.fz b).1 hb () (fun _ _ => !b) rfl
  cases b <;> simp at hc
end
end W3c3

namespace W3c3
-- the diagonal relation on Bool as an arrow into repeat 1 Prop
def RD : TypeVec.Arrow (TypeVec.prod bv bv) (TypeVec.repeat 1 Prop) := fun i => match i with
  | .fz => fun p => (p.1 = p.2 : Prop)
  | .fs k => nomatch k
end W3c3

namespace W3c3
noncomputable section
-- unlawful MvFunctor with value Bool: map flips the value unless its 0-th component is surjective
def WK (γ : TypeVec.{0} 1) : Type := Bool
open Classical in
instance : MvFunctor WK where
  map φ u := if Function.Surjective (φ Fin2.fz) then u else !u
def uv : TypeVec.{0} 1 := fun _ => Unit
-- the relation p.2 = true on Bool as an arrow into repeat 1 Prop
def R2 : TypeVec.Arrow (TypeVec.prod bv bv) (TypeVec.repeat 1 Prop) := fun i => match i with
  | .fz => fun p => (p.2 = true : Prop)
  | .fs k => nomatch k
def ft : TypeVec.Arrow uv bv := fun i => match i with | .fz => fun _ => true | .fs k => nomatch k
end
open Classical in
theorem iteA {p q : Prop} (u : Bool) (h : (if p then u else !u) = (if q then true else !true))
    (hp : p) (hq : ¬ q) : u = false := by rw [if_pos hp, if_neg hq] at h; exact h
open Classical in
theorem iteB {p q : Prop} (u : Bool) (h : (if p then u else !u) = (if q then true else !true))
    (hp : ¬ p) (hq : ¬ q) : u = true := by rw [if_neg hp, if_neg hq] at h; cases u <;> simp_all
end W3c3

namespace W3c3
-- non-natural corecursion step for Const 1 Bool: the output records whether the second map is injective
noncomputable def gC : ∀ {X : Type}, (MvQPF.Cofix KB tv0 → X) → (Bool → X) → Bool → KB (tv0 ::: X) :=
  fun {X} _ k' _ => MvQPF.Const.mk (@decide (Function.Injective k') (Classical.propDecidable _))
theorem gC_dest (b : Bool) : MvQPF.Cofix.dest (MvQPF.Cofix.corec₁ (@gC) b) = MvQPF.Const.mk true := by
  rw [MvQPF.Cofix.corec₁, MvQPF.Cofix.dest_corec']
  exact congrArg MvQPF.Const.mk (@decide_eq_true _ (Classical.propDecidable _) Sum.inr_injective)
theorem gC_ni : ¬ Function.Injective (MvQPF.Cofix.corec₁ (@gC)) := fun hi =>
  absurd (hi (MvQPF.Cofix.ext _ _ ((gC_dest true).trans (gC_dest false).symm))) (by decide)
theorem gC_val : (@gC (MvQPF.Cofix KB tv0) id (MvQPF.Cofix.corec₁ (@gC)) true) = MvQPF.Const.mk false :=
  congrArg MvQPF.Const.mk (@decide_eq_false _ (Classical.propDecidable _) gC_ni)
end W3c3

universe u v w

-- `Rat.cast_list_sum` idx 2: necessary (alpha = ZMod 2 (char 2 field), args [2⁻¹, 2⁻¹])
theorem c3_0 : ¬ drop0% Rat.cast_list_sum 2 := fun h => by
  have := @h F2 _ [2⁻¹, 2⁻¹]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil, castF2] at this
  revert this; decide +kernel

-- `Rat.cast_multiset_sum` idx 2: necessary (alpha = ZMod 2 (char 2 field), args (↑([2⁻¹, 2⁻¹] : List ℚ) : Multiset ℚ))
theorem c3_1 : ¬ drop0% Rat.cast_multiset_sum 2 := fun h => by
  have := @h F2 _ (↑([2⁻¹, 2⁻¹] : List ℚ) : Multiset ℚ)
  simp only [Multiset.map_coe, Multiset.sum_coe, Multiset.prod_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil, castF2] at this
  revert this; decide +kernel

-- `Rat.cast_list_prod` idx 2: necessary (alpha = ZMod 2 (char 2 field), args [2⁻¹, 2])
theorem c3_2 : ¬ drop0% Rat.cast_list_prod 2 := fun h => by
  have := @h F2 _ [2⁻¹, 2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil, castF2] at this
  revert this; decide +kernel

-- `Rat.cast_multiset_prod` idx 2: necessary (alpha = ZMod 2 (char 2 field), args (↑([2⁻¹, 2] : List ℚ) : Multiset ℚ))
theorem c3_3 : ¬ drop0% Rat.cast_multiset_prod 2 := fun h => by
  have := @h F2 _ (↑([2⁻¹, 2] : List ℚ) : Multiset ℚ)
  simp only [Multiset.map_coe, Multiset.sum_coe, Multiset.prod_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil, castF2] at this
  revert this; decide +kernel

-- `Rat.cast_injective` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2 0)
theorem c3_4 : ¬ drop0% Rat.cast_injective 2 := fun h => by
  have := @h F2 _ 2 0
  simp only [castF2] at this
  revert this; decide +kernel

-- `Rat.cast_inj` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2 0)
theorem c3_5 : ¬ drop0% Rat.cast_inj 2 := fun h => by
  have := @h F2 _ 2 0
  simp only [castF2] at this
  revert this; decide +kernel

-- `Rat.cast_eq_zero` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2)
theorem c3_6 : ¬ drop0% Rat.cast_eq_zero 2 := fun h => by
  have := @h F2 _ 2
  simp only [castF2] at this
  revert this; decide +kernel

-- `Rat.cast_ne_zero` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2)
theorem c3_7 : ¬ drop0% Rat.cast_ne_zero 2 := fun h => by
  have := @h F2 _ 2
  simp only [castF2] at this
  revert this; decide +kernel

-- `Rat.cast_add` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2⁻¹ 2⁻¹)
theorem c3_8 : ¬ drop0% Rat.cast_add 2 := fun h => by
  have := @h F2 _ 2⁻¹ 2⁻¹
  simp only [castF2] at this
  revert this; decide +kernel

-- `Rat.cast_sub` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 1 2⁻¹)
theorem c3_9 : ¬ drop0% Rat.cast_sub 2 := fun h => by
  have := @h F2 _ 1 2⁻¹
  simp only [castF2] at this
  revert this; decide +kernel

-- `Rat.cast_mul` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2⁻¹ 2)
theorem c3_10 : ¬ drop0% Rat.cast_mul 2 := fun h => by
  have := @h F2 _ 2⁻¹ 2
  simp only [castF2] at this
  revert this; decide +kernel

-- `Rat.coe_castHom` idx 2: necessary (ZMod 2 is a division ring without CharZero)
theorem c3_11 : ¬ indep0% Rat.coe_castHom 2 := fun h => not_cz (@h F2 _)

-- `Rat.cast_inv` idx 2: removable (Rat.cast of inverse commutes in every division ring (by cases on (q.num : α) = 0; cast_inv_of_ne_zero otherwise))
theorem c3_12 : drop% Rat.cast_inv 2 := fun p => rat_cast_inv p

-- `Rat.cast_div` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2 2)
theorem c3_13 : ¬ drop0% Rat.cast_div 2 := fun h => by
  have := @h F2 _ 2 2
  simp only [castF2, f2_div] at this
  revert this; decide +kernel

-- `Rat.cast_zpow` idx 2: removable (holds in every division ring: Rat.cast_pow plus the general cast_inv)
theorem c3_14 : drop% Rat.cast_zpow 2 := fun p n => rat_cast_zpow p n

-- `Rat.cast_divInt` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2 2)
theorem c3_15 : ¬ drop0% Rat.cast_divInt 2 := fun h => by
  have := @h F2 _ 2 2
  simp only [castF2, f2_div] at this
  revert this; decide +kernel

-- `NNRat.cast_injective` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2 0)
theorem c3_16 : ¬ drop0% NNRat.cast_injective 2 := fun h => by
  have := @h F2 _ 2 0
  simp only [ncastF2] at this
  revert this; decide +kernel

-- `NNRat.cast_inj` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2 0)
theorem c3_17 : ¬ drop0% NNRat.cast_inj 2 := fun h => by
  have := @h F2 _ 2 0
  simp only [ncastF2] at this
  revert this; decide +kernel

-- `NNRat.cast_eq_zero` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2)
theorem c3_18 : ¬ drop0% NNRat.cast_eq_zero 2 := fun h => by
  have := @h F2 _ 2
  simp only [ncastF2] at this
  revert this; decide +kernel

-- `NNRat.cast_ne_zero` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2)
theorem c3_19 : ¬ drop0% NNRat.cast_ne_zero 2 := fun h => by
  have := @h F2 _ 2
  simp only [ncastF2] at this
  revert this; decide +kernel

-- `NNRat.cast_add` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2⁻¹ 2⁻¹)
theorem c3_20 : ¬ drop0% NNRat.cast_add 2 := fun h => by
  have := @h F2 _ 2⁻¹ 2⁻¹
  simp only [ncastF2] at this
  revert this; decide +kernel

-- `NNRat.cast_mul` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2⁻¹ 2)
theorem c3_21 : ¬ drop0% NNRat.cast_mul 2 := fun h => by
  have := @h F2 _ 2⁻¹ 2
  simp only [ncastF2] at this
  revert this; decide +kernel

-- `NNRat.coe_castHom` idx 2: necessary (ZMod 2 is a division semiring without CharZero)
theorem c3_22 : ¬ indep0% NNRat.coe_castHom 2 := fun h => not_cz (@h F2 _)

-- `NNRat.cast_inv` idx 2: removable (NNRat.cast of inverse commutes in every division semiring (cases on (q.num : α) = 0))
theorem c3_23 : drop% NNRat.cast_inv 2 := fun p => nnrat_cast_inv p

-- `NNRat.cast_zpow` idx 2: removable (holds in every division semiring: NNRat.cast_pow plus the general cast_inv)
theorem c3_24 : drop% NNRat.cast_zpow 2 := fun p n => nnrat_cast_zpow p n

-- `NNRat.cast_divNat` idx 2: necessary (alpha = ZMod 2 (char 2 field), args 2 2)
theorem c3_25 : ¬ drop0% NNRat.cast_divNat 2 := fun h => by
  have := @h F2 _ 2 2
  simp only [ncastF2, f2_div] at this
  revert this; decide +kernel

-- `NNRat.cast_divNat_of_ne_zero` idx 4: necessary (alpha = ZMod 2 (char 2 field), args 2 2)
theorem c3_26 : ¬ drop0% NNRat.cast_divNat_of_ne_zero 4 := fun h => by
  have := @h F2 _ 2 2
  simp only [ncastF2, f2_div] at this
  revert this; decide +kernel

-- `NNRat.cast_add_of_ne_zero` idx 4: necessary (alpha = ZMod 2 (char 2 field), args 2⁻¹ 1 (by decide +kernel))
theorem c3_27 : ¬ drop0% NNRat.cast_add_of_ne_zero 4 := fun h => by
  have := @h F2 _ 2⁻¹ 1 (by decide +kernel)
  simp only [ncastF2] at this
  revert this; decide +kernel

-- `NNRat.cast_add_of_ne_zero` idx 5: necessary (alpha = ZMod 2 (char 2 field), args 1 2⁻¹ (by decide +kernel))
theorem c3_28 : ¬ drop0% NNRat.cast_add_of_ne_zero 5 := fun h => by
  have := @h F2 _ 1 2⁻¹ (by decide +kernel)
  simp only [ncastF2] at this
  revert this; decide +kernel

-- `NNRat.cast_mul_of_ne_zero` idx 4: necessary (alpha = ZMod 2 (char 2 field), args 2⁻¹ 2 (by decide +kernel))
theorem c3_29 : ¬ drop0% NNRat.cast_mul_of_ne_zero 4 := fun h => by
  have := @h F2 _ 2⁻¹ 2 (by decide +kernel)
  simp only [ncastF2] at this
  revert this; decide +kernel

-- `NNRat.cast_mul_of_ne_zero` idx 5: necessary (alpha = ZMod 2 (char 2 field), args 2 2⁻¹ (by decide +kernel))
theorem c3_30 : ¬ drop0% NNRat.cast_mul_of_ne_zero 5 := fun h => by
  have := @h F2 _ 2 2⁻¹ (by decide +kernel)
  simp only [ncastF2] at this
  revert this; decide +kernel

-- `NNRat.cast_inv_of_ne_zero` idx 3: removable (NNRat.cast commutes with inverse in every division semiring (W3c3.nnrat_cast_inv))
theorem c3_31 : drop% NNRat.cast_inv_of_ne_zero 3 := by intros; exact nnrat_cast_inv _

-- `NNRat.cast_div_of_ne_zero` idx 4: necessary (alpha = ZMod 2 (char 2 field), args 2⁻¹ 2⁻¹ (by decide +kernel))
theorem c3_32 : ¬ drop0% NNRat.cast_div_of_ne_zero 4 := fun h => by
  have := @h F2 _ 2⁻¹ 2⁻¹ (by decide +kernel)
  simp only [ncastF2, f2_div] at this
  revert this; decide +kernel

-- `NNRat.cast_div_of_ne_zero` idx 5: necessary (alpha = ZMod 2 (char 2 field), args 2 2 (by decide +kernel))
theorem c3_33 : ¬ drop0% NNRat.cast_div_of_ne_zero 5 := fun h => by
  have := @h F2 _ 2 2 (by decide +kernel)
  simp only [ncastF2, f2_div] at this
  revert this; decide +kernel

-- `Rat.cast_divInt_of_ne_zero` idx 4: necessary (alpha = ZMod 2 (char 2 field), args 2 2)
theorem c3_34 : ¬ drop0% Rat.cast_divInt_of_ne_zero 4 := fun h => by
  have := @h F2 _ 2 2
  simp only [castF2, f2_div] at this
  revert this; decide +kernel

-- `Rat.cast_mkRat_of_ne_zero` idx 4: necessary (alpha = ZMod 2 (char 2 field), args 2 2)
theorem c3_35 : ¬ drop0% Rat.cast_mkRat_of_ne_zero 4 := fun h => by
  have := @h F2 _ 2 2
  simp only [castF2, f2_div] at this
  revert this; decide +kernel

-- `Rat.cast_add_of_ne_zero` idx 4: necessary (alpha = ZMod 2 (char 2 field), args 2⁻¹ 1 (by decide +kernel))
theorem c3_36 : ¬ drop0% Rat.cast_add_of_ne_zero 4 := fun h => by
  have := @h F2 _ 2⁻¹ 1 (by decide +kernel)
  simp only [castF2] at this
  revert this; decide +kernel

-- `Rat.cast_add_of_ne_zero` idx 5: necessary (alpha = ZMod 2 (char 2 field), args 1 2⁻¹ (by decide +kernel))
theorem c3_37 : ¬ drop0% Rat.cast_add_of_ne_zero 5 := fun h => by
  have := @h F2 _ 1 2⁻¹ (by decide +kernel)
  simp only [castF2] at this
  revert this; decide +kernel

-- `Rat.cast_sub_of_ne_zero` idx 4: necessary (alpha = ZMod 2 (char 2 field), args 2⁻¹ 1 (by decide +kernel))
theorem c3_38 : ¬ drop0% Rat.cast_sub_of_ne_zero 4 := fun h => by
  have := @h F2 _ 2⁻¹ 1 (by decide +kernel)
  simp only [castF2] at this
  revert this; decide +kernel

-- `Rat.cast_sub_of_ne_zero` idx 5: necessary (alpha = ZMod 2 (char 2 field), args 1 2⁻¹ (by decide +kernel))
theorem c3_39 : ¬ drop0% Rat.cast_sub_of_ne_zero 5 := fun h => by
  have := @h F2 _ 1 2⁻¹ (by decide +kernel)
  simp only [castF2] at this
  revert this; decide +kernel

-- `Rat.cast_mul_of_ne_zero` idx 4: necessary (alpha = ZMod 2 (char 2 field), args 2⁻¹ 2 (by decide +kernel))
theorem c3_40 : ¬ drop0% Rat.cast_mul_of_ne_zero 4 := fun h => by
  have := @h F2 _ 2⁻¹ 2 (by decide +kernel)
  simp only [castF2] at this
  revert this; decide +kernel

-- `Rat.cast_mul_of_ne_zero` idx 5: necessary (alpha = ZMod 2 (char 2 field), args 2 2⁻¹ (by decide +kernel))
theorem c3_41 : ¬ drop0% Rat.cast_mul_of_ne_zero 5 := fun h => by
  have := @h F2 _ 2 2⁻¹ (by decide +kernel)
  simp only [castF2] at this
  revert this; decide +kernel

-- `Rat.cast_inv_of_ne_zero` idx 3: removable (Rat.cast commutes with inverse in every division ring (W3c3.rat_cast_inv))
theorem c3_42 : drop% Rat.cast_inv_of_ne_zero 3 := by intros; exact rat_cast_inv _

-- `Rat.cast_div_of_ne_zero` idx 4: necessary (alpha = ZMod 2 (char 2 field), args 2⁻¹ 2⁻¹ (by decide +kernel))
theorem c3_43 : ¬ drop0% Rat.cast_div_of_ne_zero 4 := fun h => by
  have := @h F2 _ 2⁻¹ 2⁻¹ (by decide +kernel)
  simp only [castF2, f2_div] at this
  revert this; decide +kernel

-- `Rat.cast_div_of_ne_zero` idx 5: necessary (alpha = ZMod 2 (char 2 field), args 2 2 (by decide +kernel))
theorem c3_44 : ¬ drop0% Rat.cast_div_of_ne_zero 5 := fun h => by
  have := @h F2 _ 2 2 (by decide +kernel)
  simp only [castF2, f2_div] at this
  revert this; decide +kernel

-- `map_nnratCast` idx 6: necessary (zero map ℚ≥0 → ℚ≥0 as a bare FunLike)
theorem c3_45 : ¬ drop0% map_nnratCast 6 := fun h => absurd (@h (FW ℚ≥0 ℚ≥0) ℚ≥0 ℚ≥0 _ _ _ ⟨fun _ => 0⟩ 1) (by decide +kernel)

-- `eq_nnratCast` idx 4: necessary (zero map as a bare FunLike)
theorem c3_46 : ¬ drop0% eq_nnratCast 4 := fun h => absurd (@h (FW ℚ≥0 ℚ≥0) ℚ≥0 _ _ ⟨fun _ => 0⟩ 1) (by decide +kernel)

-- `map_ratCast` idx 6: necessary (zero map ℚ → ℚ as a bare FunLike)
theorem c3_47 : ¬ drop0% map_ratCast 6 := fun h => absurd (@h (FW ℚ ℚ) ℚ ℚ _ _ _ ⟨fun _ => 0⟩ 1) (by decide +kernel)

-- `eq_ratCast` idx 4: necessary (zero map as a bare FunLike)
theorem c3_48 : ¬ drop0% eq_ratCast 4 := fun h => absurd (@h (FW ℚ ℚ) ℚ _ _ ⟨fun _ => 0⟩ 1) (by decide +kernel)

-- `MonoidWithZeroHomClass.ext_nnrat'` idx 4: necessary (f = id, g x = if x.den = 1 then x else 0 (agree on ℕ, differ at 1/2) as bare FunLikes)
theorem c3_49 : ¬ drop0% MonoidWithZeroHomClass.ext_nnrat' 4 := fun h => fwN_ne (@h (FW ℚ≥0 ℚ≥0) ℚ≥0 _ _ ⟨id⟩ ⟨intPartN⟩ (fun n => (intPartN_nat n).symm))

-- `MonoidWithZeroHomClass.ext_nnrat'` idx 7: necessary (id vs the hom x ↦ (x ≠ 0 ? 1 : 0) on ℚ≥0)
theorem c3_50 : ¬ drop0% MonoidWithZeroHomClass.ext_nnrat' 7 := fun h => nzN_ne (@h (ℚ≥0 →*₀ ℚ≥0) ℚ≥0 _ _ _ (MonoidWithZeroHom.id _) nzN)

-- `MonoidWithZeroHomClass.ext_nnrat` idx 4: necessary (id vs the hom x ↦ (x ≠ 0 ? 1 : 0) on ℚ≥0)
theorem c3_51 : ¬ drop0% MonoidWithZeroHomClass.ext_nnrat 4 := fun h => nzN_ne (@h ℚ≥0 _ (MonoidWithZeroHom.id _) nzN)

-- `MonoidWithZeroHomClass.ext_nnrat_on_pnat` idx 4: necessary (f = id, g x = if x.den = 1 then x else 0 as bare FunLikes)
theorem c3_52 : ¬ drop0% MonoidWithZeroHomClass.ext_nnrat_on_pnat 4 := fun h => fwN_ne (@h (FW ℚ≥0 ℚ≥0) ℚ≥0 _ _ ⟨id⟩ ⟨intPartN⟩ (fun n _ => (intPartN_nat n).symm))

-- `MonoidWithZeroHomClass.ext_nnrat_on_pnat` idx 7: necessary (id vs x ↦ (x ≠ 0 ? 1 : 0))
theorem c3_53 : ¬ drop0% MonoidWithZeroHomClass.ext_nnrat_on_pnat 7 := fun h => nzN_ne (@h (ℚ≥0 →*₀ ℚ≥0) ℚ≥0 _ _ _ (MonoidWithZeroHom.id _) nzN)

-- `MonoidWithZeroHomClass.ext_rat'` idx 4: necessary (f = id, g x = if x.den = 1 then x else 0 as bare FunLikes)
theorem c3_54 : ¬ drop0% MonoidWithZeroHomClass.ext_rat' 4 := fun h => fwQ_ne (@h (FW ℚ ℚ) ℚ _ _ ⟨id⟩ ⟨intPartQ⟩ (fun n => (intPartQ_int n).symm))

-- `MonoidWithZeroHomClass.ext_rat'` idx 7: necessary (id vs x ↦ (x ≠ 0 ? 1 : 0) on ℚ)
theorem c3_55 : ¬ drop0% MonoidWithZeroHomClass.ext_rat' 7 := fun h => nzQ_ne (@h (ℚ →*₀ ℚ) ℚ _ _ _ (MonoidWithZeroHom.id _) nzQ)

-- `MonoidWithZeroHomClass.ext_rat` idx 4: necessary (id vs x ↦ (x ≠ 0 ? 1 : 0) on ℚ)
theorem c3_56 : ¬ drop0% MonoidWithZeroHomClass.ext_rat 4 := fun h => nzQ_ne (@h ℚ _ (MonoidWithZeroHom.id _) nzQ)

-- `MonoidWithZeroHomClass.ext_rat_on_pnat` idx 4: necessary (f = id, g x = if x.den = 1 then x else 0 as bare FunLikes)
theorem c3_57 : ¬ drop0% MonoidWithZeroHomClass.ext_rat_on_pnat 4 := fun h => fwQ_ne (@h (FW ℚ ℚ) ℚ _ _ ⟨id⟩ ⟨intPartQ⟩ (intPartQ_int (-1)).symm (fun n _ => (intPartQ_int n).symm))

-- `MonoidWithZeroHomClass.ext_rat_on_pnat` idx 7: necessary (id vs |·| on ℚ: agree on positive naturals, differ at -1)
theorem c3_58 : ¬ drop0% MonoidWithZeroHomClass.ext_rat_on_pnat 7 := fun h => absQ_ne (@h (ℚ →*₀ ℚ) ℚ _ _ _ (MonoidWithZeroHom.id _) absQ (fun n hn => absQ_nat n))

-- `MonoidWithZeroHomClass.ext_rat_on_pnat` idx 8: necessary (id vs sign x = x/|x| on ℚ: agree at -1, differ at 2)
theorem c3_59 : ¬ drop0% MonoidWithZeroHomClass.ext_rat_on_pnat 8 := fun h => sgnQ_ne (@h (ℚ →*₀ ℚ) ℚ _ _ _ (MonoidWithZeroHom.id _) sgnQ sgnQ_neg1)

-- `RingHom.ext_rat` idx 4: necessary (two different bare FunLike maps ℚ → ℚ)
theorem c3_60 : ¬ drop0% RingHom.ext_rat 4 := fun h => absurd (congrArg (fun f : FW ℚ ℚ => f.toFun 1) (@h (FW ℚ ℚ) ℚ _ _ ⟨id⟩ ⟨fun _ => 0⟩)) (by decide +kernel)

-- `Setoid.ext` idx 3: necessary (discrete vs total setoid on Bool)
theorem c3_61 : ¬ drop1% Setoid.ext 3 := fun h => by
  have := congrArg (fun s : Setoid Bool => s.r true false) (@h Bool (EqS Bool) (TopS Bool))
  exact absurd (cast this.symm trivial : true = false) (by decide)

-- `Quot.induction_on` idx 4: necessary (beta = False)
theorem c3_62 : ¬ drop1% Quot.induction_on 4 := fun h => @h Unit (fun _ _ => True) (fun _ => False) (Quot.mk _ ())

-- `Quot.Subsingleton` idx 2: necessary (Quot of Bool by Eq)
theorem c3_63 : ¬ drop1% Quot.Subsingleton 2 := fun h => absurd (congrArg (Quot.lift id (fun _ _ e => e)) ((@h Bool Eq).elim (Quot.mk _ true) (Quot.mk _ false))) (by decide)

-- `Quot.lift₂_mk` idx 7: necessary (r total on Bool, f a b = a)
theorem c3_64 : ¬ indep1% Quot.lift₂_mk 7 := fun h => by
  have := @h Bool Unit Bool (fun _ _ => True) (fun _ _ => True) (fun a _ => a) (fun _ _ _ _ => rfl) true () true false () trivial
  exact absurd (show true = false from this) (by decide)

-- `Quot.liftOn₂_mk` idx 9: necessary (r total on Bool, f a b = a)
theorem c3_65 : ¬ indep1% Quot.liftOn₂_mk 9 := fun h => by
  have := @h Bool Unit Bool (fun _ _ => True) (fun _ _ => True) true () (fun a _ => a) (fun _ _ _ _ => rfl) true false () trivial
  exact absurd (show true = false from this) (by decide)

-- `Quot.map₂_mk` idx 7: necessary (s total, t = Eq, f a b = b)
theorem c3_66 : ¬ indep1% Quot.map₂_mk 7 := fun h => by
  have := @h Unit Bool Bool (fun _ _ => True) (fun _ _ => True) Eq (fun _ b => b) (fun _ _ _ _ => rfl) () true () true false trivial
  exact absurd (show true = false from this) (by decide)

-- `Quot.induction_on₂` idx 7: necessary (delta = False)
theorem c3_67 : ¬ drop1% Quot.induction_on₂ 7 := fun h => @h Unit Unit (fun _ _ => True) (fun _ _ => True) (fun _ _ => False) (Quot.mk _ ()) (Quot.mk _ ())

-- `Quot.induction_on₃` idx 10: necessary (delta = False)
theorem c3_68 : ¬ drop1% Quot.induction_on₃ 10 := fun h => @h Unit Unit Unit (fun _ _ => True) (fun _ _ => True) (fun _ _ => True) (fun _ _ _ => False) (Quot.mk _ ()) (Quot.mk _ ()) (Quot.mk _ ())

-- `Quotient.instSubsingletonQuotient` idx 2: necessary (discrete setoid on Bool)
theorem c3_69 : ¬ drop1% Quotient.instSubsingletonQuotient 2 := fun h => absurd (show true = false from Quotient.exact ((@h Bool (EqS Bool)).elim (Quotient.mk _ true) (Quotient.mk _ false))) (by decide)

-- `Quotient.map_mk` idx 5: necessary (total setoid to discrete setoid, f = id)
theorem c3_70 : ¬ indep1% Quotient.map_mk 5 := fun h => by
  have := @h Bool Bool (TopS Bool) (EqS Bool) id true true false trivial
  exact absurd (show true = false from this) (by decide)

-- `Quotient.map₂_mk` idx 7: necessary (total setoid to discrete setoid, f a b = a)
theorem c3_71 : ¬ indep1% Quotient.map₂_mk 7 := fun h => by
  have := @h Bool Unit (TopS Bool) (EqS Unit) Bool (EqS Bool) (fun a _ => a) true () true false trivial () () rfl
  exact absurd (show true = false from this) (by decide)

-- `Quotient.lift_mk` idx 4: necessary (total setoid, f = id)
theorem c3_72 : ¬ indep1% Quotient.lift_mk 4 := fun h => by
  have := @h Bool Bool (TopS Bool) id true true false trivial
  exact absurd (show true = false from this) (by decide)

-- `Quotient.lift_comp_mk` idx 4: necessary (total setoid, f = id)
theorem c3_73 : ¬ indep1% Quotient.lift_comp_mk 4 := fun h => by
  have := @h Bool Bool (TopS Bool) id true false trivial
  exact absurd (show true = false from this) (by decide)

-- `Quotient.lift_surjective_iff` idx 4: necessary (total setoid, f = id)
theorem c3_74 : ¬ indep1% Quotient.lift_surjective_iff 4 := fun h => by
  have := @h Bool Bool (TopS Bool) id true false trivial
  exact absurd (show true = false from this) (by decide)

-- `Quotient.lift_surjective` idx 4: necessary (total setoid, f = id)
theorem c3_75 : ¬ indep1% Quotient.lift_surjective 4 := fun h => by
  have := @h Bool Bool (TopS Bool) id Function.surjective_id true false trivial
  exact absurd (show true = false from this) (by decide)

-- `Quotient.lift_surjective` idx 5: necessary (f constant true on Unit)
theorem c3_76 : ¬ drop1% Quotient.lift_surjective 5 := fun h => by
  obtain ⟨x, hx⟩ := @h Unit Bool (EqS Unit) (fun _ => true) (fun _ _ _ => rfl) false
  induction x using Quotient.ind with | _ a
  cases a; exact absurd hx (by decide)

-- `Quotient.lift₂_mk` idx 6: necessary (total setoid on Bool, f a b = a)
theorem c3_77 : ¬ indep1% Quotient.lift₂_mk 6 := fun h => by
  have := @h Bool Unit Bool (TopS Bool) (EqS Unit) (fun a _ => a) true () true () false () trivial rfl
  exact absurd (show true = false from this) (by decide)

-- `Quotient.liftOn_mk` idx 4: necessary (total setoid, f = id)
theorem c3_78 : ¬ indep1% Quotient.liftOn_mk 4 := fun h => by
  have := @h Bool Bool (TopS Bool) id true true false trivial
  exact absurd (show true = false from this) (by decide)

-- `Quotient.liftOn₂_mk` idx 6: necessary (total setoid on Bool, f a b = a)
theorem c3_79 : ¬ indep1% Quotient.liftOn₂_mk 6 := fun h => by
  have := @h Bool Unit Bool (TopS Bool) (EqS Unit) (fun a _ => a) true () true () false () trivial rfl
  exact absurd (show true = false from this) (by decide)

-- `Quot.map_surjective` idx 5: necessary (ra total, rb = Eq, f = id)
theorem c3_80 : ¬ indep1% Quot.map_surjective 5 := fun h => by
  have := @h Bool Bool (fun _ _ => True) Eq id Function.surjective_id true false trivial
  exact absurd (show true = false from this) (by decide)

-- `Quot.map_surjective` idx 6: necessary (f constant true on Unit)
theorem c3_81 : ¬ drop1% Quot.map_surjective 6 := fun h => by
  obtain ⟨x, hx⟩ := @h Unit Bool Eq Eq (fun _ => true) (fun _ _ _ => rfl) (Quot.mk _ false)
  induction x using Quot.ind with | _ a
  cases a; exact absurd (congrArg (Quot.lift id (fun _ _ e => e)) hx) (by decide)

-- `Quotient.map_surjective` idx 5: necessary (total to discrete setoid, f = id)
theorem c3_82 : ¬ indep1% Quotient.map_surjective 5 := fun h => by
  have := @h Bool Bool (TopS Bool) (EqS Bool) id Function.surjective_id true false trivial
  exact absurd (show true = false from this) (by decide)

-- `Quotient.map_surjective` idx 6: necessary (f constant true on Unit)
theorem c3_83 : ¬ drop1% Quotient.map_surjective 6 := fun h => by
  obtain ⟨x, hx⟩ := @h Unit Bool (EqS Unit) (EqS Bool) (fun _ => true) (fun _ _ _ => rfl) (Quotient.mk _ false)
  induction x using Quotient.ind with | _ a
  cases a; exact absurd (congrArg (Quotient.lift (s := EqS Bool) id (fun _ _ e => e)) hx) (by decide)

-- `Quotient.induction_on_pi` idx 5: necessary (p = False)
theorem c3_84 : ¬ drop1% Quotient.induction_on_pi 5 := fun h => @h PUnit (fun _ => Unit) (fun _ => EqS Unit) (fun _ => False) (fun _ => Quotient.mk _ ())

-- `Trunc.ind` idx 2: necessary (beta = False)
theorem c3_85 : ¬ drop1% Trunc.ind 2 := fun h => @h Unit (fun _ => False) (Trunc.mk ())

-- `Trunc.induction_on` idx 3: necessary (beta = False)
theorem c3_86 : ¬ drop1% Trunc.induction_on 3 := fun h => @h Unit (fun _ => False) (Trunc.mk ())

-- `Trunc.induction_on₂` idx 5: necessary (C = False)
theorem c3_87 : ¬ drop1% Trunc.induction_on₂ 5 := fun h => @h Unit Unit (fun _ _ => False) (Trunc.mk ()) (Trunc.mk ())

-- `Quotient.liftOn'_mk''` idx 4: necessary (total setoid, f = id)
theorem c3_88 : ¬ indep1% Quotient.liftOn'_mk'' 4 := fun h => by
  have := @h Bool Bool (TopS Bool) id true true false trivial
  exact absurd (show true = false from this) (by decide)

-- `Quotient.surjective_liftOn'` idx 4: necessary (total setoid, f = id)
theorem c3_89 : ¬ indep1% Quotient.surjective_liftOn' 4 := fun h => by
  have := @h Bool Bool (TopS Bool) id true false trivial
  exact absurd (show true = false from this) (by decide)

-- `Quotient.liftOn₂'_mk''` idx 6: necessary (total setoid on Bool, f a b = a)
theorem c3_90 : ¬ indep1% Quotient.liftOn₂'_mk'' 6 := fun h => by
  have := @h Bool Unit Bool (TopS Bool) (EqS Unit) (fun a _ => a) true () true () false () trivial rfl
  exact absurd (show true = false from this) (by decide)

-- `Quotient.ind'` idx 3: necessary (p = False)
theorem c3_91 : ¬ drop1% Quotient.ind' 3 := fun h => @h Unit (EqS Unit) (fun _ => False) (Quotient.mk'' ())

-- `Quotient.ind₂'` idx 5: necessary (p = False)
theorem c3_92 : ¬ drop1% Quotient.ind₂' 5 := fun h => @h Unit Unit (EqS Unit) (EqS Unit) (fun _ _ => False) (Quotient.mk'' ()) (Quotient.mk'' ())

-- `Quotient.inductionOn'` idx 4: necessary (p = False)
theorem c3_93 : ¬ drop1% Quotient.inductionOn' 4 := fun h => @h Unit (EqS Unit) (fun _ => False) (Quotient.mk'' ())

-- `Quotient.inductionOn₂'` idx 7: necessary (p = False)
theorem c3_94 : ¬ drop1% Quotient.inductionOn₂' 7 := fun h => @h Unit Unit (EqS Unit) (EqS Unit) (fun _ _ => False) (Quotient.mk'' ()) (Quotient.mk'' ())

-- `Quotient.inductionOn₃'` idx 10: necessary (p = False)
theorem c3_95 : ¬ drop1% Quotient.inductionOn₃' 10 := fun h => @h Unit Unit Unit (EqS Unit) (EqS Unit) (EqS Unit) (fun _ _ _ => False) (Quotient.mk'' ()) (Quotient.mk'' ()) (Quotient.mk'' ())

-- `Quotient.hrecOn'_mk''` idx 4: necessary (total setoid, phi = Bool, f = id)
theorem c3_96 : ¬ indep1% Quotient.hrecOn'_mk'' 4 := fun h => absurd (eq_of_heq (@h Bool (TopS Bool) (fun _ => Bool) id true true false trivial)) (by decide)

-- `Quotient.hrecOn₂'_mk''` idx 6: necessary (total setoid, phi = Bool, f a b = a)
theorem c3_97 : ¬ indep1% Quotient.hrecOn₂'_mk'' 6 := fun h => absurd (eq_of_heq (@h Bool Unit (TopS Bool) (EqS Unit) (fun _ _ => Bool) (fun a _ => a) true (Quotient.mk'' ()) true () false () trivial rfl)) (by decide)

-- `Quotient.map'_mk''` idx 5: necessary (total to discrete setoid, f = id)
theorem c3_98 : ¬ indep1% Quotient.map'_mk'' 5 := fun h => by
  have := @h Bool Bool (TopS Bool) (EqS Bool) id true true false trivial
  exact absurd (show true = false from this) (by decide)

-- `Quotient.map₂'_mk''` idx 7: necessary (total to discrete setoid, f a b = a)
theorem c3_99 : ¬ indep1% Quotient.map₂'_mk'' 7 := fun h => by
  have := @h Bool Unit Bool (TopS Bool) (EqS Unit) (EqS Bool) (fun a _ => a) true true false trivial () () rfl
  exact absurd (show true = false from this) (by decide)

-- `Quotient.exact'` idx 4: necessary (discrete setoid on Bool)
theorem c3_100 : ¬ drop1% Quotient.exact' 4 := fun h => absurd (show true = false from @h Bool (EqS Bool) true false) (by decide)

-- `Quotient.sound'` idx 4: necessary (discrete setoid on Bool)
theorem c3_101 : ¬ drop1% Quotient.sound' 4 := fun h => absurd (show true = false from Quotient.exact (@h Bool (EqS Bool) true false)) (by decide)

-- `Quotient.liftOn'_mk` idx 5: necessary (total setoid, f = id)
theorem c3_102 : ¬ indep1% Quotient.liftOn'_mk 5 := fun h => by
  have := @h Bool Bool (TopS Bool) true id true false trivial
  exact absurd (show true = false from this) (by decide)

-- `Quotient.liftOn₂'_mk` idx 6: necessary (total setoid on Bool, f a b = a)
theorem c3_103 : ¬ indep1% Quotient.liftOn₂'_mk 6 := fun h => by
  have := @h Bool Unit Bool (TopS Bool) (EqS Unit) (fun a _ => a) true () true () false () trivial rfl
  exact absurd (show true = false from this) (by decide)

-- `Quotient.map'_mk` idx 5: necessary (total to discrete setoid, f = id)
theorem c3_104 : ¬ indep1% Quotient.map'_mk 5 := fun h => by
  have := @h Bool Bool (TopS Bool) (EqS Bool) id true true false trivial
  exact absurd (show true = false from this) (by decide)

-- `Prod.fst_surjective` idx 2: necessary (beta empty)
theorem c3_105 : ¬ drop0% Prod.fst_surjective 2 := fun h => by
  obtain ⟨⟨_, e⟩, _⟩ := @h Unit Empty ()
  exact e.elim

-- `Prod.snd_surjective` idx 2: necessary (alpha empty)
theorem c3_106 : ¬ drop0% Prod.snd_surjective 2 := fun h => by
  obtain ⟨⟨e, _⟩, _⟩ := @h Empty Unit ()
  exact e.elim

-- `Function.Surjective.prodMap` idx 6: necessary (f constant true)
theorem c3_107 : ¬ drop0% Function.Surjective.prodMap 6 := fun h => by
  obtain ⟨⟨a, b⟩, hx⟩ := @h Unit Unit Bool Unit (fun _ => true) id Function.surjective_id (false, ())
  exact absurd (congrArg Prod.fst hx) (by simp)

-- `Function.Surjective.prodMap` idx 7: necessary (g constant true)
theorem c3_108 : ¬ drop0% Function.Surjective.prodMap 7 := fun h => by
  obtain ⟨⟨a, b⟩, hx⟩ := @h Unit Unit Unit Bool id (fun _ => true) Function.surjective_id ((), false)
  exact absurd (congrArg Prod.snd hx) (by simp)

-- `Function.Bijective.prodMap` idx 6: necessary (f constant true)
theorem c3_109 : ¬ drop0% Function.Bijective.prodMap 6 := fun h => by
  obtain ⟨⟨a, b⟩, hx⟩ := (@h Unit Unit Bool Unit (fun _ => true) id Function.bijective_id).2 (false, ())
  exact absurd (congrArg Prod.fst hx) (by simp)

-- `Function.Bijective.prodMap` idx 7: necessary (g constant true)
theorem c3_110 : ¬ drop0% Function.Bijective.prodMap 7 := fun h => by
  obtain ⟨⟨a, b⟩, hx⟩ := (@h Unit Unit Unit Bool id (fun _ => true) Function.bijective_id).2 ((), false)
  exact absurd (congrArg Prod.snd hx) (by simp)

-- `Function.LeftInverse.prodMap` idx 8: necessary (f1 constant true on Unit, f2 to Unit)
theorem c3_111 : ¬ drop0% Function.LeftInverse.prodMap 8 := fun h => absurd (congrArg Prod.fst (@h Unit Bool Unit Unit (fun _ => true) id (fun _ => ()) id (fun _ => rfl) (false, ()))) (by simp)

-- `Function.LeftInverse.prodMap` idx 9: necessary (g1 constant true on Unit)
theorem c3_112 : ¬ drop0% Function.LeftInverse.prodMap 9 := fun h => absurd (congrArg Prod.snd (@h Unit Unit Unit Bool id (fun _ => true) id (fun _ => ()) (fun _ => rfl) ((), false))) (by simp)

-- `Function.RightInverse.prodMap` idx 8: necessary (f2 constant true)
theorem c3_113 : ¬ drop0% Function.RightInverse.prodMap 8 := fun h => absurd (congrArg Prod.fst (@h Bool Unit Unit Unit (fun _ => ()) id (fun _ => true) id (fun _ => rfl) (false, ()))) (by simp)

-- `Function.RightInverse.prodMap` idx 9: necessary (g2 constant true)
theorem c3_114 : ¬ drop0% Function.RightInverse.prodMap 9 := fun h => absurd (congrArg Prod.snd (@h Unit Unit Bool Unit id (fun _ => ()) id (fun _ => true) (fun _ => rfl) ((), false))) (by simp)

-- `Function.Involutive.prodMap` idx 4: necessary (f constant true on Bool)
theorem c3_115 : ¬ drop0% Function.Involutive.prodMap 4 := fun h => absurd (congrArg Prod.fst (@h Bool Unit (fun _ => true) id (fun _ => rfl) (false, ()))) (by simp)

-- `Function.Involutive.prodMap` idx 5: necessary (g constant true on Bool)
theorem c3_116 : ¬ drop0% Function.Involutive.prodMap 5 := fun h => absurd (congrArg Prod.snd (@h Unit Bool id (fun _ => true) (fun _ => rfl) ((), false))) (by simp)

-- `Prod.map_injective` idx 4: necessary (alpha empty, g constant)
theorem c3_117 : ¬ drop0% Prod.map_injective 4 := fun h => by
  have hi := (( @h Empty Bool Unit Unit _ Empty.elim (fun _ => ())).1 (fun x _ _ => x.1.elim)).2
  exact absurd (@hi true false rfl) (by decide)

-- `Prod.map_injective` idx 5: necessary (beta empty, f constant)
theorem c3_118 : ¬ drop0% Prod.map_injective 5 := fun h => by
  have hi := (( @h Bool Empty Unit Unit _ (fun _ => ()) Empty.elim).1 (fun x _ _ => x.2.elim)).1
  exact absurd (@hi true false rfl) (by decide)

-- `Prod.map_surjective` idx 4: necessary (gamma (and alpha) empty, g constant true)
theorem c3_119 : ¬ drop0% Prod.map_surjective 4 := fun h => by
  obtain ⟨b, hb⟩ := ((@h Empty Unit Empty Bool _ id (fun _ => true)).1 (fun y => y.1.elim)).2 false
  cases b; exact absurd hb (by decide)

-- `Prod.map_surjective` idx 5: necessary (delta (and beta) empty, f constant true)
theorem c3_120 : ¬ drop0% Prod.map_surjective 5 := fun h => by
  obtain ⟨b, hb⟩ := ((@h Unit Empty Bool Empty _ (fun _ => true) id).1 (fun y => y.2.elim)).1 false
  cases b; exact absurd hb (by decide)

-- `Prod.map_bijective` idx 4: necessary (alpha = gamma empty, g constant)
theorem c3_121 : ¬ drop0% Prod.map_bijective 4 := fun h => by
  have hi := ((@h Empty Bool Empty Bool _ id (fun _ => true)).1 ⟨fun x _ _ => x.1.elim, fun y => y.1.elim⟩).2.1
  exact absurd (@hi true false rfl) (by decide)

-- `Prod.map_bijective` idx 5: necessary (beta = delta empty, f constant)
theorem c3_122 : ¬ drop0% Prod.map_bijective 5 := fun h => by
  have hi := ((@h Bool Empty Bool Empty _ (fun _ => true) id).1 ⟨fun x _ _ => x.2.elim, fun y => y.2.elim⟩).1.1
  exact absurd (@hi true false rfl) (by decide)

-- `Prod.map_leftInverse` idx 4: necessary (beta empty, g1 constant true)
theorem c3_123 : ¬ drop0% Prod.map_leftInverse 4 := fun h => absurd (((@h Empty Empty Unit Bool _ id (fun _ => true) id (fun _ => ())).1 (fun x => x.1.elim)).2 false) (by decide)

-- `Prod.map_leftInverse` idx 5: necessary (delta empty, f1 constant true)
theorem c3_124 : ¬ drop0% Prod.map_leftInverse 5 := fun h => absurd (((@h Unit Bool Empty Empty _ (fun _ => true) id (fun _ => ()) id).1 (fun x => x.2.elim)).1 false) (by decide)

-- `Prod.map_rightInverse` idx 4: necessary (alpha empty, g2 constant true)
theorem c3_125 : ¬ drop0% Prod.map_rightInverse 4 := fun h => absurd (((@h Empty Empty Bool Unit _ id (fun _ => ()) id (fun _ => true)).1 (fun x => x.1.elim)).2 false) (by decide)

-- `Prod.map_rightInverse` idx 5: necessary (gamma empty, f2 constant true)
theorem c3_126 : ¬ drop0% Prod.map_rightInverse 5 := fun h => absurd (((@h Bool Unit Empty Empty _ (fun _ => ()) id (fun _ => true) id).1 (fun x => x.2.elim)).1 false) (by decide)

-- `Prod.map_involutive` idx 2: necessary (alpha empty, g constant true)
theorem c3_127 : ¬ drop0% Prod.map_involutive 2 := fun h => absurd (((@h Empty Bool _ id (fun _ => true)).1 (fun x => x.1.elim)).2 false) (by decide)

-- `Prod.map_involutive` idx 3: necessary (beta empty, f constant true)
theorem c3_128 : ¬ drop0% Prod.map_involutive 3 := fun h => absurd (((@h Bool Empty _ (fun _ => true) id).1 (fun x => x.2.elim)).1 false) (by decide)

-- `Function.Injective.pprod_map` idx 6: necessary (f constant)
theorem c3_129 : ¬ drop1% Function.Injective.pprod_map 6 := fun h => absurd (congrArg PProd.fst (@h Bool Unit Unit Unit (fun _ => ()) id (fun _ _ e => e) ⟨true, ()⟩ ⟨false, ()⟩ rfl)) (by decide)

-- `Function.Injective.pprod_map` idx 7: necessary (g constant)
theorem c3_130 : ¬ drop1% Function.Injective.pprod_map 7 := fun h => absurd (congrArg PProd.snd (@h Unit Unit Bool Unit id (fun _ => ()) (fun _ _ e => e) ⟨(), true⟩ ⟨(), false⟩ rfl)) (by decide)

-- `List.TProd.elim_of_ne` idx 6: necessary (i = true, j = false, l = [])
theorem c3_131 : ¬ indep0% List.TProd.elim_of_ne 6 := fun h => absurd (@h Bool (fun _ => Unit) true false [] _ (by decide) ((), PUnit.unit)) (by decide)

-- `List.TProd.elim_of_ne` idx 7: necessary (i = j)
theorem c3_132 : ¬ indep0% List.TProd.elim_of_ne 7 := fun h => @h Bool (fun _ => Unit) true true [] _ List.mem_cons_self ((), PUnit.unit) rfl

-- `List.TProd.elim_of_mem` idx 6: necessary (l = [i] (i repeated), v = (true, false))
theorem c3_133 : ¬ drop0% List.TProd.elim_of_mem 6 := fun h => absurd (@h Bool (fun _ => Bool) true true [true] _ (List.mem_singleton_self _) (true, false, PUnit.unit)) (by decide +kernel)

-- `List.TProd.elim_of_mem` idx 7: necessary (l = [])
theorem c3_134 : ¬ indep0% List.TProd.elim_of_mem 7 := fun h => List.not_mem_nil (@h Bool (fun _ => Unit) true true [] _ (by simp) ((), PUnit.unit))

-- `List.TProd.elim_mk` idx 6: necessary (l = [])
theorem c3_135 : ¬ indep0% List.TProd.elim_mk 6 := fun h => List.not_mem_nil (@h Unit (fun _ => Unit) _ [] (fun _ => ()) ())

-- `List.TProd.ext_iff` idx 4: necessary (l = [(), ()], v = (true, false), w = (true, true))
theorem c3_136 : ¬ drop0% List.TProd.ext_iff 4 := fun h => absurd (congrArg (fun v => v.2.1) ((@h Unit (fun _ => Bool) _ [(), ()] (true, false, PUnit.unit) (true, true, PUnit.unit)).2 (fun i hi => by cases i; rfl))) (by decide)

-- `List.TProd.ext` idx 4: necessary (l = [(), ()], v = (true, false), w = (true, true))
theorem c3_137 : ¬ drop0% List.TProd.ext 4 := fun h => absurd (congrArg (fun v => v.2.1) (@h Unit (fun _ => Bool) _ [(), ()] (true, false, PUnit.unit) (true, true, PUnit.unit) (fun i hi => by cases i; rfl))) (by decide)

-- `List.TProd.ext` idx 7: necessary (l = [()], v ≠ w)
theorem c3_138 : ¬ drop0% List.TProd.ext 7 := fun h => absurd (congrArg Prod.fst (@h Unit (fun _ => Bool) _ [()] (List.nodup_singleton _) (true, PUnit.unit) (false, PUnit.unit))) (by decide)

-- `List.TProd.mk_elim` idx 4: necessary (l = [(), ()], v = (true, false))
theorem c3_139 : ¬ drop0% List.TProd.mk_elim 4 := fun h => absurd (congrArg (fun v => v.2.1) (@h Unit (fun _ => Bool) [(), ()] _ (fun _ => by simp) (true, false, PUnit.unit))) (by decide +kernel)

-- `List.TProd.mk_elim` idx 5: necessary (l = [])
theorem c3_140 : ¬ indep0% List.TProd.mk_elim 5 := fun h => List.not_mem_nil (@h Unit (fun _ => Unit) [] _ List.nodup_nil PUnit.unit ())

-- `Set.elim_preimage_pi` idx 4: necessary (l = [(), ()], t = {true}, v = (true, false))
theorem c3_141 : ¬ drop0% Set.elim_preimage_pi 4 := fun h => by
  have e := @h Unit (fun _ => Bool) _ [(), ()] (fun _ => by simp) (fun _ => {true})
  have h1 : ((true, false, PUnit.unit) : List.TProd (fun _ : Unit => Bool) [(), ()]) ∈ Set.tprod [(), ()] (fun _ => ({true} : Set Bool)) := by
    rw [← e]; intro i _; cases i; rfl
  exact absurd h1.2.1 (by simp)

-- `Set.elim_preimage_pi` idx 5: necessary (l = [])
theorem c3_142 : ¬ indep0% Set.elim_preimage_pi 5 := fun h => List.not_mem_nil (@h Unit (fun _ => Unit) _ [] List.nodup_nil (fun _ => Set.univ) ())

-- `_private.Mathlib.Data.QPF.Univariate.Basic.0.QPF.Cofix.bisim_aux` idx 3: removable (with h' dropped the statement is exactly QPF.Cofix.bisim_rel)
theorem c3_143 : drop% _private.Mathlib.Data.QPF.Univariate.Basic.«0».QPF.Cofix.bisim_aux 3 := fun r h => QPF.Cofix.bisim_rel r h

-- `_private.Mathlib.Data.QPF.Univariate.Basic.0.QPF.Cofix.bisim_aux` idx 4: necessary (constant Bool QPF, r total)
theorem c3_144 : ¬ drop0% _private.Mathlib.Data.QPF.Univariate.Basic.«0».QPF.Cofix.bisim_aux 4 := fun h => cc_ne (@h CB.Obj qCB (fun _ _ => True) (fun _ => trivial) (cc true) (cc false) trivial)

-- `_private.Mathlib.Data.QPF.Univariate.Basic.0.QPF.Cofix.bisim_aux` idx 7: necessary (constant Bool QPF, r = Eq)
theorem c3_145 : ¬ drop0% _private.Mathlib.Data.QPF.Univariate.Basic.«0».QPF.Cofix.bisim_aux 7 := fun h => cc_ne (@h CB.Obj qCB Eq (fun _ => rfl) (fun x y e => by rw [e]) (cc true) (cc false))

-- `QPF.lawfulFunctor` idx 2: necessary (QPF whose mapConst flips the shape)
theorem c3_146 : ¬ drop0% QPF.lawfulFunctor 2 := fun h => by
  have L := @h SF qSF
  have := congrFun (congrFun (@LawfulFunctor.map_const SF _ L Unit Unit) ()) (⟨true, fun _ => ()⟩ : SF Unit)
  exact absurd (show (false : Bool) = true from congrArg Sigma.fst this) (by decide)

-- `QPF.recF_eq_of_Wequiv` idx 6: necessary (constant Bool QPF, u = shape)
theorem c3_147 : ¬ drop0% QPF.recF_eq_of_Wequiv 6 := fun h => absurd ((wb_rec true).symm.trans ((@h CB.Obj qCB Bool (fun x => x.1) (wb true) (wb false)).trans (wb_rec false))) (by decide)

-- `QPF.Wequiv.abs'` idx 4: necessary (constant Bool QPF: W elements with different shapes)
theorem c3_148 : ¬ drop0% QPF.Wequiv.abs' 4 := fun h => absurd ((wb_rec true).symm.trans ((QPF.recF_eq_of_Wequiv (fun x => x.1) _ _ (@h CB.Obj qCB (wb true) (wb false))).trans (wb_rec false))) (by decide)

-- `QPF.Wequiv.symm` idx 4: necessary (constant Bool QPF: W elements with different shapes)
theorem c3_149 : ¬ drop0% QPF.Wequiv.symm 4 := fun h => absurd ((wb_rec true).symm.trans ((QPF.recF_eq_of_Wequiv (fun x => x.1) _ _ (@h CB.Obj qCB (wb false) (wb true))).trans (wb_rec false))) (by decide)

-- `QPF.Fix.ind_rec` idx 5: necessary (constant Bool QPF, Fix nonempty)
theorem c3_150 : ¬ drop0% QPF.Fix.ind_rec 5 := fun h => absurd (@h CB.Obj qCB Bool (fun _ => true) (fun _ => false) fx) (by decide)

-- `QPF.Fix.rec_unique` idx 5: necessary (constant Bool QPF: two different h)
theorem c3_151 : ¬ drop0% QPF.Fix.rec_unique 5 := fun h => absurd (congrFun ((@h CB.Obj qCB Bool (fun _ => true) (fun _ => true)).symm.trans (@h CB.Obj qCB Bool (fun _ => true) (fun _ => false))) fx) (by decide)

-- `QPF.Fix.ind` idx 3: necessary (p = False on a nonempty Fix)
theorem c3_152 : ¬ drop0% QPF.Fix.ind 3 := fun h => @h CB.Obj qCB (fun _ => False) fx

-- `QPF.Cofix.bisim_rel` idx 3: necessary (r total)
theorem c3_153 : ¬ drop0% QPF.Cofix.bisim_rel 3 := fun h => cc_ne (@h CB.Obj qCB (fun _ _ => True) (cc true) (cc false) trivial)

-- `QPF.Cofix.bisim_rel` idx 6: necessary (r empty)
theorem c3_154 : ¬ drop0% QPF.Cofix.bisim_rel 6 := fun h => cc_ne (@h CB.Obj qCB (fun _ _ => False) (fun _ _ e => e.elim) (cc true) (cc false))

-- `QPF.Cofix.bisim` idx 3: necessary (r total)
theorem c3_155 : ¬ drop0% QPF.Cofix.bisim 3 := fun h => cc_ne (@h CB.Obj qCB (fun _ _ => True) (cc true) (cc false) trivial)

-- `QPF.Cofix.bisim` idx 6: necessary (r empty)
theorem c3_156 : ¬ drop0% QPF.Cofix.bisim 6 := fun h => cc_ne (@h CB.Obj qCB (fun _ _ => False) (fun _ _ e => e.elim) (cc true) (cc false))

-- `QPF.Cofix.bisim'` idx 6: necessary (Q total, u v constant different)
theorem c3_157 : ¬ drop0% QPF.Cofix.bisim' 6 := fun h => cc_ne (@h CB.Obj qCB Unit (fun _ => True) (fun _ => cc true) (fun _ => cc false) () trivial)

-- `QPF.Cofix.bisim'` idx 8: necessary (Q empty)
theorem c3_158 : ¬ drop0% QPF.Cofix.bisim' 8 := fun h => cc_ne (@h CB.Obj qCB Unit (fun _ => False) (fun _ => cc true) (fun _ => cc false) (fun _ e => e.elim) ())

-- `QPF.supp_eq_of_isUniform` idx 2: necessary (non-uniform QPF PLift (Nonempty α))
theorem c3_159 : ¬ drop0% QPF.supp_eq_of_isUniform 2 := fun h => by
  have e := @h NE qNE Bool () (fun _ => true)
  have : true ∈ Functor.supp (QPF.abs (PFunctor.Obj.mk (P := qNE.P) () (fun _ => true))) := by rw [e]; exact ⟨(), trivial, rfl⟩
  exact ne_supp true _ this

-- `QPF.liftp_iff_of_isUniform` idx 2: necessary (non-uniform QPF PLift (Nonempty α), p = False)
theorem c3_160 : ¬ drop0% QPF.liftp_iff_of_isUniform 2 := fun h => by
  obtain ⟨⟨⟨⟨_, hf⟩⟩⟩, _⟩ := (@h NE qNE Bool neT (fun _ => False)).2 (fun u hu => ne_supp u _ hu)
  exact hf

-- `QPF.supp_map` idx 2: necessary (non-uniform QPF PLift (Nonempty α), g constant)
theorem c3_161 : ¬ drop0% QPF.supp_map 2 := fun h => by
  have e := @h NE qNE Bool Unit (fun _ => ()) neT
  have h1 : () ∈ Functor.supp ((fun _ : Bool => ()) <$> neT) := by
    rw [QPF.mem_supp]; intro a f _; exact ⟨(), trivial, rfl⟩
  rw [e] at h1
  obtain ⟨b, hb, _⟩ := h1
  exact ne_supp b _ hb

-- `_private.Mathlib.Data.QPF.Multivariate.Constructions.Cofix.0.MvQPF.Cofix.bisim_aux` idx 6: necessary (Const 1 Bool, r total)
theorem c3_162 : ¬ drop0% _private.Mathlib.Data.QPF.Multivariate.Constructions.Cofix.«0».MvQPF.Cofix.bisim_aux 6 := fun h => mc_ne (@h 0 KB _ tv0 (fun _ _ => True) (fun _ => trivial) (mc true) (mc false) trivial)

-- `_private.Mathlib.Data.QPF.Multivariate.Constructions.Cofix.0.MvQPF.Cofix.bisim_aux` idx 9: necessary (Const 1 Bool, r = Eq)
theorem c3_163 : ¬ drop0% _private.Mathlib.Data.QPF.Multivariate.Constructions.Cofix.«0».MvQPF.Cofix.bisim_aux 9 := fun h => mc_ne (@h 0 KB _ tv0 Eq (fun _ => rfl) (fun x y e => by rw [e]) (mc true) (mc false))

-- `MvQPF.Cofix.bisim_rel` idx 5: necessary (Const 1 Bool, r total)
theorem c3_164 : ¬ drop0% MvQPF.Cofix.bisim_rel 5 := fun h => mc_ne (@h 0 KB _ tv0 (fun _ _ => True) (mc true) (mc false) trivial)

-- `MvQPF.Cofix.bisim_rel` idx 8: necessary (Const 1 Bool, r empty)
theorem c3_165 : ¬ drop0% MvQPF.Cofix.bisim_rel 8 := fun h => mc_ne (@h 0 KB _ tv0 (fun _ _ => False) (fun _ _ e => e.elim) (mc true) (mc false))

-- `MvQPF.Cofix.bisim` idx 5: necessary (Const 1 Bool, r total)
theorem c3_166 : ¬ drop0% MvQPF.Cofix.bisim 5 := fun h => mc_ne (@h 0 KB _ tv0 (fun _ _ => True) (mc true) (mc false) trivial)

-- `MvQPF.Cofix.bisim` idx 8: necessary (Const 1 Bool, r empty)
theorem c3_167 : ¬ drop0% MvQPF.Cofix.bisim 8 := fun h => mc_ne (@h 0 KB _ tv0 (fun _ _ => False) (fun _ _ e => e.elim) (mc true) (mc false))

-- `MvQPF.Cofix.bisim₂` idx 5: necessary (Const 1 Bool, r total)
theorem c3_168 : ¬ drop0% MvQPF.Cofix.bisim₂ 5 := fun h => mc_ne (@h 0 KB _ tv0 (fun _ _ => True) (mc true) (mc false) trivial)

-- `MvQPF.Cofix.bisim₂` idx 8: necessary (Const 1 Bool, r empty)
theorem c3_169 : ¬ drop0% MvQPF.Cofix.bisim₂ 8 := fun h => mc_ne (@h 0 KB _ tv0 (fun _ _ => False) (fun _ _ e => e.elim) (mc true) (mc false))

-- `MvQPF.Cofix.bisim'` idx 8: necessary (Q total, u v constant different)
theorem c3_170 : ¬ drop0% MvQPF.Cofix.bisim' 8 := fun h => mc_ne (@h 0 KB _ tv0 Unit (fun _ => True) (fun _ => mc true) (fun _ => mc false) () trivial)

-- `MvQPF.Cofix.bisim'` idx 10: necessary (Q empty)
theorem c3_171 : ¬ drop0% MvQPF.Cofix.bisim' 10 := fun h => mc_ne (@h 0 KB _ tv0 Unit (fun _ => False) (fun _ => mc true) (fun _ => mc false) (fun _ e => e.elim) ())

-- `MvQPF.Cofix.ext` idx 6: necessary (two different Cofix points of Const 1 Bool)
theorem c3_172 : ¬ drop0% MvQPF.Cofix.ext 6 := fun h => mc_ne (@h 0 KB _ tv0 (mc true) (mc false))

-- `MvQPF.Cofix.ext_mk` idx 6: necessary (Const 1 Bool)
theorem c3_173 : ¬ drop0% MvQPF.Cofix.ext_mk 6 := fun h => absurd (show (true : Bool) = false from @h 0 KB _ tv0 (MvQPF.Const.mk true) (MvQPF.Const.mk false)) (by decide)

-- `MvQPF.Fix.ind_rec` idx 7: necessary (Const 1 Bool, Fix nonempty)
theorem c3_174 : ¬ drop0% MvQPF.Fix.ind_rec 7 := fun h => absurd (@h 0 KB _ tv0 Bool (fun _ => true) (fun _ => false) mfx) (by decide)

-- `MvQPF.Fix.rec_unique` idx 7: necessary (Const 1 Bool: two different h)
theorem c3_175 : ¬ drop0% MvQPF.Fix.rec_unique 7 := fun h => absurd (congrFun ((@h 0 KB _ tv0 Bool (fun _ => true) (fun _ => true)).symm.trans (@h 0 KB _ tv0 Bool (fun _ => true) (fun _ => false))) mfx) (by decide)

-- `MvQPF.Fix.ind` idx 5: necessary (p = False on a nonempty Fix)
theorem c3_176 : ¬ drop0% MvQPF.Fix.ind 5 := fun h => @h 0 KB _ tv0 (fun _ => False) mfx

-- `MvQPF.recF_eq_of_wEquiv` idx 8: necessary (Const 1 Bool, u = get)
theorem c3_177 : ¬ drop0% MvQPF.recF_eq_of_wEquiv 8 := fun h => absurd ((mw_rec true).symm.trans ((@h 0 KB _ tv0 Bool getC (mw true) (mw false)).trans (mw_rec false))) (by decide)

-- `MvQPF.wEquiv.abs'` idx 6: necessary (Const 1 Bool: W points of different shape)
theorem c3_178 : ¬ drop0% MvQPF.wEquiv.abs' 6 := fun h => mw_ne (@h 0 KB _ tv0 (mw true) (mw false))

-- `MvQPF.wEquiv.symm` idx 6: necessary (Const 1 Bool: W points of different shape)
theorem c3_179 : ¬ drop0% MvQPF.wEquiv.symm 6 := fun h => mw_ne (@h 0 KB _ tv0 (mw false) (mw true))

-- `MvQPF.wEquiv_map` idx 8: necessary (Const 1 Bool, g = id)
theorem c3_180 : ¬ drop0% MvQPF.wEquiv_map 8 := fun h => absurd ((mwm_rec true).symm.trans ((MvQPF.recF_eq_of_wEquiv tv0 getC _ _ (@h 0 KB _ tv0 tv0 TypeVec.id (mw true) (mw false))).trans (mwm_rec false))) (by decide)

-- `MvQPF.supp_eq_of_isUniform` idx 3: necessary (non-uniform MvQPF PLift (Nonempty (α 0)))
theorem c3_181 : ¬ drop0% MvQPF.supp_eq_of_isUniform 3 := fun h => by
  have e := @h 1 MNE qMNE bv () (fun _ _ => true) Fin2.fz
  exact mne_supp true _ ((Set.ext_iff.1 e true).2 ⟨(), trivial, rfl⟩)

-- `MvQPF.liftP_iff_of_isUniform` idx 3: necessary (non-uniform MvQPF PLift (Nonempty (α 0)), p = False)
theorem c3_182 : ¬ drop0% MvQPF.liftP_iff_of_isUniform 3 := fun h => by
  obtain ⟨⟨⟨⟨_, hf⟩⟩⟩, _⟩ := (@h 1 MNE qMNE bv mneT (fun _ _ => False)).2 (fun i => match i with | .fz => fun u hu => mne_supp u _ hu | .fs k => nomatch k)
  exact hf

-- `MvQPF.supp_map` idx 3: necessary (non-uniform MvQPF PLift (Nonempty (α 0)), g constant)
theorem c3_183 : ¬ drop0% MvQPF.supp_map 3 := fun h => by
  have e := @h 1 MNE qMNE bv (fun _ => Unit) (fun _ _ => ()) mneT Fin2.fz
  have h1 : () ∈ MvFunctor.supp (MvFunctor.map (fun _ _ => ()) mneT : MNE (fun _ => Unit)) Fin2.fz := by
    refine (MvQPF.mem_supp _ _ _).2 ?_; intro a f _; exact ⟨(), trivial, rfl⟩
  rw [e] at h1
  obtain ⟨b, hb, _⟩ := h1
  exact mne_supp b _ hb

-- `MvQPF.liftR_map_last'` idx 8: necessary (projection functor Prj 0, R = Eq, f = not)
theorem c3_184 : ¬ drop0% MvQPF.liftR_map_last' 8 := fun h => by
  obtain ⟨u, h1, h2⟩ := @h 0 (MvQPF.Prj Fin2.fz) _ tv0 Bool Eq (show Bool from true) not
  have hu := u.2
  change u.1.1 = u.1.2 at hu
  change u.1.1 = false at h1
  change u.1.2 = true at h2
  rw [h1, h2] at hu
  exact absurd (show (false : Bool) = true from hu) (by decide)

-- `MvQPF.liftR_map_last` idx 11: necessary (projection functor Prj 0, R = Eq, f = id, g = not)
theorem c3_185 : ¬ drop0% MvQPF.liftR_map_last 11 := fun h => by
  obtain ⟨u, h1, h2⟩ := @h 0 (MvQPF.Prj Fin2.fz) _ _ tv0 Bool Bool Eq (show Bool from true) id not
  have hu := u.2
  change u.1.1 = u.1.2 at hu
  change u.1.1 = true at h1
  change u.1.2 = false at h2
  rw [h1, h2] at hu
  exact absurd (show (true : Bool) = false from hu) (by decide)

-- `MvQPF.liftR_map` idx 11: necessary (projection functor Prj 0, R = diagonal, f = id, g = not)
theorem c3_186 : ¬ drop0% MvQPF.liftR_map 11 := fun h => by
  obtain ⟨u, h1, h2⟩ := @h 1 bv bv (MvQPF.Prj Fin2.fz) _ _ RD (show Bool from true) TypeVec.id
    (fun i => match i with | .fz => not | .fs k => nomatch k)
    (fun i => match i with | .fz => fun b => ⟨(b, b), rfl⟩ | .fs k => nomatch k)
  have hu := u.2
  change u.1.1 = u.1.2 at hu
  change u.1.1 = true at h1
  change u.1.2 = false at h2
  rw [h1, h2] at hu
  exact absurd (show (true : Bool) = false from hu) (by decide)

-- `MvQPF.liftR_map` idx 5: necessary (unlawful MvFunctor WK (value Bool, map flips unless the component is surjective), R = (p.2 = true), f = g constant true on Unit)
theorem c3_187 : ¬ drop0% MvQPF.liftR_map 5 := fun h => by
  obtain ⟨u, h1, h2⟩ := @h 1 uv bv WK _ R2 (show WK uv from true) ft ft
    (fun i => match i with | .fz => fun _ => ⟨(true, true), rfl⟩ | .fs k => nomatch k)
    (by funext i u; match i with | .fz => rfl)
  dsimp only [MvFunctor.map] at h1 h2
  have s1 : ¬ Function.Surjective (ft Fin2.fz) := fun hs => by
    obtain ⟨w, e⟩ := hs false; cases w; exact absurd (show true = false from e) (by decide)
  have e1 := iteA u h1 (fun b => ⟨⟨(b, true), rfl⟩, rfl⟩) s1
  have e2 := iteB u h2 (fun c => by
    obtain ⟨⟨⟨a, b⟩, hp⟩, e⟩ := c false
    change b = true at hp; change b = false at e; rw [hp] at e; exact absurd e (by decide)) s1
  exact absurd (e1.symm.trans e2) (by decide)

-- `MvQPF.Cofix.dest_corec₁` idx 7: necessary (Const 1 Bool with a non-natural step g (output = whether the second map is injective))
theorem c3_188 : ¬ drop0% MvQPF.Cofix.dest_corec₁ 7 := fun h => by
  have e := @h 0 KB _ tv0 Bool (@gC) true
  rw [gC_dest, gC_val] at e
  exact absurd (show (true : Bool) = false from e) (by decide)
