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
namespace W3c4
def RQ := ℚ
instance : Field RQ := inferInstanceAs (Field ℚ)
instance : LinearOrder RQ := inferInstanceAs (LinearOrder ℚᵒᵈ)
theorem RQ_not : ¬ IsStrictOrderedRing RQ := fun h => by
  have := h.toZeroLEOneClass.zero_le_one; change (1:ℚ) ≤ 0 at this; norm_num at this
/-- swap 1/2 ↔ 3/2 and -1/2 ↔ -3/2 (fixes every integer) -/
def ψ (x : ℚ) : ℚ := if x = 1/2 then 3/2 else if x = 3/2 then 1/2 else
  if x = -1/2 then -3/2 else if x = -3/2 then -1/2 else x
theorem ψψ (x : ℚ) : ψ (ψ x) = x := by
  by_cases h1 : x = 1/2; · subst h1; norm_num [ψ]
  by_cases h2 : x = 3/2; · subst h2; norm_num [ψ]
  by_cases h3 : x = -1/2; · subst h3; norm_num [ψ]
  by_cases h4 : x = -3/2; · subst h4; norm_num [ψ]
  have : ψ x = x := by simp only [ψ, h1, h2, h3, h4, ite_false]
  rw [this, this]
theorem ψ_inj : Function.Injective ψ := fun a b h => by rw [← ψψ a, h, ψψ]
theorem ψ_int (n : ℤ) : ψ (n : ℚ) = n := by
  unfold ψ
  split_ifs with h1 h2 h3 h4
  · have := congrArg (· * 2) h1; norm_num at this; norm_cast at this; omega
  · have := congrArg (· * 2) h2; norm_num at this; norm_cast at this; omega
  · have := congrArg (· * 2) h3; norm_num at this; norm_cast at this; omega
  · have := congrArg (· * 2) h4; norm_num at this; norm_cast at this; omega
  · rfl
/-- ℚ with the field structure of ℚ and the order pulled back along ψ: a linear order with a
lawful `FloorRing` that is not a strict ordered ring (floor of 3/2 is 0) -/
def P := ℚ
instance : Field P := inferInstanceAs (Field ℚ)
instance : LinearOrder P := LinearOrder.lift' (fun x : P => ψ x) ψ_inj
instance : DecidableLE P := fun a b => inferInstanceAs (Decidable (ψ a ≤ ψ b))
instance : DecidableLT P := fun a b => inferInstanceAs (Decidable (ψ a < ψ b))
instance : FloorRing P where
  floor x := ⌊ψ x⌋
  ceil x := ⌈ψ x⌉
  gc_coe_floor z a := by
    show (ψ (z : ℚ)) ≤ ψ a ↔ z ≤ ⌊ψ a⌋
    rw [ψ_int, Int.le_floor]
  gc_ceil_coe a z := by
    show ⌈ψ a⌉ ≤ z ↔ ψ a ≤ ψ (z : ℚ)
    rw [ψ_int, Int.ceil_le]
theorem nnr32 : Mathlib.Meta.NormNum.IsNNRat (3/2 : P) 3 2 :=
  ⟨invertibleOfNonzero (show ((2:ℕ):ℚ) ≠ 0 by norm_num), by
    rw [invOf_eq_inv]; change (3/2:ℚ) = ((3:ℕ):ℚ) * ((2:ℕ):ℚ)⁻¹; norm_num⟩
theorem rat32 : Mathlib.Meta.NormNum.IsRat (3/2 : P) 3 2 :=
  ⟨invertibleOfNonzero (show ((2:ℕ):ℚ) ≠ 0 by norm_num), by
    rw [invOf_eq_inv]; change (3/2:ℚ) = ((3:ℤ):ℚ) * ((2:ℕ):ℚ)⁻¹; norm_num⟩
theorem ratm32 : Mathlib.Meta.NormNum.IsRat (-3/2 : P) (Int.negOfNat 3) 2 :=
  ⟨invertibleOfNonzero (show ((2:ℕ):ℚ) ≠ 0 by norm_num), by
    rw [invOf_eq_inv]; change (-3/2:ℚ) = ((Int.negOfNat 3:ℤ):ℚ) * ((2:ℕ):ℚ)⁻¹; norm_num⟩
theorem no_inv0 {α : Type*} [Ring α] [Nontrivial α] (i : Invertible ((0:ℕ):α)) : False := by
  have h1 : ((0:ℕ):α) * ⅟((0:ℕ):α) = 1 := mul_invOf_self _
  simp at h1
theorem rat11 : Mathlib.Meta.NormNum.IsRat (1 : ℚ) 1 1 :=
  ⟨invertibleOfNonzero (show ((1:ℕ):ℚ) ≠ 0 by norm_num), by rw [invOf_eq_inv]; norm_num⟩
end W3c4
open W3c4

namespace W3c4
open Computation in
theorem pne {a b : ℕ} (h : a ≠ b) : (Computation.pure a : Computation ℕ) ≠ Computation.pure b := fun e => by
  have := congrArg destruct e; simp [destruct_pure] at this; exact h this
open Computation in
theorem ene (a : ℕ) : empty ℕ ≠ Computation.pure a := fun e => by
  have := congrArg destruct e; simp [destruct_pure, destruct_empty] at this
open Computation in
theorem npe {a b : ℕ} (h : a ≠ b) : ¬ a ∈ (Computation.pure b : Computation ℕ) := fun m => h (eq_of_pure_mem m)
theorem ne_equiv {a b : ℕ} (h : a ≠ b) : ¬ Computation.Equiv (Computation.pure a : Computation ℕ) (Computation.pure b) := fun e =>
  npe h ((e a).1 (Computation.ret_mem a))
theorem bot_pure : ¬ Computation.LiftRel (fun _ _ : ℕ => False) (Computation.pure 0) (Computation.pure 0) := fun e =>
  (Computation.liftRel_pure _ _ _).1 e
end W3c4

-- `Computation.destruct_eq_pure` idx 3: necessary (s = empty, a = 0)
theorem c4_201 : ¬ drop0% Computation.destruct_eq_pure 3 := fun h => ene 0 (h (s := Computation.empty ℕ) (a := 0))
-- `Computation.destruct_eq_think` idx 3: necessary (s = s' = pure 0)
theorem c4_202 : ¬ drop0% Computation.destruct_eq_think 3 := fun h => by
  have := congrArg Computation.destruct (h (s := (Computation.pure 0 : Computation ℕ)) (s' := Computation.pure 0))
  simp [Computation.destruct_pure, Computation.destruct_think] at this
-- `Computation.eq_of_bisim` idx 2: necessary (R = ⊤, pure 0, pure 1)
theorem c4_203 : ¬ drop0% Computation.eq_of_bisim 2 := fun h =>
  pne (show (0:ℕ) ≠ 1 by decide) (h (fun _ _ => True) (s₁ := Computation.pure 0) (s₂ := Computation.pure 1) trivial)
-- `Computation.eq_of_bisim` idx 5: necessary (R = ⊥ is a bisimulation, pure 0, pure 1)
theorem c4_204 : ¬ drop0% Computation.eq_of_bisim 5 := fun h =>
  pne (show (0:ℕ) ≠ 1 by decide) (h (fun _ _ => False) (fun _ _ f => f.elim) (s₁ := Computation.pure 0) (s₂ := Computation.pure 1))
-- `Computation.le_stable` idx 5: necessary (s = think (pure 0), m = 1, n = 0)
theorem c4_205 : ¬ drop0% Computation.le_stable 5 := fun h => by
  have := h (Computation.think (Computation.pure 0)) (a := 0) (m := 1) (n := 0) rfl
  exact absurd this (by decide)
-- `Computation.think_mem` idx 3: necessary (s = empty)
theorem c4_206 : ¬ drop0% Computation.think_mem 3 := fun h =>
  Computation.notMem_empty 0 (Computation.of_think_mem (h (s := Computation.empty ℕ) (a := 0)))
-- `Computation.think_terminates` idx 2: necessary (s = empty)
theorem c4_207 : ¬ drop0% Computation.think_terminates 2 := fun h => by
  have := h (Computation.empty ℕ); rw [← Computation.think_empty] at this
  exact Computation.not_terminates_empty this
-- `Computation.eq_empty_of_not_terminates` idx 2: necessary (s = pure 0)
theorem c4_208 : ¬ drop0% Computation.eq_empty_of_not_terminates 2 := fun h =>
  ene 0 (h (s := (Computation.pure 0 : Computation ℕ))).symm
-- `Computation.mem_promises` idx 3: necessary (s = pure 0, a = 1)
theorem c4_209 : ¬ drop0% Computation.mem_promises 3 := fun h => by
  have := h (s := (Computation.pure 0 : Computation ℕ)) (a := 1) (Computation.ret_mem 0); exact absurd this (by decide)
-- `Computation.mem_of_promises` idx 2: necessary (s = empty promises everything)
theorem c4_210 : ¬ drop0% Computation.mem_of_promises 2 := fun h =>
  Computation.notMem_empty 0 (h (Computation.empty ℕ) (a := 0) (fun _ m => (Computation.notMem_empty _ m).elim))
-- `Computation.get_eq_of_promises` idx 2: necessary (dependent; s = empty promises 0 but does not terminate)
theorem c4_211 : ¬ indep0% Computation.get_eq_of_promises 2 := fun h =>
  Computation.not_terminates_empty (h (Computation.empty ℕ) (a := 0) (fun _ m => (Computation.notMem_empty _ m).elim))
-- `Computation.Results.val_unique` idx 6: necessary (s = pure 0, a = 1, b = 0)
theorem c4_212 : ¬ drop0% Computation.Results.val_unique 6 := fun h => by
  have := h (s := (Computation.pure 0 : Computation ℕ)) (a := 1) (b := 0) (m := 0) (Computation.results_pure 0)
  exact absurd this (by decide)
-- `Computation.Results.val_unique` idx 7: necessary (s = pure 0, a = 0, b = 1)
theorem c4_213 : ¬ drop0% Computation.Results.val_unique 7 := fun h => by
  have := h (s := (Computation.pure 0 : Computation ℕ)) (a := 0) (b := 1) (n := 0) (Computation.results_pure 0)
  exact absurd this (by decide)
-- `Computation.Results.len_unique` idx 6: necessary (s = pure 0, m = 1, n = 0)
theorem c4_214 : ¬ drop0% Computation.Results.len_unique 6 := fun h => by
  have := h (s := (Computation.pure 0 : Computation ℕ)) (a := 0) (m := 1) (Computation.results_pure 0)
  exact absurd this (by decide)
-- `Computation.Results.len_unique` idx 7: necessary (s = pure 0, m = 0, n = 1)
theorem c4_215 : ¬ drop0% Computation.Results.len_unique 7 := fun h => by
  have := h (s := (Computation.pure 0 : Computation ℕ)) (b := 0) (n := 1) (Computation.results_pure 0)
  exact absurd this (by decide)
-- `Computation.results_think` idx 4: necessary (s = empty)
theorem c4_216 : ¬ drop0% Computation.results_think 4 := fun h =>
  Computation.notMem_empty 0 (Computation.results_think_iff.1 (h (s := Computation.empty ℕ) (a := 0) (n := 0))).mem
-- `Computation.eq_thinkN` idx 4: necessary (s = empty, n = 0)
theorem c4_217 : ¬ drop0% Computation.eq_thinkN 4 := fun h => ene 0 (h (s := Computation.empty ℕ) (a := 0) (n := 0))
-- `Computation.results_bind` idx 8: necessary (s = pure 1, f = pure, a = b = 0)
theorem c4_218 : ¬ drop0% Computation.results_bind 8 := fun h => by
  have := h (s := (Computation.pure 1 : Computation ℕ)) (f := Computation.pure) (a := 0) (m := 0) (Computation.results_pure 0)
  rw [Computation.ret_bind] at this; exact npe (by decide) this.mem
-- `Computation.results_bind` idx 9: necessary (s = pure 0, f = pure, b = 1)
theorem c4_219 : ¬ drop0% Computation.results_bind 9 := fun h => by
  have := h (s := (Computation.pure 0 : Computation ℕ)) (f := Computation.pure) (b := 1) (n := 0) (Computation.results_pure 0)
  rw [Computation.ret_bind] at this; exact npe (by decide) this.mem
-- `Computation.terminates_bind` idx 5: necessary (s = pure 0, f = fun _ => empty)
theorem c4_220 : ¬ drop0% Computation.terminates_bind 5 := fun h => by
  have := h (Computation.pure 0 : Computation ℕ) (fun _ => Computation.empty ℕ)
  rw [Computation.ret_bind] at this; exact Computation.not_terminates_empty this
-- `Computation.bind_promises` idx 6: necessary (s = pure 1, f = pure, a = b = 0)
theorem c4_221 : ¬ drop0% Computation.bind_promises 6 := fun h => by
  have := h (s := (Computation.pure 1 : Computation ℕ)) (f := Computation.pure) (a := 0) (b := 0) (fun _ m => (Computation.eq_of_pure_mem m).symm)
  rw [Computation.ret_bind] at this; exact absurd (this (Computation.ret_mem 1)) (by decide)
-- `Computation.bind_promises` idx 7: necessary (s = pure 0, f = pure, b = 1)
theorem c4_222 : ¬ drop0% Computation.bind_promises 7 := fun h => by
  have := h (s := (Computation.pure 0 : Computation ℕ)) (f := Computation.pure) (a := 0) (b := 1) (fun _ m => (Computation.eq_of_pure_mem m).symm)
  rw [Computation.ret_bind] at this; exact absurd (this (Computation.ret_mem 0)) (by decide)
-- `Computation.Equiv.symm` idx 3: necessary (pure 0, pure 1)
theorem c4_223 : ¬ drop0% Computation.Equiv.symm 3 := fun h =>
  ne_equiv (show (0:ℕ) ≠ 1 by decide) (h (t := Computation.pure 0) (s := Computation.pure 1))
-- `Computation.Equiv.trans` idx 4: necessary (s = pure 1, t = u = pure 0)
theorem c4_224 : ¬ drop0% Computation.Equiv.trans 4 := fun h =>
  ne_equiv (show (1:ℕ) ≠ 0 by decide) (h (s := Computation.pure 1) (t := Computation.pure 0) (u := Computation.pure 0) (Computation.Equiv.refl _))
-- `Computation.Equiv.trans` idx 5: necessary (s = t = pure 0, u = pure 1)
theorem c4_225 : ¬ drop0% Computation.Equiv.trans 5 := fun h =>
  ne_equiv (show (0:ℕ) ≠ 1 by decide) (h (s := Computation.pure 0) (t := Computation.pure 0) (u := Computation.pure 1) (Computation.Equiv.refl _))
-- `Computation.equiv_of_mem` idx 4: necessary (s = pure 1, t = pure 0, a = 0)
theorem c4_226 : ¬ drop0% Computation.equiv_of_mem 4 := fun h =>
  ne_equiv (show (1:ℕ) ≠ 0 by decide) (h (s := Computation.pure 1) (t := Computation.pure 0) (a := 0) (Computation.ret_mem 0))
-- `Computation.equiv_of_mem` idx 5: necessary (s = pure 0, t = pure 1, a = 0)
theorem c4_227 : ¬ drop0% Computation.equiv_of_mem 5 := fun h =>
  ne_equiv (show (0:ℕ) ≠ 1 by decide) (h (s := Computation.pure 0) (t := Computation.pure 1) (a := 0) (Computation.ret_mem 0))
-- `Computation.terminates_congr` idx 3: necessary (pure 0, empty)
theorem c4_228 : ¬ drop0% Computation.terminates_congr 3 := fun h =>
  Computation.not_terminates_empty ((h (c₁ := (Computation.pure 0 : Computation ℕ)) (c₂ := Computation.empty ℕ)).1 inferInstance)
-- `Computation.promises_congr` idx 3: necessary (pure 0, pure 1, a = 0)
theorem c4_229 : ¬ drop0% Computation.promises_congr 3 := fun h => by
  have := (h (c₁ := (Computation.pure 0 : Computation ℕ)) (c₂ := Computation.pure 1) 0).1 (fun _ m => (Computation.eq_of_pure_mem m).symm)
  exact absurd (this (Computation.ret_mem 1)) (by decide)
-- `Computation.get_equiv` idx 3: necessary (pure 0, pure 1)
theorem c4_230 : ¬ drop0% Computation.get_equiv 3 := fun h => by
  have := h (c₁ := (Computation.pure 0 : Computation ℕ)) (c₂ := Computation.pure 1); simp at this
-- `Computation.bind_congr` idx 6: necessary (s1 = pure 0, s2 = pure 1, f1 = f2 = pure)
theorem c4_231 : ¬ drop0% Computation.bind_congr 6 := fun h => by
  have := h (s1 := (Computation.pure 0 : Computation ℕ)) (s2 := Computation.pure 1) (f1 := Computation.pure) (f2 := Computation.pure) (fun _ => Computation.Equiv.refl _)
  rw [Computation.ret_bind, Computation.ret_bind] at this; exact ne_equiv (by decide) this
-- `Computation.equiv_pure_of_mem` idx 3: necessary (s = pure 1, a = 0)
theorem c4_232 : ¬ drop0% Computation.equiv_pure_of_mem 3 := fun h =>
  ne_equiv (show (1:ℕ) ≠ 0 by decide) (h (s := Computation.pure 1) (a := 0))
-- `Computation.LiftRel.refl` idx 2: necessary (R = ⊥)
theorem c4_233 : ¬ drop0% Computation.LiftRel.refl 2 := fun h =>
  bot_pure ((h (fun _ _ : ℕ => False)).refl (Computation.pure 0))
-- `Computation.LiftRel.symm` idx 2: necessary (R = <, pure 0, pure 1)
theorem c4_234 : ¬ drop0% Computation.LiftRel.symm 2 := fun h => by
  have := (h (fun a b : ℕ => a < b)).symm (Computation.pure 0) (Computation.pure 1) ((Computation.liftRel_pure _ _ _).2 (by decide))
  exact absurd ((Computation.liftRel_pure _ _ _).1 this) (by decide)
-- `Computation.LiftRel.trans` idx 2: necessary (R = ≠, pure 0, pure 1, pure 0)
theorem c4_235 : ¬ drop0% Computation.LiftRel.trans 2 := fun h => by
  have := (h (fun a b : ℕ => a ≠ b)).trans (Computation.pure 0) (Computation.pure 1) (Computation.pure 0)
    ((Computation.liftRel_pure _ _ _).2 (by decide)) ((Computation.liftRel_pure _ _ _).2 (by decide))
  exact absurd ((Computation.liftRel_pure _ _ _).1 this) (by decide)
-- `Computation.LiftRel.equiv` idx 2: necessary (R = ⊥)
theorem c4_236 : ¬ drop0% Computation.LiftRel.equiv 2 := fun h =>
  bot_pure ((h (fun _ _ : ℕ => False)).refl (Computation.pure 0))
-- `Computation.terminates_of_liftRel` idx 5: necessary (s = pure 0, t = empty)
theorem c4_237 : ¬ drop0% Computation.terminates_of_liftRel 5 := fun h =>
  Computation.not_terminates_empty ((h (R := fun _ _ : ℕ => True) (s := Computation.pure 0) (t := Computation.empty ℕ)).1 inferInstance)
-- `Computation.rel_of_liftRel` idx 9: necessary (R = Eq, pure 0, a = 0, b = 1)
theorem c4_238 : ¬ drop0% Computation.rel_of_liftRel 9 := fun h => by
  have := h (R := fun a b : ℕ => a = b) (ca := Computation.pure 0) (cb := Computation.pure 0) ((Computation.liftRel_pure _ _ _).2 rfl)
    (a := 0) (b := 1) (Computation.ret_mem 0)
  exact absurd this (by decide)
-- `Computation.liftRel_of_mem` idx 7: necessary (ca = empty, cb = pure 0, R = ⊤)
theorem c4_239 : ¬ drop0% Computation.liftRel_of_mem 7 := fun h => by
  have := h (R := fun _ _ : ℕ => True) (a := 0) (b := 0) (ca := Computation.empty ℕ) (cb := Computation.pure 0) (Computation.ret_mem 0) trivial
  obtain ⟨a, ha, -⟩ := (Computation.liftRel_pure_right _ _ _).1 this
  exact Computation.notMem_empty a ha
-- `Computation.exists_of_liftRel_left` idx 7: necessary (R = Eq, pure 0, a = 1)
theorem c4_240 : ¬ drop0% Computation.exists_of_liftRel_left 7 := fun h => by
  obtain ⟨b, hb, e⟩ := h (R := fun a b : ℕ => a = b) (ca := Computation.pure 0) (cb := Computation.pure 0) ((Computation.liftRel_pure _ _ _).2 rfl) (a := 1)
  rw [Computation.eq_of_pure_mem hb] at e; exact absurd e (by decide)
-- `Computation.exists_of_liftRel_right` idx 7: necessary (R = Eq, pure 0, b = 1)
theorem c4_241 : ¬ drop0% Computation.exists_of_liftRel_right 7 := fun h => by
  obtain ⟨a, ha, e⟩ := h (R := fun a b : ℕ => a = b) (ca := Computation.pure 0) (cb := Computation.pure 0) ((Computation.liftRel_pure _ _ _).2 rfl) (b := 1)
  rw [Computation.eq_of_pure_mem ha] at e; exact absurd e (by decide)
-- `Computation.liftRel_bind` idx 11: necessary (R = S = Eq, pure 0, f1 = pure 0, f2 = pure 1)
theorem c4_242 : ¬ drop0% Computation.liftRel_bind 11 := fun h => by
  have := h (fun a b : ℕ => a = b) (fun a b : ℕ => a = b) (s1 := Computation.pure 0) (s2 := Computation.pure 0)
    (f1 := fun _ => Computation.pure 0) (f2 := fun _ => Computation.pure 1) ((Computation.liftRel_pure _ _ _).2 rfl)
  rw [Computation.ret_bind, Computation.ret_bind] at this
  exact absurd ((Computation.liftRel_pure _ _ _).1 this) (by decide)
-- `Computation.liftRel_mem_cases` idx 5: necessary (ca = pure 0, cb = empty)
theorem c4_243 : ¬ drop0% Computation.liftRel_mem_cases 5 := fun h => by
  have := h (R := fun _ _ : ℕ => True) (ca := Computation.pure 0) (cb := Computation.empty ℕ) (fun b m => (Computation.notMem_empty b m).elim)
  obtain ⟨b, hb, -⟩ := (Computation.liftRel_pure_left _ _ _).1 this
  exact Computation.notMem_empty b hb
-- `Computation.liftRel_mem_cases` idx 6: necessary (ca = empty, cb = pure 0)
theorem c4_244 : ¬ drop0% Computation.liftRel_mem_cases 6 := fun h => by
  have := h (R := fun _ _ : ℕ => True) (ca := Computation.empty ℕ) (cb := Computation.pure 0) (fun b m => (Computation.notMem_empty b m).elim)
  obtain ⟨a, ha, -⟩ := (Computation.liftRel_pure_right _ _ _).1 this
  exact Computation.notMem_empty a ha
-- `Computation.liftRel_congr` idx 7: necessary (R = Eq, ca = pure 0, ca' = pure 1, cb = cb' = pure 0)
theorem c4_245 : ¬ drop0% Computation.liftRel_congr 7 := fun h => by
  have := (h (R := fun a b : ℕ => a = b) (ca := Computation.pure 0) (ca' := Computation.pure 1) (cb := Computation.pure 0) (cb' := Computation.pure 0)
    (Computation.Equiv.refl _)).1 ((Computation.liftRel_pure _ _ _).2 rfl)
  exact absurd ((Computation.liftRel_pure _ _ _).1 this) (by decide)
-- `Computation.liftRel_congr` idx 8: necessary (R = Eq, ca = ca' = pure 0, cb = pure 0, cb' = pure 1)
theorem c4_246 : ¬ drop0% Computation.liftRel_congr 8 := fun h => by
  have := (h (R := fun a b : ℕ => a = b) (ca := Computation.pure 0) (ca' := Computation.pure 0) (cb := Computation.pure 0) (cb' := Computation.pure 1)
    (Computation.Equiv.refl _)).1 ((Computation.liftRel_pure _ _ _).2 rfl)
  exact absurd ((Computation.liftRel_pure _ _ _).1 this) (by decide)
-- `Computation.liftRel_map` idx 11: necessary (R = S = Eq, pure 0, f1 = 0, f2 = 1)
theorem c4_247 : ¬ drop0% Computation.liftRel_map 11 := fun h => by
  have := h (fun a b : ℕ => a = b) (fun a b : ℕ => a = b) (s1 := Computation.pure 0) (s2 := Computation.pure 0)
    (f1 := fun _ => 0) (f2 := fun _ => 1) ((Computation.liftRel_pure _ _ _).2 rfl)
  rw [Computation.map_pure, Computation.map_pure] at this
  exact absurd ((Computation.liftRel_pure _ _ _).1 this) (by decide)
-- `Computation.map_congr` idx 5: necessary (f = id, pure 0, pure 1)
theorem c4_248 : ¬ drop0% Computation.map_congr 5 := fun h => by
  have := h (s1 := (Computation.pure 0 : Computation ℕ)) (s2 := Computation.pure 1) (f := id)
  rw [Computation.map_pure, Computation.map_pure] at this; exact ne_equiv (by decide) this
-- `Computation.LiftRelRec.lem` idx 4: necessary (C = ⊤, R = ⊥, pure 0)
theorem c4_249 : ¬ drop0% Computation.LiftRelRec.lem 4 := fun h =>
  bot_pure (h (R := fun _ _ : ℕ => False) (fun _ _ => True) (Computation.pure 0) (Computation.pure 0) trivial 0 (Computation.ret_mem 0))
-- `Computation.LiftRelRec.lem` idx 7: necessary (C = ⊥, R = ⊥, pure 0)
theorem c4_250 : ¬ drop0% Computation.LiftRelRec.lem 7 := fun h =>
  bot_pure (h (R := fun _ _ : ℕ => False) (fun _ _ => False) (fun f => f.elim) (Computation.pure 0) (Computation.pure 0) 0 (Computation.ret_mem 0))
-- `Computation.liftRel_rec` idx 4: necessary (C = ⊤, R = ⊥, pure 0)
theorem c4_251 : ¬ drop0% Computation.liftRel_rec 4 := fun h =>
  bot_pure (h (R := fun _ _ : ℕ => False) (fun _ _ => True) (Computation.pure 0) (Computation.pure 0) trivial)
-- `Computation.liftRel_rec` idx 7: necessary (C = ⊥, R = ⊥, pure 0)
theorem c4_252 : ¬ drop0% Computation.liftRel_rec 7 := fun h =>
  bot_pure (h (R := fun _ _ : ℕ => False) (fun _ _ => False) (fun f => f.elim) (Computation.pure 0) (Computation.pure 0))
-- `Computation.LiftRelRec.lem` idx 9: removable (the weakened statement is `Computation.liftRel_rec` with an unused binder)
theorem c4_253 : drop% Computation.LiftRelRec.lem 9 := by
  intro α β R C H ca cb Hc a; exact Computation.liftRel_rec C H ca cb Hc
-- `Computation.Results.length` idx 4: removable (dependent, derivable: results imply termination)
theorem c4_254 : indep% Computation.Results.length 4 := by
  intro α s a n h; exact Computation.terminates_of_mem h.mem
-- `Computation.get_equiv` idx 4: removable (dependent, derivable from the equivalence and the other termination)
theorem c4_255 : indep% Computation.get_equiv 4 := by
  intro α c₁ c₂ h _; exact (Computation.terminates_congr h).2 inferInstance
-- `Computation.get_equiv` idx 5: removable (dependent, derivable from the equivalence and the other termination)
theorem c4_256 : indep% Computation.get_equiv 5 := by
  intro α c₁ c₂ h _; exact (Computation.terminates_congr h).1 inferInstance

namespace W3c4
/-- Semiquot Bool with both values -/
def sqU : Semiquot Bool := Semiquot.mk (a := true) (s := Set.univ) trivial
theorem sqU_not_pure : ¬ sqU.IsPure := fun h => absurd (h true (Set.mem_univ _) false (Set.mem_univ _)) (by decide)
/-- the constant infinite sequence 0, 0, … -/
def zs : Stream'.Seq ℕ := Stream'.Seq.ofStream (fun _ => 0)
theorem zs_nt : ¬ zs.Terminates := Stream'.Seq.not_terminates_iff.2 (fun n => rfl)
theorem pw_head {R : ℕ → ℕ → Prop} {a b : ℕ} {t : Stream'.Seq ℕ} (h : ¬ R a b) :
    ¬ Stream'.Seq.Pairwise R (.cons a (.cons b t)) := fun p => h (Stream'.Seq.Pairwise_cons_cons_head p)
theorem pw_tail {R : ℕ → ℕ → Prop} {a b c : ℕ} {t : Stream'.Seq ℕ} (h : ¬ R b c) :
    ¬ Stream'.Seq.Pairwise R (.cons a (.cons b (.cons c t))) := fun p => pw_head h (Stream'.Seq.Pairwise.cons_elim p).2
theorem pw10 : Stream'.Seq.Pairwise (fun a b : ℕ => a ≠ b) (.cons 1 (.cons 0 .nil)) :=
  Stream'.Seq.Pairwise.cons (fun x hx => by
    rcases Stream'.Seq.mem_cons_iff.1 hx with rfl | hx
    · decide
    · exact (Stream'.Seq.notMem_nil _ hx).elim) Stream'.Seq.Pairwise_cons_nil
theorem not_pw010 : ¬ Stream'.Seq.Pairwise (fun a b : ℕ => a ≠ b) (.cons 0 (.cons 1 (.cons 0 .nil))) := fun p =>
  p 0 2 (by decide) 0 rfl 0 rfl rfl
end W3c4

-- `Semiquot.eq_mk_of_mem` idx 3: necessary (dependent; q = pure true, a = false)
theorem c4_301 : ¬ indep0% Semiquot.eq_mk_of_mem 3 := fun h =>
  absurd (Semiquot.mem_pure.1 (h (q := Semiquot.pure true) (a := false))) (by decide)
-- `Semiquot.blur_eq_blur'` idx 3: necessary (dependent; q = pure true, s = ∅)
theorem c4_302 : ¬ indep0% Semiquot.blur_eq_blur' 3 := fun h =>
  h (Semiquot.pure true) ∅ (Semiquot.mem_pure_self true)
-- `Semiquot.mem_blur'` idx 3: necessary (dependent; q = pure true, s = ∅)
theorem c4_303 : ¬ indep0% Semiquot.mem_blur' 3 := fun h =>
  h (Semiquot.pure true) (s := ∅) (a := true) (Semiquot.mem_pure_self true)
-- `Semiquot.liftOn_ofMem` idx 4: necessary (dependent; q = {true, false}, f = id)
theorem c4_304 : ¬ indep0% Semiquot.liftOn_ofMem 4 := fun h =>
  absurd (h sqU id true (Set.mem_univ _) true (Set.mem_univ _) false (Set.mem_univ _)) (by decide)
-- `Semiquot.get_mem` idx 2: necessary (dependent; q = {true, false} is not pure)
theorem c4_305 : ¬ indep0% Semiquot.get_mem 2 := fun h => sqU_not_pure (h (q := sqU))
-- `Semiquot.eq_pure` idx 2: necessary (dependent; q = {true, false} is not pure)
theorem c4_306 : ¬ indep0% Semiquot.eq_pure 2 := fun h => sqU_not_pure (h (q := sqU))
-- `Semiquot.IsPure.mono` idx 3: necessary (s = {true, false}, t = pure true)
theorem c4_307 : ¬ drop0% Semiquot.IsPure.mono 3 := fun h =>
  sqU_not_pure (h (s := sqU) (t := Semiquot.pure true) (Semiquot.pure_isPure true))
-- `Semiquot.IsPure.mono` idx 4: necessary (s = t = {true, false})
theorem c4_308 : ¬ drop0% Semiquot.IsPure.mono 4 := fun h => sqU_not_pure (h (s := sqU) (t := sqU) le_rfl)
-- `Semiquot.IsPure.min` idx 3: necessary (s = pure true, t = {true, false})
theorem c4_309 : ¬ drop0% Semiquot.IsPure.min 3 := fun h => by
  have e := (h (s := Semiquot.pure true) (t := sqU)).1 (Semiquot.pure_le.2 (Set.mem_univ _))
  have : false ∈ Semiquot.pure true := e ▸ (Set.mem_univ false : false ∈ (Set.univ : Set Bool))
  exact absurd (Semiquot.mem_pure.1 this) (by decide)
-- `Semiquot.isPure_of_subsingleton` idx 1: necessary (q = {true, false})
theorem c4_310 : ¬ drop0% Semiquot.isPure_of_subsingleton 1 := fun h => sqU_not_pure (h sqU)
-- `Stream'.Seq.length'_of_terminates` idx 2: necessary (dependent; the constant sequence 0, 0, … does not terminate)
theorem c4_311 : ¬ indep0% Stream'.Seq.length'_of_terminates 2 := fun h => zs_nt (h (s := zs))
-- `Stream'.Seq.length_cons` idx 3: necessary (dependent; constant infinite sequence)
theorem c4_312 : ¬ indep0% Stream'.Seq.length_cons 3 := fun h => zs_nt (h (x := 0) (s := zs))
-- `Stream'.Seq.length_eq_zero` idx 2: necessary (dependent; constant infinite sequence)
theorem c4_313 : ¬ indep0% Stream'.Seq.length_eq_zero 2 := fun h => zs_nt (h (s := zs))
-- `Stream'.Seq.length_le_iff` idx 3: necessary (dependent; constant infinite sequence)
theorem c4_314 : ¬ indep0% Stream'.Seq.length_le_iff 3 := fun h => zs_nt (h (s := zs) (n := 0))
-- `Stream'.Seq.lt_length_iff` idx 3: necessary (dependent; constant infinite sequence)
theorem c4_315 : ¬ indep0% Stream'.Seq.lt_length_iff 3 := fun h => zs_nt (h (s := zs) (n := 0))
-- `Stream'.Seq.length_toList` idx 2: necessary (dependent; constant infinite sequence)
theorem c4_316 : ¬ indep0% Stream'.Seq.length_toList 2 := fun h => zs_nt (h zs)
-- `Stream'.Seq.getElem?_toList` idx 2: necessary (dependent; constant infinite sequence)
theorem c4_317 : ¬ indep0% Stream'.Seq.getElem?_toList 2 := fun h => zs_nt (h zs 0)
-- `Stream'.Seq.ofList_toList` idx 2: necessary (dependent; constant infinite sequence)
theorem c4_318 : ¬ indep0% Stream'.Seq.ofList_toList 2 := fun h => zs_nt (h zs)
-- `Stream'.Seq.getLast?_toList` idx 2: necessary (dependent; constant infinite sequence)
theorem c4_319 : ¬ indep0% Stream'.Seq.getLast?_toList 2 := fun h => zs_nt (h zs)
-- `Stream'.Seq.length_map` idx 4: necessary (dependent; map id of the constant infinite sequence)
theorem c4_320 : ¬ indep0% Stream'.Seq.length_map 4 := fun h => by
  have := h (s := zs) (f := id); rw [Stream'.Seq.map_id] at this; exact zs_nt this
-- `Stream'.Seq.all_get` idx 3: necessary (s = [0], p = False)
theorem c4_321 : ¬ drop0% Stream'.Seq.all_get 3 := fun h =>
  h (p := fun _ : ℕ => False) (s := .cons 0 .nil) (n := 0) (x := 0) rfl
-- `Stream'.Seq.all_of_get` idx 3: necessary (s = [0], p = False)
theorem c4_322 : ¬ drop0% Stream'.Seq.all_of_get 3 := fun h =>
  h (p := fun _ : ℕ => False) (s := .cons 0 .nil) 0 (Stream'.Seq.mem_cons 0 _)
-- `Stream'.Seq.all_coind_drop_motive` idx 3: necessary (motive = False, step vacuous)
theorem c4_323 : ¬ drop0% Stream'.Seq.all_coind_drop_motive 3 := fun h =>
  h (s := (Stream'.Seq.nil : Stream'.Seq ℕ)) (fun _ => False) (fun _ _ f => f) 0
-- `Stream'.Seq.all_coind_drop_motive` idx 4: necessary (motive = (· = [0]), n = 1)
theorem c4_324 : ¬ drop0% Stream'.Seq.all_coind_drop_motive 4 := fun h => by
  have := h (s := (.cons 0 .nil : Stream'.Seq ℕ)) (fun t => t = .cons 0 .nil) rfl 1
  simp [Stream'.Seq.drop, Stream'.Seq.tail_cons] at this
-- `Stream'.Seq.all_coind` idx 4: necessary (motive = False, s = [0], p = False)
theorem c4_325 : ¬ drop0% Stream'.Seq.all_coind 4 := fun h =>
  h (s := (.cons 0 .nil : Stream'.Seq ℕ)) (p := fun _ => False) (fun _ => False) (fun _ _ f => f.elim) 0 (Stream'.Seq.mem_cons 0 _)
-- `Stream'.Seq.all_coind` idx 5: necessary (motive = True, s = [0], p = False)
theorem c4_326 : ¬ drop0% Stream'.Seq.all_coind 5 := fun h =>
  h (s := (.cons 0 .nil : Stream'.Seq ℕ)) (p := fun _ => False) (fun _ => True) trivial 0 (Stream'.Seq.mem_cons 0 _)
-- `Stream'.Seq.all_coind` idx 7: necessary (s = nil, motive = all p, p = False, x = 0)
theorem c4_327 : ¬ drop0% Stream'.Seq.all_coind 7 := fun h =>
  h (s := (.nil : Stream'.Seq ℕ)) (p := fun _ => False) (fun t => ∀ x ∈ t, False)
    (fun x hx => Stream'.Seq.notMem_nil x hx)
    (fun hd tl hm => ⟨hm hd (Stream'.Seq.mem_cons hd tl), fun x hx => hm x (Stream'.Seq.mem_cons_of_mem hd hx)⟩) 0
-- `Stream'.Seq.take_all` idx 3: necessary (s = [0], n = 1, p = False)
theorem c4_328 : ¬ drop0% Stream'.Seq.take_all 3 := fun h =>
  h (s := (.cons 0 .nil : Stream'.Seq ℕ)) (p := fun _ => False) (n := 1) (x := 0)
    (by simp [Stream'.Seq.take_succ_cons])
-- `Stream'.Seq.set_all` idx 3: necessary (s = [0], set index 1 to 1, p = (· = 1), y = 0)
theorem c4_329 : ¬ drop0% Stream'.Seq.set_all 3 := fun h => by
  have := h (p := fun x : ℕ => x = 1) (s := .cons 0 .nil) (n := 1) (x := 1) rfl 0
    (Stream'.Seq.get?_mem (n := 0) (by rw [Stream'.Seq.set_cons_succ]; rfl))
  exact absurd this (by decide)
-- `Stream'.Seq.set_all` idx 6: necessary (s = [0], p = (· = 0), set index 0 to 1)
theorem c4_330 : ¬ drop0% Stream'.Seq.set_all 6 := fun h => by
  have := h (p := fun x : ℕ => x = 0) (s := .cons 0 .nil)
    (fun x hx => by
      rcases Stream'.Seq.mem_cons_iff.1 hx with rfl | hx
      · rfl
      · exact (Stream'.Seq.notMem_nil _ hx).elim) (n := 0) (x := 1) 1
    (by rw [Stream'.Seq.set_cons_zero]; exact Stream'.Seq.mem_cons 1 _)
  exact absurd this (by decide)
-- `Stream'.Seq.Pairwise.cons` idx 4: necessary (R = ⊥, hd = 0, tl = [0])
theorem c4_331 : ¬ drop0% Stream'.Seq.Pairwise.cons 4 := fun h =>
  pw_head (R := fun _ _ => False) id (h (hd := 0) (tl := .cons 0 .nil) Stream'.Seq.Pairwise_cons_nil)
-- `Stream'.Seq.Pairwise.cons` idx 5: necessary (R = ≠, hd = 1, tl = [0, 0])
theorem c4_332 : ¬ drop0% Stream'.Seq.Pairwise.cons 5 := fun h =>
  pw_tail (R := fun a b : ℕ => a ≠ b) (by decide) (h (hd := 1) (tl := .cons 0 (.cons 0 .nil)) (fun x hx => by
    rcases Stream'.Seq.mem_cons_iff.1 hx with rfl | hx
    · decide
    rcases Stream'.Seq.mem_cons_iff.1 hx with rfl | hx
    · decide
    · exact (Stream'.Seq.notMem_nil _ hx).elim))
-- `Stream'.Seq.Pairwise.cons_cons_of_trans` idx 2: necessary (R = ≠ is not transitive: [0, 1, 0])
theorem c4_333 : ¬ drop0% Stream'.Seq.Pairwise.cons_cons_of_trans 2 := fun h =>
  not_pw010 (h (hd := 0) (tl_hd := 1) (tl_tl := .cons 0 .nil) (by decide) pw10)
-- `Stream'.Seq.Pairwise.cons_cons_of_trans` idx 6: necessary (R = <, hd = 1, tl_hd = 0, tl_tl = nil)
theorem c4_334 : ¬ drop0% Stream'.Seq.Pairwise.cons_cons_of_trans 6 := fun h =>
  pw_head (R := fun a b : ℕ => a < b) (by decide) (h (hd := 1) (tl_hd := 0) (tl_tl := .nil) Stream'.Seq.Pairwise_cons_nil)
-- `Stream'.Seq.Pairwise.cons_cons_of_trans` idx 7: necessary (R = <, [0, 1, 0])
theorem c4_335 : ¬ drop0% Stream'.Seq.Pairwise.cons_cons_of_trans 7 := fun h =>
  pw_tail (R := fun a b : ℕ => a < b) (by decide) (h (hd := 0) (tl_hd := 1) (tl_tl := .cons 0 .nil) (by decide))
-- `Stream'.Seq.Pairwise.coind` idx 4: necessary (motive = False, R = ⊥, s = [0, 0])
theorem c4_336 : ¬ drop0% Stream'.Seq.Pairwise.coind 4 := fun h =>
  pw_head (R := fun _ _ => False) id (h (s := .cons 0 (.cons 0 .nil)) (fun _ => False) (fun _ _ f => f.elim))
-- `Stream'.Seq.Pairwise.coind` idx 5: necessary (motive = True, R = ⊥, s = [0, 0])
theorem c4_337 : ¬ drop0% Stream'.Seq.Pairwise.coind 5 := fun h =>
  pw_head (R := fun _ _ => False) id (h (s := .cons 0 (.cons 0 .nil)) (fun _ => True) trivial)
-- `Stream'.Seq.Pairwise.coind_trans` idx 5: necessary (motive = False, R = <, s = [1, 0])
theorem c4_338 : ¬ drop0% Stream'.Seq.Pairwise.coind_trans 5 := fun h =>
  pw_head (R := fun a b : ℕ => a < b) (by decide) (h (s := .cons 1 (.cons 0 .nil)) (fun _ => False) (fun _ _ f => f.elim))
-- `Stream'.Seq.Pairwise.coind_trans` idx 6: necessary (motive = True, R = <, s = [1, 0])
theorem c4_339 : ¬ drop0% Stream'.Seq.Pairwise.coind_trans 6 := fun h =>
  pw_head (R := fun a b : ℕ => a < b) (by decide) (h (s := .cons 1 (.cons 0 .nil)) (fun _ => True) trivial)
-- `Stream'.Seq.Pairwise_tail` idx 3: necessary (R = ⊥, s = [0, 0, 0])
theorem c4_340 : ¬ drop0% Stream'.Seq.Pairwise_tail 3 := fun h =>
  pw_head (R := fun _ _ => False) id (h (s := .cons 0 (.cons 0 (.cons 0 .nil))))
-- `Stream'.Seq.Pairwise_drop` idx 3: necessary (R = ⊥, s = [0, 0], n = 0)
theorem c4_341 : ¬ drop0% Stream'.Seq.Pairwise_drop 3 := fun h =>
  pw_head (R := fun _ _ => False) id (h (s := .cons 0 (.cons 0 .nil)) (n := 0))
-- `Stream'.Seq.at_least_as_long_as_coind` idx 5: necessary (motive = False, a = nil, b = [0])
theorem c4_342 : ¬ drop0% Stream'.Seq.at_least_as_long_as_coind 5 := fun h => by
  have := h (a := (.nil : Stream'.Seq ℕ)) (b := (.cons 0 .nil : Stream'.Seq ℕ)) (fun _ _ => False) (fun _ _ f => f.elim)
  simp [Stream'.Seq.length'_nil, Stream'.Seq.length'_cons] at this
-- `Stream'.Seq.at_least_as_long_as_coind` idx 6: necessary (motive = True, a = nil, b = [0])
theorem c4_343 : ¬ drop0% Stream'.Seq.at_least_as_long_as_coind 6 := fun h => by
  have := h (a := (.nil : Stream'.Seq ℕ)) (b := (.cons 0 .nil : Stream'.Seq ℕ)) (fun _ _ => True) trivial
  simp [Stream'.Seq.length'_nil, Stream'.Seq.length'_cons] at this

namespace W3c4
theorem sq2 : Squarefree (2:ℤ) := Int.prime_two.squarefree
end W3c4

-- `Stream'.Seq.Pairwise.coind_trans` idx 2: necessary (R = ≠ is not transitive; motive = consecutive entries differ, s = [0, 1, 0])
theorem c4_344 : ¬ drop0% Stream'.Seq.Pairwise.coind_trans 2 := fun h => not_pw010 (h (R := fun a b : ℕ => a ≠ b)
    (s := .cons 0 (.cons 1 (.cons 0 .nil)))
    (fun t => ∀ n a b, t.get? n = some a → t.get? (n + 1) = some b → a ≠ b)
    (by
      intro n a b ha hb
      rcases n with _ | _ | n <;> simp [Stream'.Seq.get?_cons_succ, Stream'.Seq.get?_cons_zero] at ha hb <;> omega)
    (fun hd tl hm => ⟨fun x hx => hm 0 hd x rfl hx, fun n a b ha hb => hm (n + 1) a b ha hb⟩))
-- `NNRat.Nonneg.coe_ofScientific` idx 3: necessary (dependent; K = ℚ with reversed order is not a strict ordered ring)
theorem c4_501 : ¬ indep0% NNRat.Nonneg.coe_ofScientific 3 := fun h => RQ_not (h (K := RQ) 0 false 0)
-- `Rat.sq_mul_squarefree_unique` idx 3: necessary (d₁ = 1, d₂ = 4, r₁ = 2, r₂ = 1)
theorem c4_502 : ¬ drop0% Rat.sq_mul_squarefree_unique 3 := fun h =>
  absurd (h (d₁ := 1) (d₂ := 4) squarefree_one 2 1 (by norm_num) (by norm_num)) (by decide)
-- `Rat.sq_mul_squarefree_unique` idx 6: necessary (d₁ = 1, d₂ = 2, r₁ = r₂ = 0)
theorem c4_503 : ¬ drop0% Rat.sq_mul_squarefree_unique 6 := fun h =>
  absurd (h (d₁ := 1) (d₂ := 2) squarefree_one sq2 0 0 (by norm_num)) (by decide)
-- `Rat.sq_mul_squarefree_unique` idx 7: necessary (d₁ = 1, d₂ = 2, r₁ = r₂ = 1)
theorem c4_504 : ¬ drop0% Rat.sq_mul_squarefree_unique 7 := fun h =>
  absurd (h (d₁ := 1) (d₂ := 2) squarefree_one sq2 1 1 one_ne_zero) (by decide)
-- `Rat.lift_binop_eq` idx 3: necessary (f = 1, f₁ = 0, f₂ = 1)
theorem c4_505 : ¬ drop0% Rat.lift_binop_eq 3 := fun h => by
  have := h (fun _ _ => 1) (fun _ _ _ _ => 0) (fun _ _ _ _ => 1) (fun _ _ => one_ne_zero) 1 1 1 1 one_ne_zero
    one_ne_zero (fun _ _ => rfl)
  revert this; decide +kernel
-- `Rat.lift_binop_eq` idx 4: necessary (f₁ = f₂ = if n₁ = 2 then 0 else 1, f x y = if x.num = 2 then 0 else 1, a = b = 2)
theorem c4_506 : ¬ drop0% Rat.lift_binop_eq 4 := fun h => by
  have := h (fun x _ => if x.num = 2 then 0 else 1) (fun n₁ _ _ _ => if n₁ = 2 then 0 else 1)
    (fun n₁ _ _ _ => if n₁ = 2 then 0 else 1)
    (by
      intro n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂
      show (if n₁ = 2 then (0:ℚ) else 1) = _
      by_cases e : n₁ = 2 <;> simp [e])
    2 2 1 1 (by decide) (by decide) (fun _ _ => mul_comm _ _)
  revert this; decide +kernel
-- `Rat.lift_binop_eq` idx 9: necessary (b = 0: f x y = x + 1, f₁ = n₁ + d₁, f₂ = d₁)
theorem c4_507 : ¬ drop0% Rat.lift_binop_eq 9 := fun h => by
  have := h (fun x _ => x + 1) (fun n₁ d₁ _ _ => n₁ + d₁) (fun _ d₁ _ _ => d₁)
    (by
      intro n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂
      have hr := Rat.num_div_den (⟨n₁, d₁, h₁, c₁⟩ : ℚ)
      have hd : (d₁ : ℚ) ≠ 0 := by exact_mod_cast h₁
      show (⟨n₁, d₁, h₁, c₁⟩ : ℚ) + 1 = _
      rw [Rat.divInt_eq_div]; push_cast
      rw [add_div, div_self hd, ← hr])
    (fun h _ => h) 1 0 1 1 one_ne_zero (fun h1 _ => by simp at h1; simp [h1])
  revert this; decide +kernel
-- `Rat.lift_binop_eq` idx 10: necessary (d = 0: f x y = y + 1, f₁ = n₂ + d₂, f₂ = d₂)
theorem c4_508 : ¬ drop0% Rat.lift_binop_eq 10 := fun h => by
  have := h (fun _ y => y + 1) (fun _ _ n₂ d₂ => n₂ + d₂) (fun _ _ _ d₂ => d₂)
    (by
      intro n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂
      have hr := Rat.num_div_den (⟨n₂, d₂, h₂, c₂⟩ : ℚ)
      have hd : (d₂ : ℚ) ≠ 0 := by exact_mod_cast h₂
      show (⟨n₂, d₂, h₂, c₂⟩ : ℚ) + 1 = _
      rw [Rat.divInt_eq_div]; push_cast
      rw [add_div, div_self hd, ← hr])
    (fun _ h => h) 1 1 1 0 one_ne_zero (fun _ h2 => by simp at h2; simp [h2])
  revert this; decide +kernel
-- `Rat.lift_binop_eq` idx 11: necessary (f x y = x.num, f₁ = n₁, f₂ = 1, a = b = 2)
theorem c4_509 : ¬ drop0% Rat.lift_binop_eq 11 := fun h => by
  have := h (fun x _ => (x.num : ℚ)) (fun n₁ _ _ _ => n₁) (fun _ _ _ _ => 1)
    (by intro n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂; exact (Rat.divInt_one _).symm)
    (fun _ _ => one_ne_zero) 2 2 1 1 (by decide) (by decide)
  revert this; decide +kernel
-- `Nat.ratSqrt_sq_le` idx 2: removable (at prec = 0 the square root is 0 / 0 = 0)
theorem c4_510 : drop% Nat.ratSqrt_sq_le 2 := by
  intro x prec
  rcases Nat.eq_zero_or_pos prec with rfl | hp
  · simp [Nat.ratSqrt]
  · exact Nat.ratSqrt_sq_le x hp
-- `NNRat.cast_zpow_of_ne_zero` idx 4: removable (if the numerator casts to 0 then the cast of q and of q⁻¹ are both 0)
theorem c4_511 : drop% NNRat.cast_zpow_of_ne_zero 4 := by
  intro K _ q z
  by_cases hq : (q.num : K) = 0
  · have h0 : (NNRat.cast q : K) = 0 := by rw [NNRat.cast_def, hq, zero_div]
    have h1 : (NNRat.cast q⁻¹ : K) = 0 := by
      rcases eq_or_ne q 0 with rfl | hq0
      · simp
      · have e : (q⁻¹).den = q.num := by
          have := Rat.den_inv_of_ne_zero (q := (q : ℚ)) (by exact_mod_cast hq0)
          rw [← NNRat.den_coe, NNRat.coe_inv, this, NNRat.num_coe]; simp
        rw [NNRat.cast_def, e, hq, div_zero]
    obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
    · simp
    · simp_rw [zpow_neg, zpow_natCast, ← inv_pow, NNRat.cast_pow, h0, h1, inv_zero]
  · exact NNRat.cast_zpow_of_ne_zero q z hq

-- `Rat.cast_pos_of_pos` idx 4: necessary (K = ℚ with reversed order, q = 1)
theorem c4_1 : ¬ drop0% Rat.cast_pos_of_pos 4 := fun h => by
  have := h (K := RQ) (q := 1) (by decide); revert this; decide +kernel

-- `Rat.cast_strictMono` idx 3: necessary (K = ℚ reversed: cast 0 < cast 1 fails)
theorem c4_2 : ¬ drop0% Rat.cast_strictMono 3 := fun h => by
  have := h (K := RQ) (show (0:ℚ) < 1 by decide); revert this; decide +kernel

-- `Rat.cast_mono` idx 3: necessary (K = ℚ reversed: cast 1 ≤ cast 2 fails)
theorem c4_3 : ¬ drop0% Rat.cast_mono 3 := fun h => by
  have := h (K := RQ) (show (1:ℚ) ≤ 2 by decide); revert this; decide +kernel

-- `Rat.castOrderEmbedding_apply` idx 3: necessary (dependent: K = ℚ reversed is not a strict ordered ring)
theorem c4_4 : ¬ indep0% Rat.castOrderEmbedding_apply 3 := fun h => by
  exact RQ_not (h (K := RQ) 0)

-- `Rat.cast_le` idx 5: necessary (K = ℚ reversed, (p := 0) (q := 1): right side true, left side false)
theorem c4_5 : ¬ drop0% Rat.cast_le 5 := fun h => by
  have := (h (K := RQ) (p := 0) (q := 1)).2 (by decide); revert this; decide +kernel

-- `Rat.cast_lt` idx 5: necessary (K = ℚ reversed, (p := 0) (q := 1): right side true, left side false)
theorem c4_6 : ¬ drop0% Rat.cast_lt 5 := fun h => by
  have := (h (K := RQ) (p := 0) (q := 1)).2 (by decide); revert this; decide +kernel

-- `Rat.cast_nonneg` idx 4: necessary (K = ℚ reversed, (q := 1): right side true, left side false)
theorem c4_7 : ¬ drop0% Rat.cast_nonneg 4 := fun h => by
  have := (h (K := RQ) (q := 1)).2 (by decide); revert this; decide +kernel

-- `Rat.cast_nonpos` idx 4: necessary (K = ℚ reversed, (q := 1): left side true, right side false)
theorem c4_8 : ¬ drop0% Rat.cast_nonpos 4 := fun h => by
  have := (h (K := RQ) (q := 1)).1 (by decide +kernel); revert this; decide +kernel

-- `Rat.cast_pos` idx 4: necessary (K = ℚ reversed, (q := 1): right side true, left side false)
theorem c4_9 : ¬ drop0% Rat.cast_pos 4 := fun h => by
  have := (h (K := RQ) (q := 1)).2 (by decide); revert this; decide +kernel

-- `Rat.cast_lt_zero` idx 4: necessary (K = ℚ reversed, (q := 1): left side true, right side false)
theorem c4_10 : ¬ drop0% Rat.cast_lt_zero 4 := fun h => by
  have := (h (K := RQ) (q := 1)).1 (by decide +kernel); revert this; decide +kernel

-- `Rat.cast_le_natCast` idx 3: necessary (K = ℚ reversed, (m := 0) (n := 1): right side true, left side false)
theorem c4_11 : ¬ drop0% Rat.cast_le_natCast 3 := fun h => by
  have := (h (K := RQ) (m := 0) (n := 1)).2 (by decide); revert this; decide +kernel

-- `Rat.natCast_le_cast` idx 3: necessary (K = ℚ reversed, (m := 0) (n := 1): right side true, left side false)
theorem c4_12 : ¬ drop0% Rat.natCast_le_cast 3 := fun h => by
  have := (h (K := RQ) (m := 0) (n := 1)).2 (by decide); revert this; decide +kernel

-- `Rat.cast_le_intCast` idx 3: necessary (K = ℚ reversed, (m := 0) (n := 1): right side true, left side false)
theorem c4_13 : ¬ drop0% Rat.cast_le_intCast 3 := fun h => by
  have := (h (K := RQ) (m := 0) (n := 1)).2 (by decide); revert this; decide +kernel

-- `Rat.intCast_le_cast` idx 3: necessary (K = ℚ reversed, (m := 0) (n := 1): right side true, left side false)
theorem c4_14 : ¬ drop0% Rat.intCast_le_cast 3 := fun h => by
  have := (h (K := RQ) (m := 0) (n := 1)).2 (by decide); revert this; decide +kernel

-- `Rat.cast_lt_natCast` idx 3: necessary (K = ℚ reversed, (m := 0) (n := 1): right side true, left side false)
theorem c4_15 : ¬ drop0% Rat.cast_lt_natCast 3 := fun h => by
  have := (h (K := RQ) (m := 0) (n := 1)).2 (by decide); revert this; decide +kernel

-- `Rat.natCast_lt_cast` idx 3: necessary (K = ℚ reversed, (m := 0) (n := 1): right side true, left side false)
theorem c4_16 : ¬ drop0% Rat.natCast_lt_cast 3 := fun h => by
  have := (h (K := RQ) (m := 0) (n := 1)).2 (by decide); revert this; decide +kernel

-- `Rat.cast_lt_intCast` idx 3: necessary (K = ℚ reversed, (m := 0) (n := 1): right side true, left side false)
theorem c4_17 : ¬ drop0% Rat.cast_lt_intCast 3 := fun h => by
  have := (h (K := RQ) (m := 0) (n := 1)).2 (by decide); revert this; decide +kernel

-- `Rat.intCast_lt_cast` idx 3: necessary (K = ℚ reversed, (m := 0) (n := 1): right side true, left side false)
theorem c4_18 : ¬ drop0% Rat.intCast_lt_cast 3 := fun h => by
  have := (h (K := RQ) (m := 0) (n := 1)).2 (by decide); revert this; decide +kernel

-- `Rat.cast_min` idx 3: necessary (K = ℚ reversed, p = 0, q = 1)
theorem c4_19 : ¬ drop0% Rat.cast_min 3 := fun h => by
  have := h (K := RQ) 0 1; revert this; decide +kernel

-- `Rat.cast_max` idx 3: necessary (K = ℚ reversed, p = 0, q = 1)
theorem c4_20 : ¬ drop0% Rat.cast_max 3 := fun h => by
  have := h (K := RQ) 0 1; revert this; decide +kernel

-- `Rat.cast_abs` idx 3: necessary (K = ℚ reversed, q = 1: |1| = -1 in K)
theorem c4_21 : ¬ drop0% Rat.cast_abs 3 := fun h => by
  have := h (K := RQ) 1; revert this; decide +kernel

-- `Rat.preimage_cast_Icc` idx 3: necessary (K = ℚ reversed, bounds 0 1, point 0)
theorem c4_22 : ¬ drop0% Rat.preimage_cast_Icc 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0 1) 0; revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `Rat.preimage_cast_Ico` idx 3: necessary (K = ℚ reversed, bounds 0 1, point 0)
theorem c4_23 : ¬ drop0% Rat.preimage_cast_Ico 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0 1) 0; revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `Rat.preimage_cast_Ioc` idx 3: necessary (K = ℚ reversed, bounds 0 1, point 1)
theorem c4_24 : ¬ drop0% Rat.preimage_cast_Ioc 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0 1) 1; revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `Rat.preimage_cast_Ioo` idx 3: necessary (K = ℚ reversed, bounds 0 1, point (1/2))
theorem c4_25 : ¬ drop0% Rat.preimage_cast_Ioo 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0 1) (1/2); revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `Rat.preimage_cast_Ici` idx 3: necessary (K = ℚ reversed, bounds 0, point 1)
theorem c4_26 : ¬ drop0% Rat.preimage_cast_Ici 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0) 1; revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `Rat.preimage_cast_Iic` idx 3: necessary (K = ℚ reversed, bounds 0, point 1)
theorem c4_27 : ¬ drop0% Rat.preimage_cast_Iic 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0) 1; revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `Rat.preimage_cast_Ioi` idx 3: necessary (K = ℚ reversed, bounds 0, point 1)
theorem c4_28 : ¬ drop0% Rat.preimage_cast_Ioi 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0) 1; revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `Rat.preimage_cast_Iio` idx 3: necessary (K = ℚ reversed, bounds 0, point 1)
theorem c4_29 : ¬ drop0% Rat.preimage_cast_Iio 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0) 1; revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `Rat.preimage_cast_uIcc` idx 3: necessary (K = ℚ with order pulled back along the swap 1/2 ↔ 3/2, bounds 0 1, point (3/2))
theorem c4_30 : ¬ drop0% Rat.preimage_cast_uIcc 3 := fun h => by
  have := Set.ext_iff.1 (h (K := P) 0 1) (3/2); revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `Rat.preimage_cast_uIoc` idx 3: necessary (K = ℚ with order pulled back along the swap 1/2 ↔ 3/2, bounds 0 1, point (3/2))
theorem c4_31 : ¬ drop0% Rat.preimage_cast_uIoc 3 := fun h => by
  have := Set.ext_iff.1 (h (K := P) 0 1) (3/2); revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `NNRat.cast_strictMono` idx 3: necessary (K = ℚ reversed: cast 0 < cast 1 fails)
theorem c4_32 : ¬ drop0% NNRat.cast_strictMono 3 := fun h => by
  have := h (K := RQ) (show (0:ℚ≥0) < 1 by decide); revert this; decide +kernel

-- `NNRat.cast_mono` idx 3: necessary (K = ℚ reversed: cast 1 ≤ cast 2 fails)
theorem c4_33 : ¬ drop0% NNRat.cast_mono 3 := fun h => by
  have := h (K := RQ) (show (1:ℚ≥0) ≤ 2 by decide); revert this; decide +kernel

-- `NNRat.castOrderEmbedding_apply` idx 3: necessary (dependent: K = ℚ reversed is not a strict ordered ring)
theorem c4_34 : ¬ indep0% NNRat.castOrderEmbedding_apply 3 := fun h => by
  exact RQ_not (h (K := RQ) 0)

-- `NNRat.cast_le` idx 3: necessary (K = ℚ reversed, (p := 0) (q := 1): right side true, left side false)
theorem c4_35 : ¬ drop0% NNRat.cast_le 3 := fun h => by
  have := (h (K := RQ) (p := 0) (q := 1)).2 (by decide); revert this; decide +kernel

-- `NNRat.cast_lt` idx 3: necessary (K = ℚ reversed, (p := 0) (q := 1): right side true, left side false)
theorem c4_36 : ¬ drop0% NNRat.cast_lt 3 := fun h => by
  have := (h (K := RQ) (p := 0) (q := 1)).2 (by decide); revert this; decide +kernel

-- `NNRat.cast_nonpos` idx 3: necessary (K = ℚ reversed, (q := 1): left side true, right side false)
theorem c4_37 : ¬ drop0% NNRat.cast_nonpos 3 := fun h => by
  have := (h (K := RQ) (q := 1)).1 (by decide +kernel); revert this; decide +kernel

-- `NNRat.cast_pos` idx 3: necessary (K = ℚ reversed, (q := 1): right side true, left side false)
theorem c4_38 : ¬ drop0% NNRat.cast_pos 3 := fun h => by
  have := (h (K := RQ) (q := 1)).2 (by decide); revert this; decide +kernel

-- `NNRat.cast_lt_zero` idx 3: necessary (K = ℚ reversed, (q := 1): left side true, right side false)
theorem c4_39 : ¬ drop0% NNRat.cast_lt_zero 3 := fun h => by
  have := (h (K := RQ) (q := 1)).1 (by decide +kernel); revert this; decide +kernel

-- `NNRat.not_cast_lt_zero` idx 3: necessary (K = ℚ reversed, q = 1: cast 1 < 0 holds)
theorem c4_40 : ¬ drop0% NNRat.not_cast_lt_zero 3 := fun h => by
  have := h (K := RQ) (q := 1); revert this; decide +kernel

-- `NNRat.cast_le_one` idx 3: necessary (K = ℚ reversed, (p := 0): right side true, left side false)
theorem c4_41 : ¬ drop0% NNRat.cast_le_one 3 := fun h => by
  have := (h (K := RQ) (p := 0)).2 (by decide); revert this; decide +kernel

-- `NNRat.one_le_cast` idx 3: necessary (K = ℚ reversed, (p := 0): left side true, right side false)
theorem c4_42 : ¬ drop0% NNRat.one_le_cast 3 := fun h => by
  have := (h (K := RQ) (p := 0)).1 (by decide +kernel); revert this; decide +kernel

-- `NNRat.cast_lt_one` idx 3: necessary (K = ℚ reversed, (p := 0): right side true, left side false)
theorem c4_43 : ¬ drop0% NNRat.cast_lt_one 3 := fun h => by
  have := (h (K := RQ) (p := 0)).2 (by decide); revert this; decide +kernel

-- `NNRat.one_lt_cast` idx 3: necessary (K = ℚ reversed, (p := 0): left side true, right side false)
theorem c4_44 : ¬ drop0% NNRat.one_lt_cast 3 := fun h => by
  have := (h (K := RQ) (p := 0)).1 (by decide +kernel); revert this; decide +kernel

-- `NNRat.cast_le_ofNat` idx 3: necessary (K = ℚ reversed, (p := 0) (n := 2): right side true, left side false)
theorem c4_45 : ¬ drop0% NNRat.cast_le_ofNat 3 := fun h => by
  have := (h (K := RQ) (p := 0) (n := 2)).2 (by decide); revert this; decide +kernel

-- `NNRat.cast_le_ofNat` idx 6: necessary (dependent: n = 0 is not AtLeastTwo)
theorem c4_46 : ¬ indep0% NNRat.cast_le_ofNat 6 := fun h => by
  have := h (K := ℚ) (p := 0) (n := 0); obtain ⟨h2⟩ := this; omega

-- `NNRat.ofNat_le_cast` idx 3: necessary (K = ℚ reversed, (p := 0) (n := 2): left side true, right side false)
theorem c4_47 : ¬ drop0% NNRat.ofNat_le_cast 3 := fun h => by
  have := (h (K := RQ) (p := 0) (n := 2)).1 (by decide +kernel); revert this; decide +kernel

-- `NNRat.ofNat_le_cast` idx 6: necessary (dependent: n = 0 is not AtLeastTwo)
theorem c4_48 : ¬ indep0% NNRat.ofNat_le_cast 6 := fun h => by
  have := h (K := ℚ) (p := 0) (n := 0); obtain ⟨h2⟩ := this; omega

-- `NNRat.cast_lt_ofNat` idx 3: necessary (K = ℚ reversed, (p := 0) (n := 2): right side true, left side false)
theorem c4_49 : ¬ drop0% NNRat.cast_lt_ofNat 3 := fun h => by
  have := (h (K := RQ) (p := 0) (n := 2)).2 (by decide); revert this; decide +kernel

-- `NNRat.cast_lt_ofNat` idx 6: necessary (dependent: n = 0 is not AtLeastTwo)
theorem c4_50 : ¬ indep0% NNRat.cast_lt_ofNat 6 := fun h => by
  have := h (K := ℚ) (p := 0) (n := 0); obtain ⟨h2⟩ := this; omega

-- `NNRat.ofNat_lt_cast` idx 3: necessary (K = ℚ reversed, (p := 0) (n := 2): left side true, right side false)
theorem c4_51 : ¬ drop0% NNRat.ofNat_lt_cast 3 := fun h => by
  have := (h (K := RQ) (p := 0) (n := 2)).1 (by decide +kernel); revert this; decide +kernel

-- `NNRat.ofNat_lt_cast` idx 6: necessary (dependent: n = 0 is not AtLeastTwo)
theorem c4_52 : ¬ indep0% NNRat.ofNat_lt_cast 6 := fun h => by
  have := h (K := ℚ) (p := 0) (n := 0); obtain ⟨h2⟩ := this; omega

-- `NNRat.cast_le_natCast` idx 3: necessary (K = ℚ reversed, (m := 0) (n := 1): right side true, left side false)
theorem c4_53 : ¬ drop0% NNRat.cast_le_natCast 3 := fun h => by
  have := (h (K := RQ) (m := 0) (n := 1)).2 (by decide); revert this; decide +kernel

-- `NNRat.natCast_le_cast` idx 3: necessary (K = ℚ reversed, (m := 0) (n := 1): right side true, left side false)
theorem c4_54 : ¬ drop0% NNRat.natCast_le_cast 3 := fun h => by
  have := (h (K := RQ) (m := 0) (n := 1)).2 (by decide); revert this; decide +kernel

-- `NNRat.cast_lt_natCast` idx 3: necessary (K = ℚ reversed, (m := 0) (n := 1): right side true, left side false)
theorem c4_55 : ¬ drop0% NNRat.cast_lt_natCast 3 := fun h => by
  have := (h (K := RQ) (m := 0) (n := 1)).2 (by decide); revert this; decide +kernel

-- `NNRat.natCast_lt_cast` idx 3: necessary (K = ℚ reversed, (m := 0) (n := 1): right side true, left side false)
theorem c4_56 : ¬ drop0% NNRat.natCast_lt_cast 3 := fun h => by
  have := (h (K := RQ) (m := 0) (n := 1)).2 (by decide); revert this; decide +kernel

-- `NNRat.cast_min` idx 3: necessary (K = ℚ reversed, p = 0, q = 1)
theorem c4_57 : ¬ drop0% NNRat.cast_min 3 := fun h => by
  have := h (K := RQ) 0 1; revert this; decide +kernel

-- `NNRat.cast_max` idx 3: necessary (K = ℚ reversed, p = 0, q = 1)
theorem c4_58 : ¬ drop0% NNRat.cast_max 3 := fun h => by
  have := h (K := RQ) 0 1; revert this; decide +kernel

-- `NNRat.preimage_cast_Icc` idx 3: necessary (K = ℚ reversed, bounds 0 1, point 0)
theorem c4_59 : ¬ drop0% NNRat.preimage_cast_Icc 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0 1) 0; revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `NNRat.preimage_cast_Ico` idx 3: necessary (K = ℚ reversed, bounds 0 1, point 0)
theorem c4_60 : ¬ drop0% NNRat.preimage_cast_Ico 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0 1) 0; revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `NNRat.preimage_cast_Ioc` idx 3: necessary (K = ℚ reversed, bounds 0 1, point 1)
theorem c4_61 : ¬ drop0% NNRat.preimage_cast_Ioc 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0 1) 1; revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `NNRat.preimage_cast_Ioo` idx 3: necessary (K = ℚ reversed, bounds 0 1, point (1/2))
theorem c4_62 : ¬ drop0% NNRat.preimage_cast_Ioo 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0 1) (1/2); revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `NNRat.preimage_cast_Ici` idx 3: necessary (K = ℚ reversed, bounds 0, point 1)
theorem c4_63 : ¬ drop0% NNRat.preimage_cast_Ici 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0) 1; revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `NNRat.preimage_cast_Iic` idx 3: necessary (K = ℚ reversed, bounds 0, point 1)
theorem c4_64 : ¬ drop0% NNRat.preimage_cast_Iic 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0) 1; revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `NNRat.preimage_cast_Ioi` idx 3: necessary (K = ℚ reversed, bounds 0, point 1)
theorem c4_65 : ¬ drop0% NNRat.preimage_cast_Ioi 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0) 1; revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `NNRat.preimage_cast_Iio` idx 3: necessary (K = ℚ reversed, bounds 0, point 1)
theorem c4_66 : ¬ drop0% NNRat.preimage_cast_Iio 3 := fun h => by
  have := Set.ext_iff.1 (h (K := RQ) 0) 1; revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `NNRat.preimage_cast_uIcc` idx 3: necessary (K = ℚ with order pulled back along the swap 1/2 ↔ 3/2, bounds 0 1, point (3/2))
theorem c4_67 : ¬ drop0% NNRat.preimage_cast_uIcc 3 := fun h => by
  have := Set.ext_iff.1 (h (K := P) 0 1) (3/2); revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `NNRat.preimage_cast_uIoc` idx 3: necessary (K = ℚ with order pulled back along the swap 1/2 ↔ 3/2, bounds 0 1, point (3/2))
theorem c4_68 : ¬ drop0% NNRat.preimage_cast_uIoc 3 := fun h => by
  have := Set.ext_iff.1 (h (K := P) 0 1) (3/2); revert this; simp only [Set.mem_preimage, Set.mem_Icc, Set.mem_Ico, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ici, Set.mem_Iic, Set.mem_Ioi, Set.mem_Iio, Set.mem_uIcc, Set.mem_uIoc]; decide +kernel

-- `Rat.floor_cast` idx 3: necessary (α = ℚ ordered via the swap 1/2 ↔ 3/2, -1/2 ↔ -3/2 (lawful FloorRing, not strict ordered ring), value ±3/2)
theorem c4_101 : ¬ drop0% Rat.floor_cast 3 := fun h => by have := h (α := P) (3/2); revert this; decide +kernel

-- `Rat.ceil_cast` idx 3: necessary (α = ℚ ordered via the swap 1/2 ↔ 3/2, -1/2 ↔ -3/2 (lawful FloorRing, not strict ordered ring), value ±3/2)
theorem c4_102 : ¬ drop0% Rat.ceil_cast 3 := fun h => by have := h (α := P) (3/2); revert this; decide +kernel

-- `Rat.round_cast` idx 3: necessary (α = ℚ ordered via the swap 1/2 ↔ 3/2, -1/2 ↔ -3/2 (lawful FloorRing, not strict ordered ring), value ±3/2)
theorem c4_103 : ¬ drop0% Rat.round_cast 3 := fun h => by have := h (α := P) (3/2); revert this; decide +kernel

-- `Rat.cast_fract` idx 3: necessary (α = ℚ ordered via the swap 1/2 ↔ 3/2, -1/2 ↔ -3/2 (lawful FloorRing, not strict ordered ring), value ±3/2)
theorem c4_104 : ¬ drop0% Rat.cast_fract 3 := fun h => by have := h (α := P) (3/2); revert this; decide +kernel

-- `Rat.isNat_intFloor_ofIsNNRat` idx 3: necessary (α = ℚ ordered via the swap 1/2 ↔ 3/2, -1/2 ↔ -3/2 (lawful FloorRing, not strict ordered ring), value ±3/2)
theorem c4_105 : ¬ drop0% Rat.isNat_intFloor_ofIsNNRat 3 := fun h => by
  have := (h (α := P) _ _ _ nnr32).out; revert this; decide +kernel

-- `Rat.isInt_intFloor_ofIsRat_neg` idx 3: necessary (α = ℚ ordered via the swap 1/2 ↔ 3/2, -1/2 ↔ -3/2 (lawful FloorRing, not strict ordered ring), value ±3/2)
theorem c4_106 : ¬ drop0% Rat.isInt_intFloor_ofIsRat_neg 3 := fun h => by
  have := (h (α := P) _ _ _ ratm32).out; revert this; decide +kernel

-- `Rat.isNat_intCeil_ofIsNNRat` idx 3: necessary (α = ℚ ordered via the swap 1/2 ↔ 3/2, -1/2 ↔ -3/2 (lawful FloorRing, not strict ordered ring), value ±3/2)
theorem c4_107 : ¬ drop0% Rat.isNat_intCeil_ofIsNNRat 3 := fun h => by
  have := (h (α := P) _ _ _ nnr32).out; revert this; decide +kernel

-- `Rat.isInt_intCeil_ofIsRat_neg` idx 3: necessary (α = ℚ ordered via the swap 1/2 ↔ 3/2, -1/2 ↔ -3/2 (lawful FloorRing, not strict ordered ring), value ±3/2)
theorem c4_108 : ¬ drop0% Rat.isInt_intCeil_ofIsRat_neg 3 := fun h => by
  have := (h (α := P) _ _ _ ratm32).out; revert this; decide +kernel

-- `Rat.isNat_intFract_of_isNat` idx 6: necessary (ℚ, r = 1/2: fract r ≠ 0)
theorem c4_109 : ¬ drop0% Rat.isNat_intFract_of_isNat 6 := fun h => by
  have := (h (R := ℚ) (1/2) 0).out; revert this; decide +kernel

-- `Rat.isNat_intFract_of_isInt` idx 6: necessary (ℚ, r = 1/2: fract r ≠ 0)
theorem c4_110 : ¬ drop0% Rat.isNat_intFract_of_isInt 6 := fun h => by
  have := (h (R := ℚ) (1/2) 0).out; revert this; decide +kernel

-- `Rat.isNNRat_intFract_of_isNNRat` idx 3: necessary (α = ℚ ordered via the swap 1/2 ↔ 3/2, -1/2 ↔ -3/2 (lawful FloorRing, not strict ordered ring), value ±3/2)
theorem c4_111 : ¬ drop0% Rat.isNNRat_intFract_of_isNNRat 3 := fun h => by
  obtain ⟨_, e⟩ := h (α := P) _ _ _ nnr32; rw [invOf_eq_inv] at e; revert e; decide +kernel

-- `Rat.isNNRat_intFract_of_isNNRat` idx 8: necessary (d = 0: IsNNRat/IsRat with denominator 0 needs Invertible 0)
theorem c4_112 : ¬ drop0% Rat.isNNRat_intFract_of_isNNRat 8 := fun h => by
  obtain ⟨i, _⟩ := h (α := ℚ) 0 0 0; exact no_inv0 i

-- `Rat.isRat_intFract_of_isRat_negOfNat` idx 3: necessary (α = ℚ ordered via the swap 1/2 ↔ 3/2, -1/2 ↔ -3/2 (lawful FloorRing, not strict ordered ring), value ±3/2)
theorem c4_113 : ¬ drop0% Rat.isRat_intFract_of_isRat_negOfNat 3 := fun h => by
  obtain ⟨_, e⟩ := h (α := P) _ _ _ ratm32; rw [invOf_eq_inv] at e; revert e; decide +kernel

-- `Rat.isRat_intFract_of_isRat_negOfNat` idx 8: necessary (d = 0: IsNNRat/IsRat with denominator 0 needs Invertible 0)
theorem c4_114 : ¬ drop0% Rat.isRat_intFract_of_isRat_negOfNat 8 := fun h => by
  obtain ⟨i, _⟩ := h (α := ℚ) 0 0 0; exact no_inv0 i

-- `Rat.IsRat.isInt_round` idx 3: necessary (α = ℚ ordered via the swap 1/2 ↔ 3/2, -1/2 ↔ -3/2 (lawful FloorRing, not strict ordered ring), value ±3/2)
theorem c4_115 : ¬ drop0% Rat.IsRat.isInt_round 3 := fun h => by
  have := (h (R := P) _ _ _ 2 (by decide +kernel) rat32).out; revert this; decide +kernel

-- `Rat.IsRat.isInt_round` idx 9: necessary (ℚ, r = 1 = 1/1, res = 0)
theorem c4_116 : ¬ drop0% Rat.IsRat.isInt_round 9 := fun h => by
  have := (h (R := ℚ) _ _ _ 0 rat11).out; norm_num at this

-- `Rat.IsRat.isInt_round` idx 10: necessary (ℚ, r = 1, n = 0, d = 1, res = 0)
theorem c4_117 : ¬ drop0% Rat.IsRat.isInt_round 10 := fun h => by
  have := (h (R := ℚ) 1 0 1 0 (by norm_num)).out; norm_num at this

