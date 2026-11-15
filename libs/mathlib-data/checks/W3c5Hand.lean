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

namespace W3c5

open Set

-- helper: ℕ and Ioi 0 are infinite, with ncard 0 and encard ⊤
theorem iN : (univ : Set ℕ).Infinite := infinite_univ
theorem iI : (Ioi 0 : Set ℕ).Infinite := Ioi_infinite 0
theorem nU : (univ : Set ℕ).ncard = 0 := iN.ncard
theorem nI : (Ioi 0 : Set ℕ).ncard = 0 := iI.ncard
theorem eU : (univ : Set ℕ).encard = ⊤ := iN.encard_eq
theorem eI : (Ioi 0 : Set ℕ).encard = ⊤ := iI.encard_eq
theorem dI : (univ : Set ℕ) \ Ioi 0 = {0} := by ext n; simp
theorem cI : (Ioi 0 : Set ℕ)ᶜ = {0} := by ext n; simp
theorem iU : insert 0 (Ioi 0 : Set ℕ) = univ := by ext n; simp; try omega
theorem d0 : (univ : Set ℕ) \ {0} = Ioi 0 := by ext n; simp; try omega
theorem c0 : ({0} : Set ℕ)ᶜ = Ioi 0 := by ext n; simp; try omega
theorem uI : (univ : Set ℕ) ∩ Ioi 0 = Ioi 0 := by simp
theorem Iu : (Ioi 0 : Set ℕ) ∩ univ = Ioi 0 := by simp
theorem I0 : (Ioi 0 : Set ℕ) ∩ {0} = ∅ := by ext n; simp
theorem I0' : ({0} : Set ℕ) ∩ Ioi 0 = ∅ := by ext n; simp
theorem I0u : (Ioi 0 : Set ℕ) ∪ {0} = univ := by ext n; simp; try omega
theorem I0u' : ({0} : Set ℕ) ∪ Ioi 0 = univ := by ext n; simp; try omega
theorem d0I : ({0} : Set ℕ) \ Ioi 0 = {0} := by ext n; simp; try omega
theorem dI0 : (Ioi 0 : Set ℕ) \ {0} = Ioi 0 := by ext n; simp; try omega
theorem Ine : (Ioi 0 : Set ℕ) ≠ univ := fun e => by
  have h0 : (0 : ℕ) ∈ Ioi 0 := by rw [e]; exact mem_univ 0
  simp at h0
theorem nC : ({0} : Set ℕ).ncard = 1 := ncard_singleton 0
theorem eC : ({0} : Set ℕ).encard = 1 := encard_singleton 0
-- helper: the reals are uncountable
theorem nCR : ¬ (univ : Set ℝ).Countable := Cardinal.not_countable_real
theorem iR : (univ : Set ℝ).Infinite := fun h => nCR h.countable
theorem eR : (univ : Set ℝ).encard = ⊤ := iR.encard_eq
-- helper: no injection of the reals into ℕ
theorem noInj (f : ℝ → ℕ) (hf : InjOn f univ) : False :=
  nCR ((mapsTo_univ f univ).countable_of_injOn hf countable_univ)
-- helper: predecessor collapses 0 and 1 and is surjective on ℕ
theorem pred_img : Nat.pred '' (univ : Set ℕ) = univ := by
  ext n; simp only [mem_image, mem_univ, true_and, iff_true]; exact ⟨n + 1, rfl⟩
theorem pred_ni : ¬ InjOn Nat.pred (univ : Set ℕ) := fun h => absurd (h (mem_univ 0) (mem_univ 1) rfl) (by decide)
-- helper: a constant map on Bool is not injective
theorem const_ni {β : Type} (b : β) : ¬ InjOn (fun _ : Bool => b) univ :=
  fun h => absurd (h (mem_univ true) (mem_univ false) rfl) (by decide)
-- helper: the sets with ncard 0 in ℕ form an infinite family
theorem cofin_inf : {t : Set ℕ | t ⊆ univ ∧ t.ncard = 0}.Infinite := by
  refine infinite_of_injective_forall_mem (f := fun k : ℕ => ({k}ᶜ : Set ℕ)) ?_ ?_
  · intro a b hab; simpa using hab
  · intro k; exact ⟨subset_univ _, (finite_singleton k).infinite_compl.ncard⟩

end W3c5

open W3c5

-- `Set.Finite.encard_eq_coe_toFinset_card` idx 2: necessary (s = univ : Set ℕ)
theorem c5_1 : ¬ indep0% Set.Finite.encard_eq_coe_toFinset_card 2 := fun h => iN (h (s := Set.univ))

-- `Set.finite_of_encard_le_coe` idx 3: necessary (s = univ : Set ℕ)
theorem c5_2 : ¬ drop0% Set.finite_of_encard_le_coe 3 := fun h => iN (h (s := Set.univ) (k := 0))

-- `Set.finite_of_encard_eq_coe` idx 3: necessary (s = univ : Set ℕ)
theorem c5_3 : ¬ drop0% Set.finite_of_encard_eq_coe 3 := fun h => iN (h (s := Set.univ) (k := 0))

-- `Set.encard_sdiff` idx 4: necessary (s = Ioi 0, t = univ in ℕ: 1 vs ⊤ - ⊤ = 0)
theorem c5_4 : ¬ drop0% Set.encard_sdiff 4 := fun h => by
  have := h (s := Set.Ioi 0) (t := Set.univ) (Set.subset_univ _)
  simp [eI, eU, dI] at this

-- `Set.encard_diff` idx 4: necessary (s = Ioi 0, t = univ in ℕ)
theorem c5_5 : ¬ drop0% Set.encard_diff 4 := fun h => by
  have := h (s := Set.Ioi 0) (t := Set.univ) (Set.subset_univ _)
  simp [eI, eU, dI] at this

-- `Set.encard_sdiff'` idx 3: necessary (s = Ioi 0, t = univ in ℕ)
theorem c5_6 : ¬ drop0% Set.encard_sdiff' 3 := fun h => by
  have := h (s := Set.Ioi 0) (t := Set.univ)
  simp [eI, eU, dI, uI] at this

-- `Set.encard_eq_encard_iff_encard_sdiff_eq_encard_sdiff` idx 3: necessary (s = univ, t = Ioi 0 in ℕ)
theorem c5_7 : ¬ drop0% Set.encard_eq_encard_iff_encard_sdiff_eq_encard_sdiff 3 := fun h => by
  have := h (s := Set.univ) (t := Set.Ioi 0)
  simp [eI, eU, dI] at this

-- `Set.encard_eq_encard_iff_encard_diff_eq_encard_diff` idx 3: necessary (s = univ, t = Ioi 0 in ℕ)
theorem c5_8 : ¬ drop0% Set.encard_eq_encard_iff_encard_diff_eq_encard_diff 3 := fun h => by
  have := h (s := Set.univ) (t := Set.Ioi 0)
  simp [eI, eU, dI] at this

-- `Set.encard_le_encard_iff_encard_sdiff_le_encard_sdiff` idx 3: necessary (s = univ, t = Ioi 0 in ℕ)
theorem c5_9 : ¬ drop0% Set.encard_le_encard_iff_encard_sdiff_le_encard_sdiff 3 := fun h => by
  have := h (s := Set.univ) (t := Set.Ioi 0)
  simp [eI, eU, dI] at this

-- `Set.encard_le_encard_iff_encard_diff_le_encard_diff` idx 3: necessary (s = univ, t = Ioi 0 in ℕ)
theorem c5_10 : ¬ drop0% Set.encard_le_encard_iff_encard_diff_le_encard_diff 3 := fun h => by
  have := h (s := Set.univ) (t := Set.Ioi 0)
  simp [eI, eU, dI] at this

-- `Set.encard_lt_encard_iff_encard_sdiff_lt_encard_sdiff` idx 3: necessary (s = Ioi 0, t = univ in ℕ)
theorem c5_11 : ¬ drop0% Set.encard_lt_encard_iff_encard_sdiff_lt_encard_sdiff 3 := fun h => by
  have := h (s := Set.Ioi 0) (t := Set.univ)
  simp [eI, eU, dI] at this

-- `Set.encard_lt_encard_iff_encard_diff_lt_encard_diff` idx 3: necessary (s = Ioi 0, t = univ in ℕ)
theorem c5_12 : ¬ drop0% Set.encard_lt_encard_iff_encard_diff_lt_encard_diff 3 := fun h => by
  have := h (s := Set.Ioi 0) (t := Set.univ)
  simp [eI, eU, dI] at this

-- `Set.finite_iff_finite_of_encard_eq_encard` idx 3: necessary (s = ∅, t = univ in ℕ)
theorem c5_13 : ¬ drop0% Set.finite_iff_finite_of_encard_eq_encard 3 := fun h =>
  iN ((h (s := (∅ : Set ℕ)) (t := Set.univ)).1 Set.finite_empty)

-- `Set.infinite_iff_infinite_of_encard_eq_encard` idx 3: necessary (s = univ, t = ∅ in ℕ)
theorem c5_14 : ¬ drop0% Set.infinite_iff_infinite_of_encard_eq_encard 3 := fun h =>
  ((h (s := (Set.univ : Set ℕ)) (t := ∅)).1 iN) Set.finite_empty

-- `Set.Finite.finite_of_encard_le` idx 4: necessary (s = t = univ : Set ℕ)
theorem c5_15 : ¬ drop0% Set.Finite.finite_of_encard_le 4 := fun h =>
  iN (h (s := (Set.univ : Set ℕ)) (t := (Set.univ : Set ℕ)) le_rfl)

-- `Set.Finite.finite_of_encard_le` idx 5: necessary (s = ∅, t = univ in ℕ)
theorem c5_16 : ¬ drop0% Set.Finite.finite_of_encard_le 5 := fun h =>
  iN (h (s := (∅ : Set ℕ)) (t := (Set.univ : Set ℕ)) Set.finite_empty)

-- `Set.Finite.eq_of_subset_of_encard_le'` idx 3: necessary (s = Ioi 0 ⊂ t = univ in ℕ)
theorem c5_17 : ¬ drop0% Set.Finite.eq_of_subset_of_encard_le' 3 := fun h => by
  have := h (s := Set.Ioi 0) (t := Set.univ) (Set.subset_univ _) (by simp [eI, eU])
  have h0 : (0 : ℕ) ∈ Set.Ioi 0 := this ▸ Set.mem_univ 0
  simp at h0

-- `Set.Finite.eq_of_subset_of_encard_le` idx 3: necessary (s = Ioi 0 ⊂ t = univ in ℕ)
theorem c5_18 : ¬ drop0% Set.Finite.eq_of_subset_of_encard_le 3 := fun h => by
  have := h (s := Set.Ioi 0) (t := Set.univ) (Set.subset_univ _) (by simp [eI, eU])
  have h0 : (0 : ℕ) ∈ Set.Ioi 0 := this ▸ Set.mem_univ 0
  simp at h0

-- `Set.Finite.encard_lt_encard` idx 3: necessary (Ioi 0 ⊂ univ in ℕ, both encard ⊤)
theorem c5_19 : ¬ drop0% Set.Finite.encard_lt_encard 3 := fun h => by
  have := h (s := Set.Ioi 0) (t := Set.univ) (Set.ssubset_univ_iff.2 Ine)
  simp [eI, eU] at this

-- `Set.encard_strictMono` idx 1: necessary (Ioi 0 ⊂ univ in ℕ, both encard ⊤)
theorem c5_20 : ¬ drop0% Set.encard_strictMono 1 := fun h => by
  have := @h ℕ (Set.Ioi 0) Set.univ (Set.ssubset_univ_iff.2 Ine)
  simp [eI, eU] at this

-- `Set.Finite.encard_lt_card` idx 2: necessary (s = Ioi 0 in ℕ: ⊤ < ⊤)
theorem c5_21 : ¬ drop0% Set.Finite.encard_lt_card 2 := fun h => by
  have := h (s := Set.Ioi 0) Ine
  simp [eI] at this

-- `Set.Finite.encard_lt_card` idx 3: necessary (s = univ : Set Unit)
theorem c5_22 : ¬ drop0% Set.Finite.encard_lt_card 3 := fun h => by
  have := h (s := (Set.univ : Set Unit)) Set.finite_univ
  simp at this

-- `Set.encard_compl` idx 2: necessary (s = Ioi 0 in ℕ: 1 vs ⊤ - ⊤)
theorem c5_23 : ¬ drop0% Set.encard_compl 2 := fun h => by
  have := h (s := Set.Ioi 0)
  rw [cI, eI] at this; simp at this

-- `Set.encard_exchange` idx 4: necessary (s = {0, 1}, a = 0, b = 1)
theorem c5_24 : ¬ drop0% Set.encard_exchange 4 := fun h => by
  have := h (s := ({0, 1} : Set ℕ)) (a := 0) (b := 1) (by simp)
  have e : insert 0 (({0, 1} : Set ℕ) \ {1}) = {0} := by ext n; simp; try omega
  rw [e, Set.encard_pair (by decide)] at this; simp at this

-- `Set.encard_exchange'` idx 4: necessary (s = {0, 1}, a = 0, b = 1)
theorem c5_25 : ¬ drop0% Set.encard_exchange' 4 := fun h => by
  have := h (s := ({0, 1} : Set ℕ)) (a := 0) (b := 1) (by simp)
  have e : insert 0 ({0, 1} : Set ℕ) \ {1} = {0} := by ext n; simp; try omega
  rw [e, Set.encard_pair (by decide)] at this; simp at this

-- `Set.encard_exchange'` idx 5: necessary (s = ∅, a = 0, b = 1)
theorem c5_26 : ¬ drop0% Set.encard_exchange' 5 := fun h => by
  have := h (s := (∅ : Set ℕ)) (a := 0) (b := 1) (by simp)
  have e : insert 0 (∅ : Set ℕ) \ {1} = {0} := by ext n; simp; try omega
  rw [e] at this; simp at this

-- `Set.Finite.eq_insert_of_subset_of_encard_eq_succ` idx 3: necessary (s = Ioi 1, t = univ in ℕ)
theorem c5_27 : ¬ drop0% Set.Finite.eq_insert_of_subset_of_encard_eq_succ 3 := fun h => by
  obtain ⟨a, ha⟩ := h (s := Set.Ioi 1) (t := Set.univ) (Set.subset_univ _)
    (by rw [(Set.Ioi_infinite 1).encard_eq, eU]; rfl)
  have h0 : (0 : ℕ) ∈ insert a (Set.Ioi 1) := ha ▸ Set.mem_univ 0
  have h1 : (1 : ℕ) ∈ insert a (Set.Ioi 1) := ha ▸ Set.mem_univ 1
  simp at h0 h1; omega

-- `Set.Finite.eq_insert_of_subset_of_encard_eq_succ` idx 4: necessary (s = {0}, t = {1, 2})
theorem c5_28 : ¬ drop0% Set.Finite.eq_insert_of_subset_of_encard_eq_succ 4 := fun h => by
  obtain ⟨a, ha⟩ := h (s := ({0} : Set ℕ)) (t := {1, 2}) (Set.finite_singleton 0)
    (by rw [Set.encard_pair (by decide), eC]; rfl)
  have h0 : (0 : ℕ) ∈ ({1, 2} : Set ℕ) := ha ▸ by simp
  simp at h0

-- `Set.exists_superset_subset_encard_eq` idx 4: necessary (s = {0}, t = {1}, k = 1)
theorem c5_29 : ¬ drop0% Set.exists_superset_subset_encard_eq 4 := fun h => by
  obtain ⟨r, h1, h2, -⟩ := h (s := ({0} : Set ℕ)) (t := {1}) (k := 1) (by simp) (by simp)
  have := h2 (h1 (Set.mem_singleton 0)); simp at this

-- `Set.exists_superset_subset_encard_eq` idx 6: necessary (s = t = ∅, k = 1)
theorem c5_30 : ¬ drop0% Set.exists_superset_subset_encard_eq 6 := fun h => by
  obtain ⟨r, -, h2, h3⟩ := h (s := (∅ : Set ℕ)) (t := ∅) (k := 1) le_rfl (by simp)
  rw [Set.subset_empty_iff.1 h2] at h3; simp at h3

-- `Set.Finite.injOn_of_encard_image_eq` idx 4: necessary (s = univ : Set ℕ, f = pred)
theorem c5_31 : ¬ drop0% Set.Finite.injOn_of_encard_image_eq 4 := fun h =>
  pred_ni (h (s := Set.univ) (f := Nat.pred) (by rw [pred_img]))

-- `Set.Finite.injOn_of_encard_image_eq` idx 5: necessary (s = univ : Set Bool, f constant)
theorem c5_32 : ¬ drop0% Set.Finite.injOn_of_encard_image_eq 5 := fun h =>
  const_ni () (h (s := Set.univ) (f := fun _ : Bool => ()) Set.finite_univ)

-- `Set.encard_le_encard_of_injOn` idx 6: necessary (univ : Set Bool to univ : Set Unit)
theorem c5_33 : ¬ drop0% Set.encard_le_encard_of_injOn 6 := fun h => by
  have := h (s := (Set.univ : Set Bool)) (t := (Set.univ : Set Unit)) (f := fun _ => ()) (Set.mapsTo_univ _ _)
  rw [Set.encard_univ, Set.encard_univ] at this; simp at this

-- `Set.Finite.exists_injOn_of_encard_le` idx 2: necessary (s = ∅ : Set Unit, t = ∅ : Set Empty)
theorem c5_34 : ¬ drop0% Set.Finite.exists_injOn_of_encard_le 2 := fun h => by
  obtain ⟨f, -⟩ := h (s := (∅ : Set Unit)) (t := (∅ : Set Empty)) Set.finite_empty (by simp)
  exact (f ()).elim

-- `Set.Finite.exists_injOn_of_encard_le` idx 5: necessary (s = univ : Set ℝ, t = univ : Set ℕ)
theorem c5_35 : ¬ drop0% Set.Finite.exists_injOn_of_encard_le 5 := fun h => by
  obtain ⟨f, -, hf⟩ := h (s := (Set.univ : Set ℝ)) (t := (Set.univ : Set ℕ)) (by rw [eR, eU])
  exact noInj f hf

-- `Set.Finite.exists_bijOn_of_encard_eq` idx 4: necessary (s = ∅ : Set Unit, t = ∅ : Set Empty)
theorem c5_36 : ¬ drop0% Set.Finite.exists_bijOn_of_encard_eq 4 := fun h => by
  obtain ⟨f, -⟩ := h (s := (∅ : Set Unit)) (t := (∅ : Set Empty)) Set.finite_empty (by simp)
  exact (f ()).elim

-- `Set.Finite.exists_bijOn_of_encard_eq` idx 5: necessary (s = univ : Set ℝ, t = univ : Set ℕ)
theorem c5_37 : ¬ drop0% Set.Finite.exists_bijOn_of_encard_eq 5 := fun h => by
  obtain ⟨f, hf⟩ := h (s := (Set.univ : Set ℝ)) (t := (Set.univ : Set ℕ)) (by rw [eR, eU])
  exact noInj f hf.injOn

-- `Set.ncard_eq_toFinset_card` idx 2: necessary (s = univ : Set ℕ)
theorem c5_38 : ¬ indep0% Set.ncard_eq_toFinset_card 2 := fun h => iN (h Set.univ)

-- `Set.cast_ncard` idx 2: necessary (s = univ : Set ℕ: 0 vs ℵ₀)
theorem c5_39 : ¬ drop0% Set.cast_ncard 2 := fun h => by
  have := h (s := (Set.univ : Set ℕ))
  rw [nU, Cardinal.mk_univ, Cardinal.mk_nat] at this
  exact Cardinal.aleph0_ne_zero.{0} (by simpa using this.symm)

-- `Set.ncard_mono` idx 1: necessary ({0} ⊆ univ in ℕ: 1 ≤ 0)
theorem c5_40 : ¬ drop0% Set.ncard_mono 1 := fun h => by
  have := @h ℕ {0} Set.univ (Set.subset_univ _)
  simp only [nC, nU] at this; omega

-- `Set.finite_of_ncard_ne_zero` idx 2: necessary (s = univ : Set ℕ)
theorem c5_41 : ¬ drop0% Set.finite_of_ncard_ne_zero 2 := fun h => iN (h (s := Set.univ))

-- `Set.finite_of_ncard_pos` idx 2: necessary (s = univ : Set ℕ)
theorem c5_42 : ¬ drop0% Set.finite_of_ncard_pos 2 := fun h => iN (h (s := Set.univ))

open Classical in
-- `Set.ncard_insert_eq_ite` idx 4: necessary (s = Ioi 0, a = 0 in ℕ)
theorem c5_43 : ¬ drop0% Set.ncard_insert_eq_ite 4 := fun h => by
  have := h (s := Set.Ioi 0) (a := 0)
  rw [iU, nU, nI] at this; simp at this

-- `Set.ncard_sdiff_singleton_add_one` idx 4: necessary (s = univ, a = 0 in ℕ)
theorem c5_44 : ¬ drop0% Set.ncard_sdiff_singleton_add_one 4 := fun h => by
  have := h (s := Set.univ) (a := 0) (Set.mem_univ _)
  rw [d0, nU, nI] at this; simp at this

-- `Set.ncard_diff_singleton_add_one` idx 4: necessary (s = univ, a = 0 in ℕ)
theorem c5_45 : ¬ drop0% Set.ncard_diff_singleton_add_one 4 := fun h => by
  have := h (s := Set.univ) (a := 0) (Set.mem_univ _)
  rw [d0, nU, nI] at this; simp at this

-- `Set.ncard_sdiff_singleton_lt_of_mem` idx 4: necessary (s = univ, a = 0 in ℕ)
theorem c5_46 : ¬ drop0% Set.ncard_sdiff_singleton_lt_of_mem 4 := fun h => by
  have := h (s := Set.univ) (a := 0) (Set.mem_univ _)
  rw [d0, nU, nI] at this; simp at this

-- `Set.ncard_diff_singleton_lt_of_mem` idx 4: necessary (s = univ, a = 0 in ℕ)
theorem c5_47 : ¬ drop0% Set.ncard_diff_singleton_lt_of_mem 4 := fun h => by
  have := h (s := Set.univ) (a := 0) (Set.mem_univ _)
  rw [d0, nU, nI] at this; simp at this

-- `Set.ncard_exchange` idx 4: necessary (s = {0, 1}, a = 0, b = 1)
theorem c5_48 : ¬ drop0% Set.ncard_exchange 4 := fun h => by
  have := h (s := ({0, 1} : Set ℕ)) (a := 0) (b := 1) (by simp)
  have e : insert 0 (({0, 1} : Set ℕ) \ {1}) = {0} := by ext n; simp; try omega
  rw [e, Set.ncard_pair (by decide)] at this; simp at this

-- `Set.ncard_exchange'` idx 4: necessary (s = {0, 1}, a = 0, b = 1)
theorem c5_49 : ¬ drop0% Set.ncard_exchange' 4 := fun h => by
  have := h (s := ({0, 1} : Set ℕ)) (a := 0) (b := 1) (by simp)
  have e : insert 0 ({0, 1} : Set ℕ) \ {1} = {0} := by ext n; simp; try omega
  rw [e, Set.ncard_pair (by decide)] at this; simp at this

-- `Set.odd_card_insert_iff` idx 4: necessary (s = Ioi 0, a = 0 in ℕ)
theorem c5_50 : ¬ drop0% Set.odd_card_insert_iff 4 := fun h => by
  have := h (s := Set.Ioi 0) (a := 0) (by simp)
  rw [iU, nU, nI] at this; simp at this

-- `Set.ncard_image2_le` idx 6: necessary (s = univ : Set ℕ, t = {0}, f constant 0)
theorem c5_51 : ¬ drop0% Set.ncard_image2_le 6 := fun h => by
  have := h (f := fun (_ : ℕ) (_ : ℕ) => (0 : ℕ)) (s := Set.univ) (t := {0}) (Set.finite_singleton 0)
  have e : Set.image2 (fun (_ : ℕ) (_ : ℕ) => (0 : ℕ)) Set.univ {0} = {0} := by
    ext n; simp [eq_comm]
  rw [e, nU, nC] at this; simp at this

-- `Set.injOn_of_ncard_image_eq` idx 4: necessary (s = univ : Set Bool, f constant)
theorem c5_52 : ¬ drop0% Set.injOn_of_ncard_image_eq 4 := fun h =>
  const_ni () (h (s := Set.univ) (f := fun _ : Bool => ()) Set.finite_univ)

-- `Set.injOn_of_ncard_image_eq` idx 5: necessary (s = univ : Set ℕ, f = pred)
theorem c5_53 : ¬ drop0% Set.injOn_of_ncard_image_eq 5 := fun h =>
  pred_ni (h (s := Set.univ) (f := Nat.pred) (by rw [pred_img]))

-- `Set.ncard_image_iff` idx 4: necessary (s = univ : Set ℕ, f = pred)
theorem c5_54 : ¬ drop0% Set.ncard_image_iff 4 := fun h =>
  pred_ni ((h (s := Set.univ) (f := Nat.pred)).1 (by rw [pred_img]))

-- `Set.fiber_ncard_ne_zero_iff_mem_image` idx 5: necessary (s = univ : Set ℕ, f constant 0, y = 0)
theorem c5_55 : ¬ drop0% Set.fiber_ncard_ne_zero_iff_mem_image 5 := fun h => by
  have := (h (s := (Set.univ : Set ℕ)) (f := fun _ => (0 : ℕ)) (y := 0)).2 ⟨0, Set.mem_univ _, rfl⟩
  have e : {x | x ∈ (Set.univ : Set ℕ) ∧ (fun _ => (0 : ℕ)) x = 0} = Set.univ := by ext; simp
  rw [e, nU] at this; exact this rfl

-- `Set.map_eq_of_subset` idx 4: necessary (s = univ : Set ℕ, f = succ)
theorem c5_56 : ¬ drop0% Set.map_eq_of_subset 4 := fun h => by
  have := h (s := (Set.univ : Set ℕ)) (f := ⟨Nat.succ, Nat.succ_injective⟩) (Set.subset_univ _)
  rw [Set.eq_univ_iff_forall] at this
  obtain ⟨x, -, hx⟩ := this 0
  exact Nat.succ_ne_zero x hx

-- `Set.sep_of_ncard_eq` idx 6: necessary (s = univ : Set ℕ, P = (· ≠ 0), a = 0)
theorem c5_57 : ¬ drop0% Set.sep_of_ncard_eq 6 := fun h => by
  have e : {x | x ∈ (Set.univ : Set ℕ) ∧ x ≠ 0} = Set.Ioi 0 := by ext n; simp; try omega
  exact h (s := Set.univ) (P := fun x => x ≠ 0) (a := 0) (by rw [e, nI, nU]) (Set.mem_univ 0) rfl

-- `Set.ncard_strictMono` idx 1: necessary ({0} ⊂ univ in ℕ: 1 < 0)
theorem c5_58 : ¬ drop0% Set.ncard_strictMono 1 := fun h => by
  have := @h ℕ {0} Set.univ (Set.ssubset_univ_iff.2 (fun e => by
    have h1 : (1 : ℕ) ∈ ({0} : Set ℕ) := by rw [e]; exact Set.mem_univ 1
    simp at h1))
  simp only [nC, nU] at this; omega

-- `Set.ncard_eq_of_bijective` idx 4: necessary (s = univ : Set Bool, n = 1, f constant true)
theorem c5_59 : ¬ drop0% Set.ncard_eq_of_bijective 4 := fun h => by
  have := h (s := (Set.univ : Set Bool)) (n := 1) (fun _ _ => true) (fun _ _ => Set.mem_univ _)
    (fun i j hi hj _ => by omega)
  rw [Set.ncard_univ] at this; simp at this

-- `Set.ncard_eq_of_bijective` idx 5: necessary (s = ∅ : Set ℕ, n = 1, f constant 0)
theorem c5_60 : ¬ drop0% Set.ncard_eq_of_bijective 5 := fun h => by
  have := h (s := (∅ : Set ℕ)) (n := 1) (fun _ _ => 0) (fun a ha => ha.elim)
    (fun i j hi hj _ => by omega)
  simp at this

-- `Set.ncard_eq_of_bijective` idx 6: necessary (s = {0}, n = 2, f constant 0)
theorem c5_61 : ¬ drop0% Set.ncard_eq_of_bijective 6 := fun h => by
  have := h (s := ({0} : Set ℕ)) (n := 2) (fun _ _ => 0)
    (fun a ha => ⟨0, by omega, (Set.mem_singleton_iff.1 ha).symm⟩) (fun _ _ => Set.mem_singleton _)
  rw [nC] at this; simp at this

-- `Set.ncard_congr` idx 5: necessary (s = {0} : Set ℕ, t = ∅ : Set ℕ, f constant 0)
theorem c5_62 : ¬ drop0% Set.ncard_congr 5 := fun h => by
  have := h (s := ({0} : Set ℕ)) (t := (∅ : Set ℕ)) (fun _ _ => 0)
    (fun a b ha hb _ => by rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]) (fun b hb => hb.elim)
  rw [nC] at this; simp at this

-- `Set.ncard_congr` idx 6: necessary (univ : Set Bool onto univ : Set Unit)
theorem c5_63 : ¬ drop0% Set.ncard_congr 6 := fun h => by
  have := h (s := (Set.univ : Set Bool)) (t := (Set.univ : Set Unit)) (fun _ _ => ())
    (fun _ _ => Set.mem_univ _) (fun b _ => ⟨true, Set.mem_univ _, rfl⟩)
  rw [Set.ncard_univ, Set.ncard_univ] at this; simp at this

-- `Set.ncard_congr` idx 7: necessary (s = ∅ : Set Unit, t = univ : Set Unit)
theorem c5_64 : ¬ drop0% Set.ncard_congr 7 := fun h => by
  have := h (s := (∅ : Set Unit)) (t := (Set.univ : Set Unit)) (fun _ _ => ())
    (fun _ _ => Set.mem_univ _) (fun a b ha => ha.elim)
  rw [Set.ncard_univ] at this; simp at this

-- `Set.ncard_le_ncard_of_injOn` idx 6: necessary (univ : Set Bool to univ : Set Unit)
theorem c5_65 : ¬ drop0% Set.ncard_le_ncard_of_injOn 6 := fun h => by
  have := h (s := (Set.univ : Set Bool)) (t := (Set.univ : Set Unit)) (fun _ => ())
    (fun _ _ => Set.mem_univ _) Set.finite_univ
  rw [Set.ncard_univ, Set.ncard_univ] at this; simp at this

-- `Set.surj_on_of_inj_on_of_ncard_le` idx 5: necessary (s = univ : Set Unit, t = {0} : Set ℕ, f constant 1)
theorem c5_66 : ¬ drop0% Set.surj_on_of_inj_on_of_ncard_le 5 := fun h => by
  obtain ⟨a, ha, e⟩ := h (s := (Set.univ : Set Unit)) (t := ({0} : Set ℕ)) (fun _ _ => 1)
    (fun _ _ _ _ _ => rfl) (by rw [nC, Set.ncard_univ]; simp) (Set.finite_singleton 0) 0 (Set.mem_singleton 0)
  simp at e

-- `Set.surj_on_of_inj_on_of_ncard_le` idx 6: necessary (univ : Set Bool to itself, f constant true)
theorem c5_67 : ¬ drop0% Set.surj_on_of_inj_on_of_ncard_le 6 := fun h => by
  obtain ⟨a, ha, e⟩ := h (s := (Set.univ : Set Bool)) (t := (Set.univ : Set Bool)) (fun _ _ => true)
    (fun _ _ => Set.mem_univ _) le_rfl Set.finite_univ false (Set.mem_univ _)
  simp at e

-- `Set.surj_on_of_inj_on_of_ncard_le` idx 7: necessary (s = ∅, t = univ : Set Unit)
theorem c5_68 : ¬ drop0% Set.surj_on_of_inj_on_of_ncard_le 7 := fun h => by
  obtain ⟨a, ha, e⟩ := h (s := (∅ : Set Unit)) (t := (Set.univ : Set Unit)) (fun _ _ => ())
    (fun _ _ => Set.mem_univ _) (fun _ _ ha => ha.elim) Set.finite_univ () (Set.mem_univ _)
  exact ha

-- `Set.surj_on_of_inj_on_of_ncard_le` idx 8: necessary (s = ∅ : Set Unit, t = univ : Set ℕ)
theorem c5_69 : ¬ drop0% Set.surj_on_of_inj_on_of_ncard_le 8 := fun h => by
  obtain ⟨a, ha, e⟩ := h (s := (∅ : Set Unit)) (t := (Set.univ : Set ℕ)) (fun _ _ => 0)
    (fun _ _ => Set.mem_univ _) (fun _ _ ha => ha.elim) (by rw [nU]; simp) 0 (Set.mem_univ _)
  exact ha

-- `Set.surj_on_of_inj_on_of_ncard_le` idx 10: necessary (s = t = ∅ : Set Unit, b = ())
theorem c5_70 : ¬ drop0% Set.surj_on_of_inj_on_of_ncard_le 10 := fun h => by
  obtain ⟨a, ha, e⟩ := h (s := (∅ : Set Unit)) (t := (∅ : Set Unit)) (fun _ _ => ())
    (fun _ ha => ha.elim) (fun _ _ ha => ha.elim) le_rfl Set.finite_empty ()
  exact ha

-- `Set.inj_on_of_surj_on_of_ncard_le` idx 5: removable (the finite set of values {f a ha} contains t and can replace it, so the maps-to hypothesis is not needed)
theorem c5_71 : drop% Set.inj_on_of_surj_on_of_ncard_le 5 := by
  intro α β s t f hsurj hst a₁ ha₁ a₂ ha₂ he hs
  have ht' := hs.dependent_image f
  exact Set.inj_on_of_surj_on_of_ncard_le f (t := {y | ∃ x hx, f x hx = y}) (fun a ha => ⟨a, ha, rfl⟩)
    (fun b hb => hb) (hst.trans (Set.ncard_le_ncard (fun b hb => hsurj b hb) ht')) ha₁ ha₂ he hs

-- `Set.inj_on_of_surj_on_of_ncard_le` idx 6: necessary (univ : Set Bool to itself, f constant true)
theorem c5_72 : ¬ drop0% Set.inj_on_of_surj_on_of_ncard_le 6 := fun h => by
  have := h (s := (Set.univ : Set Bool)) (t := (Set.univ : Set Bool)) (fun _ _ => true)
    (fun _ _ => Set.mem_univ _) le_rfl (Set.mem_univ true) (Set.mem_univ false) rfl Set.finite_univ
  simp at this

-- `Set.inj_on_of_surj_on_of_ncard_le` idx 7: necessary (univ : Set Bool onto univ : Set Unit)
theorem c5_73 : ¬ drop0% Set.inj_on_of_surj_on_of_ncard_le 7 := fun h => by
  have := h (s := (Set.univ : Set Bool)) (t := (Set.univ : Set Unit)) (fun _ _ => ())
    (fun _ _ => Set.mem_univ _) (fun _ _ => ⟨true, Set.mem_univ _, rfl⟩) (Set.mem_univ true) (Set.mem_univ false)
    rfl Set.finite_univ
  simp at this

-- `Set.inj_on_of_surj_on_of_ncard_le` idx 9: necessary (s = t = {true}, f = id, a₁ = false)
theorem c5_74 : ¬ indep0% Set.inj_on_of_surj_on_of_ncard_le 9 := fun h => by
  have := h (s := ({true} : Set Bool)) (t := {true}) (fun a _ => a) (fun _ ha => ha) (fun b hb => ⟨b, hb, rfl⟩)
    le_rfl (a₁ := false) (a₂ := true) rfl (Set.finite_singleton _)
  simp at this

-- `Set.inj_on_of_surj_on_of_ncard_le` idx 11: necessary (s = t = {true}, f = id, a₂ = false)
theorem c5_75 : ¬ indep0% Set.inj_on_of_surj_on_of_ncard_le 11 := fun h => by
  have := h (s := ({true} : Set Bool)) (t := {true}) (fun a _ => a) (fun _ ha => ha) (fun b hb => ⟨b, hb, rfl⟩)
    le_rfl (a₁ := true) rfl (a₂ := false) (Set.finite_singleton _)
  simp at this

-- `Set.inj_on_of_surj_on_of_ncard_le` idx 12: necessary (s = t = univ : Set Bool, f = id, a₁ = true, a₂ = false)
theorem c5_76 : ¬ drop0% Set.inj_on_of_surj_on_of_ncard_le 12 := fun h => by
  have := h (s := (Set.univ : Set Bool)) (t := Set.univ) (fun a _ => a) (fun _ _ => Set.mem_univ _)
    (fun b _ => ⟨b, Set.mem_univ _, rfl⟩) le_rfl (Set.mem_univ true) (Set.mem_univ false) Set.finite_univ
  simp at this

-- `Set.inj_on_of_surj_on_of_ncard_le` idx 13: necessary (s = t = univ : Set ℕ, f = pred)
theorem c5_77 : ¬ drop0% Set.inj_on_of_surj_on_of_ncard_le 13 := fun h => by
  have := h (s := (Set.univ : Set ℕ)) (t := Set.univ) (fun a _ => Nat.pred a) (fun _ _ => Set.mem_univ _)
    (fun b _ => ⟨b + 1, Set.mem_univ _, rfl⟩) le_rfl (Set.mem_univ 0) (Set.mem_univ 1) rfl
  simp at this

-- `Set.ncard_powerset_ncard` idx 2: necessary (s = univ : Set ℕ, n = 0: infinitely many sets of ncard 0)
theorem c5_78 : ¬ drop0% Set.ncard_powerset_ncard 2 := fun h => by
  have := h (s := (Set.univ : Set ℕ)) 0
  rw [cofin_inf.ncard] at this; simp at this

-- `Set.ncard_union_add_ncard_inter` idx 3: necessary (s = Ioi 0, t = {0} in ℕ)
theorem c5_79 : ¬ drop0% Set.ncard_union_add_ncard_inter 3 := fun h => by
  have := h (Set.Ioi 0) {0} (Set.finite_singleton 0)
  rw [I0u, I0, nU, nI, nC] at this; simp at this

-- `Set.ncard_union_add_ncard_inter` idx 4: necessary (s = {0}, t = Ioi 0 in ℕ)
theorem c5_80 : ¬ drop0% Set.ncard_union_add_ncard_inter 4 := fun h => by
  have := h {0} (Set.Ioi 0) (Set.finite_singleton 0)
  rw [I0u', I0', nU, nI, nC] at this; simp at this

-- `Set.ncard_inter_add_ncard_union` idx 3: necessary (s = Ioi 0, t = {0} in ℕ)
theorem c5_81 : ¬ drop0% Set.ncard_inter_add_ncard_union 3 := fun h => by
  have := h (Set.Ioi 0) {0} (Set.finite_singleton 0)
  rw [I0u, I0, nU, nI, nC] at this; simp at this

-- `Set.ncard_inter_add_ncard_union` idx 4: necessary (s = {0}, t = Ioi 0 in ℕ)
theorem c5_82 : ¬ drop0% Set.ncard_inter_add_ncard_union 4 := fun h => by
  have := h {0} (Set.Ioi 0) (Set.finite_singleton 0)
  rw [I0u', I0', nU, nI, nC] at this; simp at this

-- `Set.ncard_union_eq` idx 4: necessary (s = Ioi 0, t = {0} in ℕ)
theorem c5_83 : ¬ drop0% Set.ncard_union_eq 4 := fun h => by
  have := h (s := Set.Ioi 0) (t := {0}) (Set.disjoint_iff_inter_eq_empty.2 I0) (Set.finite_singleton 0)
  rw [I0u, nU, nI, nC] at this; simp at this

-- `Set.ncard_union_eq_iff` idx 3: necessary (s = Ioi 0, t = {0} in ℕ)
theorem c5_84 : ¬ drop0% Set.ncard_union_eq_iff 3 := fun h => by
  have := (h (s := Set.Ioi 0) (t := {0}) (Set.finite_singleton 0)).2 (Set.disjoint_iff_inter_eq_empty.2 I0)
  rw [I0u, nU, nI, nC] at this; simp at this

-- `Set.ncard_union_eq_iff` idx 4: necessary (s = {0}, t = Ioi 0 in ℕ)
theorem c5_85 : ¬ drop0% Set.ncard_union_eq_iff 4 := fun h => by
  have := (h (s := {0}) (t := Set.Ioi 0) (Set.finite_singleton 0)).2 (Set.disjoint_iff_inter_eq_empty.2 I0')
  rw [I0u', nU, nI, nC] at this; simp at this

-- `Set.ncard_union_lt` idx 3: removable (if s is infinite, the union has ncard 0 while t, finite and meeting s, has positive ncard)
theorem c5_86 : drop% Set.ncard_union_lt 3 := by
  intro α s t ht hd
  by_cases hs : s.Finite
  · exact Set.ncard_union_lt hs ht hd
  · rw [(Set.Infinite.mono Set.subset_union_left hs).ncard, Set.Infinite.ncard hs, zero_add]
    exact (Set.ncard_pos ht).2 ((Set.not_disjoint_iff_nonempty_inter.1 hd).mono Set.inter_subset_right)

-- `Set.ncard_union_lt` idx 4: removable (if t is infinite, the union has ncard 0 while s, finite and meeting t, has positive ncard)
theorem c5_87 : drop% Set.ncard_union_lt 4 := by
  intro α s t hs hd
  by_cases ht : t.Finite
  · exact Set.ncard_union_lt hs ht hd
  · rw [(Set.Infinite.mono Set.subset_union_right ht).ncard, Set.Infinite.ncard ht, add_zero]
    exact (Set.ncard_pos hs).2 ((Set.not_disjoint_iff_nonempty_inter.1 hd).mono Set.inter_subset_left)

-- `Set.ncard_sdiff_add_ncard_of_subset` idx 4: necessary (s = {0}, t = univ in ℕ)
theorem c5_88 : ¬ drop0% Set.ncard_sdiff_add_ncard_of_subset 4 := fun h => by
  have := h (s := {0}) (t := Set.univ) (Set.subset_univ _)
  rw [d0, nI, nC, nU] at this; simp at this

-- `Set.ncard_diff_add_ncard_of_subset` idx 4: necessary (s = {0}, t = univ in ℕ)
theorem c5_89 : ¬ drop0% Set.ncard_diff_add_ncard_of_subset 4 := fun h => by
  have := h (s := {0}) (t := Set.univ) (Set.subset_univ _)
  rw [d0, nI, nC, nU] at this; simp at this

-- `Set.ncard_sdiff'` idx 4: necessary (s = Ioi 0, t = univ in ℕ)
theorem c5_90 : ¬ drop0% Set.ncard_sdiff' 4 := fun h => by
  have := h (s := Set.Ioi 0) (t := Set.univ) (Set.subset_univ _)
  rw [dI, nI, nC, nU] at this; simp at this

-- `Set.ncard_diff'` idx 4: necessary (s = Ioi 0, t = univ in ℕ)
theorem c5_91 : ¬ drop0% Set.ncard_diff' 4 := fun h => by
  have := h (s := Set.Ioi 0) (t := Set.univ) (Set.subset_univ _)
  rw [dI, nI, nC, nU] at this; simp at this

-- `Set.ncard_sdiff` idx 4: necessary (s = Ioi 0, t = univ in ℕ)
theorem c5_92 : ¬ drop0% Set.ncard_sdiff 4 := fun h => by
  have := h (s := Set.Ioi 0) (t := Set.univ) (Set.subset_univ _)
  rw [dI, nI, nC, nU] at this; simp at this

-- `Set.ncard_diff` idx 4: necessary (s = Ioi 0, t = univ in ℕ)
theorem c5_93 : ¬ drop0% Set.ncard_diff 4 := fun h => by
  have := h (s := Set.Ioi 0) (t := Set.univ) (Set.subset_univ _)
  rw [dI, nI, nC, nU] at this; simp at this

-- `Set.cast_ncard_sdiff` idx 6: necessary (s = {0}, t = univ in ℕ, R = ℤ: 0 = 0 - 1)
theorem c5_94 : ¬ drop0% Set.cast_ncard_sdiff 6 := fun h => by
  have := h (s := {0}) (t := Set.univ) (R := ℤ) (Set.subset_univ _)
  rw [d0, nI, nC, nU] at this; simp at this

-- `Set.ncard_sdiff_add_ncard` idx 3: necessary (s = univ, t = {0} in ℕ)
theorem c5_95 : ¬ drop0% Set.ncard_sdiff_add_ncard 3 := fun h => by
  have := h Set.univ {0} (Set.finite_singleton 0)
  rw [d0, nI, nC, Set.univ_union, nU] at this; simp at this

-- `Set.ncard_sdiff_add_ncard` idx 4: necessary (s = {0}, t = Ioi 0 in ℕ)
theorem c5_96 : ¬ drop0% Set.ncard_sdiff_add_ncard 4 := fun h => by
  have := h {0} (Set.Ioi 0) (Set.finite_singleton 0)
  rw [d0I, nI, nC, I0u', nU] at this; simp at this

-- `Set.ncard_diff_add_ncard` idx 3: necessary (s = univ, t = {0} in ℕ)
theorem c5_97 : ¬ drop0% Set.ncard_diff_add_ncard 3 := fun h => by
  have := h Set.univ {0} (Set.finite_singleton 0)
  rw [d0, nI, nC, Set.univ_union, nU] at this; simp at this

-- `Set.ncard_diff_add_ncard` idx 4: necessary (s = {0}, t = Ioi 0 in ℕ)
theorem c5_98 : ¬ drop0% Set.ncard_diff_add_ncard 4 := fun h => by
  have := h {0} (Set.Ioi 0) (Set.finite_singleton 0)
  rw [d0I, nI, nC, I0u', nU] at this; simp at this

-- `Set.ncard_inter_add_ncard_sdiff_eq_ncard` idx 3: necessary (s = univ, t = {0} in ℕ)
theorem c5_99 : ¬ drop0% Set.ncard_inter_add_ncard_sdiff_eq_ncard 3 := fun h => by
  have := h Set.univ {0}
  rw [Set.univ_inter, d0, nI, nC, nU] at this; simp at this

-- `Set.ncard_inter_add_ncard_diff_eq_ncard` idx 3: necessary (s = univ, t = {0} in ℕ)
theorem c5_100 : ¬ drop0% Set.ncard_inter_add_ncard_diff_eq_ncard 3 := fun h => by
  have := h Set.univ {0}
  rw [Set.univ_inter, d0, nI, nC, nU] at this; simp at this

-- `Set.ncard_sdiff''` idx 3: necessary (s = Ioi 0, t = univ in ℕ)
theorem c5_101 : ¬ drop0% Set.ncard_sdiff'' 3 := fun h => by
  have := h (s := Set.Ioi 0) (t := Set.univ)
  rw [dI, uI, nI, nC, nU] at this; simp at this

-- `Set.ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff` idx 3: necessary (s = univ, t = {0} in ℕ)
theorem c5_102 : ¬ drop0% Set.ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff 3 := fun h => by
  have := (h (s := Set.univ) (t := {0}) (Set.finite_singleton 0)).2 (by rw [d0, nI, Set.diff_univ]; simp)
  rw [nU, nC] at this; simp at this

-- `Set.ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff` idx 4: necessary (s = {0}, t = univ in ℕ)
theorem c5_103 : ¬ drop0% Set.ncard_eq_ncard_iff_ncard_sdiff_eq_ncard_sdiff 4 := fun h => by
  have := (h (s := {0}) (t := Set.univ) (Set.finite_singleton 0)).2 (by rw [d0, nI, Set.diff_univ]; simp)
  rw [nU, nC] at this; simp at this

-- `Set.ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff` idx 3: necessary (s = univ, t = {0} in ℕ)
theorem c5_104 : ¬ drop0% Set.ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff 3 := fun h => by
  have := (h (s := Set.univ) (t := {0}) (Set.finite_singleton 0)).2 (by rw [d0, nI, Set.diff_univ]; simp)
  rw [nU, nC] at this; simp at this

-- `Set.ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff` idx 4: necessary (s = {0}, t = univ in ℕ)
theorem c5_105 : ¬ drop0% Set.ncard_eq_ncard_iff_ncard_diff_eq_ncard_diff 4 := fun h => by
  have := (h (s := {0}) (t := Set.univ) (Set.finite_singleton 0)).2 (by rw [d0, nI, Set.diff_univ]; simp)
  rw [nU, nC] at this; simp at this

-- `Set.ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff` idx 4: necessary (s = {0}, t = univ in ℕ)
theorem c5_106 : ¬ drop0% Set.ncard_le_ncard_iff_ncard_sdiff_le_ncard_sdiff 4 := fun h => by
  have := (h (s := {0}) (t := Set.univ) (Set.finite_singleton 0)).2 (by rw [Set.diff_univ]; simp)
  rw [nU, nC] at this; simp at this

-- `Set.ncard_le_ncard_iff_ncard_diff_le_ncard_diff` idx 4: necessary (s = {0}, t = univ in ℕ)
theorem c5_107 : ¬ drop0% Set.ncard_le_ncard_iff_ncard_diff_le_ncard_diff 4 := fun h => by
  have := (h (s := {0}) (t := Set.univ) (Set.finite_singleton 0)).2 (by rw [Set.diff_univ]; simp)
  rw [nU, nC] at this; simp at this

-- `Set.ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff` idx 3: necessary (s = univ, t = {0} in ℕ)
theorem c5_108 : ¬ drop0% Set.ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff 3 := fun h => by
  have := (h (s := Set.univ) (t := {0}) (Set.finite_singleton 0)).1 (by rw [nU, nC]; decide)
  rw [d0, nI, Set.diff_univ] at this; simp at this

-- `Set.ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff` idx 4: removable (if t is infinite, t and t \ s both have ncard 0, so both sides are false)
theorem c5_109 : drop% Set.ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff 4 := by
  intro α s t hs
  by_cases ht : t.Finite
  · exact Set.ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff hs ht
  · rw [Set.Infinite.ncard ht, Set.Infinite.ncard (Set.Infinite.diff ht hs)]; simp

-- `Set.ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff` idx 3: necessary (s = univ, t = {0} in ℕ)
theorem c5_110 : ¬ drop0% Set.ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff 3 := fun h => by
  have := (h (s := Set.univ) (t := {0}) (Set.finite_singleton 0)).1 (by rw [nU, nC]; decide)
  rw [d0, nI, Set.diff_univ] at this; simp at this

-- `Set.ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff` idx 4: removable (if t is infinite, t and t \ s both have ncard 0, so both sides are false)
theorem c5_111 : drop% Set.ncard_lt_ncard_iff_ncard_diff_lt_ncard_diff 4 := by
  intro α s t hs
  by_cases ht : t.Finite
  · exact Set.ncard_lt_ncard_iff_ncard_sdiff_lt_ncard_sdiff hs ht
  · rw [Set.Infinite.ncard ht, Set.Infinite.ncard (Set.Infinite.diff ht hs)]; simp

-- `Set.ncard_add_ncard_compl` idx 2: necessary (s = Ioi 0 in ℕ: 0 + 1 vs Nat.card ℕ = 0)
theorem c5_112 : ¬ drop0% Set.ncard_add_ncard_compl 2 := fun h => by
  have := h (Set.Ioi 0) (by rw [cI]; exact Set.finite_singleton 0)
  rw [cI, nI, nC, Nat.card_eq_zero_of_infinite] at this; simp at this

-- `Set.ncard_compl_add_ncard` idx 2: necessary (s = Ioi 0 in ℕ)
theorem c5_113 : ¬ drop0% Set.ncard_compl_add_ncard 2 := fun h => by
  have := h (Set.Ioi 0) (by rw [cI]; exact Set.finite_singleton 0)
  rw [cI, nI, nC, Nat.card_eq_zero_of_infinite] at this; simp at this

-- `Set.ncard_compl` idx 2: necessary (s = Ioi 0 in ℕ: 1 vs 0 - 0)
theorem c5_114 : ¬ drop0% Set.ncard_compl 2 := fun h => by
  have := h (Set.Ioi 0)
  rw [cI, nI, nC, Nat.card_eq_zero_of_infinite] at this; simp at this

-- `Set.ncard_compl_of_ncard_eq_add` idx 4: necessary (s = Ioi 0 in ℕ, n = 0)
theorem c5_115 : ¬ drop0% Set.ncard_compl_of_ncard_eq_add 4 := fun h => by
  have := h (Set.Ioi 0) (n := 0) (by rw [nI, Nat.card_eq_zero_of_infinite])
  rw [cI, nC] at this; simp at this

-- `Set.eq_univ_iff_ncard` idx 1: necessary (s = ∅ in ℕ: both ncard 0)
theorem c5_116 : ¬ drop0% Set.eq_univ_iff_ncard 1 := fun h =>
  Set.empty_ne_univ ((h (∅ : Set ℕ)).2 (by rw [Set.ncard_empty, Nat.card_eq_zero_of_infinite]))

-- `Set.exists_subsuperset_card_eq` idx 4: necessary (s = {0}, t = {1}, n = 1)
theorem c5_117 : ¬ drop0% Set.exists_subsuperset_card_eq 4 := fun h => by
  obtain ⟨u, h1, h2, -⟩ := h (s := ({0} : Set ℕ)) (t := {1}) (n := 1) (by simp) (by simp)
  have := h2 (h1 (Set.mem_singleton 0)); simp at this

-- `Set.exists_subsuperset_card_eq` idx 5: necessary (s = t = {0}, n = 0)
theorem c5_118 : ¬ drop0% Set.exists_subsuperset_card_eq 5 := fun h => by
  obtain ⟨u, h1, h2, h3⟩ := h (s := ({0} : Set ℕ)) (t := {0}) (n := 0) subset_rfl (Nat.zero_le _)
  rw [Set.Subset.antisymm h2 h1, nC] at h3; simp at h3

-- `Set.Infinite.exists_superset_ncard_eq` idx 3: necessary (s = t = ∅, k = 1)
theorem c5_119 : ¬ drop0% Set.Infinite.exists_superset_ncard_eq 3 := fun h => by
  obtain ⟨u, -, -, h2, h3⟩ := h (s := (∅ : Set ℕ)) (t := ∅) subset_rfl Set.finite_empty (k := 1) (by simp)
  rw [Set.subset_empty_iff.1 h2] at h3; simp at h3

-- `Set.Infinite.exists_superset_ncard_eq` idx 4: necessary (s = {0}, t = Ioi 0, k = 1)
theorem c5_120 : ¬ drop0% Set.Infinite.exists_superset_ncard_eq 4 := fun h => by
  obtain ⟨u, -, h1, h2, -⟩ := h (s := ({0} : Set ℕ)) (t := Set.Ioi 0) iI (Set.finite_singleton 0) (k := 1) (by simp)
  have := h2 (h1 (Set.mem_singleton 0)); simp at this

-- `Set.Infinite.exists_superset_ncard_eq` idx 5: necessary (s = t = univ : Set ℕ, k = 0)
theorem c5_121 : ¬ drop0% Set.Infinite.exists_superset_ncard_eq 5 := fun h => by
  obtain ⟨u, hu, h1, -, -⟩ := h (s := (Set.univ : Set ℕ)) (t := Set.univ) iN subset_rfl (k := 0) (by simp)
  exact iN (hu.subset h1)

-- `Set.Infinite.exists_superset_ncard_eq` idx 7: necessary (s = {0}, t = univ : Set ℕ, k = 0)
theorem c5_122 : ¬ drop0% Set.Infinite.exists_superset_ncard_eq 7 := fun h => by
  obtain ⟨u, hu, h1, -, h3⟩ := h (s := ({0} : Set ℕ)) (t := Set.univ) iN (Set.subset_univ _)
    (Set.finite_singleton 0) (k := 0)
  have := (Set.ncard_pos hu).2 ⟨0, h1 (Set.mem_singleton 0)⟩; omega

-- `Set.exists_superset_ncard_eq` idx 2: necessary (α = Unit, s = ∅, k = 2)
theorem c5_123 : ¬ drop0% Set.exists_superset_ncard_eq 2 := fun h => by
  obtain ⟨t, -, -, h3⟩ := h (s := (∅ : Set Unit)) (k := 2) Set.finite_empty (by simp)
  have := Set.ncard_le_ncard (Set.subset_univ t) Set.finite_univ
  rw [Set.ncard_univ, Nat.card_unique] at this; omega

-- `Set.exists_superset_ncard_eq` idx 4: necessary (s = univ : Set ℕ, k = 0)
theorem c5_124 : ¬ drop0% Set.exists_superset_ncard_eq 4 := fun h => by
  obtain ⟨t, ht, h1, -⟩ := h (s := (Set.univ : Set ℕ)) (k := 0) (by simp)
  exact iN (ht.subset h1)

-- `Set.exists_superset_ncard_eq` idx 5: necessary (s = {0} : Set ℕ, k = 0)
theorem c5_125 : ¬ drop0% Set.exists_superset_ncard_eq 5 := fun h => by
  obtain ⟨t, ht, h1, h3⟩ := h (s := ({0} : Set ℕ)) (k := 0) (Set.finite_singleton 0)
  have := (Set.ncard_pos ht).2 ⟨0, h1 (Set.mem_singleton 0)⟩; omega

-- `Set.exists_ncard_eq` idx 1: necessary (α = Unit, k = 2)
theorem c5_126 : ¬ drop0% Set.exists_ncard_eq 1 := fun h => by
  obtain ⟨t, -, h3⟩ := h Unit 2
  have := Set.ncard_le_ncard (Set.subset_univ t) Set.finite_univ
  rw [Set.ncard_univ, Nat.card_unique] at this; omega

-- `Set.exists_subset_or_subset_of_two_mul_lt_ncard` idx 4: necessary (s = t = ∅, n = 0)
theorem c5_127 : ¬ drop0% Set.exists_subset_or_subset_of_two_mul_lt_ncard 4 := fun h => by
  obtain ⟨r, h1, h2⟩ := h (s := (∅ : Set ℕ)) (t := ∅) (n := 0)
  rw [or_self, Set.subset_empty_iff] at h2; rw [h2] at h1; simp at h1

-- `Set.exists_eq_insert_iff_ncard` idx 3: necessary (s = Ioi 0, t = univ in ℕ)
theorem c5_128 : ¬ drop0% Set.exists_eq_insert_iff_ncard 3 := fun h => by
  have := ((h (s := Set.Ioi 0) (t := Set.univ)).1 ⟨0, by simp, iU⟩).2
  rw [nI, nU] at this; simp at this

-- `Set.ncard_le_one` idx 2: necessary (s = univ : Set ℕ)
theorem c5_129 : ¬ drop0% Set.ncard_le_one 2 := fun h => by
  have := (h (s := (Set.univ : Set ℕ))).1 (by rw [nU]; omega) 0 (Set.mem_univ _) 1 (Set.mem_univ _)
  simp at this

-- `Set.ncard_le_one_iff_subsingleton` idx 2: necessary (s = univ : Set ℕ)
theorem c5_130 : ¬ drop0% Set.ncard_le_one_iff_subsingleton 2 := fun h => by
  have := (h (s := (Set.univ : Set ℕ))).1 (by rw [nU]; omega) (Set.mem_univ 0) (Set.mem_univ 1)
  simp at this

-- `Set.ncard_le_one_iff` idx 2: necessary (s = univ : Set ℕ)
theorem c5_131 : ¬ drop0% Set.ncard_le_one_iff 2 := fun h => by
  have := (h (s := (Set.univ : Set ℕ))).1 (by rw [nU]; omega) (Set.mem_univ 0) (Set.mem_univ 1)
  simp at this

-- `Set.ncard_le_one_iff_eq` idx 2: necessary (s = univ : Set ℕ)
theorem c5_132 : ¬ drop0% Set.ncard_le_one_iff_eq 2 := fun h => by
  rcases (h (s := (Set.univ : Set ℕ))).1 (by rw [nU]; omega) with e | ⟨a, e⟩
  · exact Set.univ_nonempty.ne_empty e
  · have := e ▸ Set.mem_univ (a + 1); simp at this

-- `Set.ncard_le_one_iff_subset_singleton` idx 2: necessary (α = Empty, s = ∅)
theorem c5_133 : ¬ drop0% Set.ncard_le_one_iff_subset_singleton 2 := fun h => by
  obtain ⟨x, -⟩ := (h (s := (∅ : Set Empty)) Set.finite_empty).1 (by simp)
  exact x.elim

-- `Set.ncard_le_one_iff_subset_singleton` idx 3: necessary (s = univ : Set ℕ)
theorem c5_134 : ¬ drop0% Set.ncard_le_one_iff_subset_singleton 3 := fun h => by
  obtain ⟨x, hx⟩ := (h (s := (Set.univ : Set ℕ))).1 (by rw [nU]; omega)
  have := hx (Set.mem_univ (x + 1)); simp at this

-- `Set.one_lt_ncard_iff_nontrivial` idx 2: necessary (s = univ : Set ℕ)
theorem c5_135 : ¬ drop0% Set.one_lt_ncard_iff_nontrivial 2 := fun h => by
  have := (h (s := (Set.univ : Set ℕ))).2 ⟨0, Set.mem_univ _, 1, Set.mem_univ _, by decide⟩
  rw [nU] at this; omega

-- `Set.one_lt_ncard` idx 2: necessary (s = univ : Set ℕ)
theorem c5_136 : ¬ drop0% Set.one_lt_ncard 2 := fun h => by
  have := (h (s := (Set.univ : Set ℕ))).2 ⟨0, Set.mem_univ _, 1, Set.mem_univ _, by decide⟩
  rw [nU] at this; omega

-- `Set.one_lt_ncard_iff` idx 2: necessary (s = univ : Set ℕ)
theorem c5_137 : ¬ drop0% Set.one_lt_ncard_iff 2 := fun h => by
  have := (h (s := (Set.univ : Set ℕ))).2 ⟨0, 1, Set.mem_univ _, Set.mem_univ _, by decide⟩
  rw [nU] at this; omega

-- `Set.two_lt_ncard_iff` idx 2: necessary (s = univ : Set ℕ)
theorem c5_138 : ¬ drop0% Set.two_lt_ncard_iff 2 := fun h => by
  have := (h (s := (Set.univ : Set ℕ))).2
    ⟨0, 1, 2, Set.mem_univ _, Set.mem_univ _, Set.mem_univ _, by decide, by decide, by decide⟩
  rw [nU] at this; omega

-- `Set.two_lt_ncard` idx 2: necessary (s = univ : Set ℕ)
theorem c5_139 : ¬ drop0% Set.two_lt_ncard 2 := fun h => by
  have := (h (s := (Set.univ : Set ℕ))).2
    ⟨0, Set.mem_univ _, 1, Set.mem_univ _, 2, Set.mem_univ _, by decide, by decide, by decide⟩
  rw [nU] at this; omega

-- `Set.three_lt_ncard_iff` idx 2: necessary (s = univ : Set ℕ)
theorem c5_140 : ¬ drop0% Set.three_lt_ncard_iff 2 := fun h => by
  have := (h (s := (Set.univ : Set ℕ))).2
    ⟨0, 1, 2, 3, Set.mem_univ _, Set.mem_univ _, Set.mem_univ _, Set.mem_univ _,
      by decide, by decide, by decide, by decide, by decide, by decide⟩
  rw [nU] at this; omega

-- `Set.three_lt_ncard` idx 2: necessary (s = univ : Set ℕ)
theorem c5_141 : ¬ drop0% Set.three_lt_ncard 2 := fun h => by
  have := (h (s := (Set.univ : Set ℕ))).2
    ⟨0, Set.mem_univ _, 1, Set.mem_univ _, 2, Set.mem_univ _, 3, Set.mem_univ _,
      by decide, by decide, by decide, by decide, by decide, by decide⟩
  rw [nU] at this; omega

-- `Set.eq_insert_of_ncard_eq_succ` idx 3: necessary (s = ∅, n = 0)
theorem c5_142 : ¬ drop0% Set.eq_insert_of_ncard_eq_succ 3 := fun h => by
  obtain ⟨a, t, -, e, -⟩ := h (s := (∅ : Set ℕ)) (n := 0)
  exact (Set.insert_nonempty a t).ne_empty e

-- `Set.ncard_eq_succ` idx 3: necessary (s = univ : Set ℕ, n = 0)
theorem c5_143 : ¬ drop0% Set.ncard_eq_succ 3 := fun h => by
  have := (h (s := (Set.univ : Set ℕ)) (n := 0)).2 ⟨0, Set.Ioi 0, by simp, iU, nI⟩
  rw [nU] at this; simp at this

-- `Function.Surjective.card_le_card_add_one_iff` idx 2: necessary (f = (· / 2) on ℕ)
theorem c5_144 : ¬ drop0% Function.Surjective.card_le_card_add_one_iff 2 := fun h => by
  have := (h (f := fun n : ℕ => n / 2) (fun m => ⟨2 * m, show 2 * m / 2 = m by omega⟩)).1
    (by rw [Nat.card_eq_zero_of_infinite]; omega) 0 1 2 3 rfl rfl (by decide) (by decide)
  have h0 : (0 : ℕ) ∈ ({2, 3} : Set ℕ) := this ▸ by simp
  simp at h0

-- `Function.Surjective.card_le_card_add_one_iff` idx 4: necessary (f = Fin.val : Fin 3 → ℕ)
theorem c5_145 : ¬ drop0% Function.Surjective.card_le_card_add_one_iff 4 := fun h => by
  have := (h (f := fun i : Fin 3 => i.val)).2 (fun a b c d hab _ hne _ => absurd (Fin.ext hab) hne)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_zero_of_infinite] at this; simp at this

-- `Set.ncard_le_ncard_image_add_one_iff` idx 3: necessary (s = univ : Set ℕ, f = (· / 2))
theorem c5_146 : ¬ drop0% Set.ncard_le_ncard_image_add_one_iff 3 := fun h => by
  have := (h (Set.univ : Set ℕ) (fun n => n / 2)).1 (by rw [nU]; omega) 0 (Set.mem_univ _) 1 (Set.mem_univ _)
    2 (Set.mem_univ _) 3 (Set.mem_univ _) rfl rfl (by decide) (by decide)
  have h0 : (0 : ℕ) ∈ ({2, 3} : Set ℕ) := this ▸ by simp
  simp at h0

namespace W3c5
open Computation Stream'

-- helper: a computation whose first step is think reaches termination through that step
theorem parTerm {β : Type} {S : WSeq (Computation ℕ)} {f : β → ℕ ⊕ β} {x : β}
    (hC : destruct (parallel S) = Sum.inr (corec f x)) (T : Terminates (corec f x)) :
    Terminates (parallel S) := by
  rw [destruct_eq_think hC]; infer_instance
-- helper: parallel of the empty sequence has no value
theorem parNil (a : ℕ) : a ∉ parallel (WSeq.nil : WSeq (Computation ℕ)) := fun ha => by
  obtain ⟨c, hc, -⟩ := exists_of_mem_parallel ha
  exact WSeq.notMem_nil c hc
-- helper: parallel of the one-element sequence [empty] has no value
theorem parE (a : ℕ) : a ∉ parallel (WSeq.cons (empty ℕ) WSeq.nil) := fun ha => by
  obtain ⟨c, hc, hac⟩ := exists_of_mem_parallel ha
  rcases (WSeq.mem_cons_iff _ _).1 hc with rfl | hc
  · exact notMem_empty a hac
  · exact WSeq.notMem_nil c hc
-- helper: parallel of [pure 0] has value 0 and only 0
theorem parP0 : (0 : ℕ) ∈ parallel (WSeq.cons (Computation.pure 0) WSeq.nil) := by
  refine ⟨1, ?_⟩; rfl
theorem parP (a : ℕ) (ha : a ∈ parallel (WSeq.cons (Computation.pure 0) WSeq.nil)) : a = 0 :=
  mem_unique ha parP0
-- helper: two sequences that are elementwise equivalent but whose parallel values differ
def Sl : WSeq (Computation ℕ) := WSeq.cons (think (think (Computation.pure 0))) (WSeq.cons (Computation.pure 1) WSeq.nil)
def Sf : WSeq (Computation ℕ) := WSeq.cons (Computation.pure 0) (WSeq.cons (Computation.pure 1) WSeq.nil)
theorem Sl1 : (1 : ℕ) ∈ parallel Sl := by refine ⟨3, ?_⟩; rfl
theorem Sf0 : (0 : ℕ) ∈ parallel Sf := by refine ⟨2, ?_⟩; rfl
theorem SlSf : WSeq.LiftRel Computation.Equiv Sl Sf :=
  (WSeq.liftRel_cons _ _ _ _ _).2 ⟨(think_equiv _).trans (think_equiv _),
    (WSeq.liftRel_cons _ _ _ _ _).2 ⟨Computation.Equiv.refl _, WSeq.liftRel_nil _⟩⟩
theorem notEq : ¬ Computation.Equiv (parallel Sl) (parallel Sf) := fun e => by
  have := mem_unique ((e 1).1 Sl1) Sf0; simp at this

end W3c5

open Computation Stream' in
-- `Stream'.Seq.get?_mk` idx 2: necessary (f = none, some (), some (), …)
theorem c5_147 : ¬ indep0% Stream'.Seq.get?_mk 2 := fun h => by
  have := h (α := Unit) (fun n => if n = 0 then none else some ()) (n := 0) rfl
  simp at this

open Computation Stream' in
-- `Stream'.Seq.ge_stable` idx 5: necessary (s = [()], n = 0, m = 1)
theorem c5_148 : ¬ drop0% Stream'.Seq.ge_stable 5 := fun h => by
  obtain ⟨a, ha⟩ := h (Seq.cons () Seq.nil) (aₙ := ()) (n := 0) (m := 1) (by simp)
  simp at ha

open Computation Stream' in
-- `Stream'.Seq.corec_nil` idx 4: necessary (f = fun _ => some ((), ()))
theorem c5_149 : ¬ drop0% Stream'.Seq.corec_nil 4 := fun h => by
  have := h (fun (_ : Unit) => some ((), ())) ()
  rw [Seq.corec_cons (f := fun (_ : Unit) => some ((), ())) rfl] at this
  exact Seq.cons_ne_nil this

open Computation Stream' in
-- `Stream'.Seq.corec_cons` idx 6: necessary (f = fun _ => none)
theorem c5_150 : ¬ drop0% Stream'.Seq.corec_cons 6 := fun h => by
  have := h (f := fun (_ : Unit) => (none : Option (Unit × Unit))) (b := ()) (x := ()) (s := ())
  rw [Seq.corec_nil (f := fun (_ : Unit) => (none : Option (Unit × Unit))) (b := ()) rfl] at this
  exact Seq.cons_ne_nil this.symm

open Computation Stream' in
-- `Stream'.Seq.eq_of_bisim` idx 2: necessary (R = ⊤, s₁ = [()], s₂ = nil)
theorem c5_151 : ¬ drop0% Stream'.Seq.eq_of_bisim 2 := fun h =>
  Seq.cons_ne_nil (h (fun _ _ => True) (s₁ := Seq.cons () Seq.nil) (s₂ := Seq.nil) trivial)

open Computation Stream' in
-- `Stream'.Seq.eq_of_bisim` idx 5: necessary (R = ⊥ is a bisimulation, s₁ = [()], s₂ = nil)
theorem c5_152 : ¬ drop0% Stream'.Seq.eq_of_bisim 5 := fun h =>
  Seq.cons_ne_nil (h (fun _ _ => False) (by intro _ _ h; exact h.elim) (s₁ := Seq.cons () Seq.nil) (s₂ := Seq.nil))

open Computation Stream' in
-- `Stream'.Seq.eq_of_bisim'` idx 4: necessary (motive = ⊥, s₁ = [()], s₂ = nil)
theorem c5_153 : ¬ drop0% Stream'.Seq.eq_of_bisim' 4 := fun h =>
  Seq.cons_ne_nil (h (s₁ := Seq.cons () Seq.nil) (s₂ := Seq.nil) (fun _ _ => False) (by intro _ _ h; exact h.elim))

open Computation Stream' in
-- `Stream'.Seq.eq_of_bisim'` idx 5: necessary (motive = ⊤, s₁ = [()], s₂ = nil)
theorem c5_154 : ¬ drop0% Stream'.Seq.eq_of_bisim' 5 := fun h =>
  Seq.cons_ne_nil (h (s₁ := Seq.cons () Seq.nil) (s₂ := Seq.nil) (fun _ _ => True) trivial)

open Computation Stream' in
-- `Stream'.Seq.eq_of_bisim_strong` idx 4: necessary (motive = ⊥, s₁ = [()], s₂ = nil)
theorem c5_155 : ¬ drop0% Stream'.Seq.eq_of_bisim_strong 4 := fun h =>
  Seq.cons_ne_nil (h (s₁ := Seq.cons () Seq.nil) (s₂ := Seq.nil) (fun _ _ => False) (by intro _ _ h; exact h.elim))

open Computation Stream' in
-- `Stream'.Seq.eq_of_bisim_strong` idx 5: necessary (motive = ⊤, s₁ = [()], s₂ = nil)
theorem c5_156 : ¬ drop0% Stream'.Seq.eq_of_bisim_strong 5 := fun h =>
  Seq.cons_ne_nil (h (s₁ := Seq.cons () Seq.nil) (s₂ := Seq.nil) (fun _ _ => True) trivial)

open Computation Stream' in
-- `Stream'.Seq.mem_rec_on` idx 5: necessary (C = ⊥, s = [()])
theorem c5_157 : ¬ drop0% Stream'.Seq.mem_rec_on 5 := fun h =>
  h (C := fun _ => False) (Seq.mem_cons () Seq.nil)

open Computation Stream' in
-- `_private.Mathlib.Data.Seq.Parallel.0.Computation.terminates_parallel.aux` idx 4: necessary (l = [], S = nil: the state of parallel nil)
theorem c5_158 : ¬ drop0% _private.Mathlib.Data.Seq.Parallel.«0».Computation.terminates_parallel.aux 4 := fun h => by
  have T := h (l := []) (S := (WSeq.nil : WSeq (Computation ℕ))) (c := Computation.pure 0) (ret_terminates 0)
  have P : Terminates (parallel (WSeq.nil : WSeq (Computation ℕ))) := T
  obtain ⟨a, ha⟩ := P.term
  exact parNil a ha

open Computation Stream' in
-- `_private.Mathlib.Data.Seq.Parallel.0.Computation.terminates_parallel.aux` idx 5: necessary (l = [empty], S = nil: the state after one step of parallel [empty])
theorem c5_159 : ¬ drop0% _private.Mathlib.Data.Seq.Parallel.«0».Computation.terminates_parallel.aux 5 := fun h => by
  have T := h (l := [empty ℕ]) (S := (WSeq.nil : WSeq (Computation ℕ))) (c := empty ℕ) (List.mem_singleton_self _)
  have P := parTerm (S := WSeq.cons (empty ℕ) WSeq.nil) (by rw [Computation.parallel, Computation.corec_eq]; rfl) T
  obtain ⟨a, ha⟩ := P.term
  exact parE a ha

open Computation Stream' in
-- `Computation.terminates_parallel` idx 3: necessary (S = nil, c = pure 0)
theorem c5_160 : ¬ drop0% Computation.terminates_parallel 3 := fun h => by
  obtain ⟨a, ha⟩ := (h (S := (WSeq.nil : WSeq (Computation ℕ))) (c := Computation.pure 0)).term
  exact parNil a ha

open Computation Stream' in
-- `Computation.terminates_parallel` idx 4: necessary (S = [empty], c = empty)
theorem c5_161 : ¬ drop0% Computation.terminates_parallel 4 := fun h => by
  obtain ⟨a, ha⟩ := (h (S := WSeq.cons (empty ℕ) WSeq.nil) (c := empty ℕ) (WSeq.mem_cons _ _)).term
  exact parE a ha

open Computation Stream' in
-- `Computation.exists_of_mem_parallel` idx 3: necessary (S = nil)
theorem c5_162 : ¬ drop0% Computation.exists_of_mem_parallel 3 := fun h => by
  obtain ⟨c, hc, -⟩ := h (S := (WSeq.nil : WSeq (Computation ℕ))) (a := 0)
  exact WSeq.notMem_nil c hc

open Computation Stream' in
-- `Computation.parallel_empty` idx 2: necessary (S = [pure 0])
theorem c5_163 : ¬ drop0% Computation.parallel_empty 2 := fun h => by
  have := parP0; rw [h] at this; exact notMem_empty 0 this

open Computation Stream' in
-- `Computation.parallel_promises` idx 3: necessary (S = [pure 0], a = 1)
theorem c5_164 : ¬ drop0% Computation.parallel_promises 3 := fun h => by
  have := h (S := WSeq.cons (Computation.pure 0) WSeq.nil) (a := 1) parP0; simp at this

open Computation Stream' in
-- `Computation.mem_parallel` idx 3: necessary (S = [pure 0, pure 1]: 0 and 1 would both be values)
theorem c5_165 : ¬ drop0% Computation.mem_parallel 3 := fun h => by
  have h1 := h (S := W3c5.Sf) (c := Computation.pure 1)
    ((WSeq.mem_cons_iff _ _).2 (Or.inr (WSeq.mem_cons _ _))) (ret_mem 1)
  have := mem_unique h1 W3c5.Sf0; simp at this

open Computation Stream' in
-- `Computation.mem_parallel` idx 5: necessary (S = nil, c = pure 0, a = 0)
theorem c5_166 : ¬ drop0% Computation.mem_parallel 5 := fun h =>
  parNil 0 (h (S := WSeq.nil) (a := 0) (fun s hs => (WSeq.notMem_nil s hs).elim) (c := Computation.pure 0) (ret_mem 0))

open Computation Stream' in
-- `Computation.mem_parallel` idx 6: necessary (S = [empty], c = empty, a = 0)
theorem c5_167 : ¬ drop0% Computation.mem_parallel 6 := fun h => by
  refine parE 0 (h (S := WSeq.cons (empty ℕ) WSeq.nil) (a := 0) ?_ (c := empty ℕ) (WSeq.mem_cons _ _))
  intro s hs
  rcases (WSeq.mem_cons_iff _ _).1 hs with rfl | hs
  · exact fun a ha => (notMem_empty a ha).elim
  · exact (WSeq.notMem_nil s hs).elim

open Computation Stream' in
-- `Computation.parallel_congr_lem` idx 4: necessary (S = nil, T = [pure 1], a = 0)
theorem c5_168 : ¬ drop0% Computation.parallel_congr_lem 4 := fun h => by
  have := (h (S := WSeq.nil) (T := WSeq.cons (Computation.pure 1) WSeq.nil) (a := 0)).1
    (fun s hs => (WSeq.notMem_nil s hs).elim) _ (WSeq.mem_cons _ _) (ret_mem 1)
  simp at this

open Computation Stream' in
-- `Computation.parallel_congr_left` idx 4: necessary (S = [think (think (pure 0)), pure 1], T = [pure 0, pure 1]: parallel values 1 and 0)
theorem c5_169 : ¬ drop0% Computation.parallel_congr_left 4 := fun h =>
  W3c5.notEq (h (a := 0) W3c5.SlSf)

open Computation Stream' in
-- `Computation.parallel_congr_left` idx 5: necessary (S = nil, T = [pure 0])
theorem c5_170 : ¬ drop0% Computation.parallel_congr_left 5 := fun h =>
  parNil 0 ((h (S := WSeq.nil) (T := WSeq.cons (Computation.pure 0) WSeq.nil) (a := 0)
    (fun s hs => (WSeq.notMem_nil s hs).elim) 0).2 parP0)

open Computation Stream' in
-- `Computation.parallel_congr_right` idx 4: necessary (S = [think (think (pure 0)), pure 1], T = [pure 0, pure 1]: parallel values 1 and 0)
theorem c5_171 : ¬ drop0% Computation.parallel_congr_right 4 := fun h =>
  W3c5.notEq (h (a := 0) W3c5.SlSf)

open Computation Stream' in
-- `Computation.parallel_congr_right` idx 5: necessary (S = [pure 0], T = nil)
theorem c5_172 : ¬ drop0% Computation.parallel_congr_right 5 := fun h =>
  parNil 0 ((h (S := WSeq.cons (Computation.pure 0) WSeq.nil) (T := WSeq.nil) (a := 0)
    (fun s hs => (WSeq.notMem_nil s hs).elim) 0).1 parP0)

-- `Set.PiSetCoe.canLift` idx 2: necessary (ι = Bool, α false = Empty, α true = Unit, s = {true})
theorem c5_173 : ¬ drop0% Set.PiSetCoe.canLift 2 := fun h => by
  obtain ⟨y, -⟩ := (h Bool (fun b => cond b Unit Empty) {true}).prf
    (fun i => by obtain ⟨i, hi⟩ := i; obtain rfl := Set.mem_singleton_iff.1 hi; exact ()) trivial
  exact (y false).elim

-- `Set.PiSetCoe.canLift'` idx 2: necessary (ι = Unit, α = Empty, s = ∅)
theorem c5_174 : ¬ drop0% Set.PiSetCoe.canLift' 2 := fun h => by
  obtain ⟨y, -⟩ := (h Unit Empty ∅).prf (fun i => i.2.elim) trivial
  exact (y ()).elim

-- `SetCoe.ext` idx 4: necessary (two different points of univ : Set Bool)
theorem c5_175 : ¬ drop0% SetCoe.ext 4 := fun h =>
  absurd (congrArg Subtype.val (h (s := (Set.univ : Set Bool)) (a := ⟨true, trivial⟩) (b := ⟨false, trivial⟩)))
    (by decide)

-- `Set.eq_or_ssubset_of_subset` idx 3: necessary (s = {true}, t = ∅)
theorem c5_176 : ¬ drop0% Set.eq_or_ssubset_of_subset 3 := fun h => by
  rcases h (s := ({true} : Set Bool)) (t := ∅) with e | e
  · exact Set.singleton_ne_empty true e
  · exact e.1 (Set.mem_singleton true)

-- `Set.univ_nonempty` idx 1: necessary (α = Empty)
theorem c5_177 : ¬ drop0% Set.univ_nonempty 1 := fun h => by
  obtain ⟨x, -⟩ := h (α := Empty); exact x.elim

-- `Set.Nonempty.to_type` idx 2: necessary (α = Empty, s = ∅)
theorem c5_178 : ¬ drop0% Set.Nonempty.to_type 2 := fun h =>
  (h (α := Empty) (s := ∅)).elim fun x => x.elim

-- `Set.univ.nonempty` idx 1: necessary (α = Empty)
theorem c5_179 : ¬ drop0% Set.univ.nonempty 1 := fun h =>
  (h (α := Empty)).elim fun x => x.1.elim

-- `Set.instNonemptyTop` idx 1: necessary (α = Empty)
theorem c5_180 : ¬ drop0% Set.instNonemptyTop 1 := fun h =>
  (h (α := Empty)).elim fun x => x.1.elim

-- `Set.empty_ne_univ` idx 1: necessary (α = Empty)
theorem c5_181 : ¬ drop0% Set.empty_ne_univ 1 := fun h =>
  h (α := Empty) (Set.ext fun x => x.elim)

-- `Set.Nonempty.eq_univ` idx 3: necessary (α = Unit, s = ∅)
theorem c5_182 : ¬ drop0% Set.Nonempty.eq_univ 3 := fun h =>
  Set.empty_ne_univ (h (α := Unit) (s := ∅))

-- `Set.exists_mem_univ_of_nonempty` idx 1: necessary (α = Empty)
theorem c5_183 : ¬ drop0% Set.exists_mem_univ_of_nonempty 1 := fun h => by
  obtain ⟨x, -⟩ := h Empty; exact x.elim

-- `Set.exists_mem_of_nonempty` idx 1: necessary (α = Empty)
theorem c5_184 : ¬ drop0% Set.exists_mem_of_nonempty 1 := fun h => by
  obtain ⟨x, -⟩ := h Empty; exact x.elim

-- `Set.nontrivial_of_nonempty` idx 1: necessary (Set Empty has one element)
theorem c5_185 : ¬ drop0% Set.nontrivial_of_nonempty 1 := fun h => by
  obtain ⟨x, y, hne⟩ := (h (α := Empty)).exists_pair_ne
  exact hne (Set.ext fun a => a.elim)

-- `Set.union_congr_right` idx 4: necessary (s = {0}, t = u = ∅)
theorem c5_186 : ¬ drop0% Set.union_congr_right 4 := fun h => by
  have := h (s := ({0} : Set ℕ)) (t := ∅) (u := ∅) (Set.empty_subset _)
  simp at this

-- `Set.union_congr_right` idx 5: necessary (s = ∅, t = {0}, u = ∅)
theorem c5_187 : ¬ drop0% Set.union_congr_right 5 := fun h => by
  have := h (s := (∅ : Set ℕ)) (t := {0}) (u := ∅) (Set.empty_subset _)
  simp at this

-- `Set.union_eq_union_mono_left` idx 6: necessary (s₁ = univ, t = {0}, u = ∅, s₂ = ∅)
theorem c5_188 : ¬ drop0% Set.union_eq_union_mono_left 6 := fun h => by
  have := h (s₁ := (Set.univ : Set ℕ)) (t := {0}) (u := ∅) (s₂ := ∅) (by simp)
  simp at this

-- `Set.union_eq_union_mono_right` idx 6: necessary (s = {0}, t = ∅, u₁ = univ, u₂ = ∅)
theorem c5_189 : ¬ drop0% Set.union_eq_union_mono_right 6 := fun h => by
  have := h (s := ({0} : Set ℕ)) (t := ∅) (u₁ := Set.univ) (u₂ := ∅) (by simp)
  simp at this

-- `Set.inter_eq_inter_mono_left` idx 6: necessary (s₁ = ∅, t = {0}, u = ∅, s₂ = univ)
theorem c5_190 : ¬ drop0% Set.inter_eq_inter_mono_left 6 := fun h => by
  have := h (s₁ := (∅ : Set ℕ)) (t := {0}) (u := ∅) (s₂ := Set.univ) (by simp)
  simp at this

-- `Set.inter_eq_inter_mono_right` idx 6: necessary (s = {0}, t = ∅, u₁ = ∅, u₂ = univ)
theorem c5_191 : ¬ drop0% Set.inter_eq_inter_mono_right 6 := fun h => by
  have := h (s := ({0} : Set ℕ)) (t := ∅) (u₁ := ∅) (u₂ := Set.univ) (by simp)
  simp at this

-- `Function.Injective.nonempty_apply_iff` idx 4: necessary (f = complement on Set Unit, s = ∅)
theorem c5_192 : ¬ drop0% Function.Injective.nonempty_apply_iff 4 := fun h => by
  have := (h (f := fun s : Set Unit => sᶜ) compl_injective (s := ∅)).1 (by simp)
  exact Set.not_nonempty_empty this

-- `Subsingleton.eq_univ_of_nonempty` idx 3: necessary (α = Unit, s = ∅)
theorem c5_193 : ¬ drop0% Subsingleton.eq_univ_of_nonempty 3 := fun h =>
  Set.empty_ne_univ (h (α := Unit) (s := ∅))

-- `Subsingleton.set_cases` idx 1: necessary (α = Bool, p s = (s = ∅ ∨ s = univ), s = {true})
theorem c5_194 : ¬ drop0% Subsingleton.set_cases 1 := fun h => by
  rcases h (α := Bool) (p := fun s => s = ∅ ∨ s = Set.univ) (Or.inl rfl) (Or.inr rfl) {true} with e | e
  · exact Set.singleton_ne_empty true e
  · have := e ▸ Set.mem_univ false; simp at this

-- `Subsingleton.set_cases` idx 3: necessary (α = Unit, p s = (s = univ), s = ∅)
theorem c5_195 : ¬ drop0% Subsingleton.set_cases 3 := fun h =>
  Set.empty_ne_univ (h (α := Unit) (p := fun s => s = Set.univ) rfl ∅)

-- `Subsingleton.set_cases` idx 4: necessary (α = Unit, p s = (s = ∅), s = univ)
theorem c5_196 : ¬ drop0% Subsingleton.set_cases 4 := fun h =>
  Set.empty_ne_univ (h (α := Unit) (p := fun s => s = ∅) rfl Set.univ).symm
