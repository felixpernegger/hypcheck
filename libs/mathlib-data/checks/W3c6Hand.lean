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

namespace W3c6

-- helper: two incomparable points (sum order): a preorder that is not directed
abbrev U2 := Unit ⊕ Unit
theorem u2_le : ∀ a b : U2, a ≤ b → a = b := by
  rintro (⟨⟩|⟨⟩) (⟨⟩|⟨⟩) h <;> simp_all
def sel (i : Bool) : U2 := if i then .inl () else .inr ()
def selN (i : Bool) : ℕ := if i then 0 else 1

-- helpers: the quantifier facts behind the distributivity models
theorem ne_l : True := trivial
theorem ne_nr : True := trivial
theorem ne_r : True := trivial
theorem ne_nl : True := trivial
theorem ds_r : ∀ i : Bool, ∃ j : U2, j = sel i := fun i => ⟨_, rfl⟩
theorem ds_nl : ¬ ∃ j : U2, ∀ i : Bool, j = sel i := fun ⟨j, hj⟩ => by
  have := (hj true).symm.trans (hj false); simp [sel] at this
theorem di_l : ∀ j : U2, ∃ i : Bool, j = sel i := by
  rintro (⟨⟩|⟨⟩)
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩
theorem di_nr : ¬ ∃ i : Bool, ∀ j : U2, j = sel i := fun ⟨i, hi⟩ => by
  cases i
  · exact absurd (hi (.inl ())) (by simp [sel])
  · exact absurd (hi (.inr ())) (by simp [sel])
theorem hs_r : ∀ i : Bool, ∃ j : ℕ, j = selN i := fun i => ⟨_, rfl⟩
theorem hs_nl : ¬ ∃ j : ℕ, ∀ i : Bool, j = selN i := fun ⟨j, hj⟩ => by
  have := (hj true).symm.trans (hj false); simp [selN] at this
theorem hi_l : ∀ j : ℕ, ∃ i : Bool, j ≠ selN i := fun j =>
  if hj : j = 0 then ⟨false, by simp [selN, hj]⟩ else ⟨true, by simp [selN, hj]⟩
theorem hi_nr : ¬ ∃ i : Bool, ∀ j : ℕ, j ≠ selN i := fun ⟨i, hi⟩ => hi _ rfl
theorem fsm_r : ∀ i : ℕ, ∃ j : ℕ, i ≤ j := fun i => ⟨i, le_rfl⟩
theorem fsm_nl : ¬ ∃ j : ℕ, ∀ i : ℕ, i ≤ j := fun ⟨j, hj⟩ => absurd (hj (j+1)) (by omega)
theorem fsa_r : ∀ i : ℕ, ∃ j : ℤ, j ≤ -(i:ℤ) := fun i => ⟨_, le_rfl⟩
theorem fsa_nl : ¬ ∃ j : ℤ, ∀ i : ℕ, j ≤ -(i:ℤ) := fun ⟨j, hj⟩ => absurd (hj ((-j).toNat + 1)) (by omega)
theorem fim_l : ∀ j : ℤ, ∃ i : ℕ, -(i:ℤ) ≤ j := fun j => ⟨(-j).toNat, by omega⟩
theorem fim_nr : ¬ ∃ i : ℕ, ∀ j : ℤ, -(i:ℤ) ≤ j := fun ⟨i, hi⟩ => absurd (hi (-(i:ℤ) - 1)) (by omega)
theorem fia_l : ∀ j : ℕ, ∃ i : ℕ, j ≤ i := fun j => ⟨j, le_rfl⟩
theorem fia_nr : ¬ ∃ i : ℕ, ∀ j : ℕ, j ≤ i := fun ⟨i, hi⟩ => absurd (hi (i+1)) (by omega)

end W3c6
open W3c6

namespace W3c6

-- helper: ℕ is infinite as a set
theorem iN : (Set.univ : Set ℕ).Infinite := Set.infinite_univ
-- helper: a set equal to univ in ℕ is not finite as a type
theorem nfN {s : Set ℕ} (h : s = Set.univ) : ¬ Finite ↑s := fun hf =>
  iN (h ▸ Set.toFinite s)
theorem nfsN {s : Set ℕ} (h : s = Set.univ) : ¬ s.Finite := fun hf => iN (h ▸ hf)
theorem nfU {s : Set (ULift.{1} ℕ)} (h : s = Set.univ) : ¬ s.Finite := fun hf =>
  Set.infinite_univ (h ▸ hf)
theorem nfUt {s : Set (ULift.{1} ℕ)} (h : s = Set.univ) : ¬ Finite ↑s := fun hf =>
  nfU h (Set.toFinite s)

end W3c6
open W3c6

-- `Finite.Set.finite_iUnion` idx 2: necessary (iota = Nat, f i = {i} in ULift Nat: union univ)
theorem c6_0 : ¬ drop1% Finite.Set.finite_iUnion 2 := fun h => by
  have := @h (ULift.{1} ℕ) ℕ (fun i => {ULift.up i}) (fun _ => inferInstance)
  exact nfUt (by ext ⟨x⟩; simp) this

-- `Finite.Set.finite_iUnion` idx 4: necessary (iota = True, f = univ in Nat)
theorem c6_1 : ¬ drop0% Finite.Set.finite_iUnion 4 := fun h => by
  have := @h ℕ True inferInstance (fun _ => Set.univ)
  exact nfN (by simp) this

-- `Finite.Set.finite_sUnion` idx 2: necessary (s = all singletons of Nat)
theorem c6_2 : ¬ drop0% Finite.Set.finite_sUnion 2 := fun h => by
  have := @h ℕ (Set.range fun n => {n}) (fun t => by obtain ⟨_, n, rfl⟩ := t; infer_instance)
  exact nfN (by ext x; simp) this

-- `Finite.Set.finite_sUnion` idx 3: necessary (s = {univ})
theorem c6_3 : ¬ drop0% Finite.Set.finite_sUnion 3 := fun h => by
  have := @h ℕ {Set.univ} inferInstance
  exact nfN (by simp) this

-- `Finite.Set.finite_biUnion` idx 3: necessary (s = univ, t i = {i})
theorem c6_4 : ¬ drop0% Finite.Set.finite_biUnion 3 := fun h => by
  have := @h ℕ ℕ Set.univ (fun i => {i}) (fun _ _ => inferInstance)
  exact nfN (by ext x; simp) this

-- `Finite.Set.finite_biUnion` idx 5: necessary (s = {0}, t = univ)
theorem c6_5 : ¬ drop0% Finite.Set.finite_biUnion 5 := fun h => by
  have := @h ℕ ℕ {0} inferInstance (fun _ => Set.univ)
  exact nfN (by simp) this

-- `Finite.Set.finite_biUnion'` idx 3: necessary (s = univ, t i = {i})
theorem c6_6 : ¬ drop0% Finite.Set.finite_biUnion' 3 := fun h => by
  have := @h ℕ ℕ Set.univ (fun i => {i}) (fun _ => inferInstance)
  exact nfN (by ext x; simp) this

-- `Finite.Set.finite_biUnion'` idx 5: necessary (s = empty-free {0}, t = univ)
theorem c6_7 : ¬ drop0% Finite.Set.finite_biUnion' 5 := fun h => by
  have := @h ℕ ℕ {0} inferInstance (fun _ => Set.univ)
  exact nfN (by simp) this

-- `Finite.Set.finite_biUnion''` idx 3: necessary (p = True everywhere, t i = {i})
theorem c6_8 : ¬ drop0% Finite.Set.finite_biUnion'' 3 := fun h => by
  have := @h ℕ ℕ (fun _ => True) (fun i => {i}) (fun _ => inferInstance)
  exact nfN (by ext x; simp) this

-- `Finite.Set.finite_biUnion''` idx 5: necessary (p = (· = 0), t = univ)
theorem c6_9 : ¬ drop0% Finite.Set.finite_biUnion'' 5 := fun h => by
  have := @h ℕ ℕ (fun i => i = 0) (by simp only [Set.ofPred_eq_eq_singleton]; infer_instance) (fun _ => Set.univ)
  exact nfN (by simp) this

-- `Finite.Set.finite_iInter` idx 2: necessary (iota = False: intersection univ)
theorem c6_10 : ¬ drop0% Finite.Set.finite_iInter 2 := fun h => by
  have := @h ℕ False (fun _ => ∅) (fun i => i.elim)
  exact nfN (by simp) this

-- `Finite.Set.finite_iInter` idx 4: necessary (iota = True, t = univ)
theorem c6_11 : ¬ drop0% Finite.Set.finite_iInter 4 := fun h => by
  have := @h ℕ True inferInstance (fun _ => Set.univ)
  exact nfN (by simp) this

-- `Set.finite_iUnion` idx 2: necessary (iota = Nat, f i = {i} in ULift Nat)
theorem c6_12 : ¬ drop1% Set.finite_iUnion 2 := fun h => by
  have := @h (ULift.{1} ℕ) ℕ (fun i => {ULift.up i}) (fun _ => Set.finite_singleton _)
  exact nfU (by ext ⟨x⟩; simp) this

-- `Set.finite_iUnion` idx 4: necessary (iota = True, f = univ)
theorem c6_13 : ¬ drop0% Set.finite_iUnion 4 := fun h => by
  have := @h ℕ True inferInstance (fun _ => Set.univ)
  exact nfsN (by simp) this

-- `Set.Finite.biUnion'` idx 3: necessary (s = univ, t i _ = {i})
theorem c6_14 : ¬ drop0% Set.Finite.biUnion' 3 := fun h => by
  have := @h ℕ ℕ Set.univ (fun i _ => {i}) (fun _ _ => Set.finite_singleton _)
  exact nfsN (by ext x; simp) this

-- `Set.Finite.biUnion'` idx 5: necessary (s = {0}, t = univ)
theorem c6_15 : ¬ drop0% Set.Finite.biUnion' 5 := fun h => by
  have := @h ℕ ℕ {0} (Set.finite_singleton _) (fun _ _ => Set.univ)
  exact nfsN (by simp) this

-- `Set.Finite.biUnion` idx 3: necessary (s = univ, t i = {i})
theorem c6_16 : ¬ drop0% Set.Finite.biUnion 3 := fun h => by
  have := @h ℕ ℕ Set.univ (fun i => {i}) (fun _ _ => Set.finite_singleton _)
  exact nfsN (by ext x; simp) this

-- `Set.Finite.biUnion` idx 5: necessary (s = {0}, t = univ)
theorem c6_17 : ¬ drop0% Set.Finite.biUnion 5 := fun h => by
  have := @h ℕ ℕ {0} (Set.finite_singleton _) (fun _ => Set.univ)
  exact nfsN (by simp) this

-- `Set.Finite.sUnion` idx 2: necessary (s = all singletons)
theorem c6_18 : ¬ drop0% Set.Finite.sUnion 2 := fun h => by
  have := @h ℕ (Set.range fun n => {n}) (by rintro _ ⟨n, rfl⟩; exact Set.finite_singleton n)
  exact nfsN (by ext x; simp) this

-- `Set.Finite.sUnion` idx 3: necessary (s = {univ})
theorem c6_19 : ¬ drop0% Set.Finite.sUnion 3 := fun h => by
  have := @h ℕ {Set.univ} (Set.finite_singleton _)
  exact nfsN (by simp) this

-- `Set.Finite.sInter` idx 3: necessary (s = empty: intersection univ)
theorem c6_20 : ¬ drop0% Set.Finite.sInter 3 := fun h => by
  have := @h ℕ ∅ ∅ Set.finite_empty
  exact nfsN (by simp) this

-- `Set.Finite.sInter` idx 4: necessary (s = {univ}, t = univ)
theorem c6_21 : ¬ drop0% Set.Finite.sInter 4 := fun h => by
  have := @h ℕ {Set.univ} Set.univ rfl
  exact nfsN (by simp) this

-- `Set.Finite.iUnion` idx 4: necessary (t = univ, s i = {i})
theorem c6_22 : ¬ drop0% Set.Finite.iUnion 4 := fun h => by
  have := @h ℕ ℕ (fun i => {i}) Set.univ (fun _ _ => Set.finite_singleton _) (by simp)
  exact nfsN (by ext x; simp) this

-- `Set.Finite.iUnion` idx 5: necessary (iota = Unit, t = univ, s = univ)
theorem c6_23 : ¬ drop0% Set.Finite.iUnion 5 := fun h => by
  have := @h ℕ Unit (fun _ => Set.univ) Set.univ Set.finite_univ (fun i hi => (hi (Set.mem_univ i)).elim)
  exact nfsN (Set.iUnion_const _) this

-- `Set.Finite.iUnion` idx 6: necessary (t = empty, s i = {i})
theorem c6_24 : ¬ drop0% Set.Finite.iUnion 6 := fun h => by
  have := @h ℕ ℕ (fun i => {i}) ∅ Set.finite_empty (by simp)
  exact nfsN (by ext x; simp) this

-- `Set.finite_iUnion_iff` idx 3: necessary (s i = {0} for all i: union finite, infinitely many nonempty)
theorem c6_25 : ¬ drop0% Set.finite_iUnion_iff 3 := fun h => by
  have := (@h ℕ ℕ (fun _ => {0})).1 (by simp)
  exact nfsN (by simp) this.2

-- `Set.Infinite.iUnion₂` idx 6: necessary (s = empty)
theorem c6_26 : ¬ drop0% Set.Infinite.iUnion₂ 6 := fun h => by
  have := @h ℕ True (fun _ => True) (fun _ _ => ∅) trivial trivial
  simp at this

-- `Set.finite_iUnion_of_subsingleton` idx 2: necessary (iota = Nat, s i = {i} in ULift Nat)
theorem c6_27 : ¬ drop1% Set.finite_iUnion_of_subsingleton 2 := fun h => by
  have := (@h (ULift.{1} ℕ) ℕ (fun i => {ULift.up i})).2 (fun _ => Set.finite_singleton _)
  exact nfU (by ext ⟨x⟩; simp) this

-- `Set.PairwiseDisjoint.finite_biUnion_iff` idx 4: necessary (s = univ, f = const {0})
theorem c6_28 : ¬ drop0% Set.PairwiseDisjoint.finite_biUnion_iff 4 := fun h => by
  have := (@h ℕ ℕ (fun _ => {0}) Set.univ).1 (by simp)
  exact nfsN (by ext x; simp) this.2

-- `Set.Finite.preimage'` idx 4: necessary (f = id, s = univ)
theorem c6_29 : ¬ drop0% Set.Finite.preimage' 4 := fun h => by
  have := @h ℕ ℕ id Set.univ (fun b _ => by simp)
  exact nfsN (by simp) this

-- `Set.Finite.preimage'` idx 5: necessary (f : Nat → Unit, s = univ)
theorem c6_30 : ¬ drop0% Set.Finite.preimage' 5 := fun h => by
  have := @h ℕ Unit (fun _ => ()) Set.univ Set.finite_univ
  exact nfsN (by simp) this

-- `Set.union_finset_finite_of_range_finite` idx 3: necessary (f n = {n})
theorem c6_31 : ¬ drop0% Set.union_finset_finite_of_range_finite 3 := fun h => by
  have := @h ℕ ℕ (fun n => {n})
  exact nfsN (by ext x; simp) this

-- `Set.Finite.of_finite_fibers` idx 4: necessary (f = id, s = univ)
theorem c6_32 : ¬ drop0% Set.Finite.of_finite_fibers 4 := fun h => by
  have := @h ℕ ℕ id Set.univ (fun x _ => (Set.finite_singleton x).subset (by simp))
  exact nfsN rfl this

-- `Set.Finite.of_finite_fibers` idx 5: necessary (f : Nat → Unit, s = univ)
theorem c6_33 : ¬ drop0% Set.Finite.of_finite_fibers 5 := fun h => by
  have := @h ℕ Unit (fun _ => ()) Set.univ (Set.toFinite _)
  exact nfsN rfl this

-- `Set.finite_subset_iUnion` idx 2: necessary (s = univ, t i = {i})
theorem c6_34 : ¬ drop0% Set.finite_subset_iUnion 2 := fun h => by
  obtain ⟨I, hI, hs⟩ := @h ℕ Set.univ ℕ (fun i => {i}) (fun x _ => by simp)
  exact nfsN (Set.eq_univ_of_univ_subset (by simpa using hs)) hI

-- `Set.eq_finite_iUnion_of_finite_subset_iUnion` idx 4: necessary (t = univ, s i = {i})
theorem c6_35 : ¬ drop0% Set.eq_finite_iUnion_of_finite_subset_iUnion 4 := fun h => by
  obtain ⟨I, hI, σ, hσ, hσs, ht⟩ := @h ℕ ℕ (fun i => {i}) Set.univ (fun x _ => by simp)
  have : Finite ↑{i | i ∈ I} := hI.to_subtype
  exact nfsN ht.symm (Set.finite_iUnion hσ)

-- `Set.infinite_iUnion` idx 2: necessary (iota = Unit, s = empty)
theorem c6_36 : ¬ drop0% Set.infinite_iUnion 2 := fun h => by
  have := @h ℕ Unit (fun _ => ∅) (fun _ _ _ => rfl)
  simp at this

-- `Set.Infinite.biUnion` idx 5: necessary (s = const empty, a = univ)
theorem c6_37 : ¬ drop0% Set.Infinite.biUnion 5 := fun h => by
  have := @h ℕ ℕ (fun _ => ∅) Set.univ iN
  simp at this
-- `Set.Finite.iInf_biSup_of_monotone` idx 4: necessary (case ne: iota = Unit, iota' = Empty, alpha = Prop, predicate True)
theorem c6_d0 : ¬ drop0% Set.Finite.iInf_biSup_of_monotone 4 := fun h => by
  have := h (ι := Unit) (ι' := Empty) (α := Prop) (s := ∅) (f := fun i j => True) (Set.toFinite _) (fun i _ => by intro a; exact a.elim)
  refine absurd (cast this ?_) ?_
  · simp
  · simp

-- `Set.Finite.iInf_biSup_of_monotone` idx 5: necessary (case dir: iota = Bool, iota' = U2, alpha = Prop, predicate j = sel i)
theorem c6_d1 : ¬ drop0% Set.Finite.iInf_biSup_of_monotone 5 := fun h => by
  have := h (ι := Bool) (ι' := U2) (α := Prop) (s := Set.univ) (f := fun i j => j = sel i) (Set.toFinite _) (fun i _ => by intro a b hab; obtain rfl := u2_le a b hab; exact le_rfl)
  refine absurd (cast this ?_) ?_
  · simpa using di_l
  · simpa using di_nr

-- `Set.Finite.iInf_biSup_of_monotone` idx 8: necessary (case fin: iota = ℕ, iota' = ℤ, alpha = Prop, predicate -(i:ℤ) ≤ j)
theorem c6_d2 : ¬ drop0% Set.Finite.iInf_biSup_of_monotone 8 := fun h => by
  have := h (ι := ℕ) (ι' := ℤ) (α := Prop) (s := Set.univ) (f := fun i j => -(i:ℤ) ≤ j) (fun i _ => by intro a b hab hx; omega)
  refine absurd (cast this ?_) ?_
  · simpa using fim_l
  · simpa using fim_nr

-- `Set.Finite.iInf_biSup_of_monotone` idx 10: necessary (case hf: iota = Bool, iota' = ℕ, alpha = Prop, predicate j ≠ selN i)
theorem c6_d3 : ¬ drop0% Set.Finite.iInf_biSup_of_monotone 10 := fun h => by
  have := h (ι := Bool) (ι' := ℕ) (α := Prop) (s := Set.univ) (f := fun i j => j ≠ selN i) (Set.toFinite _)
  refine absurd (cast this ?_) ?_
  · simpa using hi_l
  · simpa using hi_nr

-- `Set.Finite.iSup_biInf_of_monotone` idx 4: necessary (case ne: iota = Unit, iota' = Empty, alpha = Prop, predicate True)
theorem c6_d4 : ¬ drop0% Set.Finite.iSup_biInf_of_monotone 4 := fun h => by
  have := h (ι := Unit) (ι' := Empty) (α := Prop) (s := ∅) (f := fun i j => True) (Set.toFinite _) (fun i _ => by intro a; exact a.elim)
  refine absurd (cast this.symm ?_) ?_
  · simp
  · simp

-- `Set.Finite.iSup_biInf_of_monotone` idx 5: necessary (case dir: iota = Bool, iota' = U2, alpha = Prop, predicate j = sel i)
theorem c6_d5 : ¬ drop0% Set.Finite.iSup_biInf_of_monotone 5 := fun h => by
  have := h (ι := Bool) (ι' := U2) (α := Prop) (s := Set.univ) (f := fun i j => j = sel i) (Set.toFinite _) (fun i _ => by intro a b hab; obtain rfl := u2_le a b hab; exact le_rfl)
  refine absurd (cast this.symm ?_) ?_
  · simpa using ds_r
  · simpa using ds_nl

-- `Set.Finite.iSup_biInf_of_monotone` idx 8: necessary (case fin: iota = ℕ, iota' = ℕ, alpha = Prop, predicate i ≤ j)
theorem c6_d6 : ¬ drop0% Set.Finite.iSup_biInf_of_monotone 8 := fun h => by
  have := h (ι := ℕ) (ι' := ℕ) (α := Prop) (s := Set.univ) (f := fun i j => i ≤ j) (fun i _ => by intro a b hab hx; omega)
  refine absurd (cast this.symm ?_) ?_
  · simpa using fsm_r
  · simpa using fsm_nl

-- `Set.Finite.iSup_biInf_of_monotone` idx 10: necessary (case hf: iota = Bool, iota' = ℕ, alpha = Prop, predicate j = selN i)
theorem c6_d7 : ¬ drop0% Set.Finite.iSup_biInf_of_monotone 10 := fun h => by
  have := h (ι := Bool) (ι' := ℕ) (α := Prop) (s := Set.univ) (f := fun i j => j = selN i) (Set.toFinite _)
  refine absurd (cast this.symm ?_) ?_
  · simpa using hs_r
  · simpa using hs_nl

-- `Set.Finite.iInf_biSup_of_antitone` idx 4: necessary (case ne: iota = Unit, iota' = Empty, alpha = Prop, predicate True)
theorem c6_d8 : ¬ drop0% Set.Finite.iInf_biSup_of_antitone 4 := fun h => by
  have := h (ι := Unit) (ι' := Empty) (α := Prop) (s := ∅) (f := fun i j => True) (Set.toFinite _) (fun i _ => by intro a; exact a.elim)
  refine absurd (cast this ?_) ?_
  · simp
  · simp

-- `Set.Finite.iInf_biSup_of_antitone` idx 5: necessary (case dir: iota = Bool, iota' = U2, alpha = Prop, predicate j = sel i)
theorem c6_d9 : ¬ drop0% Set.Finite.iInf_biSup_of_antitone 5 := fun h => by
  have := h (ι := Bool) (ι' := U2) (α := Prop) (s := Set.univ) (f := fun i j => j = sel i) (Set.toFinite _) (fun i _ => by intro a b hab; obtain rfl := u2_le a b hab; exact le_rfl)
  refine absurd (cast this ?_) ?_
  · simpa using di_l
  · simpa using di_nr

-- `Set.Finite.iInf_biSup_of_antitone` idx 8: necessary (case fin: iota = ℕ, iota' = ℕ, alpha = Prop, predicate j ≤ i)
theorem c6_d10 : ¬ drop0% Set.Finite.iInf_biSup_of_antitone 8 := fun h => by
  have := h (ι := ℕ) (ι' := ℕ) (α := Prop) (s := Set.univ) (f := fun i j => j ≤ i) (fun i _ => by intro a b hab hx; omega)
  refine absurd (cast this ?_) ?_
  · simpa using fia_l
  · simpa using fia_nr

-- `Set.Finite.iInf_biSup_of_antitone` idx 10: necessary (case hf: iota = Bool, iota' = ℕ, alpha = Prop, predicate j ≠ selN i)
theorem c6_d11 : ¬ drop0% Set.Finite.iInf_biSup_of_antitone 10 := fun h => by
  have := h (ι := Bool) (ι' := ℕ) (α := Prop) (s := Set.univ) (f := fun i j => j ≠ selN i) (Set.toFinite _)
  refine absurd (cast this ?_) ?_
  · simpa using hi_l
  · simpa using hi_nr

-- `Set.Finite.iSup_biInf_of_antitone` idx 4: necessary (case ne: iota = Unit, iota' = Empty, alpha = Prop, predicate True)
theorem c6_d12 : ¬ drop0% Set.Finite.iSup_biInf_of_antitone 4 := fun h => by
  have := h (ι := Unit) (ι' := Empty) (α := Prop) (s := ∅) (f := fun i j => True) (Set.toFinite _) (fun i _ => by intro a; exact a.elim)
  refine absurd (cast this.symm ?_) ?_
  · simp
  · simp

-- `Set.Finite.iSup_biInf_of_antitone` idx 5: necessary (case dir: iota = Bool, iota' = U2, alpha = Prop, predicate j = sel i)
theorem c6_d13 : ¬ drop0% Set.Finite.iSup_biInf_of_antitone 5 := fun h => by
  have := h (ι := Bool) (ι' := U2) (α := Prop) (s := Set.univ) (f := fun i j => j = sel i) (Set.toFinite _) (fun i _ => by intro a b hab; obtain rfl := u2_le a b hab; exact le_rfl)
  refine absurd (cast this.symm ?_) ?_
  · simpa using ds_r
  · simpa using ds_nl

-- `Set.Finite.iSup_biInf_of_antitone` idx 8: necessary (case fin: iota = ℕ, iota' = ℤ, alpha = Prop, predicate j ≤ -(i:ℤ))
theorem c6_d14 : ¬ drop0% Set.Finite.iSup_biInf_of_antitone 8 := fun h => by
  have := h (ι := ℕ) (ι' := ℤ) (α := Prop) (s := Set.univ) (f := fun i j => j ≤ -(i:ℤ)) (fun i _ => by intro a b hab hx; omega)
  refine absurd (cast this.symm ?_) ?_
  · simpa using fsa_r
  · simpa using fsa_nl

-- `Set.Finite.iSup_biInf_of_antitone` idx 10: necessary (case hf: iota = Bool, iota' = ℕ, alpha = Prop, predicate j = selN i)
theorem c6_d15 : ¬ drop0% Set.Finite.iSup_biInf_of_antitone 10 := fun h => by
  have := h (ι := Bool) (ι' := ℕ) (α := Prop) (s := Set.univ) (f := fun i j => j = selN i) (Set.toFinite _)
  refine absurd (cast this.symm ?_) ?_
  · simpa using hs_r
  · simpa using hs_nl

-- `iInf_iSup_of_monotone` idx 3: necessary (case fin: iota = ℕ, iota' = ℤ, alpha = Prop, predicate -(i:ℤ) ≤ j)
theorem c6_d16 : ¬ drop0% iInf_iSup_of_monotone 3 := fun h => by
  have := h (ι := ℕ) (ι' := ℤ) (α := Prop) (f := fun i j => -(i:ℤ) ≤ j) (fun i => by intro a b hab hx; omega)
  refine absurd (cast this ?_) ?_
  · simpa using fim_l
  · simpa using fim_nr

-- `iInf_iSup_of_monotone` idx 5: necessary (case ne: iota = Empty, iota' = Empty, alpha = Prop, predicate True)
theorem c6_d17 : ¬ drop0% iInf_iSup_of_monotone 5 := fun h => by
  have := h (ι := Empty) (ι' := Empty) (α := Prop) (f := fun i j => True) (fun i => by intro a; exact a.elim)
  refine absurd (cast this ?_) ?_
  · simp
  · simp

-- `iInf_iSup_of_monotone` idx 6: necessary (case dir: iota = Bool, iota' = U2, alpha = Prop, predicate j = sel i)
theorem c6_d18 : ¬ drop0% iInf_iSup_of_monotone 6 := fun h => by
  have := h (ι := Bool) (ι' := U2) (α := Prop) (f := fun i j => j = sel i) (fun i => by intro a b hab; obtain rfl := u2_le a b hab; exact le_rfl)
  refine absurd (cast this ?_) ?_
  · simpa using di_l
  · simpa using di_nr

-- `iInf_iSup_of_monotone` idx 9: necessary (case hf: iota = Bool, iota' = ℕ, alpha = Prop, predicate j ≠ selN i)
theorem c6_d19 : ¬ drop0% iInf_iSup_of_monotone 9 := fun h => by
  have := h (ι := Bool) (ι' := ℕ) (α := Prop) (f := fun i j => j ≠ selN i) 
  refine absurd (cast this ?_) ?_
  · simpa using hi_l
  · simpa using hi_nr

-- `iSup_iInf_of_monotone` idx 3: necessary (case fin: iota = ℕ, iota' = ℕ, alpha = Prop, predicate i ≤ j)
theorem c6_d20 : ¬ drop0% iSup_iInf_of_monotone 3 := fun h => by
  have := h (ι := ℕ) (ι' := ℕ) (α := Prop) (f := fun i j => i ≤ j) (fun i => by intro a b hab hx; omega)
  refine absurd (cast this.symm ?_) ?_
  · simpa using fsm_r
  · simpa using fsm_nl

-- `iSup_iInf_of_monotone` idx 5: necessary (case ne: iota = Empty, iota' = Empty, alpha = Prop, predicate True)
theorem c6_d21 : ¬ drop0% iSup_iInf_of_monotone 5 := fun h => by
  have := h (ι := Empty) (ι' := Empty) (α := Prop) (f := fun i j => True) (fun i => by intro a; exact a.elim)
  refine absurd (cast this.symm ?_) ?_
  · simp
  · simp

-- `iSup_iInf_of_monotone` idx 6: necessary (case dir: iota = Bool, iota' = U2, alpha = Prop, predicate j = sel i)
theorem c6_d22 : ¬ drop0% iSup_iInf_of_monotone 6 := fun h => by
  have := h (ι := Bool) (ι' := U2) (α := Prop) (f := fun i j => j = sel i) (fun i => by intro a b hab; obtain rfl := u2_le a b hab; exact le_rfl)
  refine absurd (cast this.symm ?_) ?_
  · simpa using ds_r
  · simpa using ds_nl

-- `iSup_iInf_of_monotone` idx 9: necessary (case hf: iota = Bool, iota' = ℕ, alpha = Prop, predicate j = selN i)
theorem c6_d23 : ¬ drop0% iSup_iInf_of_monotone 9 := fun h => by
  have := h (ι := Bool) (ι' := ℕ) (α := Prop) (f := fun i j => j = selN i) 
  refine absurd (cast this.symm ?_) ?_
  · simpa using hs_r
  · simpa using hs_nl

-- `iInf_iSup_of_antitone` idx 3: necessary (case fin: iota = ℕ, iota' = ℕ, alpha = Prop, predicate j ≤ i)
theorem c6_d24 : ¬ drop0% iInf_iSup_of_antitone 3 := fun h => by
  have := h (ι := ℕ) (ι' := ℕ) (α := Prop) (f := fun i j => j ≤ i) (fun i => by intro a b hab hx; omega)
  refine absurd (cast this ?_) ?_
  · simpa using fia_l
  · simpa using fia_nr

-- `iInf_iSup_of_antitone` idx 5: necessary (case ne: iota = Empty, iota' = Empty, alpha = Prop, predicate True)
theorem c6_d25 : ¬ drop0% iInf_iSup_of_antitone 5 := fun h => by
  have := h (ι := Empty) (ι' := Empty) (α := Prop) (f := fun i j => True) (fun i => by intro a; exact a.elim)
  refine absurd (cast this ?_) ?_
  · simp
  · simp

-- `iInf_iSup_of_antitone` idx 6: necessary (case dir: iota = Bool, iota' = U2, alpha = Prop, predicate j = sel i)
theorem c6_d26 : ¬ drop0% iInf_iSup_of_antitone 6 := fun h => by
  have := h (ι := Bool) (ι' := U2) (α := Prop) (f := fun i j => j = sel i) (fun i => by intro a b hab; obtain rfl := u2_le a b hab; exact le_rfl)
  refine absurd (cast this ?_) ?_
  · simpa using di_l
  · simpa using di_nr

-- `iInf_iSup_of_antitone` idx 9: necessary (case hf: iota = Bool, iota' = ℕ, alpha = Prop, predicate j ≠ selN i)
theorem c6_d27 : ¬ drop0% iInf_iSup_of_antitone 9 := fun h => by
  have := h (ι := Bool) (ι' := ℕ) (α := Prop) (f := fun i j => j ≠ selN i) 
  refine absurd (cast this ?_) ?_
  · simpa using hi_l
  · simpa using hi_nr

-- `iSup_iInf_of_antitone` idx 3: necessary (case fin: iota = ℕ, iota' = ℤ, alpha = Prop, predicate j ≤ -(i:ℤ))
theorem c6_d28 : ¬ drop0% iSup_iInf_of_antitone 3 := fun h => by
  have := h (ι := ℕ) (ι' := ℤ) (α := Prop) (f := fun i j => j ≤ -(i:ℤ)) (fun i => by intro a b hab hx; omega)
  refine absurd (cast this.symm ?_) ?_
  · simpa using fsa_r
  · simpa using fsa_nl

-- `iSup_iInf_of_antitone` idx 5: necessary (case ne: iota = Empty, iota' = Empty, alpha = Prop, predicate True)
theorem c6_d29 : ¬ drop0% iSup_iInf_of_antitone 5 := fun h => by
  have := h (ι := Empty) (ι' := Empty) (α := Prop) (f := fun i j => True) (fun i => by intro a; exact a.elim)
  refine absurd (cast this.symm ?_) ?_
  · simp
  · simp

-- `iSup_iInf_of_antitone` idx 6: necessary (case dir: iota = Bool, iota' = U2, alpha = Prop, predicate j = sel i)
theorem c6_d30 : ¬ drop0% iSup_iInf_of_antitone 6 := fun h => by
  have := h (ι := Bool) (ι' := U2) (α := Prop) (f := fun i j => j = sel i) (fun i => by intro a b hab; obtain rfl := u2_le a b hab; exact le_rfl)
  refine absurd (cast this.symm ?_) ?_
  · simpa using ds_r
  · simpa using ds_nl

-- `iSup_iInf_of_antitone` idx 9: necessary (case hf: iota = Bool, iota' = ℕ, alpha = Prop, predicate j = selN i)
theorem c6_d31 : ¬ drop0% iSup_iInf_of_antitone 9 := fun h => by
  have := h (ι := Bool) (ι' := ℕ) (α := Prop) (f := fun i j => j = selN i) 
  refine absurd (cast this.symm ?_) ?_
  · simpa using hs_r
  · simpa using hs_nl

-- `Set.iUnion_iInter_of_monotone` idx 3: necessary (case fin: iota = ℕ, iota' = ℕ, alpha = Set Unit, predicate i ≤ j)
theorem c6_d32 : ¬ drop0% Set.iUnion_iInter_of_monotone 3 := fun h => by
  have := h (ι := ℕ) (ι' := ℕ) (α := Unit) (s := fun i j => {_u : Unit | i ≤ j}) (fun i => by intro a b hab x hx; simp only [Set.mem_setOf_eq] at hx ⊢; omega)
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this.symm ?_) ?_
  · simpa using fsm_r
  · simpa using fsm_nl

-- `Set.iUnion_iInter_of_monotone` idx 5: necessary (case dir: iota = Bool, iota' = U2, alpha = Set Unit, predicate j = sel i)
theorem c6_d33 : ¬ drop0% Set.iUnion_iInter_of_monotone 5 := fun h => by
  have := h (ι := Bool) (ι' := U2) (α := Unit) (s := fun i j => {_u : Unit | j = sel i}) (fun i => by intro a b hab; obtain rfl := u2_le a b hab; exact le_rfl)
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this.symm ?_) ?_
  · simpa using ds_r
  · simpa using ds_nl

-- `Set.iUnion_iInter_of_monotone` idx 6: necessary (case ne: iota = Empty, iota' = Empty, alpha = Set Unit, predicate True)
theorem c6_d34 : ¬ drop0% Set.iUnion_iInter_of_monotone 6 := fun h => by
  have := h (ι := Empty) (ι' := Empty) (α := Unit) (s := fun i j => {_u : Unit | True}) (fun i => by intro a; exact a.elim)
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this.symm ?_) ?_
  · simp
  · simp

-- `Set.iUnion_iInter_of_monotone` idx 8: necessary (case hf: iota = Bool, iota' = ℕ, alpha = Set Unit, predicate j = selN i)
theorem c6_d35 : ¬ drop0% Set.iUnion_iInter_of_monotone 8 := fun h => by
  have := h (ι := Bool) (ι' := ℕ) (α := Unit) (s := fun i j => {_u : Unit | j = selN i}) 
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this.symm ?_) ?_
  · simpa using hs_r
  · simpa using hs_nl

-- `Set.iUnion_iInter_of_antitone` idx 3: necessary (case fin: iota = ℕ, iota' = ℤ, alpha = Set Unit, predicate j ≤ -(i:ℤ))
theorem c6_d36 : ¬ drop0% Set.iUnion_iInter_of_antitone 3 := fun h => by
  have := h (ι := ℕ) (ι' := ℤ) (α := Unit) (s := fun i j => {_u : Unit | j ≤ -(i:ℤ)}) (fun i => by intro a b hab x hx; simp only [Set.mem_setOf_eq] at hx ⊢; omega)
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this.symm ?_) ?_
  · simpa using fsa_r
  · simpa using fsa_nl

-- `Set.iUnion_iInter_of_antitone` idx 5: necessary (case dir: iota = Bool, iota' = U2, alpha = Set Unit, predicate j = sel i)
theorem c6_d37 : ¬ drop0% Set.iUnion_iInter_of_antitone 5 := fun h => by
  have := h (ι := Bool) (ι' := U2) (α := Unit) (s := fun i j => {_u : Unit | j = sel i}) (fun i => by intro a b hab; obtain rfl := u2_le a b hab; exact le_rfl)
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this.symm ?_) ?_
  · simpa using ds_r
  · simpa using ds_nl

-- `Set.iUnion_iInter_of_antitone` idx 6: necessary (case ne: iota = Empty, iota' = Empty, alpha = Set Unit, predicate True)
theorem c6_d38 : ¬ drop0% Set.iUnion_iInter_of_antitone 6 := fun h => by
  have := h (ι := Empty) (ι' := Empty) (α := Unit) (s := fun i j => {_u : Unit | True}) (fun i => by intro a; exact a.elim)
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this.symm ?_) ?_
  · simp
  · simp

-- `Set.iUnion_iInter_of_antitone` idx 8: necessary (case hf: iota = Bool, iota' = ℕ, alpha = Set Unit, predicate j = selN i)
theorem c6_d39 : ¬ drop0% Set.iUnion_iInter_of_antitone 8 := fun h => by
  have := h (ι := Bool) (ι' := ℕ) (α := Unit) (s := fun i j => {_u : Unit | j = selN i}) 
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this.symm ?_) ?_
  · simpa using hs_r
  · simpa using hs_nl

-- `Set.iInter_iUnion_of_monotone` idx 3: necessary (case fin: iota = ℕ, iota' = ℤ, alpha = Set Unit, predicate -(i:ℤ) ≤ j)
theorem c6_d40 : ¬ drop0% Set.iInter_iUnion_of_monotone 3 := fun h => by
  have := h (ι := ℕ) (ι' := ℤ) (α := Unit) (s := fun i j => {_u : Unit | -(i:ℤ) ≤ j}) (fun i => by intro a b hab x hx; simp only [Set.mem_setOf_eq] at hx ⊢; omega)
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this ?_) ?_
  · simpa using fim_l
  · simpa using fim_nr

-- `Set.iInter_iUnion_of_monotone` idx 5: necessary (case dir: iota = Bool, iota' = U2, alpha = Set Unit, predicate j = sel i)
theorem c6_d41 : ¬ drop0% Set.iInter_iUnion_of_monotone 5 := fun h => by
  have := h (ι := Bool) (ι' := U2) (α := Unit) (s := fun i j => {_u : Unit | j = sel i}) (fun i => by intro a b hab; obtain rfl := u2_le a b hab; exact le_rfl)
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this ?_) ?_
  · simpa using di_l
  · simpa using di_nr

-- `Set.iInter_iUnion_of_monotone` idx 6: necessary (case ne: iota = Empty, iota' = Empty, alpha = Set Unit, predicate True)
theorem c6_d42 : ¬ drop0% Set.iInter_iUnion_of_monotone 6 := fun h => by
  have := h (ι := Empty) (ι' := Empty) (α := Unit) (s := fun i j => {_u : Unit | True}) (fun i => by intro a; exact a.elim)
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this ?_) ?_
  · simp
  · simp

-- `Set.iInter_iUnion_of_monotone` idx 8: necessary (case hf: iota = Bool, iota' = ℕ, alpha = Set Unit, predicate j ≠ selN i)
theorem c6_d43 : ¬ drop0% Set.iInter_iUnion_of_monotone 8 := fun h => by
  have := h (ι := Bool) (ι' := ℕ) (α := Unit) (s := fun i j => {_u : Unit | j ≠ selN i}) 
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this ?_) ?_
  · simpa using hi_l
  · simpa using hi_nr

-- `Set.iInter_iUnion_of_antitone` idx 3: necessary (case fin: iota = ℕ, iota' = ℕ, alpha = Set Unit, predicate j ≤ i)
theorem c6_d44 : ¬ drop0% Set.iInter_iUnion_of_antitone 3 := fun h => by
  have := h (ι := ℕ) (ι' := ℕ) (α := Unit) (s := fun i j => {_u : Unit | j ≤ i}) (fun i => by intro a b hab x hx; simp only [Set.mem_setOf_eq] at hx ⊢; omega)
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this ?_) ?_
  · simpa using fia_l
  · simpa using fia_nr

-- `Set.iInter_iUnion_of_antitone` idx 5: necessary (case dir: iota = Bool, iota' = U2, alpha = Set Unit, predicate j = sel i)
theorem c6_d45 : ¬ drop0% Set.iInter_iUnion_of_antitone 5 := fun h => by
  have := h (ι := Bool) (ι' := U2) (α := Unit) (s := fun i j => {_u : Unit | j = sel i}) (fun i => by intro a b hab; obtain rfl := u2_le a b hab; exact le_rfl)
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this ?_) ?_
  · simpa using di_l
  · simpa using di_nr

-- `Set.iInter_iUnion_of_antitone` idx 6: necessary (case ne: iota = Empty, iota' = Empty, alpha = Set Unit, predicate True)
theorem c6_d46 : ¬ drop0% Set.iInter_iUnion_of_antitone 6 := fun h => by
  have := h (ι := Empty) (ι' := Empty) (α := Unit) (s := fun i j => {_u : Unit | True}) (fun i => by intro a; exact a.elim)
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this ?_) ?_
  · simp
  · simp

-- `Set.iInter_iUnion_of_antitone` idx 8: necessary (case hf: iota = Bool, iota' = ℕ, alpha = Set Unit, predicate j ≠ selN i)
theorem c6_d47 : ¬ drop0% Set.iInter_iUnion_of_antitone 8 := fun h => by
  have := h (ι := Bool) (ι' := ℕ) (α := Unit) (s := fun i j => {_u : Unit | j ≠ selN i}) 
  replace this := congrArg (fun S => () ∈ S) this
  refine absurd (cast this ?_) ?_
  · simpa using hi_l
  · simpa using hi_nr

namespace W3c6

-- helper: negation on Bool as a bare FunLike (preserves neither top nor bottom)
def bnot : Bool ≃ Bool := ⟨not, not, Bool.not_not, Bool.not_not⟩
theorem bnot_apply (b : Bool) : bnot b = !b := rfl

-- helper: "the complement is finite", a lattice map Set Nat to Prop preserving inf and top only finitely
def cofin : InfTopHom (Set ℕ) Prop where
  toFun s := sᶜ.Finite
  map_inf' s t := by
    show (s ∩ t)ᶜ.Finite = (sᶜ.Finite ∧ tᶜ.Finite)
    rw [Set.compl_inter]; exact propext Set.finite_union
  map_top' := by
    show (Set.univ : Set ℕ)ᶜ.Finite = True
    simp
theorem cofin_apply (s : Set ℕ) : cofin s = sᶜ.Finite := rfl

-- helper: "is infinite", a lattice map Set Nat to Prop preserving sup and bottom only finitely
def infi : SupBotHom (Set ℕ) Prop where
  toFun s := s.Infinite
  map_sup' s t := by
    show (s ∪ t).Infinite = (s.Infinite ∨ t.Infinite)
    exact propext Set.infinite_union
  map_bot' := by
    show (∅ : Set ℕ).Infinite = False
    simp
theorem infi_apply (s : Set ℕ) : infi s = s.Infinite := rfl

end W3c6
open W3c6

-- `Set.map_finite_biInf` idx 7: necessary (F = Bool ≃ Bool, f = negation, s = empty: f top = false)
theorem c6_38 : ¬ drop0% Set.map_finite_biInf 7 := fun h => by
  have := h (α := Bool) (β := Bool) (F := Bool ≃ Bool) (ι := Empty) (s := ∅) Set.finite_empty bnot (fun e => e.elim)
  simp [bnot_apply] at this

-- `Set.map_finite_biInf` idx 9: necessary (f s = (complement of s finite), s = univ, g i = complement of {i})
theorem c6_39 : ¬ drop0% Set.map_finite_biInf 9 := fun h => by
  have := h (α := Set ℕ) (β := Prop) (F := InfTopHom (Set ℕ) Prop) (ι := ℕ) (s := Set.univ) cofin (fun i => {i}ᶜ)
  refine absurd (cast this.symm ?_) ?_
  · simp [cofin_apply]
  · simp only [cofin_apply, Set.mem_univ, iInf_pos, Set.compl_iInter, compl_compl]
    exact nfsN (by ext; simp)

-- `Set.map_finite_biSup` idx 7: necessary (F = Bool ≃ Bool, f = negation, s = empty: f bot = true)
theorem c6_40 : ¬ drop0% Set.map_finite_biSup 7 := fun h => by
  have := h (α := Bool) (β := Bool) (F := Bool ≃ Bool) (ι := Empty) (s := ∅) Set.finite_empty bnot (fun e => e.elim)
  simp [bnot_apply] at this

-- `Set.map_finite_biSup` idx 9: necessary (f s = (s infinite), s = univ, g i = {i})
theorem c6_41 : ¬ drop0% Set.map_finite_biSup 9 := fun h => by
  have := h (α := Set ℕ) (β := Prop) (F := SupBotHom (Set ℕ) Prop) (ι := ℕ) (s := Set.univ) infi (fun i => {i})
  refine absurd (cast this ?_) ?_
  · simp only [infi_apply, Set.mem_univ, iSup_pos]
    exact fun hf => iN (hf.subset (fun x _ => Set.mem_iUnion.2 ⟨x, rfl⟩))
  · simp [infi_apply]

-- `Set.map_finite_iInf` idx 7: necessary (F = Bool ≃ Bool, negation, iota = Empty)
theorem c6_42 : ¬ drop0% Set.map_finite_iInf 7 := fun h => by
  have := h (α := Bool) (β := Bool) (F := Bool ≃ Bool) (ι := Empty) bnot (fun e => e.elim)
  simp [bnot_apply] at this

-- `Set.map_finite_iInf` idx 8: necessary (cofinite map, iota = Nat, g i = complement of {i})
theorem c6_43 : ¬ drop0% Set.map_finite_iInf 8 := fun h => by
  have := h (α := Set ℕ) (β := Prop) (F := InfTopHom (Set ℕ) Prop) (ι := ℕ) cofin (fun i => {i}ᶜ)
  refine absurd (cast this.symm ?_) ?_
  · simp [cofin_apply]
  · simp only [cofin_apply, Set.compl_iInter, compl_compl]
    exact nfsN (by ext; simp)

-- `Set.map_finite_iSup` idx 7: necessary (F = Bool ≃ Bool, negation, iota = Empty)
theorem c6_44 : ¬ drop0% Set.map_finite_iSup 7 := fun h => by
  have := h (α := Bool) (β := Bool) (F := Bool ≃ Bool) (ι := Empty) bnot (fun e => e.elim)
  simp [bnot_apply] at this

-- `Set.map_finite_iSup` idx 8: necessary (infinite map, iota = Nat, g i = {i})
theorem c6_45 : ¬ drop0% Set.map_finite_iSup 8 := fun h => by
  have := h (α := Set ℕ) (β := Prop) (F := SupBotHom (Set ℕ) Prop) (ι := ℕ) infi (fun i => {i})
  refine absurd (cast this ?_) ?_
  · simp only [infi_apply]
    exact fun hf => iN (hf.subset (fun x _ => Set.mem_iUnion.2 ⟨x, rfl⟩))
  · simp [infi_apply]

-- `Set.iUnion_pi_of_monotone` idx 3: necessary (iota' = Empty, I = empty: left empty, right univ)
theorem c6_94 : ¬ drop0% Set.iUnion_pi_of_monotone 3 := fun h => by
  have := h (ι := Unit) (ι' := Empty) (α := fun _ => Unit) (I := ∅) (s := fun _ _ => Set.univ)
    Set.finite_empty (fun i hi => absurd hi (Set.notMem_empty i))
  replace this := congrArg (fun S => (fun _ => ()) ∈ S) this
  simp at this

-- `Set.iUnion_pi_of_monotone` idx 7: necessary (iota = iota' = Nat, I = univ, s i j = (i ≤ j) on Unit)
theorem c6_95 : ¬ drop0% Set.iUnion_pi_of_monotone 7 := fun h => by
  have := h (ι := ℕ) (ι' := ℕ) (α := fun _ => Unit) (I := Set.univ) (s := fun i j => {_u | i ≤ j})
    (fun i _ a b hab x hx => le_trans hx hab)
  replace this := congrArg (fun S => (fun _ => ()) ∈ S) this
  refine absurd (cast this.symm ?_) ?_
  · simpa using fsm_r
  · simpa using fsm_nl

-- `Set.iUnion_pi_of_monotone` idx 8: necessary (iota = Bool, s true j = (j = 0), s false j = (j = 1))
theorem c6_96 : ¬ drop0% Set.iUnion_pi_of_monotone 8 := fun h => by
  have := h (ι := Bool) (ι' := ℕ) (α := fun _ => Unit) (I := Set.univ) (s := fun i j => {_u | j = selN i})
    (Set.toFinite _)
  replace this := congrArg (fun S => (fun _ => ()) ∈ S) this
  refine absurd (cast this.symm ?_) ?_
  · simpa using hs_r
  · simpa using hs_nl

-- `Set.iUnion_univ_pi_of_monotone` idx 3: necessary (iota = iota' = Empty: left empty, right univ)
theorem c6_97 : ¬ drop0% Set.iUnion_univ_pi_of_monotone 3 := fun h => by
  have := h (ι := Empty) (ι' := Empty) (α := fun _ => Unit) (s := fun _ _ => Set.univ)
    (fun i => i.elim)
  replace this := congrArg (fun S => (fun _ => ()) ∈ S) this
  simp at this

-- `Set.iUnion_univ_pi_of_monotone` idx 4: necessary (iota = iota' = Nat, s i j = (i ≤ j) on Unit)
theorem c6_98 : ¬ drop0% Set.iUnion_univ_pi_of_monotone 4 := fun h => by
  have := h (ι := ℕ) (ι' := ℕ) (α := fun _ => Unit) (s := fun i j => {_u | i ≤ j})
    (fun i a b hab x hx => le_trans hx hab)
  replace this := congrArg (fun S => (fun _ => ()) ∈ S) this
  refine absurd (cast this.symm ?_) ?_
  · simpa using fsm_r
  · simpa using fsm_nl

-- `Set.iUnion_univ_pi_of_monotone` idx 7: necessary (iota = Bool, s true j = (j = 0), s false j = (j = 1))
theorem c6_99 : ¬ drop0% Set.iUnion_univ_pi_of_monotone 7 := fun h => by
  have := h (ι := Bool) (ι' := ℕ) (α := fun _ => Unit) (s := fun i j => {_u | j = selN i})
  replace this := congrArg (fun S => (fun _ => ()) ∈ S) this
  refine absurd (cast this.symm ?_) ?_
  · simpa using hs_r
  · simpa using hs_nl

-- `Set.Finite.biInf_iSup_eq` idx 3: necessary (kappa = False, s = empty: left top, right bottom)
theorem c6_100 : ¬ drop0% Set.Finite.biInf_iSup_eq 3 := fun h => by
  have := h (α := Prop) (ι := Unit) (κ := fun _ => False) (s := ∅) Set.finite_empty (f := fun _ _ => True)
  refine absurd (cast this ?_) ?_
  · simp
  · simp only [iSup_Prop_eq, not_exists]; intro g; exact (g ()).elim

-- `Set.Finite.biSup_iInf_eq` idx 3: necessary (kappa = False, s = empty: left bottom, right top)
theorem c6_102 : ¬ drop0% Set.Finite.biSup_iInf_eq 3 := fun h => by
  have := h (α := Prop) (ι := Unit) (κ := fun _ => False) (s := ∅) Set.finite_empty (f := fun _ _ => True)
  refine absurd (cast this.symm ?_) ?_
  · simp only [iInf_Prop_eq]; intro g; exact (g ()).elim
  · simp

namespace W3c6

/-- Closed sets of the reals (from Probe2): points at distance at least 1/(n+1) from 0 (for true),
resp. the point 0 (for false). -/
noncomputable def clF (n : ℕ) (b : Bool) : TopologicalSpace.Closeds ℝ :=
  if b then ⟨{x | 1 / ((n : ℝ) + 1) ≤ |x|}, isClosed_le continuous_const continuous_abs⟩
  else ⟨{0}, isClosed_singleton⟩

-- helper: the sup of the pointwise infima is bottom
theorem clL : (⨆ n, ⨅ b, clF n b) = ⊥ := by
  refine iSup_eq_bot.mpr fun n => eq_bot_iff.mpr ?_
  refine le_trans (le_inf (iInf_le _ true) (iInf_le _ false)) ?_
  rw [← SetLike.coe_subset_coe, TopologicalSpace.Closeds.coe_inf, TopologicalSpace.Closeds.coe_bot]
  rintro x ⟨h1, h2⟩
  simp [clF] at h1 h2
  subst h2
  simp at h1
  have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  linarith

-- helper: 0 lies in every closed sup of a choice
theorem clR : (0 : ℝ) ∈ (⨅ g : (ℕ → Bool), ⨆ n, clF n (g n)) := by
  rw [TopologicalSpace.Closeds.mem_iInf]
  intro g
  by_cases hg : ∃ n, g n = false
  · obtain ⟨n, hn⟩ := hg
    apply le_iSup (fun n => clF n (g n)) n
    simp [clF, hn]
  · have hg' : ∀ n, g n = true := fun n => by
      by_contra hc; exact hg ⟨n, by simpa using hc⟩
    have hsub : ∀ n : ℕ, (1 / ((n : ℝ) + 1)) ∈ (⨆ n, clF n (g n)) := fun n => by
      apply le_iSup (fun n => clF n (g n)) n
      simp only [clF, hg' n, ite_true]
      show 1 / ((n : ℝ) + 1) ≤ |1 / ((n : ℝ) + 1)|
      exact le_abs_self _
    exact (⨆ n, clF n (g n)).isClosed.mem_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
      (Filter.Eventually.of_forall hsub)

theorem clNe : (⨆ n, ⨅ b, clF n b) ≠ ⨅ g : (ℕ → Bool), ⨆ n, clF n (g n) := fun e => by
  have := clR
  rw [← e, clL, ← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot] at this
  exact this

end W3c6
open W3c6

-- `Set.Finite.biInf_iSup_eq` idx 6: necessary (alpha = order dual of TopologicalSpace.Closeds Real (a frame), s = univ in Nat, kappa = Bool, f = clF: complete distributivity fails)
theorem c6_101 : ¬ (∀ {α : Type} {ι : Type} {κ : ι → Type} [Nonempty ((a : ι) → κ a)] [Order.Frame α] {s : Set ι}
    {f : (a : ι) → κ a → α}, ⨅ a ∈ s, ⨆ (b : κ a), f a b = ⨆ (g : (a : ι) → κ a), ⨅ a ∈ s, f a (g a)) := fun h => by
  have := h (α := (TopologicalSpace.Closeds ℝ)ᵒᵈ) (ι := ℕ) (κ := fun _ => Bool) (s := Set.univ)
    (f := fun n b => OrderDual.toDual (clF n b))
  replace this := congrArg OrderDual.ofDual this
  simp only [ofDual_iInf, ofDual_iSup, OrderDual.ofDual_toDual, Set.mem_univ, iInf_pos, iSup_pos] at this
  exact clNe this

-- `Set.Finite.biSup_iInf_eq` idx 6: necessary (alpha = TopologicalSpace.Closeds Real (a coframe), s = univ in Nat, kappa = Bool, f = clF: complete distributivity fails)
theorem c6_103 : ¬ (∀ {α : Type} {ι : Type} {κ : ι → Type} [Nonempty ((a : ι) → κ a)] [Order.Coframe α] {s : Set ι}
    {f : (a : ι) → κ a → α}, ⨆ a ∈ s, ⨅ (b : κ a), f a b = ⨅ (g : (a : ι) → κ a), ⨆ a ∈ s, f a (g a)) := fun h => by
  have := h (α := TopologicalSpace.Closeds ℝ) (ι := ℕ) (κ := fun _ => Bool) (s := Set.univ) (f := clF)
  simp only [Set.mem_univ, iInf_pos, iSup_pos] at this
  exact clNe this

namespace W3c6

-- helper: a set of U2 containing both points is bounded neither above nor below
theorem u2_nbb {s : Set U2} (h1 : Sum.inl () ∈ s) (h2 : Sum.inr () ∈ s) : ¬ BddBelow s := fun ⟨b, hb⟩ =>
  by have := (u2_le _ _ (hb h1)).symm.trans (u2_le _ _ (hb h2)); simp at this
theorem u2_nba {s : Set U2} (h1 : Sum.inl () ∈ s) (h2 : Sum.inr () ∈ s) : ¬ BddAbove s := fun ⟨b, hb⟩ =>
  by have := (u2_le _ _ (hb h1)).trans (u2_le _ _ (hb h2)).symm; simp at this
-- helper: nothing is bounded in the empty type
theorem e_nbb (s : Set Empty) : ¬ BddBelow s := fun ⟨b, _⟩ => b.elim
theorem e_nba (s : Set Empty) : ¬ BddAbove s := fun ⟨b, _⟩ => b.elim

-- helper: a finite exhaustion of the naturals by initial segments
def exN : (Set.univ : Set ℕ).FiniteExhaustion where
  toFun n := {m | m ≤ n}
  finite' n := (Set.finite_le_nat n).to_subtype
  subset_succ' n := fun m (hm : m ≤ n) => (show m ≤ n + 1 by omega)
  iUnion_eq' := Set.eq_univ_of_forall fun m => Set.mem_iUnion.2 ⟨m, le_refl m⟩

end W3c6
open W3c6

-- `Set.Finite.bddBelow` idx 2: necessary (alpha = Unit + Unit with incomparable points, s = univ)
theorem c6_104 : ¬ drop0% Set.Finite.bddBelow 2 := fun h =>
  u2_nbb (Set.mem_univ _) (Set.mem_univ _) (h (α := U2) (s := Set.univ) (Set.toFinite _))

-- `Set.Finite.bddBelow` idx 3: necessary (alpha = Empty, s = empty)
theorem c6_105 : ¬ drop0% Set.Finite.bddBelow 3 := fun h =>
  e_nbb _ (h (α := Empty) (s := ∅) Set.finite_empty)

-- `Set.Finite.bddBelow` idx 5: necessary (alpha = Int, s = univ)
theorem c6_106 : ¬ drop0% Set.Finite.bddBelow 5 := fun h =>
  not_bddBelow_univ (h (α := ℤ) (s := Set.univ))

-- `Set.Finite.bddAbove` idx 2: necessary (alpha = Unit + Unit, s = univ)
theorem c6_107 : ¬ drop0% Set.Finite.bddAbove 2 := fun h =>
  u2_nba (Set.mem_univ _) (Set.mem_univ _) (h (α := U2) (s := Set.univ) (Set.toFinite _))

-- `Set.Finite.bddAbove` idx 3: necessary (alpha = Empty, s = empty)
theorem c6_108 : ¬ drop0% Set.Finite.bddAbove 3 := fun h =>
  e_nba _ (h (α := Empty) (s := ∅) Set.finite_empty)

-- `Set.Finite.bddBelow_biUnion` idx 3: necessary (alpha = Unit + Unit, I = Bool, S i = {sel i})
theorem c6_109 : ¬ drop0% Set.Finite.bddBelow_biUnion 3 := fun h => by
  have := (h (α := U2) (β := Bool) (I := Set.univ) (S := fun i => {sel i}) (Set.toFinite _)).2
    (fun i _ => bddBelow_singleton)
  exact u2_nbb (Set.mem_biUnion (x := true) (Set.mem_univ _) rfl)
    (Set.mem_biUnion (x := false) (Set.mem_univ _) rfl) this

-- `Set.Finite.bddBelow_biUnion` idx 4: necessary (alpha = Empty, I = empty)
theorem c6_110 : ¬ drop0% Set.Finite.bddBelow_biUnion 4 := fun h =>
  e_nbb _ ((h (α := Empty) (β := Unit) (I := ∅) (S := fun _ => ∅) Set.finite_empty).2 (fun i hi => hi.elim))

-- `Set.Finite.bddBelow_biUnion` idx 7: necessary (alpha = Int, I = univ in Nat, S i = {-i})
theorem c6_111 : ¬ drop0% Set.Finite.bddBelow_biUnion 7 := fun h => by
  obtain ⟨b, hb⟩ := (h (α := ℤ) (β := ℕ) (I := Set.univ) (S := fun i => {-(i:ℤ)})).2
    (fun i _ => bddBelow_singleton)
  have := hb (Set.mem_biUnion (x := (-b).toNat + 1) (Set.mem_univ _) rfl)
  omega

-- `Set.Finite.bddAbove_biUnion` idx 3: necessary (alpha = Unit + Unit, I = Bool, S i = {sel i})
theorem c6_112 : ¬ drop0% Set.Finite.bddAbove_biUnion 3 := fun h => by
  have := (h (α := U2) (β := Bool) (I := Set.univ) (S := fun i => {sel i}) (Set.toFinite _)).2
    (fun i _ => bddAbove_singleton)
  exact u2_nba (Set.mem_biUnion (x := true) (Set.mem_univ _) rfl)
    (Set.mem_biUnion (x := false) (Set.mem_univ _) rfl) this

-- `Set.Finite.bddAbove_biUnion` idx 4: necessary (alpha = Empty, I = empty)
theorem c6_113 : ¬ drop0% Set.Finite.bddAbove_biUnion 4 := fun h =>
  e_nba _ ((h (α := Empty) (β := Unit) (I := ∅) (S := fun _ => ∅) Set.finite_empty).2 (fun i hi => hi.elim))

-- `Set.Finite.bddAbove_biUnion` idx 7: necessary (alpha = Nat, I = univ, S i = {i})
theorem c6_114 : ¬ drop0% Set.Finite.bddAbove_biUnion 7 := fun h => by
  obtain ⟨b, hb⟩ := (h (α := ℕ) (β := ℕ) (I := Set.univ) (S := fun i => {i})).2
    (fun i _ => bddAbove_singleton)
  have := hb (Set.mem_biUnion (x := b + 1) (Set.mem_univ _) rfl)
  omega

-- `Set.infinite_of_not_bddBelow` idx 2: necessary (alpha = Unit + Unit, s = univ: finite, not bounded)
theorem c6_115 : ¬ drop0% Set.infinite_of_not_bddBelow 2 := fun h =>
  h (α := U2) (s := Set.univ) (u2_nbb (Set.mem_univ _) (Set.mem_univ _)) (Set.toFinite _)

-- `Set.infinite_of_not_bddBelow` idx 3: necessary (alpha = Empty, s = empty)
theorem c6_116 : ¬ drop0% Set.infinite_of_not_bddBelow 3 := fun h =>
  h (α := Empty) (s := ∅) (e_nbb _) Set.finite_empty

-- `Set.infinite_of_not_bddAbove` idx 3: necessary (alpha = Empty, s = empty)
theorem c6_117 : ¬ drop0% Set.infinite_of_not_bddAbove 3 := fun h =>
  h (α := Empty) (s := ∅) (e_nba _) Set.finite_empty

-- `Finset.bddBelow` idx 2: necessary (alpha = Empty, s = empty)
theorem c6_118 : ¬ drop0% Finset.bddBelow 2 := fun h => e_nbb _ (h (α := Empty) ∅)

-- `Finset.bddAbove` idx 2: necessary (alpha = Empty, s = empty)
theorem c6_119 : ¬ drop0% Finset.bddAbove 2 := fun h => e_nba _ (h (α := Empty) ∅)

-- `Directed.exists_mem_subset_of_finset_subset_biUnion` idx 2: necessary (iota = Empty, s = empty)
theorem c6_120 : ¬ drop0% Directed.exists_mem_subset_of_finset_subset_biUnion 2 := fun h => by
  obtain ⟨i, _⟩ := h (α := ℕ) (ι := Empty) (f := fun e => e.elim) (fun e => e.elim) (s := ∅) (by simp)
  exact i.elim

-- `Directed.exists_mem_subset_of_finset_subset_biUnion` idx 4: necessary (f b = {b} on Bool, s = univ)
theorem c6_121 : ¬ drop0% Directed.exists_mem_subset_of_finset_subset_biUnion 4 := fun h => by
  obtain ⟨i, hi⟩ := h (α := Bool) (ι := Bool) (f := fun b => {b}) (s := Finset.univ)
    (fun x _ => Set.mem_iUnion.2 ⟨x, rfl⟩)
  have := hi (Finset.mem_coe.2 (Finset.mem_univ (!i)))
  cases i <;> simp at this

-- `Directed.exists_mem_subset_of_finset_subset_biUnion` idx 6: necessary (f = empty, s = {0})
theorem c6_122 : ¬ drop0% Directed.exists_mem_subset_of_finset_subset_biUnion 6 := fun h => by
  obtain ⟨i, hi⟩ := h (α := ℕ) (ι := Unit) (f := fun _ => ∅) (fun _ _ => ⟨(), le_rfl, le_rfl⟩) (s := {0})
  simpa using hi (Finset.mem_coe.2 (Finset.mem_singleton_self 0))

-- `DirectedOn.exists_mem_subset_of_finset_subset_biUnion` idx 4: necessary (c = empty)
theorem c6_123 : ¬ drop0% DirectedOn.exists_mem_subset_of_finset_subset_biUnion 4 := fun h => by
  obtain ⟨i, hi, _⟩ := h (α := ℕ) (ι := Unit) (f := fun _ => ∅) (c := ∅) (fun x hx => hx.elim) (s := ∅) (by simp)
  exact hi

-- `DirectedOn.exists_mem_subset_of_finset_subset_biUnion` idx 5: necessary (c = univ in Bool, f b = {b}, s = univ)
theorem c6_124 : ¬ drop0% DirectedOn.exists_mem_subset_of_finset_subset_biUnion 5 := fun h => by
  obtain ⟨i, _, hi⟩ := h (α := Bool) (ι := Bool) (f := fun b => {b}) (c := Set.univ) ⟨true, trivial⟩
    (s := Finset.univ) (fun x _ => Set.mem_biUnion (x := x) (Set.mem_univ _) rfl)
  have := hi (Finset.mem_coe.2 (Finset.mem_univ (!i)))
  cases i <;> simp at this

-- `DirectedOn.exists_mem_subset_of_finset_subset_biUnion` idx 7: necessary (c = {()}, f = empty, s = {0})
theorem c6_125 : ¬ drop0% DirectedOn.exists_mem_subset_of_finset_subset_biUnion 7 := fun h => by
  obtain ⟨i, _, hi⟩ := h (α := ℕ) (ι := Unit) (f := fun _ => ∅) (c := {()}) ⟨(), rfl⟩
    (fun x _ y _ => ⟨(), rfl, le_rfl, le_rfl⟩) (s := {0})
  simpa using hi (Finset.mem_coe.2 (Finset.mem_singleton_self 0))

-- `DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion` idx 2: necessary (c = empty, s = empty)
theorem c6_126 : ¬ drop0% DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion 2 := fun h => by
  obtain ⟨t, ht, _⟩ := h (α := ℕ) (c := ∅) (fun x hx => hx.elim) (s := ∅) Set.finite_empty (by simp)
  exact ht

-- `DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion` idx 3: necessary (c = {{true}, {false}}, s = univ)
theorem c6_127 : ¬ drop0% DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion 3 := fun h => by
  obtain ⟨t, ht, hst⟩ := h (α := Bool) (c := {{true}, {false}}) ⟨{true}, by simp⟩ (s := Set.univ)
    (Set.toFinite _) (fun x _ => by cases x <;> simp)
  rcases ht with rfl | rfl
  · simpa using hst (Set.mem_univ false)
  · simpa using hst (Set.mem_univ true)

-- `DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion` idx 5: necessary (c = initial segments of Nat, s = univ)
theorem c6_128 : ¬ drop0% DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion 5 := fun h => by
  obtain ⟨t, ⟨n, rfl⟩, hst⟩ := h (α := ℕ) (c := Set.range fun n => Set.Iic n) ⟨_, 0, rfl⟩
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact ⟨_, ⟨max a b, rfl⟩, Set.Iic_subset_Iic.2 (le_max_left a b), Set.Iic_subset_Iic.2 (le_max_right a b)⟩)
    (s := Set.univ) (fun x _ => Set.mem_sUnion.2 ⟨_, ⟨x, rfl⟩, Set.mem_Iic.2 le_rfl⟩)
  have := hst (Set.mem_univ (n + 1))
  simp at this

-- `DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion` idx 6: necessary (c = {empty}, s = {0})
theorem c6_129 : ¬ drop0% DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion 6 := fun h => by
  obtain ⟨t, ht, hst⟩ := h (α := ℕ) (c := {∅}) ⟨∅, rfl⟩ (fun x hx y hy => ⟨∅, rfl, by simp_all, by simp_all⟩)
    (s := {0}) (Set.finite_singleton 0)
  rw [Set.mem_singleton_iff.1 ht] at hst
  simpa using hst (Set.mem_singleton 0)

-- `Set.Finite.fin_embedding` idx 2: necessary (s = univ in Nat)
theorem c6_130 : ¬ drop0% Set.Finite.fin_embedding 2 := fun h => by
  obtain ⟨n, f, hf⟩ := h (α := ℕ) (s := Set.univ)
  exact iN (hf ▸ Set.finite_range f)

-- `Set.Finite.fin_param` idx 2: necessary (s = univ in Nat)
theorem c6_131 : ¬ drop0% Set.Finite.fin_param 2 := fun h => by
  obtain ⟨n, f, -, hf⟩ := h (α := ℕ) (s := Set.univ)
  exact iN (hf ▸ Set.finite_range f)

-- `Set.Finite.induction_to` idx 3: necessary (S = univ in Nat, C = finite, S0 = empty)
theorem c6_132 : ¬ drop0% Set.Finite.induction_to 3 := fun h => by
  refine iN (h (α := ℕ) (C := Set.Finite) (S := Set.univ) ∅ (Set.empty_subset _) Set.finite_empty ?_)
  intro s hs hfin
  obtain ⟨a, -, ha⟩ := Set.exists_of_ssubset hs
  exact ⟨a, ⟨Set.mem_univ a, ha⟩, hfin.insert a⟩

-- `Set.Finite.induction_to` idx 5: necessary (S = empty, S0 = {0}, C = (· = {0}))
theorem c6_133 : ¬ drop0% Set.Finite.induction_to 5 := fun h => by
  have := h (α := ℕ) (C := fun s => s = {0}) (S := ∅) Set.finite_empty {0} rfl
    (fun s hs => absurd (Set.empty_subset s) hs.not_subset)
  simp at this

-- `Set.Finite.induction_to` idx 6: necessary (C = False, S = S0 = empty)
theorem c6_134 : ¬ drop0% Set.Finite.induction_to 6 := fun h =>
  h (α := ℕ) (C := fun _ => False) (S := ∅) Set.finite_empty ∅ (Set.empty_subset _)
    (fun s hs => absurd (Set.empty_subset s) hs.not_subset)

-- `Set.Finite.induction_to` idx 7: necessary (C = (· = empty), S = {0}, S0 = empty)
theorem c6_135 : ¬ drop0% Set.Finite.induction_to 7 := fun h => by
  have := h (α := ℕ) (C := fun s => s = ∅) (S := {0}) (Set.finite_singleton 0) ∅ (Set.empty_subset _) rfl
  simp at this

-- `Set.Finite.induction_to_univ` idx 1: necessary (alpha = Nat, C = finite, S0 = empty)
theorem c6_136 : ¬ drop0% Set.Finite.induction_to_univ 1 := fun h => by
  refine iN (h (α := ℕ) (C := Set.Finite) ∅ Set.finite_empty ?_)
  intro S hS hfin
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem S).1 hS
  exact ⟨a, ha, hfin.insert a⟩

-- `Set.Finite.induction_to_univ` idx 4: necessary (alpha = Unit, C = False)
theorem c6_137 : ¬ drop0% Set.Finite.induction_to_univ 4 := fun h =>
  h (α := Unit) (C := fun _ => False) ∅ (fun S _ hC => hC.elim)

-- `Set.Finite.induction_to_univ` idx 5: necessary (alpha = Unit, C = (· = empty), S0 = empty)
theorem c6_138 : ¬ drop0% Set.Finite.induction_to_univ 5 := fun h => by
  have := h (α := Unit) (C := fun s => s = ∅) ∅ rfl
  simp at this

-- `Set.exists_max_image` idx 5: necessary (s = univ in Nat, f = id)
theorem c6_139 : ¬ drop0% Set.exists_max_image 5 := fun h => by
  obtain ⟨a, -, ha⟩ := h (α := ℕ) (β := ℕ) Set.univ id ⟨0, trivial⟩
  have := ha (a + 1) trivial
  simp at this

-- `Set.exists_min_image` idx 5: necessary (s = univ in Int, f = id)
theorem c6_140 : ¬ drop0% Set.exists_min_image 5 := fun h => by
  obtain ⟨a, -, ha⟩ := h (α := ℤ) (β := ℤ) Set.univ id ⟨0, trivial⟩
  have := ha (a - 1) trivial
  simp at this

-- `Set.exists_upper_bound_image` idx 2: necessary (alpha = Empty)
theorem c6_141 : ¬ drop0% Set.exists_upper_bound_image 2 := fun h => by
  obtain ⟨a, -⟩ := h (α := Empty) (β := ℕ) ∅ (fun e => e.elim) Set.finite_empty
  exact a.elim

-- `Set.exists_upper_bound_image` idx 6: necessary (s = univ in Nat, f = id)
theorem c6_142 : ¬ drop0% Set.exists_upper_bound_image 6 := fun h => by
  obtain ⟨a, ha⟩ := h (α := ℕ) (β := ℕ) Set.univ id
  have := ha (a + 1) trivial
  simp at this

-- `Set.exists_lower_bound_image` idx 2: necessary (alpha = Empty)
theorem c6_143 : ¬ drop0% Set.exists_lower_bound_image 2 := fun h => by
  obtain ⟨a, -⟩ := h (α := Empty) (β := ℕ) ∅ (fun e => e.elim) Set.finite_empty
  exact a.elim

-- `Set.exists_lower_bound_image` idx 6: necessary (s = univ in Int, f = id)
theorem c6_144 : ¬ drop0% Set.exists_lower_bound_image 6 := fun h => by
  obtain ⟨a, ha⟩ := h (α := ℤ) (β := ℤ) Set.univ id
  have := ha (a - 1) trivial
  simp at this

-- `List.finite_length_eq` idx 1: necessary (alpha = Nat, n = 1: all singleton lists)
theorem c6_145 : ¬ drop0% List.finite_length_eq 1 := fun h =>
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => [n]) (fun a b e => by simpa using e)
    (fun n => rfl) (h ℕ 1)

-- `List.finite_length_lt` idx 1: necessary (alpha = Nat, n = 2)
theorem c6_146 : ¬ drop0% List.finite_length_lt 1 := fun h =>
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => [n]) (fun a b e => by simpa using e)
    (fun n => show 1 < 2 by omega) (h ℕ 2)

-- `List.finite_length_le` idx 1: necessary (alpha = Nat, n = 1)
theorem c6_147 : ¬ drop0% List.finite_length_le 1 := fun h =>
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => [n]) (fun a b e => by simpa using e)
    (fun n => le_refl 1) (h ℕ 1)

-- `Finite.Set.finite_seq` idx 4: necessary (f = constant maps Unit to Nat, s = univ)
theorem c6_148 : ¬ drop0% Finite.Set.finite_seq 4 := fun h => by
  have := h (α := Unit) (β := ℕ) (Set.range fun n _ => n) Set.univ
  exact nfN (Set.eq_univ_of_forall fun n => by simp [Set.seq_def]) this

-- `Finite.Set.finite_seq` idx 5: necessary (f = {id}, s = univ in Nat)
theorem c6_149 : ¬ drop0% Finite.Set.finite_seq 5 := fun h => by
  have := h (α := ℕ) (β := ℕ) {id} Set.univ
  exact nfN (Set.eq_univ_of_forall fun n => by simp [Set.seq_def]) this

-- `Set.Finite.bind` idx 4: necessary (s = univ in Nat, f n = {n})
theorem c6_150 : ¬ drop0% Set.Finite.bind 4 := fun h => by
  have := h (α := ℕ) (β := ℕ) (s := Set.univ) (f := fun n => {n}) (fun _ _ => Set.finite_singleton _)
  exact nfsN (Set.eq_univ_of_forall fun n => by simp [Set.bind_def]) this

-- `Set.Finite.bind` idx 5: necessary (s = {0}, f = const univ)
theorem c6_151 : ¬ drop0% Set.Finite.bind 5 := fun h => by
  have := h (α := ℕ) (β := ℕ) (s := {0}) (f := fun _ => Set.univ) (Set.finite_singleton 0)
  exact nfsN (Set.eq_univ_of_forall fun n => by simp [Set.bind_def]) this

-- `Set.Finite.seq` idx 4: necessary (f = constant maps Unit to Nat, s = univ)
theorem c6_152 : ¬ drop0% Set.Finite.seq 4 := fun h => by
  have := h (α := Unit) (β := ℕ) (f := Set.range fun n _ => n) (s := Set.univ) Set.finite_univ
  exact nfsN (Set.eq_univ_of_forall fun n => by simp [Set.seq_def]) this

-- `Set.Finite.seq` idx 5: necessary (f = {id}, s = univ in Nat)
theorem c6_153 : ¬ drop0% Set.Finite.seq 5 := fun h => by
  have := h (α := ℕ) (β := ℕ) (f := {id}) (s := Set.univ) (Set.finite_singleton _)
  exact nfsN (Set.eq_univ_of_forall fun n => by simp [Set.seq_def]) this

-- `Set.Finite.seq'` idx 4: necessary (f = constant maps Unit to Nat, s = univ)
theorem c6_154 : ¬ drop0% Set.Finite.seq' 4 := fun h => by
  have := h (α := Unit) (β := ℕ) (f := Set.range fun n _ => n) (s := Set.univ) Set.finite_univ
  exact nfsN (Set.eq_univ_of_forall fun n => by simp [Set.seq_eq_set_seq, Set.seq_def]) this

-- `Set.Finite.seq'` idx 5: necessary (f = {id}, s = univ in Nat)
theorem c6_155 : ¬ drop0% Set.Finite.seq' 5 := fun h => by
  have := h (α := ℕ) (β := ℕ) (f := {id}) (s := Set.univ) (Set.finite_singleton _)
  exact nfsN (Set.eq_univ_of_forall fun n => by simp [Set.seq_eq_set_seq, Set.seq_def]) this

-- `Set.Finite.finite_subsets` idx 2: necessary (a = univ in Nat: contains all singletons)
theorem c6_156 : ¬ drop0% Set.Finite.finite_subsets 2 := fun h =>
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ({n} : Set ℕ)) Set.singleton_injective
    (fun n => Set.subset_univ _) (h (α := ℕ) (a := Set.univ))

-- `Set.Finite.powerset` idx 2: necessary (s = univ in Nat)
theorem c6_157 : ¬ drop0% Set.Finite.powerset 2 := fun h =>
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ({n} : Set ℕ)) Set.singleton_injective
    (fun n => Set.subset_univ _) (h (α := ℕ) (s := Set.univ))

-- `Finite.Set.finite_replacement` idx 2: necessary (alpha = Nat, f = id)
theorem c6_158 : ¬ drop0% Finite.Set.finite_replacement 2 := fun h => by
  refine nfN ?_ (h (α := ℕ) (β := ℕ) id)
  exact Set.eq_univ_of_forall fun n => ⟨n, rfl⟩

-- `Set.Finite.dependent_image` idx 3: necessary (s = univ in Nat, F x _ = x)
theorem c6_159 : ¬ drop0% Set.Finite.dependent_image 3 := fun h => by
  refine nfsN ?_ (h (α := ℕ) (β := ℕ) (s := Set.univ) (fun x _ => x))
  exact Set.eq_univ_of_forall fun n => ⟨n, trivial, rfl⟩

-- `Set.Finite.exists_subset_finite_image_eq` idx 5: necessary (f = id, s = u = univ in Nat)
theorem c6_160 : ¬ drop0% Set.Finite.exists_subset_finite_image_eq 5 := fun h => by
  obtain ⟨t, -, ht, hft⟩ := h (α := ℕ) (β := ℕ) (f := id) (s := Set.univ) (u := Set.univ) (by simp)
  exact nfsN (by simpa using hft) ht

-- `Function.Injective.range_eq_range_iff_subset` idx 2: necessary (alpha = Nat, f = succ, g = id)
theorem c6_161 : ¬ drop0% Function.Injective.range_eq_range_iff_subset 2 := fun h => by
  have := (h (α := ℕ) (γ := ℕ) (f := Nat.succ) (g := id) Nat.succ_injective).2
    (fun x _ => ⟨x, rfl⟩)
  have h0 : (0 : ℕ) ∈ Set.range (id : ℕ → ℕ) := ⟨0, rfl⟩
  rw [← this] at h0
  obtain ⟨y, hy⟩ := h0
  exact Nat.succ_ne_zero y hy

-- `Function.Injective.range_eq_range_iff_subset` idx 5: necessary (alpha = Bool, f = const true, g = id)
theorem c6_162 : ¬ drop0% Function.Injective.range_eq_range_iff_subset 5 := fun h => by
  have := (h (α := Bool) (γ := Bool) (f := fun _ => true) (g := id)).2 (fun x _ => ⟨x, rfl⟩)
  have h0 : false ∈ Set.range (id : Bool → Bool) := ⟨false, rfl⟩
  rw [← this] at h0
  obtain ⟨y, hy⟩ := h0
  simp at hy

-- `Set.FiniteExhaustion.mono` idx 5: necessary (K n = {m | m ≤ n} in Nat, m = 1, n = 0)
theorem c6_163 : ¬ drop0% Set.FiniteExhaustion.mono 5 := fun h => by
  have := h (α := ℕ) (s := Set.univ) exN (m := 1) (n := 0)
  have h1 : (1 : ℕ) ∈ exN 1 := show (1 : ℕ) ≤ 1 from le_refl 1
  exact absurd (this h1) (show ¬ ((1 : ℕ) ≤ 0) by omega)
