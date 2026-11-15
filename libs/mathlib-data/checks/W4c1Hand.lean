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

open Set

namespace W4c1

/-- The trivial setoid (one class). -/
def topS (X : Type) : Setoid X := ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩

macro "w41" : tactic => `(tactic| first
  | (simp at this; done)
  | (simp [Set.ext_iff] at this; done)
  | (simp [Function.onFun] at this; done)
  | (simp_all; done)
  | (simp_all [Set.ext_iff]; done))

/-- Unit plus Unit with the sum order: two incomparable points, every map is monotone and antitone. -/
abbrev U2 := Unit ⊕ Unit
theorem u2_mono (f : U2 → Set Unit) : Monotone f := by
  rintro (⟨⟩|⟨⟩) (⟨⟩|⟨⟩) h <;> simp_all
theorem u2_anti (f : U2 → Set Unit) : Antitone f := by
  rintro (⟨⟩|⟨⟩) (⟨⟩|⟨⟩) h <;> simp_all
/-- Monotone and antitone Bool-indexed families in Set Unit. -/
theorem mB : Monotone (fun b : Bool => if b then (univ : Set Unit) else ∅) := by
  intro a b hab; cases a <;> cases b <;> first | exact absurd hab (by decide) | simp
theorem aB : Antitone (fun b : Bool => if b then (∅ : Set Unit) else univ) := by
  intro a b hab; cases a <;> cases b <;> first | exact absurd hab (by decide) | simp
/-- No point lies in every singleton of a two-point index. -/
theorem noCommon {x : ULift.{1} Bool} (h1 : x = ULift.up true) (h2 : x = ULift.up false) : False := by
  rw [h1] at h2; simp at h2
theorem pairU : Pairwise (fun i j : Unit => Disjoint (∅ : Set Unit) ∅) := fun i j hij => (hij (Subsingleton.elim i j)).elim

end W4c1

open W4c1
-- `Set.eq_univ_of_coe_eq` idx 3: necessary (gamma = empty in a nonempty beta)
theorem c1_1 : ¬ drop0% Set.eq_univ_of_coe_eq 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit Set.univ ∅) ⟨(), trivial⟩; w41
-- `Set.eq_univ_of_image_val_eq` idx 3: necessary (gamma = empty in a nonempty beta)
theorem c1_2 : ¬ drop0% Set.eq_univ_of_image_val_eq 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit Set.univ ∅) ⟨(), trivial⟩; w41
-- `Set.preimage_congr` idx 5: necessary (f = id, g = not on Bool, s = {true})
theorem c1_3 : ¬ drop0% Set.preimage_congr 5 := fun h => by
  have := Set.ext_iff.mp (@h Bool Bool id not {true}) true; w41
-- `Set.preimage_const_of_mem` idx 4: necessary (b not in s = empty)
theorem c1_4 : ¬ drop0% Set.preimage_const_of_mem 4 := fun h => by
  have := Set.ext_iff.mp (@h Unit Bool true ∅) (); w41
-- `Set.exists_eq_const_of_preimage_singleton` idx 2: necessary (alpha = beta = empty)
theorem c1_5 : ¬ drop0% Set.exists_eq_const_of_preimage_singleton 2 := fun h => by
  obtain ⟨b, _⟩ := @h Empty Empty Empty.elim (fun b => b.elim); exact b.elim
-- `Set.preimage_subtype_coe_eq_compl` idx 4: necessary (s = univ, u = v = empty)
theorem c1_6 : ¬ drop0% Set.preimage_subtype_coe_eq_compl 4 := fun h => by
  have := Set.ext_iff.mp (@h Unit univ ∅ ∅ (by simp)) ⟨(), trivial⟩; w41
-- `Set.preimage_subtype_coe_eq_compl` idx 5: necessary (s = u = v = univ)
theorem c1_7 : ¬ drop0% Set.preimage_subtype_coe_eq_compl 5 := fun h => by
  have := Set.ext_iff.mp (@h Unit univ univ univ (by simp)) ⟨(), trivial⟩; w41
-- `Set.preimage_subset` idx 6: necessary (f constant on Bool, t = {true}, s = univ)
theorem c1_8 : ¬ drop0% Set.preimage_subset 6 := fun h => by
  have := @h Bool Unit (fun _ => ()) univ {true} (by intro x _; exact ⟨true, rfl, rfl⟩) false trivial; w41
-- `Set.preimage_subset_of_surjOn` idx 5: necessary (injectivity dropped: f constant on Bool, s = {true}, t = univ)
theorem c1_9 : ¬ drop0% Set.preimage_subset_of_surjOn 5 := fun h => by
  have := @h Bool Unit (fun _ => ()) {true} univ (by intro y _; exact ⟨true, rfl, rfl⟩) false trivial; w41
-- `Function.Semiconj.set_image` idx 5: necessary (f = ga = id, gb = not on Bool)
theorem c1_10 : ¬ drop0% Function.Semiconj.set_image 5 := fun h => by
  have := Set.ext_iff.mp (@h Bool Bool id id not {true}) true; w41
-- `Function.Commute.set_image` idx 3: necessary (two different constants on Bool)
theorem c1_11 : ¬ drop0% Function.Commute.set_image 3 := fun h => by
  have := Set.ext_iff.mp (@h Bool (fun _ => true) (fun _ => false) {true}) true; w41
-- `Set.image_inter_on` idx 5: necessary (f constant, s = {true}, t = {false})
theorem c1_12 : ¬ drop0% Set.image_inter_on 5 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit (fun _ => ()) {true} {false}) (); w41
-- `Set.image_eq_preimage_of_inverse` idx 4: necessary (f : Bool to Unit, g = const true, s = {false})
theorem c1_13 : ¬ drop0% Set.image_eq_preimage_of_inverse 4 := fun h => by
  have := Set.ext_iff.mp (congrFun (@h Bool Unit (fun _ => ()) (fun _ => true) (fun _ => rfl)) {false}) (); w41
-- `Set.image_eq_preimage_of_inverse` idx 5: necessary (f = const true : Unit to Bool, g = const)
theorem c1_14 : ¬ drop0% Set.image_eq_preimage_of_inverse 5 := fun h => by
  have := Set.ext_iff.mp (congrFun (@h Unit Bool (fun _ => true) (fun _ => ()) (fun _ => rfl)) univ) false; w41
-- `Function.Involutive.image_eq_preimage_symm` idx 2: necessary (f = const true on Bool)
theorem c1_15 : ¬ drop0% Function.Involutive.image_eq_preimage_symm 2 := fun h => by
  have := Set.ext_iff.mp (congrFun (@h Bool (fun _ => true)) {false}) true; w41
-- `Set.mem_image_iff_of_inverse` idx 6: necessary (f : Bool to Unit, g = const true, s = {false})
theorem c1_16 : ¬ drop0% Set.mem_image_iff_of_inverse 6 := fun h => by
  have := @h Bool Unit (fun _ => ()) (fun _ => true) () {false} (fun _ => rfl); w41
-- `Set.mem_image_iff_of_inverse` idx 7: necessary (f = const true : Unit to Bool, b = false)
theorem c1_17 : ¬ drop0% Set.mem_image_iff_of_inverse 7 := fun h => by
  have := @h Unit Bool (fun _ => true) (fun _ => ()) false univ (fun _ => rfl); w41
-- `Set.prod_quotient_preimage_eq_image` idx 5: necessary (g = const false, h = const true, r = {(false, false)})
theorem c1_18 : ¬ drop0% Set.prod_quotient_preimage_eq_image 5 := fun h => by
  have := Set.ext_iff.mp (@h Unit Bool (topS Unit) (fun _ => false) (fun _ => true) {(false, false)})
    (Quotient.mk _ (), Quotient.mk _ ()); w41
-- `Set.powerset_insert_injOn` idx 3: necessary (a in s: insert a empty = insert a {a})
theorem c1_19 : ¬ drop0% Set.powerset_insert_injOn 3 := fun h => by
  have := @h Unit {()} () ∅ (by simp) {()} (by simp) (by simp); w41
-- `Set.image_compl_eq_range_sdiff_image` idx 3: necessary (f constant on Bool, s = {true})
theorem c1_20 : ¬ drop0% Set.image_compl_eq_range_sdiff_image 3 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit (fun _ => ()) {true}) (); w41
-- `Set.image_compl_eq_range_diff_image` idx 3: necessary (f constant on Bool, s = {true})
theorem c1_21 : ¬ drop0% Set.image_compl_eq_range_diff_image 3 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit (fun _ => ()) {true}) (); w41
-- `Set.range_sdiff_image` idx 3: necessary (f constant on Bool, s = {true})
theorem c1_22 : ¬ drop0% Set.range_sdiff_image 3 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit (fun _ => ()) {true}) (); w41
-- `Set.range_diff_image` idx 3: necessary (f constant on Bool, s = {true})
theorem c1_23 : ¬ drop0% Set.range_diff_image 3 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit (fun _ => ()) {true}) (); w41
-- `Set.range_eq_singleton_iff` idx 3: necessary (empty index)
theorem c1_24 : ¬ drop0% Set.range_eq_singleton_iff 3 := fun h => by
  have := Set.ext_iff.mp ((@h Unit False (fun x => x.elim) ()).mpr (fun x => x.elim)) (); w41
-- `Set.range_eq_singleton` idx 3: necessary (empty index)
theorem c1_25 : ¬ drop0% Set.range_eq_singleton 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit False (fun x => x.elim) () (fun x => x.elim)) (); w41
-- `Set.preimage_subset_preimage_iff` idx 5: necessary (f from Empty, s = univ, t = empty)
theorem c1_26 : ¬ drop0% Set.preimage_subset_preimage_iff 5 := fun h => by
  have := (@h Unit Empty univ ∅ Empty.elim).mp (by intro x; exact x.elim) (Set.mem_univ ()); w41
-- `Set.preimage_eq_preimage'` idx 5: necessary (f from Empty, s = univ, t = empty)
theorem c1_27 : ¬ drop0% Set.preimage_eq_preimage' 5 := fun h => by
  have := (@h Unit Empty univ ∅ Empty.elim (Set.empty_subset _)).mp (by ext x; exact x.elim); w41
-- `Set.preimage_eq_preimage'` idx 6: necessary (f from Empty, s = empty, t = univ)
theorem c1_28 : ¬ drop0% Set.preimage_eq_preimage' 6 := fun h => by
  have := (@h Unit Empty ∅ univ Empty.elim (Set.empty_subset _)).mp (by ext x; exact x.elim); w41
-- `Prod.range_fst` idx 2: necessary (beta empty)
theorem c1_29 : ¬ drop0% Prod.range_fst 2 := fun h => by
  have := Set.ext_iff.mp (@h Unit Empty) (); w41
-- `Prod.range_snd` idx 2: necessary (alpha empty)
theorem c1_30 : ¬ drop0% Prod.range_snd 2 := fun h => by
  have := Set.ext_iff.mp (@h Empty Unit) (); w41
-- `Set.range_eval` idx 2: necessary (iota = Bool, alpha false empty; at Prop the statement holds)
theorem c1_31 : ¬ drop1% Set.range_eval 2 := fun h => by
  have := Set.ext_iff.mp (@h Bool (fun b => if b then PUnit else PEmpty) true) PUnit.unit
  obtain ⟨g, _⟩ := this.mpr trivial
  exact PEmpty.elim (g false)
-- `Set.range_quotient_lift` idx 4: necessary (iota = Bool, f = id, all of Bool one class; at Prop it holds)
theorem c1_32 : ¬ ∀ {α : Type} {ι : Type} {f : ι → α} [s : Setoid ι] (a b : ι), a ≈ b → f a = f b :=
  fun h => absurd (@h Bool Bool id (topS Bool) true false trivial) (by decide)
-- `Set.range_quotient_lift_on'` idx 4: necessary (iota = Bool, f = id, all of Bool one class; at Prop it holds)
theorem c1_33 : ¬ ∀ {α : Type} {ι : Type} {f : ι → α} {s : Setoid ι} (a b : ι), s a b → f a = f b :=
  fun h => absurd (@h Bool Bool id (topS Bool) true false trivial) (by decide)
-- `Set.canLift` idx 4: necessary (c from Empty to Unit, p true)
theorem c1_34 : ¬ drop0% Set.canLift 4 := fun h => by
  obtain ⟨s, hs⟩ := (@h Unit Empty Empty.elim (fun _ => True)).prf univ (fun _ _ => trivial)
  have := Set.ext_iff.mp hs (); w41
-- `Set.range_const` idx 2: necessary (empty index)
theorem c1_35 : ¬ drop0% Set.range_const 2 := fun h => by
  have := Set.ext_iff.mp (@h Unit False ()) (); w41
-- `Set.rightInverse_rangeSplitting` idx 3: necessary (f constant on Bool)
theorem c1_36 : ¬ drop0% Set.rightInverse_rangeSplitting 3 := fun h => by
  have := @h Bool Unit (fun _ => ())
  exact absurd ((this true).symm.trans (this false)) (by decide)
-- `Set.preimage_rangeSplitting` idx 3: necessary (f constant on Bool)
theorem c1_37 : ¬ drop0% Set.preimage_rangeSplitting 3 := fun h => by
  have := @h Bool Unit (fun _ => ())
  have a := (Set.ext_iff.mp (congrFun this {true}) (rangeFactorization (fun _ : Bool => ()) true)).mpr ⟨true, rfl, rfl⟩
  have b := (Set.ext_iff.mp (congrFun this {false}) (rangeFactorization (fun _ : Bool => ()) true)).mpr ⟨false, rfl, rfl⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff] at a b
  rw [a] at b; exact absurd b (by decide)
-- `Set.rangeSplitting_strictMono` idx 5: necessary (f = antitone injective Bool to Nat)
theorem c1_38 : ¬ drop0% Set.rangeSplitting_strictMono 5 := fun h => by
  have hm := @h Bool ℕ _ _ (fun b => if b then 0 else 1)
  have e : rangeSplitting (fun b : Bool => if b then 0 else 1) ⟨0, true, rfl⟩ = true := by
    have := apply_rangeSplitting (fun b : Bool => if b then (0:ℕ) else 1) ⟨0, true, rfl⟩
    revert this; cases rangeSplitting (fun b : Bool => if b then (0:ℕ) else 1) ⟨0, true, rfl⟩ <;> simp
  have := @hm ⟨0, true, rfl⟩ ⟨1, false, rfl⟩ (by show (0:ℕ) < 1; decide)
  rw [e] at this; exact absurd this (not_lt.mpr (Bool.le_true _))
-- `Set.image_of_range_union_range_eq_univ` idx 13: necessary (h constant true, f1 constant false, f = id on Unit, g from Empty)
theorem c1_39 : ¬ drop0% Set.image_of_range_union_range_eq_univ 13 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit Unit Unit Empty Empty (fun _ => true) id (fun _ => false) id Empty.elim
    Empty.elim id (funext fun x => x.elim) (Set.eq_univ_of_forall fun x => Or.inl ⟨x, rfl⟩) univ) true; w41
-- `Set.image_of_range_union_range_eq_univ` idx 14: necessary (mirror of idx 13)
theorem c1_40 : ¬ drop0% Set.image_of_range_union_range_eq_univ 14 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit Empty Empty Unit Unit (fun _ => true) Empty.elim Empty.elim id id
    (fun _ => false) id (funext fun x => x.elim) (Set.eq_univ_of_forall fun x => Or.inr ⟨x, rfl⟩) univ) true; w41
-- `Set.image_of_range_union_range_eq_univ` idx 15: necessary (f, g from Empty, beta = Unit)
theorem c1_41 : ¬ drop0% Set.image_of_range_union_range_eq_univ 15 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit Empty Empty Empty Empty id Empty.elim Empty.elim id Empty.elim Empty.elim id
    (funext fun x => x.elim) (funext fun x => x.elim) univ) (); w41
-- `Set.Subsingleton.image` idx 3: necessary (s = univ in Bool, f = id)
theorem c1_42 : ¬ drop0% Set.Subsingleton.image 3 := fun h => by
  have := @h Bool Bool univ id true ⟨true, trivial, rfl⟩ false ⟨false, trivial, rfl⟩; w41
-- `Set.subsingleton_of_preimage` idx 3: necessary (f from Empty, s = univ in Bool)
theorem c1_43 : ¬ drop0% Set.subsingleton_of_preimage 3 := fun h => by
  have := @h Empty Bool Empty.elim univ (by intro x; exact x.elim) true trivial false trivial; w41
-- `Set.Nontrivial.preimage` idx 5: necessary (f : Unit to Bool, s = univ)
theorem c1_44 : ¬ drop0% Set.Nontrivial.preimage 5 := fun h => by
  obtain ⟨x, _, y, _, hxy⟩ := @h Unit Bool (fun _ => true) univ ⟨true, trivial, false, trivial, by decide⟩
  exact hxy rfl
-- `Set.Nontrivial.image` idx 5: necessary (f constant, s = univ in Bool)
theorem c1_45 : ¬ drop0% Set.Nontrivial.image 5 := fun h => by
  obtain ⟨x, _, y, _, hxy⟩ := @h Bool Unit univ (fun _ => ()) ⟨true, trivial, false, trivial, by decide⟩
  exact hxy rfl
-- `Set.Nontrivial.image_of_injOn` idx 5: necessary (f constant, s = univ in Bool)
theorem c1_46 : ¬ drop0% Set.Nontrivial.image_of_injOn 5 := fun h => by
  obtain ⟨x, _, y, _, hxy⟩ := @h Bool Unit univ (fun _ => ()) ⟨true, trivial, false, trivial, by decide⟩
  exact hxy rfl
-- `Set.image_nontrivial` idx 4: necessary (f constant, s = univ in Bool)
theorem c1_47 : ¬ drop0% Set.image_nontrivial 4 := fun h => by
  obtain ⟨x, _, y, _, hxy⟩ := (@h Bool Unit univ (fun _ => ())).mpr ⟨true, trivial, false, trivial, by decide⟩
  exact hxy rfl
-- `Set.InjOn.image_nontrivial_iff` idx 4: necessary (f constant, s = univ in Bool)
theorem c1_48 : ¬ drop0% Set.InjOn.image_nontrivial_iff 4 := fun h => by
  obtain ⟨x, _, y, _, hxy⟩ := (@h Bool Unit univ (fun _ => ())).mpr ⟨true, trivial, false, trivial, by decide⟩
  exact hxy rfl
-- `Set.nontrivial_of_preimage` idx 3: necessary (f constant Bool to Unit, s = univ)
theorem c1_49 : ¬ drop0% Set.nontrivial_of_preimage 3 := fun h => by
  obtain ⟨x, _, y, _, hxy⟩ := @h Bool Unit (fun _ => ()) univ ⟨true, trivial, false, trivial, by decide⟩
  exact hxy rfl
-- `Function.Injective.subsingleton_image_iff` idx 3: necessary (f constant, s = univ in Bool)
theorem c1_50 : ¬ drop0% Function.Injective.subsingleton_image_iff 3 := fun h => by
  have := (@h Bool Unit (fun _ => ()) univ).mp (by intro x _ y _; rfl) (Set.mem_univ true) (Set.mem_univ false)
  w41
-- `Function.Injective.image_strictMono` idx 3: necessary (f constant: {true} < univ, same image)
theorem c1_51 : ¬ drop0% Function.Injective.image_strictMono 3 := fun h => by
  have hm := @h Bool Unit (fun _ => ())
  have := @hm {true} univ (by
    refine lt_of_le_of_ne (Set.subset_univ _) ?_
    intro e; have := Set.ext_iff.mp e false; simp at this)
  w41
-- `Function.Surjective.preimage_subset_preimage_iff` idx 5: necessary (f from Empty, s = univ, t = empty)
theorem c1_52 : ¬ drop0% Function.Surjective.preimage_subset_preimage_iff 5 := fun h => by
  have := (@h Empty Bool Empty.elim univ ∅).mp (by intro x; exact x.elim) (Set.mem_univ true); w41
-- `Function.Surjective.range_comp` idx 4: necessary (f : False to True)
theorem c1_53 : ¬ drop0% Function.Surjective.range_comp 4 := fun h => by
  have := Set.ext_iff.mp (@h Unit False True (fun x => x.elim) (fun _ => ())) (); w41
-- `Function.Injective.mem_range_iff_existsUnique` idx 3: necessary (f constant on Bool)
theorem c1_54 : ¬ drop0% Function.Injective.mem_range_iff_existsUnique 3 := fun h => by
  obtain ⟨a, _, hu⟩ := (@h Bool Unit (fun _ => ()) ()).mp ⟨true, rfl⟩
  exact absurd ((hu true rfl).trans (hu false rfl).symm) (by decide)
-- `Function.Injective.compl_image_eq` idx 3: necessary (f = const false on Bool, s = {true})
theorem c1_55 : ¬ drop0% Function.Injective.compl_image_eq 3 := fun h => by
  have := Set.ext_iff.mp (@h Bool Bool (fun _ => false) {true}) false; w41
-- `Function.Involutive.preimage` idx 2: necessary (f = const false on Bool)
theorem c1_56 : ¬ drop0% Function.Involutive.preimage 2 := fun h => by
  have := Set.ext_iff.mp (@h Bool (fun _ => false) {true}) true; w41
-- `Function.LeftInverse.image_eq` idx 4: necessary (f = id, g = not on Bool, s = {true})
theorem c1_57 : ¬ drop0% Function.LeftInverse.image_eq 4 := fun h => by
  have := Set.ext_iff.mp (@h Bool Bool id not {true}) true; w41
-- `IsCompl.preimage` idx 5: necessary (s = t = empty, f = id on Unit)
theorem c1_58 : ¬ drop0% IsCompl.preimage 5 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit id ∅ ∅).sup_eq_top (); w41
-- `Set.disjoint_preimage_iff` idx 3: necessary (f from Empty, s = t = univ in Unit)
theorem c1_59 : ¬ drop0% Set.disjoint_preimage_iff 3 := fun h => by
  have := (@h Empty Unit Empty.elim univ univ).mp (Set.disjoint_iff.mpr (by intro x; exact x.elim))
  have := Set.disjoint_iff.mp this (show () ∈ univ ∩ univ from ⟨trivial, trivial⟩); w41
-- `sigma_mk_preimage_image'` idx 5: necessary (i = j)
theorem c1_60 : ¬ drop0% sigma_mk_preimage_image' 5 := fun h => by
  have := Set.ext_iff.mp (@h Unit (fun _ => Unit) () () univ) (); w41
-- `Set.inclusion_right` idx 3: necessary (s = univ not inside t = {true} in Bool)
theorem c1_61 : ¬ indep0% Set.inclusion_right 3 := fun h => by
  have := @h Bool univ {true} ⟨true, rfl⟩ trivial false trivial; w41
-- `Set.inclusion_right` idx 5: necessary (s = empty, t = univ in Unit)
theorem c1_62 : ¬ indep0% Set.inclusion_right 5 := fun h => by
  have := @h Unit ∅ univ (Set.empty_subset _) ⟨(), trivial⟩; w41
-- `Set.inclusion_inclusion` idx 4: necessary (s = univ, t = {true}, u = univ in Bool)
theorem c1_63 : ¬ indep0% Set.inclusion_inclusion 4 := fun h => by
  have := @h Bool univ {true} univ (Set.subset_univ _) ⟨false, trivial⟩ false trivial; w41
-- `Set.inclusion_inclusion` idx 5: necessary (s = {true}, t = univ, u = {true} in Bool)
theorem c1_64 : ¬ indep0% Set.inclusion_inclusion 5 := fun h => by
  have := @h Bool {true} univ {true} (Set.subset_univ _) ⟨true, rfl⟩ false trivial; w41
-- `Set.coe_inclusion` idx 3: necessary (s = univ, t = {true} in Bool)
theorem c1_65 : ¬ indep0% Set.coe_inclusion 3 := fun h => by
  have := @h Bool univ {true} ⟨false, trivial⟩ false trivial; w41
-- `Set.inclusion_inj` idx 3: necessary (s = univ, t = {true} in Bool)
theorem c1_66 : ¬ indep0% Set.inclusion_inj 3 := fun h => by
  have := @h Bool univ {true} ⟨false, trivial⟩ ⟨false, trivial⟩ false trivial; w41
-- `Set.inclusion_le_inclusion` idx 4: necessary (s = univ, t = {true} in Bool)
theorem c1_67 : ¬ indep0% Set.inclusion_le_inclusion 4 := fun h => by
  have := @h Bool _ univ {true} ⟨false, trivial⟩ ⟨false, trivial⟩ false trivial; w41
-- `Set.inclusion_lt_inclusion` idx 4: necessary (s = univ, t = {true} in Bool)
theorem c1_68 : ¬ indep0% Set.inclusion_lt_inclusion 4 := fun h => by
  have := @h Bool _ univ {true} ⟨false, trivial⟩ ⟨false, trivial⟩ false trivial; w41
-- `LE.le.ssubset_of_mem_notMem` idx 4: necessary (s = {true}, t = {false}, a = false)
theorem c1_69 : ¬ drop0% LE.le.ssubset_of_mem_notMem 4 := fun h => by
  have := (@h Bool {true} {false} false rfl (by simp)).1 (Set.mem_singleton true); w41
-- `HasSubset.Subset.ssubset_of_mem_notMem` idx 4: necessary (s = {true}, t = {false}, a = false)
theorem c1_70 : ¬ drop0% HasSubset.Subset.ssubset_of_mem_notMem 4 := fun h => by
  have := (@h Bool {true} {false} false rfl (by simp)).1 (Set.mem_singleton true); w41
-- `Set.eq_of_nonempty_of_subsingleton` idx 4: necessary (s = empty, t = univ in Unit)
theorem c1_71 : ¬ drop0% Set.eq_of_nonempty_of_subsingleton 4 := fun h => by
  have := Set.ext_iff.mp (@h Unit _ ∅ univ ⟨⟨(), trivial⟩⟩) (); w41
-- `Set.insert_sdiff_eq_singleton` idx 3: necessary (a in s = univ)
theorem c1_72 : ¬ drop0% Set.insert_sdiff_eq_singleton 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit () univ) (); w41
-- `Set.insert_diff_eq_singleton` idx 3: necessary (a in s = univ)
theorem c1_73 : ¬ drop0% Set.insert_diff_eq_singleton 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit () univ) (); w41
-- `Set.range_ite_const` idx 6: necessary (p never holds, x = true, y = false)
theorem c1_74 : ¬ drop0% Set.range_ite_const 6 := fun h => by
  have := Set.ext_iff.mp (@h Unit Bool (fun _ => False) _ true false ⟨(), id⟩) true; w41
-- `Set.biInter_subset_of_mem` idx 5: necessary (x not in s = empty, t = empty)
theorem c1_75 : ¬ drop0% Set.biInter_subset_of_mem 5 := fun h => by
  have := @h Unit Unit ∅ (fun _ => ∅) () () (by simp); w41
-- `Set.biInter_subset_biInter_left` idx 5: necessary (s = empty, s' = univ, t = empty)
theorem c1_76 : ¬ drop0% Set.biInter_subset_biInter_left 5 := fun h => by
  have := @h Unit Unit ∅ univ (fun _ => ∅) () (by simp); w41
-- `Set.biInter_mono` idx 6: necessary (s = univ, s' = empty, t = t' = empty)
theorem c1_77 : ¬ drop0% Set.biInter_mono 6 := fun h => by
  have := @h Unit Unit univ ∅ (fun _ => ∅) (fun _ => ∅) (fun _ _ => subset_rfl) () (by simp); w41
-- `Set.biInter_const` idx 3: necessary (s = empty, t = empty)
theorem c1_78 : ¬ drop0% Set.biInter_const 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit ∅ ∅) (); w41
-- `Set.biInter_inter` idx 3: necessary (s = empty, f = t = empty)
theorem c1_79 : ¬ drop0% Set.biInter_inter 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit ∅ (fun _ => ∅) ∅) (); w41
-- `Set.inter_biInter` idx 3: necessary (s = empty, f = t = empty)
theorem c1_80 : ¬ drop0% Set.inter_biInter 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit ∅ (fun _ => ∅) ∅) (); w41
-- `Set.mem_sUnion_of_mem` idx 4: necessary (x not in t = empty, S = {empty})
theorem c1_81 : ¬ drop0% Set.mem_sUnion_of_mem 4 := fun h => by
  have := @h Unit () ∅ {∅} rfl; w41
-- `Set.subset_sUnion_of_subset` idx 4: necessary (s = univ, u = empty, t = {empty})
theorem c1_82 : ¬ drop0% Set.subset_sUnion_of_subset 4 := fun h => by
  have := @h Unit univ {∅} ∅ rfl () trivial; w41
-- `Set.sUnion_subset` idx 3: necessary (S = {univ}, t = empty)
theorem c1_83 : ¬ drop0% Set.sUnion_subset 3 := fun h => by
  have := @h Unit {univ} ∅ () (by simp); w41
-- `Set.sUnion_mono_subsets` idx 3: necessary (f = const empty, s = {univ})
theorem c1_84 : ¬ drop0% Set.sUnion_mono_subsets 3 := fun h => by
  have := @h Unit {univ} (fun _ => ∅) () (by simp); w41
-- `Set.sUnion_mono_supsets` idx 3: necessary (f = const univ, s = {empty})
theorem c1_85 : ¬ drop0% Set.sUnion_mono_supsets 3 := fun h => by
  have := @h Unit {∅} (fun _ => univ) () (by simp); w41
-- `Set.subset_sInter` idx 3: necessary (S = {empty}, t = univ)
theorem c1_86 : ¬ drop0% Set.subset_sInter 3 := fun h => by
  have := @h Unit {∅} univ () trivial; w41
-- `Set.sUnion_subset_sUnion` idx 3: necessary (S = {univ}, T = empty)
theorem c1_87 : ¬ drop0% Set.sUnion_subset_sUnion 3 := fun h => by
  have := @h Unit {univ} ∅ () (by simp); w41
-- `Set.sInter_subset_sInter` idx 3: necessary (S = {empty}, T = empty)
theorem c1_88 : ¬ drop0% Set.sInter_subset_sInter 3 := fun h => by
  have := @h Unit {∅} ∅ () (by simp); w41
-- `Set.sUnion_mem_empty_univ` idx 2: necessary (S = {{true}} in Bool)
theorem c1_89 : ¬ drop0% Set.sUnion_mem_empty_univ 2 := fun h => by
  have := @h Bool {{true}}
  simp only [Set.sUnion_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at this
  rcases this with e | e
  · have := Set.ext_iff.mp e true; simp at this
  · have := Set.ext_iff.mp e false; simp at this
-- `Set.Nonempty.of_sUnion_eq_univ` idx 1: necessary (alpha empty, s = empty)
theorem c1_90 : ¬ drop0% Set.Nonempty.of_sUnion_eq_univ 1 := fun h => by
  have := @h Empty ∅ (by ext x; exact x.elim); w41
-- `Set.iInter_eq_empty_of_eq_empty` idx 4: necessary (f = const univ)
theorem c1_91 : ¬ drop0% Set.iInter_eq_empty_of_eq_empty 4 := fun h => by
  have := Set.ext_iff.mp (@h Unit True trivial (fun _ => univ)) (); w41
-- `Set.sUnion_mono` idx 3: necessary (S = {univ}, T = empty)
theorem c1_92 : ¬ drop0% Set.sUnion_mono 3 := fun h => by
  have := @h Unit {univ} ∅ () (by simp); w41
-- `Set.sInter_mono` idx 3: necessary (S = {empty}, T = empty)
theorem c1_93 : ¬ drop0% Set.sInter_mono 3 := fun h => by
  have := @h Unit {∅} ∅ () (by simp); w41
-- `Set.iUnion_range_eq_sUnion` idx 4: necessary (beta = Empty, C = {univ})
theorem c1_94 : ¬ drop0% Set.iUnion_range_eq_sUnion 4 := fun h => by
  have := Set.ext_iff.mp (@h Unit Empty {univ} (fun _ x => x.elim)) (); w41
-- `Set.iUnion_range_eq_iUnion` idx 5: necessary (beta = Empty, C = const univ)
theorem c1_95 : ¬ drop0% Set.iUnion_range_eq_iUnion 5 := fun h => by
  have := Set.ext_iff.mp (@h Unit Empty True (fun _ => univ) (fun _ x => x.elim)) (); w41
-- `Set.biUnion_lt_eq_iUnion` idx 3: necessary (alpha = Unit has a maximum, s = univ)
theorem c1_96 : ¬ drop0% Set.biUnion_lt_eq_iUnion 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit _ (fun _ => univ)) (); w41
-- `Set.biInter_lt_eq_iInter` idx 3: necessary (alpha = Unit has a maximum, s = empty)
theorem c1_97 : ¬ drop0% Set.biInter_lt_eq_iInter 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit _ (fun _ => ∅)) (); w41
-- `Set.biUnion_gt_eq_iUnion` idx 3: necessary (alpha = Unit has a minimum, s = univ)
theorem c1_98 : ¬ drop0% Set.biUnion_gt_eq_iUnion 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit _ (fun _ => univ)) (); w41
-- `Set.biInter_gt_eq_iInf` idx 3: necessary (alpha = Unit has a minimum, s = empty)
theorem c1_99 : ¬ drop0% Set.biInter_gt_eq_iInf 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit _ (fun _ => ∅)) (); w41
-- `Set.directedOn_iUnion` idx 4: necessary (iota = Bool, f b = {b}, r = Eq; at Prop the statement holds)
theorem c1_100 : ¬ drop1% Set.directedOn_iUnion 4 := fun h => by
  have := @h (ULift Bool) Bool (· = ·) (fun b => {ULift.up b}) (by intro b x hx y hy; exact ⟨x, hx, rfl, by simp_all⟩)
  obtain ⟨z, _, h1, h2⟩ := this (ULift.up true) (Set.mem_iUnion.mpr ⟨true, rfl⟩) (ULift.up false)
    (Set.mem_iUnion.mpr ⟨false, rfl⟩)
  exact noCommon h1.symm h2.symm
-- `Set.directedOn_iUnion` idx 5: necessary (single index, f = univ in Bool, r = Eq)
theorem c1_101 : ¬ drop0% Set.directedOn_iUnion 5 := fun h => by
  have := @h Bool True (· = ·) (fun _ => univ) (fun x _ => ⟨x, subset_rfl, subset_rfl⟩)
  obtain ⟨z, _, h1, h2⟩ := this true (Set.mem_iUnion.mpr ⟨trivial, trivial⟩) false
    (Set.mem_iUnion.mpr ⟨trivial, trivial⟩)
  exact absurd (h1.trans h2.symm) (by decide)
-- `Set.directedOn_sUnion` idx 3: necessary (S = {{true}, {false}}, r = Eq)
theorem c1_102 : ¬ drop0% Set.directedOn_sUnion 3 := fun h => by
  have := @h Bool (· = ·) {{true}, {false}} (by
    intro x hx a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> exact ⟨a, ha, rfl, by simp_all⟩)
  obtain ⟨z, _, h1, h2⟩ := this true ⟨{true}, by simp, rfl⟩ false ⟨{false}, by simp, rfl⟩
  exact absurd (h1.trans h2.symm) (by decide)
-- `Set.directedOn_sUnion` idx 4: necessary (S = {univ} in Bool, r = Eq)
theorem c1_103 : ¬ drop0% Set.directedOn_sUnion 4 := fun h => by
  have := @h Bool (· = ·) {univ} (by intro a ha b hb; exact ⟨a, ha, subset_rfl, by simp_all⟩)
  obtain ⟨z, _, h1, h2⟩ := this true ⟨univ, rfl, trivial⟩ false ⟨univ, rfl, trivial⟩
  exact absurd (h1.trans h2.symm) (by decide)
-- `Function.Surjective.iUnion_comp` idx 4: necessary (f : False to True, g = univ)
theorem c1_104 : ¬ drop0% Function.Surjective.iUnion_comp 4 := fun h => by
  have := Set.ext_iff.mp (@h Unit False True (fun x => x.elim) (fun _ => univ)) (); w41
-- `Function.Surjective.iInter_comp` idx 4: necessary (f : False to True, g = empty)
theorem c1_105 : ¬ drop0% Function.Surjective.iInter_comp 4 := fun h => by
  have := Set.ext_iff.mp (@h Unit False True (fun x => x.elim) (fun _ => ∅)) (); w41
-- `Set.biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ` idx 3: necessary (Es = empty, I = empty)
theorem c1_106 : ¬ drop0% Set.biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit (fun _ => ∅) pairU ∅) (); w41
-- `Set.biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ` idx 4: necessary (iota = Bool, Es = univ, I = {true})
theorem c1_107 : ¬ drop0% Set.biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ 4 := fun h => by
  have := Set.ext_iff.mp (@h Unit Bool (fun _ => univ) (Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨true, trivial⟩) {true}) (); w41
-- `Set.coe_unionEqSigmaOfDisjoint_symm_apply` idx 3: necessary (t = const univ over Bool)
theorem c1_108 : ¬ indep0% Set.coe_unionEqSigmaOfDisjoint_symm_apply 3 := fun h => by
  have := @h Bool Unit (fun _ => univ) ⟨true, ⟨(), trivial⟩⟩ true false (by decide); w41
-- `Set.coe_snd_unionEqSigmaOfDisjoint` idx 3: necessary (t = const univ over Bool)
theorem c1_109 : ¬ indep0% Set.coe_snd_unionEqSigmaOfDisjoint 3 := fun h => by
  have := @h Bool Unit (fun _ => univ) ⟨(), Set.mem_iUnion.mpr ⟨true, trivial⟩⟩ true false (by decide); w41
-- `Set.image_projection_prod` idx 3: necessary (v false = empty, v true = univ)
theorem c1_110 : ¬ drop0% Set.image_projection_prod 3 := fun h => by
  have := Set.ext_iff.mp (@h Bool (fun _ => Unit) (fun b => if b then univ else ∅) true) (); w41
-- `Set.mapsTo_iUnion₂_iUnion₂` idx 7: necessary (s = univ, t = empty)
theorem c1_111 : ¬ drop0% Set.mapsTo_iUnion₂_iUnion₂ 7 := fun h => by
  have := @h Unit Unit True (fun _ => True) (fun _ _ => univ) (fun _ _ => ∅) id () (by simp); w41
-- `Set.mapsTo_iInter_iInter` idx 6: necessary (s = univ, t = empty)
theorem c1_112 : ¬ drop0% Set.mapsTo_iInter_iInter 6 := fun h => by
  have := @h Unit Unit True (fun _ => univ) (fun _ => ∅) id () (by simp); w41
-- `Set.mapsTo_iInter₂_iInter₂` idx 7: necessary (s = univ, t = empty)
theorem c1_113 : ¬ drop0% Set.mapsTo_iInter₂_iInter₂ 7 := fun h => by
  have := @h Unit Unit True (fun _ => True) (fun _ _ => univ) (fun _ _ => ∅) id () (by simp); w41
-- `Set.surjective_iff_surjective_of_iUnion_eq_univ` idx 5: necessary (empty index, f from Empty)
theorem c1_114 : ¬ drop0% Set.surjective_iff_surjective_of_iUnion_eq_univ 5 := fun h => by
  obtain ⟨a, _⟩ := (@h Empty Unit False Empty.elim (fun x => x.elim)).mpr (fun i => i.elim) ()
  exact a.elim
-- `Set.bijective_iff_bijective_of_iUnion_eq_univ` idx 5: necessary (empty index, f from Empty)
theorem c1_115 : ¬ drop0% Set.bijective_iff_bijective_of_iUnion_eq_univ 5 := fun h => by
  obtain ⟨a, _⟩ := ((@h Empty Unit False Empty.elim (fun x => x.elim)).mpr (fun i => i.elim)).2 ()
  exact a.elim
-- `Set.InjOn.image_iInter_eq` idx 3: necessary (empty index, f = const true : Unit to Bool)
theorem c1_116 : ¬ drop0% Set.InjOn.image_iInter_eq 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit Bool False (fun x => x.elim) (fun _ => true) (by intro x hx; simp at hx)) false
  w41
-- `Set.InjOn.image_iInter_eq` idx 6: necessary (iota = Bool, s b = {b}, f constant; at Prop the statement holds)
theorem c1_117 : ¬ drop1% Set.InjOn.image_iInter_eq 6 := fun h => by
  have := (Set.ext_iff.mp (@h (ULift Bool) PUnit Bool _ (fun b => {ULift.up b}) (fun _ => PUnit.unit))
    PUnit.unit).mpr (by simp)
  obtain ⟨x, hx, -⟩ := this
  exact noCommon (Set.mem_iInter.mp hx true) (Set.mem_iInter.mp hx false)
-- `Set.InjOn.image_biInter_eq` idx 7: necessary (iota = Bool, p = True, s b = {b}, f constant; at Prop it holds)
theorem c1_118 : ¬ drop1% Set.InjOn.image_biInter_eq 7 := fun h => by
  have := (Set.ext_iff.mp (@h (ULift Bool) PUnit Bool (fun _ => True) (fun b _ => {ULift.up b}) ⟨true, trivial⟩
    (fun _ => PUnit.unit)) PUnit.unit).mpr (by simp)
  obtain ⟨x, hx, -⟩ := this
  exact noCommon (Set.mem_iInter₂.mp hx true trivial) (Set.mem_iInter₂.mp hx false trivial)
-- `Set.image_iInter` idx 4: necessary (empty index, f from Empty)
theorem c1_119 : ¬ drop0% Set.image_iInter 4 := fun h => by
  have := Set.ext_iff.mp (@h Empty Unit False Empty.elim (fun x => x.elim)) (); w41
-- `Set.image_iInter₂` idx 5: necessary (empty index, f from Empty)
theorem c1_120 : ¬ drop0% Set.image_iInter₂ 5 := fun h => by
  have := Set.ext_iff.mp (@h Empty Unit False (fun _ => True) Empty.elim (fun x => x.elim)) (); w41
-- `Set.inj_on_iUnion_of_directed` idx 4: necessary (iota = Bool, s b = {b}, f constant; at Prop it holds)
theorem c1_121 : ¬ drop1% Set.inj_on_iUnion_of_directed 4 := fun h => by
  have := @h (ULift Bool) PUnit Bool (fun b => {ULift.up b}) (fun _ => PUnit.unit)
    (by intro b x hx y hy _; simp_all) (ULift.up true) (Set.mem_iUnion.mpr ⟨true, rfl⟩) (ULift.up false)
    (Set.mem_iUnion.mpr ⟨false, rfl⟩) rfl
  simp at this
-- `Set.inj_on_iUnion_of_directed` idx 6: necessary (single index, s = univ in Bool, f constant)
theorem c1_122 : ¬ drop0% Set.inj_on_iUnion_of_directed 6 := fun h => by
  have := @h Bool Unit True (fun _ => univ) (fun x _ => ⟨x, subset_rfl, subset_rfl⟩) (fun _ => ()) true
    (Set.mem_iUnion.mpr ⟨trivial, trivial⟩) false (Set.mem_iUnion.mpr ⟨trivial, trivial⟩) rfl; w41
-- `Set.surjOn_sUnion` idx 5: necessary (s = empty, T = {univ})
theorem c1_123 : ¬ drop0% Set.surjOn_sUnion 5 := fun h => by
  have := @h Unit Unit ∅ {univ} id () ⟨univ, rfl, trivial⟩; w41
-- `Set.surjOn_iUnion₂_iUnion₂` idx 7: necessary (s = empty, t = univ)
theorem c1_124 : ¬ drop0% Set.surjOn_iUnion₂_iUnion₂ 7 := fun h => by
  have := @h Unit Unit True (fun _ => True) (fun _ _ => ∅) (fun _ _ => univ) id () (by simp); w41
-- `Set.surjOn_iInter` idx 3: necessary (empty index, f = const true : Unit to Bool, t = univ)
theorem c1_125 : ¬ drop0% Set.surjOn_iInter 3 := fun h => by
  have := @h Unit Bool False (fun x => x.elim) univ (fun _ => true) (fun i => i.elim)
    (by intro x hx; simp at hx) false trivial; w41
-- `Set.surjOn_iInter` idx 8: necessary (iota = Bool, s b = {b}, f constant, t = univ; at Prop it holds)
theorem c1_126 : ¬ drop1% Set.surjOn_iInter 8 := fun h => by
  have := @h (ULift Bool) PUnit Bool _ (fun b => {ULift.up b}) univ (fun _ => PUnit.unit)
    (by intro b y _; exact ⟨ULift.up b, rfl, rfl⟩) PUnit.unit trivial
  obtain ⟨x, hx, -⟩ := this
  exact noCommon (Set.mem_iInter.mp hx true) (Set.mem_iInter.mp hx false)
-- `Set.surjOn_iInter_iInter` idx 3: necessary (empty index, f = const true : Unit to Bool)
theorem c1_127 : ¬ drop0% Set.surjOn_iInter_iInter 3 := fun h => by
  have := @h Unit Bool False (fun x => x.elim) (fun x => x.elim) (fun _ => true) (fun i => i.elim)
    (by intro x hx; simp at hx) false (by simp); w41
-- `Set.surjOn_iInter_iInter` idx 7: necessary (single index, s = empty, t = univ)
theorem c1_128 : ¬ drop0% Set.surjOn_iInter_iInter 7 := fun h => by
  have := @h Unit Unit True ⟨trivial⟩ (fun _ => ∅) (fun _ => univ) id (Set.injOn_of_injective Function.injective_id)
    () (by simp); w41
-- `Set.surjOn_iInter_iInter` idx 8: necessary (iota = Bool, s b = {b}, t = univ, f constant; at Prop it holds)
theorem c1_129 : ¬ drop1% Set.surjOn_iInter_iInter 8 := fun h => by
  have := @h (ULift Bool) PUnit Bool _ (fun b => {ULift.up b}) (fun _ => univ) (fun _ => PUnit.unit)
    (by intro b y _; exact ⟨ULift.up b, rfl, rfl⟩) PUnit.unit (by simp)
  obtain ⟨x, hx, -⟩ := this
  exact noCommon (Set.mem_iInter.mp hx true) (Set.mem_iInter.mp hx false)
-- `Set.bijOn_iUnion` idx 7: necessary (iota = Bool, s b = {b}, t = univ, f constant; at Prop it holds)
theorem c1_130 : ¬ drop1% Set.bijOn_iUnion 7 := fun h => by
  have := (@h (ULift Bool) PUnit Bool (fun b => {ULift.up b}) (fun _ => univ) (fun _ => PUnit.unit)
    (fun b => ⟨Set.mapsTo_univ _ _, Set.injOn_singleton _ _, by intro y _; exact ⟨ULift.up b, rfl, rfl⟩⟩)).2.1
    (Set.mem_iUnion.mpr ⟨true, rfl⟩) (Set.mem_iUnion.mpr ⟨false, rfl⟩) rfl
  simp at this
-- `Set.bijOn_iInter` idx 3: necessary (empty index, f = const true : Unit to Bool)
theorem c1_131 : ¬ drop0% Set.bijOn_iInter 3 := fun h => by
  have := (@h Unit Bool False (fun x => x.elim) (fun x => x.elim) (fun _ => true) (fun i => i.elim)
    (by intro x hx; simp at hx)).2.2 (show false ∈ ⋂ i : False, (fun x => x.elim : False → Set Bool) i by simp); w41
-- `Set.bijOn_iInter` idx 7: necessary (single index, s = empty, t = univ)
theorem c1_132 : ¬ drop0% Set.bijOn_iInter 7 := fun h => by
  have := (@h Unit Unit True ⟨trivial⟩ (fun _ => ∅) (fun _ => univ) id
    (Set.injOn_of_injective Function.injective_id)).2.2 (show () ∈ ⋂ _ : True, (univ : Set Unit) by simp); w41
-- `Set.bijOn_iInter` idx 8: necessary (iota = Bool, s b = {b}, t = univ, f constant; at Prop it holds)
theorem c1_133 : ¬ drop1% Set.bijOn_iInter 8 := fun h => by
  have := (@h (ULift Bool) PUnit Bool _ (fun b => {ULift.up b}) (fun _ => univ) (fun _ => PUnit.unit)
    (fun b => ⟨Set.mapsTo_univ _ _, Set.injOn_singleton _ _, by intro y _; exact ⟨ULift.up b, rfl, rfl⟩⟩)).2.2
    (show PUnit.unit ∈ ⋂ _ : Bool, (univ : Set PUnit) by simp)
  obtain ⟨x, hx, -⟩ := this
  exact noCommon (Set.mem_iInter.mp hx true) (Set.mem_iInter.mp hx false)
-- `Set.bijOn_iUnion_of_directed` idx 4: necessary (iota = Bool, s b = {b}, t = univ, f constant; at Prop it holds)
theorem c1_134 : ¬ drop1% Set.bijOn_iUnion_of_directed 4 := fun h => by
  have := (@h (ULift Bool) PUnit Bool (fun b => {ULift.up b}) (fun _ => univ) (fun _ => PUnit.unit)
    (fun b => ⟨Set.mapsTo_univ _ _, Set.injOn_singleton _ _, by intro y _; exact ⟨ULift.up b, rfl, rfl⟩⟩)).2.1
    (Set.mem_iUnion.mpr ⟨true, rfl⟩) (Set.mem_iUnion.mpr ⟨false, rfl⟩) rfl
  simp at this
-- `Set.bijOn_iUnion_of_directed` idx 7: necessary (single index, s = empty, t = univ)
theorem c1_135 : ¬ drop0% Set.bijOn_iUnion_of_directed 7 := fun h => by
  have := (@h Unit Unit True (fun _ => ∅) (fun x _ => ⟨x, subset_rfl, subset_rfl⟩) (fun _ => univ) id).2.2
    (show () ∈ ⋃ _ : True, (univ : Set Unit) by simp); w41
-- `Set.bijOn_iInter_of_directed` idx 3: necessary (empty index, f = const true : Unit to Bool)
theorem c1_136 : ¬ drop0% Set.bijOn_iInter_of_directed 3 := fun h => by
  have := (@h Unit Bool False (fun x => x.elim) (fun x => x.elim) (fun x => x.elim) (fun _ => true)
    (fun i => i.elim)).2.2 (show false ∈ ⋂ i : False, (fun x => x.elim : False → Set Bool) i by simp); w41
-- `Set.bijOn_iInter_of_directed` idx 5: necessary (iota = Bool, s b = {b}, t = univ, f constant; at Prop it holds)
theorem c1_137 : ¬ drop1% Set.bijOn_iInter_of_directed 5 := fun h => by
  have := (@h (ULift Bool) PUnit Bool _ (fun b => {ULift.up b}) (fun _ => univ) (fun _ => PUnit.unit)
    (fun b => ⟨Set.mapsTo_univ _ _, Set.injOn_singleton _ _, by intro y _; exact ⟨ULift.up b, rfl, rfl⟩⟩)).2.2
    (show PUnit.unit ∈ ⋂ _ : Bool, (univ : Set PUnit) by simp)
  obtain ⟨x, hx, -⟩ := this
  exact noCommon (Set.mem_iInter.mp hx true) (Set.mem_iInter.mp hx false)
-- `Set.bijOn_iInter_of_directed` idx 8: necessary (single index, s = empty, t = univ)
theorem c1_138 : ¬ drop0% Set.bijOn_iInter_of_directed 8 := fun h => by
  have := (@h Unit Unit True ⟨trivial⟩ (fun _ => ∅) (fun x _ => ⟨x, subset_rfl, subset_rfl⟩) (fun _ => univ) id).2.2
    (show () ∈ ⋂ _ : True, (univ : Set Unit) by simp); w41
-- `Set.biUnion_inter_of_pairwise_disjoint` idx 3: necessary (iota = Bool, f = univ, s = {true}, t = {false})
theorem c1_139 : ¬ drop0% Set.biUnion_inter_of_pairwise_disjoint 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit Bool (fun _ => univ) {true} {false}) (); w41
-- `Set.biUnion_iInter_of_pairwise_disjoint` idx 3: necessary (kappa empty, f = empty over Unit)
theorem c1_140 : ¬ drop0% Set.biUnion_iInter_of_pairwise_disjoint 3 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit Empty (fun _ => ∅) pairU (fun x => x.elim)) (); w41
-- `Set.biUnion_iInter_of_pairwise_disjoint` idx 5: necessary (kappa = iota = Bool, s j = {j}, f = univ)
theorem c1_141 : ¬ drop0% Set.biUnion_iInter_of_pairwise_disjoint 5 := fun h => by
  have := (Set.ext_iff.mp (@h Unit Bool Bool _ (fun _ => univ) (fun j => {j})) ()).mpr (by simp)
  obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp this
  have h1 := Set.mem_iInter.mp hi true; have h2 := Set.mem_iInter.mp hi false
  rw [Set.mem_singleton_iff] at h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
-- `Set.iUnion_prod_of_monotone` idx 6: necessary (alpha = Bool, s antitone, t monotone with disjoint supports)
theorem c1_142 : ¬ drop0% Set.iUnion_prod_of_monotone 6 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit Unit _ (fun b => if b then ∅ else univ) (fun b => if b then univ else ∅) mB)
    ((), ()); w41
-- `Set.iUnion_prod_of_monotone` idx 7: necessary (alpha = Bool, s monotone, t antitone with disjoint supports)
theorem c1_143 : ¬ drop0% Set.iUnion_prod_of_monotone 7 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit Unit _ (fun b => if b then univ else ∅) (fun b => if b then ∅ else univ) mB)
    ((), ()); w41
-- `Set.prod_iInter` idx 5: necessary (empty index, s = empty)
theorem c1_144 : ¬ drop0% Set.prod_iInter 5 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit False ∅ (fun x => x.elim)) ((), ()); w41
-- `Set.seq_mono` idx 6: necessary (s0 = {id}, s1 = empty, t0 = t1 = univ)
theorem c1_145 : ¬ drop0% Set.seq_mono 6 := fun h => by
  have := @h Unit Unit {id} ∅ univ univ subset_rfl () ⟨id, rfl, (), trivial, rfl⟩; w41
-- `Set.seq_mono` idx 7: necessary (s0 = s1 = {id}, t0 = univ, t1 = empty)
theorem c1_146 : ¬ drop0% Set.seq_mono 7 := fun h => by
  have := @h Unit Unit {id} {id} univ ∅ subset_rfl () ⟨id, rfl, (), trivial, rfl⟩; w41
-- `Set.nonempty_of_union_eq_top_of_nonempty` idx 4: necessary (alpha empty, t = empty)
theorem c1_147 : ¬ drop0% Set.nonempty_of_union_eq_top_of_nonempty 4 := fun h => by
  have := @h Empty Unit ∅ (fun _ => ∅) (by ext x; exact x.elim); w41
-- `Set.nonempty_of_nonempty_iUnion` idx 3: necessary (empty index)
theorem c1_148 : ¬ drop0% Set.nonempty_of_nonempty_iUnion 3 := fun h => by
  obtain ⟨x⟩ := @h Unit False (fun x => x.elim); exact x
-- `Set.nonempty_of_nonempty_iUnion_eq_univ` idx 3: necessary (alpha empty, empty index)
theorem c1_149 : ¬ drop0% Set.nonempty_of_nonempty_iUnion_eq_univ 3 := fun h => by
  obtain ⟨x⟩ := @h Empty False (fun x => x.elim) (by ext x; exact x.elim); exact x
-- `Set.nonempty_of_nonempty_iUnion_eq_univ` idx 4: necessary (alpha = Unit, empty index)
theorem c1_150 : ¬ drop0% Set.nonempty_of_nonempty_iUnion_eq_univ 4 := fun h => by
  obtain ⟨x⟩ := @h Unit False (fun x => x.elim) _; exact x
-- `Set.iUnion₂_subset` idx 5: necessary (s = univ, t = empty)
theorem c1_151 : ¬ drop0% Set.iUnion₂_subset 5 := fun h => by
  have := @h Unit True (fun _ => True) (fun _ _ => univ) ∅ () (by simp); w41
-- `Set.subset_iInter₂` idx 5: necessary (s = univ, t = empty)
theorem c1_152 : ¬ drop0% Set.subset_iInter₂ 5 := fun h => by
  have := @h Unit True (fun _ => True) univ (fun _ _ => ∅) () trivial; w41
-- `Set.iInter_subset_iUnion` idx 2: necessary (empty index)
theorem c1_153 : ¬ drop0% Set.iInter_subset_iUnion 2 := fun h => by
  have := @h Unit False (fun x => x.elim) () (by simp); w41
-- `Set.subset_iUnion₂_of_subset` idx 7: necessary (s = univ, t = empty)
theorem c1_154 : ¬ drop0% Set.subset_iUnion₂_of_subset 7 := fun h => by
  have := @h Unit True (fun _ => True) univ (fun _ _ => ∅) trivial trivial () trivial; w41
-- `Set.iInter₂_subset_of_subset` idx 7: necessary (s = univ, t = empty)
theorem c1_155 : ¬ drop0% Set.iInter₂_subset_of_subset 7 := fun h => by
  have := @h Unit True (fun _ => True) (fun _ _ => univ) ∅ trivial trivial () (by simp); w41
-- `Set.iUnion₂_mono'` idx 7: necessary (s = univ over True, iota' empty)
theorem c1_156 : ¬ drop0% Set.iUnion₂_mono' 7 := fun h => by
  have := @h Unit True False (fun _ => True) (fun x => x.elim) (fun _ _ => univ) (fun x => x.elim) () (by simp); w41
-- `Set.iInter₂_mono'` idx 7: necessary (iota empty, t = empty over True)
theorem c1_157 : ¬ drop0% Set.iInter₂_mono' 7 := fun h => by
  have := @h Unit False True (fun x => x.elim) (fun _ => True) (fun x => x.elim) (fun _ _ => ∅) () (by simp); w41
-- `Set.iUnion_congr_of_surjective` idx 6: necessary (h : False to True, g = univ)
theorem c1_158 : ¬ drop0% Set.iUnion_congr_of_surjective 6 := fun h => by
  have := Set.ext_iff.mp (@h Unit False True (fun x => x.elim) (fun _ => univ) (fun x => x.elim) (fun x => x.elim)) ()
  w41
-- `Set.iUnion_congr_of_surjective` idx 7: necessary (f = empty, g = univ)
theorem c1_159 : ¬ drop0% Set.iUnion_congr_of_surjective 7 := fun h => by
  have := Set.ext_iff.mp (@h Unit True True (fun _ => ∅) (fun _ => univ) id (fun y => ⟨y, rfl⟩)) (); w41
-- `Set.iInter_congr_of_surjective` idx 6: necessary (h : False to True, g = empty)
theorem c1_160 : ¬ drop0% Set.iInter_congr_of_surjective 6 := fun h => by
  have := Set.ext_iff.mp (@h Unit False True (fun x => x.elim) (fun _ => ∅) (fun x => x.elim) (fun x => x.elim)) ()
  w41
-- `Set.iInter_congr_of_surjective` idx 7: necessary (f = empty, g = univ)
theorem c1_161 : ¬ drop0% Set.iInter_congr_of_surjective 7 := fun h => by
  have := Set.ext_iff.mp (@h Unit True True (fun _ => ∅) (fun _ => univ) id (fun y => ⟨y, rfl⟩)) (); w41
-- `Set.iUnion₂_congr` idx 5: necessary (s = empty, t = univ)
theorem c1_162 : ¬ drop0% Set.iUnion₂_congr 5 := fun h => by
  have := Set.ext_iff.mp (@h Unit True (fun _ => True) (fun _ _ => ∅) (fun _ _ => univ)) (); w41
-- `Set.iInter₂_congr` idx 5: necessary (s = empty, t = univ)
theorem c1_163 : ¬ drop0% Set.iInter₂_congr 5 := fun h => by
  have := Set.ext_iff.mp (@h Unit True (fun _ => True) (fun _ _ => ∅) (fun _ _ => univ)) (); w41
-- `Set.BijOn.iUnion_comp` idx 7: necessary (s = empty, t = univ, g = univ)
theorem c1_164 : ¬ drop0% Set.BijOn.iUnion_comp 7 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit Unit ∅ univ id (fun _ => univ)) (); w41
-- `Set.BijOn.iUnion_congr` idx 8: necessary (s = empty, t = univ, f = g = univ)
theorem c1_165 : ¬ drop0% Set.BijOn.iUnion_congr 8 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit Unit ∅ univ (fun _ => univ) (fun _ => univ) id (fun _ => rfl)) (); w41
-- `Set.BijOn.iUnion_congr` idx 9: necessary (h = id on univ, f = empty, g = univ)
theorem c1_166 : ¬ drop0% Set.BijOn.iUnion_congr 9 := fun h => by
  have := Set.ext_iff.mp (@h Unit Unit Unit univ univ (fun _ => ∅) (fun _ => univ) id (Set.bijOn_id _)) (); w41
-- `Set.iUnion_const` idx 2: necessary (empty index, s = univ)
theorem c1_167 : ¬ drop0% Set.iUnion_const 2 := fun h => by
  have := Set.ext_iff.mp (@h Unit False univ) (); w41
-- `Set.iUnion_eq_const` idx 2: necessary (empty index, s = univ)
theorem c1_168 : ¬ drop0% Set.iUnion_eq_const 2 := fun h => by
  have := Set.ext_iff.mp (@h Unit False (fun x => x.elim) univ (fun x => x.elim)) (); w41
-- `Set.iInter_eq_const` idx 2: necessary (empty index, s = empty)
theorem c1_169 : ¬ drop0% Set.iInter_eq_const 2 := fun h => by
  have := Set.ext_iff.mp (@h Unit False (fun x => x.elim) ∅ (fun x => x.elim)) (); w41
-- `Set.union_iUnion` idx 2: necessary (empty index, s = univ)
theorem c1_170 : ¬ drop0% Set.union_iUnion 2 := fun h => by
  have := Set.ext_iff.mp (@h Unit False univ (fun x => x.elim)) (); w41
-- `Set.iUnion_union` idx 2: necessary (empty index, s = univ)
theorem c1_171 : ¬ drop0% Set.iUnion_union 2 := fun h => by
  have := Set.ext_iff.mp (@h Unit False univ (fun x => x.elim)) (); w41
-- `Set.inter_iInter` idx 2: necessary (empty index, s = empty)
theorem c1_172 : ¬ drop0% Set.inter_iInter 2 := fun h => by
  have := Set.ext_iff.mp (@h Unit False ∅ (fun x => x.elim)) (); w41
-- `Set.iInter_inter` idx 2: necessary (empty index, s = empty)
theorem c1_173 : ¬ drop0% Set.iInter_inter 2 := fun h => by
  have := Set.ext_iff.mp (@h Unit False ∅ (fun x => x.elim)) (); w41
-- `Set.insert_iUnion` idx 2: necessary (empty index)
theorem c1_174 : ¬ drop0% Set.insert_iUnion 2 := fun h => by
  have := Set.ext_iff.mp (@h Unit False () (fun x => x.elim)) (); w41
-- `Set.sdiff_iUnion` idx 2: necessary (empty index, s = empty)
theorem c1_175 : ¬ drop0% Set.sdiff_iUnion 2 := fun h => by
  have := Set.ext_iff.mp (@h Unit False ∅ (fun x => x.elim)) (); w41
-- `Set.diff_iUnion` idx 2: necessary (empty index, s = empty)
theorem c1_176 : ¬ drop0% Set.diff_iUnion 2 := fun h => by
  have := Set.ext_iff.mp (@h Unit False ∅ (fun x => x.elim)) (); w41
-- `Set.iUnion_symmDiff_subset` idx 3: necessary (empty index, s = univ)
theorem c1_177 : ¬ drop0% Set.iUnion_symmDiff_subset 3 := fun h => by
  have := @h Unit False univ (fun x => x.elim) () (by simp [Set.mem_symmDiff]); w41
-- `Set.symmDiff_iUnion_subset` idx 3: necessary (empty index, s = univ)
theorem c1_178 : ¬ drop0% Set.symmDiff_iUnion_subset 3 := fun h => by
  have := @h Unit False univ (fun x => x.elim) () (by simp [Set.mem_symmDiff]); w41
-- `Set.sUnion_symmDiff_sUnion_subset` idx 3: necessary (S = empty, T = {univ})
theorem c1_179 : ¬ drop0% Set.sUnion_symmDiff_sUnion_subset 3 := fun h => by
  have := @h Unit ∅ {univ} ⟨univ, rfl⟩ () (by simp [Set.mem_symmDiff]); w41
-- `Set.sUnion_symmDiff_sUnion_subset` idx 4: necessary (S = {univ}, T = empty)
theorem c1_180 : ¬ drop0% Set.sUnion_symmDiff_sUnion_subset 4 := fun h => by
  have := @h Unit {univ} ∅ ⟨univ, rfl⟩ () (by simp [Set.mem_symmDiff]); w41
-- `Set.iUnion_inter_of_monotone` idx 3: necessary (iota = Unit + Unit, not directed, s and t on different summands)
theorem c1_181 : ¬ drop0% Set.iUnion_inter_of_monotone 3 := fun h => by
  have := Set.ext_iff.mp (@h U2 Unit _ (Sum.elim (fun _ => univ) (fun _ => ∅)) (Sum.elim (fun _ => ∅) (fun _ => univ))
    (u2_mono _) (u2_mono _)) (); w41
-- `Set.iUnion_inter_of_monotone` idx 6: necessary (iota = Bool, s antitone, t monotone with disjoint supports)
theorem c1_182 : ¬ drop0% Set.iUnion_inter_of_monotone 6 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit _ _ (fun b => if b then ∅ else univ) (fun b => if b then univ else ∅) mB) (); w41
-- `Set.iUnion_inter_of_monotone` idx 7: necessary (iota = Bool, s monotone, t antitone with disjoint supports)
theorem c1_183 : ¬ drop0% Set.iUnion_inter_of_monotone 7 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit _ _ (fun b => if b then univ else ∅) (fun b => if b then ∅ else univ) mB) (); w41
-- `Set.iUnion_inter_of_antitone` idx 3: necessary (iota = Unit + Unit, not codirected)
theorem c1_184 : ¬ drop0% Set.iUnion_inter_of_antitone 3 := fun h => by
  have := Set.ext_iff.mp (@h U2 Unit _ (Sum.elim (fun _ => univ) (fun _ => ∅)) (Sum.elim (fun _ => ∅) (fun _ => univ))
    (u2_anti _) (u2_anti _)) (); w41
-- `Set.iUnion_inter_of_antitone` idx 6: necessary (iota = Bool, s monotone, t antitone with disjoint supports)
theorem c1_185 : ¬ drop0% Set.iUnion_inter_of_antitone 6 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit _ _ (fun b => if b then univ else ∅) (fun b => if b then ∅ else univ) aB) (); w41
-- `Set.iUnion_inter_of_antitone` idx 7: necessary (iota = Bool, s antitone, t monotone with disjoint supports)
theorem c1_186 : ¬ drop0% Set.iUnion_inter_of_antitone 7 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit _ _ (fun b => if b then ∅ else univ) (fun b => if b then univ else ∅) aB) (); w41
-- `Set.iInter_union_of_monotone` idx 3: necessary (iota = Unit + Unit, not codirected)
theorem c1_187 : ¬ drop0% Set.iInter_union_of_monotone 3 := fun h => by
  have := Set.ext_iff.mp (@h U2 Unit _ (Sum.elim (fun _ => univ) (fun _ => ∅)) (Sum.elim (fun _ => ∅) (fun _ => univ))
    (u2_mono _) (u2_mono _)) (); w41
-- `Set.iInter_union_of_monotone` idx 6: necessary (iota = Bool, s antitone, t monotone, complementary)
theorem c1_188 : ¬ drop0% Set.iInter_union_of_monotone 6 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit _ _ (fun b => if b then ∅ else univ) (fun b => if b then univ else ∅) mB) (); w41
-- `Set.iInter_union_of_monotone` idx 7: necessary (iota = Bool, s monotone, t antitone, complementary)
theorem c1_189 : ¬ drop0% Set.iInter_union_of_monotone 7 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit _ _ (fun b => if b then univ else ∅) (fun b => if b then ∅ else univ) mB) (); w41
-- `Set.iInter_union_of_antitone` idx 3: necessary (iota = Unit + Unit, not directed)
theorem c1_190 : ¬ drop0% Set.iInter_union_of_antitone 3 := fun h => by
  have := Set.ext_iff.mp (@h U2 Unit _ (Sum.elim (fun _ => univ) (fun _ => ∅)) (Sum.elim (fun _ => ∅) (fun _ => univ))
    (u2_anti _) (u2_anti _)) (); w41
-- `Set.iInter_union_of_antitone` idx 6: necessary (iota = Bool, s monotone, t antitone, complementary)
theorem c1_191 : ¬ drop0% Set.iInter_union_of_antitone 6 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit _ _ (fun b => if b then univ else ∅) (fun b => if b then ∅ else univ) aB) (); w41
-- `Set.iInter_union_of_antitone` idx 7: necessary (iota = Bool, s antitone, t monotone, complementary)
theorem c1_192 : ¬ drop0% Set.iInter_union_of_antitone 7 := fun h => by
  have := Set.ext_iff.mp (@h Bool Unit _ _ (fun b => if b then ∅ else univ) (fun b => if b then univ else ∅) aB) (); w41
