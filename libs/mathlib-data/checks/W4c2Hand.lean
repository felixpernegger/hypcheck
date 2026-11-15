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

namespace W4c2

/-- ℤ with a linear order transported from ℕ along `Equiv.intEquivNat`: a well-order, not compatible with addition -/
def EZ := ℤ
instance : AddCancelCommMonoid EZ := inferInstanceAs (AddCancelCommMonoid ℤ)
instance : LinearOrder EZ := LinearOrder.lift' (fun x : EZ => Equiv.intEquivNat (x : ℤ)) Equiv.intEquivNat.injective
instance : WellFoundedLT EZ := InvImage.wf (fun x : EZ => Equiv.intEquivNat (x : ℤ)) wellFounded_lt
theorem ez_wf : (Set.univ : Set EZ).IsWF := Set.isWF_univ_iff.2 inferInstance
theorem ez_pwo : (Set.univ : Set EZ).IsPWO := ez_wf.isPWO
theorem ez_inf : (Set.antidiagonal (Set.univ : Set EZ) Set.univ (0 : ℤ)).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (((n : ℤ) : EZ), ((-(n : ℤ) : ℤ) : EZ)))
    (fun a b h => by have := congrArg (fun p : EZ × EZ => (p.1 : ℤ)) h; exact Nat.cast_injective (R := ℤ) this)
    (fun n => ⟨trivial, trivial, show (n : ℤ) + -(n : ℤ) = 0 by omega⟩)

/-- multiplicative copy -/
def MEZ := ℤ
instance : CancelCommMonoid MEZ := inferInstanceAs (CancelCommMonoid (Multiplicative ℤ))
instance : LinearOrder MEZ := LinearOrder.lift' (fun x : MEZ => Equiv.intEquivNat (x : ℤ)) Equiv.intEquivNat.injective
instance : WellFoundedLT MEZ := InvImage.wf (fun x : MEZ => Equiv.intEquivNat (x : ℤ)) wellFounded_lt
theorem mez_wf : (Set.univ : Set MEZ).IsWF := Set.isWF_univ_iff.2 inferInstance
theorem mez_pwo : (Set.univ : Set MEZ).IsPWO := mez_wf.isPWO
theorem mez_inf : (Set.mulAntidiagonal (Set.univ : Set MEZ) Set.univ ((0 : ℤ) : MEZ)).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (((n : ℤ) : MEZ), ((-(n : ℤ) : ℤ) : MEZ)))
    (fun a b h => by have := congrArg (fun p : MEZ × MEZ => (p.1 : ℤ)) h; exact Nat.cast_injective (R := ℤ) this)
    (fun n => ⟨trivial, trivial, show (n : ℤ) + -(n : ℤ) = 0 by omega⟩)

/-- ℕ under multiplication: antidiagonal of 0 is infinite -/
theorem nat_inf : (Set.mulAntidiagonal (Set.univ : Set ℕ) Set.univ 0).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (0, n))
    (fun a b h => by simpa using h) (fun n => ⟨trivial, trivial, zero_mul n⟩)
theorem enat_inf : (Set.antidiagonal (Set.univ : Set ℕ∞) Set.univ ⊤).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((⊤ : ℕ∞), (n : ℕ∞)))
    (fun a b h => by simpa using h) (fun n => ⟨trivial, trivial, top_add _⟩)

/-- the naturals inside ℤ are PWO; with s = univ the antidiagonal of 0 is infinite -/
theorem natZ_pwo : (Set.range (Nat.cast : ℕ → ℤ)).IsPWO := by
  rw [← Set.image_univ]; exact (Set.isPWO_of_wellQuasiOrderedLE _).image_of_monotone Nat.mono_cast
theorem z_inf1 : (Set.antidiagonal (Set.univ : Set ℤ) (Set.range (Nat.cast : ℕ → ℤ)) 0).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (-(n : ℤ), (n : ℤ)))
    (fun a b h => by simpa using h) (fun n => ⟨trivial, ⟨n, rfl⟩, by simp⟩)
theorem z_inf2 : (Set.antidiagonal (Set.range (Nat.cast : ℕ → ℤ)) (Set.univ : Set ℤ) 0).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : ℤ), -(n : ℤ)))
    (fun a b h => by simpa using h) (fun n => ⟨⟨n, rfl⟩, trivial, by simp⟩)
abbrev MZ := Multiplicative ℤ
def nz (n : ℕ) : MZ := Multiplicative.ofAdd (n : ℤ)
theorem natMZ_pwo : (Set.range nz).IsPWO := by
  rw [← Set.image_univ]; exact (Set.isPWO_of_wellQuasiOrderedLE _).image_of_monotone
    (fun a b h => by simp only [nz, Multiplicative.ofAdd_le]; exact_mod_cast h)
theorem mz_inf1 : (Set.mulAntidiagonal (Set.univ : Set MZ) (Set.range nz) 1).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (Multiplicative.ofAdd (-(n : ℤ)), nz n))
    (fun a b h => by simpa [nz] using h) (fun n => ⟨trivial, ⟨n, rfl⟩, by simp [nz]⟩)
theorem mz_inf2 : (Set.mulAntidiagonal (Set.range nz) (Set.univ : Set MZ) 1).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (nz n, Multiplicative.ofAdd (-(n : ℤ))))
    (fun a b h => by simpa [nz] using h) (fun n => ⟨⟨n, rfl⟩, trivial, by simp [nz]⟩)

/-- Fin 3 with the order 1 < 0 < 2: a cancellative commutative group with a linear order, addition not monotone -/
def F3 := Fin 3
def rk (x : Fin 3) : ℕ := ![1, 0, 2] x
theorem rk_inj : Function.Injective rk := by decide
instance : AddCommGroup F3 := inferInstanceAs (AddCommGroup (Fin 3))
instance : LinearOrder F3 := LinearOrder.lift' (fun x : F3 => rk (x : Fin 3)) rk_inj
def f3 (x : Fin 3) : F3 := x
def MF3 := Fin 3
instance : CommGroup MF3 := inferInstanceAs (CommGroup (Multiplicative (Fin 3)))
instance : LinearOrder MF3 := LinearOrder.lift' (fun x : MF3 => rk (x : Fin 3)) rk_inj
def mf3 (x : Fin 3) : MF3 := x
def mz (n : ℤ) : MZ := Multiplicative.ofAdd n

/-- n ↦ n and n ↦ -n as maps ℕ → ℤ -/
def pos (n : ℕ) : ℤ := n
def neg (n : ℕ) : ℤ := -(n : ℤ)
theorem pos_mono : MonotoneOn pos Set.univ := fun a _ b _ h => by unfold pos; omega
theorem pos_smono : StrictMonoOn pos Set.univ := fun a _ b _ h => by unfold pos; omega
theorem neg_anti : AntitoneOn neg Set.univ := fun a _ b _ h => by unfold neg; omega
theorem neg_santi : StrictAntiOn neg Set.univ := fun a _ b _ h => by unfold neg; omega
theorem pos_nanti : ¬ AntitoneOn pos Set.univ := fun h => absurd (h (Set.mem_univ 0) (Set.mem_univ 1) (by decide)) (by decide)
theorem pos_nsanti : ¬ StrictAntiOn pos Set.univ := fun h => absurd (h (Set.mem_univ 0) (Set.mem_univ 1) (by decide)) (by decide)
theorem neg_nmono : ¬ MonotoneOn neg Set.univ := fun h => absurd (h (Set.mem_univ 0) (Set.mem_univ 1) (by decide)) (by decide)
theorem neg_nsmono : ¬ StrictMonoOn neg Set.univ := fun h => absurd (h (Set.mem_univ 0) (Set.mem_univ 1) (by decide)) (by decide)
theorem emp_on {β : Type} [Preorder β] (f : ℕ → β) : MonotoneOn f ∅ ∧ AntitoneOn f ∅ ∧ StrictMonoOn f ∅ ∧ StrictAntiOn f ∅ :=
  ⟨fun _ ha => absurd ha (Set.notMem_empty _), fun _ ha => absurd ha (Set.notMem_empty _),
   fun _ ha => absurd ha (Set.notMem_empty _), fun _ ha => absurd ha (Set.notMem_empty _)⟩

/-- Bool maps -/
theorem bnot_inv : Set.RightInvOn not not (Set.univ : Set Bool) := fun x _ => Bool.not_not x
theorem bid_inv : Set.RightInvOn id id (Set.univ : Set Bool) := fun x _ => rfl
theorem bmaps (f : Bool → Bool) : Set.MapsTo f Set.univ Set.univ := fun _ _ => trivial
theorem bnot_nmono : ¬ MonotoneOn not (Set.univ : Set Bool) := fun h => absurd (h (Set.mem_univ false) (Set.mem_univ true) (by decide)) (by decide)
theorem bnot_nsmono : ¬ StrictMonoOn not (Set.univ : Set Bool) := fun h => absurd (h (Set.mem_univ false) (Set.mem_univ true) (by decide)) (by decide)
theorem bid_nanti : ¬ AntitoneOn id (Set.univ : Set Bool) := fun h => absurd (h (Set.mem_univ false) (Set.mem_univ true) (by decide)) (by decide)
theorem bid_nsanti : ¬ StrictAntiOn id (Set.univ : Set Bool) := fun h => absurd (h (Set.mem_univ false) (Set.mem_univ true) (by decide)) (by decide)
theorem bct_nsmono : ¬ StrictMonoOn (fun _ => true) (Set.univ : Set Bool) := fun h => absurd (h (Set.mem_univ false) (Set.mem_univ true) (by decide)) (by decide)
theorem bct_nsanti : ¬ StrictAntiOn (fun _ => true) (Set.univ : Set Bool) := fun h => absurd (h (Set.mem_univ false) (Set.mem_univ true) (by decide)) (by decide)
theorem bid_smono : StrictMonoOn id (Set.univ : Set Bool) := fun a _ b _ => by cases a <;> cases b <;> decide
theorem bnot_santi : StrictAntiOn not (Set.univ : Set Bool) := fun a _ b _ => by cases a <;> cases b <;> decide
theorem bemp_on (f : Bool → Bool) : MonotoneOn f ∅ ∧ AntitoneOn f ∅ ∧ StrictMonoOn f ∅ ∧ StrictAntiOn f ∅ :=
  ⟨fun _ ha => absurd ha (Set.notMem_empty _), fun _ ha => absurd ha (Set.notMem_empty _),
   fun _ ha => absurd ha (Set.notMem_empty _), fun _ ha => absurd ha (Set.notMem_empty _)⟩

/-- set-valued maps on ℕ: `up` monotone (∅ at 0, univ after), `dn` antitone (univ at 0, ∅ after) -/
def up (n : ℕ) : Set ℕ := if n = 0 then ∅ else Set.univ
def dn (n : ℕ) : Set ℕ := if n = 0 then Set.univ else ∅
theorem up_nanti (g : ℕ → Set ℕ) (hg : g 0 = Set.univ ∧ g 1 = Set.univ ∨ g 0 = ∅ ∧ g 1 = ∅) :
    ¬ (up 1 ⊓ g 1 ≤ up 0 ⊓ g 0 ∧ up 1 ⊔ g 1 ≤ up 0 ⊔ g 0) := by
  rcases hg with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [up, h0, h1]
theorem dn_nmono (g : ℕ → Set ℕ) (hg : g 0 = Set.univ ∧ g 1 = Set.univ ∨ g 0 = ∅ ∧ g 1 = ∅) :
    ¬ (dn 0 ⊓ g 0 ≤ dn 1 ⊓ g 1 ∧ dn 0 ⊔ g 0 ≤ dn 1 ⊔ g 1) := by
  rcases hg with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [dn, h0, h1]

/-- relations on ℕ with named instances -/
def le' (x y : ℕ) : Prop := x ≤ y
instance : Std.Refl le' := ⟨fun x => Nat.le_refl x⟩
/-- related iff one of them is 0 (symmetric, not reflexive) -/
def r0 (x y : ℕ) : Prop := x = 0 ∨ y = 0
instance : Std.Symm r0 := ⟨fun x y h => h.symm⟩
/-- related iff equal or one of them is 0 (symmetric, reflexive, not transitive) -/
def rr (x y : ℕ) : Prop := x = 0 ∨ y = 0 ∨ x = y
instance : Std.Symm rr := ⟨fun x y h => by unfold rr at *; omega⟩
instance : Std.Refl rr := ⟨fun x => Or.inr (Or.inr rfl)⟩
def ff (_ _ : ℕ) : Prop := False
instance : Std.Symm ff := ⟨fun _ _ h => h⟩
def eqr (x y : ℕ) : Prop := x = y
instance : Std.Symm eqr := ⟨fun _ _ h => h.symm⟩
instance : Std.Refl eqr := ⟨fun _ => rfl⟩

/-- a set with two distinct elements not related is not pairwise related -/
theorem np {α : Type*} {S : Set α} {r : α → α → Prop} {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y)
    (hr : ¬ r x y) : ¬ S.Pairwise r := fun h => hr (h hx hy hne)
theorem m0 : (0:ℕ) ∈ ({0, 1} : Set ℕ) := Set.mem_insert _ _
theorem m1 : (1:ℕ) ∈ ({0, 1} : Set ℕ) := Set.mem_insert_of_mem _ rfl
theorem np01 {r : ℕ → ℕ → Prop} (hp : ({0, 1} : Set ℕ).Pairwise r) (hr : ¬ r 0 1) : False := np m0 m1 (by decide) hr hp
theorem np10 {r : ℕ → ℕ → Prop} (hp : ({0, 1} : Set ℕ).Pairwise r) (hr : ¬ r 1 0) : False := np m1 m0 (by decide) hr hp
theorem np12 {r : ℕ → ℕ → Prop} (hp : ({0, 1, 2} : Set ℕ).Pairwise r) (hr : ¬ r 1 2) : False := np (x := 1) (y := 2) (by simp) (by simp) (by decide) hr hp
/-- ∅ at 0, univ elsewhere -/
def fz (n : ℕ) : Set ℕ := if n = 0 then ∅ else Set.univ
theorem uu : ¬ Disjoint (Set.univ : Set ℕ) Set.univ := by simp
theorem npd01 : ¬ ({0, 1} : Set ℕ).PairwiseDisjoint (fun _ => (Set.univ : Set ℕ)) := fun hp => np01 (r := Function.onFun Disjoint _) hp uu
theorem npd12 : ¬ ({0, 1, 2} : Set ℕ).PairwiseDisjoint fz := fun hp => np12 (r := Function.onFun Disjoint fz) hp (by simp [Function.onFun, fz])
theorem pd_emp (s : Set ℕ) : s.PairwiseDisjoint (fun _ => (∅ : Set ℕ)) := fun _ _ _ _ _ => by simp [Function.onFun]
theorem pd_one (i : ℕ) (f : ℕ → Set ℕ) : ({i} : Set ℕ).PairwiseDisjoint f := Set.pairwiseDisjoint_singleton i f
theorem pd_sing : ({0, 1} : Set ℕ).PairwiseDisjoint (fun n => ({n} : Set ℕ)) := fun i _ j _ hij => by
  simpa [Function.onFun] using hij

end W4c2

-- `Set.MulAntidiagonal.finite_of_isPWO` idx 3: necessary (ℕ under multiplication, s = t = univ, a = 0)
theorem c2_ma1 : ¬ drop0% Set.MulAntidiagonal.finite_of_isPWO 3 := fun h =>
  W4c2.nat_inf (h (s := Set.univ) (t := Set.univ) (Set.isPWO_of_wellQuasiOrderedLE _) (Set.isPWO_of_wellQuasiOrderedLE _) 0)
-- `Set.AddAntidiagonal.finite_of_isPWO` idx 3: necessary (ℕ∞, s = t = univ, a = ⊤)
theorem c2_ma2 : ¬ drop0% Set.AddAntidiagonal.finite_of_isPWO 3 := fun h =>
  W4c2.enat_inf (h (s := Set.univ) (t := Set.univ) (Set.isPWO_of_wellQuasiOrderedLE _) (Set.isPWO_of_wellQuasiOrderedLE _) ⊤)
-- `Set.MulAntidiagonal.finite_of_isPWO` idx 4: necessary (ℤ well-ordered along a bijection with ℕ, s = t = univ)
theorem c2_ma3 : ¬ drop0% Set.MulAntidiagonal.finite_of_isPWO 4 := fun h =>
  W4c2.mez_inf (h (α := W4c2.MEZ) (s := Set.univ) (t := Set.univ) W4c2.mez_pwo W4c2.mez_pwo _)
-- `Set.AddAntidiagonal.finite_of_isPWO` idx 4: necessary (ℤ well-ordered along a bijection with ℕ, s = t = univ)
theorem c2_ma4 : ¬ drop0% Set.AddAntidiagonal.finite_of_isPWO 4 := fun h =>
  W4c2.ez_inf (h (α := W4c2.EZ) (s := Set.univ) (t := Set.univ) W4c2.ez_pwo W4c2.ez_pwo _)
-- `Set.MulAntidiagonal.finite_of_isWF` idx 3: necessary (ℤ well-ordered along a bijection with ℕ)
theorem c2_ma5 : ¬ drop0% Set.MulAntidiagonal.finite_of_isWF 3 := fun h =>
  W4c2.mez_inf (h (α := W4c2.MEZ) (s := Set.univ) (t := Set.univ) W4c2.mez_wf W4c2.mez_wf _)
-- `Set.AddAntidiagonal.finite_of_isWF` idx 3: necessary (ℤ well-ordered along a bijection with ℕ)
theorem c2_ma6 : ¬ drop0% Set.AddAntidiagonal.finite_of_isWF 3 := fun h =>
  W4c2.ez_inf (h (α := W4c2.EZ) (s := Set.univ) (t := Set.univ) W4c2.ez_wf W4c2.ez_wf _)
-- `Set.AddAntidiagonal.finite_of_isPWO` idx 7: necessary (ℤ, s = univ, t = ℕ, a = 0)
theorem c2_ma7 : ¬ drop0% Set.AddAntidiagonal.finite_of_isPWO 7 := fun h =>
  W4c2.z_inf1 (h (s := Set.univ) W4c2.natZ_pwo 0)
-- `Set.AddAntidiagonal.finite_of_isPWO` idx 8: necessary (ℤ, s = ℕ, t = univ, a = 0)
theorem c2_ma8 : ¬ drop0% Set.AddAntidiagonal.finite_of_isPWO 8 := fun h =>
  W4c2.z_inf2 (h (t := Set.univ) W4c2.natZ_pwo 0)
-- `Set.MulAntidiagonal.finite_of_isPWO` idx 7: necessary (Multiplicative ℤ, s = univ, t = ℕ, a = 1)
theorem c2_ma9 : ¬ drop0% Set.MulAntidiagonal.finite_of_isPWO 7 := fun h =>
  W4c2.mz_inf1 (h (s := Set.univ) W4c2.natMZ_pwo 1)
-- `Set.MulAntidiagonal.finite_of_isPWO` idx 8: necessary (Multiplicative ℤ, s = ℕ, t = univ, a = 1)
theorem c2_ma10 : ¬ drop0% Set.MulAntidiagonal.finite_of_isPWO 8 := fun h =>
  W4c2.mz_inf2 (h (t := Set.univ) W4c2.natMZ_pwo 1)
-- `Set.AddAntidiagonal.finite_of_isWF` idx 6: necessary (ℤ, s = univ, t = ℕ, a = 0)
theorem c2_ma11 : ¬ drop0% Set.AddAntidiagonal.finite_of_isWF 6 := fun h =>
  W4c2.z_inf1 (h (s := Set.univ) W4c2.natZ_pwo.isWF 0)
-- `Set.AddAntidiagonal.finite_of_isWF` idx 7: necessary (ℤ, s = ℕ, t = univ, a = 0)
theorem c2_ma12 : ¬ drop0% Set.AddAntidiagonal.finite_of_isWF 7 := fun h =>
  W4c2.z_inf2 (h (t := Set.univ) W4c2.natZ_pwo.isWF 0)
-- `Set.MulAntidiagonal.finite_of_isWF` idx 6: necessary (Multiplicative ℤ, s = univ, t = ℕ, a = 1)
theorem c2_ma13 : ¬ drop0% Set.MulAntidiagonal.finite_of_isWF 6 := fun h =>
  W4c2.mz_inf1 (h (s := Set.univ) W4c2.natMZ_pwo.isWF 1)
-- `Set.MulAntidiagonal.finite_of_isWF` idx 7: necessary (Multiplicative ℤ, s = ℕ, t = univ, a = 1)
theorem c2_ma14 : ¬ drop0% Set.MulAntidiagonal.finite_of_isWF 7 := fun h =>
  W4c2.mz_inf2 (h (t := Set.univ) W4c2.natMZ_pwo.isWF 1)
-- `Set.MulAntidiagonal.fst_eq_fst_iff_snd_eq_snd` idx 2: necessary (ℕ under multiplication, x = (0,1), y = (0,2), a = 0)
theorem c2_mb1 : ¬ drop0% Set.MulAntidiagonal.fst_eq_fst_iff_snd_eq_snd 2 := fun h => by
  have := (h (s := Set.univ) (t := Set.univ) (a := 0) (x := ⟨((0 : ℕ), 1), trivial, trivial, rfl⟩)
    (y := ⟨((0 : ℕ), 2), trivial, trivial, rfl⟩)).1 rfl
  exact absurd this (by simp)
-- `Set.AddAntidiagonal.fst_eq_fst_iff_snd_eq_snd` idx 2: necessary (ℕ∞, x = (⊤,0), y = (⊤,1), a = ⊤)
theorem c2_mb2 : ¬ drop0% Set.AddAntidiagonal.fst_eq_fst_iff_snd_eq_snd 2 := fun h => by
  have := (h (s := Set.univ) (t := Set.univ) (a := ⊤) (x := ⟨((⊤ : ℕ∞), 0), trivial, trivial, top_add _⟩)
    (y := ⟨((⊤ : ℕ∞), 1), trivial, trivial, top_add _⟩)).1 rfl
  exact absurd this (by simp)
-- `Set.MulAntidiagonal.eq_of_fst_eq_fst` idx 2: necessary (ℕ under multiplication, x = (0,1), y = (0,2), a = 0)
theorem c2_mb3 : ¬ drop0% Set.MulAntidiagonal.eq_of_fst_eq_fst 2 := fun h => by
  have := h (s := Set.univ) (t := Set.univ) (a := 0) (x := ⟨((0 : ℕ), 1), trivial, trivial, rfl⟩)
    (y := ⟨((0 : ℕ), 2), trivial, trivial, rfl⟩) rfl
  exact absurd (congrArg Subtype.val this) (by simp)
-- `Set.AddAntidiagonal.eq_of_fst_eq_fst` idx 2: necessary (ℕ∞, x = (⊤,0), y = (⊤,1), a = ⊤)
theorem c2_mb4 : ¬ drop0% Set.AddAntidiagonal.eq_of_fst_eq_fst 2 := fun h => by
  have := h (s := Set.univ) (t := Set.univ) (a := ⊤) (x := ⟨((⊤ : ℕ∞), 0), trivial, trivial, top_add _⟩)
    (y := ⟨((⊤ : ℕ∞), 1), trivial, trivial, top_add _⟩) rfl
  exact absurd (congrArg Subtype.val this) (by simp)
-- `Set.MulAntidiagonal.eq_of_snd_eq_snd` idx 2: necessary (ℕ under multiplication, x = (1,0), y = (2,0), a = 0)
theorem c2_mb5 : ¬ drop0% Set.MulAntidiagonal.eq_of_snd_eq_snd 2 := fun h => by
  have := h (s := Set.univ) (t := Set.univ) (a := 0) (x := ⟨((1 : ℕ), 0), trivial, trivial, rfl⟩)
    (y := ⟨((2 : ℕ), 0), trivial, trivial, rfl⟩) rfl
  exact absurd (congrArg Subtype.val this) (by simp)
-- `Set.AddAntidiagonal.eq_of_snd_eq_snd` idx 2: necessary (ℕ∞, x = (0,⊤), y = (1,⊤), a = ⊤)
theorem c2_mb6 : ¬ drop0% Set.AddAntidiagonal.eq_of_snd_eq_snd 2 := fun h => by
  have := h (s := Set.univ) (t := Set.univ) (a := ⊤) (x := ⟨((0 : ℕ∞), ⊤), trivial, trivial, add_top _⟩)
    (y := ⟨((1 : ℕ∞), ⊤), trivial, trivial, add_top _⟩) rfl
  exact absurd (congrArg Subtype.val this) (by simp)
-- `Set.AddAntidiagonal.eq_of_fst_eq_fst` idx 8: necessary (ℕ, x = (0,1), y = (1,0), a = 1)
theorem c2_mb7 : ¬ drop0% Set.AddAntidiagonal.eq_of_fst_eq_fst 8 := fun h => by
  have := h (s := Set.univ) (t := Set.univ) (a := 1) (x := ⟨((0 : ℕ), 1), trivial, trivial, rfl⟩)
    (y := ⟨((1 : ℕ), 0), trivial, trivial, rfl⟩)
  exact absurd (congrArg Subtype.val this) (by simp)
-- `Set.AddAntidiagonal.eq_of_snd_eq_snd` idx 8: necessary (ℕ, x = (0,1), y = (1,0), a = 1)
theorem c2_mb8 : ¬ drop0% Set.AddAntidiagonal.eq_of_snd_eq_snd 8 := fun h => by
  have := h (s := Set.univ) (t := Set.univ) (a := 1) (x := ⟨((0 : ℕ), 1), trivial, trivial, rfl⟩)
    (y := ⟨((1 : ℕ), 0), trivial, trivial, rfl⟩)
  exact absurd (congrArg Subtype.val this) (by simp)
-- `Set.MulAntidiagonal.eq_of_fst_eq_fst` idx 8: necessary (Multiplicative ℤ, x = (0,1), y = (1,0) additively, a = 1)
theorem c2_mb9 : ¬ drop0% Set.MulAntidiagonal.eq_of_fst_eq_fst 8 := fun h => by
  have := h (s := Set.univ) (t := Set.univ) (a := W4c2.mz 1) (x := ⟨(W4c2.mz 0, W4c2.mz 1), trivial, trivial, rfl⟩)
    (y := ⟨(W4c2.mz 1, W4c2.mz 0), trivial, trivial, rfl⟩)
  exact absurd (congrArg Subtype.val this) (by simp [W4c2.mz])
-- `Set.MulAntidiagonal.eq_of_snd_eq_snd` idx 8: necessary (Multiplicative ℤ, x = (0,1), y = (1,0) additively, a = 1)
theorem c2_mb10 : ¬ drop0% Set.MulAntidiagonal.eq_of_snd_eq_snd 8 := fun h => by
  have := h (s := Set.univ) (t := Set.univ) (a := W4c2.mz 1) (x := ⟨(W4c2.mz 0, W4c2.mz 1), trivial, trivial, rfl⟩)
    (y := ⟨(W4c2.mz 1, W4c2.mz 0), trivial, trivial, rfl⟩)
  exact absurd (congrArg Subtype.val this) (by simp [W4c2.mz])
-- `Set.MulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd` idx 3: necessary (ℕ under multiplication, x = (0,1), y = (0,2), a = 0)
theorem c2_mb11 : ¬ drop0% Set.MulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd 3 := fun h => by
  have := h Set.univ Set.univ 0 (x := ⟨((0 : ℕ), 1), trivial, trivial, rfl⟩)
    (y := ⟨((0 : ℕ), 2), trivial, trivial, rfl⟩) (by decide) (by decide)
  exact absurd (congrArg Subtype.val this) (by simp)
-- `Set.AddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd` idx 3: necessary (ℕ∞, x = (⊤,0), y = (⊤,1), a = ⊤)
theorem c2_mb12 : ¬ drop0% Set.AddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd 3 := fun h => by
  have := h Set.univ Set.univ ⊤ (x := ⟨((⊤ : ℕ∞), 0), trivial, trivial, top_add _⟩)
    (y := ⟨((⊤ : ℕ∞), 1), trivial, trivial, top_add _⟩) le_rfl zero_le_one
  exact absurd (congrArg Subtype.val this) (by simp)
-- `Set.AddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd` idx 4: necessary (Fin 3 ordered 1 < 0 < 2, x = (1,1), y = (0,2), a = 2)
theorem c2_mb13 : ¬ drop0% Set.AddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd 4 := fun h => by
  have := h (α := W4c2.F3) Set.univ Set.univ (W4c2.f3 2) (x := ⟨(W4c2.f3 1, W4c2.f3 1), trivial, trivial, by decide⟩)
    (y := ⟨(W4c2.f3 0, W4c2.f3 2), trivial, trivial, by decide⟩) (by decide) (by decide)
  exact absurd (congrArg Subtype.val this) (by decide)
-- `Set.MulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd` idx 4: necessary (multiplicative Fin 3 ordered 1 < 0 < 2, x = (1,1), y = (0,2), a = 2)
theorem c2_mb14 : ¬ drop0% Set.MulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd 4 := fun h => by
  have := h (α := W4c2.MF3) Set.univ Set.univ (W4c2.mf3 2) (x := ⟨(W4c2.mf3 1, W4c2.mf3 1), trivial, trivial, by decide⟩)
    (y := ⟨(W4c2.mf3 0, W4c2.mf3 2), trivial, trivial, by decide⟩) (by decide) (by decide)
  exact absurd (congrArg Subtype.val this) (by decide)
-- `Set.AddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd` idx 10: necessary (ℕ, x = (1,0), y = (0,1), a = 1)
theorem c2_mb15 : ¬ drop0% Set.AddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd 10 := fun h => by
  have := h Set.univ Set.univ 1 (x := ⟨((1 : ℕ), 0), trivial, trivial, rfl⟩)
    (y := ⟨((0 : ℕ), 1), trivial, trivial, rfl⟩) (by decide)
  exact absurd (congrArg Subtype.val this) (by simp)
-- `Set.AddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd` idx 11: necessary (ℕ, x = (0,1), y = (1,0), a = 1)
theorem c2_mb16 : ¬ drop0% Set.AddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd 11 := fun h => by
  have := h Set.univ Set.univ 1 (x := ⟨((0 : ℕ), 1), trivial, trivial, rfl⟩)
    (y := ⟨((1 : ℕ), 0), trivial, trivial, rfl⟩) (by decide)
  exact absurd (congrArg Subtype.val this) (by simp)
-- `Set.MulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd` idx 10: necessary (Multiplicative ℤ, x = (1,0), y = (0,1) additively)
theorem c2_mb17 : ¬ drop0% Set.MulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd 10 := fun h => by
  have := h Set.univ Set.univ (W4c2.mz 1) (x := ⟨(W4c2.mz 1, W4c2.mz 0), trivial, trivial, rfl⟩)
    (y := ⟨(W4c2.mz 0, W4c2.mz 1), trivial, trivial, rfl⟩) (by decide)
  exact absurd (congrArg Subtype.val this) (by simp [W4c2.mz])
-- `Set.MulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd` idx 11: necessary (Multiplicative ℤ, x = (0,1), y = (1,0) additively)
theorem c2_mb18 : ¬ drop0% Set.MulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd 11 := fun h => by
  have := h Set.univ Set.univ (W4c2.mz 1) (x := ⟨(W4c2.mz 0, W4c2.mz 1), trivial, trivial, rfl⟩)
    (y := ⟨(W4c2.mz 1, W4c2.mz 0), trivial, trivial, rfl⟩) (by decide)
  exact absurd (congrArg Subtype.val this) (by simp [W4c2.mz])
-- `MonotoneOn.congr` idx 7: necessary (f₁ = f₂ = neg : ℕ → ℤ on univ)
theorem c2_mo1 : ¬ drop0% MonotoneOn.congr 7 := fun h => W4c2.neg_nmono (h (s := Set.univ) (f₁ := W4c2.neg) (f₂ := W4c2.neg) (fun _ _ => rfl))
-- `MonotoneOn.congr` idx 8: necessary (f₁ = pos, f₂ = neg : ℕ → ℤ on univ)
theorem c2_mo2 : ¬ drop0% MonotoneOn.congr 8 := fun h => W4c2.neg_nmono (h (s := Set.univ) (f₁ := W4c2.pos) (f₂ := W4c2.neg) W4c2.pos_mono)
-- `Set.EqOn.congr_monotoneOn` idx 7: necessary (f₁ = pos, f₂ = neg : ℕ → ℤ on univ)
theorem c2_mo3 : ¬ drop0% Set.EqOn.congr_monotoneOn 7 := fun h => W4c2.neg_nmono ((h (s := Set.univ) (f₁ := W4c2.pos) (f₂ := W4c2.neg)).1 W4c2.pos_mono)
-- `MonotoneOn.mono` idx 7: necessary (s = s₂ = univ, f = neg : ℕ → ℤ)
theorem c2_mo4 : ¬ drop0% MonotoneOn.mono 7 := fun h => W4c2.neg_nmono (h (s := Set.univ) (s₂ := Set.univ) (f := W4c2.neg) subset_rfl)
-- `MonotoneOn.mono` idx 8: necessary (s = ∅, s₂ = univ, f = neg : ℕ → ℤ)
theorem c2_mo5 : ¬ drop0% MonotoneOn.mono 8 := fun h => W4c2.neg_nmono (h (s := ∅) (s₂ := Set.univ) (f := W4c2.neg) (W4c2.emp_on _).1)
-- `AntitoneOn.congr` idx 7: necessary (f₁ = f₂ = pos : ℕ → ℤ on univ)
theorem c2_mo6 : ¬ drop0% AntitoneOn.congr 7 := fun h => W4c2.pos_nanti (h (s := Set.univ) (f₁ := W4c2.pos) (f₂ := W4c2.pos) (fun _ _ => rfl))
-- `AntitoneOn.congr` idx 8: necessary (f₁ = neg, f₂ = pos : ℕ → ℤ on univ)
theorem c2_mo7 : ¬ drop0% AntitoneOn.congr 8 := fun h => W4c2.pos_nanti (h (s := Set.univ) (f₁ := W4c2.neg) (f₂ := W4c2.pos) W4c2.neg_anti)
-- `Set.EqOn.congr_antitoneOn` idx 7: necessary (f₁ = neg, f₂ = pos : ℕ → ℤ on univ)
theorem c2_mo8 : ¬ drop0% Set.EqOn.congr_antitoneOn 7 := fun h => W4c2.pos_nanti ((h (s := Set.univ) (f₁ := W4c2.neg) (f₂ := W4c2.pos)).1 W4c2.neg_anti)
-- `AntitoneOn.mono` idx 7: necessary (s = s₂ = univ, f = pos : ℕ → ℤ)
theorem c2_mo9 : ¬ drop0% AntitoneOn.mono 7 := fun h => W4c2.pos_nanti (h (s := Set.univ) (s₂ := Set.univ) (f := W4c2.pos) subset_rfl)
-- `AntitoneOn.mono` idx 8: necessary (s = ∅, s₂ = univ, f = pos : ℕ → ℤ)
theorem c2_mo10 : ¬ drop0% AntitoneOn.mono 8 := fun h => W4c2.pos_nanti (h (s := ∅) (s₂ := Set.univ) (f := W4c2.pos) (W4c2.emp_on _).2.1)
-- `StrictMonoOn.congr` idx 7: necessary (f₁ = f₂ = neg : ℕ → ℤ on univ)
theorem c2_mo11 : ¬ drop0% StrictMonoOn.congr 7 := fun h => W4c2.neg_nsmono (h (s := Set.univ) (f₁ := W4c2.neg) (f₂ := W4c2.neg) (fun _ _ => rfl))
-- `StrictMonoOn.congr` idx 8: necessary (f₁ = pos, f₂ = neg : ℕ → ℤ on univ)
theorem c2_mo12 : ¬ drop0% StrictMonoOn.congr 8 := fun h => W4c2.neg_nsmono (h (s := Set.univ) (f₁ := W4c2.pos) (f₂ := W4c2.neg) W4c2.pos_smono)
-- `Set.EqOn.congr_strictMonoOn` idx 7: necessary (f₁ = pos, f₂ = neg : ℕ → ℤ on univ)
theorem c2_mo13 : ¬ drop0% Set.EqOn.congr_strictMonoOn 7 := fun h => W4c2.neg_nsmono ((h (s := Set.univ) (f₁ := W4c2.pos) (f₂ := W4c2.neg)).1 W4c2.pos_smono)
-- `StrictMonoOn.mono` idx 7: necessary (s = s₂ = univ, f = neg : ℕ → ℤ)
theorem c2_mo14 : ¬ drop0% StrictMonoOn.mono 7 := fun h => W4c2.neg_nsmono (h (s := Set.univ) (s₂ := Set.univ) (f := W4c2.neg) subset_rfl)
-- `StrictMonoOn.mono` idx 8: necessary (s = ∅, s₂ = univ, f = neg : ℕ → ℤ)
theorem c2_mo15 : ¬ drop0% StrictMonoOn.mono 8 := fun h => W4c2.neg_nsmono (h (s := ∅) (s₂ := Set.univ) (f := W4c2.neg) (W4c2.emp_on _).2.2.1)
-- `StrictAntiOn.congr` idx 7: necessary (f₁ = f₂ = pos : ℕ → ℤ on univ)
theorem c2_mo16 : ¬ drop0% StrictAntiOn.congr 7 := fun h => W4c2.pos_nsanti (h (s := Set.univ) (f₁ := W4c2.pos) (f₂ := W4c2.pos) (fun _ _ => rfl))
-- `StrictAntiOn.congr` idx 8: necessary (f₁ = neg, f₂ = pos : ℕ → ℤ on univ)
theorem c2_mo17 : ¬ drop0% StrictAntiOn.congr 8 := fun h => W4c2.pos_nsanti (h (s := Set.univ) (f₁ := W4c2.neg) (f₂ := W4c2.pos) W4c2.neg_santi)
-- `Set.EqOn.congr_strictAntiOn` idx 7: necessary (f₁ = neg, f₂ = pos : ℕ → ℤ on univ)
theorem c2_mo18 : ¬ drop0% Set.EqOn.congr_strictAntiOn 7 := fun h => W4c2.pos_nsanti ((h (s := Set.univ) (f₁ := W4c2.neg) (f₂ := W4c2.pos)).1 W4c2.neg_santi)
-- `StrictAntiOn.mono` idx 7: necessary (s = s₂ = univ, f = pos : ℕ → ℤ)
theorem c2_mo19 : ¬ drop0% StrictAntiOn.mono 7 := fun h => W4c2.pos_nsanti (h (s := Set.univ) (s₂ := Set.univ) (f := W4c2.pos) subset_rfl)
-- `AntitoneOn.monotone` idx 6: necessary (f = pos : ℕ → ℤ, s = univ, points 0 ≤ 1)
theorem c2_mo20 : ¬ drop0% AntitoneOn.monotone 6 := fun h => by
  have H := h (s := Set.univ) (f := W4c2.pos)
  exact absurd (@H ⟨0, trivial⟩ ⟨1, trivial⟩ (Subtype.mk_le_mk.2 (by decide))) (by decide)
-- `Monotone.codRestrict` idx 5: necessary (f = neg : ℕ → ℤ, s = univ, points 0 ≤ 1)
theorem c2_mo21 : ¬ drop0% Monotone.codRestrict 5 := fun h => by
  have H := h (f := W4c2.neg) (s := Set.univ) (fun _ => trivial)
  exact absurd (@H 0 1 (by decide)) (fun hh => by
    have := Subtype.coe_le_coe.2 hh; change W4c2.neg 0 ≤ W4c2.neg 1 at this; unfold W4c2.neg at this; omega)
-- `strictMonoOn_insert_iff_of_forall_le` idx 7: necessary (f = neg : ℕ → ℤ, s = {1}, a = 0)
theorem c2_mo22 : ¬ drop0% strictMonoOn_insert_iff_of_forall_le 7 := fun h => by
  have H := (h (f := W4c2.neg) (s := {1}) (a := 0)).2 ⟨fun b hb hba => by simp at hb; omega,
    fun x hx y hy hxy => by simp at hx hy; omega⟩
  exact absurd (H (Set.mem_insert 0 _) (Set.mem_insert_of_mem _ rfl) (by decide)) (by decide)
-- `strictMonoOn_insert_iff_of_forall_ge` idx 7: necessary (f = neg : ℕ → ℤ, s = {0}, a = 1)
theorem c2_mo23 : ¬ drop0% strictMonoOn_insert_iff_of_forall_ge 7 := fun h => by
  have H := (h (f := W4c2.neg) (s := {0}) (a := 1)).2 ⟨fun b hb hba => by simp at hb; omega,
    fun x hx y hy hxy => by simp at hx hy; omega⟩
  exact absurd (H (Set.mem_insert_of_mem _ rfl) (Set.mem_insert 1 _) (by decide)) (by decide)
-- `strictAntiOn_insert_iff_of_forall_ge` idx 7: necessary (f = pos : ℕ → ℤ, s = {0}, a = 1)
theorem c2_mo24 : ¬ drop0% strictAntiOn_insert_iff_of_forall_ge 7 := fun h => by
  have H := (h (f := W4c2.pos) (s := {0}) (a := 1)).2 ⟨fun b hb hba => by simp at hb; omega,
    fun x hx y hy hxy => by simp at hx hy; omega⟩
  exact absurd (H (Set.mem_insert_of_mem _ rfl) (Set.mem_insert 1 _) (by decide)) (by decide)
-- `Function.monotoneOn_of_rightInvOn_of_mapsTo` idx 8: necessary (φ = ψ = not on Bool, s = t = univ)
theorem c2_mo25 : ¬ drop0% Function.monotoneOn_of_rightInvOn_of_mapsTo 8 := fun h => W4c2.bnot_nmono (h (φ := not) (ψ := not) (t := Set.univ) (s := Set.univ) W4c2.bnot_inv (W4c2.bmaps _))
-- `Function.monotoneOn_of_rightInvOn_of_mapsTo` idx 9: necessary (φ = (fun _ => false), ψ = not on Bool, s = t = univ)
theorem c2_mo26 : ¬ drop0% Function.monotoneOn_of_rightInvOn_of_mapsTo 9 := fun h => W4c2.bnot_nmono (h (φ := (fun _ => false)) (ψ := not) (t := Set.univ) (s := Set.univ) (fun a _ b _ _ => le_rfl) (W4c2.bmaps _))
-- `Function.monotoneOn_of_rightInvOn_of_mapsTo` idx 10: necessary (φ = ψ = not on Bool, t = ∅, s = univ)
theorem c2_mo27 : ¬ drop0% Function.monotoneOn_of_rightInvOn_of_mapsTo 10 := fun h => W4c2.bnot_nmono (h (φ := not) (ψ := not) (t := ∅) (s := Set.univ) (W4c2.bemp_on _).1 W4c2.bnot_inv)
-- `Function.strictMonoOn_of_rightInvOn_of_mapsTo` idx 8: necessary (φ = ψ = not on Bool, s = t = univ)
theorem c2_mo28 : ¬ drop0% Function.strictMonoOn_of_rightInvOn_of_mapsTo 8 := fun h => W4c2.bnot_nsmono (h (φ := not) (ψ := not) (t := Set.univ) (s := Set.univ) W4c2.bnot_inv (W4c2.bmaps _))
-- `Function.strictMonoOn_of_rightInvOn_of_mapsTo` idx 9: necessary (φ = id, ψ = (fun _ => true) on Bool, s = t = univ)
theorem c2_mo29 : ¬ drop0% Function.strictMonoOn_of_rightInvOn_of_mapsTo 9 := fun h => W4c2.bct_nsmono (h (φ := id) (ψ := (fun _ => true)) (t := Set.univ) (s := Set.univ) W4c2.bid_smono (W4c2.bmaps _))
-- `Function.strictMonoOn_of_rightInvOn_of_mapsTo` idx 10: necessary (φ = ψ = not on Bool, t = ∅, s = univ)
theorem c2_mo30 : ¬ drop0% Function.strictMonoOn_of_rightInvOn_of_mapsTo 10 := fun h => W4c2.bnot_nsmono (h (φ := not) (ψ := not) (t := ∅) (s := Set.univ) (W4c2.bemp_on _).2.2.1 W4c2.bnot_inv)
-- `Function.antitoneOn_of_rightInvOn_of_mapsTo` idx 8: necessary (φ = ψ = id on Bool, s = t = univ)
theorem c2_mo31 : ¬ drop0% Function.antitoneOn_of_rightInvOn_of_mapsTo 8 := fun h => W4c2.bid_nanti (h (φ := id) (ψ := id) (t := Set.univ) (s := Set.univ) W4c2.bid_inv (W4c2.bmaps _))
-- `Function.antitoneOn_of_rightInvOn_of_mapsTo` idx 9: necessary (φ = (fun _ => false), ψ = id on Bool, s = t = univ)
theorem c2_mo32 : ¬ drop0% Function.antitoneOn_of_rightInvOn_of_mapsTo 9 := fun h => W4c2.bid_nanti (h (φ := (fun _ => false)) (ψ := id) (t := Set.univ) (s := Set.univ) (fun a _ b _ _ => le_rfl) (W4c2.bmaps _))
-- `Function.antitoneOn_of_rightInvOn_of_mapsTo` idx 10: necessary (φ = ψ = id on Bool, t = ∅, s = univ)
theorem c2_mo33 : ¬ drop0% Function.antitoneOn_of_rightInvOn_of_mapsTo 10 := fun h => W4c2.bid_nanti (h (φ := id) (ψ := id) (t := ∅) (s := Set.univ) (W4c2.bemp_on _).2.1 W4c2.bid_inv)
-- `Function.strictAntiOn_of_rightInvOn_of_mapsTo` idx 8: necessary (φ = ψ = id on Bool, s = t = univ)
theorem c2_mo34 : ¬ drop0% Function.strictAntiOn_of_rightInvOn_of_mapsTo 8 := fun h => W4c2.bid_nsanti (h (φ := id) (ψ := id) (t := Set.univ) (s := Set.univ) W4c2.bid_inv (W4c2.bmaps _))
-- `Function.strictAntiOn_of_rightInvOn_of_mapsTo` idx 9: necessary (φ = not, ψ = (fun _ => true) on Bool, s = t = univ)
theorem c2_mo35 : ¬ drop0% Function.strictAntiOn_of_rightInvOn_of_mapsTo 9 := fun h => W4c2.bct_nsanti (h (φ := not) (ψ := (fun _ => true)) (t := Set.univ) (s := Set.univ) W4c2.bnot_santi (W4c2.bmaps _))
-- `Function.strictAntiOn_of_rightInvOn_of_mapsTo` idx 10: necessary (φ = ψ = id on Bool, t = ∅, s = univ)
theorem c2_mo36 : ¬ drop0% Function.strictAntiOn_of_rightInvOn_of_mapsTo 10 := fun h => W4c2.bid_nsanti (h (φ := id) (ψ := id) (t := ∅) (s := Set.univ) (W4c2.bemp_on _).2.2.2 W4c2.bid_inv)
-- `Monotone.inter` idx 5: necessary (f = dn, g = const Set.univ on ℕ)
theorem c2_mo37 : ¬ drop0% Monotone.inter 5 := fun h => absurd (h (f := W4c2.dn) (g := fun _ => (Set.univ : Set ℕ)) monotone_const (by decide : (0:ℕ) ≤ 1)) (by simp [W4c2.dn])
-- `Monotone.inter` idx 6: necessary (f = const Set.univ, g = dn on ℕ)
theorem c2_mo38 : ¬ drop0% Monotone.inter 6 := fun h => absurd (h (f := fun _ => (Set.univ : Set ℕ)) (g := W4c2.dn) monotone_const (by decide : (0:ℕ) ≤ 1)) (by simp [W4c2.dn])
-- `MonotoneOn.inter` idx 6: necessary (f = dn, g = const Set.univ on ℕ, s = univ)
theorem c2_mo39 : ¬ drop0% MonotoneOn.inter 6 := fun h => absurd (h (f := W4c2.dn) (g := fun _ => (Set.univ : Set ℕ)) (s := Set.univ) monotoneOn_const (Set.mem_univ 0) (Set.mem_univ 1) (by decide)) (by simp [W4c2.dn])
-- `MonotoneOn.inter` idx 7: necessary (f = const Set.univ, g = dn on ℕ, s = univ)
theorem c2_mo40 : ¬ drop0% MonotoneOn.inter 7 := fun h => absurd (h (f := fun _ => (Set.univ : Set ℕ)) (g := W4c2.dn) (s := Set.univ) monotoneOn_const (Set.mem_univ 0) (Set.mem_univ 1) (by decide)) (by simp [W4c2.dn])
-- `Monotone.union` idx 5: necessary (f = dn, g = const ∅ on ℕ)
theorem c2_mo41 : ¬ drop0% Monotone.union 5 := fun h => absurd (h (f := W4c2.dn) (g := fun _ => (∅ : Set ℕ)) monotone_const (by decide : (0:ℕ) ≤ 1)) (by simp [W4c2.dn])
-- `Monotone.union` idx 6: necessary (f = const ∅, g = dn on ℕ)
theorem c2_mo42 : ¬ drop0% Monotone.union 6 := fun h => absurd (h (f := fun _ => (∅ : Set ℕ)) (g := W4c2.dn) monotone_const (by decide : (0:ℕ) ≤ 1)) (by simp [W4c2.dn])
-- `MonotoneOn.union` idx 6: necessary (f = dn, g = const ∅ on ℕ, s = univ)
theorem c2_mo43 : ¬ drop0% MonotoneOn.union 6 := fun h => absurd (h (f := W4c2.dn) (g := fun _ => (∅ : Set ℕ)) (s := Set.univ) monotoneOn_const (Set.mem_univ 0) (Set.mem_univ 1) (by decide)) (by simp [W4c2.dn])
-- `MonotoneOn.union` idx 7: necessary (f = const ∅, g = dn on ℕ, s = univ)
theorem c2_mo44 : ¬ drop0% MonotoneOn.union 7 := fun h => absurd (h (f := fun _ => (∅ : Set ℕ)) (g := W4c2.dn) (s := Set.univ) monotoneOn_const (Set.mem_univ 0) (Set.mem_univ 1) (by decide)) (by simp [W4c2.dn])
-- `Antitone.inter` idx 5: necessary (f = up, g = const Set.univ on ℕ)
theorem c2_mo45 : ¬ drop0% Antitone.inter 5 := fun h => absurd (h (f := W4c2.up) (g := fun _ => (Set.univ : Set ℕ)) antitone_const (by decide : (0:ℕ) ≤ 1)) (by simp [W4c2.up])
-- `Antitone.inter` idx 6: necessary (f = const Set.univ, g = up on ℕ)
theorem c2_mo46 : ¬ drop0% Antitone.inter 6 := fun h => absurd (h (f := fun _ => (Set.univ : Set ℕ)) (g := W4c2.up) antitone_const (by decide : (0:ℕ) ≤ 1)) (by simp [W4c2.up])
-- `AntitoneOn.inter` idx 6: necessary (f = up, g = const Set.univ on ℕ, s = univ)
theorem c2_mo47 : ¬ drop0% AntitoneOn.inter 6 := fun h => absurd (h (f := W4c2.up) (g := fun _ => (Set.univ : Set ℕ)) (s := Set.univ) antitoneOn_const (Set.mem_univ 0) (Set.mem_univ 1) (by decide)) (by simp [W4c2.up])
-- `AntitoneOn.inter` idx 7: necessary (f = const Set.univ, g = up on ℕ, s = univ)
theorem c2_mo48 : ¬ drop0% AntitoneOn.inter 7 := fun h => absurd (h (f := fun _ => (Set.univ : Set ℕ)) (g := W4c2.up) (s := Set.univ) antitoneOn_const (Set.mem_univ 0) (Set.mem_univ 1) (by decide)) (by simp [W4c2.up])
-- `Antitone.union` idx 5: necessary (f = up, g = const ∅ on ℕ)
theorem c2_mo49 : ¬ drop0% Antitone.union 5 := fun h => absurd (h (f := W4c2.up) (g := fun _ => (∅ : Set ℕ)) antitone_const (by decide : (0:ℕ) ≤ 1)) (by simp [W4c2.up])
-- `Antitone.union` idx 6: necessary (f = const ∅, g = up on ℕ)
theorem c2_mo50 : ¬ drop0% Antitone.union 6 := fun h => absurd (h (f := fun _ => (∅ : Set ℕ)) (g := W4c2.up) antitone_const (by decide : (0:ℕ) ≤ 1)) (by simp [W4c2.up])
-- `AntitoneOn.union` idx 6: necessary (f = up, g = const ∅ on ℕ, s = univ)
theorem c2_mo51 : ¬ drop0% AntitoneOn.union 6 := fun h => absurd (h (f := W4c2.up) (g := fun _ => (∅ : Set ℕ)) (s := Set.univ) antitoneOn_const (Set.mem_univ 0) (Set.mem_univ 1) (by decide)) (by simp [W4c2.up])
-- `AntitoneOn.union` idx 7: necessary (f = const ∅, g = up on ℕ, s = univ)
theorem c2_mo52 : ¬ drop0% AntitoneOn.union 7 := fun h => absurd (h (f := fun _ => (∅ : Set ℕ)) (g := W4c2.up) (s := Set.univ) antitoneOn_const (Set.mem_univ 0) (Set.mem_univ 1) (by decide)) (by simp [W4c2.up])
-- `Set.monotone_ofPred` idx 4: necessary (p a b := a = 0 on ℕ)
theorem c2_mo53 : ¬ drop0% Set.monotone_ofPred 4 := fun h => absurd (h (p := fun (a b : ℕ) => a = 0) (by decide : (0:ℕ) ≤ 1)) (by simp)
-- `Set.monotone_setOf` idx 4: necessary (p a b := a = 0 on ℕ)
theorem c2_mo54 : ¬ drop0% Set.monotone_setOf 4 := fun h => absurd (h (p := fun (a b : ℕ) => a = 0) (by decide : (0:ℕ) ≤ 1)) (by simp)
-- `Set.antitone_ofPred` idx 4: necessary (p a b := a = 1 on ℕ)
theorem c2_mo55 : ¬ drop0% Set.antitone_ofPred 4 := fun h => absurd (h (p := fun (a b : ℕ) => a = 1) (by decide : (0:ℕ) ≤ 1)) (by simp)
-- `Set.antitone_setOf` idx 4: necessary (p a b := a = 1 on ℕ)
theorem c2_mo56 : ¬ drop0% Set.antitone_setOf 4 := fun h => absurd (h (p := fun (a b : ℕ) => a = 1) (by decide : (0:ℕ) ≤ 1)) (by simp)
-- `Monotone.iUnion_nat_add` idx 2: necessary (f = dn (univ at 0, ∅ after), k = 1)
theorem c2_mo57 : ¬ drop0% Monotone.iUnion_nat_add 2 := fun h => by
  have H := h (f := W4c2.dn) 1
  have h0 : (0:ℕ) ∈ ⋃ n, W4c2.dn n := Set.mem_iUnion.2 ⟨0, by simp [W4c2.dn]⟩
  rw [← H] at h0; simp [W4c2.dn] at h0
-- `Antitone.iInter_nat_add` idx 2: necessary (f = up (∅ at 0, univ after), k = 1)
theorem c2_mo58 : ¬ drop0% Antitone.iInter_nat_add 2 := fun h => by
  have H := h (f := W4c2.up) 1
  have h0 : (0:ℕ) ∈ ⋂ n, W4c2.up (n + 1) := Set.mem_iInter.2 fun n => by simp [W4c2.up]
  rw [H] at h0; simp [W4c2.up] at h0
-- `disjoint_memPartition` idx 6: necessary (n = 0, u = univ, v = {0} in ℕ)
theorem c2_mo59 : ¬ drop0% disjoint_memPartition 6 := fun h => by
  have := h (fun _ => (∅ : Set ℕ)) 0 (u := Set.univ) (v := {0}) rfl
    (fun e => by have h1 : (1:ℕ) ∈ ({0} : Set ℕ) := e ▸ Set.mem_univ 1; simp at h1)
  simp at this
-- `disjoint_memPartition` idx 7: necessary (n = 0, u = v = univ in ℕ)
theorem c2_mo60 : ¬ drop0% disjoint_memPartition 7 := fun h => by
  have := h (fun _ => (∅ : Set ℕ)) 0 (u := Set.univ) (v := Set.univ) rfl rfl
  simp at this
-- `memPartitionSet_of_mem` idx 6: necessary (f = const {0}, n = 1, a = 1, s = univ ∩ {0} in ℕ)
theorem c2_mo61 : ¬ drop0% memPartitionSet_of_mem 6 := fun h => by
  have H := h (f := fun _ => ({0} : Set ℕ)) (n := 1) (a := 1) (s := Set.univ ∩ {0}) ⟨Set.univ, rfl, Or.inl rfl⟩
  have h1 := mem_memPartitionSet (fun _ => ({0} : Set ℕ)) 1 1
  rw [H] at h1; simp at h1
-- `Set.Subsingleton.image2` idx 5: necessary (s = univ, t = {0} in ℕ, f a b = a)
theorem c2_mo62 : ¬ drop0% Set.Subsingleton.image2 5 := fun h => absurd (h (s := (Set.univ : Set ℕ)) (t := ({0} : Set ℕ)) Set.subsingleton_singleton (fun a _ => a)
  ⟨0, trivial, 0, rfl, rfl⟩ ⟨1, trivial, 0, rfl, rfl⟩) (by decide)
-- `Set.Subsingleton.image2` idx 6: necessary (s = {0}, t = univ in ℕ, f a b = b)
theorem c2_mo63 : ¬ drop0% Set.Subsingleton.image2 6 := fun h => absurd (h (s := ({0} : Set ℕ)) (t := (Set.univ : Set ℕ)) Set.subsingleton_singleton (fun _ b => b)
  ⟨0, rfl, 0, trivial, rfl⟩ ⟨0, rfl, 1, trivial, rfl⟩) (by decide)
-- `pairwise_on_bool` idx 2: necessary (r = ≤ on ℕ, a = 0, b = 1)
theorem c2_pw1 : ¬ drop0% pairwise_on_bool 2 := fun h => absurd ((h (r := W4c2.le') (a := 0) (b := 1)).2 (by unfold W4c2.le'; omega) (show false ≠ true by decide))
  (by simp [Function.onFun, W4c2.le'])
-- `Std.Symm.pairwise_on` idx 4: necessary (r = ≤ on ℕ, f = id on ℕ)
theorem c2_pw2 : ¬ drop0% Std.Symm.pairwise_on 4 := fun h => absurd ((h (r := W4c2.le') (id : ℕ → ℕ)).2 (fun m n hmn => by unfold W4c2.le'; simp; omega) (show (1:ℕ) ≠ 0 by decide))
  (by simp [Function.onFun, W4c2.le'])
-- `Symmetric.pairwise_on` idx 4: necessary (r = ≤ on ℕ, f = id on ℕ)
theorem c2_pw3 : ¬ drop0% Symmetric.pairwise_on 4 := fun h => absurd ((h (r := W4c2.le') (id : ℕ → ℕ)).2 (fun m n hmn => by unfold W4c2.le'; simp; omega) (show (1:ℕ) ≠ 0 by decide))
  (by simp [Function.onFun, W4c2.le'])
-- `pairwise_disjoint_mono` idx 6: necessary (f = g = const univ : Bool → Set ℕ)
theorem c2_pw4 : ¬ drop0% pairwise_disjoint_mono 6 := fun h => W4c2.uu (h (f := fun _ : Bool => (Set.univ : Set ℕ)) (g := fun _ => Set.univ) le_rfl (show true ≠ false by decide))
-- `pairwise_disjoint_mono` idx 7: necessary (f = const ∅, g = const univ : Bool → Set ℕ)
theorem c2_pw5 : ¬ drop0% pairwise_disjoint_mono 7 := fun h => W4c2.uu (h (f := fun _ : Bool => (∅ : Set ℕ)) (g := fun _ => Set.univ) (fun _ _ _ => by simp [Function.onFun]) (show true ≠ false by decide))
-- `Pairwise.disjoint_extend_bot` idx 7: necessary (e = id on Bool, f = const univ : Bool → Set ℕ)
theorem c2_pw6 : ¬ drop0% Pairwise.disjoint_extend_bot 7 := fun h => W4c2.uu (by
    have := h (e := (id : Bool → Bool)) (f := fun _ => (Set.univ : Set ℕ)) (fun _ _ _ => rfl) (show true ≠ false by decide)
    simpa [Function.onFun, Function.extend_def] using this)
-- `Pairwise.disjoint_extend_bot` idx 8: removable (removable: distinct b₁ ≠ b₂ in the range come from distinct preimages, so hf alone gives disjointness; outside the range the value is ⊥)
theorem c2_pw7 : drop% Pairwise.disjoint_extend_bot 8 := by
  intro α β γ _ _ e f hf b₁ b₂ hne
  show Disjoint (Function.extend e f ⊥ b₁) (Function.extend e f ⊥ b₂)
  classical
  rw [Function.extend_def, Function.extend_def]
  split_ifs with h1 h2 h2
  · exact hf (fun hc => hne (by rw [← Classical.choose_spec h1, ← Classical.choose_spec h2, hc]))
  · exact disjoint_bot_right
  · exact disjoint_bot_left
  · exact disjoint_bot_left
-- `Set.Pairwise.mono` idx 4: necessary (s = ∅, t = {0,1}, r = ⊥ on ℕ)
theorem c2_pw8 : ¬ drop0% Set.Pairwise.mono 4 := fun h => W4c2.np01 (h (r := W4c2.ff) (s := ∅) (t := {0, 1}) (Set.pairwise_empty _)) id
-- `Set.Pairwise.mono` idx 5: necessary (s = t = {0,1}, r = ⊥ on ℕ)
theorem c2_pw9 : ¬ drop0% Set.Pairwise.mono 5 := fun h => W4c2.np01 (h (r := W4c2.ff) (s := {0, 1}) (t := {0, 1}) subset_rfl) id
-- `Set.Pairwise.mono'` idx 4: necessary (r = ⊤, p = ⊥ on ℕ, s = {0,1})
theorem c2_pw10 : ¬ drop0% Set.Pairwise.mono' 4 := fun h => W4c2.np01 (h (r := fun _ _ => True) (p := W4c2.ff) (s := {0, 1}) (fun _ _ _ _ _ => trivial)) id
-- `Set.Pairwise.mono'` idx 5: necessary (r = p = ⊥ on ℕ, s = {0,1})
theorem c2_pw11 : ¬ drop0% Set.Pairwise.mono' 5 := fun h => W4c2.np01 (h (r := W4c2.ff) (p := W4c2.ff) (s := {0, 1}) le_rfl) id
-- `Set.Pairwise.mono''` idx 5: necessary (s = ∅, t = {0,1}, r = p = ⊥)
theorem c2_pw12 : ¬ drop0% Set.Pairwise.mono'' 5 := fun h => W4c2.np01 (h (r := W4c2.ff) (p := W4c2.ff) (s := ∅) (t := {0, 1}) (fun _ _ h => h) (Set.pairwise_empty _)) id
-- `Set.Pairwise.mono''` idx 6: necessary (s = t = {0,1}, r = ⊤, p = ⊥)
theorem c2_pw13 : ¬ drop0% Set.Pairwise.mono'' 6 := fun h => W4c2.np01 (h (r := fun _ _ => True) (p := W4c2.ff) (s := {0, 1}) (t := {0, 1}) subset_rfl (fun _ _ _ _ _ => trivial)) id
-- `Set.Pairwise.mono''` idx 7: necessary (s = t = {0,1}, r = p = ⊥)
theorem c2_pw14 : ¬ drop0% Set.Pairwise.mono'' 7 := fun h => W4c2.np01 (h (r := W4c2.ff) (p := W4c2.ff) (s := {0, 1}) (t := {0, 1}) subset_rfl (fun _ _ h => h)) id
-- `Set.Pairwise.inter_left` idx 3: necessary (s = t = {0,1}, r = ⊥)
theorem c2_pw15 : ¬ drop0% Set.Pairwise.inter_left 3 := fun h => absurd (h (r := W4c2.ff) (s := {0, 1}) {0, 1}) (W4c2.np ⟨W4c2.m0, W4c2.m0⟩ ⟨W4c2.m1, W4c2.m1⟩ (by decide) id)
-- `Set.Pairwise.inter_right` idx 3: necessary (s = t = {0,1}, r = ⊥)
theorem c2_pw16 : ¬ drop0% Set.Pairwise.inter_right 3 := fun h => absurd (h (r := W4c2.ff) (s := {0, 1}) {0, 1}) (W4c2.np ⟨W4c2.m0, W4c2.m0⟩ ⟨W4c2.m1, W4c2.m1⟩ (by decide) id)
-- `Set.Subsingleton.pairwise` idx 2: necessary (s = {0,1}, r = ⊥)
theorem c2_pw17 : ¬ drop0% Set.Subsingleton.pairwise 2 := fun h => W4c2.np01 (h (s := {0, 1}) W4c2.ff) id
-- `Set.Nonempty.pairwise_iff_exists_forall` idx 6: necessary (α = ι = Empty, s = ∅, r = Eq)
theorem c2_pw18 : ¬ drop0% Set.Nonempty.pairwise_iff_exists_forall 6 := fun h => by
  obtain ⟨z, _⟩ := (h (α := Empty) (ι := Empty) (r := Eq) (f := id) (s := ∅)).1 (Set.pairwise_empty _)
  exact z.elim
-- `Set.Nonempty.pairwise_eq_iff_exists_eq` idx 3: necessary (α = ι = Empty, s = ∅)
theorem c2_pw19 : ¬ drop0% Set.Nonempty.pairwise_eq_iff_exists_eq 3 := fun h => by
  obtain ⟨z, _⟩ := (h (α := Empty) (ι := Empty) (f := id) (s := ∅)).1 (Set.pairwise_empty _)
  exact z.elim
-- `Set.pairwise_iff_exists_forall` idx 2: necessary (α = ι = Empty, s = ∅, r = Eq)
theorem c2_pw20 : ¬ drop0% Set.pairwise_iff_exists_forall 2 := fun h => by
  obtain ⟨z, _⟩ := (h (∅ : Set Empty) (id : Empty → Empty) (r := Eq)).1 (Set.pairwise_empty _)
  exact z.elim
-- `Set.pairwise_eq_iff_exists_eq` idx 2: necessary (α = ι = Empty, s = ∅)
theorem c2_pw21 : ¬ drop0% Set.pairwise_eq_iff_exists_eq 2 := fun h => by
  obtain ⟨z, _⟩ := (h (∅ : Set Empty) (id : Empty → Empty)).1 (Set.pairwise_empty _)
  exact z.elim
-- `Set.pairwise_union_of_symm` idx 4: necessary (r = ≤ on ℕ, s = {0}, t = {1})
theorem c2_pw22 : ¬ drop0% Set.pairwise_union_of_symm 4 := fun h => absurd ((h (r := W4c2.le') (s := {0}) (t := {1})).2 ⟨Set.pairwise_singleton _ _, Set.pairwise_singleton _ _, (fun a ha b hb _ => by simp at ha hb; subst ha; subst hb; unfold W4c2.le'; omega)⟩)
  (W4c2.np (x := 1) (y := 0) (by simp) (by simp) (by decide) (by unfold W4c2.le'; omega))
-- `Set.pairwise_union_of_symm_of_refl` idx 4: necessary (r = ≤ on ℕ, s = {0}, t = {1})
theorem c2_pw23 : ¬ drop0% Set.pairwise_union_of_symm_of_refl 4 := fun h => absurd ((h (r := W4c2.le') (s := {0}) (t := {1})).2 ⟨Set.pairwise_singleton _ _, Set.pairwise_singleton _ _, (fun a ha b hb => by simp at ha hb; subst ha; subst hb; unfold W4c2.le'; omega)⟩)
  (W4c2.np (x := 1) (y := 0) (by simp) (by simp) (by decide) (by unfold W4c2.le'; omega))
-- `Set.pairwise_union_of_symmetric` idx 4: necessary (r = ≤ on ℕ, s = {0}, t = {1})
theorem c2_pw24 : ¬ drop0% Set.pairwise_union_of_symmetric 4 := fun h => absurd ((h (r := W4c2.le') (s := {0}) (t := {1})).2 ⟨Set.pairwise_singleton _ _, Set.pairwise_singleton _ _, (fun a ha b hb _ => by simp at ha hb; subst ha; subst hb; unfold W4c2.le'; omega)⟩)
  (W4c2.np (x := 1) (y := 0) (by simp) (by simp) (by decide) (by unfold W4c2.le'; omega))
-- `Set.Pairwise.insert` idx 4: necessary (s = {1,2}, a = 0, r x y := x = 0 ∨ y = 0)
theorem c2_pw25 : ¬ drop0% Set.Pairwise.insert 4 := fun h => W4c2.np12 (h (r := W4c2.r0) (s := {1, 2}) (a := 0) (fun b _ _ => ⟨Or.inl rfl, Or.inr rfl⟩)) (by simp [W4c2.r0])
-- `Set.Pairwise.insert` idx 5: necessary (s = {1}, a = 0, r = ⊥)
theorem c2_pw26 : ¬ drop0% Set.Pairwise.insert 5 := fun h => W4c2.np01 (h (r := W4c2.ff) (s := {1}) (a := 0) (Set.pairwise_singleton _ _)) id
-- `Set.Pairwise.insert_of_notMem` idx 5: necessary (s = {1,2}, a = 0, r x y := x = 0 ∨ y = 0)
theorem c2_pw27 : ¬ drop0% Set.Pairwise.insert_of_notMem 5 := fun h => W4c2.np12 (h (r := W4c2.r0) (s := {1, 2}) (a := 0) (by simp) (fun b _ => ⟨Or.inl rfl, Or.inr rfl⟩)) (by simp [W4c2.r0])
-- `Set.Pairwise.insert_of_notMem` idx 6: necessary (s = {1}, a = 0, r = ⊥)
theorem c2_pw28 : ¬ drop0% Set.Pairwise.insert_of_notMem 6 := fun h => W4c2.np01 (h (r := W4c2.ff) (s := {1}) (a := 0) (by simp) (Set.pairwise_singleton _ _)) id
-- `Set.pairwise_insert_of_symm` idx 4: necessary (r = ≤ on ℕ, s = {1}, a = 0)
theorem c2_pw29 : ¬ drop0% Set.pairwise_insert_of_symm 4 := fun h => W4c2.np10 ((h (r := W4c2.le') (s := {1}) (a := 0)).2 ⟨Set.pairwise_singleton _ _, fun b hb _ => by simp at hb; subst hb; unfold W4c2.le'; omega⟩)
  (by unfold W4c2.le'; omega)
-- `Set.pairwise_insert_of_symm_of_refl` idx 4: necessary (r = ≤ on ℕ, s = {1}, a = 0)
theorem c2_pw30 : ¬ drop0% Set.pairwise_insert_of_symm_of_refl 4 := fun h => W4c2.np10 ((h (r := W4c2.le') (s := {1}) (a := 0)).2 ⟨Set.pairwise_singleton _ _, fun b hb => by simp at hb; subst hb; unfold W4c2.le'; omega⟩)
  (by unfold W4c2.le'; omega)
-- `Set.pairwise_insert_of_symmetric` idx 4: necessary (r = ≤ on ℕ, s = {1}, a = 0)
theorem c2_pw31 : ¬ drop0% Set.pairwise_insert_of_symmetric 4 := fun h => W4c2.np10 ((h (r := W4c2.le') (s := {1}) (a := 0)).2 ⟨Set.pairwise_singleton _ _, fun b hb _ => by simp at hb; subst hb; unfold W4c2.le'; omega⟩)
  (by unfold W4c2.le'; omega)
-- `Set.pairwise_insert_of_symm_of_notMem` idx 4: necessary (r = ≤ on ℕ, s = {1}, a = 0)
theorem c2_pw32 : ¬ drop0% Set.pairwise_insert_of_symm_of_notMem 4 := fun h => W4c2.np10 ((h (r := W4c2.le') (s := {1}) (a := 0) (by simp)).2 ⟨Set.pairwise_singleton _ _, fun b hb => by simp at hb; subst hb; unfold W4c2.le'; omega⟩)
  (by unfold W4c2.le'; omega)
-- `Set.pairwise_insert_of_symmetric_of_notMem` idx 4: necessary (r = ≤ on ℕ, s = {1}, a = 0)
theorem c2_pw33 : ¬ drop0% Set.pairwise_insert_of_symmetric_of_notMem 4 := fun h => W4c2.np10 ((h (r := W4c2.le') (s := {1}) (a := 0) (by simp)).2 ⟨Set.pairwise_singleton _ _, fun b hb => by simp at hb; subst hb; unfold W4c2.le'; omega⟩)
  (by unfold W4c2.le'; omega)
-- `Set.Pairwise.insert_of_symm` idx 4: necessary (r = ≤ on ℕ, s = {1}, a = 0)
theorem c2_pw34 : ¬ drop0% Set.Pairwise.insert_of_symm 4 := fun h => W4c2.np10 (h (r := W4c2.le') (s := {1}) (a := 0) (Set.pairwise_singleton _ _) (fun b hb _ => by simp at hb; subst hb; unfold W4c2.le'; omega))
  (by unfold W4c2.le'; omega)
-- `Set.Pairwise.insert_of_symm` idx 5: necessary (s = {1,2}, a = 0, r x y := x = 0 ∨ y = 0 (symmetric))
theorem c2_pw35 : ¬ drop0% Set.Pairwise.insert_of_symm 5 := fun h => W4c2.np12 (h (r := W4c2.r0) (s := {1, 2}) (a := 0) (fun b _ _ => Or.inl rfl)) (by simp [W4c2.r0])
-- `Set.Pairwise.insert_of_symm` idx 6: necessary (s = {1}, a = 0, r = ⊥ (symmetric))
theorem c2_pw36 : ¬ drop0% Set.Pairwise.insert_of_symm 6 := fun h => W4c2.np01 (h (r := W4c2.ff) (s := {1}) (a := 0) (Set.pairwise_singleton _ _)) id
-- `Set.Pairwise.insert_of_symmetric` idx 4: necessary (r = ≤ on ℕ, s = {1}, a = 0)
theorem c2_pw37 : ¬ drop0% Set.Pairwise.insert_of_symmetric 4 := fun h => W4c2.np10 (h (r := W4c2.le') (s := {1}) (a := 0) (Set.pairwise_singleton _ _) (fun b hb _ => by simp at hb; subst hb; unfold W4c2.le'; omega))
  (by unfold W4c2.le'; omega)
-- `Set.Pairwise.insert_of_symmetric` idx 5: necessary (s = {1,2}, a = 0, r x y := x = 0 ∨ y = 0 (symmetric))
theorem c2_pw38 : ¬ drop0% Set.Pairwise.insert_of_symmetric 5 := fun h => W4c2.np12 (h (r := W4c2.r0) (s := {1, 2}) (a := 0) (fun b _ _ => Or.inl rfl)) (by simp [W4c2.r0])
-- `Set.Pairwise.insert_of_symmetric` idx 6: necessary (s = {1}, a = 0, r = ⊥ (symmetric))
theorem c2_pw39 : ¬ drop0% Set.Pairwise.insert_of_symmetric 6 := fun h => W4c2.np01 (h (r := W4c2.ff) (s := {1}) (a := 0) (Set.pairwise_singleton _ _)) id
-- `Set.Pairwise.insert_of_symm_of_refl` idx 4: necessary (r = ≤ on ℕ (reflexive), s = {1}, a = 0)
theorem c2_pw40 : ¬ drop0% Set.Pairwise.insert_of_symm_of_refl 4 := fun h => W4c2.np10 (h (r := W4c2.le') (s := {1}) (a := 0) (Set.pairwise_singleton _ _) (fun b hb => by simp at hb; subst hb; unfold W4c2.le'; omega))
  (by unfold W4c2.le'; omega)
-- `Set.Pairwise.insert_of_symm_of_refl` idx 5: removable (removable: with symmetry, h gives r a b and r b a for every b ∈ s; reflexivity is never used (same proof as Set.Pairwise.insert_of_symm))
theorem c2_pw41 : drop% Set.Pairwise.insert_of_symm_of_refl 5 := fun hs h => hs.insert_of_symm fun b hb _ => h b hb
-- `Set.Pairwise.insert_of_symm_of_refl` idx 6: necessary (s = {1,2}, a = 0, r x y := x = 0 ∨ y = 0 ∨ x = y (symmetric, reflexive))
theorem c2_pw42 : ¬ drop0% Set.Pairwise.insert_of_symm_of_refl 6 := fun h => W4c2.np12 (h (r := W4c2.rr) (s := {1, 2}) (a := 0) (fun b _ => Or.inl rfl)) (by simp [W4c2.rr])
-- `Set.Pairwise.insert_of_symm_of_refl` idx 7: necessary (s = {1}, a = 0, r = Eq)
theorem c2_pw43 : ¬ drop0% Set.Pairwise.insert_of_symm_of_refl 7 := fun h => W4c2.np01 (h (r := W4c2.eqr) (s := {1}) (a := 0) (Set.pairwise_singleton _ _)) (by simp [W4c2.eqr])
-- `Set.pairwise_pair_of_symm` idx 4: necessary (r = ≤ on ℕ, a = 0, b = 1)
theorem c2_pw44 : ¬ drop0% Set.pairwise_pair_of_symm 4 := fun h => W4c2.np10 ((h (r := W4c2.le') (a := 0) (b := 1)).2 (fun _ => by unfold W4c2.le'; omega)) (by unfold W4c2.le'; omega)
-- `Set.pairwise_pair_of_symmetric` idx 4: necessary (r = ≤ on ℕ, a = 0, b = 1)
theorem c2_pw45 : ¬ drop0% Set.pairwise_pair_of_symmetric 4 := fun h => W4c2.np10 ((h (r := W4c2.le') (a := 0) (b := 1)).2 (fun _ => by unfold W4c2.le'; omega)) (by unfold W4c2.le'; omega)
-- `Set.pairwise_pair_of_symm_of_refl` idx 4: necessary (r = ≤ on ℕ, a = 0, b = 1)
theorem c2_pw46 : ¬ drop0% Set.pairwise_pair_of_symm_of_refl 4 := fun h => W4c2.np10 ((h (r := W4c2.le') (a := 0) (b := 1)).2 (by unfold W4c2.le'; omega)) (by unfold W4c2.le'; omega)
-- `Set.InjOn.pairwise_ne` idx 4: necessary (f = const 0, s = {0,1})
theorem c2_pw47 : ¬ drop0% Set.InjOn.pairwise_ne 4 := fun h => W4c2.np01 (h (f := fun _ : ℕ => (0 : ℕ)) (s := {0, 1})) (by simp)
-- `Set.Pairwise.image` idx 5: necessary (f = id, s = {0,1}, r = ⊥)
theorem c2_pw48 : ¬ drop0% Set.Pairwise.image 5 := fun h => absurd (h (r := W4c2.ff) (f := id) (s := {0, 1})) (W4c2.np ⟨0, W4c2.m0, rfl⟩ ⟨1, W4c2.m1, rfl⟩ (by decide) id)
-- `Set.InjOn.pairwise_image` idx 5: necessary (f = const 0, s = {0,1}, r = ⊥)
theorem c2_pw49 : ¬ drop0% Set.InjOn.pairwise_image 5 := fun h => W4c2.np01 ((h (r := W4c2.ff) (f := fun _ : ℕ => (0 : ℕ)) (s := {0, 1})).1
    (fun x hx y hy hxy => by obtain ⟨_, _, rfl⟩ := hx; obtain ⟨_, _, rfl⟩ := hy; exact absurd rfl hxy)) id
-- `Pairwise.range_pairwise` idx 4: necessary (f = id on ℕ, r = ⊥)
theorem c2_pw50 : ¬ drop0% Pairwise.range_pairwise 4 := fun h => absurd (h (r := W4c2.ff) (f := (id : ℕ → ℕ))) (W4c2.np ⟨0, rfl⟩ ⟨1, rfl⟩ (by decide) id)
-- `Pairwise.set_of_subtype` idx 3: necessary (s = {0,1}, r = ⊥)
theorem c2_pw51 : ¬ drop0% Pairwise.set_of_subtype 3 := fun h => W4c2.np01 (h {0, 1} W4c2.ff) id
-- `Set.Pairwise.subtype` idx 3: necessary (s = {0,1}, r = ⊥)
theorem c2_pw52 : ¬ drop0% Set.Pairwise.subtype 3 := fun h => h ({0, 1} : Set ℕ) W4c2.ff (show (⟨0, W4c2.m0⟩ : ({0, 1} : Set ℕ)) ≠ ⟨1, W4c2.m1⟩ by simp)
-- `Set.PairwiseDisjoint.disjoint_of_ne` idx 6: necessary (s = univ, f = const univ, i = 0, j = 1)
theorem c2_pw53 : ¬ drop0% Set.PairwiseDisjoint.disjoint_of_ne 6 := fun h => W4c2.uu (h (s := (Set.univ : Set ℕ)) (f := (fun _ => (Set.univ : Set ℕ))) (i := 0) (j := 1) trivial trivial (by decide))
-- `Set.PairwiseDisjoint.disjoint_of_ne` idx 9: necessary (s = {1}, f = const univ, i = 0, j = 1)
theorem c2_pw54 : ¬ drop0% Set.PairwiseDisjoint.disjoint_of_ne 9 := fun h => W4c2.uu (h (s := {1}) (f := (fun _ => (Set.univ : Set ℕ))) (W4c2.pd_one _ _) (i := 0) (j := 1) rfl (by decide))
-- `Set.PairwiseDisjoint.disjoint_of_ne` idx 10: necessary (s = {0}, f = const univ, i = 0, j = 1)
theorem c2_pw55 : ¬ drop0% Set.PairwiseDisjoint.disjoint_of_ne 10 := fun h => W4c2.uu (h (s := {0}) (f := (fun _ => (Set.univ : Set ℕ))) (W4c2.pd_one _ _) (i := 0) (j := 1) rfl (by decide))
-- `Set.PairwiseDisjoint.subset` idx 7: necessary (s = t = {0,1}, f = const univ)
theorem c2_pw56 : ¬ drop0% Set.PairwiseDisjoint.subset 7 := fun h => W4c2.npd01 (h (s := {0, 1}) (t := {0, 1}) (f := (fun _ => (Set.univ : Set ℕ))) subset_rfl)
-- `Set.PairwiseDisjoint.subset` idx 8: necessary (t = ∅, s = {0,1}, f = const univ)
theorem c2_pw57 : ¬ drop0% Set.PairwiseDisjoint.subset 8 := fun h => W4c2.npd01 (h (s := {0, 1}) (t := ∅) (f := (fun _ => (Set.univ : Set ℕ))) (Set.pairwise_empty _))
-- `Set.PairwiseDisjoint.mono_on` idx 7: necessary (f = g = const univ, s = {0,1})
theorem c2_pw58 : ¬ drop0% Set.PairwiseDisjoint.mono_on 7 := fun h => W4c2.npd01 (h (s := {0, 1}) (f := (fun _ => (Set.univ : Set ℕ))) (g := (fun _ => (Set.univ : Set ℕ))) (fun _ _ => le_rfl))
-- `Set.PairwiseDisjoint.mono_on` idx 8: necessary (f = const ∅, g = const univ, s = {0,1})
theorem c2_pw59 : ¬ drop0% Set.PairwiseDisjoint.mono_on 8 := fun h => W4c2.npd01 (h (s := {0, 1}) (f := (fun _ => (∅ : Set ℕ))) (g := (fun _ => (Set.univ : Set ℕ))) (W4c2.pd_emp _))
-- `Set.PairwiseDisjoint.mono` idx 7: necessary (f = g = const univ, s = {0,1})
theorem c2_pw60 : ¬ drop0% Set.PairwiseDisjoint.mono 7 := fun h => W4c2.npd01 (h (s := {0, 1}) (f := (fun _ => (Set.univ : Set ℕ))) (g := (fun _ => (Set.univ : Set ℕ))) le_rfl)
-- `Set.PairwiseDisjoint.mono` idx 8: necessary (f = const ∅, g = const univ, s = {0,1})
theorem c2_pw61 : ¬ drop0% Set.PairwiseDisjoint.mono 8 := fun h => W4c2.npd01 (h (s := {0, 1}) (f := (fun _ => (∅ : Set ℕ))) (g := (fun _ => (Set.univ : Set ℕ))) (W4c2.pd_emp _))
-- `Set.PairwiseDisjoint.insert` idx 6: necessary (s = {1,2}, i = 0, f = ∅ at 0, univ elsewhere)
theorem c2_pw62 : ¬ drop0% Set.PairwiseDisjoint.insert 6 := fun h => W4c2.npd12 (h (s := {1, 2}) (f := W4c2.fz) (i := 0) (fun j _ _ => by simp [W4c2.fz]))
-- `Set.PairwiseDisjoint.insert` idx 8: necessary (s = {1}, i = 0, f = const univ)
theorem c2_pw63 : ¬ drop0% Set.PairwiseDisjoint.insert 8 := fun h => W4c2.npd01 (h (s := {1}) (f := (fun _ => (Set.univ : Set ℕ))) (W4c2.pd_one _ _) (i := 0))
-- `Set.PairwiseDisjoint.insert_of_notMem` idx 6: necessary (s = {1,2}, i = 0, f = ∅ at 0, univ elsewhere)
theorem c2_pw64 : ¬ drop0% Set.PairwiseDisjoint.insert_of_notMem 6 := fun h => W4c2.npd12 (h (s := {1, 2}) (f := W4c2.fz) (i := 0) (by simp) (fun j _ => by simp [W4c2.fz]))
-- `Set.PairwiseDisjoint.insert_of_notMem` idx 9: necessary (s = {1}, i = 0, f = const univ)
theorem c2_pw65 : ¬ drop0% Set.PairwiseDisjoint.insert_of_notMem 9 := fun h => W4c2.npd01 (h (s := {1}) (f := (fun _ => (Set.univ : Set ℕ))) (W4c2.pd_one _ _) (i := 0) (by simp))
-- `Set.InjOn.pairwiseDisjoint_image` idx 8: necessary (g = const 0, s = {0,1}, f = const univ)
theorem c2_pw66 : ¬ drop0% Set.InjOn.pairwiseDisjoint_image 8 := fun h => W4c2.npd01 ((h (f := (fun _ => (Set.univ : Set ℕ))) (g := fun _ : ℕ => (0 : ℕ)) (s := {0, 1})).1
    (fun x hx y hy hxy => by obtain ⟨_, _, rfl⟩ := hx; obtain ⟨_, _, rfl⟩ := hy; exact absurd rfl hxy))
-- `Set.PairwiseDisjoint.range` idx 7: necessary (s = {0,1}, f = ∅ at 0, univ elsewhere, g x = x + 1 (range {1,2}))
theorem c2_pw67 : ¬ drop0% Set.PairwiseDisjoint.range 7 := fun h => by
  have H := h (s := ({0, 1} : Set ℕ)) (f := W4c2.fz) (fun x => x.1 + 1) (fun i _ j _ hij => by
    simp at *; rcases ‹i = 0 ∨ i = 1› with rfl | rfl <;> rcases ‹j = 0 ∨ j = 1› with rfl | rfl <;> simp_all [Function.onFun, W4c2.fz])
  exact absurd H (W4c2.np (x := 1) (y := 2) ⟨⟨0, W4c2.m0⟩, rfl⟩ ⟨⟨1, W4c2.m1⟩, rfl⟩ (by decide) (by simp [Function.onFun, W4c2.fz]))
-- `Set.PairwiseDisjoint.range` idx 8: necessary (s = {0,1}, f = const univ, g = Subtype.val)
theorem c2_pw68 : ¬ drop0% Set.PairwiseDisjoint.range 8 := fun h => absurd (h (s := ({0, 1} : Set ℕ)) (f := (fun _ => (Set.univ : Set ℕ))) Subtype.val (fun _ => le_rfl))
    (W4c2.np ⟨⟨0, W4c2.m0⟩, rfl⟩ ⟨⟨1, W4c2.m1⟩, rfl⟩ (by decide) W4c2.uu)
-- `Set.PairwiseDisjoint.union` idx 7: necessary (s = {0,1}, t = ∅, f = const univ)
theorem c2_pw69 : ¬ drop0% Set.PairwiseDisjoint.union 7 := fun h => W4c2.npd01 (by simpa using h (s := {0, 1}) (t := ∅) (f := (fun _ => (Set.univ : Set ℕ))) (Set.pairwise_empty _) (fun _ _ _ hj => absurd hj (Set.notMem_empty _)))
-- `Set.PairwiseDisjoint.union` idx 8: necessary (s = ∅, t = {0,1}, f = const univ)
theorem c2_pw70 : ¬ drop0% Set.PairwiseDisjoint.union 8 := fun h => W4c2.npd01 (by simpa using h (s := ∅) (t := {0, 1}) (f := (fun _ => (Set.univ : Set ℕ))) (Set.pairwise_empty _) (fun _ hi => absurd hi (Set.notMem_empty _)))
-- `Set.PairwiseDisjoint.union` idx 9: necessary (s = {0}, t = {1}, f = const univ)
theorem c2_pw71 : ¬ drop0% Set.PairwiseDisjoint.union 9 := fun h => absurd (h (s := {0}) (t := {1}) (f := (fun _ => (Set.univ : Set ℕ))) (W4c2.pd_one _ _) (W4c2.pd_one _ _))
    (W4c2.np (x := 0) (y := 1) (by simp) (by simp) (by decide) W4c2.uu)
-- `Set.PairwiseDisjoint.elim` idx 11: necessary (s = {0,1}, f = const ∅, i = 0, j = 1)
theorem c2_pw72 : ¬ drop0% Set.PairwiseDisjoint.elim 11 := fun h => absurd (h (s := {0, 1}) (f := (fun _ => (∅ : Set ℕ))) (W4c2.pd_emp _) W4c2.m0 W4c2.m1) (by decide)
-- `Set.PairwiseDisjoint.eq_or_disjoint` idx 6: necessary (s = univ, f = const univ, i = 0, j = 1)
theorem c2_pw73 : ¬ drop0% Set.PairwiseDisjoint.eq_or_disjoint 6 := fun h => (h (s := (Set.univ : Set ℕ)) (f := (fun _ => (Set.univ : Set ℕ))) (i := 0) (j := 1) trivial trivial).elim (by decide) W4c2.uu
-- `Set.PairwiseDisjoint.eq_or_disjoint` idx 9: necessary (s = {1}, f = const univ, i = 0, j = 1)
theorem c2_pw74 : ¬ drop0% Set.PairwiseDisjoint.eq_or_disjoint 9 := fun h => (h (s := {1}) (f := (fun _ => (Set.univ : Set ℕ))) (W4c2.pd_one _ _) (i := 0) (j := 1) rfl).elim (by decide) W4c2.uu
-- `Set.PairwiseDisjoint.eq_or_disjoint` idx 10: necessary (s = {0}, f = const univ, i = 0, j = 1)
theorem c2_pw75 : ¬ drop0% Set.PairwiseDisjoint.eq_or_disjoint 10 := fun h => (h (s := {0}) (f := (fun _ => (Set.univ : Set ℕ))) (W4c2.pd_one _ _) (i := 0) (j := 1) rfl).elim (by decide) W4c2.uu
-- `Pairwise.pairwiseDisjoint` idx 5: necessary (f = const univ, s = {0,1})
theorem c2_pw76 : ¬ drop0% Pairwise.pairwiseDisjoint 5 := fun h => W4c2.npd01 (h (f := (fun _ => (Set.univ : Set ℕ))) {0, 1})
-- `Set.PairwiseDisjoint.elim'` idx 11: necessary (s = {0,1}, f = const ∅, i = 0, j = 1)
theorem c2_pw77 : ¬ drop0% Set.PairwiseDisjoint.elim' 11 := fun h => absurd (h (s := {0, 1}) (f := (fun _ => (∅ : Set ℕ))) (W4c2.pd_emp _) W4c2.m0 W4c2.m1) (by decide)
-- `Set.PairwiseDisjoint.eq_of_le` idx 11: necessary (s = {0,1}, f = const ∅, i = 0, j = 1)
theorem c2_pw78 : ¬ drop0% Set.PairwiseDisjoint.eq_of_le 11 := fun h => absurd (h (s := {0, 1}) (f := (fun _ => (∅ : Set ℕ))) (W4c2.pd_emp _) W4c2.m0 W4c2.m1 le_rfl) (by decide)
-- `Set.PairwiseDisjoint.eq_of_le` idx 12: necessary (s = {0,1}, f n = {n}, i = 0, j = 1)
theorem c2_pw79 : ¬ drop0% Set.PairwiseDisjoint.eq_of_le 12 := fun h => absurd (h (s := {0, 1}) (f := fun n => ({n} : Set ℕ)) W4c2.pd_sing W4c2.m0 W4c2.m1 (by simp)) (by decide)
-- `Set.PairwiseDisjoint.elim_set` idx 10: necessary (s = {0,1}, f n = {n}, i = 0, j = 1, a = 1)
theorem c2_pw80 : ¬ drop0% Set.PairwiseDisjoint.elim_set 10 := fun h => absurd (h (s := {0, 1}) (f := fun n => ({n} : Set ℕ)) W4c2.pd_sing W4c2.m0 W4c2.m1 1 rfl) (by decide)
-- `Set.PairwiseDisjoint.elim_set` idx 11: necessary (s = {0,1}, f n = {n}, i = 0, j = 1, a = 0)
theorem c2_pw81 : ¬ drop0% Set.PairwiseDisjoint.elim_set 11 := fun h => absurd (h (s := {0, 1}) (f := fun n => ({n} : Set ℕ)) W4c2.pd_sing W4c2.m0 W4c2.m1 0 rfl) (by decide)
-- `Set.PairwiseDisjoint.prod` idx 8: necessary (s = {0,1}, t = {0}, f = g = const univ)
theorem c2_pw82 : ¬ drop0% Set.PairwiseDisjoint.prod 8 := fun h => absurd (h (s := ({0, 1} : Set ℕ)) (t := ({0} : Set ℕ)) (f := (fun _ => (Set.univ : Set ℕ))) (g := (fun _ => (Set.univ : Set ℕ))) (W4c2.pd_one _ _))
    (W4c2.np (x := (0, 0)) (y := (1, 0)) (by simp) (by simp) (by decide) (by simp [Function.onFun]))
-- `Set.PairwiseDisjoint.prod` idx 9: necessary (s = {0}, t = {0,1}, f = g = const univ)
theorem c2_pw83 : ¬ drop0% Set.PairwiseDisjoint.prod 9 := fun h => absurd (h (s := ({0} : Set ℕ)) (t := ({0, 1} : Set ℕ)) (f := (fun _ => (Set.univ : Set ℕ))) (g := (fun _ => (Set.univ : Set ℕ))) (W4c2.pd_one _ _))
    (W4c2.np (x := (0, 0)) (y := (0, 1)) (by simp) (by simp) (by decide) (by simp [Function.onFun]))
-- `Set.pairwiseDisjoint_pi` idx 5: necessary (ι = Unit, ι' = α = ℕ, s = univ, f = const univ)
theorem c2_pw84 : ¬ drop0% Set.pairwiseDisjoint_pi 5 := fun h => absurd (h (ι := Unit) (ι' := fun _ => ℕ) (α := fun _ => ℕ) (s := fun _ => Set.univ) (f := fun _ _ => Set.univ))
    (W4c2.np (x := fun _ => 0) (y := fun _ => 1) (by simp) (by simp) (fun e => absurd (congrFun e ()) (by decide)) (by simp [Function.onFun]))
-- `Set.pairwiseDisjoint_image_right_iff` idx 6: necessary (s = {0}, t = {0,1}, f = const 0)
theorem c2_pw85 : ¬ drop0% Set.pairwiseDisjoint_image_right_iff 6 := fun h => by
  have H := (h (f := fun (_ _ : ℕ) => (0 : ℕ)) (s := {0}) (t := {0, 1})).1 (W4c2.pd_one _ _)
  exact absurd (H (show ((0:ℕ), (0:ℕ)) ∈ ({0} : Set ℕ) ×ˢ ({0, 1} : Set ℕ) from ⟨rfl, W4c2.m0⟩)
    (show ((0:ℕ), (1:ℕ)) ∈ ({0} : Set ℕ) ×ˢ ({0, 1} : Set ℕ) from ⟨rfl, W4c2.m1⟩) rfl) (by simp)
-- `Set.pairwiseDisjoint_image_left_iff` idx 6: necessary (s = {0,1}, t = {0}, f = const 0)
theorem c2_pw86 : ¬ drop0% Set.pairwiseDisjoint_image_left_iff 6 := fun h => by
  have H := (h (f := fun (_ _ : ℕ) => (0 : ℕ)) (s := {0, 1}) (t := {0})).1 (W4c2.pd_one _ _)
  exact absurd (H (show ((0:ℕ), (0:ℕ)) ∈ ({0, 1} : Set ℕ) ×ˢ ({0} : Set ℕ) from ⟨W4c2.m0, rfl⟩)
    (show ((1:ℕ), (0:ℕ)) ∈ ({0, 1} : Set ℕ) ×ˢ ({0} : Set ℕ) from ⟨W4c2.m1, rfl⟩) rfl) (by simp)
