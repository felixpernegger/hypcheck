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

namespace W4c3
set_option hygiene false in
/-- simp at this, then close a leftover empty = univ. -/
macro "c3fin" : tactic => `(tactic| (simp at this; try exact Set.empty_ne_univ ‹_›))
end W4c3

open Set

-- `Set.prod_eq_univ` idx 4
theorem c3_1 : ¬ drop0% Set.prod_eq_univ 4 := fun h => by
  have := (h (α := Empty) (β := Unit) (s := univ) (t := ∅)).1 (Set.eq_univ_of_forall fun p => p.1.elim)
  exact Set.empty_ne_univ this.2
-- `Set.prod_eq_univ` idx 5
theorem c3_2 : ¬ drop0% Set.prod_eq_univ 5 := fun h => by
  have := (h (α := Unit) (β := Empty) (s := ∅) (t := univ)).1 (Set.eq_univ_of_forall fun p => p.2.elim)
  exact Set.empty_ne_univ this.1
-- `Set.prod_subset_prod_iff'` idx 6
theorem c3_3 : ¬ drop0% Set.prod_subset_prod_iff' 6 := fun h => by
  have := (h (s := (∅ : Set ℕ)) (t := (univ : Set ℕ)) (s₁ := ∅) (t₁ := ∅)).1 (by simp)
  c3fin
-- `Set.prod_subset_prod_iff_left` idx 5
theorem c3_4 : ¬ drop0% Set.prod_subset_prod_iff_left 5 := fun h => by
  have := (h (s := (univ : Set ℕ)) (t := (∅ : Set ℕ)) (s₁ := ∅)).1 (by simp)
  c3fin
-- `Set.prod_eq_prod_iff_of_nonempty` idx 6
theorem c3_5 : ¬ drop0% Set.prod_eq_prod_iff_of_nonempty 6 := fun h => by
  have := (h (s := (∅ : Set ℕ)) (t := (univ : Set ℕ)) (s₁ := ∅) (t₁ := ∅)).1 (by simp)
  c3fin
-- `Set.prod_eq_iff_eq` idx 5
theorem c3_6 : ¬ drop0% Set.prod_eq_iff_eq 5 := fun h => by
  have := (h (s := (univ : Set ℕ)) (t := (∅ : Set ℕ)) (s₁ := ∅)).1 (by simp)
  c3fin
-- `Monotone.set_prod` idx 6
theorem c3_7 : ¬ drop0% Monotone.set_prod 6 := fun h => by
  have := h (f := fun b : Bool => if b then (∅ : Set Unit) else univ) (g := fun _ : Bool => (univ : Set Unit))
    monotone_const (show false ≤ true by decide)
  c3fin
-- `Antitone.set_prod` idx 6
theorem c3_8 : ¬ drop0% Antitone.set_prod 6 := fun h => by
  have := h (f := fun b : Bool => if b then (univ : Set Unit) else ∅) (g := fun _ : Bool => (univ : Set Unit))
    antitone_const (show false ≤ true by decide)
  c3fin
-- `Antitone.set_prod` idx 7
theorem c3_9 : ¬ drop0% Antitone.set_prod 7 := fun h => by
  have := h (g := fun b : Bool => if b then (univ : Set Unit) else ∅) (f := fun _ : Bool => (univ : Set Unit))
    antitone_const (show false ≤ true by decide)
  c3fin
-- `MonotoneOn.set_prod` idx 7
theorem c3_10 : ¬ drop0% MonotoneOn.set_prod 7 := fun h => by
  have := h (s := univ) (f := fun b : Bool => if b then (∅ : Set Unit) else univ) (g := fun _ : Bool => (univ : Set Unit))
    monotoneOn_const (mem_univ false) (mem_univ true) (show false ≤ true by decide)
  c3fin
-- `MonotoneOn.set_prod` idx 8
theorem c3_11 : ¬ drop0% MonotoneOn.set_prod 8 := fun h => by
  have := h (s := univ) (g := fun b : Bool => if b then (∅ : Set Unit) else univ) (f := fun _ : Bool => (univ : Set Unit))
    monotoneOn_const (mem_univ false) (mem_univ true) (show false ≤ true by decide)
  c3fin
-- `AntitoneOn.set_prod` idx 7
theorem c3_12 : ¬ drop0% AntitoneOn.set_prod 7 := fun h => by
  have := h (s := univ) (f := fun b : Bool => if b then (univ : Set Unit) else ∅) (g := fun _ : Bool => (univ : Set Unit))
    antitoneOn_const (mem_univ false) (mem_univ true) (show false ≤ true by decide)
  c3fin
-- `AntitoneOn.set_prod` idx 8
theorem c3_13 : ¬ drop0% AntitoneOn.set_prod 8 := fun h => by
  have := h (s := univ) (g := fun b : Bool => if b then (univ : Set Unit) else ∅) (f := fun _ : Bool => (univ : Set Unit))
    antitoneOn_const (mem_univ false) (mem_univ true) (show false ≤ true by decide)
  c3fin
-- `Set.EqOn.left_of_eqOn_prodMap` idx 11
theorem c3_14 : ¬ drop0% Set.EqOn.left_of_eqOn_prodMap 11 := fun h => by
  have := h (s := univ) (t := (∅ : Set ℕ)) (f := fun n : ℕ => n) (f' := fun _ => 0) (g := id) (g' := id)
    (fun p hp => by simp at hp) (mem_univ 1)
  c3fin
-- `Set.EqOn.right_of_eqOn_prodMap` idx 11
theorem c3_15 : ¬ drop0% Set.EqOn.right_of_eqOn_prodMap 11 := fun h => by
  have := h (t := univ) (s := (∅ : Set ℕ)) (g := fun n : ℕ => n) (g' := fun _ => 0) (f := id) (f' := id)
    (fun p hp => by simp at hp) (mem_univ 1)
  c3fin
-- `Set.eqOn_prodMap_iff` idx 10
theorem c3_16 : ¬ drop0% Set.eqOn_prodMap_iff 10 := fun h => by
  have := ((h (t := univ) (s := (∅ : Set ℕ)) (g := fun n : ℕ => n) (g' := fun _ => 0) (f := id) (f' := id)
    (by simp)).1 (fun p hp => by simp at hp)).2 (mem_univ 1)
  c3fin
-- `Set.eqOn_prodMap_iff` idx 11
theorem c3_17 : ¬ drop0% Set.eqOn_prodMap_iff 11 := fun h => by
  have := ((h (s := univ) (t := (∅ : Set ℕ)) (f := fun n : ℕ => n) (f' := fun _ => 0) (g := id) (g' := id)
    (by simp)).1 (fun p hp => by simp at hp)).1 (mem_univ 1)
  c3fin
-- `Set.diagonal_nonempty` idx 1
theorem c3_18 : ¬ drop0% Set.diagonal_nonempty 1 := fun h => by
  obtain ⟨p, _⟩ := h (α := Empty); exact p.1.elim
-- `Set.diagonal_eq_univ` idx 1
theorem c3_19 : ¬ drop0% Set.diagonal_eq_univ 1 := fun h => by
  have := (Set.ext_iff.1 (h (α := Bool)) (true, false)).2 trivial
  c3fin
-- `Set.range_const_eq_diagonal` idx 2
theorem c3_20 : ¬ drop0% Set.range_const_eq_diagonal 2 := fun h => by
  obtain ⟨b, _⟩ := (Set.ext_iff.1 (h (α := Empty) (β := Empty)) (fun e => e.elim)).2 (fun x => x.elim)
  exact b.elim
-- `Set.Subsingleton.offDiag_eq_empty` idx 2
theorem c3_21 : ¬ drop0% Set.Subsingleton.offDiag_eq_empty 2 := fun h => by
  have : (true, false) ∈ (univ : Set Bool).offDiag := by simp [Set.mem_offDiag]
  rw [h] at this; exact this

-- `Set.subsingleton_univ_pi` idx 3
theorem c3_22 : ¬ drop0% Set.subsingleton_univ_pi 3 := fun h => by
  have := h (t := fun _ : Unit => (univ : Set Bool))
    (show (fun _ : Unit => true) ∈ Set.univ.pi (fun _ : Unit => (univ : Set Bool)) by simp)
    (show (fun _ : Unit => false) ∈ Set.univ.pi (fun _ : Unit => (univ : Set Bool)) by simp)
  exact absurd (congrFun this ()) (by decide)
-- `Set.pi_mono'` idx 6
theorem c3_23 : ¬ drop0% Set.pi_mono' 6 := fun h => by
  have := h (s₁ := (univ : Set Unit)) (s₂ := univ) (t₁ := fun _ => (univ : Set Unit)) (t₂ := fun _ => ∅)
    subset_rfl (show (fun _ => ()) ∈ Set.univ.pi (fun _ : Unit => (univ : Set Unit)) by simp)
  c3fin
-- `Set.pi_mono'` idx 7
theorem c3_24 : ¬ drop0% Set.pi_mono' 7 := fun h => by
  have := h (s₁ := (∅ : Set Unit)) (s₂ := univ) (t₁ := fun _ => (∅ : Set Unit)) (t₂ := fun _ => ∅)
    (fun _ _ => subset_rfl) (show (fun _ => ()) ∈ Set.pi ∅ (fun _ : Unit => (∅ : Set Unit)) by simp)
  c3fin
-- `Set.pi_mono` idx 5
theorem c3_25 : ¬ drop0% Set.pi_mono 5 := fun h => by
  have := h (s := (univ : Set Unit)) (t₁ := fun _ => (univ : Set Unit)) (t₂ := fun _ => ∅)
    (show (fun _ => ()) ∈ Set.univ.pi (fun _ : Unit => (univ : Set Unit)) by simp)
  c3fin
-- `Set.pi_congr` idx 6
theorem c3_26 : ¬ drop0% Set.pi_congr 6 := fun h => by
  have := h (s₁ := (∅ : Set Unit)) (s₂ := univ) (t₁ := fun _ => (∅ : Set Unit)) (t₂ := fun _ => ∅)
    (fun _ _ => rfl)
  c3fin
-- `Set.pi_congr` idx 7
theorem c3_27 : ¬ drop0% Set.pi_congr 7 := fun h => by
  have := h (s₁ := (univ : Set Unit)) (s₂ := univ) (t₁ := fun _ => (univ : Set Unit)) (t₂ := fun _ => ∅) rfl
  c3fin
-- `Set.pi_eq_empty` idx 5
theorem c3_28 : ¬ drop0% Set.pi_eq_empty 5 := fun h => by
  have := h (s := (∅ : Set Unit)) (t := fun _ => (∅ : Set Unit)) (i := ()) rfl
  c3fin
-- `Set.pi_eq_empty` idx 6
theorem c3_29 : ¬ drop0% Set.pi_eq_empty 6 := fun h => by
  have := h (s := (univ : Set Unit)) (t := fun _ => (univ : Set Unit)) (i := ()) trivial
  c3fin
-- `Set.univ_pi_eq_empty` idx 4
theorem c3_30 : ¬ drop0% Set.univ_pi_eq_empty 4 := fun h => by
  have := h (t := fun _ : Unit => (univ : Set Unit)) (i := ())
  c3fin
-- `Set.univ_pi_empty` idx 2
theorem c3_31 : ¬ drop0% Set.univ_pi_empty 2 := fun h => by
  have := h (ι := Empty) (α := fun _ => Unit)
  have h2 : (fun e : Empty => e.elim : ∀ i : Empty, (fun _ => Unit) i) ∈ Set.univ.pi (fun _ => (∅ : Set Unit)) :=
    fun e => e.elim
  rw [this] at h2; exact h2
-- `Set.Disjoint.set_pi` idx 6
theorem c3_32 : ¬ drop0% Set.Disjoint.set_pi 6 := fun h => by
  have := h (s := (∅ : Set Unit)) (t₁ := fun _ => (∅ : Set Unit)) (t₂ := fun _ => ∅) (i := ()) (by simp)
  c3fin
-- `Set.Disjoint.set_pi` idx 7
theorem c3_33 : ¬ drop0% Set.Disjoint.set_pi 7 := fun h => by
  have := h (s := (univ : Set Unit)) (t₁ := fun _ => (univ : Set Unit)) (t₂ := fun _ => univ) (i := ()) trivial
  c3fin
-- `Set.pi_image_pi_of_subset` idx 5
theorem c3_34 : ¬ drop0% Set.pi_image_pi_of_subset 5 := fun h => by
  have := h (s₁ := (∅ : Set Unit)) (s₂ := univ) (C := fun _ => (∅ : Set (Set Unit))) (empty_subset _)
  c3fin
-- `Set.pi_eq_empty_iff'` idx 4
theorem c3_35 : ¬ drop0% Set.pi_eq_empty_iff' 4 := fun h => by
  have := (h (s := (∅ : Set Unit)) (t := fun _ => (univ : Set Empty))).1
    (Set.eq_empty_of_forall_notMem fun f _ => (f ()).elim)
  c3fin
-- `Set.disjoint_pi` idx 5
theorem c3_36 : ¬ drop0% Set.disjoint_pi 5 := fun h => by
  have := (h (s := (∅ : Set Unit)) (t₁ := fun _ => (univ : Set Empty)) (t₂ := fun _ => univ)).1
    (Set.disjoint_left.2 fun f _ _ => (f ()).elim)
  c3fin
-- `Set.union_pi_inter` idx 6
theorem c3_37 : ¬ drop0% Set.union_pi_inter 6 := fun h => by
  have := h (s₁ := (∅ : Set Unit)) (s₂ := univ) (t₁ := fun _ => (∅ : Set Unit)) (t₂ := fun _ => univ)
    (fun _ h => absurd trivial h)
  c3fin
-- `Set.union_pi_inter` idx 7
theorem c3_38 : ¬ drop0% Set.union_pi_inter 7 := fun h => by
  have := h (s₂ := (∅ : Set Unit)) (s₁ := univ) (t₂ := fun _ => (∅ : Set Unit)) (t₁ := fun _ => univ)
    (fun _ h => absurd trivial h)
  c3fin
-- `Set.pi_update_of_notMem` idx 6
theorem c3_39 : ¬ drop0% Set.pi_update_of_notMem 6 := fun h => by
  have := h (s := (univ : Set Unit)) (i := ()) (fun _ => false) true
    (fun _ (x : Bool) => if x then (univ : Set Unit) else ∅)
  c3fin
-- `Set.pi_update_of_mem` idx 6
theorem c3_40 : ¬ drop0% Set.pi_update_of_mem 6 := fun h => by
  have := h (s := (∅ : Set Unit)) (i := ()) (fun _ => ()) () (fun _ _ => (∅ : Set Unit))
  c3fin
-- `Set.eval_image_pi_subset` idx 5
theorem c3_41 : ¬ drop0% Set.eval_image_pi_subset 5 := fun h => by
  have := h (s := (∅ : Set Unit)) (t := fun _ => (∅ : Set Unit)) (i := ())
  c3fin
-- `Set.subset_eval_image_pi` idx 4
theorem c3_42 : ¬ drop0% Set.subset_eval_image_pi 4 := fun h => by
  have := h (s := (univ : Set Bool)) (t := fun b => if b then (∅ : Set Unit) else univ) false
  c3fin
-- `Set.eval_image_pi` idx 5
theorem c3_43 : ¬ drop0% Set.eval_image_pi 5 := fun h => by
  have := h (s := (∅ : Set Unit)) (t := fun _ => (∅ : Set Unit)) (i := ()) (by simp)
  c3fin
-- `Set.eval_image_pi` idx 6
theorem c3_44 : ¬ drop0% Set.eval_image_pi 6 := fun h => by
  have := h (s := (univ : Set Bool)) (t := fun b => if b then (∅ : Set Unit) else univ) (i := false) trivial
  c3fin
-- `Set.eval_image_pi_of_notMem` idx 6
theorem c3_45 : ¬ drop0% Set.eval_image_pi_of_notMem 6 := fun h => by
  classical
  have := h (s := (univ : Set Unit)) (t := fun _ => ({true} : Set Bool)) (i := ())
  have hne : (Set.univ.pi fun _ : Unit => ({true} : Set Bool)).Nonempty := ⟨fun _ => true, by simp⟩
  rw [if_pos hne] at this
  have h2 : false ∈ Function.eval () '' Set.univ.pi fun _ : Unit => ({true} : Set Bool) := this ▸ trivial
  obtain ⟨x, h1, h3⟩ := h2
  have h4 : x () = true := h1 () trivial
  simp [h4] at h3
-- `Set.eval_image_univ_pi` idx 4
theorem c3_46 : ¬ drop0% Set.eval_image_univ_pi 4 := fun h => by
  have := h (t := fun b => if b then (∅ : Set Unit) else univ) (i := false)
  c3fin
-- `Set.piMap_mapsTo_pi` idx 7
theorem c3_47 : ¬ drop0% Set.piMap_mapsTo_pi 7 := fun h => by
  have := h (I := (univ : Set Unit)) (f := fun _ (x : Unit) => x) (s := fun _ => univ) (t := fun _ => (∅ : Set Unit))
    (show (fun _ => ()) ∈ Set.univ.pi (fun _ : Unit => (univ : Set Unit)) by simp)
  c3fin
-- `Set.piMap_image_pi` idx 5
theorem c3_48 : ¬ drop0% Set.piMap_image_pi 5 := fun h => by
  have := h (s := (∅ : Set Unit)) (f := fun _ (_ : Unit) => true) (fun _ => univ)
  have h2 : (fun _ => false) ∈ Set.pi (∅ : Set Unit) fun i => (fun _ (_ : Unit) => true) i '' (fun _ => (univ : Set Unit)) i := by simp
  rw [← this] at h2
  obtain ⟨x, _, hx⟩ := h2
  have := congrFun hx (); simp at this
-- `Set.update_mem_pi_iff_of_mem` idx 8
theorem c3_49 : ¬ drop0% Set.update_mem_pi_iff_of_mem 8 := fun h => by
  have := (h (s := (univ : Set Bool)) (t := fun j => if j then (univ : Set Unit) else ∅) (a := fun _ => ())
    (i := true) (b := ())).2 (by simp)
  have := this false trivial
  c3fin
-- `Set.update_preimage_pi` idx 7
theorem c3_50 : ¬ drop0% Set.update_preimage_pi 7 := fun h => by
  have := h (s := (∅ : Set Unit)) (t := fun _ => (∅ : Set Unit)) (i := ()) (f := fun _ => ()) (by simp)
  c3fin
-- `Set.update_preimage_pi` idx 8
theorem c3_51 : ¬ drop0% Set.update_preimage_pi 8 := fun h => by
  have := h (s := (univ : Set Bool)) (t := fun j => if j then (univ : Set Unit) else ∅) (i := true)
    (f := fun _ => ()) trivial
  have h2 := (Set.ext_iff.1 this ()).2 (by simp)
  have := h2 false trivial
  c3fin
-- `Set.update_preimage_univ_pi` idx 6
theorem c3_52 : ¬ drop0% Set.update_preimage_univ_pi 6 := fun h => by
  have := h (t := fun j => if j then (univ : Set Unit) else ∅) (i := true) (f := fun _ => ())
  have h2 := (Set.ext_iff.1 this ()).2 (by simp)
  have := h2 false trivial
  c3fin
-- `Set.exists_range_eq_graphOn_univ` idx 4
theorem c3_53 : ¬ drop0% Set.exists_range_eq_graphOn_univ 4 := fun h => by
  obtain ⟨f', hf'⟩ := h (f := fun e : Empty => (e.elim : Unit × Unit)) (fun g => g.elim)
  have : ((), f' ()) ∈ Set.univ.graphOn f' := by simp
  rw [← hf'] at this; obtain ⟨e, _⟩ := this; exact e.elim
-- `Set.exists_range_eq_graphOn_univ` idx 5
theorem c3_54 : ¬ drop0% Set.exists_range_eq_graphOn_univ 5 := fun h => by
  obtain ⟨f', hf'⟩ := h (f := fun b : Bool => ((), b)) (fun _ => ⟨true, rfl⟩)
  have : ((), !f' ()) ∈ Set.range (fun b : Bool => ((), b)) := ⟨_, rfl⟩
  rw [hf'] at this; c3fin
-- `Set.exists_equiv_range_eq_graphOn_univ` idx 4
theorem c3_55 : ¬ drop0% Set.exists_equiv_range_eq_graphOn_univ 4 := fun h => by
  obtain ⟨e, _⟩ := h (f := fun _ : Unit => (true, ())) (fun _ => ⟨(), rfl⟩) (fun _ _ => by simp)
  exact absurd (e.injective (Subsingleton.elim (e true) (e false))) (by decide)
-- `Set.exists_equiv_range_eq_graphOn_univ` idx 5
theorem c3_56 : ¬ drop0% Set.exists_equiv_range_eq_graphOn_univ 5 := fun h => by
  obtain ⟨e, _⟩ := h (f := fun _ : Unit => ((), true)) (fun _ => ⟨(), rfl⟩) (fun _ _ => by simp)
  exact absurd (e.symm.injective (Subsingleton.elim (e.symm true) (e.symm false))) (by decide)
-- `Set.exists_equiv_range_eq_graphOn_univ` idx 6
theorem c3_57 : ¬ drop0% Set.exists_equiv_range_eq_graphOn_univ 6 := fun h => by
  obtain ⟨e, he⟩ := h (f := fun p : Bool × Bool => p) (fun b => ⟨(b, b), rfl⟩) (fun b => ⟨(b, b), rfl⟩)
  have : (true, !e true) ∈ Set.range (fun p : Bool × Bool => p) := ⟨_, rfl⟩
  rw [he] at this; c3fin
-- `Set.exists_eq_graphOn_univ` idx 3
theorem c3_58 : ¬ drop0% Set.exists_eq_graphOn_univ 3 := fun h => by
  obtain ⟨f, hf⟩ := h (s := (∅ : Set (Unit × Unit)))
  have : ((), f ()) ∈ Set.univ.graphOn f := by simp
  rw [← hf] at this; exact this
-- `Set.exists_eq_mgraphOn_univ` idx 3
theorem c3_59 : ¬ drop0% Set.exists_eq_mgraphOn_univ 3 := fun h => by
  obtain ⟨f, hf⟩ := h (s := (∅ : Set (Unit × Unit)))
  have : ((), f ()) ∈ Set.univ.graphOn f := by simp
  rw [← hf] at this; exact this

namespace W4c3
/-- Two distinct unrelated members refute pairwise. -/
theorem np {α : Type*} {s : Set α} {r : α → α → Prop} {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    (hne : x ≠ y) (hr : ¬ r x y) : ¬ s.Pairwise r := fun h => hr (h hx hy hne)
/-- Two distinct indices sharing an element refute pairwise disjointness of set families. -/
theorem npd {α ι : Type*} {s : Set ι} {f : ι → Set α} {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hne : i ≠ j) (x : α) (hxi : x ∈ f i) (hxj : x ∈ f j) : ¬ s.PairwiseDisjoint f :=
  fun h => Set.disjoint_left.1 (h hi hj hne) hxi hxj
theorem ntt : ¬ Disjoint true true := by simp
end W4c3
open W4c3

-- `Set.pairwise_iUnion` idx 4
theorem c3_61 : ¬ drop1% Set.pairwise_iUnion 4 := fun h => by
  have := (h (κ := Bool) (r := fun _ _ : ULift.{1} ℕ => False)
    (f := fun b => if b then {ULift.up 0} else {ULift.up 1})).2 (fun n => by cases n <;> simp)
  exact np (x := ULift.up 0) (y := ULift.up 1) (by simp) (by simp) (by simp) id this
-- `Set.pairwise_iUnion₂` idx 2
theorem c3_62 : ¬ drop0% Set.pairwise_iUnion₂ 2 := fun h => by
  have := h (s := {{0}, {1}}) (fun _ _ : ℕ => False) (by simp)
  exact np (x := 0) (y := 1) (by simp) (by simp) (by simp) id this
-- `Set.pairwise_iUnion₂` idx 4
theorem c3_63 : ¬ drop0% Set.pairwise_iUnion₂ 4 := fun h => by
  have := h (s := {{0, 1}}) (by simp [DirectedOn]) (fun _ _ : ℕ => False)
  exact np (x := 0) (y := 1) (by simp) (by simp) (by simp) id this
-- `Set.pairwise_iUnion₂_iff` idx 3
theorem c3_64 : ¬ drop0% Set.pairwise_iUnion₂_iff 3 := fun h => by
  have := (h (s := {{0}, {1}}) (r := fun _ _ : ℕ => False)).2 (by simp)
  exact np (x := 0) (y := 1) (by simp) (by simp) (by simp) id this
-- `Set.pairwise_sUnion` idx 3
theorem c3_65 : ¬ drop0% Set.pairwise_sUnion 3 := fun h => by
  have := (h (s := {{0}, {1}}) (r := fun _ _ : ℕ => False)).2 (by simp)
  exact np (x := 0) (y := 1) (by simp) (by simp) (by simp) id this
-- `Set.pairwiseDisjoint_iUnion` idx 7
theorem c3_66 : ¬ drop0% Set.pairwiseDisjoint_iUnion 7 := fun h => by
  have := (h (g := fun b : Bool => if b then ({0} : Set ℕ) else {1}) (f := fun _ => true)).2
    (fun n => by cases n <;> simp)
  exact np (x := 0) (y := 1) (by simp) (by simp) (by simp) ntt this
-- `Set.pairwiseDisjoint_sUnion` idx 6
theorem c3_67 : ¬ drop0% Set.pairwiseDisjoint_sUnion 6 := fun h => by
  have := (h (s := {{0}, {1}}) (f := fun (_ : ℕ) => true)).2 (by simp)
  exact np (x := 0) (y := 1) (by simp) (by simp) (by simp) ntt this
-- `Set.PairwiseDisjoint.biUnion` idx 7
theorem c3_68 : ¬ drop0% Set.PairwiseDisjoint.biUnion 7 := fun h => by
  have := h (s := univ) (g := fun b : Bool => if b then ({0} : Set ℕ) else {1}) (f := fun _ => true)
    (fun n _ => by cases n <;> simp)
  exact np (x := 0) (y := 1) (by simp) (by simp) (by simp) ntt this
-- `Set.PairwiseDisjoint.biUnion` idx 8
theorem c3_69 : ¬ drop0% Set.PairwiseDisjoint.biUnion 8 := fun h => by
  have := h (s := (univ : Set Unit)) (g := fun _ => ({0, 1} : Set ℕ)) (f := fun _ => true)
    (fun a _ b _ hab => absurd (Subsingleton.elim a b) hab)
  exact np (x := 0) (y := 1) (by simp) (by simp) (by simp) ntt this
-- `Set.PairwiseDisjoint.prod_left` idx 7
theorem c3_70 : ¬ drop0% Set.PairwiseDisjoint.prod_left 7 := fun h => by
  have := h (s := ({0, 1} : Set ℕ)) (t := (univ : Set Unit)) (f := fun _ => true)
    (fun a _ b _ hab => absurd (Subsingleton.elim a b) hab)
  exact np (x := (0, ())) (y := (1, ())) (by simp) (by simp) (by simp) ntt this
-- `Set.PairwiseDisjoint.prod_left` idx 8
theorem c3_71 : ¬ drop0% Set.PairwiseDisjoint.prod_left 8 := fun h => by
  have := h (t := ({0, 1} : Set ℕ)) (s := (univ : Set Unit)) (f := fun _ => true)
    (fun a _ b _ hab => absurd (Subsingleton.elim a b) hab)
  exact np (x := ((), 0)) (y := ((), 1)) (by simp) (by simp) (by simp) ntt this
-- `Set.coe_biUnionEqSigmaOfDisjoint_symm_apply` idx 4
theorem c3_72 : ¬ indep0% Set.coe_biUnionEqSigmaOfDisjoint_symm_apply 4 := fun h =>
  npd (s := univ) (f := fun _ : Bool => ({0} : Set ℕ)) (i := true) (j := false) trivial trivial (by decide)
    0 rfl rfl (h ⟨⟨true, trivial⟩, ⟨0, rfl⟩⟩)
-- `Set.coe_snd_biUnionEqSigmaOfDisjoint` idx 4
theorem c3_73 : ¬ indep0% Set.coe_snd_biUnionEqSigmaOfDisjoint 4 := fun h =>
  npd (s := univ) (f := fun _ : Bool => ({0} : Set ℕ)) (i := true) (j := false) trivial trivial (by decide)
    0 rfl rfl (h ⟨0, by simp⟩)
-- `Set.pairwiseDisjoint_pair_insert` idx 3
theorem c3_74 : ¬ drop0% Set.pairwiseDisjoint_pair_insert 3 := fun h =>
  npd (i := (∅ : Set ℕ)) (j := {0}) (by simp) (by simp) (by simp) {0} (by simp) (by simp)
    (h (s := {0}) (a := 0))
-- `Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion` idx 5
theorem c3_75 : ¬ drop0% Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion 5 := fun h => by
  have := h (s := {true}) (t := {false}) (f := fun _ => ({0} : Set ℕ)) (by simp) (by simp)
  simp at this
-- `Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion` idx 6
theorem c3_76 : ¬ drop0% Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion 6 := fun h => by
  have := h (s := {true}) (t := ∅) (f := fun _ => (∅ : Set ℕ)) (by simp) (by simp)
  simp at this
-- `Pairwise.subset_of_biUnion_subset_biUnion` idx 5
theorem c3_77 : ¬ drop0% Pairwise.subset_of_biUnion_subset_biUnion 5 := fun h => by
  have := h (s := {true}) (t := {false}) (f := fun _ => ({0} : Set ℕ)) (by simp) (by simp)
  simp at this
-- `Pairwise.subset_of_biUnion_subset_biUnion` idx 6
theorem c3_78 : ¬ drop0% Pairwise.subset_of_biUnion_subset_biUnion 6 := fun h => by
  have := h (s := {true}) (t := ∅) (f := fun _ => (∅ : Set ℕ)) (fun _ _ _ => by simp [Function.onFun]) (by simp)
  simp at this
-- `Pairwise.subset_of_biUnion_subset_biUnion` idx 7
theorem c3_79 : ¬ drop0% Pairwise.subset_of_biUnion_subset_biUnion 7 := fun h => by
  have := h (s := univ) (t := ∅) (f := fun _ : Unit => ({0} : Set ℕ)) (fun a b hab => absurd (Subsingleton.elim a b) hab) (by simp)
  simp at this
-- `Pairwise.biUnion_injective` idx 3
theorem c3_80 : ¬ drop0% Pairwise.biUnion_injective 3 := fun h => by
  have := @h _ _ (fun _ : Bool => ({0} : Set ℕ)) (fun _ => by simp) {true} {false} (by simp)
  simp at this
-- `Pairwise.biUnion_injective` idx 4
theorem c3_81 : ¬ drop0% Pairwise.biUnion_injective 4 := fun h => by
  have := @h _ _ (fun _ : Unit => (∅ : Set ℕ)) (fun _ _ _ => by simp [Function.onFun]) ∅ univ (by simp)
  exact Set.empty_ne_univ this
-- `pairwiseDisjoint_unique` idx 5
theorem c3_82 : ¬ drop0% pairwiseDisjoint_unique 5 := fun h => by
  obtain ⟨i, _, hu⟩ := h (s := univ) (f := fun _ : Bool => ({0} : Set ℕ)) (y := 0) (by simp)
  have h1 := hu true ⟨trivial, rfl⟩
  have h2 := hu false ⟨trivial, rfl⟩
  exact absurd (h1.trans h2.symm) (by decide)

-- `Set.piecewise_eq_of_mem` idx 7
theorem c3_83 : ¬ drop1% Set.piecewise_eq_of_mem 7 := fun h => by
  classical
  have := h (δ := fun _ => Bool) (∅ : Set (ULift.{1} Bool)) (fun _ => true) (fun _ => false) (i := ULift.up true)
  simp at this
-- `Set.piecewise_eq_of_notMem` idx 7
theorem c3_84 : ¬ drop1% Set.piecewise_eq_of_notMem 7 := fun h => by
  classical
  have := h (δ := fun _ => Bool) (univ : Set (ULift.{1} Bool)) (fun _ => true) (fun _ => false) (i := ULift.up true)
  simp at this
-- `Set.piecewise_le` idx 8
theorem c3_85 : ¬ drop0% Set.piecewise_le 8 := fun h => by
  classical
  have := h (δ := fun _ : Unit => ℕ) (s := univ) (f₁ := fun _ => 1) (f₂ := fun _ => 0) (g := fun _ => 0)
    (fun _ h => absurd trivial h) ()
  simp at this
-- `Set.piecewise_le` idx 9
theorem c3_86 : ¬ drop0% Set.piecewise_le 9 := fun h => by
  classical
  have := h (δ := fun _ : Unit => ℕ) (s := ∅) (f₁ := fun _ => 0) (f₂ := fun _ => 1) (g := fun _ => 0)
    (fun _ h => absurd h id) ()
  simp at this
-- `Set.le_piecewise` idx 8
theorem c3_87 : ¬ drop0% Set.le_piecewise 8 := fun h => by
  classical
  have := h (δ := fun _ : Unit => ℕ) (s := univ) (f₁ := fun _ => 0) (f₂ := fun _ => 1) (g := fun _ => 1)
    (fun _ h => absurd trivial h) ()
  simp at this
-- `Set.le_piecewise` idx 9
theorem c3_88 : ¬ drop0% Set.le_piecewise 9 := fun h => by
  classical
  have := h (δ := fun _ : Unit => ℕ) (s := ∅) (f₁ := fun _ => 1) (f₂ := fun _ => 0) (g := fun _ => 1)
    (fun _ h => absurd h id) ()
  simp at this
-- `Set.piecewise_mono` idx 9
theorem c3_89 : ¬ drop0% Set.piecewise_mono 9 := fun h => by
  classical
  have := h (δ := fun _ : Unit => ℕ) (s := univ) (f₁ := fun _ => 1) (f₂ := fun _ => 0) (g₁ := fun _ => 0)
    (g₂ := fun _ => 0) (fun _ h => absurd trivial h) ()
  simp at this
-- `Set.piecewise_mono` idx 10
theorem c3_90 : ¬ drop0% Set.piecewise_mono 10 := fun h => by
  classical
  have := h (δ := fun _ : Unit => ℕ) (s := ∅) (f₁ := fun _ => 0) (f₂ := fun _ => 1) (g₁ := fun _ => 0)
    (g₂ := fun _ => 0) (fun _ h => absurd h id) ()
  simp at this
-- `Set.piecewise_insert_of_ne` idx 8
theorem c3_91 : ¬ drop1% Set.piecewise_insert_of_ne 8 := fun h => by
  classical
  have := h (δ := fun _ => Bool) (∅ : Set (ULift.{1} Bool)) (fun _ => true) (fun _ => false)
    (i := ULift.up true) (j := ULift.up true)
  simp at this
-- `Set.MapsTo.piecewise_ite` idx 11
theorem c3_92 : ¬ drop0% Set.MapsTo.piecewise_ite 11 := fun h => by
  classical
  have := h (s := univ) (s₁ := univ) (s₂ := ∅) (t := univ) (t₁ := ∅) (t₂ := ∅)
    (f₁ := fun _ : Unit => ()) (f₂ := fun _ => ()) (fun _ hx => by simp at hx)
  simp [Set.MapsTo, Set.ite] at this
-- `Set.MapsTo.piecewise_ite` idx 12
theorem c3_93 : ¬ drop0% Set.MapsTo.piecewise_ite 12 := fun h => by
  classical
  have := h (s := ∅) (s₁ := ∅) (s₂ := univ) (t := ∅) (t₁ := ∅) (t₂ := ∅)
    (f₁ := fun _ : Unit => ()) (f₂ := fun _ => ()) (fun _ hx => by simp at hx)
  simp [Set.MapsTo, Set.ite] at this
-- `Set.EqOn.piecewise_ite'` idx 9
theorem c3_94 : ¬ drop0% Set.EqOn.piecewise_ite' 9 := fun h => by
  classical
  have := h (s := univ) (t := univ) (t' := ∅) (f := fun _ : Unit => 1) (f' := fun _ => 0) (g := fun _ => 0)
    (fun _ _ => rfl) (show () ∈ (univ : Set Unit).ite univ ∅ by simp [Set.ite])
  simp at this
-- `Set.EqOn.piecewise_ite'` idx 10
theorem c3_95 : ¬ drop0% Set.EqOn.piecewise_ite' 10 := fun h => by
  classical
  have := h (s := ∅) (t := ∅) (t' := univ) (f := fun _ : Unit => 0) (f' := fun _ => 1) (g := fun _ => 0)
    (fun _ _ => rfl) (show () ∈ (∅ : Set Unit).ite ∅ univ by simp [Set.ite])
  simp at this
-- `Set.EqOn.piecewise_ite` idx 10
theorem c3_96 : ¬ drop0% Set.EqOn.piecewise_ite 10 := fun h => by
  classical
  have := h (s := ∅) (t := ∅) (t' := univ) (f := fun _ : Unit => 0) (f' := fun _ => 1) (g := fun _ => 0)
    (fun _ _ => rfl) (show () ∈ (∅ : Set Unit).ite ∅ univ by simp [Set.ite])
  simp at this
-- `mulSupport_comp_inv_smul₀` idx 7
theorem c3_97 : ¬ drop0% mulSupport_comp_inv_smul₀ 7 := fun h => by
  have := h (α := ℚ) (β := ℚ) (c := 0) (fun x : ℚ => x + 1)
  have h2 := (Set.ext_iff.1 this 0).2 (Set.mem_smul_set.2 ⟨1, by simp, by simp⟩)
  simp at h2
-- `support_comp_inv_smul₀` idx 7
theorem c3_98 : ¬ drop0% support_comp_inv_smul₀ 7 := fun h => by
  have := h (α := ℚ) (β := ℚ) (c := 0) (fun x : ℚ => x)
  have h2 := (Set.ext_iff.1 this 0).2 (Set.mem_smul_set.2 ⟨1, by simp, by simp⟩)
  simp at h2

namespace W4c3
open Set.powersetCard in
/-- The powersetCard of size 0 has one element. -/
instance ss0 {α : Type} : Subsingleton (Set.powersetCard α 0) :=
  ⟨fun s t => Subtype.ext (by rw [Finset.card_eq_zero.1 (card_eq s), Finset.card_eq_zero.1 (card_eq t)])⟩
open Set.powersetCard in
/-- The powersetCard of size 2 over Bool has one element. -/
instance ssB : Subsingleton (Set.powersetCard Bool 2) :=
  ⟨fun s t => Subtype.ext (by
    rw [Finset.eq_univ_of_card (s : Finset Bool) (by simp), Finset.eq_univ_of_card (t : Finset Bool) (by simp)])⟩
end W4c3

-- `Set.powersetCard.exists_mem_notMem` idx 2
theorem c3_99 : ¬ drop0% Set.powersetCard.exists_mem_notMem 2 := fun h => by
  obtain ⟨s, ha, _⟩ := h (α := Bool) (n := 0) (a := true) (b := false) (by simp) (by simp)
  have := (Set.powersetCard.mem_coe_iff).2 ha
  rw [Finset.card_eq_zero.1 (Set.powersetCard.card_eq s)] at this; simp at this
-- `Set.powersetCard.exists_mem_notMem` idx 3
theorem c3_100 : ¬ drop0% Set.powersetCard.exists_mem_notMem 3 := fun h => by
  obtain ⟨s, _, hb⟩ := h (α := Bool) (n := 2) (a := true) (b := false) (by norm_num) (by decide)
  apply hb; apply Set.powersetCard.mem_coe_iff.1
  rw [Finset.eq_univ_of_card (s : Finset Bool) (by simp)]; simp
-- `Set.powersetCard.coe_compl` idx 5
theorem c3_101 : ¬ indep0% Set.powersetCard.coe_compl 5 := fun h => by
  have := h (α := Unit) (n := 0) (m := 0) (s := ⟨∅, by simp⟩)
  simp at this
-- `Set.powersetCard.mem_compl` idx 5
theorem c3_102 : ¬ indep0% Set.powersetCard.mem_compl 5 := fun h => by
  have := h (α := Unit) (n := 0) (m := 0) (s := ⟨∅, by simp⟩) (a := ())
  simp at this
-- `Set.powersetCard.disjoint_iff_eq_compl` idx 5
theorem c3_103 : ¬ indep0% Set.powersetCard.disjoint_iff_eq_compl 5 := fun h => by
  have := h (α := Unit) (n := 0) (m := 0) (s := ⟨∅, by simp⟩) (t := ⟨∅, by simp⟩)
  simp at this
-- `Set.powersetCard.coe_disjUnion` idx 5
theorem c3_104 : ¬ indep0% Set.powersetCard.coe_disjUnion 5 := fun h => by
  have := h (α := Unit) (n := 1) (m := 1) (s := ⟨{()}, by simp⟩) (t := ⟨{()}, by simp⟩)
  simp at this
-- `Set.powersetCard.mem_disjUnion` idx 5
theorem c3_105 : ¬ indep0% Set.powersetCard.mem_disjUnion 5 := fun h => by
  have := h (α := Unit) (n := 1) (m := 1) (s := ⟨{()}, by simp⟩) (t := ⟨{()}, by simp⟩) (a := ())
  simp at this
-- `Set.powersetCard.instFiniteElemFinset` idx 2
theorem c3_106 : ¬ drop0% Set.powersetCard.instFiniteElemFinset 2 := fun h =>
  @not_finite (Set.powersetCard ℕ 1) inferInstance (h ℕ 1)
-- `Set.powersetCard.instInfinite` idx 2
theorem c3_107 : ¬ drop0% Set.powersetCard.instInfinite 2 := fun h =>
  @not_finite (Set.powersetCard ℕ 0) (h ℕ 0) inferInstance
-- `Set.powersetCard.instInfinite` idx 3
theorem c3_108 : ¬ drop0% Set.powersetCard.instInfinite 3 := fun h =>
  @not_finite (Set.powersetCard Bool 1) (h Bool 1) inferInstance
-- `Set.powersetCard.nontrivial` idx 2
theorem c3_109 : ¬ drop0% Set.powersetCard.nontrivial 2 := fun h =>
  @not_nontrivial (Set.powersetCard Bool 0) _ (h (α := Bool) (n := 0) (by simp))
-- `Set.powersetCard.nontrivial` idx 3
theorem c3_110 : ¬ drop0% Set.powersetCard.nontrivial 3 := fun h =>
  @not_nontrivial (Set.powersetCard Bool 2) _ (h (α := Bool) (n := 2) (by decide))
-- `Set.powersetCard.nontrivial'` idx 2
theorem c3_111 : ¬ drop0% Set.powersetCard.nontrivial' 2 := fun h =>
  @not_nontrivial (Set.powersetCard Bool 0) _ (h (α := Bool) (n := 0) (by simp))
-- `Set.powersetCard.nontrivial'` idx 3
theorem c3_112 : ¬ drop0% Set.powersetCard.nontrivial' 3 := fun h =>
  @not_nontrivial (Set.powersetCard Bool 2) _ (h (α := Bool) (n := 2) (by decide))
-- `Set.powersetCard.eq_empty_iff` idx 2
theorem c3_113 : ¬ drop0% Set.powersetCard.eq_empty_iff 2 := fun h => by
  have := (h (α := ℕ) (n := 1)).2 (by simp)
  have h2 : ({0} : Finset ℕ) ∈ Set.powersetCard ℕ 1 := by simp
  rw [this] at h2; exact h2
-- `Set.powersetCard.nontrivial_iff` idx 2
theorem c3_114 : ¬ drop0% Set.powersetCard.nontrivial_iff 2 := fun h => by
  have := ((h (α := ℕ) (n := 1)).1 inferInstance).2
  simp at this

-- `Set.range_extend` idx 4
theorem c3_115 : ¬ drop1% Set.range_extend 4 := fun h => by
  have := h (ι := Bool) (f := fun _ => ULift.up.{1} ()) (fun b => ULift.up.{1} b) (fun _ => ULift.up.{1} true)
  obtain ⟨x, hx⟩ := (Set.ext_iff.1 this (ULift.up true)).2 (Or.inl ⟨true, rfl⟩)
  obtain ⟨y, hy⟩ := (Set.ext_iff.1 this (ULift.up false)).2 (Or.inl ⟨false, rfl⟩)
  have hxy : x = y := Subsingleton.elim _ _
  subst hxy
  exact absurd (congrArg ULift.down (hx.symm.trans hy)) (by decide)
-- `Function.FactorsThrough.extend_injOn` idx 6: removable (an injective g already forces
-- extend f g j to be injective on range f)
theorem c3_116 : drop% Function.FactorsThrough.extend_injOn 6 := by
  intro α β γ f g j hg
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
  classical
  have hx : ∃ a, f a = f x := ⟨x, rfl⟩
  have hy : ∃ a, f a = f y := ⟨y, rfl⟩
  rw [Function.extend_def, dif_pos hx, Function.extend_def, dif_pos hy] at heq
  rw [← Classical.choose_spec hx, ← Classical.choose_spec hy, hg heq]
-- `Function.FactorsThrough.extend_injOn` idx 7
theorem c3_185 : ¬ drop0% Function.FactorsThrough.extend_injOn 7 := fun h => by
  have := h (f := fun b : Bool => b) (g := fun _ => ()) (j := fun _ => ()) (fun _ _ _ => rfl)
    (Set.mem_range_self true) (Set.mem_range_self false) rfl
  exact absurd this (by decide)
-- `Function.Injective.extend_injOn` idx 6: removable (an injective g already forces
-- extend f g j to be injective on range f)
theorem c3_117 : drop% Function.Injective.extend_injOn 6 := by
  intro α β γ f g j hg
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
  classical
  have hx : ∃ a, f a = f x := ⟨x, rfl⟩
  have hy : ∃ a, f a = f y := ⟨y, rfl⟩
  rw [Function.extend_def, dif_pos hx, Function.extend_def, dif_pos hy] at heq
  rw [← Classical.choose_spec hx, ← Classical.choose_spec hy, hg heq]
-- `Function.Injective.extend_injOn` idx 7
theorem c3_118 : ¬ drop0% Function.Injective.extend_injOn 7 := fun h => by
  have := h (f := fun b : Bool => b) (g := fun _ => ()) (j := fun _ => ()) (fun _ _ h => h)
    (Set.mem_range_self true) (Set.mem_range_self false) rfl
  exact absurd this (by decide)
-- `Function.Injective.extend_of_disjoint` idx 6: removable (g injective and the disjoint
-- ranges already make extend f g j injective)
theorem c3_119 : drop% Function.Injective.extend_of_disjoint 6 := by
  intro α β γ f g j hg hj hd x y h
  classical
  rw [Function.extend_def, Function.extend_def] at h
  split_ifs at h with hx hy hy
  · rw [← Classical.choose_spec hx, ← Classical.choose_spec hy, hg h]
  · exact (Set.disjoint_left.1 hd (Set.mem_range_self _) ⟨y, h.symm⟩).elim
  · exact (Set.disjoint_left.1 hd (Set.mem_range_self _) ⟨x, h⟩).elim
  · exact hj h
-- `Function.Injective.extend_of_disjoint` idx 7
theorem c3_120 : ¬ drop0% Function.Injective.extend_of_disjoint 7 := fun h => by
  have := h (f := fun b : Bool => b) (g := fun _ => (0 : ℕ)) (j := fun b => if b then 1 else 2)
    (fun _ _ h => h) (fun a b hab => by cases a <;> cases b <;> simp_all)
    (Set.disjoint_left.2 fun x ⟨_, hx⟩ ⟨b, hb⟩ => by subst hx; cases b <;> simp at hb)
    (a₁ := true) (a₂ := false) (by simp)
  exact absurd this (by decide)
-- `Function.Injective.extend_of_disjoint` idx 8
theorem c3_121 : ¬ drop0% Function.Injective.extend_of_disjoint 8 := fun h => by
  have := h (f := fun e : Empty => (e.elim : Bool)) (g := fun e : Empty => (e.elim : ℕ)) (j := fun _ => 0)
    (fun a => a.elim) (fun a => a.elim) (Set.disjoint_left.2 fun _ ⟨e, _⟩ => e.elim)
    (a₁ := true) (a₂ := false) (by simp)
  exact absurd this (by decide)
-- `Function.Injective.extend_of_disjoint` idx 9
theorem c3_122 : ¬ drop0% Function.Injective.extend_of_disjoint 9 := fun h => by
  have hinj : Function.Injective (fun _ : Unit => true) := fun _ _ _ => rfl
  have he : Function.extend (fun _ : Unit => true) (fun _ => (0 : ℕ)) (fun b : Bool => if b then 1 else 0) true = 0 :=
    hinj.extend_apply _ _ ()
  have := h (f := fun _ : Unit => true) (g := fun _ => (0 : ℕ)) (j := fun b => if b then 1 else 0)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun a b hab => by cases a <;> cases b <;> simp_all)
    (a₁ := true) (a₂ := false) (by rw [he]; simp)
  exact absurd this (by decide)
-- `Set.restrictPreimage_injective` idx 4
theorem c3_123 : ¬ drop0% Set.restrictPreimage_injective 4 := fun h => by
  have hi := h (t := (univ : Set Unit)) (f := fun _ : Bool => ())
  have := @hi ⟨true, trivial⟩ ⟨false, trivial⟩ rfl
  exact absurd (congrArg Subtype.val this) (by decide)
-- `Set.restrictPreimage_surjective` idx 4
theorem c3_124 : ¬ drop0% Set.restrictPreimage_surjective 4 := fun h => by
  obtain ⟨x, _⟩ := h (t := (univ : Set Unit)) (f := fun e : Empty => (e.elim : Unit)) ⟨(), trivial⟩
  exact x.1.elim
-- `Set.restrictPreimage_bijective` idx 4
theorem c3_125 : ¬ drop0% Set.restrictPreimage_bijective 4 := fun h => by
  obtain ⟨x, _⟩ := (h (t := (univ : Set Unit)) (f := fun e : Empty => (e.elim : Unit))).2 ⟨(), trivial⟩
  exact x.1.elim
-- `Function.Injective.restrictPreimage` idx 4
theorem c3_126 : ¬ drop0% Function.Injective.restrictPreimage 4 := fun h => by
  have hi := h (t := (univ : Set Unit)) (f := fun _ : Bool => ())
  have := @hi ⟨true, trivial⟩ ⟨false, trivial⟩ rfl
  exact absurd (congrArg Subtype.val this) (by decide)
-- `Function.Surjective.restrictPreimage` idx 4
theorem c3_127 : ¬ drop0% Function.Surjective.restrictPreimage 4 := fun h => by
  obtain ⟨x, _⟩ := h (t := (univ : Set Unit)) (f := fun e : Empty => (e.elim : Unit)) ⟨(), trivial⟩
  exact x.1.elim
-- `Function.Bijective.restrictPreimage` idx 4
theorem c3_128 : ¬ drop0% Function.Bijective.restrictPreimage 4 := fun h => by
  obtain ⟨x, _⟩ := (h (t := (univ : Set Unit)) (f := fun e : Empty => (e.elim : Unit))).2 ⟨(), trivial⟩
  exact x.1.elim
-- `Set.preimage_image_sigmaMk_of_ne` idx 4
theorem c3_129 : ¬ drop0% Set.preimage_image_sigmaMk_of_ne 4 := fun h => by
  have := h (i := ()) (j := ()) (α := fun _ => Unit) univ
  have h2 : () ∈ Sigma.mk () ⁻¹' (Sigma.mk (β := fun _ : Unit => Unit) () '' univ) := ⟨(), trivial, rfl⟩
  rw [this] at h2; exact h2
-- `Set.image_sigmaMk_preimage_sigmaMap` idx 5
theorem c3_130 : ¬ drop0% Set.image_sigmaMk_preimage_sigmaMap 5 := fun h => by
  have := h (α := fun _ : Bool => Unit) (β := fun _ : Unit => Unit) (f := fun _ => ()) (fun _ x => x) true univ
  have h2 := (Set.ext_iff.1 this ⟨false, ()⟩).2 ⟨(), trivial, rfl⟩
  obtain ⟨x, _, hx⟩ := h2
  simp at hx
-- `Set.mk_mem_sigma` idx 6
theorem c3_131 : ¬ drop0% Set.mk_mem_sigma 6 := fun h => by
  have := h (s := (∅ : Set Unit)) (t := fun _ => (univ : Set Unit)) (i := ()) (a := ()) trivial
  exact this.1
-- `Set.mk_mem_sigma` idx 7
theorem c3_132 : ¬ drop0% Set.mk_mem_sigma 7 := fun h => by
  have := h (s := (univ : Set Unit)) (t := fun _ => (∅ : Set Unit)) (i := ()) (a := ()) trivial
  exact this.2
-- `Set.sigma_mono` idx 6
theorem c3_133 : ¬ drop0% Set.sigma_mono 6 := fun h => by
  have := h (s₁ := (univ : Set Unit)) (s₂ := ∅) (t₁ := fun _ => (univ : Set Unit)) (t₂ := fun _ => univ)
    (fun _ => subset_rfl) (show (⟨(), ()⟩ : Σ _ : Unit, Unit) ∈ (univ : Set Unit).sigma fun _ => univ from ⟨trivial, trivial⟩)
  exact this.1
-- `Set.sigma_mono` idx 7
theorem c3_134 : ¬ drop0% Set.sigma_mono 7 := fun h => by
  have := h (s₁ := (univ : Set Unit)) (s₂ := univ) (t₁ := fun _ => (univ : Set Unit)) (t₂ := fun _ => ∅)
    subset_rfl (show (⟨(), ()⟩ : Σ _ : Unit, Unit) ∈ (univ : Set Unit).sigma fun _ => univ from ⟨trivial, trivial⟩)
  exact this.2
-- `Set.mk_preimage_sigma` idx 5
theorem c3_135 : ¬ drop0% Set.mk_preimage_sigma 5 := fun h => by
  have := h (s := (∅ : Set Unit)) (t := fun _ => (univ : Set Unit)) (i := ())
  have h2 : () ∈ (fun _ : Unit => (univ : Set Unit)) () := trivial
  rw [← this] at h2; exact h2.1
-- `Set.mk_preimage_sigma_eq_empty` idx 5
theorem c3_136 : ¬ drop0% Set.mk_preimage_sigma_eq_empty 5 := fun h => by
  have := h (s := (univ : Set Unit)) (t := fun _ => (univ : Set Unit)) (i := ())
  have h2 : () ∈ Sigma.mk () ⁻¹' ((univ : Set Unit).sigma fun _ => (univ : Set Unit)) := ⟨trivial, trivial⟩
  rw [this] at h2; exact h2
-- `Set.Nonempty.sigma` idx 4
theorem c3_137 : ¬ drop0% Set.Nonempty.sigma 4 := fun h => by
  obtain ⟨x, hx, _⟩ := h (s := (∅ : Set Unit)) (t := fun _ => (univ : Set Unit)) (fun _ => ⟨(), trivial⟩)
  exact hx
-- `Set.Nonempty.sigma` idx 5
theorem c3_138 : ¬ drop0% Set.Nonempty.sigma 5 := fun h => by
  obtain ⟨x, _, hx⟩ := h (s := (univ : Set Unit)) (t := fun _ => (∅ : Set Unit)) ⟨(), trivial⟩
  exact hx
-- `Set.Nonempty.sigma_fst` idx 4
theorem c3_139 : ¬ drop0% Set.Nonempty.sigma_fst 4 := fun h => by
  obtain ⟨x, hx⟩ := h (s := (∅ : Set Unit)) (α := fun _ => Unit) (t := fun _ => univ)
  exact hx
-- `Set.Nonempty.sigma_snd` idx 4
theorem c3_140 : ¬ drop0% Set.Nonempty.sigma_snd 4 := fun h => by
  obtain ⟨x, hx, _⟩ := h (s := (∅ : Set Unit)) (α := fun _ => Unit) (t := fun _ => univ)
  exact hx
-- `Set.image_sigmaMk_subset_sigma_left` idx 5
theorem c3_141 : ¬ drop0% Set.image_sigmaMk_subset_sigma_left 5 := fun h => by
  have := h (s := (univ : Set Unit)) (t := fun _ => (∅ : Set Unit)) (a := fun _ => ())
    (show (⟨(), ()⟩ : Σ _ : Unit, Unit) ∈ (fun i => (⟨i, ()⟩ : Σ _ : Unit, Unit)) '' univ from ⟨(), trivial, rfl⟩)
  exact this.2
-- `Set.image_sigmaMk_subset_sigma_right` idx 5
theorem c3_142 : ¬ drop0% Set.image_sigmaMk_subset_sigma_right 5 := fun h => by
  have := h (s := (∅ : Set Unit)) (t := fun _ => (univ : Set Unit)) (i := ())
    (show (⟨(), ()⟩ : Σ _ : Unit, Unit) ∈ Sigma.mk () '' (univ : Set Unit) from ⟨(), trivial, rfl⟩)
  exact this.1
-- `Set.fst_image_sigma` idx 4
theorem c3_143 : ¬ drop0% Set.fst_image_sigma 4 := fun h => by
  have := h (α := fun _ : Unit => Unit) (t := fun _ => ∅) univ
  have h2 : () ∈ (univ : Set Unit) := trivial
  rw [← this] at h2
  obtain ⟨x, hx, _⟩ := h2
  exact hx.2
-- `Set.eq_of_preimage_val_eq_of_subset` idx 4
theorem c3_144 : ¬ drop0% Set.eq_of_preimage_val_eq_of_subset 4 := fun h => by
  have := h (A := (∅ : Set ℕ)) (B := univ) (C := ∅) subset_rfl (Set.ext fun x => x.2.elim)
  exact Set.empty_ne_univ this.symm
-- `Set.image_val_iInter` idx 4
theorem c3_145 : ¬ drop0% Set.image_val_iInter 4 := fun h => by
  have := h (ι := False) (A := (∅ : Set ℕ)) (t := fun x => x.elim)
  simp at this
  exact Set.empty_ne_univ this
-- `Set.Subsingleton.eq_empty_or_singleton` idx 2
theorem c3_146 : ¬ drop0% Set.Subsingleton.eq_empty_or_singleton 2 := fun h => by
  rcases h (s := (univ : Set Bool)) with h1 | ⟨x, hx⟩
  · exact Set.empty_ne_univ h1.symm
  · have h2 : (!x) ∈ (univ : Set Bool) := trivial
    rw [hx] at h2; cases x <;> simp at h2
-- `Set.Subsingleton.induction_on` idx 4
theorem c3_147 : ¬ drop0% Set.Subsingleton.induction_on 4 := fun h => by
  obtain ⟨x, hx⟩ := h (s := (∅ : Set ℕ)) (p := fun s => s.Nonempty) Set.subsingleton_empty
    (fun x => Set.singleton_nonempty x)
  exact hx
-- `Set.Subsingleton.induction_on` idx 5
theorem c3_148 : ¬ drop0% Set.Subsingleton.induction_on 5 := fun h => by
  have := h (s := ({0} : Set ℕ)) (p := fun s => s = ∅) (Set.subsingleton_singleton) rfl
  simp at this
-- `Set.eq_empty_or_singleton_of_subsingleton` idx 1
theorem c3_149 : ¬ drop0% Set.eq_empty_or_singleton_of_subsingleton 1 := fun h => by
  rcases h (univ : Set Bool) with h1 | ⟨x, hx⟩
  · exact Set.empty_ne_univ h1.symm
  · have h2 : (!x) ∈ (univ : Set Bool) := trivial
    rw [hx] at h2; cases x <;> simp at h2
-- `Set.Subsingleton.denselyOrdered` idx 3
theorem c3_150 : ¬ drop0% Set.Subsingleton.denselyOrdered 3 := fun h => by
  have hd := h (s := (univ : Set Bool))
  obtain ⟨⟨c, _⟩, h1, h2⟩ := hd.dense (⟨false, Set.mem_univ _⟩ : (univ : Set Bool)) ⟨true, Set.mem_univ _⟩
    (show false < true by decide)
  have h1' : false < c := h1
  have h2' : c < true := h2
  cases c <;> simp at h1' h2'
-- `Set.nontrivial_univ` idx 1
theorem c3_151 : ¬ drop0% Set.nontrivial_univ 1 := fun h => by
  obtain ⟨x, _, y, _, hxy⟩ := h (α := Unit)
  exact hxy (Subsingleton.elim _ _)
-- `Set.nontrivial_of_univ_nontrivial` idx 1
theorem c3_152 : ¬ drop0% Set.nontrivial_of_univ_nontrivial 1 := fun h =>
  not_nontrivial Unit (h (α := Unit))
-- `Set.singleton_ne_univ` idx 1
theorem c3_153 : ¬ drop0% Set.singleton_ne_univ 1 := fun h =>
  h (α := Unit) () (Set.ext fun x => by simp)
-- `Set.singleton_ssubset_univ` idx 1
theorem c3_154 : ¬ drop0% Set.singleton_ssubset_univ 1 := fun h =>
  (h (α := Unit) ()).2 (fun x _ => by simp)
-- `Set.nontrivial_of_nontrivial` idx 2
theorem c3_155 : ¬ drop0% Set.nontrivial_of_nontrivial 2 := fun h =>
  not_nontrivial Unit (h (α := Unit) (s := univ))
-- `Set.nontrivial_of_nontrivial_coe` idx 2
theorem c3_156 : ¬ drop0% Set.nontrivial_of_nontrivial_coe 2 := fun h =>
  not_nontrivial Unit (h (α := Unit) (s := univ))
-- `Set.nontrivial_mono` idx 3
theorem c3_157 : ¬ drop0% Set.nontrivial_mono 3 := fun h => by
  have := h (s := (univ : Set Bool)) (t := {true}) (Set.nontrivial_coe_sort.2 ⟨true, trivial, false, trivial, by decide⟩)
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hne⟩ := this
  simp at hx hy; subst hx; subst hy; exact hne rfl
-- `Set.Subsingleton.not_nontrivial` idx 2
theorem c3_158 : ¬ drop0% Set.Subsingleton.not_nontrivial 2 := fun h =>
  h (s := (univ : Set Bool)) ⟨true, trivial, false, trivial, by decide⟩

-- `Function.Injective.preimage_pullbackDiagonal` idx 5
theorem c3_60 : ¬ drop0% Function.Injective.preimage_pullbackDiagonal 5 := fun h => by
  have := h (Y := True) (f := fun _ : Unit => True.intro) (g := fun _ : Bool => ())
  have h2 := (Set.ext_iff.1 this ⟨(true, false), rfl⟩).1 rfl
  have h3 : true = false := h2
  exact absurd h3 (by decide)

namespace W4c3
/-- In Multiplicative Int, ofAdd z • ofAdd (-z) = 1. -/
theorem mp (z : ℤ) : Multiplicative.ofAdd z • Multiplicative.ofAdd (-z) = 1 := by
  show Multiplicative.ofAdd z * Multiplicative.ofAdd (-z) = 1
  rw [← ofAdd_add, add_neg_cancel, ofAdd_zero]
theorem mp' (z : ℤ) : Multiplicative.ofAdd (-z) • Multiplicative.ofAdd z = 1 := by
  show Multiplicative.ofAdd (-z) * Multiplicative.ofAdd z = 1
  rw [← ofAdd_add, neg_add_cancel, ofAdd_zero]
/-- The natural numbers inside Int and inside Multiplicative Int are partially well-ordered. -/
theorem natZ_pwo : ((fun n : ℕ => (n : ℤ)) '' Set.univ).IsPWO :=
  (Set.IsPWO.of_linearOrder (Set.univ : Set ℕ)).image_of_monotone Nat.mono_cast
theorem natM_pwo : ((fun n : ℕ => Multiplicative.ofAdd (n : ℤ)) '' Set.univ).IsPWO :=
  (Set.IsPWO.of_linearOrder (Set.univ : Set ℕ)).image_of_monotone
    fun _ _ hab => Multiplicative.ofAdd_le.2 (Nat.cast_le.2 hab)
end W4c3
open W4c3

-- `Set.VAddAntidiagonal.fst_eq_fst_iff_snd_eq_snd` idx 8
theorem c3_159 : ¬ drop0% Set.VAddAntidiagonal.fst_eq_fst_iff_snd_eq_snd 8 := fun h => by
  have := (h (G := ℕ∞) (P := ℕ∞) (s := univ) (t := univ) (a := ⊤) (x := ⟨(⊤, 0), trivial, trivial, top_add _⟩)
    (y := ⟨(⊤, 1), trivial, trivial, top_add _⟩)).1 rfl
  exact zero_ne_one this
-- `Set.SMulAntidiagonal.fst_eq_fst_iff_snd_eq_snd` idx 8
theorem c3_160 : ¬ drop0% Set.SMulAntidiagonal.fst_eq_fst_iff_snd_eq_snd 8 := fun h => by
  have := (h (G := ℕ) (P := ℕ) (s := univ) (t := univ) (a := 0) (x := ⟨(0, 0), trivial, trivial, by simp⟩)
    (y := ⟨(0, 1), trivial, trivial, by simp⟩)).1 rfl
  exact absurd this (by decide)
-- `Set.VAddAntidiagonal.eq_of_fst_eq_fst` idx 8
theorem c3_161 : ¬ drop0% Set.VAddAntidiagonal.eq_of_fst_eq_fst 8 := fun h => by
  have := h (G := ℕ∞) (P := ℕ∞) (s := univ) (t := univ) (a := ⊤) (x := ⟨(⊤, 0), trivial, trivial, top_add _⟩)
    (y := ⟨(⊤, 1), trivial, trivial, top_add _⟩) rfl
  exact zero_ne_one (congrArg (fun z => z.1.2) this)
-- `Set.VAddAntidiagonal.eq_of_fst_eq_fst` idx 9
theorem c3_162 : ¬ drop0% Set.VAddAntidiagonal.eq_of_fst_eq_fst 9 := fun h => by
  have := h (G := ℤ) (P := ℤ) (s := univ) (t := univ) (a := 0) (x := ⟨(1, -1), trivial, trivial, by decide⟩)
    (y := ⟨(0, 0), trivial, trivial, by decide⟩)
  exact absurd (congrArg (fun z => z.1.1) this) (by decide)
-- `Set.SMulAntidiagonal.eq_of_fst_eq_fst` idx 8
theorem c3_163 : ¬ drop0% Set.SMulAntidiagonal.eq_of_fst_eq_fst 8 := fun h => by
  have := h (G := ℕ) (P := ℕ) (s := univ) (t := univ) (a := 0) (x := ⟨(0, 0), trivial, trivial, by simp⟩)
    (y := ⟨(0, 1), trivial, trivial, by simp⟩) rfl
  exact absurd (congrArg (fun z => z.1.2) this) (by decide)
-- `Set.SMulAntidiagonal.eq_of_fst_eq_fst` idx 9
theorem c3_164 : ¬ drop0% Set.SMulAntidiagonal.eq_of_fst_eq_fst 9 := fun h => by
  have := h (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := univ) (t := univ) (a := 1)
    (x := ⟨(Multiplicative.ofAdd 1, Multiplicative.ofAdd (-1)), trivial, trivial, mp 1⟩)
    (y := ⟨(Multiplicative.ofAdd 0, Multiplicative.ofAdd (-0)), trivial, trivial, mp 0⟩)
  exact absurd (congrArg (fun z => Multiplicative.toAdd z.1.1) this) (by decide)
-- `Set.VAddAntidiagonal.finite_of_finite` idx 4
theorem c3_165 : ¬ drop0% Set.VAddAntidiagonal.finite_of_finite 4 := fun h => by
  have hf := h (G := ℕ∞) (P := ℕ∞) (s := {⊤}) (Set.finite_singleton _) univ ⊤
  revert hf
  exact Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((⊤ : ℕ∞), (n : ℕ∞)))
    (fun a b hab => Nat.cast_injective (congrArg Prod.snd hab)) (fun n => ⟨rfl, trivial, top_add _⟩)

-- `Set.VAddAntidiagonal.finite_of_finite` idx 5
theorem c3_166 : ¬ drop0% Set.VAddAntidiagonal.finite_of_finite 5 := fun h => by
  have hf := h (G := ℤ) (P := ℤ) (s := univ) univ 0
  revert hf
  exact Set.infinite_of_injective_forall_mem (f := fun n : ℤ => (n, -n))
    (fun a b hab => congrArg Prod.fst hab) (fun n => ⟨trivial, trivial, add_neg_cancel n⟩)

-- `Set.SMulAntidiagonal.finite_of_finite_fst` idx 4
theorem c3_167 : ¬ drop0% Set.SMulAntidiagonal.finite_of_finite_fst 4 := fun h => by
  have hf := h (G := ℕ) (P := ℕ) (s := {0}) (Set.finite_singleton _) univ 0
  revert hf
  exact Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (0, n))
    (fun a b hab => congrArg Prod.snd hab) (fun n => ⟨rfl, trivial, by simp⟩)

-- `Set.SMulAntidiagonal.finite_of_finite_fst` idx 5
theorem c3_168 : ¬ drop0% Set.SMulAntidiagonal.finite_of_finite_fst 5 := fun h => by
  have hf := h (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := univ) univ 1
  revert hf
  exact Set.infinite_of_injective_forall_mem (f := fun n : ℤ => (Multiplicative.ofAdd n, Multiplicative.ofAdd (-n)))
    (fun a b hab => Multiplicative.ofAdd.injective (congrArg Prod.fst hab)) (fun n => ⟨trivial, trivial, mp n⟩)

-- `Set.VAddAntidiagonal.eq_of_snd_eq_snd` idx 8
theorem c3_169 : ¬ drop0% Set.VAddAntidiagonal.eq_of_snd_eq_snd 8 := fun h => by
  have := h (G := ℕ∞) (P := ℕ∞) (s := univ) (t := univ) (a := ⊤) (x := ⟨(0, ⊤), trivial, trivial, add_top _⟩)
    (y := ⟨(1, ⊤), trivial, trivial, add_top _⟩) rfl
  exact zero_ne_one (congrArg (fun z => z.1.1) this)
-- `Set.VAddAntidiagonal.eq_of_snd_eq_snd` idx 9
theorem c3_170 : ¬ drop0% Set.VAddAntidiagonal.eq_of_snd_eq_snd 9 := fun h => by
  have := h (G := ℤ) (P := ℤ) (s := univ) (t := univ) (a := 0) (x := ⟨(1, -1), trivial, trivial, by decide⟩)
    (y := ⟨(0, 0), trivial, trivial, by decide⟩)
  exact absurd (congrArg (fun z => z.1.1) this) (by decide)
-- `Set.SMulAntidiagonal.eq_of_snd_eq_snd` idx 8
theorem c3_171 : ¬ drop0% Set.SMulAntidiagonal.eq_of_snd_eq_snd 8 := fun h => by
  have := h (G := ℕ) (P := ℕ) (s := univ) (t := univ) (a := 0) (x := ⟨(0, 0), trivial, trivial, by simp⟩)
    (y := ⟨(1, 0), trivial, trivial, by simp⟩) rfl
  exact absurd (congrArg (fun z => z.1.1) this) (by decide)
-- `Set.SMulAntidiagonal.eq_of_snd_eq_snd` idx 9
theorem c3_172 : ¬ drop0% Set.SMulAntidiagonal.eq_of_snd_eq_snd 9 := fun h => by
  have := h (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := univ) (t := univ) (a := 1)
    (x := ⟨(Multiplicative.ofAdd 1, Multiplicative.ofAdd (-1)), trivial, trivial, mp 1⟩)
    (y := ⟨(Multiplicative.ofAdd 0, Multiplicative.ofAdd (-0)), trivial, trivial, mp 0⟩)
  exact absurd (congrArg (fun z => Multiplicative.toAdd z.1.1) this) (by decide)
-- `Set.VAddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd` idx 8
theorem c3_173 : ¬ drop0% Set.VAddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd 8 := fun h => by
  have := h (G := ℕ∞) (P := ℕ∞) (s := univ) (t := univ) (a := ⊤) (x := ⟨(⊤, 0), trivial, trivial, top_add _⟩)
    (y := ⟨(⊤, 1), trivial, trivial, top_add _⟩) le_rfl zero_le_one
  exact zero_ne_one (congrArg (fun z => z.1.2) this)
-- `Set.VAddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd` idx 11
theorem c3_174 : ¬ drop0% Set.VAddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd 11 := fun h => by
  have := h (G := ℤ) (P := ℤ) (s := univ) (t := univ) (a := 0) (x := ⟨(1, -1), trivial, trivial, by decide⟩)
    (y := ⟨(0, 0), trivial, trivial, by decide⟩) (by decide)
  exact absurd (congrArg (fun z => z.1.1) this) (by decide)
-- `Set.VAddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd` idx 12
theorem c3_175 : ¬ drop0% Set.VAddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd 12 := fun h => by
  have := h (G := ℤ) (P := ℤ) (s := univ) (t := univ) (a := 0) (x := ⟨(-1, 1), trivial, trivial, by decide⟩)
    (y := ⟨(0, 0), trivial, trivial, by decide⟩) (by decide)
  exact absurd (congrArg (fun z => z.1.1) this) (by decide)
-- `Set.SMulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd` idx 8
theorem c3_176 : ¬ drop0% Set.SMulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd 8 := fun h => by
  have := h (G := ℕ) (P := ℕ) (s := univ) (t := univ) (a := 0) (x := ⟨(0, 0), trivial, trivial, by simp⟩)
    (y := ⟨(0, 1), trivial, trivial, by simp⟩) le_rfl zero_le_one
  exact absurd (congrArg (fun z => z.1.2) this) (by decide)
-- `Set.SMulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd` idx 11
theorem c3_177 : ¬ drop0% Set.SMulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd 11 := fun h => by
  have := h (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := univ) (t := univ) (a := 1)
    (x := ⟨(Multiplicative.ofAdd 1, Multiplicative.ofAdd (-1)), trivial, trivial, mp 1⟩)
    (y := ⟨(Multiplicative.ofAdd 0, Multiplicative.ofAdd (-0)), trivial, trivial, mp 0⟩)
    (Multiplicative.ofAdd_le.2 (by decide))
  exact absurd (congrArg (fun z => Multiplicative.toAdd z.1.1) this) (by decide)
-- `Set.SMulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd` idx 12
theorem c3_178 : ¬ drop0% Set.SMulAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd 12 := fun h => by
  have := h (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := univ) (t := univ) (a := 1)
    (x := ⟨(Multiplicative.ofAdd (-1), Multiplicative.ofAdd (- -1)), trivial, trivial, mp (-1)⟩)
    (y := ⟨(Multiplicative.ofAdd 0, Multiplicative.ofAdd (-0)), trivial, trivial, mp 0⟩)
    (Multiplicative.ofAdd_le.2 (by decide))
  exact absurd (congrArg (fun z => Multiplicative.toAdd z.1.1) this) (by decide)
-- `Set.VAddAntidiagonal.finite_of_isPWO` idx 7
theorem c3_179 : ¬ drop0% Set.VAddAntidiagonal.finite_of_isPWO 7 := fun h => by
  have hf := h (G := ℕ∞) (P := ℕ∞) (s := {⊤}) (t := univ) (Set.isPWO_singleton _) (Set.IsPWO.of_linearOrder _) ⊤
  revert hf
  exact Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((⊤ : ℕ∞), (n : ℕ∞)))
    (fun a b hab => Nat.cast_injective (congrArg Prod.snd hab)) (fun n => ⟨rfl, trivial, top_add _⟩)

-- `Set.VAddAntidiagonal.finite_of_isPWO` idx 8
theorem c3_180 : ¬ drop0% Set.VAddAntidiagonal.finite_of_isPWO 8 := fun h => by
  have hf := h (G := ℤ) (P := ℤ) (s := univ) (t := (fun n : ℕ => (n : ℤ)) '' univ) natZ_pwo 0
  revert hf
  exact Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (-(n : ℤ), (n : ℤ)))
    (fun a b hab => Nat.cast_injective (congrArg Prod.snd hab))
    (fun n => ⟨trivial, ⟨n, trivial, rfl⟩, neg_add_cancel (n : ℤ)⟩)

-- `Set.VAddAntidiagonal.finite_of_isPWO` idx 9
theorem c3_181 : ¬ drop0% Set.VAddAntidiagonal.finite_of_isPWO 9 := fun h => by
  have hf := h (G := ℤ) (P := ℤ) (t := univ) (s := (fun n : ℕ => (n : ℤ)) '' univ) natZ_pwo 0
  revert hf
  exact Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : ℤ), -(n : ℤ)))
    (fun a b hab => Nat.cast_injective (congrArg Prod.fst hab))
    (fun n => ⟨⟨n, trivial, rfl⟩, trivial, add_neg_cancel (n : ℤ)⟩)

-- `Set.SMulAntidiagonal.finite_of_isPWO` idx 7
theorem c3_182 : ¬ drop0% Set.SMulAntidiagonal.finite_of_isPWO 7 := fun h => by
  have hf := h (G := ℕ) (P := ℕ) (s := {0}) (t := univ) (Set.isPWO_singleton _) (Set.IsPWO.of_linearOrder _) 0
  revert hf
  exact Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (0, n))
    (fun a b hab => congrArg Prod.snd hab) (fun n => ⟨rfl, trivial, by simp⟩)

-- `Set.SMulAntidiagonal.finite_of_isPWO` idx 8
theorem c3_183 : ¬ drop0% Set.SMulAntidiagonal.finite_of_isPWO 8 := fun h => by
  have hf := h (G := Multiplicative ℤ) (P := Multiplicative ℤ) (s := univ)
      (t := (fun n : ℕ => Multiplicative.ofAdd (n : ℤ)) '' univ) natM_pwo 1
  revert hf
  exact Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => (Multiplicative.ofAdd (-(n : ℤ)), Multiplicative.ofAdd (n : ℤ)))
    (fun a b hab => Nat.cast_injective (Multiplicative.ofAdd.injective (congrArg Prod.snd hab)))
    (fun n => ⟨trivial, ⟨n, trivial, rfl⟩, mp' (n : ℤ)⟩)

-- `Set.SMulAntidiagonal.finite_of_isPWO` idx 9
theorem c3_184 : ¬ drop0% Set.SMulAntidiagonal.finite_of_isPWO 9 := fun h => by
  have hf := h (G := Multiplicative ℤ) (P := Multiplicative ℤ) (t := univ)
      (s := (fun n : ℕ => Multiplicative.ofAdd (n : ℤ)) '' univ) natM_pwo 1
  revert hf
  exact Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => (Multiplicative.ofAdd (n : ℤ), Multiplicative.ofAdd (-(n : ℤ))))
    (fun a b hab => Nat.cast_injective (Multiplicative.ofAdd.injective (congrArg Prod.fst hab)))
    (fun n => ⟨⟨n, trivial, rfl⟩, trivial, mp (n : ℤ)⟩)

