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

namespace W4c4
/-- indepL% T i [l₁, …]: indep% T i with the universe parameters of T set to the given numerals. -/
elab "indepL% " T:ident i:num "[" ls:num,* "]" : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := (ls.getElems.toList.map fun l => Level.ofNat l.getNat)
  unless us.length == ci.levelParams.length do throwError "need {ci.levelParams} levels"
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType (xs.getD (j) default)
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push (xs.getD (j) default)
    unless or (decide (dep.size > 1)) (body.containsFVar x.fvarId!) do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

/-- dropL% T i [l₁, …]: drop% T i with the universe parameters of T set to the given numerals. -/
elab "dropL% " T:ident i:num "[" ls:num,* "]" : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := (ls.getElems.toList.map fun l => Level.ofNat l.getNat)
  unless us.length == ci.levelParams.length do throwError "need {ci.levelParams} levels"
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType (xs.getD (j) default)).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Set in
/-- Constant cover of Unit by univ, indexed by Bool. -/
def S1 : Bool → Set Unit := fun _ => univ
/-- Index as value: violates the compatibility condition. -/
def f1 : (i : Bool) → S1 i → Bool := fun i _ => i
theorem hT1 : (Set.univ : Set Unit) ⊆ Set.iUnion S1 := fun _ _ => Set.mem_iUnion.2 ⟨true, trivial⟩
theorem hS1 : Set.iUnion S1 = Set.univ := Set.eq_univ_of_forall fun _ => Set.mem_iUnion.2 ⟨true, trivial⟩
/-- Cover of Bool by univ (Bool-indexed), value depends on the index at false. -/
def f2 : (i : Bool) → ↥(Set.univ : Set Bool) → Bool := fun i x => x.val || i
/-- Cover of Bool by singletons. -/
def Ssg : Bool → Set Bool := fun i => {i}
theorem hSsg : Set.iUnion Ssg = Set.univ := Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, rfl⟩
/-- Negation as an equivalence of Bool. -/
def bnot : Bool ≃ Bool := ⟨not, not, Bool.not_not, Bool.not_not⟩
end W4c4
open W4c4

namespace W4c4
theorem cne : Stream'.const (0:ℕ) ≠ Stream'.const 1 := fun e =>
  absurd (congrArg (fun s => Stream'.get s 0) e) (by decide)
theorem nm {a b : ℕ} (hab : a ≠ b) : a ∉ Stream'.const b := fun ⟨_, e⟩ => hab e
theorem c01 : Stream'.cons (0:ℕ) (Stream'.const 1) ≠ Stream'.const 0 := fun e =>
  absurd (congrArg (fun s => Stream'.get s 1) e) (by decide)
theorem il0 (m : ℕ) : Stream'.get (Stream'.interleave (Stream'.const (0:ℕ)) (Stream'.const 0)) m = 0 := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [Stream'.get_interleave_left]; rfl
  · rw [Stream'.get_interleave_right]; rfl
theorem nm_il : (1:ℕ) ∉ Stream'.interleave (Stream'.const 0) (Stream'.const 0) := fun ⟨n, e⟩ => by
  rw [il0] at e; exact absurd e (by decide)
/-- The subtypes of Bool for True and for (· = true) are different types (different sizes). -/
theorem sub_ne : ¬ ({x : Bool // True} = {x : Bool // x = true}) := fun e => by
  have hs : ∀ u v : {x : Bool // x = true}, u = v := fun u v => Subtype.ext (u.2.trans v.2.symm)
  have := congrArg (cast e.symm) (hs (cast e ⟨false, trivial⟩) (cast e ⟨true, trivial⟩))
  simp at this
/-- Equality on Bool as an explicit setoid. -/
def eqS : Setoid Bool := ⟨(· = ·), ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
end W4c4
open W4c4

namespace W4c4
/-- One-element multisets of ℕ as `Sym ℕ 1`. -/
def sy (a : ℕ) : Sym ℕ 1 := Sym.cons a Sym.nil
theorem sy_ne : sy 0 ≠ sy 1 := fun e => by
  have := congrArg (fun s : Sym ℕ 1 => (s : Multiset ℕ)) e
  simp [sy] at this
theorem nsymm : ¬ Std.Symm (fun a b : ℕ => a < b) := fun hs => absurd (hs.symm 0 1 (by decide)) (by decide)
theorem other00 (h : (0:ℕ) ∈ s((0:ℕ), 0)) : Sym2.Mem.other h = 0 := Sym2.congr_right.1 (Sym2.other_spec h)
/-- The trivial setoid on Unit. -/
def topS : Setoid Unit := ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩
end W4c4
open W4c4

-- `Set.image_sups` idx 6: necessary (f = negation on Bool, s = {false}, t = {true})
theorem w4_0 : ¬ drop0% Set.image_sups 6 := fun h => by
  have := @h (Bool ≃ Bool) Bool Bool _ _ _ bnot {false} {true}
  simp [bnot] at this

-- `Set.image_infs` idx 6: necessary (f = negation on Bool, s = {false}, t = {true})
theorem w4_1 : ¬ drop0% Set.image_infs 6 := fun h => by
  have := @h (Bool ≃ Bool) Bool Bool _ _ _ bnot {false} {true}
  simp [bnot] at this

-- `Set.iUnionLift_mk` idx 5: necessary (S i = univ on Unit, f i _ = i)
theorem w4_2 : ¬ indepL% Set.iUnionLift_mk 5 [0,1,1] := fun h =>
  absurd (@h Unit Bool Bool S1 f1 Set.univ hT1 true ⟨(), trivial⟩ trivial true false () trivial trivial) (by decide)

-- `Set.iUnionLift_mk` idx 7: necessary (S _ = {true} in Bool, T = univ)
theorem w4_3 : ¬ indepL% Set.iUnionLift_mk 7 [0,1,1] := fun h => by
  have := @h Bool Unit Bool (fun _ => {true}) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ () ⟨true, rfl⟩ trivial
  have h2 := this (Set.mem_univ false)
  simp at h2

-- `Set.iUnionLift_mk` idx 10: necessary (T = empty)
theorem w4_4 : ¬ indepL% Set.iUnionLift_mk 10 [0,1,1] := fun h =>
  @h Unit Unit Bool (fun _ => Set.univ) (fun _ _ => true) (fun _ _ _ _ _ => rfl) ∅ (Set.empty_subset _) () ⟨(), trivial⟩

-- `Set.iUnionLift_inclusion` idx 5: necessary (S i = univ on Unit, f i _ = i)
theorem w4_5 : ¬ indepL% Set.iUnionLift_inclusion 5 [0,1,1] := fun h =>
  absurd (@h Unit Bool Bool S1 f1 Set.univ hT1 true ⟨(), trivial⟩ (Set.subset_univ _) true false () trivial trivial)
    (by decide)

-- `Set.iUnionLift_inclusion` idx 7: necessary (S _ = {true} in Bool, T = univ)
theorem w4_6 : ¬ indepL% Set.iUnionLift_inclusion 7 [0,1,1] := fun h => by
  have := @h Bool Unit Bool (fun _ => {true}) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ () ⟨true, rfl⟩
    (Set.subset_univ _)
  have h2 := this (Set.mem_univ false)
  simp at h2

-- `Set.iUnionLift_inclusion` idx 10: necessary (T = empty)
theorem w4_7 : ¬ indepL% Set.iUnionLift_inclusion 10 [0,1,1] := fun h =>
  @h Unit Unit Bool (fun _ => Set.univ) (fun _ _ => true) (fun _ _ _ _ _ => rfl) ∅ (Set.empty_subset _) ()
    ⟨(), trivial⟩ () trivial

-- `Set.iUnionLift_of_mem` idx 5: necessary (S i = univ on Unit, f i _ = i)
theorem w4_8 : ¬ indepL% Set.iUnionLift_of_mem 5 [0,1,1] := fun h =>
  absurd (@h Unit Bool Bool S1 f1 Set.univ hT1 ⟨(), trivial⟩ true trivial true false () trivial trivial) (by decide)

-- `Set.iUnionLift_of_mem` idx 10: necessary (S i = {i} in Bool, x = true, i = false)
theorem w4_9 : ¬ indepL% Set.iUnionLift_of_mem 10 [0,1,1] := fun h => by
  have := @h Bool Bool Bool Ssg (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ (fun x _ => Set.mem_iUnion.2 ⟨x, rfl⟩)
    ⟨true, trivial⟩ false
  simp [Ssg] at this

-- `Set.preimage_iUnionLift` idx 5: necessary (S i = univ on Unit, f i _ = i)
theorem w4_10 : ¬ indepL% Set.preimage_iUnionLift 5 [0,0,1] := fun h =>
  absurd (@h Unit Bool Bool S1 f1 Set.univ hT1 Set.univ true false () trivial trivial) (by decide)

-- `Set.preimage_iUnionLift` idx 7: necessary (S _ = {true} in Bool, T = univ)
theorem w4_11 : ¬ indepL% Set.preimage_iUnionLift 7 [0,0,1] := fun h => by
  have := @h Bool Unit Bool (fun _ => {true}) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ Set.univ
  have h2 := this (Set.mem_univ false)
  simp at h2

-- `Set.iUnionLift_const` idx 5: necessary (S i = univ in Bool, f i x = x || i, ci i = c = true)
theorem w4_12 : ¬ indepL% Set.iUnionLift_const 5 [0,1,1] := fun h =>
  absurd (@h Bool Bool Bool (fun _ => Set.univ) f2 Set.univ (fun _ _ => Set.mem_iUnion.2 ⟨true, trivial⟩)
    ⟨true, trivial⟩ (fun _ => ⟨true, trivial⟩) (fun _ => rfl) true (fun _ => rfl) true false false trivial trivial)
    (by decide)

-- `Set.iUnionLift_const` idx 7: necessary (S _ = {true} in Bool, T = univ)
theorem w4_13 : ¬ indepL% Set.iUnionLift_const 7 [0,1,1] := fun h => by
  have := @h Bool Unit Bool (fun _ => {true}) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ ⟨true, trivial⟩
    (fun _ => ⟨true, rfl⟩) (fun _ => rfl) true (fun _ => rfl)
  have h2 := this (Set.mem_univ false)
  simp at h2

-- `Set.iUnionLift_const` idx 10: necessary (S = univ in Bool, f = val, c = false, ci = true, cβ = true)
theorem w4_14 : ¬ dropL% Set.iUnionLift_const 10 [0,1,1] := fun h => by
  have := @h Bool Unit Bool (fun _ => Set.univ) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ
    (fun _ _ => Set.mem_iUnion.2 ⟨(), trivial⟩) ⟨false, trivial⟩ (fun _ => ⟨true, trivial⟩) true (fun _ => rfl)
  simp [Set.iUnionLift] at this

-- `Set.iUnionLift_const` idx 12: necessary (S = univ in Bool, f = val, c = ci = true, cβ = false)
theorem w4_15 : ¬ dropL% Set.iUnionLift_const 12 [0,1,1] := fun h => by
  have := @h Bool Unit Bool (fun _ => Set.univ) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ
    (fun _ _ => Set.mem_iUnion.2 ⟨(), trivial⟩) ⟨true, trivial⟩ (fun _ => ⟨true, trivial⟩) (fun _ => rfl) false
  simp [Set.iUnionLift] at this

-- `Set.iUnionLift_unary` idx 5: necessary (S i = univ on Unit, f i _ = i, u = ui = uβ = id)
theorem w4_16 : ¬ indepL% Set.iUnionLift_unary 5 [0,1,1] := fun h =>
  absurd (@h Unit Bool Bool S1 f1 Set.univ hS1.symm id (fun _ => id) (fun _ _ => rfl) id (fun _ _ => rfl)
    ⟨(), trivial⟩ true false () trivial trivial) (by decide)

-- `Set.iUnionLift_unary` idx 7: necessary (S _ = {true} in Bool, T = univ)
theorem w4_17 : ¬ indepL% Set.iUnionLift_unary 7 [0,1,1] := fun h => by
  have := @h Bool Unit Bool (fun _ => {true}) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ id (fun _ => id) id
    (fun _ _ => rfl) ⟨true, trivial⟩
  have h2 : false ∈ ⋃ _ : Unit, ({true} : Set Bool) := this ▸ Set.mem_univ false
  simp at h2

-- `Set.iUnionLift_unary` idx 12: necessary (S = univ in Bool, f = val, u = ui = id, uβ = not)
theorem w4_18 : ¬ dropL% Set.iUnionLift_unary 12 [0,1,1] := fun h => by
  have := @h Bool Unit Bool (fun _ => Set.univ) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ
    (Set.iUnion_const _).symm id (fun _ => id) (fun _ _ => rfl) not ⟨true, trivial⟩
  simp [Set.iUnionLift] at this

-- `Set.iUnionLift_binary` idx 5: necessary (S i = univ on Unit, f i _ = i, op/opi/opβ = left projection)
theorem w4_19 : ¬ indepL% Set.iUnionLift_binary 5 [0,1,1] := fun h =>
  absurd (@h Unit Bool Bool S1 f1 Set.univ hS1.symm (fun i _ => ⟨i, subset_rfl, subset_rfl⟩) (fun x _ => x)
    (fun _ x _ => x) (fun _ _ _ => rfl) (fun a _ => a) (fun _ _ _ => rfl) ⟨(), trivial⟩ ⟨(), trivial⟩
    true false () trivial trivial) (by decide)

-- `Set.iUnionLift_binary` idx 7: necessary (S _ = {true} in Bool, T = univ)
theorem w4_20 : ¬ indepL% Set.iUnionLift_binary 7 [0,1,1] := fun h => by
  have := @h Bool Unit Bool (fun _ => {true}) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ
    (fun _ _ => ⟨(), subset_rfl, subset_rfl⟩) (fun x _ => x) (fun _ x _ => x) (fun a _ => a) (fun _ _ _ => rfl)
    ⟨true, trivial⟩ ⟨true, trivial⟩
  have h2 : false ∈ ⋃ _ : Unit, ({true} : Set Bool) := this ▸ Set.mem_univ false
  simp at h2

-- `Set.iUnionLift_binary` idx 8: necessary (S i = {i} in Bool, not directed; op = left, opβ = right projection)
theorem w4_21 : ¬ dropL% Set.iUnionLift_binary 8 [0,1,1] := fun h => by
  have := @h Bool Bool Bool Ssg (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ hSsg.symm (fun x _ => x)
    (fun _ x _ => x) (fun _ _ _ => rfl) (fun _ b => b) (fun i x y => x.2.trans y.2.symm) ⟨true, trivial⟩ ⟨false, trivial⟩
  simp [Set.iUnionLift] at this

-- `Set.iUnionLift_binary` idx 11: necessary (S = univ in Bool, op x _ = !x, opi/opβ = left projection)
theorem w4_22 : ¬ dropL% Set.iUnionLift_binary 11 [0,1,1] := fun h => by
  have := @h Bool Unit Bool (fun _ => Set.univ) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ
    (Set.iUnion_const _).symm (fun _ _ => ⟨(), subset_rfl, subset_rfl⟩) (fun x _ => ⟨!x.val, trivial⟩)
    (fun _ x _ => x) (fun a _ => a) (fun _ _ _ => rfl) ⟨true, trivial⟩ ⟨true, trivial⟩
  simp [Set.iUnionLift] at this

-- `Set.iUnionLift_binary` idx 13: necessary (S = univ in Bool, op = opi = left projection, opβ = const false)
theorem w4_23 : ¬ dropL% Set.iUnionLift_binary 13 [0,1,1] := fun h => by
  have := @h Bool Unit Bool (fun _ => Set.univ) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ
    (Set.iUnion_const _).symm (fun _ _ => ⟨(), subset_rfl, subset_rfl⟩) (fun x _ => x)
    (fun _ x _ => x) (fun _ _ _ => rfl) (fun _ _ => false) ⟨true, trivial⟩ ⟨true, trivial⟩
  simp [Set.iUnionLift] at this

-- `Set.liftCover_coe` idx 5: necessary (S i = univ on Unit, f i _ = i)
theorem w4_24 : ¬ indepL% Set.liftCover_coe 5 [0,1,1] := fun h =>
  absurd (@h Unit Bool Bool S1 f1 hS1 true ⟨(), trivial⟩ true false () trivial trivial) (by decide)

-- `Set.liftCover_coe` idx 6: necessary (S _ = {true} in Bool does not cover)
theorem w4_25 : ¬ indepL% Set.liftCover_coe 6 [0,1,1] := fun h => by
  have := @h Bool Unit Bool (fun _ => {true}) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) () ⟨true, rfl⟩
  have h2 : false ∈ ⋃ _ : Unit, ({true} : Set Bool) := this ▸ Set.mem_univ false
  simp at h2

-- `Set.liftCover_of_mem` idx 5: necessary (S i = univ on Unit, f i _ = i)
theorem w4_26 : ¬ indepL% Set.liftCover_of_mem 5 [0,1,1] := fun h =>
  absurd (@h Unit Bool Bool S1 f1 hS1 true () trivial true false () trivial trivial) (by decide)

-- `Set.liftCover_of_mem` idx 6: necessary (S _ = {true} in Bool does not cover)
theorem w4_27 : ¬ indepL% Set.liftCover_of_mem 6 [0,1,1] := fun h => by
  have := @h Bool Unit Bool (fun _ => {true}) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) () true rfl
  have h2 : false ∈ ⋃ _ : Unit, ({true} : Set Bool) := this ▸ Set.mem_univ false
  simp at h2

-- `Set.liftCover_of_mem` idx 9: necessary (S i = {i} in Bool, x = true, i = false)
theorem w4_28 : ¬ indepL% Set.liftCover_of_mem 9 [0,1,1] := fun h => by
  have := @h Bool Bool Bool Ssg (fun _ x => x.val) (fun _ _ _ _ _ => rfl) hSsg false true
  simp [Ssg] at this

-- `Set.preimage_liftCover` idx 5: necessary (S i = univ on Unit, f i _ = i)
theorem w4_29 : ¬ indepL% Set.preimage_liftCover 5 [0,0,1] := fun h =>
  absurd (@h Unit Bool Bool S1 f1 hS1 Set.univ true false () trivial trivial) (by decide)

-- `Set.preimage_liftCover` idx 6: necessary (S _ = {true} in Bool does not cover)
theorem w4_30 : ¬ indepL% Set.preimage_liftCover 6 [0,0,1] := fun h => by
  have := @h Bool Unit Bool (fun _ => {true}) (fun _ x => x.val) (fun _ _ _ _ _ => rfl) Set.univ
  have h2 : false ∈ ⋃ _ : Unit, ({true} : Set Bool) := this ▸ Set.mem_univ false
  simp at h2

-- `SetLike.instFinite` idx 3: necessary (A = Set ℕ, B = ℕ)
theorem w4_31 : ¬ drop0% SetLike.instFinite 3 := fun h => by
  have := @h (Set ℕ) ℕ ⟨id, fun _ _ e => e⟩
  exact not_finite (Set ℕ)

-- `Function.eq_of_sigmaMk_comp` idx 3: necessary (γ = Empty, a = true, b = false)
theorem w4_32 : ¬ drop0% Function.eq_of_sigmaMk_comp 3 := fun h =>
  absurd (@h Bool (fun _ => Unit) Empty true false Empty.elim Empty.elim (funext fun e => e.elim)).1 (by decide)

-- `Sigma.subtype_ext` idx 6: necessary (p = ⊤, second components true, false)
theorem w4_33 : ¬ drop0% Sigma.subtype_ext 6 := fun h => by
  have := @h Unit Bool (fun _ _ => True) ⟨(), ⟨true, trivial⟩⟩ ⟨(), ⟨false, trivial⟩⟩ rfl
  simp at this

-- `Function.Injective.sigma_map` idx 6: necessary (f₁ : Bool → Unit constant, fibres Unit)
theorem w4_34 : ¬ drop0% Function.Injective.sigma_map 6 := fun h => by
  have := @h Bool Unit (fun _ => Unit) (fun _ => Unit) (fun _ => ()) (fun _ => id) (fun _ _ _ e => e)
    ⟨true, ()⟩ ⟨false, ()⟩ rfl
  simp at this

-- `Function.Injective.sigma_map` idx 7: necessary (f₁ = id on Unit, f₂ : Bool → Unit)
theorem w4_35 : ¬ drop0% Function.Injective.sigma_map 7 := fun h => by
  have := @h Unit Unit (fun _ => Bool) (fun _ => Unit) id (fun _ _ => ()) Function.injective_id
    ⟨(), true⟩ ⟨(), false⟩ rfl
  simp at this

-- `Function.Injective.of_sigma_map` idx 6: necessary (f₂ : Bool → Unit)
theorem w4_36 : ¬ drop0% Function.Injective.of_sigma_map 6 := fun h => by
  have := @h Unit Unit (fun _ => Bool) (fun _ => Unit) id (fun _ _ => ()) () (a₁ := true) (a₂ := false) rfl
  simp at this

-- `Function.Injective.sigma_map_iff` idx 6: necessary (f₁ : Bool → Unit constant, fibres Unit)
theorem w4_37 : ¬ drop0% Function.Injective.sigma_map_iff 6 := fun h => by
  have := (@h Bool Unit (fun _ => Unit) (fun _ => Unit) (fun _ => ()) (fun _ => id)).2 (fun _ _ _ e => e)
    (a₁ := ⟨true, ()⟩) (a₂ := ⟨false, ()⟩) rfl
  simp at this

-- `Function.Surjective.sigma_map` idx 6: necessary (α₁ = Empty, α₂ = Unit)
theorem w4_38 : ¬ drop0% Function.Surjective.sigma_map 6 := fun h => by
  obtain ⟨⟨e, _⟩, _⟩ := @h Empty Unit (fun _ => Unit) (fun _ => Unit) Empty.elim (fun e => e.elim) (fun e => e.elim)
    ⟨(), ()⟩
  exact e.elim

-- `Function.Surjective.sigma_map` idx 7: necessary (fibre Empty → Unit)
theorem w4_39 : ¬ drop0% Function.Surjective.sigma_map 7 := fun h => by
  obtain ⟨⟨_, e⟩, _⟩ := @h Unit Unit (fun _ => Empty) (fun _ => Unit) id (fun _ e => e.elim) Function.surjective_id
    ⟨(), ()⟩
  exact e.elim

-- `PSigma.subtype_ext` idx 6: necessary (p = ⊤, second components true, false; at Type)
theorem w4_40 : ¬ dropL% PSigma.subtype_ext 6 [1,1] := fun h => by
  have := @h Unit Bool (fun _ _ => True) ⟨(), ⟨true, trivial⟩⟩ ⟨(), ⟨false, trivial⟩⟩ rfl
  simp at this

-- `Stream'.ext` idx 3: necessary (const 0, const 1)
theorem w4_41 : ¬ drop0% Stream'.ext 3 := fun h => cne (@h ℕ _ _)

-- `Stream'.mem_cons_of_mem` idx 4: necessary (a = 1, s = const 0, b = 0)
theorem w4_42 : ¬ drop0% Stream'.mem_cons_of_mem 4 := fun h => by
  have := @h ℕ 1 (Stream'.const 0) 0
  rw [← Stream'.const_eq] at this
  exact nm (by decide) this

-- `Stream'.eq_or_mem_of_mem_cons` idx 4: necessary (a = 1, b = 0, s = const 0)
theorem w4_43 : ¬ drop0% Stream'.eq_or_mem_of_mem_cons 4 := fun h => by
  rcases @h ℕ 1 0 (Stream'.const 0) with e | m
  · exact absurd e (by decide)
  · exact nm (by decide) m

-- `Stream'.mem_of_get_eq` idx 4: necessary (a = 1, s = const 0)
theorem w4_44 : ¬ drop0% Stream'.mem_of_get_eq 4 := fun h => nm (by decide) (@h ℕ 0 (Stream'.const 0) 1)

-- `Stream'.mem_map` idx 5: necessary (f = id, a = 1, s = const 0)
theorem w4_45 : ¬ drop0% Stream'.mem_map 5 := fun h => by
  have := @h ℕ ℕ id 1 (Stream'.const 0)
  rw [Stream'.map_id] at this
  exact nm (by decide) this

-- `Stream'.exists_of_mem_map` idx 5: necessary (f = id, b = 1, s = const 0)
theorem w4_46 : ¬ drop0% Stream'.exists_of_mem_map 5 := fun h => by
  obtain ⟨a, ha, e⟩ := @h ℕ ℕ id 1 (Stream'.const 0)
  subst e
  exact nm (by decide) ha

-- `Stream'.get_of_bisim` idx 2: necessary (R = ⊤, const 0, const 1)
theorem w4_47 : ¬ drop0% Stream'.get_of_bisim 2 := fun h =>
  absurd (@h ℕ (fun _ _ => True) (Stream'.const 0) (Stream'.const 1) 0 trivial).1 (by decide)

-- `Stream'.get_of_bisim` idx 6: necessary (R = ⊥ is a bisimulation)
theorem w4_48 : ¬ drop0% Stream'.get_of_bisim 6 := fun h =>
  absurd (@h ℕ (fun _ _ => False) (fun _ _ e => e.elim) (Stream'.const 0) (Stream'.const 1) 0).1 (by decide)

-- `Stream'.eq_of_bisim` idx 2: necessary (R = ⊤)
theorem w4_49 : ¬ drop0% Stream'.eq_of_bisim 2 := fun h =>
  cne (@h ℕ (fun _ _ => True) (Stream'.const 0) (Stream'.const 1) trivial)

-- `Stream'.eq_of_bisim` idx 5: necessary (R = ⊥)
theorem w4_50 : ¬ drop0% Stream'.eq_of_bisim 5 := fun h =>
  cne (@h ℕ (fun _ _ => False) (fun _ _ e => e.elim) (Stream'.const 0) (Stream'.const 1))

-- `Stream'.bisim_simple` idx 3: necessary (const 0, const 1)
theorem w4_51 : ¬ drop0% Stream'.bisim_simple 3 := fun h =>
  cne (@h ℕ _ _ (Stream'.tail_const 0).symm (Stream'.tail_const 1).symm)

-- `Stream'.bisim_simple` idx 4: necessary (s₁ = 0 :: const 1, s₂ = const 0)
theorem w4_52 : ¬ drop0% Stream'.bisim_simple 4 := fun h =>
  c01 (@h ℕ (Stream'.cons 0 (Stream'.const 1)) (Stream'.const 0) rfl (Stream'.tail_const 0).symm)

-- `Stream'.bisim_simple` idx 5: necessary (s₁ = const 0, s₂ = 0 :: const 1)
theorem w4_53 : ¬ drop0% Stream'.bisim_simple 5 := fun h =>
  c01 (@h ℕ (Stream'.const 0) (Stream'.cons 0 (Stream'.const 1)) rfl (Stream'.tail_const 0).symm).symm

-- `Stream'.coinduction` idx 3: necessary (const 0, const 1)
theorem w4_54 : ¬ drop0% Stream'.coinduction 3 := fun h =>
  cne (@h ℕ _ _ (fun β fr e => by rw [Stream'.tail_const, Stream'.tail_const]; exact e))

-- `Stream'.coinduction` idx 4: necessary (s₁ = 0 :: const 1, s₂ = const 0)
theorem w4_55 : ¬ drop0% Stream'.coinduction 4 := fun h =>
  c01 (@h ℕ (Stream'.cons 0 (Stream'.const 1)) (Stream'.const 0) rfl)

-- `Stream'.mem_interleave_left` idx 4: necessary (a = 1, s₁ = s₂ = const 0)
theorem w4_56 : ¬ drop0% Stream'.mem_interleave_left 4 := fun h => nm_il (@h ℕ 1 (Stream'.const 0) (Stream'.const 0))

-- `Stream'.mem_interleave_right` idx 4: necessary (a = 1, s₁ = s₂ = const 0)
theorem w4_57 : ¬ drop0% Stream'.mem_interleave_right 4 := fun h => nm_il (@h ℕ 1 (Stream'.const 0) (Stream'.const 0))

-- `Stream'.mem_of_mem_even` idx 3: necessary (a = 1, s = const 0)
theorem w4_58 : ¬ drop0% Stream'.mem_of_mem_even 3 := fun h => nm (by decide) (@h ℕ 1 (Stream'.const 0))

-- `Stream'.mem_of_mem_odd` idx 3: necessary (a = 1, s = const 0)
theorem w4_59 : ¬ drop0% Stream'.mem_of_mem_odd 3 := fun h => nm (by decide) (@h ℕ 1 (Stream'.const 0))

-- `Stream'.get_append_left` idx 4: necessary (n = 0, x = [])
theorem w4_60 : ¬ indep0% Stream'.get_append_left 4 := fun h => absurd (@h ℕ 0 [] (Stream'.const 0)) (by decide)

-- `Stream'.append_right_injective` idx 4: necessary (x = [], const 0, const 1)
theorem w4_61 : ¬ drop0% Stream'.append_right_injective 4 := fun h => cne (@h ℕ [] _ _)

-- `Stream'.append_left_injective` idx 5: necessary (x = [0], y = [1])
theorem w4_62 : ¬ drop0% Stream'.append_left_injective 5 := fun h =>
  absurd (@h ℕ [0] [1] (Stream'.const 0) (Stream'.const 0) rfl) (by decide)

-- `Stream'.append_left_injective` idx 6: necessary (x = [], y = [0], a = b = const 0)
theorem w4_63 : ¬ drop0% Stream'.append_left_injective 6 := fun h =>
  absurd (@h ℕ [] [0] (Stream'.const 0) (Stream'.const 0)
    (by rw [Stream'.nil_append_stream, Stream'.cons_append_stream, Stream'.nil_append_stream, ← Stream'.const_eq]))
    (by decide)

-- `Stream'.mem_append_stream_right` idx 4: necessary (a = 1, l = [], s = const 0)
theorem w4_64 : ¬ drop0% Stream'.mem_append_stream_right 4 := fun h => by
  have := @h ℕ 1 [] (Stream'.const 0)
  rw [Stream'.nil_append_stream] at this
  exact nm (by decide) this

-- `Stream'.mem_append_stream_left` idx 4: necessary (a = 1, l = [], s = const 0)
theorem w4_65 : ¬ drop0% Stream'.mem_append_stream_left 4 := fun h => by
  have := @h ℕ 1 [] (Stream'.const 0)
  rw [Stream'.nil_append_stream] at this
  exact nm (by decide) this

-- `Stream'.getElem?_take` idx 4: necessary (k = n = 0)
theorem w4_66 : ¬ drop0% Stream'.getElem?_take 4 := fun h => by
  have := @h ℕ (Stream'.const 0) 0 0
  simp [Stream'.take_zero] at this

-- `Stream'.take_get` idx 4: necessary (m = n = 0)
theorem w4_67 : ¬ indep0% Stream'.take_get 4 := fun h => by
  have := @h ℕ 0 0 (Stream'.const 0)
  simp [Stream'.take_zero] at this

-- `Stream'.take_append_of_le_length` idx 4: necessary (n = 1, x = [], a = const 0)
theorem w4_68 : ¬ drop0% Stream'.take_append_of_le_length 4 := fun h => by
  have := @h ℕ 1 [] (Stream'.const 0)
  simp [Stream'.take_succ, Stream'.take_zero] at this

-- `Stream'.take_prefix_take_left` idx 4: necessary (m = 1, n = 0)
theorem w4_69 : ¬ drop0% Stream'.take_prefix_take_left 4 := fun h => by
  have := @h ℕ 1 0 (Stream'.const 0)
  simp [Stream'.take_succ, Stream'.take_zero] at this

-- `Stream'.drop_append_of_le_length` idx 4: necessary (n = 1, x = [], a = 1 :: const 0)
theorem w4_70 : ¬ drop0% Stream'.drop_append_of_le_length 4 := fun h => by
  have := congrArg (fun s => Stream'.get s 0) (@h ℕ 1 [] (Stream'.cons 1 (Stream'.const 0)))
  simp [Stream'.get_drop] at this

-- `Stream'.take_theorem` idx 3: necessary (const 0, const 1)
theorem w4_71 : ¬ drop0% Stream'.take_theorem 3 := fun h => cne (@h ℕ _ _)

-- `Stream'.mem_cycle` idx 4: necessary (a = 1, l = [0])
theorem w4_72 : ¬ drop0% Stream'.mem_cycle 4 := fun h => by
  have := @h ℕ 1 [0] (by simp)
  rw [Stream'.cycle_singleton] at this
  exact nm (by decide) this

-- `Subtype.heq_iff_coe_eq` idx 3: necessary (at Type: Bool, p = ⊤, q = (· = true), a1 = a2 = true)
theorem w4_73 : ¬ dropL% Subtype.heq_iff_coe_eq 3 [1] := fun h =>
  sub_ne (type_eq_of_heq ((@h Bool (fun _ => True) (fun x => x = true) ⟨true, trivial⟩ ⟨true, rfl⟩).2 rfl))

-- `Subtype.heq_iff_coe_heq` idx 7: necessary (α = β = Bool, p = ⊤, q = (· = true), a = b = true)
theorem w4_75 : ¬ dropL% Subtype.heq_iff_coe_heq 7 [1] := fun h =>
  sub_ne (type_eq_of_heq ((@h Bool Bool (fun _ => True) (fun x => x = true) ⟨true, trivial⟩ ⟨true, rfl⟩ rfl).2 HEq.rfl))

-- `Function.extend_val_apply'` idx 6: necessary (p = ⊤ on Bool, g = false, j = true)
theorem w4_76 : ¬ dropL% Function.extend_val_apply' 6 [1,1] := fun h => by
  have := @h Bool Bool (fun _ => True) (fun _ => false) (fun _ => true) true
  rw [Subtype.val_injective.extend_apply (fun _ => false) (fun _ => true) ⟨true, trivial⟩] at this
  exact absurd this (by decide)

-- `Subtype.surjective_restrict` idx 2: necessary (β false = Empty, β true = Unit, p = (· = true))
theorem w4_77 : ¬ dropL% Subtype.surjective_restrict 2 [0,1] := fun h => by
  obtain ⟨f, _⟩ := @h Bool (fun b => cond b Unit Empty) (fun x => x = true) (fun i => by
    obtain ⟨x, rfl⟩ := i; exact ())
  exact Empty.elim (f false)

-- `Subtype.map_injective` idx 6: necessary (f : Bool → Unit constant, p = q = ⊤)
theorem w4_78 : ¬ dropL% Subtype.map_injective 6 [1,1] := fun h => by
  have := @h Bool Unit (fun _ => True) (fun _ => True) (fun _ => ()) (fun _ _ => trivial) ⟨true, trivial⟩
    ⟨false, trivial⟩ rfl
  simp at this

-- `Subtype.map_involutive` idx 3: necessary (f = not, p = (· = true))
theorem w4_79 : ¬ indepL% Subtype.map_involutive 3 [1] := fun h =>
  absurd (@h Bool (fun x => x = true) not Bool.not_not true rfl) (by decide)

-- `Subtype.map_involutive` idx 4: necessary (f = const true, p = ⊤)
theorem w4_80 : ¬ dropL% Subtype.map_involutive 4 [1] := fun h => by
  have := @h Bool (fun _ => True) (fun _ => true) (fun _ _ => trivial) ⟨false, trivial⟩
  simp [Subtype.map] at this

-- `Subtype.symm` idx 5: necessary (equality setoid on Bool, s = true, t = false)
theorem w4_81 : ¬ dropL% Subtype.symm 5 [1] := fun h =>
  Bool.false_ne_true (@h Bool (fun _ => True) eqS ⟨true, trivial⟩ ⟨false, trivial⟩)

-- `Subtype.trans` idx 6: necessary (equality setoid on Bool, s = false, t = u = true)
theorem w4_82 : ¬ dropL% Subtype.trans 6 [1] := fun h =>
  Bool.false_ne_true (@h Bool (fun _ => True) eqS ⟨false, trivial⟩ ⟨true, trivial⟩ ⟨true, trivial⟩ rfl)

-- `Subtype.trans` idx 7: necessary (equality setoid on Bool, s = t = true, u = false)
theorem w4_83 : ¬ dropL% Subtype.trans 7 [1] := fun h =>
  Bool.false_ne_true (@h Bool (fun _ => True) eqS ⟨true, trivial⟩ ⟨true, trivial⟩ ⟨false, trivial⟩ rfl).symm

-- `Function.subtypeNeLift_of_neq` idx 7: necessary (i = i₀)
theorem w4_84 : ¬ indep0% Function.subtypeNeLift_of_neq 7 := fun h =>
  @h Unit _ (fun _ => Unit) () (fun _ => ()) () () rfl

-- `Sum.sum_rec_congr` idx 7: necessary (x = inl true, y = inl false)
theorem w4_85 : ¬ indep0% Sum.sum_rec_congr 7 := fun h => by
  have := @h Bool Unit (fun _ => True) (fun _ => trivial) (fun _ => trivial) (Sum.inl true) (Sum.inl false)
  simp at this

-- `Sum.LiftRel.exists_of_isLeft_left` idx 9: necessary (x = y = inr ())
theorem w4_86 : ¬ drop0% Sum.LiftRel.exists_of_isLeft_left 9 := fun h => by
  obtain ⟨_, _, _, e, _⟩ := @h Unit Unit Unit Unit (fun _ _ => True) (fun _ _ => True) (Sum.inr ()) (Sum.inr ())
    (Sum.LiftRel.inr trivial)
  simp at e

-- `Sum.LiftRel.exists_of_isLeft_right` idx 9: necessary (x = y = inr ())
theorem w4_87 : ¬ drop0% Sum.LiftRel.exists_of_isLeft_right 9 := fun h => by
  obtain ⟨_, _, _, e, _⟩ := @h Unit Unit Unit Unit (fun _ _ => True) (fun _ _ => True) (Sum.inr ()) (Sum.inr ())
    (Sum.LiftRel.inr trivial)
  simp at e

-- `Function.Injective.sumElim` idx 5: necessary (α = Bool, β = Empty, γ = True)
theorem w4_88 : ¬ drop0% Function.Injective.sumElim 5 := fun h => by
  have := @h Bool Empty True (fun _ => trivial) (fun e => e.elim) (fun e => e.elim) (fun _ e => e.elim)
    (Sum.inl true) (Sum.inl false) rfl
  simp at this

-- `Function.Surjective.sumMap` idx 6: necessary (f : Empty → Unit, g = id)
theorem w4_89 : ¬ drop0% Function.Surjective.sumMap 6 := fun h => by
  obtain ⟨x, hx⟩ := @h Empty Unit Unit Unit Empty.elim id Function.surjective_id (Sum.inl ())
  rcases x with e | u
  · exact e.elim
  · simp at hx

-- `Function.Surjective.sumMap` idx 7: necessary (f = id, g : Empty → Unit)
theorem w4_90 : ¬ drop0% Function.Surjective.sumMap 7 := fun h => by
  obtain ⟨x, hx⟩ := @h Unit Empty Unit Unit id Empty.elim Function.surjective_id (Sum.inr ())
  rcases x with u | e
  · simp at hx
  · exact e.elim

-- `Function.Bijective.sumMap` idx 6: necessary (f : Empty → Unit, g = id)
theorem w4_91 : ¬ drop0% Function.Bijective.sumMap 6 := fun h => by
  obtain ⟨x, hx⟩ := (@h Empty Unit Unit Unit Empty.elim id Function.bijective_id).2 (Sum.inl ())
  rcases x with e | u
  · exact e.elim
  · simp at hx

-- `Function.Bijective.sumMap` idx 7: necessary (f = id, g : Empty → Unit)
theorem w4_92 : ¬ drop0% Function.Bijective.sumMap 7 := fun h => by
  obtain ⟨x, hx⟩ := (@h Unit Empty Unit Unit id Empty.elim Function.bijective_id).2 (Sum.inr ())
  rcases x with u | e
  · simp at hx
  · exact e.elim

-- `Finset.sumLift₂_mono` idx 10: necessary (f₁ = {()}, g₁ = ∅ on Unit)
theorem w4_93 : ¬ drop0% Finset.sumLift₂_mono 10 := fun h => by
  have := @h Unit Unit Unit Unit Unit Unit (fun _ _ => {()}) (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅)
    (fun _ _ => subset_rfl) (Sum.inl ()) (Sum.inl ())
  simp [Finset.sumLift₂] at this

-- `Finset.sumLift₂_mono` idx 11: necessary (f₂ = {()}, g₂ = ∅ on Unit)
theorem w4_94 : ¬ drop0% Finset.sumLift₂_mono 11 := fun h => by
  have := @h Unit Unit Unit Unit Unit Unit (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => {()}) (fun _ _ => ∅)
    (fun _ _ => subset_rfl) (Sum.inr ()) (Sum.inr ())
  simp [Finset.sumLift₂] at this

-- `Finset.sumLexLift_mono` idx 14: necessary (f₁ = {()}, f₁' = ∅ on Unit)
theorem w4_95 : ¬ drop0% Finset.sumLexLift_mono 14 := fun h => by
  have := @h Unit Unit Unit Unit Unit Unit (fun _ _ => {()}) (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅)
    (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅)
    (fun _ _ => subset_rfl) (fun _ _ => subset_rfl) (fun _ _ => subset_rfl) (Sum.inl ()) (Sum.inl ())
  simp [Finset.sumLexLift] at this

-- `Finset.sumLexLift_mono` idx 15: necessary (f₂ = {()}, f₂' = ∅ on Unit)
theorem w4_96 : ¬ drop0% Finset.sumLexLift_mono 15 := fun h => by
  have := @h Unit Unit Unit Unit Unit Unit (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => {()}) (fun _ _ => ∅)
    (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅)
    (fun _ _ => subset_rfl) (fun _ _ => subset_rfl) (fun _ _ => subset_rfl) (Sum.inr ()) (Sum.inr ())
  simp [Finset.sumLexLift] at this

-- `Finset.sumLexLift_mono` idx 16: necessary (g₁ = {()}, g₁' = ∅ on Unit)
theorem w4_97 : ¬ drop0% Finset.sumLexLift_mono 16 := fun h => by
  have := @h Unit Unit Unit Unit Unit Unit (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅)
    (fun _ _ => {()}) (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅)
    (fun _ _ => subset_rfl) (fun _ _ => subset_rfl) (fun _ _ => subset_rfl) (Sum.inl ()) (Sum.inr ())
  simp [Finset.sumLexLift] at this

-- `Finset.sumLexLift_mono` idx 17: necessary (g₂ = {()}, g₂' = ∅ on Unit)
theorem w4_98 : ¬ drop0% Finset.sumLexLift_mono 17 := fun h => by
  have := @h Unit Unit Unit Unit Unit Unit (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => ∅)
    (fun _ _ => ∅) (fun _ _ => ∅) (fun _ _ => {()}) (fun _ _ => ∅)
    (fun _ _ => subset_rfl) (fun _ _ => subset_rfl) (fun _ _ => subset_rfl) (Sum.inl ()) (Sum.inr ())
  simp [Finset.sumLexLift] at this

-- `Sym.ext` idx 4: necessary ({0} ≠ {1} in Sym ℕ 1)
theorem w4_99 : ¬ drop0% Sym.ext 4 := fun h => sy_ne (@h ℕ 1 _ _)

-- `Sym.mem_cons_of_mem` idx 5: necessary (s = nil, a = 1, b = 0)
theorem w4_100 : ¬ drop0% Sym.mem_cons_of_mem 5 := fun h => by
  have := @h ℕ 0 Sym.nil 1 0
  simp at this

-- `Sym.sound` idx 4: necessary (vectors [0], [1])
theorem w4_101 : ¬ drop0% Sym.sound 4 := fun h => by
  have := congrArg (fun s : Sym ℕ 1 => (s : Multiset ℕ)) (@h ℕ 1 ⟨[0], rfl⟩ ⟨[1], rfl⟩)
  simp [Sym.ofVector] at this

-- `Sym.coe_erase` idx 5: necessary (s = {0}, a = 1)
theorem w4_102 : ¬ indep0% Sym.coe_erase 5 := fun h => by
  have := @h ℕ 0 _ (sy 0) 1
  simp [sy] at this

-- `Sym.cons_erase` idx 5: necessary (s = {0}, a = 1)
theorem w4_103 : ¬ indep0% Sym.cons_erase 5 := fun h => by
  have := @h ℕ 0 _ (sy 0) 1
  simp [sy] at this

-- `Sym.exists_cons_of_mem` idx 4: necessary (s = {0}, a = 1)
theorem w4_104 : ¬ drop0% Sym.exists_cons_of_mem 4 := fun h => by
  obtain ⟨t, e⟩ := @h ℕ 0 (sy 0) 1
  have := congrArg (fun s : Sym ℕ 1 => 1 ∈ (s : Multiset ℕ)) e
  simp [sy] at this

-- `Sym.instNontrivialHAddNatOfNat` idx 2: necessary (α = Unit)
theorem w4_105 : ¬ drop0% Sym.instNontrivialHAddNatOfNat 2 := fun h => not_nontrivial (Sym Unit 1) (@h Unit 0)

-- `Sym.map_congr` idx 6: necessary (f = id, g = const 0, s = {1})
theorem w4_106 : ¬ drop0% Sym.map_congr 6 := fun h => by
  have := congrArg (fun s : Sym ℕ 1 => 1 ∈ s) (@h ℕ ℕ 1 id (fun _ => 0) (sy 1))
  simp [sy] at this

-- `Sym.cast_cast` idx 5: necessary (n = 0, n' = n'' = 1)
theorem w4_107 : ¬ indep0% Sym.cast_cast 5 := fun h => absurd (@h ℕ 0 1 Sym.nil 1 rfl) (by decide)

-- `Sym.cast_cast` idx 6: necessary (n = n' = 0, n'' = 1)
theorem w4_108 : ¬ indep0% Sym.cast_cast 6 := fun h => absurd (@h ℕ 0 0 Sym.nil 1 rfl) (by decide)

-- `Sym.coe_cast` idx 4: necessary (n = 0, m = 1)
theorem w4_109 : ¬ indep0% Sym.coe_cast 4 := fun h => absurd (@h ℕ 0 1 Sym.nil) (by decide)

-- `Sym.mem_cast` idx 5: necessary (n = 0, m = 1)
theorem w4_110 : ¬ indep0% Sym.mem_cast 5 := fun h => absurd (@h ℕ 0 1 Sym.nil 0) (by decide)

-- `Sym.sigma_sub_ext` idx 4: necessary (n = 1, first components 0 and 1)
theorem w4_111 : ¬ drop0% Sym.sigma_sub_ext 4 := fun h =>
  absurd (congrArg Sigma.fst (@h ℕ 1 ⟨0, sy 0⟩ ⟨1, Sym.nil⟩)) (by decide)

-- `Sym.filter_ne_fill` idx 5: necessary (n = 1, a = 0, m = ⟨0, {0}⟩)
theorem w4_112 : ¬ drop0% Sym.filter_ne_fill 5 := fun h => by
  have := congrArg (fun m : (i : Fin 2) × Sym ℕ (1 - ↑i) => (m.1 : ℕ)) (@h ℕ 1 _ 0 ⟨0, sy 0⟩)
  simp [Sym.filterNe, Sym.fill, sy] at this

-- `Sym.count_coe_fill_self_of_notMem` idx 6: necessary (n = 1, a = 0, i = 0, s = {0})
theorem w4_113 : ¬ drop0% Sym.count_coe_fill_self_of_notMem 6 := fun h => by
  have := @h ℕ 1 _ 0 0 (sy 0)
  simp [Sym.coe_fill, sy] at this

-- `Sym.count_coe_fill_of_ne` idx 7: necessary (n = 1, a = x = 0, i = 1, s = nil)
theorem w4_114 : ¬ drop0% Sym.count_coe_fill_of_ne 7 := fun h => by
  have := @h ℕ 1 _ 0 0 1 Sym.nil
  simp [Sym.coe_fill] at this

-- `SymOptionSuccEquiv.encode_of_none_mem` idx 4: necessary (s = {some 0})
theorem w4_115 : ¬ indep0% SymOptionSuccEquiv.encode_of_none_mem 4 := fun h => by
  have := @h ℕ 0 _ (Sym.cons (some 0) Sym.nil)
  simp at this

-- `SymOptionSuccEquiv.encode_of_none_notMem` idx 4: necessary (s = {none})
theorem w4_116 : ¬ indep0% SymOptionSuccEquiv.encode_of_none_notMem 4 := fun h => by
  have := @h ℕ 0 _ (Sym.cons none Sym.nil)
  simp at this

-- `Sym.instInfiniteOfNeZeroNat` idx 2: necessary (α = Empty, k = 1)
theorem w4_117 : ¬ drop0% Sym.instInfiniteOfNeZeroNat 2 := fun h =>
  (Sym.oneEquiv.symm (@Classical.arbitrary _ (@Infinite.nonempty _ (@h Empty 1 _)))).elim

-- `Sym.instInfiniteOfNeZeroNat` idx 3: necessary (α = ℕ, k = 0: Sym ℕ 0 is a singleton)
theorem w4_118 : ¬ drop0% Sym.instInfiniteOfNeZeroNat 3 := fun h => by
  have := @h ℕ 0 _
  exact not_finite (Sym ℕ 0)

-- `Sym2.instInfinite` idx 1: necessary (α = Empty)
theorem w4_119 : ¬ drop0% Sym2.instInfinite 1 := fun h =>
  Sym2.ind (f := fun _ => False) (fun a _ => a.elim) (@Classical.arbitrary _ (@Infinite.nonempty _ (@h Empty)))

-- `Sym2.instInfiniteSubtypeIsDiag` idx 1: necessary (α = Empty)
theorem w4_120 : ¬ drop0% Sym2.instInfiniteSubtypeIsDiag 1 := fun h =>
  Sym2.ind (f := fun _ => False) (fun a _ => a.elim) (@Classical.arbitrary _ (@Infinite.nonempty _ (@h Empty))).1

-- `Sym2.instInfiniteSubtypeNotIsDiag` idx 1: necessary (α = Empty)
theorem w4_121 : ¬ drop0% Sym2.instInfiniteSubtypeNotIsDiag 1 := fun h =>
  Sym2.ind (f := fun _ => False) (fun a _ => a.elim) (@Classical.arbitrary _ (@Infinite.nonempty _ (@h Empty))).1

-- `Sym2.ind` idx 2: necessary (f = ⊥)
theorem w4_122 : ¬ drop0% Sym2.ind 2 := fun h => @h Unit (fun _ => False) s((), ())

-- `Sym2.inductionOn` idx 3: necessary (f = ⊥)
theorem w4_123 : ¬ drop0% Sym2.inductionOn 3 := fun h => @h Unit (fun _ => False) s((), ())

-- `Sym2.inductionOn₂` idx 5: necessary (f = ⊥)
theorem w4_124 : ¬ drop0% Sym2.inductionOn₂ 5 := fun h => @h Unit Unit (fun _ _ => False) s((), ()) s((), ())

-- `Sym2.ext` idx 3: necessary (s(0,0) ≠ s(0,1))
theorem w4_125 : ¬ drop0% Sym2.ext 3 := fun h => by
  have := @h ℕ s(0, 0) s(0, 1)
  simp at this

-- `Sym2.other_spec` idx 3: necessary (a = 1, z = s(0,0))
theorem w4_126 : ¬ indep0% Sym2.other_spec 3 := fun h => by
  have := @h ℕ 1 s(0, 0)
  simp at this

-- `Sym2.other_mem` idx 3: necessary (a = 1, z = s(0,0))
theorem w4_127 : ¬ indep0% Sym2.other_mem 3 := fun h => by
  have := @h ℕ 1 s(0, 0)
  simp at this

-- `Sym2.mem_and_mem_iff` idx 4: necessary (x = y = 0, z = s(0,1))
theorem w4_128 : ¬ drop0% Sym2.mem_and_mem_iff 4 := fun h => by
  have := (@h ℕ 0 0 s(0, 1)).1 ⟨by simp, by simp⟩
  simp at this

-- `Sym2.eq_of_ne_mem` idx 5: necessary (x = y = 0, z = s(0,1), z' = s(0,2))
theorem w4_129 : ¬ drop0% Sym2.eq_of_ne_mem 5 := fun h => by
  have := @h ℕ 0 0 s(0, 1) s(0, 2) (by simp) (by simp) (by simp) (by simp)
  simp at this

-- `Sym2.eq_of_ne_mem` idx 6: necessary (x = 0, y = 1, z = s(1,2), z' = s(0,1))
theorem w4_130 : ¬ drop0% Sym2.eq_of_ne_mem 6 := fun h => by
  have := @h ℕ 0 1 s(1, 2) s(0, 1) (by decide) (by simp) (by simp) (by simp)
  simp at this

-- `Sym2.eq_of_ne_mem` idx 7: necessary (x = 0, y = 1, z = s(0,2), z' = s(0,1))
theorem w4_131 : ¬ drop0% Sym2.eq_of_ne_mem 7 := fun h => by
  have := @h ℕ 0 1 s(0, 2) s(0, 1) (by decide) (by simp) (by simp) (by simp)
  simp at this

-- `Sym2.eq_of_ne_mem` idx 8: necessary (x = 0, y = 1, z = s(0,1), z' = s(1,2))
theorem w4_132 : ¬ drop0% Sym2.eq_of_ne_mem 8 := fun h => by
  have := @h ℕ 0 1 s(0, 1) s(1, 2) (by decide) (by simp) (by simp) (by simp)
  simp at this

-- `Sym2.eq_of_ne_mem` idx 9: necessary (x = 0, y = 1, z = s(0,1), z' = s(0,2))
theorem w4_133 : ¬ drop0% Sym2.eq_of_ne_mem 9 := fun h => by
  have := @h ℕ 0 1 s(0, 1) s(0, 2) (by decide) (by simp) (by simp) (by simp)
  simp at this

-- `Sym2.map_congr` idx 5: necessary (f = id, g = const 0, s = s(1,1))
theorem w4_134 : ¬ drop0% Sym2.map_congr 5 := fun h => by
  have := @h ℕ ℕ id (fun _ => 0) s(1, 1)
  simp at this

-- `Sym2.pair_eq_pmap` idx 6: necessary (P = (· = 0), a = 1, b = 0)
theorem w4_135 : ¬ indep0% Sym2.pair_eq_pmap 6 := fun h =>
  absurd (@h ℕ ℕ (fun x => x = 0) (fun _ _ => 0) 1 0 rfl) (by decide)

-- `Sym2.pair_eq_pmap` idx 7: necessary (P = (· = 0), a = 0, b = 1)
theorem w4_136 : ¬ indep0% Sym2.pair_eq_pmap 7 := fun h =>
  absurd (@h ℕ ℕ (fun x => x = 0) (fun _ _ => 0) 0 1 rfl) (by decide)

-- `Sym2.pmap_pair` idx 6: necessary (P = ⊥)
theorem w4_137 : ¬ indep0% Sym2.pmap_pair 6 := fun h =>
  @h ℕ ℕ (fun _ => False) (fun _ e => e.elim) 0 0 0 (by simp)

-- `Sym2.mem_pmap_iff` idx 5: necessary (P = ⊥)
theorem w4_138 : ¬ indep0% Sym2.mem_pmap_iff 5 := fun h =>
  @h ℕ ℕ (fun _ => False) (fun _ e => e.elim) s(0, 0) 0 0 (by simp)

-- `Sym2.pmap_eq_map` idx 5: necessary (P = ⊥)
theorem w4_139 : ¬ indep0% Sym2.pmap_eq_map 5 := fun h =>
  @h ℕ ℕ (fun _ => False) id s(0, 0) 0 (by simp)

-- `Sym2.map_pmap` idx 7: necessary (Q = ⊥)
theorem w4_140 : ¬ indep0% Sym2.map_pmap 7 := fun h =>
  @h ℕ ℕ ℕ (fun _ => False) id (fun _ e => e.elim) s(0, 0) 0 (by simp)

-- `Sym2.pmap_map` idx 7: necessary (P = ⊥)
theorem w4_141 : ¬ indep0% Sym2.pmap_map 7 := fun h =>
  @h ℕ ℕ ℕ (fun _ => False) (fun _ e => e.elim) id s(0, 0) 0 (by simp)

-- `Sym2.pmap_pmap` idx 8: necessary (P = ⊥)
theorem w4_142 : ¬ indep0% Sym2.pmap_pmap 8 := fun h =>
  @h ℕ ℕ ℕ (fun _ => False) (fun _ => True) (fun _ e => e.elim) (fun _ _ => 0) s(0, 0) 0 (by simp)

-- `Sym2.pmap_pmap` idx 9: necessary (P = ⊤, Q = ⊥, f = id)
theorem w4_143 : ¬ indep0% Sym2.pmap_pmap 9 := fun h =>
  @h ℕ ℕ ℕ (fun _ => True) (fun _ => False) (fun a _ => a) (fun _ e => e.elim) s(0, 0) (fun _ _ => trivial) 0
    (by simp [Sym2.mem_pmap_iff])

-- `Sym2.pmap_subtype_map_subtypeVal` idx 3: necessary (P = ⊥)
theorem w4_144 : ¬ indep0% Sym2.pmap_subtype_map_subtypeVal 3 := fun h =>
  @h ℕ (fun _ => False) s(0, 0) 0 (by simp)

-- `Sym2.attachWith_map_subtypeVal` idx 3: necessary (P = ⊥)
theorem w4_145 : ¬ indep0% Sym2.attachWith_map_subtypeVal 3 := fun h =>
  @h ℕ s(0, 0) (fun _ => False) 0 (by simp)

-- `Sym2.attachWith_inj` idx 4: necessary (P = (· = 0), z₁ = s(1,1), z₂ = s(0,0))
theorem w4_146 : ¬ indep0% Sym2.attachWith_inj 4 := fun h =>
  absurd (@h ℕ (fun x => x = 0) s(1, 1) s(0, 0) (by simp) 1 (by simp)) (by decide)

-- `Sym2.attachWith_inj` idx 5: necessary (P = (· = 0), z₁ = s(0,0), z₂ = s(1,1))
theorem w4_147 : ¬ indep0% Sym2.attachWith_inj 5 := fun h =>
  absurd (@h ℕ (fun x => x = 0) s(0, 0) s(1, 1) (by simp) 1 (by simp)) (by decide)

-- `Sym2.IsDiag.map` idx 4: necessary (z = s(0,1), f = id)
theorem w4_148 : ¬ drop0% Sym2.IsDiag.map 4 := fun h => by
  have := @h ℕ ℕ s(0, 1) id
  simp at this

-- `Sym2.isDiag_map` idx 4: necessary (f = const 0, z = s(0,1))
theorem w4_149 : ¬ drop0% Sym2.isDiag_map 4 := fun h => by
  have := (@h ℕ ℕ s(0, 1) (fun _ => 0)).1 (by simp)
  simp at this

-- `Sym2.isDiag_of_subsingleton` idx 1: necessary (α = Bool, z = s(true,false))
theorem w4_150 : ¬ drop0% Sym2.isDiag_of_subsingleton 1 := fun h => by
  have := @h Bool s(true, false)
  simp at this

-- `Sym2.diag_diagElem` idx 2: necessary (z = s(true,false))
theorem w4_151 : ¬ indep0% Sym2.diag_diagElem 2 := fun h => by
  have := @h Bool s(true, false)
  simp at this

-- `Sym2.mk_fiber_of_isDiag` idx 2: necessary (z = s(true,false))
theorem w4_152 : ¬ indep0% Sym2.mk_fiber_of_isDiag 2 := fun h => by
  have := @h Bool s(true, false)
  simp at this

-- `Sym2.diagSet_eq_univ_of_subsingleton` idx 1: necessary (α = Bool)
theorem w4_153 : ¬ drop0% Sym2.diagSet_eq_univ_of_subsingleton 1 := fun h => by
  have h2 : s(true, false) ∈ (Sym2.diagSet : Set (Sym2 Bool)) := (@h Bool) ▸ Set.mem_univ _
  simp at h2

-- `Sym2.other_ne` idx 3: necessary (z = s(0,0), a = 0)
theorem w4_154 : ¬ drop0% Sym2.other_ne 3 := fun h => @h ℕ 0 s(0, 0) (by simp) (other00 _)

-- `Sym2.other_ne` idx 4: necessary (z = s(0,1), a = 2)
theorem w4_155 : ¬ indep0% Sym2.other_ne 4 := fun h => by
  have := @h ℕ 2 s(0, 1) (by simp)
  simp at this

-- `Sym2.fromRel_mono` idx 3: necessary (r₁ = (<) on ℕ, r₂ = ⊤)
theorem w4_156 : ¬ indep0% Sym2.fromRel_mono 3 := fun h =>
  nsymm (@h ℕ (fun a b => a < b) (fun _ _ => True) ⟨fun _ _ _ => trivial⟩ (fun _ _ _ => trivial))

-- `Sym2.fromRel_mono` idx 4: necessary (r₁ = ⊥, r₂ = (<) on ℕ)
theorem w4_157 : ¬ indep0% Sym2.fromRel_mono 4 := fun h =>
  nsymm (@h ℕ (fun _ _ => False) (fun a b => a < b) ⟨fun _ _ e => e⟩ (fun _ _ e => e.elim))

-- `Sym2.fromRel_mono` idx 5: necessary (r₁ = ⊤, r₂ = ⊥)
theorem w4_158 : ¬ drop0% Sym2.fromRel_mono 5 := fun h =>
  Sym2.fromRel_prop.1 (@h ℕ (fun _ _ => True) (fun _ _ => False) ⟨fun _ _ _ => trivial⟩ ⟨fun _ _ e => e⟩
    s(0, 0) (Sym2.fromRel_prop.2 trivial))

-- `Sym2.mem_fromRel_comap` idx 3: necessary (r = (<) on ℕ)
theorem w4_159 : ¬ indep0% Sym2.mem_fromRel_comap 3 := fun h => nsymm (@h ℕ ℕ (fun a b => a < b) id s(0, 0))

-- `Sym2.mem_fromRel_irrefl_other_ne` idx 2: necessary (r = (<) on ℕ)
theorem w4_160 : ¬ indep0% Sym2.mem_fromRel_irrefl_other_ne 2 := fun h =>
  nsymm (@h ℕ (fun a b => a < b) ⟨Nat.lt_irrefl⟩ 0 s(0, 0) (by simp))

-- `Sym2.mem_fromRel_irrefl_other_ne` idx 3: necessary (r = ⊤, z = s(0,0), a = 0)
theorem w4_161 : ¬ drop0% Sym2.mem_fromRel_irrefl_other_ne 3 := fun h =>
  @h ℕ (fun _ _ => True) ⟨fun _ _ _ => trivial⟩ 0 s(0, 0) (Sym2.fromRel_prop.2 trivial) (by simp) (other00 _)

-- `Sym2.mem_fromRel_irrefl_other_ne` idx 6: necessary (r = ⊥, z = s(0,0), a = 0)
theorem w4_162 : ¬ drop0% Sym2.mem_fromRel_irrefl_other_ne 6 := fun h =>
  @h ℕ (fun _ _ => False) ⟨fun _ _ e => e⟩ ⟨fun _ e => e⟩ 0 s(0, 0) (by simp) (other00 _)

-- `Sym2.mem_fromRel_irrefl_other_ne` idx 7: necessary (r = (≠) on ℕ, z = s(0,1), a = 2)
theorem w4_163 : ¬ indep0% Sym2.mem_fromRel_irrefl_other_ne 7 := fun h => by
  have := @h ℕ (fun a b => a ≠ b) ⟨fun _ _ e => Ne.symm e⟩ ⟨fun _ e => e rfl⟩ 2 s(0, 1)
    (Sym2.fromRel_prop.2 (by decide))
  simp at this

-- `Sym2.fromRelNdrec_mk` idx 3: necessary (r = (<) on ℕ)
theorem w4_164 : ¬ indep0% Sym2.fromRelNdrec_mk 3 := fun h =>
  nsymm (@h ℕ (fun a b => a < b) True 0 1 (by decide) (fun _ _ _ => trivial))

-- `Sym2.fromRelNdrec_mk` idx 6: necessary (r = ⊥ on Unit)
theorem w4_165 : ¬ indep0% Sym2.fromRelNdrec_mk 6 := fun h =>
  @h Unit (fun _ _ => False) True ⟨fun _ _ e => e⟩ () () (fun _ _ e => e.elim) (fun _ _ e => e.elim)

-- `Sym2.fromRelNdrec_mk` idx 8: necessary (motive = Bool, r = ⊤ on Bool, f a b _ = a)
theorem w4_166 : ¬ indepL% Sym2.fromRelNdrec_mk 8 [0,1] := fun h =>
  absurd (@h Bool (fun _ _ => True) Bool ⟨fun _ _ _ => trivial⟩ true true trivial (fun a _ _ => a) true false trivial)
    (by decide)

-- `Equiv.sigmaFiberFromRel_symm_apply_coe` idx 3: necessary (r = (<) on ℕ, f constant)
theorem w4_167 : ¬ indep0% Equiv.sigmaFiberFromRel_symm_apply_coe 3 := fun h =>
  nsymm (@h ℕ Unit (fun a b => a < b) (fun _ => ()) (fun _ _ _ => rfl))

-- `Equiv.sigmaFiberFromRel_apply` idx 3: necessary (r = (<) on ℕ, f constant)
theorem w4_168 : ¬ indep0% Equiv.sigmaFiberFromRel_apply 3 := fun h =>
  nsymm (@h ℕ Unit (fun a b => a < b) (fun _ => ()) (fun _ _ _ => rfl))

-- `Equiv.sigmaFiberFromRel_symm_apply_coe` idx 5: necessary (r = ⊤ on Bool, f = id)
theorem w4_169 : ¬ indep0% Equiv.sigmaFiberFromRel_symm_apply_coe 5 := fun h => by
  have := @h Bool Bool (fun _ _ => True) ⟨fun _ _ _ => trivial⟩ id
    ⟨true, ⟨s(⟨true, rfl⟩, ⟨true, rfl⟩), Sym2.fromRel_prop.2 trivial⟩⟩ true false trivial
  exact Bool.noConfusion (show true = false from this)

-- `Equiv.sigmaFiberFromRel_apply` idx 5: necessary (r = ⊤ on Bool, f = id)
theorem w4_170 : ¬ indep0% Equiv.sigmaFiberFromRel_apply 5 := fun h => by
  have := @h Bool Bool (fun _ _ => True) ⟨fun _ _ _ => trivial⟩ id ⟨s(true, true), Sym2.fromRel_prop.2 trivial⟩
    true false trivial
  exact Bool.noConfusion (show true = false from this)

-- `Equiv.sigmaQuotientFromRel_symm_apply_coe` idx 3: necessary (r = (<) on ℕ, r' trivial on Unit)
theorem w4_171 : ¬ indep0% Equiv.sigmaQuotientFromRel_symm_apply_coe 3 := fun h =>
  nsymm (@h ℕ Unit (fun a b => a < b) topS ⟨fun _ => (), fun _ => trivial⟩)

-- `Equiv.sigmaQuotientFromRel_apply` idx 3: necessary (r = (<) on ℕ, r' trivial on Unit)
theorem w4_172 : ¬ indep0% Equiv.sigmaQuotientFromRel_apply 3 := fun h =>
  nsymm (@h ℕ Unit (fun a b => a < b) topS ⟨fun _ => (), fun _ => trivial⟩)

-- `Sym2.toRel_mono` idx 3: necessary (s₁ = univ, s₂ = ∅)
theorem w4_173 : ¬ drop0% Sym2.toRel_mono 3 := fun h =>
  (Sym2.toRel_prop _ _ _).1 (@h ℕ Set.univ ∅ 0 0 ((Sym2.toRel_prop _ _ _).2 trivial))

-- `Sym2.card_toFinset_of_isDiag` idx 3: necessary (z = s(0,1))
theorem w4_174 : ¬ drop0% Sym2.card_toFinset_of_isDiag 3 := fun h => by
  have := @h ℕ _ s(0, 1)
  rw [Sym2.card_toFinset_of_not_isDiag _ (by simp)] at this
  exact absurd this (by decide)

-- `Sym2.card_toFinset_of_not_isDiag` idx 3: necessary (z = s(0,0))
theorem w4_175 : ¬ drop0% Sym2.card_toFinset_of_not_isDiag 3 := fun h => by
  have := @h ℕ _ s(0, 0)
  rw [Sym2.card_toFinset_of_isDiag _ (by simp)] at this
  exact absurd this (by decide)

-- `Sym2.other_spec'` idx 4: necessary (a = 1, z = s(0,0))
theorem w4_176 : ¬ indep0% Sym2.other_spec' 4 := fun h => by
  have := @h ℕ _ 1 s(0, 0)
  simp at this

-- `Sym2.other_eq_other'` idx 4: necessary (a = 1, z = s(0,0))
theorem w4_177 : ¬ indep0% Sym2.other_eq_other' 4 := fun h => by
  have := @h ℕ _ 1 s(0, 0)
  simp at this

-- `Sym2.other_mem'` idx 4: necessary (a = 1, z = s(0,0))
theorem w4_178 : ¬ indep0% Sym2.other_mem' 4 := fun h => by
  have := @h ℕ _ 1 s(0, 0)
  simp at this

-- `Sym2.other_invol'` idx 4: necessary (a = 1, z = s(0,0))
theorem w4_179 : ¬ indep0% Sym2.other_invol' 4 := fun h => by
  have := @h ℕ _ 1 s(0, 0)
  simp at this

-- `Sym2.other_invol'` idx 5: removable (dependent, derivable: the other element always lies in z, by Sym2.other_mem')
theorem w4_180 : indep% Sym2.other_invol' 5 := by
  intro α _ a z ha; exact Sym2.other_mem' ha

-- `Sym2.other_invol` idx 3: necessary (a = 1, z = s(0,0))
theorem w4_181 : ¬ indep0% Sym2.other_invol 3 := fun h => by
  have := @h ℕ 1 s(0, 0)
  simp at this

-- `Sym2.other_invol` idx 4: removable (dependent, derivable: the other element always lies in z, by Sym2.other_mem)
theorem w4_182 : indep% Sym2.other_invol 4 := by
  intro α a z ha; exact Sym2.other_mem ha

-- `Sym2.instNontrivial` idx 1: necessary (α = Unit)
theorem w4_183 : ¬ drop0% Sym2.instNontrivial 1 := fun h => by
  have := @h Unit
  obtain ⟨x, y, hxy⟩ := this.exists_pair_ne
  apply hxy
  induction x using Sym2.ind
  induction y using Sym2.ind
  rfl
