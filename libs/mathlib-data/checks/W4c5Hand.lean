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

namespace W4c5
macro "zt" : tactic => `(tactic| first | decide | rfl | (simp; done) | (norm_num; done) | (simp [ZMod.val, ZMod.cast]; done) | omega)
end W4c5
open W4c5
-- `ZMod.val_lt` idx 1
theorem c5_148 : ¬ drop0% ZMod.val_lt 1 := fun h => absurd (h (n := 0) 0) (by zt)
-- `ZMod.val_le` idx 1
theorem c5_149 : ¬ drop0% ZMod.val_le 1 := fun h => absurd (h (n := 0) 1) (by zt)
-- `ZMod.cast_eq_val` idx 3
theorem c5_150 : ¬ drop0% ZMod.cast_eq_val 3 := fun h => absurd (h (n := 0) (R := ℤ) (-1)) (by zt)
-- `ZMod.natCast_rightInverse` idx 1
theorem c5_151 : ¬ drop0% ZMod.natCast_rightInverse 1 := fun h => absurd (h (n := 0) (-1)) (by zt)
-- `ZMod.natCast_zmod_surjective` idx 1
theorem c5_152 : ¬ drop0% ZMod.natCast_zmod_surjective 1 := fun h => by
  obtain ⟨k, hk⟩ := h (n := 0) (-1 : ℤ); change (k : ℤ) = -1 at hk; omega
-- `ZMod.natCast_val` idx 3
theorem c5_153 : ¬ drop0% ZMod.natCast_val 3 := fun h => absurd (h (n := 0) (R := ℤ) (-1)) (by zt)
-- `ZMod.cast_add` idx 4
theorem c5_154 : ¬ drop0% ZMod.cast_add 4 := fun h => absurd (h (n := 3) (R := ℤ) (m := 3) dvd_rfl 2 2) (by zt)
-- `ZMod.cast_add` idx 5
theorem c5_155 : ¬ drop0% ZMod.cast_add 5 := fun h => absurd (h (n := 3) (R := ℤ) (m := 0) 2 2) (by zt)
-- `ZMod.cast_mul` idx 4
theorem c5_156 : ¬ drop0% ZMod.cast_mul 4 := fun h => absurd (h (n := 3) (R := ℤ) (m := 3) dvd_rfl 2 2) (by zt)
-- `ZMod.cast_mul` idx 5
theorem c5_157 : ¬ drop0% ZMod.cast_mul 5 := fun h => absurd (h (n := 3) (R := ℤ) (m := 0) 2 2) (by zt)
-- `ZMod.castHom_apply` idx 4
theorem c5_158 : ¬ indep0% ZMod.castHom_apply 4 := fun h =>
  absurd (@CharP.cast_eq_zero_iff ℤ _ 1 (h (n := 1) (R := ℤ) (m := 1) (h := dvd_rfl) 0) 1).2 (by simp)
-- `ZMod.castHom_apply` idx 5
theorem c5_159 : ¬ indep0% ZMod.castHom_apply 5 := fun h => absurd (h (n := 1) (R := ℤ) (m := 0) 0) (by zt)
-- `ZMod.cast_sub` idx 4
theorem c5_160 : ¬ drop0% ZMod.cast_sub 4 := fun h => absurd (h (n := 3) (R := ℤ) (m := 3) dvd_rfl 0 1) (by zt)
-- `ZMod.cast_sub` idx 5
theorem c5_161 : ¬ drop0% ZMod.cast_sub 5 := fun h => absurd (h (n := 3) (R := ℤ) (m := 0) 0 1) (by zt)
-- `ZMod.cast_neg` idx 4
theorem c5_162 : ¬ drop0% ZMod.cast_neg 4 := fun h => absurd (h (n := 3) (R := ℤ) (m := 3) dvd_rfl 1) (by zt)
-- `ZMod.cast_neg` idx 5
theorem c5_163 : ¬ drop0% ZMod.cast_neg 5 := fun h => absurd (h (n := 3) (R := ℤ) (m := 0) 1) (by zt)
-- `ZMod.cast_pow` idx 4
theorem c5_164 : ¬ drop0% ZMod.cast_pow 4 := fun h => absurd (h (n := 3) (R := ℤ) (m := 3) dvd_rfl 2 2) (by zt)
-- `ZMod.cast_pow` idx 5
theorem c5_165 : ¬ drop0% ZMod.cast_pow 5 := fun h => absurd (h (n := 3) (R := ℤ) (m := 0) 2 2) (by zt)
-- `ZMod.cast_natCast` idx 5
theorem c5_166 : ¬ drop0% ZMod.cast_natCast 5 := fun h => absurd (h (n := 2) (R := ℤ) (m := 0) 2) (by zt)
-- `ZMod.cast_intCast` idx 5
theorem c5_167 : ¬ drop0% ZMod.cast_intCast 5 := fun h => absurd (h (n := 2) (R := ℤ) (m := 0) 2) (by zt)
-- `ZMod.cast_add'` idx 3
theorem c5_168 : ¬ drop0% ZMod.cast_add' 3 := fun h => absurd (h (n := 3) (R := ℤ) 2 2) (by zt)
-- `ZMod.cast_mul'` idx 3
theorem c5_169 : ¬ drop0% ZMod.cast_mul' 3 := fun h => absurd (h (n := 3) (R := ℤ) 2 2) (by zt)
-- `ZMod.cast_sub'` idx 3
theorem c5_170 : ¬ drop0% ZMod.cast_sub' 3 := fun h => absurd (h (n := 3) (R := ℤ) 0 1) (by zt)
-- `ZMod.cast_pow'` idx 3
theorem c5_171 : ¬ drop0% ZMod.cast_pow' 3 := fun h => absurd (h (n := 3) (R := ℤ) 2 2) (by zt)
-- `ZMod.ringEquivOfPrime_eq_ringEquiv` idx 4: removable (dependent, derivable: ring of prime order has that characteristic)
theorem c5_174 : indep% ZMod.ringEquivOfPrime_eq_ringEquiv 4 := by
  intro R _ _ p hp hR
  have : Nontrivial R := Fintype.one_lt_card_iff_nontrivial.1 (hR ▸ hp.one_lt)
  exact (CharP.charP_iff_prime_eq_zero hp).2 (hR ▸ Nat.cast_card_eq_zero R)
-- `ZMod.ringEquivOfPrime_eq_ringEquiv` idx 5
theorem c5_175 : ¬ indep0% ZMod.ringEquivOfPrime_eq_ringEquiv 5 := fun h =>
  absurd (h (ZMod 4) (p := 4) (ZMod.card 4)) (by decide)
-- `ZMod.ringEquivCongr_ringEquivCongr_apply` idx 3
theorem c5_177 : ¬ indep0% ZMod.ringEquivCongr_ringEquivCongr_apply 3 := fun h =>
  absurd (h (a := 0) (b := 1) (c := 1) rfl 0) (by decide)
-- `ZMod.ringEquivCongr_ringEquivCongr_apply` idx 4
theorem c5_178 : ¬ indep0% ZMod.ringEquivCongr_ringEquivCongr_apply 4 := fun h =>
  absurd (h (a := 0) (b := 0) (c := 1) rfl 0) (by decide)
-- `ZMod.ringEquivCongr_val` idx 2
theorem c5_179 : ¬ indep0% ZMod.ringEquivCongr_val 2 := fun h => absurd (h (a := 0) (b := 1) 0) (by decide)
-- `ZMod.natCast_eq_iff` idx 3
theorem c5_180 : ¬ drop0% ZMod.natCast_eq_iff 3 := fun h => absurd ((h 0 1 (-1)).2 ⟨0, by zt⟩) (by zt)
-- `ZMod.intCast_eq_iff` idx 3
theorem c5_181 : ¬ drop0% ZMod.intCast_eq_iff 3 := fun h => absurd ((h 0 1 (-1)).2 ⟨0, by zt⟩) (by zt)
-- `ZMod.cast_injective_of_le` idx 2
theorem c5_182 : ¬ drop0% ZMod.cast_injective_of_le 2 := fun h =>
  absurd (@h 0 1 (by decide) (0 : ZMod 0) (1 : ZMod 0) (by zt)) (by zt)
-- `ZMod.cast_zmod_eq_zero_iff_of_le` idx 2
theorem c5_183 : ¬ drop0% ZMod.cast_zmod_eq_zero_iff_of_le 2 := fun h =>
  absurd ((h (m := 0) (n := 1) (by decide) 1).1 (by zt)) (by zt)
-- `ZMod.cast_zmod_eq_zero_iff_of_le` idx 3
theorem c5_184 : ¬ drop0% ZMod.cast_zmod_eq_zero_iff_of_le 3 := fun h =>
  absurd ((h (m := 2) (n := 1) 1).1 (by zt)) (by zt)
-- `ZMod.val_injective` idx 1
theorem c5_185 : ¬ drop0% ZMod.val_injective 1 := fun h =>
  absurd (@h 0 (1 : ZMod 0) (-1 : ZMod 0) (by zt)) (by zt)
-- `ZMod.val_add` idx 1
theorem c5_186 : ¬ drop0% ZMod.val_add 1 := fun h => absurd (h (n := 0) 1 (-1)) (by zt)
-- `ZMod.val_add_of_lt` idx 3
theorem c5_187 : ¬ drop0% ZMod.val_add_of_lt 3 := fun h => absurd (h (n := 2) (a := 1) (b := 1)) (by zt)
-- `ZMod.val_add_val_of_le` idx 1
theorem c5_188 : ¬ drop0% ZMod.val_add_val_of_le 1 := fun h =>
  absurd (h (n := 0) (a := 1) (b := -1) (by zt)) (by zt)
-- `ZMod.val_add_val_of_le` idx 4
theorem c5_189 : ¬ drop0% ZMod.val_add_val_of_le 4 := fun h => absurd (h (n := 2) (a := 0) (b := 0)) (by zt)
-- `ZMod.val_add_of_le` idx 1
theorem c5_190 : ¬ drop0% ZMod.val_add_of_le 1 := fun h =>
  absurd (h (n := 0) (a := 1) (b := -1) (by zt)) (by zt)
-- `ZMod.val_add_of_le` idx 4
theorem c5_191 : ¬ drop0% ZMod.val_add_of_le 4 := fun h => absurd (h (n := 2) (a := 1) (b := 0)) (by zt)
-- `ZMod.val_mul_of_lt` idx 3
theorem c5_192 : ¬ drop0% ZMod.val_mul_of_lt 3 := fun h => absurd (h (n := 3) (a := 2) (b := 2)) (by zt)
-- `ZMod.val_mul_iff_lt` idx 1
theorem c5_193 : ¬ drop0% ZMod.val_mul_iff_lt 1 := fun h => absurd ((h (n := 0) 1 1).1 (by zt)) (by zt)
-- `ZMod.mul_inv_of_unit` idx 2
theorem c5_194 : ¬ drop0% ZMod.mul_inv_of_unit 2 := fun h => absurd (h (n := 2) 0) (by zt)
-- `ZMod.inv_mul_of_unit` idx 2
theorem c5_195 : ¬ drop0% ZMod.inv_mul_of_unit 2 := fun h => absurd (h (n := 2) 0) (by zt)
-- `ZMod.inv_eq_of_mul_eq_one` idx 3
theorem c5_196 : ¬ drop0% ZMod.inv_eq_of_mul_eq_one 3 := fun h => absurd (h 2 0 1) (by rw [ZMod.inv_zero]; decide)
-- `ZMod.inv_mul_eq_one_of_isUnit` idx 2
theorem c5_197 : ¬ drop0% ZMod.inv_mul_eq_one_of_isUnit 2 := fun h => absurd ((h (n := 2) (a := 0) 0).2 rfl) (by zt)
-- `ZMod.add_self_eq_zero_iff_eq_zero` idx 1
theorem c5_198 : ¬ drop0% ZMod.add_self_eq_zero_iff_eq_zero 1 := fun h => absurd ((h (n := 2) (a := 1)).1 (by zt)) (by zt)
-- `ZMod.ne_neg_self` idx 1
theorem c5_199 : ¬ drop0% ZMod.ne_neg_self 1 := fun h => h (n := 2) (a := 1) (by zt) (by zt)
-- `ZMod.ne_neg_self` idx 3
theorem c5_200 : ¬ drop0% ZMod.ne_neg_self 3 := fun h => h (n := 1) odd_one (a := 0) neg_zero.symm
-- `ZMod.val_eq_one` idx 1
theorem c5_201 : ¬ drop0% ZMod.val_eq_one 1 := fun h => absurd ((h (n := 1) 0).2 (by zt)) (by zt)
-- `ZMod.val_cast_zmod_lt` idx 1
theorem c5_202 : ¬ drop0% ZMod.val_cast_zmod_lt 1 := fun h => absurd (h (m := 0) 2 (0 : ZMod 0)) (by zt)
-- `ZMod.neg_val'` idx 1
theorem c5_204 : ¬ drop0% ZMod.neg_val' 1 := fun h => absurd (h (n := 0) 1) (by zt)
-- `ZMod.neg_val` idx 1
theorem c5_205 : ¬ drop0% ZMod.neg_val 1 := fun h => absurd (h (n := 0) 1) (by zt)
-- `ZMod.val_neg_of_ne_zero` idx 1
theorem c5_206 : ¬ drop0% ZMod.val_neg_of_ne_zero 1 := fun h =>
  absurd (@h 0 (1 : ZMod 0) ⟨by zt⟩) (by zt)
-- `ZMod.val_neg_of_ne_zero` idx 3
theorem c5_207 : ¬ drop0% ZMod.val_neg_of_ne_zero 3 := fun h => absurd (h (n := 1) 0) (by zt)
-- `ZMod.val_sub` idx 1
theorem c5_208 : ¬ drop0% ZMod.val_sub 1 := fun h => absurd (h (n := 0) (a := -1) (b := 1) (by zt)) (by zt)
-- `ZMod.val_sub` idx 4
theorem c5_209 : ¬ drop0% ZMod.val_sub 4 := fun h => absurd (h (n := 2) (a := 0) (b := 1)) (by zt)
-- `ZMod.val_cast_eq_val_of_lt` idx 2
theorem c5_210 : ¬ drop0% ZMod.val_cast_eq_val_of_lt 2 := fun h => absurd (h (m := 0) (n := 3) (a := -1) (by zt)) (by zt)
-- `ZMod.val_cast_eq_val_of_lt` idx 4
theorem c5_211 : ¬ drop0% ZMod.val_cast_eq_val_of_lt 4 := fun h => absurd (h (m := 3) (n := 2) (a := 2)) (by zt)
-- `ZMod.cast_cast_zmod_of_le` idx 2
theorem c5_212 : ¬ drop0% ZMod.cast_cast_zmod_of_le 2 := fun h => absurd (h (m := 0) (n := 1) (by decide) 1) (by zt)
-- `ZMod.cast_cast_zmod_of_le` idx 3
theorem c5_213 : ¬ drop0% ZMod.cast_cast_zmod_of_le 3 := fun h => absurd (h (m := 2) (n := 1) 1) (by zt)
-- `ZMod.val_pow` idx 4
theorem c5_215 : ¬ drop0% ZMod.val_pow 4 := fun h => absurd (h (m := 2) (n := 3) (a := 2) (ilt := ⟨by decide⟩)) (by zt)

namespace W4c5
open Stream'
/-- a weak sequence that thinks forever -/
def nv : WSeq ℕ := WSeq.flatten (Computation.empty _)
theorem nv_nt : ¬ (WSeq.destruct nv).Terminates := by
  rintro ⟨⟨b, hb⟩⟩
  rw [nv, WSeq.destruct_flatten] at hb
  obtain ⟨a, ha, -⟩ := Computation.exists_of_mem_bind hb
  exact Computation.notMem_empty a ha
theorem nv_head : ¬ (WSeq.head nv).Terminates := fun h => nv_nt ((WSeq.head_terminates_iff nv).1 h)
theorem nv_get (n : ℕ) : ¬ (WSeq.get? nv n).Terminates := fun h => nv_head (WSeq.head_terminates_of_get?_terminates h)
theorem nv_np : ¬ nv.Productive := fun h => nv_get 0 ((WSeq.productive_iff nv).1 h 0)
theorem nil_prod : (WSeq.nil : WSeq ℕ).Productive := (WSeq.productive_iff _).2 fun n => by
  rw [WSeq.get?, WSeq.dropn_nil, WSeq.head_nil]; infer_instance
@[simp] theorem nlr_nil_cons {α β} {R : α → β → Prop} {b : β} {t : WSeq β} : ¬ WSeq.LiftRel R WSeq.nil (WSeq.cons b t) :=
  fun H => by obtain ⟨a, ha, -⟩ := WSeq.exists_of_liftRel_right H (WSeq.mem_cons t b); exact WSeq.notMem_nil a ha
@[simp] theorem nlr_cons_nil {α β} {R : α → β → Prop} {a : α} {s : WSeq α} : ¬ WSeq.LiftRel R (WSeq.cons a s) WSeq.nil :=
  fun H => by obtain ⟨b, hb, -⟩ := WSeq.exists_of_liftRel_left H (WSeq.mem_cons s a); exact WSeq.notMem_nil b hb
theorem lrT : WSeq.LiftRel (fun _ _ : ℕ => True) (WSeq.cons 0 WSeq.nil) (WSeq.cons 0 WSeq.nil) :=
  (WSeq.liftRel_cons _ _ _ _ _).2 ⟨trivial, WSeq.liftRel_nil _⟩
end W4c5
open W4c5 Stream'
-- `Stream'.WSeq.head_terminates_of_head_tail_terminates` idx 2
theorem c5_67 : ¬ drop0% Stream'.WSeq.head_terminates_of_head_tail_terminates 2 := fun h => nv_head (h nv)
-- `Stream'.WSeq.destruct_some_of_destruct_tail_some` idx 3
theorem c5_68 : ¬ drop0% Stream'.WSeq.destruct_some_of_destruct_tail_some 3 := fun h => by
  obtain ⟨a, ha⟩ := h (s := (WSeq.nil : WSeq ℕ)) (a := (0, WSeq.nil)); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.head_some_of_head_tail_some` idx 3
theorem c5_69 : ¬ drop0% Stream'.WSeq.head_some_of_head_tail_some 3 := fun h => by
  obtain ⟨a, ha⟩ := h (s := (WSeq.nil : WSeq ℕ)) (a := 0); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.head_some_of_get?_some` idx 4
theorem c5_70 : ¬ drop0% Stream'.WSeq.head_some_of_get?_some 4 := fun h => by
  obtain ⟨a, ha⟩ := h (s := (WSeq.nil : WSeq ℕ)) (a := 0) (n := 0); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.get?_terminates_le` idx 4
theorem c5_71 : ¬ drop0% Stream'.WSeq.get?_terminates_le 4 := fun h => by
  have := h (s := WSeq.cons 0 nv) (m := 1) (n := 0) (by
    rw [show WSeq.get? (WSeq.cons 0 nv) 0 = WSeq.head (WSeq.cons 0 nv) from rfl, WSeq.head_cons]; infer_instance)
  rw [← WSeq.get?_tail, WSeq.tail_cons] at this; exact nv_get 0 this
-- `Stream'.WSeq.get?_terminates_le` idx 5
theorem c5_72 : ¬ drop0% Stream'.WSeq.get?_terminates_le 5 := fun h => nv_get 0 (h (s := nv) (le_refl 0))
-- `Stream'.WSeq.head_terminates_of_get?_terminates` idx 3
theorem c5_73 : ¬ drop0% Stream'.WSeq.head_terminates_of_get?_terminates 3 := fun h => nv_head (h (s := nv) (n := 0))
-- `Stream'.WSeq.destruct_terminates_of_get?_terminates` idx 3
theorem c5_74 : ¬ drop0% Stream'.WSeq.destruct_terminates_of_get?_terminates 3 := fun h => nv_nt (h (s := nv) (n := 0))
-- `Stream'.WSeq.mem_rec_on` idx 4
theorem c5_75 : ¬ drop0% Stream'.WSeq.mem_rec_on 4 := fun h =>
  WSeq.notMem_nil 0 (h (C := fun s => (0 : ℕ) ∈ s) (a := 0) (s := WSeq.nil)
    (fun b s' hb => (WSeq.mem_cons_iff _ _).2 hb) (fun s hs => (WSeq.mem_think s 0).2 hs))
-- `Stream'.WSeq.mem_rec_on` idx 5
theorem c5_76 : ¬ drop0% Stream'.WSeq.mem_rec_on 5 := fun h =>
  h (C := fun _ => False) (a := 0) (s := WSeq.cons 0 WSeq.nil) (WSeq.mem_cons _ _) (fun _ h => h)
-- `Stream'.WSeq.mem_rec_on` idx 6
theorem c5_77 : ¬ drop0% Stream'.WSeq.mem_rec_on 6 := fun h => by
  obtain ⟨b, s', e⟩ := h (C := fun s => ∃ b s', s = WSeq.cons b s') (a := 0) (s := WSeq.think (WSeq.cons 0 WSeq.nil))
    ((WSeq.mem_think _ _).2 (WSeq.mem_cons _ _)) (fun b s' _ => ⟨b, s', rfl⟩)
  have := congrArg Seq.destruct e; rw [WSeq.seq_destruct_think, WSeq.seq_destruct_cons] at this
  cases this
-- `Stream'.WSeq.eq_or_mem_iff_mem` idx 5
theorem c5_78 : ¬ drop0% Stream'.WSeq.eq_or_mem_iff_mem 5 := fun h =>
  WSeq.notMem_nil 0 ((h (s := WSeq.nil) (a := 0) (a' := 0) (s' := WSeq.nil)).2 (Or.inl rfl))
-- `Stream'.WSeq.mem_cons_of_mem` idx 4
theorem c5_79 : ¬ drop0% Stream'.WSeq.mem_cons_of_mem 4 := fun h => by
  have := h (s := (WSeq.nil : WSeq ℕ)) 0 (a := 1); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.mem_of_mem_tail` idx 3
theorem c5_80 : ¬ drop0% Stream'.WSeq.mem_of_mem_tail 3 := fun h => WSeq.notMem_nil 0 (h (s := WSeq.nil) (a := 0))
-- `Stream'.WSeq.mem_of_mem_dropn` idx 4
theorem c5_81 : ¬ drop0% Stream'.WSeq.mem_of_mem_dropn 4 := fun h => WSeq.notMem_nil 0 (h (s := WSeq.nil) (a := 0) (n := 0))
-- `Stream'.WSeq.get?_mem` idx 4
theorem c5_82 : ¬ drop0% Stream'.WSeq.get?_mem 4 := fun h => WSeq.notMem_nil 0 (h (s := WSeq.nil) (a := 0) (n := 0))
-- `Stream'.WSeq.exists_get?_of_mem` idx 3
theorem c5_83 : ¬ drop0% Stream'.WSeq.exists_get?_of_mem 3 := fun h => by
  obtain ⟨n, hn⟩ := h (s := (WSeq.nil : WSeq ℕ)) (a := 0); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.exists_dropn_of_mem` idx 3
theorem c5_84 : ¬ drop0% Stream'.WSeq.exists_dropn_of_mem 3 := fun h => by
  obtain ⟨n, s', hn⟩ := h (s := (WSeq.nil : WSeq ℕ)) (a := 0); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.head_terminates_of_mem` idx 3
theorem c5_85 : ¬ drop0% Stream'.WSeq.head_terminates_of_mem 3 := fun h => nv_head (h (s := nv) (a := 0))
-- `Stream'.WSeq.of_mem_append` idx 4
theorem c5_86 : ¬ drop0% Stream'.WSeq.of_mem_append 4 := fun h => by
  have := h (s₁ := (WSeq.nil : WSeq ℕ)) (s₂ := WSeq.nil) (a := 0); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.mem_append_left` idx 4
theorem c5_87 : ¬ drop0% Stream'.WSeq.mem_append_left 4 := fun h => by
  have := h (s₁ := (WSeq.nil : WSeq ℕ)) (s₂ := WSeq.nil) (a := 0); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.exists_of_mem_map` idx 5
theorem c5_88 : ¬ drop0% Stream'.WSeq.exists_of_mem_map 5 := fun h => by
  obtain ⟨a, ha, -⟩ := h (f := (id : ℕ → ℕ)) (b := 0) (s := WSeq.nil); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.mem_map` idx 5
theorem c5_89 : ¬ drop0% Stream'.WSeq.mem_map 5 := fun h => by
  have := h (id : ℕ → ℕ) (a := 0) (s := WSeq.nil); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.exists_of_mem_join` idx 3
theorem c5_90 : ¬ drop0% Stream'.WSeq.exists_of_mem_join 3 := fun h => by
  obtain ⟨s, hs, -⟩ := h (a := (0 : ℕ)) (S := WSeq.nil); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.exists_of_mem_bind` idx 5
theorem c5_91 : ¬ drop0% Stream'.WSeq.exists_of_mem_bind 5 := fun h => by
  obtain ⟨a, ha, -⟩ := h (s := (WSeq.nil : WSeq ℕ)) (f := fun _ => (WSeq.nil : WSeq ℕ)) (b := 0); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.Productive.get?_terminates` idx 2
theorem c5_94 : ¬ drop0% Stream'.WSeq.Productive.get?_terminates 2 := fun h => nv_get 0 (h (s := nv) 0)
-- `Stream'.WSeq.get?_terminates` idx 2
theorem c5_95 : ¬ drop0% Stream'.WSeq.get?_terminates 2 := fun h => nv_get 0 (h nv 0)
-- `Stream'.WSeq.head_terminates` idx 2
theorem c5_96 : ¬ drop0% Stream'.WSeq.head_terminates 2 := fun h => nv_head (h nv)
-- `Stream'.WSeq.productive_tail` idx 2
theorem c5_97 : ¬ drop0% Stream'.WSeq.productive_tail 2 := fun h => by
  have := (WSeq.productive_iff _).1 (h nv) 0; rw [WSeq.get?_tail] at this; exact nv_get 1 this
-- `Stream'.WSeq.productive_dropn` idx 2
theorem c5_98 : ¬ drop0% Stream'.WSeq.productive_dropn 2 := fun h => nv_np (h nv 0)
-- `Stream'.WSeq.productive_congr` idx 3
theorem c5_99 : ¬ drop0% Stream'.WSeq.productive_congr 3 := fun h => nv_np ((h (s := WSeq.nil) (t := nv)).1 nil_prod)
-- `Stream'.WSeq.LiftRelO.imp` idx 6
theorem c5_100 : ¬ drop0% Stream'.WSeq.LiftRelO.imp 6 := fun h => by
  have := h (R := fun _ _ : ℕ => True) (S := fun _ _ : ℕ => False) (C := fun _ _ => True) (D := fun _ _ => True)
    (fun _ _ h => h) (o := some (0, WSeq.nil)) (p := some (0, WSeq.nil)) ⟨trivial, trivial⟩; simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.LiftRelO.imp` idx 7
theorem c5_101 : ¬ drop0% Stream'.WSeq.LiftRelO.imp 7 := fun h => by
  have := h (R := fun _ _ : ℕ => True) (S := fun _ _ : ℕ => True) (C := fun _ _ => True) (D := fun _ _ => False)
    (fun _ _ h => h) (o := some (0, WSeq.nil)) (p := some (0, WSeq.nil)) ⟨trivial, trivial⟩; simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.LiftRelO.imp` idx 10
theorem c5_102 : ¬ drop0% Stream'.WSeq.LiftRelO.imp 10 := fun h => by
  have := h (R := fun _ _ : ℕ => True) (S := fun _ _ : ℕ => True) (C := fun _ _ => True) (D := fun _ _ => True)
    (fun _ _ h => h) (fun _ _ h => h) (o := some (0, WSeq.nil)) (p := none); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.LiftRelO.imp_right` idx 5
theorem c5_103 : ¬ drop0% Stream'.WSeq.LiftRelO.imp_right 5 := fun h => by
  have := h (fun _ _ : ℕ => True) (C := fun _ _ => True) (D := fun _ _ => False)
    (o := some (0, WSeq.nil)) (p := some (0, WSeq.nil)) ⟨trivial, trivial⟩; simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.LiftRelO.imp_right` idx 8
theorem c5_104 : ¬ drop0% Stream'.WSeq.LiftRelO.imp_right 8 := fun h => by
  have := h (fun _ _ : ℕ => True) (C := fun _ _ => True) (D := fun _ _ => True) (fun _ _ h => h)
    (o := some (0, WSeq.nil)) (p := none); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.BisimO.imp` idx 3
theorem c5_105 : ¬ drop0% Stream'.WSeq.BisimO.imp 3 := fun h => by
  have := h (R := fun _ _ : WSeq ℕ => True) (S := fun _ _ => False)
    (o := some (0, WSeq.nil)) (p := some (0, WSeq.nil)) ⟨rfl, trivial⟩; simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.BisimO.imp` idx 6
theorem c5_106 : ¬ drop0% Stream'.WSeq.BisimO.imp 6 := fun h => by
  have := h (R := fun _ _ : WSeq ℕ => True) (S := fun _ _ => True) (fun _ _ h => h)
    (o := some (0, WSeq.nil)) (p := none); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.liftRel_destruct` idx 5
theorem c5_107 : ¬ drop0% Stream'.WSeq.liftRel_destruct 5 := fun h => by
  have := h (R := fun _ _ : ℕ => True) (s := WSeq.nil) (t := WSeq.cons 0 WSeq.nil); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.LiftRel.swap_lem` idx 5
theorem c5_108 : ¬ drop0% Stream'.WSeq.LiftRel.swap_lem 5 := fun h =>
  nlr_cons_nil (h (R := fun _ _ : ℕ => True) (s1 := WSeq.nil) (s2 := WSeq.cons 0 WSeq.nil))
-- `Stream'.WSeq.LiftRelO.refl` idx 2
theorem c5_109 : ¬ drop0% Stream'.WSeq.LiftRelO.refl 2 := fun h => by
  have := (h (fun _ _ : ℕ => False)).refl (some (0, WSeq.nil)); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.LiftRel.refl` idx 2
theorem c5_110 : ¬ drop0% Stream'.WSeq.LiftRel.refl 2 := fun h => by
  have := (h (fun _ _ : ℕ => False)).refl (WSeq.cons 0 WSeq.nil); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.LiftRel.symm` idx 2
theorem c5_111 : ¬ drop0% Stream'.WSeq.LiftRel.symm 2 := fun h => by
  have := (h (fun a b : ℕ => a < b)).symm (WSeq.cons 0 WSeq.nil) (WSeq.cons 1 WSeq.nil)
    ((WSeq.liftRel_cons _ _ _ _ _).2 ⟨by decide, WSeq.liftRel_nil _⟩); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.LiftRel.trans` idx 2
theorem c5_112 : ¬ drop0% Stream'.WSeq.LiftRel.trans 2 := fun h => by
  have := (h (fun a b : ℕ => b = a + 1)).trans (WSeq.cons 0 WSeq.nil) (WSeq.cons 1 WSeq.nil) (WSeq.cons 2 WSeq.nil)
    ((WSeq.liftRel_cons _ _ _ _ _).2 ⟨rfl, WSeq.liftRel_nil _⟩) ((WSeq.liftRel_cons _ _ _ _ _).2 ⟨rfl, WSeq.liftRel_nil _⟩); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.LiftRel.equiv` idx 2
theorem c5_113 : ¬ drop0% Stream'.WSeq.LiftRel.equiv 2 := fun h => by
  have := (h (fun _ _ : ℕ => False)).refl (WSeq.cons 0 WSeq.nil); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.Equiv.symm` idx 3
theorem c5_114 : ¬ drop0% Stream'.WSeq.Equiv.symm 3 := fun h =>
  nlr_cons_nil (h (s := (WSeq.nil : WSeq ℕ)) (t := WSeq.cons 0 WSeq.nil))
-- `Stream'.WSeq.Equiv.trans` idx 4
theorem c5_115 : ¬ drop0% Stream'.WSeq.Equiv.trans 4 := fun h =>
  nlr_cons_nil (h (s := WSeq.cons (0 : ℕ) WSeq.nil) (t := WSeq.nil) (u := WSeq.nil) (WSeq.Equiv.refl _))
-- `Stream'.WSeq.Equiv.trans` idx 5
theorem c5_116 : ¬ drop0% Stream'.WSeq.Equiv.trans 5 := fun h =>
  nlr_nil_cons (h (s := (WSeq.nil : WSeq ℕ)) (t := WSeq.nil) (u := WSeq.cons 0 WSeq.nil) (WSeq.Equiv.refl _))
-- `Stream'.WSeq.destruct_congr` idx 3
theorem c5_117 : ¬ drop0% Stream'.WSeq.destruct_congr 3 := fun h => by
  have := h (s := (WSeq.nil : WSeq ℕ)) (t := WSeq.cons 0 WSeq.nil); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.liftRel_dropn_destruct` idx 5
theorem c5_118 : ¬ drop0% Stream'.WSeq.liftRel_dropn_destruct 5 := fun h => by
  have := h (R := fun _ _ : ℕ => True) (s := WSeq.nil) (t := WSeq.cons 0 WSeq.nil) 0; simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.exists_of_liftRel_left` idx 5
theorem c5_119 : ¬ drop0% Stream'.WSeq.exists_of_liftRel_left 5 := fun h => by
  obtain ⟨b, hb, -⟩ := h (R := fun _ _ : ℕ => True) (s := WSeq.cons 0 WSeq.nil) (t := WSeq.nil) (WSeq.mem_cons _ _); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.exists_of_liftRel_left` idx 7
theorem c5_120 : ¬ drop0% Stream'.WSeq.exists_of_liftRel_left 7 := fun h => by
  obtain ⟨b, hb, -⟩ := h (R := fun _ _ : ℕ => True) (s := WSeq.nil) (t := WSeq.nil) (WSeq.liftRel_nil _) (a := 0); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.exists_of_liftRel_right` idx 5
theorem c5_121 : ¬ drop0% Stream'.WSeq.exists_of_liftRel_right 5 := fun h => by
  obtain ⟨b, hb, -⟩ := h (R := fun _ _ : ℕ => True) (s := WSeq.nil) (t := WSeq.cons 0 WSeq.nil) (WSeq.mem_cons _ _); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.exists_of_liftRel_right` idx 7
theorem c5_122 : ¬ drop0% Stream'.WSeq.exists_of_liftRel_right 7 := fun h => by
  obtain ⟨b, hb, -⟩ := h (R := fun _ _ : ℕ => True) (s := WSeq.nil) (t := WSeq.nil) (WSeq.liftRel_nil _) (b := 0); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.cons_congr` idx 4
theorem c5_123 : ¬ drop0% Stream'.WSeq.cons_congr 4 := fun h => by
  have := h (s := (WSeq.nil : WSeq ℕ)) (t := WSeq.cons 0 WSeq.nil) 0; simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.think_congr` idx 3
theorem c5_124 : ¬ drop0% Stream'.WSeq.think_congr 3 := fun h => by
  have := h (s := (WSeq.nil : WSeq ℕ)) (t := WSeq.cons 0 WSeq.nil); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.head_congr` idx 3
theorem c5_125 : ¬ drop0% Stream'.WSeq.head_congr 3 := fun h => by
  have := (h (s := (WSeq.nil : WSeq ℕ)) (t := WSeq.cons 0 WSeq.nil) none).1; simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.flatten_equiv` idx 3
theorem c5_126 : ¬ drop0% Stream'.WSeq.flatten_equiv 3 := fun h => by
  have := h (c := Computation.pure (WSeq.nil : WSeq ℕ)) (s := WSeq.cons 0 WSeq.nil); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.liftRel_flatten` idx 5
theorem c5_127 : ¬ drop0% Stream'.WSeq.liftRel_flatten 5 := fun h => by
  have := h (R := fun _ _ : ℕ => True) (c1 := Computation.pure WSeq.nil) (c2 := Computation.pure (WSeq.cons 0 WSeq.nil)); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.flatten_congr` idx 3
theorem c5_128 : ¬ drop0% Stream'.WSeq.flatten_congr 3 := fun h => by
  have := h (c1 := Computation.pure (WSeq.nil : WSeq ℕ)) (c2 := Computation.pure (WSeq.cons 0 WSeq.nil)); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.tail_congr` idx 3
theorem c5_129 : ¬ drop0% Stream'.WSeq.tail_congr 3 := fun h => by
  have := h (s := (WSeq.nil : WSeq ℕ)) (t := WSeq.cons 0 (WSeq.cons 1 WSeq.nil)); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.dropn_congr` idx 3
theorem c5_130 : ¬ drop0% Stream'.WSeq.dropn_congr 3 := fun h => by
  have := h (s := (WSeq.nil : WSeq ℕ)) (t := WSeq.cons 0 WSeq.nil) 0; simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.get?_congr` idx 3
theorem c5_131 : ¬ drop0% Stream'.WSeq.get?_congr 3 := fun h => by
  have := (h (s := (WSeq.nil : WSeq ℕ)) (t := WSeq.cons 0 WSeq.nil) 0 none).1; simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.mem_congr` idx 3
theorem c5_132 : ¬ drop0% Stream'.WSeq.mem_congr 3 := fun h => by
  have := (h (s := (WSeq.nil : WSeq ℕ)) (t := WSeq.cons 0 WSeq.nil) 0).2 (WSeq.mem_cons _ _); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.Equiv.ext` idx 3
theorem c5_133 : ¬ drop0% Stream'.WSeq.Equiv.ext 3 := fun h =>
  nlr_nil_cons (h (s := (WSeq.nil : WSeq ℕ)) (t := WSeq.cons 0 WSeq.nil))
-- `Stream'.WSeq.liftRel_map` idx 10
theorem c5_134 : ¬ drop0% Stream'.WSeq.liftRel_map 10 := fun h => by
  have := h (fun _ _ : ℕ => True) (fun _ _ : ℕ => True) (s1 := WSeq.nil) (s2 := WSeq.cons 0 WSeq.nil)
    (f1 := id) (f2 := id) (fun _ => trivial); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.liftRel_map` idx 11
theorem c5_135 : ¬ drop0% Stream'.WSeq.liftRel_map 11 := fun h => by
  have := h (fun _ _ : ℕ => True) (fun _ _ : ℕ => False) (s1 := WSeq.cons 0 WSeq.nil) (s2 := WSeq.cons 0 WSeq.nil)
    (f1 := id) (f2 := id) lrT; simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.map_congr` idx 5
theorem c5_136 : ¬ drop0% Stream'.WSeq.map_congr 5 := fun h => by
  have := h (id : ℕ → ℕ) (s := WSeq.nil) (t := WSeq.cons 0 WSeq.nil); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.liftRel_append` idx 7
theorem c5_137 : ¬ drop0% Stream'.WSeq.liftRel_append 7 := fun h => by
  have := h (fun _ _ : ℕ => True) (s1 := WSeq.nil) (t1 := WSeq.cons 0 WSeq.nil) (s2 := WSeq.nil) (t2 := WSeq.nil)
    (WSeq.liftRel_nil _); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.liftRel_append` idx 8
theorem c5_138 : ¬ drop0% Stream'.WSeq.liftRel_append 8 := fun h => by
  have := h (fun _ _ : ℕ => True) (s1 := WSeq.nil) (t1 := WSeq.nil) (s2 := WSeq.nil) (t2 := WSeq.cons 0 WSeq.nil)
    (WSeq.liftRel_nil _); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.liftRel_join.lem` idx 9
theorem c5_141 : ¬ drop0% Stream'.WSeq.liftRel_join.lem 9 := fun h => by
  obtain ⟨b, hb, hr⟩ := h (fun _ _ : ℕ => True) (S := WSeq.nil) (T := WSeq.nil) (U := fun _ _ => True)
    (WSeq.liftRel_nil _) (fun _ _ _ => trivial) (a := some (0, WSeq.nil)); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *; subst hb; exact hr
-- `Stream'.WSeq.liftRel_join` idx 5
theorem c5_142 : ¬ drop0% Stream'.WSeq.liftRel_join 5 := fun h => by
  have := h (fun _ _ : ℕ => True) (S := WSeq.nil) (T := WSeq.cons (WSeq.cons 0 WSeq.nil) WSeq.nil); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.join_congr` idx 3
theorem c5_143 : ¬ drop0% Stream'.WSeq.join_congr 3 := fun h => by
  have := h (S := (WSeq.nil : WSeq (WSeq ℕ))) (T := WSeq.cons (WSeq.cons 0 WSeq.nil) WSeq.nil); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.liftRel_bind` idx 10
theorem c5_144 : ¬ drop0% Stream'.WSeq.liftRel_bind 10 := fun h => by
  have := h (fun _ _ : ℕ => True) (fun _ _ : ℕ => True) (s1 := WSeq.nil) (s2 := WSeq.cons 0 WSeq.nil)
    (f1 := fun _ => WSeq.cons 0 WSeq.nil) (f2 := fun _ => WSeq.cons 0 WSeq.nil) (fun _ => lrT); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.liftRel_bind` idx 11
theorem c5_145 : ¬ drop0% Stream'.WSeq.liftRel_bind 11 := fun h => by
  have := h (fun _ _ : ℕ => True) (fun _ _ : ℕ => True) (s1 := WSeq.cons 0 WSeq.nil) (s2 := WSeq.cons 0 WSeq.nil)
    (f1 := fun _ => WSeq.nil) (f2 := fun _ => WSeq.cons 0 WSeq.nil) lrT; simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.bind_congr` idx 6
theorem c5_146 : ¬ drop0% Stream'.WSeq.bind_congr 6 := fun h => by
  have := h (s1 := (WSeq.nil : WSeq ℕ)) (s2 := WSeq.cons 0 WSeq.nil)
    (f1 := fun _ => (WSeq.cons 0 WSeq.nil : WSeq ℕ)) (f2 := fun _ => WSeq.cons 0 WSeq.nil) (fun _ => WSeq.Equiv.refl _); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *
-- `Stream'.WSeq.bind_congr` idx 7
theorem c5_147 : ¬ drop0% Stream'.WSeq.bind_congr 7 := fun h => by
  have := h (s1 := WSeq.cons (0 : ℕ) WSeq.nil) (s2 := WSeq.cons 0 WSeq.nil)
    (f1 := fun _ => (WSeq.nil : WSeq ℕ)) (f2 := fun _ => WSeq.cons 0 WSeq.nil) (WSeq.Equiv.refl _); simp [WSeq.destruct_nil, WSeq.destruct_cons, WSeq.destruct_think, WSeq.head_nil, WSeq.head_cons, WSeq.tail_nil, WSeq.tail_cons, WSeq.map_nil, WSeq.map_cons, WSeq.join_nil, WSeq.join_cons, WSeq.nil_append, WSeq.cons_append, WSeq.flatten_pure, WSeq.liftRel_think_left, WSeq.liftRel_think_right, WSeq.liftRel_cons, Computation.liftRel_pure, WSeq.LiftRelO, WSeq.BisimO, WSeq.bind, WSeq.Equiv, WSeq.drop, WSeq.dropn_nil, WSeq.get?, WSeq.notMem_nil, WSeq.mem_cons_iff, Computation.mem_pure_iff, Computation.Equiv] at *

namespace W4c5
/-- the singleton vectors -/
abbrev v0 : List.Vector ℕ 1 := 0 ::ᵥ List.Vector.nil
abbrev v1 : List.Vector ℕ 1 := 1 ::ᵥ List.Vector.nil
abbrev v00 : List.Vector ℕ 2 := 0 ::ᵥ 0 ::ᵥ List.Vector.nil
theorem mem_v0 : 0 ∈ v0.toList := by simp
end W4c5
open W4c5
-- `List.Vector.ext` idx 4
theorem c5_16 : ¬ drop0% List.Vector.ext 4 := fun h => absurd (h (v := v0) (w := v1)) (by decide)
-- `List.Vector.pmap_cons` idx 7
theorem c5_17 : ¬ indep0% List.Vector.pmap_cons 7 := fun h =>
  h (p := fun _ : ℕ => False) (β := ℕ) (fun _ h => h.elim) 0 List.Vector.nil 0 (by simp)
-- `List.Vector.pmap_cons'` idx 7
theorem c5_18 : ¬ indep0% List.Vector.pmap_cons' 7 := fun h =>
  h (p := fun _ : ℕ => False) (β := ℕ) (fun _ h => h.elim) 0 List.Vector.nil (by simp)
-- `List.Vector.pmap_cons'` idx 8
theorem c5_19 : ¬ indep0% List.Vector.pmap_cons' 8 := fun h =>
  absurd (h (p := fun x : ℕ => x = 0) (β := ℕ) (fun _ _ => 0) 0 v1 rfl 1 (by simp)) (by decide)
-- `List.Vector.getElem_map` idx 6
theorem c5_20 : ¬ indep0% List.Vector.getElem_map 6 := fun h =>
  absurd (h (n := 0) (β := ℕ) (List.Vector.nil : List.Vector ℕ 0) id (i := 0)) (by decide)
-- `List.Vector.toList_pmap` idx 6
theorem c5_21 : ¬ indep0% List.Vector.toList_pmap 6 := fun h =>
  h (p := fun _ : ℕ => False) (β := ℕ) (fun _ h => h.elim) v0 0 mem_v0
-- `List.Vector.getElem_pmap` idx 6
theorem c5_22 : ¬ indep0% List.Vector.getElem_pmap 6 := fun h =>
  h (p := fun _ : ℕ => False) (β := ℕ) (fun _ h => h.elim) v0 (i := 0) (by decide) 0 mem_v0
-- `List.Vector.getElem_pmap` idx 8
theorem c5_23 : ¬ indep0% List.Vector.getElem_pmap 8 := fun h =>
  absurd (h (p := fun _ : ℕ => True) (β := ℕ) (fun _ _ => 0) (List.Vector.nil : List.Vector ℕ 0) (by simp) (i := 0)) (by decide)
-- `List.Vector.insertIdx_comm` idx 6
theorem c5_24 : ¬ drop0% List.Vector.insertIdx_comm 6 := fun h => absurd (h (n := 1) 1 2 1 0 v0) (by decide)
-- `List.Vector.get_set_of_ne` idx 5
theorem c5_25 : ¬ drop0% List.Vector.get_set_of_ne 5 := fun h => absurd (h (v := v0) (i := 0) (j := 0) 1) (by decide)
-- `List.Vector.eq` idx 4
theorem c5_29 : ¬ drop0% List.Vector.eq 4 := fun h => absurd (h v0 v1) (by decide)
-- `List.Vector.getElem_def` idx 4
theorem c5_30 : ¬ indep0% List.Vector.getElem_def 4 := fun h => absurd (h (List.Vector.nil : List.Vector ℕ 0) 0) (by decide)
-- `List.Vector.toList_getElem` idx 4
theorem c5_31 : ¬ indep0% List.Vector.toList_getElem 4 := fun h => absurd (h (List.Vector.nil : List.Vector ℕ 0) 0) (by simp)
-- `List.Vector.map_pmap` idx 8
theorem c5_32 : ¬ indep0% List.Vector.map_pmap 8 := fun h =>
  h v0 (p := fun _ : ℕ => False) (γ := ℕ) (β := ℕ) id (fun _ h => h.elim) 0 mem_v0
-- `List.Vector.pmap_map` idx 8
theorem c5_33 : ¬ indep0% List.Vector.pmap_map 8 := fun h =>
  h v0 (p := fun _ : ℕ => False) (γ := ℕ) (fun _ h => h.elim) id 0 mem_v0
-- `List.Vector.mapAccumr_bisim` idx 11
theorem c5_34 : ¬ drop0% List.Vector.mapAccumr_bisim 11 := fun h =>
  (h (xs := (List.Vector.nil : List.Vector ℕ 0)) (f₁ := fun _ s => (s, (0 : ℕ))) (f₂ := fun _ s => (s, 0)) (s₁ := (0 : ℕ))
    (s₂ := (0 : ℕ)) (fun _ _ => False) (fun _ h => h.elim)).1
-- `List.Vector.mapAccumr_bisim` idx 12
theorem c5_35 : ¬ drop0% List.Vector.mapAccumr_bisim 12 := fun h =>
  absurd (h (xs := v0) (f₁ := fun _ s => (s, (0 : ℕ))) (f₂ := fun _ s => (s, 1)) (s₁ := (0 : ℕ))
    (s₂ := (0 : ℕ)) (fun _ _ => True) trivial).2 (by decide)
-- `List.Vector.mapAccumr_bisim_tail` idx 10
theorem c5_36 : ¬ drop0% List.Vector.mapAccumr_bisim_tail 10 := fun h =>
  absurd (h (xs := v0) (f₁ := fun _ s => (s, (0 : ℕ))) (f₂ := fun _ s => (s, 1)) (s₁ := (0 : ℕ)) (s₂ := (0 : ℕ))) (by decide)
-- `List.Vector.mapAccumr₂_bisim` idx 13
theorem c5_37 : ¬ drop0% List.Vector.mapAccumr₂_bisim 13 := fun h =>
  (h (xs := (List.Vector.nil : List.Vector ℕ 0)) (ys := (List.Vector.nil : List.Vector ℕ 0))
    (f₁ := fun _ _ s => (s, (0 : ℕ))) (f₂ := fun _ _ s => (s, 0)) (s₁ := (0 : ℕ))
    (s₂ := (0 : ℕ)) (fun _ _ => False) (fun _ _ h => h.elim)).1
-- `List.Vector.mapAccumr₂_bisim` idx 14
theorem c5_38 : ¬ drop0% List.Vector.mapAccumr₂_bisim 14 := fun h =>
  absurd (h (xs := v0) (ys := v0) (f₁ := fun _ _ s => (s, (0 : ℕ))) (f₂ := fun _ _ s => (s, 1)) (s₁ := (0 : ℕ))
    (s₂ := (0 : ℕ)) (fun _ _ => True) trivial).2 (by decide)
-- `List.Vector.mapAccumr_eq_map` idx 8
theorem c5_39 : ¬ drop0% List.Vector.mapAccumr_eq_map 8 := fun h =>
  absurd (h (xs := v00) (f := fun _ s => (s + 1, s)) (s₀ := 0) ∅ (fun _ _ hs => hs.elim) (fun _ _ _ hs => hs.elim)) (by decide)
-- `List.Vector.mapAccumr_eq_map` idx 9
theorem c5_40 : ¬ drop0% List.Vector.mapAccumr_eq_map 9 := fun h =>
  absurd (h (xs := v00) (f := fun _ s => (s + 1, s)) (s₀ := 0) {0} rfl
    (fun _ s s' hs hs' => by simp only [Set.mem_singleton_iff] at hs hs'; subst hs hs'; rfl)) (by decide)
-- `List.Vector.mapAccumr_eq_map` idx 10
theorem c5_41 : ¬ drop0% List.Vector.mapAccumr_eq_map 10 := fun h =>
  absurd (h (xs := v00) (f := fun _ s => (s + 1, s)) (s₀ := 0) Set.univ trivial (fun _ _ _ => trivial)) (by decide)
-- `List.Vector.mapAccumr₂_eq_map₂` idx 10
theorem c5_42 : ¬ drop0% List.Vector.mapAccumr₂_eq_map₂ 10 := fun h =>
  absurd (h (xs := v00) (ys := v00) (f := fun _ _ s => (s + 1, s)) (s₀ := 0) ∅ (fun _ _ _ hs => hs.elim)
    (fun _ _ _ _ hs => hs.elim)) (by decide)
-- `List.Vector.mapAccumr₂_eq_map₂` idx 11
theorem c5_43 : ¬ drop0% List.Vector.mapAccumr₂_eq_map₂ 11 := fun h =>
  absurd (h (xs := v00) (ys := v00) (f := fun _ _ s => (s + 1, s)) (s₀ := 0) {0} rfl
    (fun _ _ s s' hs hs' => by simp only [Set.mem_singleton_iff] at hs hs'; subst hs hs'; rfl)) (by decide)
-- `List.Vector.mapAccumr₂_eq_map₂` idx 12
theorem c5_44 : ¬ drop0% List.Vector.mapAccumr₂_eq_map₂ 12 := fun h =>
  absurd (h (xs := v00) (ys := v00) (f := fun _ _ s => (s + 1, s)) (s₀ := 0) Set.univ trivial (fun _ _ _ _ => trivial)) (by decide)
-- `List.Vector.mapAccumr_eq_map_of_constant_state` idx 7
theorem c5_45 : ¬ drop0% List.Vector.mapAccumr_eq_map_of_constant_state 7 := fun h =>
  absurd (h (xs := v0) (fun _ s => (s + 1, s)) 0) (by decide)
-- `List.Vector.mapAccumr₂_eq_map₂_of_constant_state` idx 9
theorem c5_46 : ¬ drop0% List.Vector.mapAccumr₂_eq_map₂_of_constant_state 9 := fun h =>
  absurd (h (xs := v0) (ys := v0) (fun _ _ s => (s + 1, s)) 0) (by decide)
-- `List.Vector.mapAccumr_eq_map_of_unused_state` idx 8
theorem c5_47 : ¬ drop0% List.Vector.mapAccumr_eq_map_of_unused_state 8 := fun h =>
  absurd (h (xs := v0) (fun _ s => (s, s)) (fun _ => 1) 0) (by decide)
-- `List.Vector.mapAccumr₂_eq_map₂_of_unused_state` idx 10
theorem c5_48 : ¬ drop0% List.Vector.mapAccumr₂_eq_map₂_of_unused_state 10 := fun h =>
  absurd (h (xs := v00) (ys := v00) (fun _ _ s => (s + 1, s)) (fun _ _ => 1) 0) (by decide)
-- `List.Vector.mapAccumr_redundant_pair` idx 7
theorem c5_49 : ¬ drop0% List.Vector.mapAccumr_redundant_pair 7 := fun h =>
  absurd (h (s := 0) (xs := v00) (fun _ p => ((p.1, p.1 + 1), p.2))) (by decide)
-- `List.Vector.mapAccumr₂_redundant_pair` idx 9
theorem c5_50 : ¬ drop0% List.Vector.mapAccumr₂_redundant_pair 9 := fun h =>
  absurd (h (s := 0) (xs := v00) (ys := v00) (fun _ _ p => ((p.1, p.1 + 1), p.2))) (by decide)
-- `List.Vector.mapAccumr₂_unused_input_left` idx 10
theorem c5_51 : ¬ drop0% List.Vector.mapAccumr₂_unused_input_left 10 := fun h =>
  absurd (h (s := 0) (xs := v0) (ys := v1) (fun a _ s => (s, a)) (fun b s => (s, b))) (by decide)
-- `List.Vector.mapAccumr₂_unused_input_right` idx 10
theorem c5_52 : ¬ drop0% List.Vector.mapAccumr₂_unused_input_right 10 := fun h =>
  absurd (h (s := 0) (xs := v0) (ys := v1) (fun _ b s => (s, b)) (fun a s => (s, a))) (by decide)
-- `List.Vector.map₂_comm` idx 6
theorem c5_53 : ¬ drop0% List.Vector.map₂_comm 6 := fun h => absurd (h v0 v1 (fun a _ => a)) (by decide)
-- `List.Vector.mapAccumr₂_comm` idx 8
theorem c5_54 : ¬ drop0% List.Vector.mapAccumr₂_comm 8 := fun h => absurd (h (s := 0) v0 v1 (fun a _ s => (s, a))) (by decide)
-- `List.Vector.mem_of_mem_tail` idx 4
theorem c5_55 : ¬ drop0% List.Vector.mem_of_mem_tail 4 := fun h => absurd (h 0 (List.Vector.nil : List.Vector ℕ 0)) (by simp)
-- `List.Vector.head_pmap` idx 6
theorem c5_56 : ¬ indep0% List.Vector.head_pmap 6 := fun h =>
  h (p := fun _ : ℕ => False) (β := ℕ) (fun _ h => h.elim) v0 0 mem_v0
-- `List.Vector.tail_pmap` idx 6
theorem c5_57 : ¬ indep0% List.Vector.tail_pmap 6 := fun h =>
  h (p := fun _ : ℕ => False) (β := ℕ) (fun _ h => h.elim) v0 0 mem_v0
-- `VectorAllP.imp` idx 4
theorem c5_58 : ¬ drop0% VectorAllP.imp 4 := fun h =>
  h (p := fun _ : ℕ => True) (q := fun _ => False) (v := Vector3.cons 0 Vector3.nil) trivial
-- `VectorAllP.imp` idx 6
theorem c5_59 : ¬ drop0% VectorAllP.imp 6 := fun h =>
  h (p := fun _ : ℕ => False) (q := fun _ => False) (fun _ h => h) (v := Vector3.cons 0 Vector3.nil)
-- `TypeVec.Arrow.ext` idx 5
theorem c5_10 : ¬ drop0% TypeVec.Arrow.ext 5 := fun h =>
  absurd (congrFun (congrFun (h (n := 1) (α := fun _ => Bool) (β := fun _ => Bool) (fun _ => id) (fun _ => not)) Fin2.fz) true)
    (by simp)
namespace W4c5
/-- identity at the last index, negation elsewhere -/
def gN : TypeVec.Arrow (n := 2) (fun _ => Bool) (fun _ => Bool) := fun i => match i with
  | .fz => id
  | .fs _ => not
end W4c5
-- `TypeVec.eq_of_drop_last_eq` idx 5
theorem c5_11 : ¬ drop0% TypeVec.eq_of_drop_last_eq 5 := fun h =>
  absurd (congrFun (congrFun (h (n := 1) (α := fun _ => Bool) (β := fun _ => Bool) (f := fun _ => id) (g := gN) rfl)
    (Fin2.fs Fin2.fz)) true) (by decide)
-- `TypeVec.eq_of_drop_last_eq` idx 6
theorem c5_12 : ¬ drop0% TypeVec.eq_of_drop_last_eq 6 := fun h =>
  absurd (congrFun (congrFun (h (n := 0) (α := fun _ => Bool) (β := fun _ => Bool) (f := fun _ => id) (g := fun _ => not)
    (funext fun i => nomatch i)) Fin2.fz) true) (by decide)
-- `TypeVec.splitFun_inj` idx 7
theorem c5_13 : ¬ drop0% TypeVec.splitFun_inj 7 := fun h =>
  absurd (congrFun (h (n := 0) (α := fun _ => Bool) (α' := fun _ => Bool) (f := fun i => nomatch i) (f' := fun i => nomatch i)
    (g := id) (g' := not)).2 true) (fun e => Bool.noConfusion e)
-- `TypeVec.appendFun_inj` idx 9
theorem c5_14 : ¬ drop0% TypeVec.appendFun_inj 9 := fun h =>
  absurd (congrFun (h (n := 0) (α := fun i => nomatch i) (α' := fun i => nomatch i) (β := Bool) (β' := Bool)
    (f := fun i => nomatch i) (f' := fun i => nomatch i) (g := id) (g' := not)).2 true) (fun e => Bool.noConfusion e)
-- `ULift.instNonempty_mathlib` idx 1
theorem c5_15 : ¬ drop0% ULift.instNonempty_mathlib 1 := fun h => (h (α := Empty)).elim fun x => x.down.elim
-- `Sym2.ncard_mk_fiber_of_isDiag` idx 2
theorem c5_1 : ¬ drop0% Sym2.ncard_mk_fiber_of_isDiag 2 := fun h =>
  absurd (h (z := s((0 : ℕ), 1))) (by rw [Sym2.ncard_mk_fiber_of_not_isDiag (by simp)]; decide)
-- `Sym2.ncard_mk_fiber_of_not_isDiag` idx 2
theorem c5_2 : ¬ drop0% Sym2.ncard_mk_fiber_of_not_isDiag 2 := fun h =>
  absurd (h (z := s((0 : ℕ), 0))) (by rw [Sym2.ncard_mk_fiber_of_isDiag (by simp)]; decide)
-- `Finsupp.mem_sym2_support_of_mul_ne_zero` idx 5
theorem c5_5 : ¬ drop0% Finsupp.mem_sym2_support_of_mul_ne_zero 5 := fun h =>
  absurd (h (M₀ := ℕ) (f := 0) s((0 : ℕ), 0)) (by simp)
-- `Finsupp.sym2_support_eq_preimage_support_mul` idx 3
theorem c5_4 : ¬ drop0% Finsupp.sym2_support_eq_preimage_support_mul 3 := fun h => by
  have := (Set.ext_iff.1 (h (M₀ := ZMod 4) (Finsupp.single (0 : ℕ) 2))) s(0, 0)
  simp [Finsupp.support_single_ne_zero _ (show (2 : ZMod 4) ≠ 0 by decide)] at this
  revert this; decide
-- `WType.elim_injective` idx 4
theorem c5_60 : ¬ drop0% WType.elim_injective 4 := fun h => by
  have := h (α := Bool) (β := fun _ => Empty) Unit (fun _ => ()) (a₁ := WType.mk true Empty.elim)
    (a₂ := WType.mk false Empty.elim) rfl
  injection this with h1; cases h1
-- `WType.instIsEmpty` idx 2
theorem c5_61 : ¬ drop0% WType.instIsEmpty 2 := fun h => (h (β := fun _ : Unit => Empty)).false (WType.mk () Empty.elim)
-- `WType.infinite_of_nonempty_of_isEmpty` idx 5
theorem c5_62 : ¬ drop0% WType.infinite_of_nonempty_of_isEmpty 5 := fun h => by
  obtain ⟨w⟩ := (h (α := Unit) (β := fun _ => Unit) () ()).nonempty
  exact (WType.elim Empty (fun p => p.2 ()) w).elim
-- `WType.cardinalMk_le_of_le'` idx 3
theorem c5_63 : ¬ drop0% WType.cardinalMk_le_of_le' 3 := fun h => by
  have := h (α := Unit) (β := fun _ => Empty) (κ := 0)
  rw [nonpos_iff_eq_zero, Cardinal.mk_eq_zero_iff] at this
  exact this.false (WType.mk () Empty.elim)
-- `WType.cardinalMk_le_of_le` idx 3
theorem c5_65 : ¬ drop0% WType.cardinalMk_le_of_le 3 := fun h => by
  have := h (α := Unit) (β := fun _ => Empty) (κ := 0)
  rw [nonpos_iff_eq_zero, Cardinal.mk_eq_zero_iff] at this
  exact this.false (WType.mk () Empty.elim)

namespace W4c5
open Stream'
theorem nt_of_eq_think {α : Type} {c : Computation α} (e : c = c.think) : ¬ c.Terminates := by
  rintro ⟨⟨a, ha⟩⟩
  refine Computation.memRecOn (C := fun s => s = c → False) ha ?_ ?_ rfl
  · intro h; have := congrArg Computation.destruct (h.trans e); simp at this
  · intro s ih h; apply ih; have := congrArg Computation.destruct (h.trans e); simpa using this
theorem nv_think : nv = WSeq.think nv := by
  show WSeq.flatten (Computation.empty (WSeq ℕ)) = WSeq.think (WSeq.flatten (Computation.empty (WSeq ℕ)))
  rw [← WSeq.flatten_think, ← Computation.think_empty]
theorem nv_toList : WSeq.toList nv = (WSeq.toList nv).think := by
  conv_lhs => rw [nv_think]
  exact WSeq.toList'_think [] nv
theorem nv_toList_nt : ¬ (WSeq.toList nv).Terminates := nt_of_eq_think nv_toList
/-- Option with a broken map (always none): pure and seq are those of Option -/
def BO (α : Type) : Type := Option α
instance : Applicative BO where
  pure := some
  seq f x := Option.bind f fun g => Option.map g (x ())
  map _ _ := none
instance {α} [DecidableEq α] : DecidableEq (BO α) := inferInstanceAs (DecidableEq (Option α))
/-- the identity transformation from BO to Option and back -/
def ηBO : ApplicativeTransformation BO Option where
  app _ x := x
  preserves_pure' _ := rfl
  preserves_seq' _ _ := rfl
def ηOB : ApplicativeTransformation Option BO where
  app _ x := x
  preserves_pure' _ := rfl
  preserves_seq' f x := by cases f <;> cases x <;> rfl
end W4c5
open W4c5 Stream'
-- `Stream'.WSeq.IsFinite.out` idx 2
theorem c5_92 : ¬ drop0% Stream'.WSeq.IsFinite.out 2 := fun h => nv_toList_nt (h (s := nv))
-- `Stream'.WSeq.toList_terminates` idx 2
theorem c5_93 : ¬ drop0% Stream'.WSeq.toList_terminates 2 := fun h => nv_toList_nt (h nv)
-- `Stream'.WSeq.liftRel_join.lem` idx 6
theorem c5_139 : ¬ drop0% Stream'.WSeq.liftRel_join.lem 6 := fun h => by
  obtain ⟨b, hb, hr⟩ := h (fun _ _ : ℕ => True) (S := WSeq.nil) (T := WSeq.cons (WSeq.cons 0 WSeq.nil) WSeq.nil)
    (U := fun _ _ => True) (fun _ _ _ => trivial) (a := none)
    (by rw [WSeq.join_nil, WSeq.destruct_nil]; exact Computation.ret_mem _)
  rw [WSeq.join_cons, WSeq.destruct_think, WSeq.cons_append, WSeq.destruct_cons] at hb
  have hb' := Computation.eq_of_pure_mem (Computation.of_think_mem hb)
  subst hb'; exact hr
-- `Stream'.WSeq.liftRel_join.lem` idx 7
theorem c5_140 : ¬ drop0% Stream'.WSeq.liftRel_join.lem 7 := fun h => by
  obtain ⟨b, hb, hr⟩ := h (fun _ _ : ℕ => True) (S := WSeq.cons (WSeq.cons 0 WSeq.nil) WSeq.nil)
    (T := WSeq.cons (WSeq.cons 0 WSeq.nil) WSeq.nil) (U := fun _ _ => False)
    ((WSeq.liftRel_cons _ _ _ _ _).2 ⟨lrT, WSeq.liftRel_nil _⟩) (a := some (0, WSeq.append WSeq.nil (WSeq.join WSeq.nil)))
    (by rw [WSeq.join_cons, WSeq.destruct_think, WSeq.cons_append, WSeq.destruct_cons]
        exact Computation.think_mem (Computation.ret_mem _))
  rw [WSeq.join_cons, WSeq.destruct_think, WSeq.cons_append, WSeq.destruct_cons] at hb
  have hb' := Computation.eq_of_pure_mem (Computation.of_think_mem hb)
  subst hb'; exact hr.2
-- `Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel` idx 3
theorem c5_3 : ¬ drop0% Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel 3 := fun h => by
  have e := h (α := Unit) (r := fun _ _ => True) ⟨fun _ _ h => h⟩
  rw [Cardinal.eq_one_iff_unique.2 ⟨inferInstance, ⟨⟨((), ()), trivial⟩⟩⟩,
    Cardinal.eq_one_iff_unique.2 ⟨⟨fun ⟨a, _⟩ ⟨b, _⟩ => Subtype.ext (by
      induction a using Sym2.ind; induction b using Sym2.ind; rfl)⟩, ⟨⟨s((), ()), Sym2.fromRel_prop.2 trivial⟩⟩⟩,
    mul_one] at e
  exact absurd e (by exact_mod_cast (show (1 : ℕ) ≠ 2 by decide))
-- `BinaryTree.traverse_pure` idx 4
theorem c5_6 : ¬ drop0% BinaryTree.traverse_pure 4 := fun h =>
  absurd (h (BinaryTree.node (0 : ℕ) .nil .nil) (m := BO)) (by decide)
-- `BinaryTree.comp_traverse` idx 5
theorem c5_7 : ¬ drop0% BinaryTree.comp_traverse 5 := fun h =>
  absurd (congrArg Functor.Comp.run (h (F := Option) (G := BO) (fun b : ℕ => some b) (fun a : ℕ => (some a : BO ℕ)) .nil))
    (by decide)
-- `BinaryTree.naturality` idx 5
theorem c5_8 : ¬ drop0% BinaryTree.naturality 5 := fun h =>
  absurd (h ηBO (fun a : ℕ => (some a : BO ℕ)) (BinaryTree.node 0 .nil .nil)) (by decide)
-- `BinaryTree.naturality` idx 6
theorem c5_9 : ¬ drop0% BinaryTree.naturality 6 := fun h =>
  absurd (h ηOB (fun a : ℕ => some a) (BinaryTree.node 0 .nil .nil)) (by decide)
-- `List.Vector.comp_traverse` idx 5
theorem c5_26 : ¬ drop0% List.Vector.comp_traverse 5 := fun h =>
  absurd (congrArg Functor.Comp.run (h (F := Option) (G := BO) (fun b : ℕ => some b) (fun a : ℕ => (some a : BO ℕ))
    (List.Vector.nil : List.Vector ℕ 0))) (by decide)
-- `List.Vector.naturality` idx 5
theorem c5_27 : ¬ drop0% List.Vector.naturality 5 := fun h =>
  absurd (h ηOB (fun a : ℕ => some a) v0) (by decide)
-- `List.Vector.naturality` idx 6
theorem c5_28 : ¬ drop0% List.Vector.naturality 6 := fun h =>
  absurd (h ηBO (fun a : ℕ => (some a : BO ℕ)) v0) (by decide)

namespace W4c5
/-- ZMod 2 × ZMod 2 has characteristic 2 -/
instance cp22 : CharP (ZMod 2 × ZMod 2) 2 := ⟨fun x => by
  rw [Prod.ext_iff]; simp [ZMod.natCast_eq_zero_iff]⟩
theorem card22 : Fintype.card (ZMod 2 × ZMod 2) = 4 := rfl
/-- a set-like type of arbitrary subsets of ZMod 2 -/
structure SS where c : Set (ZMod 2)
instance : SetLike SS (ZMod 2) := ⟨SS.c, fun a b h => by cases a; cases b; congr⟩
theorem mem_SS (x : ZMod 2) (s : Set (ZMod 2)) : x ∈ (⟨s⟩ : SS) ↔ x ∈ s := Iff.rfl
end W4c5
open W4c5
-- `ZMod.castHom_bijective` idx 3
theorem c5_172 : ¬ indep0% ZMod.castHom_bijective 3 := fun h =>
  absurd ((@CharP.cast_eq_zero_iff (ZMod 2 × ZMod 2) _ 4 (h (n := 4) (ZMod 2 × ZMod 2) card22) 2).1 (by decide)) (by decide)
-- `ZMod.castHom_bijective` idx 5
theorem c5_173 : ¬ drop0% ZMod.castHom_bijective 5 := fun h => by
  obtain ⟨x, hx⟩ := (h (n := 2) (ZMod 2 × ZMod 2)).2 (1, 0)
  rcases (show ∀ y : ZMod 2, y = 0 ∨ y = 1 by decide) x with rfl | rfl <;> simp at hx <;> revert hx <;> decide
-- `ZMod.ringEquivOfPrime_eq_ringEquiv` idx 6
theorem c5_176 : ¬ indep0% ZMod.ringEquivOfPrime_eq_ringEquiv 6 := fun h =>
  absurd (h (ZMod 2 × ZMod 2) (p := 2) Nat.prime_two) (by rw [card22]; decide)
-- `ZMod.val_cast_zmod_lt` idx 3: removable (the cast of `a` lands in `ZMod n` as `a.val`, whose value is at most `a.val`)
theorem c5_203 : drop% ZMod.val_cast_zmod_lt 3 := by
  intro m _ n a
  rw [ZMod.cast_eq_val, ZMod.val_natCast]
  exact lt_of_le_of_lt (Nat.mod_le _ _) (ZMod.val_lt a)
-- `ZMod.val_pow` idx 3: removable (for n = 0 the hypothesis is false, for n = 1 both sides are 0)
theorem c5_214 : drop% ZMod.val_pow 3 := by
  intro m n a h
  rcases n with _ | _ | n
  · exact absurd h (Nat.not_lt_zero _)
  · have e : ∀ x : ZMod 1, x.val = 0 := fun x => Fin.val_eq_zero x
    simp only [e] at h ⊢
    rcases m with _ | m <;> simp_all
  · exact @ZMod.val_pow m (n + 2) a ⟨by omega⟩ h
-- `ZMod.val_pow_le` idx 2: removable (for n = 0 val is natAbs, for n = 1 val is 0)
theorem c5_216 : drop% ZMod.val_pow_le 2 := by
  intro m n a
  rcases n with _ | _ | n
  · show Int.natAbs ((id a : ℤ) ^ m) ≤ Int.natAbs (id a : ℤ) ^ m
    rw [Int.natAbs_pow]
  · have e : ∀ x : ZMod 1, x.val = 0 := fun x => Fin.val_eq_zero x
    simp only [e]; exact Nat.zero_le _
  · exact @ZMod.val_pow_le m (n + 2) ⟨by omega⟩ a
-- `zmod_smul_mem` idx 5
theorem c5_217 : ¬ drop0% zmod_smul_mem 5 := fun h => by
  have := h (n := 2) (S := SS) (G := ZMod 2) (K := ⟨{1}⟩) (x := 1) rfl 0
  rw [mem_SS] at this; revert this; decide
-- `zmod_smul_mem` idx 9
theorem c5_218 : ¬ drop0% zmod_smul_mem 9 := fun h => by
  have := h (n := 2) (S := AddSubgroup (ZMod 2)) (G := ZMod 2) (K := ⊥) (x := 1) 1
  rw [AddSubgroup.mem_bot] at this; revert this; decide
-- `smulMemClass` idx 5
theorem c5_219 : ¬ drop0% smulMemClass 5 := fun h => by
  have inst := h (n := 2) (S := SS) (G := ZMod 2)
  have := inst.smul_mem (s := (⟨{1}⟩ : SS)) (0 : ZMod 2) (m := 1) rfl
  rw [mem_SS] at this; revert this; decide
-- `AddSubgroupClass.coe_zmod_smul` idx 5
theorem c5_220 : ¬ indep0% AddSubgroupClass.coe_zmod_smul 5 := fun h => by
  have := h (n := 2) (S := SS) (G := ZMod 2) (K := ⟨Set.univ⟩) 0 ⟨0, trivial⟩
  exact (ZeroMemClass.zero_mem (⟨∅⟩ : SS) : (0 : ZMod 2) ∈ (∅ : Set (ZMod 2)))
-- `ZModModule.char_ne_one` idx 4
theorem c5_221 : ¬ drop0% ZModModule.char_ne_one 4 := fun h => h 1 Unit rfl
-- `ZModModule.two_le_char` idx 4
theorem c5_222 : ¬ drop0% ZModModule.two_le_char 4 := fun h =>
  absurd (@h 0 ℤ _ (inferInstanceAs (Module ℤ ℤ)) _) (by decide)
-- `ZModModule.two_le_char` idx 5
theorem c5_223 : ¬ drop0% ZModModule.two_le_char 5 := fun h => absurd (h 1 Unit) (by decide)
-- `ZModModule.periodicPts_add_left` idx 4
theorem c5_224 : ¬ drop0% ZModModule.periodicPts_add_left 4 := fun h => by
  have e := @h 0 ℤ _ (inferInstanceAs (Module ℤ ℤ)) 1
  have : (0 : ℤ) ∈ Function.periodicPts (fun x => 1 + x) := by rw [e]; trivial
  obtain ⟨k, hk, hp⟩ := Function.mem_periodicPts.1 this
  have := hp.eq
  simp [add_left_iterate] at this; omega

namespace W4c5
/-- W-type with a leaf constructor and an ℕ-branching constructor -/
def βW : Bool → Type := fun b => cond b Empty ℕ
def LW : WType βW := WType.mk true (fun e => Empty.elim e)
def TW : WType βW := WType.mk false (fun _ => LW)
/-- Boolean sequences embed as ℕ-branching trees with leaves LW/TW -/
def embW (f : ℕ → Bool) : WType βW := WType.mk false (fun n => cond (f n) TW LW)
theorem embW_inj : Function.Injective embW := by
  intro f g e
  unfold embW at e
  injection e with _ e2
  funext n
  have := congrFun e2 n
  cases hf : f n <;> cases hg : g n <;> simp [hf, hg, TW, LW] at this ⊢
theorem W_big : ¬ Cardinal.mk (WType βW) ≤ max (Cardinal.mk Bool) Cardinal.aleph0 := by
  intro h
  have h1 := Cardinal.mk_le_of_injective embW_inj
  rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat] at h1
  have h2 : max (Cardinal.mk Bool) Cardinal.aleph0 = Cardinal.aleph0 := max_eq_right Cardinal.mk_le_aleph0
  exact absurd (h1.trans (h.trans h2.le)) (not_le.2 (Cardinal.cantor _))
end W4c5
open W4c5
-- `WType.cardinalMk_le_max_aleph0_of_finite'` idx 2
theorem c5_64 : ¬ drop0% WType.cardinalMk_le_max_aleph0_of_finite' 2 := fun h =>
  W_big (by have := h (α := Bool) (β := βW); rwa [Cardinal.lift_id] at this)
-- `WType.cardinalMk_le_max_aleph0_of_finite` idx 2
theorem c5_66 : ¬ drop0% WType.cardinalMk_le_max_aleph0_of_finite 2 := fun h => W_big (h (α := Bool) (β := βW))
