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
import all Mathlib.Basic.Complex.Basic
import all Mathlib.Basic.Complex.BigOperators
import all Mathlib.Basic.Countable.Basic
import all Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Small
import all Mathlib.Basic.Denumerable
import all Mathlib.Basic.ENNReal.Action
import all Mathlib.Basic.ENNReal.Basic
import all Mathlib.Basic.ENNReal.BigOperators
import all Mathlib.Basic.ENNReal.Holder
import all Mathlib.Basic.ENNReal.Inv
import all Mathlib.Basic.ENNReal.Lemmas
import all Mathlib.Basic.ENNReal.Operations
import all Mathlib.Basic.ENNReal.Real
import all Mathlib.Basic.ExistsUnique
import all Mathlib.Basic.Finite.Defs
import all Mathlib.Basic.Finite.Prod
import all Mathlib.Basic.Finite.Set
import all Mathlib.Basic.Finite.Sigma
import all Mathlib.Basic.Finite.Sum
import all Mathlib.Basic.FunLike.Basic
import all Mathlib.Basic.FunLike.Embedding
import all Mathlib.Basic.FunLike.Equiv
import all Mathlib.Basic.IsEmpty.Basic
import all Mathlib.Basic.IsEmpty.Defs
import all Mathlib.Basic.Logic.Basic
import all Mathlib.Basic.Logic.Lemmas
import all Mathlib.Basic.NNReal.Basic
import all Mathlib.Basic.NNReal.Defs
import all Mathlib.Basic.NNReal.Star
import all Mathlib.Basic.Nonempty
import all Mathlib.Basic.Nontrivial.Basic
import all Mathlib.Basic.Nontrivial.Defs
import all Mathlib.Basic.Opposite
import all Mathlib.Basic.PEquiv
import all Mathlib.Basic.Real.Basic
import all Mathlib.Basic.Real.ConjExponents
import all Mathlib.Basic.Real.Embedding
import all Mathlib.Basic.Real.ENatENNReal
import all Mathlib.Basic.Real.Pointwise
import all Mathlib.Basic.Real.Sign
import all Mathlib.Basic.Real.Star
import all Mathlib.Basic.Rel.Cover
import all Mathlib.Basic.Rel
import all Mathlib.Basic.Rel.Separated
import all Mathlib.Basic.SetLike.Basic
import all Mathlib.Basic.Sign.Basic
import all Mathlib.Basic.Sign.Defs
import all Mathlib.Basic.SProd
import all Mathlib.Basic.TwoPointing
import all Mathlib.Basic.Unique
import all Mathlib.Basic.UnivLE
import all Mathlib.Logic.Embedding.Basic
import all Mathlib.Logic.Embedding.Set
import all Mathlib.Logic.Encodable.Basic
import all Mathlib.Logic.Encodable.Lattice
import all Mathlib.Logic.Encodable.Pi
import all Mathlib.Logic.Equiv.Array
import all Mathlib.Logic.Equiv.Basic
import all Mathlib.Logic.Equiv.Bool
import all Mathlib.Logic.Equiv.Defs
import all Mathlib.Logic.Equiv.Embedding
import all Mathlib.Logic.Equiv.Fin.Basic
import all Mathlib.Logic.Equiv.Fin.Rotate
import all Mathlib.Logic.Equiv.Finset
import all Mathlib.Logic.Equiv.Fintype
import all Mathlib.Logic.Equiv.Functor
import all Mathlib.Logic.Equiv.List
import all Mathlib.Logic.Equiv.Multiset
import all Mathlib.Logic.Equiv.Nat
import all Mathlib.Logic.Equiv.Option
import all Mathlib.Logic.Equiv.Pairwise
import all Mathlib.Logic.Equiv.PartialEquiv
import all Mathlib.Logic.Equiv.Prod
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Logic.Equiv.Sigma
import all Mathlib.Logic.Equiv.Sum
import all Mathlib.Logic.Function.Basic
import all Mathlib.Logic.Function.Coequalizer
import all Mathlib.Logic.Function.CompTypeclasses
import all Mathlib.Logic.Function.Conjugate
import all Mathlib.Logic.Function.Const
import all Mathlib.Logic.Function.Defs
import all Mathlib.Logic.Function.DependsOn
import all Mathlib.Logic.Function.FiberPartition
import all Mathlib.Logic.Function.FromTypes
import all Mathlib.Logic.Function.Iterate
import all Mathlib.Logic.Function.OfArity
import all Mathlib.Logic.Function.ULift
import all Mathlib.Logic.Godel.GodelBetaFunction
import all Mathlib.Logic.Hydra
import all Mathlib.Logic.OpClass
import all Mathlib.Logic.Pairwise
import all Mathlib.Logic.Relation
import all Mathlib.Logic.Relator
import all Mathlib.Logic.Small.Basic
import all Mathlib.Logic.Small.Defs
import all Mathlib.Logic.Small.List
import all Mathlib.Logic.Small.Set
-- hypkit toolkit header (mathlib-logic-basic, module system; copied from mathlib-data): HCHeaderM = all
-- Mathlib.Data modules + Mathlib.Analysis.Real.Cardinality + Mathlib.Topology.Sets.Closeds + every
-- Mathlib.Logic / Mathlib.Basic module (public parts) and the drop%/indep%/drop0%/indep0%/drop1%/priv%
-- elaborators; `import all` gives the private parts of every Data, Logic and Basic module (private
-- constants, bodies of non-exposed definitions). Do NOT open a `public section`:
-- your declarations stay private, so they may mention private library constants.
-- Agents copy this file unchanged as the start of their output file (scripts/verify.sh checks it).
-- Need a module outside these? Log the row as gave_up with obstruction "needs import <Module>".

set_option linter.unusedVariables false

open Lean Meta Elab Term

open ENNReal NNReal

namespace W1c0

theorem nCtR : ¬ Countable ℝ := fun h => Cardinal.not_countable_real (Set.countable_univ_iff.mpr h)

theorem uR : Uncountable ℝ := ⟨nCtR⟩

theorem cU : Countable Unit := inferInstance

theorem finSet01 : ¬ Infinite ↑({0, 1} : Set ℕ) := fun h =>
  (Set.infinite_coe_iff.mp h) (Set.toFinite _)

theorem finSet0 : ¬ Infinite ↑({0} : Set ℕ) := fun h =>
  (Set.infinite_coe_iff.mp h) (Set.toFinite _)

theorem finSetE : ¬ Infinite ↑(∅ : Set ℕ) := fun h =>
  (Set.infinite_coe_iff.mp h) (Set.toFinite _)

theorem infU : Infinite ↑(Set.univ : Set ℕ) := Set.infinite_coe_iff.mpr Set.infinite_univ

theorem oz (n : ℤ) : (1 : ℝ≥0∞) ^ n = 1 := by
  cases n <;> simp [zpow_negSucc]

theorem infNat : ⨅ n : ℕ, ((n : ℝ≥0∞))⁻¹ = 0 := by
  rw [← ENNReal.inv_iSup, ENNReal.iSup_natCast, ENNReal.inv_top]

theorem invNat_ne (n : ℕ) : ((n : ℝ≥0∞))⁻¹ ≠ 0 := by simp

theorem u2_le : ∀ a b : Unit ⊕ Unit, a ≤ b → a = b := by
  rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) h <;> simp_all

theorem topInv : ⨅ n : ℕ, ⊤ * ((n : ℝ≥0∞))⁻¹ = ⊤ := by
  simp [ENNReal.top_mul (invNat_ne _)]

theorem invTop : ⨅ n : ℕ, ((n : ℝ≥0∞))⁻¹ * ⊤ = ⊤ := by
  simp [ENNReal.mul_top (invNat_ne _)]

theorem invDiv0 : ⨅ n : ℕ, ((n : ℝ≥0∞))⁻¹ / 0 = ⊤ := by
  simp [ENNReal.div_zero (invNat_ne _)]

end W1c0

open W1c0

universe u_1

-- `Complex.mul_inv_cancel` idx 1: z = 0
theorem w0_0 : ¬ drop0% Complex.mul_inv_cancel 1 := fun h => absurd (@h 0) (by simp)

-- `nonempty_embedding_nat` idx 1: α = ℝ
theorem w0_1 : ¬ drop1% nonempty_embedding_nat 1 := fun h =>
  nCtR (h ℝ).some.injective.countable

-- `Function.Embedding.countable` idx 2: id on ℝ
theorem w0_2 : ¬ drop1% Function.Embedding.countable 2 := fun h =>
  nCtR (h (Function.Embedding.refl ℝ))

-- `instCountableSum` idx 2: α = ℝ
theorem w0_3 : ¬ drop0% instCountableSum 2 := fun h => by
  have := @h ℝ Unit inferInstance; exact nCtR (Sum.inl_injective (β := Unit)).countable

-- `instCountableSum` idx 3: β = ℝ
theorem w0_4 : ¬ drop0% instCountableSum 3 := fun h => by
  have := @h Unit ℝ inferInstance; exact nCtR (Sum.inr_injective (α := Unit)).countable

-- `Option.instCountable` idx 1: α = ℝ
theorem w0_5 : ¬ drop0% Option.instCountable 1 := fun h => by
  have := @h ℝ; exact nCtR (Option.some_injective ℝ).countable

-- `WithTop.instCountable` idx 1: α = ℝ
theorem w0_6 : ¬ drop0% WithTop.instCountable 1 := fun h => by
  have := @h ℝ; exact nCtR (WithTop.coe_injective (α := ℝ)).countable

-- `WithBot.instCountable` idx 1: α = ℝ
theorem w0_7 : ¬ drop0% WithBot.instCountable 1 := fun h => by
  have := @h ℝ; exact nCtR (WithBot.coe_injective (α := ℝ)).countable

-- `instCountableProd` idx 2: α = ℝ
theorem w0_8 : ¬ drop0% instCountableProd 2 := fun h => by
  have := @h ℝ Unit inferInstance
  exact nCtR (Function.Injective.countable (f := fun x : ℝ => (x, ())) (fun a b hab => (Prod.ext_iff.mp hab).1))

-- `instCountableProd` idx 3: β = ℝ
theorem w0_9 : ¬ drop0% instCountableProd 3 := fun h => by
  have := @h Unit ℝ inferInstance
  exact nCtR (Function.Injective.countable (f := fun x : ℝ => ((), x)) (fun a b hab => (Prod.ext_iff.mp hab).2))

-- `instUncountableProdOfNonempty` idx 3: β empty
theorem w0_10 : ¬ drop0% instUncountableProdOfNonempty 3 := fun h =>
  (@h ℝ Empty uR).not_countable inferInstance

-- `instUncountableProdOfNonempty_1` idx 2: α empty
theorem w0_11 : ¬ drop0% instUncountableProdOfNonempty_1 2 := fun h =>
  (@h Empty ℝ uR).not_countable inferInstance

-- `countable_left_of_prod_of_nonempty` idx 2: β empty
theorem w0_12 : ¬ drop0% countable_left_of_prod_of_nonempty 2 := fun h =>
  nCtR (@h ℝ Empty inferInstance)

-- `countable_left_of_prod_of_nonempty` idx 3: β = Unit
theorem w0_13 : ¬ drop0% countable_left_of_prod_of_nonempty 3 := fun h =>
  nCtR (@h ℝ Unit inferInstance)

-- `countable_right_of_prod_of_nonempty` idx 2: α empty
theorem w0_14 : ¬ drop0% countable_right_of_prod_of_nonempty 2 := fun h =>
  nCtR (@h Empty ℝ inferInstance)

-- `countable_right_of_prod_of_nonempty` idx 3: α = Unit
theorem w0_15 : ¬ drop0% countable_right_of_prod_of_nonempty 3 := fun h =>
  nCtR (@h Unit ℝ inferInstance)

-- `countable_prod_swap` idx 2: ℝ × ℝ
theorem w0_16 : ¬ drop0% countable_prod_swap 2 := fun h => by
  have := @h ℝ ℝ
  exact nCtR (Function.Injective.countable (f := fun x : ℝ => (x, x)) (fun a b hab => (Prod.ext_iff.mp hab).1))

-- `instCountableSigma` idx 2: α = ℝ
theorem w0_17 : ¬ drop0% instCountableSigma 2 := fun h => by
  have := @h ℝ (fun _ => Unit) inferInstance
  exact nCtR (Function.Injective.countable (f := fun x : ℝ => (⟨x, ()⟩ : Σ _ : ℝ, Unit))
    (fun a b hab => congrArg Sigma.fst hab))

-- `instCountableSigma` idx 3: π = ℝ
theorem w0_18 : ¬ drop0% instCountableSigma 3 := fun h => by
  have := @h Unit (fun _ => ℝ) inferInstance
  exact nCtR (Function.Injective.countable (f := fun x : ℝ => (⟨(), x⟩ : Σ _ : Unit, ℝ))
    (fun a b hab => eq_of_heq (Sigma.mk.inj hab).2))

-- `instUncountableSigmaOfNonempty` idx 2: α empty
theorem w0_19 : ¬ drop0% instUncountableSigmaOfNonempty 2 := fun h =>
  (@h Empty (fun _ => ℝ) (fun _ => uR)).not_countable
    (Function.Injective.countable (f := fun x : (Σ _ : Empty, ℝ) => x.1) (fun x => x.1.elim))

-- `SetCoe.countable` idx 1: univ in ℝ
theorem w0_20 : ¬ drop0% SetCoe.countable 1 := fun h =>
  Cardinal.not_countable_real (Set.countable_coe_iff.mp (h (Set.univ : Set ℝ)))

-- `instCountablePSum` idx 2: α = ℝ
theorem w0_21 : ¬ drop1% instCountablePSum 2 := fun h => by
  have := @h ℝ Unit inferInstance
  exact nCtR (Function.Injective.countable (f := fun x : ℝ => (PSum.inl x : ℝ ⊕' Unit))
    (fun a b hab => PSum.inl.inj hab))

-- `instCountablePSum` idx 3: β = ℝ
theorem w0_22 : ¬ drop1% instCountablePSum 3 := fun h => by
  have := @h Unit ℝ inferInstance
  exact nCtR (Function.Injective.countable (f := fun x : ℝ => (PSum.inr x : Unit ⊕' ℝ))
    (fun a b hab => PSum.inr.inj hab))

-- `instCountablePProd` idx 2: α = ℝ
theorem w0_23 : ¬ drop1% instCountablePProd 2 := fun h => by
  have := @h ℝ Unit inferInstance
  exact nCtR (Function.Injective.countable (f := fun x : ℝ => (⟨x, ()⟩ : PProd ℝ Unit))
    (fun a b hab => congrArg PProd.fst hab))

-- `instCountablePProd` idx 3: β = ℝ
theorem w0_24 : ¬ drop1% instCountablePProd 3 := fun h => by
  have := @h Unit ℝ inferInstance
  exact nCtR (Function.Injective.countable (f := fun x : ℝ => (⟨(), x⟩ : PProd Unit ℝ))
    (fun a b hab => congrArg PProd.snd hab))

-- `instCountablePSigma` idx 2: α = ℝ
theorem w0_25 : ¬ drop1% instCountablePSigma 2 := fun h => by
  have := @h ℝ (fun _ => Unit) inferInstance
  exact nCtR (Function.Injective.countable (f := fun x : ℝ => (⟨x, ()⟩ : (_ : ℝ) ×' Unit))
    (fun a b hab => congrArg PSigma.fst hab))

-- `instCountablePSigma` idx 3: π = ℝ
theorem w0_26 : ¬ drop1% instCountablePSigma 3 := fun h => by
  have := @h Unit (fun _ => ℝ) inferInstance
  exact nCtR (Function.Injective.countable (f := fun x : ℝ => (⟨(), x⟩ : (_ : Unit) ×' ℝ))
    (fun a b hab => eq_of_heq (PSigma.mk.inj hab).2))

-- `instCountableForallOfFinite` idx 2: ℕ → Prop (Cantor)
theorem w0_27 : ¬ drop1% instCountableForallOfFinite 2 := fun h => by
  have : Countable (ℕ → Prop) := @h ℕ (fun _ => Prop) inferInstance
  obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Prop)
  exact Function.cantor_surjective (α := ℕ) (fun n => {m | f n m})
    (fun s => let ⟨n, hn⟩ := hf (fun m => m ∈ s); ⟨n, by simp [hn]⟩)

-- `instCountableForallOfFinite` idx 3: Unit → ℝ
theorem w0_28 : ¬ drop1% instCountableForallOfFinite 3 := fun h => by
  have := @h Unit (fun _ => ℝ) inferInstance
  exact nCtR (Function.Injective.countable (f := fun x : ℝ => (fun _ => x : Unit → ℝ))
    (fun a b hab => congrFun hab ()))

-- `Countable.exists_injective_nat'` idx 1: α = ℝ
theorem w0_29 : ¬ drop1% Countable.exists_injective_nat' 1 := fun h => by
  obtain ⟨f, hf⟩ := @h ℝ; exact nCtR hf.countable

-- `Countable.exists_injective_nat` idx 1: α = ℝ
theorem w0_30 : ¬ drop1% Countable.exists_injective_nat 1 := fun h => by
  obtain ⟨f, hf⟩ := h ℝ; exact nCtR hf.countable

-- `Function.Injective.countable` idx 2: id on ℝ
theorem w0_31 : ¬ drop1% Function.Injective.countable 2 := fun h =>
  nCtR (@h ℝ ℝ id Function.injective_id)

-- `Function.Injective.countable` idx 4: constant ℝ → Unit
theorem w0_32 : ¬ drop1% Function.Injective.countable 4 := fun h =>
  nCtR (@h ℝ Unit cU (fun _ => ()))

-- `Function.Surjective.countable` idx 2: id on ℝ
theorem w0_33 : ¬ drop1% Function.Surjective.countable 2 := fun h =>
  nCtR (@h ℝ ℝ id Function.surjective_id)

-- `Function.Surjective.countable` idx 4: constant Unit → ℝ
theorem w0_34 : ¬ drop1% Function.Surjective.countable 4 := fun h =>
  nCtR (@h Unit ℝ cU (fun _ => 0))

-- `exists_surjective_nat` idx 1: α empty
theorem w0_35 : ¬ drop1% exists_surjective_nat 1 := fun h => by
  obtain ⟨f, _⟩ := @h Empty inferInstance; exact (f 0).elim

-- `exists_surjective_nat` idx 2: α = ℝ
theorem w0_36 : ¬ drop1% exists_surjective_nat 2 := fun h => by
  obtain ⟨f, hf⟩ := @h ℝ inferInstance; exact nCtR hf.countable

-- `countable_iff_exists_surjective` idx 1: α empty
theorem w0_37 : ¬ drop1% countable_iff_exists_surjective 1 := fun h => by
  obtain ⟨f, _⟩ := (@h Empty).mp inferInstance; exact (f 0).elim

-- `Countable.of_equiv` idx 2: ℝ ≃ ℝ
theorem w0_38 : ¬ drop1% Countable.of_equiv 2 := fun h => nCtR (h ℝ (Equiv.refl ℝ))

-- `instCountableULift` idx 1: ULift ℝ
theorem w0_39 : ¬ drop0% instCountableULift 1 := fun h => by
  have := @h ℝ; exact nCtR (Function.Injective.countable (f := ULift.up) ULift.up_injective)

-- `instCountablePLift` idx 1: PLift ℝ
theorem w0_40 : ¬ drop1% instCountablePLift 1 := fun h => by
  have := @h ℝ; exact nCtR (Function.Injective.countable (f := PLift.up) PLift.up_injective)

-- `Subsingleton.to_countable` idx 1: ℝ
theorem w0_41 : ¬ drop1% Subsingleton.to_countable 1 := fun h => nCtR (@h ℝ)

-- `Subtype.countable` idx 1: ℝ with p = True
theorem w0_42 : ¬ drop1% Subtype.countable 1 := fun h => by
  have := @h ℝ (fun _ => True)
  exact nCtR (Function.Injective.countable (f := fun x : ℝ => (⟨x, trivial⟩ : {x : ℝ // True}))
    (fun a b hab => congrArg Subtype.val hab))

-- `Finite.to_countable` idx 1: ℝ
theorem w0_43 : ¬ drop1% Finite.to_countable 1 := fun h => nCtR (@h ℝ)

-- `Quotient.countable` idx 1: Quot Eq on ℝ
theorem w0_44 : ¬ drop1% Quotient.countable 1 := fun h => by
  have := @h ℝ Eq
  exact nCtR (Function.Surjective.countable (f := Quot.lift (r := Eq) id (fun _ _ h => h))
    (fun x => ⟨Quot.mk _ x, rfl⟩))

-- `instCountableQuotient` idx 1: Quotient by equality on ℝ
theorem w0_45 : ¬ drop1% instCountableQuotient 1 := fun h => by
  let s : Setoid ℝ := ⟨Eq, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  have := @h ℝ s
  exact nCtR (Function.Surjective.countable (f := Quotient.lift (s := s) id (fun _ _ h => h))
    (fun x => ⟨Quotient.mk s x, rfl⟩))

-- `not_uncountable` idx 1: ℝ
theorem w0_46 : ¬ drop1% not_uncountable 1 := fun h => @h ℝ uR

-- `Function.Injective.uncountable` idx 4: constant ℝ → Unit
theorem w0_47 : ¬ drop1% Function.Injective.uncountable 4 := fun h =>
  (@h ℝ Unit uR (fun _ => ())).not_countable inferInstance

-- `Function.Surjective.uncountable` idx 4: constant Unit → ℝ
theorem w0_48 : ¬ drop1% Function.Surjective.uncountable 4 := fun h =>
  (@h Unit ℝ uR (fun _ => 0)).not_countable inferInstance

-- `not_injective_uncountable_countable` idx 3: id on ℝ
theorem w0_49 : ¬ drop1% not_injective_uncountable_countable 3 := fun h =>
  @h ℝ ℝ uR id Function.injective_id

-- `not_surjective_countable_uncountable` idx 2: id on ℝ
theorem w0_50 : ¬ drop1% not_surjective_countable_uncountable 2 := fun h =>
  @h ℝ ℝ uR id Function.surjective_id

-- `uncountable_iff_forall_not_surjective` idx 1: α empty
theorem w0_51 : ¬ drop1% uncountable_iff_forall_not_surjective 1 := fun h =>
  ((@h Empty).mpr (fun f => (f 0).elim)).not_countable inferInstance

-- `instInfiniteOfUncountable` idx 1: Unit
theorem w0_52 : ¬ drop1% instInfiniteOfUncountable 1 := fun h =>
  (@h Unit).not_finite inferInstance

-- `Countable.toSmall` idx 1: α = Type (not small in Type)
theorem w0_53 : ¬ ∀ (α : Type 1), Small.{0} α := fun h => not_small_type.{0, 0} (h Type)

-- `Nat.Subtype.succ_le_of_lt` idx 1: s = {0, 1}, y = 0 < x = 1
theorem w0_54 : ¬ indep0% Nat.Subtype.succ_le_of_lt 1 := fun h =>
  finSet01 (@h {0, 1} (Classical.decPred _) ⟨1, by simp⟩ ⟨0, by simp⟩ Nat.one_pos)

-- `Nat.Subtype.succ_le_of_lt` idx 5: x = y in univ
theorem w0_55 : ¬ drop0% Nat.Subtype.succ_le_of_lt 5 := fun h =>
  let y : ↑(Set.univ : Set ℕ) := ⟨0, trivial⟩
  absurd (@h Set.univ infU (Classical.decPred _) y y)
    (not_le.mpr (@Nat.Subtype.lt_succ_self _ infU (Classical.decPred _) y))

-- `Nat.Subtype.le_succ_of_forall_lt_le` idx 1: s = {0}
theorem w0_56 : ¬ indep0% Nat.Subtype.le_succ_of_forall_lt_le 1 := fun h =>
  finSet0 (@h {0} (Classical.decPred _) ⟨0, rfl⟩ ⟨0, rfl⟩
    (fun z hz => le_of_eq (Subtype.ext (Set.mem_singleton_iff.mp z.2))))

-- `Nat.Subtype.le_succ_of_forall_lt_le` idx 5: x = succ (succ y) in univ
theorem w0_57 : ¬ drop0% Nat.Subtype.le_succ_of_forall_lt_le 5 := fun h =>
  let y : ↑(Set.univ : Set ℕ) := ⟨0, trivial⟩
  letI := Classical.decPred (· ∈ (Set.univ : Set ℕ))
  absurd (@h Set.univ infU _ (@Nat.Subtype.succ _ infU _ (@Nat.Subtype.succ _ infU _ y)) y)
    (not_le.mpr (@Nat.Subtype.lt_succ_self _ infU _ _))

-- `Nat.Subtype.lt_succ_self` idx 1: s = {0}
theorem w0_58 : ¬ indep0% Nat.Subtype.lt_succ_self 1 := fun h =>
  finSet0 (@h {0} (Classical.decPred _) ⟨0, rfl⟩)

-- `Nat.Subtype.lt_succ_iff_le` idx 1: s = {0}
theorem w0_59 : ¬ indep0% Nat.Subtype.lt_succ_iff_le 1 := fun h =>
  finSet0 (@h {0} (Classical.decPred _) ⟨0, rfl⟩ ⟨0, rfl⟩)

-- `Nat.Subtype.ofNat_surjective` idx 1: s = ∅
theorem w0_60 : ¬ indep0% Nat.Subtype.ofNat_surjective 1 := fun h =>
  finSetE (@h ∅ (Classical.decPred _))

-- `Nat.Subtype.ofNat_range` idx 1: s = ∅
theorem w0_61 : ¬ indep0% Nat.Subtype.ofNat_range 1 := fun h =>
  finSetE (@h ∅ (Classical.decPred _))

-- `Nat.Subtype.coe_comp_ofNat_range` idx 1: s = ∅
theorem w0_62 : ¬ indep0% Nat.Subtype.coe_comp_ofNat_range 1 := fun h =>
  finSetE (@h ∅ (Classical.decPred _))

-- `_private.Mathlib.Basic.Denumerable.0.Nat.Subtype.right_inverse_aux` idx 1: s = ∅
theorem w0_63 : ¬ indep0% _private.Mathlib.Basic.Denumerable.«0».Nat.Subtype.right_inverse_aux 1 :=
  fun h => finSetE (@h ∅ (Classical.decPred _) 0)

-- `nonempty_denumerable` idx 1: α = ℝ
theorem w0_64 : ¬ drop0% nonempty_denumerable 1 := fun h => by
  letI := (h ℝ).some; exact nCtR inferInstance

-- `nonempty_denumerable` idx 2: α = Unit
theorem w0_65 : ¬ drop0% nonempty_denumerable 2 := fun h =>
  Nat.zero_ne_one ((@Denumerable.eqv Unit (h Unit).some).symm.injective (Subsingleton.elim _ _))

-- `nonempty_equiv_of_countable` idx 2: ℝ ≃ ℕ
theorem w0_66 : ¬ drop0% nonempty_equiv_of_countable 2 := fun h =>
  nCtR ((@h ℝ ℕ _ _ _).some.injective.countable)

-- `nonempty_equiv_of_countable` idx 3: Unit ≃ ℕ
theorem w0_67 : ¬ drop0% nonempty_equiv_of_countable 3 := fun h =>
  Nat.zero_ne_one ((@h Unit ℕ _ _ _).some.symm.injective (Subsingleton.elim _ _))

-- `nonempty_equiv_of_countable` idx 4: ℕ ≃ ℝ
theorem w0_68 : ¬ drop0% nonempty_equiv_of_countable 4 := fun h =>
  nCtR ((@h ℕ ℝ _ _ _).some.symm.injective.countable)

-- `nonempty_equiv_of_countable` idx 5: ℕ ≃ Unit
theorem w0_69 : ¬ drop0% nonempty_equiv_of_countable 5 := fun h =>
  Nat.zero_ne_one ((@h ℕ Unit _ _ _).some.injective (Subsingleton.elim _ _))

-- `ENNReal.instIsScalarTowerNNReal` idx 5: ENNReal acting on itself by m • n = n
theorem w0_70 : ¬ drop0% ENNReal.instIsScalarTowerNNReal 5 := fun h => by
  have := (@h ℝ≥0∞ ℝ≥0∞ _ _ ⟨fun _ n => n⟩).smul_assoc (0 : ℝ≥0) (1 : ℝ≥0∞) (1 : ℝ≥0∞)
  change (1 : ℝ≥0∞) = (0 : ℝ≥0) • (1 : ℝ≥0∞) at this
  simp at this

-- `ENNReal.smulCommClass_left` idx 4: m • n = 1
theorem w0_71 : ¬ drop0% ENNReal.smulCommClass_left 4 := fun h => by
  have := (@h ℝ≥0∞ ℝ≥0∞ _ ⟨fun _ _ => 1⟩).smul_comm (0 : ℝ≥0) (1 : ℝ≥0∞) (1 : ℝ≥0∞)
  change (0 : ℝ≥0) • (1 : ℝ≥0∞) = 1 at this
  simp at this

-- `ENNReal.smulCommClass_right` idx 4: m • n = 1
theorem w0_72 : ¬ drop0% ENNReal.smulCommClass_right 4 := fun h => by
  have := (@h ℝ≥0∞ ℝ≥0∞ _ ⟨fun _ _ => 1⟩).smul_comm (1 : ℝ≥0∞) (0 : ℝ≥0) (1 : ℝ≥0∞)
  change (1 : ℝ≥0∞) = (0 : ℝ≥0) • (1 : ℝ≥0∞) at this
  simp at this

-- `ENNReal.coe_smul` idx 5: removable, the tower R ℝ≥0 ℝ≥0∞ applied to s and 1 gives the claim
theorem w0_73 : drop% ENNReal.coe_smul 5 := by
  intro R r s _ _ _
  have := smul_assoc r s (1 : ℝ≥0∞)
  simp only [ENNReal.smul_def, smul_eq_mul, mul_one] at this
  exact this

-- `ENNReal.coe_smul` idx 6: ℝ≥0 acting on ℝ≥0∞ by the constant 0
theorem w0_74 : ¬ drop0% ENNReal.coe_smul 6 := fun h => by
  have := @h ℝ≥0 1 1 _ ⟨fun _ _ => 0⟩ _
  change (((1 : ℝ≥0) • (1 : ℝ≥0) : ℝ≥0) : ℝ≥0∞) = 0 at this
  simp at this

-- `ENNReal.smul_top` idx 2: R = ℕ × ℕ acting through the first factor; (0, 1) • ⊤ = 0
theorem w0_75 : ¬ drop0% ENNReal.smul_top 2 := fun h => by
  let φ : ℕ × ℕ →+* ℝ≥0∞ := (Nat.castRingHom ℝ≥0∞).comp (RingHom.fst ℕ ℕ)
  letI M : Module (ℕ × ℕ) ℝ≥0∞ := Module.compHom ℝ≥0∞ φ
  have T : IsScalarTower (ℕ × ℕ) ℝ≥0∞ ℝ≥0∞ := ⟨fun c x y => mul_assoc (φ c) x y⟩
  have F : Module.IsTorsionFree (ℕ × ℕ) ℝ≥0∞ := ⟨fun r hr x y hxy => by
    have ha : r.1 ≠ 0 := by
      intro h0
      have := hr.1 (show r * (1, 0) = r * (0, 0) by ext <;> simp [h0])
      simp at this
    change (r.1 : ℝ≥0∞) * x = (r.1 : ℝ≥0∞) * y at hxy
    exact (ENNReal.mul_right_inj (by exact_mod_cast ha) (ENNReal.natCast_ne_top _)).mp hxy⟩
  have := @h (ℕ × ℕ) _ M T F (Classical.decEq _) (0, 1)
  rw [if_neg (by simp)] at this
  change φ (0, 1) * ⊤ = ⊤ at this
  simp [φ] at this

-- `ENNReal.smul_top` idx 4: removable, c ≠ 0 acts injectively (IsDomain + torsion-free), and c • ⊤ = c • ⊤ + c • ⊤ forces c • ⊤ ∈ {0, ⊤}; 0 is excluded by injectivity
theorem w0_76 : drop% ENNReal.smul_top 4 := by
  intro R _ _ _ _ _ c
  split_ifs with hc
  · subst hc; exact zero_smul _ _
  · have hinj : Function.Injective (fun x : ℝ≥0∞ => c • x) := smul_right_injective ℝ≥0∞ hc
    by_contra hne
    have h2 : c • (⊤ : ℝ≥0∞) + c • ⊤ = c • ⊤ + 0 := by rw [← smul_add, top_add, add_zero]
    have h0 : c • (⊤ : ℝ≥0∞) = 0 := (ENNReal.add_right_inj hne).mp h2
    exact ENNReal.top_ne_zero (hinj (h0.trans (smul_zero c).symm))

-- `ENNReal.smul_top` idx 5: R = ℕ[X] acting through evaluation at 0; X • ⊤ = 0
theorem w0_77 : ¬ drop0% ENNReal.smul_top 5 := fun h => by
  let φ : Polynomial ℕ →+* ℝ≥0∞ := Polynomial.eval₂RingHom (Nat.castRingHom ℝ≥0∞) 0
  letI M : Module (Polynomial ℕ) ℝ≥0∞ := Module.compHom ℝ≥0∞ φ
  have T : IsScalarTower (Polynomial ℕ) ℝ≥0∞ ℝ≥0∞ := ⟨fun c x y => mul_assoc (φ c) x y⟩
  have := @h (Polynomial ℕ) _ _ M T (Classical.decEq _) Polynomial.X
  rw [if_neg Polynomial.X_ne_zero] at this
  change φ Polynomial.X * ⊤ = ⊤ at this
  simp [φ] at this

-- `ENNReal.coe_comp_toNNReal_comp` idx 2: f = ⊤
theorem w0_78 : ¬ drop0% ENNReal.coe_comp_toNNReal_comp 2 := fun h => by
  have := congrFun (@h Unit (fun _ => ⊤)) (); simp at this

-- `ENNReal.coe_sSup` idx 1: s = univ
theorem w0_79 : ¬ drop0% ENNReal.coe_sSup 1 := fun h => by
  have := @h Set.univ
  have ht : (⨆ a ∈ (Set.univ : Set ℝ≥0), (a : ℝ≥0∞)) = ⊤ := by
    simp only [Set.mem_univ, iSup_pos]
    exact (ENNReal.iSup_coe_eq_top (f := fun a : ℝ≥0 => a)).mpr (by simp [not_bddAbove_univ])
  rw [ht] at this; exact ENNReal.coe_ne_top this

-- `ENNReal.coe_iSup` idx 2: ι = ℕ, f = cast
theorem w0_80 : ¬ drop1% ENNReal.coe_iSup 2 := fun h => by
  have := @h ℕ (fun n => (n : ℝ≥0))
  simp only [ENNReal.coe_natCast, ENNReal.iSup_natCast] at this
  exact ENNReal.coe_ne_top this

-- `ENNReal.coe_iInf` idx 1: ι empty
theorem w0_81 : ¬ drop0% ENNReal.coe_iInf 1 := fun h => by
  have := @h False (fun e => e.elim)
  have h2 : (⨅ a : False, ((a.elim : ℝ≥0) : ℝ≥0∞)) = ⊤ := iInf_of_empty _
  rw [h2] at this
  exact ENNReal.coe_ne_top this

-- `Set.OrdConnected.preimage_coe_nnreal_ennreal` idx 1: u = {0, 2}
theorem w0_82 : ¬ drop0% Set.OrdConnected.preimage_coe_nnreal_ennreal 1 := fun h => by
  have := (@h {0, 2}).out (x := 0) (y := 2) (by simp) (by simp) (show (1 : ℝ≥0) ∈ Set.Icc 0 2 by norm_num)
  norm_num at this

-- `Set.OrdConnected.image_coe_nnreal_ennreal` idx 1: t = {0, 2}
theorem w0_83 : ¬ drop0% Set.OrdConnected.image_coe_nnreal_ennreal 1 := fun h => by
  have := (@h {0, 2}).out (x := 0) (y := 2) (by simp) (by simp) (show (1 : ℝ≥0∞) ∈ Set.Icc 0 2 by norm_num)
  norm_num at this

-- `Set.OrdConnected.preimage_ennreal_ofReal` idx 1: u = {0, 2}
theorem w0_84 : ¬ drop0% Set.OrdConnected.preimage_ennreal_ofReal 1 := fun h => by
  have := (@h {0, 2}).out (x := 0) (y := 2) (by simp) (by simp) (show (1 : ℝ) ∈ Set.Icc 0 2 by norm_num)
  norm_num at this

-- `Set.OrdConnected.image_ennreal_ofReal` idx 1: s = {0, 2}
theorem w0_85 : ¬ drop0% Set.OrdConnected.image_ennreal_ofReal 1 := fun h => by
  have := (@h {0, 2}).out (x := 0) (y := 2) (by simp) (by simp) (show (1 : ℝ≥0∞) ∈ Set.Icc 0 2 by norm_num)
  norm_num at this

-- `ENNReal.ofReal_prod_of_nonneg` idx 3: f = -1 on Bool
theorem w0_86 : ¬ drop0% ENNReal.ofReal_prod_of_nonneg 3 := fun h => by
  have := @h Bool Finset.univ (fun _ => -1)
  simp [Fintype.prod_bool, ENNReal.ofReal_of_nonpos (show (-1 : ℝ) ≤ 0 by norm_num)] at this

-- `ENNReal.iInf_sum` idx 4: ι empty, s = ∅
theorem w0_87 : ¬ drop0% ENNReal.iInf_sum 4 := fun h => by
  have := @h Empty Unit (fun e => e.elim) ∅ (fun _ i => i.elim); simp at this

-- `ENNReal.iInf_sum` idx 5: f i a = [i ≠ a] on Bool
theorem w0_88 : ¬ drop0% ENNReal.iInf_sum 5 := fun h => by
  have := @h Bool Bool (fun i a => if i = a then 0 else 1) Finset.univ inferInstance
  simp [Fintype.sum_bool, iInf_bool_eq] at this

-- `ENNReal.prod_ne_top` idx 3: f = ⊤
theorem w0_89 : ¬ drop0% ENNReal.prod_ne_top 3 := fun h => by
  have := @h Unit {()} (fun _ => ⊤); simp at this

-- `ENNReal.prod_lt_top` idx 3: f = ⊤
theorem w0_90 : ¬ drop0% ENNReal.prod_lt_top 3 := fun h => by
  have := @h Unit {()} (fun _ => ⊤); simp at this

-- `ENNReal.lt_top_of_sum_ne_top` idx 3: f = ⊤
theorem w0_91 : ¬ drop0% ENNReal.lt_top_of_sum_ne_top 3 := fun h => by
  have := @h Unit {()} (fun _ => ⊤) () (by simp); simp at this

-- `ENNReal.lt_top_of_sum_ne_top` idx 5: s = ∅, f = ⊤
theorem w0_92 : ¬ drop0% ENNReal.lt_top_of_sum_ne_top 5 := fun h => by
  have := @h Unit ∅ (fun _ => ⊤) (by simp) (); simp at this

-- `ENNReal.toNNReal_sum` idx 3: f = (⊤, 1)
theorem w0_93 : ¬ drop0% ENNReal.toNNReal_sum 3 := fun h => by
  have := @h Bool Finset.univ (fun b => if b then ⊤ else 1); simp [Fintype.sum_bool] at this

-- `ENNReal.toReal_sum` idx 3: f = (⊤, 1)
theorem w0_94 : ¬ drop0% ENNReal.toReal_sum 3 := fun h => by
  have := @h Bool Finset.univ (fun b => if b then ⊤ else 1); simp [Fintype.sum_bool] at this

-- `ENNReal.ofReal_sum_of_nonneg` idx 3: f = (1, -1)
theorem w0_95 : ¬ drop0% ENNReal.ofReal_sum_of_nonneg 3 := fun h => by
  have := @h Bool Finset.univ (fun b => if b then 1 else -1)
  simp [Fintype.sum_bool, ENNReal.ofReal_of_nonpos (show (-1 : ℝ) ≤ 0 by norm_num)] at this

-- `ENNReal.sum_lt_sum_of_nonempty` idx 5: f = g = 0
theorem w0_96 : ¬ drop0% ENNReal.sum_lt_sum_of_nonempty 5 := fun h => by
  have := @h Unit {()} (by simp) 0 0; simp at this

-- `ENNReal.exists_le_of_sum_le` idx 5: f = 1, g = 0
theorem w0_97 : ¬ drop0% ENNReal.exists_le_of_sum_le 5 := fun h => by
  have := @h Unit {()} (by simp) 1 0; simp at this

-- `ENNReal.prod_inv_distrib` idx 3: f = (0, ⊤)
theorem w0_98 : ¬ drop0% ENNReal.prod_inv_distrib 3 := fun h => by
  have := @h Bool (fun b => if b then 0 else ⊤) Finset.univ; simp [Fintype.prod_bool] at this

-- `ENNReal.prod_div_distrib` idx 4: f = 1, g = (0, ⊤)
theorem w0_99 : ¬ drop0% ENNReal.prod_div_distrib 4 := fun h => by
  have := @h Bool (fun _ => 1) (fun b => if b then 0 else ⊤) Finset.univ; simp [Fintype.prod_bool] at this

-- `ENNReal.prod_div_distrib_of_ne_top` idx 4: f = 1, g = (0, ⊤)
theorem w0_100 : ¬ drop0% ENNReal.prod_div_distrib_of_ne_top 4 := fun h => by
  have := @h Bool (fun _ => 1) (fun b => if b then 0 else ⊤) Finset.univ; simp [Fintype.prod_bool] at this

-- `ENNReal.prod_div_distrib_of_ne_zero` idx 4: f = 1, g = (0, ⊤)
theorem w0_101 : ¬ drop0% ENNReal.prod_div_distrib_of_ne_zero 4 := fun h => by
  have := @h Bool (fun _ => 1) (fun b => if b then 0 else ⊤) Finset.univ; simp [Fintype.prod_bool] at this

-- `ENNReal.finsetSum_iSup` idx 4: f a i = [a = i] on Bool
theorem w0_102 : ¬ drop0% ENNReal.finsetSum_iSup 4 := fun h => by
  have := @h Bool Bool Finset.univ (fun a i => if a = i then 1 else 0)
  simp [Fintype.sum_bool, iSup_bool_eq] at this

-- `ENNReal.finsetSum_iSup_of_monotone` idx 3: ι = Unit ⊕ Unit (not directed, every map monotone)
theorem w0_103 : ¬ drop0% ENNReal.finsetSum_iSup_of_monotone 3 := fun h => by
  have := @h (Unit ⊕ Unit) (Unit ⊕ Unit) _ Finset.univ (fun a i => if a = i then 1 else 0)
    (fun a i j hij => by rw [u2_le i j hij])
  simp [Fintype.sum_sum_type, iSup_sum] at this

-- `ENNReal.finsetSum_iSup_of_monotone` idx 6: f a i = [a = i] on Bool
theorem w0_104 : ¬ drop0% ENNReal.finsetSum_iSup_of_monotone 6 := fun h => by
  have := @h Bool Bool _ _ Finset.univ (fun a i => if a = i then 1 else 0)
  simp [Fintype.sum_bool, iSup_bool_eq] at this

-- `ENNReal.HolderTriple.holderConjugate_div_div` idx 3: p = q = r = 1
theorem w0_105 : ¬ drop0% ENNReal.HolderTriple.holderConjugate_div_div 3 := fun h => by
  have := ENNReal.holderConjugate_iff.mp (h 1 1 1 one_ne_zero one_ne_top); norm_num at this

-- `ENNReal.HolderTriple.holderConjugate_div_div` idx 4: p = q = r = 0
theorem w0_106 : ¬ drop0% ENNReal.HolderTriple.holderConjugate_div_div 4 := fun h => by
  have := ENNReal.holderConjugate_iff.mp (@h 0 0 0 ⟨by simp⟩ zero_ne_top); simp at this

-- `ENNReal.HolderTriple.holderConjugate_div_div` idx 5: p = q = r = ⊤
theorem w0_107 : ¬ drop0% ENNReal.HolderTriple.holderConjugate_div_div 5 := fun h => by
  have := ENNReal.holderConjugate_iff.mp (@h ⊤ ⊤ ⊤ ⟨by simp⟩ top_ne_zero); simp at this

-- `ENNReal.div_mul_div_cancel` idx 4: b = ⊤
theorem w0_108 : ¬ drop0% ENNReal.div_mul_div_cancel 4 := fun h => by
  have := @h 1 ⊤ 1 top_ne_zero; simp at this

-- `ENNReal.inv_mul_le_iff` idx 4: x = ⊤
theorem w0_109 : ¬ drop0% ENNReal.inv_mul_le_iff 4 := fun h => by
  have := @h ⊤ 1 0 top_ne_zero; simp at this

-- `ENNReal.mul_inv_le_iff` idx 4: y = ⊤
theorem w0_110 : ¬ drop0% ENNReal.mul_inv_le_iff 4 := fun h => by
  have := @h 1 ⊤ 0 top_ne_zero; simp at this

-- `ENNReal.div_le_iff` idx 4: y = ⊤
theorem w0_111 : ¬ drop0% ENNReal.div_le_iff 4 := fun h => by
  have := @h 1 ⊤ 0 top_ne_zero; simp at this

-- `ENNReal.div_le_iff'` idx 4: y = ⊤
theorem w0_112 : ¬ drop0% ENNReal.div_le_iff' 4 := fun h => by
  have := @h 1 ⊤ 0 top_ne_zero; simp at this

-- `ENNReal.mul_div_mul_left` idx 4: c = ⊤
theorem w0_113 : ¬ drop0% ENNReal.mul_div_mul_left 4 := fun h => by
  have := @h ⊤ 1 1 top_ne_zero; simp at this

-- `ENNReal.mul_div_mul_right` idx 4: c = ⊤
theorem w0_114 : ¬ drop0% ENNReal.mul_div_mul_right 4 := fun h => by
  have := @h ⊤ 1 1 top_ne_zero; simp at this

-- `ENNReal.sub_div` idx 3: a = ⊤, b = 1, c = 0
theorem w0_115 : ¬ drop0% ENNReal.sub_div 3 := fun h => by
  have := @h ⊤ 1 0; simp at this

-- `ENNReal.le_div_iff_mul_le` idx 4: b = c = ⊤
theorem w0_116 : ¬ drop0% ENNReal.le_div_iff_mul_le 4 := fun h => by
  have := @h 1 ⊤ ⊤ (Or.inl top_ne_zero); simp at this

-- `ENNReal.div_le_iff_le_mul` idx 4: b = ⊤, c = 0
theorem w0_117 : ¬ drop0% ENNReal.div_le_iff_le_mul 4 := fun h => by
  have := @h 1 ⊤ 0 (Or.inl top_ne_zero); simp at this

-- `ENNReal.lt_div_iff_mul_lt` idx 4: b = ⊤, c = 0
theorem w0_118 : ¬ drop0% ENNReal.lt_div_iff_mul_lt 4 := fun h => by
  have := @h 1 ⊤ 0 (Or.inl top_ne_zero); simp at this

-- `ENNReal.div_lt_iff` idx 4: b = c = ⊤
theorem w0_119 : ¬ drop0% ENNReal.div_lt_iff 4 := fun h => by
  have := @h 1 ⊤ ⊤ (Or.inl top_ne_zero); simp at this

-- `ENNReal.div_lt_div_iff_left` idx 4: c = ⊤
theorem w0_120 : ¬ drop0% ENNReal.div_lt_div_iff_left 4 := fun h => by
  have := @h 1 2 ⊤ top_ne_zero; simp at this

-- `ENNReal.div_lt_div_iff_right` idx 4: a = ⊤
theorem w0_121 : ¬ drop0% ENNReal.div_lt_div_iff_right 4 := fun h => by
  have := @h ⊤ 2 1 top_ne_zero; simp [ENNReal.top_div] at this

-- `ENNReal.div_lt_div_right` idx 3: c = 0
theorem w0_122 : ¬ drop0% ENNReal.div_lt_div_right 3 := fun h => by
  have := @h 1 2 0 zero_ne_top one_lt_two; simp at this

-- `ENNReal.div_lt_div_right` idx 4: c = ⊤
theorem w0_123 : ¬ drop0% ENNReal.div_lt_div_right 4 := fun h => by
  have := @h 1 2 ⊤ top_ne_zero one_lt_two; simp at this

-- `ENNReal.div_lt_div_left` idx 4: a = ⊤
theorem w0_124 : ¬ drop0% ENNReal.div_lt_div_left 4 := fun h => by
  have := @h ⊤ 2 1 top_ne_zero one_lt_two; simp [ENNReal.top_div] at this

-- `ENNReal.exists_pos_mul_lt` idx 2: a = ⊤
theorem w0_125 : ¬ drop0% ENNReal.exists_pos_mul_lt 2 := fun h => by
  obtain ⟨c, hc, hlt⟩ := @h ⊤ 1 one_ne_zero
  rw [ENNReal.mul_top hc.ne'] at hlt; simp at hlt

-- `ENNReal.mul_le_iff_le_inv` idx 4: r = ⊤
theorem w0_126 : ¬ drop0% ENNReal.mul_le_iff_le_inv 4 := fun h => by
  have := @h 1 ⊤ ⊤ top_ne_zero; simp at this

-- `ENNReal.eq_div_iff` idx 4: a = ⊤
theorem w0_127 : ¬ drop0% ENNReal.eq_div_iff 4 := fun h => by
  have := @h ⊤ 1 ⊤ top_ne_zero; simp at this

-- `ENNReal.div_eq_div_iff` idx 5: a = ⊤, b = 1, c = 0, d = 1
theorem w0_128 : ¬ drop0% ENNReal.div_eq_div_iff 5 := fun h => by
  have := @h ⊤ 1 0 1 top_ne_zero one_ne_zero one_ne_top; simp at this

-- `ENNReal.div_eq_div_iff` idx 7: a = 1, b = ⊤, c = 1, d = 0
theorem w0_129 : ¬ drop0% ENNReal.div_eq_div_iff 7 := fun h => by
  have := @h 1 ⊤ 1 0 one_ne_zero one_ne_top top_ne_zero; simp at this

-- `ENNReal.div_mul` idx 4: b = c = ⊤
theorem w0_130 : ¬ drop0% ENNReal.div_mul 4 := fun h => by
  have := @h ⊤ ⊤ 1 (Or.inl top_ne_zero); simp at this

-- `ENNReal.mul_div_mul_comm` idx 4: c = 0, d = ⊤
theorem w0_131 : ¬ drop0% ENNReal.mul_div_mul_comm 4 := fun h => by
  have := @h 1 1 0 ⊤ (Or.inl zero_ne_top); simp at this

-- `ENNReal.mul_div_mul_comm` idx 5: c = ⊤, d = 0
theorem w0_132 : ¬ drop0% ENNReal.mul_div_mul_comm 5 := fun h => by
  have := @h 1 1 ⊤ 0 (Or.inl top_ne_zero); simp at this

-- `ENNReal.half_lt_self` idx 2: a = ⊤
theorem w0_133 : ¬ drop0% ENNReal.half_lt_self 2 := fun h => by
  have := @h ⊤ top_ne_zero; simp [ENNReal.top_div] at this

-- `ENNReal.sub_half` idx 1: a = ⊤
theorem w0_134 : ¬ drop0% ENNReal.sub_half 1 := fun h => by
  have := @h ⊤; simp [ENNReal.top_div] at this

-- `ENNReal.le_mul_of_forall_lt` idx 3: a = 0, b = ⊤, c = 1
theorem w0_135 : ¬ drop0% ENNReal.le_mul_of_forall_lt 3 := fun h => by
  have := @h 0 ⊤ 1 (Or.inl zero_ne_top) (fun a' _ b' hb' => (not_top_lt hb').elim); simp at this

-- `ENNReal.le_mul_of_forall_lt` idx 4: a = ⊤, b = 0, c = 1
theorem w0_136 : ¬ drop0% ENNReal.le_mul_of_forall_lt 4 := fun h => by
  have := @h ⊤ 0 1 (Or.inl top_ne_zero) (fun a' ha' => (not_top_lt ha').elim); simp at this

-- `ENNReal.exists_nnreal_pos_mul_lt` idx 2: a = ⊤
theorem w0_137 : ¬ drop0% ENNReal.exists_nnreal_pos_mul_lt 2 := fun h => by
  obtain ⟨n, hn, hlt⟩ := @h ⊤ 1 one_ne_zero
  rw [ENNReal.mul_top (by simpa using hn.ne')] at hlt; simp at hlt

-- `ENNReal.coe_zpow` idx 1: r = 0, n = -1
theorem w0_138 : ¬ drop0% ENNReal.coe_zpow 1 := fun h => by
  have := @h 0 (-1); simp [zpow_neg_one, oz] at this

-- `ENNReal.zpow_pos` idx 2: a = ⊤, n = -1
theorem w0_139 : ¬ drop0% ENNReal.zpow_pos 2 := fun h => by
  have := @h ⊤ top_ne_zero (-1); simp [zpow_neg_one, oz] at this

-- `ENNReal.zpow_lt_top` idx 1: a = 0, n = -1
theorem w0_140 : ¬ drop0% ENNReal.zpow_lt_top 1 := fun h => by
  have := @h 0 zero_ne_top (-1); simp [zpow_neg_one, oz] at this

-- `ENNReal.zpow_ne_top` idx 1: a = 0, n = -1
theorem w0_141 : ¬ drop0% ENNReal.zpow_ne_top 1 := fun h => by
  have := @h 0 zero_ne_top (-1); simp [zpow_neg_one, oz] at this

-- `ENNReal.exists_mem_Ico_zpow` idx 2: x = 0, y = 2
theorem w0_142 : ¬ drop0% ENNReal.exists_mem_Ico_zpow 2 := fun h => by
  obtain ⟨n, h1, -⟩ := @h 0 2 zero_ne_top one_lt_two (by norm_num)
  exact absurd h1 (not_le.mpr (ENNReal.zpow_pos (by norm_num) (by norm_num) n))

-- `ENNReal.exists_mem_Ico_zpow` idx 3: x = ⊤, y = 2
theorem w0_143 : ¬ drop0% ENNReal.exists_mem_Ico_zpow 3 := fun h => by
  obtain ⟨n, -, h2⟩ := @h ⊤ 2 top_ne_zero one_lt_two (by norm_num)
  exact not_top_lt h2

-- `ENNReal.exists_mem_Ico_zpow` idx 4: y = 1, x = 2
theorem w0_144 : ¬ drop0% ENNReal.exists_mem_Ico_zpow 4 := fun h => by
  obtain ⟨n, h1, h2⟩ := @h 2 1 (by norm_num) (by norm_num) one_ne_top
  simp [oz] at h2

-- `ENNReal.exists_mem_Ico_zpow` idx 5: removable, for y = ⊤ take n = -1 (x < 1) or n = 0 (x ≥ 1)
theorem w0_145 : drop% ENNReal.exists_mem_Ico_zpow 5 := by
  intro x y hx hxt hy
  by_cases hyt : y = ⊤
  · subst hyt
    by_cases hx1 : x < 1
    · exact ⟨-1, by simp [zpow_neg_one, hx1]⟩
    · exact ⟨0, by simp [not_lt.mp hx1, lt_top_iff_ne_top.mpr hxt]⟩
  · exact ENNReal.exists_mem_Ico_zpow hx hxt hy hyt

-- `ENNReal.exists_mem_Ioc_zpow` idx 3: x = ⊤, y = 2
theorem w0_146 : ¬ drop0% ENNReal.exists_mem_Ioc_zpow 3 := fun h => by
  obtain ⟨n, -, h2⟩ := @h ⊤ 2 top_ne_zero one_lt_two (by norm_num)
  exact (ENNReal.zpow_lt_top (a := 2) (by norm_num) (by norm_num) (n + 1)).ne (top_le_iff.mp h2)

-- `ENNReal.exists_mem_Ioc_zpow` idx 4: y = 1, x = 2
theorem w0_147 : ¬ drop0% ENNReal.exists_mem_Ioc_zpow 4 := fun h => by
  obtain ⟨n, h1, h2⟩ := @h 2 1 (by norm_num) (by norm_num) one_ne_top
  simp [oz] at h2

-- `ENNReal.exists_mem_Ioc_zpow` idx 5: removable, for y = ⊤ take n = -1 (x ≤ 1) or n = 0 (x > 1)
theorem w0_148 : drop% ENNReal.exists_mem_Ioc_zpow 5 := by
  intro x y hx hxt hy
  by_cases hyt : y = ⊤
  · subst hyt
    by_cases hx1 : x ≤ 1
    · exact ⟨-1, by simp [zpow_neg_one, hx1, pos_iff_ne_zero.mpr hx]⟩
    · exact ⟨0, by simp [not_le.mp hx1]⟩
  · exact ENNReal.exists_mem_Ioc_zpow hx hxt hy hyt

-- `ENNReal.Ioo_zero_top_eq_iUnion_Ico_zpow` idx 1: y = 1
theorem w0_149 : ¬ drop0% ENNReal.Ioo_zero_top_eq_iUnion_Ico_zpow 1 := fun h => by
  have h1 : (1 : ℝ≥0∞) ∈ Set.Ioo 0 ⊤ := by simp
  rw [@h 1 one_ne_top] at h1; simp [oz] at h1

-- `ENNReal.Ioo_zero_top_eq_iUnion_Ico_zpow` idx 2: y = ⊤, 0 lies in the n = -1 piece
theorem w0_150 : ¬ drop0% ENNReal.Ioo_zero_top_eq_iUnion_Ico_zpow 2 := fun h => by
  have h0 : (0 : ℝ≥0∞) ∈ ⋃ n : ℤ, Set.Ico ((⊤ : ℝ≥0∞) ^ n) (⊤ ^ (n + 1)) :=
    Set.mem_iUnion.mpr ⟨-1, by simp [zpow_neg_one]⟩
  rw [← @h ⊤ one_lt_top] at h0; simp at h0

-- `ENNReal.monotone_zpow` idx 1: x = 0
theorem w0_151 : ¬ drop0% ENNReal.monotone_zpow 1 := fun h => by
  have := @h 0 0 1 zero_le_one; simp at this

-- `ENNReal.zpow_add` idx 2: x = ⊤, m = 1, n = -1
theorem w0_152 : ¬ drop0% ENNReal.zpow_add 2 := fun h => by
  have := @h ⊤ top_ne_zero 1 (-1); simp [zpow_neg_one, oz] at this

-- `ENNReal.zpow_sub` idx 2: x = ⊤, m = n = 1
theorem w0_153 : ¬ drop0% ENNReal.zpow_sub 2 := fun h => by
  have := @h ⊤ top_ne_zero 1 1; simp [zpow_neg_one, oz] at this

-- `ENNReal.zpow_le_one_of_nonpos` idx 3: x = 0, n = -1
theorem w0_154 : ¬ drop0% ENNReal.zpow_le_one_of_nonpos 3 := fun h => by
  have := @h (-1) (by norm_num) 0; simp [zpow_neg_one, oz] at this

-- `ENNReal.mul_iInf'` idx 3: a = ⊤, f n = 1/n on ℕ
theorem w0_155 : ¬ drop1% ENNReal.mul_iInf' 3 := fun h => by
  have := @h ℕ (fun n => ((n : ℝ≥0∞))⁻¹) ⊤ (fun h0 => (top_ne_zero h0).elim)
  rw [infNat, topInv, mul_zero] at this; exact zero_ne_top this

-- `ENNReal.mul_iInf'` idx 4: a = 0, ι empty
theorem w0_156 : ¬ drop1% ENNReal.mul_iInf' 4 := fun h => by
  have := @h Empty (fun e => e.elim) 0 (fun h0 => (zero_ne_top h0).elim); simp at this

-- `ENNReal.iInf_mul'` idx 3: a = ⊤, f n = 1/n on ℕ
theorem w0_157 : ¬ drop1% ENNReal.iInf_mul' 3 := fun h => by
  have := @h ℕ (fun n => ((n : ℝ≥0∞))⁻¹) ⊤ (fun h0 => (top_ne_zero h0).elim)
  rw [infNat, invTop, zero_mul] at this; exact zero_ne_top this

-- `ENNReal.iInf_mul'` idx 4: a = 0, ι empty
theorem w0_158 : ¬ drop1% ENNReal.iInf_mul' 4 := fun h => by
  have := @h Empty (fun e => e.elim) 0 (fun h0 => (zero_ne_top h0).elim); simp at this

-- `ENNReal.mul_iInf_of_ne` idx 3: a = 0, ι empty
theorem w0_159 : ¬ drop1% ENNReal.mul_iInf_of_ne 3 := fun h => by
  have := @h Empty (fun e => e.elim) 0 zero_ne_top; simp at this

-- `ENNReal.mul_iInf_of_ne` idx 4: a = ⊤, f n = 1/n on ℕ
theorem w0_160 : ¬ drop1% ENNReal.mul_iInf_of_ne 4 := fun h => by
  have := @h ℕ (fun n => ((n : ℝ≥0∞))⁻¹) ⊤ top_ne_zero
  rw [infNat, topInv, mul_zero] at this; exact zero_ne_top this

-- `ENNReal.iInf_mul_of_ne` idx 3: a = 0, ι empty
theorem w0_161 : ¬ drop1% ENNReal.iInf_mul_of_ne 3 := fun h => by
  have := @h Empty (fun e => e.elim) 0 zero_ne_top; simp at this

-- `ENNReal.iInf_mul_of_ne` idx 4: a = ⊤, f n = 1/n on ℕ
theorem w0_162 : ¬ drop1% ENNReal.iInf_mul_of_ne 4 := fun h => by
  have := @h ℕ (fun n => ((n : ℝ≥0∞))⁻¹) ⊤ top_ne_zero
  rw [infNat, invTop, zero_mul] at this; exact zero_ne_top this

-- `ENNReal.mul_iInf` idx 3: a = 0, ι empty
theorem w0_163 : ¬ drop1% ENNReal.mul_iInf 3 := fun h => by
  have := @h Empty (fun e => e.elim) 0 (fun h0 => (zero_ne_top h0).elim); simp at this

-- `ENNReal.mul_iInf` idx 4: a = ⊤, f n = 1/n on ℕ
theorem w0_164 : ¬ drop1% ENNReal.mul_iInf 4 := fun h => by
  have := @h ℕ (fun n => ((n : ℝ≥0∞))⁻¹) ⊤ inferInstance
  rw [infNat, topInv, mul_zero] at this; exact zero_ne_top this

-- `ENNReal.iInf_mul` idx 3: a = 0, ι empty
theorem w0_165 : ¬ drop1% ENNReal.iInf_mul 3 := fun h => by
  have := @h Empty (fun e => e.elim) 0 (fun h0 => (zero_ne_top h0).elim); simp at this

-- `ENNReal.iInf_mul` idx 4: a = ⊤, f n = 1/n on ℕ
theorem w0_166 : ¬ drop1% ENNReal.iInf_mul 4 := fun h => by
  have := @h ℕ (fun n => ((n : ℝ≥0∞))⁻¹) ⊤ inferInstance
  rw [infNat, invTop, zero_mul] at this; exact zero_ne_top this

-- `ENNReal.iInf_div'` idx 3: a = 0, f n = 1/n on ℕ
theorem w0_167 : ¬ drop1% ENNReal.iInf_div' 3 := fun h => by
  have := @h ℕ (fun n => ((n : ℝ≥0∞))⁻¹) 0 (fun h0 => (zero_ne_top h0).elim)
  rw [infNat, invDiv0, ENNReal.zero_div] at this; exact zero_ne_top this

-- `ENNReal.iInf_div'` idx 4: a = ⊤, ι empty
theorem w0_168 : ¬ drop1% ENNReal.iInf_div' 4 := fun h => by
  have := @h Empty (fun e => e.elim) ⊤ (fun h0 => (top_ne_zero h0).elim); simp at this

-- `ENNReal.iInf_div_of_ne` idx 3: a = 0, f n = 1/n on ℕ
theorem w0_169 : ¬ drop1% ENNReal.iInf_div_of_ne 3 := fun h => by
  have := @h ℕ (fun n => ((n : ℝ≥0∞))⁻¹) 0 zero_ne_top
  rw [infNat, invDiv0, ENNReal.zero_div] at this; exact zero_ne_top this

-- `ENNReal.iInf_div_of_ne` idx 4: a = ⊤, ι empty
theorem w0_170 : ¬ drop1% ENNReal.iInf_div_of_ne 4 := fun h => by
  have := @h Empty (fun e => e.elim) ⊤ top_ne_zero; simp at this

-- `ENNReal.iInf_div` idx 3: a = ⊤, ι empty
theorem w0_171 : ¬ drop1% ENNReal.iInf_div 3 := fun h => by
  have := @h Empty (fun e => e.elim) ⊤ (fun h0 => (top_ne_zero h0).elim); simp at this

-- `ENNReal.iInf_div` idx 4: a = 0, f n = 1/n on ℕ
theorem w0_172 : ¬ drop1% ENNReal.iInf_div 4 := fun h => by
  have := @h ℕ (fun n => ((n : ℝ≥0∞))⁻¹) 0 inferInstance
  rw [infNat, invDiv0, ENNReal.zero_div] at this; exact zero_ne_top this

-- `ENNReal.le_iInf_mul_iInf` idx 5: ι empty, g = 0, a = 1
theorem w0_173 : ¬ drop1% ENNReal.le_iInf_mul_iInf 5 := fun h => by
  have := @h Empty Unit (fun e => e.elim) 1 (fun _ => 0) ⟨(), zero_ne_top⟩ (fun i => i.elim); simp at this

-- `ENNReal.le_iInf_mul_iInf` idx 6: κ empty, f = 0, a = 1
theorem w0_174 : ¬ drop1% ENNReal.le_iInf_mul_iInf 6 := fun h => by
  have := @h Unit Empty (fun _ => 0) 1 (fun e => e.elim) ⟨(), zero_ne_top⟩ (fun _ j => j.elim); simp at this

-- `ENNReal.iInf_mul_iInf` idx 3: f = ⊤, g n = 1/n on ℕ
theorem w0_175 : ¬ drop1% ENNReal.iInf_mul_iInf 3 := fun h => by
  have := @h ℕ (fun _ => ⊤) (fun n => ((n : ℝ≥0∞))⁻¹) ⟨1, by simp⟩
    (fun i j => ⟨i, by simp [ENNReal.top_mul (invNat_ne _)]⟩)
  simp only [iInf_const] at this
  rw [infNat, topInv, mul_zero] at this; exact zero_ne_top this

-- `ENNReal.iInf_mul_iInf` idx 4: f n = 1/n on ℕ, g = ⊤
theorem w0_176 : ¬ drop1% ENNReal.iInf_mul_iInf 4 := fun h => by
  have := @h ℕ (fun n => ((n : ℝ≥0∞))⁻¹) (fun _ => ⊤) ⟨1, by simp⟩
    (fun i j => ⟨i, by simp [ENNReal.mul_top (invNat_ne _)]⟩)
  simp only [iInf_const] at this
  rw [infNat, invTop, zero_mul] at this; exact zero_ne_top this

-- `ENNReal.iInf_mul_iInf` idx 5: f = (1, 2), g = (2, 1) on Bool
theorem w0_177 : ¬ drop1% ENNReal.iInf_mul_iInf 5 := fun h => by
  have := @h Bool (fun b => if b then 1 else 2) (fun b => if b then 2 else 1) ⟨true, by simp⟩ ⟨true, by simp⟩
  simp [iInf_bool_eq] at this

-- `ENNReal.smul_iSup` idx 3: Unit acting by the constant 1, ι empty
theorem w0_178 : ¬ drop0% ENNReal.smul_iSup 3 := fun h => by
  have := @h False Unit ⟨fun _ _ => 1⟩ (fun e => e.elim) ()
  simp only [iSup_of_empty, bot_eq_zero'] at this; exact one_ne_zero this

-- `ENNReal.smul_sSup` idx 2: Unit acting by the constant 1, s = ∅
theorem w0_179 : ¬ drop0% ENNReal.smul_sSup 2 := fun h => by
  have := @h Unit ⟨fun _ _ => 1⟩ ∅ ()
  simp only [sSup_empty, Set.mem_empty_iff_false, iSup_false, iSup_const, bot_eq_zero'] at this
  exact one_ne_zero this

-- `ENNReal.ofReal_div_le` idx 2: x = y = -1
theorem w0_180 : ¬ drop0% ENNReal.ofReal_div_le 2 := fun h => by
  have := @h (-1) (-1)
  simp [ENNReal.ofReal_of_nonpos (show (-1 : ℝ) ≤ 0 by norm_num)] at this

-- `ENNReal.ofReal_div_of_pos` idx 2: x = 1, y = 0
theorem w0_181 : ¬ drop0% ENNReal.ofReal_div_of_pos 2 := fun h => by
  have := @h 1 0; simp at this
