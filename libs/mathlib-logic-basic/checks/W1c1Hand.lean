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

namespace W1c1

-- Unit ⊕ Unit: no two distinct points are comparable, so every map is monotone
abbrev U2 := Unit ⊕ Unit
theorem u2_mono {β : Type*} [Preorder β] (f : U2 → β) : Monotone f := by
  intro a b hab
  rcases a with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rcases b with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp_all

-- an injection from an infinite type rules out finiteness of the target
theorem nf {α β : Sort*} [Infinite α] (f : α → β) (hf : Function.Injective f) : ¬ Finite β :=
  fun _ => Infinite.not_finite (Finite.of_injective f hf)

theorem finNE : Finite (ℕ × Empty) := Finite.of_injective (fun x => x.2) (fun a _ _ => a.2.elim)
theorem finEN : Finite (Empty × ℕ) := Finite.of_injective (fun x => x.1) (fun a _ _ => a.1.elim)

theorem nUP : ¬ (Set.univ ×ˢ Set.univ : Set (ℕ × Unit)).Finite := by
  rw [Set.univ_prod_univ]; exact Set.infinite_univ
theorem nUP' : ¬ (Set.univ ×ˢ Set.univ : Set (Unit × ℕ)).Finite := by
  rw [Set.univ_prod_univ]; exact Set.infinite_univ

-- swaps 0 ↔ n: infinitely many permutations of ℕ
def sw (n : ℕ) : ℕ ≃ ℕ := Equiv.swap 0 n
theorem sw_inj : Function.Injective sw := fun a b e => by
  have := DFunLike.congr_fun e 0
  simpa [sw] using this

-- ℕ with left-projection addition/multiplication: every permutation fixing nothing special is a hom
def LP := ℕ
instance : Add LP := ⟨fun a _ => a⟩
instance : Mul LP := ⟨fun a _ => a⟩
def lpA (n : ℕ) : LP ≃+ LP := { toEquiv := (Equiv.swap (0 : ℕ) n : ℕ ≃ ℕ), map_add' := fun _ _ => rfl }
def lpM (n : ℕ) : LP ≃* LP := { toEquiv := (Equiv.swap (0 : ℕ) n : ℕ ≃ ℕ), map_mul' := fun _ _ => rfl }
theorem lpA_inj : Function.Injective lpA := fun a b e => by
  have := DFunLike.congr_fun e (0 : ℕ)
  change Equiv.swap (0 : ℕ) a 0 = Equiv.swap (0 : ℕ) b 0 at this
  simpa using this
theorem lpM_inj : Function.Injective lpM := fun a b e => by
  have := DFunLike.congr_fun e (0 : ℕ)
  change Equiv.swap (0 : ℕ) a 0 = Equiv.swap (0 : ℕ) b 0 at this
  simpa using this

-- Bool-indexed family where q true holds for two proofs
theorem eu_q : ∃! x : Bool, ∃! hx : Bool, (x || hx) = true := by
  refine ⟨false, ⟨true, rfl, fun y hy => by simpa using hy⟩, fun y ⟨hy, h1, h2⟩ => ?_⟩
  cases y
  · rfl
  · exact absurd ((h2 false rfl).trans (h2 true rfl).symm) (by decide)

theorem finU : Finite Unit := inferInstance
theorem finImU : Finite ↑((fun _ : ℕ => ()) '' Set.univ) := Set.finite_coe_iff.mpr (Set.toFinite _)
theorem finRU : Finite ↑(Set.range (fun _ : ℕ => (⟨()⟩ : ULift.{1} Unit))) :=
  Set.finite_coe_iff.mpr (Set.toFinite _)

end W1c1

open W1c1


-- `ENNReal.mul_left_strictMono` idx 2: necessary (a = ⊤: 1 * ⊤ = 2 * ⊤)
theorem c1_0 : ¬ drop0% ENNReal.mul_left_strictMono 2 :=
  fun h => by have := @h ⊤ (by simp) 1 2 (by norm_num); simp at this

-- `ENNReal.mul_lt_mul_right` idx 4: necessary (a = ⊤, b = 1, c = 2)
theorem c1_1 : ¬ drop0% ENNReal.mul_lt_mul_right 4 :=
  fun h => by have := @h ⊤ 1 2 (by simp) (by norm_num); simp at this

-- `ENNReal.mul_lt_mul_left` idx 4: necessary (a = ⊤, b = 1, c = 2)
theorem c1_2 : ¬ drop0% ENNReal.mul_lt_mul_left 4 :=
  fun h => by have := @h ⊤ 1 2 (by simp) (by norm_num); simp at this

-- `ENNReal.mul_le_mul_iff_right` idx 4: necessary (a = ⊤, b = 2, c = 1)
theorem c1_3 : ¬ drop0% ENNReal.mul_le_mul_iff_right 4 :=
  fun h => by have := @h ⊤ 2 1 (by simp); norm_num at this

-- `ENNReal.mul_le_mul_iff_left` idx 4: necessary (c = ⊤, a = 2, b = 1)
theorem c1_4 : ¬ drop0% ENNReal.mul_le_mul_iff_left 4 :=
  fun h => by have := @h 2 1 ⊤ (by simp); norm_num at this

-- `ENNReal.mul_lt_mul_iff_right` idx 4: necessary (a = ⊤, b = 1, c = 2)
theorem c1_5 : ¬ drop0% ENNReal.mul_lt_mul_iff_right 4 :=
  fun h => by have := @h ⊤ 1 2 (by simp); norm_num at this

-- `ENNReal.mul_lt_mul_iff_left` idx 4: necessary (c = ⊤, a = 1, b = 2)
theorem c1_6 : ¬ drop0% ENNReal.mul_lt_mul_iff_left 4 :=
  fun h => by have := @h 1 2 ⊤ (by simp); norm_num at this

-- `ENNReal.le_of_add_le_add_left` idx 3: necessary (a = ⊤, b = 1, c = 0)
theorem c1_7 : ¬ drop0% ENNReal.le_of_add_le_add_left 3 :=
  fun h => by have := @h ⊤ 1 0 (by simp); norm_num at this

-- `ENNReal.le_of_add_le_add_right` idx 3: necessary (a = ⊤, b = 1, c = 0)
theorem c1_8 : ¬ drop0% ENNReal.le_of_add_le_add_right 3 :=
  fun h => by have := @h ⊤ 1 0 (by simp); norm_num at this

-- `ENNReal.add_lt_add_left` idx 3: necessary (a = ⊤, b = 0, c = 1)
theorem c1_9 : ¬ drop0% ENNReal.add_lt_add_left 3 :=
  fun h => by have := @h ⊤ 0 1 (by simp); norm_num at this

-- `ENNReal.add_lt_add_right` idx 3: necessary (a = ⊤, b = 0, c = 1)
theorem c1_10 : ¬ drop0% ENNReal.add_lt_add_right 3 :=
  fun h => by have := @h ⊤ 0 1 (by simp); norm_num at this

-- `ENNReal.add_lt_add_of_le_of_lt` idx 4: necessary (a = b = ⊤, c = 0, d = 1)
theorem c1_11 : ¬ drop0% ENNReal.add_lt_add_of_le_of_lt 4 :=
  fun h => by have := @h ⊤ ⊤ 0 1 le_rfl (by simp); norm_num at this

-- `ENNReal.add_lt_add_of_le_of_lt` idx 5: necessary (a = 2, b = 0, c = 0, d = 1)
theorem c1_12 : ¬ drop0% ENNReal.add_lt_add_of_le_of_lt 5 :=
  fun h => by have := @h 2 0 0 1 (by simp) (by simp); norm_num at this

-- `ENNReal.add_lt_add_of_lt_of_le` idx 4: necessary (c = d = ⊤, a = 0, b = 1)
theorem c1_13 : ¬ drop0% ENNReal.add_lt_add_of_lt_of_le 4 :=
  fun h => by have := @h 0 1 ⊤ ⊤ (by simp) le_rfl; norm_num at this

-- `ENNReal.add_lt_add_of_lt_of_le` idx 6: necessary (a = 0, b = 1, c = 5, d = 0)
theorem c1_14 : ¬ drop0% ENNReal.add_lt_add_of_lt_of_le 6 :=
  fun h => by have := @h 0 1 5 0 (by simp) (by simp); norm_num at this

-- `ENNReal.toReal_le_add_of_top_imp_top` idx 4: necessary (a = 1, b = ⊤, c = 0)
theorem c1_15 : ¬ drop0% ENNReal.toReal_le_add_of_top_imp_top 4 :=
  fun h => by have := @h 1 ⊤ 0 (by simp) (by simp); norm_num at this

-- `ENNReal.toReal_le_add_of_top_imp_top` idx 5: necessary (a = 1, b = 0, c = ⊤)
theorem c1_16 : ¬ drop0% ENNReal.toReal_le_add_of_top_imp_top 5 :=
  fun h => by have := @h 1 0 ⊤ (by simp) (by simp); norm_num at this

-- `ENNReal.toReal_le_add'` idx 4: necessary (a = 1, b = ⊤, c = 0)
theorem c1_17 : ¬ drop0% ENNReal.toReal_le_add' 4 :=
  fun h => by have := @h 1 ⊤ 0 (by simp) (by simp); norm_num at this

-- `ENNReal.toReal_le_add'` idx 5: necessary (a = 1, b = 0, c = ⊤)
theorem c1_18 : ¬ drop0% ENNReal.toReal_le_add' 5 :=
  fun h => by have := @h 1 0 ⊤ (by simp) (by simp); norm_num at this

-- `ENNReal.toReal_le_add` idx 4: necessary (a = 1, b = ⊤, c = 0)
theorem c1_19 : ¬ drop0% ENNReal.toReal_le_add 4 :=
  fun h => by have := @h 1 ⊤ 0 (by simp) (by simp); norm_num at this

-- `ENNReal.toReal_le_add` idx 5: necessary (a = 1, b = 0, c = ⊤)
theorem c1_20 : ¬ drop0% ENNReal.toReal_le_add 5 :=
  fun h => by have := @h 1 0 ⊤ (by simp) (by simp); norm_num at this

-- `ENNReal.add_lt_add` idx 4: necessary (a = 2, b = 0, c = 0, d = 1)
theorem c1_21 : ¬ drop0% ENNReal.add_lt_add 4 :=
  fun h => by have := @h 2 0 0 1 (by simp); norm_num at this

-- `ENNReal.add_right_inj` idx 3: necessary (a = ⊤, b = 0, c = 1)
theorem c1_22 : ¬ drop0% ENNReal.add_right_inj 3 :=
  fun h => by have := @h ⊤ 0 1; norm_num at this

-- `ENNReal.sub_add_eq_add_sub` idx 4: necessary (a = b = ⊤, c = 1)
theorem c1_23 : ¬ drop0% ENNReal.sub_add_eq_add_sub 4 :=
  fun h => by have := @h ⊤ ⊤ 1 le_rfl; norm_num at this

-- `ENNReal.add_sub_add_eq_sub_right` idx 3: necessary (a = 1, b = 0, c = ⊤)
theorem c1_24 : ¬ drop0% ENNReal.add_sub_add_eq_sub_right 3 :=
  fun h => by have := @h 1 0 ⊤; norm_num at this

-- `ENNReal.add_sub_add_eq_sub_left` idx 3: necessary (a = 1, b = 0, c = ⊤)
theorem c1_25 : ¬ drop0% ENNReal.add_sub_add_eq_sub_left 3 :=
  fun h => by have := @h 1 0 ⊤; norm_num at this

-- `ENNReal.lt_add_of_sub_lt_left` idx 3: necessary (a = b = ⊤, c = 1)
theorem c1_26 : ¬ drop0% ENNReal.lt_add_of_sub_lt_left 3 :=
  fun h => by have := @h ⊤ ⊤ 1 (by simp); norm_num at this

-- `ENNReal.lt_add_of_sub_lt_right` idx 3: necessary (a = c = ⊤, b = 1)
theorem c1_27 : ¬ drop0% ENNReal.lt_add_of_sub_lt_right 3 :=
  fun h => by have := @h ⊤ 1 ⊤ (by simp); norm_num at this

-- `ENNReal.le_sub_of_add_le_left` idx 3: necessary (a = c = ⊤, b = 1)
theorem c1_28 : ¬ drop0% ENNReal.le_sub_of_add_le_left 3 :=
  fun h => by have := @h ⊤ 1 ⊤ (by simp); norm_num at this

-- `ENNReal.le_sub_of_add_le_right` idx 3: necessary (b = c = ⊤, a = 1)
theorem c1_29 : ¬ drop0% ENNReal.le_sub_of_add_le_right 3 :=
  fun h => by have := @h 1 ⊤ ⊤ (by simp); norm_num at this

-- `ENNReal.sub_lt_iff_lt_right` idx 3: necessary (a = b = ⊤, c = 1)
theorem c1_30 : ¬ drop0% ENNReal.sub_lt_iff_lt_right 3 :=
  fun h => by have := @h ⊤ ⊤ 1 le_rfl; norm_num at this

-- `ENNReal.sub_lt_iff_lt_left` idx 3: necessary (a = b = ⊤, c = 1)
theorem c1_31 : ¬ drop0% ENNReal.sub_lt_iff_lt_left 3 :=
  fun h => by have := @h ⊤ ⊤ 1 le_rfl; norm_num at this

-- `ENNReal.le_sub_iff_add_le_left` idx 3: necessary (b = c = ⊤, a = 1)
theorem c1_32 : ¬ drop0% ENNReal.le_sub_iff_add_le_left 3 :=
  fun h => by have := @h 1 ⊤ ⊤ le_rfl; norm_num at this

-- `ENNReal.le_sub_iff_add_le_right` idx 3: necessary (b = c = ⊤, a = 1)
theorem c1_33 : ¬ drop0% ENNReal.le_sub_iff_add_le_right 3 :=
  fun h => by have := @h 1 ⊤ ⊤ le_rfl; norm_num at this

-- `ENNReal.sub_lt_of_sub_lt` idx 4: necessary (a = b = ⊤, c = 1)
theorem c1_34 : ¬ drop0% ENNReal.sub_lt_of_sub_lt 4 :=
  fun h => by have := @h ⊤ ⊤ 1 le_top (by simp); norm_num at this

-- `ENNReal.sub_sub_cancel` idx 2: necessary (a = ⊤, b = 1)
theorem c1_35 : ¬ drop0% ENNReal.sub_sub_cancel 2 :=
  fun h => by have := @h ⊤ 1 le_top; norm_num at this

-- `ENNReal.sub_right_inj` idx 3: necessary (a = ⊤, b = 0, c = 1)
theorem c1_36 : ¬ drop0% ENNReal.sub_right_inj 3 :=
  fun h => by have := @h ⊤ 0 1 le_top le_top; norm_num at this

-- `ENNReal.sub_mul` idx 3: necessary (a = ⊤, b = 1, c = ⊤)
theorem c1_37 : ¬ drop0% ENNReal.sub_mul 3 :=
  fun h => by have := @h ⊤ 1 ⊤; norm_num at this

-- `ENNReal.mul_sub` idx 3: necessary (a = ⊤, b = ⊤, c = 1)
theorem c1_38 : ¬ drop0% ENNReal.mul_sub 3 :=
  fun h => by have := @h ⊤ ⊤ 1; norm_num at this

-- `ENNReal.sub_le_sub_iff_left` idx 4: necessary (a = ⊤, b = 0, c = 1)
theorem c1_39 : ¬ drop0% ENNReal.sub_le_sub_iff_left 4 :=
  fun h => by have := @h ⊤ 0 1 le_top; norm_num at this

-- `ENNReal.toReal_sub_of_le` idx 3: necessary (a = ⊤, b = 1)
theorem c1_40 : ¬ drop0% ENNReal.toReal_sub_of_le 3 :=
  fun h => by have := @h ⊤ 1 le_top; norm_num at this

-- `ENNReal.sub_sub_sub_cancel_left` idx 3: necessary (a = ⊤, b = 1, c = 0)
theorem c1_41 : ¬ drop0% ENNReal.sub_sub_sub_cancel_left 3 :=
  fun h => by have := @h ⊤ 1 0 le_top; norm_num at this

-- `ENNReal.mem_Ioo_self_sub_add` idx 3: necessary (x = ⊤)
theorem c1_42 : ¬ drop0% ENNReal.mem_Ioo_self_sub_add 3 :=
  fun h => by have := @h ⊤ 1 1 (by simp) (by simp) (by simp); norm_num at this

-- `ENNReal.toNNReal_iInf` idx 2: necessary (ι = Bool, f = (1, ⊤))
theorem c1_43 : ¬ drop1% ENNReal.toNNReal_iInf 2 :=
  fun h => by have := @h Bool (fun b => if b then ⊤ else 1); have h2 := ciInf_le (Set.finite_range fun i : Bool => ((if i then ⊤ else 1 : ENNReal)).toNNReal).bddBelow true; simp only [iInf_bool_eq] at this; simp at this h2; rw [← this] at h2; norm_num at h2

-- `ENNReal.toNNReal_sInf` idx 1: necessary (s = {1, ⊤})
theorem c1_44 : ¬ drop0% ENNReal.toNNReal_sInf 1 :=
  fun h => by have := h {1, ⊤}; simp [csInf_pair] at this

-- `ENNReal.toReal_iInf` idx 2: necessary (ι = Bool, f = (1, ⊤))
theorem c1_45 : ¬ drop1% ENNReal.toReal_iInf 2 :=
  fun h => by have := @h Bool (fun b => if b then ⊤ else 1); have h2 := ciInf_le (Set.finite_range fun i : Bool => ((if i then ⊤ else 1 : ENNReal)).toReal).bddBelow true; simp only [iInf_bool_eq] at this; simp at this h2; rw [← this] at h2; norm_num at h2

-- `ENNReal.toReal_sInf` idx 1: necessary (s = {1, ⊤})
theorem c1_46 : ¬ drop0% ENNReal.toReal_sInf 1 :=
  fun h => by have := h {1, ⊤}; simp [csInf_pair] at this

-- `ENNReal.ofReal_iInf` idx 1: necessary (ι empty)
theorem c1_47 : ¬ drop0% ENNReal.ofReal_iInf 1 :=
  fun h => by have := @h False (fun _ => 1); simp at this

-- `ENNReal.iInf_add_iInf` idx 3: necessary (ι = Bool, f = (1, 0), g = (0, 1))
theorem c1_48 : ¬ drop1% ENNReal.iInf_add_iInf 3 :=
  fun h => by have := @h Bool (fun b => if b then 0 else 1) (fun b => if b then 1 else 0); simp only [iInf_bool_eq] at this; simp at this

-- `ENNReal.iInf_add_iInf_of_monotone` idx 2: necessary (ι = Unit ⊕ Unit (not codirected), f = (0, 1), g = (1, 0))
theorem c1_49 : ¬ drop0% ENNReal.iInf_add_iInf_of_monotone 2 :=
  fun h => by have := @h U2 _ (Sum.elim (fun _ => 0) (fun _ => 1)) (Sum.elim (fun _ => 1) (fun _ => 0)) (u2_mono _) (u2_mono _); simp [iInf_sum] at this

-- `ENNReal.iInf_add_iInf_of_monotone` idx 5: necessary (ι = Bool, f antitone (1, 0), g = (0, 1))
theorem c1_50 : ¬ drop0% ENNReal.iInf_add_iInf_of_monotone 5 :=
  fun h => by have := @h Bool _ _ (fun b => if b then 0 else 1) (fun b => if b then 1 else 0) (by intro a b hab; cases a <;> cases b <;> first | exact absurd hab (by decide) | simp); simp only [iInf_bool_eq] at this; simp at this

-- `ENNReal.iInf_add_iInf_of_monotone` idx 6: necessary (ι = Bool, g antitone)
theorem c1_51 : ¬ drop0% ENNReal.iInf_add_iInf_of_monotone 6 :=
  fun h => by have := @h Bool _ _ (fun b => if b then 1 else 0) (fun b => if b then 0 else 1) (by intro a b hab; cases a <;> cases b <;> first | exact absurd hab (by decide) | simp); simp only [iInf_bool_eq] at this; simp at this

-- `ENNReal.le_iInf₂_add_iInf₂` idx 7: necessary (a = 1, f = g = 0)
theorem c1_52 : ¬ drop0% ENNReal.le_iInf₂_add_iInf₂ 7 :=
  fun h => by have := @h True 1 True (fun _ => True) (fun _ => True) (fun _ _ => 0) (fun _ _ => 0); simp at this

-- `ENNReal.toNNReal_iSup` idx 2: necessary (ι = Bool, f = (1, ⊤))
theorem c1_53 : ¬ drop1% ENNReal.toNNReal_iSup 2 :=
  fun h => by have := @h Bool (fun b => if b then ⊤ else 1); have h2 := le_ciSup (Set.finite_range fun i : Bool => ((if i then ⊤ else 1 : ENNReal)).toNNReal).bddAbove false; simp only [iSup_bool_eq] at this; simp at this h2; rw [← this] at h2; norm_num at h2

-- `ENNReal.toNNReal_sSup` idx 1: necessary (s = {1, ⊤})
theorem c1_54 : ¬ drop0% ENNReal.toNNReal_sSup 1 :=
  fun h => by have := h {1, ⊤}; simp [csSup_pair] at this

-- `ENNReal.toReal_iSup` idx 2: necessary (ι = Bool, f = (1, ⊤))
theorem c1_55 : ¬ drop1% ENNReal.toReal_iSup 2 :=
  fun h => by have := @h Bool (fun b => if b then ⊤ else 1); have h2 := le_ciSup (Set.finite_range fun i : Bool => ((if i then ⊤ else 1 : ENNReal)).toReal).bddAbove false; simp only [iSup_bool_eq] at this; simp at this h2; rw [← this] at h2; norm_num at h2

-- `ENNReal.toReal_sSup` idx 1: necessary (s = {1, ⊤})
theorem c1_56 : ¬ drop0% ENNReal.toReal_sSup 1 :=
  fun h => by have := h {1, ⊤}; simp [csSup_pair] at this

-- `ENNReal.add_iSup` idx 2: necessary (ι empty, a = 1)
theorem c1_57 : ¬ drop0% ENNReal.add_iSup 2 :=
  fun h => by have := @h False 1 (fun _ => 0); simp at this

-- `ENNReal.iSup_add` idx 2: necessary (ι empty, a = 1)
theorem c1_58 : ¬ drop0% ENNReal.iSup_add 2 :=
  fun h => by have := @h False 1 (fun _ => 0); simp at this

-- `ENNReal.iSup_add_iSup_le` idx 4: necessary (ι empty, g = 1, a = 0)
theorem c1_59 : ¬ drop0% ENNReal.iSup_add_iSup_le 4 :=
  fun h => by have := @h False True (fun _ => 0) 0 ⟨trivial⟩ (fun _ => 1) (fun i => i.elim); simp at this

-- `ENNReal.iSup_add_iSup_le` idx 5: necessary (κ empty, f = 1, a = 0)
theorem c1_60 : ¬ drop0% ENNReal.iSup_add_iSup_le 5 :=
  fun h => by have := @h True False (fun _ => 1) 0 ⟨trivial⟩ (fun _ => 0) (fun _ j => j.elim); simp at this

-- `ENNReal.biSup_add_biSup_le'` idx 6: necessary (p never true, g = 1, a = 0)
theorem c1_61 : ¬ drop0% ENNReal.biSup_add_biSup_le' 6 :=
  fun h => by have := @h True True (fun _ => 0) 0 (fun _ => False) (fun _ => True) ⟨trivial, trivial⟩ (fun _ => 1) (fun _ hp => hp.elim); simp at this

-- `ENNReal.biSup_add_biSup_le'` idx 7: necessary (q never true, f = 1, a = 0)
theorem c1_62 : ¬ drop0% ENNReal.biSup_add_biSup_le' 7 :=
  fun h => by have := @h True True (fun _ => 1) 0 (fun _ => True) (fun _ => False) ⟨trivial, trivial⟩ (fun _ => 0) (fun _ _ _ hq => hq.elim); simp at this

-- `ENNReal.biSup_add_biSup_le` idx 4: necessary (s = ∅, g = 1, a = 0)
theorem c1_63 : ¬ drop0% ENNReal.biSup_add_biSup_le 4 :=
  fun h => by have := @h Unit Unit ∅ Set.univ Set.univ_nonempty (fun _ => 0) (fun _ => 1) 0 (fun i hi => hi.elim); simp at this

-- `ENNReal.biSup_add_biSup_le` idx 5: necessary (t = ∅, f = 1, a = 0)
theorem c1_64 : ¬ drop0% ENNReal.biSup_add_biSup_le 5 :=
  fun h => by have := @h Unit Unit Set.univ ∅ Set.univ_nonempty (fun _ => 1) (fun _ => 0) 0 (fun _ _ j hj => hj.elim); simp at this

-- `ENNReal.iSup_add_iSup` idx 3: necessary (ι = Bool, f = (0, 1), g = (1, 0))
theorem c1_65 : ¬ drop1% ENNReal.iSup_add_iSup 3 :=
  fun h => by have := @h Bool (fun b => if b then 1 else 0) (fun b => if b then 0 else 1); simp only [iSup_bool_eq] at this; simp at this

-- `ENNReal.iSup_add_iSup_of_monotone` idx 2: necessary (ι = Unit ⊕ Unit (not directed))
theorem c1_66 : ¬ drop0% ENNReal.iSup_add_iSup_of_monotone 2 :=
  fun h => by have := @h U2 _ (Sum.elim (fun _ => 1) (fun _ => 0)) (Sum.elim (fun _ => 0) (fun _ => 1)) (u2_mono _) (u2_mono _); simp [iSup_sum] at this

-- `ENNReal.iSup_add_iSup_of_monotone` idx 5: necessary (ι = Bool, f antitone)
theorem c1_67 : ¬ drop0% ENNReal.iSup_add_iSup_of_monotone 5 :=
  fun h => by have := @h Bool _ _ (fun b => if b then 0 else 1) (fun b => if b then 1 else 0) (by intro a b hab; cases a <;> cases b <;> first | exact absurd hab (by decide) | simp); simp only [iSup_bool_eq] at this; simp at this

-- `ENNReal.iSup_add_iSup_of_monotone` idx 6: necessary (ι = Bool, g antitone)
theorem c1_68 : ¬ drop0% ENNReal.iSup_add_iSup_of_monotone 6 :=
  fun h => by have := @h Bool _ _ (fun b => if b then 1 else 0) (fun b => if b then 0 else 1) (by intro a b hab; cases a <;> cases b <;> first | exact absurd hab (by decide) | simp); simp only [iSup_bool_eq] at this; simp at this

-- `ENNReal.sub_iSup` idx 3: necessary (ι empty, a = 1)
theorem c1_69 : ¬ drop0% ENNReal.sub_iSup 3 :=
  fun h => by have := @h False (fun _ => 0) 1 (by simp); simp at this

-- `ENNReal.sub_iSup` idx 4: necessary (a = ⊤, ι = ℕ, f n = n)
theorem c1_70 : ¬ drop1% ENNReal.sub_iSup 4 :=
  fun h => by have := @h ℕ (fun n => (n : ENNReal)) ⊤ inferInstance; simp [ENNReal.iSup_natCast] at this

-- `ENNReal.exists_lt_add_of_lt_add` idx 3: necessary (x = ⊤, y = z = 1)
theorem c1_71 : ¬ drop0% ENNReal.exists_lt_add_of_lt_add 3 :=
  fun h => by obtain ⟨y', -, z', -, hlt⟩ := @h ⊤ 1 1 (by simp) (by simp); exact not_top_lt hlt

-- `ENNReal.ofReal_add` idx 2: necessary (p = -1, q = 1)
theorem c1_72 : ¬ drop0% ENNReal.ofReal_add 2 :=
  fun h => by have := @h (-1) 1 (by norm_num); norm_num [ENNReal.ofReal_of_nonpos] at this

-- `ENNReal.toReal_mono_of_top_imp_top` idx 3: necessary (a = 1, b = ⊤)
theorem c1_73 : ¬ drop0% ENNReal.toReal_mono_of_top_imp_top 3 :=
  fun h => by have := @h 1 ⊤ le_top; norm_num at this

-- `ENNReal.toReal_mono'` idx 3: necessary (a = 1, b = ⊤)
theorem c1_74 : ¬ drop0% ENNReal.toReal_mono' 3 :=
  fun h => by have := @h 1 ⊤ le_top; norm_num at this

-- `ENNReal.toReal_strict_mono` idx 2: necessary (a = 1, b = ⊤)
theorem c1_75 : ¬ drop0% ENNReal.toReal_strict_mono 2 :=
  fun h => by have := @h 1 ⊤ (by simp); norm_num at this

-- `ENNReal.le_toNNReal_of_coe_le` idx 3: necessary (a = ⊤, p = 1)
theorem c1_76 : ¬ drop0% ENNReal.le_toNNReal_of_coe_le 3 :=
  fun h => by have := @h ⊤ 1 le_top; norm_num at this

-- `ENNReal.toNNReal_strict_mono` idx 2: necessary (a = 1, b = ⊤)
theorem c1_77 : ¬ drop0% ENNReal.toNNReal_strict_mono 2 :=
  fun h => by have := @h 1 ⊤ (by simp); norm_num at this

-- `ENNReal.ofReal_eq_ofReal_iff` idx 2: necessary (p = -1, q = 0)
theorem c1_78 : ¬ drop0% ENNReal.ofReal_eq_ofReal_iff 2 :=
  fun h => by have := @h (-1) 0 le_rfl; norm_num at this

-- `ENNReal.ofReal_eq_ofReal_iff` idx 3: necessary (p = 0, q = -1)
theorem c1_79 : ¬ drop0% ENNReal.ofReal_eq_ofReal_iff 3 :=
  fun h => by have := @h 0 (-1) le_rfl; norm_num at this

-- `ENNReal.ofReal_lt_ofReal_iff` idx 2: necessary (p = -2, q = -1)
theorem c1_80 : ¬ drop0% ENNReal.ofReal_lt_ofReal_iff 2 :=
  fun h => by have := @h (-2) (-1); norm_num [ENNReal.ofReal_of_nonpos] at this

-- `ENNReal.ofReal_lt_ofReal_iff_of_nonneg` idx 2: necessary (p = -2, q = -1)
theorem c1_81 : ¬ drop0% ENNReal.ofReal_lt_ofReal_iff_of_nonneg 2 :=
  fun h => by have := @h (-2) (-1); norm_num [ENNReal.ofReal_of_nonpos] at this

-- `_private.Mathlib.Basic.ENNReal.Real.0.ENNReal.Bound.ofReal_pos_of_pos` idx 1: necessary (p = 0)
theorem c1_82 : ¬ drop0% _private.Mathlib.Basic.ENNReal.Real.«0».ENNReal.Bound.ofReal_pos_of_pos 1 :=
  fun h => by have := @h 0; norm_num at this

-- `ENNReal.ofReal_le_iff_le_toReal` idx 2: necessary (a = 1, b = ⊤)
theorem c1_83 : ¬ drop0% ENNReal.ofReal_le_iff_le_toReal 2 :=
  fun h => by have := @h 1 ⊤; norm_num at this

-- `ENNReal.le_ofReal_iff_toReal_le` idx 2: necessary (a = ⊤, b = 0)
theorem c1_84 : ¬ drop0% ENNReal.le_ofReal_iff_toReal_le 2 :=
  fun h => by have := @h ⊤ 0 le_rfl; norm_num at this

-- `ENNReal.ofReal_mul` idx 2: necessary (p = q = -1)
theorem c1_85 : ¬ drop0% ENNReal.ofReal_mul 2 :=
  fun h => by have := @h (-1) (-1); norm_num [ENNReal.ofReal_of_nonpos] at this

-- `ENNReal.ofReal_mul'` idx 2: necessary (p = q = -1)
theorem c1_86 : ¬ drop0% ENNReal.ofReal_mul' 2 :=
  fun h => by have := @h (-1) (-1); norm_num [ENNReal.ofReal_of_nonpos] at this

-- `ENNReal.ofReal_pow` idx 1: necessary (p = -1, n = 2)
theorem c1_87 : ¬ drop0% ENNReal.ofReal_pow 1 :=
  fun h => by have := @h (-1) 2; norm_num [ENNReal.ofReal_of_nonpos] at this

-- `existsUnique_iff_exists` idx 1: necessary (α = Bool, p = True)
theorem c1_88 : ¬ drop1% existsUnique_iff_exists 1 :=
  fun h => by obtain ⟨x, -, hu⟩ := (@h Bool (fun _ => True)).mpr ⟨true, trivial⟩; exact absurd ((hu true trivial).trans (hu false trivial).symm) (by decide)

-- `existsUnique_const` idx 2: necessary (α empty, b = True)
theorem c1_89 : ¬ drop0% existsUnique_const 2 :=
  fun h => by obtain ⟨x, -⟩ := (@h True False inferInstance).mpr trivial; exact x

-- `existsUnique_const` idx 3: necessary (α = Bool, b = True)
theorem c1_90 : ¬ drop1% existsUnique_const 3 :=
  fun h => by obtain ⟨x, -, hu⟩ := (@h True Bool ⟨true⟩).mpr trivial; exact absurd ((hu true trivial).trans (hu false trivial).symm) (by decide)

-- `existsUnique_prop_of_true` idx 2: necessary (p = False)
theorem c1_91 : ¬ indep0% existsUnique_prop_of_true 2 :=
  fun h => @h False (fun _ => True)

-- `ExistsUnique.elim₂` idx 2: necessary (α = Bool, p x = Bool, q x h = (x || h): q true has two proofs, b = False)
theorem c1_92 : ¬ drop1% ExistsUnique.elim₂ 2 :=
  fun h => @h Bool (fun _ => Bool) (fun x hx => (x || hx) = true) False eu_q (fun x _ _ H => by cases x; exacts [absurd (H true true rfl) (by decide), absurd (H false true rfl) (by decide)])

-- `ExistsUnique.elim₂` idx 5: necessary (q = False, b = False)
theorem c1_93 : ¬ drop0% ExistsUnique.elim₂ 5 :=
  fun h => @h True (fun _ => True) inferInstance (fun _ _ => False) False (fun _ _ hq _ => hq)

-- `ExistsUnique.elim₂` idx 6: necessary (q = True, b = False)
theorem c1_94 : ¬ drop0% ExistsUnique.elim₂ 6 :=
  fun h => @h True (fun _ => True) inferInstance (fun _ _ => True) False ⟨trivial, ⟨trivial, trivial, fun _ _ => rfl⟩, fun _ _ => rfl⟩

-- `ExistsUnique.intro₂` idx 2: necessary (α = Unit, p = Bool, q = True)
theorem c1_95 : ¬ drop1% ExistsUnique.intro₂ 2 :=
  fun h => by obtain ⟨x, ⟨hx, -, hu⟩, -⟩ := @h Unit (fun _ => Bool) (fun _ _ => True) () true trivial (fun _ _ _ => rfl); exact absurd ((hu true trivial).trans (hu false trivial).symm) (by decide)

-- `ExistsUnique.intro₂` idx 6: necessary (q = False)
theorem c1_96 : ¬ drop0% ExistsUnique.intro₂ 6 :=
  fun h => by obtain ⟨x, ⟨hx, hq, -⟩, -⟩ := @h True (fun _ => True) inferInstance (fun _ _ => False) trivial trivial (fun _ _ hq => hq.elim); exact hq

-- `ExistsUnique.intro₂` idx 7: necessary (α = Bool, q = True)
theorem c1_97 : ¬ drop1% ExistsUnique.intro₂ 7 :=
  fun h => by obtain ⟨x, -, hu⟩ := @h Bool (fun _ => Unit) inferInstance (fun _ _ => True) true () trivial; exact absurd ((hu true ⟨(), trivial, fun _ _ => rfl⟩).trans (hu false ⟨(), trivial, fun _ _ => rfl⟩).symm) (by decide)

-- `ExistsUnique.exists₂` idx 3: necessary (q = False)
theorem c1_98 : ¬ drop0% ExistsUnique.exists₂ 3 :=
  fun h => by obtain ⟨_, _, hq⟩ := @h True (fun _ => True) (fun _ _ => False); exact hq

-- `ExistsUnique.unique₂` idx 2: necessary (α = Bool, p x = Bool, q x h = (x || h), y₁ = true, y₂ = false)
theorem c1_99 : ¬ drop1% ExistsUnique.unique₂ 2 :=
  fun h => absurd (@h Bool (fun _ => Bool) (fun x hx => (x || hx) = true) eu_q true false true rfl true rfl) (by decide)

-- `ExistsUnique.unique₂` idx 4: necessary (α = Bool, q = True)
theorem c1_100 : ¬ drop1% ExistsUnique.unique₂ 4 :=
  fun h => absurd (@h Bool (fun _ => Unit) inferInstance (fun _ _ => True) true false () trivial () trivial) (by decide)

-- `ExistsUnique.unique₂` idx 8: necessary (α = Bool, q x = (x = true), y₁ = false)
theorem c1_101 : ¬ drop1% ExistsUnique.unique₂ 8 :=
  fun h => absurd (@h Bool (fun _ => Unit) inferInstance (fun x _ => x = true) ⟨true, ⟨(), rfl, fun _ _ => rfl⟩, fun y ⟨_, hy, _⟩ => hy⟩ false true () () rfl) (by decide)

-- `ExistsUnique.unique₂` idx 10: necessary (α = Bool, q x = (x = true), y₂ = false)
theorem c1_102 : ¬ drop1% ExistsUnique.unique₂ 10 :=
  fun h => absurd (@h Bool (fun _ => Unit) inferInstance (fun x _ => x = true) ⟨true, ⟨(), rfl, fun _ _ => rfl⟩, fun y ⟨_, hy, _⟩ => hy⟩ true false () rfl ()) (by decide)

-- `Finite.exists_equiv_fin` idx 1: necessary (α = ℕ)
theorem c1_103 : ¬ drop1% Finite.exists_equiv_fin 1 :=
  fun h => by obtain ⟨n, ⟨e⟩⟩ := h ℕ; exact nf e e.injective inferInstance

-- `Finite.of_equiv` idx 2: necessary (α = β = ℕ)
theorem c1_104 : ¬ drop1% Finite.of_equiv 2 :=
  fun h => nf id Function.injective_id (@h ℕ ℕ (Equiv.refl ℕ))

-- `Function.Bijective.finite_iff` idx 3: necessary (α = Unit, β = ℕ)
theorem c1_105 : ¬ drop1% Function.Bijective.finite_iff 3 :=
  fun h => nf id Function.injective_id ((@h Unit ℕ (fun _ => 0)).mp inferInstance)

-- `Finite.ofBijective` idx 2: necessary (α = β = ℕ, f = id)
theorem c1_106 : ¬ drop1% Finite.ofBijective 2 :=
  fun h => nf id Function.injective_id (@h ℕ ℕ id Function.bijective_id)

-- `Finite.ofBijective` idx 4: necessary (α = Unit, β = ℕ)
theorem c1_107 : ¬ drop1% Finite.ofBijective 4 :=
  fun h => nf id Function.injective_id (@h Unit ℕ finU (fun _ => 0))

-- `instFinitePLift` idx 1: necessary (α = ℕ)
theorem c1_108 : ¬ drop1% instFinitePLift 1 :=
  fun h => nf PLift.up (fun _ _ e => congrArg PLift.down e) (@h ℕ)

-- `instFiniteULift` idx 1: necessary (α = ℕ)
theorem c1_109 : ¬ drop0% instFiniteULift 1 :=
  fun h => nf ULift.up (fun _ _ e => congrArg ULift.down e) (@h ℕ)

-- `instInfinitePLift` idx 1: necessary (α = True)
theorem c1_110 : ¬ drop0% instInfinitePLift 1 :=
  fun h => @Infinite.not_finite (PLift True) (@h True) inferInstance

-- `instInfiniteULift` idx 1: necessary (α = Unit)
theorem c1_111 : ¬ drop0% instInfiniteULift 1 :=
  fun h => @Infinite.not_finite (ULift.{0} Unit) (@h Unit) inferInstance

-- `Infinite.false` idx 1: necessary (α = ℕ)
theorem c1_112 : ¬ drop1% Infinite.false 1 :=
  fun h => @h ℕ inferInstance

-- `Finite.of_not_infinite` idx 1: necessary (α = ℕ)
theorem c1_113 : ¬ drop1% Finite.of_not_infinite 1 :=
  fun h => nf id Function.injective_id (@h ℕ)

-- `Finite.not_infinite` idx 1: necessary (α = ℕ)
theorem c1_114 : ¬ drop1% Finite.not_infinite 1 :=
  fun h => @h ℕ inferInstance

-- `Set.toFinite` idx 2: necessary (s = univ ℕ)
theorem c1_115 : ¬ drop0% Set.toFinite 2 :=
  fun h => Set.infinite_univ (h (Set.univ : Set ℕ))

-- `Set.Finite.to_subtype` idx 2: necessary (s = univ ℕ)
theorem c1_116 : ¬ drop0% Set.Finite.to_subtype 2 :=
  fun h => Set.infinite_univ (Set.finite_coe_iff.mp (@h ℕ Set.univ))

-- `Set.Finite.not_infinite` idx 2: necessary (s = univ ℕ)
theorem c1_117 : ¬ drop0% Set.Finite.not_infinite 2 :=
  fun h => @h ℕ Set.univ Set.infinite_univ

-- `Set.Infinite.to_subtype` idx 2: necessary (s = ∅)
theorem c1_118 : ¬ drop0% Set.Infinite.to_subtype 2 :=
  fun h => Set.infinite_coe_iff.mp (@h ℕ ∅) Set.finite_empty

-- `Finite.instProd` idx 2: necessary (α = ℕ, β = Unit)
theorem c1_119 : ¬ drop0% Finite.instProd 2 :=
  fun h => nf (fun n : ℕ => (n, ())) (fun _ _ e => congrArg Prod.fst e) (@h ℕ Unit inferInstance)

-- `Finite.instProd` idx 3: necessary (α = Unit, β = ℕ)
theorem c1_120 : ¬ drop0% Finite.instProd 3 :=
  fun h => nf (fun n : ℕ => ((), n)) (fun _ _ e => congrArg Prod.snd e) (@h Unit ℕ inferInstance)

-- `Finite.instPProd` idx 2: necessary (α = ℕ, β = Unit)
theorem c1_121 : ¬ drop1% Finite.instPProd 2 :=
  fun h => nf (fun n : ℕ => (⟨n, ()⟩ : ℕ ×' Unit)) (fun _ _ e => congrArg PProd.fst e) (@h ℕ Unit inferInstance)

-- `Finite.instPProd` idx 3: necessary (α = Unit, β = ℕ)
theorem c1_122 : ¬ drop1% Finite.instPProd 3 :=
  fun h => nf (fun n : ℕ => (⟨(), n⟩ : Unit ×' ℕ)) (fun _ _ e => congrArg PProd.snd e) (@h Unit ℕ inferInstance)

-- `Finite.prod_left` idx 2: necessary (α = ℕ, β = Unit)
theorem c1_123 : ¬ drop0% Finite.prod_left 2 :=
  fun h => nf id Function.injective_id (@h ℕ Unit inferInstance)

-- `Finite.prod_left` idx 3: necessary (α = ℕ, β = Empty)
theorem c1_124 : ¬ drop0% Finite.prod_left 3 :=
  fun h => nf id Function.injective_id (@h ℕ Empty finNE)

-- `Finite.prod_right` idx 2: necessary (β = ℕ, α = Unit)
theorem c1_125 : ¬ drop0% Finite.prod_right 2 :=
  fun h => nf id Function.injective_id (@h ℕ Unit inferInstance)

-- `Finite.prod_right` idx 3: necessary (β = ℕ, α = Empty)
theorem c1_126 : ¬ drop0% Finite.prod_right 3 :=
  fun h => nf id Function.injective_id (@h ℕ Empty finEN)

-- `Prod.finite_iff` idx 2: necessary (α = Empty, β = ℕ)
theorem c1_127 : ¬ drop0% Prod.finite_iff 2 :=
  fun h => nf id Function.injective_id ((@h Empty ℕ inferInstance).mp finEN).2

-- `Prod.finite_iff` idx 3: necessary (α = ℕ, β = Empty)
theorem c1_128 : ¬ drop0% Prod.finite_iff 3 :=
  fun h => nf id Function.injective_id ((@h ℕ Empty inferInstance).mp finNE).1

-- `Pi.finite` idx 2: necessary (α = ℕ, β = Bool)
theorem c1_129 : ¬ drop1% Pi.finite 2 :=
  fun h => nf (fun n : ℕ => fun m : ℕ => decide (m = n)) (fun a b e => by simpa using congrFun e a) (@h ℕ (fun _ => Bool) inferInstance)

-- `Pi.finite` idx 3: necessary (α = Unit, β = ℕ)
theorem c1_130 : ¬ drop1% Pi.finite 3 :=
  fun h => nf (fun n : ℕ => fun _ : Unit => n) (fun _ _ e => congrFun e ()) (@h Unit (fun _ => ℕ) inferInstance)

-- `Function.Embedding.finite` idx 2: necessary (α = Unit, β = ℕ)
theorem c1_131 : ¬ drop1% Function.Embedding.finite 2 :=
  fun h => nf (fun n : ℕ => (⟨fun _ => n, fun _ _ _ => rfl⟩ : Unit ↪ ℕ)) (fun _ _ e => DFunLike.congr_fun e ()) (@h Unit ℕ)

-- `Equiv.finite_right` idx 2: necessary (α = β = ℕ (swaps))
theorem c1_132 : ¬ drop1% Equiv.finite_right 2 :=
  fun h => nf sw sw_inj (@h ℕ ℕ)

-- `Equiv.finite_left` idx 2: necessary (α = β = ℕ (swaps))
theorem c1_133 : ¬ drop1% Equiv.finite_left 2 :=
  fun h => nf sw sw_inj (@h ℕ ℕ)

-- `AddEquiv.finite_left` idx 4: necessary (ℕ with left-projection addition: every permutation is additive)
theorem c1_134 : ¬ drop0% AddEquiv.finite_left 4 :=
  fun h => nf lpA lpA_inj (@h LP LP _ _)

-- `MulEquiv.finite_left` idx 4: necessary (ℕ with left-projection multiplication)
theorem c1_135 : ¬ drop0% MulEquiv.finite_left 4 :=
  fun h => nf lpM lpM_inj (@h LP LP _ _)

-- `AddEquiv.finite_right` idx 4: necessary (ℕ with left-projection addition)
theorem c1_136 : ¬ drop0% AddEquiv.finite_right 4 :=
  fun h => nf lpA lpA_inj (@h LP LP _ _)

-- `MulEquiv.finite_right` idx 4: necessary (ℕ with left-projection multiplication)
theorem c1_137 : ¬ drop0% MulEquiv.finite_right 4 :=
  fun h => nf lpM lpM_inj (@h LP LP _ _)

-- `Finite.Set.finite_prod` idx 4: necessary (s = univ ℕ, t = univ Unit)
theorem c1_138 : ¬ drop0% Finite.Set.finite_prod 4 :=
  fun h => nUP (Set.finite_coe_iff.mp (@h ℕ Unit Set.univ Set.univ inferInstance))

-- `Finite.Set.finite_prod` idx 5: necessary (s = univ Unit, t = univ ℕ)
theorem c1_139 : ¬ drop0% Finite.Set.finite_prod 5 :=
  fun h => nUP' (Set.finite_coe_iff.mp (@h Unit ℕ Set.univ Set.univ inferInstance))

-- `Finite.Set.finite_image2` idx 6: necessary (f = left projection, s = univ ℕ, t = univ Unit)
theorem c1_140 : ¬ drop0% Finite.Set.finite_image2 6 :=
  fun h => by have := Set.finite_coe_iff.mp (@h ℕ Unit ℕ (fun a _ => a) Set.univ Set.univ inferInstance); rw [Set.image2_left Set.univ_nonempty] at this; exact Set.infinite_univ this

-- `Finite.Set.finite_image2` idx 7: necessary (f = right projection, s = univ Unit, t = univ ℕ)
theorem c1_141 : ¬ drop0% Finite.Set.finite_image2 7 :=
  fun h => by have := Set.finite_coe_iff.mp (@h Unit ℕ ℕ (fun _ b => b) Set.univ Set.univ inferInstance); rw [Set.image2_right Set.univ_nonempty] at this; exact Set.infinite_univ this

-- `Set.Finite.prod` idx 4: necessary (s = univ ℕ, t = univ Unit)
theorem c1_142 : ¬ drop0% Set.Finite.prod 4 :=
  fun h => nUP (@h ℕ Unit Set.univ Set.univ (Set.toFinite _))

-- `Set.Finite.prod` idx 5: necessary (s = univ Unit, t = univ ℕ)
theorem c1_143 : ¬ drop0% Set.Finite.prod 5 :=
  fun h => nUP' (@h Unit ℕ Set.univ Set.univ (Set.toFinite _))

-- `Set.Finite.of_prod_left` idx 4: necessary (s = univ ℕ, t = univ Unit)
theorem c1_144 : ¬ drop0% Set.Finite.of_prod_left 4 :=
  fun h => Set.infinite_univ (@h ℕ Unit Set.univ Set.univ Set.univ_nonempty)

-- `Set.Finite.of_prod_left` idx 5: necessary (s = univ ℕ, t = ∅)
theorem c1_145 : ¬ drop0% Set.Finite.of_prod_left 5 :=
  fun h => Set.infinite_univ (@h ℕ Unit Set.univ ∅ (by simp))

-- `Set.Finite.of_prod_right` idx 4: necessary (s = univ Unit, t = univ ℕ)
theorem c1_146 : ¬ drop0% Set.Finite.of_prod_right 4 :=
  fun h => Set.infinite_univ (@h Unit ℕ Set.univ Set.univ Set.univ_nonempty)

-- `Set.Finite.of_prod_right` idx 5: necessary (s = ∅, t = univ ℕ)
theorem c1_147 : ¬ drop0% Set.Finite.of_prod_right 5 :=
  fun h => Set.infinite_univ (@h Unit ℕ ∅ Set.univ (by simp))

-- `Set.Infinite.prod_left` idx 5: necessary (s = univ ℕ, t = ∅)
theorem c1_148 : ¬ drop0% Set.Infinite.prod_left 5 :=
  fun h => @h ℕ Unit Set.univ ∅ Set.infinite_univ (by simp)

-- `Set.Infinite.prod_right` idx 5: necessary (s = ∅, t = univ ℕ)
theorem c1_149 : ¬ drop0% Set.Infinite.prod_right 5 :=
  fun h => @h Unit ℕ ∅ Set.univ Set.infinite_univ (by simp)

-- `Set.Finite.offDiag` idx 2: necessary (s = univ ℕ)
theorem c1_150 : ¬ drop0% Set.Finite.offDiag 2 :=
  fun h => (Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n, n + 1)) (fun _ _ e => congrArg Prod.fst e) (fun n => by simp [Set.mem_offDiag])) (@h ℕ Set.univ)

-- `Set.Finite.image2` idx 6: necessary (f = left projection, s = univ ℕ, t = univ Unit)
theorem c1_151 : ¬ drop0% Set.Finite.image2 6 :=
  fun h => by have := @h ℕ Unit ℕ Set.univ Set.univ (fun a _ => a) (Set.toFinite _); rw [Set.image2_left Set.univ_nonempty] at this; exact Set.infinite_univ this

-- `Set.Finite.image2` idx 7: necessary (f = right projection, s = univ Unit, t = univ ℕ)
theorem c1_152 : ¬ drop0% Set.Finite.image2 7 :=
  fun h => by have := @h Unit ℕ ℕ Set.univ Set.univ (fun _ b => b) (Set.toFinite _); rw [Set.image2_right Set.univ_nonempty] at this; exact Set.infinite_univ this

-- `Set.Finite.toFinset_prod` idx 4: necessary (s = univ ℕ, t = univ Unit)
theorem c1_153 : ¬ indep0% Set.Finite.toFinset_prod 4 :=
  fun h => Set.infinite_univ (@h ℕ Unit Set.univ Set.univ (Set.toFinite _))

-- `Set.Finite.toFinset_prod` idx 5: necessary (s = univ Unit, t = univ ℕ)
theorem c1_154 : ¬ indep0% Set.Finite.toFinset_prod 5 :=
  fun h => Set.infinite_univ (@h Unit ℕ Set.univ Set.univ (Set.toFinite _))

-- `Set.Finite.toFinset_offDiag` idx 2: necessary (s = univ ℕ)
theorem c1_155 : ¬ indep0% Set.Finite.toFinset_offDiag 2 :=
  fun h => Set.infinite_univ (@h ℕ Set.univ)

-- `Set.Infinite.image2_left` idx 8: necessary (t = ∅)
theorem c1_156 : ¬ drop0% Set.Infinite.image2_left 8 :=
  fun h => @h ℕ Unit ℕ (fun a _ => a) Set.univ ∅ () Set.infinite_univ (fun _ _ _ _ e => e) (by simp)

-- `Set.Infinite.image2_left` idx 9: necessary (f constant 0, s = univ ℕ)
theorem c1_157 : ¬ drop0% Set.Infinite.image2_left 9 :=
  fun h => @h ℕ Unit ℕ (fun _ _ => 0) Set.univ Set.univ () Set.infinite_univ trivial ((Set.finite_singleton 0).subset (by rintro _ ⟨a, -, b, -, rfl⟩; rfl))

-- `Set.Infinite.image2_right` idx 8: necessary (s = ∅)
theorem c1_158 : ¬ drop0% Set.Infinite.image2_right 8 :=
  fun h => @h Unit ℕ ℕ (fun _ b => b) ∅ Set.univ () Set.infinite_univ (fun _ _ _ _ e => e) (by simp)

-- `Set.Infinite.image2_right` idx 9: necessary (f constant 0, t = univ ℕ)
theorem c1_159 : ¬ drop0% Set.Infinite.image2_right 9 :=
  fun h => @h Unit ℕ ℕ (fun _ _ => 0) Set.univ Set.univ () Set.infinite_univ trivial ((Set.finite_singleton 0).subset (by rintro _ ⟨a, -, b, -, rfl⟩; rfl))

-- `Set.infinite_image2` idx 6: necessary (f a b = b : Unit, s = univ ℕ)
theorem c1_160 : ¬ drop0% Set.infinite_image2 6 :=
  fun h => ((@h ℕ Unit Unit (fun _ b => b) Set.univ Set.univ (fun _ _ _ _ _ _ _ => rfl)).mpr (Or.inl ⟨Set.infinite_univ, Set.univ_nonempty⟩)) (Set.toFinite _)

-- `Set.infinite_image2` idx 7: necessary (f a b = a : Unit, t = univ ℕ)
theorem c1_161 : ¬ drop0% Set.infinite_image2 7 :=
  fun h => ((@h Unit ℕ Unit (fun a _ => a) Set.univ Set.univ (fun _ _ _ _ _ _ _ => rfl)).mpr (Or.inr ⟨Set.infinite_univ, Set.univ_nonempty⟩)) (Set.toFinite _)

-- `Set.finite_image2` idx 6: necessary (f a b = b : Unit, s = univ ℕ)
theorem c1_162 : ¬ drop0% Set.finite_image2 6 :=
  fun h => by rcases (@h ℕ Unit Unit (fun _ b => b) Set.univ Set.univ (fun _ _ _ _ _ _ _ => rfl)).mp (Set.toFinite _) with ⟨hs, -⟩ | hs | ht; exacts [Set.infinite_univ hs, Set.univ_nonempty.ne_empty hs, Set.univ_nonempty.ne_empty ht]

-- `Set.finite_image2` idx 7: necessary (f a b = a : Unit, t = univ ℕ)
theorem c1_163 : ¬ drop0% Set.finite_image2 7 :=
  fun h => by rcases (@h Unit ℕ Unit (fun a _ => a) Set.univ Set.univ (fun _ _ _ _ _ _ _ => rfl)).mp (Set.toFinite _) with ⟨-, ht⟩ | hs | ht; exacts [Set.infinite_univ ht, Set.univ_nonempty.ne_empty hs, Set.univ_nonempty.ne_empty ht]

-- `Finite.Set.finite_of_finite_image` idx 4: necessary (f constant, s = univ ℕ)
theorem c1_164 : ¬ drop0% Finite.Set.finite_of_finite_image 4 :=
  fun h => Set.infinite_univ (Set.finite_coe_iff.mp (@h ℕ Unit Set.univ (fun _ => ()) finImU))

-- `Finite.Set.finite_of_finite_image` idx 5: necessary (f = id, s = univ ℕ)
theorem c1_165 : ¬ drop0% Finite.Set.finite_of_finite_image 5 :=
  fun h => Set.infinite_univ (Set.finite_coe_iff.mp (@h ℕ ℕ Set.univ id (Set.injOn_id _)))

-- `Finite.of_injective_finite_range` idx 3: necessary (ι = ℕ, f constant)
theorem c1_166 : ¬ drop1% Finite.of_injective_finite_range 3 :=
  fun h => nf id Function.injective_id (@h (ULift.{1} Unit) ℕ (fun _ => ⟨()⟩) finRU)

-- `Finite.of_injective_finite_range` idx 4: necessary (ι = ℕ, f = ULift.up)
theorem c1_167 : ¬ drop1% Finite.of_injective_finite_range 4 :=
  fun h => nf id Function.injective_id (@h (ULift.{1} ℕ) ℕ ULift.up ULift.up_injective)

-- `Finite.instSigma` idx 2: necessary (α = ℕ, β = Unit)
theorem c1_168 : ¬ drop0% Finite.instSigma 2 :=
  fun h => nf (fun n : ℕ => (⟨n, ()⟩ : Σ _ : ℕ, Unit)) (fun _ _ e => congrArg Sigma.fst e) (@h ℕ (fun _ => Unit) inferInstance)

-- `Finite.instSigma` idx 3: necessary (α = Unit, β = ℕ)
theorem c1_169 : ¬ drop0% Finite.instSigma 3 :=
  fun h => nf (fun n : ℕ => (⟨(), n⟩ : Σ _ : Unit, ℕ)) (fun _ _ e => by simpa using e) (@h Unit (fun _ => ℕ) inferInstance)

-- `Finite.instPSigma` idx 2: necessary (ι = ℕ, π = Unit)
theorem c1_170 : ¬ drop1% Finite.instPSigma 2 :=
  fun h => nf (fun n : ℕ => (⟨n, ()⟩ : Σ' _ : ℕ, Unit)) (fun _ _ e => congrArg PSigma.fst e) (@h ℕ (fun _ => Unit) inferInstance)

-- `Finite.instPSigma` idx 3: necessary (ι = Unit, π = ℕ)
theorem c1_171 : ¬ drop1% Finite.instPSigma 3 :=
  fun h => nf (fun n : ℕ => (⟨(), n⟩ : Σ' _ : Unit, ℕ)) (fun _ _ e => by simpa using e) (@h Unit (fun _ => ℕ) inferInstance)

-- `Finite.Set.finite_sigma` idx 4: necessary (s = univ ℕ, t = univ Unit)
theorem c1_172 : ¬ drop0% Finite.Set.finite_sigma 4 :=
  fun h => (Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (⟨n, ()⟩ : Σ _ : ℕ, Unit)) (fun _ _ e => congrArg Sigma.fst e) (fun n => by simp)) (Set.finite_coe_iff.mp (@h ℕ (fun _ => Unit) Set.univ (fun _ => Set.univ) inferInstance))

-- `Finite.Set.finite_sigma` idx 5: necessary (s = univ Unit, t = univ ℕ)
theorem c1_173 : ¬ drop0% Finite.Set.finite_sigma 5 :=
  fun h => (Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (⟨(), n⟩ : Σ _ : Unit, ℕ)) (fun _ _ e => by simpa using e) (fun n => by simp)) (Set.finite_coe_iff.mp (@h Unit (fun _ => ℕ) Set.univ (fun _ => Set.univ) inferInstance))

-- `Set.Finite.sigma` idx 4: necessary (s = univ ℕ, t = univ Unit)
theorem c1_174 : ¬ drop0% Set.Finite.sigma 4 :=
  fun h => (Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (⟨n, ()⟩ : Σ _ : ℕ, Unit)) (fun _ _ e => congrArg Sigma.fst e) (fun n => by simp)) (@h ℕ (fun _ => Unit) Set.univ (fun _ => Set.univ) (fun _ _ => Set.toFinite _))

-- `Set.Finite.sigma` idx 5: necessary (s = univ Unit, t = univ ℕ)
theorem c1_175 : ¬ drop0% Set.Finite.sigma 5 :=
  fun h => (Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (⟨(), n⟩ : Σ _ : Unit, ℕ)) (fun _ _ e => by simpa using e) (fun n => by simp)) (@h Unit (fun _ => ℕ) Set.univ (fun _ => Set.univ) (Set.toFinite _))

-- `Finite.instSum` idx 2: necessary (α = ℕ)
theorem c1_176 : ¬ drop0% Finite.instSum 2 :=
  fun h => nf (Sum.inl : ℕ → ℕ ⊕ Unit) Sum.inl_injective (@h ℕ Unit inferInstance)

-- `Finite.instSum` idx 3: necessary (β = ℕ)
theorem c1_177 : ¬ drop0% Finite.instSum 3 :=
  fun h => nf (Sum.inr : ℕ → Unit ⊕ ℕ) Sum.inr_injective (@h Unit ℕ inferInstance)

-- `Finite.sum_left` idx 2: necessary (α = ℕ)
theorem c1_178 : ¬ drop0% Finite.sum_left 2 :=
  fun h => nf id Function.injective_id (@h ℕ Unit)

-- `Finite.sum_right` idx 2: necessary (β = ℕ)
theorem c1_179 : ¬ drop0% Finite.sum_right 2 :=
  fun h => nf id Function.injective_id (@h ℕ Unit)

-- `Finite.instPSum` idx 2: necessary (α = ℕ)
theorem c1_180 : ¬ drop1% Finite.instPSum 2 :=
  fun h => nf (PSum.inl : ℕ → ℕ ⊕' Unit) (fun _ _ e => PSum.inl.inj e) (@h ℕ Unit inferInstance)

-- `Finite.instPSum` idx 3: necessary (β = ℕ)
theorem c1_181 : ¬ drop1% Finite.instPSum 3 :=
  fun h => nf (PSum.inr : ℕ → Unit ⊕' ℕ) (fun _ _ e => PSum.inr.inj e) (@h Unit ℕ inferInstance)

-- `Finite.psum_left` idx 2: necessary (α = ℕ)
theorem c1_182 : ¬ drop1% Finite.psum_left 2 :=
  fun h => nf id Function.injective_id (@h ℕ Unit)

-- `Finite.psum_right` idx 2: necessary (β = ℕ)
theorem c1_183 : ¬ drop1% Finite.psum_right 2 :=
  fun h => nf id Function.injective_id (@h Unit ℕ)
