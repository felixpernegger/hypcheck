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

elab "indep1% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.one
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := (xs.getD (i.getNat) default)
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType (xs.getD (j) default)
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push (xs.getD (j) default)
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

universe u_1 u_2 u_3 u_4

namespace W1c2
theorem acc_irr {α : Sort _} {r : α → α → Prop} {x : α} (h : Acc r x) : ¬ r x x := by
  induction h with
  | intro x _ ih => exact fun hx => ih x hx hx
theorem bool_ne_unit : (Bool : Type) ≠ Unit := fun e => by
  have h : ∀ x y : Bool, x = y := by rw [e]; intro x y; rfl
  exact absurd (h true false) (by decide)
theorem refl_ne_swap : Equiv.refl Bool ≠ Equiv.swap true false := fun e => by
  have := congrArg (fun f : Equiv.Perm Bool => f true) e
  simp at this
theorem tn_m1 : (-1 : ℝ).toNNReal = 0 := Real.toNNReal_of_nonpos (by norm_num)
theorem tn_m2 : (-2 : ℝ).toNNReal = 0 := Real.toNNReal_of_nonpos (by norm_num)
@[instance_reducible] def S1 : SMul ℝ ℝ := ⟨fun m n => m + n⟩
theorem S1_apply (m n : ℝ) : @HSMul.hSMul ℝ ℝ ℝ (@instHSMul ℝ ℝ S1) m n = m + n := rfl
end W1c2
open W1c2

-- `DFunLike.ext'` idx 6: necessary — F = Perm Bool, f = refl, g = swap (universe 1)
theorem c2_1 : ¬ drop1% DFunLike.ext' 6 := fun h =>
  refl_ne_swap (@h (Equiv.Perm Bool) Bool (fun _ => Bool) _ (Equiv.refl Bool) (Equiv.swap true false))
-- `DFunLike.exists_ne` idx 6: necessary — f = g = refl in Perm Bool
theorem c2_2 : ¬ drop1% DFunLike.exists_ne 6 := fun h => by
  obtain ⟨x, hx⟩ := @h (Equiv.Perm Bool) Bool (fun _ => Bool) _ (Equiv.refl Bool) (Equiv.refl Bool)
  exact hx rfl
-- `DFunLike.subsingleton_cod` idx 4: necessary — Perm Bool is not subsingleton
theorem c2_3 : ¬ drop1% DFunLike.subsingleton_cod 4 := fun h =>
  refl_ne_swap ((@h (Equiv.Perm Bool) Bool (fun _ => Bool) _).elim _ _)
-- `DFunLike.subsingleton_dom` idx 4: necessary — Perm Bool is not subsingleton
theorem c2_4 : ¬ drop1% DFunLike.subsingleton_dom 4 := fun h =>
  refl_ne_swap ((@h (Equiv.Perm Bool) Bool (fun _ => Bool) _).elim _ _)
-- `DFunLike.congr` idx 8: necessary — refl true ≠ swap true
theorem c2_5 : ¬ drop1% DFunLike.congr 8 := fun h =>
  absurd (@h (Equiv.Perm Bool) Bool Bool _ (Equiv.refl Bool) (Equiv.swap true false) true true rfl) (by simp)
-- `DFunLike.congr` idx 9: necessary — refl true ≠ refl false
theorem c2_6 : ¬ drop1% DFunLike.congr 9 := fun h =>
  absurd (@h (Equiv.Perm Bool) Bool Bool _ (Equiv.refl Bool) (Equiv.refl Bool) true false rfl) (by simp)
-- `DFunLike.congr_arg` idx 7: necessary — refl true ≠ refl false
theorem c2_7 : ¬ drop1% DFunLike.congr_arg 7 := fun h =>
  absurd (@h (Equiv.Perm Bool) Bool Bool _ (Equiv.refl Bool) true false) (by simp)
-- `EmbeddingLike.injective'` idx 4: necessary — the zero map in ℕ →+ ℕ is not injective
theorem c2_8 : ¬ drop1% EmbeddingLike.injective' 4 := fun h => by
  have := @h (ℕ →+ ℕ) ℕ ℕ inferInstance 0
  exact absurd (this (show (0 : ℕ →+ ℕ) 0 = (0 : ℕ →+ ℕ) 1 from rfl)) (by decide)
-- `EmbeddingLike.injective` idx 4: necessary — the zero map in ℕ →+ ℕ is not injective
theorem c2_9 : ¬ drop1% EmbeddingLike.injective 4 := fun h => by
  have := @h (ℕ →+ ℕ) ℕ ℕ inferInstance 0
  exact absurd (this (show (0 : ℕ →+ ℕ) 0 = (0 : ℕ →+ ℕ) 1 from rfl)) (by decide)
-- `EmbeddingLike.apply_eq_iff_eq` idx 4: necessary — the zero map in ℕ →+ ℕ
theorem c2_10 : ¬ drop1% EmbeddingLike.apply_eq_iff_eq 4 := fun h =>
  absurd ((@h (ℕ →+ ℕ) ℕ ℕ inferInstance 0 0 1).mp rfl) (by decide)
-- `EmbeddingLike.comp_injective` idx 5: necessary — e = 0 in ℕ →+ ℕ, f = id
theorem c2_11 : ¬ drop1% EmbeddingLike.comp_injective 5 := fun h => by
  have := (@h ℕ ℕ ℕ (ℕ →+ ℕ) inferInstance id 0).mpr Function.injective_id
  exact absurd (this (show ((0 : ℕ →+ ℕ) ∘ id) 0 = ((0 : ℕ →+ ℕ) ∘ id) 1 from rfl)) (by decide)
-- `EquivLike.coe_injective'` idx 6: removable — coe is determined by inv (coe e x = coe e (inv g (coe g x)) = coe g x)
theorem c2_12 : drop% EquivLike.coe_injective' 6 := by
  intro E α β _ e g hinv
  refine EquivLike.coe_injective' e g ?_ hinv
  funext x
  calc EquivLike.coe e x = EquivLike.coe e (EquivLike.inv g (EquivLike.coe g x)) := by
        rw [EquivLike.left_inv g x]
    _ = EquivLike.coe e (EquivLike.inv e (EquivLike.coe g x)) := by rw [hinv]
    _ = EquivLike.coe g x := EquivLike.right_inv e _
-- `EquivLike.coe_injective'` idx 7: removable — inv is determined by coe
theorem c2_13 : drop% EquivLike.coe_injective' 7 := by
  intro E α β _ e g hcoe
  refine EquivLike.coe_injective' e g hcoe ?_
  funext x
  calc EquivLike.inv e x = EquivLike.inv e (EquivLike.coe g (EquivLike.inv g x)) := by
        rw [EquivLike.right_inv g x]
    _ = EquivLike.inv e (EquivLike.coe e (EquivLike.inv g x)) := by rw [hcoe]
    _ = EquivLike.inv g x := EquivLike.left_inv e _
-- `EquivLike.subsingleton_dom` idx 4: necessary — Perm Bool is not subsingleton
theorem c2_14 : ¬ drop1% EquivLike.subsingleton_dom 4 := fun h =>
  refl_ne_swap ((@h (Equiv.Perm Bool) Bool Bool _).elim _ _)
-- `wellFounded_of_isEmpty` idx 1: necessary — the total relation on True
theorem c2_15 : ¬ drop0% wellFounded_of_isEmpty 1 := fun h =>
  acc_irr ((@h True (fun _ _ => True)).apply trivial) trivial
-- `not_isEmpty_of_nonempty` idx 1: necessary — α = False
theorem c2_16 : ¬ drop0% not_isEmpty_of_nonempty 1 := fun h => h False ⟨id⟩
-- `Function.extend_of_isEmpty` idx 3: necessary — extend id (const true) (const false) () = true
theorem c2_17 : ¬ drop1% Function.extend_of_isEmpty 3 := fun H =>
  absurd ((Function.injective_id.extend_apply (fun _ : Unit => true) (fun _ : Unit => false) ()).symm.trans
    (congrFun (@H Unit Unit Bool id (fun _ => true) (fun _ => false)) ())) (by decide)
-- `leftTotal_empty` idx 3: necessary — empty relation on True
theorem c2_18 : ¬ drop0% leftTotal_empty 3 := fun h => by
  obtain ⟨b, hb⟩ := @h True True (fun _ _ => False) trivial
  exact hb
-- `leftTotal_iff_isEmpty_left` idx 3: necessary — total relation on True
theorem c2_19 : ¬ drop0% leftTotal_iff_isEmpty_left 3 := fun h =>
  ((@h True True (fun _ _ => True)).mp (fun _ => ⟨trivial, trivial⟩)).false trivial
-- `rightTotal_empty` idx 3: necessary — empty relation on True
theorem c2_20 : ¬ drop0% rightTotal_empty 3 := fun h => by
  obtain ⟨b, hb⟩ := @h True True (fun _ _ => False) trivial
  exact hb
-- `rightTotal_iff_isEmpty_right` idx 3: necessary — total relation on True
theorem c2_21 : ¬ drop0% rightTotal_iff_isEmpty_right 3 := fun h =>
  ((@h True True (fun _ _ => True)).mp (fun _ => ⟨trivial, trivial⟩)).false trivial
-- `biTotal_empty` idx 3: necessary — α = True, β = False
theorem c2_22 : ¬ drop0% biTotal_empty 3 := fun h => by
  obtain ⟨b, _⟩ := (@h True False (fun _ _ => False) inferInstance).1 trivial
  exact b
-- `biTotal_empty` idx 4: necessary — α = False, β = True
theorem c2_23 : ¬ drop0% biTotal_empty 4 := fun h => by
  obtain ⟨a, _⟩ := (@h False True (fun _ _ => False) inferInstance).2 trivial
  exact a
-- `biTotal_iff_isEmpty_right` idx 3: necessary — total relation on True
theorem c2_24 : ¬ drop0% biTotal_iff_isEmpty_right 3 := fun h =>
  ((@h True True (fun _ _ => True)).mp ⟨fun _ => ⟨trivial, trivial⟩, fun _ => ⟨trivial, trivial⟩⟩).false trivial
-- `biTotal_iff_isEmpty_left` idx 3: necessary — total relation on True
theorem c2_25 : ¬ drop0% biTotal_iff_isEmpty_left 3 := fun h =>
  ((@h True True (fun _ _ => True)).mp ⟨fun _ => ⟨trivial, trivial⟩, fun _ => ⟨trivial, trivial⟩⟩).false trivial
-- `Function.not_surjective_of_isEmpty_of_nonempty` idx 3: necessary — id on False is surjective
theorem c2_26 : ¬ drop0% Function.not_surjective_of_isEmpty_of_nonempty 3 := fun h =>
  @h False False _ id Function.surjective_id
-- `Function.Surjective.isEmpty` idx 4: necessary — False.elim : False → True
theorem c2_27 : ¬ drop0% Function.Surjective.isEmpty 4 := fun h =>
  (@h False True ⟨id⟩ False.elim).false trivial
-- `instIsEmptyForallOfNonempty` idx 3: necessary — α = False: the Pi type is inhabited
theorem c2_28 : ¬ drop0% instIsEmptyForallOfNonempty 3 := fun h =>
  (@h False (fun _ => False) (fun x => x.elim)).false (fun x => x)
-- `instIsEmptyPSum` idx 2: necessary — α = True
theorem c2_29 : ¬ drop0% instIsEmptyPSum 2 := fun h => (@h True False _).false (PSum.inl trivial)
-- `instIsEmptyPSum` idx 3: necessary — β = True
theorem c2_30 : ¬ drop0% instIsEmptyPSum 3 := fun h => (@h False True _).false (PSum.inr trivial)
-- `instIsEmptySum` idx 2: necessary — α = Unit
theorem c2_31 : ¬ drop0% instIsEmptySum 2 := fun h => (@h Unit Empty _).false (Sum.inl ())
-- `instIsEmptySum` idx 3: necessary — β = Unit
theorem c2_32 : ¬ drop0% instIsEmptySum 3 := fun h => (@h Empty Unit _).false (Sum.inr ())
-- `congr_arg_heq` idx 5: necessary — id true vs id false
theorem c2_33 : ¬ drop1% congr_arg_heq 5 := fun h =>
  absurd (eq_of_heq (@h Bool (fun _ => Bool) id true false)) (by decide)
-- `dcongr_heq` idx 8: necessary — f = id on Bool, a₁ = true, a₂ = false
theorem c2_34 : ¬ drop1% dcongr_heq 8 := fun h =>
  absurd (eq_of_heq (@h Bool Bool (fun _ => Bool) (fun _ => Bool) id id true false
    (fun _ _ _ => rfl) (fun _ _ => HEq.rfl))) (by decide)
-- `dcongr_heq` idx 9: necessary — β₁ = const Bool, β₂ = const Unit on Unit (Bool ≠ Unit)
theorem c2_35 : ¬ drop1% dcongr_heq 9 := fun h =>
  bool_ne_unit (type_eq_of_heq (@h Unit Unit (fun _ => Bool) (fun _ => Unit) (fun _ => true) (fun _ => ())
    () () HEq.rfl (fun _ hb => absurd (congrFun (eq_of_heq hb) ()) bool_ne_unit)))
-- `dcongr_heq` idx 10: necessary — const true vs const false on Unit
theorem c2_36 : ¬ drop1% dcongr_heq 10 := fun h =>
  absurd (eq_of_heq (@h Unit Unit (fun _ => Bool) (fun _ => Bool) (fun _ => true) (fun _ => false)
    () () HEq.rfl (fun _ _ _ => rfl))) (by decide)
-- `cast_heq_iff_heq` idx 3: necessary — α = True, β = False
theorem c2_37 : ¬ indep0% cast_heq_iff_heq 3 := fun h => cast (@h True False True trivial trivial) trivial
-- `heq_cast_iff_heq` idx 3: necessary — β = True, γ = False
theorem c2_38 : ¬ indep0% heq_cast_iff_heq 3 := fun h => cast (@h True True False trivial trivial) trivial
-- `heq_of_eq_cast` idx 4: necessary — α = Bool, β = Unit (universe 1)
theorem c2_39 : ¬ indep1% heq_of_eq_cast 4 := fun h => bool_ne_unit (@h Bool Unit true ()).symm
-- `eq_cast_iff_heq` idx 2: necessary — α = Bool, β = Unit (universe 1)
theorem c2_40 : ¬ indep1% eq_cast_iff_heq 2 := fun h => bool_ne_unit (@h Bool Unit true ()).symm

-- `forall₂_imp` idx 4: necessary — p = True, q = False
theorem c2_41 : ¬ drop0% forall₂_imp 4 := fun h =>
  @h True (fun _ => True) (fun _ _ => True) (fun _ _ => False) (fun _ _ => trivial) trivial trivial
-- `forall₂_imp` idx 5: necessary — p = q = False
theorem c2_42 : ¬ drop0% forall₂_imp 5 := fun h =>
  @h True (fun _ => True) (fun _ _ => False) (fun _ _ => False) (fun _ _ x => x) trivial trivial
-- `forall₃_imp` idx 5: necessary — p = True, q = False
theorem c2_43 : ¬ drop0% forall₃_imp 5 := fun h =>
  @h True (fun _ => True) (fun _ _ => True) (fun _ _ _ => True) (fun _ _ _ => False)
    (fun _ _ _ => trivial) trivial trivial trivial
-- `forall₃_imp` idx 6: necessary — p = q = False
theorem c2_44 : ¬ drop0% forall₃_imp 6 := fun h =>
  @h True (fun _ => True) (fun _ _ => True) (fun _ _ _ => False) (fun _ _ _ => False)
    (fun _ _ _ x => x) trivial trivial trivial
-- `Exists₂.imp` idx 4: necessary — p = True, q = False
theorem c2_45 : ¬ drop0% Exists₂.imp 4 := fun h => by
  obtain ⟨_, _, h⟩ := @h True (fun _ => True) (fun _ _ => True) (fun _ _ => False) ⟨trivial, trivial, trivial⟩
  exact h
-- `Exists₂.imp` idx 5: necessary — p = q = False
theorem c2_46 : ¬ drop0% Exists₂.imp 5 := fun h => by
  obtain ⟨_, _, h⟩ := @h True (fun _ => True) (fun _ _ => False) (fun _ _ => False) (fun _ _ x => x)
  exact h
-- `Exists₃.imp` idx 5: necessary — p = True, q = False
theorem c2_47 : ¬ drop0% Exists₃.imp 5 := fun h => by
  obtain ⟨_, _, _, h⟩ := @h True (fun _ => True) (fun _ _ => True) (fun _ _ _ => True) (fun _ _ _ => False)
    ⟨trivial, trivial, trivial, trivial⟩
  exact h
-- `Exists₃.imp` idx 6: necessary — p = q = False
theorem c2_48 : ¬ drop0% Exists₃.imp 6 := fun h => by
  obtain ⟨_, _, _, h⟩ := @h True (fun _ => True) (fun _ _ => True) (fun _ _ _ => False) (fun _ _ _ => False)
    (fun _ _ _ x => x)
  exact h
-- `forall_imp_iff_exists_imp` idx 3: necessary — α = False, b = True
theorem c2_49 : ¬ drop0% forall_imp_iff_exists_imp 3 := fun h => by
  obtain ⟨x, _⟩ := (@h False (fun _ => True) True).mp (fun _ => trivial)
  exact x
-- `Exists.fst` idx 2: necessary — b = False
theorem c2_50 : ¬ drop0% Exists.fst 2 := fun h => @h False (fun _ => True)
-- `Exists.snd` idx 2: necessary — b = False (dependent)
theorem c2_51 : ¬ indep0% Exists.snd 2 := fun h => by
  obtain ⟨x, _⟩ := @h False (fun _ => True)
  exact x
-- `exists_prop_of_false` idx 2: necessary — p = True
theorem c2_52 : ¬ drop0% exists_prop_of_false 2 := fun h => @h True (fun _ => True) ⟨trivial, trivial⟩
-- `forall_prop_congr` idx 4: necessary — q = True, q' = False
theorem c2_53 : ¬ drop0% forall_prop_congr 4 := fun h =>
  (@h True True (fun _ => True) (fun _ => False) Iff.rfl).mp (fun _ => trivial) trivial
-- `forall_prop_congr` idx 5: necessary — p = True, p' = False (dependent)
theorem c2_54 : ¬ indep0% forall_prop_congr 5 := fun h =>
  (@h True False (fun _ => True) (fun _ => True) (fun _ => Iff.rfl)).mp trivial
-- `forall_prop_congr'` idx 4: necessary — q = True, q' = False
theorem c2_55 : ¬ drop0% forall_prop_congr' 4 := fun h =>
  cast (@h True True (fun _ => True) (fun _ => False) Iff.rfl) (fun _ => trivial) trivial
-- `forall_prop_congr'` idx 5: necessary — p = True, p' = False (dependent)
theorem c2_56 : ¬ indep0% forall_prop_congr' 5 := fun h =>
  (@h True False (fun _ => True) (fun _ => True) (fun _ => Iff.rfl)).mp trivial
-- `Classical.axiom_of_choice` idx 3: necessary — r empty
theorem c2_57 : ¬ drop0% Classical.axiom_of_choice 3 := fun h => by
  obtain ⟨f, hf⟩ := @h True (fun _ => True) (fun _ _ => False)
  exact hf trivial
-- `BEx.elim` idx 4: necessary — P = False, b = False
theorem c2_58 : ¬ drop0% BEx.elim 4 := fun h =>
  @h True (fun _ => True) (fun _ _ => False) False (fun _ _ x => x)
-- `BEx.elim` idx 5: necessary — P = True, b = False
theorem c2_59 : ¬ drop0% BEx.elim 5 := fun h =>
  @h True (fun _ => True) (fun _ _ => True) False ⟨trivial, trivial, trivial⟩
-- `BEx.intro` idx 4: necessary — p = False (dependent)
theorem c2_60 : ¬ indep0% BEx.intro 4 := fun h => @h True (fun _ => False) (fun _ _ => True) trivial
-- `BEx.intro` idx 5: necessary — P = False
theorem c2_61 : ¬ drop0% BEx.intro 5 := fun h => by
  obtain ⟨_, _, h⟩ := @h True (fun _ => True) (fun _ _ => False) trivial trivial
  exact h
-- `BAll.imp_right` idx 4: necessary — P = True, Q = False
theorem c2_62 : ¬ drop0% BAll.imp_right 4 := fun h =>
  @h True (fun _ => True) (fun _ _ => True) (fun _ _ => False) (fun _ _ => trivial) trivial trivial
-- `BAll.imp_right` idx 5: necessary — P = Q = False
theorem c2_63 : ¬ drop0% BAll.imp_right 5 := fun h =>
  @h True (fun _ => True) (fun _ _ => False) (fun _ _ => False) (fun _ _ x => x) trivial trivial
-- `BAll.imp_right` idx 7: necessary — p = False (dependent)
theorem c2_64 : ¬ indep0% BAll.imp_right 7 := fun h =>
  @h True (fun _ => False) (fun _ _ => True) (fun _ _ => True) (fun _ h _ => h.elim) (fun _ h => h.elim) trivial
-- `BEx.imp_right` idx 4: necessary — P = True, Q = False
theorem c2_65 : ¬ drop0% BEx.imp_right 4 := fun h => by
  obtain ⟨_, _, h⟩ := @h True (fun _ => True) (fun _ _ => True) (fun _ _ => False) ⟨trivial, trivial, trivial⟩
  exact h
-- `BEx.imp_right` idx 5: necessary — P = Q = False
theorem c2_66 : ¬ drop0% BEx.imp_right 5 := fun h => by
  obtain ⟨_, _, h⟩ := @h True (fun _ => True) (fun _ _ => False) (fun _ _ => False) (fun _ _ x => x)
  exact h
-- `not_forall₂_of_exists₂_not` idx 3: necessary — P = True
theorem c2_67 : ¬ drop0% not_forall₂_of_exists₂_not 3 := fun h =>
  @h True (fun _ => True) (fun _ _ => True) (fun _ _ => trivial)
-- `forall_and_left` idx 1: necessary — α = False, q = False
theorem c2_68 : ¬ drop0% forall_and_left 1 := fun h =>
  ((@h False False (fun _ => True)).mp (fun x => x.elim)).1
-- `forall_and_right` idx 1: necessary — α = False, q = False
theorem c2_69 : ¬ drop0% forall_and_right 1 := fun h =>
  ((@h False (fun _ => True) False).mp (fun x => x.elim)).2
-- `Function.Injective.ite` idx 5: necessary — p = True, g constant 0, f = (1, 2) on Bool
theorem c2_70 : ¬ drop1% Function.Injective.ite 5 := fun h => by
  have := @h ℕ Bool (fun _ => True) inferInstance (fun _ => 0) (fun b => if b then 1 else 2)
    (by intro a b hab; cases a <;> cases b <;> simp_all)
    (by intro x y hxy; cases y <;> simp at hxy)
  exact absurd (this (show (if True then 0 else if true then 1 else 2 : ℕ) = (if True then 0 else if false then 1 else 2) by simp)) (by decide)
-- `Function.Injective.ite` idx 7: necessary — p = False, f constant 0, g = (1, 2) on Bool
theorem c2_71 : ¬ drop1% Function.Injective.ite 7 := fun h => by
  have := @h ℕ Bool (fun _ => False) inferInstance (fun b => if b then 1 else 2)
    (by intro a b hab; cases a <;> cases b <;> simp_all) (fun _ => 0)
    (by intro x y hxy; cases x <;> simp at hxy)
  exact absurd (this (show (if False then (if true then 1 else 2) else 0 : ℕ) = (if False then (if false then 1 else 2) else 0) by simp)) (by decide)
-- `Function.Injective.ite` idx 8: necessary — p = (· = true), g = id, f = not
theorem c2_72 : ¬ drop1% Function.Injective.ite 8 := fun h => by
  have := @h Bool Bool (fun b => b = true) inferInstance id Function.injective_id not
    (by intro a b hab; cases a <;> cases b <;> simp_all)
  exact absurd (this (show (if true = true then id true else not true) = (if false = true then id false else not false) by decide)) (by decide)
-- `Membership.mem.ne_of_notMem` idx 6: necessary — a = b = 0, s = ∅
theorem c2_73 : ¬ drop0% Membership.mem.ne_of_notMem 6 := fun h =>
  @h ℕ (Set ℕ) _ ∅ 0 0 (Set.notMem_empty 0) rfl
-- `Membership.mem.ne_of_notMem` idx 7: necessary — a = b = 0, s = univ
theorem c2_74 : ¬ drop0% Membership.mem.ne_of_notMem 7 := fun h =>
  @h ℕ (Set ℕ) _ Set.univ 0 0 (Set.mem_univ 0) rfl
-- `Membership.mem.ne_of_notMem'` idx 6: necessary — s = t = ∅
theorem c2_75 : ¬ drop0% Membership.mem.ne_of_notMem' 6 := fun h =>
  @h ℕ (Set ℕ) _ ∅ ∅ 0 (Set.notMem_empty 0) rfl
-- `Membership.mem.ne_of_notMem'` idx 7: necessary — s = t = univ
theorem c2_76 : ¬ drop0% Membership.mem.ne_of_notMem' 7 := fun h =>
  @h ℕ (Set ℕ) _ Set.univ Set.univ 0 (Set.mem_univ 0) rfl
-- `beq_ext` idx 3: necessary — constant-true and constant-false BEq on Bool
theorem c2_77 : ¬ drop0% beq_ext 3 := fun h =>
  absurd (congrArg (fun i : BEq Bool => @BEq.beq Bool i true true) (@h Bool ⟨fun _ _ => true⟩ ⟨fun _ _ => false⟩))
    (by decide)
-- `lawful_beq_subsingleton` idx 3: necessary — the lawful BEq on Bool vs constant false
theorem c2_78 : ¬ drop0% lawful_beq_subsingleton 3 := fun h =>
  absurd (congrArg (fun i : BEq Bool => @BEq.beq Bool i true true) (@h Bool ⟨fun _ _ => false⟩ instBEqOfDecidableEq inferInstance))
    (by decide)
-- `lawful_beq_subsingleton` idx 4: necessary — the lawful BEq on Bool vs constant false
theorem c2_79 : ¬ drop0% lawful_beq_subsingleton 4 := fun h =>
  absurd (congrArg (fun i : BEq Bool => @BEq.beq Bool i true true) (@h Bool instBEqOfDecidableEq ⟨fun _ _ => false⟩ inferInstance))
    (by decide)

-- `Real.toNNReal_sum_of_nonneg` idx 3: necessary — f = (1, -1) on Bool
theorem c2_80 : ¬ drop0% Real.toNNReal_sum_of_nonneg 3 := fun h => by
  have := @h Bool Finset.univ (fun b => if b then 1 else -1)
  simp [Fintype.sum_bool, tn_m1] at this
-- `Real.toNNReal_prod_of_nonneg` idx 3: necessary — f = (-1, -1) on Bool
theorem c2_81 : ¬ drop0% Real.toNNReal_prod_of_nonneg 3 := fun h => by
  have := @h Bool Finset.univ (fun _ => -1)
  simp [Fintype.prod_bool, tn_m1] at this
-- `NNReal.le_iInf_add_iInf` idx 2: necessary — ι = Empty (⨅ = 0), a = 1
theorem c2_82 : ¬ drop1% NNReal.le_iInf_add_iInf 2 := fun h => by
  have := @h Empty Unit _ Empty.elim (fun _ => 0) 1 (fun i => i.elim)
  simp [NNReal.iInf_empty] at this
-- `NNReal.le_iInf_add_iInf` idx 3: necessary — ι' = Empty (⨅ = 0), a = 1
theorem c2_83 : ¬ drop1% NNReal.le_iInf_add_iInf 3 := fun h => by
  have := @h Unit Empty _ (fun _ => 0) Empty.elim 1 (fun _ j => j.elim)
  simp [NNReal.iInf_empty] at this
-- `NNReal.le_mul_iInf` idx 1: necessary — ι = Empty, a = g = 1
theorem c2_84 : ¬ drop1% NNReal.le_mul_iInf 1 := fun h => by
  have := @h Empty 1 1 Empty.elim (fun i => i.elim)
  simp [NNReal.iInf_empty] at this
-- `NNReal.le_iInf_mul` idx 1: necessary — ι = Empty, a = h = 1
theorem c2_85 : ¬ drop1% NNReal.le_iInf_mul 1 := fun h => by
  have := @h Empty 1 Empty.elim 1 (fun i => i.elim)
  simp [NNReal.iInf_empty] at this
-- `NNReal.le_iInf_mul_iInf` idx 1: necessary — ι = Empty, a = 1
theorem c2_86 : ¬ drop1% NNReal.le_iInf_mul_iInf 1 := fun h => by
  have := @h Empty 1 Empty.elim Empty.elim (fun i => i.elim)
  simp [NNReal.iInf_empty] at this
-- `NNReal.instIsScalarTowerOfReal` idx 5: necessary — M = N = ℝ with m • n := m + n
theorem c2_87 : ¬ drop0% NNReal.instIsScalarTowerOfReal 5 := fun h => by
  have := (@h ℝ ℝ _ _ S1).1 (2 : NNReal) (0 : ℝ) (1 : ℝ)
  simp only [S1_apply, NNReal.smul_def, smul_eq_mul] at this
  norm_num at this
-- `NNReal.smulCommClass_left` idx 4: necessary — M = N = ℝ with m • n := m + n
theorem c2_88 : ¬ drop0% NNReal.smulCommClass_left 4 := fun h => by
  have := (@h ℝ ℝ _ S1).1 (2 : NNReal) (1 : ℝ) (0 : ℝ)
  simp only [S1_apply, NNReal.smul_def, smul_eq_mul] at this
  norm_num at this
-- `NNReal.smulCommClass_right` idx 4: necessary — M = N = ℝ with m • n := m + n
theorem c2_89 : ¬ drop0% NNReal.smulCommClass_right 4 := fun h => by
  have := (@h ℝ ℝ _ S1).1 (1 : ℝ) (2 : NNReal) (0 : ℝ)
  simp only [S1_apply, NNReal.smul_def, smul_eq_mul] at this
  norm_num at this
-- `Real.toNNReal_eq_toNNReal_iff` idx 2: necessary — r = -1, p = 0
theorem c2_94 : ¬ drop0% Real.toNNReal_eq_toNNReal_iff 2 := fun h => by
  have := (@h (-1) 0 le_rfl).mp (by rw [tn_m1, Real.toNNReal_zero])
  norm_num at this
-- `Real.toNNReal_eq_toNNReal_iff` idx 3: necessary — r = 0, p = -1
theorem c2_95 : ¬ drop0% Real.toNNReal_eq_toNNReal_iff 3 := fun h => by
  have := (@h 0 (-1) le_rfl).mp (by rw [tn_m1, Real.toNNReal_zero])
  norm_num at this
-- `Real.toNNReal_lt_toNNReal_iff` idx 2: necessary — r = -2, p = -1
theorem c2_96 : ¬ drop0% Real.toNNReal_lt_toNNReal_iff 2 := fun h => by
  have := (@h (-2) (-1)).mpr (by norm_num)
  rw [tn_m1, tn_m2] at this
  exact lt_irrefl _ this
-- `Real.toNNReal_lt_toNNReal_iff_of_nonneg` idx 2: necessary — r = -2, p = -1
theorem c2_97 : ¬ drop0% Real.toNNReal_lt_toNNReal_iff_of_nonneg 2 := fun h => by
  have := (@h (-2) (-1)).mpr (by norm_num)
  rw [tn_m1, tn_m2] at this
  exact lt_irrefl _ this
-- `Real.toNNReal_le_toNNReal_iff_of_pos` idx 2: necessary — r = -1, p = -2
theorem c2_98 : ¬ drop0% Real.toNNReal_le_toNNReal_iff_of_pos 2 := fun h => by
  have := (@h (-1) (-2)).mp (by rw [tn_m1, tn_m2])
  norm_num at this
-- `Real.toNNReal_add` idx 2: necessary — r = -1, p = 1
theorem c2_99 : ¬ drop0% Real.toNNReal_add 2 := fun h => by
  have := @h (-1) 1 zero_le_one
  norm_num [tn_m1] at this
-- `Real.toNNReal_add_toNNReal` idx 2: necessary — r = -1, p = 1
theorem c2_100 : ¬ drop0% Real.toNNReal_add_toNNReal 2 := fun h => by
  have := @h (-1) 1 zero_le_one
  norm_num [tn_m1] at this
-- `Real.toNNReal_add_toNNReal` idx 3: necessary — r = 1, p = -1
theorem c2_101 : ¬ drop0% Real.toNNReal_add_toNNReal 3 := fun h => by
  have := @h 1 (-1) zero_le_one
  norm_num [tn_m1] at this
-- `Real.toNNReal_pow` idx 1: necessary — x = -1, n = 2
theorem c2_102 : ¬ drop0% Real.toNNReal_pow 1 := fun h => by
  have := @h (-1) 2
  norm_num [tn_m1] at this
-- `Real.toNNReal_zpow` idx 1: necessary — x = -1, n = 2
theorem c2_103 : ¬ drop0% Real.toNNReal_zpow 1 := fun h => by
  have := @h (-1) 2
  norm_num [tn_m1] at this
-- `Real.toNNReal_mul` idx 2: necessary — p = q = -1
theorem c2_104 : ¬ drop0% Real.toNNReal_mul 2 := fun h => by
  have := @h (-1) (-1)
  norm_num [tn_m1] at this
-- `NNReal.exists_mem_Ico_zpow` idx 2: necessary — x = 0, y = 2
theorem c2_105 : ¬ drop0% NNReal.exists_mem_Ico_zpow 2 := fun h => by
  obtain ⟨n, h1, _⟩ := @h 0 2 one_lt_two
  exact absurd h1 (not_le.mpr (zpow_pos (by norm_num : (0:NNReal) < 2) n))
-- `Real.toNNReal_div` idx 2: necessary — x = y = -1
theorem c2_106 : ¬ drop0% Real.toNNReal_div 2 := fun h => by
  have := @h (-1) (-1)
  norm_num [tn_m1] at this
-- `Real.toNNReal_div'` idx 2: necessary — x = y = -1
theorem c2_107 : ¬ drop0% Real.toNNReal_div' 2 := fun h => by
  have := @h (-1) (-1)
  norm_num [tn_m1] at this
-- `NNReal.iSup_eq_zero` idx 2: necessary — ι = ℕ, f n = n: unbounded, so ⨆ is the junk value 0
theorem c2_108 : ¬ drop1% NNReal.iSup_eq_zero 2 := fun h => by
  have hs : ⨆ n : ℕ, (n : NNReal) = 0 := NNReal.iSup_of_not_bddAbove (by
    rintro ⟨b, hb⟩
    obtain ⟨n, hn⟩ := exists_nat_gt b
    exact absurd (hb ⟨n, rfl⟩) (not_le.mpr hn))
  have := (@h ℕ (fun n => (n : NNReal))).mp hs 1
  norm_num at this
-- `Set.OrdConnected.preimage_coe_nnreal_real` idx 1: necessary — s = {0, 2}
theorem c2_109 : ¬ drop0% Set.OrdConnected.preimage_coe_nnreal_real 1 := fun h => by
  have := (@h {0, 2}).out (show (0:NNReal) ∈ NNReal.toReal ⁻¹' {0, 2} by simp)
    (show (2:NNReal) ∈ NNReal.toReal ⁻¹' {0, 2} by simp) (show (1:NNReal) ∈ Set.Icc 0 2 by
      constructor <;> norm_num)
  norm_num at this
-- `Set.OrdConnected.image_coe_nnreal_real` idx 1: necessary — t = {0, 2}
theorem c2_110 : ¬ drop0% Set.OrdConnected.image_coe_nnreal_real 1 := fun h => by
  have := (@h {0, 2}).out (show (0:ℝ) ∈ NNReal.toReal '' {0, 2} from ⟨0, by simp, by simp⟩)
    (show (2:ℝ) ∈ NNReal.toReal '' {0, 2} from ⟨2, by simp, by simp⟩) (show (1:ℝ) ∈ Set.Icc 0 2 by
      constructor <;> norm_num)
  obtain ⟨x, hx, hx1⟩ := this
  rcases hx with rfl | rfl <;> norm_num at hx1
-- `Set.OrdConnected.image_real_toNNReal` idx 1: necessary — s = {0, 2}
theorem c2_111 : ¬ drop0% Set.OrdConnected.image_real_toNNReal 1 := fun h => by
  have := (@h {0, 2}).out (show (0:NNReal) ∈ Real.toNNReal '' {0, 2} from ⟨0, by simp, by simp⟩)
    (show (2:NNReal) ∈ Real.toNNReal '' {0, 2} from ⟨2, by simp, by simp⟩) (show (1:NNReal) ∈ Set.Icc 0 2 by
      constructor <;> norm_num)
  obtain ⟨x, hx, hx1⟩ := this
  rcases hx with rfl | rfl <;> norm_num at hx1
-- `Set.OrdConnected.preimage_real_toNNReal` idx 1: necessary — t = {0, 2}
theorem c2_112 : ¬ drop0% Set.OrdConnected.preimage_real_toNNReal 1 := fun h => by
  have := (@h {0, 2}).out (show (0:ℝ) ∈ Real.toNNReal ⁻¹' {0, 2} by simp)
    (show (2:ℝ) ∈ Real.toNNReal ⁻¹' {0, 2} by simp) (show (1:ℝ) ∈ Set.Icc 0 2 by
      constructor <;> norm_num)
  norm_num at this
-- `Real.nnabs_of_nonneg` idx 1: necessary — x = -1
theorem c2_113 : ¬ drop0% Real.nnabs_of_nonneg 1 := fun h => by
  have := congrArg NNReal.toReal (@h (-1))
  norm_num [tn_m1] at this
-- `Real.nnreal_induction_on` idx 1: necessary — motive = False
theorem c2_114 : ¬ drop0% Real.nnreal_induction_on 1 := fun h => @h (fun _ => False) (fun _ h => h) 0
-- `Real.nnreal_induction_on` idx 2: necessary — motive = (0 ≤ ·)
theorem c2_115 : ¬ drop0% Real.nnreal_induction_on 2 := fun h =>
  absurd (@h (fun r => 0 ≤ r) (fun x => x.2) (-1)) (by norm_num)
-- `Real.nnreal_induction_on'` idx 1: necessary — motive = (· ≠ 0)
theorem c2_116 : ¬ drop0% Real.nnreal_induction_on' 1 := fun h =>
  @h (fun r => r ≠ 0) (fun x hx => (NNReal.coe_pos.mpr hx).ne')
    (fun x hx _ => neg_ne_zero.mpr (NNReal.coe_pos.mpr hx).ne') 0 rfl
-- `Real.nnreal_induction_on'` idx 2: necessary — motive = (· ≤ 0)
theorem c2_117 : ¬ drop0% Real.nnreal_induction_on' 2 := fun h =>
  absurd (@h (fun r => r ≤ 0) le_rfl (fun x _ _ => neg_nonpos.mpr x.2) 1) (by norm_num)
-- `Real.nnreal_induction_on'` idx 3: necessary — motive = (0 ≤ ·)
theorem c2_118 : ¬ drop0% Real.nnreal_induction_on' 3 := fun h =>
  absurd (@h (fun r => 0 ≤ r) le_rfl (fun x _ => x.2) (-1)) (by norm_num)

-- `Nonempty.map` idx 3: necessary — α = β = False
theorem c2_123 : ¬ drop0% Nonempty.map 3 := fun h => by
  obtain ⟨x⟩ := @h False False id
  exact x
-- `Nonempty.map2` idx 4: necessary — α = False, β = True, γ = False
theorem c2_124 : ¬ drop0% Nonempty.map2 4 := fun h => by
  obtain ⟨x⟩ := @h False True False (fun a _ => a) ⟨trivial⟩
  exact x
-- `Nonempty.map2` idx 5: necessary — α = True, β = False, γ = False
theorem c2_125 : ¬ drop0% Nonempty.map2 5 := fun h => by
  obtain ⟨x⟩ := @h True False False (fun _ b => b) ⟨trivial⟩
  exact x
-- `Nonempty.elim_to_inhabited` idx 1: necessary — α = False, p = False
theorem c2_126 : ¬ drop0% Nonempty.elim_to_inhabited 1 := fun h => @h False False (fun a => a.default)
-- `Function.Surjective.nonempty` idx 2: necessary — id on False
theorem c2_127 : ¬ drop0% Function.Surjective.nonempty 2 := fun h => by
  obtain ⟨x⟩ := @h False False id Function.surjective_id
  exact x
-- `Function.Surjective.nonempty` idx 4: necessary — α = False, β = True
theorem c2_128 : ¬ drop0% Function.Surjective.nonempty 4 := fun h => by
  obtain ⟨x⟩ := @h False True ⟨trivial⟩ False.elim
  exact x
-- `nontrivial_of_lt` idx 4: necessary — α = Unit
theorem c2_129 : ¬ drop0% nontrivial_of_lt 4 := fun h => not_nontrivial Unit (@h Unit _ () ())
-- `exists_pair_lt` idx 1: necessary — α = Unit
theorem c2_130 : ¬ drop0% exists_pair_lt 1 := fun h => by
  obtain ⟨x, y, hxy⟩ := h Unit
  exact lt_irrefl x (by rwa [Subsingleton.elim x y])
-- `Option.nontrivial` idx 1: necessary — Option Empty has one element
theorem c2_131 : ¬ drop0% Option.nontrivial 1 := fun h => by
  obtain ⟨x, y, hxy⟩ := (@h Empty).exists_pair_ne
  rcases x with _ | ⟨⟨⟩⟩
  rcases y with _ | ⟨⟨⟩⟩
  exact hxy rfl
-- `nontrivial_prod_right` idx 2: necessary — α = Empty, β = Bool
theorem c2_132 : ¬ drop0% nontrivial_prod_right 2 := fun h => by
  obtain ⟨⟨a, _⟩, _, _⟩ := (@h Empty Bool ⟨⟨true, false, by decide⟩⟩).exists_pair_ne
  exact a.elim
-- `nontrivial_prod_right` idx 3: necessary — α = β = Unit
theorem c2_133 : ¬ drop0% nontrivial_prod_right 3 := fun h => not_nontrivial (Unit × Unit) (@h Unit Unit _)
-- `nontrivial_prod_left` idx 2: necessary — α = β = Unit
theorem c2_134 : ¬ drop0% nontrivial_prod_left 2 := fun h => not_nontrivial (Unit × Unit) (@h Unit Unit _)
-- `nontrivial_prod_left` idx 3: necessary — α = Bool, β = Empty
theorem c2_135 : ¬ drop0% nontrivial_prod_left 3 := fun h => by
  obtain ⟨⟨_, b⟩, _, _⟩ := (@h Bool Empty _).exists_pair_ne
  exact b.elim
-- `instNontrivialSum` idx 2: necessary — α = Unit, β = Empty
theorem c2_136 : ¬ drop0% instNontrivialSum 2 := fun h => not_nontrivial (Unit ⊕ Empty) (@h Unit Empty)
-- `instNontrivialSum_1` idx 2: necessary — α = Empty, β = Unit
theorem c2_137 : ¬ drop0% instNontrivialSum_1 2 := fun h => not_nontrivial (Empty ⊕ Unit) (@h Empty Unit)
-- `instNontrivialSumOfNonempty` idx 2: necessary — α = Empty, β = Unit
theorem c2_138 : ¬ drop0% instNontrivialSumOfNonempty 2 := fun h =>
  not_nontrivial (Empty ⊕ Unit) (@h Empty Unit _)
-- `instNontrivialSumOfNonempty` idx 3: necessary — α = Unit, β = Empty
theorem c2_139 : ¬ drop0% instNontrivialSumOfNonempty 3 := fun h =>
  not_nontrivial (Unit ⊕ Empty) (@h Unit Empty _)
-- `instSubsingletonSumOfIsEmpty` idx 2: necessary — α = Bool, β = Empty
theorem c2_140 : ¬ drop0% instSubsingletonSumOfIsEmpty 2 := fun h =>
  absurd ((@h Bool Empty _).elim (Sum.inl true) (Sum.inl false)) (by simp)
-- `instSubsingletonSumOfIsEmpty_1` idx 3: necessary — α = Empty, β = Bool
theorem c2_141 : ¬ drop0% instSubsingletonSumOfIsEmpty_1 3 := fun h =>
  absurd ((@h Empty Bool _).elim (Sum.inr true) (Sum.inr false)) (by simp)
-- `Pi.nontrivial_at` idx 3: necessary — I = Bool, f true = Bool, f false = Empty
theorem c2_142 : ¬ drop0% Pi.nontrivial_at 3 := fun h => by
  obtain ⟨g, _, _⟩ := (@h Bool (fun b => Bool.rec Empty Bool b) true (inferInstanceAs (Nontrivial Bool))).exists_pair_ne
  exact Empty.elim (g false)
-- `Pi.nontrivial_at` idx 4: necessary — I = Unit, f = const Unit
theorem c2_143 : ¬ drop0% Pi.nontrivial_at 4 := fun h =>
  not_nontrivial (Unit → Unit) (@h Unit (fun _ => Unit) () _)
-- `Pi.nontrivial` idx 3: necessary — I = Bool, f false = Bool, f true = Empty
theorem c2_144 : ¬ drop0% Pi.nontrivial 3 := fun h => by
  obtain ⟨g, _, _⟩ := (@h Bool (fun b => Bool.rec Bool Empty b) _ (inferInstanceAs (Nontrivial Bool))).exists_pair_ne
  exact Empty.elim (g true)
-- `Pi.nontrivial` idx 4: necessary — I = Unit, f = const Unit
theorem c2_145 : ¬ drop0% Pi.nontrivial 4 := fun h =>
  not_nontrivial (Unit → Unit) (@h Unit (fun _ => Unit) _ _)
-- `Function.nontrivial` idx 2: necessary — α = Empty, β = Bool
theorem c2_146 : ¬ drop0% Function.nontrivial 2 := fun h => not_nontrivial (Empty → Bool) (@h Empty Bool _)
-- `Function.nontrivial` idx 3: necessary — α = β = Unit
theorem c2_147 : ¬ drop0% Function.nontrivial 3 := fun h => not_nontrivial (Unit → Unit) (@h Unit Unit _)
-- `Nontrivial.exists_pair_ne` idx 1: necessary — α = Unit
theorem c2_148 : ¬ drop0% Nontrivial.exists_pair_ne 1 := fun h => by
  obtain ⟨x, y, hxy⟩ := @h Unit
  exact hxy rfl
-- `exists_pair_ne` idx 1: necessary — α = Unit
theorem c2_149 : ¬ drop0% exists_pair_ne 1 := fun h => by
  obtain ⟨x, y, hxy⟩ := h Unit
  exact hxy rfl
-- `Function.Injective.nontrivial` idx 2: necessary — id on Unit
theorem c2_150 : ¬ drop0% Function.Injective.nontrivial 2 := fun h =>
  not_nontrivial Unit (@h Unit Unit id Function.injective_id)
-- `Function.Injective.nontrivial` idx 4: necessary — Bool → Unit
theorem c2_151 : ¬ drop0% Function.Injective.nontrivial 4 := fun h =>
  not_nontrivial Unit (@h Bool Unit ⟨⟨true, false, by decide⟩⟩ (fun _ => ()))
-- `Function.Injective.exists_ne` idx 2: necessary — id on Unit
theorem c2_152 : ¬ drop0% Function.Injective.exists_ne 2 := fun h => by
  obtain ⟨x, hx⟩ := @h Unit Unit id Function.injective_id ()
  exact hx rfl
-- `Decidable.exists_ne` idx 1: necessary — α = Unit
theorem c2_153 : ¬ drop0% Decidable.exists_ne 1 := fun h => by
  obtain ⟨y, hy⟩ := @h Unit _ ()
  exact hy rfl
-- `exists_ne` idx 1: necessary — α = Unit
theorem c2_154 : ¬ drop0% exists_ne 1 := fun h => by
  obtain ⟨y, hy⟩ := @h Unit ()
  exact hy rfl
-- `nontrivial_of_ne` idx 3: necessary — α = Unit
theorem c2_155 : ¬ drop0% nontrivial_of_ne 3 := fun h => not_nontrivial Unit (@h Unit () ())
-- `Function.nontrivial_of_nontrivial` idx 2: necessary — β = Unit
theorem c2_156 : ¬ drop0% Function.nontrivial_of_nontrivial 2 := fun h => not_nontrivial Unit (h Unit Unit)
-- `Nontrivial.to_nonempty` idx 1: necessary — α = Empty
theorem c2_157 : ¬ drop0% Nontrivial.to_nonempty 1 := fun h => by
  obtain ⟨x⟩ := @h Empty
  exact x.elim
-- `not_subsingleton` idx 1: necessary — α = Unit
theorem c2_158 : ¬ drop0% not_subsingleton 1 := fun h => h Unit inferInstance
-- `Function.Surjective.nontrivial` idx 2: necessary — id on Unit
theorem c2_159 : ¬ drop0% Function.Surjective.nontrivial 2 := fun h =>
  not_nontrivial Unit (@h Unit Unit id Function.surjective_id)
-- `Function.Surjective.nontrivial` idx 4: necessary — Unit → Bool
theorem c2_160 : ¬ drop0% Function.Surjective.nontrivial 4 := fun h =>
  not_nontrivial Unit (@h Unit Bool ⟨⟨true, false, by decide⟩⟩ (fun _ => true))
-- `NeZero.nontrivial` idx 3: necessary — α = Unit, a = 0
theorem c2_161 : ¬ drop0% NeZero.nontrivial 3 := fun h => not_nontrivial Unit (@h Unit _ 0)
-- `Opposite.instNonempty` idx 1: necessary — α = False
theorem c2_162 : ¬ drop0% Opposite.instNonempty 1 := fun h => by
  obtain ⟨x⟩ := @h False
  exact x.unop
-- `Opposite.instSubsingleton` idx 1: necessary — α = Bool (universe 1)
theorem c2_163 : ¬ drop1% Opposite.instSubsingleton 1 := fun h =>
  absurd (congrArg Opposite.unop ((@h Bool).elim (Opposite.op true) (Opposite.op false))) (by decide)
-- `Opposite.small` idx 1: necessary — X = Type is not small (universes u_1 = 1, u_2 = 0)
theorem c2_164 : ¬ ∀ {X : Type 1}, Small.{0, 1} (Opposite.{2} X) := fun h =>
  not_small_type.{0, 0} (@small_map.{0} _ _ (@h (Type 0)) Opposite.equivToOpposite)
-- `PEquiv.single_trans_of_mem` idx 10: necessary — f = ⊥ on Unit
theorem c2_165 : ¬ drop0% PEquiv.single_trans_of_mem 10 := fun h => by
  have := congrArg (fun g : Unit ≃. Unit => g ()) (@h Unit Unit Unit _ _ _ () () () ⊥)
  simp at this
-- `PEquiv.trans_single_of_mem` idx 10: necessary — f = ⊥ on Unit
theorem c2_166 : ¬ drop0% PEquiv.trans_single_of_mem 10 := fun h => by
  have := congrArg (fun g : Unit ≃. Unit => g ()) (@h Unit Unit Unit _ _ _ () () () ⊥)
  simp at this
-- `PEquiv.trans_single_of_eq_none` idx 8: necessary — f = refl on Unit
theorem c2_167 : ¬ drop0% PEquiv.trans_single_of_eq_none 8 := fun h => by
  have := congrArg (fun g : Unit ≃. Unit => g ()) (@h Unit Unit Unit _ _ () () (PEquiv.refl Unit))
  simp at this
-- `PEquiv.single_trans_of_eq_none` idx 8: necessary — f = refl on Unit
theorem c2_168 : ¬ drop0% PEquiv.single_trans_of_eq_none 8 := fun h => by
  have := congrArg (fun g : Unit ≃. Unit => g ()) (@h Unit Unit Unit _ _ () () (PEquiv.refl Unit))
  simp at this
-- `Real.ind_mk` idx 2: necessary — C = False
theorem c2_169 : ¬ drop0% Real.ind_mk 2 := fun h => @h (fun _ => False) 0
-- `Real.le_mk_of_forall_le` idx 2: necessary — x = mk 0 + 1
theorem c2_170 : ¬ drop0% Real.le_mk_of_forall_le 2 := fun h => by
  have := @h (Real.mk 0 + 1) 0
  linarith
-- `Real.mk_le_of_forall_le` idx 2: necessary — x = mk 0 - 1
theorem c2_171 : ¬ drop0% Real.mk_le_of_forall_le 2 := fun h => by
  have := @h 0 (Real.mk 0 - 1)
  linarith
-- `Real.mk_near_of_forall_near` idx 3: necessary — ε = -1
theorem c2_172 : ¬ drop0% Real.mk_near_of_forall_near 3 := fun h => by
  have := @h 0 0 (-1)
  linarith [abs_nonneg (Real.mk 0 - 0)]
-- `Real.mul_add_one_le_add_one_pow` idx 1: necessary — a = -4, b = 3
theorem c2_173 : ¬ drop0% Real.mul_add_one_le_add_one_pow 1 := fun h => by
  have := @h (-4) 3
  norm_num at this
-- `IsPowMul.map_one_le_one` idx 3: necessary — f = const 2
theorem c2_174 : ¬ drop0% IsPowMul.map_one_le_one 3 := fun h =>
  absurd (@h Unit _ (fun _ => 2)) (by norm_num)

namespace W1c2
/-- ℝ with the partial order whose only strict relation is 0 < 1 (all ℝ-module structure kept) -/
def RP := ℝ
instance : AddCommMonoid RP := inferInstanceAs (AddCommMonoid ℝ)
instance : Module ℝ RP := inferInstanceAs (Module ℝ ℝ)
def RPle (x y : ℝ) : Prop := x = y ∨ (x = 0 ∧ y = 1)
instance : PartialOrder RP where
  le x y := RPle x y
  le_refl x := Or.inl rfl
  le_trans x y z hxy hyz := by
    unfold RPle at *
    rcases hxy with rfl | ⟨rfl, rfl⟩ <;> rcases hyz with rfl | ⟨h1, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨h1, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · norm_num at h1
  le_antisymm x y hxy hyx := by
    unfold RPle at *
    rcases hxy with h | ⟨rfl, rfl⟩
    · exact h
    · rcases hyx with h | ⟨h, _⟩ <;> norm_num at h
theorem rp_lt01 : (0 : RP) < (1 : ℝ) := by
  refine lt_of_le_of_ne (Or.inr ⟨rfl, rfl⟩) ?_
  intro h; exact absurd (show (0:ℝ) = 1 from h) (by norm_num)
theorem rp_not_le (x y : RP) (hxy : @Ne ℝ x y) (hx : @Ne ℝ y 1) : ¬ x ≤ y := by
  intro h
  rcases (h : RPle x y) with h | ⟨_, h⟩
  · exact hxy h
  · exact hx h
/-- ℝ with the constant star 1 -/
def RS := ℝ
instance : AddCommMonoid RS := inferInstanceAs (AddCommMonoid ℝ)
instance : Module ℝ RS := inferInstanceAs (Module ℝ ℝ)
instance : Star RS := ⟨fun _ => (1 : ℝ)⟩
theorem unitsNN : Nontrivial NNRealˣ :=
  ⟨⟨1, Units.mk0 2 two_ne_zero, fun h => by
    have := congrArg Units.val h; norm_num at this⟩⟩
instance : IsOrderedMonoid Unit where
  mul_le_mul_left _ _ _ _ := le_rfl
abbrev WU := WithZero Unit
noncomputable def fWU : WU →*₀ NNReal := WithZero.lift' 1
theorem fWU_mono : StrictMono fWU := by
  intro a b hab
  induction a using WithZero.recZeroCoe <;> induction b using WithZero.recZeroCoe
  · exact absurd hab (lt_irrefl _)
  · simp [fWU]
  · exact absurd hab (not_lt.mpr bot_le)
  · exact absurd hab (by simp)
theorem fWU_units (d : WUˣ) : fWU d = 1 := by
  have hd : (d : WU) ≠ 0 := d.ne_zero
  induction h : (d : WU) using WithZero.recZeroCoe with
  | zero => exact absurd h hd
  | coe a => simp [fWU]
end W1c2

-- `NNReal.instPosSMulStrictMono` idx 3: necessary — ℝ with the partial order {0 < 1}: 2 • 0 < 2 • 1 fails
theorem c2_90 : ¬ drop0% NNReal.instPosSMulStrictMono 3 := fun h => by
  have := (@h RP _ _).smul_lt_smul_of_pos_left (show (0:NNReal) < 2 by norm_num) rp_lt01
  exact rp_not_le _ _ (by show ((2:NNReal):ℝ) * 0 ≠ (2:NNReal) * 1; norm_num)
    (by show ((2:NNReal):ℝ) * 1 ≠ 1; norm_num) this.le
-- `NNReal.instSMulPosStrictMono` idx 4: necessary — ℝ with the partial order {0 < 1}: 1 • 1 < 2 • 1 fails
theorem c2_91 : ¬ drop0% NNReal.instSMulPosStrictMono 4 := fun h => by
  have := (@h RP _ _ _).smul_lt_smul_of_pos_right rp_lt01 (show (1:NNReal) < 2 by norm_num)
  exact rp_not_le _ _ (by show ((1:NNReal):ℝ) * 1 ≠ (2:NNReal) * 1; norm_num)
    (by show ((2:NNReal):ℝ) * 1 ≠ 1; norm_num) this.le
-- `NNReal.instIsStrictOrderedModule` idx 4: necessary — ℝ with the partial order {0 < 1}: 2 • 0 < 2 • 1 fails
theorem c2_92 : ¬ drop0% NNReal.instIsStrictOrderedModule 4 := fun h => by
  have := (@h RP _ _ _).toPosSMulStrictMono.smul_lt_smul_of_pos_left (show (0:NNReal) < 2 by norm_num) rp_lt01
  exact rp_not_le _ _ (by show ((2:NNReal):ℝ) * 0 ≠ (2:NNReal) * 1; norm_num)
    (by show ((2:NNReal):ℝ) * 1 ≠ 1; norm_num) this.le
-- `instStarModuleNNRealOfReal` idx 4: necessary — ℝ with constant star 1: star (2 • 0) = 1 ≠ 2 = 2 • star 0
theorem c2_93 : ¬ drop0% instStarModuleNNRealOfReal 4 := fun h => by
  have := (@h RS _ _ _).star_smul (2 : NNReal) (0 : RS)
  have h2 : (1 : ℝ) = ((2:NNReal) : ℝ) * 1 := this
  norm_num at h2
-- `NNReal.exists_lt_of_strictMono` idx 2: necessary — Γ₀ = WithZero Unit (trivial units), f = 0 ↦ 0, 1 ↦ 1, r = 1/2
theorem c2_119 : ¬ drop0% NNReal.exists_lt_of_strictMono 2 := fun h => by
  obtain ⟨d, hd⟩ := @h WU _ fWU fWU_mono (1/2) (by norm_num)
  rw [fWU_units] at hd
  norm_num at hd
-- `NNReal.exists_lt_of_strictMono` idx 6: necessary — Γ₀ = NNReal, f = id, r = 0
theorem c2_120 : ¬ drop0% NNReal.exists_lt_of_strictMono 6 := fun h => by
  obtain ⟨d, hd⟩ := @h NNReal _ unitsNN (MonoidWithZeroHom.id NNReal) strictMono_id 0
  exact not_lt_zero hd
-- `Real.exists_lt_of_strictMono` idx 2: necessary — Γ₀ = WithZero Unit (trivial units), r = 1/2
theorem c2_121 : ¬ drop0% Real.exists_lt_of_strictMono 2 := fun h => by
  obtain ⟨d, hd⟩ := @h WU _ fWU fWU_mono (1/2) (by norm_num)
  rw [fWU_units] at hd
  norm_num at hd
-- `Real.exists_lt_of_strictMono` idx 6: necessary — Γ₀ = NNReal, f = id, r = 0
theorem c2_122 : ¬ drop0% Real.exists_lt_of_strictMono 6 := fun h => by
  obtain ⟨d, hd⟩ := @h NNReal _ unitsNN (MonoidWithZeroHom.id NNReal) strictMono_id 0
  exact absurd hd (not_lt.mpr (NNReal.coe_nonneg _))
