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

open scoped ENNReal NNReal

namespace W1c3

open SetRel

/-- a non-transitive relation on ℕ: 0 → 1 → 2 -/
def Rs : SetRel ℕ ℕ := {(0, 1), (1, 2)}
theorem Rs_nt : ¬ Rs.IsTrans := fun h =>
  absurd (SetRel.trans (R := Rs) (a := 0) (b := 1) (c := 2) (by simp [Rs]) (by simp [Rs])) (by simp [Rs])
/-- a non-symmetric (vacuously transitive) relation on Bool -/
def R1 : SetRel Bool Bool := {(false, true)}
theorem R1_ns : ¬ R1.IsSymm := fun h =>
  absurd (SetRel.symm (R := R1) (a := false) (b := true) (by simp [R1])) (by simp [R1])
instance R1_tr : R1.IsTrans := ⟨by intro a b c h1 h2; simp [R1] at h1 h2; simp_all⟩
/-- a symmetric non-transitive relation on Bool -/
def Rc : SetRel Bool Bool := {(false, true), (true, false)}
theorem Rc_nt : ¬ Rc.IsTrans := fun h =>
  absurd (SetRel.trans (R := Rc) (a := false) (b := true) (c := false) (by simp [Rc]) (by simp [Rc])) (by simp [Rc])
instance Rc_sy : Rc.IsSymm := ⟨by intro a b h; simp [Rc] at h ⊢; tauto⟩
/-- a reflexive non-transitive relation on ℕ -/
def Rr : SetRel ℕ ℕ := {p | p.1 = p.2 ∨ p.2 = p.1 + 1}
instance Rr_refl : Rr.IsRefl := ⟨fun a => by simp [Rr]⟩
theorem Rr_nt : ¬ Rr.IsTrans := fun h =>
  absurd (SetRel.trans (R := Rr) (a := 0) (b := 1) (c := 2) (by simp [Rr]) (by simp [Rr])) (by simp [Rr])
theorem empty_nrefl : ¬ (∅ : SetRel Unit Unit).IsRefl := fun h =>
  absurd (SetRel.refl (R := (∅ : SetRel Unit Unit)) ()) (by simp)

/-- the one-point relation on Bool -/
def Rt : SetRel Bool Bool := {(true, true)}

end W1c3

namespace W1c3

theorem bI (f : Bool → ℝ) : ⨅ i, f i = min (f true) (f false) :=
  le_antisymm (le_min (ciInf_le (Set.finite_range _).bddBelow true)
    (ciInf_le (Set.finite_range _).bddBelow false)) (le_ciInf fun i => by cases i <;> simp)
theorem bS (f : Bool → ℝ) : ⨆ i, f i = max (f true) (f false) :=
  le_antisymm (ciSup_le fun i => by cases i <;> simp)
    (max_le (le_ciSup (Set.finite_range _).bddAbove true) (le_ciSup (Set.finite_range _).bddAbove false))

/-- ℝ as a scalar field acting on ℝ through the swap 1 ↔ 2: a • x = ψ (a * ψ x), a non-monotone
`MulActionWithZero` (2 • 1 = 4, 2 • 2 = 1) -/
def RA := ℝ
noncomputable instance : Field RA := inferInstanceAs (Field ℝ)
noncomputable instance : LinearOrder RA := inferInstanceAs (LinearOrder ℝ)
instance : IsStrictOrderedRing RA := inferInstanceAs (IsStrictOrderedRing ℝ)
noncomputable def ψ : Equiv.Perm ℝ := Equiv.swap 1 2
theorem ψ0 : ψ 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by norm_num) (by norm_num)
theorem ψ1 : ψ 1 = 2 := Equiv.swap_apply_left _ _
theorem ψ2 : ψ 2 = 1 := Equiv.swap_apply_right _ _
theorem ψ4 : ψ 4 = 4 := Equiv.swap_apply_of_ne_of_ne (by norm_num) (by norm_num)
theorem ψψ (x : ℝ) : ψ (ψ x) = x := Equiv.swap_apply_self _ _ _
noncomputable instance actW : MulActionWithZero RA ℝ where
  smul a x := ψ ((show ℝ from a) * ψ x)
  one_smul x := by show ψ (1 * ψ x) = x; rw [one_mul, ψψ]
  mul_smul a b x := by
    show ψ (((show ℝ from a) * (show ℝ from b)) * ψ x) = ψ ((show ℝ from a) * ψ (ψ ((show ℝ from b) * ψ x)))
    rw [ψψ, mul_assoc]
  smul_zero a := by show ψ (_ * ψ 0) = 0; rw [ψ0, mul_zero, ψ0]
  zero_smul x := by show ψ (0 * ψ x) = 0; rw [zero_mul, ψ0]
theorem sA1 : (2 : RA) • (1 : ℝ) = 4 := by
  show ψ ((2 : ℝ) * ψ 1) = 4; rw [ψ1]; norm_num [ψ4]
theorem sA2 : (2 : RA) • (2 : ℝ) = 1 := by
  show ψ ((2 : ℝ) * ψ 2) = 1; rw [ψ2]; norm_num [ψ2]
theorem two_nn : (0 : RA) ≤ 2 := show (0 : ℝ) ≤ 2 by norm_num

end W1c3

namespace W1c3

/-- Fin 3 with its usual order is archimedean (but not an ordered monoid) -/
instance F3arch : Archimedean (Fin 3) :=
  ⟨fun x y hy => ⟨2 * y.val, by revert x y; decide⟩⟩
theorem F3_not_ord : ¬ IsOrderedAddMonoid (Fin 3) := fun h =>
  absurd (add_le_add_left (show (1 : Fin 3) ≤ 2 by decide) (1 : Fin 3)) (by decide)
theorem F3_three (m : ℕ) : ((3 * m : ℕ) : ℤ) • (1 : Fin 3) = 0 := by
  induction m with
  | zero => simp
  | succ k ih => rw [show 3 * (k + 1) = 3 * k + 3 by ring, Nat.cast_add, add_zsmul, ih]; decide

/-- ℤ with the reversed order and 1 = 1 (so 1 < 0): ordered archimedean group, not `ZeroLEOneClass` -/
def ZD := ℤᵒᵈ
instance : AddCommGroup ZD := inferInstanceAs (AddCommGroup ℤᵒᵈ)
instance : LinearOrder ZD := inferInstanceAs (LinearOrder ℤᵒᵈ)
instance : IsOrderedAddMonoid ZD := inferInstanceAs (IsOrderedAddMonoid ℤᵒᵈ)
instance : Archimedean ZD := inferInstanceAs (Archimedean ℤᵒᵈ)
instance : One ZD := ⟨(1 : ℤ)⟩
instance : NeZero (1 : ZD) := ⟨show (1 : ℤ) ≠ 0 by decide⟩
theorem ZD_le (a b : ZD) : a ≤ b ↔ (show ℤ from b) ≤ (show ℤ from a) := Iff.rfl
theorem ZD_lt (a b : ZD) : a < b ↔ (show ℤ from b) < (show ℤ from a) := Iff.rfl
theorem ZD_zsmul (n : ℤ) (a : ZD) : (show ℤ from n • a) = n * (show ℤ from a) := zsmul_eq_mul _ _
theorem ZD_nsmul (n : ℕ) (a : ZD) : (show ℤ from n • a) = n * (show ℤ from a) := nsmul_eq_mul _ _
theorem ZD_not : ¬ ZeroLEOneClass ZD := fun h => absurd h.zero_le_one (by decide)

/-- ℤ with 1 = 0: ordered archimedean group, `ZeroLEOneClass`, not `NeZero 1` -/
def Z0 := ℤ
instance : AddCommGroup Z0 := inferInstanceAs (AddCommGroup ℤ)
instance : LinearOrder Z0 := inferInstanceAs (LinearOrder ℤ)
instance : IsOrderedAddMonoid Z0 := inferInstanceAs (IsOrderedAddMonoid ℤ)
instance : Archimedean Z0 := inferInstanceAs (Archimedean ℤ)
instance : One Z0 := ⟨(0 : ℤ)⟩
instance : ZeroLEOneClass Z0 := ⟨show (0 : ℤ) ≤ 0 from le_rfl⟩
theorem Z0_zsmul (n : ℤ) (a : Z0) : (show ℤ from n • a) = n * (show ℤ from a) := zsmul_eq_mul _ _
theorem Z0_nsmul (n : ℕ) (a : Z0) : (show ℤ from n • a) = n * (show ℤ from a) := nsmul_eq_mul _ _

/-- lexicographic ℤ × ℤ with 1 = (0, 1): ordered, `ZeroLEOneClass`, `NeZero 1`, not archimedean -/
def NA := ℤ ×ₗ ℤ
instance : AddCommGroup NA := inferInstanceAs (AddCommGroup (ℤ ×ₗ ℤ))
instance : LinearOrder NA := inferInstanceAs (LinearOrder (ℤ ×ₗ ℤ))
def NA.mk (a b : ℤ) : NA := toLex (a, b)
theorem NA_le (a b c d : ℤ) : NA.mk a b ≤ NA.mk c d ↔ a < c ∨ a = c ∧ b ≤ d := Prod.Lex.toLex_le_toLex
theorem NA_lt (a b c d : ℤ) : NA.mk a b < NA.mk c d ↔ a < c ∨ a = c ∧ b < d := Prod.Lex.toLex_lt_toLex
theorem NA_eta (x : NA) : ∃ a b, x = NA.mk a b := ⟨(ofLex x).1, (ofLex x).2, rfl⟩
theorem NA_add (a b c d : ℤ) : NA.mk a b + NA.mk c d = NA.mk (a + c) (b + d) := rfl
theorem NA_zsmul (n a b : ℤ) : n • NA.mk a b = NA.mk (n * a) (n * b) := by
  show toLex (n • (a, b)) = _; simp [NA.mk]
theorem NA_nsmul (n : ℕ) (a b : ℤ) : n • NA.mk a b = NA.mk (n * a) (n * b) := by
  show toLex (n • (a, b)) = _; simp [NA.mk]
instance : IsOrderedAddMonoid NA where
  add_le_add_left x y h z := by
    obtain ⟨a, b, rfl⟩ := NA_eta x; obtain ⟨c, d, rfl⟩ := NA_eta y; obtain ⟨e, f, rfl⟩ := NA_eta z
    rw [NA_add, NA_add, NA_le] at *; omega
instance : One NA := ⟨NA.mk 0 1⟩
theorem NA_one : (1 : NA) = NA.mk 0 1 := rfl
theorem NA_zero : (0 : NA) = NA.mk 0 0 := rfl
instance : ZeroLEOneClass NA := ⟨by rw [NA_one, NA_zero, NA_le]; omega⟩
instance : NeZero (1 : NA) := ⟨fun h => by have := congrArg (fun x : NA => (ofLex x).2) h; simp [NA_one, NA_zero, NA.mk] at this⟩
theorem NA_not : ¬ Archimedean NA := fun h => by
  obtain ⟨n, hn⟩ := h.arch (NA.mk 1 0) (y := 1) (by rw [NA_one, NA_zero, NA_lt]; omega)
  rw [NA_one, NA_nsmul, NA_le] at hn; omega

end W1c3

namespace W1c3
open Archimedean

theorem unbQ {S : Set ℚ} (h : ∀ n : ℕ, ∃ r ∈ S, (n : ℚ) ≤ r) : ¬ BddAbove S := by
  rintro ⟨b, hb⟩; obtain ⟨n, hn⟩ := exists_nat_gt b; obtain ⟨r, hr, hnr⟩ := h n
  have := hb hr; linarith
theorem unbR {S : Set ℚ} (h : ∀ n : ℕ, ∃ r ∈ S, (n : ℚ) ≤ r) : ¬ BddAbove ((Rat.castHom ℝ) '' S) := by
  rintro ⟨b, hb⟩; obtain ⟨n, hn⟩ := exists_nat_gt b; obtain ⟨r, hr, hnr⟩ := h n
  have := hb ⟨r, hr, rfl⟩; have : ((n : ℚ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hnr
  simp only [Rat.cast_natCast] at this; simp only [eq_ratCast] at *; linarith
theorem F3_mem (x : Fin 3) (hx : x ≠ 0) (n : ℕ) : ((3 * n : ℕ) : ℚ) ∈ ratLt x := by
  show ((3 * n : ℕ) : ℚ).num • (1 : Fin 3) < ((3 * n : ℕ) : ℚ).den • x
  rw [Rat.num_natCast, Rat.den_natCast, F3_three, one_smul]; exact Fin.pos_iff_ne_zero.mpr hx
theorem F3_unb (x : Fin 3) (hx : x ≠ 0) : ∀ n : ℕ, ∃ r ∈ ratLt x, (n : ℚ) ≤ r :=
  fun n => ⟨_, F3_mem x hx n, by push_cast; linarith [(n.cast_nonneg : (0 : ℚ) ≤ n)]⟩
theorem F3_empty (r : ℚ) : r ∉ ratLt (0 : Fin 3) := by
  show ¬ r.num • (1 : Fin 3) < r.den • (0 : Fin 3); rw [smul_zero]; exact Fin.not_lt_zero _
theorem ZD_mem (x : ℤ) (n : ℕ) : ((n + x.natAbs + 1 : ℕ) : ℚ) ∈ ratLt (show ZD from x) := by
  show ((n + x.natAbs + 1 : ℕ) : ℚ).num • (1 : ZD) < ((n + x.natAbs + 1 : ℕ) : ℚ).den • (show ZD from x)
  rw [Rat.num_natCast, Rat.den_natCast, ZD_lt, ZD_zsmul, ZD_nsmul]
  show (1 : ℕ) * x < ((n + x.natAbs + 1 : ℕ) : ℤ) * 1; have h1 : x ≤ |x| := le_abs_self x; push_cast; omega
theorem ZD_unb (x : ℤ) : ∀ n : ℕ, ∃ r ∈ ratLt (show ZD from x), (n : ℚ) ≤ r :=
  fun n => ⟨_, ZD_mem x n, by push_cast; linarith [(x.natAbs.cast_nonneg : (0 : ℚ) ≤ x.natAbs)]⟩
theorem Z0_mem (x : ℤ) (hx : 0 < x) (r : ℚ) : r ∈ ratLt (show Z0 from x) := by
  show r.num • (1 : Z0) < r.den • (show Z0 from x)
  show (show ℤ from r.num • (1 : Z0)) < (show ℤ from r.den • (show Z0 from x))
  rw [Z0_zsmul, Z0_nsmul]; show r.num * 0 < (r.den : ℤ) * x; rw [mul_zero]; exact mul_pos (by exact_mod_cast r.den_pos) hx
theorem Z0_unb (x : ℤ) (hx : 0 < x) : ∀ n : ℕ, ∃ r ∈ ratLt (show Z0 from x), (n : ℚ) ≤ r :=
  fun n => ⟨n, Z0_mem x hx n, le_rfl⟩
theorem Z0_empty (r : ℚ) : r ∉ ratLt (0 : Z0) := by
  show ¬ r.num • (1 : Z0) < r.den • (0 : Z0); rw [smul_zero]
  show ¬ (show ℤ from r.num • (1 : Z0)) < 0; rw [Z0_zsmul]; show ¬ r.num * 0 < 0; simp
theorem NA_mem (a b : ℤ) (ha : 0 < a) (r : ℚ) : r ∈ ratLt (NA.mk a b) := by
  show r.num • (1 : NA) < r.den • NA.mk a b
  rw [NA_one, NA_zsmul, NA_nsmul, NA_lt]; left; have := r.den_pos; simp only [mul_zero]; positivity
theorem NA_unb (a b : ℤ) (ha : 0 < a) : ∀ n : ℕ, ∃ r ∈ ratLt (NA.mk a b), (n : ℚ) ≤ r :=
  fun n => ⟨n, NA_mem a b ha n, le_rfl⟩
theorem NA_empty (r : ℚ) : r ∉ ratLt (NA.mk (-1) 0) := by
  show ¬ r.num • (1 : NA) < r.den • NA.mk (-1) 0
  rw [NA_one, NA_zsmul, NA_nsmul, NA_lt]; have := r.den_pos; omega

theorem NA_m1 : (-1 : ℚ) ∈ ratLt (NA.mk 1 0 + NA.mk (-1) 0) := by
  rw [NA_add]; show (-1 : ℚ).num • (1 : NA) < (-1 : ℚ).den • NA.mk (1 + -1) (0 + 0)
  rw [NA_one, NA_zsmul, NA_nsmul, NA_lt]; norm_num

end W1c3

namespace W1c3
open Archimedean

theorem NA_empty2 (r : ℚ) : r ∉ ratLt (NA.mk (-1) 1) := by
  show ¬ r.num • (1 : NA) < r.den • NA.mk (-1) 1
  rw [NA_one, NA_zsmul, NA_nsmul, NA_lt]; have := r.den_pos; omega
theorem NA_f1 : embedRealFun (NA.mk (-1) 1) = 0 := by
  have : ratLt (NA.mk (-1) 1) = ∅ := Set.eq_empty_of_forall_notMem NA_empty2
  show sSup ((Rat.castHom ℝ) '' ratLt (NA.mk (-1) 1)) = 0
  rw [this, Set.image_empty, Real.sSup_empty]
theorem NA_f2 : (1 / 2 : ℝ) ≤ embedRealFun (NA.mk 0 1) := by
  have hmem : ∀ r : ℚ, r ∈ ratLt (NA.mk 0 1) ↔ r.num < r.den := by
    intro r; show r.num • (1 : NA) < r.den • NA.mk 0 1 ↔ _
    rw [NA_one, NA_zsmul, NA_nsmul, NA_lt]; simp
  have hb : BddAbove ((Rat.castHom ℝ) '' ratLt (NA.mk 0 1)) := by
    refine ⟨1, ?_⟩; rintro _ ⟨r, hr, rfl⟩
    rw [hmem] at hr
    have h1 : r < 1 := by
      rw [← Rat.num_div_den r, div_lt_one (by exact_mod_cast r.den_pos)]; exact_mod_cast hr
    simp only [eq_ratCast]; exact_mod_cast h1.le
  have h2 : (1 / 2 : ℚ) ∈ ratLt (NA.mk 0 1) := by rw [hmem]; decide +kernel
  have := le_csSup hb ⟨1 / 2, h2, rfl⟩
  rw [show ((Rat.castHom ℝ) (1 / 2 : ℚ)) = (1 / 2 : ℝ) by simp] at this; exact this

end W1c3

namespace W1c3
open Archimedean

universe u

/-- with 1 < 0 in an archimedean ordered group, every `ratLt x` contains all large naturals -/
theorem neg_one_unb {M : Type u} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [One M]
    [Archimedean M] (h1 : (1 : M) < 0) (x : M) (n : ℕ) : ((n + 1 + Classical.choose
      (Archimedean.arch (-x) (neg_pos.mpr h1)) : ℕ) : ℚ) ∈ ratLt x := by
  have hk := Classical.choose_spec (Archimedean.arch (-x) (neg_pos.mpr h1))
  set k := Classical.choose (Archimedean.arch (-x) (neg_pos.mpr h1))
  show ((n + 1 + k : ℕ) : ℚ).num • (1 : M) < ((n + 1 + k : ℕ) : ℚ).den • x
  rw [Rat.num_natCast, Rat.den_natCast, natCast_zsmul, one_smul]
  have hp : 0 < (n + 1) • (-1 : M) := nsmul_pos (neg_pos.mpr h1) (Nat.succ_ne_zero n)
  have e : (n + 1 + k) • (-1 : M) = (n + 1) • (-1 : M) + k • (-1 : M) := add_nsmul _ _ _
  simp only [smul_neg] at e hp hk
  rw [← neg_lt_neg_iff, e]
  calc -x ≤ -(k • (1 : M)) := hk
    _ < -((n + 1) • (1 : M)) + -(k • (1 : M)) := lt_add_of_pos_left _ hp

theorem neg_one_unb' {M : Type u} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [One M]
    [Archimedean M] (h1 : (1 : M) < 0) (x : M) : ∀ n : ℕ, ∃ r ∈ ratLt x, (n : ℚ) ≤ r :=
  fun n => ⟨_, neg_one_unb h1 x n, by push_cast; linarith [(Nat.cast_nonneg _ : (0 : ℚ) ≤ (Classical.choose
      (Archimedean.arch (-x) (neg_pos.mpr h1)) : ℕ))]⟩

theorem unbR' {S : Set ℚ} (h : ∀ n : ℕ, ∃ r ∈ S, (n : ℚ) ≤ r) : ¬ BddAbove ((Rat.castHom ℝ) '' S) := by
  rintro ⟨b, hb⟩; obtain ⟨n, hn⟩ := exists_nat_gt b; obtain ⟨r, hr, hnr⟩ := h n
  have := hb ⟨r, hr, rfl⟩; have : ((n : ℚ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hnr
  simp only [Rat.cast_natCast] at this; simp only [eq_ratCast] at *; linarith

theorem neg_one_zero {M : Type u} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [One M]
    [Archimedean M] (h1 : (1 : M) < 0) (x : M) : embedRealFun x = 0 :=
  Real.sSup_of_not_bddAbove (unbR' (neg_one_unb' h1 x))

/-- with 1 = 0 every `ratLt x` is empty or everything -/
theorem one_zero_fun {M : Type u} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [One M]
    (h1 : (1 : M) = 0) (x : M) : embedRealFun x = 0 := by
  rcases le_or_gt x 0 with hx | hx
  · have : ratLt x = ∅ := by
      ext r; simp only [Set.mem_empty_iff_false, iff_false]
      show ¬ r.num • (1 : M) < r.den • x
      rw [h1, smul_zero, not_lt]; exact nsmul_nonpos hx _
    show sSup ((Rat.castHom ℝ) '' ratLt x) = 0
    rw [this, Set.image_empty, Real.sSup_empty]
  · refine Real.sSup_of_not_bddAbove (unbR' fun n => ⟨n, ?_, le_rfl⟩)
    show (n : ℚ).num • (1 : M) < (n : ℚ).den • x
    rw [h1, smul_zero, Rat.den_natCast, one_smul]; exact hx

end W1c3

namespace W1c3
open scoped Pointwise

universe v

/-- a monotone scalar a ≠ 0 acts on ℝ as an order isomorphism -/
noncomputable def smulIso {α : Type v} [Field α] [LinearOrder α] [MulActionWithZero α ℝ] [PosSMulMono α ℝ]
    {a : α} (ha : 0 ≤ a) (a0 : a ≠ 0) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (fun x : ℝ => a • x)
    (Monotone.strictMono_of_injective (fun x y hxy => smul_le_smul_of_nonneg_left hxy ha)
      (fun x y hxy => by
        have := congrArg (a⁻¹ • ·) hxy; simpa [smul_smul, inv_mul_cancel₀ a0] using this))
    (fun y => ⟨a⁻¹ • y, by simp [smul_smul, mul_inv_cancel₀ a0]⟩)

theorem sInf_smul_nn {α : Type v} [Field α] [LinearOrder α] [MulActionWithZero α ℝ] [PosSMulMono α ℝ]
    {a : α} (ha : 0 ≤ a) (s : Set ℝ) : sInf (a • s) = a • sInf s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [Set.smul_set_empty, Real.sInf_empty, smul_zero]
  by_cases a0 : a = 0
  · subst a0; rw [Set.zero_smul_set hs, zero_smul]; exact csInf_singleton 0
  have hE : a • s = smulIso ha a0 '' s := (Set.image_smul).symm
  rw [hE]
  by_cases hb : BddBelow s
  · exact ((smulIso ha a0).map_csInf' hs hb).symm
  · rw [Real.sInf_of_not_bddBelow (by rwa [OrderIso.bddBelow_image]), Real.sInf_of_not_bddBelow hb, smul_zero]

theorem sSup_smul_nn {α : Type v} [Field α] [LinearOrder α] [MulActionWithZero α ℝ] [PosSMulMono α ℝ]
    {a : α} (ha : 0 ≤ a) (s : Set ℝ) : sSup (a • s) = a • sSup s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [Set.smul_set_empty, Real.sSup_empty, smul_zero]
  by_cases a0 : a = 0
  · subst a0; rw [Set.zero_smul_set hs, zero_smul]; exact csSup_singleton 0
  have hE : a • s = smulIso ha a0 '' s := (Set.image_smul).symm
  rw [hE]
  by_cases hb : BddAbove s
  · exact ((smulIso ha a0).map_csSup' hs hb).symm
  · rw [Real.sSup_of_not_bddAbove (by rwa [OrderIso.bddAbove_image]), Real.sSup_of_not_bddAbove hb, smul_zero]

/-- for a module, `IsOrderedModule` alone makes nonpositive scalars have nonnegative negatives -/
theorem neg_nonneg_of_mod {α : Type v} [Field α] [LinearOrder α] [Module α ℝ] [IsOrderedModule α ℝ]
    {a : α} (ha : a ≤ 0) : 0 ≤ -a := by
  by_contra hlt; push_neg at hlt
  have h1 : a • (1 : ℝ) ≤ 0 := by simpa using smul_le_smul_of_nonneg_right ha (zero_le_one : (0 : ℝ) ≤ 1)
  have h2 : 0 ≤ a • (1 : ℝ) := by simpa using smul_le_smul_of_nonneg_right hlt.le (zero_le_one : (0 : ℝ) ≤ 1)
  have h3 : a • (1 : ℝ) = 0 := le_antisymm h1 h2
  have a0 : a ≠ 0 := by rintro rfl; simp at hlt
  have := congrArg (a⁻¹ • ·) h3; simp [smul_smul, inv_mul_cancel₀ a0] at this

end W1c3

namespace W1c3
open scoped Pointwise

theorem negS {α : Type v} [Field α] [Module α ℝ] (a : α) (s : Set ℝ) : (-a) • s = -(a • s) := by
  ext x; simp only [Set.mem_neg, Set.mem_smul_set]; constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, by rw [neg_smul, neg_neg]⟩
  · rintro ⟨y, hy, h⟩; exact ⟨y, hy, by rw [neg_smul, h, neg_neg]⟩
theorem smulN {α : Type v} [Field α] [Module α ℝ] (a : α) (s : Set ℝ) : a • (-s) = -(a • s) := by
  ext x; simp only [Set.mem_neg, Set.mem_smul_set]; constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨-y, hy, by rw [smul_neg]⟩
  · rintro ⟨y, hy, h⟩; exact ⟨-y, by rwa [neg_neg], by rw [smul_neg, h, neg_neg]⟩

theorem sInf_smul_np {α : Type v} [Field α] [LinearOrder α] [Module α ℝ] [IsOrderedModule α ℝ]
    {a : α} (ha : a ≤ 0) (s : Set ℝ) : sInf (a • s) = a • sSup s := by
  have hn := neg_nonneg_of_mod ha
  rw [Real.sInf_def, ← negS, sSup_smul_nn hn, neg_smul, neg_neg]

theorem sSup_smul_np {α : Type v} [Field α] [LinearOrder α] [Module α ℝ] [IsOrderedModule α ℝ]
    {a : α} (ha : a ≤ 0) (s : Set ℝ) : sSup (a • s) = a • sInf s := by
  have hn := neg_nonneg_of_mod ha
  rw [Real.sInf_def s, smul_neg, ← neg_smul, ← sSup_smul_nn hn, smulN, negS, neg_neg]

end W1c3

namespace W1c3
open Archimedean

/-- ℤ ordered through φ (φ n = n except φ 2 = -1/2): archimedean, 0 ≤ 1, not an ordered monoid -/
def φz (n : ℤ) : ℚ := if n = 2 then -1 / 2 else n
theorem φz_inj : Function.Injective φz := by
  intro a b h; unfold φz at h
  by_cases ha : a = 2 <;> by_cases hb : b = 2 <;> simp only [ha, hb, if_true, if_false] at h
  · rw [ha, hb]
  · exfalso; have : (2 * b : ℚ) = -1 := by linarith
    have : 2 * b = -1 := by exact_mod_cast this
    omega
  · exfalso; have : (2 * a : ℚ) = -1 := by linarith
    have : 2 * a = -1 := by exact_mod_cast this
    omega
  · exact_mod_cast h
def WZ := ℤ
instance : AddCommGroup WZ := inferInstanceAs (AddCommGroup ℤ)
instance : LinearOrder WZ := LinearOrder.lift' (fun x : WZ => φz (show ℤ from x)) φz_inj
instance : One WZ := ⟨(1 : ℤ)⟩
theorem WZ_le (a b : WZ) : a ≤ b ↔ φz (show ℤ from a) ≤ φz (show ℤ from b) := Iff.rfl
theorem WZ_lt (a b : WZ) : a < b ↔ φz (show ℤ from a) < φz (show ℤ from b) := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, WZ_le, WZ_le]
theorem WZ_zsmul (n : ℤ) (a : WZ) : (show ℤ from n • a) = n * (show ℤ from a) := zsmul_eq_mul _ _
theorem WZ_nsmul (n : ℕ) (a : WZ) : (show ℤ from n • a) = n * (show ℤ from a) := nsmul_eq_mul _ _
instance : ZeroLEOneClass WZ := ⟨by rw [WZ_le]; show φz 0 ≤ φz 1; norm_num [φz]⟩
instance : NeZero (1 : WZ) := ⟨show (1 : ℤ) ≠ 0 by decide⟩
theorem φz_le_abs (x : ℤ) : φz x ≤ |x| := by
  unfold φz; split_ifs with h
  · subst h; norm_num
  · exact_mod_cast le_abs_self x
theorem arch_aux (x y : ℤ) (hy : φz 0 < φz y) : φz x ≤ φz (((x.natAbs + 3 : ℕ) : ℤ) * y) := by
  have hy1 : 1 ≤ y := by
    by_cases h2 : y = 2
    · omega
    · have : (0 : ℚ) < y := by simpa [φz, h2] using hy
      have : 0 < y := by exact_mod_cast this
      omega
  have hx := φz_le_abs x
  have ha : |x| = (x.natAbs : ℤ) := Int.abs_eq_natAbs x
  have hm : ((x.natAbs : ℤ) + 3) ≤ ((x.natAbs + 3 : ℕ) : ℤ) * y := by push_cast; nlinarith
  have e : φz (((x.natAbs + 3 : ℕ) : ℤ) * y) = ((((x.natAbs + 3 : ℕ) : ℤ) * y : ℤ) : ℚ) := by
    unfold φz; rw [if_neg (by omega)]
  rw [e]
  have : (|x| : ℤ) ≤ ((x.natAbs + 3 : ℕ) : ℤ) * y := by rw [ha]; omega
  have : ((|x| : ℤ) : ℚ) ≤ ((((x.natAbs + 3 : ℕ) : ℤ) * y : ℤ) : ℚ) := by exact_mod_cast this
  push_cast at hx this ⊢; linarith
instance : Archimedean WZ := ⟨fun x y hy => ⟨(show ℤ from x).natAbs + 3, by
  rw [WZ_le, WZ_nsmul]; exact arch_aux x y hy⟩⟩
/-- in WZ, 2 < 0, so 2 ∈ ratLt 0 and embedRealFun 0 ≥ 2 -/
theorem WZ_f0 : (2 : ℝ) ≤ embedRealFun (0 : WZ) := by
  have hmem : ∀ r : ℚ, r ∈ ratLt (0 : WZ) ↔ φz r.num < 0 := by
    intro r; show r.num • (1 : WZ) < r.den • (0 : WZ) ↔ _
    rw [smul_zero, WZ_lt, WZ_zsmul]; show φz (r.num * 1) < φz 0 ↔ _; simp [φz]
  have hb : BddAbove ((Rat.castHom ℝ) '' ratLt (0 : WZ)) := by
    refine ⟨2, ?_⟩; rintro _ ⟨r, hr, rfl⟩
    rw [hmem] at hr; unfold φz at hr
    have h2 : r ≤ 2 := by
      split_ifs at hr with h
      · have e : (r.num : ℚ) / r.den = r := Rat.num_div_den r
        rw [h] at e; rw [← e, div_le_iff₀ (by exact_mod_cast r.den_pos)]
        have : (1 : ℚ) ≤ r.den := by exact_mod_cast r.den_pos
        push_cast; linarith
      · have : r.num < 0 := by exact_mod_cast hr
        have : r < 0 := Rat.num_neg.mp this
        linarith
    simp only [eq_ratCast]; exact_mod_cast h2
  have h2 : (2 : ℚ) ∈ ratLt (0 : WZ) := by rw [hmem]; norm_num [φz]
  have := le_csSup hb ⟨2, h2, rfl⟩
  rw [show ((Rat.castHom ℝ) (2 : ℚ)) = (2 : ℝ) by simp] at this; exact this

end W1c3

namespace W1c3
open Archimedean
open scoped Pointwise

/-- the unit -1 (not an instance) -/
def negOneI (M : Type u) [AddCommGroup M] [One M] : One M := ⟨-(1 : M)⟩

theorem negSetAdd (A B : Set ℚ) : -(A + B) = -A + -B := by
  ext r; simp only [Set.mem_neg, Set.mem_add]; constructor
  · rintro ⟨a, ha, b, hb, h⟩; exact ⟨-a, by simpa using ha, -b, by simpa using hb, by linarith⟩
  · rintro ⟨a, ha, b, hb, h⟩; exact ⟨-a, ha, -b, hb, by linarith⟩

/-- with 1 < 0, ratLt for the unit 1 is the negative of ratLt for the unit -1 (which is ≥ 0) -/
theorem ratLt_add_neg {M : Type u} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [i1 : One M]
    [Archimedean M] (h1 : (1 : M) < 0) (x y : M) : ratLt (x + y) = ratLt x + ratLt y := by
  have hz : @ZeroLEOneClass M _ (negOneI M) _ :=
    @ZeroLEOneClass.mk M _ (negOneI M) _ (show (0 : M) ≤ -(1 : M) from (neg_pos.mpr h1).le)
  have hn : @NeZero M _ (@One.one M (negOneI M)) := ⟨show -(1 : M) ≠ 0 from (neg_pos.mpr h1).ne'⟩
  have key : ∀ z : M, @ratLt M _ _ i1 z = -(@ratLt M _ _ (negOneI M) z) := by
    intro z; ext r
    show r.num • (1 : M) < r.den • z ↔ (-r).num • (-(1 : M)) < (-r).den • z
    rw [Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, neg_smul, smul_neg, neg_neg]
  rw [key, key, key, @Archimedean.ratLt_add M _ _ _ (negOneI M) hz hn _ x y, negSetAdd]

theorem ratLt'_add_neg {M : Type u} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [One M]
    [Archimedean M] (h1 : (1 : M) < 0) (x y : M) : ratLt' (x + y) = ratLt' x + ratLt' y := by
  rw [ratLt', ratLt_add_neg h1, Set.image_add]

end W1c3

-- `Real.HolderTriple.of_pos` idx 2: necessary (p=0,q=1)
theorem c3_1 : ¬ drop0% Real.HolderTriple.of_pos 2 := fun h => by
  have := @h 0 1 one_pos
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderTriple.of_pos` idx 3: necessary (p=1,q=0)
theorem c3_2 : ¬ drop0% Real.HolderTriple.of_pos 3 := fun h => by
  have := @h 1 0 one_pos
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderTriple.holderConjugate_div_div` idx 3: necessary (p=q=r=0)
theorem c3_3 : ¬ drop0% Real.HolderTriple.holderConjugate_div_div 3 := fun h => by
  have := @h 0 0 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderConjugate.conjExponent_eq` idx 2: necessary (p=0,q=1)
theorem c3_4 : ¬ drop0% Real.HolderConjugate.conjExponent_eq 2 := fun h => by
  have := @h 0 1
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderConjugate.inv_inv` idx 2: necessary (a=0,b=1)
theorem c3_5 : ¬ drop0% Real.HolderConjugate.inv_inv 2 := fun h => by
  have := @h 0 1 (by norm_num) (by norm_num)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderConjugate.inv_inv` idx 3: necessary (a=1,b=0)
theorem c3_6 : ¬ drop0% Real.HolderConjugate.inv_inv 3 := fun h => by
  have := @h 1 0 (by norm_num) (by norm_num)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderConjugate.inv_inv` idx 4: necessary (a=b=1)
theorem c3_7 : ¬ drop0% Real.HolderConjugate.inv_inv 4 := fun h => by
  have := @h 1 1 one_pos one_pos
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderConjugate.inv_one_sub_inv` idx 1: necessary (a=0)
theorem c3_8 : ¬ drop0% Real.HolderConjugate.inv_one_sub_inv 1 := fun h => by
  have := @h 0 (by norm_num)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderConjugate.inv_one_sub_inv` idx 2: necessary (a=1)
theorem c3_9 : ¬ drop0% Real.HolderConjugate.inv_one_sub_inv 2 := fun h => by
  have := @h 1 one_pos
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderConjugate.one_sub_inv_inv` idx 1: necessary (a=0)
theorem c3_10 : ¬ drop0% Real.HolderConjugate.one_sub_inv_inv 1 := fun h => by
  have := @h 0 (by norm_num)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderConjugate.one_sub_inv_inv` idx 2: necessary (a=1)
theorem c3_11 : ¬ drop0% Real.HolderConjugate.one_sub_inv_inv 2 := fun h => by
  have := @h 1 one_pos
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.holderConjugate_iff_eq_conjExponent` idx 2: necessary (p=q=0)
theorem c3_12 : ¬ drop0% Real.holderConjugate_iff_eq_conjExponent 2 := fun h => by
  have := @h 0 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderConjugate.conjExponent` idx 1: necessary (p=0)
theorem c3_13 : ¬ drop0% Real.HolderConjugate.conjExponent 1 := fun h => by
  have := @h 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.holderConjugate_one_div` idx 2: necessary (a=0,b=1)
theorem c3_14 : ¬ drop0% Real.holderConjugate_one_div 2 := fun h => by
  have := @h 0 1 (by norm_num) (by norm_num)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.holderConjugate_one_div` idx 3: necessary (a=1,b=0)
theorem c3_15 : ¬ drop0% Real.holderConjugate_one_div 3 := fun h => by
  have := @h 1 0 (by norm_num) (by norm_num)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.holderConjugate_one_div` idx 4: necessary (a=b=1)
theorem c3_16 : ¬ drop0% Real.holderConjugate_one_div 4 := fun h => by
  have := @h 1 1 one_pos one_pos
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.HolderTriple.of_pos` idx 2: necessary (p=0,q=1)
theorem c3_17 : ¬ drop0% NNReal.HolderTriple.of_pos 2 := fun h => by
  have := @h 0 1 one_pos
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.HolderTriple.of_pos` idx 3: necessary (p=1,q=0)
theorem c3_18 : ¬ drop0% NNReal.HolderTriple.of_pos 3 := fun h => by
  have := @h 1 0 one_pos
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.HolderTriple.holderConjugate_div_div` idx 3: necessary (p=q=r=0)
theorem c3_19 : ¬ drop0% NNReal.HolderTriple.holderConjugate_div_div 3 := fun h => by
  have := @h 0 0 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.HolderConjugate.conjExponent_eq` idx 2: necessary (p=0,q=1)
theorem c3_20 : ¬ drop0% NNReal.HolderConjugate.conjExponent_eq 2 := fun h => by
  have := @h 0 1
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.HolderConjugate.inv_inv` idx 2: necessary (a=0,b=1)
theorem c3_21 : ¬ drop0% NNReal.HolderConjugate.inv_inv 2 := fun h => by
  have := @h 0 1 (by norm_num) (by norm_num)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.HolderConjugate.inv_inv` idx 3: necessary (a=1,b=0)
theorem c3_22 : ¬ drop0% NNReal.HolderConjugate.inv_inv 3 := fun h => by
  have := @h 1 0 (by norm_num) (by norm_num)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.HolderConjugate.inv_inv` idx 4: necessary (a=b=1)
theorem c3_23 : ¬ drop0% NNReal.HolderConjugate.inv_inv 4 := fun h => by
  have := @h 1 1 one_pos one_pos
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.HolderConjugate.inv_one_sub_inv` idx 1: necessary (a=0)
theorem c3_24 : ¬ drop0% NNReal.HolderConjugate.inv_one_sub_inv 1 := fun h => by
  have := @h 0 (by norm_num)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.HolderConjugate.inv_one_sub_inv` idx 2: necessary (a=1)
theorem c3_25 : ¬ drop0% NNReal.HolderConjugate.inv_one_sub_inv 2 := fun h => by
  have := @h 1 one_pos
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.HolderConjugate.one_sub_inv_inv` idx 1: necessary (a=0)
theorem c3_26 : ¬ drop0% NNReal.HolderConjugate.one_sub_inv_inv 1 := fun h => by
  have := @h 0 (by norm_num)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.HolderConjugate.one_sub_inv_inv` idx 2: necessary (a=1)
theorem c3_27 : ¬ drop0% NNReal.HolderConjugate.one_sub_inv_inv 2 := fun h => by
  have := @h 1 one_pos
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.holderConjugate_iff_eq_conjExponent` idx 2: necessary (p=q=0)
theorem c3_28 : ¬ drop0% NNReal.holderConjugate_iff_eq_conjExponent 2 := fun h => by
  have := @h 0 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.HolderConjugate.conjExponent` idx 1: necessary (p=0)
theorem c3_29 : ¬ drop0% NNReal.HolderConjugate.conjExponent 1 := fun h => by
  have := @h 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.holderConjugate_one_div` idx 2: necessary (a=0,b=1)
theorem c3_30 : ¬ drop0% NNReal.holderConjugate_one_div 2 := fun h => by
  have := @h 0 1 (by norm_num) (by norm_num)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.holderConjugate_one_div` idx 3: necessary (a=1,b=0)
theorem c3_31 : ¬ drop0% NNReal.holderConjugate_one_div 3 := fun h => by
  have := @h 1 0 (by norm_num) (by norm_num)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.holderConjugate_one_div` idx 4: necessary (a=b=1)
theorem c3_32 : ¬ drop0% NNReal.holderConjugate_one_div 4 := fun h => by
  have := @h 1 1 one_pos one_pos
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderTriple.toNNReal` idx 3: necessary (p=q=r=0)
theorem c3_33 : ¬ drop0% Real.HolderTriple.toNNReal 3 := fun h => by
  have := @h 0 0 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderConjugate.toNNReal` idx 2: necessary (p=q=0)
theorem c3_34 : ¬ drop0% Real.HolderConjugate.toNNReal 2 := fun h => by
  have := @h 0 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.coe_conjExponent` idx 1: necessary (p=1: 0 vs top)
theorem c3_35 : ¬ drop0% ENNReal.coe_conjExponent 1 := fun h => by
  have := @h 1
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.holderTriple_coe_iff` idx 3: necessary (p=q=r=0)
theorem c3_36 : ¬ drop0% ENNReal.holderTriple_coe_iff 3 := fun h => by
  have := @h 0 0 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.HolderTriple.coe_ennreal` idx 3: removable (the Hoelder triple forces r ≠ 0)
theorem c3_37 : drop% NNReal.HolderTriple.coe_ennreal 3 := fun h =>
  (ENNReal.holderTriple_coe_iff h.ne_zero').mpr h

-- `NNReal.HolderTriple.coe_ennreal` idx 4: necessary (p=q=0,r=1)
theorem c3_38 : ¬ drop0% NNReal.HolderTriple.coe_ennreal 4 := fun h => by
  have := @h 0 0 1 one_ne_zero
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `NNReal.HolderConjugate.coe_ennreal` idx 2: necessary (p=q=0)
theorem c3_39 : ¬ drop0% NNReal.HolderConjugate.coe_ennreal 2 := fun h => by
  have := @h 0 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderTriple.ennrealOfReal` idx 3: necessary (p=q=0,r=1)
theorem c3_40 : ¬ drop0% Real.HolderTriple.ennrealOfReal 3 := fun h => by
  have := @h 0 0 1
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `Real.HolderConjugate.ennrealOfReal` idx 2: necessary (p=q=0)
theorem c3_41 : ¬ drop0% Real.HolderConjugate.ennrealOfReal 2 := fun h => by
  have := @h 0 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderTriple.of_toReal` idx 3: necessary (p=q=0,r=1)
theorem c3_42 : ¬ drop0% ENNReal.HolderTriple.of_toReal 3 := fun h => by
  have := @h 0 0 1
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderTriple.toReal_iff` idx 3: necessary (p=0,q=1,r=0)
theorem c3_43 : ¬ drop0% ENNReal.HolderTriple.toReal_iff 3 := fun h => by
  have := @h 0 1 0 (by simp)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderTriple.toReal_iff` idx 4: necessary (p=1,q=0,r=0)
theorem c3_44 : ¬ drop0% ENNReal.HolderTriple.toReal_iff 4 := fun h => by
  have := @h 1 0 0 (by simp)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderTriple.toReal` idx 3: necessary (p=0,q=1,r=0)
theorem c3_45 : ¬ drop0% ENNReal.HolderTriple.toReal 3 := fun h => by
  have := @h 0 1 0 (by simp) ⟨by simp⟩
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderTriple.toReal` idx 4: necessary (p=1,q=0,r=0)
theorem c3_46 : ¬ drop0% ENNReal.HolderTriple.toReal 4 := fun h => by
  have := @h 1 0 0 (by simp) ⟨by simp⟩
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderTriple.toReal` idx 5: necessary (p=q=r=1)
theorem c3_47 : ¬ drop0% ENNReal.HolderTriple.toReal 5 := fun h => by
  have := @h 1 1 1 (by simp) (by simp)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderTriple.of_toNNReal` idx 3: necessary (p=q=0,r=1)
theorem c3_48 : ¬ drop0% ENNReal.HolderTriple.of_toNNReal 3 := fun h => by
  have := @h 0 0 1
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderTriple.toNNReal_iff` idx 3: necessary (p=0,q=1,r=0)
theorem c3_49 : ¬ drop0% ENNReal.HolderTriple.toNNReal_iff 3 := fun h => by
  have := @h 0 1 0 (by simp)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderTriple.toNNReal_iff` idx 4: necessary (p=1,q=0,r=0)
theorem c3_50 : ¬ drop0% ENNReal.HolderTriple.toNNReal_iff 4 := fun h => by
  have := @h 1 0 0 (by simp)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderTriple.toNNReal` idx 3: necessary (p=0,q=1,r=0)
theorem c3_51 : ¬ drop0% ENNReal.HolderTriple.toNNReal 3 := fun h => by
  have := @h 0 1 0 (by simp) ⟨by simp⟩
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderTriple.toNNReal` idx 4: necessary (p=1,q=0,r=0)
theorem c3_52 : ¬ drop0% ENNReal.HolderTriple.toNNReal 4 := fun h => by
  have := @h 1 0 0 (by simp) ⟨by simp⟩
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderTriple.toNNReal` idx 5: necessary (p=q=r=1)
theorem c3_53 : ¬ drop0% ENNReal.HolderTriple.toNNReal 5 := fun h => by
  have := @h 1 1 1 (by simp) (by simp)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.of_toReal` idx 2: necessary (p=q=0)
theorem c3_54 : ¬ drop0% ENNReal.HolderConjugate.of_toReal 2 := fun h => by
  have := @h 0 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.toReal_iff` idx 2: necessary (p=top,q=1)
theorem c3_55 : ¬ drop0% ENNReal.HolderConjugate.toReal_iff 2 := fun h => by
  have := @h ⊤ 1
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.toReal` idx 2: necessary (p=top,q=1)
theorem c3_56 : ¬ drop0% ENNReal.HolderConjugate.toReal 2 := fun h => by
  have := @h ⊤ 1 ENNReal.HolderConjugate.top_one
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.toReal` idx 3: necessary (p=2,q=1)
theorem c3_57 : ¬ drop0% ENNReal.HolderConjugate.toReal 3 := fun h => by
  have := @h 2 1 (by norm_num)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.toReal_of_ne_top` idx 2: necessary (p=top,q=1)
theorem c3_58 : ¬ drop0% ENNReal.HolderConjugate.toReal_of_ne_top 2 := fun h => by
  have := @h ⊤ 1 ENNReal.one_ne_top ENNReal.HolderConjugate.top_one
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.toReal_of_ne_top` idx 3: necessary (p=1,q=top)
theorem c3_59 : ¬ drop0% ENNReal.HolderConjugate.toReal_of_ne_top 3 := fun h => by
  have := @h 1 ⊤ ENNReal.one_ne_top ENNReal.HolderConjugate.one_top
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.toReal_of_ne_top` idx 4: necessary (p=q=1)
theorem c3_60 : ¬ drop0% ENNReal.HolderConjugate.toReal_of_ne_top 4 := fun h => by
  have := @h 1 1 ENNReal.one_ne_top ENNReal.one_ne_top
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.of_toNNReal` idx 2: necessary (p=q=0)
theorem c3_61 : ¬ drop0% ENNReal.HolderConjugate.of_toNNReal 2 := fun h => by
  have := @h 0 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.toNNReal_iff` idx 2: necessary (p=top,q=1)
theorem c3_62 : ¬ drop0% ENNReal.HolderConjugate.toNNReal_iff 2 := fun h => by
  have := @h ⊤ 1
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.toNNReal` idx 2: necessary (p=top,q=1)
theorem c3_63 : ¬ drop0% ENNReal.HolderConjugate.toNNReal 2 := fun h => by
  have := @h ⊤ 1 ENNReal.HolderConjugate.top_one
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.toNNReal` idx 3: necessary (p=2,q=1)
theorem c3_64 : ¬ drop0% ENNReal.HolderConjugate.toNNReal 3 := fun h => by
  have := @h 2 1 (by rw [ENNReal.toNNReal_ofNat]; norm_num)
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.conjExponent` idx 1: necessary (p=0)
theorem c3_65 : ¬ drop0% ENNReal.HolderConjugate.conjExponent 1 := fun h => by
  have := @h 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.instConjExponentOfFactLeOfNat` idx 1: necessary (p=0)
theorem c3_66 : ¬ drop0% ENNReal.HolderConjugate.instConjExponentOfFactLeOfNat 1 := fun h => by
  have := @h 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.inv_inv` idx 2: necessary (a=b=1)
theorem c3_67 : ¬ drop0% ENNReal.HolderConjugate.inv_inv 2 := fun h => by
  have := @h 1 1
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.inv_one_sub_inv` idx 1: necessary (a=top)
theorem c3_68 : ¬ drop0% ENNReal.HolderConjugate.inv_one_sub_inv 1 := fun h => by
  have := @h ⊤
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.inv_one_sub_inv'` idx 1: necessary (a=0)
theorem c3_69 : ¬ drop0% ENNReal.HolderConjugate.inv_one_sub_inv' 1 := fun h => by
  have := @h 0
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.HolderConjugate.one_sub_inv_inv` idx 1: necessary (a=top)
theorem c3_70 : ¬ drop0% ENNReal.HolderConjugate.one_sub_inv_inv 1 := fun h => by
  have := @h ⊤
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

-- `ENNReal.isConjExponent_iff_eq_conjExponent` idx 2: necessary (p=0,q=top)
theorem c3_71 : ¬ drop0% ENNReal.isConjExponent_iff_eq_conjExponent 2 := fun h => by
  have := @h 0 ⊤
  first | (norm_num [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done) | (simp [Real.holderTriple_iff, NNReal.holderTriple_iff, ENNReal.holderTriple_iff, Real.conjExponent, NNReal.conjExponent, ENNReal.conjExponent, ENNReal.toNNReal_ofNat] at this; done)

open SetRel

-- `SetRel.dom_univ` idx 2: necessary (alpha=Unit, beta=Empty)
theorem c3_100 : ¬ drop0% SetRel.dom_univ 2 := fun h => by have := congrArg (() ∈ ·) (@h Unit Empty); simp at this

-- `SetRel.cod_univ` idx 2: necessary (alpha=Empty, beta=Unit)
theorem c3_101 : ¬ drop0% SetRel.cod_univ 2 := fun h => by have := congrArg (() ∈ ·) (@h Empty Unit); simp at this

-- `SetRel.comp_subset_comp` idx 7: necessary (R1=univ, R2=empty on Unit)
theorem c3_102 : ¬ drop0% SetRel.comp_subset_comp 7 := fun h => by have := @h Unit Unit Unit Set.univ ∅ Set.univ Set.univ subset_rfl (a := ((), ())) (by simp); simp at this

-- `SetRel.comp_subset_comp` idx 8: necessary (S1=univ, S2=empty on Unit)
theorem c3_103 : ¬ drop0% SetRel.comp_subset_comp 8 := fun h => by have := @h Unit Unit Unit Set.univ Set.univ Set.univ ∅ subset_rfl (a := ((), ())) (by simp); simp at this

-- `SetRel.comp_subset_comp_left` idx 6: necessary (R1=univ, R2=empty on Unit)
theorem c3_104 : ¬ drop0% SetRel.comp_subset_comp_left 6 := fun h => by have := @h Unit Unit Unit Set.univ ∅ Set.univ (a := ((), ())) (by simp); simp at this

-- `SetRel.comp_subset_comp_right` idx 6: necessary (S1=univ, S2=empty on Unit)
theorem c3_105 : ¬ drop0% SetRel.comp_subset_comp_right 6 := fun h => by have := @h Unit Unit Unit Set.univ Set.univ ∅ (a := ((), ())) (by simp); simp at this

-- `Monotone.relComp` idx 7: necessary (f antitone on Bool, g constant univ)
theorem c3_106 : ¬ drop0% Monotone.relComp 7 := fun h => by have := Set.mem_of_subset_of_mem (@h Unit Unit Unit Bool _ (fun b => if b then ∅ else Set.univ) (fun _ => Set.univ) (fun _ _ _ => le_rfl) false true (show false ≤ true by decide)) (show ((), ()) ∈ _ by simp); simp at this

-- `Monotone.relComp` idx 8: necessary (g antitone on Bool, f constant univ)
theorem c3_107 : ¬ drop0% Monotone.relComp 8 := fun h => by have := Set.mem_of_subset_of_mem (@h Unit Unit Unit Bool _ (fun _ => Set.univ) (fun b => if b then ∅ else Set.univ) (fun _ _ _ => le_rfl) false true (show false ≤ true by decide)) (show ((), ()) ∈ _ by simp); simp at this

-- `SetRel.prod_comp_prod_of_disjoint` idx 5: necessary (all sets univ on Unit)
theorem c3_108 : ¬ drop0% SetRel.prod_comp_prod_of_disjoint 5 := fun h => by have := congrArg (((), ()) ∈ ·) (@h Unit Unit Unit Set.univ Set.univ Set.univ Set.univ); simp at this

-- `SetRel.image_subset_image` idx 5: necessary (R=univ, s1=univ, s2=empty)
theorem c3_109 : ¬ drop0% SetRel.image_subset_image 5 := fun h => by have := @h Unit Unit Set.univ Set.univ ∅ (a := ()) (by simp); simp at this

-- `SetRel.preimage_subset_preimage` idx 5: necessary (R=univ, t1=univ, t2=empty)
theorem c3_110 : ¬ drop0% SetRel.preimage_subset_preimage 5 := fun h => by have := @h Unit Unit Set.univ Set.univ ∅ (a := ()) (by simp); simp at this

-- `SetRel.image_univ_left` idx 3: necessary (s=empty)
theorem c3_111 : ¬ drop0% SetRel.image_univ_left 3 := fun h => by have := congrArg (() ∈ ·) (@h Unit Unit ∅); simp at this

-- `SetRel.preimage_univ_left` idx 3: necessary (t=empty)
theorem c3_112 : ¬ drop0% SetRel.preimage_univ_left 3 := fun h => by have := congrArg (() ∈ ·) (@h Unit Unit ∅); simp at this

-- `SetRel.image_eq_cod_of_dom_subset` idx 4: necessary (R=univ, s=empty)
theorem c3_113 : ¬ drop0% SetRel.image_eq_cod_of_dom_subset 4 := fun h => by have := congrArg (() ∈ ·) (@h Unit Unit Set.univ ∅); simp at this

-- `SetRel.preimage_eq_dom_of_cod_subset` idx 4: necessary (R=univ, t=empty)
theorem c3_114 : ¬ drop0% SetRel.preimage_eq_dom_of_cod_subset 4 := fun h => by have := congrArg (() ∈ ·) (@h Unit Unit Set.univ ∅); simp at this

-- `SetRel.core_subset_core` idx 5: necessary (R=univ, t1=univ, t2=empty)
theorem c3_115 : ¬ drop0% SetRel.core_subset_core 5 := fun h => by have := @h Unit Unit Set.univ Set.univ ∅ (a := ()) (by simp); simp at this

-- `SetRel.ball_mono` idx 4: necessary (R1=univ, R2=empty)
theorem c3_116 : ¬ drop0% SetRel.ball_mono 4 := fun h => by have := @h Unit Unit Set.univ ∅ () (a := ()) (by simp); simp at this

-- `SetRel.ball_subset_ball_of_comp_subset` idx 5: necessary (R1=R2={(true,true)} on Bool, a=true, b=false)
theorem c3_117 : ¬ drop0% SetRel.ball_subset_ball_of_comp_subset 5 := fun h => by have := Set.mem_of_subset_of_mem (@h Bool W1c3.Rt W1c3.Rt true false (by intro p; simp [W1c3.Rt]; aesop)) (show true ∈ W1c3.Rt.ball true by simp [W1c3.Rt]); simp [W1c3.Rt] at this

-- `SetRel.ball_subset_ball_of_comp_subset` idx 6: necessary (R1=univ, R2=empty)
theorem c3_118 : ¬ drop0% SetRel.ball_subset_ball_of_comp_subset 6 := fun h => by have := Set.mem_of_subset_of_mem (@h Unit Set.univ ∅ () () (by simp)) (show () ∈ SetRel.ball Set.univ () by simp); simp at this

-- `SetRel.isRefl_inter` idx 3: necessary (R1=empty, R2=univ)
theorem c3_119 : ¬ drop0% SetRel.isRefl_inter 3 := fun h => W1c3.empty_nrefl (by simpa using @h Unit ∅ Set.univ SetRel.isRefl_univ)

-- `SetRel.isRefl_inter` idx 4: necessary (R1=univ, R2=empty)
theorem c3_120 : ¬ drop0% SetRel.isRefl_inter 4 := fun h => W1c3.empty_nrefl (by simpa using @h Unit Set.univ ∅ SetRel.isRefl_univ)

-- `SetRel.IsRefl.comp` idx 3: necessary (R1=empty, R2=univ)
theorem c3_121 : ¬ drop0% SetRel.IsRefl.comp 3 := fun h => W1c3.empty_nrefl (by simpa using @h Unit ∅ Set.univ SetRel.isRefl_univ)

-- `SetRel.IsRefl.comp` idx 4: necessary (R1=univ, R2=empty)
theorem c3_122 : ¬ drop0% SetRel.IsRefl.comp 4 := fun h => W1c3.empty_nrefl (by simpa using @h Unit Set.univ ∅ SetRel.isRefl_univ)

-- `SetRel.IsRefl.sInter` idx 2: necessary (family {empty})
theorem c3_123 : ¬ drop0% SetRel.IsRefl.sInter 2 := fun h => W1c3.empty_nrefl (by simpa using @h Unit {∅})

-- `SetRel.isRefl_iInter` idx 3: necessary (iota=True, R=empty)
theorem c3_124 : ¬ drop0% SetRel.isRefl_iInter 3 := fun h => W1c3.empty_nrefl (by simpa using @h Unit True (fun _ => ∅))

-- `SetRel.isRefl_preimage` idx 4: necessary (R=empty, f=id)
theorem c3_125 : ¬ drop0% SetRel.isRefl_preimage 4 := fun h => W1c3.empty_nrefl (by simpa using @h Unit Unit ∅ id)

-- `SetRel.isRefl_mono` idx 4: necessary (R1=univ, R2=empty)
theorem c3_126 : ¬ drop0% SetRel.isRefl_mono 4 := fun h => W1c3.empty_nrefl (@h Unit Set.univ ∅ SetRel.isRefl_univ)

-- `SetRel.symm` idx 4: necessary (R={(false,true)})
theorem c3_127 : ¬ drop0% SetRel.symm 4 := fun h => W1c3.R1_ns ⟨fun a b hab => @h Bool W1c3.R1 a b hab⟩

-- `SetRel.inv_eq_self` idx 2: necessary (R={(false,true)})
theorem c3_128 : ¬ drop0% SetRel.inv_eq_self 2 := fun h => W1c3.R1_ns (by rw [← SetRel.inv_eq_self_iff]; exact @h Bool W1c3.R1)

-- `SetRel.instIsSymmInv` idx 2: necessary (R={(true,false)})
theorem c3_129 : ¬ drop0% SetRel.instIsSymmInv 2 := fun h => W1c3.R1_ns (@h Bool W1c3.R1.inv)

-- `SetRel.isSymm_inter` idx 3: necessary (R1={(false,true)}, R2=univ)
theorem c3_130 : ¬ drop0% SetRel.isSymm_inter 3 := fun h => W1c3.R1_ns (by simpa using @h Bool W1c3.R1 Set.univ inferInstance)

-- `SetRel.isSymm_inter` idx 4: necessary (R1=univ, R2={(false,true)})
theorem c3_131 : ¬ drop0% SetRel.isSymm_inter 4 := fun h => W1c3.R1_ns (by simpa using @h Bool Set.univ W1c3.R1 inferInstance)

-- `SetRel.IsSymm.sInter` idx 2: necessary (family {R1})
theorem c3_132 : ¬ drop0% SetRel.IsSymm.sInter 2 := fun h => W1c3.R1_ns (by simpa using @h Bool {W1c3.R1})

-- `SetRel.isSymm_iInter` idx 3: necessary (iota=True)
theorem c3_133 : ¬ drop0% SetRel.isSymm_iInter 3 := fun h => W1c3.R1_ns (by simpa using @h Bool True (fun _ => W1c3.R1))

-- `SetRel.isSymm_preimage` idx 4: necessary (f=id)
theorem c3_134 : ¬ drop0% SetRel.isSymm_preimage 4 := fun h => W1c3.R1_ns (by simpa using @h Bool Bool W1c3.R1 id)

-- `SetRel.isSymm_image` idx 4: necessary (f=id)
theorem c3_135 : ¬ drop0% SetRel.isSymm_image 4 := fun h => W1c3.R1_ns (by simpa using @h Bool Bool W1c3.R1 id)

-- `SetRel.isSymm_comp_self` idx 2: necessary (R={(0,1),(1,2)} on Nat)
theorem c3_136 : ¬ drop0% SetRel.isSymm_comp_self 2 := fun h => by have := @h ℕ W1c3.Rs; have := SetRel.symm (R := W1c3.Rs ○ W1c3.Rs) (a := 0) (b := 2) ⟨1, by simp [W1c3.Rs]⟩; obtain ⟨b, h1, h2⟩ := this; simp [W1c3.Rs] at h1 h2

-- `SetRel.prod_subset_comm` idx 4: necessary (R={(false,true)}, s1={false}, s2={true})
theorem c3_137 : ¬ drop0% SetRel.prod_subset_comm 4 := fun h => by have := Set.mem_of_subset_of_mem ((@h Bool {false} {true} W1c3.R1).mp (by intro p; simp [W1c3.R1])) (show (true, false) ∈ ({true} : Set Bool) ×ˢ ({false} : Set Bool) by simp); simp [W1c3.R1] at this

-- `SetRel.preimage_eq_image` idx 3: necessary (R={(false,true)}, s={false})
theorem c3_138 : ¬ drop0% SetRel.preimage_eq_image 3 := fun h => by have := congrArg (true ∈ ·) (@h Bool {false} W1c3.R1); simp [W1c3.R1] at this

-- `SetRel.symmetrize_mono` idx 3: necessary (R1=univ, R2=empty)
theorem c3_139 : ¬ drop0% SetRel.symmetrize_mono 3 := fun h => by have := @h Unit Set.univ ∅ (a := ((), ())) (by simp [SetRel.symmetrize]); simp [SetRel.symmetrize] at this

-- `SetRel.trans` idx 5: necessary (R={(0,1),(1,2)})
theorem c3_140 : ¬ drop0% SetRel.trans 5 := fun h => W1c3.Rs_nt ⟨fun a b c => @h ℕ W1c3.Rs a b c⟩

-- `SetRel.trans` idx 6: necessary (R={(false,true)}, a=true, b=false, c=true)
theorem c3_141 : ¬ drop0% SetRel.trans 6 := fun h => by have := @h Bool W1c3.R1 true false true inferInstance (by simp [W1c3.R1]); simp [W1c3.R1] at this

-- `SetRel.trans` idx 7: necessary (R={(false,true)}, a=false, b=true, c=false)
theorem c3_142 : ¬ drop0% SetRel.trans 7 := fun h => by have := @h Bool W1c3.R1 false true false inferInstance (by simp [W1c3.R1]); simp [W1c3.R1] at this

-- `SetRel.comp_subset_self` idx 2: necessary (R={(0,1),(1,2)})
theorem c3_143 : ¬ drop0% SetRel.comp_subset_self 2 := fun h => W1c3.Rs_nt (SetRel.isTrans_iff_comp_subset_self.mpr (@h ℕ W1c3.Rs))

-- `SetRel.comp_eq_self` idx 2: necessary (R={(false,true)} (transitive, not reflexive))
theorem c3_144 : ¬ drop0% SetRel.comp_eq_self 2 := fun h => by have := congrArg ((false, true) ∈ ·) (@h Bool W1c3.R1 inferInstance); simp [W1c3.R1] at this

-- `SetRel.comp_eq_self` idx 3: necessary (R reflexive non-transitive on Nat)
theorem c3_145 : ¬ drop0% SetRel.comp_eq_self 3 := fun h => W1c3.Rr_nt (SetRel.isTrans_iff_comp_subset_self.mpr (@h ℕ W1c3.Rr inferInstance).le)

-- `SetRel.isTrans_inter` idx 3: necessary (R1={(0,1),(1,2)}, R2=univ)
theorem c3_146 : ¬ drop0% SetRel.isTrans_inter 3 := fun h => W1c3.Rs_nt (by simpa using @h ℕ W1c3.Rs Set.univ inferInstance)

-- `SetRel.isTrans_inter` idx 4: necessary (R1=univ, R2={(0,1),(1,2)})
theorem c3_147 : ¬ drop0% SetRel.isTrans_inter 4 := fun h => W1c3.Rs_nt (by simpa using @h ℕ Set.univ W1c3.Rs inferInstance)

-- `SetRel.IsTrans.sInter` idx 2: necessary (family {Rs})
theorem c3_148 : ¬ drop0% SetRel.IsTrans.sInter 2 := fun h => W1c3.Rs_nt (by simpa using @h ℕ {W1c3.Rs})

-- `SetRel.isTrans_iInter` idx 3: necessary (iota=True)
theorem c3_149 : ¬ drop0% SetRel.isTrans_iInter 3 := fun h => W1c3.Rs_nt (by simpa using @h ℕ True (fun _ => W1c3.Rs))

-- `SetRel.isTrans_preimage` idx 4: necessary (f=id)
theorem c3_150 : ¬ drop0% SetRel.isTrans_preimage 4 := fun h => W1c3.Rs_nt (by simpa using @h ℕ ℕ W1c3.Rs id)

-- `SetRel.isTrans_symmetrize` idx 2: necessary (R={(false,true),(true,false)})
theorem c3_151 : ¬ drop0% SetRel.isTrans_symmetrize 2 := fun h => W1c3.Rc_nt (by have := @h Bool W1c3.Rc; rwa [show W1c3.Rc.symmetrize = W1c3.Rc by ext p; simp [SetRel.symmetrize, W1c3.Rc]; aesop] at this)

open scoped Pointwise

-- `Real.sInf_smul_of_nonneg` idx 5: necessary (alpha=R acting by a•x = swap12(a*swap12 x) (not monotone), a=2, s={1,2})
theorem c3_200 : ¬ drop0% Real.sInf_smul_of_nonneg 5 := fun h => by
  have := @h W1c3.RA _ _ _ W1c3.actW 2 W1c3.two_nn {1, 2}
  simp only [Set.smul_set_insert, Set.smul_set_singleton, csInf_pair, csSup_pair, W1c3.sA1, W1c3.sA2] at this; norm_num [W1c3.sA1, W1c3.sA2] at this

-- `Real.sInf_smul_of_nonneg` idx 7: necessary (alpha=R, a=-1, s={0,1})
theorem c3_201 : ¬ drop0% Real.sInf_smul_of_nonneg 7 := fun h => by
  have := @h ℝ _ _ _ _ _ (-1) {0, 1}
  simp only [Set.smul_set_insert, Set.smul_set_singleton, csInf_pair, csSup_pair] at this; norm_num at this

-- `Real.smul_iInf_of_nonneg` idx 6: necessary (stated at iota : Type, alpha : Type; alpha=R acting through swap12 (not monotone), a=2, iota=Bool, f=(1,2))
theorem c3_202 : ¬ (∀ {ι : Type} {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [MulActionWithZero α ℝ] {a : α}, 0 ≤ a → ∀ (f : ι → ℝ), (a • ⨅ i, f i) = ⨅ i, a • f i) := fun h => by
  have := @h Bool W1c3.RA _ _ _ W1c3.actW 2 W1c3.two_nn (fun b => if b then 1 else 2)
  simp only [W1c3.bI, W1c3.bS] at this; norm_num [W1c3.sA1, W1c3.sA2] at this

-- `Real.smul_iInf_of_nonneg` idx 8: necessary (stated at iota : Type, alpha : Type; alpha=R, a=-1, iota=Bool, f=(0,1))
theorem c3_203 : ¬ (∀ {ι : Type} {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [MulActionWithZero α ℝ] [IsOrderedModule α ℝ] {a : α} (f : ι → ℝ), (a • ⨅ i, f i) = ⨅ i, a • f i) := fun h => by
  have := @h Bool ℝ _ _ _ _ _ (-1) (fun b => if b then 0 else 1)
  simp only [W1c3.bI, W1c3.bS] at this; norm_num at this

-- `Real.sSup_smul_of_nonneg` idx 5: necessary (alpha=R acting by a•x = swap12(a*swap12 x) (not monotone), a=2, s={1,2})
theorem c3_204 : ¬ drop0% Real.sSup_smul_of_nonneg 5 := fun h => by
  have := @h W1c3.RA _ _ _ W1c3.actW 2 W1c3.two_nn {1, 2}
  simp only [Set.smul_set_insert, Set.smul_set_singleton, csInf_pair, csSup_pair, W1c3.sA1, W1c3.sA2] at this; norm_num [W1c3.sA1, W1c3.sA2] at this

-- `Real.sSup_smul_of_nonneg` idx 7: necessary (alpha=R, a=-1, s={0,1})
theorem c3_205 : ¬ drop0% Real.sSup_smul_of_nonneg 7 := fun h => by
  have := @h ℝ _ _ _ _ _ (-1) {0, 1}
  simp only [Set.smul_set_insert, Set.smul_set_singleton, csInf_pair, csSup_pair] at this; norm_num at this

-- `Real.smul_iSup_of_nonneg` idx 6: necessary (stated at iota : Type, alpha : Type; alpha=R acting through swap12 (not monotone), a=2, iota=Bool, f=(1,2))
theorem c3_206 : ¬ (∀ {ι : Type} {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [MulActionWithZero α ℝ] {a : α}, 0 ≤ a → ∀ (f : ι → ℝ), (a • ⨆ i, f i) = ⨆ i, a • f i) := fun h => by
  have := @h Bool W1c3.RA _ _ _ W1c3.actW 2 W1c3.two_nn (fun b => if b then 1 else 2)
  simp only [W1c3.bI, W1c3.bS] at this; norm_num [W1c3.sA1, W1c3.sA2] at this

-- `Real.smul_iSup_of_nonneg` idx 8: necessary (stated at iota : Type, alpha : Type; alpha=R, a=-1, iota=Bool, f=(0,1))
theorem c3_207 : ¬ (∀ {ι : Type} {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [MulActionWithZero α ℝ] [IsOrderedModule α ℝ] {a : α} (f : ι → ℝ), (a • ⨆ i, f i) = ⨆ i, a • f i) := fun h => by
  have := @h Bool ℝ _ _ _ _ _ (-1) (fun b => if b then 0 else 1)
  simp only [W1c3.bI, W1c3.bS] at this; norm_num at this

-- `Real.sInf_smul_of_nonpos` idx 7: necessary (alpha=R, a=1, s={0,1})
theorem c3_208 : ¬ drop0% Real.sInf_smul_of_nonpos 7 := fun h => by
  have := @h ℝ _ _ _ _ _ (1) {0, 1}
  simp only [Set.smul_set_insert, Set.smul_set_singleton, csInf_pair, csSup_pair] at this; norm_num at this

-- `Real.smul_iSup_of_nonpos` idx 8: necessary (stated at iota : Type, alpha : Type; alpha=R, a=1, iota=Bool, f=(0,1))
theorem c3_209 : ¬ (∀ {ι : Type} {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Module α ℝ] [IsOrderedModule α ℝ] {a : α} (f : ι → ℝ), (a • ⨆ i, f i) = ⨅ i, a • f i) := fun h => by
  have := @h Bool ℝ _ _ _ _ _ (1) (fun b => if b then 0 else 1)
  simp only [W1c3.bI, W1c3.bS] at this; norm_num at this

-- `Real.sSup_smul_of_nonpos` idx 7: necessary (alpha=R, a=1, s={0,1})
theorem c3_210 : ¬ drop0% Real.sSup_smul_of_nonpos 7 := fun h => by
  have := @h ℝ _ _ _ _ _ (1) {0, 1}
  simp only [Set.smul_set_insert, Set.smul_set_singleton, csInf_pair, csSup_pair] at this; norm_num at this

-- `Real.smul_iInf_of_nonpos` idx 8: necessary (stated at iota : Type, alpha : Type; alpha=R, a=1, iota=Bool, f=(0,1))
theorem c3_211 : ¬ (∀ {ι : Type} {α : Type} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Module α ℝ] [IsOrderedModule α ℝ] {a : α} (f : ι → ℝ), (a • ⨅ i, f i) = ⨆ i, a • f i) := fun h => by
  have := @h Bool ℝ _ _ _ _ _ (1) (fun b => if b then 0 else 1)
  simp only [W1c3.bI, W1c3.bS] at this; norm_num at this

-- `Real.mul_iInf_of_nonneg` idx 2: necessary (iota=Bool, r=-1, f=(0,1))
theorem c3_212 : ¬ drop1% Real.mul_iInf_of_nonneg 2 := fun h => by
  have := @h Bool (-1) (fun b => if b then 0 else 1)
  simp only [W1c3.bI, W1c3.bS] at this; norm_num at this

-- `Real.mul_iSup_of_nonneg` idx 2: necessary (iota=Bool, r=-1, f=(0,1))
theorem c3_213 : ¬ drop1% Real.mul_iSup_of_nonneg 2 := fun h => by
  have := @h Bool (-1) (fun b => if b then 0 else 1)
  simp only [W1c3.bI, W1c3.bS] at this; norm_num at this

-- `Real.mul_iInf_of_nonpos` idx 2: necessary (iota=Bool, r=1, f=(0,1))
theorem c3_214 : ¬ drop1% Real.mul_iInf_of_nonpos 2 := fun h => by
  have := @h Bool (1) (fun b => if b then 0 else 1)
  simp only [W1c3.bI, W1c3.bS] at this; norm_num at this

-- `Real.mul_iSup_of_nonpos` idx 2: necessary (iota=Bool, r=1, f=(0,1))
theorem c3_215 : ¬ drop1% Real.mul_iSup_of_nonpos 2 := fun h => by
  have := @h Bool (1) (fun b => if b then 0 else 1)
  simp only [W1c3.bI, W1c3.bS] at this; norm_num at this

-- `Real.iInf_mul_of_nonneg` idx 2: necessary (iota=Bool, r=-1, f=(0,1))
theorem c3_216 : ¬ drop1% Real.iInf_mul_of_nonneg 2 := fun h => by
  have := @h Bool (-1) (fun b => if b then 0 else 1)
  simp only [W1c3.bI, W1c3.bS] at this; norm_num at this

-- `Real.iSup_mul_of_nonneg` idx 2: necessary (iota=Bool, r=-1, f=(0,1))
theorem c3_217 : ¬ drop1% Real.iSup_mul_of_nonneg 2 := fun h => by
  have := @h Bool (-1) (fun b => if b then 0 else 1)
  simp only [W1c3.bI, W1c3.bS] at this; norm_num at this

-- `Real.iInf_mul_of_nonpos` idx 2: necessary (iota=Bool, r=1, f=(0,1))
theorem c3_218 : ¬ drop1% Real.iInf_mul_of_nonpos 2 := fun h => by
  have := @h Bool (1) (fun b => if b then 0 else 1)
  simp only [W1c3.bI, W1c3.bS] at this; norm_num at this

-- `Real.iSup_mul_of_nonpos` idx 2: necessary (iota=Bool, r=1, f=(0,1))
theorem c3_219 : ¬ drop1% Real.iSup_mul_of_nonpos 2 := fun h => by
  have := @h Bool (1) (fun b => if b then 0 else 1)
  simp only [W1c3.bI, W1c3.bS] at this; norm_num at this

-- `num_smul_one_lt_den_smul_add` idx 3: necessary (Fin 3 with its usual order (archimedean, 0 ≤ 1, not an ordered monoid); u=v=0, x=1, y=2)
theorem c3_300 : ¬ drop0% num_smul_one_lt_den_smul_add 3 := fun h => by
  have := @h (Fin 3) _ _ _ 0 0 1 2 (by simp) (by simp)
  revert this; simp

-- `num_smul_one_lt_den_smul_add` idx 9: necessary (M=ℤ, u=1, v=0, x=0, y=1)
theorem c3_301 : ¬ drop0% num_smul_one_lt_den_smul_add 9 := fun h => by
  have := @h ℤ _ _ _ _ 1 0 0 1 (by simp); simp at this

-- `num_smul_one_lt_den_smul_add` idx 10: necessary (M=ℤ, u=0, v=1, x=1, y=0)
theorem c3_302 : ¬ drop0% num_smul_one_lt_den_smul_add 10 := fun h => by
  have := @h ℤ _ _ _ _ 0 1 1 0 (by simp); simp at this

-- `num_le_nat_mul_den` idx 5: necessary (ℤ with reversed order, 1 = 1 (so 1 < 0); num=1, den=1, x=0, n=0)
theorem c3_303 : ¬ drop0% num_le_nat_mul_den 5 := fun h => absurd (@h W1c3.ZD _ _ _ _ _ 1 1 0 (by decide) 0 (by decide)) (by decide)

-- `num_le_nat_mul_den` idx 6: necessary (ℤ with 1 = 0; num=1, den=1, x=0, n=0)
theorem c3_304 : ¬ drop0% num_le_nat_mul_den 6 := fun h => absurd (@h W1c3.Z0 _ _ _ _ _ 1 1 0 (by decide) 0 (by decide)) (by decide)

-- `Archimedean.ratLt_bddAbove` idx 3: necessary (Fin 3 with its usual order (archimedean, 0 ≤ 1, not an ordered monoid); ratLt x unbounded)
theorem c3_305 : ¬ drop0% Archimedean.ratLt_bddAbove 3 := fun h => W1c3.unbQ (W1c3.F3_unb 1 (by decide)) (@h (Fin 3) _ _ _ _ _ _ (1 : Fin 3))

-- `Archimedean.ratLt_bddAbove` idx 5: necessary (ℤ with reversed order, 1 = 1 (so 1 < 0); ratLt x unbounded)
theorem c3_306 : ¬ drop0% Archimedean.ratLt_bddAbove 5 := fun h => W1c3.unbQ (W1c3.ZD_unb 0) (@h W1c3.ZD _ _ _ _ _ _ (show W1c3.ZD from (0 : ℤ)))

-- `Archimedean.ratLt_bddAbove` idx 6: necessary (ℤ with 1 = 0; ratLt x unbounded)
theorem c3_307 : ¬ drop0% Archimedean.ratLt_bddAbove 6 := fun h => W1c3.unbQ (W1c3.Z0_unb 1 one_pos) (@h W1c3.Z0 _ _ _ _ _ _ (show W1c3.Z0 from (1 : ℤ)))

-- `Archimedean.ratLt_bddAbove` idx 7: necessary (lexicographic ℤ × ℤ with 1 = (0,1) (not archimedean); ratLt x unbounded)
theorem c3_308 : ¬ drop0% Archimedean.ratLt_bddAbove 7 := fun h => W1c3.unbQ (W1c3.NA_unb 1 0 one_pos) (@h W1c3.NA _ _ _ _ _ _ (W1c3.NA.mk 1 0))

-- `Archimedean.ratLt_nonempty` idx 3: necessary (Fin 3 with its usual order (archimedean, 0 ≤ 1, not an ordered monoid); ratLt 0 empty)
theorem c3_309 : ¬ drop0% Archimedean.ratLt_nonempty 3 := fun h => by obtain ⟨r, hr⟩ := @h (Fin 3) _ _ _ _ _ _ 0; exact W1c3.F3_empty r hr

-- `Archimedean.ratLt_nonempty` idx 7: necessary (lexicographic ℤ × ℤ with 1 = (0,1) (not archimedean); ratLt (-1,0) empty)
theorem c3_310 : ¬ drop0% Archimedean.ratLt_nonempty 7 := fun h => by obtain ⟨r, hr⟩ := @h W1c3.NA _ _ _ _ _ _ (W1c3.NA.mk (-1) 0); exact W1c3.NA_empty r hr

-- `Archimedean.ratLt_add` idx 3: necessary (Fin 3 with its usual order (archimedean, 0 ≤ 1, not an ordered monoid); x=1, y=2: 0 in ratLt 1 + ratLt 2, ratLt 0 empty)
theorem c3_311 : ¬ drop0% Archimedean.ratLt_add 3 := fun h => by
  have e := @h (Fin 3) _ _ _ _ _ _ 1 2
  have m : (0 : ℚ) ∈ Archimedean.ratLt (1 : Fin 3) + Archimedean.ratLt (2 : Fin 3) :=
    ⟨0, (by show (0 : ℚ).num • (1 : Fin 3) < (0 : ℚ).den • _; simp), 0, (by show (0 : ℚ).num • (1 : Fin 3) < (0 : ℚ).den • _; simp), by simp⟩
  rw [← e, show (1 + 2 : Fin 3) = 0 by decide] at m; exact W1c3.F3_empty 0 m

-- `Archimedean.ratLt_add` idx 6: necessary (ℤ with 1 = 0; x=1, y=0: ratLt 1 = univ, ratLt 0 empty)
theorem c3_312 : ¬ drop0% Archimedean.ratLt_add 6 := fun h => by
  have e := @h W1c3.Z0 _ _ _ _ _ _ (show W1c3.Z0 from (1 : ℤ)) 0
  have m : (0 : ℚ) ∈ Archimedean.ratLt ((show W1c3.Z0 from (1 : ℤ)) + 0) := by rw [add_zero]; exact W1c3.Z0_mem 1 one_pos 0
  rw [e] at m; obtain ⟨a, ha, b, hb, -⟩ := m; exact W1c3.Z0_empty b hb

-- `Archimedean.ratLt_add` idx 7: necessary (lexicographic ℤ × ℤ with 1 = (0,1) (not archimedean); x=(1,0), y=(-1,0): -1 in ratLt 0, ratLt y empty)
theorem c3_313 : ¬ drop0% Archimedean.ratLt_add 7 := fun h => by
  have e := @h W1c3.NA _ _ _ _ _ _ (W1c3.NA.mk 1 0) (W1c3.NA.mk (-1) 0)
  have m : (-1 : ℚ) ∈ Archimedean.ratLt (W1c3.NA.mk 1 0 + W1c3.NA.mk (-1) 0) := W1c3.NA_m1
  rw [e] at m; obtain ⟨a, ha, b, hb, -⟩ := m; exact W1c3.NA_empty b hb

-- `Archimedean.ratLt'_bddAbove` idx 3: necessary (Fin 3 with its usual order (archimedean, 0 ≤ 1, not an ordered monoid); ratLt x unbounded)
theorem c3_314 : ¬ drop0% Archimedean.ratLt'_bddAbove 3 := fun h => W1c3.unbR (W1c3.F3_unb 1 (by decide)) (@h (Fin 3) _ _ _ _ _ _ (1 : Fin 3))

-- `Archimedean.ratLt'_bddAbove` idx 5: necessary (ℤ with reversed order, 1 = 1 (so 1 < 0); ratLt x unbounded)
theorem c3_315 : ¬ drop0% Archimedean.ratLt'_bddAbove 5 := fun h => W1c3.unbR (W1c3.ZD_unb 0) (@h W1c3.ZD _ _ _ _ _ _ (show W1c3.ZD from (0 : ℤ)))

-- `Archimedean.ratLt'_bddAbove` idx 6: necessary (ℤ with 1 = 0; ratLt x unbounded)
theorem c3_316 : ¬ drop0% Archimedean.ratLt'_bddAbove 6 := fun h => W1c3.unbR (W1c3.Z0_unb 1 one_pos) (@h W1c3.Z0 _ _ _ _ _ _ (show W1c3.Z0 from (1 : ℤ)))

-- `Archimedean.ratLt'_bddAbove` idx 7: necessary (lexicographic ℤ × ℤ with 1 = (0,1) (not archimedean); ratLt x unbounded)
theorem c3_317 : ¬ drop0% Archimedean.ratLt'_bddAbove 7 := fun h => W1c3.unbR (W1c3.NA_unb 1 0 one_pos) (@h W1c3.NA _ _ _ _ _ _ (W1c3.NA.mk 1 0))

-- `Archimedean.ratLt'_nonempty` idx 3: necessary (Fin 3 with its usual order (archimedean, 0 ≤ 1, not an ordered monoid); ratLt 0 empty)
theorem c3_318 : ¬ drop0% Archimedean.ratLt'_nonempty 3 := fun h => by obtain ⟨_, r, hr, -⟩ := @h (Fin 3) _ _ _ _ _ _ 0; exact W1c3.F3_empty r hr

-- `Archimedean.ratLt'_nonempty` idx 7: necessary (lexicographic ℤ × ℤ with 1 = (0,1) (not archimedean); ratLt (-1,0) empty)
theorem c3_319 : ¬ drop0% Archimedean.ratLt'_nonempty 7 := fun h => by obtain ⟨_, r, hr, -⟩ := @h W1c3.NA _ _ _ _ _ _ (W1c3.NA.mk (-1) 0); exact W1c3.NA_empty r hr

-- `Archimedean.ratLt'_add` idx 3: necessary (Fin 3 with its usual order (archimedean, 0 ≤ 1, not an ordered monoid); x=1, y=2)
theorem c3_320 : ¬ drop0% Archimedean.ratLt'_add 3 := fun h => by
  have e := @h (Fin 3) _ _ _ _ _ _ 1 2
  have m : (0 : ℝ) ∈ Archimedean.ratLt' (1 : Fin 3) + Archimedean.ratLt' (2 : Fin 3) :=
    ⟨0, ⟨0, (by show (0 : ℚ).num • (1 : Fin 3) < (0 : ℚ).den • _; simp), by simp⟩, 0, ⟨0, (by show (0 : ℚ).num • (1 : Fin 3) < (0 : ℚ).den • _; simp), by simp⟩, by simp⟩
  rw [← e, show (1 + 2 : Fin 3) = 0 by decide] at m; obtain ⟨r, hr, -⟩ := m; exact W1c3.F3_empty r hr

-- `Archimedean.ratLt'_add` idx 6: necessary (ℤ with 1 = 0; x=1, y=0)
theorem c3_321 : ¬ drop0% Archimedean.ratLt'_add 6 := fun h => by
  have e := @h W1c3.Z0 _ _ _ _ _ _ (show W1c3.Z0 from (1 : ℤ)) 0
  have m : (0 : ℝ) ∈ Archimedean.ratLt' ((show W1c3.Z0 from (1 : ℤ)) + 0) := by
    rw [add_zero]; exact ⟨0, W1c3.Z0_mem 1 one_pos 0, by simp⟩
  rw [e] at m; obtain ⟨a, ha, b, ⟨b', hb', -⟩, -⟩ := m; exact W1c3.Z0_empty b' hb'

-- `Archimedean.ratLt'_add` idx 7: necessary (lexicographic ℤ × ℤ with 1 = (0,1) (not archimedean); x=(1,0), y=(-1,0))
theorem c3_322 : ¬ drop0% Archimedean.ratLt'_add 7 := fun h => by
  have e := @h W1c3.NA _ _ _ _ _ _ (W1c3.NA.mk 1 0) (W1c3.NA.mk (-1) 0)
  have m : (-1 : ℝ) ∈ Archimedean.ratLt' (W1c3.NA.mk 1 0 + W1c3.NA.mk (-1) 0) := ⟨-1, W1c3.NA_m1, by simp⟩
  rw [e] at m; obtain ⟨a, ha, b, ⟨b', hb', -⟩, -⟩ := m; exact W1c3.NA_empty b' hb'

-- `Archimedean.embedRealFun_strictMono` idx 3: necessary (Fin 3 with its usual order (archimedean, 0 ≤ 1, not an ordered monoid); x<y with both ratLt unbounded, so embedRealFun x = embedRealFun y = 0)
theorem c3_323 : ¬ drop0% Archimedean.embedRealFun_strictMono 3 := fun h => by
  have := @h (Fin 3) _ _ _ _ _ _ (a := (1 : Fin 3)) (b := (2 : Fin 3)) (by decide)
  have e1 : Archimedean.embedRealFun (1 : Fin 3) = 0 := Real.sSup_of_not_bddAbove (W1c3.unbR (W1c3.F3_unb 1 (by decide)))
  have e2 : Archimedean.embedRealFun (2 : Fin 3) = 0 := Real.sSup_of_not_bddAbove (W1c3.unbR (W1c3.F3_unb 2 (by decide)))
  rw [e1, e2] at this; exact lt_irrefl _ this

-- `Archimedean.embedRealFun_strictMono` idx 5: necessary (ℤ with reversed order, 1 = 1 (so 1 < 0); x<y with both ratLt unbounded, so embedRealFun x = embedRealFun y = 0)
theorem c3_324 : ¬ drop0% Archimedean.embedRealFun_strictMono 5 := fun h => by
  have := @h W1c3.ZD _ _ _ _ _ _ (a := (show W1c3.ZD from (1 : ℤ))) (b := (show W1c3.ZD from (0 : ℤ))) (show (0 : ℤ) < 1 by decide)
  have e1 : Archimedean.embedRealFun (show W1c3.ZD from (1 : ℤ)) = 0 := Real.sSup_of_not_bddAbove (W1c3.unbR (W1c3.ZD_unb 1))
  have e2 : Archimedean.embedRealFun (show W1c3.ZD from (0 : ℤ)) = 0 := Real.sSup_of_not_bddAbove (W1c3.unbR (W1c3.ZD_unb 0))
  rw [e1, e2] at this; exact lt_irrefl _ this

-- `Archimedean.embedRealFun_strictMono` idx 6: necessary (ℤ with 1 = 0; x<y with both ratLt unbounded, so embedRealFun x = embedRealFun y = 0)
theorem c3_325 : ¬ drop0% Archimedean.embedRealFun_strictMono 6 := fun h => by
  have := @h W1c3.Z0 _ _ _ _ _ _ (a := (show W1c3.Z0 from (1 : ℤ))) (b := (show W1c3.Z0 from (2 : ℤ))) (show (1 : ℤ) < 2 by decide)
  have e1 : Archimedean.embedRealFun (show W1c3.Z0 from (1 : ℤ)) = 0 := Real.sSup_of_not_bddAbove (W1c3.unbR (W1c3.Z0_unb 1 one_pos))
  have e2 : Archimedean.embedRealFun (show W1c3.Z0 from (2 : ℤ)) = 0 := Real.sSup_of_not_bddAbove (W1c3.unbR (W1c3.Z0_unb 2 two_pos))
  rw [e1, e2] at this; exact lt_irrefl _ this

-- `Archimedean.embedRealFun_strictMono` idx 7: necessary (lexicographic ℤ × ℤ with 1 = (0,1) (not archimedean); x<y with both ratLt unbounded, so embedRealFun x = embedRealFun y = 0)
theorem c3_326 : ¬ drop0% Archimedean.embedRealFun_strictMono 7 := fun h => by
  have := @h W1c3.NA _ _ _ _ _ _ (a := (W1c3.NA.mk 1 0)) (b := (W1c3.NA.mk 2 0)) (by rw [W1c3.NA_lt]; omega)
  have e1 : Archimedean.embedRealFun (W1c3.NA.mk 1 0) = 0 := Real.sSup_of_not_bddAbove (W1c3.unbR (W1c3.NA_unb 1 0 one_pos))
  have e2 : Archimedean.embedRealFun (W1c3.NA.mk 2 0) = 0 := Real.sSup_of_not_bddAbove (W1c3.unbR (W1c3.NA_unb 2 0 two_pos))
  rw [e1, e2] at this; exact lt_irrefl _ this

-- `Archimedean.embedReal_apply` idx 3: necessary (Fin 3 with its usual order (archimedean, 0 ≤ 1, not an ordered monoid) (dependent: the dropped class itself fails))
theorem c3_327 : ¬ indep0% Archimedean.embedReal_apply 3 := fun h => W1c3.F3_not_ord (@h (Fin 3) _ _ _ _ _ _ 0)

-- `Archimedean.embedReal_apply` idx 5: necessary (ℤ with reversed order, 1 = 1 (so 1 < 0) (dependent: the dropped class itself fails))
theorem c3_328 : ¬ indep0% Archimedean.embedReal_apply 5 := fun h => W1c3.ZD_not (@h W1c3.ZD _ _ _ _ _ _ 0)

-- `Archimedean.embedReal_apply` idx 7: necessary (lexicographic ℤ × ℤ with 1 = (0,1) (not archimedean) (dependent: the dropped class itself fails))
theorem c3_329 : ¬ indep0% Archimedean.embedReal_apply 7 := fun h => W1c3.NA_not (@h W1c3.NA _ _ _ _ _ _ 0)

-- `Archimedean.embedReal_injective` idx 3: necessary (Fin 3 with its usual order (archimedean, 0 ≤ 1, not an ordered monoid) (dependent: the dropped class itself fails))
theorem c3_330 : ¬ indep0% Archimedean.embedReal_injective 3 := fun h => W1c3.F3_not_ord (@h (Fin 3) _ _ _ _ _ _)

-- `Archimedean.embedReal_injective` idx 5: necessary (ℤ with reversed order, 1 = 1 (so 1 < 0) (dependent: the dropped class itself fails))
theorem c3_331 : ¬ indep0% Archimedean.embedReal_injective 5 := fun h => W1c3.ZD_not (@h W1c3.ZD _ _ _ _ _ _)

-- `Archimedean.embedReal_injective` idx 7: necessary (lexicographic ℤ × ℤ with 1 = (0,1) (not archimedean) (dependent: the dropped class itself fails))
theorem c3_332 : ¬ indep0% Archimedean.embedReal_injective 7 := fun h => W1c3.NA_not (@h W1c3.NA _ _ _ _ _ _)

-- `Archimedean.embedReal_one` idx 3: necessary (Fin 3 with its usual order (archimedean, 0 ≤ 1, not an ordered monoid) (dependent: the dropped class itself fails))
theorem c3_333 : ¬ indep0% Archimedean.embedReal_one 3 := fun h => W1c3.F3_not_ord (@h (Fin 3) _ _ _ _ _ _)

-- `Archimedean.embedReal_one` idx 5: necessary (ℤ with reversed order, 1 = 1 (so 1 < 0) (dependent: the dropped class itself fails))
theorem c3_334 : ¬ indep0% Archimedean.embedReal_one 5 := fun h => W1c3.ZD_not (@h W1c3.ZD _ _ _ _ _ _)

-- `Archimedean.embedReal_one` idx 7: necessary (lexicographic ℤ × ℤ with 1 = (0,1) (not archimedean) (dependent: the dropped class itself fails))
theorem c3_335 : ¬ indep0% Archimedean.embedReal_one 7 := fun h => W1c3.NA_not (@h W1c3.NA _ _ _ _ _ _)

-- `Archimedean.exists_orderAddMonoidHom_real_injective` idx 3: necessary (Fin 3 with its usual order (archimedean, 0 ≤ 1, not an ordered monoid); additive maps Fin 3 → ℝ vanish)
theorem c3_336 : ¬ drop0% Archimedean.exists_orderAddMonoidHom_real_injective 3 := fun h => by
  obtain ⟨f, hf⟩ := @h (Fin 3) _ _ _
  have h3 : f (1 + 1 + 1) = f 1 + f 1 + f 1 := by rw [map_add, map_add]
  rw [show (1 + 1 + 1 : Fin 3) = 0 by decide, map_zero] at h3
  have : f 1 = f 0 := by rw [map_zero]; linarith
  exact absurd (hf this) (by decide)

-- `Archimedean.exists_orderAddMonoidHom_real_injective` idx 4: necessary (lexicographic ℤ × ℤ with 1 = (0,1) (not archimedean); an injective monotone additive map would make it archimedean)
theorem c3_337 : ¬ drop0% Archimedean.exists_orderAddMonoidHom_real_injective 4 := fun h => by
  obtain ⟨f, hf⟩ := @h W1c3.NA _ _ _
  have hle : f 0 ≤ f (W1c3.NA.mk 0 1) := OrderHomClass.mono f (by rw [W1c3.NA_zero, W1c3.NA_le]; omega)
  have hne : f 0 ≠ f (W1c3.NA.mk 0 1) := fun e => by
    have := congrArg (fun x : W1c3.NA => (ofLex x).2) (hf e); simp [W1c3.NA_zero, W1c3.NA.mk] at this
  have hc : 0 < f (W1c3.NA.mk 0 1) := lt_of_le_of_ne (by simpa using hle) (by simpa using hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (f (W1c3.NA.mk 1 0) / f (W1c3.NA.mk 0 1))
  have hm : f (n • W1c3.NA.mk 0 1) ≤ f (W1c3.NA.mk 1 0) := OrderHomClass.mono f (by rw [W1c3.NA_nsmul, W1c3.NA_le]; omega)
  rw [map_nsmul, nsmul_eq_mul] at hm
  rw [div_lt_iff₀ hc] at hn; linarith

-- `Archimedean.embedRealFun_add` idx 7: necessary (lexicographic ℤ × ℤ with 1 = (0,1); x = (1,0), y = (-1,1): f x = 0, f y = 0, f (x+y) = f 1 ≥ 1/2)
theorem c3_420 : ¬ drop0% Archimedean.embedRealFun_add 7 := fun h => by
  have e := @h W1c3.NA _ _ _ _ _ _ (W1c3.NA.mk 1 0) (W1c3.NA.mk (-1) 1)
  have e1 : Archimedean.embedRealFun (W1c3.NA.mk 1 0) = 0 :=
    Real.sSup_of_not_bddAbove (W1c3.unbR (W1c3.NA_unb 1 0 one_pos))
  rw [W1c3.NA_add, e1, W1c3.NA_f1] at e
  have := W1c3.NA_f2; norm_num at e; rw [e] at this; norm_num at this

universe u_1

-- `Archimedean.ratLt_nonempty` idx 5: removable (if 1 < 0, large naturals lie in ratLt x; else the library lemma)
theorem c3_400 : drop% Archimedean.ratLt_nonempty 5 := by
  intro M _ _ _ _ _ _ x
  rcases lt_or_gt_of_ne (NeZero.ne (1 : M)) with h1 | h1
  · exact ⟨_, W1c3.neg_one_unb h1 x 0⟩
  · haveI : ZeroLEOneClass M := ⟨h1.le⟩; exact Archimedean.ratLt_nonempty x

-- `Archimedean.ratLt'_nonempty` idx 5: removable (as for ratLt_nonempty)
theorem c3_401 : drop% Archimedean.ratLt'_nonempty 5 := by
  intro M _ _ _ _ _ _ x
  rcases lt_or_gt_of_ne (NeZero.ne (1 : M)) with h1 | h1
  · exact ⟨_, _, W1c3.neg_one_unb h1 x 0, rfl⟩
  · haveI : ZeroLEOneClass M := ⟨h1.le⟩; exact Archimedean.ratLt'_nonempty x

-- `Archimedean.embedRealFun_zero` idx 5: removable (if 1 < 0, every ratLt x is unbounded, so embedRealFun is 0)
theorem c3_402 : drop% Archimedean.embedRealFun_zero 5 := by
  intro M _ _ _ _ _ _
  rcases lt_or_gt_of_ne (NeZero.ne (1 : M)) with h1 | h1
  · exact W1c3.neg_one_zero h1 0
  · haveI : ZeroLEOneClass M := ⟨h1.le⟩; exact Archimedean.embedRealFun_zero M

-- `Archimedean.embedRealFun_add` idx 5: removable (if 1 < 0, embedRealFun is identically 0)
theorem c3_403 : drop% Archimedean.embedRealFun_add 5 := by
  intro M _ _ _ _ _ _ x y
  rcases lt_or_gt_of_ne (NeZero.ne (1 : M)) with h1 | h1
  · rw [W1c3.neg_one_zero h1, W1c3.neg_one_zero h1, W1c3.neg_one_zero h1, add_zero]
  · haveI : ZeroLEOneClass M := ⟨h1.le⟩; exact Archimedean.embedRealFun_add x y

-- `Archimedean.embedRealFun_zero` idx 6: removable (if 1 = 0, every ratLt x is empty or everything, so embedRealFun is 0)
theorem c3_404 : drop% Archimedean.embedRealFun_zero 6 := by
  intro M _ _ _ _ _ _
  by_cases h1 : (1 : M) = 0
  · exact W1c3.one_zero_fun h1 0
  · haveI : NeZero (1 : M) := ⟨h1⟩; exact Archimedean.embedRealFun_zero M

-- `Archimedean.embedRealFun_add` idx 6: removable (if 1 = 0, embedRealFun is identically 0)
theorem c3_405 : drop% Archimedean.embedRealFun_add 6 := by
  intro M _ _ _ _ _ _ x y
  by_cases h1 : (1 : M) = 0
  · rw [W1c3.one_zero_fun h1, W1c3.one_zero_fun h1, W1c3.one_zero_fun h1, add_zero]
  · haveI : NeZero (1 : M) := ⟨h1⟩; exact Archimedean.embedRealFun_add x y

-- `Archimedean.embedRealFun_zero` idx 7: removable (ratLt 0 is the set of negative rationals without any archimedean hypothesis)
theorem c3_406 : drop% Archimedean.embedRealFun_zero 7 := by
  intro M _ _ _ _ _ _
  have h1 : (0 : M) < 1 := lt_of_le_of_ne zero_le_one (NeZero.ne (1 : M)).symm
  have hS : Archimedean.ratLt (0 : M) = {r : ℚ | r < 0} := by
    ext r
    show r.num • (1 : M) < r.den • (0 : M) ↔ r < 0
    rw [smul_zero, ← zero_zsmul (1 : M), zsmul_lt_zsmul_iff_left h1, Rat.num_neg]
  show sSup ((Rat.castHom ℝ) '' Archimedean.ratLt (0 : M)) = 0
  rw [hS]
  have hb : ∀ y ∈ (Rat.castHom ℝ) '' {r : ℚ | r < 0}, y ≤ 0 := by
    rintro _ ⟨r, hr, rfl⟩; simp only [eq_ratCast, Rat.cast_nonpos]; exact (show r < 0 from hr).le
  have hne : ((Rat.castHom ℝ) '' {r : ℚ | r < 0}).Nonempty := ⟨_, -1, show (-1 : ℚ) < 0 by norm_num, rfl⟩
  refine le_antisymm (csSup_le hne hb) ?_
  by_contra hlt; push_neg at hlt
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  have := le_csSup (a := (q : ℝ)) ⟨0, hb⟩ ⟨q, show q < 0 by exact_mod_cast hq2, by simp⟩
  linarith

universe u_2 u_3

-- `Real.sInf_smul_of_nonneg` idx 3: removable (a monotone invertible scalar acts as an order isomorphism of ℝ)
theorem c3_430 : drop% Real.sInf_smul_of_nonneg 3 := by
  intro α _ _ _ _ a ha s; exact W1c3.sInf_smul_nn ha s

-- `Real.sSup_smul_of_nonneg` idx 3: removable (a monotone invertible scalar acts as an order isomorphism of ℝ)
theorem c3_431 : drop% Real.sSup_smul_of_nonneg 3 := by
  intro α _ _ _ _ a ha s; exact W1c3.sSup_smul_nn ha s

-- `Real.smul_iInf_of_nonneg` idx 4: removable (from the sInf version without IsStrictOrderedRing)
theorem c3_432 : drop% Real.smul_iInf_of_nonneg 4 := by
  intro ι α _ _ _ _ a ha f
  exact (W1c3.sInf_smul_nn ha _).symm.trans congr(sInf $((Set.range_comp ..).symm))

-- `Real.smul_iSup_of_nonneg` idx 4: removable (from the sSup version without IsStrictOrderedRing)
theorem c3_433 : drop% Real.smul_iSup_of_nonneg 4 := by
  intro ι α _ _ _ _ a ha f
  exact (W1c3.sSup_smul_nn ha _).symm.trans congr(sSup $((Set.range_comp ..).symm))

-- `Real.sInf_smul_of_nonpos` idx 3: removable (IsOrderedModule over a module forces 0 ≤ -a; then reduce to the nonneg case)
theorem c3_434 : drop% Real.sInf_smul_of_nonpos 3 := by
  intro α _ _ _ _ a ha s; exact W1c3.sInf_smul_np ha s

-- `Real.sSup_smul_of_nonpos` idx 3: removable (IsOrderedModule over a module forces 0 ≤ -a; then reduce to the nonneg case)
theorem c3_435 : drop% Real.sSup_smul_of_nonpos 3 := by
  intro α _ _ _ _ a ha s; exact W1c3.sSup_smul_np ha s

-- `Real.smul_iSup_of_nonpos` idx 4: removable (from the sInf version without IsStrictOrderedRing)
theorem c3_436 : drop% Real.smul_iSup_of_nonpos 4 := by
  intro ι α _ _ _ _ a ha f
  exact (W1c3.sInf_smul_np ha _).symm.trans congr(sInf $((Set.range_comp ..).symm))

-- `Real.smul_iInf_of_nonpos` idx 4: removable (from the sSup version without IsStrictOrderedRing)
theorem c3_437 : drop% Real.smul_iInf_of_nonpos 4 := by
  intro ι α _ _ _ _ a ha f
  exact (W1c3.sSup_smul_np ha _).symm.trans congr(sSup $((Set.range_comp ..).symm))

-- `Archimedean.embedRealFun_zero` idx 3: necessary (ℤ ordered through φ with φ 2 = -1/2, φ n = n otherwise: archimedean, 0 ≤ 1, not ordered; 2 ∈ ratLt 0, so embedRealFun 0 ≥ 2)
theorem c3_440 : ¬ drop0% Archimedean.embedRealFun_zero 3 := fun h => by
  have e := @h W1c3.WZ _ _ _ _ _ _
  have := W1c3.WZ_f0; rw [e] at this; norm_num at this

-- `Archimedean.embedRealFun_add` idx 3: necessary (same model: embedRealFun 0 ≥ 2, but additivity at 0 + 0 forces it to be 0)
theorem c3_441 : ¬ drop0% Archimedean.embedRealFun_add 3 := fun h => by
  have e := @h W1c3.WZ _ _ _ _ _ _ 0 0
  rw [add_zero] at e
  have := W1c3.WZ_f0; linarith

-- `Archimedean.ratLt_add` idx 5: removable (if 1 < 0, ratLt for 1 is the negative of ratLt for the unit -1 > 0, and negation is additive on sets)
theorem c3_450 : drop% Archimedean.ratLt_add 5 := by
  intro M _ _ _ _ _ _ x y
  rcases lt_or_gt_of_ne (NeZero.ne (1 : M)) with h1 | h1
  · exact W1c3.ratLt_add_neg h1 x y
  · haveI : ZeroLEOneClass M := ⟨h1.le⟩; exact Archimedean.ratLt_add x y

-- `Archimedean.ratLt'_add` idx 5: removable (as for ratLt_add)
theorem c3_451 : drop% Archimedean.ratLt'_add 5 := by
  intro M _ _ _ _ _ _ x y
  rcases lt_or_gt_of_ne (NeZero.ne (1 : M)) with h1 | h1
  · exact W1c3.ratLt'_add_neg h1 x y
  · haveI : ZeroLEOneClass M := ⟨h1.le⟩; exact Archimedean.ratLt'_add x y
