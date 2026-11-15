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

namespace W1c4
open SetRel
def U0 : SetRel Unit Unit := ∅
instance U0symm : U0.IsSymm := ⟨fun _ _ h => h⟩
def Ule : SetRel Bool Bool := {p | p.1 ≤ p.2}
instance Ulerefl : Ule.IsRefl := ⟨fun a => show a ≤ a from le_refl a⟩
def Rft : SetRel Bool Bool := {p | p = (false, true)}
def Rtf : SetRel Bool Bool := {p | p = (true, false)}
def Rne : SetRel Bool Bool := {p | p.1 ≠ p.2}
instance Rnesymm : Rne.IsSymm := ⟨fun a b (h : a ≠ b) => show b ≠ a from h.symm⟩
def R01 : SetRel (Fin 3) (Fin 3) := {p | p = (0, 1)}
def R01s : SetRel (Fin 3) (Fin 3) := {p | p = (0, 1) ∨ p = (1, 0)}
instance R01ssymm : R01s.IsSymm := ⟨fun a b (h : (a, b) = (0, 1) ∨ (a, b) = (1, 0)) =>
  show (b, a) = (0, 1) ∨ (b, a) = (1, 0) by simp only [Prod.mk.injEq] at h ⊢; tauto⟩
def SL : SetLike (Set Unit) Unit := ⟨id, Function.injective_id⟩
def leT : LE (Set Unit) := ⟨fun _ _ => True⟩
def revLE : LE (Set Unit) := ⟨fun a b => b ⊆ a⟩
def revTop : @OrderTop (Set Unit) revLE := @OrderTop.mk _ revLE ⟨∅⟩ (fun a => Set.empty_subset a)
def triv : Preorder (Set Unit) where
  le _ _ := True
  lt _ _ := False
  lt_iff_le_not_ge _ _ := ⟨False.elim, fun h => h.2 trivial⟩
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
def revPO : PartialOrder (Set Unit) := inferInstanceAs (PartialOrder (Set Unit)ᵒᵈ)
theorem revPO_lt : @LT.lt (Set Unit) revPO.toLT Set.univ ∅ :=
  show (∅ : Set Unit) < Set.univ from Set.empty_ssubset.mpr Set.univ_nonempty
theorem revPO_nlt : ¬ @LT.lt (Set Unit) revPO.toLT ∅ Set.univ :=
  show ¬ (Set.univ : Set Unit) < ∅ from fun h => h.2 (Set.empty_subset _)
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

/-- ℤ with the reversed order: a commutative ring with a linear order, not an ordered ring. -/
def RZ := ℤ
instance : CommRing RZ := inferInstanceAs (CommRing ℤ)
instance : LinearOrder RZ := inferInstanceAs (LinearOrder ℤᵒᵈ)
instance : Nontrivial RZ := inferInstanceAs (Nontrivial ℤ)
instance : IsOrderedRing Unit where
  add_le_add_left := by intros; exact le_rfl
  zero_le_one := le_rfl
  mul_le_mul_of_nonneg_left := by intros; exact le_rfl
  mul_le_mul_of_nonneg_right := by intros; exact le_rfl
/-- Order key on ℤ: 0 < 1 < -1 < 2 < -2 < …; every nonzero element is positive. -/
def keyK (n : ℤ) : ℕ := if 0 ≤ n then 2 * n.toNat else 2 * (-n).toNat + 1
theorem keyK_inj : Function.Injective keyK := by
  intro a b h; simp only [keyK] at h; split_ifs at h <;> omega
/-- ℤ ordered by keyK: commutative ring + linear order, 0 < 1 < -1 (abs 1 = -1). -/
def ZK := ℤ
instance : CommRing ZK := inferInstanceAs (CommRing ℤ)
instance : LinearOrder ZK := LinearOrder.lift' (fun n : ℤ => keyK n) keyK_inj
/-- Order key on ℤ swapping 2 and -2: 0 < 1 but 2 = 1 + 1 < 0. -/
def keyS (n : ℤ) : ℤ := if n = 2 then -2 else if n = -2 then 2 else n
theorem keyS_inj : Function.Injective keyS := by
  intro a b h; simp only [keyS] at h; split_ifs at h <;> omega
def ZS := ℤ
instance : AddCommGroup ZS := inferInstanceAs (AddCommGroup ℤ)
instance : LinearOrder ZS := LinearOrder.lift' (fun n : ℤ => keyS n) keyS_inj
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
/-- The setoid relating everything. -/
def topS (α : Sort*) : Setoid α := ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩
/-- The setoid given by equality. -/
def eqS (α : Sort*) : Setoid α := ⟨Eq, eq_equivalence⟩
/-- Option with `map` always `none`: a functor that is not lawful. -/
def BO : Type → Type := Option
instance : Functor BO where map _ _ := none
theorem BO_nl : ¬ LawfulFunctor BO := fun h => by
  have h2 : (none : Option Unit) = some () := h.id_map (α := Unit) (some ()); cases h2
/-- Bifunctor with `bimap` always `none`: not lawful. -/
def BF (α _β : Type) : Type := Option α
instance : Bifunctor BF where bimap _ _ _ := none
theorem BF_nl : ¬ LawfulBifunctor BF := fun h => by
  have h2 : (none : Option Unit) = some () := h.id_bimap (α := Unit) (β := Unit) (some ()); cases h2
theorem nCtR : ¬ Countable ℝ := fun h => Cardinal.not_countable_real (Set.countable_univ_iff.mpr h)
/-- The pairs over `true` in `Σ _ : Bool, Unit` form a one-point subtype. -/
def uq : Unique {ab : (_ : Bool) × Unit // ab.1 = true} :=
  ⟨⟨⟨⟨true, ()⟩, rfl⟩⟩, fun ⟨⟨a, u⟩, h⟩ => by cases a with | false => simp at h | true => rfl⟩
theorem unit_ne_bool : (Unit : Type) ≠ Bool := fun e => by
  have : Subsingleton Bool := e ▸ inferInstance
  exact absurd (Subsingleton.elim true false) (by decide)
end W1c4
open W1c4
universe u

-- `SetRel.IsCover.refl` idx 2
theorem c4_1 : ¬ drop0% SetRel.IsCover.refl 2 := fun h => by
  have := @h Unit ∅ Set.univ; simp [SetRel.IsCover] at this
-- `SetRel.IsCover.rfl` idx 2
theorem c4_2 : ¬ drop0% SetRel.IsCover.rfl 2 := fun h => by
  have := @h Unit ∅ Set.univ; simp [SetRel.IsCover] at this
-- `SetRel.IsCover.mono` idx 5
theorem c4_3 : ¬ drop0% SetRel.IsCover.mono 5 := fun h => by
  have := @h Unit Set.univ Set.univ Set.univ ∅ (by simp); simp at this
-- `SetRel.IsCover.mono` idx 6
theorem c4_4 : ¬ drop0% SetRel.IsCover.mono 6 := fun h => by
  have := @h Unit Set.univ Set.univ ∅ ∅ (by simp); simp at this
-- `SetRel.IsCover.anti` idx 5
theorem c4_5 : ¬ drop0% SetRel.IsCover.anti 5 := fun h => by
  have := @h Unit Set.univ Set.univ ∅ ∅ (by simp); simp at this
-- `SetRel.IsCover.mono_entourage` idx 5
theorem c4_6 : ¬ drop0% SetRel.IsCover.mono_entourage 5 := fun h => by
  have := @h Unit Set.univ ∅ Set.univ Set.univ (by simp); simp [SetRel.IsCover] at this
-- `SetRel.IsCover.union` idx 6
theorem c4_7 : ¬ drop0% SetRel.IsCover.union 6 := fun h => by
  have := @h Unit Set.univ Set.univ ∅ ∅ ∅ (by simp); simp at this
-- `SetRel.IsCover.union` idx 7
theorem c4_8 : ¬ drop0% SetRel.IsCover.union 7 := fun h => by
  have := @h Unit Set.univ ∅ Set.univ ∅ ∅ (by simp); simp at this
-- `SetRel.IsCover.of_maximal_isSeparated` idx 4
theorem c4_9 : ¬ drop0% SetRel.IsCover.of_maximal_isSeparated 4 := fun h => by
  have := @h Unit U0 Set.univ Set.univ _ ⟨⟨subset_rfl, fun _ _ _ _ _ h => h⟩, fun _ _ _ => Set.subset_univ _⟩
  simp [SetRel.IsCover, U0] at this
-- `SetRel.IsCover.of_maximal_isSeparated` idx 5
theorem c4_10 : ¬ drop0% SetRel.IsCover.of_maximal_isSeparated 5 := fun h => by
  have := @h Bool Ule Set.univ {false} _ ⟨⟨Set.subset_univ _, by simp⟩, fun t ht hsub => by
    intro b hb
    cases b
    · simp
    · exfalso
      have h2 := ht.2 (show false ∈ t from hsub rfl) hb (by simp)
      exact h2 (by simp [Ule])⟩
  have h3 := this (show true ∈ Set.univ from trivial)
  simp [Ule] at h3
  exact absurd h3 (by decide)
-- `SetRel.IsCover.of_maximal_isSeparated` idx 6
theorem c4_11 : ¬ drop0% SetRel.IsCover.of_maximal_isSeparated 6 := fun h => by
  have := @h Unit Set.univ Set.univ ∅ _ _; simp at this
-- `SetRel.IsSeparated.of_subsingleton` idx 3
theorem c4_12 : ¬ drop0% SetRel.IsSeparated.of_subsingleton 3 := fun h => by
  have := @h Bool Set.univ Set.univ
  exact this (Set.mem_univ false) (Set.mem_univ true) (by simp) trivial
-- `Set.Subsingleton.relIsSeparated` idx 3
theorem c4_13 : ¬ drop0% Set.Subsingleton.relIsSeparated 3 := fun h => by
  have := @h Bool Set.univ Set.univ
  exact this (Set.mem_univ false) (Set.mem_univ true) (by simp) trivial
-- `SetRel.IsSeparated.mono_left` idx 4
theorem c4_14 : ¬ drop0% SetRel.IsSeparated.mono_left 4 := fun h => by
  have := @h Bool Set.univ ∅ Set.univ (fun _ _ _ _ _ h => h)
  exact this (Set.mem_univ false) (Set.mem_univ true) (by simp) trivial
-- `SetRel.IsSeparated.mono_left` idx 5
theorem c4_15 : ¬ drop0% SetRel.IsSeparated.mono_left 5 := fun h => by
  have := @h Bool Set.univ Set.univ Set.univ subset_rfl
  exact this (Set.mem_univ false) (Set.mem_univ true) (by simp) trivial
-- `SetRel.IsSeparated.mono_right` idx 4
theorem c4_16 : ¬ drop0% SetRel.IsSeparated.mono_right 4 := fun h => by
  have := @h Bool Set.univ Set.univ ∅ (fun _ h => h.elim)
  exact this (Set.mem_univ false) (Set.mem_univ true) (by simp) trivial
-- `SetRel.IsSeparated.mono_right` idx 5
theorem c4_17 : ¬ drop0% SetRel.IsSeparated.mono_right 5 := fun h => by
  have := @h Bool Set.univ Set.univ Set.univ subset_rfl
  exact this (Set.mem_univ false) (Set.mem_univ true) (by simp) trivial
-- `SetRel.isSeparated_insert` idx 4
theorem c4_18 : ¬ drop0% SetRel.isSeparated_insert 4 := fun h => by
  have := (@h Bool Rtf {true} false).2 ⟨by simp, by simp [Rtf]⟩
  exact this (show true ∈ insert false {true} by simp) (show false ∈ insert false {true} by simp) (by simp) (by simp [Rtf])
-- `SetRel.isSeparated_insert_of_notMem` idx 4
theorem c4_19 : ¬ drop0% SetRel.isSeparated_insert_of_notMem 4 := fun h => by
  have := (@h Bool Rtf {true} false (by simp)).2 ⟨by simp, by simp [Rtf]⟩
  exact this (show true ∈ insert false {true} by simp) (show false ∈ insert false {true} by simp) (by simp) (by simp [Rtf])
-- `SetRel.IsSeparated.insert'` idx 4
theorem c4_20 : ¬ drop0% SetRel.IsSeparated.insert' 4 := fun h => by
  have := @h (Fin 3) R01 {0, 1} 2 (by simp [R01]) (by simp [R01])
  exact this (show (0 : Fin 3) ∈ insert 2 {0, 1} by simp) (show (1 : Fin 3) ∈ insert 2 {0, 1} by simp) (by decide) (by simp [R01])
-- `SetRel.IsSeparated.insert'` idx 5
theorem c4_21 : ¬ drop0% SetRel.IsSeparated.insert' 5 := fun h => by
  have := @h Bool Rft {true} false (by simp) (by simp [Rft])
  exact this (show false ∈ insert false {true} by simp) (show true ∈ insert false {true} by simp) (by simp) (by simp [Rft])
-- `SetRel.IsSeparated.insert'` idx 6
theorem c4_22 : ¬ drop0% SetRel.IsSeparated.insert' 6 := fun h => by
  have := @h Bool Rtf {true} false (by simp) (by simp [Rtf])
  exact this (show true ∈ insert false {true} by simp) (show false ∈ insert false {true} by simp) (by simp) (by simp [Rtf])
-- `SetRel.IsSeparated.insert` idx 4
theorem c4_23 : ¬ drop0% SetRel.IsSeparated.insert 4 := fun h => by
  have := @h Bool Rtf {true} false (by simp) (by simp [Rtf])
  exact this (show true ∈ insert false {true} by simp) (show false ∈ insert false {true} by simp) (by simp) (by simp [Rtf])
-- `SetRel.IsSeparated.insert` idx 5
theorem c4_24 : ¬ drop0% SetRel.IsSeparated.insert 5 := fun h => by
  have := @h (Fin 3) R01s {0, 1} 2 _ (by simp [R01s])
  exact this (show (0 : Fin 3) ∈ insert 2 {0, 1} by simp) (show (1 : Fin 3) ∈ insert 2 {0, 1} by simp) (by decide) (by simp [R01s])
-- `SetRel.IsSeparated.insert` idx 6
theorem c4_25 : ¬ drop0% SetRel.IsSeparated.insert 6 := fun h => by
  have := @h Bool Rne {true} false _ (by simp)
  exact this (show true ∈ insert false {true} by simp) (show false ∈ insert false {true} by simp) (by simp) (by simp [Rne])

-- `SetLike.ext'` idx 5
theorem c4_26 : ¬ drop0% SetLike.ext' 5 := fun h =>
  Set.empty_ne_univ (@h (Set Unit) Unit SL ∅ Set.univ)
-- `SetLike.ext` idx 5
theorem c4_27 : ¬ drop0% SetLike.ext 5 := fun h =>
  Set.empty_ne_univ (@h (Set Unit) Unit SL ∅ Set.univ)
-- `SetLike.mem_of_subset` idx 5
theorem c4_28 : ¬ drop0% SetLike.mem_of_subset 5 := fun h =>
  (@h (Set Unit) Unit SL ∅ Set.univ () trivial : () ∈ (∅ : Set Unit))
-- `SetLike.mem_of_subset` idx 7
theorem c4_29 : ¬ drop0% SetLike.mem_of_subset 7 := fun h =>
  (@h (Set Unit) Unit SL ∅ ∅ (fun _ h => h) () : () ∈ (∅ : Set Unit))
-- `SetLike.mem_of_subsingleton` idx 3
theorem c4_30 : ¬ drop0% SetLike.mem_of_subsingleton 3 := fun h =>
  absurd (@h (Set Bool) Bool ⟨id, Function.injective_id⟩ {true} ⟨⟨true, rfl⟩⟩ false : false ∈ ({true} : Set Bool)) (by simp)
-- `SetLike.mem_of_subsingleton` idx 5
theorem c4_31 : ¬ drop0% SetLike.mem_of_subsingleton 5 := fun h =>
  (@h (Set Unit) Unit SL inferInstance ∅ () : () ∈ (∅ : Set Unit))
-- `SetLike.exists_notMem_of_ne_top` idx 6
theorem c4_32 : ¬ drop0% SetLike.exists_notMem_of_ne_top 6 := fun h => by
  obtain ⟨b, hb⟩ := @h (Set Unit) Unit SL _ _ Set.univ rfl
  exact hb trivial
-- `SetLike.exists_notMem_of_ne_top` idx 7
theorem c4_33 : ¬ drop0% SetLike.exists_notMem_of_ne_top 7 := fun h => by
  obtain ⟨b, hb⟩ := @h (Set Unit) Unit SL revLE revTop Set.univ
    (show (Set.univ : Set Unit) ≠ ∅ from Set.univ_nonempty.ne_empty)
  exact hb trivial
-- `SetLike.exists_not_mem_of_ne_top` idx 6
theorem c4_34 : ¬ drop0% SetLike.exists_not_mem_of_ne_top 6 := fun h => by
  obtain ⟨b, hb⟩ := @h (Set Unit) Unit SL _ _ Set.univ rfl
  exact hb trivial
-- `SetLike.exists_not_mem_of_ne_top` idx 7
theorem c4_35 : ¬ drop0% SetLike.exists_not_mem_of_ne_top 7 := fun h => by
  obtain ⟨b, hb⟩ := @h (Set Unit) Unit SL revLE revTop Set.univ
    (show (Set.univ : Set Unit) ≠ ∅ from Set.univ_nonempty.ne_empty)
  exact hb trivial
-- `IsConcreteLE.le_iff` idx 4
theorem c4_36 : ¬ drop0% IsConcreteLE.le_iff 4 := fun h =>
  ((@h (Set Unit) Unit _ leT Set.univ ∅).1 trivial (trivial : () ∈ Set.univ) : () ∈ (∅ : Set Unit))
-- `mem_of_le_of_mem` idx 4
theorem c4_37 : ¬ drop0% mem_of_le_of_mem 4 := fun h =>
  ((@h (Set Unit) Unit _ leT Set.univ ∅) trivial (trivial : () ∈ Set.univ) : () ∈ (∅ : Set Unit))
-- `mem_of_le_of_mem` idx 7
theorem c4_38 : ¬ drop0% mem_of_le_of_mem 7 := fun h =>
  ((@h (Set Unit) Unit _ _ _ Set.univ ∅) (show () ∈ (Set.univ : Set Unit) from trivial) : () ∈ (∅ : Set Unit))
-- `mem_of_le_of_mem` idx 9
theorem c4_39 : ¬ drop0% mem_of_le_of_mem 9 := fun h => by
  have h2 : ∀ ⦃x : Unit⦄, x ∈ (∅ : Set Unit) := @h (Set Unit) Unit _ _ _ ∅ ∅ le_rfl
  exact h2 (x := ())
-- `IsConcreteLE.not_le_iff_exists` idx 4
theorem c4_40 : ¬ drop0% IsConcreteLE.not_le_iff_exists 4 := fun h => by
  have := (@h (Set Unit) Unit _ leT Set.univ ∅).2 ⟨(), trivial, fun h => h⟩
  exact this trivial
-- `IsConcreteLE.lt_iff_le_and_exists` idx 4
theorem c4_41 : ¬ drop0% IsConcreteLE.lt_iff_le_and_exists 4 := fun h => by
  have := (@h (Set Unit) Unit _ triv ∅ Set.univ).2 ⟨trivial, (), trivial, fun h => h⟩
  exact this
-- `IsConcreteLE.exists_of_lt` idx 4
theorem c4_42 : ¬ drop0% IsConcreteLE.exists_of_lt 4 := fun h => by
  obtain ⟨x, hx, -⟩ := @h (Set Unit) Unit _ revPO.toPreorder Set.univ ∅ revPO_lt
  exact hx
-- `IsConcreteLE.exists_of_lt` idx 7
theorem c4_43 : ¬ drop0% IsConcreteLE.exists_of_lt 7 := fun h => by
  obtain ⟨x, hx, -⟩ := @h (Set Unit) Unit _ _ _ ∅ ∅
  exact hx
-- `SetLike.le_def` idx 4
theorem c4_44 : ¬ drop0% SetLike.le_def 4 := fun h =>
  ((@h (Set Unit) Unit _ leT Set.univ ∅).1 trivial (trivial : () ∈ Set.univ) : () ∈ (∅ : Set Unit))
-- `SetLike.not_le_iff_exists` idx 4
theorem c4_45 : ¬ drop0% SetLike.not_le_iff_exists 4 := fun h => by
  have := (@h (Set Unit) Unit _ leT Set.univ ∅).2 ⟨(), trivial, fun h => h⟩
  exact this trivial
-- `SetLike.lt_iff_le_and_exists` idx 4
theorem c4_46 : ¬ drop0% SetLike.lt_iff_le_and_exists 4 := fun h => by
  have := (@h (Set Unit) Unit _ triv ∅ Set.univ).2 ⟨trivial, (), trivial, fun h => h⟩
  exact this
-- `SetLike.exists_of_lt` idx 4
theorem c4_47 : ¬ drop0% SetLike.exists_of_lt 4 := fun h => by
  obtain ⟨x, hx, -⟩ := @h (Set Unit) Unit _ revPO.toPreorder Set.univ ∅ revPO_lt
  exact hx
-- `SetLike.exists_of_lt` idx 7
theorem c4_48 : ¬ drop0% SetLike.exists_of_lt 7 := fun h => by
  obtain ⟨x, hx, -⟩ := @h (Set Unit) Unit _ _ _ ∅ ∅
  exact hx
-- `SetLike.coe_subset_coe` idx 4
theorem c4_49 : ¬ drop0% SetLike.coe_subset_coe 4 := fun h =>
  ((@h (Set Unit) Unit SL leT Set.univ ∅).2 trivial (trivial : () ∈ Set.univ) : () ∈ (∅ : Set Unit))
-- `SetLike.coe_mono` idx 4
theorem c4_50 : ¬ drop0% SetLike.coe_mono 4 := fun h =>
  ((@h (Set Unit) Unit SL triv Set.univ ∅ trivial) (trivial : () ∈ Set.univ) : () ∈ (∅ : Set Unit))
-- `SetLike.coe_ssubset_coe` idx 4
theorem c4_51 : ¬ drop0% SetLike.coe_ssubset_coe 4 := fun h =>
  revPO_nlt ((@h (Set Unit) Unit SL revPO ∅ Set.univ).1 (Set.empty_ssubset.mpr Set.univ_nonempty))
-- `SetLike.coe_strictMono` idx 4
theorem c4_52 : ¬ drop0% SetLike.coe_strictMono 4 := fun h =>
  (@h (Set Unit) Unit SL revPO Set.univ ∅ revPO_lt).2 (Set.empty_subset _)
-- `SetLike.mem_mk_set` idx 3
theorem c4_53 : ¬ indep0% SetLike.mem_mk_set 3 := fun h =>
  @h Unit (fun _ => False) ∅ ()
-- `SetLike.mem_mk` idx 5
theorem c4_54 : ¬ indep0% SetLike.mem_mk 5 := fun h =>
  @h Unit (Finset Unit) _ (fun _ => False) ∅ ()

-- `sign_intCast` idx 3
theorem c4_55 : ¬ drop0% sign_intCast 3 := fun h => by
  have := h (α := RZ) 1; revert this; decide +kernel
-- `sign_mul` idx 3
theorem c4_56 : ¬ drop0% sign_mul 3 := fun h => by
  have := h (α := RZ) 1 1; revert this; decide +kernel
-- `sign_mul_abs` idx 3
theorem c4_57 : ¬ drop0% sign_mul_abs 3 := fun h => by
  have := h (α := ZK) 1; revert this; decide +kernel
-- `abs_mul_sign` idx 3
theorem c4_58 : ¬ drop0% abs_mul_sign 3 := fun h => by
  have := h (α := ZK) 1; revert this; decide +kernel
-- `sign_mul_self` idx 3
theorem c4_59 : ¬ drop0% sign_mul_self 3 := fun h => by
  have := h (α := ZK) 1; revert this; decide +kernel
-- `self_mul_sign` idx 3
theorem c4_60 : ¬ drop0% self_mul_sign 3 := fun h => by
  have := h (α := ZK) 1; revert this; decide +kernel
-- `sign_sum` idx 3
theorem c4_61 : ¬ drop0% sign_sum 3 := fun h => by
  have := h (α := ZS) (s := (Finset.univ : Finset Bool)) (f := fun _ => (show ZS from (1 : ℤ))) Finset.univ_nonempty 1
    (fun _ _ => by decide +kernel)
  revert this; decide +kernel
-- `sign_sum` idx 9
theorem c4_62 : ¬ drop0% sign_sum 9 := fun h => by
  have := h (α := ℤ) (s := (Finset.univ : Finset Unit)) (f := fun _ => 0) Finset.univ_nonempty 1
  simp at this
-- `exists_signed_sum'` idx 1
theorem c4_63 : ¬ drop0% exists_signed_sum' 1 := fun h => by
  obtain ⟨β, _, sgn, g, -, hc, -⟩ := h (α := Empty) ∅ (fun _ => 0) 1 (by simp)
  have : Nonempty β := Fintype.card_pos_iff.mp (by omega)
  exact (g this.some).elim
-- `exists_signed_sum'` idx 6
theorem c4_64 : ¬ drop0% exists_signed_sum' 6 := fun h => by
  obtain ⟨β, _, sgn, g, -, hc, hf⟩ := h (α := Unit) Finset.univ (fun _ => 1) 0
  have : IsEmpty β := Fintype.card_eq_zero_iff.mp hc
  have := hf () (Finset.mem_univ _)
  simp at this
-- `SignType.map_cast'` idx 9
theorem c4_65 : ¬ drop0% SignType.map_cast' 9 := fun h => by
  have := h (α := ℤ) (β := ℤ) (fun x => if x = 1 then 5 else x) (by decide) (by decide) 1
  revert this; decide
-- `SignType.map_cast'` idx 10
theorem c4_66 : ¬ drop0% SignType.map_cast' 10 := fun h => by
  have := h (α := ℤ) (β := ℤ) (fun x => if x = 0 then 5 else x) (by decide) (by decide) 0
  revert this; decide
-- `SignType.map_cast'` idx 11
theorem c4_67 : ¬ drop0% SignType.map_cast' 11 := fun h => by
  have := h (α := ℤ) (β := ℤ) (fun x => if x = -1 then 5 else x) (by decide) (by decide) (-1)
  revert this; decide
-- `SignType.map_cast` idx 7
theorem c4_68 : ¬ drop0% SignType.map_cast 7 := fun h => by
  have := h (α := ℤ) (β := ℤ) (F := OneHom ℤ ℤ) ⟨fun x => if x = 0 then 5 else x, rfl⟩ 0
  revert this; decide
-- `SignType.map_cast` idx 8
theorem c4_69 : ¬ drop0% SignType.map_cast 8 := fun h => by
  have := h (α := ℤ) (β := ℤ) (F := ℤ →+ ℤ) (AddMonoidHom.mulLeft 2) 1
  revert this; simp
-- `StrictMono.sign_comp` idx 9
theorem c4_70 : ¬ drop0% StrictMono.sign_comp 9 := fun h => by
  have := h (α := ℤ) (β := ℤ) (F := Equiv.Perm ℤ) (f := Equiv.addRight 1)
    (fun a b hab => by simpa using hab) 0
  revert this; decide
-- `StrictMono.sign_comp` idx 11
theorem c4_71 : ¬ drop0% StrictMono.sign_comp 11 := fun h => by
  have := h (α := ℤ) (β := ℤ) (F := ℤ →+ ℤ) (f := AddMonoidHom.mulLeft (-1)) 1
  revert this; simp
-- `sign_one` idx 3
theorem c4_72 : ¬ drop0% sign_one 3 := fun h => by
  have := h (α := RZ); revert this; decide +kernel
-- `sign_one` idx 5
theorem c4_73 : ¬ drop0% sign_one 5 := fun h => by
  have := h (α := Unit); revert this; decide
-- `TwoPointing.instNonemptyOfNontrivial` idx 1
theorem c4_74 : ¬ drop0% TwoPointing.instNonemptyOfNontrivial 1 := fun h => by
  obtain ⟨p⟩ := h (α := Unit); exact p.fst_ne_snd (Subsingleton.elim _ _)
-- `TwoPointing.pi_fst` idx 3
theorem c4_75 : ¬ indep0% TwoPointing.pi_fst 3 := fun h => by
  obtain ⟨x⟩ := h Empty TwoPointing.bool; exact x.elim
-- `TwoPointing.pi_snd` idx 3
theorem c4_76 : ¬ indep0% TwoPointing.pi_snd 3 := fun h => by
  obtain ⟨x⟩ := h Empty TwoPointing.bool; exact x.elim
-- `Unique.ext` idx 3: removable, `Unique α` is a subsingleton
theorem c4_77 : drop% Unique.ext 3 := fun {α} x y => Subsingleton.elim x y
-- `nonempty_unique` idx 2
theorem c4_78 : ¬ drop0% nonempty_unique 2 := fun h => by
  obtain ⟨u⟩ := h False; exact u.default
-- `UnivLE.small` idx 0
theorem c4_79 : ¬ dropL% UnivLE.small 0 [1, 0] := fun h => not_small_type.{0, 0} (h Type)
-- `Small.trans_univLE` idx 1
theorem c4_80 : ¬ dropL% Small.trans_univLE 1 [0, 0, 1] := fun h => not_small_type.{0, 0} (h Type)
-- `Small.trans_univLE` idx 2
theorem c4_81 : ¬ dropL% Small.trans_univLE 2 [1, 0, 1] := fun h => not_small_type.{0, 0} (h Type)
-- `UnivLE.trans` idx 0
theorem c4_82 : ¬ dropL% UnivLE.trans 0 [1, 0, 0] := fun h => not_small_type.{0, 0} ((h).small Type)
-- `UnivLE.trans` idx 1
theorem c4_83 : ¬ dropL% UnivLE.trans 1 [1, 1, 0] := fun h => not_small_type.{0, 0} ((h).small Type)
-- `UnivLE.succ` idx 0
theorem c4_84 : ¬ dropL% UnivLE.succ 0 [2, 0] := fun h => not_small_type.{1, 0} (h.small (Type 1))
-- `univLE_of_max` idx 0
theorem c4_85 : ¬ dropL% univLE_of_max 0 [1, 0] := fun h => not_small_type.{0, 0} (h.small Type)

-- `Set.embeddingOfSubset_apply_coe` idx 3
theorem c4_86 : ¬ indep0% Set.embeddingOfSubset_apply_coe 3 := fun h =>
  (h (Set.univ : Set Unit) ∅ ⟨(), trivial⟩ (trivial : () ∈ Set.univ) : () ∈ (∅ : Set Unit))
-- `subtypeOrEquiv_apply` idx 4
theorem c4_87 : ¬ indep0% subtypeOrEquiv_apply 4 := fun h =>
  (h (fun _ : Unit => True) (fun _ => True) ⟨(), .inl trivial⟩) le_rfl le_rfl () trivial
-- `subtypeOrEquiv_symm_inl` idx 4
theorem c4_88 : ¬ indep0% subtypeOrEquiv_symm_inl 4 := fun h =>
  (h (fun _ : Unit => True) (fun _ => True) ⟨(), trivial⟩) le_rfl le_rfl () trivial
-- `subtypeOrEquiv_symm_inr` idx 4
theorem c4_89 : ¬ indep0% subtypeOrEquiv_symm_inr 4 := fun h =>
  (h (fun _ : Unit => True) (fun _ => True) ⟨(), trivial⟩) le_rfl le_rfl () trivial
-- `Function.Embedding.sigmaSet_apply` idx 3
theorem c4_90 : ¬ indep0% Function.Embedding.sigmaSet_apply 3 := fun h => by
  have := @h Unit Bool (fun _ => Set.univ) ⟨true, (), trivial⟩ true false (by decide)
  simp [Function.onFun] at this
-- `Function.Embedding.coe_sigmaSet` idx 3
theorem c4_91 : ¬ indep0% Function.Embedding.coe_sigmaSet 3 := fun h => by
  have := @h Unit Bool (fun _ => Set.univ) true false (by decide)
  simp [Function.onFun] at this
-- `Function.Embedding.sigmaSet_preimage` idx 3
theorem c4_92 : ¬ indep0% Function.Embedding.sigmaSet_preimage 3 := fun h => by
  have := @h Unit Bool (fun _ => Set.univ) true ∅ true false (by decide)
  simp [Function.onFun] at this
-- `Function.Embedding.sigmaSet_range` idx 3
theorem c4_93 : ¬ indep0% Function.Embedding.sigmaSet_range 3 := fun h => by
  have := @h Unit Bool (fun _ => Set.univ) true false (by decide)
  simp [Function.onFun] at this
-- `nonempty_encodable` idx 1
theorem c4_94 : ¬ drop0% nonempty_encodable 1 := fun h => by
  obtain ⟨e⟩ := h ℝ; exact nCtR (@Encodable.countable ℝ e)
-- `ULower.ext` idx 4
theorem c4_95 : ¬ drop0% ULower.ext 4 := fun h =>
  absurd ((ULower.equiv Bool).injective (@h Bool _ ((ULower.equiv Bool) true) ((ULower.equiv Bool) false))) (by decide)
-- `Encodable.axiom_of_choice` idx 5
theorem c4_96 : ¬ drop0% Encodable.axiom_of_choice 5 := fun h => by
  obtain ⟨f, hf⟩ := h (α := Unit) (β := fun _ => Unit) (R := fun _ _ => False); exact hf ()
-- `Directed.sequence_mono_nat` idx 6
theorem c4_97 : ¬ indep0% Directed.sequence_mono_nat 6 := fun h => by
  obtain ⟨z, hz, -⟩ := h (α := Bool) (β := Unit) (r := fun _ _ => False) (f := fun _ => ()) 0 true true
  exact hz
-- `Directed.rel_sequence` idx 6
theorem c4_98 : ¬ indep0% Directed.rel_sequence 6 := fun h => by
  obtain ⟨z, hz, -⟩ := h (α := Bool) (β := Unit) (r := fun _ _ => False) (f := fun _ => ()) true true true
  exact hz
-- `Directed.sequence_mono` idx 6
theorem c4_99 : ¬ indep0% Directed.sequence_mono 6 := fun h => by
  obtain ⟨z, h1, h2⟩ := h (α := Unit ⊕ Unit) (β := Unit ⊕ Unit) (f := id) (Sum.inl ()) (Sum.inr ())
  cases z <;> simp at h1 h2
-- `Directed.le_sequence` idx 6
theorem c4_100 : ¬ indep0% Directed.le_sequence 6 := fun h => by
  obtain ⟨z, h1, h2⟩ := h (α := Unit ⊕ Unit) (β := Unit ⊕ Unit) (f := id) (Sum.inl ()) (Sum.inl ()) (Sum.inr ())
  cases z <;> simp at h1 h2
-- `Directed.sequence_anti` idx 6
theorem c4_101 : ¬ indep0% Directed.sequence_anti 6 := fun h => by
  obtain ⟨z, h1, h2⟩ := h (α := Unit ⊕ Unit) (β := Unit ⊕ Unit) (f := id) (Sum.inl ()) (Sum.inr ())
  cases z <;> simp at h1 h2
-- `Directed.sequence_le` idx 6
theorem c4_102 : ¬ indep0% Directed.sequence_le 6 := fun h => by
  obtain ⟨z, h1, h2⟩ := h (α := Unit ⊕ Unit) (β := Unit ⊕ Unit) (f := id) (Sum.inl ()) (Sum.inl ()) (Sum.inr ())
  cases z <;> simp at h1 h2
-- `Encodable.iUnion_decode₂_cases` idx 5
theorem c4_103 : ¬ drop0% Encodable.iUnion_decode₂_cases 5 := fun h => by
  have := h (α := Unit) (β := Empty) (f := Empty.elim) (C := fun s => s.Nonempty) (fun b => b.elim) (n := 0)
  simp at this
-- `Encodable.iUnion_decode₂_cases` idx 6
theorem c4_104 : ¬ drop0% Encodable.iUnion_decode₂_cases 6 := fun h => by
  have := h (α := Unit) (β := Unit) (f := fun _ => Set.univ) (C := fun s => s = ∅) rfl (n := 0)
  have hm : () ∈ ⋃ b ∈ Encodable.decode₂ Unit 0, (fun _ : Unit => (Set.univ : Set Unit)) b :=
    Set.mem_iUnion₂.mpr ⟨(), Encodable.mem_decode₂.mpr rfl, trivial⟩
  rw [this] at hm; exact hm
-- `Encodable.iUnion_decode₂_disjoint_on` idx 4
theorem c4_105 : ¬ drop0% Encodable.iUnion_decode₂_disjoint_on 4 := fun h => by
  have := h (α := Unit) (β := Bool) (f := fun _ => Set.univ) (i := 0) (j := 1) (by decide)
  have h0 : () ∈ ⋃ b ∈ Encodable.decode₂ Bool 0, (Set.univ : Set Unit) :=
    Set.mem_iUnion₂.mpr ⟨false, Encodable.mem_decode₂.mpr rfl, trivial⟩
  have h1 : () ∈ ⋃ b ∈ Encodable.decode₂ Bool 1, (Set.univ : Set Unit) :=
    Set.mem_iUnion₂.mpr ⟨true, Encodable.mem_decode₂.mpr rfl, trivial⟩
  exact Set.disjoint_left.mp this h0 h1
-- `Encodable.List.Vector.countable` idx 1
theorem c4_106 : ¬ drop0% Encodable.List.Vector.countable 1 := fun h =>
  nCtR (@Function.Injective.countable _ _ (@h ℝ 1) (fun x : ℝ => (⟨[x], rfl⟩ : List.Vector ℝ 1))
    (fun a b e => by simpa using congrArg Subtype.val e))
-- `Array.countable` idx 1
theorem c4_107 : ¬ drop0% Array.countable 1 := fun h =>
  nCtR (@Function.Injective.countable _ _ (@h ℝ) (fun x : ℝ => #[x]) (fun a b e => by simpa using e))
-- `List.countable` idx 1
theorem c4_108 : ¬ drop0% List.countable 1 := fun h =>
  nCtR (@Function.Injective.countable _ _ (@h ℝ) (fun x : ℝ => [x]) (fun a b e => by simpa using e))
-- `Multiset.countable` idx 1
theorem c4_109 : ¬ drop0% Multiset.countable 1 := fun h =>
  nCtR (@Function.Injective.countable _ _ (@h ℝ) (fun x : ℝ => ({x} : Multiset ℝ)) (fun a b e => by simpa using e))
-- `Finset.countable` idx 1
theorem c4_110 : ¬ drop0% Finset.countable 1 := fun h =>
  nCtR (@Function.Injective.countable _ _ (@h ℝ) (fun x : ℝ => ({x} : Finset ℝ)) (fun a b e => by simpa using e))

-- `Equiv.Perm.subtypeCongr.left_apply` idx 6
theorem c4_111 : ¬ indep0% Equiv.Perm.subtypeCongr.left_apply 6 := fun h =>
  h (ε := Unit) (p := fun _ => False) (Equiv.refl _) (Equiv.refl _) (a := ())
-- `Equiv.subtypeSubtypeEquivSubtype_apply_coe` idx 3
theorem c4_112 : ¬ indep0% Equiv.subtypeSubtypeEquivSubtype_apply_coe 3 := fun h =>
  absurd (h (α := Bool) (p := (· = true)) (q := fun _ => True) ⟨⟨true, rfl⟩, trivial⟩ (x := false) trivial) (by decide)
-- `Equiv.sigmaSigmaSubtype_apply` idx 7
theorem c4_113 : ¬ indep0% Equiv.sigmaSigmaSubtype_apply 7 := fun h =>
  absurd (h (α := Bool) (β := fun _ => Unit) (γ := fun _ _ => Unit) (fun ab => ab.1 = true) (uniq := uq)
    (a := false) (b := ())) (by decide)
-- `Equiv.sigmaSigmaSubtype_symm_apply` idx 8
theorem c4_114 : ¬ indep0% Equiv.sigmaSigmaSubtype_symm_apply 8 := fun h =>
  absurd (h (α := Bool) (β := fun _ => Unit) (γ := fun _ _ => Unit) (fun ab => ab.1 = true) (uniq := uq)
    (a := false) (b := ()) ()) (by decide)
-- `Equiv.Perm.extendDomain_apply_subtype` idx 7
theorem c4_115 : ¬ indep0% Equiv.Perm.extendDomain_apply_subtype 7 := fun h =>
  h (α' := Empty) (β' := Unit) (Equiv.refl _) (p := fun _ => False) (Equiv.equivOfIsEmpty _ _) (b := ())
-- `Equiv.subtypeQuotientEquivQuotientSubtype_mk` idx 5
theorem c4_116 : ¬ indep0% Equiv.subtypeQuotientEquivQuotientSubtype_mk 5 := fun h =>
  ((h (α := True) (fun _ => False) (s₁ := topS _) (s₂ := topS _) (fun _ => True)
    (fun x _ => x.2.elim) trivial trivial) trivial).2 trivial
-- `Equiv.subtypeQuotientEquivQuotientSubtype_mk` idx 6
theorem c4_117 : ¬ indepL% Equiv.subtypeQuotientEquivQuotientSubtype_mk 6 [1] := fun h => by
  have := ((h (α := Bool) (fun _ => True) (s₁ := topS _) (s₂ := eqS _) (fun _ => True)
    (fun _ => Iff.rfl) true trivial) ⟨true, trivial⟩ ⟨false, trivial⟩).2 trivial
  exact absurd (congrArg Subtype.val this) (by decide)
-- `Equiv.subtypeQuotientEquivQuotientSubtype_mk` idx 8
theorem c4_118 : ¬ indep0% Equiv.subtypeQuotientEquivQuotientSubtype_mk 8 := fun h =>
  h (α := True) (fun _ => False) (s₁ := topS _) (s₂ := topS _) (fun _ => False)
    (fun _ => Iff.rfl) (fun x _ => x.2.elim) trivial
-- `Equiv.subtypeQuotientEquivQuotientSubtype_symm_mk` idx 5
theorem c4_119 : ¬ indep0% Equiv.subtypeQuotientEquivQuotientSubtype_symm_mk 5 := fun h =>
  ((h (α := True) (fun _ => True) (s₁ := topS _) (s₂ := topS _) (fun _ => False)
    (fun _ _ => Iff.rfl) ⟨trivial, trivial⟩) trivial).1 trivial
-- `Equiv.subtypeQuotientEquivQuotientSubtype_symm_mk` idx 6
theorem c4_120 : ¬ indepL% Equiv.subtypeQuotientEquivQuotientSubtype_symm_mk 6 [1] := fun h => by
  have := ((h (α := Bool) (fun _ => True) (s₁ := topS _) (s₂ := eqS _) (fun _ => True)
    (fun _ => Iff.rfl) ⟨true, trivial⟩) ⟨true, trivial⟩ ⟨false, trivial⟩).2 trivial
  exact absurd (congrArg Subtype.val this) (by decide)
-- `Equiv.instNontrivialPerm` idx 1
theorem c4_121 : ¬ drop0% Equiv.instNontrivialPerm 1 := fun h => by
  obtain ⟨x, y, hxy⟩ := (h Unit).exists_pair_ne; exact hxy (Subsingleton.elim _ _)
-- `Equiv.image_swap_of_mem_of_notMem` idx 6
theorem c4_122 : ¬ drop0% Equiv.image_swap_of_mem_of_notMem 6 := fun h => by
  have := Set.ext_iff.mp (h (s := (Set.univ : Set Bool)) (i := true) (j := false) trivial) true
  simp at this
-- `Function.Involutive.coe_toPerm` idx 2
theorem c4_123 : ¬ indepL% Function.Involutive.coe_toPerm 2 [1] := fun h =>
  absurd (h (α := Bool) (f := fun _ => true) false) (by decide)
-- `Function.Involutive.toPerm_symm` idx 2
theorem c4_124 : ¬ indepL% Function.Involutive.toPerm_symm 2 [1] := fun h =>
  absurd (h (α := Bool) (f := fun _ => true) false) (by decide)
-- `Function.Involutive.toPerm_involutive` idx 2
theorem c4_125 : ¬ indepL% Function.Involutive.toPerm_involutive 2 [1] := fun h =>
  absurd (h (α := Bool) (f := fun _ => true) false) (by decide)
-- `Function.Involutive.symm_eq_self_of_involutive` idx 2
theorem c4_126 : ¬ dropL% Function.Involutive.symm_eq_self_of_involutive 2 [1] := fun h => by
  have := congrArg (fun g => g 0) (h (Equiv.addRight (1 : ℤ)))
  simp at this
-- `Equiv.piCongrSet_symm_apply` idx 4
theorem c4_127 : ¬ indep0% Equiv.piCongrSet_symm_apply 4 := fun h =>
  Set.empty_ne_univ (h (α := Unit) (W := fun _ => True) (s := Set.univ) (t := ∅) (fun _ => trivial) ⟨(), trivial⟩).symm
-- `Equiv.piCongrSet_apply` idx 4
theorem c4_128 : ¬ indep0% Equiv.piCongrSet_apply 4 := fun h =>
  Set.empty_ne_univ (h (α := Unit) (W := fun _ => True) (s := ∅) (t := Set.univ) (fun _ => trivial) ⟨(), trivial⟩)
-- `Function.Injective.swap_comp` idx 5
theorem c4_129 : ¬ dropL% Function.Injective.swap_comp 5 [1, 1] := fun h => by
  have := congrFun (h (f := fun i : Fin 3 => decide (i = 0)) 0 1) 2
  revert this; decide
-- `Equiv.coe_fn_mk` idx 4
theorem c4_130 : ¬ indepL% Equiv.coe_fn_mk 4 [1, 1] := fun h =>
  absurd (h (α := Bool) (β := Unit) (fun _ => ()) (fun _ => true) (fun _ => rfl) false) (by decide)
-- `Equiv.coe_fn_mk` idx 5
theorem c4_131 : ¬ indepL% Equiv.coe_fn_mk 5 [1, 1] := fun h =>
  absurd (h (α := Unit) (β := Bool) (fun _ => true) (fun _ => ()) (fun _ => rfl) false) (by decide)
-- `Equiv.symm_mk` idx 4
theorem c4_132 : ¬ indepL% Equiv.symm_mk 4 [1, 1] := fun h =>
  absurd (h (α := Bool) (β := Unit) (fun _ => ()) (fun _ => true) (fun _ => rfl) false) (by decide)
-- `Equiv.symm_mk` idx 5
theorem c4_133 : ¬ indepL% Equiv.symm_mk 5 [1, 1] := fun h =>
  absurd (h (α := Unit) (β := Bool) (fun _ => true) (fun _ => ()) (fun _ => rfl) false) (by decide)
-- `Equiv.coe_fn_symm_mk` idx 4
theorem c4_134 : ¬ indepL% Equiv.coe_fn_symm_mk 4 [1, 1] := fun h =>
  absurd (h (α := Bool) (β := Unit) (fun _ => ()) (fun _ => true) (fun _ => rfl) false) (by decide)
-- `Equiv.coe_fn_symm_mk` idx 5
theorem c4_135 : ¬ indepL% Equiv.coe_fn_symm_mk 5 [1, 1] := fun h =>
  absurd (h (α := Unit) (β := Bool) (fun _ => true) (fun _ => ()) (fun _ => rfl) false) (by decide)
-- `Equiv.nontrivial` idx 3
theorem c4_136 : ¬ drop0% Equiv.nontrivial 3 := fun h => by
  obtain ⟨x, y, hxy⟩ := (h (Equiv.refl Unit)).exists_pair_ne; exact hxy (Subsingleton.elim _ _)
-- `Equiv.nonempty` idx 3
theorem c4_137 : ¬ drop0% Equiv.nonempty 3 := fun h => by
  obtain ⟨x⟩ := h (Equiv.refl False); exact x
-- `Equiv.cast_apply` idx 2
theorem c4_138 : ¬ indep0% Equiv.cast_apply 2 := fun h =>
  cast (h (α := True) (β := False) trivial) trivial
-- `Equiv.cast_symm` idx 2
theorem c4_139 : ¬ indep0% Equiv.cast_symm 2 := fun h =>
  cast (h (α := True) (β := False)) trivial
-- `Equiv.cast_trans` idx 3
theorem c4_140 : ¬ indep0% Equiv.cast_trans 3 := fun h =>
  cast (h (α := True) (β := False) (γ := False) rfl) trivial
-- `Equiv.cast_trans` idx 4
theorem c4_141 : ¬ indep0% Equiv.cast_trans 4 := fun h =>
  cast (h (α := True) (β := True) (γ := False) rfl) trivial
-- `Equiv.cast_eq_iff_heq` idx 2
theorem c4_142 : ¬ indepL% Equiv.cast_eq_iff_heq 2 [1] := fun h =>
  unit_ne_bool (h (α := Unit) (β := Bool) (a := ()) (b := true))
-- `Equiv.forall₂_congr` idx 8
theorem c4_143 : ¬ drop0% Equiv.forall₂_congr 8 := fun h =>
  (h (p := fun _ _ => True) (q := fun _ _ => False) (Equiv.refl True) (Equiv.refl True)).1
    (fun _ _ => trivial) trivial trivial
-- `Equiv.forall₂_congr'` idx 8
theorem c4_144 : ¬ drop0% Equiv.forall₂_congr' 8 := fun h =>
  (h (p := fun _ _ => True) (q := fun _ _ => False) (Equiv.refl True) (Equiv.refl True)).1
    (fun _ _ => trivial) trivial trivial
-- `Equiv.forall₃_congr` idx 11
theorem c4_145 : ¬ drop0% Equiv.forall₃_congr 11 := fun h =>
  (h (p := fun _ _ _ => True) (q := fun _ _ _ => False) (Equiv.refl True) (Equiv.refl True) (Equiv.refl True)).1
    (fun _ _ _ => trivial) trivial trivial trivial
-- `Equiv.forall₃_congr'` idx 11
theorem c4_146 : ¬ drop0% Equiv.forall₃_congr' 11 := fun h =>
  (h (p := fun _ _ _ => True) (q := fun _ _ _ => False) (Equiv.refl True) (Equiv.refl True) (Equiv.refl True)).1
    (fun _ _ _ => trivial) trivial trivial trivial
-- `Quotient.congr_mk` idx 5
theorem c4_147 : ¬ indepL% Quotient.congr_mk 5 [1, 1] := fun h =>
  absurd (show true = false from (h (ra := topS Bool) (rb := eqS Bool) (Equiv.refl Bool) true true false).1 trivial) (by decide)
-- `Nat.divModEquiv_symm_apply` idx 1: removable, `NeZero n` follows from `p.2 : Fin n`
theorem c4_148 : indep% Nat.divModEquiv_symm_apply 1 := fun _ p => NeZero.of_pos p.2.pos
-- `Int.divModEquiv_symm_apply` idx 1: removable, `NeZero n` follows from `p.2 : Fin n`
theorem c4_149 : indep% Int.divModEquiv_symm_apply 1 := fun _ p => NeZero.of_pos p.2.pos
-- `lt_finRotate_iff_ne_neg_one` idx 1: removable, `NeZero n` follows from `i : Fin n`
theorem c4_150 : indep% lt_finRotate_iff_ne_neg_one 1 := fun i => NeZero.of_pos i.pos
-- `coe_finRotate_symm_of_ne_zero` idx 1: removable, `NeZero n` follows from `i : Fin n`
theorem c4_151 : indep% coe_finRotate_symm_of_ne_zero 1 := fun {_ i} => NeZero.of_pos i.pos
-- `finRotate_symm_lt_iff_ne_zero` idx 1: removable, `NeZero n` follows from `i : Fin n`
theorem c4_152 : indep% finRotate_symm_lt_iff_ne_zero 1 := fun i => NeZero.of_pos i.pos

-- `Equiv.Perm.viaFintypeEmbedding_apply_mem_range` idx 7
theorem c4_153 : ¬ indep0% Equiv.Perm.viaFintypeEmbedding_apply_mem_range 7 := fun h => by
  obtain ⟨a, _⟩ := h (α := Empty) (β := Unit) (Equiv.refl _) ⟨Empty.elim, fun a => a.elim⟩ (b := ())
  exact a.elim
-- `Equiv.extendSubtype_apply_of_mem` idx 5
theorem c4_154 : ¬ indep0% Equiv.extendSubtype_apply_of_mem 5 := fun h =>
  Set.infinite_univ (α := ℕ) (Set.finite_coe_iff.mp (h (α := ℕ) (p := fun _ => True) (q := fun _ => True) (Equiv.refl _) 0 trivial))
-- `Equiv.extendSubtype_mem` idx 5
theorem c4_155 : ¬ indep0% Equiv.extendSubtype_mem 5 := fun h =>
  Set.infinite_univ (α := ℕ) (Set.finite_coe_iff.mp (h (α := ℕ) (p := fun _ => True) (q := fun _ => True) (Equiv.refl _) 0 trivial))
-- `Equiv.extendSubtype_mem` idx 8
theorem c4_156 : ¬ drop0% Equiv.extendSubtype_mem 8 := fun h =>
  Equiv.extendSubtype_not_mem (Equiv.refl {x : Bool // x = true}) false (by decide) (h (p := (· = true)) (q := (· = true)) (Equiv.refl _) false)
-- `Equiv.extendSubtype_apply_of_not_mem` idx 5
theorem c4_157 : ¬ indep0% Equiv.extendSubtype_apply_of_not_mem 5 := fun h =>
  (Set.finite_singleton (0 : ℕ)).infinite_compl (Set.finite_coe_iff.mp (h (α := ℕ) (p := fun n => n ≠ 0) (q := fun n => n ≠ 0) (Equiv.refl _) 0 (fun h0 => h0 rfl)))
-- `Equiv.extendSubtype_not_mem` idx 5
theorem c4_158 : ¬ indep0% Equiv.extendSubtype_not_mem 5 := fun h =>
  (Set.finite_singleton (0 : ℕ)).infinite_compl (Set.finite_coe_iff.mp (h (α := ℕ) (p := fun n => n ≠ 0) (q := fun n => n ≠ 0) (Equiv.refl _) 0 (fun h0 => h0 rfl)))
-- `Equiv.extendSubtype_not_mem` idx 8
theorem c4_159 : ¬ drop0% Equiv.extendSubtype_not_mem 8 := fun h =>
  h (Equiv.refl {x : Bool // x = true}) true (Equiv.extendSubtype_mem (Equiv.refl {x : Bool // x = true}) true rfl)
-- `Equiv.Perm.exists_extending_pair` idx 2
theorem c4_160 : ¬ drop0% Equiv.Perm.exists_extending_pair 2 := fun h => by
  obtain ⟨σ, hσ⟩ := h (α := ℕ) (β := ℕ) id Nat.succ Function.injective_id Nat.succ_injective
  obtain ⟨b, hb⟩ := σ.surjective 0
  have := hσ b; simp only [id] at this; rw [this] at hb; exact Nat.succ_ne_zero _ hb
-- `Functor.mapEquiv_apply` idx 4
theorem c4_161 : ¬ indep0% Functor.mapEquiv_apply 4 := fun h =>
  BO_nl (h (α := Unit) (β := Unit) BO (Equiv.refl _) (show BO Unit from none))
-- `Functor.mapEquiv_symm_apply` idx 4
theorem c4_162 : ¬ indep0% Functor.mapEquiv_symm_apply 4 := fun h =>
  BO_nl (h (α := Unit) (β := Unit) BO (Equiv.refl _) (show BO Unit from none))
-- `Functor.mapEquiv_refl` idx 3
theorem c4_163 : ¬ indep0% Functor.mapEquiv_refl 3 := fun h =>
  BO_nl (h (α := Unit) BO)
-- `Bifunctor.mapEquiv_apply` idx 6
theorem c4_164 : ¬ indep0% Bifunctor.mapEquiv_apply 6 := fun h =>
  BF_nl (h (α := Unit) (β := Unit) (α' := Unit) (β' := Unit) BF (Equiv.refl _) (Equiv.refl _) (show BF Unit Unit from none))
-- `Bifunctor.mapEquiv_symm_apply` idx 6
theorem c4_165 : ¬ indep0% Bifunctor.mapEquiv_symm_apply 6 := fun h =>
  BF_nl (h (α := Unit) (β := Unit) (α' := Unit) (β' := Unit) BF (Equiv.refl _) (Equiv.refl _) (show BF Unit Unit from none))
-- `Bifunctor.mapEquiv_refl_refl` idx 4
theorem c4_166 : ¬ indep0% Bifunctor.mapEquiv_refl_refl 4 := fun h =>
  BF_nl (h (α := Unit) (α' := Unit) BF)
-- `Equiv.removeNoneAux_some` idx 4
theorem c4_167 : ¬ drop0% Equiv.removeNoneAux_some 4 := fun h => by
  have := h (α := Unit) (β := Unit) (Equiv.swap none (some ())) (x := ()); simp at this
-- `Equiv.removeNone_aux_some` idx 4
theorem c4_168 : ¬ drop0% Equiv.removeNone_aux_some 4 := fun h => by
  have := h (α := Unit) (β := Unit) (Equiv.swap none (some ())) (x := ()); simp at this
-- `Equiv.removeNone_some` idx 4
theorem c4_169 : ¬ drop0% Equiv.removeNone_some 4 := fun h => by
  have := h (α := Unit) (β := Unit) (Equiv.swap none (some ())) (x := ()); simp at this
-- `Equiv.optionSubtype_apply_apply` idx 6: removable, `e` is injective and sends `none` to `x`
theorem c4_170 : indep% Equiv.optionSubtype_apply_apply 6 := by
  intro α β _ x e a h; exact Option.some_ne_none a (e.1.injective (h.trans e.2.symm))
-- `EmbeddingLike.pairwise_comp` idx 4
theorem c4_171 : ¬ dropL% EmbeddingLike.pairwise_comp 4 [0, 0, 1] := fun h => by
  have := h (X := Unit) (Y := ℕ) (F := ℕ →+ Unit) 0 (p := (· ≠ ·)) (fun _ _ h => h) (i := 0) (j := 1) (by decide)
  exact this (Subsingleton.elim _ _)
-- `EmbeddingLike.pairwise_comp` idx 7
theorem c4_172 : ¬ dropL% EmbeddingLike.pairwise_comp 7 [0, 0, 1] := fun h =>
  h (X := Bool) (Y := Bool) (F := Bool ≃ Bool) (Equiv.refl _) (p := fun _ _ => False) (i := true) (j := false) (by decide)
