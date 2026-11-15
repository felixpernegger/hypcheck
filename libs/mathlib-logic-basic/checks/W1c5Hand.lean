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

universe u_1 u_2 u_3 u_4

namespace W1c5
open Set

/-- indepL% T i [l₁, …]: indep% T i with the universe parameters of T set to the given numerals (copied from W4c4). -/
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

/-- dropL% T i [l₁, …]: drop% T i with the universe parameters of T set to the given numerals (copied from W4c4). -/
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

/-- Partial equivalence between finite types from decidable data (source `S`, target `T`). -/
def mkG {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  (f : α → β) (g : β → α) (S : α → Bool) (T : β → Bool)
  (h1 : ∀ x, S x = true → T (f x) = true := by decide)
  (h2 : ∀ x, T x = true → S (g x) = true := by decide)
  (h3 : ∀ x, S x = true → g (f x) = x := by decide)
  (h4 : ∀ x, T x = true → f (g x) = x := by decide) : PartialEquiv α β where
  toFun := f
  invFun := g
  source := {x | S x = true}
  target := {x | T x = true}
  map_source' := h1
  map_target' := h2
  left_inv' := h3
  right_inv' := h4

/-- Partial equivalence on Bool from decidable data. -/
abbrev mkB (f g : Bool → Bool) (S T : Bool → Bool)
  (h1 : ∀ x, S x = true → T (f x) = true := by decide)
  (h2 : ∀ x, T x = true → S (g x) = true := by decide)
  (h3 : ∀ x, S x = true → g (f x) = x := by decide)
  (h4 : ∀ x, T x = true → f (g x) = x := by decide) : PartialEquiv Bool Bool := mkG f g S T h1 h2 h3 h4

/-- Identity on Bool (source and target univ). -/
abbrev R := mkB id id (fun _ => true) (fun _ => true)
/-- Negation on Bool (source and target univ). -/
abbrev N := mkB not not (fun _ => true) (fun _ => true)
/-- Empty source and target, arbitrary functions. -/
abbrev E (f g : Bool → Bool) := mkB f g (fun _ => false) (fun _ => false) (by simp) (by simp) (by simp) (by simp)
/-- Partial equivalence `true ↦ true` with source and target `{true}`. -/
abbrev Tt := mkB id id (fun x => x) (fun x => x)
/-- `true ↦ false`, source `{true}`, target `{false}`. -/
abbrev Tf := mkB not not (fun x => x) (fun x => !x)
/-- `false ↦ true`, source `{false}`, target `{true}`. -/
abbrev Ft := mkB (fun _ => true) (fun _ => false) (fun x => !x) (fun x => x)
/-- Unit → Bool, constant `b`, source univ, target `{b}`. -/
def pU (b : Bool) : PartialEquiv Unit Bool where
  toFun := fun _ => b
  invFun := fun _ => ()
  source := univ
  target := {b}
  map_source' := fun _ _ => rfl
  map_target' := fun _ _ => trivial
  left_inv' := fun _ _ => rfl
  right_inv' := fun _ hx => hx.symm

end W1c5
open W1c5 Set Function
-- `PartialEquiv.coe_mk` idx 7: necessary (g x ∉ s: f=g=id on Bool, s=∅, t=univ)
theorem c5_1 : ¬ indep0% PartialEquiv.coe_mk 7 := fun h => by
  have := @h Bool Bool id id ∅ univ (by simp) (by simp) (by simp) true trivial
  simp at this

-- `PartialEquiv.coe_mk` idx 8: necessary (left_inv fails: Bool→Unit constant, g = const true, s,t univ)
theorem c5_2 : ¬ indep0% PartialEquiv.coe_mk 8 := fun h => by
  have := @h Bool Unit (fun _ => ()) (fun _ => true) univ univ (by simp) (by simp) (by simp) false trivial
  simp at this

-- `PartialEquiv.coe_mk` idx 9: necessary (right_inv fails: Unit→Bool constant true, s,t univ)
theorem c5_3 : ¬ indep0% PartialEquiv.coe_mk 9 := fun h => by
  have := @h Unit Bool (fun _ => true) (fun _ => ()) univ univ (by simp) (by simp) (by simp) false trivial
  simp at this

-- `PartialEquiv.coe_symm_mk` idx 7: necessary (g x ∉ s: f=g=id on Bool, s=∅, t=univ)
theorem c5_4 : ¬ indep0% PartialEquiv.coe_symm_mk 7 := fun h => by
  have := @h Bool Bool id id ∅ univ (by simp) (by simp) (by simp) true trivial
  simp at this

-- `PartialEquiv.coe_symm_mk` idx 8: necessary (left_inv fails: Bool→Unit constant, g = const true, s,t univ)
theorem c5_5 : ¬ indep0% PartialEquiv.coe_symm_mk 8 := fun h => by
  have := @h Bool Unit (fun _ => ()) (fun _ => true) univ univ (by simp) (by simp) (by simp) false trivial
  simp at this

-- `PartialEquiv.coe_symm_mk` idx 9: necessary (right_inv fails: Unit→Bool constant true, s,t univ)
theorem c5_6 : ¬ indep0% PartialEquiv.coe_symm_mk 9 := fun h => by
  have := @h Unit Bool (fun _ => true) (fun _ => ()) univ univ (by simp) (by simp) (by simp) false trivial
  simp at this

-- `PartialEquiv.IsImage.apply_mem_iff` idx 7: necessary (e with empty source, s=∅, t=univ, x=true)
theorem c5_7 : ¬ drop0% PartialEquiv.IsImage.apply_mem_iff 7 := fun h => by
  have := @h Bool Bool (E id id) ∅ univ true (fun x hx => by simp [mkG] at hx)
  simp [mkG] at this

-- `PartialEquiv.IsImage.symm_apply_mem_iff` idx 7: necessary (e with empty source, s=univ, t=∅, y=true)
theorem c5_8 : ¬ drop0% PartialEquiv.IsImage.symm_apply_mem_iff 7 := fun h => by
  have := @h Bool Bool (E id id) univ ∅ (fun x hx => by simp [mkG] at hx) true
  simp [mkG] at this

-- `PartialEquiv.IsImage.mapsTo` idx 5: necessary (e=id on Bool, s=univ, t=∅)
theorem c5_9 : ¬ drop0% PartialEquiv.IsImage.mapsTo 5 := fun h => by
  have := @h Bool Bool R univ ∅ true (by simp [mkG])
  simp [mkG] at this

-- `PartialEquiv.IsImage.restr_source` idx 5: necessary (IsImage fails: e=id on Bool, s=univ, t=∅)
theorem c5_10 : ¬ indep0% PartialEquiv.IsImage.restr_source 5 := fun h => by
  have := @h Bool Bool R univ ∅ true
  simp [mkG] at this

-- `PartialEquiv.IsImage.restr_apply` idx 5: necessary (IsImage fails: e=id on Bool, s=univ, t=∅)
theorem c5_11 : ¬ indep0% PartialEquiv.IsImage.restr_apply 5 := fun h => by
  have := @h Bool Bool R univ ∅ true
  simp [mkG] at this

-- `PartialEquiv.IsImage.restr_symm_apply` idx 5: necessary (IsImage fails: e=id on Bool, s=univ, t=∅)
theorem c5_12 : ¬ indep0% PartialEquiv.IsImage.restr_symm_apply 5 := fun h => by
  have := @h Bool Bool R univ ∅ true
  simp [mkG] at this

-- `PartialEquiv.IsImage.restr_target` idx 5: necessary (IsImage fails: e=id on Bool, s=univ, t=∅)
theorem c5_13 : ¬ indep0% PartialEquiv.IsImage.restr_target 5 := fun h => by
  have := @h Bool Bool R univ ∅ true
  simp [mkG] at this

-- `PartialEquiv.IsImage.of_preimage_eq` idx 5: necessary (IsImage fails: e=id on Bool, s=univ, t=∅)
theorem c5_14 : ¬ drop0% PartialEquiv.IsImage.of_preimage_eq 5 := fun h => by
  have := @h Bool Bool R univ ∅ true
  simp [mkG] at this

-- `PartialEquiv.IsImage.of_symm_preimage_eq` idx 5: necessary (IsImage fails: e=id on Bool, s=univ, t=∅)
theorem c5_15 : ¬ drop0% PartialEquiv.IsImage.of_symm_preimage_eq 5 := fun h => by
  have := @h Bool Bool R univ ∅ true
  simp [mkG] at this

-- `PartialEquiv.IsImage.of_image_eq` idx 5: necessary (IsImage fails: e=id on Bool, s=univ, t=∅)
theorem c5_16 : ¬ drop0% PartialEquiv.IsImage.of_image_eq 5 := fun h => by
  have := @h Bool Bool R univ ∅ true
  simp [mkG] at this

-- `PartialEquiv.IsImage.of_symm_image_eq` idx 5: necessary (IsImage fails: e=id on Bool, s=univ, t=∅)
theorem c5_17 : ¬ drop0% PartialEquiv.IsImage.of_symm_image_eq 5 := fun h => by
  have := @h Bool Bool R univ ∅ true
  simp [mkG] at this

-- `PartialEquiv.IsImage.compl` idx 5: necessary (e=id, s=∅, t=univ: complement pair not an image)
theorem c5_18 : ¬ drop0% PartialEquiv.IsImage.compl 5 := fun h => by
  have := @h Bool Bool R ∅ univ true
  simp [mkG] at this

-- `PartialEquiv.IsImage.inter` idx 7: necessary (e=id, s=univ, t=∅, s'=t'=univ)
theorem c5_19 : ¬ drop0% PartialEquiv.IsImage.inter 7 := fun h => by
  have := @h Bool Bool R univ ∅ univ univ (fun x _ => by simp) true
  simp [mkG] at this

-- `PartialEquiv.IsImage.inter` idx 8: necessary (e=id, s=t=univ, s'=univ, t'=∅)
theorem c5_20 : ¬ drop0% PartialEquiv.IsImage.inter 8 := fun h => by
  have := @h Bool Bool R univ univ univ ∅ (fun x _ => by simp) true
  simp [mkG] at this

-- `PartialEquiv.IsImage.union` idx 7: necessary (e=id, s=univ, t=∅, s'=t'=∅)
theorem c5_21 : ¬ drop0% PartialEquiv.IsImage.union 7 := fun h => by
  have := @h Bool Bool R univ ∅ ∅ ∅ (fun x _ => by simp) true
  simp [mkG] at this

-- `PartialEquiv.IsImage.union` idx 8: necessary (e=id, s=t=∅, s'=univ, t'=∅)
theorem c5_22 : ¬ drop0% PartialEquiv.IsImage.union 8 := fun h => by
  have := @h Bool Bool R ∅ ∅ univ ∅ (fun x _ => by simp) true
  simp [mkG] at this

-- `PartialEquiv.IsImage.diff` idx 7: necessary (e=id, s=univ, t=∅, s'=t'=∅)
theorem c5_23 : ¬ drop0% PartialEquiv.IsImage.diff 7 := fun h => by
  have := @h Bool Bool R univ ∅ ∅ ∅ (fun x _ => by simp) true
  simp [mkG] at this

-- `PartialEquiv.IsImage.diff` idx 8: necessary (e=id, s=t=univ, s'=univ, t'=∅)
theorem c5_24 : ¬ drop0% PartialEquiv.IsImage.diff 8 := fun h => by
  have := @h Bool Bool R univ univ univ ∅ (fun x _ => by simp) false
  simp [mkG] at this

-- `PartialEquiv.IsImage.leftInvOn_piecewise` idx 8: necessary (e=id, e'=empty-source with not, s=univ, t=∅)
theorem c5_25 : ¬ drop0% PartialEquiv.IsImage.leftInvOn_piecewise 8 := fun h => by
  have := @h Bool Bool R univ ∅ (E not not) (fun _ => Classical.dec _) (fun _ => Classical.dec _) (fun x hx => by simp [mkG] at hx) true
  simp [mkG, Set.ite] at this

-- `PartialEquiv.IsImage.leftInvOn_piecewise` idx 9: necessary (e=empty-source with not, e'=id, s=∅, t=univ)
theorem c5_26 : ¬ drop0% PartialEquiv.IsImage.leftInvOn_piecewise 9 := fun h => by
  have := @h Bool Bool (E not not) ∅ univ R (fun _ => Classical.dec _) (fun _ => Classical.dec _) (fun x hx => by simp [mkG] at hx) true
  simp [mkG, Set.ite] at this

-- `PartialEquiv.IsImage.inter_eq_of_inter_eq_of_eqOn` idx 6: necessary (e=id, e'=empty, s=∅, t=univ)
theorem c5_27 : ¬ drop0% PartialEquiv.IsImage.inter_eq_of_inter_eq_of_eqOn 6 := fun h => by
  have := @h Bool Bool R ∅ univ (E id id) (fun x hx => by simp [mkG] at hx) (by simp) (by simp [Set.EqOn])
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `PartialEquiv.IsImage.inter_eq_of_inter_eq_of_eqOn` idx 7: necessary (e=empty, e'=id, s=∅, t=univ)
theorem c5_28 : ¬ drop0% PartialEquiv.IsImage.inter_eq_of_inter_eq_of_eqOn 7 := fun h => by
  have := @h Bool Bool (E id id) ∅ univ R (fun x hx => by simp [mkG] at hx) (by simp) (by simp [Set.EqOn])
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `PartialEquiv.IsImage.inter_eq_of_inter_eq_of_eqOn` idx 8: necessary (e=empty, e'=id, s=t=univ)
theorem c5_29 : ¬ drop0% PartialEquiv.IsImage.inter_eq_of_inter_eq_of_eqOn 8 := fun h => by
  have := @h Bool Bool (E id id) univ univ R (fun x _ => by simp) (fun x _ => by simp) (fun x hx => by simp [mkG] at hx)
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `PartialEquiv.IsImage.inter_eq_of_inter_eq_of_eqOn` idx 9: necessary (Unit→Bool constants true/false (source univ, targets {true},{false}), s=t=univ)
theorem c5_30 : ¬ drop0% PartialEquiv.IsImage.inter_eq_of_inter_eq_of_eqOn 9 := fun h => by
  have := @h Unit Bool (pU true) univ univ (pU false) (fun x _ => by simp) (fun x _ => by simp) (by simp [pU])
  have := congrArg (true ∈ ·) this
  simp [pU] at this

-- `PartialEquiv.IsImage.symm_eq_on_of_inter_eq_of_eqOn` idx 6: necessary (e=id, e'=empty source with inverse not, s=∅, t=univ)
theorem c5_31 : ¬ drop0% PartialEquiv.IsImage.symm_eq_on_of_inter_eq_of_eqOn 6 := fun h => by
  have := @h Bool Bool R ∅ univ (E id not) (by simp) (by simp [Set.EqOn]) true (by simp [mkG])
  simp [mkG] at this

-- `PartialEquiv.IsImage.symm_eq_on_of_inter_eq_of_eqOn` idx 7: necessary (e=id, e'=empty source with inverse not, s=t=univ)
theorem c5_32 : ¬ drop0% PartialEquiv.IsImage.symm_eq_on_of_inter_eq_of_eqOn 7 := fun h => by
  have := @h Bool Bool R univ univ (E id not) (fun x _ => by simp) (fun x _ => by simp [mkG]) true (by simp [mkG])
  simp [mkG] at this

-- `PartialEquiv.IsImage.symm_eq_on_of_inter_eq_of_eqOn` idx 8: necessary (e=id, e'=not, s=t=univ)
theorem c5_33 : ¬ drop0% PartialEquiv.IsImage.symm_eq_on_of_inter_eq_of_eqOn 8 := fun h => by
  have := @h Bool Bool R univ univ N (fun x _ => by simp) (by simp [mkG]) true (by simp [mkG])
  simp [mkG] at this

-- `PartialEquiv.isImage_source_target_of_disjoint` idx 4: necessary (e: true↦false on {true}, e': id on {true})
theorem c5_34 : ¬ drop0% PartialEquiv.isImage_source_target_of_disjoint 4 := fun h => by
  have := @h Bool Bool Tf Tt (by simp [mkG, Set.disjoint_left]) true (by simp [mkG])
  simp [mkG] at this

-- `PartialEquiv.isImage_source_target_of_disjoint` idx 5: necessary (e: true↦true on {true}, e': false↦true on {false})
theorem c5_35 : ¬ drop0% PartialEquiv.isImage_source_target_of_disjoint 5 := fun h => by
  have := @h Bool Bool Tt Ft (by simp [mkG, Set.disjoint_left]) true (by simp [mkG])
  simp [mkG] at this

-- `PartialEquiv.ext` idx 4: necessary (empty-source equivs with toFun id vs not)
theorem c5_36 : ¬ drop0% PartialEquiv.ext 4 := fun h => by
  have := @h Bool Bool (E id id) (E not id) (fun _ => rfl) rfl
  have := congrArg (fun e : PartialEquiv Bool Bool => e true) this
  simp [mkG] at this

-- `PartialEquiv.ext` idx 5: necessary (empty-source equivs with invFun id vs not)
theorem c5_37 : ¬ drop0% PartialEquiv.ext 5 := fun h => by
  have := @h Bool Bool (E id id) (E id not) (fun _ => rfl) rfl
  have := congrArg (fun e : PartialEquiv Bool Bool => e.symm true) this
  simp [mkG] at this

-- `PartialEquiv.ext` idx 6: necessary (id on Bool vs id with empty source)
theorem c5_38 : ¬ drop0% PartialEquiv.ext 6 := fun h => by
  have := @h Bool Bool R (E id id) (fun _ => rfl) (fun _ => rfl)
  have := congrArg (fun e : PartialEquiv Bool Bool => true ∈ e.source) this
  simp [mkG] at this

-- `PartialEquiv.restr_eq_of_source_subset` idx 4: necessary (e=id, s=∅)
theorem c5_39 : ¬ drop0% PartialEquiv.restr_eq_of_source_subset 4 := fun h => by
  have := congrArg (fun e : PartialEquiv Bool Bool => true ∈ e.source) (@h Bool Bool R ∅)
  simp [mkG] at this

-- `PartialEquiv.trans'_source` idx 5: necessary (e=id (target univ), e'=empty source)
theorem c5_40 : ¬ indep0% PartialEquiv.trans'_source 5 := fun h => by
  have := @h Bool Bool Bool R (E id id)
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `PartialEquiv.trans'_symm_apply` idx 5: necessary (e=id (target univ), e'=empty source)
theorem c5_41 : ¬ indep0% PartialEquiv.trans'_symm_apply 5 := fun h => by
  have := @h Bool Bool Bool R (E id id) true
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `PartialEquiv.trans'_target` idx 5: necessary (e=id (target univ), e'=empty source)
theorem c5_42 : ¬ indep0% PartialEquiv.trans'_target 5 := fun h => by
  have := @h Bool Bool Bool R (E id id)
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `PartialEquiv.trans'_apply` idx 5: necessary (e=id (target univ), e'=empty source)
theorem c5_43 : ¬ indep0% PartialEquiv.trans'_apply 5 := fun h => by
  have := @h Bool Bool Bool R (E id id) true
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `PartialEquiv.mem_symm_trans_source` idx 6: necessary (e=empty, e'=id, x=true)
theorem c5_44 : ¬ drop0% PartialEquiv.mem_symm_trans_source 6 := fun h => by
  have := @h Bool Bool Bool (E id id) R true (by simp [mkG])
  simp [mkG] at this

-- `PartialEquiv.mem_symm_trans_source` idx 7: necessary (e=id, e'=empty, x=true)
theorem c5_45 : ¬ drop0% PartialEquiv.mem_symm_trans_source 7 := fun h => by
  have := @h Bool Bool Bool R (E id id) true (by simp [mkG])
  simp [mkG] at this

-- `PartialEquiv.EqOnSource.source_eq` idx 4: necessary (id vs empty-source)
theorem c5_46 : ¬ drop0% PartialEquiv.EqOnSource.source_eq 4 := fun h => by
  have := @h Bool Bool R (E id id)
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `PartialEquiv.EqOnSource.eqOn` idx 4: necessary (id vs not)
theorem c5_47 : ¬ drop0% PartialEquiv.EqOnSource.eqOn 4 := fun h => by
  have := @h Bool Bool R N true (by simp [mkG])
  simp [mkG] at this

-- `PartialEquiv.EqOnSource.target_eq` idx 4: necessary (id vs empty-source)
theorem c5_48 : ¬ drop0% PartialEquiv.EqOnSource.target_eq 4 := fun h => by
  have := @h Bool Bool R (E id id)
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `PartialEquiv.EqOnSource.symm'` idx 4: necessary (id vs empty-source)
theorem c5_49 : ¬ drop0% PartialEquiv.EqOnSource.symm' 4 := fun h => by
  have := @h Bool Bool R (E id id)
  have := PartialEquiv.EqOnSource.source_eq this
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `PartialEquiv.EqOnSource.symm_eqOn` idx 4: necessary (id vs not)
theorem c5_50 : ¬ drop0% PartialEquiv.EqOnSource.symm_eqOn 4 := fun h => by
  have := @h Bool Bool R N true (by simp [mkG])
  simp [mkG] at this

-- `PartialEquiv.EqOnSource.trans'` idx 7: necessary (e=id, e'=empty, f=f'=id)
theorem c5_51 : ¬ drop0% PartialEquiv.EqOnSource.trans' 7 := fun h => by
  have := @h Bool Bool Bool R (E id id) R R (Setoid.refl R)
  have := PartialEquiv.EqOnSource.source_eq this
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `PartialEquiv.EqOnSource.trans'` idx 8: necessary (e=e'=f=id, f'=empty)
theorem c5_52 : ¬ drop0% PartialEquiv.EqOnSource.trans' 8 := fun h => by
  have := @h Bool Bool Bool R R R (E id id) (Setoid.refl R)
  have := PartialEquiv.EqOnSource.source_eq this
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `PartialEquiv.EqOnSource.restr` idx 4: necessary (id vs empty-source, s=univ)
theorem c5_53 : ¬ drop0% PartialEquiv.EqOnSource.restr 4 := fun h => by
  have := @h Bool Bool R (E id id) univ
  have := PartialEquiv.EqOnSource.source_eq this
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `PartialEquiv.EqOnSource.source_inter_preimage_eq` idx 4: necessary (id vs empty-source, s=univ)
theorem c5_54 : ¬ drop0% PartialEquiv.EqOnSource.source_inter_preimage_eq 4 := fun h => by
  have := @h Bool Bool R (E id id) univ
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `PartialEquiv.eq_of_eqOnSource_univ` idx 4: necessary (id vs not on Bool, both with univ source/target)
theorem c5_55 : ¬ drop0% PartialEquiv.eq_of_eqOnSource_univ 4 := fun h => by
  have := @h Bool Bool R N (Set.eq_univ_of_forall fun _ => rfl) (Set.eq_univ_of_forall fun _ => rfl)
  have := congrArg (fun e : PartialEquiv Bool Bool => e true) this
  simp [mkG] at this

-- `PartialEquiv.eq_of_eqOnSource_univ` idx 5: necessary (Fin 3 → Bool, source {0,1}, target univ, toFun differs only at 2)
theorem c5_56 : ¬ drop0% PartialEquiv.eq_of_eqOnSource_univ 5 := fun h => by
  have := @h (Fin 3) Bool (mkG (fun x => decide (x = 1)) (fun b => if b then 1 else 0) (fun x => decide (x ≠ 2)) (fun _ => true))
    (mkG (fun x => decide (x ≠ 0)) (fun b => if b then 1 else 0) (fun x => decide (x ≠ 2)) (fun _ => true))
    ⟨rfl, fun x hx => by revert hx; fin_cases x <;> simp [mkG]⟩ (Set.eq_univ_of_forall fun _ => rfl)
  have := congrArg (fun e : PartialEquiv (Fin 3) Bool => e 2) this
  simp [mkG] at this

-- `PartialEquiv.eq_of_eqOnSource_univ` idx 6: necessary (Bool → Fin 3, source univ, target {0,1}, invFun differs only at 2)
theorem c5_57 : ¬ drop0% PartialEquiv.eq_of_eqOnSource_univ 6 := fun h => by
  have := @h Bool (Fin 3) (mkG (fun b => if b then 1 else 0) (fun x => decide (x = 1)) (fun _ => true) (fun x => decide (x ≠ 2)))
    (mkG (fun b => if b then 1 else 0) (fun x => decide (x ≠ 0)) (fun _ => true) (fun x => decide (x ≠ 2)))
    ⟨rfl, fun _ _ => rfl⟩ (Set.eq_univ_of_forall fun _ => rfl)
  have := congrArg (fun e : PartialEquiv Bool (Fin 3) => e.symm 2) this
  simp [mkG] at this

-- `PartialEquiv.piecewise_symm_apply` idx 8: necessary (e=id, e'=empty source, s=univ, t=∅)
theorem c5_58 : ¬ indep0% PartialEquiv.piecewise_symm_apply 8 := fun h => by
  have := @h Bool Bool R (E id id) univ ∅ (fun _ => Classical.dec _) (fun _ => Classical.dec _) (fun x hx => by simp [mkG] at hx) true
  simp [mkG] at this

-- `PartialEquiv.piecewise_source` idx 8: necessary (e=id, e'=empty source, s=univ, t=∅)
theorem c5_59 : ¬ indep0% PartialEquiv.piecewise_source 8 := fun h => by
  have := @h Bool Bool R (E id id) univ ∅ (fun _ => Classical.dec _) (fun _ => Classical.dec _) (fun x hx => by simp [mkG] at hx) true
  simp [mkG] at this

-- `PartialEquiv.piecewise_apply` idx 8: necessary (e=id, e'=empty source, s=univ, t=∅)
theorem c5_60 : ¬ indep0% PartialEquiv.piecewise_apply 8 := fun h => by
  have := @h Bool Bool R (E id id) univ ∅ (fun _ => Classical.dec _) (fun _ => Classical.dec _) (fun x hx => by simp [mkG] at hx) true
  simp [mkG] at this

-- `PartialEquiv.piecewise_target` idx 8: necessary (e=id, e'=empty source, s=univ, t=∅)
theorem c5_61 : ¬ indep0% PartialEquiv.piecewise_target 8 := fun h => by
  have := @h Bool Bool R (E id id) univ ∅ (fun _ => Classical.dec _) (fun _ => Classical.dec _) (fun x hx => by simp [mkG] at hx) true
  simp [mkG] at this

-- `PartialEquiv.piecewise_symm_apply` idx 9: necessary (e=empty source, e'=id, s=univ, t=∅)
theorem c5_62 : ¬ indep0% PartialEquiv.piecewise_symm_apply 9 := fun h => by
  have := @h Bool Bool (E id id) R univ ∅ (fun _ => Classical.dec _) (fun _ => Classical.dec _) (fun x hx => by simp [mkG] at hx) true
  simp [mkG] at this

-- `PartialEquiv.piecewise_source` idx 9: necessary (e=empty source, e'=id, s=univ, t=∅)
theorem c5_63 : ¬ indep0% PartialEquiv.piecewise_source 9 := fun h => by
  have := @h Bool Bool (E id id) R univ ∅ (fun _ => Classical.dec _) (fun _ => Classical.dec _) (fun x hx => by simp [mkG] at hx) true
  simp [mkG] at this

-- `PartialEquiv.piecewise_apply` idx 9: necessary (e=empty source, e'=id, s=univ, t=∅)
theorem c5_64 : ¬ indep0% PartialEquiv.piecewise_apply 9 := fun h => by
  have := @h Bool Bool (E id id) R univ ∅ (fun _ => Classical.dec _) (fun _ => Classical.dec _) (fun x hx => by simp [mkG] at hx) true
  simp [mkG] at this

-- `PartialEquiv.piecewise_target` idx 9: necessary (e=empty source, e'=id, s=univ, t=∅)
theorem c5_65 : ¬ indep0% PartialEquiv.piecewise_target 9 := fun h => by
  have := @h Bool Bool (E id id) R univ ∅ (fun _ => Classical.dec _) (fun _ => Classical.dec _) (fun x hx => by simp [mkG] at hx) true
  simp [mkG] at this

-- `PartialEquiv.symm_piecewise` idx 8: necessary (e=id, e'=empty source, s=univ, t=∅)
theorem c5_66 : ¬ indep0% PartialEquiv.symm_piecewise 8 := fun h => by
  have := @h Bool Bool R (E id id) univ ∅ (fun _ => Classical.dec _) (fun _ => Classical.dec _) (fun x hx => by simp [mkG] at hx) true
  simp [mkG] at this

-- `PartialEquiv.symm_piecewise` idx 9: necessary (e=empty source, e'=id, s=univ, t=∅)
theorem c5_67 : ¬ indep0% PartialEquiv.symm_piecewise 9 := fun h => by
  have := @h Bool Bool (E id id) R univ ∅ (fun _ => Classical.dec _) (fun _ => Classical.dec _) (fun x hx => by simp [mkG] at hx) true
  simp [mkG] at this

-- `PartialEquiv.disjointUnion_apply` idx 4: necessary (sources both {true}, targets {true},{false})
theorem c5_68 : ¬ indep0% PartialEquiv.disjointUnion_apply 4 := fun h => by
  have := @h Bool Bool Tt Tf (by simp [mkG, Set.disjoint_left]) (fun _ => Classical.dec _) (fun _ => Classical.dec _)
  simp [mkG, Set.disjoint_left] at this

-- `PartialEquiv.disjointUnion_source` idx 4: necessary (sources both {true}, targets {true},{false})
theorem c5_69 : ¬ indep0% PartialEquiv.disjointUnion_source 4 := fun h => by
  have := @h Bool Bool Tt Tf (by simp [mkG, Set.disjoint_left]) (fun _ => Classical.dec _) (fun _ => Classical.dec _)
  simp [mkG, Set.disjoint_left] at this

-- `PartialEquiv.disjointUnion_symm_apply` idx 4: necessary (sources both {true}, targets {true},{false})
theorem c5_70 : ¬ indep0% PartialEquiv.disjointUnion_symm_apply 4 := fun h => by
  have := @h Bool Bool Tt Tf (by simp [mkG, Set.disjoint_left]) (fun _ => Classical.dec _) (fun _ => Classical.dec _)
  simp [mkG, Set.disjoint_left] at this

-- `PartialEquiv.disjointUnion_target` idx 4: necessary (sources both {true}, targets {true},{false})
theorem c5_71 : ¬ indep0% PartialEquiv.disjointUnion_target 4 := fun h => by
  have := @h Bool Bool Tt Tf (by simp [mkG, Set.disjoint_left]) (fun _ => Classical.dec _) (fun _ => Classical.dec _)
  simp [mkG, Set.disjoint_left] at this

-- `PartialEquiv.disjointUnion_apply` idx 5: necessary (sources {true},{false}, both targets {true})
theorem c5_72 : ¬ indep0% PartialEquiv.disjointUnion_apply 5 := fun h => by
  have := @h Bool Bool Tt Ft (by simp [mkG, Set.disjoint_left]) (fun _ => Classical.dec _) (fun _ => Classical.dec _)
  simp [mkG, Set.disjoint_left] at this

-- `PartialEquiv.disjointUnion_source` idx 5: necessary (sources {true},{false}, both targets {true})
theorem c5_73 : ¬ indep0% PartialEquiv.disjointUnion_source 5 := fun h => by
  have := @h Bool Bool Tt Ft (by simp [mkG, Set.disjoint_left]) (fun _ => Classical.dec _) (fun _ => Classical.dec _)
  simp [mkG, Set.disjoint_left] at this

-- `PartialEquiv.disjointUnion_symm_apply` idx 5: necessary (sources {true},{false}, both targets {true})
theorem c5_74 : ¬ indep0% PartialEquiv.disjointUnion_symm_apply 5 := fun h => by
  have := @h Bool Bool Tt Ft (by simp [mkG, Set.disjoint_left]) (fun _ => Classical.dec _) (fun _ => Classical.dec _)
  simp [mkG, Set.disjoint_left] at this

-- `PartialEquiv.disjointUnion_target` idx 5: necessary (sources {true},{false}, both targets {true})
theorem c5_75 : ¬ indep0% PartialEquiv.disjointUnion_target 5 := fun h => by
  have := @h Bool Bool Tt Ft (by simp [mkG, Set.disjoint_left]) (fun _ => Classical.dec _) (fun _ => Classical.dec _)
  simp [mkG, Set.disjoint_left] at this

-- `PartialEquiv.disjointUnion_eq_piecewise` idx 4: necessary (sources both {true}, targets {true},{false})
theorem c5_76 : ¬ indep0% PartialEquiv.disjointUnion_eq_piecewise 4 := fun h => by
  have := @h Bool Bool Tt Tf (by simp [mkG, Set.disjoint_left]) (fun _ => Classical.dec _) (fun _ => Classical.dec _)
  simp [mkG, Set.disjoint_left] at this

-- `PartialEquiv.disjointUnion_eq_piecewise` idx 5: necessary (sources {true},{false}, both targets {true})
theorem c5_77 : ¬ indep0% PartialEquiv.disjointUnion_eq_piecewise 5 := fun h => by
  have := @h Bool Bool Tt Ft (by simp [mkG, Set.disjoint_left]) (fun _ => Classical.dec _) (fun _ => Classical.dec _)
  simp [mkG, Set.disjoint_left] at this

-- `Set.BijOn.toPartialEquiv_apply` idx 2: necessary (α = Empty, s = t = ∅)
theorem c5_78 : ¬ indep0% Set.BijOn.toPartialEquiv_apply 2 := fun h => by
  have := @h Empty Bool Empty.elim ∅ ∅ (Set.bijOn_empty _)
  exact this.elim fun e => e.elim

-- `Set.BijOn.toPartialEquiv_source` idx 2: necessary (α = Empty, s = t = ∅)
theorem c5_79 : ¬ indep0% Set.BijOn.toPartialEquiv_source 2 := fun h => by
  have := @h Empty Bool Empty.elim ∅ ∅ (Set.bijOn_empty _)
  exact this.elim fun e => e.elim

-- `Set.BijOn.toPartialEquiv_symm_apply` idx 2: necessary (α = Empty, s = t = ∅)
theorem c5_80 : ¬ indep0% Set.BijOn.toPartialEquiv_symm_apply 2 := fun h => by
  have := @h Empty Bool Empty.elim ∅ ∅ (Set.bijOn_empty _)
  exact this.elim fun e => e.elim

-- `Set.BijOn.toPartialEquiv_target` idx 2: necessary (α = Empty, s = t = ∅)
theorem c5_81 : ¬ indep0% Set.BijOn.toPartialEquiv_target 2 := fun h => by
  have := @h Empty Bool Empty.elim ∅ ∅ (Set.bijOn_empty _)
  exact this.elim fun e => e.elim

-- `Set.equivOfEq_symm_apply` idx 3: necessary (s, t = ∅, univ on Bool)
theorem c5_82 : ¬ indep0% Set.equivOfEq_symm_apply 3 := fun h => by
  have := @h Bool ∅ univ ⟨true, trivial⟩
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `Set.equivOfEq_apply` idx 3: necessary (s, t = ∅, univ on Bool)
theorem c5_83 : ¬ indep0% Set.equivOfEq_apply 3 := fun h => by
  have := @h Bool univ ∅ ⟨true, trivial⟩
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `Equiv.Set.congr_apply` idx 3: necessary (s, t = ∅, univ on Bool)
theorem c5_84 : ¬ indep0% Equiv.Set.congr_apply 3 := fun h => by
  have := @h Bool univ ∅ ⟨true, trivial⟩
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `Equiv.Set.congr_symm_apply` idx 3: necessary (s, t = ∅, univ on Bool)
theorem c5_85 : ¬ indep0% Equiv.Set.congr_symm_apply 3 := fun h => by
  have := @h Bool ∅ univ ⟨true, trivial⟩
  have := congrArg (true ∈ ·) this
  simp [mkG] at this

-- `Equiv.Set.union_apply_left` idx 6: necessary (s=∅, t=univ)
theorem c5_86 : ¬ indep0% Equiv.Set.union_apply_left 6 := fun h => by
  have := @h Bool ∅ univ (fun _ => Classical.dec _) (by simp) ⟨true, by simp⟩
  simp at this

-- `Equiv.Set.union_apply_right` idx 6: necessary (s=univ, t=∅)
theorem c5_87 : ¬ indep0% Equiv.Set.union_apply_right 6 := fun h => by
  have := @h Bool univ ∅ (fun _ => Classical.dec _) (by simp) ⟨true, by simp⟩
  simp at this

-- `Equiv.Set.sumDiffSubset_apply_inl` idx 3: necessary (s=univ, t=∅)
theorem c5_88 : ¬ indep0% Equiv.Set.sumDiffSubset_apply_inl 3 := fun h => by
  have := @h Bool univ ∅ (fun _ => Classical.dec _) ⟨true, trivial⟩
  exact this (Set.mem_univ true)

-- `Equiv.Set.sumDiffSubset_apply_inr` idx 3: necessary (s={true}, t={false})
theorem c5_89 : ¬ indep0% Equiv.Set.sumDiffSubset_apply_inr 3 := fun h => by
  have := @h Bool {true} {false} (fun _ => Classical.dec _) ⟨false, by simp⟩
  have := this (rfl : true ∈ ({true} : Set Bool))
  simp at this

-- `Equiv.Set.sumDiffSubset_symm_apply_of_mem` idx 3: necessary (s=univ, t={false}, x=false)
theorem c5_90 : ¬ indep0% Equiv.Set.sumDiffSubset_symm_apply_of_mem 3 := fun h => by
  have := @h Bool univ {false} (fun _ => Classical.dec _) ⟨false, rfl⟩ trivial
  have := this (Set.mem_univ true)
  simp at this

-- `Equiv.Set.sumDiffSubset_symm_apply_of_mem` idx 6: necessary (s=∅, t=univ)
theorem c5_91 : ¬ indep0% Equiv.Set.sumDiffSubset_symm_apply_of_mem 6 := fun h => by
  have := @h Bool ∅ univ (Set.empty_subset _) (fun _ => Classical.dec _) ⟨true, trivial⟩
  simp at this

-- `Equiv.Set.sumDiffSubset_symm_apply_of_notMem` idx 3: necessary (s={true}, t={false}, x=false)
theorem c5_92 : ¬ indep0% Equiv.Set.sumDiffSubset_symm_apply_of_notMem 3 := fun h => by
  have := @h Bool {true} {false} (fun _ => Classical.dec _) ⟨false, rfl⟩ (by simp)
  have := this (rfl : true ∈ ({true} : Set Bool))
  simp at this

-- `Equiv.ofLeftInverse_symm_apply` idx 4: necessary (f=id on Bool, f_inv = const true)
theorem c5_93 : ¬ indepL% Equiv.ofLeftInverse_symm_apply 4 [1, 0] := fun h => by
  have := @h Bool Bool id (fun _ _ => true) ⟨true, true, rfl⟩ ⟨true⟩ false
  exact absurd this (by decide)

-- `Equiv.apply_ofInjective_symm` idx 3: necessary (f: Bool → Unit constant)
theorem c5_94 : ¬ indepL% Equiv.apply_ofInjective_symm 3 [1, 0] := fun h => by
  have := @h Bool Unit (fun _ => ()) ⟨(), true, rfl⟩ true false rfl
  exact absurd this (by decide)

-- `Equiv.swap_bijOn_exchange` idx 6: necessary (a=true, b=false, s=univ)
theorem c5_95 : ¬ drop0% Equiv.swap_bijOn_exchange 6 := fun h => by
  have := (@h Bool _ true false univ trivial).mapsTo (Set.mem_univ false)
  simp at this

-- `Function.const_injective` idx 2: necessary (α = Empty)
theorem c5_96 : ¬ dropL% Function.const_injective 2 [1, 1] := fun h => absurd (@h Empty Bool true false (funext fun e => e.elim)) (by decide)

-- `Function.const_inj` idx 2: necessary (α = Empty)
theorem c5_97 : ¬ dropL% Function.const_inj 2 [1, 1] := fun h => absurd ((@h Empty Bool true false).mp (funext fun e => e.elim)) (by decide)

-- `Function.hfunext` idx 6: necessary (α = Empty, α' = Unit: hypothesis vacuous, f' const true / const false both HEq to the empty function)
theorem c5_98 : ¬ dropL% Function.hfunext 6 [1, 1] := fun h => by
  have h1 := @h Empty Unit (fun _ => Bool) (fun _ => Bool) (fun e => e.elim) (fun _ => true) (fun a => a.elim)
  have h2 := @h Empty Unit (fun _ => Bool) (fun _ => Bool) (fun e => e.elim) (fun _ => false) (fun a => a.elim)
  exact absurd (congrFun (eq_of_heq (h1.symm.trans h2)) ()) (by decide)

-- `Function.hfunext` idx 7: necessary (α = α' = Unit, f = const true, f' = const false)
theorem c5_99 : ¬ dropL% Function.hfunext 7 [1, 1] := fun h => absurd (congrFun (eq_of_heq (@h Unit Unit (fun _ => Bool) (fun _ => Bool) (fun _ => true) (fun _ => false) rfl)) ()) (by decide)

-- `Function.not_injective_const` idx 2: necessary (α = Unit)
theorem c5_100 : ¬ dropL% Function.not_injective_const 2 [0, 0] := fun h => @h Unit Unit () (fun _ _ _ => rfl)

-- `Function.Injective.of_comp_right` idx 6: necessary (γ = Empty, f: Bool → Unit)
theorem c5_101 : ¬ dropL% Function.Injective.of_comp_right 6 [1, 1, 1] := fun h => absurd (@h Bool Unit Empty (fun _ => ()) Empty.elim (fun a => a.elim) true false rfl) (by decide)

-- `Function.Surjective.bijective₂_of_injective` idx 5: necessary (f: Unit → Bool const true, g = id)
theorem c5_102 : ¬ dropL% Function.Surjective.bijective₂_of_injective 5 [1, 1, 1] := fun h => by
  obtain ⟨_, hx⟩ := (@h Unit Bool Unit (fun _ => true) id (fun b => ⟨b, rfl⟩) (fun _ _ _ => rfl)).1.2 false
  exact Bool.noConfusion hx

-- `Function.Surjective.bijective₂_of_injective` idx 6: necessary (f = id on Unit, g: Empty → Unit)
theorem c5_103 : ¬ dropL% Function.Surjective.bijective₂_of_injective 6 [1, 1, 1] := fun h => by
  obtain ⟨a, _⟩ := (@h Unit Unit Empty id Empty.elim (fun b => ⟨b, rfl⟩) (fun a => a.elim)).2.2 ()
  exact a.elim

-- `Function.Surjective.bijective₂_of_injective` idx 7: necessary (f: Bool → Unit, g = id)
theorem c5_104 : ¬ dropL% Function.Surjective.bijective₂_of_injective 7 [1, 1, 1] := fun h => absurd ((@h Bool Unit Bool (fun _ => ()) id (fun _ => ⟨true, rfl⟩) (fun b => ⟨b, rfl⟩)).1.1 (a₁ := true) (a₂ := false) rfl) (by decide)

-- `Function.Injective.piMap` idx 4: necessary (ι = Unit, f: Bool → Unit)
theorem c5_105 : ¬ dropL% Function.Injective.piMap 4 [1, 1, 1] := fun h => absurd (congrFun (@h Unit (fun _ => Bool) (fun _ => Unit) (fun _ _ => ()) (fun _ => true) (fun _ => false) rfl) ()) (by decide)

-- `Function.injective_comp_left_iff` idx 3: necessary (α = Empty, g: Bool → Unit)
theorem c5_106 : ¬ dropL% Function.injective_comp_left_iff 3 [1, 1, 1] := fun h => absurd ((@h Empty Bool Unit (fun _ => ())).mp (fun a b _ => funext fun e => e.elim) (a₁ := true) (a₂ := false) rfl) (by decide)

-- `Function.Injective.dite` idx 6: necessary (p = True, f constant)
theorem c5_107 : ¬ dropL% Function.Injective.dite 6 [1, 1] := fun h => absurd (@h Bool Unit (fun _ => True) _ (fun _ => ()) (fun _ => ()) (fun a => (a.2 trivial).elim) (by intro x x' hx hx'; exact (hx' trivial).elim) true false rfl) (by decide)

-- `Function.Injective.dite` idx 7: necessary (p = False, f' constant)
theorem c5_108 : ¬ dropL% Function.Injective.dite 7 [1, 1] := fun h => absurd (@h Bool Unit (fun _ => False) _ (fun _ => ()) (fun _ => ()) (fun a => a.2.elim) (by intro x x' hx hx'; exact hx.elim) true false rfl) (by decide)

-- `Function.Surjective.of_comp_left` idx 6: necessary (f: Bool → Unit, g = const true)
theorem c5_109 : ¬ dropL% Function.Surjective.of_comp_left 6 [1, 1, 1] := fun h => by
  obtain ⟨_, hx⟩ := @h Bool Unit Unit (fun _ => ()) (fun _ => true) (fun _ => ⟨(), rfl⟩) false
  exact Bool.noConfusion hx

-- `Function.Injective.bijective₂_of_surjective` idx 5: necessary (f: Bool → Unit, g = id)
theorem c5_110 : ¬ dropL% Function.Injective.bijective₂_of_surjective 5 [1, 1, 1] := fun h => absurd ((@h Bool Unit Bool (fun _ => ()) id (fun _ _ h => h) (fun _ => ⟨true, rfl⟩)).1.1 (a₁ := true) (a₂ := false) rfl) (by decide)

-- `Function.Injective.bijective₂_of_surjective` idx 6: necessary (f = id on Unit, g: Bool → Unit)
theorem c5_111 : ¬ dropL% Function.Injective.bijective₂_of_surjective 6 [1, 1, 1] := fun h => absurd ((@h Unit Unit Bool id (fun _ => ()) (fun _ _ h => h) (fun _ => ⟨true, rfl⟩)).2.1 (a₁ := true) (a₂ := false) rfl) (by decide)

-- `Function.Injective.bijective₂_of_surjective` idx 7: necessary (f: Unit → Bool, g = id)
theorem c5_112 : ¬ dropL% Function.Injective.bijective₂_of_surjective 7 [1, 1, 1] := fun h => by
  obtain ⟨_, hx⟩ := (@h Unit Bool Unit (fun _ => true) id (fun _ _ _ => rfl) (fun _ _ h => h)).1.2 false
  exact Bool.noConfusion hx

-- `Function.Surjective.forall₃` idx 3: necessary (α = Empty, p = False)
theorem c5_113 : ¬ dropL% Function.Surjective.forall₃ 3 [1, 1] := fun h => (@h Empty Unit Empty.elim (fun _ _ _ => False)).mpr (fun a => a.elim) () () ()

-- `Function.Surjective.exists₂` idx 3: necessary (α = Empty, p = True)
theorem c5_114 : ¬ dropL% Function.Surjective.exists₂ 3 [1, 1] := fun h => by
  obtain ⟨a, _⟩ := (@h Empty Unit Empty.elim (fun _ _ => True)).mp ⟨(), (), trivial⟩
  exact a.elim

-- `Function.Surjective.exists₃` idx 3: necessary (α = Empty, p = True)
theorem c5_115 : ¬ dropL% Function.Surjective.exists₃ 3 [1, 1] := fun h => by
  obtain ⟨a, _⟩ := (@h Empty Unit Empty.elim (fun _ _ _ => True)).mp ⟨(), (), (), trivial⟩
  exact a.elim

-- `Function.injective_comp_right_iff_surjective` idx 4: necessary (γ = Unit, f: Empty → Unit)
theorem c5_116 : ¬ dropL% Function.injective_comp_right_iff_surjective 4 [1, 1, 0] := fun h => by
  obtain ⟨a, _⟩ := (@h Empty Unit Empty.elim Unit).mp (fun _ _ _ => funext fun _ => rfl) ()
  exact a.elim

-- `Function.Surjective.right_cancellable` idx 4: necessary (α = Empty, g₁ = id, g₂ = not)
theorem c5_117 : ¬ dropL% Function.Surjective.right_cancellable 4 [1, 1, 1] := fun h => absurd (congrFun ((@h Empty Bool Bool Empty.elim id not).mp (funext fun e => e.elim)) true) (by decide)

-- `Function.Injective.existsUnique_iff_exists` idx 3: necessary (f: Bool → Unit)
theorem c5_118 : ¬ dropL% Function.Injective.existsUnique_iff_exists 3 [1, 1] := fun h => by
  obtain ⟨a, _, hu⟩ := (@h Bool Unit (fun _ => ()) ()).mpr ⟨true, rfl⟩
  exact absurd ((hu true rfl).trans (hu false rfl).symm) (by decide)

-- `Function.Bijective.of_comp_iff'` idx 4: necessary (f: Bool → Unit, g = id)
theorem c5_119 : ¬ dropL% Function.Bijective.of_comp_iff' 4 [1, 1, 1] := fun h => absurd (((@h Bool Unit Bool (fun _ => ()) id).mpr ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩).1 (a₁ := true) (a₂ := false) rfl) (by decide)

-- `Function.Bijective.of_comp_left` idx 6: necessary (f: Bool → Unit, g: Unit → Bool const true)
theorem c5_120 : ¬ dropL% Function.Bijective.of_comp_left 6 [1, 1, 1] := fun h => by
  obtain ⟨_, hx⟩ := (@h Bool Unit Unit (fun _ => ()) (fun _ => true) ⟨fun _ _ _ => rfl, fun _ => ⟨(), rfl⟩⟩).2 false
  exact Bool.noConfusion hx

-- `Function.IsPartialInv.get_eq` idx 6: necessary (f: Unit → Bool const true, g its partial inverse, x = false)
theorem c5_121 : ¬ indepL% Function.IsPartialInv.get_eq 6 [0, 1] := fun h => absurd (@h Unit Bool (fun _ => true) (fun b => if b then some () else none) (by intro x y; revert x y; decide) false) (by decide)

-- `Function.injective_of_isPartialInv_right` idx 8: necessary (f: Unit → Bool const true, x=false, y=true)
theorem c5_122 : ¬ dropL% Function.injective_of_isPartialInv_right 8 [0, 1] := fun h => absurd (@h Unit Bool (fun _ => true) (fun b => if b then some () else none) (by intro x y; revert x y; decide) false true () rfl) (by decide)

-- `Function.injective_of_isPartialInv_right` idx 9: necessary (f: Unit → Bool const true, x=true, y=false)
theorem c5_123 : ¬ dropL% Function.injective_of_isPartialInv_right 9 [0, 1] := fun h => absurd (@h Unit Bool (fun _ => true) (fun b => if b then some () else none) (by intro x y; revert x y; decide) true false () rfl) (by decide)

-- `Function.IsPartialInv.comp` idx 7: necessary (f = id, g = none (not partial inverse), h = id, i = some)
theorem c5_124 : ¬ dropL% Function.IsPartialInv.comp 7 [0, 0, 1] := fun h => by
  have := ((@h Unit Unit Unit id (fun _ => none) id some (by intro x y; revert x y; decide)) () ()).mpr rfl
  simp at this

-- `Function.IsPartialInv.comp` idx 8: necessary (f = id, g = some, h = id, i = none)
theorem c5_125 : ¬ dropL% Function.IsPartialInv.comp 8 [0, 0, 1] := fun h => by
  have := ((@h Unit Unit Unit id some id (fun _ => none) (by intro x y; revert x y; decide)) () ()).mpr rfl
  simp at this

-- `Function.RightInverse.comp` idx 7: necessary (f = g = const true, h = i = id)
theorem c5_126 : ¬ dropL% Function.RightInverse.comp 7 [1, 1, 1] := fun h => absurd (@h Bool Bool Bool (fun _ => true) (fun _ => true) id id (fun _ => rfl) false) (by decide)

-- `Function.LeftInverse.rightInverse_of_injective` idx 5: necessary (f: Bool → Unit, g = const true)
theorem c5_127 : ¬ dropL% Function.LeftInverse.rightInverse_of_injective 5 [1, 1] := fun h => absurd (@h Bool Unit (fun _ => ()) (fun _ => true) (fun _ => rfl) false) (by decide)

-- `Function.LeftInverse.rightInverse_of_surjective` idx 5: necessary (f: Bool → Unit, g = const true)
theorem c5_128 : ¬ dropL% Function.LeftInverse.rightInverse_of_surjective 5 [1, 1] := fun h => absurd (@h Bool Unit (fun _ => ()) (fun _ => true) (fun _ => rfl) false) (by decide)

-- `Function.RightInverse.leftInverse_of_surjective` idx 5: necessary (f: Unit → Bool const true, g: Bool → Unit)
theorem c5_129 : ¬ dropL% Function.RightInverse.leftInverse_of_surjective 5 [1, 1] := fun h => absurd (@h Unit Bool (fun _ => true) (fun _ => ()) (fun _ => rfl) false) (by decide)

-- `Function.RightInverse.leftInverse_of_injective` idx 5: necessary (f: Unit → Bool const true, g: Bool → Unit)
theorem c5_130 : ¬ dropL% Function.RightInverse.leftInverse_of_injective 5 [1, 1] := fun h => absurd (@h Unit Bool (fun _ => true) (fun _ => ()) (fun _ => rfl) false) (by decide)

-- `Function.Injective.isPartialInv` idx 3: necessary (f: Bool → Unit)
theorem c5_131 : ¬ dropL% Function.Injective.isPartialInv 3 [0, 1] := fun h => by
  have h1 := ((@h Bool Unit (fun _ => ())) true ()).mpr rfl
  have h2 := ((@h Bool Unit (fun _ => ())) false ()).mpr rfl
  exact absurd (Option.some.inj (h1.symm.trans h2)) (by decide)

-- `Function.partialInv_left` idx 3: necessary (f: Bool → Unit)
theorem c5_132 : ¬ dropL% Function.partialInv_left 3 [0, 1] := fun h => absurd (Option.some.inj ((@h Bool Unit (fun _ => ()) true).symm.trans (@h Bool Unit (fun _ => ()) false))) (by decide)

-- `Function.invFun_neg` idx 2: necessary (α = Empty)
theorem c5_133 : ¬ indepL% Function.invFun_neg 2 [1, 1] := fun h => by
  have := @h Empty Unit Empty.elim () (fun ⟨a, _⟩ => a.elim)
  exact this.elim fun a => a.elim

-- `Function.invFun_neg` idx 5: necessary (f = id on Bool: invFun id b = b, not constant)
theorem c5_134 : ¬ dropL% Function.invFun_neg 5 [1, 1] := fun h => by
  have e1 : invFun (id : Bool → Bool) true = true := Function.invFun_eq (f := (id : Bool → Bool)) ⟨true, rfl⟩
  have e2 : invFun (id : Bool → Bool) false = false := Function.invFun_eq (f := (id : Bool → Bool)) ⟨false, rfl⟩
  have h1 := @h Bool Bool ⟨true⟩ id true
  have h2 := @h Bool Bool ⟨true⟩ id false
  exact absurd (e1.symm.trans (h1.trans (h2.symm.trans e2))) (by decide)

-- `Function.invFun_eq_of_injective_of_rightInverse` idx 2: necessary (α = β = Empty)
theorem c5_135 : ¬ indepL% Function.invFun_eq_of_injective_of_rightInverse 2 [1, 1] := fun h => by
  have := @h Empty Empty id id (fun _ _ h => h) (fun _ => rfl)
  exact this.elim fun a => a.elim

-- `Function.invFun_eq_of_injective_of_rightInverse` idx 5: necessary (f: Bool → Unit; two different right inverses)
theorem c5_136 : ¬ dropL% Function.invFun_eq_of_injective_of_rightInverse 5 [1, 1] := fun h => by
  have h1 := @h Bool Unit ⟨true⟩ (fun _ => ()) (fun _ => true) (fun _ => rfl)
  have h2 := @h Bool Unit ⟨true⟩ (fun _ => ()) (fun _ => false) (fun _ => rfl)
  exact absurd (congrFun (h1.symm.trans h2) ()) (by decide)

-- `Function.invFun_eq_of_injective_of_rightInverse` idx 6: necessary (f = id on Bool; g = const true and const false)
theorem c5_137 : ¬ dropL% Function.invFun_eq_of_injective_of_rightInverse 6 [1, 1] := fun h => by
  have h1 := @h Bool Bool ⟨true⟩ id (fun _ => true) (fun _ _ h => h)
  have h2 := @h Bool Bool ⟨true⟩ id (fun _ => false) (fun _ _ h => h)
  exact absurd (congrFun (h1.symm.trans h2) true) (by decide)

-- `Function.rightInverse_invFun` idx 2: necessary (α = β = Empty)
theorem c5_138 : ¬ indepL% Function.rightInverse_invFun 2 [1, 1] := fun h => by
  have := @h Empty Empty id (fun b => ⟨b, rfl⟩)
  exact this.elim fun a => a.elim

-- `Function.leftInverse_invFun` idx 2: necessary (α = β = Empty)
theorem c5_139 : ¬ indepL% Function.leftInverse_invFun 2 [1, 1] := fun h => by
  have := @h Empty Empty id (fun _ _ h => h)
  exact this.elim fun a => a.elim

-- `Function.leftInverse_invFun` idx 4: necessary (f: Bool → Unit)
theorem c5_140 : ¬ dropL% Function.leftInverse_invFun 4 [1, 1] := fun h => absurd ((@h Bool Unit ⟨true⟩ (fun _ => ()) true).symm.trans (@h Bool Unit ⟨true⟩ (fun _ => ()) false)) (by decide)

-- `Function.invFun_surjective` idx 2: necessary (α = β = Empty)
theorem c5_141 : ¬ indepL% Function.invFun_surjective 2 [1, 1] := fun h => by
  have := @h Empty Empty id (fun _ _ h => h)
  exact this.elim fun a => a.elim

-- `Function.invFun_surjective` idx 4: necessary (f: Bool → Unit)
theorem c5_142 : ¬ dropL% Function.invFun_surjective 4 [1, 1] := fun h => by
  obtain ⟨u, hu⟩ := @h Bool Unit ⟨true⟩ (fun _ => ()) true
  obtain ⟨v, hv⟩ := @h Bool Unit ⟨true⟩ (fun _ => ()) false
  cases u; cases v
  exact absurd (hu.symm.trans hv) (by decide)

-- `Function.invFun_comp` idx 2: necessary (α = β = Empty)
theorem c5_143 : ¬ indepL% Function.invFun_comp 2 [1, 1] := fun h => by
  have := @h Empty Empty id (fun _ _ h => h)
  exact this.elim fun a => a.elim

-- `Function.invFun_comp` idx 4: necessary (f: Bool → Unit)
theorem c5_144 : ¬ dropL% Function.invFun_comp 4 [1, 1] := fun h => by
  have := @h Bool Unit ⟨true⟩ (fun _ => ())
  exact absurd ((congrFun this true).symm.trans (congrFun this false)) (by decide)

-- `Function.Injective.hasLeftInverse` idx 2: necessary (α = Empty, β = Unit)
theorem c5_145 : ¬ dropL% Function.Injective.hasLeftInverse 2 [1, 1] := fun h => by
  obtain ⟨g, _⟩ := @h Empty Unit Empty.elim (fun a => a.elim)
  exact (g ()).elim

-- `Function.Injective.hasLeftInverse` idx 4: necessary (f: Bool → Unit)
theorem c5_146 : ¬ dropL% Function.Injective.hasLeftInverse 4 [1, 1] := fun h => by
  obtain ⟨g, hg⟩ := @h Bool Unit ⟨true⟩ (fun _ => ())
  exact absurd ((hg true).symm.trans (hg false)) (by decide)

-- `Function.injective_iff_hasLeftInverse` idx 2: necessary (α = Empty, β = Unit)
theorem c5_147 : ¬ dropL% Function.injective_iff_hasLeftInverse 2 [1, 1] := fun h => by
  obtain ⟨g, _⟩ := (@h Empty Unit Empty.elim).mp (fun a => a.elim)
  exact (g ()).elim

-- `Function.Surjective.hasRightInverse` idx 3: necessary (f: Unit → Bool const true)
theorem c5_148 : ¬ dropL% Function.Surjective.hasRightInverse 3 [1, 1] := fun h => by
  obtain ⟨g, hg⟩ := @h Unit Bool (fun _ => true)
  exact Bool.noConfusion (hg false)

-- `Function.surjective_to_subsingleton` idx 2: necessary (α = Empty, β = Unit)
theorem c5_149 : ¬ dropL% Function.surjective_to_subsingleton 2 [1, 1] := fun h => by
  obtain ⟨a, _⟩ := @h Empty Unit _ Empty.elim ()
  exact a.elim

-- `Function.bijective_of_subsingleton'` idx 2: necessary (α = Empty, β = Unit)
theorem c5_150 : ¬ dropL% Function.bijective_of_subsingleton' 2 [1, 1] := fun h => by
  obtain ⟨a, _⟩ := (@h Empty Unit _ _ Empty.elim).2 ()
  exact a.elim

-- `Function.Surjective.piMap` idx 4: necessary (ι = Unit, f: Unit → Bool const true)
theorem c5_151 : ¬ dropL% Function.Surjective.piMap 4 [1, 1, 1] := fun h => by
  obtain ⟨a, ha⟩ := @h Unit (fun _ => Unit) (fun _ => Bool) (fun _ _ => true) (fun _ => false)
  exact Bool.noConfusion (congrFun ha ())

-- `Function.surjective_comp_left_iff` idx 3: necessary (α = Empty, g: Unit → Bool)
theorem c5_152 : ¬ dropL% Function.surjective_comp_left_iff 3 [1, 1, 1] := fun h => by
  obtain ⟨_, hx⟩ := (@h Empty Unit Bool (fun _ => true)).mp (fun k => ⟨Empty.elim, funext fun e => e.elim⟩) false
  exact Bool.noConfusion hx

-- `Function.Bijective.piMap` idx 4: necessary (ι = Unit, f: Bool → Unit)
theorem c5_153 : ¬ dropL% Function.Bijective.piMap 4 [1, 1, 1] := fun h => absurd (congrFun ((@h Unit (fun _ => Bool) (fun _ => Unit) (fun _ _ => ())).1 (a₁ := fun _ => true) (a₂ := fun _ => false) rfl) ()) (by decide)

-- `Function.update_of_ne` idx 5: necessary (a = a')
theorem c5_154 : ¬ dropL% Function.update_of_ne 5 [1, 1] := fun h => by
  have := @h Bool (fun _ => Bool) _ true true true (fun _ => false)
  simp at this

-- `Function.surjective_eval` idx 2: necessary (β true = Bool, β false = Empty)
theorem c5_155 : ¬ dropL% Function.surjective_eval 2 [1, 1] := fun h => by
  obtain ⟨x, _⟩ := @h Bool (fun b => cond b Bool Empty) true (true : Bool)
  exact (x false).elim

-- `Function.update_apply_of_injective` idx 7: necessary (f: Bool → Unit)
theorem c5_156 : ¬ dropL% Function.update_apply_of_injective 7 [1, 1, 1] := fun h => by
  have := @h Unit (fun _ => Bool) Bool _ _ (fun _ => false) (fun _ => ()) true true false
  simp at this

-- `Function.rec_update` idx 7: necessary (recursor constant true, ctor = id on Unit)
theorem c5_157 : ¬ dropL% Function.rec_update 7 [1, 1, 1] := fun h => by
  have := @h Unit Unit (fun _ => Bool) _ _ id (fun _ _ => true) (fun _ _ _ _ => rfl) (fun _ => true) () false
  have := congrFun this ()
  simp at this

-- `Function.rec_update` idx 8: necessary (κ = Bool, ctor = const true, recursor f _ = f ())
theorem c5_158 : ¬ dropL% Function.rec_update 8 [1, 1, 1] := fun h => by
  have := @h Unit Bool (fun _ => Bool) _ _ (fun _ => true) (fun f _ => f ()) (fun _ _ => rfl) (fun _ => false) () true
  have := congrFun this false
  simp at this

-- `Function.update_comm` idx 5: necessary (a = b, v ≠ w)
theorem c5_159 : ¬ dropL% Function.update_comm 5 [1, 1] := fun h => by
  have := congrFun (@h Bool _ (fun _ => Bool) true true true false (fun _ => true)) true
  simp at this

-- `Pi.map_injective` idx 3: necessary (α true = Empty, α false = Bool, β = Unit)
theorem c5_160 : ¬ dropL% Pi.map_injective 3 [1, 1, 1] := fun h => by
  have := (@h Bool (fun b => cond b Empty Bool) (fun _ => Unit) (fun _ _ => ())).mp (fun x _ _ => (x true).elim) false (a₁ := true) (a₂ := false) rfl
  exact Bool.noConfusion (this : (true : Bool) = false)

-- `Function.FactorsThrough.extend_apply` idx 5: necessary (f: Bool → Unit, g = id)
theorem c5_161 : ¬ dropL% Function.FactorsThrough.extend_apply 5 [1, 1, 1] := fun h => absurd ((@h Bool Unit Bool (fun _ => ()) id (fun _ => true) true).symm.trans (@h Bool Unit Bool (fun _ => ()) id (fun _ => true) false)) (by decide)

-- `Function.extend_apply'` idx 7: necessary (f = id, g = const true, e' = const false)
theorem c5_162 : ¬ dropL% Function.extend_apply' 7 [1, 1, 1] := fun h => by
  have h1 := @h Bool Bool Bool id (fun _ => true) (fun _ => false) true
  have h2 := Function.Injective.extend_apply (f := (id : Bool → Bool)) Function.injective_id (fun _ => true) (fun _ => false) true
  exact absurd (h2.symm.trans h1) (by decide)

-- `Function.Injective.extend_comp` idx 5: removable
theorem c5_163 : drop% Function.Injective.extend_comp 5 := by
  intro γ α₁ α₂ α₃ f₁₂ f₂₃ h₂₃ g e'
  funext a
  by_cases h₃ : ∃ b, f₂₃ b = a
  · obtain ⟨b, rfl⟩ := h₃
    rw [Function.Injective.extend_apply h₂₃]
    have hp : (fun c => (f₂₃ ∘ f₁₂) c = f₂₃ b) = (fun c => f₁₂ c = b) :=
      funext fun c => propext h₂₃.eq_iff
    unfold Function.extend
    rw [hp]
    rfl
  · rw [Function.extend_apply' _ _ _ h₃, Function.extend_apply']
    exact fun ⟨c, hc⟩ => h₃ ⟨f₁₂ c, hc⟩

-- `Function.Injective.extend_comp` idx 7: necessary (f₂₃: Bool → Unit constant with chosen preimage c, f₁₂ = const (!c), g = const false, e' = const true)
theorem c5_164 : ¬ dropL% Function.Injective.extend_comp 7 [1, 1, 1, 1] := fun h => by
  let f23 : Bool → Unit := fun _ => ()
  have hex : ∃ a, f23 a = () := ⟨true, rfl⟩
  let c := Classical.choose hex
  have := congrFun (@h Bool Unit Bool Unit (fun _ : Unit => !c) (fun _ _ _ => rfl) f23 (fun _ => false) (fun _ => true)) ()
  rw [Function.extend_def, dif_pos ⟨(), rfl⟩, Function.extend_def, dif_pos hex, Function.extend_def, dif_neg] at this
  · exact Bool.noConfusion this
  · rintro ⟨_, hc⟩; exact Bool.not_ne_self c hc

-- `Function.factorsThrough_iff` idx 5: necessary (α = γ = Empty, β = Unit)
theorem c5_165 : ¬ dropL% Function.factorsThrough_iff 5 [1, 1, 1] := fun h => by
  obtain ⟨e, _⟩ := (@h Empty Unit Empty Empty.elim id).mp (fun a => a.elim)
  exact (e ()).elim

-- `Function.extend_injective` idx 4: necessary (f: Bool → Unit constant with chosen preimage c: g = id and g = const c have the same extension)
theorem c5_166 : ¬ dropL% Function.extend_injective 4 [1, 1, 1] := fun h => by
  let f23 : Bool → Unit := fun _ => ()
  have hex : ∃ a, f23 a = () := ⟨true, rfl⟩
  let c := Classical.choose hex
  have key : (fun g : Bool → Bool => extend f23 g (fun _ => true)) id = (fun g => extend f23 g (fun _ => true)) (fun _ => c) := by
    funext u
    cases u
    show extend f23 id (fun _ => true) () = extend f23 (fun _ => c) (fun _ => true) ()
    rw [Function.extend_def, Function.extend_def, dif_pos hex, dif_pos hex]
    rfl
  have := congrFun (@h Bool Unit Bool f23 (fun _ => true) id (fun _ => c) key) (!c)
  exact Bool.not_ne_self c this

-- `Function.FactorsThrough.extend_comp` idx 6: necessary (f: Bool → Unit, g = id)
theorem c5_167 : ¬ dropL% Function.FactorsThrough.extend_comp 6 [1, 1, 1] := fun h => by
  have := @h Bool Unit Bool (fun _ => ()) id (fun _ => true)
  exact absurd ((congrFun this true).symm.trans (congrFun this false)) (by decide)

-- `Function.Injective.extend_update` idx 6: necessary (f: Bool → Unit constant with chosen preimage c, i = !c)
theorem c5_168 : ¬ dropL% Function.Injective.extend_update 6 [1, 1, 1] := fun h => by
  let f23 : Bool → Unit := fun _ => ()
  have hex : ∃ a, f23 a = () := ⟨true, rfl⟩
  let c := Classical.choose hex
  have := congrFun (@h Bool Unit Bool f23 _ _ (fun _ => false) (fun _ => false) (!c) true) ()
  rw [Function.extend_def, dif_pos hex] at this
  rw [Function.update_of_ne (Bool.not_ne_self c).symm] at this
  simp at this

-- `Function.Injective.surjective_comp_right` idx 4: necessary (α = γ = Empty, β = Unit)
theorem c5_169 : ¬ dropL% Function.Injective.surjective_comp_right 4 [1, 1, 1] := fun h => by
  obtain ⟨g, _⟩ := @h Empty Unit Empty Empty.elim (fun a => a.elim) Empty.elim
  exact (g ()).elim

-- `Function.surjective_comp_right_iff_injective` idx 4: necessary (γ = Unit, f: Bool → Unit)
theorem c5_170 : ¬ dropL% Function.surjective_comp_right_iff_injective 4 [1, 1, 0] := fun h => absurd ((@h Bool Unit (fun _ => ()) Unit).mp (fun k => ⟨fun _ => (), funext fun _ => rfl⟩) (a₁ := true) (a₂ := false) rfl) (by decide)

-- `Function.FactorsThrough.comp_left` idx 6: necessary (f: Bool → Unit, g = g' = id)
theorem c5_171 : ¬ dropL% Function.FactorsThrough.comp_left 6 [1, 1, 1, 1] := fun h => absurd (@h Bool Unit Bool Bool (fun _ => ()) id id true false rfl) (by decide)

-- `Function.FactorsThrough.comp_right` idx 6: necessary (f: Bool → Unit, g = g' = id)
theorem c5_172 : ¬ dropL% Function.FactorsThrough.comp_right 6 [1, 1, 1, 1] := fun h => absurd (@h Bool Unit Bool Bool (fun _ => ()) id id true false rfl) (by decide)

-- `Function.Injective2.left'` idx 5: necessary (β = Empty)
theorem c5_173 : ¬ dropL% Function.Injective2.left' 5 [1, 1, 1] := fun h => absurd (@h Bool Empty Unit (fun _ e => e.elim) (fun _ _ b => b.elim) true false (funext fun e => e.elim)) (by decide)

-- `Function.Injective2.right'` idx 5: necessary (α = Empty)
theorem c5_174 : ¬ dropL% Function.Injective2.right' 5 [1, 1, 1] := fun h => absurd (@h Empty Bool Unit (fun e _ => e.elim) (fun a => a.elim) true false (funext fun e => e.elim)) (by decide)

-- `Std.Symm.forall_existsUnique_iff'` idx 2: necessary (r a b := b = true on Bool (not symmetric))
theorem c5_175 : ¬ dropL% Std.Symm.forall_existsUnique_iff' 2 [1] := fun h => by
  obtain ⟨f, hinv, hr⟩ := (@h Bool (fun _ b => b = true)).mp (fun a => ⟨true, rfl, fun y hy => hy⟩)
  have a1 : f false = true := cast (congrFun (congrFun hr false) true) rfl
  have a2 : f true = true := cast (congrFun (congrFun hr true) true) rfl
  have := hinv false
  rw [a1, a2] at this
  exact Bool.noConfusion this

-- `Symmetric.forall_existsUnique_iff'` idx 2: necessary (r a b := b = true on Bool (not symmetric))
theorem c5_176 : ¬ dropL% Symmetric.forall_existsUnique_iff' 2 [1] := fun h => by
  obtain ⟨f, hinv, hr⟩ := (@h Bool (fun _ b => b = true)).mp (fun a => ⟨true, rfl, fun y hy => hy⟩)
  have a1 : f false = true := cast (congrFun (congrFun hr false) true) rfl
  have a2 : f true = true := cast (congrFun (congrFun hr true) true) rfl
  have := hinv false
  rw [a1, a2] at this
  exact Bool.noConfusion this

-- `Std.Symm.forall_existsUnique_iff` idx 2: necessary (r a b := b = true on Bool (not symmetric))
theorem c5_177 : ¬ dropL% Std.Symm.forall_existsUnique_iff 2 [1] := fun h => by
  obtain ⟨f, hinv, hr⟩ := (@h Bool (fun _ b => b = true)).mp (fun a => ⟨true, rfl, fun y hy => hy⟩)
  have a1 : f false = true := (hr (a := false) (b := true)).mp rfl
  have a2 : f true = true := (hr (a := true) (b := true)).mp rfl
  have := hinv false
  rw [a1, a2] at this
  exact Bool.noConfusion this

-- `Symmetric.forall_existsUnique_iff` idx 2: necessary (r a b := b = true on Bool (not symmetric))
theorem c5_178 : ¬ dropL% Symmetric.forall_existsUnique_iff 2 [1] := fun h => by
  obtain ⟨f, hinv, hr⟩ := (@h Bool (fun _ b => b = true)).mp (fun a => ⟨true, rfl, fun y hy => hy⟩)
  have a1 : f false = true := (hr (a := false) (b := true)).mp rfl
  have a2 : f true = true := (hr (a := true) (b := true)).mp rfl
  have := hinv false
  rw [a1, a2] at this
  exact Bool.noConfusion this

-- `eq_mp_bijective` idx 2: necessary (Unit ≠ Empty)
theorem c5_179 : ¬ indepL% eq_mp_bijective 2 [1] := fun h => absurd (@h Unit Empty) (fun e => (cast e ()).elim)

-- `eq_mpr_bijective` idx 2: necessary (Unit ≠ Empty)
theorem c5_180 : ¬ indepL% eq_mpr_bijective 2 [1] := fun h => absurd (@h Unit Empty) (fun e => (cast e ()).elim)

-- `cast_bijective` idx 2: necessary (Unit ≠ Empty)
theorem c5_181 : ¬ indepL% cast_bijective 2 [1] := fun h => absurd (@h Unit Empty) (fun e => (cast e ()).elim)

-- `cast_inj` idx 2: necessary (Unit ≠ Empty)
theorem c5_182 : ¬ indepL% cast_inj 2 [0] := fun h => absurd (@h Unit Empty () ()) (fun e => (cast e ()).elim)

-- `Function.LeftInverse.eq_rec_eq` idx 5: necessary (f: Bool → Unit, g = const true)
theorem c5_183 : ¬ indepL% Function.LeftInverse.eq_rec_eq 5 [1, 1, 1] := fun h => absurd (@h Bool Unit (fun _ => Unit) (fun _ => ()) (fun _ => true) (fun _ => ()) true false) (by decide)

-- `Function.LeftInverse.eq_rec_on_eq` idx 5: necessary (f: Bool → Unit, g = const true)
theorem c5_184 : ¬ indepL% Function.LeftInverse.eq_rec_on_eq 5 [1, 1, 1] := fun h => absurd (@h Bool Unit (fun _ => Unit) (fun _ => ()) (fun _ => true) (fun _ => ()) true false) (by decide)

-- `Function.LeftInverse.cast_eq` idx 5: necessary (f: Bool → Unit, g = const true)
theorem c5_185 : ¬ indepL% Function.LeftInverse.cast_eq 5 [1, 1, 1] := fun h => absurd (@h Bool Unit (fun _ => Unit) (fun _ => ()) (fun _ => true) (fun _ => ()) true false) (by decide)

-- `Set.separatesPoints_mono` idx 4: necessary (A = univ, B = ∅)
theorem c5_186 : ¬ drop0% Set.separatesPoints_mono 4 := fun h => by
  obtain ⟨f, hf, _⟩ := @h Bool Bool univ ∅ (fun x y hxy => ⟨id, trivial, hxy⟩) true false (by decide)
  exact hf

-- `Set.separatesPoints_mono` idx 5: necessary (A = B = ∅)
theorem c5_187 : ¬ drop0% Set.separatesPoints_mono 5 := fun h => by
  obtain ⟨f, hf, _⟩ := @h Bool Bool ∅ ∅ (subset_refl _) true false (by decide)
  exact hf

-- `InvImage.equivalence` idx 4: necessary (r = False)
theorem c5_188 : ¬ dropL% InvImage.equivalence 4 [1, 1] := fun h => (@h Bool Bool (fun _ _ => False) id).refl true
