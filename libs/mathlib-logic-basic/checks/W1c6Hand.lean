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

namespace W1c6
/-- dropL% T i [l₁, …]: drop% T i with the universe parameters of T set to the given numerals (copied from mathlib-data W4c4). -/
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

/-- Boolean implication: neither associative nor idempotent. -/
def imp : Bool → Bool → Bool := fun a b => !a || b
theorem imp_not_assoc : ¬ Std.Associative imp := fun ⟨h⟩ => absurd (h false false false) (by decide)
theorem imp_not_idem : ¬ Std.IdempotentOp imp := fun ⟨h⟩ => absurd (h false) (by decide)
theorem and_assoc' : Std.Associative and := ⟨fun a b c => by cases a <;> cases b <;> cases c <;> rfl⟩
theorem and_idem' : Std.IdempotentOp and := ⟨fun a => by cases a <;> rfl⟩
theorem nsB : ¬ Subsingleton Bool := fun hs => absurd (@Subsingleton.elim _ hs true false) (by decide)
theorem npB : ¬ Pairwise (fun _ _ : Bool => False) := fun h => h (show true ≠ false by decide)
theorem nspB : ¬ (Set.univ : Set Bool).Pairwise (fun _ _ => False) :=
  fun h => h (Set.mem_univ true) (Set.mem_univ false) (by decide)
theorem ncoB : ¬ Function.IsConstOn (id : Bool → Bool) Set.univ :=
  fun h => absurd (h (Set.mem_univ true) (Set.mem_univ false)) (by decide)
/-- With the empty relation, a cut-expand step removes exactly one element. -/
theorem cut_bot {α : Type} {s' s : Multiset α} (h : Relation.CutExpand (fun _ _ : α => False) s' s) :
    Multiset.card s' + 1 = Multiset.card s := by
  obtain ⟨t, a, ht, he⟩ := h
  have : t = 0 := Multiset.eq_zero_of_forall_notMem fun x hx => ht x hx
  subst this
  have := congrArg Multiset.card he
  simpa using this
/-- For an irreflexive relation, a cut-expand step from a singleton replaces it by elements below it. -/
theorem cut_single {α : Type} {r : α → α → Prop} [Std.Irrefl r] {s' : Multiset α} {a : α}
    (h : Relation.CutExpand r s' {a}) : ∀ x ∈ s', r x a := by
  classical
  rw [Relation.cutExpand_iff] at h
  obtain ⟨t, b, ht, hb, rfl⟩ := h
  rw [Multiset.mem_singleton] at hb
  subst hb
  simpa using ht
/-- A descending chain gives an inaccessible start point. -/
theorem notAcc {β : Type} {R : β → β → Prop} (f : ℕ → β) (hf : ∀ n, R (f (n+1)) (f n)) : ¬ Acc R (f 0) := by
  intro h
  suffices ∀ x, Acc R x → ∀ n, f n = x → False from this _ h 0 rfl
  intro x hx
  induction hx with
  | intro x _ ih => intro n hn; exact ih (f (n+1)) (hn ▸ hf n) (n+1) rfl
theorem accSelf {β : Type} {R : β → β → Prop} {x : β} (h : R x x) : ¬ Acc R x := fun ha => by
  induction ha with
  | intro y _ ih => exact ih y h h
instance gtIrr : Std.Irrefl (fun a b : ℕ => a > b) := ⟨fun a => lt_irrefl a⟩
instance botIrr {α : Type} : Std.Irrefl (fun _ _ : α => False) := ⟨fun _ h => h⟩
/-- CutExpand along > on ℕ is not accessible at {0}. -/
theorem gtCut : ¬ Acc (Relation.CutExpand (fun a b : ℕ => a > b)) {0} :=
  notAcc (fun n => ({n} : Multiset ℕ)) fun n => Relation.cutExpand_singleton_singleton (Nat.lt_succ_self n)
end W1c6
-- `Function.Semiconj.comp_right` idx 7: necessary (f = id, ga = not, ga' = gb = gb' = id on Bool)
theorem c6_1 : ¬ drop0% Function.Semiconj.comp_right 7 :=
  fun h => absurd ((@h Bool Bool id not id id id (fun _ => rfl)) true) (by decide)

-- `Function.Semiconj.trans` idx 8: necessary (fab = fbc = id, ga = not, gb = gc = id on Bool)
theorem c6_2 : ¬ drop0% Function.Semiconj.trans 8 :=
  fun h => absurd ((@h Bool Bool Bool id id not id id (fun _ => rfl)) true) (by decide)

-- `Function.Semiconj.trans` idx 9: necessary (fab = fbc = id, ga = gb = id, gc = not on Bool)
theorem c6_3 : ¬ drop0% Function.Semiconj.trans 9 :=
  fun h => absurd ((@h Bool Bool Bool id id id id not (fun _ => rfl)) true) (by decide)

-- `Function.Semiconj.comp_left` idx 8: necessary (fab = fbc = id, ga = gb = id, gc = not on Bool)
theorem c6_4 : ¬ drop0% Function.Semiconj.comp_left 8 :=
  fun h => absurd ((@h Bool Bool Bool id id id id not (fun _ => rfl)) true) (by decide)

-- `Function.Semiconj.comp_left` idx 9: necessary (fab = fbc = id, ga = not, gb = gc = id on Bool)
theorem c6_5 : ¬ drop0% Function.Semiconj.comp_left 9 :=
  fun h => absurd ((@h Bool Bool Bool id id not id id (fun _ => rfl)) true) (by decide)

-- `Function.Semiconj.inverses_right` idx 7: necessary (f = ga = ga' = id, gb = gb' = not on Bool)
theorem c6_6 : ¬ drop0% Function.Semiconj.inverses_right 7 :=
  fun h => absurd ((@h Bool Bool id id id not not (fun _ => rfl) (fun x => by cases x <;> rfl)) true) (by decide)

-- `Function.Semiconj.inverses_right` idx 8: necessary (f = ga = gb = gb' = id, ga' = not on Bool)
theorem c6_7 : ¬ drop0% Function.Semiconj.inverses_right 8 :=
  fun h => absurd ((@h Bool Bool id id not id id (fun _ => rfl) (fun _ => rfl)) true) (by decide)

-- `Function.Semiconj.inverses_right` idx 9: necessary (f = ga = ga' = gb = id, gb' = not on Bool)
theorem c6_8 : ¬ drop0% Function.Semiconj.inverses_right 9 :=
  fun h => absurd ((@h Bool Bool id id id id not (fun _ => rfl) (fun _ => rfl)) true) (by decide)

-- `Function.Semiconj.inverse_left` idx 6: necessary (f = f' = id, ga = not, gb = id on Bool)
theorem c6_9 : ¬ drop0% Function.Semiconj.inverse_left 6 :=
  fun h => absurd ((@h Bool Bool id not id id (fun _ => rfl) (fun _ => rfl)) true) (by decide)

-- `Function.Semiconj.inverse_left` idx 7: necessary (α = Bool, β = Unit, f' = const true, ga = not)
theorem c6_10 : ¬ drop0% Function.Semiconj.inverse_left 7 :=
  fun h => absurd ((@h Bool Unit (fun _ => ()) not id (fun _ => true) (fun _ => rfl) (fun _ => rfl)) ()) (by decide)

-- `Function.Semiconj.inverse_left` idx 8: necessary (α = Bool, β = Option Bool, f = some, f' = getD false, gb sends none to some true)
theorem c6_11 : ¬ drop0% Function.Semiconj.inverse_left 8 :=
  fun h => absurd ((@h Bool (Option Bool) some id (fun o => if o = none then some true else o) (fun o => o.getD false) (fun x => by cases x <;> rfl) (fun x => rfl)) none) (by decide)

-- `Function.Semiconj.option_map` idx 5: necessary (f = id, ga = not, gb = id on Bool)
theorem c6_12 : ¬ drop0% Function.Semiconj.option_map 5 :=
  fun h => absurd ((@h Bool Bool id not id) (some true)) (by decide)

-- `Function.Semiconj.commute` idx 3: necessary (f = not, g = const true)
theorem c6_13 : ¬ drop0% Function.Semiconj.commute 3 :=
  fun h => absurd ((@h Bool not (fun _ => true)) true) (by decide)

-- `Function.Commute.semiconj` idx 3: necessary (f = not, g = const true)
theorem c6_14 : ¬ drop0% Function.Commute.semiconj 3 :=
  fun h => absurd ((@h Bool not (fun _ => true)) true) (by decide)

-- `Function.Commute.comp_right` idx 4: necessary (f = not, g = const true, g' = id)
theorem c6_15 : ¬ drop0% Function.Commute.comp_right 4 :=
  fun h => absurd ((@h Bool not (fun _ => true) id (fun _ => rfl)) true) (by decide)

-- `Function.Commute.comp_right` idx 5: necessary (f = not, g = id, g' = const true)
theorem c6_16 : ¬ drop0% Function.Commute.comp_right 5 :=
  fun h => absurd ((@h Bool not id (fun _ => true) (fun _ => rfl)) true) (by decide)

-- `Function.Commute.comp_left` idx 4: necessary (f = not, f' = id, g = const true)
theorem c6_17 : ¬ drop0% Function.Commute.comp_left 4 :=
  fun h => absurd ((@h Bool not id (fun _ => true) (fun _ => rfl)) true) (by decide)

-- `Function.Commute.comp_left` idx 5: necessary (f = id, f' = not, g = const true)
theorem c6_18 : ¬ drop0% Function.Commute.comp_left 5 :=
  fun h => absurd ((@h Bool id not (fun _ => true) (fun _ => rfl)) true) (by decide)

-- `Function.Commute.option_map` idx 3: necessary (f = not, g = const true)
theorem c6_19 : ¬ drop0% Function.Commute.option_map 3 :=
  fun h => absurd ((@h Bool not (fun _ => true)) (some true)) (by decide)

-- `Function.Semiconj₂.comp` idx 8: necessary (f = f' = id, ga = gb = and, gc = or)
theorem c6_20 : ¬ drop0% Function.Semiconj₂.comp 8 :=
  fun h => absurd ((@h Bool Bool Bool id and and id or (fun _ _ => rfl)) true false) (by decide)

-- `Function.Semiconj₂.comp` idx 9: necessary (f = f' = id, ga = or, gb = gc = and)
theorem c6_21 : ¬ drop0% Function.Semiconj₂.comp 9 :=
  fun h => absurd ((@h Bool Bool Bool id or and id and (fun _ _ => rfl)) true false) (by decide)

-- `Function.Semiconj₂.isAssociative_right` idx 6: necessary (f = id, ga = and, gb = Boolean implication (not associative))
theorem c6_22 : ¬ drop0% Function.Semiconj₂.isAssociative_right 6 :=
  fun h => W1c6.imp_not_assoc (@h Bool Bool id and W1c6.imp W1c6.and_assoc' Function.surjective_id)

-- `Function.Semiconj₂.isAssociative_right` idx 7: necessary (α = Unit, f = const true into Bool, gb = implication)
theorem c6_23 : ¬ drop0% Function.Semiconj₂.isAssociative_right 7 :=
  fun h => W1c6.imp_not_assoc (@h Unit Bool (fun _ => true) (fun _ _ => ()) W1c6.imp ⟨fun _ _ _ => rfl⟩ (fun _ _ => rfl))

-- `Function.Semiconj₂.isAssociative_left` idx 5: necessary (f = id, ga = gb = implication)
theorem c6_24 : ¬ drop0% Function.Semiconj₂.isAssociative_left 5 :=
  fun h => W1c6.imp_not_assoc (@h Bool Bool id W1c6.imp W1c6.imp (fun _ _ => rfl) Function.injective_id)

-- `Function.Semiconj₂.isAssociative_left` idx 6: necessary (f = id, ga = implication, gb = and)
theorem c6_25 : ¬ drop0% Function.Semiconj₂.isAssociative_left 6 :=
  fun h => W1c6.imp_not_assoc (@h Bool Bool id W1c6.imp and W1c6.and_assoc' Function.injective_id)

-- `Function.Semiconj₂.isAssociative_left` idx 7: necessary (β = Unit, ga = implication on Bool)
theorem c6_26 : ¬ drop0% Function.Semiconj₂.isAssociative_left 7 :=
  fun h => W1c6.imp_not_assoc (@h Bool Unit (fun _ => ()) W1c6.imp (fun _ _ => ()) ⟨fun _ _ _ => rfl⟩ (fun _ _ => rfl))

-- `Function.Semiconj₂.isIdempotent_right` idx 6: necessary (f = id, ga = and, gb = implication (not idempotent))
theorem c6_27 : ¬ drop0% Function.Semiconj₂.isIdempotent_right 6 :=
  fun h => W1c6.imp_not_idem (@h Bool Bool id and W1c6.imp W1c6.and_idem' Function.surjective_id)

-- `Function.Semiconj₂.isIdempotent_right` idx 7: necessary (α = Unit, f = const true, gb = implication)
theorem c6_28 : ¬ drop0% Function.Semiconj₂.isIdempotent_right 7 :=
  fun h => W1c6.imp_not_idem (@h Unit Bool (fun _ => true) (fun _ _ => ()) W1c6.imp ⟨fun _ => rfl⟩ (fun _ _ => rfl))

-- `Function.Semiconj₂.isIdempotent_left` idx 5: necessary (f = id, ga = gb = implication)
theorem c6_29 : ¬ drop0% Function.Semiconj₂.isIdempotent_left 5 :=
  fun h => W1c6.imp_not_idem (@h Bool Bool id W1c6.imp W1c6.imp (fun _ _ => rfl) Function.injective_id)

-- `Function.Semiconj₂.isIdempotent_left` idx 6: necessary (f = id, ga = implication, gb = and)
theorem c6_30 : ¬ drop0% Function.Semiconj₂.isIdempotent_left 6 :=
  fun h => W1c6.imp_not_idem (@h Bool Bool id W1c6.imp and W1c6.and_idem' Function.injective_id)

-- `Function.Semiconj₂.isIdempotent_left` idx 7: necessary (β = Unit, ga = implication on Bool)
theorem c6_31 : ¬ drop0% Function.Semiconj₂.isIdempotent_left 7 :=
  fun h => W1c6.imp_not_idem (@h Bool Unit (fun _ => ()) W1c6.imp (fun _ _ => ()) ⟨fun _ => rfl⟩ (fun _ _ => rfl))

-- `Function.IsConst.of_subsingleton_domain` idx 2: necessary (id on Bool)
theorem c6_32 : ¬ drop1% Function.IsConst.of_subsingleton_domain 2 :=
  fun h => absurd ((@h Bool Bool id) true false) (by decide)

-- `Function.IsConst.of_subsingleton_codomain` idx 2: necessary (id on Bool)
theorem c6_33 : ¬ drop1% Function.IsConst.of_subsingleton_codomain 2 :=
  fun h => absurd ((@h Bool Bool id) true false) (by decide)

-- `Function.IsConst.of_forall_eq` idx 4: necessary (id on Bool, b = true)
theorem c6_34 : ¬ drop1% Function.IsConst.of_forall_eq 4 :=
  fun h => absurd ((@h Bool Bool id true) true false) (by decide)

-- `Function.isConst_iff_exists_forall_eq` idx 2: necessary (α = β = Empty)
theorem c6_35 : ¬ drop1% Function.isConst_iff_exists_forall_eq 2 :=
  fun h => by obtain ⟨b, _⟩ := (@h Empty Empty id).1 (fun x => x.elim); exact b.elim

-- `Function.isConst_iff_exists_forall_eq_of_nonempty_domain` idx 2: necessary (α = β = Empty)
theorem c6_36 : ¬ drop1% Function.isConst_iff_exists_forall_eq_of_nonempty_domain 2 :=
  fun h => by obtain ⟨b, _⟩ := (@h Empty Empty id).1 (fun x => x.elim); exact b.elim

-- `Function.isConst_iff_exists_eq_const` idx 2: necessary (α = β = Empty)
theorem c6_37 : ¬ drop1% Function.isConst_iff_exists_eq_const 2 :=
  fun h => by obtain ⟨b, _⟩ := (@h Empty Empty id).1 (fun x => x.elim); exact b.elim

-- `Function.IsConst.exists_eq_const` idx 2: necessary (α = β = Empty)
theorem c6_38 : ¬ drop1% Function.IsConst.exists_eq_const 2 :=
  fun h => by obtain ⟨b, _⟩ := (@h Empty Empty id (fun x => x.elim)); exact b.elim

-- `Function.isConst_iff_exists_eq_const_of_nonempty_domain` idx 2: necessary (α = β = Empty)
theorem c6_39 : ¬ drop1% Function.isConst_iff_exists_eq_const_of_nonempty_domain 2 :=
  fun h => by obtain ⟨b, _⟩ := (@h Empty Empty id).1 (fun x => x.elim); exact b.elim

-- `Function.IsConst.comp_left` idx 4: necessary (f = g = id on Bool)
theorem c6_40 : ¬ drop1% Function.IsConst.comp_left 4 :=
  fun h => absurd ((@h Bool Bool Bool id id) true false) (by decide)

-- `Function.IsConst.comp_right` idx 4: necessary (f = g = id on Bool)
theorem c6_41 : ¬ drop1% Function.IsConst.comp_right 4 :=
  fun h => absurd ((@h Bool Bool Bool id id) true false) (by decide)

-- `Function.not_isConst_of_apply_ne` idx 5: necessary (f = id on Unit (constant))
theorem c6_42 : ¬ drop1% Function.not_isConst_of_apply_ne 5 :=
  fun h => (@h Unit Unit id () ()) (fun _ _ => rfl)

-- `Function.IsConst.injective_iff` idx 3: necessary (f = id on Bool)
theorem c6_43 : ¬ drop1% Function.IsConst.injective_iff 3 :=
  fun h => W1c6.nsB ((@h Bool Bool id).1 Function.injective_id)

-- `Function.Injective.isConst_iff` idx 3: necessary (f = const true on Bool)
theorem c6_44 : ¬ drop1% Function.Injective.isConst_iff 3 :=
  fun h => W1c6.nsB ((@h Bool Bool (fun _ => true)).1 (fun _ _ => rfl))

-- `Function.isConst_and_surjective_iff_of_nonempty` idx 2: necessary (α = Empty, β = Unit)
theorem c6_45 : ¬ drop1% Function.isConst_and_surjective_iff_of_nonempty 2 :=
  fun h => by obtain ⟨_, hs⟩ := (@h Empty Unit Empty.elim).2 inferInstance; obtain ⟨x, _⟩ := hs (); exact x.elim

-- `Function.IsConst.surjective_iff` idx 2: necessary (α = Empty, β = Unit)
theorem c6_46 : ¬ drop1% Function.IsConst.surjective_iff 2 :=
  fun h => by obtain ⟨x, _⟩ := (@h Empty Unit Empty.elim (fun x => x.elim)).2 inferInstance (); exact x.elim

-- `Function.IsConst.surjective_iff` idx 4: necessary (f = id on Bool)
theorem c6_47 : ¬ drop1% Function.IsConst.surjective_iff 4 :=
  fun h => W1c6.nsB ((@h Bool Bool ⟨true⟩ id).1 Function.surjective_id)

-- `Function.Surjective.isConst_iff` idx 3: necessary (f = const true on Bool)
theorem c6_48 : ¬ drop1% Function.Surjective.isConst_iff 3 :=
  fun h => W1c6.nsB ((@h Bool Bool (fun _ => true)).1 (fun _ _ => rfl))

-- `Function.IsConst.isConstOn` idx 4: necessary (f = id on Bool, s = univ)
theorem c6_49 : ¬ dropL% Function.IsConst.isConstOn 4 [1, 0] :=
  fun h => W1c6.ncoB (@h Bool Bool id Set.univ)

-- `Function.IsConstOn.anti` idx 5: necessary (f = id, s = t = univ on Bool)
theorem c6_50 : ¬ dropL% Function.IsConstOn.anti 5 [1, 0] :=
  fun h => W1c6.ncoB (@h Bool Bool id Set.univ Set.univ subset_rfl)

-- `Function.IsConstOn.anti` idx 6: necessary (f = id, s = univ, t = ∅)
theorem c6_51 : ¬ dropL% Function.IsConstOn.anti 6 [1, 0] :=
  fun h => W1c6.ncoB (@h Bool Bool id Set.univ ∅ (fun x hx => absurd hx (Set.notMem_empty x)))

-- `Function.IsConstOn.of_eqOn` idx 5: necessary (f = g = id, s = univ)
theorem c6_52 : ¬ drop0% Function.IsConstOn.of_eqOn 5 :=
  fun h => W1c6.ncoB (@h Bool Bool id id Set.univ (fun _ _ => rfl))

-- `Function.IsConstOn.of_eqOn` idx 6: necessary (f = const true, g = id, s = univ)
theorem c6_53 : ¬ drop0% Function.IsConstOn.of_eqOn 6 :=
  fun h => W1c6.ncoB (@h Bool Bool (fun _ => true) id Set.univ (fun _ _ _ _ => rfl))

-- `Function.IsConstOn.congr` idx 6: necessary (f = g = id, s = t = univ)
theorem c6_54 : ¬ drop0% Function.IsConstOn.congr 6 :=
  fun h => W1c6.ncoB (@h Bool Bool id id Set.univ Set.univ (fun _ _ => rfl) rfl)

-- `Function.IsConstOn.congr` idx 7: necessary (f = const true, g = id, s = t = univ)
theorem c6_55 : ¬ drop0% Function.IsConstOn.congr 7 :=
  fun h => W1c6.ncoB (@h Bool Bool (fun _ => true) id Set.univ Set.univ (fun _ _ _ _ => rfl) rfl)

-- `Function.IsConstOn.congr` idx 8: necessary (f = g = id, s = ∅, t = univ)
theorem c6_56 : ¬ drop0% Function.IsConstOn.congr 8 :=
  fun h => W1c6.ncoB (@h Bool Bool id id ∅ Set.univ (fun x hx => absurd hx (Set.notMem_empty x)) (fun _ _ => rfl))

-- `Set.EqOn.isConstOn_iff` idx 5: necessary (f = const true, g = id, s = univ)
theorem c6_57 : ¬ drop0% Set.EqOn.isConstOn_iff 5 :=
  fun h => W1c6.ncoB ((@h Bool Bool (fun _ => true) id Set.univ).1 (fun _ _ _ _ => rfl))

-- `Function.IsConstOn.of_subsingleton` idx 3: necessary (s = univ in Bool, f = id)
theorem c6_58 : ¬ dropL% Function.IsConstOn.of_subsingleton 3 [1, 0] :=
  fun h => W1c6.ncoB (@h Bool Bool Set.univ id)

-- `Function.IsConstOn.of_forall_eq` idx 5: necessary (f = id, s = univ, b = true)
theorem c6_59 : ¬ dropL% Function.IsConstOn.of_forall_eq 5 [1, 0] :=
  fun h => W1c6.ncoB (@h Bool Bool id Set.univ true)

-- `Function.isConstOn_iff_exists_forall_eq` idx 2: necessary (α = β = Empty, s = ∅)
theorem c6_60 : ¬ dropL% Function.isConstOn_iff_exists_forall_eq 2 [1, 0] :=
  fun h => by obtain ⟨b, _⟩ := (@h Empty Empty id ∅).1 (fun x hx => x.elim); exact b.elim

-- `Function.isConstOn_iff_exists_forall_eq_of_nonempty` idx 4: necessary (α = β = Empty, s = ∅)
theorem c6_61 : ¬ dropL% Function.isConstOn_iff_exists_forall_eq_of_nonempty 4 [1, 0] :=
  fun h => by obtain ⟨b, _⟩ := (@h Empty Empty id ∅).1 (fun x hx => x.elim); exact b.elim

-- `Function.isConstOn_iff_exists_eqOn_const` idx 2: necessary (α = β = Empty, s = ∅)
theorem c6_62 : ¬ drop0% Function.isConstOn_iff_exists_eqOn_const 2 :=
  fun h => by obtain ⟨b, _⟩ := (@h Empty Empty id ∅).1 (fun x hx => x.elim); exact b.elim

-- `Function.IsConstOn.exists_eqOn_const` idx 2: necessary (α = β = Empty, s = ∅)
theorem c6_63 : ¬ drop0% Function.IsConstOn.exists_eqOn_const 2 :=
  fun h => by obtain ⟨b, _⟩ := (@h Empty Empty id ∅ (fun x hx => x.elim)); exact b.elim

-- `Function.IsConstOn.exists_eqOn_const` idx 5: necessary (f = id on Bool, s = univ)
theorem c6_64 : ¬ drop0% Function.IsConstOn.exists_eqOn_const 5 :=
  fun h => by obtain ⟨b, hb⟩ := (@h Bool Bool ⟨true⟩ id Set.univ); have := hb (Set.mem_univ (!b)); revert this; cases b <;> decide

-- `Function.isConstOn_iff_exists_eqOn_const_of_nonempty` idx 4: necessary (α = β = Empty, s = ∅)
theorem c6_65 : ¬ drop0% Function.isConstOn_iff_exists_eqOn_const_of_nonempty 4 :=
  fun h => by obtain ⟨b, _⟩ := (@h Empty Empty id ∅).1 (fun x hx => x.elim); exact b.elim

-- `Function.IsConstOn.comp_left` idx 5: necessary (f = g = id on Bool, s = univ)
theorem c6_66 : ¬ dropL% Function.IsConstOn.comp_left 5 [1, 1, 0] :=
  fun h => W1c6.ncoB (@h Bool Bool Bool id Set.univ id)

-- `Function.IsConstOn.comp_right` idx 4: necessary (g = f = id on Bool, s = t = univ)
theorem c6_67 : ¬ drop0% Function.IsConstOn.comp_right 4 :=
  fun h => W1c6.ncoB (@h Bool Bool id Set.univ id Set.univ (fun _ _ => Set.mem_univ _))

-- `Function.IsConstOn.comp_right` idx 7: necessary (g = f = id, t = ∅, s = univ)
theorem c6_68 : ¬ drop0% Function.IsConstOn.comp_right 7 :=
  fun h => W1c6.ncoB (@h Bool Bool id ∅ (fun x hx => absurd hx (Set.notMem_empty x)) id Set.univ)

-- `Function.IsConst.isConstOn_comp` idx 3: necessary (g = f = id on Bool, s = univ)
theorem c6_69 : ¬ dropL% Function.IsConst.isConstOn_comp 3 [0, 1] :=
  fun h => W1c6.ncoB (@h Bool Bool id id Set.univ)

-- `Function.IsConstOn.injOn_iff` idx 4: necessary (f = id on Bool, s = univ)
theorem c6_70 : ¬ drop0% Function.IsConstOn.injOn_iff 4 :=
  fun h => absurd (((@h Bool Bool id Set.univ).1 (fun _ _ _ _ e => e)) (Set.mem_univ true) (Set.mem_univ false)) (by decide)

-- `Set.InjOn.isConstOn_iff` idx 4: necessary (f = const true on Bool, s = univ)
theorem c6_71 : ¬ drop0% Set.InjOn.isConstOn_iff 4 :=
  fun h => absurd (((@h Bool Bool (fun _ => true) Set.univ).1 (fun _ _ _ _ => rfl)) (Set.mem_univ true) (Set.mem_univ false)) (by decide)

-- `Function.Injective.beq_eq` idx 5: necessary (β = Bool with the always-false BEq, f = id)
theorem c6_72 : ¬ drop0% Function.Injective.beq_eq 5 :=
  fun h => absurd (@h Bool Bool inferInstance inferInstance ⟨fun _ _ => false⟩ id Function.injective_id true true) (by decide)

-- `dependsOn_iff_exists_comp` idx 3: necessary (ι = Unit, α = Empty, β = Empty, s = ∅)
theorem c6_73 : ¬ drop0% dependsOn_iff_exists_comp 3 :=
  fun h => by obtain ⟨g, _⟩ := (@h Unit (fun _ => Empty) Empty (fun x => (x ()).elim) ∅).1 (fun x _ _ => (x ()).elim); exact (g fun i => absurd i.2 (Set.notMem_empty _)).elim

-- `DependsOn.mono` idx 6: necessary (f = evaluation at () on Unit → Bool, s = univ, t = ∅)
theorem c6_74 : ¬ drop0% DependsOn.mono 6 :=
  fun h => absurd ((@h Unit (fun _ => Bool) Bool (fun x => x ()) Set.univ ∅ (fun x y hxy => hxy () trivial)) (x := fun _ => true) (y := fun _ => false) (fun i hi => absurd hi (Set.notMem_empty i))) (by decide)

-- `DependsOn.mono` idx 7: necessary (f = evaluation at (), s = t = ∅)
theorem c6_75 : ¬ drop0% DependsOn.mono 7 :=
  fun h => absurd ((@h Unit (fun _ => Bool) Bool (fun x => x ()) ∅ ∅ subset_rfl) (x := fun _ => true) (y := fun _ => false) (fun i hi => absurd hi (Set.notMem_empty i))) (by decide)

-- `DependsOn.empty` idx 4: necessary (f = evaluation at ())
theorem c6_76 : ¬ drop0% DependsOn.empty 4 :=
  fun h => absurd (@h Unit (fun _ => Bool) Bool (fun x => x ()) (fun _ => true) (fun _ => false)) (by decide)

-- `Function.Semiconj.iterate_left` idx 3: necessary (f = id, g 0 = id, g n = const true otherwise)
theorem c6_77 : ¬ drop0% Function.Semiconj.iterate_left 3 :=
  fun h => absurd ((@h Bool id (fun n x => if n = 0 then x else true) 1 0) false) (by decide)

-- `Function.Commute.iterate_iterate` idx 3: necessary (f = not, g = const true)
theorem c6_78 : ¬ drop0% Function.Commute.iterate_iterate 3 :=
  fun h => absurd ((@h Bool not (fun _ => true) 1 1) true) (by decide)

-- `Function.Commute.iterate_eq_of_map_eq` idx 6: necessary (f = not, g = id, n = 1)
theorem c6_79 : ¬ drop0% Function.Commute.iterate_eq_of_map_eq 6 :=
  fun h => absurd (@h Bool not id (fun _ => rfl) 1 true) (by decide)

-- `Function.Semiconj₂.iterate` idx 3: necessary (f = not, op = and, n = 1)
theorem c6_80 : ¬ drop0% Function.Semiconj₂.iterate 3 :=
  fun h => absurd ((@h Bool not and 1) true false) (by decide)

-- `Relation.cutExpand_le_invImage_lex` idx 3: necessary (r = ⊤ on Unit: CutExpand r {()} {()} but Lex is irreflexive)
theorem c6_81 : ¬ drop0% Relation.cutExpand_le_invImage_lex 3 :=
  fun h => by obtain ⟨i, _, hi⟩ := (@h Unit (fun _ _ => True) inferInstance) {()} {()} ⟨{()}, (), fun _ _ => trivial, rfl⟩; exact lt_irrefl _ hi

-- `Relation.cutExpand_singleton` idx 4: necessary (r = ⊥, s = {x}: card mismatch)
theorem c6_82 : ¬ drop0% Relation.cutExpand_singleton 4 :=
  fun h => absurd (W1c6.cut_bot (@h Unit (fun _ _ => False) {()} ())) (by decide)

-- `Relation.cutExpand_singleton_singleton` idx 4: necessary (r = ⊥, x' = x)
theorem c6_83 : ¬ drop0% Relation.cutExpand_singleton_singleton 4 :=
  fun h => absurd (W1c6.cut_bot (@h Unit (fun _ _ => False) () ())) (by decide)

-- `Relation.cutExpand_add_single` idx 5: necessary (r = ⊥, s = 0, a' = a)
theorem c6_84 : ¬ drop0% Relation.cutExpand_add_single 5 :=
  fun h => absurd (W1c6.cut_bot (@h Unit (fun _ _ => False) () () 0)) (by decide)

-- `Relation.cutExpand_single_add` idx 4: necessary (r = ⊥, s = 0, a' = a)
theorem c6_85 : ¬ drop0% Relation.cutExpand_single_add 4 :=
  fun h => absurd (W1c6.cut_bot (@h Unit (fun _ _ => False) () () 0)) (by decide)

-- `Relation.cutExpand_iff` idx 3: necessary (r = ⊤ on Unit, s = s' = 0)
theorem c6_86 : ¬ drop0% Relation.cutExpand_iff 3 :=
  fun h => by obtain ⟨t, a, _, ha, _⟩ := (@h Unit (fun _ _ => True) inferInstance 0 0).1 ⟨{()}, (), fun _ _ => trivial, rfl⟩; exact Multiset.notMem_zero a ha

-- `Relation.not_cutExpand_zero` idx 2: necessary (r = ⊤ on Unit: CutExpand r 0 0)
theorem c6_87 : ¬ drop0% Relation.not_cutExpand_zero 2 :=
  fun h => @h Unit (fun _ _ => True) 0 ⟨{()}, (), fun _ _ => trivial, rfl⟩

-- `Relation.cutExpand_closed` idx 2: necessary (r = Eq on Bool, p = (· = true), s = 0, s' = {false})
theorem c6_88 : ¬ drop0% Relation.cutExpand_closed 2 :=
  fun h => absurd (@h Bool (· = ·) (· = true) (fun e hp => e ▸ hp) {false} 0 ⟨{false, false}, false, by simp, by decide⟩ (by simp) false (by simp)) (by decide)

-- `Relation.cutExpand_closed` idx 4: necessary (r = < on Bool, p = (· = true), s = {true}, s' = {false})
theorem c6_89 : ¬ drop0% Relation.cutExpand_closed 4 :=
  fun h => absurd (@h Bool (· < ·) inferInstance (· = true) {false} {true} ⟨{false}, true, by simp, by decide⟩ (by simp) false (by simp)) (by decide)

-- `Relation.cutExpand_closed` idx 7: necessary (r = ⊥, s = {true}, s' = {false})
theorem c6_90 : ¬ drop0% Relation.cutExpand_closed 7 :=
  fun h => absurd (@h Bool (fun _ _ => False) inferInstance (· = true) (fun e _ => e.elim) {false} {true} (by simp) false (by simp)) (by decide)

-- `Relation.cutExpand_closed` idx 8: necessary (r = ⊥, s = {false, false}, s' = {false})
theorem c6_91 : ¬ drop0% Relation.cutExpand_closed 8 :=
  fun h => absurd (@h Bool (fun _ _ => False) inferInstance (· = true) (fun e _ => e.elim) {false} {false, false} ⟨0, false, by simp, by decide⟩ false (by simp)) (by decide)

-- `Relation.cutExpand_closed` idx 10: necessary (r = ⊥, s = {true}, s' = 0, a = false)
theorem c6_92 : ¬ drop0% Relation.cutExpand_closed 10 :=
  fun h => absurd (@h Bool (fun _ _ => False) inferInstance (· = true) (fun e _ => e.elim) 0 {true} ⟨0, true, by simp, by decide⟩ (by simp) false) (by decide)

-- `Relation.cutExpand_double` idx 5: necessary (r = < on Bool, a = a₁ = true, a₂ = false)
theorem c6_93 : ¬ drop0% Relation.cutExpand_double 5 :=
  fun h => absurd (W1c6.cut_single (@h Bool (· < ·) true true false (by decide)) true (by simp)) (by decide)

-- `Relation.cutExpand_double` idx 6: necessary (r = < on Bool, a = a₂ = true, a₁ = false)
theorem c6_94 : ¬ drop0% Relation.cutExpand_double 6 :=
  fun h => absurd (W1c6.cut_single (@h Bool (· < ·) true false true (by decide)) true (by simp)) (by decide)

-- `Relation.cutExpand_pair_left` idx 5: necessary (r = ⊥, all points equal: card mismatch)
theorem c6_95 : ¬ drop0% Relation.cutExpand_pair_left 5 :=
  fun h => absurd (W1c6.cut_bot (@h Unit (fun _ _ => False) () () ())) (by decide)

-- `Relation.cutExpand_pair_right` idx 5: necessary (r = ⊥, all points equal: card mismatch)
theorem c6_96 : ¬ drop0% Relation.cutExpand_pair_right 5 :=
  fun h => absurd (W1c6.cut_bot (@h Unit (fun _ _ => False) () () ())) (by decide)

-- `Relation.cutExpand_double_left` idx 6: necessary (r = < on Bool, a = a₁ = true, a₂ = b = false)
theorem c6_97 : ¬ drop0% Relation.cutExpand_double_left 6 :=
  fun h => by have hc := @h Bool (· < ·) true true false false (by decide); rw [show ({true, false, false} : Multiset Bool) = {true, false} + {false} by decide, show ({true, false} : Multiset Bool) = {true} + {false} by decide, Relation.cutExpand_add_right] at hc; exact absurd (W1c6.cut_single hc true (by simp)) (by decide)

-- `Relation.cutExpand_double_left` idx 7: necessary (r = < on Bool, a = a₂ = true, a₁ = b = false)
theorem c6_98 : ¬ drop0% Relation.cutExpand_double_left 7 :=
  fun h => by have hc := @h Bool (· < ·) true false true false (by decide); rw [show ({false, true, false} : Multiset Bool) = {false, true} + {false} by decide, show ({true, false} : Multiset Bool) = {true} + {false} by decide, Relation.cutExpand_add_right] at hc; exact absurd (W1c6.cut_single hc true (by simp)) (by decide)

-- `Relation.acc_of_singleton` idx 2: necessary (r = ⊤ on Unit, s = 0: CutExpand r 0 0)
theorem c6_99 : ¬ drop0% Relation.acc_of_singleton 2 :=
  fun h => W1c6.accSelf (R := Relation.CutExpand (fun _ _ : Unit => True)) ⟨{()}, (), fun _ _ => trivial, rfl⟩ (@h Unit (fun _ _ => True) 0 (fun a ha => absurd ha (Multiset.notMem_zero a)))

-- `Relation.acc_of_singleton` idx 4: necessary (r = > on ℕ (irreflexive, not well-founded), s = {0})
theorem c6_100 : ¬ drop0% Relation.acc_of_singleton 4 :=
  fun h => W1c6.gtCut (@h ℕ (fun a b => a > b) inferInstance {0})

-- `Acc.cutExpand` idx 2: necessary (r = (both true) on Bool, a = false: Acc r false but CutExpand r {false} {false})
theorem c6_101 : ¬ drop0% Acc.cutExpand 2 :=
  fun h => W1c6.accSelf (R := Relation.CutExpand (fun x y : Bool => x = true ∧ y = true)) ⟨{true}, true, by simp, rfl⟩ (@h Bool (fun x y => x = true ∧ y = true) false (Acc.intro _ fun y hy => absurd hy.2 (by decide)))

-- `Acc.cutExpand` idx 4: necessary (r = > on ℕ, a = 0)
theorem c6_102 : ¬ drop0% Acc.cutExpand 4 :=
  fun h => W1c6.gtCut (@h ℕ (fun a b => a > b) inferInstance 0)

-- `WellFounded.cutExpand` idx 2: necessary (r = > on ℕ, not well-founded)
theorem c6_103 : ¬ drop0% WellFounded.cutExpand 2 :=
  fun h => W1c6.gtCut ((@h ℕ (fun a b => a > b)).apply {0})

-- `instRightCommutativeOfCommutativeOfAssociative` idx 2: necessary (right projection on Bool: associative, not right-commutative)
theorem c6_104 : ¬ drop1% instRightCommutativeOfCommutativeOfAssociative 2 :=
  fun h => absurd ((@h Bool (fun _ b => b) ⟨fun _ _ _ => rfl⟩).right_comm true true false) (by decide)

-- `Pairwise.mono` idx 3: necessary (r = p = ⊥ on Bool)
theorem c6_105 : ¬ drop0% Pairwise.mono 3 :=
  fun h => W1c6.npB (@h Bool (fun _ _ => False) (fun _ _ => False) (fun _ _ e => e))

-- `Pairwise.mono` idx 4: necessary (r = ⊤, p = ⊥ on Bool)
theorem c6_106 : ¬ drop0% Pairwise.mono 4 :=
  fun h => W1c6.npB (@h Bool (fun _ _ => True) (fun _ _ => False) (fun _ _ _ => trivial))

-- `Subsingleton.pairwise` idx 2: necessary (α = Bool, r = ⊥)
theorem c6_107 : ¬ drop0% Subsingleton.pairwise 2 :=
  fun h => W1c6.npB (@h Bool (fun _ _ => False))

-- `Pairwise.comp_of_injective` idx 3: necessary (r = ⊥, f = id on Bool)
theorem c6_108 : ¬ drop0% Pairwise.comp_of_injective 3 :=
  fun h => (@h Bool Bool (fun _ _ => False) id Function.injective_id) (show true ≠ false by decide)

-- `Pairwise.comp_of_injective` idx 5: necessary (r = ≠ on Bool, f = const true)
theorem c6_109 : ¬ drop0% Pairwise.comp_of_injective 5 :=
  fun h => (@h Bool Bool (· ≠ ·) (fun _ _ e => e) (fun _ => true)) (show true ≠ false by decide) rfl

-- `Pairwise.of_comp_of_surjective` idx 4: necessary (r = ⊥, f = id on Bool)
theorem c6_110 : ¬ drop0% Pairwise.of_comp_of_surjective 4 :=
  fun h => W1c6.npB (@h Bool Bool (fun _ _ => False) id Function.surjective_id)

-- `Pairwise.of_comp_of_surjective` idx 5: necessary (β = Unit, α = Bool, r = ⊥)
theorem c6_111 : ¬ drop0% Pairwise.of_comp_of_surjective 5 :=
  fun h => W1c6.npB (@h Bool Unit (fun _ _ => False) (fun _ => true) (fun _ _ hij => (hij rfl).elim))

-- `Function.Bijective.pairwise_comp_iff` idx 4: necessary (β = Unit, α = Bool, r = ⊥)
theorem c6_112 : ¬ drop0% Function.Bijective.pairwise_comp_iff 4 :=
  fun h => W1c6.npB ((@h Bool Unit (fun _ _ => False) (fun _ => true)).1 (fun _ _ hij => (hij rfl).elim))

-- `pairwise_fin_succ_iff_of_isSymm` idx 2: necessary (n = 1, R i j := i = 0 ∧ j = 1 (not symmetric))
theorem c6_113 : ¬ drop0% pairwise_fin_succ_iff_of_isSymm 2 :=
  fun h => absurd (@h 1 (fun i j => i = 0 ∧ j = 1)) (by unfold Pairwise; decide)

-- `Set.pairwise_of_forall` idx 3: necessary (s = univ in Bool, r = ⊥)
theorem c6_114 : ¬ drop0% Set.pairwise_of_forall 3 :=
  fun h => W1c6.nspB (@h Bool Set.univ (fun _ _ => False))

-- `Set.Pairwise.imp_on` idx 4: necessary (r = p = ⊥, s = univ in Bool)
theorem c6_115 : ¬ drop0% Set.Pairwise.imp_on 4 :=
  fun h => W1c6.nspB (@h Bool (fun _ _ => False) (fun _ _ => False) Set.univ (fun _ _ _ _ _ e => e.elim))

-- `Set.Pairwise.imp_on` idx 5: necessary (r = ⊤, p = ⊥, s = univ in Bool)
theorem c6_116 : ¬ drop0% Set.Pairwise.imp_on 5 :=
  fun h => W1c6.nspB (@h Bool (fun _ _ => True) (fun _ _ => False) Set.univ (fun _ _ _ _ _ => trivial))

-- `Set.Pairwise.imp` idx 4: necessary (r = p = ⊥, s = univ in Bool)
theorem c6_117 : ¬ drop0% Set.Pairwise.imp 4 :=
  fun h => W1c6.nspB (@h Bool (fun _ _ => False) (fun _ _ => False) Set.univ (fun _ _ e => e))

-- `Set.Pairwise.imp` idx 5: necessary (r = ⊤, p = ⊥, s = univ in Bool)
theorem c6_118 : ¬ drop0% Set.Pairwise.imp 5 :=
  fun h => W1c6.nspB (@h Bool (fun _ _ => True) (fun _ _ => False) Set.univ (fun _ _ _ _ _ => trivial))

-- `Set.Pairwise.eq` idx 8: necessary (r = ⊤, s = univ, a = true, b = false)
theorem c6_119 : ¬ drop0% Set.Pairwise.eq 8 :=
  fun h => absurd (@h Bool (fun _ _ => True) Set.univ true false (fun _ _ _ _ _ => trivial) (Set.mem_univ _) (Set.mem_univ _)) (by decide)

-- `Set.Pairwise.of_forall₂` idx 3: necessary (r = ⊥, s = univ in Bool)
theorem c6_120 : ¬ drop0% Set.Pairwise.of_forall₂ 3 :=
  fun h => W1c6.nspB (@h Bool (fun _ _ => False) Set.univ)

-- `Set.Pairwise.on_injective` idx 5: necessary (r = ⊥, f = id, s = univ)
theorem c6_121 : ¬ drop0% Set.Pairwise.on_injective 5 :=
  fun h => (@h Bool Bool (fun _ _ => False) id Set.univ Function.injective_id (fun _ => Set.mem_univ _)) (show true ≠ false by decide)

-- `Set.Pairwise.on_injective` idx 6: necessary (r = ≠, f = const true, s = univ)
theorem c6_122 : ¬ drop0% Set.Pairwise.on_injective 6 :=
  fun h => (@h Bool Bool (· ≠ ·) (fun _ => true) Set.univ (fun _ _ _ _ e => e) (fun _ => Set.mem_univ _)) (show true ≠ false by decide) rfl

-- `Set.Pairwise.on_injective` idx 7: necessary (r = ⊥, f = id, s = ∅)
theorem c6_123 : ¬ drop0% Set.Pairwise.on_injective 7 :=
  fun h => (@h Bool Bool (fun _ _ => False) id ∅ (fun x hx => absurd hx (Set.notMem_empty x)) Function.injective_id) (show true ≠ false by decide)

-- `Pairwise.set_pairwise` idx 2: necessary (r = ⊥, s = univ in Bool)
theorem c6_124 : ¬ drop0% Pairwise.set_pairwise 2 :=
  fun h => W1c6.nspB (@h Bool (fun _ _ => False) Set.univ)
