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

namespace W1c7

theorem notAcc {β : Type*} {R : β → β → Prop} (f : ℕ → β) (hf : ∀ n, R (f (n+1)) (f n)) : ¬ Acc R (f 0) := by
  intro h
  have : ∀ y, Acc R y → ∀ n, y = f n → False := fun y hy => by
    induction hy with
    | intro z _ ih => intro n hz; subst hz; exact ih _ (hf n) (n+1) rfl
  exact this _ h 0 rfl
theorem notAccSelf {β : Type*} {R : β → β → Prop} {x : β} (hx : R x x) : ¬ Acc R x :=
  notAcc (fun _ => x) (fun _ => hx)
/-- strict order false < true on Bool: transitive, not symmetric, not reflexive -/
abbrev lt2 (a b : Bool) : Prop := a = false ∧ b = true
/-- reflexive, not symmetric, not transitive on Fin 3 (0-1, 1-2 steps) -/
abbrev rr3 (a b : Fin 3) : Prop := a = b ∨ a.val + 1 = b.val
/-- transitive (no chains) relation on Fin 4 with steps 0-1 and 2-3 -/
abbrev r4 (a b : Fin 4) : Prop := (a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3)
/-- Fin 4 → Fin 3, 0,1,2,3 to 0,1,1,2 -/
def f43 (i : Fin 4) : Fin 3 := ⟨(i.val + 1) / 2, by omega⟩
/-- equivalence on Fin 4 with classes 01, 23 -/
abbrev e4 (a b : Fin 4) : Prop := a.val / 2 = b.val / 2

end W1c7
open W1c7

namespace W1c7
/-- successor steps on Fin 3 (0-1, 1-2): not transitive, not reflexive -/
abbrev st3 (a b : Fin 3) : Prop := a.val + 1 = b.val
theorem tg02 : Relation.TransGen st3 0 2 := .tail (b := 1) (.single (by decide)) (by decide)
theorem rtg02 : Relation.ReflTransGen st3 0 2 := .tail (b := 1) (.single (by decide)) (by decide)
theorem tg_head {α : Type*} {r : α → α → Prop} {a c : α} (h : Relation.TransGen r a c) : ∃ b, r a b :=
  (Relation.TransGen.head'_iff.1 h).imp fun _ h => h.1
theorem eqvF {α : Type*} {a b : α} (h : Relation.EqvGen (fun _ _ : α => False) a b) : a = b := by
  induction h with
  | rel _ _ h => exact h.elim
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ i1 i2 => exact i1.trans i2
theorem rtgF {α : Type*} {a b : α} (h : Relation.ReflTransGen (fun _ _ : α => False) a b) : b = a :=
  (Relation.reflTransGen_iff_eq (fun _ h => h)).1 h
/-- fan on Fin 3: 0 → 1, 0 → 2 -/
abbrev fan3 (a b : Fin 3) : Prop := a = 0 ∧ b ≠ 0
/-- two V's without chains on Fin 5: 0,1 → 3 and 1,2 → 4 (transitive) -/
abbrev vv5 (a b : Fin 5) : Prop := (b = 3 ∧ (a = 0 ∨ a = 1)) ∨ (b = 4 ∧ (a = 1 ∨ a = 2))
/-- vv5 plus 3,4 → 5 → 5 on Fin 6: joinable successors, Join not transitive -/
abbrev vv6 (a b : Fin 6) : Prop :=
  (b = 3 ∧ (a = 0 ∨ a = 1)) ∨ (b = 4 ∧ (a = 1 ∨ a = 2)) ∨ (b = 5 ∧ (a = 3 ∨ a = 4 ∨ a = 5))
end W1c7

namespace W1c7
/-- a type into which `Type` injects is not `Small.{0}` -/
theorem nsInj {X : Type 1} (f : Type → X) (hf : Function.Injective f) : ¬ Small.{0} X := fun _ =>
  not_small_type.{0, 0} (small_of_injective hf)
/-- a type that surjects onto `Type` is not `Small.{0}` -/
theorem nsSurj {X : Type 1} (f : X → Type) (hf : Function.Surjective f) : ¬ Small.{0} X := fun _ =>
  not_small_type.{0, 0} (small_of_surjective hf)
theorem ntType : Nontrivial Type := ⟨⟨Empty, Unit, fun h => (cast h.symm ()).elim⟩⟩
end W1c7
-- `Subrelation.antisymm` idx 3: necessary
theorem w1c7_0 : ¬ drop0% Subrelation.antisymm 3 := fun h => by
  have := h (α := Unit) (r := fun _ _ => True) (r' := fun _ _ => False) (fun _ _ h => trivial)
  exact cast (congrFun (congrFun this ()) ()) trivial

-- `Subrelation.antisymm` idx 4: necessary
theorem w1c7_1 : ¬ drop0% Subrelation.antisymm 4 := fun h => by
  have := h (α := Unit) (r := fun _ _ => False) (r' := fun _ _ => True) (fun _ _ h => h.elim)
  exact cast (congrFun (congrFun this ()) ()).symm trivial

-- `Std.Symm.flip_eq` idx 2: necessary
theorem w1c7_2 : ¬ drop0% Std.Symm.flip_eq 2 := fun h => by
  have := congrFun (congrFun (h (r := lt2)) true) false
  exact absurd (cast this ⟨rfl, rfl⟩).1 (by decide)

-- `Symmetric.flip_eq` idx 2: necessary
theorem w1c7_3 : ¬ drop0% Symmetric.flip_eq 2 := fun h => by
  have := congrFun (congrFun (h (r := lt2)) true) false
  exact absurd (cast this ⟨rfl, rfl⟩).1 (by decide)

-- `Std.Symm.swap_eq` idx 2: necessary
theorem w1c7_4 : ¬ drop0% Std.Symm.swap_eq 2 := fun h => by
  have := congrFun (congrFun (h (r := lt2)) true) false
  exact absurd (cast this ⟨rfl, rfl⟩).1 (by decide)

-- `Symmetric.swap_eq` idx 2: necessary
theorem w1c7_5 : ¬ drop0% Symmetric.swap_eq 2 := fun h => by
  have := congrFun (congrFun (h (r := lt2)) true) false
  exact absurd (cast this ⟨rfl, rfl⟩).1 (by decide)

-- `Acc.of_fibration` idx 5: necessary
theorem w1c7_6 : ¬ drop0% Acc.of_fibration 5 := fun h => by
  have := h (α := Unit) (β := Unit) (rα := fun _ _ => False) (rβ := fun _ _ => True) (f := id) (a := ())
    (Acc.intro () fun _ h => h.elim)
  exact notAccSelf trivial this

-- `Acc.of_fibration` idx 7: necessary
theorem w1c7_7 : ¬ drop0% Acc.of_fibration 7 := fun h => by
  have := h (α := Unit) (β := Unit) (rα := fun _ _ => True) (rβ := fun _ _ => True) (f := id)
    (fun _ _ _ => ⟨(), trivial, rfl⟩) (a := ())
  exact notAccSelf trivial this

-- `Acc.of_downward_closed` idx 4: necessary
theorem w1c7_8 : ¬ drop0% Acc.of_downward_closed 4 := fun h => by
  have := h (α := Unit) (β := Bool) (rβ := fun b _ => b = true) (f := fun _ => false) ()
    (Acc.intro () fun _ hy => absurd hy Bool.false_ne_true)
  exact notAccSelf (R := fun b _ => b = true) (x := true) rfl (this.inv rfl)

-- `Acc.of_downward_closed` idx 6: necessary
theorem w1c7_9 : ¬ drop0% Acc.of_downward_closed 6 := fun h => by
  have := h (α := Unit) (β := Unit) (rβ := fun _ _ => True) (f := id) (fun {_ b} _ => ⟨b, rfl⟩) ()
  exact notAccSelf trivial this

-- `Relation.map_apply_apply` idx 6: necessary
theorem w1c7_10 : ¬ drop0% Relation.map_apply_apply 6 := fun h => by
  have := h (α := Bool) (β := Unit) (γ := Unit) (δ := Unit) (f := fun _ => ()) (g := id)
    Function.injective_id (fun a _ => a = true) false ()
  exact Bool.false_ne_true (this.1 ⟨true, (), rfl, rfl, rfl⟩)

-- `Relation.map_apply_apply` idx 7: necessary
theorem w1c7_11 : ¬ drop0% Relation.map_apply_apply 7 := fun h => by
  have := h (α := Unit) (β := Bool) (γ := Unit) (δ := Unit) (f := id) (g := fun _ => ())
    Function.injective_id (fun _ b => b = true) () false
  exact Bool.false_ne_true (this.1 ⟨(), true, rfl, rfl, rfl⟩)

-- `Std.Symm.map` idx 3: necessary
theorem w1c7_12 : ¬ drop0% Std.Symm.map 3 := fun h => by
  have := h (r := lt2) (f := id)
  rw [Relation.map_id_id] at this
  exact absurd (this.symm false true ⟨rfl, rfl⟩).1 (by decide)

-- `Relation.map_symmetric` idx 3: necessary
theorem w1c7_13 : ¬ drop0% Relation.map_symmetric 3 := fun h => by
  have := h (r := lt2) (f := id)
  rw [Relation.map_id_id] at this
  exact absurd (this.symm false true ⟨rfl, rfl⟩).1 (by decide)

-- `IsTrans.map` idx 3: necessary
theorem w1c7_14 : ¬ drop0% IsTrans.map 3 := fun h => by
  have := h (r := rr3) (f := id) (fun x y e => Or.inl e)
  rw [Relation.map_id_id] at this
  exact absurd (this.trans 0 1 2 (by decide) (by decide)) (by decide)

-- `IsTrans.map` idx 5: necessary
theorem w1c7_15 : ¬ drop0% IsTrans.map 5 := fun h => by
  have : IsTrans (Fin 4) r4 := ⟨by decide⟩
  have := h (r := r4) (f := f43)
  have h01 : Relation.Map r4 f43 f43 0 1 := ⟨0, 1, by decide, rfl, rfl⟩
  have h12 : Relation.Map r4 f43 f43 1 2 := ⟨2, 3, by decide, rfl, rfl⟩
  obtain ⟨a, b, hab, ha, hb⟩ := this.trans _ _ _ h01 h12
  revert a b; decide

-- `Relation.map_equivalence` idx 3: necessary
theorem w1c7_16 : ¬ drop0% Relation.map_equivalence 3 := fun h => by
  have := h (r := rr3) id Function.surjective_id (fun x y e => Or.inl e)
  rw [Relation.map_id_id] at this
  exact absurd (this.symm (show rr3 0 1 by decide)) (by decide)

-- `Relation.map_equivalence` idx 6: necessary
theorem w1c7_17 : ¬ drop0% Relation.map_equivalence 6 := fun h => by
  have := h (r := e4) ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩ f43
    (fun b => by revert b; decide)
  have h01 : Relation.Map e4 f43 f43 0 1 := ⟨0, 1, by decide, rfl, rfl⟩
  have h12 : Relation.Map e4 f43 f43 1 2 := ⟨2, 3, by decide, rfl, rfl⟩
  obtain ⟨a, b, hab, ha, hb⟩ := this.trans h01 h12
  revert a b; decide

-- `Relation.map_mono` idx 8: necessary
theorem w1c7_18 : ¬ drop0% Relation.map_mono 8 := fun h => by
  have := h (α := Unit) (β := Unit) (γ := Unit) (δ := Unit) (r := fun _ _ => True) (s := fun _ _ => False)
    (f := id) (g := id) () () ⟨(), (), trivial, rfl, rfl⟩
  obtain ⟨_, _, h, _⟩ := this
  exact h

-- `Relation.bicompl_le_of_le_map` idx 8: necessary
theorem w1c7_19 : ¬ drop0% Relation.bicompl_le_of_le_map 8 := fun h => by
  have := h (α := Bool) (β := Unit) (γ := Unit) (δ := Unit) (r := fun a _ => a = true)
    (s := fun _ _ => True) (f := fun _ => ()) (g := id) Function.injective_id
    (fun _ _ _ => ⟨true, (), rfl, rfl, rfl⟩) false () trivial
  exact Bool.false_ne_true this

-- `Relation.bicompl_le_of_le_map` idx 9: necessary
theorem w1c7_20 : ¬ drop0% Relation.bicompl_le_of_le_map 9 := fun h => by
  have := h (α := Unit) (β := Bool) (γ := Unit) (δ := Unit) (r := fun _ b => b = true)
    (s := fun _ _ => True) (f := id) (g := fun _ => ()) Function.injective_id
    (fun _ _ _ => ⟨(), true, rfl, rfl, rfl⟩) () false trivial
  exact Bool.false_ne_true this

-- `Relation.bicompl_le_of_le_map` idx 10: necessary
theorem w1c7_21 : ¬ drop0% Relation.bicompl_le_of_le_map 10 := fun h =>
  h (α := Unit) (β := Unit) (γ := Unit) (δ := Unit) (r := fun _ _ => False)
    (s := fun _ _ => True) (f := id) (g := id) Function.injective_id Function.injective_id () () trivial

-- `Relation.onFun_le_of_le_map` idx 5: necessary
theorem w1c7_22 : ¬ drop0% Relation.onFun_le_of_le_map 5 := fun h => by
  have := h (α := Bool) (β := Unit) (r := fun a b => a = b) (s := fun _ _ => True) (f := fun _ => ())
    (fun _ _ _ => ⟨true, true, rfl, rfl, rfl⟩) false true trivial
  exact Bool.false_ne_true this

-- `Relation.onFun_le_of_le_map` idx 6: necessary
theorem w1c7_23 : ¬ drop0% Relation.onFun_le_of_le_map 6 := fun h =>
  h (α := Unit) (β := Unit) (r := fun _ _ => False) (s := fun _ _ => True) (f := id)
    Function.injective_id () () trivial

-- `Relation.le_map_of_bicompl_le` idx 8: necessary
theorem w1c7_24 : ¬ drop0% Relation.le_map_of_bicompl_le 8 := fun h => by
  obtain ⟨a, _⟩ := h (α := Empty) (β := Unit) (γ := Unit) (δ := Unit) (r := fun _ _ => True)
    (s := fun _ _ => True) (f := Empty.elim) (g := id) Function.surjective_id (fun a => a.elim) () () trivial
  exact a.elim

-- `Relation.le_map_of_bicompl_le` idx 9: necessary
theorem w1c7_25 : ¬ drop0% Relation.le_map_of_bicompl_le 9 := fun h => by
  obtain ⟨_, b, _⟩ := h (α := Unit) (β := Empty) (γ := Unit) (δ := Unit) (r := fun _ _ => True)
    (s := fun _ _ => True) (f := id) (g := Empty.elim) Function.surjective_id (fun _ b => b.elim) () () trivial
  exact b.elim

-- `Relation.le_map_of_bicompl_le` idx 10: necessary
theorem w1c7_26 : ¬ drop0% Relation.le_map_of_bicompl_le 10 := fun h => by
  obtain ⟨_, _, h, _⟩ := h (α := Unit) (β := Unit) (γ := Unit) (δ := Unit) (r := fun _ _ => False)
    (s := fun _ _ => True) (f := id) (g := id) Function.surjective_id Function.surjective_id () () trivial
  exact h

-- `Relation.le_map_of_onFun_le` idx 5: necessary
theorem w1c7_27 : ¬ drop0% Relation.le_map_of_onFun_le 5 := fun h => by
  obtain ⟨a, _⟩ := h (α := Empty) (β := Unit) (r := fun _ _ => True) (s := fun _ _ => True)
    (f := Empty.elim) (fun a => a.elim) () () trivial
  exact a.elim

-- `Relation.le_map_of_onFun_le` idx 6: necessary
theorem w1c7_28 : ¬ drop0% Relation.le_map_of_onFun_le 6 := fun h => by
  obtain ⟨_, _, h, _⟩ := h (α := Unit) (β := Unit) (r := fun _ _ => False) (s := fun _ _ => True)
    (f := id) Function.surjective_id () () trivial
  exact h

-- `Relation.le_map_iff_bicompl_le` idx 8: necessary
theorem w1c7_29 : ¬ drop0% Relation.le_map_iff_bicompl_le 8 := fun h => by
  obtain ⟨a, _⟩ := (h (α := Empty) (β := Unit) (γ := Unit) (δ := Unit) (r := fun _ _ => True)
    (s := fun _ _ => True) (f := Empty.elim) (g := id) Function.bijective_id).2 (fun a => a.elim) () () trivial
  exact a.elim

-- `Relation.le_map_iff_bicompl_le` idx 9: necessary
theorem w1c7_30 : ¬ drop0% Relation.le_map_iff_bicompl_le 9 := fun h => by
  obtain ⟨_, b, _⟩ := (h (α := Unit) (β := Empty) (γ := Unit) (δ := Unit) (r := fun _ _ => True)
    (s := fun _ _ => True) (f := id) (g := Empty.elim) Function.bijective_id).2 (fun _ b => b.elim) () () trivial
  exact b.elim

-- `Relation.le_map_iff_onFun_le` idx 5: necessary
theorem w1c7_31 : ¬ drop0% Relation.le_map_iff_onFun_le 5 := fun h => by
  obtain ⟨a, _⟩ := (h (α := Empty) (β := Unit) (r := fun _ _ => True) (s := fun _ _ => True)
    (f := Empty.elim)).2 (fun a => a.elim) () () trivial
  exact a.elim

-- `Relation.bicompl_map_eq_of_injective` idx 7: necessary
theorem w1c7_32 : ¬ drop0% Relation.bicompl_map_eq_of_injective 7 := fun h => by
  have e := congrFun (congrFun (h (α := Bool) (β := Unit) (γ := Unit) (δ := Unit) (fun a _ => a = true)
    (f := fun _ => ()) (g := id) Function.injective_id) false) ()
  exact Bool.false_ne_true (cast e ⟨true, (), rfl, rfl, rfl⟩)

-- `Relation.bicompl_map_eq_of_injective` idx 8: necessary
theorem w1c7_33 : ¬ drop0% Relation.bicompl_map_eq_of_injective 8 := fun h => by
  have e := congrFun (congrFun (h (α := Unit) (β := Bool) (γ := Unit) (δ := Unit) (fun _ b => b = true)
    (f := id) (g := fun _ => ()) Function.injective_id) ()) false
  exact Bool.false_ne_true (cast e ⟨(), true, rfl, rfl, rfl⟩)

-- `Relation.onFun_map_eq_of_injective` idx 4: necessary
theorem w1c7_34 : ¬ drop0% Relation.onFun_map_eq_of_injective 4 := fun h => by
  have e := congrFun (congrFun (h (α := Bool) (β := Unit) (fun a b => a = b) (f := fun _ => ())) false) true
  exact Bool.false_ne_true (cast e ⟨true, true, rfl, rfl, rfl⟩)

-- `Relation.map_bicompl_eq_of_surjective` idx 7: necessary
theorem w1c7_35 : ¬ drop0% Relation.map_bicompl_eq_of_surjective 7 := fun h => by
  have e := congrFun (congrFun (h (α := Empty) (β := Unit) (γ := Unit) (δ := Unit) (fun _ _ => True)
    (f := Empty.elim) (g := id) Function.surjective_id) ()) ()
  obtain ⟨a, _⟩ := cast e.symm trivial
  exact a.elim

-- `Relation.map_bicompl_eq_of_surjective` idx 8: necessary
theorem w1c7_36 : ¬ drop0% Relation.map_bicompl_eq_of_surjective 8 := fun h => by
  have e := congrFun (congrFun (h (α := Unit) (β := Empty) (γ := Unit) (δ := Unit) (fun _ _ => True)
    (f := id) (g := Empty.elim) Function.surjective_id) ()) ()
  obtain ⟨_, b, _⟩ := cast e.symm trivial
  exact b.elim

-- `Relation.map_onFun_eq_of_surjective` idx 4: necessary
theorem w1c7_37 : ¬ drop0% Relation.map_onFun_eq_of_surjective 4 := fun h => by
  have e := congrFun (congrFun (h (α := Empty) (β := Unit) (fun _ _ => True) (f := Empty.elim)) ()) ()
  obtain ⟨a, _⟩ := cast e.symm trivial
  exact a.elim

-- `Acc.of_map` idx 5: necessary
theorem w1c7_38 : ¬ drop0% Acc.of_map 5 := fun h =>
  notAccSelf (R := fun _ _ : Unit => True) trivial (h (β := Unit) (f := id) (a := ()))

-- `Function.Injective.acc_map_iff` idx 5: necessary
theorem w1c7_39 : ¬ drop0% Function.Injective.acc_map_iff 5 := fun h => by
  have := (h (α := Bool) (β := Unit) (r := fun a b => a = true ∧ b = true) (f := fun _ => ()) (a := false)).2
    (Acc.intro false fun _ hy => absurd hy.2 Bool.false_ne_true)
  exact notAccSelf ⟨true, true, ⟨rfl, rfl⟩, rfl, rfl⟩ this

-- `Relation.ReflGen.mono` idx 3: necessary
theorem w1c7_40 : ¬ drop0% Relation.ReflGen.mono 3 := fun h => by
  have := h (r := fun _ _ : Bool => True) (p := fun _ _ => False) false true (.single trivial)
  cases this with
  | single h => exact h

-- `Relation.ReflGen.stdSymm` idx 2: necessary
theorem w1c7_41 : ¬ drop0% Relation.ReflGen.stdSymm 2 := fun h => by
  have := (h (r := lt2)).symm false true (.single ⟨rfl, rfl⟩)
  cases this with
  | single h => exact absurd h.1 (by decide)

-- `Relation.ReflGen.symmetric` idx 2: necessary
theorem w1c7_42 : ¬ drop0% Relation.ReflGen.symmetric 2 := fun h => by
  have := (h (r := lt2)).symm false true (.single ⟨rfl, rfl⟩)
  cases this with
  | single h => exact absurd h.1 (by decide)

-- `Relation.ReflGen.instIsPreorderOfIsTrans` idx 2: necessary
theorem w1c7_43 : ¬ drop0% Relation.ReflGen.instIsPreorderOfIsTrans 2 := fun h => by
  have := (h (r := st3)).trans 0 1 2 (.single (by decide)) (.single (by decide))
  rw [Relation.reflGen_iff] at this
  revert this; decide

-- `Relation.ReflTransGen.stdSymm` idx 2: necessary
theorem w1c7_44 : ¬ drop0% Relation.ReflTransGen.stdSymm 2 := fun h => by
  have := (h (r := lt2)).symm false true (.single ⟨rfl, rfl⟩)
  rw [Relation.reflTransGen_iff_eq (by decide)] at this
  exact absurd this (by decide)

-- `Relation.ReflTransGen.symmetric` idx 2: necessary
theorem w1c7_45 : ¬ drop0% Relation.ReflTransGen.symmetric 2 := fun h => by
  have := (h (r := lt2)).symm false true (.single ⟨rfl, rfl⟩)
  rw [Relation.reflTransGen_iff_eq (by decide)] at this
  exact absurd this (by decide)

-- `Relation.ReflTransGen.head_induction_on` idx 5: necessary
theorem w1c7_46 : ¬ indep0% Relation.ReflTransGen.head_induction_on 5 := fun h => by
  have := h (α := Bool) (r := fun _ _ => False) (b := true) (motive := fun _ _ => True) (a := false)
    trivial (fun _ _ _ => trivial)
  exact absurd (rtgF this) (by decide)

-- `Relation.ReflTransGen.head_induction_on` idx 6: necessary
theorem w1c7_47 : ¬ drop0% Relation.ReflTransGen.head_induction_on 6 := fun h =>
  h (α := Unit) (r := fun _ _ => False) (b := ()) (motive := fun _ _ => False) (a := ())
    .refl (fun _ _ h => h)

-- `Relation.ReflTransGen.head_induction_on` idx 7: necessary
theorem w1c7_48 : ¬ drop0% Relation.ReflTransGen.head_induction_on 7 := fun h => by
  have := h (α := Bool) (r := lt2) (b := true) (motive := fun a _ => a = true) (a := false)
    (.single ⟨rfl, rfl⟩) rfl
  exact absurd this (by decide)

-- `Relation.ReflTransGen.trans_induction_on` idx 5: necessary
theorem w1c7_49 : ¬ indep0% Relation.ReflTransGen.trans_induction_on 5 := fun h => by
  have := h (α := Bool) (r := fun _ _ => False) (motive := fun _ => True) (a := false) (b := true)
    (fun _ => trivial) (fun _ => trivial) (fun _ _ _ _ => trivial)
  exact absurd (rtgF this) (by decide)

-- `Relation.ReflTransGen.trans_induction_on` idx 6: necessary
theorem w1c7_50 : ¬ drop0% Relation.ReflTransGen.trans_induction_on 6 := fun h =>
  h (α := Unit) (r := fun _ _ => False) (motive := fun _ => False) (a := ()) (b := ())
    .refl (fun h => h.elim) (fun _ _ h _ => h)

-- `Relation.ReflTransGen.trans_induction_on` idx 7: necessary
theorem w1c7_51 : ¬ drop0% Relation.ReflTransGen.trans_induction_on 7 := fun h => by
  have := h (α := Bool) (r := lt2) (motive := fun {a b} _ => a = b) (a := false) (b := true)
    (.single ⟨rfl, rfl⟩) (fun _ => rfl) (fun _ _ h1 h2 => h1.trans h2)
  exact absurd this (by decide)

-- `Relation.ReflTransGen.trans_induction_on` idx 8: necessary
theorem w1c7_52 : ¬ drop0% Relation.ReflTransGen.trans_induction_on 8 := fun h => by
  have := h (α := Fin 3) (r := st3) (motive := fun {a b} _ => a = b ∨ st3 a b) (a := 0) (b := 2)
    rtg02 (fun _ => Or.inl rfl) (fun h => Or.inr h)
  revert this; decide

-- `Relation.ReflTransGen.total_of_right_unique` idx 5: necessary
theorem w1c7_53 : ¬ drop0% Relation.ReflTransGen.total_of_right_unique 5 := fun h => by
  have := h (α := Fin 3) (r := fan3) (a := 0) (b := 1) (c := 2) (.single (by decide)) (.single (by decide))
  rw [Relation.reflTransGen_iff_eq (by decide), Relation.reflTransGen_iff_eq (by decide)] at this
  revert this; decide

-- `Relation.ReflTransGen.total_of_right_unique` idx 6: necessary
theorem w1c7_54 : ¬ drop0% Relation.ReflTransGen.total_of_right_unique 6 := fun h => by
  have := h (α := Bool) (r := fun _ _ => False) (a := false) (b := true) (c := false)
    (fun _ _ _ h => h.elim) .refl
  rcases this with h | h <;> exact absurd (rtgF h) (by decide)

-- `Relation.ReflTransGen.total_of_right_unique` idx 7: necessary
theorem w1c7_55 : ¬ drop0% Relation.ReflTransGen.total_of_right_unique 7 := fun h => by
  have := h (α := Bool) (r := fun _ _ => False) (a := false) (b := false) (c := true)
    (fun _ _ _ h => h.elim) .refl
  rcases this with h | h <;> exact absurd (rtgF h) (by decide)

-- `Relation.TransGen.tail'` idx 5: necessary
theorem w1c7_56 : ¬ drop0% Relation.TransGen.tail' 5 := fun h => by
  obtain ⟨_, h⟩ := tg_head (h (r := lt2) (a := true) (b := false) (c := true) ⟨rfl, rfl⟩)
  exact absurd h.1 (by decide)

-- `Relation.TransGen.head` idx 5: necessary
theorem w1c7_57 : ¬ drop0% Relation.TransGen.head 5 := fun h => by
  obtain ⟨_, h⟩ := tg_head (h (r := lt2) (a := true) (b := false) (c := true) (.single ⟨rfl, rfl⟩))
  exact absurd h.1 (by decide)

-- `Relation.TransGen.head_induction_on` idx 5: necessary
theorem w1c7_58 : ¬ indep0% Relation.TransGen.head_induction_on 5 := fun h => by
  obtain ⟨_, h⟩ := tg_head (h (α := Unit) (r := fun _ _ => False) (b := ()) (motive := fun _ _ => True) (a := ())
    (fun _ => trivial) (fun _ _ _ => trivial))
  exact h

-- `Relation.TransGen.head_induction_on` idx 6: necessary
theorem w1c7_59 : ¬ drop0% Relation.TransGen.head_induction_on 6 := fun h =>
  h (α := Unit) (r := fun _ _ => True) (b := ()) (motive := fun _ _ => False) (a := ())
    (.single trivial) (fun _ _ h => h)

-- `Relation.TransGen.head_induction_on` idx 7: necessary
theorem w1c7_60 : ¬ drop0% Relation.TransGen.head_induction_on 7 := fun h => by
  have := h (α := Fin 3) (r := st3) (b := 2) (motive := fun a _ => st3 a 2) (a := 0) tg02 (fun h => h)
  revert this; decide

-- `Relation.TransGen.trans_induction_on` idx 5: necessary
theorem w1c7_61 : ¬ indep0% Relation.TransGen.trans_induction_on 5 := fun h => by
  obtain ⟨_, h⟩ := tg_head (h (α := Unit) (r := fun _ _ => False) (motive := fun _ => True) (a := ()) (b := ())
    (fun _ => trivial) (fun _ _ _ _ => trivial))
  exact h

-- `Relation.TransGen.trans_induction_on` idx 6: necessary
theorem w1c7_62 : ¬ drop0% Relation.TransGen.trans_induction_on 6 := fun h =>
  h (α := Unit) (r := fun _ _ => True) (motive := fun _ => False) (a := ()) (b := ())
    (.single trivial) (fun _ _ h _ => h)

-- `Relation.TransGen.trans_induction_on` idx 7: necessary
theorem w1c7_63 : ¬ drop0% Relation.TransGen.trans_induction_on 7 := fun h => by
  have := h (α := Fin 3) (r := st3) (motive := fun {a b} _ => st3 a b) (a := 0) (b := 2) tg02 (fun h => h)
  revert this; decide

-- `Relation.TransGen.trans_right` idx 5: necessary
theorem w1c7_64 : ¬ drop0% Relation.TransGen.trans_right 5 := fun h => by
  obtain ⟨_, h⟩ := tg_head (h (r := lt2) (a := true) (b := false) (c := true) (.single ⟨rfl, rfl⟩))
  exact absurd h.1 (by decide)

-- `Relation.TransGen.stdSymm` idx 2: necessary
theorem w1c7_65 : ¬ drop0% Relation.TransGen.stdSymm 2 := fun h => by
  obtain ⟨_, h⟩ := tg_head ((h (r := lt2)).symm false true (.single ⟨rfl, rfl⟩))
  exact absurd h.1 (by decide)

-- `Relation.TransGen.symmetric` idx 2: necessary
theorem w1c7_66 : ¬ drop0% Relation.TransGen.symmetric 2 := fun h => by
  obtain ⟨_, h⟩ := tg_head ((h (r := lt2)).symm false true (.single ⟨rfl, rfl⟩))
  exact absurd h.1 (by decide)

-- `Relation.TransGen.instIsPreorderOfRefl` idx 2: necessary
theorem w1c7_67 : ¬ drop0% Relation.TransGen.instIsPreorderOfRefl 2 := fun h => by
  obtain ⟨_, h⟩ := tg_head ((h (α := Unit) (r := fun _ _ => False)).refl ())
  exact h

-- `Relation.reflGen_eq_self` idx 2: necessary
theorem w1c7_68 : ¬ drop0% Relation.reflGen_eq_self 2 := fun h =>
  cast (congrFun (congrFun (h (α := Unit) (r := fun _ _ => False)) ()) ()) .refl

-- `Relation.reflGen_minimal` idx 3: necessary
theorem w1c7_69 : ¬ drop0% Relation.reflGen_minimal 3 := fun h =>
  h (α := Unit) (r := fun _ _ => False) (r' := fun _ _ => False) (fun _ _ h => h) () () .refl

-- `Relation.reflGen_minimal` idx 4: necessary
theorem w1c7_70 : ¬ drop0% Relation.reflGen_minimal 4 := fun h => by
  have := h (α := Bool) (r := fun _ _ => True) (r' := Eq) false true (.single trivial)
  exact absurd this (by decide)

-- `Relation.transGen_eq_self` idx 2: necessary
theorem w1c7_71 : ¬ drop0% Relation.transGen_eq_self 2 := fun h => by
  have := cast (congrFun (congrFun (h (r := st3)) 0) 2) tg02
  revert this; decide

-- `Relation.TransGen.lift` idx 5: necessary
theorem w1c7_72 : ¬ drop0% Relation.TransGen.lift 5 := fun h => by
  obtain ⟨_, h⟩ := tg_head (h (α := Unit) (β := Unit) (r := fun _ _ => True) (p := fun _ _ => False) id
    () () (.single trivial))
  exact h

-- `Relation.TransGen.lift'` idx 5: necessary
theorem w1c7_73 : ¬ drop0% Relation.TransGen.lift' 5 := fun h => by
  obtain ⟨_, h⟩ := tg_head (h (α := Unit) (β := Unit) (r := fun _ _ => True) (p := fun _ _ => False) id
    () () (.single trivial))
  exact h

-- `Relation.TransGen.closed` idx 3: necessary
theorem w1c7_74 : ¬ drop0% Relation.TransGen.closed 3 := fun h => by
  obtain ⟨_, h⟩ := tg_head (h (α := Unit) (r := fun _ _ => True) (p := fun _ _ => False)
    () () (.single trivial))
  exact h

-- `Relation.TransGen.mono` idx 3: necessary
theorem w1c7_75 : ¬ drop0% Relation.TransGen.mono 3 := fun h => by
  obtain ⟨_, h⟩ := tg_head (h (α := Unit) (r := fun _ _ => True) (p := fun _ _ => False)
    () () (.single trivial))
  exact h

-- `Relation.transGen_minimal` idx 3: necessary
theorem w1c7_76 : ¬ drop0% Relation.transGen_minimal 3 := fun h => by
  have := h (r := st3) (r' := st3) (fun _ _ h => h) 0 2 tg02
  revert this; decide

-- `Relation.transGen_minimal` idx 4: necessary
theorem w1c7_77 : ¬ drop0% Relation.transGen_minimal 4 := fun h => by
  have : IsTrans Unit (fun _ _ => False) := ⟨fun _ _ _ h _ => h⟩
  exact h (r := fun _ _ => True) (r' := fun _ _ => False) () () (.single trivial)

-- `Relation.reflTransGen_iff_eq` idx 4: necessary
theorem w1c7_78 : ¬ drop0% Relation.reflTransGen_iff_eq 4 := fun h => by
  have := (h (r := fun _ _ : Bool => True) (a := false) (b := true)).1 (.single trivial)
  exact absurd this (by decide)

-- `Relation.ReflTransGen.lift` idx 5: necessary
theorem w1c7_79 : ¬ drop0% Relation.ReflTransGen.lift 5 := fun h => by
  have := h (α := Bool) (β := Bool) (r := fun _ _ => True) (p := fun _ _ => False) id
    false true (.single trivial)
  exact absurd (rtgF this) (by decide)

-- `Relation.ReflTransGen.mono` idx 3: necessary
theorem w1c7_80 : ¬ drop0% Relation.ReflTransGen.mono 3 := fun h => by
  have := h (α := Bool) (r := fun _ _ => True) (p := fun _ _ => False) false true (.single trivial)
  exact absurd (rtgF this) (by decide)

-- `Relation.reflTransGen_eq_self` idx 2: necessary
theorem w1c7_81 : ¬ drop0% Relation.reflTransGen_eq_self 2 := fun h => by
  have : IsTrans Unit (fun _ _ => False) := ⟨fun _ _ _ h _ => h⟩
  exact cast (congrFun (congrFun (h (r := fun _ _ => False)) ()) ()) .refl

-- `Relation.reflTransGen_eq_self` idx 3: necessary
theorem w1c7_82 : ¬ drop0% Relation.reflTransGen_eq_self 3 := fun h => by
  have : Std.Refl rr3 := ⟨fun _ => Or.inl rfl⟩
  have := cast (congrFun (congrFun (h (r := rr3)) 0) 2) (.tail (.single (by decide)) (show rr3 1 2 by decide))
  revert this; decide

-- `Relation.ReflTransGen.lift'` idx 5: necessary
theorem w1c7_83 : ¬ drop0% Relation.ReflTransGen.lift' 5 := fun h => by
  have := h (α := Bool) (β := Bool) (r := fun _ _ => True) (p := fun _ _ => False) id
    false true (.single trivial)
  exact absurd (rtgF this) (by decide)

-- `Relation.reflTransGen_closed` idx 3: necessary
theorem w1c7_84 : ¬ drop0% Relation.reflTransGen_closed 3 := fun h => by
  have := h (α := Bool) (r := fun _ _ => True) (p := fun _ _ => False) false true (.single trivial)
  exact absurd (rtgF this) (by decide)

-- `Relation.reflTransGen_eq_transGen` idx 2: necessary
theorem w1c7_85 : ¬ drop0% Relation.reflTransGen_eq_transGen 2 := fun h => by
  obtain ⟨_, h⟩ := tg_head (cast (congrFun (congrFun (h (α := Unit) (r := fun _ _ => False)) ()) ()) .refl)
  exact h

-- `Relation.reflTransGen_eq_reflGen` idx 2: necessary
theorem w1c7_86 : ¬ drop0% Relation.reflTransGen_eq_reflGen 2 := fun h => by
  have := cast (congrFun (congrFun (h (r := st3)) 0) 2) rtg02
  rw [Relation.reflGen_iff] at this
  revert this; decide

-- `Relation.EqvGen.mono` idx 3: necessary
theorem w1c7_87 : ¬ drop0% Relation.EqvGen.mono 3 := fun h => by
  have := h (α := Bool) (r := fun _ _ => True) (p := fun _ _ => False) false true (.rel _ _ trivial)
  exact absurd (eqvF this) (by decide)

-- `Relation.EqvGen.eqvGen_le` idx 3: necessary
theorem w1c7_88 : ¬ drop0% Relation.EqvGen.eqvGen_le 3 := fun h =>
  h (α := Unit) (r := fun _ _ => False) (r' := fun _ _ => False) (fun _ _ h => h) () () (.refl _)

-- `Relation.EqvGen.eqvGen_le` idx 4: necessary
theorem w1c7_89 : ¬ drop0% Relation.EqvGen.eqvGen_le 4 := fun h => by
  have := h (α := Bool) (r := fun _ _ => True) (r' := Eq) false true (.rel _ _ trivial)
  exact absurd this (by decide)

-- `Relation.EqvGen.eqvGen_mono` idx 3: necessary
theorem w1c7_90 : ¬ drop0% Relation.EqvGen.eqvGen_mono 3 := fun h => by
  have := h (α := Bool) (r := fun _ _ => True) (r' := fun _ _ => False) false true (.rel _ _ trivial)
  exact absurd (eqvF this) (by decide)

-- `Relation.EqvGen.eqvGen_eq_reflTransGen` idx 2: necessary
theorem w1c7_91 : ¬ drop0% Relation.EqvGen.eqvGen_eq_reflTransGen 2 := fun h => by
  have := cast (congrFun (congrFun (h (r := lt2)) true) false) (.symm _ _ (.rel _ _ ⟨rfl, rfl⟩))
  rw [Relation.reflTransGen_iff_eq (by decide)] at this
  exact absurd this (by decide)

-- `Relation.church_rosser` idx 5: necessary
theorem w1c7_92 : ¬ drop0% Relation.church_rosser 5 := fun h => by
  obtain ⟨d, h1, h2⟩ := h (α := Fin 3) (r := fan3) (a := 0) (b := 1) (c := 2) (.single (by decide))
    (.single (by decide))
  rw [Relation.reflTransGen_iff_eq (by decide)] at h1 h2
  exact absurd (h1.symm.trans h2) (by decide)

-- `Relation.church_rosser` idx 6: necessary
theorem w1c7_93 : ¬ drop0% Relation.church_rosser 6 := fun h => by
  obtain ⟨d, h1, h2⟩ := h (α := Bool) (r := fun _ _ => False) (a := false) (b := true) (c := false)
    (fun _ _ _ h => h.elim) .refl
  exact absurd ((rtgF h1).symm.trans (rtgF h2)) (by decide)

-- `Relation.church_rosser` idx 7: necessary
theorem w1c7_94 : ¬ drop0% Relation.church_rosser 7 := fun h => by
  obtain ⟨d, h1, h2⟩ := h (α := Bool) (r := fun _ _ => False) (a := false) (b := false) (c := true)
    (fun _ _ _ h => h.elim) .refl
  exact absurd ((rtgF h1).symm.trans (rtgF h2)) (by decide)

-- `Relation.le_join_of_refl` idx 2: necessary
theorem w1c7_95 : ¬ drop0% Relation.le_join_of_refl 2 := fun h => by
  obtain ⟨c, _, h2⟩ := h (r := lt2) false true ⟨rfl, rfl⟩
  exact absurd h2.1 (by decide)

-- `Relation.join_of_single` idx 2: necessary
theorem w1c7_96 : ¬ drop0% Relation.join_of_single 2 := fun h => by
  obtain ⟨c, _, h2⟩ := h (r := lt2) false true ⟨rfl, rfl⟩
  exact absurd h2.1 (by decide)

-- `Relation.Join.refl` idx 2: necessary
theorem w1c7_97 : ¬ drop0% Relation.Join.refl 2 := fun h => by
  obtain ⟨c, h1, _⟩ := (h (α := Unit) (r := fun _ _ => False)).refl ()
  exact h1

-- `Relation.reflexive_join` idx 2: necessary
theorem w1c7_98 : ¬ drop0% Relation.reflexive_join 2 := fun h => by
  obtain ⟨c, h1, _⟩ := (h (α := Unit) (r := fun _ _ => False)).refl ()
  exact h1

-- `Relation.isTrans_join` idx 2: necessary
theorem w1c7_99 : ¬ drop0% Relation.isTrans_join 2 := fun h => by
  have k : ∀ a b : Fin 6, vv6 a b → vv6 b 5 := by decide
  have := h (r := vv6) (fun a b c hab hac => ⟨5, k a b hab, k a c hac⟩)
  have h3 := this.trans 0 1 2 ⟨3, by decide⟩ ⟨4, by decide⟩
  unfold Relation.Join at h3
  revert h3; decide

-- `Relation.isTrans_join` idx 3: necessary
theorem w1c7_100 : ¬ drop0% Relation.isTrans_join 3 := fun h => by
  have : IsTrans (Fin 5) vv5 := ⟨by decide⟩
  have := h (r := vv5)
  have h3 := this.trans 0 1 2 ⟨3, by decide⟩ ⟨4, by decide⟩
  unfold Relation.Join at h3
  revert h3; decide

-- `Relation.equivalence_join` idx 2: necessary
theorem w1c7_101 : ¬ drop0% Relation.equivalence_join 2 := fun h => by
  obtain ⟨c, h1, _⟩ := (h (α := Unit) (r := fun _ _ => False) (fun _ _ _ h => h.elim)).refl ()
  exact h1

-- `Relation.equivalence_join` idx 3: necessary
theorem w1c7_102 : ¬ drop0% Relation.equivalence_join 3 := fun h => by
  have : IsPreorder (Fin 5) (fun a b => a = b ∨ vv5 a b) := { refl := by decide, trans := by decide }
  have h3 := (h (r := fun a b => a = b ∨ vv5 a b)).trans (x := 0) (y := 1) (z := 2) ⟨3, by decide⟩ ⟨4, by decide⟩
  unfold Relation.Join at h3
  revert h3; decide

-- `Relation.equivalence_join_reflTransGen` idx 2: necessary
theorem w1c7_103 : ¬ drop0% Relation.equivalence_join_reflTransGen 2 := fun h => by
  have : IsTrans (Fin 5) vv5 := ⟨by decide⟩
  have h3 := (h (r := vv5)).trans (x := 0) (y := 1) (z := 2) ⟨3, .single (by decide), .single (by decide)⟩
    ⟨4, .single (by decide), .single (by decide)⟩
  rw [Relation.reflTransGen_eq_reflGen] at h3
  unfold Relation.Join at h3
  simp only [Relation.reflGen_iff] at h3
  revert h3; decide

-- `Relation.join_le_of_equivalence_of_le` idx 3: necessary
theorem w1c7_104 : ¬ drop0% Relation.join_le_of_equivalence_of_le 3 := fun h => by
  have := h (r := lt2) (r' := lt2) (fun _ _ h => h) false false ⟨true, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  exact absurd this.2 (by decide)

-- `Relation.join_le_of_equivalence_of_le` idx 4: necessary
theorem w1c7_105 : ¬ drop0% Relation.join_le_of_equivalence_of_le 4 := fun h => by
  have := h (α := Bool) (r := Eq) (r' := fun _ _ => True) ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
    false true ⟨true, trivial, trivial⟩
  exact absurd this (by decide)

-- `Relation.join_of_equivalence` idx 3: necessary
theorem w1c7_106 : ¬ drop0% Relation.join_of_equivalence 3 := fun h => by
  have := h (r := lt2) (r' := lt2) (fun _ _ h => h) false false ⟨true, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  exact absurd this.2 (by decide)

-- `Relation.join_of_equivalence` idx 4: necessary
theorem w1c7_107 : ¬ drop0% Relation.join_of_equivalence 4 := fun h => by
  have := h (α := Bool) (r := Eq) (r' := fun _ _ => True) ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
    false true ⟨true, trivial, trivial⟩
  exact absurd this (by decide)

-- `Relation.reflTransGen_le_of_le` idx 3: necessary
theorem w1c7_108 : ¬ drop0% Relation.reflTransGen_le_of_le 3 := fun h => by
  have : IsTrans Unit (fun _ _ => False) := ⟨fun _ _ _ h _ => h⟩
  exact h (r := fun _ _ => False) (r' := fun _ _ => False) (fun _ _ h => h) () () .refl

-- `Relation.reflTransGen_le_of_le` idx 4: necessary
theorem w1c7_109 : ¬ drop0% Relation.reflTransGen_le_of_le 4 := fun h => by
  have : Std.Refl rr3 := ⟨fun _ => Or.inl rfl⟩
  have := h (r := rr3) (r' := rr3) (fun _ _ h => h) 0 2 (.tail (b := 1) (.single (by decide)) (by decide))
  revert this; decide

-- `Relation.reflTransGen_le_of_le` idx 5: necessary
theorem w1c7_110 : ¬ drop0% Relation.reflTransGen_le_of_le 5 := fun h => by
  have := h (α := Bool) (r := Eq) (r' := fun _ _ => True) false true (.single trivial)
  exact absurd this (by decide)

-- `Relation.reflTransGen_of_isTrans_reflexive` idx 3: necessary
theorem w1c7_111 : ¬ drop0% Relation.reflTransGen_of_isTrans_reflexive 3 := fun h => by
  have : IsTrans Unit (fun _ _ => False) := ⟨fun _ _ _ h _ => h⟩
  exact h (r := fun _ _ => False) (r' := fun _ _ => False) (fun _ _ h => h) () () .refl

-- `Relation.reflTransGen_of_isTrans_reflexive` idx 4: necessary
theorem w1c7_112 : ¬ drop0% Relation.reflTransGen_of_isTrans_reflexive 4 := fun h => by
  have : Std.Refl rr3 := ⟨fun _ => Or.inl rfl⟩
  have := h (r := rr3) (r' := rr3) (fun _ _ h => h) 0 2 (.tail (b := 1) (.single (by decide)) (by decide))
  revert this; decide

-- `Relation.reflTransGen_of_isTrans_reflexive` idx 5: necessary
theorem w1c7_113 : ¬ drop0% Relation.reflTransGen_of_isTrans_reflexive 5 := fun h => by
  have := h (α := Bool) (r := Eq) (r' := fun _ _ => True) false true (.single trivial)
  exact absurd this (by decide)

-- `Relation.reflTransGen_le_of_equivalence_of_le` idx 3: necessary
theorem w1c7_114 : ¬ drop0% Relation.reflTransGen_le_of_equivalence_of_le 3 := fun h =>
  h (α := Unit) (r := fun _ _ => False) (r' := fun _ _ => False) (fun _ _ h => h) () () .refl

-- `Relation.reflTransGen_le_of_equivalence_of_le` idx 4: necessary
theorem w1c7_115 : ¬ drop0% Relation.reflTransGen_le_of_equivalence_of_le 4 := fun h => by
  have := h (α := Bool) (r := Eq) (r' := fun _ _ => True) ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
    false true (.single trivial)
  exact absurd this (by decide)

-- `Relation.reflTransGen_of_equivalence` idx 3: necessary
theorem w1c7_116 : ¬ drop0% Relation.reflTransGen_of_equivalence 3 := fun h =>
  h (α := Unit) (r := fun _ _ => False) (r' := fun _ _ => False) (fun _ _ h => h) () () .refl

-- `Relation.reflTransGen_of_equivalence` idx 4: necessary
theorem w1c7_117 : ¬ drop0% Relation.reflTransGen_of_equivalence 4 := fun h => by
  have := h (α := Bool) (r := Eq) (r' := fun _ _ => True) ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
    false true (.single trivial)
  exact absurd this (by decide)

-- `Quot.eqvGen_exact` idx 4: necessary
theorem w1c7_118 : ¬ drop0% Quot.eqvGen_exact 4 := fun h =>
  absurd (eqvF (h (α := Bool) (r := fun _ _ => False) (a := false) (b := true))) (by decide)

-- `Quot.eqvGen_sound` idx 4: necessary
theorem w1c7_119 : ¬ drop0% Quot.eqvGen_sound 4 := fun h => by
  have := congrArg (Quot.lift (fun b : Bool => b) (fun _ _ (h : False) => h.elim))
    (h (α := Bool) (r := fun _ _ => False) (a := false) (b := true))
  exact absurd this (by decide)

-- `Equivalence.eqvGen_iff` idx 4: necessary
theorem w1c7_120 : ¬ drop0% Equivalence.eqvGen_iff 4 := fun h =>
  (h (α := Unit) (r := fun _ _ => False) (a := ()) (b := ())).1 (.refl _)

-- `Equivalence.eqvGen_eq` idx 2: necessary
theorem w1c7_121 : ¬ drop0% Equivalence.eqvGen_eq 2 := fun h =>
  cast (congrFun (congrFun (h (α := Unit) (r := fun _ _ => False)) ()) ()) (.refl _)

-- `Relator.RightTotal.rel_forall` idx 3: necessary
theorem w1c7_122 : ¬ drop1% Relator.RightTotal.rel_forall 3 := fun h => by
  have := h (α := Unit) (β := Bool) (R := fun _ b => b = true)
  exact absurd ((this (a := fun _ => Unit) (b := fun b => b = true) (fun _ _ hab _ => hab))
    (fun _ => ()) false) (by decide)

-- `Relator.LeftTotal.rel_exists` idx 3: necessary
theorem w1c7_123 : ¬ drop1% Relator.LeftTotal.rel_exists 3 := fun h => by
  have := h (α := Bool) (β := Unit) (R := fun a _ => a = true)
  obtain ⟨_, h⟩ := (this (a := fun a => a = false) (b := fun _ => False)
    (fun _ _ hab hp => absurd (hab.symm.trans hp) (by decide))) ⟨false, rfl⟩
  exact h

-- `Relator.BiTotal.rel_forall` idx 3: necessary
theorem w1c7_124 : ¬ drop1% Relator.BiTotal.rel_forall 3 := fun h => by
  have := h (α := Unit) (β := Bool) (R := fun _ b => b = true)
  have := (this (a := fun _ => True) (b := fun b => b = true) (fun _ _ hab => ⟨fun _ => hab, fun _ => trivial⟩)).1
    (fun _ => trivial) false
  exact absurd this (by decide)

-- `Relator.BiTotal.rel_exists` idx 3: necessary
theorem w1c7_125 : ¬ drop1% Relator.BiTotal.rel_exists 3 := fun h => by
  have := h (α := Bool) (β := Unit) (R := fun a _ => a = true)
  obtain ⟨_, h⟩ := (this (a := fun a => a = false) (b := fun _ => False)
    (fun _ _ hab => ⟨fun hp => absurd (hab.symm.trans hp) (by decide), False.elim⟩)).1 ⟨false, rfl⟩
  exact h

-- `Relator.left_unique_of_rel_eq` idx 4: necessary
theorem w1c7_126 : ¬ drop1% Relator.left_unique_of_rel_eq 4 := fun h => by
  have h' := h (α := Bool) (β := Unit) (R := fun _ _ => True) (eq' := Eq)
  have := @h' false true () trivial trivial
  exact absurd this (by decide)

-- `Relator.LeftUnique.flip` idx 3: necessary
theorem w1c7_127 : ¬ drop0% Relator.LeftUnique.flip 3 := fun h => by
  have h' := h (α := Bool) (β := Unit) (r := fun _ _ => True)
  have := @h' () false true trivial trivial
  exact absurd this (by decide)

-- `Relator.rel_eq` idx 3: necessary
theorem w1c7_128 : ¬ drop0% Relator.rel_eq 3 := fun h => by
  have h' := h (α := Bool) (β := Unit) (r := fun _ _ => True)
  have := (@h' false () trivial true () trivial).2 rfl
  exact absurd this (by decide)

-- `Relator.LeftTotal.refl` idx 2: necessary
theorem w1c7_129 : ¬ drop0% Relator.LeftTotal.refl 2 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h (); exact h) (h (α := Unit) (r₁₁ := fun _ _ => False))

-- `Relator.LeftTotal.symm` idx 4: necessary
theorem w1c7_130 : ¬ drop0% Relator.LeftTotal.symm 4 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h (); exact h) (h (α := Unit) (β := Unit) (r₁₂ := fun _ _ => True) (r₂₁ := fun _ _ => False) (fun _ => ⟨(), trivial⟩))

-- `Relator.LeftTotal.symm` idx 5: necessary
theorem w1c7_131 : ¬ drop0% Relator.LeftTotal.symm 5 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h (); exact h) (h (α := Unit) (β := Unit) (r₁₂ := fun _ _ => False) (r₂₁ := fun _ _ => False)
    (fun _ _ h => h))

-- `Relator.LeftTotal.trans` idx 6: necessary
theorem w1c7_132 : ¬ drop0% Relator.LeftTotal.trans 6 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h (); exact h) (h (α := Unit) (β := Unit) (γ := Unit) (r₁₂ := fun _ _ => True) (r₂₃ := fun _ _ => True)
    (r₁₃ := fun _ _ => False) (fun _ => ⟨(), trivial⟩) (fun _ => ⟨(), trivial⟩))

-- `Relator.LeftTotal.trans` idx 7: necessary
theorem w1c7_133 : ¬ drop0% Relator.LeftTotal.trans 7 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h (); exact h) (h (α := Unit) (β := Unit) (γ := Unit) (r₁₂ := fun _ _ => False) (r₂₃ := fun _ _ => True)
    (r₁₃ := fun _ _ => False) (fun _ _ _ h _ => h) (fun _ => ⟨(), trivial⟩))

-- `Relator.LeftTotal.trans` idx 8: necessary
theorem w1c7_134 : ¬ drop0% Relator.LeftTotal.trans 8 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h (); exact h) (h (α := Unit) (β := Unit) (γ := Unit) (r₁₂ := fun _ _ => True) (r₂₃ := fun _ _ => False)
    (r₁₃ := fun _ _ => False) (fun _ _ _ _ h => h) (fun _ => ⟨(), trivial⟩))

-- `Relator.RightTotal.refl` idx 2: necessary
theorem w1c7_135 : ¬ drop0% Relator.RightTotal.refl 2 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h (); exact h) (h (α := Unit) (r₁₁ := fun _ _ => False))

-- `Relator.RightTotal.symm` idx 4: necessary
theorem w1c7_136 : ¬ drop0% Relator.RightTotal.symm 4 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h (); exact h) (h (α := Unit) (β := Unit) (r₁₂ := fun _ _ => True) (r₂₁ := fun _ _ => False) (fun _ => ⟨(), trivial⟩))

-- `Relator.RightTotal.symm` idx 5: necessary
theorem w1c7_137 : ¬ drop0% Relator.RightTotal.symm 5 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h (); exact h) (h (α := Unit) (β := Unit) (r₁₂ := fun _ _ => False) (r₂₁ := fun _ _ => False)
    (fun _ _ h => h))

-- `Relator.RightTotal.trans` idx 6: necessary
theorem w1c7_138 : ¬ drop0% Relator.RightTotal.trans 6 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h (); exact h) (h (α := Unit) (β := Unit) (γ := Unit) (r₁₂ := fun _ _ => True) (r₂₃ := fun _ _ => True)
    (r₁₃ := fun _ _ => False) (fun _ => ⟨(), trivial⟩) (fun _ => ⟨(), trivial⟩))

-- `Relator.RightTotal.trans` idx 7: necessary
theorem w1c7_139 : ¬ drop0% Relator.RightTotal.trans 7 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h (); exact h) (h (α := Unit) (β := Unit) (γ := Unit) (r₁₂ := fun _ _ => False) (r₂₃ := fun _ _ => True)
    (r₁₃ := fun _ _ => False) (fun _ _ _ h _ => h) (fun _ => ⟨(), trivial⟩))

-- `Relator.RightTotal.trans` idx 8: necessary
theorem w1c7_140 : ¬ drop0% Relator.RightTotal.trans 8 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h (); exact h) (h (α := Unit) (β := Unit) (γ := Unit) (r₁₂ := fun _ _ => True) (r₂₃ := fun _ _ => False)
    (r₁₃ := fun _ _ => False) (fun _ _ _ _ h => h) (fun _ => ⟨(), trivial⟩))

-- `Relator.BiTotal.refl` idx 2: necessary
theorem w1c7_141 : ¬ drop0% Relator.BiTotal.refl 2 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h.1 (); exact h) (h (α := Unit) (r₁₁ := fun _ _ => False))

-- `Relator.BiTotal.symm` idx 4: necessary
theorem w1c7_142 : ¬ drop0% Relator.BiTotal.symm 4 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h.1 (); exact h) (h (α := Unit) (β := Unit) (r₁₂ := fun _ _ => True) (r₂₁ := fun _ _ => False) ⟨fun _ => ⟨(), trivial⟩, fun _ => ⟨(), trivial⟩⟩)

-- `Relator.BiTotal.symm` idx 5: necessary
theorem w1c7_143 : ¬ drop0% Relator.BiTotal.symm 5 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h.1 (); exact h) (h (α := Unit) (β := Unit) (r₁₂ := fun _ _ => False) (r₂₁ := fun _ _ => False)
    (fun _ _ h => h))

-- `Relator.BiTotal.trans` idx 6: necessary
theorem w1c7_144 : ¬ drop0% Relator.BiTotal.trans 6 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h.1 (); exact h) (h (α := Unit) (β := Unit) (γ := Unit) (r₁₂ := fun _ _ => True) (r₂₃ := fun _ _ => True)
    (r₁₃ := fun _ _ => False) ⟨fun _ => ⟨(), trivial⟩, fun _ => ⟨(), trivial⟩⟩ ⟨fun _ => ⟨(), trivial⟩, fun _ => ⟨(), trivial⟩⟩)

-- `Relator.BiTotal.trans` idx 7: necessary
theorem w1c7_145 : ¬ drop0% Relator.BiTotal.trans 7 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h.1 (); exact h) (h (α := Unit) (β := Unit) (γ := Unit) (r₁₂ := fun _ _ => False) (r₂₃ := fun _ _ => True)
    (r₁₃ := fun _ _ => False) (fun _ _ _ h _ => h) ⟨fun _ => ⟨(), trivial⟩, fun _ => ⟨(), trivial⟩⟩)

-- `Relator.BiTotal.trans` idx 8: necessary
theorem w1c7_146 : ¬ drop0% Relator.BiTotal.trans 8 := fun h => by
  exact (fun h => by obtain ⟨_, h⟩ := h.1 (); exact h) (h (α := Unit) (β := Unit) (γ := Unit) (r₁₂ := fun _ _ => True) (r₂₃ := fun _ _ => False)
    (r₁₃ := fun _ _ => False) (fun _ _ _ _ h => h) ⟨fun _ => ⟨(), trivial⟩, fun _ => ⟨(), trivial⟩⟩)

-- `small_subtype` idx 1: necessary
theorem w1c7_147 : ¬ ∀ (α : Type 1) (P : α → Prop), Small.{0, 1} (Subtype fun x => P x) := fun h =>
  nsInj (fun X => (⟨X, trivial⟩ : {x : Type // True})) (fun _ _ e => congrArg Subtype.val e) (h Type fun _ => True)

-- `small_of_injective` idx 2: necessary
theorem w1c7_148 : ¬ ∀ {α : Type 1} {β : Type 1} {f : α → β}, Function.Injective f → Small.{0, 1} α := fun h =>
  not_small_type.{0, 0} (h (α := Type) (β := Type) (f := id) Function.injective_id)

-- `small_of_injective` idx 4: necessary
theorem w1c7_149 : ¬ ∀ {α : Type 1} {β : Type 0} [Small.{0, 0} β] {f : α → β}, Small.{0, 1} α := fun h =>
  not_small_type.{0, 0} (h (α := Type) (β := Unit) (f := fun _ => ()))

-- `small_of_surjective` idx 2: necessary
theorem w1c7_150 : ¬ ∀ {α : Type 1} {β : Type 1} {f : α → β}, Function.Surjective f → Small.{0, 1} β := fun h =>
  not_small_type.{0, 0} (h (α := Type) (β := Type) (f := id) Function.surjective_id)

-- `small_of_surjective` idx 4: necessary
theorem w1c7_151 : ¬ ∀ {α : Type 0} {β : Type 1} [Small.{0, 0} α] {f : α → β}, Small.{0, 1} β := fun h =>
  not_small_type.{0, 0} (h (α := Unit) (β := Type) (f := fun _ => Unit))

-- `small_subsingleton` idx 1: necessary
theorem w1c7_152 : ¬ ∀ (α : Type 1), Small.{0, 1} α := fun h =>
  not_small_type.{0, 0} (h Type)

-- `small_of_injective_of_exists` idx 3: necessary
theorem w1c7_153 : ¬ ∀ {α : Type 1} {β : Type 1} {γ : Type 1} (f : α → γ) {g : β → γ},
    Function.Injective g → (∀ b, ∃ a, f a = g b) → Small.{0, 1} β := fun h =>
  not_small_type.{0, 0} (h (α := Type) (β := Type) (γ := Type) id (g := id) Function.injective_id
    (fun b => ⟨b, rfl⟩))

-- `small_of_injective_of_exists` idx 6: necessary
theorem w1c7_154 : ¬ ∀ {α : Type 0} {β : Type 1} {γ : Type 0} [Small.{0, 0} α] (f : α → γ) {g : β → γ},
    (∀ b, ∃ a, f a = g b) → Small.{0, 1} β := fun h =>
  not_small_type.{0, 0} (h (α := Unit) (β := Type) (γ := Unit) id (g := fun _ => ()) (fun _ => ⟨(), rfl⟩))

-- `small_of_injective_of_exists` idx 7: necessary
theorem w1c7_155 : ¬ ∀ {α : Type 0} {β : Type 1} {γ : Type 1} [Small.{0, 0} α] (f : α → γ) {g : β → γ},
    Function.Injective g → Small.{0, 1} β := fun h =>
  not_small_type.{0, 0} (h (α := Unit) (β := Type) (γ := Type) (fun _ => Unit) (g := id) Function.injective_id)

-- `small_Pi` idx 2: necessary
theorem w1c7_156 : ¬ ∀ {α : Type 1} (β : α → Type 0) [∀ a, Small.{0, 0} (β a)], Small.{0, 1} ((a : α) → β a) :=
  fun h => nsInj (fun X : Type => fun Y : Type => X = Y) (fun X Y e => cast (congrFun e Y).symm rfl)
    (h (α := Type) (fun _ => Prop))

-- `small_Pi` idx 3: necessary
theorem w1c7_157 : ¬ ∀ {α : Type 0} (β : α → Type 1) [Small.{0, 0} α], Small.{0, 1} ((a : α) → β a) :=
  fun h => nsInj (fun X : Type => fun _ : Unit => X) (fun X Y e => congrFun e ())
    (h (α := Unit) (fun _ => Type))

-- `small_prod` idx 2: necessary
theorem w1c7_158 : ¬ ∀ {α : Type 1} {β : Type 0} [Small.{0, 0} β], Small.{0, 1} (α × β) := fun h =>
  nsInj (fun X : Type => (X, ())) (fun _ _ e => congrArg Prod.fst e) (h (α := Type) (β := Unit))

-- `small_prod` idx 3: necessary
theorem w1c7_159 : ¬ ∀ {α : Type 0} {β : Type 1} [Small.{0, 0} α], Small.{0, 1} (α × β) := fun h =>
  nsInj (fun X : Type => ((), X)) (fun _ _ e => congrArg Prod.snd e) (h (α := Unit) (β := Type))

-- `small_sum` idx 2: necessary
theorem w1c7_160 : ¬ ∀ {α : Type 1} {β : Type 0} [Small.{0, 0} β], Small.{0, 1} (α ⊕ β) := fun h =>
  nsInj (fun X : Type => (Sum.inl X : Type ⊕ Unit)) Sum.inl_injective (h (α := Type) (β := Unit))

-- `small_sum` idx 3: necessary
theorem w1c7_161 : ¬ ∀ {α : Type 0} {β : Type 1} [Small.{0, 0} α], Small.{0, 1} (α ⊕ β) := fun h =>
  nsInj (fun X : Type => (Sum.inr X : Unit ⊕ Type)) Sum.inr_injective (h (α := Unit) (β := Type))

-- `small_set` idx 1: necessary
theorem w1c7_162 : ¬ ∀ {α : Type 1}, Small.{0, 1} (Set α) := fun h =>
  nsInj (fun X : Type => ({X} : Set Type)) (fun _ _ e => Set.singleton_injective e) (h (α := Type))

-- `small_quot` idx 1: necessary
theorem w1c7_163 : ¬ ∀ {α : Type 1} (r : α → α → Prop), Small.{0, 1} (Quot r) := fun h =>
  nsSurj (Quot.lift (r := fun _ _ : Type => False) id (fun _ _ h => h.elim)) (fun X => ⟨Quot.mk _ X, rfl⟩)
    (h (α := Type) (fun _ _ => False))

-- `small_quotient` idx 1: necessary
theorem w1c7_164 : ¬ ∀ {α : Type 1} (s : Setoid α), Small.{0, 1} (Quotient s) := fun h =>
  nsSurj (Quotient.lift (s := ⟨Eq, eq_equivalence⟩) (id : Type → Type) (fun _ _ h => h))
    (fun X => ⟨Quotient.mk _ X, rfl⟩) (h (α := Type) ⟨Eq, eq_equivalence⟩)

-- `small_orderDual` idx 1: necessary
theorem w1c7_165 : ¬ ∀ {α : Type 1}, Small.{0, 1} (OrderDual α) := fun h =>
  nsInj (fun X : Type => OrderDual.toDual X) OrderDual.toDual.injective (h (α := Type))

-- `Small.equiv_small` idx 1: necessary
theorem w1c7_166 : ¬ ∀ {α : Type 1}, ∃ S : Type 0, Nonempty (α ≃ S) := fun h => by
  obtain ⟨S, ⟨e⟩⟩ := h (α := Type)
  exact not_small_type.{0, 0} (Small.mk' e)

-- `Shrink.ext_iff` idx 1: necessary
theorem w1c7_167 : ¬ ∀ {α : Type 1}, Small.{0, 1} α := fun h =>
  not_small_type.{0, 0} (h (α := Type))

-- `Shrink.ext` idx 1: necessary
theorem w1c7_168 : ¬ ∀ {α : Type 1}, Small.{0, 1} α := fun h =>
  not_small_type.{0, 0} (h (α := Type))

-- `Shrink.ext` idx 4: necessary
theorem w1c7_169 : ¬ drop0% Shrink.ext 4 := fun h =>
  absurd ((equivShrink Bool).injective (h (α := Bool) (x := equivShrink Bool false) (y := equivShrink Bool true)))
    (by decide)

-- `Shrink.rec_equivShrink` idx 1: necessary
theorem w1c7_170 : ¬ ∀ {α : Type 1} (a : α), Small.{0, 1} α := fun h =>
  not_small_type.{0, 0} (h (α := Type) Unit)

-- `small_map` idx 2: necessary
theorem w1c7_171 : ¬ ∀ {α : Type 1} {β : Type 1} (e : α ≃ β), Small.{0, 1} α := fun h =>
  not_small_type.{0, 0} (h (α := Type) (β := Type) (Equiv.refl _))

-- `small_lift` idx 1: necessary
theorem w1c7_172 : ¬ ∀ (α : Type 1), Small.{max 0 0, 1} α := fun h =>
  not_small_type.{0, 0} (h Type)

-- `small_ulift` idx 1: necessary
theorem w1c7_173 : ¬ ∀ (α : Type 1), Small.{0, max 0 1} (ULift.{0, 1} α) := fun h =>
  nsInj (fun X : Type => ULift.up.{0, 1} X) ULift.up_injective (h Type)

-- `small_plift` idx 1: necessary
theorem w1c7_174 : ¬ ∀ (α : Type 1), Small.{0} (PLift α) := fun h =>
  not_small_type.{0, 0} (@small_of_injective _ _ (h Type) (fun X : Type => PLift.up X) PLift.up_injective)

-- `instNontrivialShrink` idx 1: necessary
theorem w1c7_175 : ¬ ∀ {α : Type 1} [Nontrivial α], Small.{0, 1} α := fun h =>
  not_small_type.{0, 0} (@h Type ntType)

-- `instNontrivialShrink` idx 2: necessary
theorem w1c7_176 : ¬ drop0% instNontrivialShrink 2 := fun h => by
  have := h (α := Unit)
  have := (equivShrink Unit).symm.injective.nontrivial
  exact not_nontrivial Unit this

-- `small_sigma` idx 2: necessary
theorem w1c7_177 : ¬ ∀ {α : Type 1} (β : α → Type 0) [∀ a, Small.{0, 0} (β a)], Small.{0, 1} ((a : α) × β a) :=
  fun h => nsInj (fun X : Type => (⟨X, ()⟩ : (_ : Type) × Unit)) (fun _ _ e => congrArg Sigma.fst e)
    (h (α := Type) (fun _ => Unit))

-- `small_sigma` idx 3: necessary
theorem w1c7_178 : ¬ ∀ {α : Type 0} (β : α → Type 1) [Small.{0, 0} α], Small.{0, 1} ((a : α) × β a) :=
  fun h => nsInj (fun X : Type => (⟨(), X⟩ : (_ : Unit) × Type)) (fun _ _ e => by cases e; rfl)
    (h (α := Unit) (fun _ => Type))

-- `smallVector` idx 2: necessary
theorem w1c7_179 : ¬ ∀ {α : Type 1} {n : ℕ}, Small.{0, 1} (List.Vector α n) := fun h =>
  nsInj (fun X : Type => (⟨[X], rfl⟩ : List.Vector Type 1))
    (fun _ _ e => List.head_eq_of_cons_eq (congrArg Subtype.val e)) (h (α := Type) (n := 1))

-- `smallList` idx 1: necessary
theorem w1c7_180 : ¬ ∀ {α : Type 1}, Small.{0, 1} (List α) := fun h =>
  nsInj (fun X : Type => [X]) (fun _ _ e => List.head_eq_of_cons_eq e) (h (α := Type))
