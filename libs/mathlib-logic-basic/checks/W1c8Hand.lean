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
namespace W1c8
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

/-- A type into which Type injects is not 0-small. -/
theorem nsm {X : Type 1} (f : Type → X) (hf : Function.Injective f) : ¬ Small.{0} X :=
  fun _ => not_small_type.{0, 0} (small_of_injective hf)
/-- A set of types containing every type is not 0-small. -/
theorem nsub {s : Set Type} (h : ∀ x, x ∈ s) : ¬ Small.{0} ↥s :=
  nsm (fun x => ⟨x, h x⟩) (fun _ _ e => congrArg Subtype.val e)
/-- Same, with the smallness proof first (fixes the set before the membership proof is elaborated). -/
theorem nS {s : Set Type} (hs : Small.{0} ↥s) (h : ∀ x, x ∈ s) : False := nsub h hs
/-- The empty set of types is 0-small (instance search times out on it). -/
instance sE {α : Type 1} : Small.{0} ↥(∅ : Set α) := ⟨⟨PEmpty, ⟨Equiv.equivPEmpty _⟩⟩⟩
end W1c8

open W1c8 Set

-- `small_subset` idx 3
theorem w8_1 : ¬ dropL% small_subset 3 [0,1] :=
  fun h => nS (@h Type ∅ univ sE) (fun x => mem_univ x)
-- `small_subset` idx 4
theorem w8_2 : ¬ dropL% small_subset 4 [0,1] :=
  fun h => nS (@h Type univ univ subset_rfl) (fun x => mem_univ x)
-- `small_powerset` idx 2
theorem w8_3 : ¬ dropL% small_powerset 2 [0,1] :=
  fun h => nsm (X := ↥(𝒫 (univ : Set Type))) (fun x => ⟨{x}, subset_univ _⟩)
    (fun a b e => by simpa using congrArg Subtype.val e) (@h Type univ)
-- `small_setProd` idx 4
theorem w8_4 : ¬ dropL% small_setProd 4 [0,1,0] :=
  fun h => nsm (X := ↥((univ : Set Type) ×ˢ (univ : Set Unit))) (fun x => ⟨(x, ()), by simp⟩)
    (fun a b e => by simpa using congrArg Subtype.val e) (@h Type Unit univ univ inferInstance)
-- `small_setProd` idx 5
theorem w8_5 : ¬ dropL% small_setProd 5 [0,0,1] :=
  fun h => nsm (X := ↥((univ : Set Unit) ×ˢ (univ : Set Type))) (fun x => ⟨((), x), by simp⟩)
    (fun a b e => by simpa using congrArg Subtype.val e) (@h Unit Type univ univ inferInstance)
-- `small_setPi` idx 3
theorem w8_6 : ¬ dropL% small_setPi 3 [0,1,0] :=
  fun h => nsm (X := ↥(Set.pi univ (fun _ : Type => (univ : Set Prop)))) (fun x => ⟨fun y => y = x, by simp⟩)
    (fun a b e => by
      have := congrFun (congrArg Subtype.val e) a
      exact cast this rfl)
    (@h Type (fun _ => Prop) (fun _ => univ) (fun _ => inferInstance))
-- `small_setPi` idx 4
theorem w8_7 : ¬ dropL% small_setPi 4 [0,0,1] :=
  fun h => nsm (X := ↥(Set.pi univ (fun _ : Unit => (univ : Set Type)))) (fun x => ⟨fun _ => x, by simp⟩)
    (fun a b e => congrFun (congrArg Subtype.val e) ())
    (@h Unit (fun _ => Type) (fun _ => univ) inferInstance)
-- `small_range` idx 3
theorem w8_8 : ¬ dropL% small_range 3 [0,1,1] :=
  fun h => nS (@h Type Type id) (fun x => ⟨x, rfl⟩)
-- `small_image` idx 4
theorem w8_9 : ¬ dropL% small_image 4 [0,1,1] :=
  fun h => nS (@h Type Type id univ) (fun x => ⟨x, trivial, rfl⟩)
-- `small_image2` idx 6
theorem w8_10 : ¬ dropL% small_image2 6 [0,1,0,1] :=
  fun h => nS (@h Type Unit Type (fun a _ => a) univ univ inferInstance) (fun x => mem_image2_of_mem (mem_univ x) (mem_univ ()))
-- `small_image2` idx 7
theorem w8_11 : ¬ dropL% small_image2 7 [0,0,1,1] :=
  fun h => nS (@h Unit Type Type (fun _ b => b) univ univ inferInstance) (fun x => mem_image2_of_mem (mem_univ ()) (mem_univ x))
-- `small_univ` idx 1
theorem w8_12 : ¬ dropL% small_univ 1 [0,1] :=
  fun h => nS (@h Type) (fun x => mem_univ x)
-- `small_union` idx 3
theorem w8_13 : ¬ dropL% small_union 3 [0,1] :=
  fun h => nS (@h Type univ ∅ sE) (fun x => Or.inl (mem_univ x))
-- `small_union` idx 4
theorem w8_14 : ¬ dropL% small_union 4 [0,1] :=
  fun h => nS (@h Type ∅ univ sE) (fun x => Or.inr (mem_univ x))
-- `small_iUnion` idx 2
theorem w8_15 : ¬ dropL% small_iUnion 2 [0,1,1] :=
  fun h => nS (@h Type Type (fun i => {i}) inferInstance) (fun x => mem_iUnion.2 ⟨x, rfl⟩)
-- `small_iUnion` idx 4
theorem w8_16 : ¬ dropL% small_iUnion 4 [0,1,0] :=
  fun h => nS (@h Type Unit inferInstance (fun _ => univ)) (fun x => mem_iUnion.2 ⟨(), mem_univ x⟩)
-- `small_sUnion` idx 2
theorem w8_17 : ¬ dropL% small_sUnion 2 [0,1] :=
  fun h => nS (@h Type (range fun x : Type => ({x} : Set Type)) (fun t => by
      obtain ⟨_, x, rfl⟩ := t
      infer_instance)) (fun x => ⟨{x}, ⟨x, rfl⟩, rfl⟩)
-- `small_sUnion` idx 3
theorem w8_18 : ¬ dropL% small_sUnion 3 [0,1] :=
  fun h => nS (@h Type {univ} inferInstance) (fun x => ⟨univ, rfl, mem_univ x⟩)
-- `small_biUnion` idx 3
theorem w8_19 : ¬ dropL% small_biUnion 3 [0,1,1] :=
  fun h => nS (@h Type Type univ (fun i _ => {i}) inferInstance) (fun x => by simp)
-- `small_biUnion` idx 5
theorem w8_20 : ¬ dropL% small_biUnion 5 [0,1,0] :=
  fun h => nS (@h Type Unit univ inferInstance (fun _ _ => univ)) (fun x => by simp)
-- `small_insert` idx 3
theorem w8_21 : ¬ dropL% small_insert 3 [0,1] :=
  fun h => nS (@h Type PUnit univ) (fun x => Or.inr (mem_univ x))
-- `small_diff` idx 3
theorem w8_22 : ¬ dropL% small_diff 3 [0,1] :=
  fun h => nS (@h Type univ ∅) (fun x => ⟨mem_univ x, notMem_empty x⟩)
-- `small_sep` idx 3
theorem w8_23 : ¬ dropL% small_sep 3 [0,1] :=
  fun h => nS (@h Type univ (fun _ => True)) (fun x => ⟨mem_univ x, trivial⟩)
-- `small_inter_of_left` idx 3
theorem w8_24 : ¬ dropL% small_inter_of_left 3 [0,1] :=
  fun h => nS (@h Type univ univ) (fun x => ⟨mem_univ x, mem_univ x⟩)
-- `small_inter_of_right` idx 3
theorem w8_25 : ¬ dropL% small_inter_of_right 3 [0,1] :=
  fun h => nS (@h Type univ univ) (fun x => ⟨mem_univ x, mem_univ x⟩)
-- `small_iInter` idx 4
theorem w8_26 : ¬ dropL% small_iInter 4 [0,1,0] :=
  fun h => nS (@h Type Unit (fun _ => univ) ()) (fun x => mem_iInter.2 fun _ => mem_univ x)
-- `small_iInter'` idx 2
theorem w8_27 : ¬ dropL% small_iInter' 2 [0,1,0] :=
  fun h => nS (@h Type Empty (fun _ => univ) (fun i => i.elim)) (fun x => mem_iInter.2 fun i => i.elim)
-- `small_iInter'` idx 4
theorem w8_28 : ¬ dropL% small_iInter' 4 [0,1,0] :=
  fun h => nS (@h Type Unit inferInstance (fun _ => univ)) (fun x => mem_iInter.2 fun _ => mem_univ x)
-- `small_sInter` idx 3
theorem w8_29 : ¬ dropL% small_sInter 3 [0,1] :=
  fun h => nS (@h Type ∅ ∅ sE) (fun x => fun t ht => absurd ht (notMem_empty t))
-- `small_sInter` idx 4
theorem w8_30 : ¬ dropL% small_sInter 4 [0,1] :=
  fun h => nS (@h Type {univ} univ rfl) (fun x => fun t ht => by rw [mem_singleton_iff.1 ht]; exact mem_univ x)
-- `small_sInter'` idx 2
theorem w8_31 : ¬ dropL% small_sInter' 2 [0,1] :=
  fun h => nS (@h Type ∅ (fun t => absurd t.2 (notMem_empty _))) (fun x => fun t ht => absurd ht (notMem_empty t))
-- `small_sInter'` idx 3
theorem w8_32 : ¬ dropL% small_sInter' 3 [0,1] :=
  fun h => nS (@h Type {univ} ⟨⟨univ, rfl⟩⟩) (fun x => fun t ht => by rw [mem_singleton_iff.1 ht]; exact mem_univ x)
-- `small_biInter` idx 4
theorem w8_33 : ¬ indep0% small_biInter 4 :=
  fun h => notMem_empty () (@h Unit Unit ∅ () (fun _ _ => univ))
-- `small_biInter` idx 6
theorem w8_34 : ¬ dropL% small_biInter 6 [0,1,0] :=
  fun h => nS (@h Type Unit univ () trivial (fun _ _ => univ)) (fun x => by simp)
-- `small_biInter'` idx 3
theorem w8_35 : ¬ dropL% small_biInter' 3 [0,1,0] :=
  fun h => nS (@h Type Unit ∅ (fun _ _ => univ) (fun i hi => absurd hi (notMem_empty i))) (fun x => by simp)
-- `small_biInter'` idx 5
theorem w8_36 : ¬ dropL% small_biInter' 5 [0,1,0] :=
  fun h => nS (@h Type Unit univ inferInstance (fun _ _ => univ)) (fun x => by simp)
