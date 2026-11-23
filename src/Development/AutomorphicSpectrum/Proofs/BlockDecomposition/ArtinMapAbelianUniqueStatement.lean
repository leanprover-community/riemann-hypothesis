module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinMapAbelianUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

@[expose] public section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

theorem _root_.GlobalTheory.T.artin_map_abelian_unique : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (Art Art' : Neutral.B1.IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K), Neutral.B1.IsGlobalArtinMap K Art → Neutral.B1.IsGlobalArtinMap K Art' → ∀ (L : IntermediateField K (AlgebraicClosure K)) (h : Neutral.B1.IsFiniteAbelian K L) (c : Neutral.B1.IdeleClassGroup K), Neutral.B1.abRestrict K L h (Art c) = Neutral.B1.abRestrict K L h (Art' c) := by
  exact @GlobalTheory.CompanionTheory.ArtinUniq.abRestrict_eq
