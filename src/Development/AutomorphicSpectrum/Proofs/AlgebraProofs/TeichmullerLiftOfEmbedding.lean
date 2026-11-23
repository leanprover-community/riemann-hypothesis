module

public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.WeilBound.CoreStatements.HodgeTatePoints.EqOfPowEqSelf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem teichmuller_lift_of_embedding : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (F : Type) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (ζ : O), IsPrimitiveRoot ζ (Fintype.card F - 1) → ∀ σ : F →+* IsLocalRing.ResidueField O, (∃! χ : F →*₀ O, ∀ a, IsLocalRing.residue O (χ a) = σ a) ∧ ∀ (σ' : F →+* IsLocalRing.ResidueField O) (χ χ' : F →*₀ O), (∀ a, σ' a = σ a ^ p) → (∀ a, IsLocalRing.residue O (χ a) = σ a) → (∀ a, IsLocalRing.residue O (χ' a) = σ' a) → ∀ a, χ' a = χ a ^ p :=
  PositivityTheory.HtPt.Teich.glue_teich

end GlobalTheory.CompanionTheory.Ar.Num
