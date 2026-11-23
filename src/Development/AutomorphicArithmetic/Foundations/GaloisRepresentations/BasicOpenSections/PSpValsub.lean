module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIffIntegrallyClosedAlgCStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgClosedResidueFieldOfAic
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
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.Gal.Mod.spValsub :
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (V : ValuationSubring Ω), AIC V ∧ SH V := by
  intro Ω _ _ V
  have hclosed : IsAlgClosed (FractionRing V) :=
    IsAlgClosed.of_ringEquiv Ω (FractionRing V)
      (IsLocalization.algEquiv (nonZeroDivisors V) Ω (FractionRing V)).toRingEquiv
  have hA : AIC V := (GlobalTheory.T.monicPolynomialsHaveRoots_iff_integrallyClosed_algClosed V).2 ⟨inferInstance, hclosed⟩
  exact ⟨hA, GlobalTheory.GenusTwoPureComparison.Cmp.sh_of_aic hA⟩
