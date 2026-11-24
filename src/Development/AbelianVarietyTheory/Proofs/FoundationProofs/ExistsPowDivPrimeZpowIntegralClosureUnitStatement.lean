module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowDivPrimeZpowIntegralClosureUnit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedIntegersAdicComplete
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.exists_pow_div_prime_zpow_integralClosure_unit : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ x : Ω, x ≠ 0 → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsInt (p := p) (x ^ b / (p : Ω) ^ a) ∧
    IsInt (p := p) ((p : Ω) ^ a / x ^ b) := by
  intro p _ Ω _ _ hΩ x hx
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
  have : IsAdicComplete (IsLocalRing.maximalIdeal (O0 p)) (O0 p) := by
    rw [hmax]
    exact o0_isAdicComplete_span_p p
  have : FaithfulSMul (O0 p) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hΩ.inj
  let _ : Algebra (FractionRing (O0 p)) Ω := FractionRing.liftAlgebra (O0 p) Ω
  have : IsScalarTower (O0 p) (FractionRing (O0 p)) Ω :=
    FractionRing.isScalarTower_liftAlgebra (O0 p) Ω
  have : Algebra.IsAlgebraic (O0 p) Ω := hΩ.alg
  have : Algebra.IsAlgebraic (FractionRing (O0 p)) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) (FractionRing (O0 p)))
  have hIntegral := exists_pow_div_zpow_isIntegral (O0 p) (FractionRing (O0 p)) Ω (p : O0 p)
    hirr x hx
  simpa only [IsInt, map_natCast] using hIntegral
