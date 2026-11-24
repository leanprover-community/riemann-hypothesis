module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.LaEqSqrtSmulLam
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

@[expose] public section

noncomputable section

open MeasureTheory Matrix GlobalTheory.WeilM

namespace GlobalTheory.CompanionTheory.VacLoc

section Ground

variable {R : Type} [CommRing R] [TopologicalSpace R]

structure GoodChar (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) : Prop where
  norm_one : ∀ x, ‖ψ x‖ = 1
  compact : IsCompact (O : Set R)
  isOpen : IsOpen (O : Set R)
  ann : ∀ x : R, (∀ y ∈ O, ψ (x * y) = 1) ↔ ((u⁻¹ : Rˣ) : R) * x ∈ O
  basis : ∀ U ∈ nhds (0 : R), ∃ v : Rˣ, ∀ y ∈ O, (v : R) * y ∈ U
  den : ∀ x : R, ∃ v : Rˣ, (v : R) ∈ O ∧ (v : R) * x ∈ O

def pair {κ : Type} (μ : @Measure (κ → R) (borel _)) (φ φ' : (κ → R) → ℂ) : ℂ :=
  ∫ x, (starRingEnd ℂ) (φ x) * φ' x ∂μ

variable [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ]

def IsModel (ψ : AddChar R ℂ) (d : Darboux B κ) (μ : @Measure (κ → R) (borel _))
    (S : GlobalTheory.CompanionTheory.FinHeis.Sys W (SB (κ → R))) : Prop :=
  (∀ w (φ : SB (κ → R)), ((S.rho w φ : SB (κ → R)) : (κ → R) → ℂ) = d.rho ψ w φ) ∧
  (∀ φ φ' : SB (κ → R), S.B φ φ' = pair μ φ φ') ∧ ∀ w w', S.c w w' = ψ (⅟(2 : R) * B w w')

end Ground

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end GlobalTheory.CompanionTheory.VacLoc
