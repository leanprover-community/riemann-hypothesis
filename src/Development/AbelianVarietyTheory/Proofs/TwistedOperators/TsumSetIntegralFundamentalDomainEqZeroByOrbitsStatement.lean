module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSetIntegralFundamentalDomainEqZeroByOrbits
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.tsum_setIntegral_fundamentalDomain_eq_zero_by_orbits : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y] [MulAction Γ Y] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 ν → ∀ Φ : Y → H → ℂ, (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) → ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ → (∀ y (𝓖 : Set H), IsFundamentalDomain ((MulAction.stabilizer Γ y).map Γ.subtype) 𝓖 ν → IntegrableOn (Φ y) 𝓖 ν → ∫ h in 𝓖, Φ y h ∂ν = 0) → ∑' y, ∫ h in 𝓕, Φ y h ∂ν = 0 := by
  first | exact @GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero | exact GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero | (intros; apply GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero <;> assumption)
