module

import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex

namespace GlobalTheory.IntegralGauge

theorem exists_chart_local {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (ψ : Sp V ⟶ X) : ∃ j, ⊤ ≤ ψ ⁻¹ᵁ L.U j := by
  have h : ψ (IsLocalRing.closedPoint V) ∈ (⨆ i, L.U i) := by rw [hL.1]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨j, fun w _ => (IsLocalRing.specializes_closedPoint (R := V) w).mem_open (ψ ⁻¹ᵁ L.U j).isOpen hj⟩

theorem exists_extension {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (S : ValuationSubring F)
    (hS : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S)
    (x : TF (R := R) F ⟶ D.P.A) : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left := by
  apply GlobalTheory.ValuesExist.exists_ext <;> assumption

theorem exists_integral_gauge (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (S : ValuationSubring F)
    (hS : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) :
    ∃ J : (Sp F ⟶ D.P.A.left) → D.P.L.ι, (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) ∧ ∀ x : TF (R := R) F ⟶ D.P.A,
      ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left ∧ ⊤ ≤ x₀ ⁻¹ᵁ D.P.L.U (J x.left) := by
  have key : ∀ ψ : Sp F ⟶ D.P.A.left, ∃ j, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U j ∧
      ((∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ) →
        ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ D.P.L.U j) := fun ψ => by
    by_cases h : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = ψ
    · obtain ⟨x₀, rfl⟩ := h
      obtain ⟨j, hj⟩ := exists_chart_local D.P.isLB x₀
      exact ⟨j, fun w _ => hj (trivial : spMap S.subtype w ∈ (⊤ : (Sp S).Opens)), fun _ => ⟨x₀, rfl, hj⟩⟩
    · obtain ⟨j, hj⟩ := exists_chart_local D.P.isLB ψ
      exact ⟨j, hj, fun h' => (h h').elim⟩
  choose J h₁ h₂ using key
  exact ⟨J, h₁, fun x => h₂ x.left (exists_extension D S hS x)⟩

end GlobalTheory.IntegralGauge
