module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.IntGauge

theorem exists_ball (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 := by
  refine ⟨{ carrier := {x | ‖x‖ ≤ 1}
            mul_mem' := fun {a b} ha hb => by
              simp only [Set.mem_setOf_eq, norm_mul] at *
              exact mul_le_one₀ ha (norm_nonneg _) hb
            one_mem' := by simp
            add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
            zero_mem' := by simp
            neg_mem' := fun {a} ha => by simpa using ha
            mem_or_inv_mem' := fun x => by
              by_cases h : ‖x‖ ≤ 1
              · exact Or.inl h
              · right
                show ‖x⁻¹‖ ≤ 1
                rw [norm_inv]
                exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 h)) }, fun x => Iff.rfl⟩

theorem exists_intN : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∃ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN := by
  intro V _ _ _ _ _ D C _ _ _ _ _ _ hC
  obtain ⟨S, hS⟩ := exists_ball C
  obtain ⟨N, ν, hν⟩ := GlobalTheory.ValuesExist.exists_integral_values GlobalTheory.firstFiveLaws.1 V D.toPre D.psi_even D.tau_bimult
    C S (fun r => (hS _).2 (hC.1 r))
  exact ⟨N, ν, S, hS, hν⟩

end GlobalTheory.IntGauge
end
