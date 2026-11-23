module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquareStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1StructureBaseChangeExtensionStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem axesE1_of_axesO1 : AxesVanishingStructureSheafDegOne → AxesVanishingExtendedDegOne := by
  intro hO R₀ R₁ _ _ _ q hq A _ g hab hsm c h₁ h₂
  obtain ⟨B, hB, pr, pr', habB, hsmB, hp, hp', -, -, -, hl, hr⟩ :=
    GlobalTheory.T.exists_abelianScheme_baseChange_and_square R₀ R₁ A g hab hsm
  letI : GrpObj B := hB
  obtain ⟨e, he⟩ := GlobalTheory.T.h1_structure_base_change_extension R₀ R₁ q hq
  set c₁ := (e _ _ _ _ _ hp').symm c with hc₁
  have hc : e _ _ _ _ _ hp' c₁ = c := by simp [hc₁]
  have hl' : IsPullO (overW (lift (𝟙 B) 1)) c₁ 0 := by
    refine he _ _ _ _ _ hp' _ _ _ _ _ hp _ _ (overW (lift (𝟙 A) 1)) (overW (lift (𝟙 B) 1)) hl c₁ 0 ?_
    rw [hc, map_zero]; exact h₁
  have hr' : IsPullO (overW (lift 1 (𝟙 B))) c₁ 0 := by
    refine he _ _ _ _ _ hp' _ _ _ _ _ hp _ _ (overW (lift 1 (𝟙 A))) (overW (lift 1 (𝟙 B))) hr c₁ 0 ?_
    rw [hc, map_zero]; exact h₂
  have h0 : c₁ = 0 := hO R₁ B g habB hsmB c₁ hl' hr'
  rw [← hc, h0, map_zero]

end GlobalTheory.Obs
