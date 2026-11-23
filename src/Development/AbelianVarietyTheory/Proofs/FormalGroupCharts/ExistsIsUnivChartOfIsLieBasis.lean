module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftInjective
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsJetChartCoordinatesNilpotentStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsJetPointsOfIsLieBasis
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetChartCoordinatesUniqueCommGroupStatement
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isUnivChart_of_isLieBasis :
    ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G],
      Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v →
      ∃ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), IsUnivChart G d x ∧
        (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) := by
  intro R _ G _ _ hG d v hv
  obtain ⟨x, h₁, h₂, h₃⟩ := GlobalTheory.exists_jetPoints_of_isLieBasis R G hG d v hv
  refine ⟨x, ⟨h₁, h₂, ?_⟩, h₃⟩
  intro A _ _ aug m hm y hy
  obtain ⟨ψ, hψ, hyψ⟩ := GlobalTheory.T.exists_jetChart_coordinates_nilpotent R G hG d v hv x h₁ h₂ h₃ A aug m hm y hy
  refine ⟨ψ, ⟨hψ, hyψ⟩, ?_⟩
  rintro ψ' ⟨hψ', hyψ'⟩
  exact GlobalTheory.T.jetChart_coordinates_unique_commGroup R G hG d v hv x h₁ h₂ h₃ A aug m hm ψ' ψ hψ' hψ (hyψ'.symm.trans hyψ)

end GlobalTheory
