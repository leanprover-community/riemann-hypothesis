module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolLift

theorem lift_of_pullback_comp : ∀ {S₀ S₁ S₂ : Scheme.{0}} (f₁ : S₁ ⟶ S₀) (f₂ : S₂ ⟶ S₁) (A : PolAV S₀) (B : PolAV S₁) (P : PolAV S₂) (b : B.A.left ⟶ A.A.left) (a : P.A.left ⟶ A.A.left), IsGrpPullback B.A A.A f₁ b → IsGrpPullback P.A A.A (f₂ ≫ f₁) a → ∃ c : P.A.left ⟶ B.A.left, c ≫ b = a ∧ c ≫ B.A.hom = P.A.hom ≫ f₂ ∧ IsGrpPullback P.A B.A f₂ c ∧ (LBIso P.L (A.L.pull a) → LBIso B.L (A.L.pull b) → LBIso P.L (B.L.pull c)) := by
  intro S₀ S₁ S₂ f₁ f₂ A B P b a hB hP
  have w : a ≫ A.A.hom = (P.A.hom ≫ f₂) ≫ f₁ := by
    rw [hP.1.w, Category.assoc]
  refine ⟨hB.1.lift a (P.A.hom ≫ f₂) w, hB.1.lift_fst _ _ w, hB.1.lift_snd _ _ w, ?_, ?_⟩
  · exact IsGrpPullback.cancel hB (hP.congr rfl (hB.1.lift_fst _ _ w).symm) (hB.1.lift_snd _ _ w)
  · intro hPa hBb
    have e : hB.1.lift a (P.A.hom ≫ f₂) w ≫ b = a := hB.1.lift_fst _ _ w
    have h2 : LBIso (B.L.pull (hB.1.lift a (P.A.hom ≫ f₂) w)) (A.L.pull a) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull B.L _ _ rfl)
        (chartPullSame A.L (fun _ => a) (fun _ => b) _ _ fun _ => e.symm) hBb
    exact LBIso.trans P.isLB (pull_isLB A.isLB a) (pull_isLB B.isLB _) hPa h2.symm

end GlobalTheory.PolLift
