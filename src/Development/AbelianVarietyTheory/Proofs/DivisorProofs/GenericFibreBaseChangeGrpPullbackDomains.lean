module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
namespace GlobalTheory.GenFibreBaseChange

theorem genFibre_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ → ∀ (G : Over (Sp R)) [GrpObj G], ∃ π₀ : ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).left ⟶ ((Over.pullback (jK R)).obj G).left, IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) ((Over.pullback (jK R)).obj G) (spMap a) π₀ ∧ ∀ L : LB G.left, L.IsLB → LBIso ((L.pull (pullback.fst G.hom (spMap ρ))).pull (pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R'))) ((L.pull (pullback.fst G.hom (jK R))).pull π₀) := by
  intro R R' _ _ _ _ ρ a ha G _
  have hsq : jK R' ≫ spMap ρ = spMap a ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ha]
  have hw : (pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R') ≫ pullback.fst G.hom (spMap ρ)) ≫ G.hom =
      (pullback.snd (pullback.snd G.hom (spMap ρ)) (jK R') ≫ spMap a) ≫ jK R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hsq,
      Category.assoc]
  let π₀ : pullback (pullback.snd G.hom (spMap ρ)) (jK R') ⟶ pullback G.hom (jK R) := pullback.lift _ _ hw
  have e₁ : π₀ ≫ pullback.fst G.hom (jK R) =
      pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R') ≫ pullback.fst G.hom (spMap ρ) := pullback.lift_fst _ _ _
  have e₂ : π₀ ≫ pullback.snd G.hom (jK R) = pullback.snd (pullback.snd G.hom (spMap ρ)) (jK R') ≫ spMap a :=
    pullback.lift_snd _ _ _
  refine ⟨π₀, ?_, fun L hL => ?_⟩
  · have n := (isGrpPullback_pullback ((Over.pullback (spMap ρ)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap ρ))
    rw [hsq] at n
    have n' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) G (spMap a ≫ jK R)
        (π₀ ≫ pullback.fst G.hom (jK R)) := by
      rw [e₁]; exact n
    exact IsGrpPullback.cancel (isGrpPullback_pullback G (jK R)) n' e₂
  · have h₁ := GlobalTheory.Spread.lbIso_pull_pull hL (a := pullback.fst G.hom (spMap ρ))
      (pullback.fst (pullback.snd G.hom (spMap ρ)) (jK R')) rfl
    have h₂ := GlobalTheory.Spread.lbIso_pull_pull hL (a := pullback.fst G.hom (jK R)) π₀ e₁.symm
    exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _)
      (LBIso.symm h₁) h₂

end GlobalTheory.GenFibreBaseChange
