module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymGrpPull

theorem inv_left_comp {S T : Scheme.{0}} (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S)
    (α : B.left ⟶ A.left) (h : IsGrpPullback B A y α) :
    (GrpObj.inv : B ⟶ B).left ≫ α = α ≫ (GrpObj.inv : A ⟶ A).left := by
  have hw : α ≫ A.hom = B.hom ≫ y := h.1.w
  let f : (B ⟶ B) → (Over.mk (B.hom ≫ y) ⟶ A) := fun x =>
    Over.homMk (x.left ≫ α) (by
      change (x.left ≫ α) ≫ A.hom = B.hom ≫ y
      rw [Category.assoc, hw, ← Category.assoc, Over.w x])
  have hmul : ∀ x z : B ⟶ B, f (x * z) = f x * f z := fun x z =>
    Over.OverMorphism.ext (h.2 B x z (f x) (f z) rfl rfl).symm
  have h1 : f 1 = 1 := by
    have e : f 1 * f 1 = f 1 * 1 := by rw [← hmul, _root_.mul_one, _root_.mul_one]
    exact mul_left_cancel e
  have hinv : f (𝟙 B)⁻¹ = (f (𝟙 B))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hmul, _root_.inv_mul_cancel, h1]
  have e := congrArg CommaMorphism.left hinv
  have e' : ((𝟙 B ≫ GrpObj.inv : B ⟶ B)).left ≫ α = (f (𝟙 B) ≫ GrpObj.inv).left := e
  simpa [f] using e'

theorem symm_pull : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S) (α : B.left ⟶ A.left), IsGrpPullback B A y α → ∀ L : LB A.left, L.IsLB → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso ((L.pull α).pull (GrpObj.inv : B ⟶ B).left) (L.pull α) := by
  intro S T A _ B _ y α h L hL hs
  have e := inv_left_comp A B y α h
  have h1 := GenSpread.lbIso_pull_pull hL (a := α) (GrpObj.inv : B ⟶ B).left rfl
  have h2 := GenSpread.lbIso_pull_pull hL (a := (GrpObj.inv : A ⟶ A).left) α e
  have h3 := GenSpread.lbIso_pullback hs α
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB hL _) (LBIso.symm h1)
    (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) h2 h3)

end GlobalTheory.SymGrpPull
