module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKSubgroupTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem kTriv_of_lamEq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L L' : LB A.left), L.IsLB → L'.IsLB → LamEq L' (𝟙 A) (𝟙 A) L (𝟙 A) (𝟙 A) → Out.KTriv A L → Out.KTriv A L' := by
  intro S A _ _ L L' hL hL' h hK R _ t x hx
  have hu : ∃ u : LB.Gen (abelian₂ A (LB.div L L')), u.IsGen := by
    simp only [LamEq, Category.comp_id] at h
    obtain ⟨w, hw⟩ := h
    exact gen_chartPull (GlobalTheory.DescendedPrincipal.chartPullDiv L L' _ _) w hw
  exact hK R t x ((GlobalTheory.UU.KTwist.inK_div_iff (x := x) hL hL' hx).1 (GlobalTheory.UU.KTwist.inK_of_lam (LB.isLB_div hL hL') hu x))

end GlobalTheory.CM
