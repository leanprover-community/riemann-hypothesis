module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidCubicalExtensionPullbackOfToricChart
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.rigidCubicalExtension_pullback_of_toricChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k] {m n : ℕ} (tC : SAB H (Sp (ChartRing k m n))) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp (ChartRing k m n) ⟶ S) (πC : tC.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tC.G G ξ πC → ∀ (PP : RigLB G) (cub : CubicalStr G PP) {X' : Scheme.{0}} (tF : SAB H X') (j : X' ⟶ S) (e : tF.G.left ⟶ G.left) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → ∀ (y : Sp (FractionRing (ChartRing k m n)) ⟶ X'), y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK tC (jK _)) (b : SABMap tK tF y), a.φ ≫ πC = b.φ ≫ e → ∃ cm' : CubeMap tC.G G, cm'.F = πC ∧ cm'.e = ξ ∧ cm'.IsPullCubical tC.cub cub := by
  first | exact @GlobalTheory.ChartCubExt.cube_pull_of_chart | exact GlobalTheory.ChartCubExt.cube_pull_of_chart | (intros; apply GlobalTheory.ChartCubExt.cube_pull_of_chart <;> assumption)
