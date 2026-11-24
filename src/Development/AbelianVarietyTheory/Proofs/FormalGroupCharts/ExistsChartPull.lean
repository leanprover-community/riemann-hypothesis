module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemPowSubMemPowSucc
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.BidegreeTwoJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.BoxTuple
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LemmaBStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.DepthExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem grp_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 _) (𝟙 _) :=
  ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun _ x y x₀ y₀ hx hy =>
    (mul_left_congr (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
      (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm⟩

section Tangent
variable {V V' : Type} [CommRing V] [CommRing V']

theorem comb_iff (t : SAB H (Sp V)) {m : ℕ} (v : Fin m → (epsR V ⟶ t.G)) (cf : Fin m → V) (w : epsR V ⟶ t.G) :
    IsLieComb cf v w ↔ IsCombAtG t (𝟙 _) (fun i => (v i).left) cf w.left := by
  simp only [Chart.comb_push (grp_id t.G), Category.comp_id]
  exact Iff.rfl

theorem tan_iff (t : SAB H (Sp V)) (w : epsR V ⟶ t.G) : IsTangent w ↔ IsTanAtG t (𝟙 _) w.left := by
  simp only [Chart.tan_push (grp_id t.G), Category.comp_id]
  exact ⟨fun h => ⟨(Over.w w).trans (Category.comp_id _).symm, h⟩, fun h => h.2⟩

variable (ψ : V →+* V') {t : SAB H (Sp V)} {t' : SAB H (Sp V')} (mp : SABMap t' t (spMap ψ))

end Tangent

end GlobalTheory.DepthExt
