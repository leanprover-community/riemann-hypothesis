module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsAbelianSchemePullbackUniversalTriple
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGPassesToPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGUniqueOnAbelianStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem chartPrimTr_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartPrimTrSt Xo c := by
  intro E _ _ _ H Dw l Xo c T io y I wPT hT
  obtain ⟨wP, hP⟩ := GermB.exists_wP Xo.univ.t
  obtain ⟨w₁, hw₁, h₁⟩ := GlobalTheory.T.primitiveIsoG_passes_to_pullback E H _ _ _ _ _ I.m1 I.w1 I.rig1 wP hP
  obtain ⟨w₂, hw₂, h₂⟩ := GlobalTheory.T.primitiveIsoG_passes_to_pullback E H _ _ _ _ _ I.m2 I.w2 I.rig2 wPT hT
  have hab := GlobalTheory.isAbelianScheme_of_pullback_univ E H Dw l Xo _ _ _ I.m1
  have e : w₁ = w₂ := GlobalTheory.T.primitiveIsoG_unique_on_abelian GlobalTheory.firstFiveLaws.1.globalFns E H _ I.t' hab w₁ w₂ hw₁ hw₂
  subst e
  exact ⟨wP, (isPrim_iff wP).2 hP, w₁, hw₁.1, h₂, h₁⟩

end GlobalTheory
