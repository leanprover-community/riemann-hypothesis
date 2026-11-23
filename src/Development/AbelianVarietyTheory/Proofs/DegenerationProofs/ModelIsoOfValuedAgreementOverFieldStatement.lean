module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelIsoOfValuedAgreementOverField
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.modelIso_of_valued_agreement_over_field : GlobalTheory.UT.LL → AllS fun {_} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {C} _ _ A u _ {_} M f {_} ν' J => ∀ u₀ : M.W, (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → ∀ ψ (he : eSec M.P.D.toPre.P.A ≫ ψ = spMap f ≫ eSec a.D₀.P.A) w e, Fit A u M f ν' J ψ w e → LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec M.P.D.toPre.P.A) (fun _ => 1)) M.P.D.toPre.rig (rigPullOf ψ (spMap f) he a.D₀.P.L a.D₀.rig) → (letI := H.starRing; ∀ x, (M.P.oD.onB.act x).left ≫ ψ = ψ ≫ (a.oa.onB.act x).left) → GlobalTheory.LN.Match a f u₀ M.P.D.toPre M.P.oD ψ he w e := by
  first | exact @GlobalTheory.FitMatch.match_of_fit | exact GlobalTheory.FitMatch.match_of_fit | (intros; apply GlobalTheory.FitMatch.match_of_fit <;> assumption)
