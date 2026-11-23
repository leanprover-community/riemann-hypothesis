module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullDegKeepsBimultActionPolarisationElement
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.pullDeg_keeps_bimult_action_polarisationElement : ∀ {O : Type} [CommRing O] [StarRing O] {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] {θ₀ : W →+* V} {D₀ : DegPre W} [Module O D₀.X] (o₀ : D₀.OAct O) {D : DegPre V} [Module O D.X] (hD : IsPullDeg θ₀ D₀ D) (ob : D.P.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) → (∀ (a : O) y, D.c (a • y) = D.c y ≫ ob.act a) → (∀ a : O, (ob.act a).left ≫ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = (hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀)) ≫ (o₀.onB.act a).left) → D₀.TauBimult → ∀ w0 : O, TraceFormTwistIso D₀ o₀ w0 → D.TauBimult ∧ ∃ o : D.OAct O, o.onB = ob ∧ TraceFormTwistIso D o w0 := by
  first | exact @GlobalTheory.tauBimult_and_exists_oAct_of_pullDeg | exact GlobalTheory.tauBimult_and_exists_oAct_of_pullDeg | (intros; apply GlobalTheory.tauBimult_and_exists_oAct_of_pullDeg <;> assumption)
