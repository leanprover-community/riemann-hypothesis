module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationPullbackLocalHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.linearUniformisation_pullback_localHom : ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (θ : R →+* V), Base R → Base V → IsLocalHom θ → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → spMap θ (genericPoint (Sp V)) ∈ W → ∃ (D₁ : DegData V (maximalIdeal V)) (hD : IsPullDeg θ D.toPre D₁.toPre) (A₁ : PolAV (Sp (FractionRing V))) (U₁ : Unif (maximalIdeal V) D₁ A₁ ((Over.pullback (specOf θ)).obj G)) (_ : Module O D₁.toPre.X) (o₁ : D₁.toPre.OAct O) (oA₁ : A₁.OAct O) (oG₁ : RingAct ((Over.pullback (specOf θ)).obj G) O), LBIso U₁.LG.L (U.LG.L.pull (pullback.fst G.hom (specOf θ))) ∧ (∀ (a : O) (y : D₁.toPre.X), hD.xe (a • y) = a • hD.xe y) ∧ (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (o.onB.act a).left) ∧ (∀ a, oG₁.act a = (Over.pullback (specOf θ)).map (oG.act a)) ∧ U₁.toUnifPre.OLinear O o₁ oA₁ oG₁ := by
  first | exact @GlobalTheory.Mum.ulin_pull | exact GlobalTheory.Mum.ulin_pull | (intros; apply GlobalTheory.Mum.ulin_pull <;> assumption)
