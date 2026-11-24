module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CFxi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationFactorPairingIsoPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfTwistedAdjointCompStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingInvolutionActionGivesPolarisedAdjointPairStatement
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.FactorAdj

theorem factor_adj : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) (F : Factor D.toPre D'.toPre), Adj (pol D') (pol D) F.pr (F.inc ≫ F.o.onB.act (Star.star F.e * F.f)) F.xp ((DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi) := by
  intro R _ _ I D D' F
  haveI := F.inc_hom
  haveI := F.o.onB.hom F.f
  have hm : IsMonHom (F.inc ≫ F.o.onB.act F.f) := inferInstance
  have H := GlobalTheory.T.of_twisted_adjoint_comp R (pol D') (pol D) F.pr (F.o.onB.act F.e) (F.o.onB.act (Star.star F.e))
    (F.inc ≫ F.o.onB.act F.f) F.xp
    (DistribSMul.toAddMonoidHom D'.toPre.X F.e) (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e))
    ((DistribSMul.toAddMonoidHom D'.toPre.X F.f).comp F.xi) F.pr_hom hm
    (fun y => c_xp F y) (fun z => c_fxi F z) (GlobalTheory.T.ringInvolutionAction_gives_polarisedAdjointPair R I D' F.O F.o F.e) (GlobalTheory.T.exists_degenerationFactor_pairing_iso_pullback R I D D' F)
  have e1 : (F.inc ≫ F.o.onB.act F.f) ≫ F.o.onB.act (Star.star F.e) = F.inc ≫ F.o.onB.act (Star.star F.e * F.f) := by
    rw [F.o.onB.map_mul, Category.assoc]
  have e2 : (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e)).comp
      ((DistribSMul.toAddMonoidHom D'.toPre.X F.f).comp F.xi) =
      (DistribSMul.toAddMonoidHom D'.toPre.X (Star.star F.e * F.f)).comp F.xi := by
    ext y
    simp [mul_smul]
  exact e1 ▸ e2 ▸ H

end GlobalTheory.MumFam.FactorAdj
