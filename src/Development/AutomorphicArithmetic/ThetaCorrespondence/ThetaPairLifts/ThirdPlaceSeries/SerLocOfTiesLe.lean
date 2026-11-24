module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocComp
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
public import Development.DiscreteGroups.GlobalIrreducibility.IneEqOfHasGreenLe
public import Development.DiscreteGroups.GlobalIrreducibility.LocTypeOfSerParamLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootsBarEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocTypeOfSerParamLe
public import Development.DiscreteGroups.GlobalIrreducibility.SerLocOfTiesLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.TypeLeaf GlobalTheory.SerSys GlobalTheory.SerSys.Bridge
open scoped Classical
attribute [local instance] GlobalTheory.SerSys.Bridge.factT
theorem serLocLe_of_alt (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (hL : LabTie D L) (hU : IneUnr D) (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc) (hP : LabParamLe D.R.nV D L rc) : SerLoc D :=
  have hS : ∀ k, (OfLabel.ofLabel (L k) (five_le D k) hG).IsOf (L k) := fun _ _ _ => rfl
  GlobalTheory.SerLocal.serLoc D _ (hL.sysTie hS) hU (_root_.DiscreteGroups.sglob.DzType.Rt.locType_of_labTie_locComp_labParamLe hL hS hC hP)
theorem serLoc_of_tame_param_le (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (hL : LabTie D L) (hU : IneUnr D) (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc)
    (h1 : ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2))
    (h2 : ∀ k, TameGen.DepthZeroCuspidal (D.host.g k))
    (h3 : ∀ k v, TameParamLe D.R.nV (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2)) : SerLoc D :=
  _root_.DiscreteGroups.sglob.DzType.Rt.serLocLe_of_alt D L rc hG hL hU hC (labParamLe_of D L rc hG h1 h2 h3)
end DiscreteGroups.sglob.DzType.Rt
end
end
