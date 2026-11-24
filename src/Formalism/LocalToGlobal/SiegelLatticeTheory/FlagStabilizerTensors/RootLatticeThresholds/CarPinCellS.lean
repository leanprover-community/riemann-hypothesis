module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinAt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotMeas
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

open Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPf

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ)

def HaarTr (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ)) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ)
      μRv →
    IsHaarOn (RStab D.R.k D.R.rS (gB C τ γ)) (muRB C τ μRv)

def QuotTr (u u' : D.what₂.Word) (τ : D.what₂.Tau) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ)) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ)
      μRv →
    IsQuotLoc μRv ν →
    PI.BesselPeriodGGP.IsQuotMeas (locW C u u' τ).μG
      ((muRB C τ μRv).map (fun x i j => ((gB C τ γ)⁻¹ * Matrix.of x * gB C τ γ) i j))
      (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ))

def PinHypAt (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) : Prop :=
  0 < Gv (Tw (D := D) u) (Tw (D := D) u') (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ)) ∧
  Formalism.FourierDecayAlt.C2.IsMonomial (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ)) ∧
  Formalism.FourierDecayAlt.C6.IsRelevant (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ))
    (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ) ∧
  IsHaarLoc (StSet (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u (vOf X τ)) (Formalism.L2.SG.Pf.Carrier.JointQuot.NV X u' (vOf X τ)) γ)
    μRv ∧ IsQuotLoc μRv ν

def CutAt (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) : Prop :=
  ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))),
    PinHypAt C u u' τ γ μRv ν →
    ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ))
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ)
        (μRv.map (fun x => Matrix.of.symm (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ))
          (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) x))) θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ))
        (trG (Formalism.L2.SG.Pf.BaseOf.Qc X C (vOf X τ)) (Formalism.L2.SG.Pf.BaseOf.Qic X C (vOf X τ)) γ)
        (fcAt C u u' τ a b ξ ξ' c) p) (Formalism.L2.SG.Pf.BaseOf.baseOf X C u u' (vOf X τ)).μSS

end Formalism.L2.SG.Pf.Carrier.CarPinTor
