module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPlace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepRealHolds
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.Carrier.EnergyFinal

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
  Formalism.L2.SG.Pf.Carrier.EnergyPlace Formalism.L2.SG.AdBridge Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}

def PlaceNormG (P : Parts X u u') (hr : P.S.G.r = D.R.rS) : Prop :=
  ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
    Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g) = Matrix.diagonal cv →
    hs2 (JvX X u u' v g) =
      ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
        (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base (phiQ P hr cv)))‖ ^ 2

theorem placeNorm_of_G (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hG : PlaceNormG P hr)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) (hL : LocRep X u u' L) : PlaceNorm P hr L := by
  intro v cv hcv
  let c : Cinf X := fun _ => cv
  have hc : c ∈ Good X u u' := fun _ => hcv
  obtain ⟨γ, hγ⟩ := InfCut.ProductExactness.StepReal_holds D X u u' 1 one_pos c hc
  have hex : ∃ γ, HasDiag X u u' 1 c γ := ⟨γ, hγ⟩
  have hd : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
    unfold hOf
    rw [dite_eq_left hex]
    exact hex.choose_spec
  have h1 : hs2 (JvX X u u' v ((hOf X u u' 1 c) v)) = L v cv := hL.2 c hc v
  have h2 := hG v ((hOf X u u' 1 c) v) cv hcv (hd v)
  exact h1.symm.trans h2

end Formalism.L2.SG.Pf.Carrier.EnergyFinal
