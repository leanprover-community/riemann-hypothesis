module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutER
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliUnderIntegral
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.ER

theorem coefficient_vector_commutation : CVComm := by
  intro k r Wp Wq _ _ _ _ _ _ s Y Y' F hF g hg
  have hs : ∀ (Z α : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)),
      Q.CV k r Z (α • f) = α • Q.CV k r Z f := fun Z => P5.tL_smulC 0 0 0 Z 0 0
  have hsm : Q.SmoothLev k r 0 Set.univ F := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hc, he⟩ := hF g₀ ((CapelliUnderIntegral.glev0 g₀).1 hg₀.1)
    exact ⟨U, f', hU, hgU, hc, fun x hx hxl => he x hx ((CapelliUnderIntegral.glev0 x).1 hxl)⟩
  have hc := capelli_commutation _ k r 0 Set.univ F isOpen_univ hsm g
    ⟨(CapelliUnderIntegral.glev0 g).2 hg, trivial⟩ (Q.uC k r 0 Y) (Q.uC k r 0 Y')
  simp only [Pi.smul_apply, hs]
  exact congrArg (fun t => s • s • t) hc

end Formalism.FourierDecayAlt.P.CutMP.ER
