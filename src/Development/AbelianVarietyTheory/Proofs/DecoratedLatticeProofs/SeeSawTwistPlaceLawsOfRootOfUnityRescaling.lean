module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombSmulLeft
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFiniteCellsAtTwistPlacesOfLocalFactorisatiStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegralLawAtTwistOfFactorisationStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegralLawLastStepsOfLocalFactoriStatement
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw

theorem laws_of_pin_resc : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPinU v w → QLaw v w ∧ QLast v w ∧ QFin v w :=
  fun D c v t w hc ht hv hW h =>
    GlobalTheory.QTw.RescTest.laws_of_qpinU v (fun w₀ h₀ =>
      ⟨GlobalTheory.T.seeSawIteratedIntegralLaw_at_twist_of_factorisation D c v t w₀ hc ht hv hW h₀, GlobalTheory.T.seeSawIteratedIntegralLawLastSteps_of_localFactorisation D c v t w₀ hc ht hv hW h₀, GlobalTheory.T.seeSawFiniteCells_at_twistPlaces_of_localFactorisation D c v t w₀ hc ht hv hW h₀⟩) w h

end GlobalTheory.QTw
