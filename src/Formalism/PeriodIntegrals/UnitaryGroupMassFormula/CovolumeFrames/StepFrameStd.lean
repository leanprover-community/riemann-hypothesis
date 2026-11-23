module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepGramH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NilpotentVolumeOne.LinearIndependentFrameWithNormal
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

noncomputable section

namespace MassDataVolumesW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

def StepFrameStd : Prop := ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
  ∃ T : X.B.I.F, (frameOf X u).IsStd X.B.I.cm.sig X.B.I.J T

theorem stepGramH_of (h : StepFrameStd) : StepGramH := by
  unfold StepGramH
  intro D X u hT1
  obtain ⟨T, hT⟩ := h X u
  exact PI.VolNzeroOne.W.det_gram_tupH_ne_zero X.B.I.cm.sig X.B.I.J (frameOf X u) T hT hT1

end MassDataVolumesW
