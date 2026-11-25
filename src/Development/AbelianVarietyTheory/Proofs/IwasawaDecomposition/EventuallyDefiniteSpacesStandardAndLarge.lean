module

public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotVstdOfGramOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSpacesOfOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RecAtOfTwoPasses
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.StdSize

theorem vstd_size_ev : Top.Ev fun K => ∀ X : Stages, K.Over X.B.toPre →
    (∀ i, Formalism.IndefR.FWT.VStd X.toD7 i) ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV := by
  refine GlobalTheory.Mem.Top.V4.TwoPass.ev_mono ?_ GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  intro K hK X hX
  obtain ⟨-, -, -, -, -, -, hVf, -⟩ := hK X hX
  obtain ⟨hR, -⟩ := GlobalTheory.Mem.HostFrames.val_of_over hX
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hVf i
    rw [GlobalTheory.StdFrameCounterexample.vstd_iff]
    refine ⟨Matrix.ext fun a b => ?_, fun x => ?_⟩
    · rw [HSpace.gram, h1, Matrix.one_apply]
    · rw [h2, Module.Basis.mem_span_iff_repr_mem, Module.Basis.repr_sum_self]
      refine forall_congr' fun a => ?_
      constructor
      · rintro ⟨y, hy⟩
        rw [← hy]; exact y.2
      · intro h
        exact ⟨⟨x a, h⟩, rfl⟩
  · have h4 := hR.2.2.2
    show 8 * X.B.R.f * X.B.R.r + 4 ≤ X.B.R.r + X.B.R.t
    omega

end GlobalTheory.Mem.StdSize
