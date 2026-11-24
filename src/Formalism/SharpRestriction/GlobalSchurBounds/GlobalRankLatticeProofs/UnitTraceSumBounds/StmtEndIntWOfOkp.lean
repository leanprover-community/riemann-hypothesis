module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EndIntWOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfRing
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WfSubst
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittFrobeniusEnd
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.MainNotions.Ext

theorem substWf_holds : SubstWf :=
  fun p _ σ f a hf ha h0 => witt_substitution p σ f a hf (fun n => ⟨0, by rw [pow_zero, one_mul]; exact ha n⟩) h0

theorem coefWfRing_holds : CoefWfRing := witt_ring_structure

theorem endIntWG_holds : EndIntWG :=
  fun p _ g hOk hW α hα hI =>
    witt_frobenius_end p g.W g.wq g.ex hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2 hOk.2.1 hOk.2.2.1 hOk.2.2.2 α.1
      ⟨0, by simpa using witt_pairing p α hα⟩ hI

end Formalism.MainNotions.Ext
