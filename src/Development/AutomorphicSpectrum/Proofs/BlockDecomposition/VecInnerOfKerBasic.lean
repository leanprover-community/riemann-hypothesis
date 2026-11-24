module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.E1

theorem vecInner_of_kerBasic : KerBasic → VecInner := by
  intro hK X ι _ Φ y j k u hΦ
  constructor
  · intro hk
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hk l] with z hz
    rw [hz, RCLike.inner_apply, mul_comm]
  · intro hk
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hk l] with z hz
    have h := (hK X (Φ j l) (hΦ j l)).2.2.2.2.1 z y
    rw [hz, h, RCLike.inner_apply, Complex.conj_conj, mul_comm]

end GlobalTheory.CompanionTheory.E1

end
