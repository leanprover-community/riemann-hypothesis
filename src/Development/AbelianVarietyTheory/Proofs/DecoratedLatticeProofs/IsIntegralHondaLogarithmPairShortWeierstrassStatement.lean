module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIntegralHondaLogarithmPairShortWeierstrass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open PowerSeries GlobalTheory.Honda

theorem _root_.GlobalTheory.T.isIntegralHondaLogarithmPair_shortWeierstrass : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 : K), ‖(2 : K)‖ = 1 → ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → IntLog (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3)) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW g2 g3)) := by
  first | exact @GlobalTheory.Honda.intLog_shortW | exact GlobalTheory.Honda.intLog_shortW | (intros; apply GlobalTheory.Honda.intLog_shortW <;> assumption)
