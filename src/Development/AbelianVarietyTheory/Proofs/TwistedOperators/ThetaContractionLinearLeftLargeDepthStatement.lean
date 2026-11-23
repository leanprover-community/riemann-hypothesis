module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumEqZeroOfMultilin
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaContractionLinearLeftLargeDepth
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

@[expose] public section

open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear

theorem _root_.GlobalTheory.T.thetaContraction_linear_left_largeDepth : Big fun ch => GlobalTheory.ConnectionLinear.ContrLin ch 0 := by
  first | exact @GlobalTheory.ConnectionLinear.contrLin_left | exact GlobalTheory.ConnectionLinear.contrLin_left | (intros; apply GlobalTheory.ConnectionLinear.contrLin_left <;> assumption)
