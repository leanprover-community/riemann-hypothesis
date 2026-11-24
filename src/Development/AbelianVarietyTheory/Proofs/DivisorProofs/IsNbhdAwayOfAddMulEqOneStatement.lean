module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNbhdAwayOfAddMulEqOne
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

open GlobalTheory.AffineCurveNbhd

theorem _root_.GlobalTheory.T.isNbhd_away_of_add_algebraMap_mul_eq_one : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f : B) (h c : A'), IsNbhd B A' f → h + algebraMap B A' f * c = 1 → IsNbhd B (Localization.Away h) f := by
  first | (exact @GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one) | (exact GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one) | (intros; apply GlobalTheory.AffineCurveNbhd.isNbhd_away_of_add_mul_eq_one <;> assumption)
