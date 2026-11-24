module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdAwayOfIsUnitMod
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
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isExcisionNbhd_away_of_isUnit_mod' : ∀ (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B), IsExcisionNbhd B A' f → IsUnit (Ideal.Quotient.mk (Ideal.span {f}) s) → IsExcisionNbhd B (Localization.Away (algebraMap B A' s)) f := by
  first | (exact @GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod) | (exact GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod) | (intros; apply GlobalTheory.EtC.isExcisionNbhd_away_of_isUnit_mod  <;> assumption)
