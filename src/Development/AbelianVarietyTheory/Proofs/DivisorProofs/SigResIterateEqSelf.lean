module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicTensorUnramifiedFrobTwistIterateDegreeStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes

namespace GlobalTheory.LKRes

theorem sigRes_iterate_val (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (n r k : ℕ) (g : GL (Fin n) (KQ p K r)) (i j : Fin n) :
    (((⇑(sigRes p K n r))^[k] g : GL (Fin n) (KQ p K r)) : Matrix (Fin n) (Fin n) (KQ p K r)) i j =
      (⇑(sigKQ p K r))^[k] ((g : Matrix (Fin n) (Fin n) (KQ p K r)) i j) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

theorem sigRes_iterate_eq_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ), 0 < r → ∀ g : GL (Fin n) (KQ p K r), (⇑(sigRes p K n r))^[r] g = g := by
  intro p _ K n r hr g
  apply Units.ext
  ext i j
  rw [sigRes_iterate_val]
  exact GlobalTheory.T.padicTensorUnramifiedFrobTwist_iterate_degree p K r hr _

end GlobalTheory.LKRes
