module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitConjOfMinpolyEq
public import GroundTheory.Brauer.SkolemNoether
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem units_conj_of_minpoly_eq_of_irreducible : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (a b : G.Cˣ),
    minpoly G.F (a : G.C) = minpoly G.F (b : G.C) → Irreducible (minpoly G.F (b : G.C)) →
      ∃ g : G.Cˣ, (a : G.C) = g * b * ↑g⁻¹ := by
  intro p _ G a b h hirr
  have hb : IsIntegral G.F (b : G.C) := IsIntegral.of_finite G.F _
  haveI : Fact (Irreducible (minpoly G.F (b : G.C))) := ⟨hirr⟩
  haveI : FiniteDimensional G.F (AdjoinRoot (minpoly G.F (b : G.C))) :=
    (AdjoinRoot.powerBasis (minpoly.ne_zero hb)).finite
  have ha : Polynomial.aeval (a : G.C) (minpoly G.F (b : G.C)) = 0 := by rw [← h]; exact minpoly.aeval _ _
  obtain ⟨y, hy⟩ := GroundTheory.Brauer.exists_unit_conj (evalQuot _ (b : G.C) (minpoly.aeval _ _))
    (evalQuot _ (a : G.C) ha)
  refine ⟨y, ?_⟩
  have := hy (AdjoinRoot.root _)
  rwa [evalQuot_root, evalQuot_root] at this

end GlobalTheory.LKCx
