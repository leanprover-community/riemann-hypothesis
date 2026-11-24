module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassPTwoMulMulSq
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
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.weierstrassP_two_mul_mul_deriv_sq : ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → 2 * z ∉ L.lattice → L.weierstrassP (2 * z) * L.derivWeierstrassP z ^ 2 = (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) ^ 2 / 4 - 2 * L.weierstrassP z * L.derivWeierstrassP z ^ 2 := by
  first | exact @GlobalTheory.weierstrassP_two_mul_mul_sq | exact GlobalTheory.weierstrassP_two_mul_mul_sq | (intros; apply GlobalTheory.weierstrassP_two_mul_mul_sq <;> assumption)
