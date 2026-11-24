module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoCubeMulDerivWeierstrassPNegTwo
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
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsLineOfAddAddEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.tendsto_cube_mul_derivWeierstrassP_neg_two : ∀ (L : PeriodPair), Filter.Tendsto (fun z : ℂ => z ^ 3 * L.derivWeierstrassP z) (𝓝[≠] 0) (𝓝 (-2)) := by
  first | exact @GlobalTheory.CMModel.tendsto_cube_mul_derivWeierstrassP | exact GlobalTheory.CMModel.tendsto_cube_mul_derivWeierstrassP | (intros; apply GlobalTheory.CMModel.tendsto_cube_mul_derivWeierstrassP <;> assumption)
