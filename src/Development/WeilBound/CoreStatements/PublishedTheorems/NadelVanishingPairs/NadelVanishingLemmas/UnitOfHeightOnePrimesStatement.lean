module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.RingHom.Etale
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.UnitOfHeightOnePrimes
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.unit_of_height_one_primes : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (J : Finset (Fin n)) (ht : ∀ j, algebraMap A L (t j) ≠ 0) (g : Lˣ), (∀ Q : Ideal A, Q.IsPrime → Q ≤ P → (∀ j ∈ J, t j ∉ Q) → ∃ a b : A, a ∉ Q ∧ b ∉ Q ∧ (g : L) * algebraMap A L b = algebraMap A L a) ↔ ∃ (u : Lˣ) (m : Fin n → ℤ), (∃ a b : A, a ∉ P ∧ b ∉ P ∧ (u : L) * algebraMap A L b = algebraMap A L a) ∧ g = u * ∏ j ∈ J, Units.mk0 _ (ht j) ^ m j := by
  first | exact @_root_.GlobalTheory.EtUnit.unit_mul_monomial_iff | exact _root_.GlobalTheory.EtUnit.unit_mul_monomial_iff | (intros; apply _root_.GlobalTheory.EtUnit.unit_mul_monomial_iff <;> assumption)
