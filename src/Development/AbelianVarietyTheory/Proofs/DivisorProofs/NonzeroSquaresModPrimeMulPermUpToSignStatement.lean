module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroSquaresModPrimeMulPermUpToSign
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.nonzeroSquaresModPrime_mul_perm_up_to_sign : ∀ (p c : ℕ), p.Prime → p % 4 = 3 → ¬ p ∣ c → ∃ (e : Sq p ≃ Sq p) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ ∀ k : Sq p, (p : ℤ) ∣ (((k.1 : ℕ) : ℤ) * c - ε * (((e k).1 : ℕ) : ℤ)) := by
  first | exact @GlobalTheory.CMModel.sq_perm_mul | exact GlobalTheory.CMModel.sq_perm_mul | (intros; apply GlobalTheory.CMModel.sq_perm_mul <;> assumption)
