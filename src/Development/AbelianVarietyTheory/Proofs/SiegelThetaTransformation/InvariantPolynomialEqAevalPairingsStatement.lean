module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolynomialEqAevalPairings
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel

@[expose] public section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.exists_aeval_pairings_eq_of_invariant : ∀ (T : Type) [Fintype T] [DecidableEq T] (n N : ℕ), N ≤ n → ∀ p : MvPolynomial (T × Bool × Fin n × Fin N) ℂ, (∀ u : T → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ z : T × Bool × Fin n × Fin N → ℂ, MvPolynomial.eval (fun v => ∑ l, (if v.2.1 then u v.1 v.2.2.1 l else conj (u v.1 v.2.2.1 l)) * z (v.1, v.2.1, l, v.2.2.2)) p = MvPolynomial.eval z p) → ∃ s : MvPolynomial (T × Fin N × Fin N) ℂ, p = MvPolynomial.aeval (fun v : T × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (T × Bool × Fin n × Fin N) ℂ)) s := by
  first | exact @GlobalTheory.invariant_polynomial_eq_aeval_pairings | exact GlobalTheory.invariant_polynomial_eq_aeval_pairings | (intros; apply GlobalTheory.invariant_polynomial_eq_aeval_pairings <;> assumption)
