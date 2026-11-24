module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRationalPointOrbitAlgebraicWeight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.span_rationalPoint_orbit_algebraicWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → ∀ v : ι → ℂ, v ≠ 0 → ∀ w : ι → ℂ, w ∈ Submodule.span ℂ {x | ∃ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n ∧ x = evM P (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) *ᵥ v} := by
  first | exact @GlobalTheory.AlgWtHW.span_ratPt_orbit | exact GlobalTheory.AlgWtHW.span_ratPt_orbit | (intros; apply GlobalTheory.AlgWtHW.span_ratPt_orbit <;> assumption)
