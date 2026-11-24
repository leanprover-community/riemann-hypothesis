module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedLvalueNeZeroEdge
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.odd_chi_and_tendsto_twisted_LSeries_ne_zero_of_prim : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) (w : ℝ), Odd k → 0 < N → 0 < M → Prim k N χ g → ((k : ℝ) + 1) / 2 ≤ w → χ (-1) = -1 ∧ ∃ v : ℂ, v ≠ 0 ∧ Tendsto (fun s : ℝ => LSeries (fun n => φ n * g n) ((w + s : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 v) := by
  first | exact @GlobalTheory.EisM.twisted_lvalue_ne_zero_edge | exact GlobalTheory.EisM.twisted_lvalue_ne_zero_edge | (intros; apply GlobalTheory.EisM.twisted_lvalue_ne_zero_edge <;> assumption)
