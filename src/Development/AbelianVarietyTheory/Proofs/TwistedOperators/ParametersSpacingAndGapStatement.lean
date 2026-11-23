module

public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParametersSpacingAndGap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.L2.Theta

theorem _root_.GlobalTheory.T.parameters_spacing_and_gap : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool} {H : ℝ}, 2 ≤ H → H ≤ G.ga → (∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) → 2 ≤ G.v G.k + G.b 1 → (∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + H ≤ G.b (l + 1)) → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → (∀ a c, a < c → 2 ≤ lam a - lam c) ∧ (∀ a c, a < c → 2 ≤ mu a - mu c) ∧ Formalism.QuantumDeterminants.GapAtLeast ε lam H ∧ Formalism.QuantumDeterminants.GapAtLeast ε' mu H := by
  first | exact @GlobalTheory.SignedHC.GridData.pi_zero_and_D0_spacing | exact GlobalTheory.SignedHC.GridData.pi_zero_and_D0_spacing | (intros; apply GlobalTheory.SignedHC.GridData.pi_zero_and_D0_spacing <;> assumption)
