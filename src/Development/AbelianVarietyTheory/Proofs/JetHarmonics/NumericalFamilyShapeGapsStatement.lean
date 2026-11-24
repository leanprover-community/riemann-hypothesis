module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
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

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.numericalFamily_shape_gaps : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → (bv ≤ b ∧ (1000000 : ℝ) ≤ bv ∧ ((2 * r + k + 1) : ℝ) ≤ b ∧ 100 * (q0 : ℝ) ≤ bv ∧ GapOK k r (h / 2)) ∧ ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → Formalism.QuantumDeterminants.IsHCParam (fun a => lam a + (ν a : ℝ)) ∧ Shape (PI.BesselPeriodGGP.eps48 k r) k (fun a => lam a + (ν a : ℝ)) bv ∧ Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (h / 2) ∧ ∀ a c, a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
  first | exact @GlobalTheory.NumFam.num_fam | exact GlobalTheory.NumFam.num_fam | (intros; apply GlobalTheory.NumFam.num_fam <;> assumption)
