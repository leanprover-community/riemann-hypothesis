module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowRealParameterSuccAllPlusLowestWeights
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gridRowRealParameter_succ_allPlus_lowestWeights : ∀ (D : D7) (j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) (n N : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool) (lam' : Fin N → ℝ) (ε' : Fin N → Bool), Formalism.L2.Theta.IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε → Formalism.L2.Theta.IsEnum (GlobalTheory.Grid.parXp D (j + 1) τ) lam' ε' → ε = Formalism.MainNotions.S.allPos n ∧ ε' = Formalism.MainNotions.S.allPos N ∧ ∃ x₁ x₃ : ℤ, (x₁ : ℚ) = -(D.hc τ).e ⟨j, hj⟩ + (n : ℚ) / 2 ∧ (x₃ : ℚ) = -((N : ℚ) / 2 + -(D.hc τ).e ⟨j, hj⟩) ∧ ∃ (hn : n ≤ N) (ν : Fin N → ℕ), Antitone ν ∧ (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) lam a = -(x₃ : ℝ) + ν (Fin.castLE hn a)) ∧ ∀ b, Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos N) lam' b = (x₁ : ℝ) + ν b := by
  first | exact @GlobalTheory.ColParam.colPar | exact GlobalTheory.ColParam.colPar | (intros; apply GlobalTheory.ColParam.colPar <;> assumption)
