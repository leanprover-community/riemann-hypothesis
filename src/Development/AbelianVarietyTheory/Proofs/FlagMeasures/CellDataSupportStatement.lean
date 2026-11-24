module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellDataSupport
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

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.cell_data_support : Hyps → ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.κN ≠ ⊤ → CellData L μG γ μR νR ν → (∀ᵐ p ∂ν, Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) ∧ ∀ b : ℝ, 0 ≤ b → b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 → Integrable (pairMaj γ b) ν → ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' → ∀ (ξ : L.Wp) (ξ' : L.Wq), Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
  first | exact @GlobalTheory.CellOrbInt.orbInt_integrable | exact GlobalTheory.CellOrbInt.orbInt_integrable | (intros; apply GlobalTheory.CellOrbInt.orbInt_integrable <;> assumption)
