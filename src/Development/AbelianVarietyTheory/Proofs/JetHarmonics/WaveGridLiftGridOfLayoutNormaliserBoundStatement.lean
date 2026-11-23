module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WaveGridLiftGridOfLayoutNormaliserBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem _root_.GlobalTheory.T.waveGrid_liftGrid_of_layout_normaliserBound : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (Λ Λ₀ : ℝ) (K N : ℕ), (∀ y, 0 < nn y) → ((∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) ∧ N * (2 * P.r + 1) ≤ Y.card ∧ ∀ y ∈ Y, I.OnCut P.u P.u' p.l0 y ∧ I.OnCut P.u P.u' p.l0 (y + 1)) → (∀ y ∈ Y, nn y * nn (y + 1) ≤ Λ₀ ^ 2 * (M.qC P (y : ℂ)).re) → 0 ≤ Λ → Λ₀ ^ 2 * (5 / 4 : ℝ) ^ N ≤ Λ ^ 2 → TBBx5.WaveGrid p nn Y Λ K N ∧ TBBx5.LiftGrid p nn Y Λ K N := by
  first | exact @GlobalTheory.GridsFromLayout.main | exact GlobalTheory.GridsFromLayout.main | (intros; apply GlobalTheory.GridsFromLayout.main <;> assumption)
