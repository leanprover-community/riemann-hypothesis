module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBP
public import Formalism.PeriodIntegrals.CapelliEig
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesCoefficientExpansionBoundBall
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
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup

@[expose] public section

open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.discreteSeries_coefficient_expansion_bound_ball' : ∀ (C : ℝ), 0 ≤ C → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (a₁ : ℕ) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ) (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), Num P.k P.r lam P.u b bv ga h q0 → Num P.k P.r lam P.u' b bv ga h q0 → P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) → P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) → n1 ν₀ + (P.r + 1) * a₁ + (P.r + 1) * (P.r + 2) ≤ q0 → R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) → PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R0.σ f → Formalism.FourierDecayAlt.P.CutBP.BigCellDerivativeExpansion p f b (C / 2 + 6) a₁ := by
  first | exact @GlobalTheory.discreteSeries_coefficient_expansion_bound_ball | exact GlobalTheory.discreteSeries_coefficient_expansion_bound_ball | (intros; apply GlobalTheory.discreteSeries_coefficient_expansion_bound_ball <;> assumption)
