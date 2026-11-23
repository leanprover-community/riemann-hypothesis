module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBP
public import Formalism.PeriodIntegrals.CapelliEig
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.WaveBallEstimateWeightedDualAlt
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.WaveInputsOfHypothesesGlobal
public import CompanionTheory.AutomorphicTheory.PieriRules.InfinitesimalCharacterDiscreteSeries
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.BigCellDerivativeExpansionOfIsDSOfCoefOf
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup

@[expose] public section

open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem discreteSeries_coefficient_expansion_bound_ball : ∀ (C : ℝ), 0 ≤ C → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (a₁ : ℕ) (ν₀ : Fin (2 * P.r + P.k + 1) → ℤ) (R0 : Rep P.k P.r) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), Num P.k P.r lam P.u b bv ga h q0 → Num P.k P.r lam P.u' b bv ga h q0 → P.T ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) → P.T' ≤ b ^ (C * ((2 * P.r + 2 : ℕ) : ℝ)) → n1 ν₀ + (P.r + 1) * a₁ + (P.r + 1) * (P.r + 2) ≤ q0 → R0.IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν₀ a : ℝ)) → PI.CapelliEig.IsKFinCoefT (k := P.k) (r := P.r) R0.σ f → Formalism.FourierDecayAlt.P.CutBP.BigCellDerivativeExpansion p f b (C / 2 + 6) a₁ := by
  intro C hC P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 a₁ ν₀ R0 f hN hN' hT hT' hq hR hf
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  have H : BranchingSupport.HypsG := CompanionTheory.PieriExpansion.hypsG_of_zuck CompanionTheory.Zuck.zuckerman_gap
  have hK : PI.KFinSmooth := H.1.2.2.1
  have hDG := CompanionTheory.WaveGrid.WEnd.isDG_of_num hN (by omega) hR
  have hC' : CompanionTheory.WaveGrid.BallW.CoefOf R0 f := fun l l' =>
    (GlobalTheory.isCoef_of_translate_smul_exists hK P.k P.r _ _ R0 Wp Wq l l' hR).1 f hf
  exact Gp91.WG.bigCellDerivativeExpansion_of_isDS_of_coefOf H C hC P Wp Wq p lam b bv ga h q0 a₁ R0 f ν₀ hN hN' hT hT' hq hDG hC'

end GlobalTheory
