module

import CompanionTheory.AutomorphicTheory.ThetaDilations.BoundedA
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionModularityStatement
import Development.WeilBound.CoreStatements.ThetaDilations.OrbitAdelic
import Development.WeilBound.CoreStatements.ThetaDilations.ProdRho
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ReductionToSiegelDomainStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionAutomorphyStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionCuspExpansionStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionGrowthBoundStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageExpectedCountStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageIntegralFormulaStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaSeriesSummableStatement

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem sb_indL {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] {a : ℕ} (ha : 0 < a) :
    SB (indL (F := F) (ι := ι) a) := by
  apply _root_.CompanionTheory.PlacePermOperatorBicommutantSpan.sb_indL <;> assumption

theorem bounded_a : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∃ C : ℝ, ∀ a : ℕ, 0 < a → ∀ x : InfinitePlace F → ℝ, SB (indL (F := F) (ι := ι) a) ∧ ‖((∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) - eis ψ lf B ρ P (indL a) (fun w => (x w : ℂ) + Complex.I))‖ ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) :=
  _root_.CompanionTheory.PlacePermOperatorBicommutantSpan.bounded_a

end PositivityTheory.PlacePermOperatorBicommutantSpan
