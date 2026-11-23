module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityBoundFromBoxVolumeGrowth
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.density_bound_from_box_volume_growth : ∀ (K W : Type) [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) (n M : ℕ), 0 < n → 2 * n < M → ∀ (H : Type) [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] (μ : Measure (Fin n → Fin M → K)) (ν : Measure H) (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞), C₀ ≠ ⊤ → (∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)))) → (∀ (S : Set (Fin n → Fin M → K)) (C : ℝ≥0∞) (a : Fin n) (s : Fin n → K), s a = 0 → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q S C → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearK a s '' S) C) → ∀ R : ℝ, 1 ≤ R → ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ ε : ℝ, 0 < ε ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) \ GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK κ R ε) δ := by
  exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.Bad.bad_density
