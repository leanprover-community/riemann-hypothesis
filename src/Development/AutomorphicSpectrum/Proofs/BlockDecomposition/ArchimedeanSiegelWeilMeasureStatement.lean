module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilMeasure
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

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.archimedean_siegel_weil_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∀ minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E), IsGramFibFree (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf → ∀ (c : HermR (Ainf F) σ n) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ), GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → Measurable φ ∧ Integrable φ (minf c) ∧ ∀ ρ : ℕ → HermR (Ainf F) σ n → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets → (∀ k, Integrable (fun X => φ X * (gramTest (Ainf F) σ J c (ρ k) X : ℂ)) (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) ∧ Filter.Tendsto (fun k => (∫ X, φ X * (gramTest (Ainf F) σ J c (ρ k) X : ℂ) ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) / ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ)) Filter.atTop (nhds (∫ X, φ X ∂(minf c))) := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.avgInf_tendsto | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.avgInf_tendsto | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.avgInf_tendsto <;> assumption)
