module

public import Formalism.RealPlaceAnalysis.StatementE
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantCoefficientsExpansion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

theorem _root_.GlobalTheory.T.quantum_determinant_coefficients_expansion : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (M : ℕ) (d : Fin M → ℕ) (X : ∀ i, Fin (d i) → Fin (d i) → Module.End ℂ W), (∀ i, GlRel (X i)) → (∀ i j, i ≠ j → ∀ p q r v, Commute (X i p q) (X j r v)) → ∃ c : Fin M → ℕ → Module.End ℂ W, (∀ i, c i (d i) = 1) ∧ (∀ i (u : ℂ), qdet (X i) u = ∑ j ∈ Finset.range (d i + 1), u ^ j • c i j) ∧ (∀ i, 1 ≤ d i → c i (d i - 1) = ∑ p, X i p p - (((d i : ℂ) * ((d i : ℂ) - 1) / 2)) • (1 : Module.End ℂ W)) ∧ ∀ i j a b, Commute (c i a) (c j b) := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.capelli_coef_commute | exact GlobalTheory.CompanionTheory.RgCOBlock.capelli_coef_commute | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.capelli_coef_commute <;> assumption)
