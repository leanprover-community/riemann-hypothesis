module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonCompleteDvrPadicAlgClosureUnitBalls
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_common_complete_dvr_padicAlgClosure_unitBalls : ∀ (p : ℕ) [Fact p.Prime] (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Algebra (FractionRing V) (PadicAlgCl p)] [Algebra (FractionRing V') (PadicAlgCl p)], IsAdicComplete (maximalIdeal V) V → IsAdicComplete (maximalIdeal V') V' → (∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ x : FractionRing V', ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V' (FractionRing V'))) → ∀ s : Finset (PadicAlgCl p), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra (FractionRing W) (PadicAlgCl p)), IsAdicComplete (maximalIdeal W) W ∧ (∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧ (↑s ⊆ Set.range (algebraMap (FractionRing W) (PadicAlgCl p))) ∧ (∀ z : PadicAlgCl p, ∃ f : Polynomial (FractionRing W), f ≠ 0 ∧ Polynomial.eval₂ (algebraMap (FractionRing W) (PadicAlgCl p)) z f = 0) ∧ (∃ (φ : V →+* W) (φK : FractionRing V →+* FractionRing W), φK.comp (algebraMap V _) = (algebraMap W _).comp φ ∧ (maximalIdeal V).map φ ≤ maximalIdeal W ∧ (algebraMap (FractionRing W) (PadicAlgCl p)).comp φK = algebraMap (FractionRing V) (PadicAlgCl p)) ∧ (∃ (φ : V' →+* W) (φK : FractionRing V' →+* FractionRing W), φK.comp (algebraMap V' _) = (algebraMap W _).comp φ ∧ (maximalIdeal V').map φ ≤ maximalIdeal W ∧ (algebraMap (FractionRing W) (PadicAlgCl p)).comp φK = algebraMap (FractionRing V') (PadicAlgCl p)) := by
  first | exact @GlobalTheory.UnifField.exists_common_ring | exact GlobalTheory.UnifField.exists_common_ring | (intros; apply GlobalTheory.UnifField.exists_common_ring <;> assumption)
