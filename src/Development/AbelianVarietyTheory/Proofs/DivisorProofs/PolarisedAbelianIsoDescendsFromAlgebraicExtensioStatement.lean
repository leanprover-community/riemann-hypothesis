module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianIsoDescendsFromAlgebraicExtensio
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.polarisedAbelian_iso_descends_from_algebraicExtension : ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K), (∀ z : K, ∃ f : Polynomial k, f ≠ 0 ∧ Polynomial.eval₂ σ z f = 0) → ∀ (B₁ B₂ : PolAV (Sp k)) (P₀ : PolAV (Sp K)) (c₁ : P₀.A.left ⟶ B₁.A.left) (c₂ : P₀.A.left ⟶ B₂.A.left), IsGrpPullback P₀.A B₁.A (spMap σ) c₁ → IsGrpPullback P₀.A B₂.A (spMap σ) c₂ → LBIso P₀.L (B₁.L.pull c₁) → LBIso P₀.L (B₂.L.pull c₂) → ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (C : PolAV (Sp k₁)) (χ : C.A.left ⟶ B₁.A.left), IsGrpPullback C.A B₁.A (spMap α) χ → LBIso C.L (B₁.L.pull χ) → ∃ χ₂ : C.A.left ⟶ B₂.A.left, IsGrpPullback C.A B₂.A (spMap α) χ₂ ∧ LBIso C.L (B₂.L.pull χ₂) ∧ ∀ d : P₀.A.left ⟶ C.A.left, d ≫ χ = c₁ → d ≫ C.A.hom = P₀.A.hom ≫ spMap β → d ≫ χ₂ = c₂ := by
  first | exact @GlobalTheory.PolIsoDescent.model_descends | exact GlobalTheory.PolIsoDescent.model_descends | (intros; apply GlobalTheory.PolIsoDescent.model_descends <;> assumption)
