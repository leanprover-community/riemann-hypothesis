module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonBaseChangePolarizedAbelianSchemeOfGe
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


theorem _root_.GlobalTheory.T.sameAt_of_sameAt_comp_algebraMap : ∀ (O Ω R₁ R₂ M Γ : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] [CommRing R₁] [CommRing R₂] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂)) (f₁ : R₁ →+* O) (f₂ : R₂ →+* O) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A)) (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)), SameAt P₁ P₂ ((algebraMap O Ω).comp f₁) ((algebraMap O Ω).comp f₂) e₁ e₂ t₁ t₂ → SameAt P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ := by
  first | exact @GlobalTheory.Poinc.sameAt_of_generic | exact GlobalTheory.Poinc.sameAt_of_generic | (intros; apply GlobalTheory.Poinc.sameAt_of_generic <;> assumption)
