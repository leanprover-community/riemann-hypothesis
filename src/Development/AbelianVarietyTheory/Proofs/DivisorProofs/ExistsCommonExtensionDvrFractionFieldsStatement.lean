module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtensionDvrFractionFields
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_common_extension_dvr_fraction_fields : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W], Base R → GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (K' Ω : Type) [Field K'] [Field Ω] (io : FractionRing R →+* K') (j : FractionRing W →+* Ω) (l : K' →+* Ω), io.Finite → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂) (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (j₂ : FractionRing W₂ →+* Ω), FinExt ρ ∧ GlobalTheory.LN.CDvr W₂ ∧ FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧ IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧ (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) ∧ (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) ∧ ∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r)) := by
  first | exact @GlobalTheory.FieldTraitExt.exists_finite_extension_of_trait | exact GlobalTheory.FieldTraitExt.exists_finite_extension_of_trait | (intros; apply GlobalTheory.FieldTraitExt.exists_finite_extension_of_trait <;> assumption)
