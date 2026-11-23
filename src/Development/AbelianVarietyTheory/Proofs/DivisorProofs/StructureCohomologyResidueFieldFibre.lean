module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomSplitBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimLEIsLocalRingQuotPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapAlgHomAlgebraMap
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.CohBaseChange

theorem main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s :=
  of_parts (@GlobalTheory.AbCoh.exists_finite_projective_model) (@GlobalTheory.AbCoh.projective_coker_of_liftsAt) (@GlobalTheory.AbCoh.cohom_split_baseChange)

end GlobalTheory.AbCoh.CohBaseChange
