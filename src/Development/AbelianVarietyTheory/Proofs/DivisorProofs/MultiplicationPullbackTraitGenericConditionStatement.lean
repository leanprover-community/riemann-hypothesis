module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbackTraitGenericCondition
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

theorem _root_.GlobalTheory.T.multiplicationPullback_trait_genericCondition : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ) (a : W)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (θ₀ : SecK C.P.L.L C.α 1) (S : SecK C.P.L.L C.α (m ^ 2)),
    (∀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J, Good C.P.L.L z J →
      sval S p z J = (val u (p ≫ C.α) z J).val * sval θ₀ (p ≫ (mulA C.A.A m).left) z J) →
    ∀ (σ : SecK C.P.L.L T.β 1) (σ₂ : SecK C.P.L.L T.β (m ^ 2)),
    (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval θ₀ p' z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J →
      sval σ₂ p z J = gs p z ⊤ (scal T.G.hom a) * sval S p' z J := by
  first | exact @GlobalTheory.Mum.pullMul_trait_generic | exact GlobalTheory.Mum.pullMul_trait_generic | (intros; apply GlobalTheory.Mum.pullMul_trait_generic <;> assumption)
