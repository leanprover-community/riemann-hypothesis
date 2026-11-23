module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbacksDifferByUnit
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

theorem _root_.GlobalTheory.T.multiplicationPullbacks_differ_by_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (m : ℕ)
    (u : LB.Gen (LB.LinComb C.P.L.L (K := Fin 2) ![𝟙 C.G.left, (mulA C.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    u.IsGen →
    ∀ (uG : LB.Gen (LB.LinComb T.U.LG.L (K := Fin 2) ![𝟙 T.G.left, (mulA T.G m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])),
    uG.IsGen → ∀ (b : W) (σ' : H0 T.U.LG.L 1) (σ : SecK C.P.L.L T.β 1), T.Carries b σ' σ →
    ∀ (σ₂ : SecK C.P.L.L T.β (m ^ 2)) (σ'' : H0 T.U.LG.L (m ^ 2)),
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J →
      sval σ₂ r z J = (val u (r ≫ T.β) z J).val * sval σ (r ≫ (mulA T.G m).left) z J) →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) (J : (Z ⟶ T.G.left) → T.U.LG.L.ι), Good T.U.LG.L z J →
      sval σ'' r z J = (val uG (r ≫ 𝟙 _) z J).val * sval σ' (r ≫ (mulA T.G m).left) z J) →
    ∃ v : Wˣ, T.Carries (b * v) σ'' σ₂ := by
  first | exact @GlobalTheory.Mum.Trait.carries_mulPull | exact GlobalTheory.Mum.Trait.carries_mulPull | (intros; apply GlobalTheory.Mum.Trait.carries_mulPull <;> assumption)
