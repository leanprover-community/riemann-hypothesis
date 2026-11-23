module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_secK_pullMul_gen : ∀ {X Y : Scheme.{0}} (L : LB X), L.IsLB → ∀ (β : Y ⟶ X) (g : Y ⟶ Y) (h : X ⟶ X), g ≫ β = β ≫ h →
    ∀ (k k' : ℕ) (u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, h] ![(k' : ℤ), -(k : ℤ)])), u.IsGen → ∀ (σ : SecK L β k),
    ∃ σ₂ : SecK L β k', ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval σ₂ r z J = (val u (r ≫ β) z J).val * sval σ (r ≫ g) z J := by
  intro X Y L hL β g h hc k k' u hu σ
  have hu' := DVR.pullGen_isGen L _ _ u hu β
  have hF : FormEq (Sum.elim (fun i => g ≫ (fun _ : Fin 1 => β) i) (fun i => β ≫ (![𝟙 X, h] : Fin 2 → (X ⟶ X)) i))
      (Sum.elim (fun _ : Fin 1 => (k : ℤ)) ![(k' : ℤ), -(k : ℤ)]) (fun _ : Fin 1 => β) (fun _ => (k' : ℤ)) := by
    intro U _ f
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Category.comp_id, hc, zpow_neg]
    rw [mul_comm (f β ^ _)]
    exact mul_inv_cancel_left _ _
  obtain ⟨σ₂, hσ₂⟩ := exists_sec hL hF (pullMulSec σ g (LB.pullGen L _ _ u β) hu')
  refine ⟨σ₂, fun Z r z J hJ => ?_⟩
  rw [hσ₂ Z r z J hJ, sval_pullMulSec σ g _ hu' r z hJ, val_pull hJ u β r, mul_comm]

end GlobalTheory.Mum
