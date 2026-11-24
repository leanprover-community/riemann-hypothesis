module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH

namespace TorusFibre
variable {k : Type} [Field k]

end TorusFibre

namespace AbelianFibre
variable {k : Type} [Field k]

theorem lbIso_of_gens {X : Scheme.{0}} {A B : LB X} (s : A.Gen) (hs : s.IsGen) (t : B.Gen) (ht : t.IsGen) :
    LBIso A B := by
  refine ⟨⟨fun p => res inf_le_left (t.s p.1) * (res inf_le_right (s.s p.2))⁻¹⟩,
    fun (p q : B.ι × A.ι) => unit_ext fun y hy => by
      have v : ∀ p : B.ι × A.ι, y ∈ B.U p.1 ⊓ A.U p.2 → gm (𝟙 X) y (B.U p.1 ⊓ A.U p.2)
          (res inf_le_left (t.s p.1) * (res inf_le_right (s.s p.2))⁻¹) =
          gm (𝟙 X) y _ (t.s p.1) * (gm (𝟙 X) y _ (s.s p.2))⁻¹ := fun p hp => by
        rw [map_mul, map_inv, gm_res (𝟙 X) y _ hp, gm_res (𝟙 X) y _ hp]
      have e₁ := congrArg (gm (𝟙 X) y _) (hs p.2 q.2)
      have e₂ := congrArg (gm (𝟙 X) y _) (ht p.1 q.1)
      have m₁ : y ∈ A.U p.2 ⊓ A.U q.2 := ⟨hy.1.2, hy.2.2⟩
      have m₂ : y ∈ B.U p.1 ⊓ B.U q.1 := ⟨hy.1.1, hy.2.1⟩
      rw [map_mul, gm_res (𝟙 X) y _ m₁, gm_res (𝟙 X) y _ m₁] at e₁
      rw [map_mul, gm_res (𝟙 X) y _ m₂, gm_res (𝟙 X) y _ m₂] at e₂
      refine ((gm_res (𝟙 X) y _ hy _).trans (v p hy.1)).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
        (gm_div A B (𝟙 X) y p q hy) ((gm_res (𝟙 X) y _ hy _).trans (v q hy.2))).trans ?_)))
      rw [e₁, e₂, mul_inv]
      exact mul_mul_mul_comm _ _ _ _⟩

end AbelianFibre

namespace MonomialImmersion
variable (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

end MonomialImmersion

end GlobalTheory.ZH
end
