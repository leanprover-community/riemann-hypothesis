module

import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAdditionFactorGeneratorTransported
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU

theorem exists_cubical_addition_factor_generator {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) {Y : Over S}
    (a b : Y ⟶ G) :
    ∃ κ : LB.Gen (LB.LinComb P.L.L (K := Fin 4) ![a.left, b.left, (a * b).left, (a * b⁻¹).left] ![2, 2, -1, -1]),
      κ.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ Y) (z : T.left) (J), Good P.L.L z J →
        val κ ρ.left z J = kap0 P.c P.sym z J (ρ ≫ a) (ρ ≫ b) := by
  apply GlobalTheory.AddGeneric.exists_additionFactor_generator_value <;> assumption

theorem exists_addSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : CP G) (T₀ : Over S) (θ : LB.Sec (LB.LinComb P.L.L (K := Fin 1) (fun _ => (snd T₀ G).left) (fun _ => ((1 : ℕ) : ℤ)))) (ρ₀ : G ⊗ G ⟶ T₀), ∃ v : LB.Sec (LB.LinComb P.L.L (K := Fin 1 ⊕ Fin 1) (Sum.elim (fun _ => (fst G G).left) (fun _ => (snd G G).left)) (Sum.elim (fun _ => ((2 : ℕ) : ℤ)) (fun _ => ((2 : ℕ) : ℤ)))), ∀ (T : Over S) (x y : T ⟶ G) (z : T.left) (J), Good P.L.L z J → sval v (lift x y).left z J = (kap0 P.c P.sym z J x y).val * (sval θ (lift (lift x y ≫ ρ₀) (x * y)).left z J * sval θ (lift (lift x y ≫ ρ₀) (x * y⁻¹)).left z J) := by
  intro S G _ _ P T₀ θ ρ₀
  obtain ⟨κ, hκ, hv⟩ := exists_cubical_addition_factor_generator P (fst G G) (snd G G)
  obtain ⟨v, hs⟩ := exists_sec P.L.isLB (K' := Fin 1 ⊕ Fin 1)
    (φ' := Sum.elim (fun _ => (fst G G).left) (fun _ => (snd G G).left))
    (ε' := Sum.elim (fun _ => ((2 : ℕ) : ℤ)) (fun _ => ((2 : ℕ) : ℤ))) (fun U _ h => by
      have e : ∀ p : G ⊗ G ⟶ G, ∏ _k : Fin 1, h ((lift ρ₀ p).left ≫ (snd T₀ G).left) ^ ((1 : ℕ) : ℤ) = h p.left :=
        fun p => by rw [Fintype.prod_unique, ← Over.comp_left, lift_snd, Nat.cast_one, zpow_one]
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) (e _) (e _))))).trans ?_
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (H1.SectionArithmetic.mulSec (genSec κ hκ) (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.pullSec θ (lift ρ₀ (fst G G * snd G G)).left)
      (H1.SectionArithmetic.pullSec θ (lift ρ₀ (fst G G * (snd G G)⁻¹)).left)))
  refine ⟨v, fun T x y z J hJ => (hs _ _ z J hJ).trans ?_⟩
  rw [H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_mulSec _ _ _ z hJ, H1.SectionArithmetic.sval_pullSec _ _ _ z hJ,
    H1.SectionArithmetic.sval_pullSec _ _ _ z hJ, sval_genSec _ _ _ z hJ, hv T _ z J hJ, ← Over.comp_left, ← Over.comp_left,
    comp_lift, comp_lift, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]

end GlobalTheory.UU
end
