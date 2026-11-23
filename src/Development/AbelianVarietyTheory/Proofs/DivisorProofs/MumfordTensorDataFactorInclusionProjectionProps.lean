module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem degPre_c_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : D.c 0 = 1 := by
  have h := D.c_add 0 0
  rw [add_zero, padd, ← Hom.mul_def] at h
  exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)

theorem tens_inc_pr_facts (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ}
    (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (i₀ : Fin r) :
    IsMonHom (T.inc i₀) ∧ T.inc i₀ ≫ T.pr i₀ = 𝟙 _ ∧ T.pr i₀ ≫ T.inc i₀ = T.act (Matrix.single i₀ i₀ 1) ∧
      ∀ y, D'.c (T.xi i₀ y) = D.c y ≫ T.inc i₀ := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr']
    rw [(T.pr_hom i).one_hom]
    split_ifs
    · simp
    · rw [comp_one, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr']
    rw [(T.pr_hom i).mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, T.inc_pr']
    split_ifs
    · simp
    · rw [comp_one]
      have : ((1 : D.P.A ⟶ D.P.A) ⊗ₘ (1 : D.P.A ⟶ D.P.A)) = lift (fst _ _ ≫ 1) (snd _ _ ≫ 1) := by
        ext <;> simp
      rw [this, ← Hom.mul_def, comp_one, comp_one, _root_.mul_one]
  · simpa using T.inc_pr' i₀ i₀
  · apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr', Tens.act_pr]
    by_cases h : i = i₀
    · subst h
      rw [if_pos rfl, Category.comp_id, Finset.prod_eq_single i]
      · simp [Matrix.single_apply]
      · intro j _ hj
        simp [Matrix.single_apply, Ne.symm hj]
      · simp
    · rw [if_neg h, comp_one]
      symm
      apply Finset.prod_eq_one
      intro j _
      simp [Matrix.single_apply, Ne.symm h]
  · intro y
    apply Fan.IsLimit.hom_ext T.lim
    intro i
    have hp : ∀ k, (Fan.mk D'.P.A T.pr).proj k = T.pr k := fun _ => rfl
    simp only [hp, Category.assoc, T.inc_pr', T.c_pr]
    by_cases h : i = i₀
    · subst h
      simp [Tens.xi]
    · rw [if_neg h, comp_one]
      simp [Tens.xi, Pi.single_apply, h, degPre_c_zero]

end GlobalTheory.Mum
