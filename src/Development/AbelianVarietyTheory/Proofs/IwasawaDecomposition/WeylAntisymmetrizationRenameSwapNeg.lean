module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.AntisymmSwap

theorem rename_swap_antisymm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (τ : ι)
    (i j : Fin (m τ)), i ≠ j →
      rename (Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩) (antisymm Q) = -antisymm Q := by
  intro ι _ _ m Q τ i j hij
  set u : ∀ t, Equiv.Perm (Fin (m t)) := Function.update 1 τ (Equiv.swap i j) with hu
  have hf : ∀ w : ∀ t, Equiv.Perm (Fin (m t)),
      (⇑(Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩)) ∘ (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))
        = fun x : Root m => (⟨x.1, (u * w) x.1 x.2⟩ : Root m) := by
    intro w
    funext ⟨t, k⟩
    simp only [Function.comp_apply, Pi.mul_apply, Equiv.Perm.mul_apply]
    by_cases ht : t = τ
    · subst ht
      simp only [hu, Function.update_self]
      rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    · have h1 : (⟨t, w t k⟩ : Root m) ≠ ⟨τ, i⟩ := fun h => ht (congrArg Sigma.fst h)
      have h2 : (⟨t, w t k⟩ : Root m) ≠ ⟨τ, j⟩ := fun h => ht (congrArg Sigma.fst h)
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, hu, Function.update_of_ne ht]
      rfl
  have hu1 : (∏ t, Equiv.Perm.sign (u t)) = -1 := by
    rw [Fintype.prod_eq_single τ]
    · simp [hu, Equiv.Perm.sign_swap hij]
    · intro t ht
      simp [hu, Function.update_of_ne ht]
  have hs : ∀ w : ∀ t, Equiv.Perm (Fin (m t)),
      (∏ t, Equiv.Perm.sign ((u * w) t) : ℤˣ) = -∏ t, Equiv.Perm.sign (w t) := by
    intro w
    simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib, hu1, neg_one_mul]
  unfold GlobalTheory.GoodMetric.antisymm

  rw [map_sum]
  simp_rw [map_zsmul, rename_rename, hf]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_equiv (Equiv.mulLeft u) (by simp) ?_
  intro w _
  simp only [Equiv.coe_mulLeft, hs, Units.val_neg, neg_smul, neg_neg]

end GlobalTheory.AntisymmSwap
