module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def extendAddHom {K K' : Type} (j : K ↪ K') : (K → ℕ) →+ (K' → ℕ) where
  toFun x := Function.extend j x 0
  map_zero' := by
    funext k'
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      simp [j.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  map_add' x y := by
    funext k'
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      simp [j.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]

theorem weight_mapDomain_blockWeight {K K' : Type} [DecidableEq K] [DecidableEq K'] (j : K ↪ K')
    (ι : K → Type) (ι' : K' → Type) (g : (Σ k, ι k) → (Σ k', ι' k'))
    (hg : ∀ v, (g v).1 = j v.1) (u : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain g u) =
      Function.extend j (Finsupp.weight (blockWeight ι) u) 0 := by
  have key : (Finsupp.weight (R := ℕ) (blockWeight ι')).comp
        (Finsupp.mapDomain.addMonoidHom (M := ℕ) g) =
      (extendAddHom j).comp (Finsupp.weight (R := ℕ) (blockWeight ι)) := by
    ext v
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.singleAddHom_apply,
      Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, Finsupp.weight_single,
      one_smul]
    show blockWeight ι' (g v) _ = Function.extend j (blockWeight ι v) 0 _
    rename_i k'
    simp only [blockWeight, hg v]
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      rw [j.injective.extend_apply]
      by_cases hav : a = v.1
      · subst hav; simp
      · rw [Pi.single_eq_of_ne (fun e => hav (j.injective e)), Pi.single_eq_of_ne hav]
    · rw [Function.extend_apply' _ _ _ h, Pi.single_eq_of_ne (fun e => h ⟨v.1, e.symm⟩)]
      rfl
  exact DFunLike.congr_fun key u

theorem RenameMultiHomog.proof : RenameMultiHomog.Statement.{u} := by
  intro R _ K K' _ _ j ι ι' g hg f d hf e he
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero g f e he
  rw [weight_mapDomain_blockWeight j ι ι' g hg u, hf hu]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
