module

public import Development.EtaleCohomology.KummerTheory.FinalTheorems
public import Mathlib.CategoryTheory.Generator.Sheaf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.KummerTheory.LHCut

theorem corep_of : Corep := by
  intro Λ _ S U
  let M : ModuleCat.{1} (ULift.{1} Λ) := ModuleCat.of (ULift.{1} Λ) (ULift.{1} Λ)
  let P : SlShv Λ S := Sheaf.freeYoneda (Scheme.etaleTopology.over S) U M
  have key : ∀ (F : SlShv Λ S) (φ : P ⟶ F),
      Sheaf.freeYonedaHomEquiv φ = Sheaf.freeYonedaHomEquiv (𝟙 P) ≫ φ.hom.app (op U) := by
    intro F φ
    conv_lhs => rw [← Category.id_comp φ]
    simp only [Sheaf.freeYonedaHomEquiv]
    rfl
  refine ⟨P, (Sheaf.freeYonedaHomEquiv (𝟙 P)).hom 1, fun F => ?_⟩
  have e : (fun φ : P ⟶ F => (φ.hom.app (op U)).hom ((Sheaf.freeYonedaHomEquiv (𝟙 P)).hom 1)) =
      (fun g : M ⟶ F.obj.obj (op U) => g.hom 1) ∘ Sheaf.freeYonedaHomEquiv := by
    funext φ
    simp only [Function.comp_apply, key F φ]
    rfl
  rw [e]
  refine Function.Bijective.comp ⟨fun g h hgh => ?_, fun n => ?_⟩ (Equiv.bijective _)
  · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    have : x = x • (1 : ULift.{1} Λ) := (mul_one x).symm
    rw [this, map_smul, map_smul]
    exact congrArg (x • ·) hgh
  · exact ⟨ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} Λ) _ n), one_smul _ n⟩

end LateralTheory.KummerTheory.LHCut
