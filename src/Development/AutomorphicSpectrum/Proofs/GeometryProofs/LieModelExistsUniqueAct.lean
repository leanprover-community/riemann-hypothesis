module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
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

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieModel_exists_unique_act : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E)
    (O : Type) [CommRing O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G →
    (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) →
    ∃! ρ : O →+* Module.End R E, M.IsActOf act ρ := by
  intro S G _ R _ x E _ _ M O _ act hmon h1 hmul hadd
  have hex : ∀ a, ∃ A : E →ₗ[R] E, (∀ e, M.pt (A e) = M.pt e ≫ act a) ∧
      ∀ B : E →ₗ[R] E, (∀ e, M.pt (B e) = M.pt e ≫ act a) → B = A := by
    intro a
    have := hmon a
    exact lieModel_exists_unique_diff S G G R x E E M M (act a)
  choose A hA hAu using hex
  have hone : LinearMap.id = A 1 := hAu 1 LinearMap.id fun e => by
    rw [h1, Category.comp_id]
    rfl
  have hmul' : ∀ a b, A (a * b) = A a * A b := fun a b => (hAu (a * b) (A a * A b) fun e => by
    rw [Module.End.mul_apply, hA a, hA b, Category.assoc, ← hmul b a, mul_comm]).symm
  have hadd' : ∀ a b, A (a + b) = A a + A b := fun a b => (hAu (a + b) (A a + A b) fun e => by
    rw [LinearMap.add_apply, M.add, hA a, hA b, ← MonObj.comp_mul, hadd]).symm
  refine ⟨RingHom.mk' { toFun := A, map_one' := hone.symm, map_mul' := hmul' } hadd',
    fun a e => hA a e, fun ρ hρ => ?_⟩
  ext a : 1
  exact hAu a (ρ a) (hρ a)

end GlobalTheory.CompanionTheory.Ar
