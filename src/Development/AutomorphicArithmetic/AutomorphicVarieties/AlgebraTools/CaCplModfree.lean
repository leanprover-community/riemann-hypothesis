module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
public import Mathlib.RingTheory.Flat.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FlatnessPrecompleteProducts
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem mult_operator_shifts_twist {Λ R B M : Type} [CommRing Λ] [CommRing R] [Algebra Λ R]
    [AddCommGroup B] [Module R B] [Module Λ B] [IsScalarTower Λ R B]
    [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower Λ R M]
    [Module.Flat R B] [Module.Flat Λ M] : Module.Flat Λ (TensorProduct R B M) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  have h1 : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor R M f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have h2 : Function.Injective
      (LinearMap.lTensor B (TensorProduct.AlgebraTensorModule.lTensor R M f)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ h1
  have h3 : ∀ x, TensorProduct.AlgebraTensorModule.assoc Λ R R B M N'
        (LinearMap.lTensor (TensorProduct R B M) f x)
      = LinearMap.lTensor B (TensorProduct.AlgebraTensorModule.lTensor R M f)
        (TensorProduct.AlgebraTensorModule.assoc Λ R R B M N x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul y n =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add (f := _), hx, hy]
      | tmul b m => simp
  intro x y hxy
  apply (TensorProduct.AlgebraTensorModule.assoc Λ R R B M N).injective
  apply h2
  rw [← h3, ← h3, hxy]

theorem UpperTheory.V.AlgebraTools.IsCplAt.finite_free_baseChange :
    ∀ (Λ R : Type) [CommRing Λ] [IsNoetherianRing Λ] [CommRing R] [IsNoetherianRing R] [Algebra Λ R]
      (p : Ideal Λ) (q : Ideal R) (L B : Type) [CommRing L] [IsLocalRing L] [CommRing B] [IsLocalRing B]
      [Algebra Λ L] [Algebra R B] [Algebra L B] [Algebra Λ B] [IsScalarTower Λ R B] [IsScalarTower Λ L B]
      (M : Type) [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower Λ R M] [Module.Finite Λ M] [Module.Flat Λ M],
      IsCplAt Λ p L → IsCplAt R q B → q.comap (algebraMap Λ R) = p →
      Module.Finite L (TensorProduct R B M) ∧ Module.Free L (TensorProduct R B M) :=
  _root_.UpperTheory.Reformulated.B.FlatnessPrecompleteProducts.finite_free_baseChange
