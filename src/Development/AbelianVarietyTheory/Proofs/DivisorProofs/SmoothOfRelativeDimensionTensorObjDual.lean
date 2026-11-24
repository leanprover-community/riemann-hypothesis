module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionTensor
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.TensorDualDim

theorem finrank_dual_eq (O X : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] :
    Module.finrank O (Module.Dual O X) = Module.finrank O X := by
  haveI : Module.FinitePresentation O X := Module.finitePresentation_of_projective O X
  let F := FractionRing O
  let f : X →ₗ[O] F ⊗[O] X := TensorProduct.mk O F X 1
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors O) f le_rfl
  let g := IsLocalizedModule.map (nonZeroDivisors O) f (Algebra.linearMap O F)
  have h2 := IsLocalizedModule.finrank_eq (nonZeroDivisors O) g le_rfl
  rw [← h1, ← h2, ← IsLocalization.finrank_eq F (nonZeroDivisors O) le_rfl,
    ← IsLocalization.finrank_eq F (nonZeroDivisors O) le_rfl,
    (LinearMap.extendScalarsOfIsLocalizationEquiv (nonZeroDivisors O) F).finrank_eq]
  exact Subspace.dual_finrank_eq

theorem smoothOfRelativeDimension_tensorObj_dual : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (g : ℕ), SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension (Module.finrank O X * g) (tensorObj (Module.Dual O X) a).hom := by
  intro S B _ _ O _ _ _ a X _ _ _ _ g hg
  have h := GlobalTheory.SerreDim.smoothOfRelativeDimension_tensor S O (Module.Dual O X) B
    (tensorObj (Module.Dual O X) a) a (tensorAct (Module.Dual O X) a) g
    ⟨GlobalTheory.Serre.isTensor (Module.Dual O X) a⟩ hg
  rwa [finrank_dual_eq] at h

end GlobalTheory.TensorDualDim
