module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Module
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ggeo.HomDual

noncomputable def homEquivDual (R P : Type) [CommRing R] (f : R) [AddCommGroup P] [Module R P]
    [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P] :
    (P →ₗ[R] Localization.Away f) ≃ₗ[Localization.Away f] Module.Dual (Localization.Away f) P :=
  { toFun := fun g =>
      LinearMap.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f) g
    invFun := fun g => g.restrictScalars R
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem finite_projective_hom : ∀ (R P : Type) [CommRing R] (f : R) [AddCommGroup P] [Module R P]
    [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P]
    [Module.Finite (Localization.Away f) P] [Module.Projective (Localization.Away f) P],
    Module.Finite (Localization.Away f) (P →ₗ[R] Localization.Away f) ∧
      Module.Projective (Localization.Away f) (P →ₗ[R] Localization.Away f) := by
  intro R P _ f _ _ _ _ _ _
  let e := homEquivDual R P f
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

end GlobalTheory.CompanionTheory.Ggeo.HomDual
