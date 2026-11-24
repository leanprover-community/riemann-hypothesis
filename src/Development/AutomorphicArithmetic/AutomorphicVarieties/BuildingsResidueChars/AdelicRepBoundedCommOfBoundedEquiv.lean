module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

theorem UpperTheory.adelic_rep_bounded_comm_of_bounded_equiv :
    UpperTheory.V.Af.CohB.BddEquiv → UpperTheory.V.Af.BA.BddSub → UpperTheory.V.Af.BA.BddOver → UpperTheory.V.Af.BA.BddComm := by
  intro hEq hSub hOver G _ Γ Λ hc hΛ
  obtain ⟨h1, h2⟩ := hc
  have f1 : (Γ.subgroupOf Λ).FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp h1
  have f2 : (Λ.subgroupOf Γ).FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp h2
  have b1 := hSub Λ (Γ.subgroupOf Λ) f1 hΛ
  have e : (Γ.subgroupOf Λ) ≃* (Λ.subgroupOf Γ) :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have b2 := hEq _ _ ⟨e⟩ b1
  exact hOver Γ (Λ.subgroupOf Γ) f2 b2
