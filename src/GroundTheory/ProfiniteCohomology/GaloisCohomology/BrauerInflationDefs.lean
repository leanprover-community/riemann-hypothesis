module

public import GroundTheory.ProfiniteCohomology.GaloisCohomology.UnitsInflationCochainsFHomApply
public import Mathlib.Algebra.Lie.OfAssociative
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

universe u


variable (K E F : Type u) [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F]
  [IsScalarTower K E F] [Normal K E]

noncomputable def unitsTowerHom :
    Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := F) E) (galUnits.{u} K E) ⟶
      galUnits.{u} K F :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Eˣ) (B := Additive Fˣ) (MonoidHom.toAdditive
    (Units.map ((algebraMap E F : E →+* F) : E →* F))), fun σ => by
    ext x
    exact AlgEquiv.restrictNormal_commutes σ E ((Additive.toMul (α := Eˣ) x : Eˣ) : E)⟩

noncomputable def unitsInflationTower (n : ℕ) :
    groupCohomology (galUnits.{u} K E) n ⟶ groupCohomology (galUnits.{u} K F) n :=
  groupCohomology.map (AlgEquiv.restrictNormalHom E) (unitsTowerHom K E F) n


section LE

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {E F : IntermediateField K L}
  (h : E ≤ F) [Normal K E]

noncomputable def galRestrictOfLE : Gal(F/K) →* Gal(E/K) :=
  letI : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  AlgEquiv.restrictNormalHom E

theorem coe_galRestrictOfLE_apply (σ : Gal(F/K)) (x : E) :
    ((galRestrictOfLE h σ x : E) : L) = ((σ (IntermediateField.inclusion h x) : F) : L) := by
  let : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  exact congrArg (fun y : F => (y : L)) (AlgEquiv.restrictNormal_commutes σ E x)

noncomputable def unitsOfLE :
    Rep.res (galRestrictOfLE h) (galUnits.{u} K E) ⟶ galUnits.{u} K F :=
  letI : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  unitsTowerHom K E F

noncomputable def unitsInflationOfLE (n : ℕ) :
    groupCohomology (galUnits.{u} K E) n ⟶ groupCohomology (galUnits.{u} K F) n :=
  groupCohomology.map (galRestrictOfLE h) (unitsOfLE h) n

end LE

end GroundTheory.ProfCoh
