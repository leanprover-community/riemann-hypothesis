module

public import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
public import GroundTheory.GlobalFields.IdeleClassGroup.InvariantsGalois
public import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
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
import Mathlib.Tactic.TypeStar
public import GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassMapIdeleClassMap
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open NumberField IntermediateField IsDedekindDomain IdeleGroup FiniteSubfield GroundTheory.ProfCoh GroundTheory.LocalField

noncomputable section

section Transport

variable {K : Type*} [Field K] [NumberField K] {L L' : Type*} [Field L] [NumberField L] [Field L']
  [NumberField L'] [Algebra K L] [Algebra K L'] [IsGalois K L] [IsGalois K L']
  [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (L' ≃ₐ[K] L')]

theorem ideleSymbol_apply_algEquiv (e : L ≃ₐ[K] L') (x : IdeleGroup K) (l : L) :
    ideleSymbol K L' x (e l) = e (ideleSymbol K L x l) := by
  let _ : Algebra L L' := e.toRingHom.toAlgebra
  have : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq fun a ↦ (e.commutes a).symm
  have h := AlgEquiv.restrictNormal_commutes (ideleSymbol K L' x) L l
  rw [restrictNormal_ideleSymbol L L' x] at h
  exact h.symm

end Transport


variable {K : FiniteSubfield} (E : FiniteSubfield) [hKE : Fact (K ≤ E)]

variable [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)]

attribute [local instance] FiniteSubfield.isGalois_of_normal


variable {K : FiniteSubfield} (ι : LocalEmbeddings K)


variable (E : FiniteSubfield) [Fact (K ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)]

attribute [local instance] FiniteSubfield.isGalois_of_normal galCommGroup


end

end GroundTheory.Global
