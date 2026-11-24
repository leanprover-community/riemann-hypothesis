module

public import GroundTheory.GlobalFields.NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol
public import GroundTheory.LocalFields.LocalArtinAbstractField
public import GroundTheory.LocalFields.MainTheorem
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
public import GroundTheory.LocalFields.LocalArtinFunctoriality

@[expose] public section

namespace GroundTheory.Global

open LocalField

noncomputable section

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] {M : Type*} [Field M] [Algebra k M] [FiniteDimensional k M] [IsGalois k M]
  [IsMulCommutative (M ≃ₐ[k] M)]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  [FiniteDimensional k M] in
theorem isAbelianGalois_of_isGalois : IsAbelianGalois k M :=
  { toIsGalois := inferInstance, toIsMulCommutative := inferInstance }


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  [FiniteDimensional k M] in
theorem apply_mem_maximalAbelianExtension {Ω : Type*} [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (ι : M →ₐ[k] Ω) (z : M) : ι z ∈ maximalAbelianExtension k Ω :=
  have := isAbelianGalois_of_isGalois (k := k) (M := M)
  have := isAbelianGalois_fieldRange ι
  le_maximalAbelianExtension ι.fieldRange ⟨z, rfl⟩

theorem normResidueSymbol_eq_localArtinMapOfField :
    have := isAbelianGalois_of_isGalois (k := k) (M := M)
    normResidueSymbol k M = localArtinMapOfField k M := by
  have := isAbelianGalois_of_isGalois (k := k) (M := M)
  ext x z
  obtain ⟨τ, hτ⟩ := exists_mk_eq_localReciprocityLimit (k := k) x
  apply (residueEmbedding k M).injective
  change residueEmbedding k M _ = residueEmbedding k M _
  rw [residueEmbedding_normResidueSymbol hτ,
    localArtinMapOfField_eq_artinOfEmbedding (residueEmbedding k M), apply_artinOfEmbedding,
    localArtinMap_apply, ← hτ, topologicalAbelianizationEquiv_mk_apply]

theorem normResidueSymbol_apply_eq_localArtinMap {Ω : Type*} [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (ι : M →ₐ[k] Ω) (x : kˣ) (z : M) :
    ι (normResidueSymbol k M x z) =
      ((localArtinMap k Ω x ⟨ι z, apply_mem_maximalAbelianExtension ι z⟩ :
        maximalAbelianExtension k Ω) : Ω) := by
  have := isAbelianGalois_of_isGalois (k := k) (M := M)
  rw [normResidueSymbol_eq_localArtinMapOfField, localArtinMapOfField_eq_artinOfEmbedding ι,
    apply_artinOfEmbedding]

variable {k' : Type*} [Field k'] [ValuativeRel k'] [TopologicalSpace k']
  [IsNonarchimedeanLocalField k'] [CharZero k'] [Algebra k k'] [ValuativeExtension k k']
  [FiniteDimensional k k']
  {M' : Type*} [Field M'] [Algebra k' M'] [Algebra k M'] [IsScalarTower k k' M']
  [FiniteDimensional k' M'] [IsGalois k' M'] [IsMulCommutative (M' ≃ₐ[k'] M')]

theorem normResidueSymbol_norm (j : M →ₐ[k] M') (x : k'ˣ) (z : M) :
    normResidueSymbol k' M' x (j z) = j (normResidueSymbol k M (normUnits k k' x) z) := by
  have : IsSepClosure k (AlgebraicClosure k') :=
    isSepClosure_of_isSeparable k k' (AlgebraicClosure k')
  set ι' : M' →ₐ[k'] AlgebraicClosure k' := IsAlgClosed.lift
  set ι : M →ₐ[k] AlgebraicClosure k' := (ι'.restrictScalars k).comp j
  apply ι'.injective
  have h1 := normResidueSymbol_apply_eq_localArtinMap ι' x (j z)
  have h2 := normResidueSymbol_apply_eq_localArtinMap ι (normUnits k k' x) z
  have h3 := localArtinMap_apply_of_algebra (Ω := AlgebraicClosure k') x
    (apply_mem_maximalAbelianExtension ι z)
  exact h1.trans (h3.trans h2.symm)

end Local

end

end GroundTheory.Global
