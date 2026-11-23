module

public import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
import GroundTheory.GlobalFields.NormResidueSymbol.AbstractUnique
public import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
public import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialInfinite
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField AdeleBaseChange IdeleGroup

noncomputable section

variable {K K' L L' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L]
  [NumberField L] [Field L'] [NumberField L'] [Algebra K K'] [Algebra K L] [Algebra K L']
  [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']


variable (K) in
def restrictScalarsHom : (L' ≃ₐ[K'] L') →* (L' ≃ₐ[K] L') where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

omit [NumberField K] [NumberField K'] [NumberField L'] in
@[simp]
theorem restrictScalarsHom_apply (σ : L' ≃ₐ[K'] L') : restrictScalarsHom K σ = σ.restrictScalars K :=
  rfl

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L']
  [IsMulCommutative (L' ≃ₐ[K'] L')]

theorem restrictNormal_restrictScalars_ideleSymbol (x : IdeleGroup K') :
    ((ideleSymbol K' L' x).restrictScalars K).restrictNormal L =
      ideleSymbol K L (ideleNorm K K' x) := by
  have h := IdeleGroup.continuous_monoidHom_ext
    (ψ := (AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L).comp
      ((restrictScalarsHom K).comp (ideleSymbol K' L')))
    (ψ' := (ideleSymbol K L).comp (ideleNorm K K'))
    ((continuous_of_discreteTopology : Continuous ((AlgEquiv.restrictNormalHom (F := K)
      (K₁ := L') L).comp (restrictScalarsHom (L' := L') K))).comp (continuous_ideleSymbol L'))
    ((continuous_ideleSymbol L).comp (continuous_ideleNorm (K := K) (L := K')))
    (fun v' a ↦ by
      change ((ideleSymbol K' L' (finiteEmbedding v' a)).restrictScalars K).restrictNormal L =
        ideleSymbol K L (ideleNorm K K' (finiteEmbedding v' a))
      rw [ideleSymbol_finiteEmbedding, ideleNorm_finiteEmbedding, ideleSymbol_finiteEmbedding]
      exact restrictNormal_localSymbol_norm (below K v') v' a)
    (fun w' a ↦ by
      change ((ideleSymbol K' L' (infiniteEmbedding w' a)).restrictScalars K).restrictNormal L =
        ideleSymbol K L (ideleNorm K K' (infiniteEmbedding w' a))
      rw [ideleSymbol_infiniteEmbedding, ideleNorm_infiniteEmbedding, ideleSymbol_infiniteEmbedding]
      exact restrictNormal_infiniteLocalSymbol_norm w' a)
  exact congrArg (fun f : IdeleGroup K' →* (L ≃ₐ[K] L) ↦ f x) h

end

end GroundTheory.Global
