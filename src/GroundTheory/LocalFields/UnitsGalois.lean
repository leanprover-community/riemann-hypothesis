module

public import GroundTheory.LocalFields.Uniqueness
public import GroundTheory.LocalFields.UnitsBasic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

def integerAlgEquivLocal (σ : L ≃ₐ[K] L) : 𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L] :=
  AlgEquiv.ofAlgHom (integerAlgHom σ.toAlgHom) (integerAlgHom σ.symm.toAlgHom)
    (AlgHom.ext fun x => Subtype.ext (σ.apply_symm_apply (x : L)))
    (AlgHom.ext fun x => Subtype.ext (σ.symm_apply_apply (x : L)))

instance integerUnitsAction : MulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ where
  smul σ u := Units.map (integerAlgEquivLocal σ : 𝒪[L] →* 𝒪[L]) u
  one_smul u := by ext; rfl
  mul_smul σ τ u := by ext; rfl
  smul_mul σ u w := map_mul (Units.map (integerAlgEquivLocal σ : 𝒪[L] →* 𝒪[L])) u w
  smul_one σ := map_one (Units.map (integerAlgEquivLocal σ : 𝒪[L] →* 𝒪[L]))

theorem unitsIncl_smul (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    unitsIncl L (σ • u) = σ • unitsIncl L u := by
  ext
  change ((integerAlgEquivLocal σ) (u : 𝒪[L]) : L) = σ ((u : 𝒪[L]) : L)
  rfl

end GroundTheory.LocalField
