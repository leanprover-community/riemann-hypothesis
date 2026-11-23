module

public import Formalism.LocalToGlobal.GlobalTheory.HLatOps
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
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianLattices.StatementLat

@[expose] public section

open Module NumberField TensorProduct

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration.ExtInvSk

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps

section
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  (K' : Type) [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']

abbrev ext (A : HLat K) (N : Submodule (𝓞 K) A.V) : Submodule (𝓞 K') (baseChange K' A).V :=
  (baseChange K' (withL A N)).L

def tau (A : HLat K) (σ : K' ≃ₐ[K] K') : (baseChange K' A).V ≃ₗ[K] (baseChange K' A).V :=
  TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl K A.V)
end

def S2 : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K]
  [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']
  (A : HLat K) (M N : Submodule (𝓞 K) A.V), N.FG → M ≤ N →
  M.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 →
  (ext K' A M).toAddSubgroup.relIndex (ext K' A N).toAddSubgroup ≠ 0 ∧
  (ext K' A M).toAddSubgroup.relIndex (ext K' A N).toAddSubgroup ≤
    M.toAddSubgroup.relIndex N.toAddSubgroup ^ finrank K K'

def GaloisDescentSubspaces : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K]
  [Field K'] [NumberField K'] [StarRing K'] [Algebra K K'] [IsGalois K K']
  (A : HLat K) (W : Submodule K' (K' ⊗[K] A.V)),
  (∀ (σ : K' ≃ₐ[K] K') (y : K' ⊗[K] A.V), y ∈ W → tau K' A σ y ∈ W) →
  ∃ W₀ : Submodule K A.V, W = W₀.baseChange K'

def ExtensionInterSubspace : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K]
  [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']
  (A : HLat K), A.L.FG → ∀ (W₀ : Submodule K A.V), W₀ ≤ Submodule.span K (A.L : Set A.V) →
  ∀ (y : (baseChange K' A).V),
  y ∈ (baseChange K' A).L → (y : K' ⊗[K] A.V) ∈ W₀.baseChange K' →
  y ∈ ext K' A (A.L ⊓ W₀.restrictScalars (𝓞 K))

end Formalism.L2.Geo.ExtensionFiltration.ExtInvSk
