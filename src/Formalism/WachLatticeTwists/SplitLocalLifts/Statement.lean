module

public import Mathlib.Algebra.Module.Submodule.Map
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
import Mathlib.NumberTheory.Padics.PadicIntegers
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.CoboundaryTransfers.Statement
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Statement
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N2

def LiftO {O : Type*} [CommRing O] (ℓ : ℕ) {H₁ H₂ : Type*} [AddCommGroup H₁] [Module O H₁]
    [AddCommGroup H₂] [Module O H₂] (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂)
    (g : H₁ →ₗ[O] H₂) (e : ℕ) : Prop :=
  ∀ κ ∈ Hf₂, ((ℓ : O) ^ e) • κ ∈ Hf₁.map g

section FinalTheorems
variable (ℓ : ℕ) [Fact ℓ.Prime] {H₁ H₂ : Type} [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ)

end FinalTheorems

end Formalism.RepresentationBoundsCohomology.JL
