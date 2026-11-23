module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsFinTyp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

noncomputable section

open NumberField

namespace Formalism.IndefR.principalLevelFrame

section SS

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]


def fixN (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (N : ℕ) : Submodule ℂ A where
  carrier := {a | ∀ κ, Formalism.L2.NG.Cong L n N κ → ρ κ a = a}
  zero_mem' := fun κ _ => map_zero _
  add_mem' := fun ha hb κ hκ => by rw [map_add (f := _), ha κ hκ, hb κ hκ]
  smul_mem' := fun c a ha κ hκ => by rw [map_smul, ha κ hκ]

def IsEqvA (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (π : Formalism.L2.NG.FinTyp L n) (Φ : π.S →ₗ[ℂ] A) : Prop :=
  ∀ (h : Formalism.AUTREP.GAf L n) (f : π.S), Φ ⟨Formalism.L2.NG.rt L n h f, π.stable h f f.2⟩ = ρ h (Φ f)

end SS

end Formalism.IndefR.principalLevelFrame
