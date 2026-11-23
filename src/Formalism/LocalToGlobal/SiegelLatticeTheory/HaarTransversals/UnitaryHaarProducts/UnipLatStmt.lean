module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipRat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Matrix NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.Pf.UnipB

open Formalism.L2.SG.Pf.Unip

def LatStepP {D : D7} (X : HidaSetting D) : Prop :=
  ∀ tY : ℕ, 0 < tY → ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (P : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ),
    (∀ v, InPat (lvk X) k (P v)) → (∀ v, (P v)ᴴ * JBv X v = -(JBv X v * P v)) →
    ∃ Y : Matrix (Kap X) (Kap X) X.B.I.E, InPat (lvk X) k Y ∧ Yᴴ * JB X = -(JB X * Y) ∧ IntDiv tY Y ∧
      ∀ v i j, ‖(P v - Y.map (X.B.I.φ v)) i j‖ ≤ ρ

def LatStepC : Prop := ∀ (D : D7) (X : HidaSetting D), LatStepP X

end Formalism.L2.SG.Pf.UnipB
