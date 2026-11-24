module

public import Formalism.HermitianCurvature.StatementB
public import Formalism.FormalDegreeBessel.FinalG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section ellreg

variable {d : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

end ellreg

def lieOf {k r : ℕ} (Sx : Set (B.Mat k r)) : Set (B.Mat k r) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Sx}

def OmQ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {g | 0 < Gf k r z z' g ∧ ∀ a : Fin r, Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

def SymbolNil : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ g ∈ B.GV k r, g ∈ OmQ k r z z' → ∀ ξ : B.Mat k r, B.inLie k r ξ → IsNilpotent ξ →
      (∀ X ∈ lieOf (Sset k r z), (Matrix.trace (ξ * X)).re = 0) →
      (∀ X ∈ lieOf (Sset k r z'), (Matrix.trace (ξ * (g * X * g⁻¹))).re = 0) →
      ξ = 0

theorem lieOf_mono {k r : ℕ} {A B' : Set (B.Mat k r)} (h : A ⊆ B') : lieOf A ⊆ lieOf B' :=
  fun _ hX t => h (hX t)

theorem UWset_sub_Sset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : UWset k r z ⊆ Sset k r z :=
  fun h hh => ⟨h, hh, 1, (nSubgroup k r).1, by simp⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JfS
