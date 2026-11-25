module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace GlobalTheory.FinalJoin2

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin
open scoped TensorProduct

def IntUnit {D : D7} (x : (AfE D)ˣ) : Prop := (x : AfE D) ∈ intAE D ∧ ((x⁻¹ : (AfE D)ˣ) : AfE D) ∈ intAE D

structure XiRec (D : D7) (p : ℕ) (de : (AfE D)ˣ →* ℂˣ) : Prop where
  real : ∀ (x : (AfE D)ˣ) (a : Af D.host.F), (x : AfE D) = a ⊗ₜ 1 → de x = 1
  rat : ∀ (x : (AfE D)ˣ) (a : D.host.E), (x : AfE D) = 1 ⊗ₜ a → de x = 1
  tame : ∀ x, IntUnit x → CongOne p x → de x = 1
  ram : ∃ x, IntUnit x ∧ CongOne (D.host.g 0 * D.host.g 1) x ∧ de x ≠ 1
  fin : ∃ m : ℕ, 0 < m ∧ ∀ x, de x ^ m = 1
  val : ∀ x, ((de x : ℂˣ) : ℂ) ∈ FO D

end GlobalTheory.FinalJoin2
