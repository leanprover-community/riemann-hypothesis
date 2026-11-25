module

public import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FractionFieldToGenericStalkAlgebraMapEq
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

section Tri

variable {m : ℕ} {u v : Matrix (Fin m) (Fin m) E}

def simpleSum {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E := ∑ a : Fin r, A a.castSucc a.succ

end Tri

section Frames

variable {σ : E →+* E} {n r : ℕ} {J s : Matrix (Fin n) (Fin n) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

end Frames

section Lattices

variable [NumberField E] {σ : E →+* E} {n r : ℕ} {J s : Matrix (Fin n) (Fin n) E}
  {P P' : Matrix (Fin n) (Fin (r + 1)) E} {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Λ M : Submodule (𝓞 E) (Fin n → E)}





end Lattices

end GlobalTheory.IntTerm
