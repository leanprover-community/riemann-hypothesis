module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JR.WeilMix

variable {r : ℕ} {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [StarRing E]

def ptrB (M : Meas r F E) (ψ : AddChar F ℂ) (f : Gl r F → ℂ) (Y : Gl r F) : ℂ :=
  letI := M.mF
  ∫ b, f (Y.1, b, Y.2.2.1, Y.2.2.2) * ψ (b ⬝ᵥ Y.2.1) ∂(Measure.pi fun _ : Fin r => M.μF)

def rowMap (g : SpecialLinearGroup (Fin 2) F) (Y : Gl r F) : Gl r F :=
  (Y.1, fun i => Y.2.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 0 1 + Y.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 1 1,
    fun i => Y.2.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 0 0 + Y.2.1 i * (g : Matrix (Fin 2) (Fin 2) F) 1 0, Y.2.2.2)

def rowAct (g : SpecialLinearGroup (Fin 2) F) (h : Gl r F → ℂ) (Y : Gl r F) : ℂ := h (rowMap g Y)

def weil (M : Meas r F E) (ψ : AddChar F ℂ) (g : SpecialLinearGroup (Fin 2) F) (f : Gl r F → ℂ) : Gl r F → ℂ :=
  ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct g (ptrB M ψ f))))

def negB (f : Gl r F → ℂ) (Y : Gl r F) : ℂ := f (Y.1, -Y.2.1, Y.2.2.1, Y.2.2.2)

end GlobalTheory.JR.WeilMix
