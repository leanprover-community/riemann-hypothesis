module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
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

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def cc (A : Et F E) (e : A.L) (p : A.K × A.K) : A.L :=
  algebraMap A.K A.L p.1 * e + algebraMap A.K A.L p.2 * (1 - e)

def ci (A : Et F E) (e : A.L) (y : A.L) : A.K × A.K :=
  (Algebra.trace A.K A.L (y * e), Algebra.trace A.K A.L (y * (1 - e)))

def kx (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (u b : A.K) : ℂ := A.psiK ψ (x * u * b)

def pt (A : Et F E) (ν : Measure A.K) (ψ : AddChar F ℂ) (x : A.K) (Φ : A.K × A.K → ℂ) (p : A.K × A.K) : ℂ :=
  fourB ν (kx A ψ x) (fun b => Φ (p.1, b)) p.2

def rg (A : Et F E) (g : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ) (p : A.K × A.K) : ℂ :=
  Φ (p.1 * (g : Matrix (Fin 2) (Fin 2) A.K) 0 0 + p.2 * (g : Matrix (Fin 2) (Fin 2) A.K) 1 0,
    p.1 * (g : Matrix (Fin 2) (Fin 2) A.K) 0 1 + p.2 * (g : Matrix (Fin 2) (Fin 2) A.K) 1 1)

def wHyp (A : Et F E) (e : A.L) (ν : Measure A.K) (ψ : AddChar F ℂ) (x : A.K)
    (g : SpecialLinearGroup (Fin 2) A.K) (φ : A.L → ℂ) (y : A.L) : ℂ :=
  pt A ν ψ x (pt A ν ψ x (pt A ν ψ x (rg A g (pt A ν ψ x (fun p => φ (cc A e p)))))) (ci A e y)

end GlobalTheory.JR.Hyp
