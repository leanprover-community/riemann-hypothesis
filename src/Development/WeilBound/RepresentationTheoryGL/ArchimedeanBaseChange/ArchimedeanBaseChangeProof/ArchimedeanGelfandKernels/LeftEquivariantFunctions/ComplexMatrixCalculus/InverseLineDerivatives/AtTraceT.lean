module

public import Development.AbelianVarietyTheory.Definitions.Foundations.GelfA
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.DeterminantPowerSmoothness.DetPowSmooth
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.RgBcC.Cxd2

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Et (lam : Fin n → ℤ) : Matrix (Fin n) (Fin n) (Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) :=
  GlobalTheory.Mem.Gelf.rowE ℂ n n + (((dw lam).detShift : ℤ) : ℂ) • (1 : Matrix (Fin n) (Fin n) (Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)))

def At (lam : Fin n → ℤ) : Matrix (Fin n) (Fin n) (Matrix (Jd n lam) (Jd n lam) ℂ) :=
  Matrix.of fun a b i j => Cxc.extL lam i (Et lam a b ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ))

def AtTrace : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ k : ℕ,
  (At lam ^ k).trace = GlobalTheory.Dec.gelfVal (infOf lam true) k • (1 : Matrix (Jd n lam) (Jd n lam) ℂ)

def AtTraceT : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ k : ℕ,
  ((Matrix.of fun a b => -(At lam b a)) ^ k).trace = GlobalTheory.Dec.gelfVal (infOf lam false) k • (1 : Matrix (Jd n lam) (Jd n lam) ℂ)

def AtDer : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ Y : Mat n,
  fderiv ℝ (Rm lam) 1 Y = ∑ a, ∑ b, Y a b • At lam a b

end PositivityTheory.RgBcC.Cxd2
