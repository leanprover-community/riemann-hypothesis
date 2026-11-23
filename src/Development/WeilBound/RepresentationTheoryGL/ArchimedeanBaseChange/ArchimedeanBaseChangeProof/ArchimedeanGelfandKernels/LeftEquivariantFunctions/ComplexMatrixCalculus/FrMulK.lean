module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InstBorelUK
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.RgBcC

variable {n : ℕ}

def FrOne : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), lefFr n lam 1 = 1

def FrMulK : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ) (k k' : Matrix.unitaryGroup (Fin n) ℂ),
  lefFr n lam (k * k').1 = lefFr n lam k.1 * lefFr n lam k'.1

def FrIso : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ) (k : Matrix.unitaryGroup (Fin n) ℂ) (v : EV n lam), ‖lefFr n lam k.1 v‖ = ‖v‖

def FrCont : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => lefFr n lam k.1

end PositivityTheory.RgBcC
