module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
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

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCAlpha

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

def lapOp : Module.End ℂ (Sm E a) :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
    ((lieS E a i j (atEmb τ 1)) ^ 2 + (lieS E a i j (atEmb τ Complex.I)) ^ 2)

def casKOp : Module.End ℂ (Sm E a) :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a, (1 / 4 : ℂ) •
    ((lieS E a i j (atEmb τ 1) - lieS E a j i (atEmb τ 1)) ^ 2 +
      (lieS E a i j (atEmb τ Complex.I) + lieS E a j i (atEmb τ Complex.I)) ^ 2)

def vecF (X : Lie E a) (f : Lie E a → ℂ) : Lie E a → ℂ := fun y => fderiv ℝ f y (rmul X y)

def lapF (f : Lie E a → ℂ) : Lie E a → ℂ :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
    (vecF E a (toL (Matrix.single i j (atEmb τ 1))) (vecF E a (toL (Matrix.single i j (atEmb τ 1))) f) +
      vecF E a (toL (Matrix.single i j (atEmb τ Complex.I))) (vecF E a (toL (Matrix.single i j (atEmb τ Complex.I))) f))

def polyF (p : Polynomial ℂ) (f : Lie E a → ℂ) : Lie E a → ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • (lapF E a)^[k] f

end GlobalTheory.HCAlpha

end
