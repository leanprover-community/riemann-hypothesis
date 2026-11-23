module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SchSharpA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.FockWeights
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

def gaW (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := lam - rhoC ε + rhoHol ε


variable {M : Type*} [AddCommGroup M] [Module ℂ M]


variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

def coordSpan (Z : Submodule ℂ (TensorProduct ℂ M (Fock n))) : Submodule ℂ M :=
  Submodule.span ℂ {v | ∃ (s : Finset (Fin (n * n))) (y : TensorProduct ℂ M (Fock n)), y ∈ Z ∧ v = tco s y}

def lineSub (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (W : Submodule ℂ M) :
    Submodule ℂ (TensorProduct ℂ M (Fock n)) :=
  khwSub ε (diagE ε (eT E) cpT cmT) (gaW ε lam) ⊓ tensFock W ⊓ physicalSubspace ε

end ReciprocityTheory.ChartRestriction.DS.TRGap
