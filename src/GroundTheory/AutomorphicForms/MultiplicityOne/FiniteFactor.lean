module

public import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection
public import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay

@[expose] public section

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

set_option linter.unusedSectionVars false

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}



variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def fixedSubspace (σ : UnitaryRep (normOneGL (K := K) (n := n)) H) (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) :
    Submodule ℂ H where
  carrier := {v | ∀ u ∈ U, σ (finProj K n u) v = v}
  add_mem' hv hw u hu := by rw [map_add (f := _), hv u hu, hw u hu]
  zero_mem' u _ := map_zero _
  smul_mem' c v hv u hu := by rw [map_smul, hv u hu]

variable (σ : UnitaryRep (normOneGL (K := K) (n := n)) H) (U : Subgroup (AdelicGLn.FiniteAdelicGL K n))

variable {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]


end MultiplicityOne

end

end GroundTheory.Automorphic
