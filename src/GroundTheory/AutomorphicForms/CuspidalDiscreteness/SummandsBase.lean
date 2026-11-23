module

public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Smoothing
public import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
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

@[expose] public section

open MeasureTheory Set Filter Topology Function

namespace GroundTheory.Automorphic

noncomputable section

namespace BanachRep

variable {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def comp (π : BanachRep G E) (f : G' →* G) (hf : Continuous f) : BanachRep G' E where
  toHom := π.toHom.comp f
  continuous_orbit' v := (π.continuous_orbit v).comp hf

end BanachRep

namespace CuspidalSpectrum

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}


variable (K n) in
def archP : archGroup K n →* Reduction.normOneGL (K := K) (n := n) :=
  (archProj (K := K) (n := n)).comp (archGroup K n).subtype

@[simp] theorem archimedeanProjection_apply (a : archGroup K n) :
    archP K n a = archProj K n (a : ArchUnits K n) := rfl

theorem continuous_archP : Continuous (archP K n) := by
  have hProj : Continuous (archProj (K := K) (n := n)) := by
    refine continuous_induced_rng.2 ?_
    change Continuous fun A : ArchUnits K n =>
      archIncl K n A * (Reduction.centralSection K n (Reduction.detModule K n (archIncl K n A)))⁻¹
    exact continuous_archIncl.mul
      ((Reduction.continuous_centralSection.comp
        (Reduction.continuous_detModule.comp continuous_archIncl)).inv)
  exact hProj.comp continuous_subtype_val

variable (μ : Measure (Reduction.normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
