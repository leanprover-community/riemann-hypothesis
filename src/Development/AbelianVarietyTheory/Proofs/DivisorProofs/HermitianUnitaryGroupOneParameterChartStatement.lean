module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianUnitaryGroupOneParameterChart
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix
open scoped Topology

theorem _root_.GlobalTheory.T.hermitian_unitary_group_one_parameter_chart : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), Hᴴ = H → IsUnit H.det →
    ∀ (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d), Function.Injective j →
      (∀ a, a ∉ Set.range j → Z a = 0) → (∀ a, (Z a)ᴴ * H + H * Z a = 0) →
      LinearIndependent ℝ (fun i => Z (j i)) →
      (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) →
      ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ g ∈ V, gᴴ * H * g = H → g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  first | exact @GlobalTheory.UnitaryGroupChart.unitary_chart | exact GlobalTheory.UnitaryGroupChart.unitary_chart | (intros; apply GlobalTheory.UnitaryGroupChart.unitary_chart <;> assumption)
