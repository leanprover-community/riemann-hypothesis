module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ShiftMap
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

theorem UpperTheory.finite_translates_matrix_coefficient :
    ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
          (p : G →* H), Continuous p → ∀ f : H → ℂ, Continuous f →
          FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : G => fun z : H => f ((p k)⁻¹ * z))) →
          ∃ (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ), Continuous ρ ∧
            ∀ x : G →₀ ℂ, (x.sum fun k c => c • ρ k) = 0 → ∀ z, (x.sum fun k c => c * f ((p k)⁻¹ * z)) = 0 :=
  _root_.UpperTheory.Reformulated.B.ShiftMap.finite_translates_matrix_coefficient
