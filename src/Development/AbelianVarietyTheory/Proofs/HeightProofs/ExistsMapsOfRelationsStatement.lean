module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotMemOfMulExp
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMapsOfRelations
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos


theorem _root_.GlobalTheory.T.exists_maps_of_relations_alt : GlobalTheory.Published.HarishChandraModules → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Ltr ε → Module.End ℂ M) (m₀ : M),
    (∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), (∀ a, ∑ i, c i • wordV σ (u i) (w a) = 0) →
      ∑ i, c i • wordE τ (u i) m₀ = 0) →
    ∃ T : Fin d → (H →ₗ[ℂ] M), (∀ a v, IsKFin ε σ v → ∀ x, T a (ltrV σ x v) = τ x (T a v)) ∧ ∑ a, T a (w a) = m₀ ∧
      ∀ a v, IsKFin ε σ v → ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), T a v = ∑ i, c i • wordE τ (u i) m₀ := by
  first | exact @GlobalTheory.TypeSum.CoefClos.exists_maps_of_relations | exact GlobalTheory.TypeSum.CoefClos.exists_maps_of_relations | (intros; apply GlobalTheory.TypeSum.CoefClos.exists_maps_of_relations <;> assumption)
