module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointIntertwinerDiscreteSeriesDescends
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

theorem _root_.GlobalTheory.T.adjoint_intertwiner_discreteSeries_descends : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : T.G →* (H →L[ℂ] H)), (∀ g x, ‖ρ g x‖ = ‖x‖) → ∀ S : D.U.H →L[ℂ] H, (∀ g x, ρ g (S x) = S (D.U.π g x)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : V →ₗ[ℂ] H) (act : Mat p q →ₗ[ℂ] Module.End ℂ V), (∀ P, KFin T (fun g => ρ g) (ι P)) → (∀ Y ∈ upq p q, ∀ P, HasDerivAt (fun t : ℝ => ρ (T.expt (t • Y)) (ι P)) (ι (act Y P)) 0) → ∃ φ : V →ₗ[ℂ] D.HK.V, (∀ P x, inner ℂ x (D.ι (φ P)) = inner ℂ (S x) (ι P)) ∧ ∀ Z P, φ (act Z P) = D.HK.act Z (φ P) := by
  first | exact @GlobalTheory.AdjDescent.adjoint_descends | exact GlobalTheory.AdjDescent.adjoint_descends | (intros; apply GlobalTheory.AdjDescent.adjoint_descends <;> assumption)
