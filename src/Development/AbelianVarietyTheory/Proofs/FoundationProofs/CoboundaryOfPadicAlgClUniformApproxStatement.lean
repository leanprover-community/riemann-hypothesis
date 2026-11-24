module

public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryOfPadicAlgClUniformApprox
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

open scoped Matrix

theorem _root_.GlobalTheory.T.coboundary_of_padicAlgCl_uniform_approx : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) (S : Set Γ) (M : Γ → Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) (f : ℕ → Γ → Fin 2 → PadicAlgCl l) (y : Γ → Fin 2 → PadicAlgCl l), (∀ s i j, ‖M s i j‖ ≤ 1) → (∀ r, ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, f r s = M s *ᵥ v - v) → (∀ r s i, ‖y s i - f r s i‖ ≤ ‖((l : ℕ) : PadicAlgCl l) ^ r‖) → ∃ v : Fin 2 → PadicAlgCl l, ∀ s ∈ S, y s = M s *ᵥ v - v := by
  first | exact @GlobalTheory.UniformCoboundary.coboundary_of_padic_approx | exact GlobalTheory.UniformCoboundary.coboundary_of_padic_approx | (intros; apply GlobalTheory.UniformCoboundary.coboundary_of_padic_approx <;> assumption)
