module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstSubstitutionOfHolomorphicFamilies
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

open Filter Topology

theorem _root_.GlobalTheory.T.exists_const_substitution_of_holomorphic_families' : ∀ (L D : Type) [Countable D] (g : ℕ) (act : D → L → L) (U : Set ℂ) (s s' : ℂ → L → Fin g → ℂ), IsOpen U → IsPreconnected U → U.Nonempty → (∀ a, DifferentiableOn ℂ (fun w => s w a) U) → (∀ a, DifferentiableOn ℂ (fun w => s' w a) U) → (∀ w ∈ U, ∃ δ, ∀ a, s' w a = s w (act δ a)) → ∃ δ, ∀ w ∈ U, ∀ a, s' w a = s w (act δ a) := by
  first | exact @GlobalTheory.exists_const_substitution_of_holomorphic_families | exact GlobalTheory.exists_const_substitution_of_holomorphic_families | (intros; apply GlobalTheory.exists_const_substitution_of_holomorphic_families <;> assumption)
