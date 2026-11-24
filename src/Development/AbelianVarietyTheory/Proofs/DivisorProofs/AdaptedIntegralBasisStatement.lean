module

public import Mathlib.RingTheory.LaurentSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedIntegralBasis
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

open PowerSeries

theorem _root_.GlobalTheory.T.exists_unit_matrix_adapted_to_flag : ∀ (F : Type) [Field F] (n R : ℕ) (W : Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)), Monotone W → ∃ g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ, ∀ (k : Fin (R + 1)) (j : Fin n), (j : ℕ) < Module.finrank (LaurentSeries F) (W k) → (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W k := by
  first | exact @GlobalTheory.LaurentFlagBasis.adapted_integral_basis | exact GlobalTheory.LaurentFlagBasis.adapted_integral_basis | (intros; apply GlobalTheory.LaurentFlagBasis.adapted_integral_basis <;> assumption)
