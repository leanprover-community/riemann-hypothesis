module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedFamily
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

open Matrix

namespace GlobalTheory

theorem adapted_basis_extension (g r : ℕ) (I L : Submodule ℚ (Fin r → ℚ)) (hIL : I ≤ L)
    (hg : Module.finrank ℚ L = g) :
    ∃ rk : ℕ, rk ≤ g ∧ ∃ ε : Fin g → Fin r → ℚ, LinearIndependent ℚ ε ∧ (∀ i, ε i ∈ L) ∧
      (∀ i : Fin g, i.val < rk → ε i ∈ I) ∧
        ∀ x ∈ I, x ∈ Submodule.span ℚ (ε '' {i | i.val < rk}) := by
  first
  | exact @_root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family
  | exact _root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family
  | (apply _root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdaptedFamilyIwasawaDecomposition.exists_adapted_family ..)

end GlobalTheory
