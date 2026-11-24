module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix GlobalTheory.LKTrip Finset

namespace GlobalTheory.SigDiag

theorem eigenvalues_multiset_eq {n : ℕ} (r : Fin n → ℝ)
    (hA : (Matrix.diagonal (fun i => ((r i : ℝ) : ℂ))).IsHermitian) :
    Multiset.map hA.eigenvalues univ.val = Multiset.map r univ.val := by
  have h3 := hA.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod] at h3
  · have h4 := congrArg (Multiset.map Complex.re) h3
    simp only [Polynomial.roots_X_sub_C, Multiset.map_map] at h4
    simpa [Function.comp_def, Multiset.bind_singleton] using h4.symm
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

theorem card_subtype_eq_of_multiset {n : ℕ} {f g : Fin n → ℝ}
    (h : Multiset.map f univ.val = Multiset.map g univ.val) (P : ℝ → Prop) [DecidablePred P] :
    Fintype.card {i // P (f i)} = Fintype.card {i // P (g i)} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have e : ∀ k : Fin n → ℝ, (univ.filter fun i => P (k i)).card =
      Multiset.countP P (Multiset.map k univ.val) := by
    intro k
    rw [Multiset.countP_map, Finset.card_def, Finset.filter_val]
  rw [e f, e g, h]

end GlobalTheory.SigDiag

namespace GlobalTheory.LKTrip

theorem sigPosH_sigNegH_diagonal : ∀ (n : ℕ) (r : Fin n → ℝ)
    (hA : (Matrix.diagonal (fun i => ((r i : ℝ) : ℂ))).IsHermitian),
    sigPosH hA = Fintype.card {i // 0 < r i} ∧ sigNegH hA = Fintype.card {i // r i < 0} := by
  intro n r hA
  have h := GlobalTheory.SigDiag.eigenvalues_multiset_eq r hA
  exact ⟨GlobalTheory.SigDiag.card_subtype_eq_of_multiset h (fun x => 0 < x),
    GlobalTheory.SigDiag.card_subtype_eq_of_multiset h (fun x => x < 0)⟩

end GlobalTheory.LKTrip
