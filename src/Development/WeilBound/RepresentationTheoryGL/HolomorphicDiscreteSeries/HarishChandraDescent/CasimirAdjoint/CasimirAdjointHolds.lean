module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Commutant
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset Matrix

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace CasimirAdjoint

theorem ent {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (g * Matrix.single a b (1 : ℂ) * g⁻¹ : Matrix (Fin n) (Fin n) ℂ) c d = g c a * g⁻¹ b d := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, ite_mul]

private theorem reorder_lemma {ι X : Type} [Fintype ι] [AddCommMonoid X] (G : ι → ι → ι → ι → X) :
    ∑ x, ∑ y, ∑ z, ∑ w, G x y z w = ∑ z, ∑ w, ∑ x, ∑ y, G x y z w := by
  calc ∑ x, ∑ y, ∑ z, ∑ w, G x y z w = ∑ x, ∑ z, ∑ y, ∑ w, G x y z w :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, ∑ w, G x y z w := Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ w, ∑ y, G x y z w :=
        Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ z, ∑ w, ∑ x, ∑ y, G x y z w :=
        Finset.sum_congr rfl fun z _ => Finset.sum_comm

theorem reorder {ι X : Type} [Fintype ι] [AddCommMonoid X] (F : ι → ι → ι → ι → ι → ι → X) :
    ∑ a, ∑ b, ∑ e, ∑ f, ∑ c, ∑ d, F a b c d e f = ∑ c, ∑ d, ∑ e, ∑ f, ∑ a, ∑ b, F a b c d e f := by
  calc ∑ a, ∑ b, ∑ e, ∑ f, ∑ c, ∑ d, F a b c d e f
        = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, F a b c d e f :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          reorder_lemma (fun e f c d => F a b c d e f)
    _ = ∑ c, ∑ d, ∑ a, ∑ b, ∑ e, ∑ f, F a b c d e f :=
        reorder_lemma (fun a b c d => ∑ e, ∑ f, F a b c d e f)
    _ = ∑ c, ∑ d, ∑ e, ∑ f, ∑ a, ∑ b, F a b c d e f :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
          reorder_lemma (fun a b e f => F a b c d e f)

end CasimirAdjoint

open CasimirAdjoint in
theorem casimir_adjoint_holds : CasAd := by
  intro n M _ _ E g hg
  have h : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  have key : ∀ c d e f : Fin n, ∑ a, ∑ b, g c a * g⁻¹ b d * (g e b * g⁻¹ a f) =
      (1 : Matrix (Fin n) (Fin n) ℂ) c f * (1 : Matrix (Fin n) (Fin n) ℂ) e d := by
    intro c d e f
    rw [← h, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  simp only [actM, casimir, ent, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  refine (reorder (fun a b c d e f => (g c a * g⁻¹ b d * (g e b * g⁻¹ a f)) • (E c d * E e f))).trans ?_
  simp only [← Finset.sum_smul, key, Matrix.one_apply, ite_mul, one_mul, zero_mul, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
