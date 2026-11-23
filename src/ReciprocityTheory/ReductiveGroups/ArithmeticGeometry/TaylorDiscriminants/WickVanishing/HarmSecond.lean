module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB

theorem mvpoly_pderiv_comm {k σ : Type} [CommRing k] (i j : σ) (p : MvPolynomial σ k) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  have h : ⁅(MvPolynomial.pderiv i : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)), MvPolynomial.pderiv j⁆ =
      (0 : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)) := by
    apply MvPolynomial.derivation_ext
    intro n
    rw [Derivation.commutator_apply, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X, Pi.single_apply,
      Pi.single_apply]
    split_ifs <;> simp
  have h' := congrArg (fun D => D p) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h'
  exact sub_eq_zero.mp h'

theorem harmSecond_holds : HarmSecondSt := by
  intro k _ T _ r cc isX hcc hX n c hc P hP
  classical
  set S : (Σ τ : T, Fin (r τ)) → (Σ τ : T, Fin (r τ)) → MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k :=
    fun l l' => ∑ b : Fin n, MvPolynomial.pderiv (l, b) (MvPolynomial.pderiv (l', b) P) with hS
  have hsymm : ∀ l l', S l l' = S l' l := by
    intro l l'
    simp only [hS]
    exact Finset.sum_congr rfl fun b _ => mvpoly_pderiv_comm _ _ _
  have hzero1 : ∀ l l' : (Σ τ : T, Fin (r τ)), isX l.1 → l'.1 = cc l.1 → S l l' = 0 := by
    rintro ⟨σ, i⟩ ⟨σ', i'⟩ hXσ h
    dsimp only at h hXσ
    subst h
    exact hP σ hXσ i i'
  have hzero : ∀ l l' : (Σ τ : T, Fin (r τ)), l'.1 = cc l.1 → S l l' = 0 := by
    intro l l' h
    rcases hX l.1 with h1 | h1
    · exact hzero1 l l' h1 h
    · rw [hsymm]
      refine hzero1 l' l (by rw [h]; exact h1) ?_
      rw [h, hcc]
  have hterm : ∀ l l', MvPolynomial.C (c l l') * S l l' = 0 := by
    intro l l'
    by_cases h : l'.1 = cc l.1
    · rw [hzero l l' h, mul_zero]
    · rw [hc l l' h, map_zero, zero_mul]
  unfold secondOrder
  simp_rw [Fintype.sum_prod_type]
  simp only [apply_ite MvPolynomial.C, ite_mul, map_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  apply Finset.sum_eq_zero
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l' _
  rw [← Finset.mul_sum]
  exact hterm l l'

end ReciprocityTheory.ChartRestriction.G.TB
