module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTowerKhatPadicSmulTorsionFreeStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryMonomialDegreeSubstExpansion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousPolyCoeffEqZero
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
import Mathlib.Tactic.Linter.Style
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

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem GlobalTheory.KZ.H3.coef_of_inv : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → ∀ (N w : ℕ) (b : X.Fn l) (c : Fin (w + 1) → X.Khat l), (∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i) → ∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b → ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k) := by
  intro Ω _ _ ε X l _ _ N w b c hb γ _ hinv
  obtain ⟨hslP, -, -, hev, -⟩ := mon_expand ℤ_[l] w
  have hk : ∀ (u : Fin 2 → ℤ_[l]) (k : Fin (w + 1)),
      (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0 ^ (k : ℕ) * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1 ^ (w - (k : ℕ)) =
        ∑ i, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) * (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) := by
    intro u k

    rw [← hev, mZl, ← Betti.eval_slP, hslP, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPolynomial.eval_C, hev]
  have key : ∀ u : Fin 2 → ℤ_[l], b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) •
      ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k) := by
    intro u
    rw [← congrFun hinv u]
    show X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (b (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)) = _

    rw [Betti.toGQ_sl, hb, map_sum]
    simp_rw [map_smul, hk, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have hz := GlobalTheory.homogeneous_poly_coeff_eq_zero l (X.Khat l)
    (fun a x ha hx => GlobalTheory.T.algebraicTowerKhat_padic_smul_torsionFree Ω ε X l a x ha hx) w
    (fun i => c i - ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k))
    (by intro u; simp_rw [smul_sub]; rw [Finset.sum_sub_distrib, ← hb u, ← key u, sub_self])
  intro i
  exact sub_eq_zero.1 (congrFun hz i)
