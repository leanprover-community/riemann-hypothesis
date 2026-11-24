module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MonomialCountAndBinomialEstimates
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Polynomial.Pochhammer

@[expose] public section

namespace GlobalTheory

private lemma finite_setOf_finsupp_degree_eq (σ : Type) [Finite σ] [Nonempty σ] (e : ℕ) :
    Finite ↑{d : σ →₀ ℕ | d.degree = e} := by
  have := Fintype.ofFinite σ
  have h : Nat.card {d : σ →₀ ℕ // d.degree = e} ≠ 0 := by
    rw [_root_.GlobalTheory.natCard_degree_eq]
    have := Fintype.card_pos (α := σ)
    exact (Nat.choose_pos (by omega)).ne'
  exact Nat.finite_of_card_ne_zero h

private lemma finrank_homogeneousSubmodule_eq_choose (σ : Type) [Fintype σ] [Nonempty σ] (K : Type)
    [Field K] (e : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule σ K e) =
      (e + Fintype.card σ - 1).choose e := by
  have := finite_setOf_finsupp_degree_eq σ e
  have := Fintype.ofFinite ↑{d : σ →₀ ℕ | d.degree = e}
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K)
      {d : σ →₀ ℕ | d.degree = e}).finrank_eq,
    ← _root_.GlobalTheory.natCard_degree_eq σ e, Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]
  rfl

private lemma cast_choose_eq_eval_descPochhammer (m e : ℕ) (hm : 1 ≤ m) :
    (((e + m - 1).choose e : ℕ) : ℚ) = (Polynomial.C (1 / ((m - 1).factorial : ℚ)) *
      (descPochhammer ℚ (m - 1)).comp (Polynomial.X + Polynomial.C ((m - 1 : ℕ) : ℚ))).eval
        (e : ℚ) := by
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  have h1 : (e : ℚ) + ((m - 1 : ℕ) : ℚ) = ((e + (m - 1) : ℕ) : ℚ) := by push_cast; ring
  rw [h1, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    show e + m - 1 = e + (m - 1) by omega, Nat.choose_symm_add]
  have : ((m - 1).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem _root_.GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule :
    ∀ (σ : Type) [Finite σ] [Nonempty σ], ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] (e : ℕ),
      ((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) : ℕ) : ℚ) =
        Q.eval (e : ℚ) := by
  intro σ _ _
  have := Fintype.ofFinite σ
  refine ⟨Polynomial.C (1 / ((Fintype.card σ - 1).factorial : ℚ)) *
    (descPochhammer ℚ (Fintype.card σ - 1)).comp
      (Polynomial.X + Polynomial.C ((Fintype.card σ - 1 : ℕ) : ℚ)), fun K _ e => ?_⟩
  rw [finrank_homogeneousSubmodule_eq_choose σ K e]
  exact cast_choose_eq_eval_descPochhammer _ e Fintype.card_pos

end GlobalTheory
