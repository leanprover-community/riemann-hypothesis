module

public import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.LiftBoundOfHypotheses
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K]

def vge (v : AddValuation K (WithTop ℚ)) (a : ℝ) (x : K) : Prop := ((a : ℝ) : WithTop ℝ) ≤ vR v x

def vle (v : AddValuation K (WithTop ℚ)) (a : ℝ) (x : K) : Prop := vR v x ≤ ((a : ℝ) : WithTop ℝ)

def cge (v : AddValuation K (WithTop ℚ)) (a : ℝ) {σ : Type} (F : MvPolynomial σ K) : Prop :=
  ∀ α, vge v a (F.coeff α)

def vN (v : AddValuation K (WithTop ℚ)) (n : ℕ) : ℝ := (((v (n : K)).untopD 0 : ℚ) : ℝ)

def bge (v : AddValuation K (WithTop ℚ)) (a : ℝ) {σ : Type} (F : MvPolynomial σ K) : Prop :=
  ∀ α, vge v (a - vN v (fact α) / 2) (F.coeff α)

def dg {σ : Type} (f : (σ →₀ ℕ) → K) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials σ K).constr K fun α => monomial α (f α)

def ldeg {L : Type} {r : ℕ} (α : L × Fin r →₀ ℕ) (i : L) : ℕ := ∑ a : Fin r, α (i, a)

def vala {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L) (θ : ℝ)
    (F : MvPolynomial (L × Fin r) K) : Prop :=
  ((θ : ℝ) : WithTop ℝ) ≤ toR (valS sg S F)

def eOut {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out] (α : L × Fin r →₀ ℕ) :
    L × Fin r →₀ ℕ := α.filter fun x => out x.1

def eIn {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out] (α : L × Fin r →₀ ℕ) :
    L × Fin r →₀ ℕ := α.filter fun x => ¬ out x.1

def coefOut {L : Type} [DecidableEq L] {r : ℕ} (out : L → Prop) [DecidablePred out] (μ : L × Fin r →₀ ℕ)
    (F : MvPolynomial (L × Fin r) K) : MvPolynomial (L × Fin r) K :=
  ∑ α ∈ F.support, if eOut out α = μ then monomial (eIn out α) (F.coeff α) else 0

theorem dg_monomial {σ : Type} (f : (σ →₀ ℕ) → K) (α : σ →₀ ℕ) (c : K) :
    dg f (monomial α c) = monomial α (f α * c) := by
  have hb : (basisMonomials σ K) α = monomial α 1 := by simp [coe_basisMonomials]
  have h1 : dg f (monomial α 1) = monomial α (f α) := by rw [← hb, dg, Module.Basis.constr_basis]
  rw [show monomial α c = c • monomial α (1 : K) by rw [smul_monomial, smul_eq_mul, mul_one], map_smul, h1,
    smul_monomial, smul_eq_mul, mul_comm]

theorem coeff_dg {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) (α : σ →₀ ℕ) :
    (dg f F).coeff α = f α * F.coeff α := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial β c =>
    rw [dg_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem mem_PolK_iff {L : Type} {r : ℕ} (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) :
    F ∈ PolK K r d ↔ ∀ α ∈ F.support, ∀ i, ldeg α i = d i := by
  simp only [PolK, mem_restrictSupport_iff, Set.subset_def, Finset.mem_coe, Set.mem_setOf_eq, ldeg]

end Formalism.MainNotions.PlaneGram
