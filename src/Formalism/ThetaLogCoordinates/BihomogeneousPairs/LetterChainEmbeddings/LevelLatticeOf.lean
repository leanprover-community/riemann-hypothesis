module

public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PairStep
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

lemma asm_num (p : ℕ) [Fact p.Prime] (a r : ℕ) (ha : 1 ≤ a) :
    r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h1 : (Nat.log p (2 * a) : ℝ) ≤ Real.logb p (8 * a + r) := by
    refine (Real.natLog_le_logb _ _).trans ?_
    apply Real.logb_le_logb_of_le hp
    · push_cast; linarith
    · push_cast; linarith
  have h2 : (Nat.log p (6 * a + r) : ℝ) ≤ Real.logb p (8 * a + r) := by
    refine (Real.natLog_le_logb _ _).trans ?_
    apply Real.logb_le_logb_of_le hp
    · push_cast; linarith
    · push_cast; linarith
  have h3 : ((r * Nat.log p (2 * a) + Nat.log p (6 * a + r) : ℕ) : ℝ) ≤ ((r : ℝ) + 1) * lgV2 p a r := by
    push_cast
    unfold lgV2
    have := mul_le_mul_of_nonneg_left h1 hr
    nlinarith
  exact_mod_cast h3.trans (Nat.le_ceil _)

lemma asm_chain (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]
    (M : ℕ → Submodule ℤ_[p] V) (u t : ℕ)
    (h : ∀ k < t, (∀ v ∈ M (k + 1), (p : ℚ_[p]) ^ u • v ∈ M k) ∧ (∀ v ∈ M k, (p : ℚ_[p]) ^ u • v ∈ M (k + 1))) :
    ∀ k ≤ t, (∀ v ∈ M k, (p : ℚ_[p]) ^ (k * u) • v ∈ M 0) ∧ (∀ v ∈ M 0, (p : ℚ_[p]) ^ (k * u) • v ∈ M k) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨i1, i2⟩ := ih (by omega)
    obtain ⟨s1, s2⟩ := h k (by omega)
    constructor
    · intro v hv
      have := i1 _ (s1 v hv)
      rwa [smul_smul, ← pow_add, ← Nat.succ_mul] at this
    · intro v hv
      have := s2 _ (i2 v hv)
      rwa [smul_smul, ← pow_add, add_comm u, ← Nat.succ_mul] at this

lemma asm_span (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]
    (A B : Submodule ℤ_[p] V) (K : ℕ) (h : ∀ v ∈ A, (p : ℚ_[p]) ^ K • v ∈ B) :
    Submodule.span ℚ_[p] (A : Set V) ≤ Submodule.span ℚ_[p] (B : Set V) := by
  have hp : ((p : ℚ_[p]) ^ K) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [Submodule.span_le]
  intro x hx
  have h1 : (p : ℚ_[p]) ^ K • x ∈ Submodule.span ℚ_[p] (B : Set V) := Submodule.subset_span (h x hx)
  have h2 := Submodule.smul_mem _ (((p : ℚ_[p]) ^ K)⁻¹) h1
  rwa [smul_smul, inv_mul_cancel₀ hp, one_smul] at h2

theorem LevelLattice_of : MidTop → MidPEq → JoinCondition → PlusCondition → Formalism.GM.M.LevelLattice := by
  intro hTop hPEq hTie hPlus p _ N r _ D a hOK hr ha hdeg hB hz hzP hYT hYU
  have hnum := asm_num p a r ha
  generalize ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊ = u at hnum ⊢
  have hT : HypJoin p (r := r) D := hYT
  have hU : HypU p (r := r) D := hYU
  obtain ⟨c1, c2⟩ := asm_chain p (fun k => Mid p (r := r) D k) u D.T.t
    (hTie p N r D a u hOK hr hdeg hz hT hnum) D.T.t le_rfl
  obtain ⟨q1, q2⟩ := hPlus p N r D a u hOK hr hdeg hB hzP hU hnum
  rw [← hTop p N r D, ← hPEq p N r D]
  have k1 : ∀ x ∈ Mid p (r := r) D D.T.t, (p : ℚ_[p]) ^ ((D.T.t + 1) * u) • x ∈ MidP p (r := r) D := by
    intro x hx
    have := q1 _ (c1 x hx)
    rwa [smul_smul, ← pow_add, add_comm u, ← Nat.succ_mul] at this
  have k2 : ∀ x ∈ MidP p (r := r) D, (p : ℚ_[p]) ^ ((D.T.t + 1) * u) • x ∈ Mid p (r := r) D D.T.t := by
    intro x hx
    have := c2 _ (q2 x hx)
    rwa [smul_smul, ← pow_add, ← Nat.succ_mul] at this
  exact ⟨le_antisymm (asm_span p _ _ _ k1) (asm_span p _ _ _ k2), k1, k2⟩

end Formalism.InvariantFactorPaths.KP.LL
