module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.Basic.Real.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianQuadricAffineSubspaceResidueRingStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveAddCharInvolutionInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrimitiveTupleOfLinearIndependentFiniteRingStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardDependentVectorsAffineGramLeStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem ncard_extend_prim_one : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k + 1 ≤ n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B) (t : B), c t = t → |(Set.ncard {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ 3 * (q : ℝ) ^ n := by
  intro B _ _ c hc ω hω hf q hq hB k n hkn x hx g t ht
  obtain ⟨χ, hχ, hχc⟩ := GlobalTheory.T.exists_primitive_addChar_involution_invariant c hc ω hω hf
  have hZ := GlobalTheory.T.card_hermitianQuadric_affineSubspace_residueRing c hc ω hω hf q hq hB χ hχ hχc k n (by omega) x hx g t ht
  have hD := GlobalTheory.T.ncard_dependent_vectors_affine_gram_le c hc ω hω hf q hq hB k n (by omega) x hx g
  set S := {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hS
  set Z := {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hZd
  set D := {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} with hDd
  have h1 : S ⊆ Z := fun y hy => hy.2
  have h2 : Z ⊆ S ∪ D := by
    intro y hy
    by_cases hp : Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B)
    · exact Or.inl ⟨hp, hy⟩
    · right
      have hne : ¬ ∀ s : Fin (k + 1) → B,
          ∑ a, s a • (Fin.cons y x : Fin (k + 1) → Fin n → B) a = 0 → s = 0 :=
        fun h => hp (GlobalTheory.T.isPrimitiveTuple_of_linearIndependent_finite_ring c hc χ hχ (k + 1) n _ h)
      push Not at hne
      obtain ⟨s, hs, hs0⟩ := hne
      rw [Fin.sum_univ_succ] at hs
      simp only [Fin.cons_zero, Fin.cons_succ] at hs
      refine ⟨hy.1, s 0, ?_, fun i => -s i.succ, ?_⟩
      · intro h0
        apply hs0
        rw [h0, zero_smul, zero_add] at hs
        have h3 := hx.eq_zero c (fun i => s i.succ) hs
        funext i
        refine Fin.cases h0 (fun j => ?_) i
        exact congrFun h3 j
      · simp only [neg_smul, Finset.sum_neg_distrib]
        exact eq_neg_of_add_eq_zero_left hs
  have h3 : S.ncard ≤ Z.ncard := Set.ncard_le_ncard h1 (Set.toFinite _)
  have h4 : Z.ncard ≤ S.ncard + 2 * q ^ n :=
    (Set.ncard_le_ncard h2 (Set.toFinite _)).trans
      ((Set.ncard_union_le _ _).trans (Nat.add_le_add_left hD _))
  have h3' : (S.ncard : ℝ) ≤ Z.ncard := by exact_mod_cast h3
  have h4' : (Z.ncard : ℝ) ≤ S.ncard + 2 * (q : ℝ) ^ n := by exact_mod_cast h4
  have h5 : (0 : ℝ) ≤ (q : ℝ) ^ n := by positivity
  rw [abs_le] at hZ ⊢
  constructor <;> linarith [hZ.1, hZ.2]

end GlobalTheory.GramCount
