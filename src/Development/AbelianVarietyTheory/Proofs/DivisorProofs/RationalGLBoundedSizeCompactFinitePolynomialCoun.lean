module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalBoundedInfiniteCompactFinitePolyCountStatement
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem ratGL_bounded_count : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ m : ℕ, ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.Finite ∧ ({γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  intro E _ _ _ a
  obtain ⟨m, hm⟩ := GlobalTheory.T.rational_boundedInfinite_compactFinite_polyCount E
  refine ⟨m * (a * a), fun Kf hKf => ?_⟩
  let Kf' : Set (Af E) := ⋃ i : Fin a, ⋃ j : Fin a, (fun g : GL (Fin a) (Af E) => g.val i j) '' Kf
  have hc : IsCompact Kf' := by
    refine isCompact_iUnion fun i => isCompact_iUnion fun j => hKf.image ?_
    exact (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Af E))).matrix_elem i j
  obtain ⟨C, hC0, hC⟩ := hm Kf' hc
  refine ⟨C ^ (a * a), pow_nonneg hC0 _, fun T hT => ?_⟩
  obtain ⟨hNf, hNc⟩ := hC T hT
  let N : Set E := {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf'}
  let S : Set (GL (Fin a) E) := {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}
  change S.Finite ∧ (S.ncard : ℝ) ≤ C ^ (a * a) * T ^ (m * (a * a))
  have hsub : ∀ γ ∈ S, ∀ i j, γ.val i j ∈ N := by
    intro γ hγ i j
    obtain ⟨h1, h2⟩ := hγ
    refine ⟨?_, ?_⟩
    · have he : pInf E (algebraMap E (Ad E) (γ.val i j)) = (toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val) i j := rfl
      rw [he]
      exact ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i)).trans h1
    · exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨_, h2, rfl⟩⟩⟩
  classical
  let F : Finset E := hNf.toFinset
  let P : Finset (Fin a → Fin a → E) := Fintype.piFinset fun _ => Fintype.piFinset fun _ => F
  let f : GL (Fin a) E → (Fin a → Fin a → E) := fun γ => γ.val
  have hf : Function.Injective f := fun x y h => Units.ext h
  have himg : f '' S ⊆ (P : Set (Fin a → Fin a → E)) := by
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [P, F, Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun i j => hsub γ hγ i j
  have hSfin : S.Finite := Set.Finite.of_finite_image ((P.finite_toSet).subset himg) hf.injOn
  refine ⟨hSfin, ?_⟩
  have hcardP : P.card = (F.card ^ a) ^ a := by
    simp [P, Fintype.card_piFinset, Finset.prod_const]
  have hS : S.ncard ≤ (F.card ^ a) ^ a := by
    rw [← Set.ncard_image_of_injective S hf, ← hcardP, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard himg P.finite_toSet
  have hF : (F.card : ℝ) ≤ C * T ^ m := by
    rw [← Set.ncard_eq_toFinset_card N hNf]; exact hNc
  calc (S.ncard : ℝ) ≤ ((F.card ^ a) ^ a : ℕ) := by exact_mod_cast hS
    _ = (F.card : ℝ) ^ (a * a) := by push_cast; rw [← pow_mul]
    _ ≤ (C * T ^ m) ^ (a * a) := pow_le_pow_left₀ (Nat.cast_nonneg _) hF _
    _ = C ^ (a * a) * T ^ (m * (a * a)) := by rw [mul_pow, ← pow_mul]

end GlobalTheory
