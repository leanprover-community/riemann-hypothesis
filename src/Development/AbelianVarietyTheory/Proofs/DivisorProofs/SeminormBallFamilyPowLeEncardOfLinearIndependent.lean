module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBallFamMonoNegAdd
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

@[expose] public section

open Filter Topology
open GlobalTheory GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem isBallFam_pow_le_encard :
    ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ (r Q : ℕ) (R : ℝ)
      (v : Fin r → G), 0 ≤ R → LinearIndependent ℤ v → (∀ j, v j ∈ B R) →
      ((Q ^ r : ℕ) : ℕ∞) ≤ (B (r * Q * R)).encard := by
  classical
  intro G _ Λ B hB r Q R v hR hv hvB
  obtain ⟨hmono, -, hadd⟩ := isBallFam_mono_neg_add G Λ B hB
  let f : (Fin r → Fin Q) → G := fun c => ∑ j, ((c j : ℕ) • v j)

  have hterm : ∀ (n : ℕ) (j : Fin r), n • v j ∈ B (n * R) := by
    intro n j
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa using hB.zero_mem 0 le_rfl
    · exact (hB.nsmul_iff n R (v j) hn (hB.subset R (hvB j))).2 (hvB j)
  have hsum : ∀ (c : Fin r → Fin Q) (s : Finset (Fin r)),
      ∑ j ∈ s, ((c j : ℕ) • v j) ∈ B (∑ j ∈ s, ((c j : ℕ) : ℝ) * R) := by
    intro c s
    induction s using Finset.induction_on with
    | empty => simpa using hB.zero_mem 0 le_rfl
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact hadd _ _ _ _ (hterm _ a) ih
  have hmem : ∀ c, f c ∈ B (r * Q * R) := by
    intro c
    refine hmono _ _ ?_ (hsum c Finset.univ)
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ hR
    calc (∑ j, ((c j : ℕ) : ℝ)) ≤ ∑ _j : Fin r, (Q : ℝ) :=
          Finset.sum_le_sum fun j _ => by exact_mod_cast (c j).isLt.le
      _ = r * Q := by simp
  have hinj : Function.Injective f := by
    intro c c' h
    have h0 : ∑ j, (((c j : ℕ) : ℤ) - ((c' j : ℕ) : ℤ)) • v j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, natCast_zsmul]
      exact sub_eq_zero.mpr h
    have := Fintype.linearIndependent_iff.1 hv _ h0
    funext j
    have hj := this j
    exact Fin.ext (by omega)
  have hsub : ((Finset.univ.image f : Finset G) : Set G) ⊆ B (r * Q * R) := by
    intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨c, rfl⟩ := hx
    exact hmem c
  calc ((Q ^ r : ℕ) : ℕ∞) = ((Finset.univ.image f).card : ℕ∞) := by
        rw [Finset.card_image_of_injective _ hinj]; simp
    _ = ((Finset.univ.image f : Finset G) : Set G).encard := (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ (B (r * Q * R)).encard := Set.encard_le_encard hsub

end GlobalTheory.VolBr
