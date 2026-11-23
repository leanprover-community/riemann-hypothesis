module

public import GroundTheory.GlobalFields.SecondInequality.Statement
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
public import GroundTheory.GlobalFields.SecondInequality.PrimeDegree
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GroundTheory.Global

open NumberField Module IntermediateField

universe u

def SecondInequality.{v} : Prop :=
  ∀ (K L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)],
    ENat.card (IdeleClassGroup K ⧸ (ideleClassNorm K L).range) ≤ Module.finrank K L

theorem SecondInequalityRoots.index_le_of_finrank_eq (hR : SecondInequalityRoots.{u}) (n : ℕ) :
    ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)], finrank K L = n →
      (ideleClassNorm K L).range.index ≠ 0 ∧ (ideleClassNorm K L).range.index ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L _ _ _ _ _ _ _ hn
  have hn0 : 0 < n := hn ▸ finrank_pos
  by_cases h1 : n = 1
  ·
    have htop : (ideleClassNorm K L).range = ⊤ := by
      rw [eq_top_iff]
      intro c _
      have := pow_finrank_mem_range_ideleClassNorm (L := L) c
      rwa [hn, h1, pow_one] at this
    rw [htop, Subgroup.index_top]
    omega
  obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd h1
  have : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (L ≃ₐ[K] L) = n := by rw [IsGalois.card_aut_eq_finrank, hn]
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q (hcard ▸ hqn)

  let H : Subgroup (L ≃ₐ[K] L) := Subgroup.zpowers g
  have : H.Normal := ⟨fun a ha b ↦ by rwa [mul_comm_of_isCyclic b a, mul_inv_cancel_right]⟩
  let M : IntermediateField K L := fixedField H
  have hML : finrank M L = q := by
    rw [finrank_fixedField_eq_card, Nat.card_zpowers, hg]
  have hKM : finrank K M * q = n := by rw [← hML, finrank_mul_finrank, hn]
  have hm_lt : finrank K M < n := by
    have : 0 < finrank K M := finrank_pos
    calc finrank K M < finrank K M * 2 := by omega
      _ ≤ finrank K M * q := Nat.mul_le_mul_left _ hq.two_le
      _ = n := hKM

  have : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
  have : IsCyclic (L ≃ₐ[M] L) :=
    isCyclic_of_prime_card (p := q) (by rw [IsGalois.card_aut_eq_finrank, hML])
  have : IsGalois K M := IsGalois.of_fixedField_normal_subgroup H
  have : IsCyclic (M ≃ₐ[K] M) :=
    isCyclic_of_surjective _ (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := L))
  have hM := ih (finrank K M) hm_lt K M rfl
  have hL := hR.index_le_of_prime (K := M) (L := L) hq hML

  have hcomp : (ideleClassNorm K M).comp (ideleClassNorm M L) = ideleClassNorm K L :=
    MonoidHom.ext fun c ↦ ideleClassNorm_ideleClassNorm c
  have hrange : (ideleClassNorm K L).range =
      (ideleClassNorm M L).range.map (ideleClassNorm K M) := by
    rw [MonoidHom.map_range, hcomp]
  have := index_map_le (ideleClassNorm K M) hL.1 hM.1
  rw [hrange]
  refine ⟨this.1, this.2.trans ?_⟩
  rw [← hKM]
  exact Nat.mul_le_mul hM.2 hL.2

theorem SecondInequalityRoots.secondInequality (hR : SecondInequalityRoots.{u}) :
    SecondInequality.{u} := by
  intro K L _ _ _ _ _ _ _
  exact (enatCard_quotient_le_iff _ _).2 (hR.index_le_of_finrank_eq _ K L rfl)

end GroundTheory.Global
