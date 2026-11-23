module

public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Global

open NumberField

def FirstInequality.{u} : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)],
    (Module.finrank K L : ℕ∞) ≤ ENat.card (IdeleClassGroup K ⧸ (ideleClassNorm K L).range)

section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem ideleClassNorm_range_eq_top_iff :
    (ideleClassNorm K L).range = ⊤ ↔
      (ideleNorm K L).range ⊔ (IdeleGroup.diagonal K).range = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro x _
    obtain ⟨c, hc⟩ := (MonoidHom.mem_range).1 (h ▸ Subgroup.mem_top (IdeleClassGroup.mk K x))
    obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective L c
    rw [ideleClassNorm_mk] at hc
    have hd : (ideleNorm K L y)⁻¹ * x ∈ (IdeleGroup.diagonal K).range :=
      QuotientGroup.eq.1 hc
    have : x = ideleNorm K L y * ((ideleNorm K L y)⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup ⟨y, rfl⟩ hd
  · intro h
    rw [eq_top_iff]
    intro c _
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
    obtain ⟨_, ⟨y, rfl⟩, z, hz, hyz⟩ := Subgroup.mem_sup.1 (h ▸ Subgroup.mem_top x)
    refine ⟨IdeleClassGroup.mk L y, ?_⟩
    rw [ideleClassNorm_mk, ← hyz]
    refine QuotientGroup.eq.2 ?_
    simpa using hz

end

section

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

theorem FirstInequality.finrank_eq_one_of_range_eq_top (hFI : FirstInequality.{u})
    (h : (ideleClassNorm K L).range = ⊤) : Module.finrank K L = 1 := by
  have hle := hFI K L
  rw [h] at hle
  have := QuotientGroup.subsingleton_quotient_top (G := IdeleClassGroup K)
  have h1 : ENat.card (IdeleClassGroup K ⧸ (⊤ : Subgroup (IdeleClassGroup K))) ≤ 1 :=
    (ENat.card_le_one_iff_subsingleton _).2 inferInstance
  have h2 : (Module.finrank K L : ℕ∞) ≤ 1 := hle.trans h1
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  have h3 : Module.finrank K L ≤ 1 := by exact_mod_cast h2
  omega

theorem FirstInequality.finrank_eq_one_of_sup_eq_top (hFI : FirstInequality.{u})
    (h : (ideleNorm K L).range ⊔ (IdeleGroup.diagonal K).range = ⊤) :
    Module.finrank K L = 1 :=
  hFI.finrank_eq_one_of_range_eq_top (ideleClassNorm_range_eq_top_iff.2 h)

end

end GroundTheory.Global
