module

public import GroundTheory.GlobalFields.IdeleGroups.LocalNorms
public import GroundTheory.GlobalFields.IdeleGroups.LocalNormsEverywhere
public import GroundTheory.GlobalFields.SecondInequality.Cyclic
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
public import GroundTheory.GlobalFields.HerbrandQuotients.CycTate
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action

@[expose] public section

namespace GroundTheory.Global

open NumberField GroundTheory.GroupCoh Module IsDedekindDomain AdeleBaseChange

universe u

section

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem mem_range_norm_of_diagonal_mem_range_ideleNorm [IsCyclic Gal(L/K)] {x : Kˣ}
    (hx : IdeleGroup.diagonal K x ∈ (ideleNorm K L).range) :
    x ∈ (Units.map (Algebra.norm K : L →* K)).range := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  obtain ⟨j, hj⟩ := hx
  set ρ := Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)
  set c : Additive (IdeleClassGroup L) := Additive.ofMul (IdeleClassGroup.mk L j)

  have hc : c ∈ (cycNorm ρ).ker := by
    rw [AddMonoidHom.mem_ker, cycNorm_apply]
    have h1 : ∏ g : Gal(L/K), g • IdeleClassGroup.mk L j = 1 := by
      rw [← ideleClassMap_ideleClassNorm, ideleClassNorm_mk, hj, IdeleClassGroup.mk_diagonal,
        map_one]
    simp only [ρ, c, Representation.ofMulDistribMulAction_apply_apply, toMul_ofMul]
    exact (ofMul_prod Finset.univ _).symm.trans (congrArg Additive.ofMul h1)

  have hsub : Subsingleton (CycTateNegOne ρ σ) :=
    (Nat.card_eq_one_iff_unique.1 (natCard_cycTateNegOne_ideleClassGroup σ hσ)).1
  have h0 : (QuotientAddGroup.mk ⟨c, hc⟩ : CycTateNegOne ρ σ) = 0 := Subsingleton.elim _ _
  obtain ⟨d, hd⟩ := AddMonoidHom.mem_range.1 ((KerModRange.mk_eq_zero_iff _).1 h0)
  obtain ⟨e, he⟩ := IdeleClassGroup.mk_surjective L (Additive.toMul d)
  rw [cycSubOne_apply, Representation.ofMulDistribMulAction_apply_apply] at hd
  have hjc : IdeleClassGroup.mk L j = IdeleClassGroup.mk L ((σ • e) / e) := by
    have := congrArg Additive.toMul hd
    simp only [c, toMul_sub, toMul_ofMul] at this
    rw [← this, ← he, map_div, smul_mk]

  obtain ⟨a, ha⟩ := QuotientGroup.eq.1 hjc.symm
  refine ⟨a, IdeleGroup.diagonal_injective K ?_⟩
  rw [← ideleNorm_diagonal, ha, map_mul, map_inv, map_div, ideleNorm_smul, div_self', inv_one,
    one_mul, hj]

theorem mem_range_norm_iff_diagonal_mem_range_ideleNorm [IsCyclic Gal(L/K)] (x : Kˣ) :
    x ∈ (Units.map (Algebra.norm K : L →* K)).range ↔
      IdeleGroup.diagonal K x ∈ (ideleNorm K L).range := by
  refine ⟨?_, mem_range_norm_of_diagonal_mem_range_ideleNorm⟩
  rintro ⟨a, rfl⟩
  exact ⟨IdeleGroup.diagonal L a, ideleNorm_diagonal a⟩

theorem mem_range_norm_iff_forall_local [IsCyclic Gal(L/K)] (x : Kˣ) :
    x ∈ (Units.map (Algebra.norm K : L →* K)).range ↔
      (∀ v, IdeleGroup.finiteProj v (IdeleGroup.diagonal K x) ∈
          (IdeleNorm.finiteLocalNorm L v).range) ∧
        ∀ v, IdeleGroup.infiniteProj v (IdeleGroup.diagonal K x) ∈
          (IdeleNorm.infiniteLocalNorm L v).range := by
  rw [mem_range_norm_iff_diagonal_mem_range_ideleNorm, IdeleNorm.mem_range_ideleNorm_iff_forall]

end

section Quadratic

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem isGalois_isCyclic_of_finrank_eq_two (h : finrank K L = 2) :
    IsGalois K L ∧ IsCyclic Gal(L/K) := by
  have : Algebra.IsQuadraticExtension K L := ⟨h⟩
  exact ⟨inferInstance, inferInstance⟩

theorem mem_range_norm_iff_diagonal_mem_range_ideleNorm_of_finrank_eq_two
    (h : finrank K L = 2) (x : Kˣ) :
    x ∈ (Units.map (Algebra.norm K : L →* K)).range ↔
      IdeleGroup.diagonal K x ∈ (ideleNorm K L).range := by
  obtain ⟨_, _⟩ := isGalois_isCyclic_of_finrank_eq_two h
  exact mem_range_norm_iff_diagonal_mem_range_ideleNorm x

theorem mem_range_norm_iff_forall_local_of_finrank_eq_two (h : finrank K L = 2) (x : Kˣ) :
    x ∈ (Units.map (Algebra.norm K : L →* K)).range ↔
      (∀ v, IdeleGroup.finiteProj v (IdeleGroup.diagonal K x) ∈
          (IdeleNorm.finiteLocalNorm L v).range) ∧
        ∀ v, IdeleGroup.infiniteProj v (IdeleGroup.diagonal K x) ∈
          (IdeleNorm.infiniteLocalNorm L v).range := by
  obtain ⟨_, _⟩ := isGalois_isCyclic_of_finrank_eq_two h
  exact mem_range_norm_iff_forall_local x

end Quadratic

end GroundTheory.Global
