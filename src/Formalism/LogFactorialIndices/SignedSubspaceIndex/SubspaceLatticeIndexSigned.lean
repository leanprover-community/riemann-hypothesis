module

public import Formalism.LogFactorialIndices.StatementIdx
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxBase
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Module
open scoped Pointwise

namespace Formalism.LatticeIndexTer.LatticeIndexValuation

theorem length_map_inj {O Y X : Type} [CommRing O] [AddCommGroup Y] [Module O Y]
    [AddCommGroup X] [Module O X] (ι : Y →ₗ[O] X) (hι : Function.Injective ι)
    (P Q : Submodule O Y) :
    Module.length O (P ⧸ Q.comap P.subtype) =
      Module.length O (P.map ι ⧸ (Q.map ι).comap (P.map ι).subtype) := by
  have e : (Q.comap P.subtype).map (Submodule.equivMapOfInjective ι hι P).toLinearMap =
      (Q.map ι).comap (P.map ι).subtype := by
    ext ⟨z, hz⟩
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨⟨w, hw⟩, hwQ, hwe⟩
      refine ⟨w, hwQ, ?_⟩
      have := congrArg Subtype.val hwe
      first
        | exact this
        | simpa using this
    · rintro ⟨w, hwQ, hwe⟩
      refine ⟨⟨y, hy⟩, ?_, ?_⟩
      · have : w = y := hι hwe
        simpa [this] using hwQ
      · ext
        rfl
  exact (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective ι hι P) e).length_eq

end Formalism.LatticeIndexTer.LatticeIndexValuation

namespace Formalism.LatticeIndexTer.LatticeIndexValuation

section Sub

variable {O K X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X]
  [IsScalarTower O K X]

theorem isLat_comap (A : Submodule O X) (hA : IsLat O K X A) (W : Submodule K X) :
    IsLat O K W (A.comap ((W.subtype).restrictScalars O)) := by
  let ι : W →ₗ[O] X := (W.subtype).restrictScalars O
  have hι : Function.Injective ι := Subtype.val_injective
  constructor
  · have : Module.Finite O A := Module.Finite.iff_fg.mpr hA.1
    have hle : (A.comap ι).map ι ≤ A := Submodule.map_comap_le ι A
    have : IsNoetherian O ((A.comap ι).map ι) := isNoetherian_of_le hle
    have hfg : ((A.comap ι).map ι).FG := Module.Finite.iff_fg.mp inferInstance
    exact Submodule.fg_of_fg_map_injective ι hι hfg
  · rw [eq_top_iff]
    rintro w -
    obtain ⟨d, hd, hdw⟩ := LatticeIndexLength.exists_smul_mem_of_span (K := K) A hA.2 (w : X)
    have hdK : algebraMap O K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hd
    have hmem : d • w ∈ Submodule.span K (A.comap ι : Set W) := by
      apply Submodule.subset_span
      show ((d • w : W) : X) ∈ A
      rw [Submodule.coe_smul_of_tower]
      exact hdw
    have hw : w = (algebraMap O K d)⁻¹ • (d • w) := by
      rw [← algebraMap_smul K d w, smul_smul, inv_mul_cancel₀ hdK, one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ hmem

end Sub

end Formalism.LatticeIndexTer.LatticeIndexValuation

namespace Formalism.LatticeIndexTer

open LatticeIndexValuation

end Formalism.LatticeIndexTer
