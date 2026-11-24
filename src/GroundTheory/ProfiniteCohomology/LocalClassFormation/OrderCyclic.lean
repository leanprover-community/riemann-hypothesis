module

public import GroundTheory.TateCohomology.TateLow
public import GroundTheory.LocalFields.CompleteTrivial
public import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.LocalField.Basic
public import GroundTheory.LocalFields.HerbrandLocal
public import GroundTheory.TateCohomology.Herbrand
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

section Bridge

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem galUnits_norm_apply (x : Additive Lˣ) :
    (galUnits.{u} K L).ρ.norm x =
      Additive.ofMul (GroundTheory.LocalField.tateNorm Gal(L/K) Lˣ (Additive.toMul x)) := by
  rw [Representation.norm, LinearMap.sum_apply, GroundTheory.LocalField.tateNorm_apply, ofMul_prod]
  rfl


omit [FiniteDimensional K L] in
theorem mem_invariants_galUnits_iff (x : Additive Lˣ) :
    x ∈ (galUnits.{u} K L).ρ.invariants ↔
      Additive.toMul x ∈ GroundTheory.LocalField.invariants Gal(L/K) Lˣ :=
  Iff.rfl

def invariantsGalUnitsEquiv :
    (galUnits.{u} K L).ρ.invariants ≃ GroundTheory.LocalField.invariants Gal(L/K) Lˣ where
  toFun x := ⟨Additive.toMul x.1, (mem_invariants_galUnits_iff K L x.1).1 x.2⟩
  invFun y := ⟨Additive.ofMul y.1, (mem_invariants_galUnits_iff K L _).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def tateZeroGalUnitsEquiv :
    ((galUnits.{u} K L).ρ.invariants ⧸ GroundTheory.GroupCoh.normRangeInvariants (galUnits.{u} K L)) ≃
      GroundTheory.LocalField.TateZero Gal(L/K) Lˣ :=
  Quotient.congr (invariantsGalUnitsEquiv K L) fun a b => by
    rw [Submodule.quotientRel_def, QuotientGroup.leftRel_apply,
      GroundTheory.GroupCoh.mem_normRangeInvariants_iff, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨m, hm⟩
      refine ⟨(Additive.toMul (α := Lˣ) m)⁻¹, ?_⟩
      rw [galUnits_norm_apply] at hm
      have h := congrArg Additive.toMul hm
      simp only [toMul_ofMul] at h
      rw [map_inv, h]
      simp [invariantsGalUnitsEquiv, div_eq_mul_inv, mul_comm]
    · rintro ⟨y, hy⟩
      refine ⟨Additive.ofMul (α := Lˣ) y⁻¹, ?_⟩
      rw [galUnits_norm_apply, toMul_ofMul, map_inv, hy]
      simp [invariantsGalUnitsEquiv, mul_comm]
      rfl

end Bridge

section Cyclic

variable {K L : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

theorem natCard_groupCohomology_two_galUnits_of_isCyclic [IsCyclic Gal(L/K)] :
    Nat.card (groupCohomology (galUnits.{u} K L) 2) = Module.finrank K L := by
  classical
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let e : groupCohomology (galUnits.{u} K L) 2 ≅
      (GroundTheory.GroupCoh.tateZeroFunctor (R := ULift.{u} ℤ) (G := Gal(L/K))).obj (galUnits.{u} K L) :=
    ((TateCohomology.isoGroupCohomology 2).app (galUnits.{u} K L)).symm ≪≫
      GroundTheory.GroupCoh.tateCohomologyPeriodicIso (galUnits.{u} K L) hσ 0 ≪≫
      (GroundTheory.GroupCoh.tateCohomologyZeroIso (R := ULift.{u} ℤ) (G := Gal(L/K))).app (galUnits.{u} K L)
  rw [Nat.card_congr e.toLinearEquiv.toEquiv]
  rw [← GroundTheory.LocalField.natCard_tateZero_units (K := K) (L := L)]
  exact Nat.card_congr (tateZeroGalUnitsEquiv K L)

end Cyclic

end GroundTheory.ProfCoh
