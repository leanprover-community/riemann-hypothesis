module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.CuspDown

theorem exists_restrict : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt (p := p) (j x)) → ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x) := by
  intro Ω _ _ _ p _ A Ωl _ _ hC j hA g
  haveI : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hC
  letI : Algebra Ω Ωl := j.toAlgebra
  haveI : IsScalarTower ℚ Ω Ωl := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ Ωl), eq_ratCast (algebraMap ℚ Ω), map_ratCast]
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let gq : Ωl ≃ₐ[ℚ] Ωl := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun x => by
    simp only [eq_ratCast, AlgEquiv.coe_toRingEquiv, RingEquiv.coe_toEquiv, AlgEquiv.coe_ringEquiv]
    exact map_ratCast g x)
  have hc : ∀ x, g (j x) = j (gq.restrictNormal Ω x) := fun x => by
    have := AlgEquiv.restrictNormal_commutes gq Ω x
    rw [RingHom.algebraMap_toAlgebra] at this
    rw [this]; rfl
  refine ⟨gq.restrictNormal Ω, fun x => ?_, hc⟩
  rw [hA, hA, ← hc]
  constructor
  · intro h
    have := GlobalTheory.K5.Basic.isInt_gal g.symm h
    rwa [AlgEquiv.symm_apply_apply] at this
  · exact GlobalTheory.K5.Basic.isInt_gal g

end GlobalTheory.CuspDown
