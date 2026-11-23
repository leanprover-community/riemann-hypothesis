module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler

theorem exists_finset_cover_units : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∃ R : Finset (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) = 1) → ∃ r ∈ R, r⁻¹ * y ∈ hatOUnits c := by
  classical
  intro E _ _ c hc
  let U : Subgroup (Af E)ˣ := (PicFin.intR E).toSubmonoid.units
  have h1 : ((hatOUnits c).subgroupOf U).FiniteIndex := PicFin.finiteIndex_units hc
  have h2 : Finite (U ⧸ (hatOUnits c).subgroupOf U) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (U ⧸ (hatOUnits c).subgroupOf U)
  refine ⟨Finset.univ.image fun q : U ⧸ (hatOUnits c).subgroupOf U => (q.out : U).1, fun y hy => ?_⟩
  have hyU : y ∈ U := (Submonoid.mem_units_iff _ _).2
    ⟨fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hy v).le,
     fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      (by rw [inv_coord, map_inv₀, hy v, inv_one])⟩
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk ⟨y, hyU⟩)), ?_⟩
  have h3 := (QuotientGroup.eq (s := (hatOUnits c).subgroupOf U)).1
    (QuotientGroup.out_eq' (QuotientGroup.mk ⟨y, hyU⟩ : U ⧸ (hatOUnits c).subgroupOf U))
  exact Subgroup.mem_subgroupOf.1 h3

end GlobalTheory.CMVal.Euler
