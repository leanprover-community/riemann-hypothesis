module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.avgMap :
    AvgMap := by
  intro G _ _ H U Z W X _ _ _ _ _ _ _ _ ρ κ η Φ ev ψ hΦ hev hinj hψ hne
  haveI := Fintype.ofFinite G
  refine ⟨∑ g : G, (ρ g⁻¹).comp (Φ.comp (ψ.comp (η g))), ?_, ?_⟩
  · obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (LinearMap.ext h)
    intro h0
    have h1 := congrArg (fun L => ev (L x)) h0

    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum,
    LinearMap.zero_apply, map_zero] at h1
    have key : ∀ g : G, ev (ρ g⁻¹ (Φ (ψ (η g x)))) = if g ∈ H then ev (Φ (ψ x)) else 0 := by
      intro g
      split_ifs with hg
      · have e1 := hψ ⟨g, hg⟩ x
        have e2 := hΦ ⟨g, hg⟩ (ψ x)
        simp only at e1 e2
        rw [e1, e2, Representation.inv_self_apply]
      · exact hev g⁻¹ (by simpa using hg) _
    rw [Finset.sum_congr rfl (fun g _ => key g), Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const] at h1
    have hc : (Finset.univ.filter (· ∈ H)).card ≠ 0 := by
      rw [← Nat.pos_iff_ne_zero, Finset.card_pos]
      exact ⟨1, by simp [H.one_mem]⟩
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact hc (by exact_mod_cast h1)
    · exact hx (hinj _ h1)
  · intro k x

    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    refine Fintype.sum_equiv (Equiv.mulRight k) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulRight, map_mul, Module.End.mul_apply, mul_inv_rev,
      Representation.self_inv_apply]
