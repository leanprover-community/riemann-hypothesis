module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.T2SpaceAfP
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

namespace UpperTheory.Gal.Spc

open UpperTheory.Gal.W2.Seed GlobalTheory.LKTrip GlobalTheory.UPel.HT

private def splitEquiv {X M : Type} [Group X] [Group M] (L : Loc X M) : X ≃* M × L.pr.ker where
  toFun g := (L.pr g, ⟨(L.loc (L.pr g))⁻¹ * g, by simp [MonoidHom.mem_ker, L.pr_loc]⟩)
  invFun x := L.loc x.1 * (x.2 : X)
  left_inv g := by simp
  right_inv x := by
    obtain ⟨m, h, hh⟩ := x
    have hh' : L.pr h = 1 := hh
    ext <;> simp [L.pr_loc, hh']
  map_mul' g h := by
    have hc : L.pr ((L.loc (L.pr g))⁻¹ * g) = 1 := by simp [L.pr_loc]
    have key := L.comm (L.pr h)⁻¹ _ hc
    rw [map_inv] at key
    refine Prod.ext (map_mul _ _ _) (Subtype.ext ?_)
    show (L.loc (L.pr (g * h)))⁻¹ * (g * h) = (L.loc (L.pr g))⁻¹ * g * ((L.loc (L.pr h))⁻¹ * h)
    rw [← mul_assoc ((L.loc (L.pr g))⁻¹ * g), ← key]
    simp [mul_assoc]

private theorem t2Space_hTGroup_gAf {p : ℕ} [Fact p.Prime] (G : HTGroup p) : T2Space G.GAf := by
  haveI := GlobalTheory.GfTop.t2Space_afP p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_locallyCompactSpace p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_totallyDisconnectedSpace p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_secondCountableTopology p
  exact (GlobalTheory.GfTop.upts_props G.star (AfP p)).2.1

theorem splitC : SplitC := by
  intro p _ G Lv k _ _ _ _ P L hcont hat Kw hKo hKc hF
  haveI := t2Space_hTGroup_gAf G
  have hker : IsClosed (L.pr.ker : Set G.GAf) := isClosed_singleton.preimage hcont
  refine ⟨inferInstance, inferInstance, inferInstance,
    ⟨splitEquiv L, fun g => (hat g).symm, Kw, (Lv.K : Subgroup G.GAf).subgroupOf L.pr.ker,
      hKo, hKc, ?_, ?_, ?_⟩, fun g h => rfl⟩
  · exact Lv.K.isOpen.preimage continuous_subtype_val
  · exact hker.isClosedEmbedding_subtypeVal.isCompact_preimage Lv.compact
  · ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨hF.2 g hg, ?_⟩
      show (L.loc (L.pr g))⁻¹ * g ∈ (Lv.K : Subgroup G.GAf)
      exact mul_mem (inv_mem (hF.1 _ (hF.2 g hg))) hg
    · rintro ⟨hm, hh⟩
      exact ⟨L.loc x.1 * (x.2 : G.GAf), mul_mem (hF.1 _ hm) hh,
        (splitEquiv L).apply_symm_apply x⟩

end UpperTheory.Gal.Spc
