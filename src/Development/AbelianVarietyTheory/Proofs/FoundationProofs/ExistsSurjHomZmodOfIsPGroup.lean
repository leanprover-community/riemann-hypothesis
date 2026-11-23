module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.PGroup
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
public import Mathlib.GroupTheory.IndexNormal
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
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
public import Mathlib.GroupTheory.Sylow

@[expose] public section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_surj_hom_zmod_of_isPGroup :
    ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] [Nontrivial G],
      IsPGroup p G → ∃ χ : G →* Multiplicative (ZMod p), Function.Surjective χ := by
  intro p hp G _ _ _ hG
  obtain ⟨n, hn, hc⟩ := hG.nontrivial_iff_card.1 inferInstance
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) p (n := m)
    (by rw [hc]; exact pow_dvd_pow p (Nat.le_succ m))
  have hi : K.index = p := by
    have := K.card_mul_index
    rw [hK, hc, pow_succ] at this
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos m) this
  haveI : K.Normal := Subgroup.normal_of_index_eq_minFac_card (by
    rw [hi, hc, hp.out.pow_minFac (Nat.succ_ne_zero m)])
  let e : (G ⧸ K) ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq (p := p) (by rw [← hi]; rfl) (by simp)
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' K), ?_⟩
  exact e.surjective.comp (QuotientGroup.mk'_surjective K)

end GlobalTheory.AlmostEt
