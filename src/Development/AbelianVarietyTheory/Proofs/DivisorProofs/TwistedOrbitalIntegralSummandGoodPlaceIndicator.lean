module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Filter GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwOrbGood

theorem avg_const {H : Type} [Group H] (c : ℂ) : GlobalTheory.BCT.avg (fun _ : H => c) = c := by
  have h : GlobalTheory.BCT.rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold GlobalTheory.BCT.avg
  rw [h, Subgroup.index_top]
  have : (∑ᶠ q : H ⧸ (⊤ : Subgroup H), (fun _ : H => c) q.out) = c := by
    rw [finsum_eq_single (fun q : H ⧸ (⊤ : Subgroup H) => (fun _ : H => c) q.out) (QuotientGroup.mk 1)
      (fun q hq => absurd (by induction q using QuotientGroup.induction_on with | H a => exact QuotientGroup.eq.2 (Subgroup.mem_top _)) hq)]
  rw [this]; simp

theorem summand_goodplace : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (KH : Subgroup H) (δ : H), δ ∈ KH → cptPart (twCent (MonoidHom.id H) δ) ≤ KH → (∀ g : H, g⁻¹ * δ * g ∈ KH → ∃ t ∈ twCent (MonoidHom.id H) δ, t⁻¹ * g ∈ KH) → ∀ x : H, GlobalTheory.TwOrbConj.summand (MonoidHom.id H) KH δ ((KH : Set H).indicator 1) x = if ∃ t ∈ twCent (MonoidHom.id H) δ, ∃ k ∈ KH, x = t * k then 1 else 0 := by
  intro H _ _ _ KH δ hδ hc hg x
  split_ifs with hx
  · obtain ⟨t, ht, k, hk, rfl⟩ := hx
    have e : t * k = t * 1 * k := by group
    rw [e, GlobalTheory.TwOrbConj.summand_rep _ _ _ _ _ ht hk]
    unfold GlobalTheory.TwOrbConj.summand
    have hmap : KH.map (MulAut.conj (1 : H)).toMonoidHom = KH := GlobalTheory.TwOrbConj.map_conj_self KH KH.one_mem
    have hcT : cptPart (twCent (MonoidHom.id H) δ) ≤ twCent (MonoidHom.id H) δ := by
      unfold GlobalTheory.BCT.cptPart
      rw [Subgroup.closure_le]
      intro y hy; exact hy.1
    have hrel : (twCent (MonoidHom.id H) δ ⊓ KH.map (MulAut.conj (1 : H)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id H) δ)) = 1 := by
      rw [hmap, Subgroup.relIndex_eq_one]
      exact le_inf hcT hc
    have hfun : (fun k : KH => (KH : Set H).indicator (1 : H → ℂ) ((1 * (k : H))⁻¹ * δ * (MonoidHom.id H) (1 * (k : H))))
        = fun _ => 1 := by
      funext k
      rw [Set.indicator_of_mem]
      · rfl
      · simp only [one_mul, MonoidHom.id_apply]
        exact KH.mul_mem (KH.mul_mem (KH.inv_mem k.2) hδ) k.2
    rw [hrel, hfun, avg_const]; simp
  · unfold GlobalTheory.TwOrbConj.summand
    have hfun : (fun k : KH => (KH : Set H).indicator (1 : H → ℂ) ((x * (k : H))⁻¹ * δ * (MonoidHom.id H) (x * (k : H))))
        = fun _ => 0 := by
      funext k
      rw [Set.indicator_of_notMem]
      intro hm
      simp only [MonoidHom.id_apply] at hm
      obtain ⟨t, ht, htk⟩ := hg (x * k) hm
      apply hx
      refine ⟨t, ht, t⁻¹ * (x * k) * (k : H)⁻¹, KH.mul_mem htk (KH.inv_mem k.2), by group⟩
    rw [hfun, avg_const]; simp

end GlobalTheory.TwOrbGood
