module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

namespace GlobalTheory.CosetSumShift

theorem sum_shift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)),
    (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) →
    ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) →
    ∀ a ∈ box n R, ∑ b ∈ S, F (a + b) = ∑ b ∈ S, F b := by
  intro k _ _ _ _ n _ r R S hS huniq F hF a ha
  classical
  have hadd : ∀ {s : kˣ} {x y : n → k}, x ∈ box n s → y ∈ box n s → x + y ∈ box n s :=
    fun hx hy i _ => add_mem_cball (hx i trivial) (hy i trivial)
  have hneg : ∀ {s : kˣ} {x : n → k}, x ∈ box n s → -x ∈ box n s :=
    fun hx i _ => neg_mem_cball (hx i trivial)
  have hzero : (0 : n → k) ∈ box n r := fun i _ => by simp [cball]
  have hmem : ∀ b ∈ S, a + b ∈ box n R := fun b hb => hadd ha (hS b hb)
  choose! c hc using fun b (hb : b ∈ S) => (huniq (a + b) (hmem b hb)).exists
  have hF' : ∀ b ∈ S, F (a + b) = F (c b) := by
    intro b hb
    have := hF _ (hc b hb).2 (c b)
    rwa [add_sub_cancel] at this
  have hinj : ∀ x ∈ S, ∀ y ∈ S, c x = c y → x = y := by
    intro x hx y hy h
    have e : x - y = (a + x - c x) + -(a + y - c y) := by rw [h]; abel
    have h1 : x - y ∈ box n r := e ▸ hadd (hc x hx).2 (hneg (hc y hy).2)
    obtain ⟨z, -, huq⟩ := huniq x (hS x hx)
    exact (huq x ⟨hx, by simpa using hzero⟩).trans (huq y ⟨hy, h1⟩).symm
  have himg : S.image c = S := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      exact (hc b hb).1
    · rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)]
  rw [Finset.sum_congr rfl hF', ← Finset.sum_image hinj, himg]

end GlobalTheory.CosetSumShift
