module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.SeqCx

theorem cycle_pair_empty (V W : Type) (D : Set (List V × List W)) (p : ℕ) (c : List V →₀ ℤ)
    (hc : c ∈ chains {l | (l, ([] : List W)) ∈ D} p) (hb : bd V c = 0) :
    Finsupp.mapDomain (fun l => (l, ([] : List W))) c ∈ chains2 D p 0 ∧
      hbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 ∧
      vbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 := by
  have hlin : ∀ d : List V →₀ ℤ, Finsupp.mapDomain (fun l => (l, ([] : List W))) d
      = Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W))) d := fun d => rfl
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [chains2, Finsupp.mem_supported]
    rw [chains, Finsupp.mem_supported] at hc
    intro z hz
    have hz' := Finsupp.mapDomain_support hz
    rw [Finset.mem_image] at hz'
    obtain ⟨l, hl, rfl⟩ := hz'
    have := hc (Finset.mem_coe.mpr hl)
    exact ⟨this.1, this.2, rfl⟩
  · have key : (hbd V W).comp (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W))))
        = (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W)))).comp (bd V) := by
      apply Finsupp.lhom_ext'
      intro l
      apply LinearMap.ext_ring
      simp [hbd, Finsupp.mapDomain_single]
    have := LinearMap.congr_fun key c
    simp only [LinearMap.comp_apply] at this
    rw [hlin, this, hb, map_zero]
  · have key : (vbd V W).comp (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W)))) = 0 := by
      apply Finsupp.lhom_ext'
      intro l
      apply LinearMap.ext_ring
      simp [vbd, bd, Finsupp.mapDomain_single]
    have := LinearMap.congr_fun key c
    simpa [LinearMap.comp_apply] using this

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pair_nil_hbd_vbd_eq_zero_of_cycle : ∀ (V W : Type) (D : Set (List V × List W)) (p : ℕ) (c : List V →₀ ℤ), c ∈ chains {l | (l, ([] : List W)) ∈ D} p → bd V c = 0 → Finsupp.mapDomain (fun l => (l, ([] : List W))) c ∈ chains2 D p 0 ∧ hbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 ∧ vbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 := by
  first
  | exact @GlobalTheory.SeqCx.cycle_pair_empty
end
