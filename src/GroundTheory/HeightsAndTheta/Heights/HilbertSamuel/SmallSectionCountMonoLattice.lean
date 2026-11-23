module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter

noncomputable section

theorem chartLat_le_chartLatNm {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) :
    chartLat y a τ ≤ chartLatNm y a τ := by
  intro s hs c hc
  have h := hs c hc
  rw [mem_integralClosure_iff]
  exact isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, h⟩)

theorem smallSectionCount_mono_lattice {Ω : Type*} [CommRing Ω] (P : ℕ → Ω → Prop) {La La' : ℕ → AddSubgroup Ω}
    (τ : ℕ) (hle : La τ ≤ La' τ) (hfin : {s : La' τ | P τ (s : Ω)}.Finite) :
    smallSectionCount P La τ ≤ smallSectionCount P La' τ := by
  unfold smallSectionCount
  have : Finite {s : La' τ // P τ (s : Ω)} := hfin.to_subtype
  have hc : Nat.card {s : La τ // P τ (s : Ω)} ≤ Nat.card {s : La' τ // P τ (s : Ω)} := by
    refine Nat.card_le_card_of_injective
      (fun s => (⟨⟨(s.1 : Ω), hle s.1.2⟩, s.2⟩ : {s : La' τ // P τ (s : Ω)})) ?_
    intro s t hst
    exact Subtype.ext (Subtype.ext (congrArg (fun u : {s : La' τ // P τ (s : Ω)} => ((u.1 : La' τ) : Ω)) hst))
  rcases Nat.eq_zero_or_pos (Nat.card {s : La τ // P τ (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hc)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
